use differential_dataflow::difference::Abelian;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::operators::arrange::ArrangeBySelf;
use differential_dataflow::operators::Reduce;
use differential_dataflow::AsCollection;
use differential_dataflow::Collection;
use timely::dataflow::operators::probe::Handle;
use timely::dataflow::operators::UnorderedInput;
use timely::dataflow::Scope;
use timely::progress::{Antichain, Timestamp};

use dogsdogsdogs::altneu::AltNeu;
use dogsdogsdogs::calculus::Integrate;

use order::Time;

/// Reclocks an FromTime collection record into AltNeu<IntoTime> collection records using the
/// `IntoTime` `frontier`.
///
/// Each record is made visible at `Alt(into_ts)` for each `into_ts` in frontier and then retracted
/// at the the combined `Neu(Lattice::join(..))` of all the `into_ts` in `frontier.
fn reclock_record<D, R, FromTime, IntoTime>(
    (data, time, diff): (D, FromTime, R),
    frontier: Antichain<IntoTime>,
) -> Vec<((D, FromTime, R), AltNeu<IntoTime>, R)>
where
    FromTime: Timestamp,
    IntoTime: Timestamp + Lattice,
    D: timely::Data,
    R: Abelian,
{
    // This is the original triplet that will become the data of the new collection
    let orig_record = (data, time, diff.clone());

    let mut updates = vec![];

    // First make the record visible at the indicated times and keep track how many copies we
    // introduce
    let mut total_diff = R::zero();
    for into_ts in frontier.iter().cloned() {
        total_diff.plus_equals(&diff);
        updates.push((orig_record.clone(), AltNeu::alt(into_ts), diff.clone()));
    }

    // And then make the record invisible at the join of all the indicated times
    let mut neu_into_ts = IntoTime::minimum();
    for into_ts in frontier.iter() {
        neu_into_ts = neu_into_ts.join(into_ts);
    }
    updates.push((orig_record, AltNeu::neu(neu_into_ts), total_diff.negate()));

    updates
}

type FromTime = u64;

fn main() {
    timely::execute_from_args(std::env::args().skip(2), move |worker| {
        let mut probe = Handle::new();

        let (mut handle, cap) = worker.dataflow::<_, _, _>(|scope| {
            scope.scoped::<AltNeu<Time>, _, _>("Reclock", |inner| {
                let ((handle, cap), stream) = inner.new_unordered_input();

                let source: Collection<_, (String, FromTime, i64), i64> = stream.as_collection();

                source
                    .inspect(|record| println!("original record {record:?}"))
                    .arrange_by_self()
                    .reduce(|(_data, _from_ts, diff), _input, output| {
                        // At any timestamp that this record has copies at we must re-assert that
                        // it has its original diff.
                        output.push(((), *diff));
                    })
                    .integrate()
                    .map(|record| record.0 .0)
                    .inspect(|record| println!("reclocked record {record:?}"))
                    .probe_with(&mut probe);

                (handle, cap)
            })
        });

        // We will pretend that there is a record "data" that was reclocked into the Time time
        // domain and it is supposed to be visible at timestamps B, C, D.
        //
        // The goal of the dataflow above is to ensure that the "data" record is never double
        // counted as the Time lattice joins.
        //
        // The way to do that is to generate the following corrective actions:
        // ("data", E, -2)
        // ("data", F, -2)
        // ("data", G, -2) <--
        // ("data", G, 2)  <-- the last two will cancel out
        let record = ("data".to_owned(), 0, 2);
        let frontier = Antichain::from_iter([Time::B, Time::C, Time::D]);
        for (record, time, diff) in reclock_record(record, frontier) {
            handle
                .session(cap.delayed(&time))
                .give((record, time, diff));
        }
        drop(cap);
        while !probe.done() {
            worker.step();
        }
    })
    .unwrap();
}

/// Defines a partialy ordered time that looks like this:
///    ,--B----E.
///   /       /  \
///  /       /    \
/// A-------C------G
///  \       \    /
///   \       \  /
///    `--D----F'
mod order {
    use differential_dataflow::lattice::Lattice;
    use serde::{Deserialize, Serialize};
    use timely::order::PartialOrder;
    use timely::progress::timestamp::{PathSummary, Refines, Timestamp};

    #[derive(Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
    pub enum Time {
        A,
        B,
        C,
        D,
        E,
        F,
        G,
    }

    impl Timestamp for Time {
        type Summary = ();

        fn minimum() -> Self {
            Self::A
        }
    }

    impl PathSummary<Time> for () {
        fn results_in(&self, src: &Time) -> Option<Time> {
            Some(*src)
        }
        fn followed_by(&self, _other: &Self) -> Option<Self> {
            Some(())
        }
    }

    impl Refines<()> for Time {
        fn to_inner(_other: ()) -> Self {
            Time::A
        }
        fn to_outer(self) {}
        fn summarize(_path: Self::Summary) -> <() as Timestamp>::Summary {}
    }

    impl PartialOrder for Time {
        fn less_equal(&self, other: &Self) -> bool {
            matches!((self, other), |(Time::A, _)| (
                Time::B,
                Time::B | Time::E | Time::G
            ) | (
                Time::C,
                Time::C | Time::E | Time::F | Time::G
            ) | (
                Time::D,
                Time::D | Time::F | Time::G
            ) | (
                Time::E,
                Time::E | Time::G
            ) | (
                Time::F,
                Time::F | Time::G
            ) | (Time::G, Time::G))
        }
    }

    impl Lattice for Time {
        fn join(&self, other: &Self) -> Self {
            match (self, other) {
                (min, max) if PartialOrder::less_equal(min, max) => *max,
                (max, min) if PartialOrder::less_equal(min, max) => *max,
                (Time::B, Time::D)
                | (Time::D, Time::B)
                | (Time::B, Time::F)
                | (Time::F, Time::B)
                | (Time::E, Time::D)
                | (Time::D, Time::E)
                | (Time::E, Time::F)
                | (Time::F, Time::E) => Time::G,
                (Time::B, Time::C) | (Time::C, Time::B) => Time::E,
                (Time::C, Time::D) | (Time::D, Time::C) => Time::F,
                _ => unreachable!(),
            }
        }

        fn meet(&self, other: &Self) -> Self {
            match (self, other) {
                (min, max) if PartialOrder::less_equal(min, max) => *min,
                (max, min) if PartialOrder::less_equal(min, max) => *min,
                (Time::B, Time::C)
                | (Time::C, Time::B)
                | (Time::C, Time::D)
                | (Time::D, Time::C)
                | (Time::B, Time::D)
                | (Time::D, Time::B)
                | (Time::B, Time::F)
                | (Time::F, Time::B)
                | (Time::E, Time::D)
                | (Time::D, Time::E) => Time::A,
                (Time::E, Time::F) | (Time::F, Time::E) => Time::C,
                _ => unreachable!(),
            }
        }
    }
}
