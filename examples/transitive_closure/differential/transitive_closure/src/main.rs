extern crate timely;
extern crate differential_dataflow;

use differential_dataflow::input::InputSession;
use differential_dataflow::operators::*;

fn main() {

        // define a new timely dataflow computation.
        timely::execute_from_args(std::env::args(), move |worker| {

        // create an input collection of data.
        let mut input = InputSession::new();

        // define a new computation.
        worker.dataflow(|scope| {

            // create a new collection from our input.
            let contents = input.to_collection(scope);

            // relation `parent` -> (FSObject, Dir)
            // relation `contents` -> (Dir, FSObject)
            
            // Compute transitive closure of `contents` relation
            let star_contents = contents.iterate(|transitive| {
                transitive.map(|(dir, fsobj)| (fsobj, dir))
                    .join(&transitive)
                    .map(|(key, (fsobj1, fsobj2))| (fsobj1, fsobj2))
                    .concat(&transitive)
                    .distinct()
            })
            .inspect(|x| println!("path: {:?}, timestamp: {:?}, diff: {:?}", x.0, x.1, x.2));

            // Find self cycles in the transitive closure 
            star_contents
                .map(|(dir, fsobj)| (fsobj, dir))
                .join(&contents)
                .inspect(|x| println!("cycle: {:?}, timestamp: {:?}, diff: {:?}", x.0, x.1, x.2));
            
        });

        // (dir, fsobj) where fsobj is either a file or a directory
        input.advance_to(0);
        input.insert((0, 1));
        input.insert((1, 2));
        input.insert((2, 3));

        input.advance_to(1);
        input.insert((3, 4));

        input.advance_to(2);
        input.remove((3, 4));

        // Add self cycles to make it fail
        input.advance_to(3);
        input.insert((3, 0));

    }).expect("Computation terminated abnormally");
}