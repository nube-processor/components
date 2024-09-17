use std::any::TypeId;

use components::{memory::RAM, processor::Processor, Components};
use env_logger::{Builder, Target};
use log::error;

fn main() {
    // std::env::set_var("RUST_LOG", "debug");
    // // log config
    // let mut builder = Builder::from_default_env();
    // builder.target(Target::Stdout);
    // builder.init();
    //
    // let mut p = Processor::new();
    // let ram = RAM::with_capacity(5);
    // let mut components = Components::new();
    // components.insert(TypeId::of::<RAM>(), Box::new(ram));
    //
    // loop {
    //     if let Err(e) = p.instruction_cicle(&mut components) {
    //         error!("{e}");
    //         break;
    //     }
    // }
}
