use std::{
    any::{Any, TypeId},
    collections::HashMap,
};

pub mod memory;
pub mod processor;

pub type Components = HashMap<TypeId, Box<dyn Any>>;
