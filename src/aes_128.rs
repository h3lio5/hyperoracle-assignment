use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*, poly::Rotation};

use std::marker::PhantomData;

#[derive(Clone, Debug)]
struct ACell<F: Field>(AssignedCell<F, F>);
