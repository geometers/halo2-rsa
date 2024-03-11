use ff::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};

#[derive(Clone)]
pub(crate) struct MulConfig {
    values_1: Column<Advice>,
    values_2: Column<Advice>,
    selector: Selector,
}

/*
values_1  values_2
   a        b
   ab
*/
impl MulConfig {
    pub(crate) fn configure<F: Field>(
        meta: &mut ConstraintSystem<F>,
        values_1: Column<Advice>,
        values_2: Column<Advice>,
    ) -> Self {
        let selector = meta.selector();

        meta.create_gate("constrain a*b", |meta| {
            let selector = meta.query_selector(selector);
            let a = meta.query_advice(values_1, Rotation::cur());
            let b = meta.query_advice(values_2, Rotation::cur());

            let ab = meta.query_advice(values_1, Rotation::next());

            vec![selector * (a * b - ab)]
        });

        Self {
            values_1,
            values_2,
            selector,
        }
    }

    pub(crate) fn synthesize<F: Field>(
        &self,
        mut layouter: impl Layouter<F>,
        a: AssignedCell<F, F>,
        b: AssignedCell<F, F>,
        ab: AssignedCell<F, F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "constrain a*b == ab",
            |mut region| {
                self.selector.enable(&mut region, 0)?;
                a.copy_advice(|| "a", &mut region, self.values_1, 0)?;
                b.copy_advice(|| "b", &mut region, self.values_2, 0)?;
                ab.copy_advice(|| "ab", &mut region, self.values_1, 1)?;

                Ok(())
            },
        )
    }
}

#[derive(Clone)]
pub(crate) struct MulAddConfig {
    values_1: Column<Advice>,
    values_2: Column<Advice>,
    selector: Selector,
}
