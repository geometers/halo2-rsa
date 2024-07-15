use ff::PrimeFieldBits;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use crate::poly_eval::{self, LoadedPoly};

#[derive(Clone)]
pub(crate) struct Config<const BASE: u8, const N: usize, const K: usize, F: PrimeFieldBits> {
    poly: poly_eval::Config<K, F>,
    carry: Column<Advice>,
    shifted_carry: Column<Advice>,
    init_selector: Selector,
    selector: Selector,
    carry_shift_selector: Selector,
}

impl<const BASE: u8, const N: usize, const K: usize, F: PrimeFieldBits> Config<BASE, N, K, F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        poly: poly_eval::Config<K, F>,
        carry: Column<Advice>,
    ) -> Self {
        let base = F::from_u128(1 << BASE);
        let init_selector = meta.selector();
        let selector = meta.selector();
        let carry_shift_selector = meta.selector();

        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        let shifted_carry = poly.range_check.running_sum;

        /*
            given array of coeffs in little-endian

            init_selector    selector       coeffs          carry
                1                0            a0      c0 | a0 = c0 * B
                0                1            a1      c1 | (a1 + c0) = c1 * B
                0                1            a2      c2 | (a2 + c1) = c2 * B
                0                1            a3      c3 | (a3 + c2) = c3 * B
                0                1            a4      c4 | (a4 + c3) = c4 * B | c4 == 0
        */

        meta.create_gate("check init carry", |meta| {
            let init_selector = meta.query_selector(init_selector);
            let coeff = meta.query_advice(poly.poly, Rotation::cur());
            let carry = meta.query_advice(carry, Rotation::cur());

            vec![init_selector * (carry * base - coeff)]
        });

        meta.create_gate("check carry", |meta| {
            let selector = meta.query_selector(selector);
            let coeff = meta.query_advice(poly.poly, Rotation::cur());
            let carry_prev = meta.query_advice(carry, Rotation::prev());
            let carry_cur = meta.query_advice(carry, Rotation::cur());
            vec![selector * (coeff + carry_prev - carry_cur * base)]
        });

        meta.create_gate("shift carry", |meta| {
            let selector = meta.query_selector(carry_shift_selector);
            let shifted_carry = meta.query_advice(shifted_carry, Rotation::cur());
            let carry_val = meta.query_advice(carry, Rotation::cur());
            let shift = {
                let two_pow_63 = Expression::Constant(F::from(1 << 63));
                let two_pow_6 = Expression::Constant(F::from(1 << 6));
                two_pow_63 * two_pow_6
            };

            vec![selector * (carry_val + shift - shifted_carry)]
        });

        Self {
            poly,
            carry,
            shifted_carry,
            selector,
            init_selector,
            carry_shift_selector,
        }
    }

    pub(crate) fn synthesize(
        &self,
        mut layouter: impl Layouter<F>,
        f: &[Value<F>; N],
        x: Value<F>,
    ) -> Result<LoadedPoly<N, F>, Error> {
        let base_inv = Value::known(F::from_u128(1 << BASE).invert().unwrap());

        /*
           init_selector    selector       coeffs          carry
               1                0            a0      c0 | a0 = c0 * B
               0                1            a1      c1 | (a1 + c0) = c1 * B
               0                1            a2      c2 | (a2 + c1) = c2 * B
               0                1            a3      c3 | (a3 + c2) = c3 * B
               0                1            a4      c4 | (a4 + c3) = c4 * B | c4 == 0
        */
        let (f_loaded, shifted_carries) = layouter.assign_region(
            || "check carry to zero",
            |mut region| {
                let mut shifted_carries = vec![];
                let shift = |carry: Value<F>| {
                    let two_pow_63 = F::from(1 << 63);
                    let two_pow_6 = F::from(1 << 6);
                    let two_pow_69 = two_pow_6 * two_pow_63;
                    carry + Value::known(two_pow_69)
                };

                // assign f
                let f_loaded = self.poly.witness_and_evaluate_inner(&mut region, 0, f, x)?;

                // enable init selector
                self.init_selector.enable(&mut region, 0)?;

                let mut carry = f[0] * base_inv;
                let mut carry_cell = region.assign_advice(|| "carry 0", self.carry, 0, || carry)?;
                // carry = [-2^69, 2^69]
                // check that carry + 2^69 is in range [0, 2^70]
                self.carry_shift_selector.enable(&mut region, 0)?;
                let shifted_carry = region.assign_advice(
                    || "shifted carry",
                    self.shifted_carry,
                    0,
                    || shift(carry),
                )?;
                shifted_carries.push(shifted_carry);

                for i in 1..N {
                    self.selector.enable(&mut region, i)?;
                    self.carry_shift_selector.enable(&mut region, i)?;

                    carry = (carry + f[i]) * base_inv;
                    carry_cell = region.assign_advice(|| "carry", self.carry, i, || carry)?;

                    let shifted_carry = region.assign_advice(
                        || "shifted carry",
                        self.shifted_carry,
                        i,
                        || shift(carry),
                    )?;
                    shifted_carries.push(shifted_carry);
                }

                region.constrain_constant(carry_cell.cell(), F::ZERO)?;

                Ok((f_loaded, shifted_carries))
            },
        )?;

        for shifted_carry in shifted_carries.iter() {
            self.poly.range_check.copy_check(
                layouter.namespace(|| "range check shifted_carry"),
                &shifted_carry,
                70,
            )?;
        }

        Ok(f_loaded)
    }
}
