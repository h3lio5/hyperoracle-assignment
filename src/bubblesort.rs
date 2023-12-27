use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};

use eth_types::Field;
use gadgets::less_than::{LtChip, LtConfig, LtInstruction};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
struct ACell<F: Field>(AssignedCell<F, F>);

#[derive(Clone, Debug)]
pub struct BubbleSortConfig<F: Field, const ARR_LEN: usize> {
    swap_selector: Selector,
    array_columns: [Column<Advice>; ARR_LEN],
    value_l: Column<Advice>,
    value_r: Column<Advice>,
    instance: Column<Instance>,
    lt: LtConfig<F, 4>,
}

#[derive(Clone, Debug)]
struct BubbleSortChip<F: Field, const ARR_LEN: usize> {
    config: BubbleSortConfig<F, ARR_LEN>,
}

impl<F: Field, const ARR_LEN: usize> BubbleSortChip<F, ARR_LEN> {
    fn construct(config: BubbleSortConfig<F, ARR_LEN>) -> Self {
        Self { config }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> BubbleSortConfig<F, ARR_LEN> {
        let swap_selector = meta.complex_selector();
        let array_columns = (0..ARR_LEN)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();

        let value_l = meta.advice_column();
        let value_r = meta.advice_column();

        let instance = meta.instance_column();

        // let _ = (0..ARR_LEN).map(|i| meta.enable_equality(array_columns[i]));
        for i in 0..ARR_LEN {
            meta.enable_equality(array_columns[i]);
        }

        meta.enable_equality(value_l);
        meta.enable_equality(value_r);
        meta.enable_equality(instance);

        // configure the LtChip
        let lt = LtChip::configure(
            meta,
            |meta| meta.query_selector(swap_selector),
            |meta| meta.query_advice(value_l, Rotation::cur()),
            |meta| meta.query_advice(value_r, Rotation::cur()),
        );

        // define the gate
        meta.create_gate("BubbleSort", |meta| {
            let q_enable = meta.query_selector(swap_selector);

            vec![q_enable.clone() * (lt.is_lt(meta, None) - q_enable)] // ideally there should be a check column, but we can drop it is essentially the same as the swap selector column.
        });

        BubbleSortConfig {
            swap_selector,
            array_columns: array_columns.as_slice().try_into().unwrap(),
            value_l,
            value_r,
            instance,
            lt,
        }
    }

    pub fn assign_first_row(
        &self,
        layouter: &mut impl Layouter<F>,
        lt_chip: LtChip<F, 4>,
        input_array: Vec<F>,
    ) -> Result<Vec<ACell<F>>, Error> {
        layouter.assign_region(
            || "first row (input array)",
            |mut region| {
                let mut prev_arr = Vec::new();
                // assign the first row
                for (i, value) in input_array.iter().enumerate() {
                    let assigned_cell = region
                        .assign_advice(
                            || "array[{i}] element",
                            self.config.array_columns[i],
                            0,
                            || Value::known(*value),
                        )
                        .map(ACell)?;

                    prev_arr.push(assigned_cell);
                }

                // fill the value_l, value_r columns with any arbitrary values as the inequality won't be checked
                region.assign_advice(
                    || "value_l",
                    self.config.value_l,
                    0,
                    || Value::known(F::from(369u64)),
                )?;
                region.assign_advice(
                    || "value_r",
                    self.config.value_l,
                    0,
                    || Value::known(F::from(369u64)),
                )?;

                lt_chip
                    .assign(
                        &mut region,
                        0,
                        Value::known(F::from(369u64)),
                        Value::known(F::from(369u64)),
                    )
                    .expect("assign first row lt_chip failed");

                // return the assigned cells which will be used to create equality constraint with the subsequent row assignment.
                Ok(prev_arr)
            },
        )
    }

    pub fn assign_row(
        &self,
        layouter: &mut impl Layouter<F>,
        lt_chip: LtChip<F, 4>,
        intermediate_array: Vec<ACell<F>>,
        swap_index: usize,
    ) -> Result<Vec<ACell<F>>, Error> {
        layouter.assign_region(
            || "intermediate row",
            |mut region| {
                let mut prev_arr = Vec::new();

                self.config
                    .swap_selector
                    .enable(&mut region, 0)
                    .expect("swap_selector enable failed @ assign_row");

                let n = intermediate_array.len();
                let mut i: usize = 0;

                while i < n {
                    if i == swap_index {
                        let mut assigned_cell = intermediate_array[i + 1]
                            .0
                            .copy_advice(
                                || "copy adjacent prev arr element",
                                &mut region,
                                self.config.array_columns[i],
                                0,
                            )
                            .map(ACell)?;

                        prev_arr.push(assigned_cell);

                        assigned_cell = intermediate_array[i]
                            .0
                            .copy_advice(
                                || "copy adjacent prev arr element",
                                &mut region,
                                self.config.array_columns[i + 1],
                                0,
                            )
                            .map(ACell)?;

                        prev_arr.push(assigned_cell);

                        i += 2;
                    } else {
                        let assigned_cell = intermediate_array[i]
                            .0
                            .copy_advice(
                                || "copy prev arr element",
                                &mut region,
                                self.config.array_columns[i],
                                0,
                            )
                            .map(ACell)?;

                        prev_arr.push(assigned_cell);

                        i += 1;
                    }
                }

                // copy the swapped pair to value_l and value_r
                prev_arr[swap_index]
                    .0
                    .copy_advice(|| "value_l assignment", &mut region, self.config.value_l, 0)
                    .expect("copy value_l @ assign_row failed");

                prev_arr[swap_index + 1]
                    .0
                    .copy_advice(|| "value_r assignment", &mut region, self.config.value_r, 0)
                    .expect("copy value_r @ assign_row failed");

                lt_chip
                    .assign(
                        &mut region,
                        0,
                        prev_arr[swap_index].0.value().copied(),
                        prev_arr[swap_index + 1].0.value().copied(),
                    )
                    .expect("lt_chip assign @ assign_row failed");

                Ok(prev_arr)
            },
        )
    }

    pub fn expose_public(&self, mut layouter: impl Layouter<F>, cell: &ACell<F>, row: usize) {
        layouter.constrain_instance(cell.0.cell(), self.config.instance, row);
    }
}

#[derive(Default)]
struct BubbleSortCicuit<F: Field, const ARR_LEN: usize> {
    input_array: Vec<F>,
    _marker: PhantomData<F>,
}

impl<F: Field, const ARR_LEN: usize> Circuit<F> for BubbleSortCicuit<F, ARR_LEN> {
    type Config = BubbleSortConfig<F, ARR_LEN>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        BubbleSortChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        let chip = BubbleSortChip::<F, ARR_LEN>::construct(config.clone());
        let lt_chip = LtChip::construct(config.lt);

        lt_chip.load(&mut layouter)?;

        let compute_bubblesort_swap_indices = |mut array: Vec<F>| {
            let mut swap_indices = Vec::new();
            for i in 0..array.len() {
                for j in 0..array.len() - i - 1 {
                    if array[j + 1] < array[j] {
                        swap_indices.push(j);
                        array.swap(j, j + 1);
                    }
                }
            }
            swap_indices
        };

        let swap_indices = compute_bubblesort_swap_indices(self.input_array.clone());

        let mut prev_arr = chip
            .assign_first_row(&mut layouter, lt_chip.clone(), self.input_array.clone())
            .expect("assign row first failed");

        let _ = (0..ARR_LEN).map(|idx| {
            chip.expose_public(layouter.namespace(|| "input array"), &prev_arr[idx], idx)
        });

        for swap_idx in swap_indices {
            prev_arr = chip
                .assign_row(&mut layouter, lt_chip.clone(), prev_arr, swap_idx)
                .expect("assign row failed");
        }

        let _ = (0..ARR_LEN).map(|idx| {
            chip.expose_public(
                layouter.namespace(|| "sorted output array"),
                &prev_arr[idx],
                idx + ARR_LEN,
            )
        });

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::BubbleSortCicuit;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr as Fp};
    use std::marker::PhantomData;

    #[test]
    fn test_bubblesort_valid() {
        let k = 9;

        // input array
        let input = vec![3, 5, 1, 2]
            .into_iter()
            .map(|value| Fp::from(value))
            .collect::<Vec<_>>();

        let output = vec![1, 2, 3, 5]
            .into_iter()
            .map(|value| Fp::from(value))
            .collect::<Vec<_>>();

        let public_input = [&input[..], &output[..]].concat();
        let circuit = BubbleSortCicuit::<Fp, 4> {
            input_array: input.clone(),
            _marker: PhantomData::<Fp>,
        };

        let prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        prover.assert_satisfied();
    }

    #[test]
    fn test_bubblesort_big_array_valid() {
        let k = 10;

        // input array
        let input = vec![3, 5, 1, 2, 10, 15, 25, 3, 9, 12]
            .into_iter()
            .map(Fp::from)
            .collect::<Vec<_>>();

        let output = vec![1, 2, 3, 3, 5, 9, 10, 12, 15, 25]
            .into_iter()
            .map(Fp::from)
            .collect::<Vec<_>>();

        let public_input = [&input[..], &output[..]].concat();
        let circuit = BubbleSortCicuit::<Fp, 10> {
            input_array: input.clone(),
            _marker: PhantomData::<Fp>,
        };

        let prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        prover.assert_satisfied();
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn print_bubblesort_vanilla() {
        use plotters::prelude::*;

        let root =
            BitMapBackend::new("bubblesort-vanilla-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Bubblesort Vanilla Layout", ("sans-serif", 60))
            .unwrap();

        // input array
        let input = vec![3, 5, 1, 2]
            .into_iter()
            .map(|value| Fp::from(value))
            .collect::<Vec<_>>();

        let mut circuit = BubbleSortCicuit::<Fp, 4> {
            input_array: input.clone(),
            _marker: PhantomData::<Fp>,
        };

        halo2_proofs::dev::CircuitLayout::default()
            .render(9, &circuit, &root)
            .unwrap();
    }
}
