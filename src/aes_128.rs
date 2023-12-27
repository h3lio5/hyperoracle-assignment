use gadgets::util::xor;
use halo2_proofs::{
    arithmetic::Field, circuit::*, halo2curves::ff::PrimeField, plonk::*, poly::Rotation,
};

use std::{alloc::LayoutErr, marker::PhantomData};

#[derive(Clone, Debug)]
struct ACell<F: PrimeField>(AssignedCell<F, F>);

static sbox_matrix: [u8; 256] = [
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
    0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
    0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
    0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
    0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
    0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
    0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
    0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
    0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
    0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
    0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16,
];

#[derive(Debug, Clone)]
struct AESByteMagicTablesConfig<F: PrimeField> {
    range_check_table: TableColumn,
    xor_table: TableColumn,
    xtime_table: TableColumn,
    sbox_table: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> AESByteMagicTablesConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let range_check_table = meta.lookup_table_column();
        let xor_table = meta.lookup_table_column();
        let xtime_table = meta.lookup_table_column();
        let sbox_table = meta.lookup_table_column();

        Self {
            range_check_table,
            xor_table,
            xtime_table,
            sbox_table,
            _marker: PhantomData,
        }
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "load the aes bytes magic lookup table",
            |mut table| {
                ////////// Range Check /////////////
                // checks if a value is within the range [0, 255)
                for (offset, value) in (0..256).enumerate() {
                    table
                        .assign_cell(
                            || "loading range check... ",
                            self.range_check_table,
                            offset,
                            || Value::known(F::from_u128(value as u128)),
                        )
                        .expect("loading range check table failed");
                }

                ////////// XOR Table /////////////
                // uses a trick to check that the (a xor b) is valid.
                // Trick: for all pairs of a byte value, i.e., (a,b) where both a and b lie in [0, 256)
                // compute f_xor = (2**24 + 2**16 * a + 2**8 * b + a xor b) and load it into the lookup table.
                // During proof generation, to check if a xor b is valid, we just lookup if the f_xor(a,b) is present in the table.
                let f_xor = || {
                    let mut xor_magic_value = vec![];
                    for a in 0..256 {
                        for b in 0..256 {
                            let value = 2_usize.pow(24)
                                + 2_usize.pow(16) * a
                                + 2_usize.pow(8) * b
                                + (a ^ b);
                            xor_magic_value.push(value);
                        }
                    }
                    xor_magic_value
                };

                let xor_magic_values = f_xor();
                for (offset, value) in xor_magic_values.into_iter().enumerate() {
                    table
                        .assign_cell(
                            || "loading xor values...",
                            self.xor_table,
                            offset,
                            || Value::known(F::from_u128(value as u128)),
                        )
                        .expect("loading xor table failed");
                }

                ////////////// XTime Table //////////////////
                // checks if galois multiplication in mix_column operation in an AES round is valid.
                // Trick: for all pairs of a byte value, i.e., (x,x_time) where both a and b lie in [0, 256)
                // compute f_xtime(a,b) = (2**25 + 2*8 * a + b), where b = xtime(a); load it into the lookup table.
                // During proof generation, to check if b is the correct xtime of a, we just lookup if f_xtime(a,b) is present in the table.
                let f_xtime = || {
                    let mut xtime_magic_values = vec![];
                    for a in 0..=255u8 {
                        let xtime = if (a & 0x80) == 0x80 {
                            (a << 1 ^ 0x1B) & 0xFF
                        } else {
                            a << 1
                        };

                        let xtime_magic =
                            2_usize.pow(25) + 2_usize.pow(8) * a as usize + xtime as usize;

                        xtime_magic_values.push(xtime_magic);
                    }
                    xtime_magic_values
                };

                let xtime_magic_values = f_xtime();
                for (offset, value) in xtime_magic_values.into_iter().enumerate() {
                    table
                        .assign_cell(
                            || "loading xtime table values...",
                            self.xtime_table,
                            offset,
                            || Value::known(F::from_u128(value as u128)),
                        )
                        .expect("loading xtime table failed");
                }

                //////////////////// SBOX Table /////////////////////
                // checks if the byte substition in the AES round happened using the correct bytes substition table
                // Trick: for all pairs of a byte value, i.e., (x,x_time) where both a and b lie in [0, 256)
                // compute f_sbox(a,b) = (a + 1) * 256 + b, where b = sbox[a]; load it into the lookup table.
                // During proof generation, to check if b = sbox[a], we just lookup if f_sbox(a,b) is present in the table.

                let f_sbox = || {
                    let mut sbox_magic_values = vec![];
                    for a in 0..256 {
                        let b = sbox_matrix[a];
                        let sbox = (a + 1) * 256 + b as usize;
                        sbox_magic_values.push(sbox);
                    }
                    sbox_magic_values
                };

                let sbox_magic_values = f_sbox();
                for (offset, value) in sbox_magic_values.into_iter().enumerate() {
                    table
                        .assign_cell(
                            || "loading sbox table values...",
                            self.sbox_table,
                            offset,
                            || Value::known(F::from_u128(value as u128)),
                        )
                        .expect("loading sbox table failed");
                }

                Ok(())
            },
        )
    }
}

#[derive(Debug, Clone)]
struct AES128Config<F: PrimeField> {
    q_range_check: Selector,
    q_xor: Selector,
    q_sbox: Selector,
    q_xor_col_adj: Selector,
    q_xor_total: Selector,
    q_xor_col_total: Selector,
    q_xtime: Selector,
    aes_state: [Column<Advice>; 16],
    byte_magic_table: AESByteMagicTablesConfig<F>,
}

impl<F: PrimeField> AES128Config<F> {
    pub fn construct(config: Self) -> Self {
        config
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_range_check = meta.complex_selector();
        let q_xor = meta.complex_selector();
        let q_sbox = meta.complex_selector();
        let q_xor_col_adj = meta.complex_selector();
        let q_xor_total = meta.complex_selector();
        let q_xor_col_total = meta.complex_selector();
        let q_xtime = meta.complex_selector();

        let aes_state = (0..16).map(|_| meta.advice_column()).collect::<Vec<_>>();

        let byte_magic_table = AESByteMagicTablesConfig::configure(meta);

        let config = Self {
            q_range_check,
            q_xor,
            q_sbox,
            q_xor_col_adj,
            q_xor_total,
            q_xor_col_total,
            q_xtime,
            aes_state: aes_state.as_slice().try_into().unwrap(),
            byte_magic_table,
        };

        meta.lookup("aes byte magic tables lookup", |meta| {
            let qrc = meta.query_selector(q_range_check);
            let qxor = meta.query_selector(q_xor);
            let qxtime = meta.query_selector(q_xtime);
            let qsbox = meta.query_selector(q_sbox);

            let mut gates = vec![];
            // perform gate check separately for each of the 16 bytes
            // for i in 0..16 {
            //     let current_val = meta.query_advice(aes_state[i], Rotation::cur());
            //     // range check
            //     gates.push((
            //         qrc.clone() * current_val,
            //         byte_magic_table.range_check_table,
            //     ));

            //     // xor
            //     let previous_val = meta.query_advice(aes_state[i], Rotation::prev());
            //     let xor_magic_value = Expression::Constant(F::from_u128(2_u128.pow(24))) + Expression::Constant(F::from_u128(2_u128.pow(16))) * previous_val + Expression::Constant(F::from_u128(2_u128.pow(8))) +
            // }
            gates
        });

        config
    }

    pub fn assign_input(
        &self,
        layouter: &mut impl Layouter<F>,
        input_array: Vec<u8>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assigning input...",
            |mut region| {
                self.q_range_check.enable(&mut region, 0)?;
                for (col_idx, &value) in input_array.iter().enumerate() {
                    region
                        .assign_advice(
                            || "assigning input row",
                            self.aes_state[col_idx],
                            0,
                            || Value::known(F::from_u128(value as u128)),
                        )
                        .expect("assigning input row failed");
                }

                Ok(())
            },
        )
    }
    pub fn assign_key(
        &self,
        layouter: &mut impl Layouter<F>,
        key: &Vec<u8>,
        flag: bool,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assigning key...",
            |mut region| {
                if flag {
                    self.q_range_check.enable(&mut region, 0)?;
                }
                for (col_idx, &value) in key.iter().enumerate() {
                    region
                        .assign_advice(
                            || "assigning input row",
                            self.aes_state[col_idx],
                            0,
                            || Value::known(F::from_u128(value as u128)),
                        )
                        .expect("assigning key row failed");
                }

                Ok(())
            },
        )
    }
    pub fn assign_xor(
        &self,
        layouter: &mut impl Layouter<F>,
        byte_arr: &Vec<u8>,
        key: &Vec<u8>,
    ) -> Result<Vec<u8>, Error> {
        layouter.assign_region(
            || "assigning add_round_key result...",
            |mut region| {
                self.q_xor.enable(&mut region, 0)?;
                let mut prev_arr = vec![];
                for (col_idx, (&value_byte, &key_byte)) in byte_arr.iter().zip(key).enumerate() {
                    let xor_value = value_byte ^ key_byte;
                    region
                        .assign_advice(
                            || "assigning input row",
                            self.aes_state[col_idx],
                            0,
                            || Value::known(F::from_u128(xor_value as u128)),
                        )
                        .expect("assigning add_round_key (xor) row failed");
                    prev_arr.push(xor_value);
                }
                Ok(prev_arr)
            },
        )
    }

    pub fn assign_sub_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        byte_arr: &Vec<u8>,
    ) -> Result<(Vec<u8>, Vec<ACell<F>>), Error> {
        layouter.assign_region(
            || "assigning sub bytes...",
            |mut region| {
                self.q_sbox.enable(&mut region, 0)?;
                let mut prev_arr = vec![];
                let mut prev_arr_acell = vec![];
                for (col_idx, &value_byte) in byte_arr.iter().enumerate() {
                    let sub_byte_value = sbox_matrix[value_byte as usize];
                    let acell = region
                        .assign_advice(
                            || "assigning sub_bytes row",
                            self.aes_state[col_idx],
                            0,
                            || Value::known(F::from_u128(sub_byte_value as u128)),
                        )
                        .map(ACell)
                        .expect("assigning sub_bytes row failed");

                    prev_arr.push(sub_byte_value);
                    prev_arr_acell.push(acell);
                }
                Ok((prev_arr, prev_arr_acell))
            },
        )
    }

    pub fn assign_shift_rows(
        &self,
        layouter: &mut impl Layouter<F>,
        prev_arr_acell: &Vec<ACell<F>>,
        prev_arr: &Vec<u8>,
    ) -> Result<Vec<u8>, Error> {
        layouter.assign_region(
            || "assigning shift row output...",
            |mut region| {
                // no selector is needed here as enforcing equality is enough to do permutation check.
                let mut prev_arr_new = Vec::new();

                // first row is shifted to the right by 0 steps, i.e., prev_arr[0..4] remain unchanged
                for i in 0..4 {
                    prev_arr_acell[i]
                        .0
                        .copy_advice(|| "shift row copy", &mut region, self.aes_state[i], 0)
                        .expect("copy advice failed @ assign_shift_rows/0");
                    prev_arr_new.push(prev_arr[i]);
                }

                // second row is shifted to the right by 1 step.
                // 4->5, 5->6, 6->7, 7->4
                for i in 4..8 {
                    let j = if i == 7 { 4 } else { i + 1 };
                    prev_arr_acell[i]
                        .0
                        .copy_advice(|| "shift row copy", &mut region, self.aes_state[j], 0)
                        .expect("copy advice failed @ assign_shift_rows/1");
                    prev_arr_new.push(prev_arr[j]);
                }

                // third row is shifted to the right by 2 steps.
                // 8->10, 9->11, 10->8, 11->9
                for i in 8..12 {
                    let j = if i > 9 { i - 2 } else { i + 2 };
                    prev_arr_acell[i]
                        .0
                        .copy_advice(|| "shift row copy", &mut region, self.aes_state[j], 0)
                        .expect("copy advice failed @ assign_shift_rows/2");
                    prev_arr_new.push(prev_arr[j]);
                }

                // fourth row is shifted to the right by 3 steps.
                // 12->15, 13->12, 14->13, 15->14
                for i in 12..16 {
                    let j = if i > 12 { i - 1 } else { i + 3 };
                    prev_arr_acell[i]
                        .0
                        .copy_advice(|| "shift row copy", &mut region, self.aes_state[j], 0)
                        .expect("copy advice failed @ assign_shift_rows/2");
                    prev_arr_new.push(prev_arr[j]);
                }

                Ok(prev_arr_new)
            },
        )
    }
    pub fn assign_xor_col_adj(
        &self,
        layouter: &mut impl Layouter<F>,
        prev_arr: &Vec<u8>,
    ) -> Result<Vec<u8>, Error> {
        layouter.assign_region(
            || "assigning xor adjacent column elements...",
            |mut region| {
                self.q_xor_col_adj.enable(&mut region, 0)?;

                let mut prev_arr_new = vec![];
                for i in 0..16 {
                    let xor_value = prev_arr[i] ^ prev_arr[(i + 4) % 16];
                    region
                        .assign_advice(
                            || "adjacent col xor",
                            self.aes_state[i],
                            0,
                            || Value::known(F::from_u128(xor_value as u128)),
                        )
                        .expect("assign advice failed @ assign_xor_col_adj");
                    prev_arr_new.push(xor_value);
                }
                Ok(prev_arr_new)
            },
        )
    }

    pub fn assign_xor_total(
        &self,
        layouter: &mut impl Layouter<F>,
        prev_arr: &Vec<u8>,
    ) -> Result<Vec<u8>, Error> {
        layouter.assign_region(
            || "assigning xor total...",
            |mut region| {
                self.q_xor_total.enable(&mut region, 0)?;

                let mut prev_arr_new = (0..16).collect::<Vec<u8>>();

                for i in 0..4 {
                    let xor_value = prev_arr[i] ^ prev_arr[i + 8];
                    for j in 0..4 {
                        region
                            .assign_advice(
                                || "assign xor total value",
                                self.aes_state[i + 4 * j],
                                0,
                                || Value::known(F::from_u128(xor_value as u128)),
                            )
                            .expect("assign advice failed @ assign_xor_total");
                        prev_arr_new[i + 4 * j] = xor_value;
                    }
                }
                Ok(prev_arr_new)
            },
        )
    }

    pub fn assign_xor_col_total(
        &self,
        layouter: &mut impl Layouter<F>,
        prev_arr_col: &Vec<u8>,
        prev_arr_total: &Vec<u8>,
    ) -> Result<Vec<u8>, Error> {
        layouter.assign_region(
            || "assigning xor(column,total)...",
            |mut region| {
                self.q_xor_col_total.enable(&mut region, 0)?;

                let mut prev_arr_new = vec![];
                for (col_idx, (&col_value, &total_value)) in
                    prev_arr_col.iter().zip(prev_arr_total).enumerate()
                {
                    let xor_value = col_value ^ total_value;
                    region
                        .assign_advice(
                            || "assign xor(col, total)",
                            self.aes_state[col_idx],
                            0,
                            || Value::known(F::from_u128(xor_value as u128)),
                        )
                        .expect("assign advice failed @ assign_xor_col_total");
                    prev_arr_new.push(xor_value);
                }
                Ok(prev_arr_new)
            },
        )
    }

    pub fn assign_xtime(
        &self,
        layouter: &mut impl Layouter<F>,
        prev_arr: &Vec<u8>,
    ) -> Result<Vec<u8>, Error> {
        layouter.assign_region(
            || "assigning xtime...",
            |mut region| {
                self.q_xtime.enable(&mut region, 0)?;

                let mut prev_arr_new = vec![];

                for (col_idx, &value) in prev_arr.iter().enumerate() {
                    let xtime_value = f_xtime(value);
                    region
                        .assign_advice(
                            || "assign xtime",
                            self.aes_state[col_idx],
                            0,
                            || Value::known(F::from_u128(xtime_value as u128)),
                        )
                        .expect("assign advice failed @ assign_xtime");
                    prev_arr_new.push(xtime_value);
                }
                Ok(prev_arr_new)
            },
        )
    }
}

#[derive(Default)]
struct AESCircuit<F: PrimeField> {
    input: [u8; 16],
    key: [u8; 16],
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for AESCircuit<F> {
    type Config = AES128Config<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        AES128Config::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let input = self.input.to_vec();
        let key = self.key.to_vec();

        let mut prev_arr: Vec<u8>;
        let mut prev_arr_acell: Vec<ACell<F>>;
        // fill in the first row with the input array.
        config
            .assign_input(&mut layouter, input.to_vec())
            .expect("failure @ assign_input");

        // fill in the second row with the key
        config
            .assign_key(&mut layouter, &key, true)
            .expect("failure @ assign_key");

        // initial add round key step
        prev_arr = config
            .assign_xor(&mut layouter, &input, &key)
            .expect("failure @ assign_add_round_key");
        // perform 9 rounds of AES128 block encryption
        for i in 0..9 {
            // substitute bytes
            (prev_arr, prev_arr_acell) = config
                .assign_sub_bytes(&mut layouter, &prev_arr)
                .expect("failure @ assign_sub_bytes");
            // shift rows
            prev_arr = config
                .assign_shift_rows(&mut layouter, &prev_arr_acell, &prev_arr)
                .expect("failure @ assign_shift_rows");

            // mix columns step is split into 5 separate steps
            // xor of adjacent elements of a column, i.e., xor (col_a[i], col_a[i+1])
            let prev_arr_xor_col_adj = config
                .assign_xor_col_adj(&mut layouter, &prev_arr)
                .expect("failure @ assign_xor_col_adj");
            // xor of all the elements of a column
            let prev_arr_xor_total = config
                .assign_xor_total(&mut layouter, &prev_arr_xor_col_adj)
                .expect("failure @ assign_xor_total");
            // xor column element with the total xor from the previous step, i.e., col_a[i] ^ t, where t = col_a[0] ^ col_a[1] ^ col_a[2] ^ col_a[3]
            let prev_arr_xor_col_total = config
                .assign_xor_col_total(&mut layouter, &prev_arr, &prev_arr_xor_total)
                .expect("failure @ assign_xor_col_total");
            // xtime
            let prev_arr_xtime = config
                .assign_xtime(&mut layouter, &prev_arr_xor_col_adj)
                .expect("failure @ assign_xtime");
            // final mix columns result
            prev_arr = config
                .assign_xor(&mut layouter, &prev_arr_xtime, &prev_arr_xor_col_total)
                .expect("failure @ mix columns assign_xor");
            // add key
            config
                .assign_key(&mut layouter, &key, false)
                .expect("failure @ aes round assign_key");
            // perform add_round_key
            prev_arr = config
                .assign_xor(&mut layouter, &prev_arr, &key)
                .expect("failure @ add_round_key assign_xor");
        }

        // final round of AES 128
        (prev_arr, prev_arr_acell) = config
            .assign_sub_bytes(&mut layouter, &prev_arr)
            .expect("failure @ final round assign_sub_bytes");
        prev_arr = config
            .assign_shift_rows(&mut layouter, &prev_arr_acell, &prev_arr)
            .expect("failure @ final round assign_shift_rows");
        // add key
        config
            .assign_key(&mut layouter, &key, false)
            .expect("failure @ final round assign_key");
        prev_arr = config
            .assign_xor(&mut layouter, &prev_arr, &key)
            .expect("failure @ final round add_round_key assign_xor");

        Ok(())
    }
}

// placing it a the end because the symbol "<<" was messing with the syntax hightlighting for the code below it.
pub fn f_xtime(value: u8) -> u8 {
    if (value & 0x80) == 0x80 {
        ((value << 1) ^ 0x1B) & 0xFF
    } else {
        value << 1
    }
}
