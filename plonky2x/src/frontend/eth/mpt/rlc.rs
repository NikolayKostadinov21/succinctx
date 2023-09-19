use std::cmp;
use itertools::Itertools;
use plonky2::{hash::poseidon::PoseidonHash, iop::target::BoolTarget};
use plonky2::iop::challenger::RecursiveChallenger;
use crate::prelude::{BoolVariable, ByteVariable, CircuitBuilder, PlonkParameters, Variable};

impl<L: PlonkParameters<D>, const D: usize> CircuitBuilder<L, D> {
    fn commit_subarray(
        &mut self,
        arr: &[ByteVariable],
        offset: Variable,
        len: Variable,
        random_variables: &[Variable]
    ) -> Variable {
        let one = self.one();
        let end_idx = self.add(offset, len);
        let mut is_within_subarray: Variable = self.zero();
        let mut commitment = self.zero();

        let mut idx_target = self.zero();
        for idx in 0..arr.len() {
            // is_within_subarray is one if idx is in the range [offset..offset+len]
            let is_at_start_idx = self.is_equal(idx_target, offset);
            is_within_subarray = self.add(is_within_subarray, is_at_start_idx.0);
            let is_at_end_idx = self.is_equal(idx_target, end_idx);
            is_within_subarray = self.sub(is_within_subarray, is_at_end_idx.0);

            let arr_bits = self.to_le_bits(arr[idx])
                .iter()
                .map(|x| BoolTarget::new_unsafe(x.0.0))
                .collect_vec();
            let arr_var= Variable(self.api.le_sum(arr_bits.iter()));

            let arrs_mul = self.mul(arr_var, random_variables[idx]);
            let random_value_if_in_range = self.mul(is_within_subarray, arrs_mul);
            commitment = self.add(commitment, random_value_if_in_range);

            idx_target = self.add(idx_target, one);
        }

        commitment
    }

    pub fn subarray_equal(
        &mut self,
        a: &[ByteVariable],
        a_offset: Variable,
        b: &[ByteVariable],
        b_offset: Variable,
        len: Variable,
    ) -> BoolVariable {
        let mut challenger = RecursiveChallenger::<L::Field, PoseidonHash, D>::new(&mut self.api);
        let challenger_seed = Vec::new();
        challenger.observe_elements(&challenger_seed);
        let random_variables = challenger.get_n_challenges(&mut self.api, cmp::max(a.len(), b.len()))
            .iter()
            .map(|target| Variable(*target))
            .collect_vec();

        let commitment_for_a = self.commit_subarray(a, a_offset, len, &random_variables[..]);
        let commitment_for_b = self.commit_subarray(b, b_offset, len, &random_variables[..]);
        self.is_equal(commitment_for_a, commitment_for_b)
    }

    #[allow(unused_variables, dead_code)]
    pub fn assert_subarray_equal(
        &mut self,
        a: &[ByteVariable],
        a_offset: Variable,
        b: &[ByteVariable],
        b_offset: Variable,
        len: Variable,
    ) {
        let subarrays_are_equal = self.subarray_equal(a, a_offset, b, b_offset, len);
        let _true = self._true();
        self.assert_is_equal(subarrays_are_equal, _true);
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use anyhow::Result;
    use crate::{frontend::builder::DefaultBuilder, prelude::{BoolVariable, Variable}};
    use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig}, field::types::Field, iop::witness::PartialWitness};
    use crate::prelude::ByteVariable;

    #[test]
    pub fn test_subarray_equal_should_succeed() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut builder = DefaultBuilder::new();

        let byte1 = ByteVariable([
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
        ]);

        let byte2 = ByteVariable([
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ZERO)),// this bit is different
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
        ]);

        let byte3 = byte1;
        let byte4 = byte2;

        let a: [ByteVariable; 2] = [byte1, byte2];
        let a_offset = builder.constant(F::ZERO);
        let b: [ByteVariable; 2] = [byte3, byte4];
        let b_offset = builder.constant(F::ZERO);
        let len: Variable = builder.constant(F::from_canonical_u8(2));
        builder.assert_subarray_equal(&a, a_offset, &b, b_offset, len);

        let pw = PartialWitness::new();
        let circuit = builder.build();
        let proof = circuit.data.prove(pw).unwrap();
        circuit.data.verify(proof)
    }

    #[test]
    #[should_panic]
    pub fn test_subarray_equal_should_fail() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut builder = DefaultBuilder::new();

        let byte1 = ByteVariable([
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
        ]);

        let byte2 = ByteVariable([
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ZERO)),// this bit is different
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
            BoolVariable(builder.constant(F::ONE)),
        ]);

        let byte3 = byte1;
        let byte4 = byte1;

        let a: [ByteVariable; 2] = [byte1, byte2];
        let a_offset = builder.constant(F::ZERO);
        let b: [ByteVariable; 2] = [byte3, byte4];
        let b_offset = builder.constant(F::ZERO);
        let len: Variable = builder.constant(F::from_canonical_u8(2));
        builder.assert_subarray_equal(&a, a_offset, &b, b_offset, len);

        let pw = PartialWitness::new();
        let circuit = builder.build();
        let proof = circuit.data.prove(pw).unwrap();
        circuit.data.verify(proof).unwrap(); // panics
    }
}
