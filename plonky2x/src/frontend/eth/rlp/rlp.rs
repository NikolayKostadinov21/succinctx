use std::marker::PhantomData;

use curta::math::prelude::PrimeField64;
use ethers::types::{Bytes, H256};
use num::bigint::ToBigInt;
use num::BigInt;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::Target;
use plonky2::iop::witness::PartitionWitness;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::util::serialization::{Buffer, IoResult};

use crate::frontend::num::u32::gadgets::multiple_comparison::list_le_circuit;
use crate::prelude::{
    ArrayVariable, BoolVariable, ByteVariable, CircuitBuilder, CircuitVariable, Variable, BytesVariable,
};

pub fn bool_to_u32(b: bool) -> u32 {
    if b {
        1
    } else {
        0
    }
}
// Note this only decodes bytes and doesn't support long strings
pub fn rlp_decode_bytes(input: &[u8]) -> (Vec<u8>, usize) {
    let prefix = input[0];
    if prefix <= 0x7F {
        (vec![prefix], 1)
    } else if prefix == 0x80 {
        (vec![], 1) // null value
    } else if prefix <= 0xB7 {
        // Short string (0-55 bytes length)
        let length = (prefix - 0x80) as usize;
        let res = &input[1..1 + length];
        (res.into(), 1 + length)
    } else if prefix <= 0xBF {
        // Long string (more than 55 bytes length)
        let len_of_str_len = (prefix - 0xB7) as usize;
        let mut str_len_bytes: Vec<u8> = input[1..1 + len_of_str_len].to_vec();
        str_len_bytes.reverse();
        let mut str_len = 0;
        for i in 0..len_of_str_len {
            str_len += str_len_bytes[i] as usize * 256_usize.pow(i as u32);
        }
        return (
            input[1 + len_of_str_len..1 + len_of_str_len + str_len].into(),
            1 + len_of_str_len + str_len,
        );
    } else {
        println!("input {:?}", input);
        panic!("Invalid prefix rlp_decode_bytes")
    }
}

pub fn rlp_decode_list_2_or_17(input: &[u8]) -> Vec<Vec<u8>> {
    println!("input {:?}", Bytes::from(input.to_vec()).to_string());
    let prefix = input[0];

    // Short list (0-55 bytes total payload)
    if prefix <= 0xF7 {
        let list_length = (prefix - 0xC0) as usize;
        // We assert that the input is simply [list_length, list_content...] and not suffixed by anything else
        assert!(input.len() == 1 + list_length);
        let (ele_1, increment) = rlp_decode_bytes(&input[1..]);
        let (ele_2, _) = rlp_decode_bytes(&input[1 + increment..]);
        vec![ele_1, ele_2]
    } else {
        println!("hi in this case");
        // TODO: check that prefix is bounded within a certain range
        let len_of_list_length = prefix - 0xF7;
        // println!("len_of_list_length {:?}", len_of_list_length);
        // TODO: figure out what to do with len_of_list_length
        let mut pos = 1 + len_of_list_length as usize;
        let mut res = vec![];
        for _ in 0..17 {
            let (ele, increment) = rlp_decode_bytes(&input[pos..]);
            println!("ele {:?}", Bytes::from(ele.clone()).to_string());
            println!("increment {:?}", increment);
            res.push(ele);
            pos += increment;
            if pos == input.len() {
                break;
            }
        }
        assert!(pos == input.len()); // Checks that we have iterated through all the input
        assert!(res.len() == 17 || res.len() == 2);
        println!("END");
        res
    }
}

/// Given `encoded` which is a RLP-encoded list, passed in as a byte array of length `M`, with "true length" `len`
pub fn decode_element_as_list<
    const ENCODING_LEN: usize,
    const LIST_LEN: usize,
    const ELEMENT_LEN: usize,
>(
    encoded: &[u8],
    len: usize,
    finish: bool,
) -> (Vec<Vec<u8>>, Vec<usize>, usize) {
    assert_eq!(encoded.len(), ENCODING_LEN);
    assert!(len <= ENCODING_LEN); // len is the "true" length of "encoded", which is padded to length `ENCODING_LEN`
    assert!(LIST_LEN == 2 || LIST_LEN == 17); // Right now we only support decoding lists of length 2 or 17

    let mut decoded_list_as_fixed = vec![vec![0u8; ELEMENT_LEN]; LIST_LEN];
    let mut decoded_list_lens = vec![0usize; LIST_LEN];
    let decoded_list_len = 0;
    if finish {
        // terminate early
        return (decoded_list_as_fixed, decoded_list_lens, decoded_list_len);
    }
    let decoded_element = rlp_decode_list_2_or_17(&encoded[..len]);
    for (i, element) in decoded_element.iter().enumerate() {
        let len: usize = element.len();
        assert!(
            len <= ELEMENT_LEN,
            "The decoded element should have length <= {ELEMENT_LEN}!"
        );
        decoded_list_as_fixed[i][..len].copy_from_slice(element);
        decoded_list_lens[i] = len;
    }
    (
        decoded_list_as_fixed,
        decoded_list_lens,
        decoded_element.len(),
    )
}

fn parse_list_element(element: [u8; 32], len: u8) -> (u32, u32) {
    let prefix = element[0];
    if len == 0 {
        (0x80, 0)
    } else if len == 1 && prefix <= 0x7F {
        (prefix as u32, 0)
    } else if len == 1 && prefix > 0x7F {
        // TODO: maybe this is the same as the below case
        (0x80 + 0x01, 1)
    } else if len <= 55 {
        (len as u32 + 0x80, len as u32)
    } else {
        panic!("Invalid length and prefix combo {} {}", len, prefix)
    }
}

// This is the vanilla implementation of the RLC trick for verifying the decoded_list
pub fn verify_decoded_list<const L: usize, const M: usize>(
    list: [[u8; 32]; L],
    lens: [u8; L],
    encoding: [u8; M],
) {
    let random = 1000_i32.to_bigint().unwrap();

    let mut size_accumulator: u32 = 0;
    let mut claim_poly = BigInt::default();
    for i in 0..L {
        let (start_byte, list_len) = parse_list_element(list[i], lens[i]);
        let mut poly = start_byte.to_bigint().unwrap() * random.pow(size_accumulator);
        for j in 0..32 {
            poly += list[i][j] as u32
                * (random.pow(1 + size_accumulator + j as u32))
                * bool_to_u32(j as u32 <= list_len);
        }
        size_accumulator += 1 + list_len;
        claim_poly += poly;
    }

    let mut encoding_poly = BigInt::default();
    for i in 3..M {
        // TODO: don't hardcode 3 here
        let idx = i - 3;
        encoding_poly += encoding[i] as u32
            * (random.pow(idx as u32))
            * bool_to_u32(idx < size_accumulator as usize);
    }

    assert!(claim_poly == encoding_poly);
}

#[derive(Debug, Clone)]
pub struct RLPDecodeListGenerator<
    F: RichField + Extendable<D>,
    const D: usize,
    const ENCODING_LEN: usize,
    const LIST_LEN: usize,
    const ELEMENT_LEN: usize,
> {
    encoding: ArrayVariable<ByteVariable, ENCODING_LEN>,
    length: Variable,
    finish: BoolVariable,
    pub decoded_list: ArrayVariable<ArrayVariable<ByteVariable, ELEMENT_LEN>, LIST_LEN>,
    pub decoded_element_lens: ArrayVariable<Variable, LIST_LEN>,
    pub len_decoded_list: Variable,
    _phantom: PhantomData<F>,
}

impl<
        F: RichField + Extendable<D>,
        const D: usize,
        const ENCODING_LEN: usize,
        const LIST_LEN: usize,
        const ELEMENT_LEN: usize,
    > RLPDecodeListGenerator<F, D, ENCODING_LEN, LIST_LEN, ELEMENT_LEN>
{
    pub fn new(
        builder: &mut CircuitBuilder<F, D>,
        encoding: ArrayVariable<ByteVariable, ENCODING_LEN>,
        length: Variable,
        finish: BoolVariable,
    ) -> Self {
        let decoded_list =
            builder.init::<ArrayVariable<ArrayVariable<ByteVariable, ELEMENT_LEN>, LIST_LEN>>();
        let decoded_element_lens = builder.init::<ArrayVariable<Variable, LIST_LEN>>();
        let len_decoded_list = builder.init::<Variable>();
        Self {
            encoding,
            length,
            finish,
            decoded_list,
            decoded_element_lens,
            len_decoded_list,
            _phantom: PhantomData,
        }
    }

    pub fn verify_decoded_list(
        builder: &mut CircuitBuilder<F, D>,
        list: ArrayVariable<ArrayVariable<ByteVariable, 32>, LIST_LEN>,
        lens: ArrayVariable<ByteVariable, LIST_LEN>,
        encoding: ArrayVariable<ByteVariable, ENCODING_LEN>
    ) {
        let random = builder.constant::<Variable>(F::from_canonical_i64(1000));

        let mut size_accumulator = builder.constant::<Variable>(F::from_canonical_u32(0));
        let mut claim_poly = builder.constant::<Variable>(F::from_canonical_u32(0));

        let one = builder.constant::<Variable>(F::ONE);

        for i in 0..LIST_LEN {
            let (start_byte, list_len) = Self::parse_list_element(&mut builder, list[i], lens[i]);
            let size_accumulator_bits = builder.to_le_bits(size_accumulator);
            let rm_pow_sa = builder.exp_from_bits(random, size_accumulator_bits.iter());
            let mut poly = builder.mul(start_byte, rm_pow_sa);
            for j in 0..32 {
                let list_idx = list[i][j];

                let size_accum_1 = builder.add(size_accumulator, one);
                let j_variable = builder.constant(F::from_canonical_u8(j as u32));
                let size_accum1_j = builder.add(size_accum_1, j_variable);
                let size_accum_j1 = builder.to_le_bits(size_accum1_j);
                let rm_pow_sa_j1 = builder.exp_from_bits(random, size_accum_j1.iter());

                let j_leq_lst_len = Self::leq(&mut builder, j_variable, list_len);
                let res_j_leq_lst_len = Self::boolvar_to_var(&mut builder, j_leq_lst_len);

                let vals_to_mul = Vec::new();
                vals_to_mul.push(poly_list_inx);
                vals_to_mul.push(rm_pow_sa_j1);
                vals_to_mul.push(res_j_leq_lst_len);

                let temp_poly = builder.mul_many(&vals_to_mul[..]);
                poly = builder.add(poly, temp_poly);
            }
            let one_list_len = builder.add_const(list_len, one);
            size_accumulator = builder.add(size_accumulator, one_list_len);
            claim_poly = builder.add(claim_poly, poly);
        }

        let mut encoding_poly = builder.constant::<Variable>(F::from_canonical_u32(0));
        for i in 3..ENCODING_LEN {
            // TODO: don't hardcode 3 here "this is a note from the succintx team"
            let idx = i - 3;

            let curr_enc = encoding[i];
            let rndm_pow_idx = builder.exp_u64(random, idx as u64);

            let id_leq_sizeacc = Self::leq(&mut builder, idx, size_accumulator);
            let res_id_leq_sizeacc = boolvar_to_var(id_leq_sizeacc);

            let vals_to_mul = Vec::new();
            vals_to_mul.push(curr_enc);
            vals_to_mul.push(rndm_pow_idx);
            vals_to_mul.push(res_id_leq_sizeacc);

            let temp_encoding_poly = builder.mul_many(&vals_to_mul[..]);
            encoding_poly = builder.add(encoding_poly, temp_encoding_poly);
        }

        let clpol_eq_encpol = builder.assert_is_equal(claim_poly, encoding_poly);
    }

    fn parse_list_element(
        builder: &mut CircuitBuilder<F, D>,
        element: ArrayVariable<ByteVariable, 32>,
        len: ByteVariable
    ) -> (ByteVariable, ByteVariable) {
        let prefix = element[0];
        let zero = builder.constant::<Variable>(F::ZERO);
        let one = builder.constant::<Variable>(F::ONE);
        let _0x7f = builder.constant::<ByteVariable>(F::from_canonical_u8(0x7F));
        let _0x80 = builder.constant(F::from_canonical_u8(0x80));
        let _55 = builder.constant(F::from_canonical_u8(0x80));

        let len_eq_0 = builder.is_equal(len, zero);
        let len_eq_1 = builder.is_equal(len, one);
        let prx_leq_n = Self::leq(&mut builder, prefix, _0x7f);

        let _0x80_0 = BytesVariable::<2>::init(&mut builder);
        let prx_0 = BytesVariable::<2>::init(&mut builder);
        let _len_0x80 = builder.add(len, _0x80);
        let len_0x80 = BytesVariable::<2>::init(&mut builder);

        _0x80_0.0.copy_from_slice(&[_0x80, zero]);
        prx_0.0.copy_from_slice(&[prefix, zero]);
        len_0x80.0.copy_from_slice(&[_len_0x80, len]);

        let len_is_leq_55_pred = Self::leq(&mut builder, len, _55);
        builder.api.assert_bool(len_is_leq_55_pred);
        let res = builder.select(len_eq_0, _0x80_0,
            builder.select(builder.and(len_eq_1, prx_leq_n), prx_0, len_0x80
        ));

        (res[0], res[1])
    }

    pub fn boolvar_to_var(
        builder: &mut CircuitBuilder<F, D>,
        b: BoolVariable
    ) -> Variable {
        let one = builder.constant(F::ONE);
        let zero = builder.constant(F::ZERO);
        let res = builder.select(b, one, zero);

        res
    }

    pub fn leq(
        builder: &mut CircuitBuilder<F, D>,
        lhs: Variable,
        rhs: Variable
    ) -> Boolvariable {
        let mut lhs_vector = Vec::new();
        let mut rhs_vector = Vec::new();

        lhs_vector.push(lhs);
        rhs_vector.push(rhs);

        BoolVariable(list_le_circuit(&mut builder, lhs_vector, rhs_vector, 32)) // check num_bits value's truthfulness
    }
}

impl<
        F: RichField + Extendable<D>,
        const D: usize,
        const ENCODING_LEN: usize,
        const LIST_LEN: usize,
        const ELEMENT_LEN: usize,
    > SimpleGenerator<F, D> for RLPDecodeListGenerator<F, D, ENCODING_LEN, LIST_LEN, ELEMENT_LEN>
{
    fn id(&self) -> String {
        "RLPDecodeListGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut targets: Vec<Target> = Vec::new();
        targets.extend(self.encoding.targets());
        targets.extend(self.length.targets());
        targets.extend(self.finish.targets());
        targets
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let finish = self.finish.get(witness);
        let encoding = self.encoding.get(witness);
        let length = self.length.get(witness).as_canonical_u64() as usize;
        let (decoded_list, decoded_list_lens, len_decoded_list) =
            decode_element_as_list::<ENCODING_LEN, LIST_LEN, ELEMENT_LEN>(
                &encoding, length, finish,
            );
        self.decoded_list.set(out_buffer, decoded_list);
        self.decoded_element_lens.set(
            out_buffer,
            decoded_list_lens
                .iter()
                .map(|x| F::from_canonical_usize(*x))
                .collect(),
        );
        self.len_decoded_list
            .set(out_buffer, F::from_canonical_usize(len_decoded_list));
    }

    #[allow(unused_variables)]
    fn serialize(&self, dst: &mut Vec<u8>, common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        todo!()
    }

    #[allow(unused_variables)]
    fn deserialize(src: &mut Buffer, common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        todo!()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilder<F, D> {
    pub fn decode_element_as_list<
        const ENCODING_LEN: usize,
        const LIST_LEN: usize,
        const ELEMENT_LEN: usize,
    >(
        &mut self,
        encoded: ArrayVariable<ByteVariable, ENCODING_LEN>,
        len: Variable,
        finish: BoolVariable,
    ) -> (
        ArrayVariable<ArrayVariable<ByteVariable, ELEMENT_LEN>, LIST_LEN>,
        ArrayVariable<Variable, LIST_LEN>,
        Variable,
    ) {
        let generator = RLPDecodeListGenerator::new(self, encoded, len, finish);
        self.add_simple_generator(&generator);
        // TODO: here add verification logic constraints using `builder` to check that the decoded list is correct
        (
            generator.decoded_list,
            generator.decoded_element_lens,
            generator.len_decoded_list,
        )
    }
}

#[cfg(test)]
mod tests {

    use curta::math::field::Field;
    use plonky2::iop::generator::generate_partial_witness;

    use super::*;
    use crate::prelude::{
        CircuitBuilderX, GoldilocksField, PartialWitness, PoseidonGoldilocksConfig,
    };
    use crate::utils::bytes;

    #[test]
    fn test_decode_element_as_list() {
        const MAX_SIZE: usize = 17 * 32 + 20;
        let rlp_encoding: Vec<u8>  = bytes!("0xf90211a0c5becd7f8e5d47c1fe63ad9fa267d86fe0811bea0a4115aac7123b85fba2d662a03ab19202cb1de4f10fb0da8b5992c54af3dabb2312203f7477918df1393e24aea0b463eb71bcae8fa3183d0232b0d50e2400c21a0131bd48d918330e8683149b76a0d49a6c09224f74cef1286dad36a7f0e23e43e8ba4013fa386a3cda8903a3fe1ea06b6702bcfe04d3a135b786833b2748614d3aea00c728f86b2d1bbbb01b4e2311a08164a965258f9be5befcbf4de8e6cb4cd028689aad98e36ffc612b7255e4fa30a0b90309c6cb6383b2cb4cfeef9511004b705f1bca2c0556aadc2a5fe7ddf665e7a0749c3cee27e5ce85715122b76c18b7b945f1a19f507d5142445b42d50b2dd65aa0dbe35c115e9013b339743ebc2d9940158fb63b9e39f248b15ab74fade183c556a0a2b202f9b8003d73c7c84c8f7eb03298c064842382e57cecac1dfc2d5cabe2ffa02c5f8eba535bf5f18ca5aec74b51e46f219150886618c0301069dfb947006810a0dc01263a3b7c7942b5f0ac23931e0fda54fabaa3e6a58d2aca7ec65957cf8131a07d47344efa308df47f7e0e10491fa22d0564dbce634397c7748cd325fadd6b90a0cf9e45e08b8d60c68a86359adfa31c82883bb4a75b1d854392deb1f4499ba113a0081a664033eb00d5a69fc60f1f8b30e41eb643c5b9772d47301b602902b8d184a058b0bcf02a206cfa7b5f275ef09c97b4ae56abd8e9072f89dad8df1b98dfaa0280");
        let mut encoding_fixed_size = [0u8; MAX_SIZE];
        encoding_fixed_size[..rlp_encoding.len()].copy_from_slice(&rlp_encoding);

        let decoded_list = rlp_decode_list_2_or_17(&rlp_encoding);
        assert!(decoded_list.len() == 17);
        let element_lengths = decoded_list
            .iter()
            .map(|item| item.len() as u8)
            .collect::<Vec<u8>>();

        let mut decoded_list_fixed_size = [[0u8; 32]; 17];
        let mut element_lengths_fixed_size = [0u8; 17];
        for (i, item) in decoded_list.iter().enumerate() {
            let len = item.len();
            assert!(len <= 32, "The nested vector is longer than 32 bytes!");
            decoded_list_fixed_size[i][..len].copy_from_slice(item);
            element_lengths_fixed_size[i] = element_lengths[i] as u8;
        }

        // TODO: move below to a different test
        verify_decoded_list::<17, MAX_SIZE>(
            decoded_list_fixed_size,
            element_lengths_fixed_size,
            encoding_fixed_size,
        );
    }

    #[test]
    fn test_rlp_decode_list_generator() {
        type F = GoldilocksField;
        let mut builder: CircuitBuilder<GoldilocksField, 2> = CircuitBuilderX::new();
        const ENCODING_LEN: usize = 600;
        const LIST_LEN: usize = 17;
        const ELEMENT_LEN: usize = 34;
        let encoding = builder.init::<ArrayVariable<ByteVariable, ENCODING_LEN>>();
        let len = builder.init::<Variable>();
        let finish = builder.init::<BoolVariable>();

        let (decoded_list, decoded_element_lens, len_decoded_list) = builder
            .decode_element_as_list::<ENCODING_LEN, LIST_LEN, ELEMENT_LEN>(
                encoding.clone(),
                len,
                finish,
            );

        builder.watch(&len_decoded_list, "len_decoded_list");
        builder.watch(&decoded_element_lens, "decoded_element_lens");
        builder.watch(&decoded_list, "decoded_list");

        let circuit = builder.build::<PoseidonGoldilocksConfig>();

        let mut partial_witness = PartialWitness::new();
        let rlp_encoding: Vec<u8>  = bytes!("0xf90211a0215ead887d4da139eba306f76d765f5c4bfb03f6118ac1eb05eec3a92e1b0076a03eb28e7b61c689fae945b279f873cfdddf4e66db0be0efead563ea08bc4a269fa03025e2cce6f9c1ff09c8da516d938199c809a7f94dcd61211974aebdb85a4e56a0188d1100731419827900267bf4e6ea6d428fa5a67656e021485d1f6c89e69be6a0b281bb20061318a515afbdd02954740f069ebc75e700fde24dfbdf8c76d57119a0d8d77d917f5b7577e7e644bbc7a933632271a8daadd06a8e7e322f12dd828217a00f301190681b368db4308d1d1aa1794f85df08d4f4f646ecc4967c58fd9bd77ba0206598a4356dd50c70cfb1f0285bdb1402b7d65b61c851c095a7535bec230d5aa000959956c2148c82c207272af1ae129403d42e8173aedf44a190e85ee5fef8c3a0c88307e92c80a76e057e82755d9d67934ae040a6ec402bc156ad58dbcd2bcbc4a0e40a8e323d0b0b19d37ab6a3d110de577307c6f8efed15097dfb5551955fc770a02da2c6b12eedab6030b55d4f7df2fb52dab0ef4db292cb9b9789fa170256a11fa0d00e11cde7531fb79a315b4d81ea656b3b452fe3fe7e50af48a1ac7bf4aa6343a066625c0eb2f6609471f20857b97598ae4dfc197666ff72fe47b94e4124900683a0ace3aa5d35ba3ebbdc0abde8add5896876b25261717c0a415c92642c7889ec66a03a4931a67ae8ebc1eca9ffa711c16599b86d5286504182618d9c2da7b83f5ef780");
        let mut encoding_fixed_size = [0u8; ENCODING_LEN];
        encoding_fixed_size[..rlp_encoding.len()].copy_from_slice(&rlp_encoding);

        encoding.set(&mut partial_witness, encoding_fixed_size.to_vec());
        len.set(
            &mut partial_witness,
            F::from_canonical_usize(rlp_encoding.len()),
        );
        finish.set(&mut partial_witness, false);
        let prover_data = circuit.data.prover_only;
        let common_data = circuit.data.common;
        let witness = generate_partial_witness(partial_witness, &prover_data, &common_data);

        let len = len_decoded_list.get(&witness);
        let decoded_element_lens = decoded_element_lens.get(&witness);
        // let decoded_list = decoded_list.get(&witness);
        assert!(len == F::from_canonical_usize(17));
        for i in 0..17 {
            if i == 16 {
                assert!(decoded_element_lens[i] == F::from_canonical_usize(0));
            } else {
                assert!(decoded_element_lens[i] == F::from_canonical_usize(32));
            }
        }
    }
}
