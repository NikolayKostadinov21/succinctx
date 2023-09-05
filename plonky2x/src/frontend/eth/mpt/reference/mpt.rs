use std::fs::File;
use std::io::Read;

use ethers::providers::{Http, Middleware, Middleware, Provider, Provider};
use ethers::types::{
    Address, Bytes, Bytes, EIP1186ProofResponse, EIP1186ProofResponse, H256, H256,
};
use ethers::utils::keccak256;
use num_bigint::{BigInt, RandBigInt, RandBigInt, ToBigInt, ToBigInt};

use crate::eth::mpt::utils::rlp_decode_list_2_or_17;
use crate::utils::{address, bytes, bytes, bytes32, bytes32, hex, hex};

const TREE_RADIX: usize = 16;
const BRANCH_NODE_LENGTH: usize = 17;
const LEAF_OR_EXTENSION_NODE_LENGTH: usize = 2;
const PREFIX_EXTENSION_EVEN: usize = 0;
const PREFIX_EXTENSION_ODD: usize = 1;
const PREFIX_LEAF_EVEN: usize = 2;
const PREFIX_LEAF_ODD: usize = 3;

// Based off of the following Solidity implementation:
// https://github.com/ethereum-optimism/optimism/blob/6e041bcd9d678a0ea2bb92cfddf9716f8ae2336c/packages/contracts-bedrock/src/libraries/trie/MerkleTrie.sol
pub fn get(key: H256, proof: Vec<Vec<u8>>, root: H256) -> Vec<u8> {
    let mut current_key_index = 0;
    let mut current_node_id = root.to_fixed_bytes().to_vec();

    let hash_key = keccak256(key.to_fixed_bytes().as_slice());
    let _ = key; // Move key so that we cannot mistakely use it again
    let key_path = to_nibbles(&hash_key[..]);
    let mut finish = false;

    for i in 0..proof.len() {
        println!("i {}", i);
        let current_node = &proof[i];

        if current_key_index == 0 {
            let hash = keccak256(current_node);
            assert_bytes_equal(&hash[..], &current_node_id);
        } else if current_node.len() >= 32 {
            println!("current node length {:?}", current_node.len());
            let hash = keccak256(current_node);
            assert_bytes_equal(&hash[..], &current_node_id);
        } else {
            println!(
                "current_node {:?}",
                Bytes::from(current_node.to_vec()).to_string()
            );
            assert_bytes_equal(current_node, &current_node_id);
        }

        let decoded = rlp_decode_list_2_or_17(current_node);
        match decoded.len() {
            BRANCH_NODE_LENGTH => {
                if current_key_index == key_path.len() {
                    // We have traversed all nibbles of the key, so we return the value in the branch node
                    finish = true;
                    current_node_id = decoded[TREE_RADIX].clone();
                } else {
                    let branch_key = key_path[current_key_index];
                    current_node_id = decoded[usize::from(branch_key)].clone();
                    current_key_index += 1;
                }
            }
            LEAF_OR_EXTENSION_NODE_LENGTH => {
                current_node_id = decoded[1].clone().clone();
                let path = to_nibbles(&decoded[0]);
                let prefix = path[0];
                match usize::from(prefix) {
                    PREFIX_LEAF_EVEN | PREFIX_LEAF_ODD => {
                        // TODO there are some other checks here around length of the return value and also the path matching the key
                        finish = true;
                    }
                    PREFIX_EXTENSION_EVEN => {
                        // If prefix_extension_even, then the offset for the path is 2
                        let path_remainder = &path[2..];
                        assert_bytes_equal(
                            path_remainder,
                            &key_path[current_key_index..current_key_index + path_remainder.len()],
                        );
                        println!("path_remainder {:?}", path_remainder.len());
                        current_key_index += path_remainder.len();
                    }
                    PREFIX_EXTENSION_ODD => {
                        // If prefix_extension_odd, then the offset for the path is 1
                        let path_remainder = &path[1..];
                        assert_bytes_equal(
                            path_remainder,
                            &key_path[current_key_index..current_key_index + path_remainder.len()],
                        );
                        current_key_index += path_remainder.len();
                    }
                    _ => panic!("Invalid prefix for leaf or extension node"),
                }
            }
            _ => {
                panic!("Invalid decoded length");
            }
        }

        println!("decoded {:?}", decoded);
        println!("current_key_idx {:?}", current_key_index);
        println!("current node id at end of loop {:?}", current_node_id);

        if finish {
            println!("Finished");
            return rlp_decode_bytes(&current_node_id[..]).0;
        }
    }

    panic!("Invalid proof");
}

pub fn get_proof_witnesses<const M: usize, const P: usize>(
    storage_proof: Vec<Vec<u8>>,
) -> ([[u8; M]; P], [u32; P]) {
    if storage_proof.len() > P {
        panic!("Outer vector has incorrect length")
    }

    let mut result: [[u8; M]; P] = [[0u8; M]; P];
    let mut lengths: [u32; P] = [0u32; P];

    for (i, inner_vec) in storage_proof.into_iter().enumerate() {
        // Check inner length
        if inner_vec.len() > M {
            println!("{:?} {}", inner_vec, inner_vec.len());
            panic!("Inner vector has incorrect length");
        }
        lengths[i] = inner_vec.len() as u32;

        let mut array: [u8; M] = [0u8; M];
        // Copy the inner vec to the array
        for (j, &byte) in inner_vec.iter().enumerate() {
            array[j] = byte;
        }
        result[i] = array;
    }

    (result, lengths)
}

const TREE_RADIX: usize = 16;
const BRANCH_NODE_LENGTH: usize = 17;
const LEAF_OR_EXTENSION_NODE_LENGTH: usize = 2;
const PREFIX_EXTENSION_EVEN: usize = 0;
const PREFIX_EXTENSION_ODD: usize = 1;
const PREFIX_LEAF_EVEN: usize = 2;
const PREFIX_LEAF_ODD: usize = 3;

pub fn verified_get<const L: usize, const M: usize, const P: usize>(
    key: [u8; 32],
    proof: [[u8; M]; P],
    root: [u8; 32],
    value: [u8; 32],
    len_nodes: [u32; P],
) {
    const MAX_NODE_SIZE: usize = 34;

    let mut current_key_idx: u32 = 0;
    let mut current_node_id = [0u8; MAX_NODE_SIZE];
    for i in 0..32 {
        current_node_id[i] = root[i];
    }
    let hash_key = keccak256(key);
    let key_path = to_sized_nibbles(hash_key);
    let mut finish: u32 = 0;
    let mut current_node = proof[0];
    for i in 0..P {
        println!("i: {}", i);
        current_node = proof[i];
        let current_node_hash = keccack_variable(current_node, len_nodes[i]);
        println!(
            "current_node_hash {:?}",
            H256::from_slice(&current_node_hash)
        );
        if (i == 0) {
            let is_eq = is_bytes32_eq(current_node_hash, root);
            assert!(is_eq == 1);
        } else {
            let first_32_byte_eq = is_bytes32_eq(
                current_node[0..32].try_into().unwrap(),
                current_node_id[0..32].try_into().unwrap(),
            );
            // println!("first_32_byte_eq: {}", first_32_byte_eq);
            let hash_eq = is_bytes32_eq(
                current_node_hash,
                current_node_id[0..32].try_into().unwrap(),
            );
            // println!("hash_eq: {}", hash_eq);
            // println!("{:?} {:?}", current_node_hash, current_node_id);
            let equality_fulfilled = is_leq(len_nodes[i], 32) * first_32_byte_eq as u32
                + (1 - is_leq(len_nodes[i], 32)) * hash_eq as u32;
            // assert equality == 1 OR finish == 1
            assert!((equality_fulfilled as i32 - 1) * (1 - finish as i32) == 0);
        }
        println!("Round {} current_node {:?}", i, current_node);
        println!("Round {} len_nodes[i] {:?}", i, len_nodes[i]);
        let (decoded, decoded_lens, witness_list_len) =
            witness_decoding::<M, L>(current_node, len_nodes[i], finish);
        // TODO: verify_decoded_list(witness_decoded_list, witness_decoded_lens, current_node, witness_list_len, len_nodes[i]);
        println!("Round {} decoded_list_len {:?}", i, witness_list_len);
        println!("Round {} decoded_element_lens {:?}", i, decoded_lens);

        let is_branch = is_eq(witness_list_len, BRANCH_NODE_LENGTH);
        let is_leaf = is_eq(witness_list_len, LEAF_OR_EXTENSION_NODE_LENGTH);
        let key_terminated = is_eq(current_key_idx as u8, 64);
        let path = to_nibbles(decoded[0]);
        let prefix = path[0];
        let prefix_leaf_even = is_eq(prefix, PREFIX_LEAF_EVEN);
        let prefix_leaf_odd = is_eq(prefix, PREFIX_LEAF_ODD);
        let prefix_extension_even = is_eq(prefix, PREFIX_EXTENSION_EVEN);
        let prefix_extension_odd = is_eq(prefix, PREFIX_EXTENSION_ODD);
        let offset = 2 * (prefix_extension_even as u32) + 1 * prefix_extension_odd as u32;

        let branch_key = mux(key_path, current_key_idx as u8);
        if (1 - finish) * is_branch * key_terminated == 1 {
            current_node_id = decoded[TREE_RADIX];
        } else if (1 - finish) * is_branch * (1 - key_terminated) == 1 {
            current_node_id = mux_nested(decoded, branch_key);
        } else if (1 - finish) * is_leaf == 1 {
            current_node_id = decoded[1];
        } else {
            // If finish = 1, all bets are off
            if (finish == 0) {
                panic!("Should not happen")
            }
        }

        println!("decoded {:?}", decoded);
        // The reason that we multiply decoded_lens[i] * 2 is because path and key path are both in nibbles

        // Only do the path remainder check if not finished AND is_leaf AND OR(prefix_extension_even, prefix_extension_odd)
        let do_path_remainder_check = (1 - finish)
            * is_leaf
            * (1 - prefix_leaf_even)
            * (1 - prefix_leaf_odd)
            * (prefix_extension_even + prefix_extension_odd
                - prefix_extension_even * prefix_extension_odd);
        let check_length = do_path_remainder_check
            * (decoded_lens[0] as u32 * 2 - offset * do_path_remainder_check);

        rlc_subarray_equal(
            path,
            offset,
            key_path,
            current_key_idx.into(),
            check_length as u8,
        );

        println!("is_leaf {}", is_leaf);
        println!("decoded_lens[0] {} offset {}", decoded_lens[0], offset);
        current_key_idx += is_branch * (1 - key_terminated) * 1 + is_leaf * check_length;

        // update finish
        if finish == 0 {
            // Can only toggle finish if it's false
            println!("finished {}", finish);
            finish =
                is_branch * key_terminated + is_leaf * prefix_leaf_even + is_leaf * prefix_leaf_odd;
        }
        // TODO other checks around the paths matching
        println!("current key idx {:?}", current_key_idx);
        println!("current node id at end of loop {:?}", current_node_id);
    }

    // At the end, assert that
    // current_node_id = rlp(value)
    println!("current_node_id {:?}", current_node_id);
    println!("value {:?}", value);

    let current_node_len = current_node_id[0] - 0x80;
    rlc_subarray_equal(
        value,
        32 - current_node_len as u32,
        current_node_id,
        1,
        current_node_len,
    );
}

#[cfg(test)]
mod tests {
    use core::ops::Add;

    use anyhow::Result;
    use ethers::prelude::k256::elliptic_curve::rand_core::block;
    use ethers::prelude::verify;
    use ethers::types::{
        Address, Address, Bytes, Bytes, EIP1186ProofResponse, EIP1186ProofResponse, H256, H256,
        U256, U256,
    };
    use ethers::utils::keccak256;
    use ethers::utils::rlp::RlpStream;
    use plonky2::iop::witness::{PartialWitness, PartialWitness, WitnessWrite, WitnessWrite};
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{
        GenericConfig, GenericConfig, PoseidonGoldilocksConfig, PoseidonGoldilocksConfig,
    };
    use subtle_encoding::hex::decode;
    use tokio::runtime::Runtime;

    use super::*;
    use crate::eth::mpt::utils::rlp_decode_list_2_or_17;
    use crate::eth::storage;
    use crate::eth::utils::{h256_to_u256_be, h256_to_u256_be, u256_to_h256_be, u256_to_h256_be};

    fn generate_fixtures() {
        // TODO: don't have mainnet RPC url here, read from a .env
        let rpc_url = "https://eth-mainnet.g.alchemy.com/v2/hIxcf_hqT9It2hS8iCFeHKklL8tNyXNF";
        let provider = Provider::<Http>::try_from(rpc_url).unwrap();

        let block_number = 17880427u64;
        let state_root =
            bytes32!("0xff90251f501c864f21d696c811af4c3aa987006916bd0e31a6c06cc612e7632e");
        let address = address!("0x55032650b14df07b85bF18A3a3eC8E0Af2e028d5");
        let location =
            bytes32!("0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5");

        let get_proof_closure = || -> EIP1186ProofResponse {
            let rt = Runtime::new().unwrap();
            rt.block_on(async {
                provider
                    .get_proof(address, vec![location], Some(block_number.into()))
                    .await
                    .unwrap()
            })
        };
        let storage_result: EIP1186ProofResponse = get_proof_closure();
        let serialized = serde_json::to_string(&storage_result).unwrap();
        println!("{}", serialized);
        // TODO: save this to fixtures/example.json programatically instead of copy-paste
    }

    fn read_fixture(filename: str) -> EIP1186ProofResponse {
        let mut file = File::open(filename).unwrap();
        let mut context = String::new();
        file.read_to_string(&mut context).unwrap();

        let context: EIP1186ProofResponse = serde_json::from_str(context.as_str()).unwrap();
        context
    }

    #[test]
    fn test_rlp_vanilla() {
        let storage_result: EIP1186ProofResponse =
            read_fixture("./src/eth/mpt/fixtures/example.json");

        let proof = storage_result.storage_proof[0]
            .proof
            .iter()
            .map(|b| b.to_vec())
            .collect::<Vec<Vec<u8>>>();
        println!(
            "Storage proof first element {:?}",
            storage_result.storage_proof[0].proof[0].to_string()
        );
        let k = keccak256::<Vec<u8>>(storage_result.storage_proof[0].proof[0].to_vec()).to_vec();
        println!(
            "keccack256 of first element {:?}",
            Bytes::from(k).to_string()
        );
        println!("storage hash {:?}", storage_result.storage_hash.to_string());
        let value = get(
            storage_result.storage_proof[0].key,
            proof,
            storage_result.storage_hash,
        );
        println!("recovered value {:?}", Bytes::from(value).to_string());
        // TODO have to left pad the recovered value to 32 bytes
        // println!("recovered value h256 {:?}", H256::from_slice(&value));
        println!(
            "true value {:?}",
            u256_to_h256_be(storage_result.storage_proof[0].value)
        );
        // TODO: make this a real test with assert

        // TODO: for some reason this doesn't work...not sure why
        // let account_key = keccak256(address.as_bytes());
        // let account_proof = storage_result.account_proof.iter().map(|b| b.to_vec()).collect::<Vec<Vec<u8>>>();
        // let account_value = get(account_key.into(), account_proof, state_root);
        // println!("account value {:?}", Bytes::from(account_value).to_string());
    }

    #[test]
    fn test_verify_decoded_list() {
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
            decoded_list_fixed_size[i][..len].copy_from_slice(&item);
            element_lengths_fixed_size[i] = element_lengths[i] as u8;
        }

        verify_decoded_list::<17, MAX_SIZE>(
            decoded_list_fixed_size,
            element_lengths_fixed_size,
            encoding_fixed_size,
        );
    }

    #[test]
    fn test_verified_get() {
        let rpc_url = "https://eth-mainnet.g.alchemy.com/v2/hIxcf_hqT9It2hS8iCFeHKklL8tNyXNF";
        let provider = Provider::<Http>::try_from(rpc_url).unwrap();

        let block_number = 17880427u64;
        let state_root =
            bytes32!("0xff90251f501c864f21d696c811af4c3aa987006916bd0e31a6c06cc612e7632e");
        let address = address!("0x55032650b14df07b85bF18A3a3eC8E0Af2e028d5");
        let location =
            bytes32!("0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5");

        // Nouns contract
        // let address = address!("0x9c8ff314c9bc7f6e59a9d9225fb22946427edc03");
        // let location = bytes32!("0x0000000000000000000000000000000000000000000000000000000000000003");

        // let get_proof_closure = || -> EIP1186ProofResponse {
        //     let rt = Runtime::new().unwrap();
        //     rt.block_on(async {
        //         provider
        //             .get_proof(address, vec![location], Some(block_number.into()))
        //             .await
        //             .unwrap()
        //     })
        // };
        // let storage_result: EIP1186ProofResponse = get_proof_closure();

        let mut file = File::open("./src/eth/mpt/example.json").unwrap();
        let mut context = String::new();
        file.read_to_string(&mut context).unwrap();
        let storage_result: EIP1186ProofResponse = serde_json::from_str(context.as_str()).unwrap();

        let storage_proof = storage_result.storage_proof[0]
            .proof
            .iter()
            .map(|b| b.to_vec())
            .collect::<Vec<Vec<u8>>>();
        let root = storage_result.storage_hash;
        let key = storage_result.storage_proof[0].key;
        let value = storage_result.storage_proof[0].value;

        println!("root {:?} key {:?} value {:?}", root, key, value);

        let value_as_h256 = u256_to_h256_be(value);
        let (proof_as_fixed, lengths_as_fixed) = get_proof_witnesses::<600, 16>(storage_proof);
        // 17 = max length of RLP decoding of proof element as list
        // 600 = max length of proof element as bytes
        // 16 = max number of elements in proof
        verified_get::<17, 600, 16>(
            key.to_fixed_bytes(),
            proof_as_fixed,
            root.to_fixed_bytes(),
            value_as_h256.to_fixed_bytes(),
            lengths_as_fixed,
        );

        // Now test verified get for account proof
    }
}