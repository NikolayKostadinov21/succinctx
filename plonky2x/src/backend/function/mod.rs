mod cli;
mod io;

use std::fs::File;
use std::io::{Read, Write};

use clap::Parser;
use curta::math::prelude::PrimeField64;
use log::{info, warn};
use plonky2::field::extension::Extendable;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig};

use self::cli::{BuildArgs, ProveArgs};
use super::circuit::serialization::{GateRegistry, WitnessGeneratorRegistry};
use crate::backend::circuit::Circuit;
use crate::backend::function::cli::{Args, Commands};
use crate::backend::function::io::{FunctionInput, FunctionOutput, FunctionOutputGroth16};

pub trait CircuitFunction {
    /// Builds the circuit.
    fn build<F, C, const D: usize>() -> Circuit<F, C, D>
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F> + 'static,
        <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>;

    fn generators<F, C, const D: usize>() -> WitnessGeneratorRegistry<F, D>
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F> + 'static,
        <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
    {
        WitnessGeneratorRegistry::new::<C>()
    }

    fn gates<F: RichField + Extendable<D>, const D: usize>() -> GateRegistry<F, D> {
        GateRegistry::new()
    }

    /// Builds the circuit and saves it to disk.
    fn compile<F, C, const D: usize>(args: BuildArgs)
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F> + 'static,
        <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
    {
        info!("Building circuit...");
        let circuit = Self::build::<F, C, D>();
        info!("Successfully built circuit.");
        info!("> Circuit: {}", circuit.id());
        info!("> Degree: {}", circuit.data.common.degree());
        info!("> Number of Gates: {}", circuit.data.common.gates.len());
        let path = format!("{}/main.circuit", args.build_dir);
        circuit.save(&path, &Self::gates(), &Self::generators::<F, C, D>());
        info!("Successfully saved circuit to disk at {}.", path);

        info!("Building verifier contract...");
        let contract_path = format!("{}/FunctionVerifier.sol", args.build_dir);
        let mut contract_file = File::create(&contract_path).unwrap();
        let contract = "pragma solidity ^0.8.16;

interface IFunctionVerifier {
    function verify(bytes32 _inputHash, bytes32 _outputHash, bytes memory _proof) external view returns (bool);

    function verificationKeyHash() external pure returns (bytes32);
}

contract FunctionVerifier is IFunctionVerifier {
    function verify(bytes32, bytes32, bytes memory) external pure returns (bool) {
        return true;
    }

    function verificationKeyHash() external pure returns (bytes32) {
        return keccak256(\"\");
    }
}
";
        contract_file.write_all(contract.as_bytes()).unwrap();
        info!(
            "Successfully saved verifier contract to disk at {}.",
            contract_path
        );
    }

    /// Generates a proof with evm-based inputs and outputs.
    /// type Groth16Proof struct {
    //     A      [2]*big.Int    `json:"a"`
    //     B      [2][2]*big.Int `json:"b"`
    //     C      [2]*big.Int    `json:"c"`
    //     Input  hexutil.Bytes  `json:"input"`
    //     Output hexutil.Bytes  `json:"output"`
    // }

    fn prove_with_evm_io<F, C, const D: usize>(args: ProveArgs, bytes: Vec<u8>)
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F> + 'static,
        <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
    {
        let path = format!("{}/main.circuit", args.build_dir);
        info!("Loading circuit from {}...", path);
        let circuit =
            Circuit::<F, C, D>::load(&path, &Self::gates(), &Self::generators::<F, C, D>())
                .unwrap();
        info!("Successfully loaded circuit.");

        let mut input = circuit.input();
        input.evm_write_all(&bytes);

        info!("Generating proof...");
        let (proof, output) = circuit.prove(&input);
        info!("Proof generated.");
        circuit.verify(&proof, &input, &output);
        info!("Proof verified.");
        let output_bytes = output.evm_read_all();

        let function_output = FunctionOutput {
            bytes: Some(hex::encode(output_bytes.clone())),
            elements: None,
            proof: hex::encode(proof.to_bytes()),
        };
        let json = serde_json::to_string_pretty(&function_output).unwrap();
        let mut file = File::create("plonky2_output.json").unwrap();
        file.write_all(json.as_bytes()).unwrap();
        info!(
            "Succesfully wrote output of {} bytes and proof to plonky2_output.json.",
            output_bytes.len()
        );

        let input_hex_string = format!("0x{}", hex::encode(bytes.clone()));
        let output_hex_string = format!("0x{}", hex::encode(output_bytes.clone()));
        let dummy_groth16_proof = FunctionOutputGroth16 {
            a: [0, 0],
            b: [[0, 0], [0, 0]],
            c: [0, 0],
            input: input_hex_string,
            output: output_hex_string,
        };
        let json = serde_json::to_string_pretty(&dummy_groth16_proof).unwrap();
        let mut file = File::create("output.json").unwrap();
        file.write_all(json.as_bytes()).unwrap();
        info!("Succesfully wrote dummy proof to output.json.");
    }

    /// Generates a proof with field-based inputs and outputs.
    fn prove_with_field_io<F, C, const D: usize>(args: ProveArgs, elements: Vec<F>)
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F> + 'static,
        <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
    {
        let path = format!("{}/main.circuit", args.build_dir);
        info!("Loading circuit from {}...", path);
        let circuit =
            Circuit::<F, C, D>::load(&path, &Self::gates(), &Self::generators::<F, C, D>())
                .unwrap();
        info!("Successfully loaded circuit.");

        let mut input = circuit.input();
        input.write_all(&elements);

        info!("Generating proof...");
        let (proof, output) = circuit.prove(&input);
        info!("Proof generated.");
        circuit.verify(&proof, &input, &output);
        info!("Proof verified.");
        let output_elements = output.read_all();

        let function_output = FunctionOutput {
            bytes: None,
            elements: Some(
                output_elements
                    .iter()
                    .map(|e| e.as_canonical_u64())
                    .collect(),
            ),
            proof: hex::encode(proof.to_bytes()),
        };
        let json = serde_json::to_string_pretty(&function_output).unwrap();
        let mut file = File::create("output.json").unwrap();
        file.write_all(json.as_bytes()).unwrap();
        info!(
            "Succesfully wrote output of {} elements and proof to output.json.",
            output_elements.len()
        );
    }

    /// Reads the function input from a JSON file path.
    fn read_function_input(input_json: String) -> FunctionInput {
        let mut file = File::open(input_json).unwrap();
        let mut data = String::new();
        file.read_to_string(&mut data).unwrap();
        serde_json::from_str(&data).unwrap()
    }

    /// The entry point for the function when using CLI-based tools.
    fn cli() {
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;

        let args = Args::parse();
        match args.command {
            Commands::Build(args) => {
                Self::compile::<F, C, D>(args);
            }
            Commands::Prove(args) => {
                let input = Self::read_function_input(args.clone().input_json);
                if input.bytes.is_some() {
                    Self::prove_with_evm_io::<F, C, D>(args, input.bytes());
                } else if input.elements.is_some() {
                    Self::prove_with_field_io::<F, C, D>(args, input.elements());
                } else {
                    warn!("No input bytes or elements found in input.json.");
                }
            }
        }
    }

    fn test<F, C, const D: usize>(input_json: String)
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F> + 'static,
        <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
    {
        let build_args = BuildArgs {
            build_dir: "./build".to_string(),
        };
        Self::compile::<F, C, D>(build_args);
        let prove_args = ProveArgs {
            build_dir: "./build".to_string(),
            input_json: input_json.clone(),
        };
        let input = Self::read_function_input(input_json);
        if input.bytes.is_some() {
            Self::prove_with_evm_io::<F, C, D>(prove_args, input.bytes());
        } else if input.elements.is_some() {
            Self::prove_with_field_io::<F, C, D>(prove_args, input.elements());
        } else {
            panic!("No input bytes or field elements found in input.json.")
        }
    }
}
