use core::fmt::Debug;
use core::marker::PhantomData;

use ethers::providers::{JsonRpcClient, Middleware, Provider};
use ethers::types::EIP1186ProofResponse;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::Target;
use plonky2::iop::witness::PartitionWitness;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::util::serialization::{Buffer, IoResult};
use tokio::runtime::Runtime;

use super::super::vars::{EthAccountVariable, EthProofVariable};
use crate::frontend::builder::CircuitBuilder;
use crate::frontend::eth::utils::u256_to_h256_be;
use crate::frontend::eth::vars::AddressVariable;
use crate::frontend::vars::{Bytes32Variable, CircuitVariable};
use crate::utils::eth::get_provider;

#[derive(Debug, Clone)]
pub struct EthStorageProofGenerator<F: RichField + Extendable<D>, const D: usize> {
    address: AddressVariable,
    storage_key: Bytes32Variable,
    block_hash: Bytes32Variable,
    pub value: Bytes32Variable,
    chain_id: u64,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> EthStorageProofGenerator<F, D> {
    pub fn new(
        builder: &mut CircuitBuilder<F, D>,
        address: AddressVariable,
        storage_key: Bytes32Variable,
        block_hash: Bytes32Variable,
    ) -> EthStorageProofGenerator<F, D> {
        let chain_id = builder.get_chain_id();
        let value = builder.init::<Bytes32Variable>();
        EthStorageProofGenerator {
            address,
            storage_key,
            block_hash,
            value,
            chain_id,
            _phantom: PhantomData::<F>,
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for EthStorageProofGenerator<F, D>
{
    fn id(&self) -> String {
        "GetStorageProofGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut targets = Vec::new();
        targets.extend(self.address.targets());
        targets.extend(self.storage_key.targets());
        targets.extend(self.block_hash.targets());
        targets
    }

    fn run_once(&self, witness: &PartitionWitness<F>, buffer: &mut GeneratedValues<F>) {
        let address = self.address.get(witness);
        let location = self.storage_key.get(witness);
        let block_hash = self.block_hash.get(witness);
        let provider = get_provider(self.chain_id);
        let rt = Runtime::new().expect("failed to create tokio runtime");
        let result: EIP1186ProofResponse = rt.block_on(async {
            provider
                .get_proof(address, vec![location], Some(block_hash.into()))
                .await
                .expect("Failed to get proof")
        });
        let value = u256_to_h256_be(result.storage_proof[0].value);
        self.value.set(buffer, value);
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
