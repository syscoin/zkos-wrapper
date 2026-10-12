use std::mem::MaybeUninit;

use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::u32::UInt32;
use circuit_mersenne_field::extension_trait::CircuitFieldExpression;
use circuit_mersenne_field::{MersenneComplex, MersenneField, MersenneQuartic};

use crate::risc_verifier;
use risc_verifier::blake2s_u32::*;
use risc_verifier::concrete::size_constants::*;
// use risc_verifier::concrete::skeleton_instance::BASE_CIRCUIT_QUERY_VALUES_NO_PADDING_U32_WORDS;
use risc_verifier::concrete::skeleton_instance::ProofSkeletonInstance;
use risc_verifier::concrete::skeleton_instance::QueryValuesInstance;
use risc_verifier::field::*;
use risc_verifier::prover::cs::definitions::*;
use risc_verifier::skeleton::{ProofSkeleton, QueryValues};
use risc_verifier::verifier_common;
use risc_verifier::verifier_common::non_determinism_source::NonDeterminismSource;
use risc_verifier::verifier_common::{
    SizedProofPowChallenges, SizedProofSecurityConfig, transcript_challenge_array_size,
};

use crate::active_security::ActiveSecurity;
use crate::wrapper_utils::prover_structs::*;

pub(crate) mod imports;
pub mod skeleton;

pub use crate::transcript::*;
use crate::wrapper_utils::verifier_traits::*;
use skeleton::*;

// Airbender now exposes verifier geometry through a security marker. The wrapper
// still compiles one security model at a time, so the shared verifier code can
// keep using concrete constants selected by the active Cargo feature.
type AirbenderProofSkeletonInstance = ProofSkeletonInstance<ActiveSecurity>;
type AirbenderQueryValuesInstance = QueryValuesInstance<ActiveSecurity>;
type ActiveGeometry = Geometry<ActiveSecurity>;

const SECURITY_CONFIG: SizedProofSecurityConfig<NUM_FRI_STEPS> = ActiveGeometry::SECURITY_CONFIG;
pub(crate) const NUM_QUERIES: usize = ActiveGeometry::NUM_QUERIES;
const NUM_QUERY_VALUES: usize = ActiveGeometry::NUM_QUERY_VALUES;
const NUM_REQUIRED_WORDS_FOR_QUERY_INDEXES: usize =
    ActiveGeometry::NUM_REQUIRED_WORDS_FOR_QUERY_INDEXES;
const LAST_FRI_STEP_EXPOSE_LEAFS: bool = ActiveGeometry::LAST_FRI_STEP_EXPOSE_LEAFS;
const LAST_FRI_STEP_LEAFS_TOTAL_SIZE_PER_COSET: usize =
    ActiveGeometry::LAST_FRI_STEP_LEAFS_TOTAL_SIZE_PER_COSET;
const NUM_FRI_STEPS_WITH_ORACLES: usize = ActiveGeometry::NUM_FRI_STEPS_WITH_ORACLES;
const TOTAL_FRI_ORACLES_PATHS_LENGTH: usize = ActiveGeometry::TOTAL_FRI_ORACLES_PATHS_LENGTH;
const TOTAL_FRI_LEAFS_SIZES: usize = ActiveGeometry::TOTAL_FRI_LEAFS_SIZES;

include!("../shared/verify_impl.rs");

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn degree_lift_challenge_geometry_matches_airbender() {
        assert_eq!(
            ActiveGeometry::DEEP_POLY_TRANSCRIPT_CHALLENGE_ARRAY_SIZE,
            transcript_challenge_array_size(
                2 * 4,
                SECURITY_CONFIG.deep_poly_alpha_pow_bits as usize,
            )
        );
    }

    #[test]
    fn degree_lift_uses_full_quartic_offset() {
        use std::alloc::Global;

        use boojum::config::DevCSConfig;
        use boojum::cs::cs_builder::new_builder;
        use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
        use boojum::cs::gates::{
            ConstantsAllocatorGate, DotProductGate, FmaGateInBaseFieldWithoutConstant, NopGate,
            ReductionGate, SelectionGate, UIntXAddGate,
        };
        use boojum::cs::traits::gate::GatePlacementStrategy;
        use boojum::cs::{CSGeometry, LookupParameters};
        use boojum::field::goldilocks::GoldilocksField;
        use boojum::gadgets::tables::range_check_16_bits::{
            RangeCheck15BitsTable, RangeCheck16BitsTable, create_range_check_15_bits_table,
            create_range_check_16_bits_table,
        };
        use boojum::gadgets::traits::witnessable::WitnessHookable;
        use boojum::worker::Worker;
        use risc_verifier::field::{
            Field, FieldExtension, Mersenne31Complex, Mersenne31Field, Mersenne31Quartic,
        };

        type F = GoldilocksField;
        let field = Mersenne31Field::new;
        let source =
            Mersenne31Quartic::from_array_of_base([field(2), field(3), field(5), field(7)]);
        let offset =
            Mersenne31Quartic::from_array_of_base([field(11), field(13), field(17), field(19)]);
        let point = Mersenne31Complex {
            c0: field(23),
            c1: field(29),
        };

        let mut factor = offset;
        factor.add_assign_base(&point);
        let mut expected = source;
        expected.mul_assign(&factor);
        let mut base_only = source;
        base_only.mul_assign_by_base(&point);
        assert_ne!(expected, base_only);

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 60,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 18);
        let builder = new_builder::<_, F>(builder_impl).allow_lookup(
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width: 1,
                num_repetitions: 10,
                share_table_id: true,
            },
        );
        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = DotProductGate::<4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = UIntXAddGate::<16>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = SelectionGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);
        let builder = ReductionGate::<F, 2>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 3>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );

        let mut owned_cs = builder.build(boojum::dag::CircuitResolverOpts::new(1 << 20));
        owned_cs
            .add_lookup_table::<RangeCheck16BitsTable<1>, 1>(create_range_check_16_bits_table());
        owned_cs
            .add_lookup_table::<RangeCheck15BitsTable<1>, 1>(create_range_check_15_bits_table());

        let cs = &mut owned_cs;
        let source = MersenneQuartic::<F>::allocate_checked(cs, source, false);
        let offset = MersenneQuartic::<F>::allocate_checked(cs, offset, false);
        let point = MersenneComplex::<F>::allocate_checked(cs, point, false);
        let result = lift_deep_expected_value(cs, source, point, offset);
        assert_eq!(result.witness_hook(&*cs)().unwrap(), expected);

        owned_cs.pad_and_shrink();
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        assert!(owned_cs.check_if_satisfied(&Worker::new_with_num_threads(2)));
    }
}
