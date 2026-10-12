use super::*;

#[test]
fn compression_row_budget_matches_security_level() {
    let circuit = crate::circuits::CompressionCircuit::new(None, crate::RiscWrapperVK::default());
    #[cfg(feature = "security_80")]
    assert_eq!(circuit.size_hint(), (Some(1 << 16), Some(1 << 24)));
    #[cfg(feature = "security_100")]
    assert_eq!(circuit.size_hint(), (Some(1 << 17), Some(1 << 24)));
}

#[cfg(feature = "security_100")]
#[test]
fn compression_row_budget_fits_current_risc_vk() {
    use crate::circuits::CompressionCircuit;
    use boojum::{
        config::SetupCSConfig,
        cs::{
            cs_builder::new_builder, cs_builder_reference::CsReferenceImplementationBuilder,
            traits::circuit::CircuitBuilder,
        },
    };
    // Public sizing fixture retained from the first current-code keygen, which
    // stopped during compression synthesis. This is not a release-accepted VK.
    // SHA256: 52c41727ee5e90d4f140c846bf5f21e30c100f8ab8c8ccced66e4008edb7c2f6.
    let vk: crate::RiscWrapperVK = serde_json::from_str(include_str!(
        "fixtures/risc-wrapper-security100-sizing.json"
    ))
    .unwrap();
    assert_eq!(vk.fixed_parameters.domain_size, 1 << 20);
    let circuit = CompressionCircuit::new(None, vk);
    let geometry = CompressionCircuit::geometry();
    let (max_rows, max_variables) = circuit.size_hint();
    let max_rows = max_rows.unwrap();
    assert_eq!(max_rows, 1 << 17);
    let builder_impl =
        CsReferenceImplementationBuilder::<F, F, SetupCSConfig, StCircuitResolver<_, _>>::new(
            geometry, max_rows,
        );
    let builder = new_builder::<_, F>(builder_impl);
    let builder = CompressionCircuit::configure_builder(builder);
    let mut cs = builder.build(max_variables.unwrap());
    circuit.synthesize_into_cs(&mut cs);
    assert!(cs.next_available_row() < max_rows);
    let (padded_rows, finalization_hint) = cs.pad_and_shrink();
    assert_eq!(padded_rows, finalization_hint.final_trace_len);
    assert!(padded_rows <= max_rows);
    // The reviewed common-crypto overlay uses 65,538 GP rows / 65,539 with the
    // copy-permutation reserve, padded to 2^17. Do not require that exact count:
    // the wrapper's unpatched upstream common-crypto dependency has fewer gates.
    // This test only synthesizes and pads; it never derives a setup or proof.
}

#[test]
pub(crate) fn compression_full_test() {
    let worker = boojum::worker::Worker::new();

    let risc_wrapper_proof = deserialize_from_bin_file(RISC_WRAPPER_PROOF_PATH).unwrap();
    let risc_wrapper_vk: crate::RiscWrapperVK =
        deserialize_from_bin_file(RISC_WRAPPER_VK_PATH).unwrap();

    #[cfg(not(feature = "gpu"))]
    let (compression_proof, compression_vk) = {
        let (
            finalization_hint,
            setup_base,
            setup,
            compression_vk,
            setup_tree,
            vars_hint,
            witness_hints,
        ) = crate::get_compression_setup(risc_wrapper_vk.clone(), &worker);

        let compression_proof = crate::prove_compression(
            risc_wrapper_proof,
            risc_wrapper_vk,
            &finalization_hint,
            &setup_base,
            &setup,
            &compression_vk,
            &setup_tree,
            &vars_hint,
            &witness_hints,
            &worker,
        );

        let is_valid = crate::verify_compression_proof(&compression_proof, &compression_vk);
        assert!(is_valid);

        (compression_proof, compression_vk)
    };

    #[cfg(feature = "gpu")]
    let (compression_proof, compression_vk) = {
        use shivini::{ProverContext, ProverContextConfig};
        let config = ProverContextConfig::default().with_smallest_supported_domain_size(1 << 15);
        let _prover_context = ProverContext::create_with_config(config).unwrap();

        let (gpu_setup, gpu_vk, finalization_hint) =
            crate::gpu::compression::get_compression_setup(&worker, risc_wrapper_vk.clone());

        let compression_proof = crate::gpu::compression::prove_compression(
            risc_wrapper_proof,
            risc_wrapper_vk,
            &finalization_hint,
            &gpu_setup,
            &gpu_vk,
            &worker,
        );

        let is_valid = crate::verify_compression_proof(&compression_proof, &gpu_vk);
        assert!(is_valid);

        (compression_proof, gpu_vk)
    };

    serialize_to_bin_file(&compression_proof, COMPRESSION_PROOF_PATH).unwrap();
    serialize_to_bin_file(&compression_vk, COMPRESSION_VK_PATH).unwrap();
}

#[test]
pub(crate) fn compression_setup_test() {
    let worker = boojum::worker::Worker::new();

    let risc_wrapper_vk = deserialize_from_bin_file(RISC_WRAPPER_VK_PATH).unwrap();

    let (
        finalization_hint,
        _setup_base,
        _setup,
        compression_vk,
        _setup_tree,
        _vars_hint,
        _witness_hints,
    ) = crate::get_compression_setup(risc_wrapper_vk, &worker);

    dbg!(finalization_hint);

    serialize_to_bin_file(&compression_vk, COMPRESSION_VK_PATH).unwrap();
}
