// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2Verifier {
    uint256 internal constant    PROOF_LEN_CPTR = 0x44;
    uint256 internal constant        PROOF_CPTR = 0x64;
    uint256 internal constant NUM_INSTANCE_CPTR = 0x07e4;
    uint256 internal constant     INSTANCE_CPTR = 0x0804;

    uint256 internal constant FIRST_QUOTIENT_X_CPTR = 0x0224;
    uint256 internal constant  LAST_QUOTIENT_X_CPTR = 0x0324;

    uint256 internal constant                VK_MPTR = 0x05e0;
    uint256 internal constant         VK_DIGEST_MPTR = 0x05e0;
    uint256 internal constant     NUM_INSTANCES_MPTR = 0x0600;
    uint256 internal constant                 K_MPTR = 0x0620;
    uint256 internal constant             N_INV_MPTR = 0x0640;
    uint256 internal constant             OMEGA_MPTR = 0x0660;
    uint256 internal constant         OMEGA_INV_MPTR = 0x0680;
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = 0x06a0;
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = 0x06c0;
    uint256 internal constant        ACC_OFFSET_MPTR = 0x06e0;
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = 0x0700;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x0720;
    uint256 internal constant              G1_X_MPTR = 0x0740;
    uint256 internal constant              G1_Y_MPTR = 0x0760;
    uint256 internal constant            G2_X_1_MPTR = 0x0780;
    uint256 internal constant            G2_X_2_MPTR = 0x07a0;
    uint256 internal constant            G2_Y_1_MPTR = 0x07c0;
    uint256 internal constant            G2_Y_2_MPTR = 0x07e0;
    uint256 internal constant      NEG_S_G2_X_1_MPTR = 0x0800;
    uint256 internal constant      NEG_S_G2_X_2_MPTR = 0x0820;
    uint256 internal constant      NEG_S_G2_Y_1_MPTR = 0x0840;
    uint256 internal constant      NEG_S_G2_Y_2_MPTR = 0x0860;

    uint256 internal constant CHALLENGE_MPTR = 0x0c80;

    uint256 internal constant THETA_MPTR = 0x0c80;
    uint256 internal constant  BETA_MPTR = 0x0ca0;
    uint256 internal constant GAMMA_MPTR = 0x0cc0;
    uint256 internal constant     Y_MPTR = 0x0ce0;
    uint256 internal constant     X_MPTR = 0x0d00;
    uint256 internal constant  ZETA_MPTR = 0x0d20;
    uint256 internal constant    NU_MPTR = 0x0d40;
    uint256 internal constant    MU_MPTR = 0x0d60;

    uint256 internal constant       ACC_LHS_X_MPTR = 0x0d80;
    uint256 internal constant       ACC_LHS_Y_MPTR = 0x0da0;
    uint256 internal constant       ACC_RHS_X_MPTR = 0x0dc0;
    uint256 internal constant       ACC_RHS_Y_MPTR = 0x0de0;
    uint256 internal constant             X_N_MPTR = 0x0e00;
    uint256 internal constant X_N_MINUS_1_INV_MPTR = 0x0e20;
    uint256 internal constant          L_LAST_MPTR = 0x0e40;
    uint256 internal constant         L_BLIND_MPTR = 0x0e60;
    uint256 internal constant             L_0_MPTR = 0x0e80;
    uint256 internal constant   INSTANCE_EVAL_MPTR = 0x0ea0;
    uint256 internal constant   QUOTIENT_EVAL_MPTR = 0x0ec0;
    uint256 internal constant      QUOTIENT_X_MPTR = 0x0ee0;
    uint256 internal constant      QUOTIENT_Y_MPTR = 0x0f00;
    uint256 internal constant       G1_SCALAR_MPTR = 0x0f20;
    uint256 internal constant   PAIRING_LHS_X_MPTR = 0x0f40;
    uint256 internal constant   PAIRING_LHS_Y_MPTR = 0x0f60;
    uint256 internal constant   PAIRING_RHS_X_MPTR = 0x0f80;
    uint256 internal constant   PAIRING_RHS_Y_MPTR = 0x0fa0;

    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) public view returns (bool) {
        assembly ("memory-safe") {
            // Read EC point (x, y) at (proof_cptr, proof_cptr + 0x20),
            // and check if the point is on affine plane,
            // and store them in (hash_mptr, hash_mptr + 0x20).
            // Return updated (success, proof_cptr, hash_mptr).
            function read_ec_point(success, proof_cptr, hash_mptr, q) -> ret0, ret1, ret2 {
                let x := calldataload(proof_cptr)
                let y := calldataload(add(proof_cptr, 0x20))
                ret0 := and(success, lt(x, q))
                ret0 := and(ret0, lt(y, q))
                ret0 := and(ret0, eq(mulmod(y, y, q), addmod(mulmod(x, mulmod(x, x, q), q), 3, q)))
                mstore(hash_mptr, x)
                mstore(add(hash_mptr, 0x20), y)
                ret1 := add(proof_cptr, 0x40)
                ret2 := add(hash_mptr, 0x40)
            }

            // Squeeze challenge by keccak256(memory[0..hash_mptr]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr, hash_mptr).
            function squeeze_challenge(challenge_mptr, hash_mptr, r) -> ret0, ret1 {
                let hash := keccak256(0x00, hash_mptr)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret0 := add(challenge_mptr, 0x20)
                ret1 := 0x20
            }

            // Squeeze challenge without absorbing new input from calldata,
            // by putting an extra 0x01 in memory[0x20] and squeeze by keccak256(memory[0..21]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr).
            function squeeze_challenge_cont(challenge_mptr, r) -> ret {
                mstore8(0x20, 0x01)
                let hash := keccak256(0x00, 0x21)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret := add(challenge_mptr, 0x20)
            }

            // Batch invert values in memory[mptr_start..mptr_end] in place.
            // Return updated (success).
            function batch_invert(success, mptr_start, mptr_end, r) -> ret {
                let gp_mptr := mptr_end
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for
                    {}
                    lt(mptr, sub(mptr_end, 0x20))
                    {}
                {
                    gp := mulmod(gp, mload(mptr), r)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), r)

                mstore(gp_mptr, 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(r, 2))
                mstore(add(gp_mptr, 0xa0), r)
                ret := and(success, staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20))
                let all_inv := mload(gp_mptr)

                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for
                    {}
                    lt(second_mptr, mptr)
                    {}
                {
                    let inv := mulmod(all_inv, mload(gp_mptr), r)
                    all_inv := mulmod(all_inv, mload(mptr), r)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), r)
                let inv_second := mulmod(all_inv, mload(first_mptr), r)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Add (x, y) into point at (0x00, 0x20).
            // Return updated (success).
            function ec_add_acc(success, x, y) -> ret {
                mstore(0x40, x)
                mstore(0x60, y)
                ret := and(success, staticcall(gas(), 0x06, 0x00, 0x80, 0x00, 0x40))
            }

            // Scale point at (0x00, 0x20) by scalar.
            function ec_mul_acc(success, scalar) -> ret {
                mstore(0x40, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x00, 0x60, 0x00, 0x40))
            }

            // Add (x, y) into point at (0x80, 0xa0).
            // Return updated (success).
            function ec_add_tmp(success, x, y) -> ret {
                mstore(0xc0, x)
                mstore(0xe0, y)
                ret := and(success, staticcall(gas(), 0x06, 0x80, 0x80, 0x80, 0x40))
            }

            // Scale point at (0x80, 0xa0) by scalar.
            // Return updated (success).
            function ec_mul_tmp(success, scalar) -> ret {
                mstore(0xc0, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x80, 0x60, 0x80, 0x40))
            }

            // Perform pairing check.
            // Return updated (success).
            function ec_pairing(success, lhs_x, lhs_y, rhs_x, rhs_y) -> ret {
                mstore(0x00, lhs_x)
                mstore(0x20, lhs_y)
                mstore(0x40, mload(G2_X_1_MPTR))
                mstore(0x60, mload(G2_X_2_MPTR))
                mstore(0x80, mload(G2_Y_1_MPTR))
                mstore(0xa0, mload(G2_Y_2_MPTR))
                mstore(0xc0, rhs_x)
                mstore(0xe0, rhs_y)
                mstore(0x100, mload(NEG_S_G2_X_1_MPTR))
                mstore(0x120, mload(NEG_S_G2_X_2_MPTR))
                mstore(0x140, mload(NEG_S_G2_Y_1_MPTR))
                mstore(0x160, mload(NEG_S_G2_Y_2_MPTR))
                ret := and(success, staticcall(gas(), 0x08, 0x00, 0x180, 0x00, 0x20))
                ret := and(ret, mload(0x00))
            }

            // Modulus
            let q := 21888242871839275222246405745257275088696311157297823662689037894645226208583 // BN254 base field
            let r := 21888242871839275222246405745257275088548364400416034343698204186575808495617 // BN254 scalar field

            // Initialize success as true
            let success := true

            {
                // Load vk_digest and num_instances of vk into memory
                mstore(0x05e0, 0x1444c1d174ac6930238c01d5dbb2b9cab1b24ecc0ddcc816c26232392e62453f) // vk_digest
                mstore(0x0600, 0x0000000000000000000000000000000000000000000000000000000000000001) // num_instances

                // Check valid length of proof
                success := and(success, eq(0x0780, calldataload(PROOF_LEN_CPTR)))

                // Check valid length of instances
                let num_instances := mload(NUM_INSTANCES_MPTR)
                success := and(success, eq(num_instances, calldataload(NUM_INSTANCE_CPTR)))

                // Absorb vk diegst
                mstore(0x00, mload(VK_DIGEST_MPTR))

                // Read instances and witness commitments and generate challenges
                let hash_mptr := 0x20
                let instance_cptr := INSTANCE_CPTR
                for
                    { let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances)) }
                    lt(instance_cptr, instance_cptr_end)
                    {}
                {
                    let instance := calldataload(instance_cptr)
                    success := and(success, lt(instance, r))
                    mstore(hash_mptr, instance)
                    instance_cptr := add(instance_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                let proof_cptr := PROOF_CPTR
                let challenge_mptr := CHALLENGE_MPTR

                // Phase 1
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0100) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)

                // Phase 2
                for
                    { let proof_cptr_end := add(proof_cptr, 0xc0) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 3
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0140) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Read evaluations
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0400) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    let eval := calldataload(proof_cptr)
                    success := and(success, lt(eval, r))
                    mstore(hash_mptr, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                // Read batch opening proof and generate challenges
                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // zeta
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)                        // nu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // mu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W'

                // Load full vk into memory
                mstore(0x05e0, 0x1444c1d174ac6930238c01d5dbb2b9cab1b24ecc0ddcc816c26232392e62453f) // vk_digest
                mstore(0x0600, 0x0000000000000000000000000000000000000000000000000000000000000001) // num_instances
                mstore(0x0620, 0x0000000000000000000000000000000000000000000000000000000000000008) // k
                mstore(0x0640, 0x3033ea246e506e898e97f570caffd704cb0bb460313fb720b29e139e5c100001) // n_inv
                mstore(0x0660, 0x1058a83d529be585820b96ff0a13f2dbd8675a9e5dd2336a6692cc1e5a526c81) // omega
                mstore(0x0680, 0x1f4d7180df5014849825f3c9b0e89d79432c51f48eb5846ae63b433f28aba10b) // omega_inv
                mstore(0x06a0, 0x167a75c0b5cf99621ee13b09c52de6bca1786efc9511b245f233ae54be0a923c) // omega_inv_to_l
                mstore(0x06c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // has_accumulator
                mstore(0x06e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // acc_offset
                mstore(0x0700, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limbs
                mstore(0x0720, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limb_bits
                mstore(0x0740, 0x0000000000000000000000000000000000000000000000000000000000000001) // g1_x
                mstore(0x0760, 0x0000000000000000000000000000000000000000000000000000000000000002) // g1_y
                mstore(0x0780, 0x198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2) // g2_x_1
                mstore(0x07a0, 0x1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed) // g2_x_2
                mstore(0x07c0, 0x090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b) // g2_y_1
                mstore(0x07e0, 0x12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa) // g2_y_2
                mstore(0x0800, 0x26186a2d65ee4d2f9c9a5b91f86597d35f192cd120caf7e935d8443d1938e23d) // neg_s_g2_x_1
                mstore(0x0820, 0x30441fd1b5d3370482c42152a8899027716989a6996c2535bc9f7fee8aaef79e) // neg_s_g2_x_2
                mstore(0x0840, 0x16f363f103c80d7bbc8ad3c6867e0822bbc6000be91a4689755c7df40221c145) // neg_s_g2_y_1
                mstore(0x0860, 0x2b1cbb3e521edf5a622d82762a44a5e63f1e50b332d71154a4a7958d6011deff) // neg_s_g2_y_2
                mstore(0x0880, 0x2239433c0351a9197eb785e30711fc02e04115fa9161fa2cbafcc91ca2d1fc5e) // fixed_comms[0].x
                mstore(0x08a0, 0x1e04e165f5e649a6cd1b606742042ee12937d50154c230f46043202465476d08) // fixed_comms[0].y
                mstore(0x08c0, 0x23879b721fcbcb3517a079090d32ec8c3562340934c29e23b86b0fc2f7dd46c2) // fixed_comms[1].x
                mstore(0x08e0, 0x0e2e32a2978913c956287fb107c8fbbb20219ab0d732cebf12113067373b7dcd) // fixed_comms[1].y
                mstore(0x0900, 0x219b07bb5dfa1ca4ecd673a3a539de0ff6939c8dff30f3986148a094fe5fa396) // fixed_comms[2].x
                mstore(0x0920, 0x14d74b4892f85d088631cb397a87c59ce9a302018ea42654b604185d8a30939a) // fixed_comms[2].y
                mstore(0x0940, 0x23ec7ff87d3127ff20d396b1f5621eb00e0c2fe06b16c18e0752f078189851ba) // fixed_comms[3].x
                mstore(0x0960, 0x06a7fa4c772db794be5ab8b900748cd8eb391d19e9aafb43da8a856bfe3b6683) // fixed_comms[3].y
                mstore(0x0980, 0x03c177a8fb56e70bde49561e430abedb64c4af7a969eec784237cb1a551cb6d6) // fixed_comms[4].x
                mstore(0x09a0, 0x0db9c1d288d75d4fd490f8723d86c1bc1be1020196919139a74c630ce1a477fc) // fixed_comms[4].y
                mstore(0x09c0, 0x2a0837eed6f213acea213dbc880404584ddc42f39bf1a6a8b4373a514cdf8213) // fixed_comms[5].x
                mstore(0x09e0, 0x251362b07b27b84f3d1f3062d4e31f84692653b6d6ad08d1636a32250ca62889) // fixed_comms[5].y
                mstore(0x0a00, 0x2d864c7033b7e7a551aae624372341aca0eec94eab784e2748a56ce3a1d9a9aa) // fixed_comms[6].x
                mstore(0x0a20, 0x0d1e598fbeb297200e313dbac01623d9d8df2207ad4ff8011854572a552c2c33) // fixed_comms[6].y
                mstore(0x0a40, 0x0ad9f754ee792f096edd4529de04fca6f318609fd174bf75bc2241a60ba3bb45) // fixed_comms[7].x
                mstore(0x0a60, 0x2b2df6203a6d0220410bcec5abb9b3432db3a4e6581f91eb596feba9625f0d9d) // fixed_comms[7].y
                mstore(0x0a80, 0x061be6fd73ab20a7304c5b52d643f7861cc8f37f2e330cbde9695a55f1b470fa) // fixed_comms[8].x
                mstore(0x0aa0, 0x1d3638550e67081d93afd9f4c7dfe96231dbf03e780ae7c815a99bce8e59925f) // fixed_comms[8].y
                mstore(0x0ac0, 0x0bbb6b8daa824d0e03462a93e5ae279da3f899fb6e7dc78cf6e022411b547517) // permutation_comms[0].x
                mstore(0x0ae0, 0x15c0954fdf71a07f1efabe3605c13d42c1e8bff41f20e65bb1917977a4290c9f) // permutation_comms[0].y
                mstore(0x0b00, 0x1ef78612909969d0ff802effb868c8b3643577c0c2541f4d177a6c799689731a) // permutation_comms[1].x
                mstore(0x0b20, 0x2ee80e1f1c202eb0bbf308a5cec5a220e724baa237a47360cba716f845a71682) // permutation_comms[1].y
                mstore(0x0b40, 0x125c8306a74dbe3977a8e863389f123f5c8fe51c904ded07ac42219253ff6315) // permutation_comms[2].x
                mstore(0x0b60, 0x0d2d2c4b8934642f8e383994006dec40485267b52a5abb3da53795817cba0a14) // permutation_comms[2].y
                mstore(0x0b80, 0x0d351760bf078d5b4dbf28d10e830bde98f51d43dd4aab66062ca8344466cf80) // permutation_comms[3].x
                mstore(0x0ba0, 0x01289005f3d1af070a93e97f05aec891314412cbdbe3052fe2a092d5bbd9507f) // permutation_comms[3].y
                mstore(0x0bc0, 0x292eaa19024920f8719ec5b799f2231c33dbc2768ba2274767ee1110f35a9fa7) // permutation_comms[4].x
                mstore(0x0be0, 0x189ba0329edf9953f444b4a6bb60d71558b8599ba3be9959a5f8eb5bd43b1ce7) // permutation_comms[4].y
                mstore(0x0c00, 0x0c28e0db2e4decc2a36413620cdc36ae237ccbc1cd1168841c5375d2a79478ce) // permutation_comms[5].x
                mstore(0x0c20, 0x17b5790a11fcde00f8acf7edc4328f37883aec0f5955f8a6f7764078edf3cd05) // permutation_comms[5].y
                mstore(0x0c40, 0x284ac053d96a33fca69eca00e16eea75ad1bf008d2a742fc846ac73d17d46d73) // permutation_comms[6].x
                mstore(0x0c60, 0x14f45666a26b8d472186dbf78e606a82891e0f122a54264418cfe2615003dfb9) // permutation_comms[6].y

                // Read accumulator from instances
                if mload(HAS_ACCUMULATOR_MPTR) {
                    let num_limbs := mload(NUM_ACC_LIMBS_MPTR)
                    let num_limb_bits := mload(NUM_ACC_LIMB_BITS_MPTR)

                    let cptr := add(INSTANCE_CPTR, mul(mload(ACC_OFFSET_MPTR), 0x20))
                    let lhs_y_off := mul(num_limbs, 0x20)
                    let rhs_x_off := mul(lhs_y_off, 2)
                    let rhs_y_off := mul(lhs_y_off, 3)
                    let lhs_x := calldataload(cptr)
                    let lhs_y := calldataload(add(cptr, lhs_y_off))
                    let rhs_x := calldataload(add(cptr, rhs_x_off))
                    let rhs_y := calldataload(add(cptr, rhs_y_off))
                    for
                        {
                            let cptr_end := add(cptr, mul(0x20, num_limbs))
                            let shift := num_limb_bits
                        }
                        lt(cptr, cptr_end)
                        {}
                    {
                        cptr := add(cptr, 0x20)
                        lhs_x := add(lhs_x, shl(shift, calldataload(cptr)))
                        lhs_y := add(lhs_y, shl(shift, calldataload(add(cptr, lhs_y_off))))
                        rhs_x := add(rhs_x, shl(shift, calldataload(add(cptr, rhs_x_off))))
                        rhs_y := add(rhs_y, shl(shift, calldataload(add(cptr, rhs_y_off))))
                        shift := add(shift, num_limb_bits)
                    }

                    success := and(success, and(lt(lhs_x, q), lt(lhs_y, q)))
                    success := and(success, eq(mulmod(lhs_y, lhs_y, q), addmod(mulmod(lhs_x, mulmod(lhs_x, lhs_x, q), q), 3, q)))
                    success := and(success, and(lt(rhs_x, q), lt(rhs_y, q)))
                    success := and(success, eq(mulmod(rhs_y, rhs_y, q), addmod(mulmod(rhs_x, mulmod(rhs_x, rhs_x, q), q), 3, q)))

                    mstore(ACC_LHS_X_MPTR, lhs_x)
                    mstore(ACC_LHS_Y_MPTR, lhs_y)
                    mstore(ACC_RHS_X_MPTR, rhs_x)
                    mstore(ACC_RHS_Y_MPTR, rhs_y)
                }

                pop(q)
            }

            // Revert earlier if anything from calldata is invalid
            if iszero(success) {
                revert(0, 0)
            }

            // Compute lagrange evaluations and instance evaluation
            {
                let k := mload(K_MPTR)
                let x := mload(X_MPTR)
                let x_n := x
                for
                    { let idx := 0 }
                    lt(idx, k)
                    { idx := add(idx, 1) }
                {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(OMEGA_MPTR)

                let mptr := X_N_MPTR
                let mptr_end := add(mptr, mul(0x20, add(mload(NUM_INSTANCES_MPTR), 6)))
                if iszero(mload(NUM_INSTANCES_MPTR)) {
                    mptr_end := add(mptr_end, 0x20)
                }
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, X_N_MPTR, add(mptr_end, 0x20), r)

                mptr := X_N_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                let l_blind := mload(add(X_N_MPTR, 0x20))
                let l_i_cptr := add(X_N_MPTR, 0x40)
                for
                    { let l_i_cptr_end := add(X_N_MPTR, 0xc0) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) }
                {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                let instance_eval := 0
                for
                    {
                        let instance_cptr := INSTANCE_CPTR
                        let instance_cptr_end := add(instance_cptr, mul(0x20, mload(NUM_INSTANCES_MPTR)))
                    }
                    lt(instance_cptr, instance_cptr_end)
                    {
                        instance_cptr := add(instance_cptr, 0x20)
                        l_i_cptr := add(l_i_cptr, 0x20)
                    }
                {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(X_N_MPTR)
                let l_0 := mload(add(X_N_MPTR, 0xc0))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            // Compute quotient evavluation
            {
                let quotient_eval_numer
                let delta := 4131629893567559867359510883348571134090853742863529169391034518566172092834
                let y := mload(Y_MPTR)
                {
                    let f_6 := calldataload(0x0564)
                    let a_0 := calldataload(0x0364)
                    let f_0 := calldataload(0x0504)
                    let var0 := addmod(a_0, f_0, r)
                    let var1 := mulmod(var0, var0, r)
                    let var2 := mulmod(var1, var1, r)
                    let var3 := mulmod(var2, var0, r)
                    let var4 := mulmod(var3, 0x9600146bec7f4fd625ea9db1f247c6376f479f8fa4b34f1227f14ac41bc4cd3, r)
                    let a_1 := calldataload(0x0384)
                    let f_1 := calldataload(0x0524)
                    let var5 := addmod(a_1, f_1, r)
                    let var6 := mulmod(var5, var5, r)
                    let var7 := mulmod(var6, var6, r)
                    let var8 := mulmod(var7, var5, r)
                    let var9 := mulmod(var8, 0x1eb832b908b873be41b430e81e9f5fa648080f6a139f5a64570e848cb09c9292, r)
                    let var10 := addmod(var4, var9, r)
                    let a_2 := calldataload(0x03a4)
                    let f_2 := calldataload(0x0544)
                    let var11 := addmod(a_2, f_2, r)
                    let var12 := mulmod(var11, var11, r)
                    let var13 := mulmod(var12, var12, r)
                    let var14 := mulmod(var13, var11, r)
                    let var15 := mulmod(var14, 0x868c3677aaeb8a5b01fc0c44f5d2367a26db160ae28eb98b63cccbea20d8af, r)
                    let var16 := addmod(var10, var15, r)
                    let a_0_next_1 := calldataload(0x03c4)
                    let var17 := sub(r, a_0_next_1)
                    let var18 := addmod(var16, var17, r)
                    let var19 := mulmod(f_6, var18, r)
                    quotient_eval_numer := var19
                }
                {
                    let f_6 := calldataload(0x0564)
                    let a_0 := calldataload(0x0364)
                    let f_0 := calldataload(0x0504)
                    let var0 := addmod(a_0, f_0, r)
                    let var1 := mulmod(var0, var0, r)
                    let var2 := mulmod(var1, var1, r)
                    let var3 := mulmod(var2, var0, r)
                    let var4 := mulmod(var3, 0xb9a382db8289f520ece763cbb2094c444663a2bf55db56999a4614a96504ebe, r)
                    let a_1 := calldataload(0x0384)
                    let f_1 := calldataload(0x0524)
                    let var5 := addmod(a_1, f_1, r)
                    let var6 := mulmod(var5, var5, r)
                    let var7 := mulmod(var6, var6, r)
                    let var8 := mulmod(var7, var5, r)
                    let var9 := mulmod(var8, 0x2de7772476f303a6d2879cdcc47c1113ef4e1936fb876d034bbcda5acdc435ec, r)
                    let var10 := addmod(var4, var9, r)
                    let a_2 := calldataload(0x03a4)
                    let f_2 := calldataload(0x0544)
                    let var11 := addmod(a_2, f_2, r)
                    let var12 := mulmod(var11, var11, r)
                    let var13 := mulmod(var12, var12, r)
                    let var14 := mulmod(var13, var11, r)
                    let var15 := mulmod(var14, 0x27948d4bcb6d665205572ebbde236b7624da6487f1b18fdbbc44e7a2dd3d793d, r)
                    let var16 := addmod(var10, var15, r)
                    let a_1_next_1 := calldataload(0x03e4)
                    let var17 := sub(r, a_1_next_1)
                    let var18 := addmod(var16, var17, r)
                    let var19 := mulmod(f_6, var18, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var19, r)
                }
                {
                    let f_6 := calldataload(0x0564)
                    let a_0 := calldataload(0x0364)
                    let f_0 := calldataload(0x0504)
                    let var0 := addmod(a_0, f_0, r)
                    let var1 := mulmod(var0, var0, r)
                    let var2 := mulmod(var1, var1, r)
                    let var3 := mulmod(var2, var0, r)
                    let var4 := mulmod(var3, 0x1fcefc218b5675feed028865d2f9ef22a1e31f41f7ce7631f645471265344dc4, r)
                    let a_1 := calldataload(0x0384)
                    let f_1 := calldataload(0x0524)
                    let var5 := addmod(a_1, f_1, r)
                    let var6 := mulmod(var5, var5, r)
                    let var7 := mulmod(var6, var6, r)
                    let var8 := mulmod(var7, var5, r)
                    let var9 := mulmod(var8, 0xd7b02b0f922e679dfd828024c17296596770fdc936f9b16ae612716ce444b3b, r)
                    let var10 := addmod(var4, var9, r)
                    let a_2 := calldataload(0x03a4)
                    let f_2 := calldataload(0x0544)
                    let var11 := addmod(a_2, f_2, r)
                    let var12 := mulmod(var11, var11, r)
                    let var13 := mulmod(var12, var12, r)
                    let var14 := mulmod(var13, var11, r)
                    let var15 := mulmod(var14, 0x1ee23b55636874a2ca16a9f3c1f9bc4ff17410f229a1271d46fdc664ee4511c7, r)
                    let var16 := addmod(var10, var15, r)
                    let a_2_next_1 := calldataload(0x0404)
                    let var17 := sub(r, a_2_next_1)
                    let var18 := addmod(var16, var17, r)
                    let var19 := mulmod(f_6, var18, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var19, r)
                }
                {
                    let f_7 := calldataload(0x0584)
                    let a_0 := calldataload(0x0364)
                    let f_0 := calldataload(0x0504)
                    let var0 := addmod(a_0, f_0, r)
                    let var1 := mulmod(var0, var0, r)
                    let var2 := mulmod(var1, var1, r)
                    let var3 := mulmod(var2, var0, r)
                    let a_3 := calldataload(0x0424)
                    let var4 := sub(r, a_3)
                    let var5 := addmod(var3, var4, r)
                    let var6 := mulmod(f_7, var5, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var6, r)
                }
                {
                    let f_7 := calldataload(0x0584)
                    let a_3 := calldataload(0x0424)
                    let var0 := mulmod(a_3, 0x9600146bec7f4fd625ea9db1f247c6376f479f8fa4b34f1227f14ac41bc4cd3, r)
                    let a_1 := calldataload(0x0384)
                    let f_1 := calldataload(0x0524)
                    let var1 := addmod(a_1, f_1, r)
                    let var2 := mulmod(var1, 0x1eb832b908b873be41b430e81e9f5fa648080f6a139f5a64570e848cb09c9292, r)
                    let var3 := addmod(var0, var2, r)
                    let a_2 := calldataload(0x03a4)
                    let f_2 := calldataload(0x0544)
                    let var4 := addmod(a_2, f_2, r)
                    let var5 := mulmod(var4, 0x868c3677aaeb8a5b01fc0c44f5d2367a26db160ae28eb98b63cccbea20d8af, r)
                    let var6 := addmod(var3, var5, r)
                    let f_3 := calldataload(0x04a4)
                    let var7 := addmod(var6, f_3, r)
                    let var8 := mulmod(var7, var7, r)
                    let var9 := mulmod(var8, var8, r)
                    let var10 := mulmod(var9, var7, r)
                    let a_0_next_1 := calldataload(0x03c4)
                    let var11 := mulmod(a_0_next_1, 0x1853f03f9b252eeb4def04f67ea4695d3e91e73306f0cd432f1e66ed55f9c9fc, r)
                    let a_1_next_1 := calldataload(0x03e4)
                    let var12 := mulmod(a_1_next_1, 0x132185516ff7885d531ce5e3792c993644db50db384d01a122b56ca429c363fc, r)
                    let var13 := addmod(var11, var12, r)
                    let a_2_next_1 := calldataload(0x0404)
                    let var14 := mulmod(a_2_next_1, 0x48c9fd0418a78de7ccd2f5fd6e0a05b79a6862e163c5e40e9f26d10389937e7, r)
                    let var15 := addmod(var13, var14, r)
                    let var16 := sub(r, var15)
                    let var17 := addmod(var10, var16, r)
                    let var18 := mulmod(f_7, var17, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var18, r)
                }
                {
                    let f_7 := calldataload(0x0584)
                    let a_3 := calldataload(0x0424)
                    let var0 := mulmod(a_3, 0xb9a382db8289f520ece763cbb2094c444663a2bf55db56999a4614a96504ebe, r)
                    let a_1 := calldataload(0x0384)
                    let f_1 := calldataload(0x0524)
                    let var1 := addmod(a_1, f_1, r)
                    let var2 := mulmod(var1, 0x2de7772476f303a6d2879cdcc47c1113ef4e1936fb876d034bbcda5acdc435ec, r)
                    let var3 := addmod(var0, var2, r)
                    let a_2 := calldataload(0x03a4)
                    let f_2 := calldataload(0x0544)
                    let var4 := addmod(a_2, f_2, r)
                    let var5 := mulmod(var4, 0x27948d4bcb6d665205572ebbde236b7624da6487f1b18fdbbc44e7a2dd3d793d, r)
                    let var6 := addmod(var3, var5, r)
                    let f_4 := calldataload(0x04c4)
                    let var7 := addmod(var6, f_4, r)
                    let a_0_next_1 := calldataload(0x03c4)
                    let var8 := mulmod(a_0_next_1, 0x1c57f77f7c6e2d7022535c06418140c40e6a2162b3311237b782b5fc2ef1eef5, r)
                    let a_1_next_1 := calldataload(0x03e4)
                    let var9 := mulmod(a_1_next_1, 0x1e830536445074ac249acf6af5d2bddc40e64ba0515d988e670aef95c403752a, r)
                    let var10 := addmod(var8, var9, r)
                    let a_2_next_1 := calldataload(0x0404)
                    let var11 := mulmod(a_2_next_1, 0x255e46607289f38834ad7a9180132c72025c31fa10473f628051c9632e142537, r)
                    let var12 := addmod(var10, var11, r)
                    let var13 := sub(r, var12)
                    let var14 := addmod(var7, var13, r)
                    let var15 := mulmod(f_7, var14, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_7 := calldataload(0x0584)
                    let a_3 := calldataload(0x0424)
                    let var0 := mulmod(a_3, 0x1fcefc218b5675feed028865d2f9ef22a1e31f41f7ce7631f645471265344dc4, r)
                    let a_1 := calldataload(0x0384)
                    let f_1 := calldataload(0x0524)
                    let var1 := addmod(a_1, f_1, r)
                    let var2 := mulmod(var1, 0xd7b02b0f922e679dfd828024c17296596770fdc936f9b16ae612716ce444b3b, r)
                    let var3 := addmod(var0, var2, r)
                    let a_2 := calldataload(0x03a4)
                    let f_2 := calldataload(0x0544)
                    let var4 := addmod(a_2, f_2, r)
                    let var5 := mulmod(var4, 0x1ee23b55636874a2ca16a9f3c1f9bc4ff17410f229a1271d46fdc664ee4511c7, r)
                    let var6 := addmod(var3, var5, r)
                    let f_5 := calldataload(0x04e4)
                    let var7 := addmod(var6, f_5, r)
                    let a_0_next_1 := calldataload(0x03c4)
                    let var8 := mulmod(a_0_next_1, 0x92ca526b2fdef96c0ec02fce8d51fdea61725cbff027a2e24ebea472f8a4181, r)
                    let a_1_next_1 := calldataload(0x03e4)
                    let var9 := mulmod(a_1_next_1, 0xf2380249580f86a2c30b2e3432d19969396c30ce1a1bf4a7cbe164eddf2ed1, r)
                    let var10 := addmod(var8, var9, r)
                    let a_2_next_1 := calldataload(0x0404)
                    let var11 := mulmod(a_2_next_1, 0xf03e31e34235cbb100bea16d54ec9e3a0e3f64ce8b0590a80de8813ede171ea, r)
                    let var12 := addmod(var10, var11, r)
                    let var13 := sub(r, var12)
                    let var14 := addmod(var7, var13, r)
                    let var15 := mulmod(f_7, var14, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_8 := calldataload(0x05a4)
                    let a_0_prev_1 := calldataload(0x0464)
                    let a_0 := calldataload(0x0364)
                    let var0 := addmod(a_0_prev_1, a_0, r)
                    let a_0_next_1 := calldataload(0x03c4)
                    let var1 := sub(r, a_0_next_1)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_8, var2, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var3, r)
                }
                {
                    let f_8 := calldataload(0x05a4)
                    let a_1_prev_1 := calldataload(0x0484)
                    let a_1 := calldataload(0x0384)
                    let var0 := addmod(a_1_prev_1, a_1, r)
                    let a_1_next_1 := calldataload(0x03e4)
                    let var1 := sub(r, a_1_next_1)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_8, var2, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var3, r)
                }
                {
                    let f_8 := calldataload(0x05a4)
                    let a_2_prev_1 := calldataload(0x0444)
                    let a_2_next_1 := calldataload(0x0404)
                    let var0 := sub(r, a_2_next_1)
                    let var1 := addmod(a_2_prev_1, var0, r)
                    let var2 := mulmod(f_8, var1, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var2, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := addmod(l_0, sub(r, mulmod(l_0, calldataload(0x06c4), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let perm_z_last := calldataload(0x0724)
                    let eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(perm_z_last, perm_z_last, r), sub(r, perm_z_last), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x0724), sub(r, calldataload(0x0704)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x06e4)
                    let rhs := calldataload(0x06c4)
                    lhs := mulmod(lhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mulmod(beta, calldataload(0x05e4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x04a4), mulmod(beta, calldataload(0x0604), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0364), mulmod(beta, calldataload(0x0624), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0384), mulmod(beta, calldataload(0x0644), r), r), gamma, r), r)
                    mstore(0x00, mulmod(beta, mload(X_MPTR), r))
                    rhs := mulmod(rhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x04a4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0364), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0384), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x0744)
                    let rhs := calldataload(0x0724)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x03a4), mulmod(beta, calldataload(0x0664), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x04c4), mulmod(beta, calldataload(0x0684), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x04e4), mulmod(beta, calldataload(0x06a4), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x03a4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x04c4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x04e4), mload(0x00), r), gamma, r), r)
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }

                pop(y)
                pop(delta)

                let quotient_eval := mulmod(quotient_eval_numer, mload(X_N_MINUS_1_INV_MPTR), r)
                mstore(QUOTIENT_EVAL_MPTR, quotient_eval)
            }

            // Compute quotient commitment
            {
                mstore(0x00, calldataload(LAST_QUOTIENT_X_CPTR))
                mstore(0x20, calldataload(add(LAST_QUOTIENT_X_CPTR, 0x20)))
                let x_n := mload(X_N_MPTR)
                for
                    {
                        let cptr := sub(LAST_QUOTIENT_X_CPTR, 0x40)
                        let cptr_end := sub(FIRST_QUOTIENT_X_CPTR, 0x40)
                    }
                    lt(cptr_end, cptr)
                    {}
                {
                    success := ec_mul_acc(success, x_n)
                    success := ec_add_acc(success, calldataload(cptr), calldataload(add(cptr, 0x20)))
                    cptr := sub(cptr, 0x40)
                }
                mstore(QUOTIENT_X_MPTR, mload(0x00))
                mstore(QUOTIENT_Y_MPTR, mload(0x20))
            }

            // Compute pairing lhs and rhs
            {
                {
                    let x := mload(X_MPTR)
                    let omega := mload(OMEGA_MPTR)
                    let omega_inv := mload(OMEGA_INV_MPTR)
                    let x_pow_of_omega := mulmod(x, omega, r)
                    mstore(0x03a0, x_pow_of_omega)
                    mstore(0x0380, x)
                    x_pow_of_omega := mulmod(x, omega_inv, r)
                    mstore(0x0360, x_pow_of_omega)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    mstore(0x0340, x_pow_of_omega)
                }
                {
                    let mu := mload(MU_MPTR)
                    for
                        {
                            let mptr := 0x03c0
                            let mptr_end := 0x0440
                            let point_mptr := 0x0340
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            point_mptr := add(point_mptr, 0x20)
                        }
                    {
                        mstore(mptr, addmod(mu, sub(r, mload(point_mptr)), r))
                    }
                    let s
                    s := mload(0x03e0)
                    s := mulmod(s, mload(0x0400), r)
                    s := mulmod(s, mload(0x0420), r)
                    mstore(0x0440, s)
                    let diff
                    diff := mload(0x03c0)
                    mstore(0x0460, diff)
                    mstore(0x00, diff)
                    diff := mload(0x03c0)
                    diff := mulmod(diff, mload(0x03e0), r)
                    diff := mulmod(diff, mload(0x0420), r)
                    mstore(0x0480, diff)
                    diff := mload(0x03e0)
                    mstore(0x04a0, diff)
                    diff := mload(0x03c0)
                    diff := mulmod(diff, mload(0x03e0), r)
                    mstore(0x04c0, diff)
                }
                {
                    let point_1 := mload(0x0360)
                    let point_2 := mload(0x0380)
                    let point_3 := mload(0x03a0)
                    let coeff
                    coeff := addmod(point_1, sub(r, point_2), r)
                    coeff := mulmod(coeff, addmod(point_1, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x03e0), r)
                    mstore(0x20, coeff)
                    coeff := addmod(point_2, sub(r, point_1), r)
                    coeff := mulmod(coeff, addmod(point_2, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x0400), r)
                    mstore(0x40, coeff)
                    coeff := addmod(point_3, sub(r, point_1), r)
                    coeff := mulmod(coeff, addmod(point_3, sub(r, point_2), r), r)
                    coeff := mulmod(coeff, mload(0x0420), r)
                    mstore(0x60, coeff)
                }
                {
                    let point_2 := mload(0x0380)
                    let coeff
                    coeff := 1
                    coeff := mulmod(coeff, mload(0x0400), r)
                    mstore(0x80, coeff)
                }
                {
                    let point_0 := mload(0x0340)
                    let point_2 := mload(0x0380)
                    let point_3 := mload(0x03a0)
                    let coeff
                    coeff := addmod(point_0, sub(r, point_2), r)
                    coeff := mulmod(coeff, addmod(point_0, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0xa0, coeff)
                    coeff := addmod(point_2, sub(r, point_0), r)
                    coeff := mulmod(coeff, addmod(point_2, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x0400), r)
                    mstore(0xc0, coeff)
                    coeff := addmod(point_3, sub(r, point_0), r)
                    coeff := mulmod(coeff, addmod(point_3, sub(r, point_2), r), r)
                    coeff := mulmod(coeff, mload(0x0420), r)
                    mstore(0xe0, coeff)
                }
                {
                    let point_2 := mload(0x0380)
                    let point_3 := mload(0x03a0)
                    let coeff
                    coeff := addmod(point_2, sub(r, point_3), r)
                    coeff := mulmod(coeff, mload(0x0400), r)
                    mstore(0x0100, coeff)
                    coeff := addmod(point_3, sub(r, point_2), r)
                    coeff := mulmod(coeff, mload(0x0420), r)
                    mstore(0x0120, coeff)
                }
                {
                    success := batch_invert(success, 0, 0x0140, r)
                    let diff_0_inv := mload(0x00)
                    mstore(0x0460, diff_0_inv)
                    for
                        {
                            let mptr := 0x0480
                            let mptr_end := 0x04e0
                        }
                        lt(mptr, mptr_end)
                        { mptr := add(mptr, 0x20) }
                    {
                        mstore(mptr, mulmod(mload(mptr), diff_0_inv, r))
                    }
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval
                    r_eval := addmod(r_eval, mulmod(mload(0x20), calldataload(0x0444), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x03a4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x0404), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x20), calldataload(0x0484), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x0384), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x03e4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x20), calldataload(0x0464), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x0364), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x03c4), r), r)
                    mstore(0x04e0, r_eval)
                }
                {
                    let coeff := mload(0x80)
                    let zeta := mload(ZETA_MPTR)
                    let r_eval
                    r_eval := mulmod(coeff, calldataload(0x05c4), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, mload(QUOTIENT_EVAL_MPTR), r), r)
                    for
                        {
                            let cptr := 0x06a4
                            let cptr_end := 0x05c4
                        }
                        lt(cptr_end, cptr)
                        { cptr := sub(cptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(cptr), r), r)
                    }
                    for
                        {
                            let cptr := 0x05a4
                            let cptr_end := 0x0484
                        }
                        lt(cptr_end, cptr)
                        { cptr := sub(cptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(cptr), r), r)
                    }
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0424), r), r)
                    r_eval := mulmod(r_eval, mload(0x0480), r)
                    mstore(0x0500, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x0704), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x06c4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x06e4), r), r)
                    r_eval := mulmod(r_eval, mload(0x04a0), r)
                    mstore(0x0520, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0724), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0120), calldataload(0x0744), r), r)
                    r_eval := mulmod(r_eval, mload(0x04c0), r)
                    mstore(0x0540, r_eval)
                }
                {
                    let sum := mload(0x20)
                    sum := addmod(sum, mload(0x40), r)
                    sum := addmod(sum, mload(0x60), r)
                    mstore(0x0560, sum)
                }
                {
                    let sum := mload(0x80)
                    mstore(0x0580, sum)
                }
                {
                    let sum := mload(0xa0)
                    sum := addmod(sum, mload(0xc0), r)
                    sum := addmod(sum, mload(0xe0), r)
                    mstore(0x05a0, sum)
                }
                {
                    let sum := mload(0x0100)
                    sum := addmod(sum, mload(0x0120), r)
                    mstore(0x05c0, sum)
                }
                {
                    for
                        {
                            let mptr := 0x00
                            let mptr_end := 0x80
                            let sum_mptr := 0x0560
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            sum_mptr := add(sum_mptr, 0x20)
                        }
                    {
                        mstore(mptr, mload(sum_mptr))
                    }
                    success := batch_invert(success, 0, 0x80, r)
                    let r_eval := mulmod(mload(0x60), mload(0x0540), r)
                    for
                        {
                            let sum_inv_mptr := 0x40
                            let sum_inv_mptr_end := 0x80
                            let r_eval_mptr := 0x0520
                        }
                        lt(sum_inv_mptr, sum_inv_mptr_end)
                        {
                            sum_inv_mptr := sub(sum_inv_mptr, 0x20)
                            r_eval_mptr := sub(r_eval_mptr, 0x20)
                        }
                    {
                        r_eval := mulmod(r_eval, mload(NU_MPTR), r)
                        r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), r), r)
                    }
                    mstore(G1_SCALAR_MPTR, sub(r, r_eval))
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let nu := mload(NU_MPTR)
                    mstore(0x00, calldataload(0xe4))
                    mstore(0x20, calldataload(0x0104))
                    success := ec_mul_acc(success, zeta)
                    success := ec_add_acc(success, calldataload(0xa4), calldataload(0xc4))
                    success := ec_mul_acc(success, zeta)
                    success := ec_add_acc(success, calldataload(0x64), calldataload(0x84))
                    mstore(0x80, calldataload(0x01e4))
                    mstore(0xa0, calldataload(0x0204))
                    success := ec_mul_tmp(success, zeta)
                    success := ec_add_tmp(success, mload(QUOTIENT_X_MPTR), mload(QUOTIENT_Y_MPTR))
                    for
                        {
                            let ptr := 0x0c40
                            let ptr_end := 0x09c0
                        }
                        lt(ptr_end, ptr)
                        { ptr := sub(ptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, zeta)
                        success := ec_add_tmp(success, mload(ptr), mload(add(ptr, 0x20)))
                    }
                    for
                        {
                            let ptr := 0x0900
                            let ptr_end := 0x0840
                        }
                        lt(ptr_end, ptr)
                        { ptr := sub(ptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, zeta)
                        success := ec_add_tmp(success, mload(ptr), mload(add(ptr, 0x20)))
                    }
                    for
                        {
                            let ptr := 0x09c0
                            let ptr_end := 0x0900
                        }
                        lt(ptr_end, ptr)
                        { ptr := sub(ptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, zeta)
                        success := ec_add_tmp(success, mload(ptr), mload(add(ptr, 0x20)))
                    }
                    success := ec_mul_tmp(success, zeta)
                    success := ec_add_tmp(success, calldataload(0x0124), calldataload(0x0144))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0480), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), r)
                    mstore(0x80, calldataload(0x0164))
                    mstore(0xa0, calldataload(0x0184))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x04a0), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), r)
                    mstore(0x80, calldataload(0x01a4))
                    mstore(0xa0, calldataload(0x01c4))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x04c0), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, mload(G1_X_MPTR))
                    mstore(0xa0, mload(G1_Y_MPTR))
                    success := ec_mul_tmp(success, mload(G1_SCALAR_MPTR))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x0764))
                    mstore(0xa0, calldataload(0x0784))
                    success := ec_mul_tmp(success, sub(r, mload(0x0440)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x07a4))
                    mstore(0xa0, calldataload(0x07c4))
                    success := ec_mul_tmp(success, mload(MU_MPTR))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                    mstore(PAIRING_LHS_Y_MPTR, mload(0x20))
                    mstore(PAIRING_RHS_X_MPTR, calldataload(0x07a4))
                    mstore(PAIRING_RHS_Y_MPTR, calldataload(0x07c4))
                }
            }

            // Random linear combine with accumulator
            if mload(HAS_ACCUMULATOR_MPTR) {
                mstore(0x00, mload(ACC_LHS_X_MPTR))
                mstore(0x20, mload(ACC_LHS_Y_MPTR))
                mstore(0x40, mload(ACC_RHS_X_MPTR))
                mstore(0x60, mload(ACC_RHS_Y_MPTR))
                mstore(0x80, mload(PAIRING_LHS_X_MPTR))
                mstore(0xa0, mload(PAIRING_LHS_Y_MPTR))
                mstore(0xc0, mload(PAIRING_RHS_X_MPTR))
                mstore(0xe0, mload(PAIRING_RHS_Y_MPTR))
                let challenge := mod(keccak256(0x00, 0x100), r)

                // [pairing_lhs] += challenge * [acc_lhs]
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_LHS_X_MPTR), mload(PAIRING_LHS_Y_MPTR))
                mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                mstore(PAIRING_LHS_Y_MPTR, mload(0x20))

                // [pairing_rhs] += challenge * [acc_rhs]
                mstore(0x00, mload(ACC_RHS_X_MPTR))
                mstore(0x20, mload(ACC_RHS_Y_MPTR))
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_RHS_X_MPTR), mload(PAIRING_RHS_Y_MPTR))
                mstore(PAIRING_RHS_X_MPTR, mload(0x00))
                mstore(PAIRING_RHS_Y_MPTR, mload(0x20))
            }

            // Perform pairing
            success := ec_pairing(
                success,
                mload(PAIRING_LHS_X_MPTR),
                mload(PAIRING_LHS_Y_MPTR),
                mload(PAIRING_RHS_X_MPTR),
                mload(PAIRING_RHS_Y_MPTR)
            )

            // Revert if anything fails
            if iszero(success) {
                revert(0x00, 0x00)
            }

            // Return 1 as result if everything succeeds
            mstore(0x00, 1)
            return(0x00, 0x20)
        }
    }
}
