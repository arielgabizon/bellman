use ff::PrimeField;
use groupy::{CurveAffine, CurveProjective};
use paired::{Engine, PairingCurveAffine};

use super::{PreparedVerifyingKey, Proof, VerifyingKey};
use crate::SynthesisError;
use paired::tests::field::random_field_tests;

pub fn prepare_verifying_key<E: Engine>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    let mut gamma = vk.gamma_g2;
    gamma.negate();
    let mut delta = vk.delta_g2;
    delta.negate();

    PreparedVerifyingKey {
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2),
        neg_gamma_g2: gamma.prepare(),
        neg_delta_g2: delta.prepare(),
        ic: vk.ic.clone(),
    }
}

pub fn verify_proof<'a, E: Engine>(
    pvk: &'a PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> Result<bool, SynthesisError> {
    if (public_inputs.len() + 1) != pvk.ic.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let mut acc = pvk.ic[0].into_projective();

    for (i, b) in public_inputs.iter().zip(pvk.ic.iter().skip(1)) {
        acc.add_assign(&b.mul(i.into_repr()));
    }

    // The original verification equation is:
    // A * B = alpha * beta + inputs * gamma + C * delta
    // ... however, we rearrange it so that it is:
    // A * B - inputs * gamma - C * delta = alpha * beta
    // or equivalently:
    // A * B + inputs * (-gamma) + C * (-delta) = alpha * beta
    // which allows us to do a single final exponentiation.

    Ok(E::final_exponentiation(&E::miller_loop(
        [
            (&proof.a.prepare(), &proof.b.prepare()),
            (&acc.into_affine().prepare(), &pvk.neg_gamma_g2),
            (&proof.c.prepare(), &pvk.neg_delta_g2),
        ]
        .iter(),
    ))
    .unwrap()
        == pvk.alpha_g1_beta_g2)
}

// randomized batch verification - see Appendix B.2 in Zcash spec
pub fn verify_proofs<'a, E: Engine>(
    rng: &mut R,
    pvk: &'a PreparedVerifyingKey<E>,
    proofs: &[Proof<E>],
    public_inputs: &[[E::Fr]],
) -> Result<bool, SynthesisError> {
    for (pub_input) in public_inputs {
        if (pub_input.len() + 1) != pvk.ic.len() {
            return Err(SynthesisError::MalformedVerifyingKey);
        }
    }

    let PI_num = pub_input.len();

    // choose random coefficients for combining the proofs
    let mut r = vec![];
    for _ in 0..proof_num {
        r.push(E::Fr::random(rng));
    }

    // create corresponding scalars for public input vk elements
    let mut PI_scalars = vec![];

    for i in 0..PI_num {
        PI_scalars.push(E::Fr::zero);
        for j in 0..proof_num {
            PI_scalars[i].add_assign(r[j].mul_assign(public_inputs[j][i]));
        }
    }

    // create group element corresponding to public input combination
    // This roughly corresponds to Accum_Gamma in spec
    let mut acc_PI = pvk.ic[0].into_projective();

    for (i, b) in PI_scalars.iter().zip(pvk.ic.iter().skip(1)) {
        acc_PI.add_assign(&b.mul(i.into_repr()));
    }

    acc_PI = acc_PI.into_affine().prepare();

    let mut sum_r = E::Fr::zero();
    for i in r.iter() {
        sum_r.add_assign(i);
    }
    let acc_Y = (pvk.alpha_g1_beta_g2).pow(sum_r.negate());

    // This corresponds to Accum_Delta
    let mut acc_C = E::zero();
    for (rand_coeff, proof) in r.iter().zip(proofs.iter()) {
        acc_C.add_assign(proof.c.mul_assign(rand_coeff))
    }

    acc_C = acc_C.prepare();

    let mut ML_G1 = vec![];
    let mut ML_G2 = vec![];
    for (rand_coeff, proof) in r.iter().zip(proofs.iter()) {
        ML_G1.push(&proof.a.mul_assign(rand_coeff).prepare());
        ML_G2.push(&proof.b.negate().prepare());
    }
    let acc_AB = E::miller_loop(ML_G1.iter().zip(ML_G2.iter()));

    let mut res = acc_AB.mul_assign(E::miller_loop([(&acc_C, &pvk.neg_delta_g2)]));

    Ok(E::final_exponentiation(&res).unwrap() == acc_Y)
}
