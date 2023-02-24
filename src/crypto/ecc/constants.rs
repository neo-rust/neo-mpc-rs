//! Various constants used in the Jubjub.

use bls12_381::Scalar;
use group::{ff::Field, Curve};
use jubjub::{ExtendedPoint};

/// The `d` constant of the twisted Edwards curve.
pub const EDWARDS_D: Scalar = Scalar::from_raw([
    0x0106_5fd6_d634_3eb1,
    0x292d_7f6d_3757_9d26,
    0xf5fd_9207_e6bd_7fd4,
    0x2a93_18e7_4bfa_2b48,
]);

/// The `A` constant of the birationally equivalent Montgomery curve.
pub const MONTGOMERY_A: Scalar = Scalar::from_raw([
    0x0000_0000_0000_a002,
    0x0000_0000_0000_0000,
    0x0000_0000_0000_0000,
    0x0000_0000_0000_0000,
]);

/// The scaling factor used for conversion to and from the Montgomery form.
pub const MONTGOMERY_SCALE: Scalar = Scalar::from_raw([
    0x8f45_35f7_cf82_b8d9,
    0xce40_6970_3da8_8abd,
    0x31de_341e_77d7_64e5,
    0x2762_de61_e862_645e,
]);

/// The number of chunks needed to represent a full scalar during fixed-base
/// exponentiation.
const FIXED_BASE_CHUNKS_PER_GENERATOR: usize = 84;

/// Reference to a circuit version of a generator for fixed-base salar multiplication.
pub type FixedGenerator = &'static [Vec<(Scalar, Scalar)>];

/// Circuit version of a generator for fixed-base salar multiplication.
pub type FixedGeneratorOwned = Vec<Vec<(Scalar, Scalar)>>;

/// Creates the 3-bit window table `[0, 1, ..., 8]` for different magnitudes of a fixed
/// generator.
pub fn generate_circuit_generator(mut gen: jubjub::SubgroupPoint) -> FixedGeneratorOwned {
    let mut windows = vec![];

    for _ in 0..FIXED_BASE_CHUNKS_PER_GENERATOR {
        let mut coeffs = vec![(Scalar::zero(), Scalar::one())];
        let mut g = gen;
        for _ in 0..7 {
            let g_affine = jubjub::ExtendedPoint::from(g).to_affine();
            coeffs.push((g_affine.get_u(), g_affine.get_v()));
            g += gen;
        }
        windows.push(coeffs);

        // gen = gen * 8
        gen = g;
    }

    windows
}

/// Returns the coordinates of this point's Montgomery curve representation, or `None` if
/// it is the point at infinity.
#[allow(clippy::many_single_char_names)]
pub fn to_montgomery_coords(g: ExtendedPoint) -> Option<(Scalar, Scalar)> {
    let g = g.to_affine();
    let (x, y) = (g.get_u(), g.get_v());

    if y == Scalar::one() {
        // The only solution for y = 1 is x = 0. (0, 1) is the neutral element, so we map
        // this to the point at infinity.
        None
    } else {
        // The map from a twisted Edwards curve is defined as
        // (x, y) -> (u, v) where
        //      u = (1 + y) / (1 - y)
        //      v = u / x
        //
        // This mapping is not defined for y = 1 and for x = 0.
        //
        // We have that y != 1 above. If x = 0, the only
        // solutions for y are 1 (contradiction) or -1.
        if x.is_zero_vartime() {
            // (0, -1) is the point of order two which is not
            // the neutral element, so we map it to (0, 0) which is
            // the only affine point of order 2.
            Some((Scalar::zero(), Scalar::zero()))
        } else {
            // The mapping is defined as above.
            //
            // (x, y) -> (u, v) where
            //      u = (1 + y) / (1 - y)
            //      v = u / x

            let u = (Scalar::one() + y) * (Scalar::one() - y).invert().unwrap();
            let v = u * x.invert().unwrap();

            // Scale it into the correct curve constants
            // scaling factor = sqrt(4 / (a - d))
            Some((u, v * MONTGOMERY_SCALE))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edwards_d() {
        // d = -(10240/10241)
        assert_eq!(
            -Scalar::from(10240) * Scalar::from(10241).invert().unwrap(),
            EDWARDS_D
        );
    }

    #[test]
    fn montgomery_a() {
        assert_eq!(Scalar::from(40962), MONTGOMERY_A);
    }

    #[test]
    fn montgomery_scale() {
        // scaling factor = sqrt(4 / (a - d))
        assert_eq!(
            MONTGOMERY_SCALE.square() * (-Scalar::one() - EDWARDS_D),
            Scalar::from(4),
        );
    }
}