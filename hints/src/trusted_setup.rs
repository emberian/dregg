use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalSerialize, Compress, SerializationError, Validate};
use hex::FromHexError;
use serde::Deserialize;

const ETHSETUP_JSON: &str = include_str!("data/trusted_setup_64.json");

/// JSON representation of the Ethereum trusted setup.
#[derive(Deserialize, Debug, PartialEq, Eq)]
pub struct JsonTrustedSetup {
    pub g1_monomial: Vec<String>,
    pub g1_lagrange: Vec<String>,
    pub g2_monomial: Vec<String>,
}

impl Default for JsonTrustedSetup {
    fn default() -> Self {
        // The embedded data is a compile-time constant; a parse failure here
        // indicates a build corruption and is unrecoverable.
        JsonTrustedSetup::from_embed()
            .expect("embedded trusted setup data is corrupt")
    }
}

/// Trusted setup for the BLS12-381 curve.
pub struct TrustedSetup<E: Pairing> {
    pub g1_points: Vec<E::G1Affine>,
    pub g2_points: Vec<E::G2Affine>,
}

/// An enum used to specify whether to check that the points are in the correct subgroup
#[derive(Debug, Copy, Clone)]
enum SubgroupCheck {
    Check,
    #[allow(unused)]
    NoCheck,
}

/// Errors from parsing the trusted setup.
#[derive(Debug)]
pub enum TrustedSetupError {
    SerializationError(SerializationError),
    HexDecodeError(FromHexError),
    BadHexPrefix,
    PointCountMismatch(usize, usize),
    InvalidSubgroup,
    IntoFailed,
    /// JSON parsing failed.
    JsonParseError,
}

impl From<SerializationError> for TrustedSetupError {
    fn from(e: SerializationError) -> Self {
        TrustedSetupError::SerializationError(e)
    }
}

impl From<FromHexError> for TrustedSetupError {
    fn from(e: FromHexError) -> Self {
        TrustedSetupError::HexDecodeError(e)
    }
}

impl JsonTrustedSetup {
    /// Parse a Json string in the format specified by the ethereum trusted setup.
    ///
    /// The file that is being used on mainnet is located here: <https://github.com/ethereum/consensus-specs/blob/389b2ddfb954731da7ccf4c0ef89fab2d4575b99/presets/mainnet/trusted_setups/trusted_setup_4096.json>
    ///
    // The format that the file follows that this function also accepts, looks like the following:
    /*
    {
      "g1_monomial": [
        "0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb",
        ...
      ],
      "g1_lagrange": [
        "0xa0413c0dcafec6dbc9f47d66785cf1e8c981044f7d13cfe3e4fcbb71b5408dfde6312493cb3c1d30516cb3ca88c03654",
        "0x8b997fb25730d661918371bb41f2a6e899cac23f04fc5365800b75433c0a953250e15e7a98fb5ca5cc56a8cd34c20c57",
        ...
      ],
      "g2_monomial": [
        "0x93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8",
        ...
      ]
    }
    */
    pub fn from_json<E: Pairing>(json: &str) -> Result<JsonTrustedSetup, TrustedSetupError> {
        let trusted_setup = Self::from_json_unchecked(json)?;
        trusted_setup.deserialize::<E>()?;
        Ok(trusted_setup)
    }

    /// Parse a Json string in the format specified by the ethereum trusted setup.
    ///
    /// This method does not check that the points are in the correct subgroup.
    pub fn from_json_unchecked(json: &str) -> Result<JsonTrustedSetup, TrustedSetupError> {
        serde_json::from_str(json).map_err(|_| TrustedSetupError::JsonParseError)
    }

    /// Load the embedded mainnet trusted setup, returning an error on parse failure.
    pub fn load_embedded() -> Result<Self, TrustedSetupError> {
        Self::from_embed()
    }

    /// Loads the official trusted setup file being used on mainnet from the embedded data folder.
    fn from_embed() -> Result<JsonTrustedSetup, TrustedSetupError> {
        Self::from_json_unchecked(ETHSETUP_JSON)
    }

    /// Deserialize the JSON into a `TrustedSetup` struct.
    pub fn deserialize<E: Pairing>(&self) -> Result<TrustedSetup<E>, TrustedSetupError> {
        let g1_size = E::G1Affine::serialized_size(&E::G1Affine::zero(), Compress::Yes);
        let g2_size = E::G2Affine::serialized_size(&E::G2Affine::zero(), Compress::Yes);
        if g1_size != 48 || g2_size != 96 {
            return Err(TrustedSetupError::PointCountMismatch(g1_size, g2_size));
        }

        let g1_points =
            deserialize_points::<_, E::G1Affine, 48>(&self.g1_monomial, SubgroupCheck::Check)?;
        let g2_points =
            deserialize_points::<_, E::G2Affine, 96>(&self.g2_monomial, SubgroupCheck::Check)?;

        Ok(TrustedSetup {
            g1_points,
            g2_points,
        })
    }
}

fn deserialize_points<T: AsRef<str>, G: AffineRepr, const N: usize>(
    g_points_hex_str: &[T],
    check: SubgroupCheck,
) -> Result<Vec<G>, TrustedSetupError> {
    let mut g_points = Vec::new();
    for g_hex_str in g_points_hex_str {
        let g_hex_str = g_hex_str.as_ref();

        let g_hex_str_without_0x = g_hex_str
            .strip_prefix("0x")
            .ok_or(TrustedSetupError::BadHexPrefix)?;
        let g_point_bytes: [u8; N] = hex::decode(g_hex_str_without_0x)?
            .try_into()
            .map_err(|_| TrustedSetupError::IntoFailed)?;
        let point = G::deserialize_with_mode(
            &mut &g_point_bytes[..],
            Compress::Yes,
            if let SubgroupCheck::Check = check {
                Validate::Yes
            } else {
                Validate::No
            },
        );

        g_points.push(point?)
    }

    Ok(g_points)
}

#[test]
fn test_embedded_setup_has_points_in_correct_subgroup() {
    let setup = JsonTrustedSetup::default();
    setup.deserialize::<crate::Curve>().unwrap();
}
