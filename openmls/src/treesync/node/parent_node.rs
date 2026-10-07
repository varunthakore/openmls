//! This module contains the [`ParentNode`] struct, its implementation, as well
//! as the [`PlainUpdatePathNode`], a helper struct for the creation of
//! [`UpdatePathNode`] instances.
use openmls_traits::crypto::OpenMlsCrypto;
use openmls_traits::types::{Ciphersuite, HpkeCiphertext};
#[cfg(not(target_arch = "wasm32"))]
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use thiserror::*;
use tls_codec::{TlsDeserialize, TlsDeserializeBytes, TlsSerialize, TlsSize, VLBytes};

use super::encryption_keys::{EncryptionKey, EncryptionKeyPair};
use crate::{
    binary_tree::array_representation::{LeafNodeIndex, ParentNodeIndex},
    ciphersuite::HpkePublicKey,
    error::LibraryError,
    messages::PathSecret,
    schedule::CommitSecret,
    treesync::{hashes::ParentHashInput, treekem::UpdatePathNode},
};

/// This struct implements the MLS parent node. It contains its public key,
/// parent hash and unmerged leaves. Additionally, it may contain the private
/// key corresponding to the public key.
#[derive(
    Debug,
    Eq,
    PartialEq,
    Clone,
    Serialize,
    Deserialize,
    TlsSerialize,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSize,
)]
pub struct ParentNode {
    pub(super) encryption_key: EncryptionKey,
    pub(super) parent_hash: VLBytes,
    pub(super) unmerged_leaves: UnmergedLeaves,
}

impl From<EncryptionKey> for ParentNode {
    fn from(public_key: EncryptionKey) -> Self {
        Self {
            encryption_key: public_key,
            parent_hash: vec![].into(),
            unmerged_leaves: UnmergedLeaves::new(),
        }
    }
}

/// Helper struct for the encryption of a [`ParentNode`].
#[cfg_attr(test, derive(Clone))]
#[derive(Debug)]
pub(crate) struct PlainUpdatePathNode {
    public_key: EncryptionKey,
    path_secret: PathSecret,
}

impl PlainUpdatePathNode {
    /// Encrypt this node and return the resulting [`UpdatePathNode`].
    pub(in crate::treesync) fn encrypt(
        &self,
        crypto: &impl OpenMlsCrypto,
        ciphersuite: Ciphersuite,
        public_keys: &[EncryptionKey],
        group_context: &[u8],
    ) -> Result<UpdatePathNode, LibraryError> {
        #[cfg(target_arch = "wasm32")]
        let public_keys = public_keys.iter();
        #[cfg(not(target_arch = "wasm32"))]
        let public_keys = public_keys.par_iter();

        public_keys
            .map(|pk| {
                self.path_secret
                    .encrypt(crypto, ciphersuite, pk, group_context)
            })
            .collect::<Result<Vec<HpkeCiphertext>, LibraryError>>()
            .map(|encrypted_path_secrets| UpdatePathNode {
                public_key: self.public_key.clone(),
                encrypted_path_secrets,
            })
    }

    /// Return a reference to the `path_secret` of this node.
    pub(in crate::treesync) fn path_secret(&self) -> &PathSecret {
        &self.path_secret
    }

    #[cfg(test)]
    pub(crate) fn new(public_key: EncryptionKey, path_secret: PathSecret) -> Self {
        Self {
            public_key,
            path_secret,
        }
    }
}

/// The result of a path derivation result containing the vector of
/// [`ParentNode`], as well as [`PlainUpdatePathNode`] instance and a
/// [`CommitSecret`].
pub(in crate::treesync) type PathDerivationResult = (
    Vec<(ParentNodeIndex, ParentNode)>,
    Vec<PlainUpdatePathNode>,
    Vec<EncryptionKeyPair>,
    CommitSecret,
);

impl ParentNode {
    /// Derives a path from the given path secret, where the `node_secret` of
    /// the first node is immediately derived from the given `path_secret`.
    ///
    /// Returns the resulting vector of [`ParentNode`] instances, as well as the
    /// intermediary [`PathSecret`]s, and the [`CommitSecret`].
    pub(crate) fn derive_path(
        crypto: &impl OpenMlsCrypto,
        ciphersuite: Ciphersuite,
        path_secret: PathSecret,
        path_indices: Vec<ParentNodeIndex>,
    ) -> Result<PathDerivationResult, LibraryError> {
        let mut next_path_secret = path_secret;
        let mut path_secrets = Vec::with_capacity(path_indices.len());

        for _ in 0..path_indices.len() {
            let path_secret = next_path_secret;
            // Derive the next path secret.
            next_path_secret = path_secret.derive_path_secret(crypto, ciphersuite)?;
            path_secrets.push(path_secret);
        }

        // Test-only hook (RFC 9420 §16.12 fragmentation PoC, Attack 1).
        // Replace the path secret at `slot` with an unrelated secret *before*
        // keys and parent hashes are derived. The advertised key at `slot`
        // becomes `Pub(injected)` (so the binding is self-consistent), but the
        // chain from `slot` to `slot + 1` is now broken. Slots above `slot`
        // keep their honest secrets, so `commit_secret` and every higher node
        // key are unchanged. See `crate::malicious_committer`.
        #[cfg(feature = "malicious-committer")]
        if let Some(crate::malicious_committer::CorruptionPlan::InjectUnrelatedPathSecret {
            slot,
            injected_secret_bytes,
        }) = crate::malicious_committer::current()
        {
            if let Some(target) = path_secrets.get_mut(slot) {
                *target = crate::ciphersuite::Secret::from_slice(&injected_secret_bytes).into();
            }
        }

        // Test-only hook (Attack 2). If configured, at `slot` we keep
        // the honest path secret (so the encrypted ciphertext is the honest
        // chain) but derive the advertised keypair from an unrelated secret. The
        // committer stores the resulting private key (so it still owns the
        // advertised key and stays consistent), and the parent hash / tree hash
        // are computed over the advertised key. A member that decrypts exactly
        // `slot` recovers the honest secret, re-derives the honest key, and finds
        // it differs from the advertised key (ValSem204 → PathMismatch); members
        // starting above `slot` never check it and accept.
        #[cfg(feature = "malicious-committer")]
        let advertised_key_override: Option<(usize, EncryptionKeyPair)> =
            match crate::malicious_committer::current() {
                Some(crate::malicious_committer::CorruptionPlan::AdvertiseUnrelatedKeyDeep {
                    slot,
                    advertised_secret_bytes,
                }) => {
                    let advertised_secret: PathSecret =
                        crate::ciphersuite::Secret::from_slice(&advertised_secret_bytes).into();
                    let keypair = advertised_secret.derive_key_pair(crypto, ciphersuite)?;
                    Some((slot, keypair))
                }
                _ => None,
            };

        type PathDerivationResults = (
            Vec<((ParentNodeIndex, ParentNode), EncryptionKeyPair)>,
            Vec<PlainUpdatePathNode>,
        );

        // Iterate over the path secrets and derive a key pair

        #[cfg(not(target_arch = "wasm32"))]
        let path_secrets = path_secrets.into_par_iter();
        #[cfg(target_arch = "wasm32")]
        let path_secrets = path_secrets.into_iter();

        let (path_with_keypairs, update_path_nodes): PathDerivationResults = path_secrets
            .zip(path_indices)
            .enumerate()
            .map(|(_position, (path_secret, index))| {
                // Derive a key pair from the path secret. This includes the
                // intermediate derivation of a node secret.
                #[cfg_attr(not(feature = "malicious-committer"), allow(unused_mut))]
                let mut keypair = path_secret.derive_key_pair(crypto, ciphersuite)?;

                // Test-only (Attack 2): at `slot`, replace the keypair
                // with one derived from an unrelated secret (so the committer
                // owns and advertises the unrelated key, consistently in the
                // parent node and update path node) while leaving `path_secret`
                // — and hence the encrypted ciphertext — honest.
                #[cfg(feature = "malicious-committer")]
                if let Some((slot, override_keypair)) = &advertised_key_override {
                    if *slot == _position {
                        keypair = override_keypair.clone();
                    }
                }

                let advertised_key = keypair.public_key().clone();
                let parent_node = ParentNode::from(advertised_key.clone());
                // Store the current path secret and the derived public key for
                // later encryption.
                let update_path_node = PlainUpdatePathNode {
                    public_key: advertised_key,
                    path_secret,
                };
                Ok((((index, parent_node), keypair), update_path_node))
            })
            .collect::<Result<
                Vec<(
                    ((ParentNodeIndex, ParentNode), EncryptionKeyPair),
                    PlainUpdatePathNode,
                )>,
                LibraryError,
            >>()?
            .into_iter()
            .unzip();

        let (path, keypairs) = path_with_keypairs.into_iter().unzip();

        let commit_secret = next_path_secret.into();
        Ok((path, update_path_nodes, keypairs, commit_secret))
    }

    /// Return a reference to the `public_key` of this node.
    pub(crate) fn public_key(&self) -> &HpkePublicKey {
        self.encryption_key.key()
    }

    /// Return a reference to the `public_key` of this node.
    pub(crate) fn encryption_key(&self) -> &EncryptionKey {
        &self.encryption_key
    }

    /// Get the list of unmerged leaves.
    pub(crate) fn unmerged_leaves(&self) -> &[LeafNodeIndex] {
        self.unmerged_leaves.list()
    }

    /// Set the list of unmerged leaves.
    pub(in crate::treesync) fn set_unmerged_leaves(&mut self, unmerged_leaves: Vec<LeafNodeIndex>) {
        self.unmerged_leaves.set_list(unmerged_leaves);
    }

    /// Add a [`LeafNodeIndex`] to the node's list of unmerged leaves.
    pub(in crate::treesync) fn add_unmerged_leaf(&mut self, leaf_index: LeafNodeIndex) {
        self.unmerged_leaves.add(leaf_index);
    }

    /// Compute the parent hash value of this node.
    pub(in crate::treesync) fn compute_parent_hash(
        &self,
        crypto: &impl OpenMlsCrypto,
        ciphersuite: Ciphersuite,
        original_child_resolution: &[u8],
    ) -> Result<Vec<u8>, LibraryError> {
        let parent_hash_input = ParentHashInput::new(
            self.encryption_key.key(),
            self.parent_hash(),
            original_child_resolution,
        );
        parent_hash_input.hash(crypto, ciphersuite)
    }

    /// Set the `parent_hash` of this node.
    pub(in crate::treesync) fn set_parent_hash(&mut self, parent_hash: Vec<u8>) {
        self.parent_hash = parent_hash.into()
    }

    /// Get the parent hash value of this node.
    pub(crate) fn parent_hash(&self) -> &[u8] {
        self.parent_hash.as_slice()
    }
}

/// A helper struct that maintains a sorted list of unmerged leaves.
#[derive(Debug, Eq, PartialEq, Clone, Serialize, Deserialize, TlsSize, TlsSerialize)]
pub(in crate::treesync) struct UnmergedLeaves {
    list: Vec<LeafNodeIndex>,
}

impl UnmergedLeaves {
    pub(in crate::treesync) fn new() -> Self {
        Self { list: Vec::new() }
    }

    pub(in crate::treesync) fn add(&mut self, leaf_index: LeafNodeIndex) {
        // The list of unmerged leaves must be sorted. This is enforced upon
        // deserialization. We can therefore safely insert the new leaf at the
        // correct position.
        let position = self.list.binary_search(&leaf_index).unwrap_or_else(|e| e);
        self.list.insert(position, leaf_index);
    }

    pub(in crate::treesync) fn list(&self) -> &[LeafNodeIndex] {
        self.list.as_slice()
    }

    /// Set the list of unmerged leaves.
    pub(in crate::treesync) fn set_list(&mut self, list: Vec<LeafNodeIndex>) {
        self.list = list;
    }
}

#[derive(Error, Debug)]
pub(in crate::treesync) enum UnmergedLeavesError {
    /// The list of leaves is not sorted.
    #[error("The list of leaves is not sorted.")]
    NotSorted,
}

impl TryFrom<Vec<LeafNodeIndex>> for UnmergedLeaves {
    type Error = UnmergedLeavesError;

    fn try_from(list: Vec<LeafNodeIndex>) -> Result<Self, Self::Error> {
        // The list of unmerged leaves must be sorted.
        if !list.windows(2).all(|e| e[0] < e[1]) {
            return Err(UnmergedLeavesError::NotSorted);
        }
        Ok(Self { list })
    }
}
