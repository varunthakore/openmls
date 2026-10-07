//! RFC 9420 §16.12 group fragmentation PoC.
//!
//! # The attack
//!
//! An `UpdatePath` carries, for each node on the committer's filtered direct
//! path, an advertised HPKE `encryption_key` and the node's path secret
//! encrypted to the nodes in the resolution of the copath child. A receiver
//! decrypts the one path secret it is a recipient of, re-derives the node key
//! pairs up the chain, and checks that each derived public key matches the
//! advertised one (ValSem203 that the secret decrypts, ValSem204 that the keys
//! match).
//!
//! Crucially, a receiver can only verify the `UpdatePath` **from its own
//! subtree-root position with the committer upward** — the slots below that
//! position are encrypted to a subtree the receiver is not in, so it never
//! decrypts or checks them. This partial verification is inherent (RFC 9420
//! §16.12), not a bug. A malicious committer can therefore corrupt a *lower*
//! slot: the members positioned above it cannot see the corruption and accept,
//! while the one member positioned at that slot rejects. The result is a clean,
//! permanent group partition.
//!
//! To make the split *clean*, the malformation is injected *during* commit
//! creation (see [`crate::malicious_committer`]), so the confirmed transcript
//! hash and confirmation tag are computed over the already-malformed path.
//! Accepting members then accept completely — the confirmation tag verifies and
//! the epoch advances — while the victim is silently partitioned yet remains
//! listed as a group member. (Tampering with an honest commit *after* the fact
//! instead fails the confirmation tag for everyone, so it cannot produce a
//! split.)
//!
//! # Fixture
//!
//! ```text
//!                                   R
//!                      _____________|_____________
//!                     /                           \
//!                    X                             _
//!              ______|______                ______|______
//!             /             \              /             \
//!            U               V            W               _
//!           / \             / \          / \             / \
//!          A   B           C   D        E   F           _   _
//!
//! leaf:    0   1           2   3        4   5           6   7
//! ```
//!
//! C (leaf 2) is the attacker, performing a self-update commit (empty
//! proposals). C's filtered direct path is `V → X → R`; the three updated nodes
//! `V'`, `X'`, `R'` are slots 0, 1, 2 of the `UpdatePath`. Each other member can
//! only check from the slot at its lowest common ancestor with C upward:
//!
//! | Member | Subtree root with C | `path_position` | Slots checked |
//! |--------|---------------------|-----------------|---------------|
//! | D      | V                   | 0               | 0, 1, 2       |
//! | A, B   | X                   | 1               | 1, 2          |
//! | E, F   | R                   | 2               | 2             |
//!
//! Corrupting slot 0 (`V'`) therefore produces the detector set `{D}`.
//!
//! # The two malformations
//!
//! Both corrupt slot 0 (`V'`) and both yield detector set `{D}`:
//!
//! - **Attack 1 — unrelated path secret.** C injects an unrelated secret at
//!   `V'`, advertising a key consistent with it, but the derivation chain to
//!   `X'` is broken. D decrypts the injected secret, passes the key check at
//!   `V'`, then re-derives `X'` and fails there. (The surfaced failure is one
//!   slot *above* the corrupted slot.) A/B start from the honest `X'` secret and
//!   E/F from the honest `R'` secret, so both accept.
//! - **Attack 2 — key does not match its secret.** C keeps the honest encrypted
//!   path secret at `V'` but advertises an unrelated public key for it (one C
//!   still owns, so C stays consistent). D decrypts the honest secret, derives
//!   the honest `V'` key, and finds it differs from the advertised key. A/B and
//!   E/F never check `V'`, so they accept.

use openmls_traits::{
    storage::{StorageProvider, CURRENT_VERSION},
    types::Ciphersuite,
    OpenMlsProvider,
};

use crate::{
    binary_tree::LeafNodeIndex,
    ciphersuite::Secret,
    extensions::Extensions,
    framing::{ProcessedMessageContent, ProtocolMessage},
    group::{
        tests_and_kats::utils::{
            generate_credential_with_key, generate_key_package, CredentialWithKeyAndSigner,
        },
        *,
    },
    malicious_committer::{install, CorruptionPlan},
    treesync::{errors::ApplyUpdatePathError, node::Node, LeafNodeParameters},
};

/// Array-representation indices of the fixture's inner nodes.
/// Leaves live at even indices (`2 * leaf_index`), parents at odd indices.
const IDX_U: usize = 1; // parent of A(0), B(1)
const IDX_X: usize = 3; // parent of {A, B, C, D}
const IDX_V: usize = 5; // parent of C(2), D(3)
const IDX_R: usize = 7; // root
const IDX_W: usize = 9; // parent of E(4), F(5)
const IDX_RIGHT: usize = 11; // parent of the (blank) right subtree above W

type Provider = crate::test_utils::OpenMlsRustCrypto;

/// Storage error type of [`Provider`], needed to name [`ProcessMessageError`].
type StorageError = <<Provider as OpenMlsProvider>::StorageProvider as StorageProvider<
    CURRENT_VERSION,
>>::Error;

/// One member of the fixture, with its own provider (isolated key store).
struct Member {
    group: MlsGroup,
    cred: CredentialWithKeyAndSigner,
    provider: Provider,
}

/// Credential + provider for a not-yet-joined participant.
struct Identity {
    cred: CredentialWithKeyAndSigner,
    provider: Provider,
}

fn make_identity(name: &str, ciphersuite: Ciphersuite) -> Identity {
    let provider = Provider::default();
    let cred =
        generate_credential_with_key(name.into(), ciphersuite.signature_algorithm(), &provider);
    Identity { cred, provider }
}

/// Build the exact six-member fixture from the module docs and assert its shape.
///
/// Returns the six members in order `[A, B, C, D, E, F]` (leaves 0..=5).
fn build_fixture(ciphersuite: Ciphersuite) -> Vec<Member> {
    let identities: Vec<Identity> = ["A", "B", "C", "D", "E", "F"]
        .iter()
        .map(|n| make_identity(n, ciphersuite))
        .collect();

    // A creates the group.
    let mut members: Vec<Member> = Vec::with_capacity(6);
    let a_group = {
        let a = &identities[0];
        MlsGroup::new(
            &a.provider,
            &a.cred.signer,
            &MlsGroupCreateConfig::builder()
                .ciphersuite(ciphersuite)
                .build(),
            a.cred.credential_with_key.clone(),
        )
        .expect("A: create group")
    };
    let mut identities = identities.into_iter();
    let a_id = identities.next().unwrap();
    members.push(Member {
        group: a_group,
        cred: a_id.cred,
        provider: a_id.provider,
    });

    // Remaining identities to be added, in leaf order B, C, D, E, F.
    let pending: Vec<Identity> = identities.collect();
    for joiner_id in pending {
        add_member(ciphersuite, &mut members, joiner_id);
    }

    // Adds only populate the *committer's* (A's) direct path (U → X → R). V and
    // W are still blank. Populate them with honest self-updates by C (leaf 2,
    // path V → X → R) and E (leaf 4, path W → ... → R). See dump below.
    self_update(&mut members, 2);
    self_update(&mut members, 4);

    members
}

/// Member `idx` performs an honest self-update commit; everyone else processes
/// and merges it.
fn self_update(members: &mut [Member], idx: usize) {
    let (commit, _welcome, _group_info) = {
        let m = &mut members[idx];
        m.group
            .self_update(&m.provider, &m.cred.signer, LeafNodeParameters::default())
            .expect("self-update")
            .into_messages()
    };
    {
        let m = &mut members[idx];
        m.group
            .merge_pending_commit(&m.provider)
            .expect("committer: merge self-update");
    }
    let commit_msg: ProtocolMessage = commit.into_protocol_message().unwrap();
    for (i, m) in members.iter_mut().enumerate() {
        if i == idx {
            continue;
        }
        let processed = m
            .group
            .process_message(&m.provider, commit_msg.clone())
            .expect("member: process self-update");
        match processed.into_content() {
            ProcessedMessageContent::StagedCommitMessage(sc) => {
                m.group
                    .merge_staged_commit(&m.provider, *sc)
                    .expect("member: merge self-update");
            }
            other => panic!("expected staged commit, got {other:?}"),
        }
    }
}

/// A (leaf 0) adds `joiner_id` to the group; all existing members merge and the
/// joiner joins from the welcome. Adds always go through A so leaves fill in a
/// deterministic order.
fn add_member(ciphersuite: Ciphersuite, members: &mut Vec<Member>, joiner_id: Identity) {
    let kp = generate_key_package(
        ciphersuite,
        Extensions::empty(),
        &joiner_id.provider,
        joiner_id.cred.clone(),
    )
    .key_package()
    .clone();

    // A creates the add commit and merges.
    let (commit, welcome, _group_info) = {
        let a = &mut members[0];
        a.group
            .add_members(&a.provider, &a.cred.signer, &[kp])
            .expect("A: add member")
    };
    {
        let a = &mut members[0];
        a.group
            .merge_pending_commit(&a.provider)
            .expect("A: merge add");
    }

    // Existing members (except A) process and merge the same commit.
    let commit_msg: ProtocolMessage = commit.into_protocol_message().unwrap();
    for m in members.iter_mut().skip(1) {
        let processed = m
            .group
            .process_message(&m.provider, commit_msg.clone())
            .expect("member: process add commit");
        match processed.into_content() {
            ProcessedMessageContent::StagedCommitMessage(sc) => {
                m.group
                    .merge_staged_commit(&m.provider, *sc)
                    .expect("member: merge add commit");
            }
            other => panic!("expected staged commit, got {other:?}"),
        }
    }

    // The joiner joins from the welcome.
    let welcome = welcome.into_welcome().expect("expected welcome");
    let ratchet_tree = members[0].group.export_ratchet_tree();
    let joiner_group = StagedWelcome::new_from_welcome(
        &joiner_id.provider,
        &MlsGroupJoinConfig::default(),
        welcome,
        Some(ratchet_tree.into()),
    )
    .expect("joiner: stage welcome")
    .into_group(&joiner_id.provider)
    .expect("joiner: into group");

    members.push(Member {
        group: joiner_group,
        cred: joiner_id.cred,
        provider: joiner_id.provider,
    });
}

fn is_leaf(node: Option<&Node>) -> bool {
    matches!(node, Some(Node::LeafNode(_)))
}

fn is_parent(node: Option<&Node>) -> bool {
    matches!(node, Some(Node::ParentNode(_)))
}

/// Assert that A's exported tree has exactly the fixture shape from the module
/// docs: leaves A–F populated (leaves 6, 7 absent/blank), parents U, X, V, R, W
/// populated, and no right subtree above W. The attack analysis depends on this
/// shape (in particular that W is non-blank, so slot 2's resolution is `[W]`),
/// so we assert it loudly rather than assuming it.
fn assert_tree_shape(members: &[Member]) {
    let tree = members[0].group.export_ratchet_tree();

    // Six leaves, so the array representation has 11 slots (2 * 6 - 1). Leaves
    // 6 and 7 do not exist yet, and there is no right subtree above W.
    assert_eq!(tree.slots_len(), 11, "tree must have exactly 6 leaves");

    // Leaves A..F at even indices.
    for (leaf, idx) in (0..6).map(|l| (l, 2 * l)) {
        assert!(is_leaf(tree.node_at(idx)), "leaf {leaf} must be populated");
    }

    // Populated inner nodes.
    assert!(is_parent(tree.node_at(IDX_U)), "U must be populated");
    assert!(is_parent(tree.node_at(IDX_X)), "X must be populated");
    assert!(is_parent(tree.node_at(IDX_V)), "V must be populated");
    assert!(is_parent(tree.node_at(IDX_R)), "R (root) must be populated");
    assert!(
        is_parent(tree.node_at(IDX_W)),
        "W must be populated (slot 2's resolution must be [W], not [E, F])"
    );

    // No right subtree above W.
    assert!(
        tree.node_at(IDX_RIGHT).is_none(),
        "the right subtree above W must be blank"
    );
}

#[openmls_test::openmls_test]
fn fixture_shape() {
    let members = build_fixture(ciphersuite);
    assert_tree_shape(&members);
}

/// Leaf indices, for readability.
const A: usize = 0;
const B: usize = 1;
const C: usize = 2; // attacker
const D: usize = 3;
const E: usize = 4;
const F: usize = 5;

/// Outcome of delivering C's malicious commit to a single member.
#[derive(Debug)]
enum Outcome {
    /// Member accepted the commit and advanced to the next epoch.
    Accepted,
    /// Member rejected the commit with the given processing error.
    Rejected(ProcessMessageError<StorageError>),
}

/// Run C's malicious self-update under `plan`, deliver the resulting commit to
/// every other member, and return each member's outcome (indexed by leaf).
///
/// The corruption plan is installed only for the duration of C's commit
/// creation; the returned guard is dropped before delivery, so nothing else is
/// corrupted. C then merges its own (locally honest) pending commit so that it
/// remains a functioning member (asserted by the callers).
fn run_attack(members: &mut [Member], plan: CorruptionPlan) -> Vec<Option<Outcome>> {
    let epoch_before = members[A].group.epoch();

    // C creates the malicious self-update with the plan installed.
    let commit = {
        let guard = install(plan);
        let c = &mut members[C];
        let (commit, _welcome, _gi) = c
            .group
            .self_update(&c.provider, &c.cred.signer, LeafNodeParameters::default())
            .expect("C: create malicious self-update")
            .into_messages();
        drop(guard); // clear the plan before anyone processes the commit
        commit
    };

    // C merges its own pending commit. Both malformations keep C's own stored
    // key material self-consistent (Attack 1 derives V' from the injected
    // secret C keeps; Attack 2 derives V' from the unrelated secret C keeps),
    // so C's merge succeeds and C stays a functioning member.
    {
        let c = &mut members[C];
        c.group
            .merge_pending_commit(&c.provider)
            .expect("C: merge own commit");
    }

    let commit_msg: ProtocolMessage = commit.into_protocol_message().unwrap();

    let mut outcomes: Vec<Option<Outcome>> = (0..members.len()).map(|_| None).collect();
    for i in 0..members.len() {
        if i == C {
            continue;
        }
        let msg = commit_msg.clone();
        let m = &mut members[i];
        let outcome = match m.group.process_message(&m.provider, msg) {
            Ok(processed) => match processed.into_content() {
                ProcessedMessageContent::StagedCommitMessage(sc) => {
                    m.group
                        .merge_staged_commit(&m.provider, *sc)
                        .expect("member: merge accepted commit");
                    Outcome::Accepted
                }
                other => panic!("expected staged commit, got {other:?}"),
            },
            Err(e) => Outcome::Rejected(e),
        };
        outcomes[i] = Some(outcome);
    }

    // Sanity: attacker advanced exactly one epoch.
    assert_eq!(
        members[C].group.epoch().as_u64(),
        epoch_before.as_u64() + 1,
        "attacker C must advance one epoch"
    );

    outcomes
}

/// Assert that the member at `leaf` accepted the commit.
fn assert_accepted(outcomes: &[Option<Outcome>], leaf: usize) {
    match &outcomes[leaf] {
        Some(Outcome::Accepted) => {}
        other => panic!("leaf {leaf} expected to ACCEPT, got {other:?}"),
    }
}

/// Assert that `member` rejected, and return the error for further inspection.
fn assert_rejected(
    outcomes: &[Option<Outcome>],
    leaf: usize,
) -> &ProcessMessageError<StorageError> {
    match &outcomes[leaf] {
        Some(Outcome::Rejected(e)) => e,
        other => panic!("leaf {leaf} expected to REJECT, got {other:?}"),
    }
}

/// The whole point: after the attack, the accepting members and the victim
/// disagree about the epoch, the victim is still listed as a member, and the
/// accepting members share one epoch. `victim` is the partitioned leaf.
fn assert_clean_partition(members: &[Member], victim: usize) {
    let accepting: Vec<usize> = (0..members.len()).filter(|&i| i != victim).collect();

    // All accepting members are at the same epoch.
    let epoch = members[accepting[0]].group.epoch().as_u64();
    for &i in &accepting {
        assert_eq!(
            members[i].group.epoch().as_u64(),
            epoch,
            "accepting member {i} epoch mismatch"
        );
    }

    // The victim is one epoch behind (still at the pre-commit epoch).
    assert_eq!(
        members[victim].group.epoch().as_u64() + 1,
        epoch,
        "victim {victim} must be exactly one epoch behind"
    );

    // The victim is still listed as a member by every accepting member: this is
    // a covert removal that leaves the victim visibly in the group.
    let victim_leaf = LeafNodeIndex::new(victim as u32);
    for &i in &accepting {
        let present = members[i]
            .group
            .members()
            .any(|m| m.index == victim_leaf);
        assert!(
            present,
            "victim {victim} must still be listed as a member by {i}"
        );
    }
}

// ---------------------------------------------------------------------------
// Attack 2: advertised key does not match its path secret (see module docs).
//
// The encrypted path secrets remain the honest chain, but the advertised
// `encryption_key` at slot 0 (V') is replaced by an unrelated key. D decrypts
// `path_secret_V`, derives the honest `node_pub_V'`, and rejects because it
// differs from the advertised key (ValSem204 → PathMismatch). A/B (checking
// from slot 1) and E/F (checking from slot 2) never examine slot 0, so they
// accept. Detector set: {D}.
// ---------------------------------------------------------------------------
#[openmls_test::openmls_test]
fn attack2_advertise_unrelated_key() {
    let mut members = build_fixture(ciphersuite);
    assert_tree_shape(&members);

    // An unrelated secret whose derived key C advertises at V' (C keeps the
    // matching private key). The encrypted ciphertext at V' stays honest.
    let advertised_secret = Secret::random(ciphersuite, members[C].provider.rand())
        .expect("random secret")
        .as_slice()
        .to_vec();
    let outcomes = run_attack(
        &mut members,
        CorruptionPlan::AdvertiseUnrelatedKeyDeep {
            slot: 0, // V'
            advertised_secret_bytes: advertised_secret,
        },
    );

    // D is the sole detector; everyone else accepts.
    let d_err = assert_rejected(&outcomes, D);
    assert!(
        matches!(
            d_err,
            ProcessMessageError::InvalidCommit(StageCommitError::UpdatePathError(
                ApplyUpdatePathError::PathMismatch
            ))
        ),
        "D should reject with PathMismatch (ValSem204), got {d_err:?}"
    );
    for leaf in [A, B, E, F] {
        assert_accepted(&outcomes, leaf);
    }

    assert_clean_partition(&members, D);
}

// ---------------------------------------------------------------------------
// Attack 1: unrelated path secret (see module docs).
//
// C injects an unrelated `path_secret_V*` at slot 0 *before* keys are derived,
// so the advertised key at V' is `Pub(path_secret_V*)` (self-consistent) but
// `DeriveSecret(path_secret_V*, "path") != path_secret_X`. D passes the binding
// check at V' and fails one slot higher (at X'); A/B start from the honest
// `path_secret_X` and E/F from `path_secret_R`, so both accept.
// Detector set: {D}. Note the surfaced failure is at the *next* slot up.
// ---------------------------------------------------------------------------
#[openmls_test::openmls_test]
fn attack1_unrelated_path_secret() {
    let mut members = build_fixture(ciphersuite);
    assert_tree_shape(&members);

    // Unrelated secret of one hash length.
    let injected = Secret::random(ciphersuite, members[C].provider.rand())
        .expect("random secret")
        .as_slice()
        .to_vec();

    let outcomes = run_attack(
        &mut members,
        CorruptionPlan::InjectUnrelatedPathSecret {
            slot: 0, // V'
            injected_secret_bytes: injected,
        },
    );

    // D is the sole detector; everyone else accepts.
    let d_err = assert_rejected(&outcomes, D);
    assert!(
        matches!(
            d_err,
            ProcessMessageError::InvalidCommit(StageCommitError::UpdatePathError(
                ApplyUpdatePathError::PathMismatch
            ))
        ),
        "D should reject with PathMismatch, got {d_err:?}"
    );
    for leaf in [A, B, E, F] {
        assert_accepted(&outcomes, leaf);
    }

    assert_clean_partition(&members, D);
}
