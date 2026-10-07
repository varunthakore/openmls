//! Test-only hook for injecting a malformed `UpdatePath` during commit creation.
//!
//! This module exists to demonstrate RFC 9420 §16.12 group fragmentation: a
//! malicious committer can craft an `UpdatePath` that a *chosen* member rejects
//! (at ValSem203/204) while every other member accepts and advances the epoch,
//! producing a silent, permanent partition.
//!
//! The corruption must be injected *during* commit creation (not by post-hoc
//! tampering), so that the confirmed transcript hash and the confirmation tag
//! are computed over the already-malformed path. Otherwise every honest member
//! would reject at the confirmation-tag check (ValSem205) instead of the
//! partial split we want to demonstrate.
//!
//! The plan is stored in a thread-local so a test can configure it without
//! changing any function signatures. It is entirely compiled out unless the
//! `malicious-committer` feature is enabled, and it does nothing unless a test
//! installs a plan.
//!
//! `slot` is the index into the committer's filtered direct path (`0` = the
//! node closest to the committer's leaf). See the `fragmentation` tests for the
//! full attack description and fixture.

use std::cell::RefCell;

/// Which malformation to inject, and where.
///
/// `slot` is the index into the committer's filtered direct path (`0` = the
/// node closest to the committer's leaf).
#[derive(Clone, Debug)]
pub enum CorruptionPlan {
    /// Attack 2 — advertised key does not match its secret: the advertised key
    /// at `slot` is derived from an unrelated secret (which the committer keeps,
    /// so the committer still owns the advertised key and stays consistent), but
    /// the *encrypted* path secret at `slot` remains the honest one. Applied
    /// during key derivation so the parent hash and tree hash are computed
    /// consistently over the unrelated key.
    ///
    /// A member that decrypts exactly `slot` recovers the honest secret, derives
    /// the honest node key, and finds it differs from the advertised key
    /// (ValSem204 → `PathMismatch`). Members starting above `slot` never check it
    /// and accept. The committer, deriving the same key from the same unrelated
    /// secret, stores the matching private key and stays a functioning member.
    ///
    /// Applied *inside* `ParentNode::derive_path`.
    AdvertiseUnrelatedKeyDeep {
        /// Index into the committer's filtered direct path to corrupt.
        slot: usize,
        /// Raw bytes of the unrelated secret whose derived key is advertised at
        /// `slot` (one ciphersuite hash length). The committer keeps the
        /// resulting keypair; the encrypted ciphertext at `slot` stays honest.
        advertised_secret_bytes: Vec<u8>,
    },

    /// Attack 1 — unrelated path secret: the path secret at `slot` is replaced
    /// by an unrelated secret *before* keys and parent hashes are derived, so
    /// the advertised key at `slot` is `Pub(injected_secret)` (self-consistent),
    /// but `DeriveSecret(injected_secret, "path")` no longer equals the next
    /// slot's secret. A member that decrypts exactly `slot` passes the binding
    /// check at `slot` and fails one slot higher; members starting above `slot`
    /// see only the honest upper chain and accept.
    ///
    /// Applied *inside* `ParentNode::derive_path`, replacing the secret used to
    /// seed the chain at `slot`.
    ///
    /// The secret is carried as raw bytes (one hash length for the ciphersuite)
    /// so this plan stays `Clone` without depending on the library's internal
    /// `PathSecret` type being clonable outside of tests.
    InjectUnrelatedPathSecret {
        /// Index into the committer's filtered direct path to corrupt.
        slot: usize,
        /// Raw bytes of the unrelated path secret to inject at `slot`
        /// (one ciphersuite hash length).
        injected_secret_bytes: Vec<u8>,
    },
}

thread_local! {
    static PLAN: RefCell<Option<CorruptionPlan>> = const { RefCell::new(None) };
}

/// Install a corruption plan for the current thread. The next commit created on
/// this thread will be malformed accordingly. Returns a guard that clears the
/// plan when dropped, so a test cannot accidentally leak corruption into a
/// later commit.
#[must_use]
pub fn install(plan: CorruptionPlan) -> PlanGuard {
    PLAN.with(|p| *p.borrow_mut() = Some(plan));
    PlanGuard(())
}

/// Clear any installed plan on the current thread.
pub fn clear() {
    PLAN.with(|p| *p.borrow_mut() = None);
}

/// Read a clone of the currently installed plan, if any.
pub(crate) fn current() -> Option<CorruptionPlan> {
    PLAN.with(|p| p.borrow().clone())
}

/// Dropping this guard clears the installed plan. See [`install`].
pub struct PlanGuard(());

impl Drop for PlanGuard {
    fn drop(&mut self) {
        clear();
    }
}
