module DY.OnlineS.Secrecy

open Comparse
open DY.Core
open DY.Lib

open DY.OnlineS.Data
open DY.OnlineS.Invariants


/// A secrecy property on the nonce.
/// If the attacker knows a nonce that is stored in one of Alice's states,
/// he must have corrupted one of Alice or Bob.
///
/// In other words:
/// As long as Alice and Bob are not corrupted,
/// the attacker doesn't know the nonce stored in one of Alice's states.

/// We show that the property follows from the protocol invariants.
/// I.e., any trace satisfying the protocol invariants has the secrecy property.
/// 
/// This is independent of how that trace was generated (or if such a trace even exists).
/// To show that the Online? Protocol satisfies the secrecy property,
/// we need to show that
/// each protocol step maintains the invariants (see DY.OnlineS.Invariants.Proof).

val n_a_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes ->
  Lemma
  (requires
    attacker_knows tr n_a /\
    trace_invariant tr /\ (
      (exists sess_id. state_was_set tr alice sess_id (SentPing {bob; n_a})) \/
      (exists sess_id. state_was_set tr alice sess_id (ReceivedAck {bob; n_a} ))
    )
  )
  (ensures is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob))

/// The proof idea is the following:
/// For any nonce stored in one of Alice's states (SentPing or ReceivedAck)
/// together with Bob,
/// we get from the state predicate in the protocol invariants,
/// that the nonce is labeled for exactly Alice and Bob.
///
/// This immediately means that one of Alice or Bob must be corrupted,
/// if the attacker knows the nonce.
/// The proof thus only consists of calling the main attacker lemma
/// `attacker_only_knows_publishable_values`.
let n_a_secrecy tr alice bob n_a =
  attacker_only_knows_publishable_values tr n_a
