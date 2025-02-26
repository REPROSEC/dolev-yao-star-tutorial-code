module DY.NSLP.Properties

open Comparse
open DY.Core
open DY.Lib
open DY.Extend
open DY.Simplified

open DY.NSLP.Data
open DY.NSLP.Invariants

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module defines the security properties of the NSL protocol:
/// * secrecy of both nonces
/// * authentication of both participants


/// The nonce n_a is unknown to the attacker,
/// unless the attacker corrupted Alice or Bob.

val n_a_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes ->
  Lemma
  (requires
    attacker_knows tr n_a /\
    trace_invariant tr /\ (
      (state_was_set_some_id tr alice (SentMsg1 {bob; n_a})) \/
      (exists n_b. state_was_set_some_id tr alice (SentMsg3 {bob; n_a; n_b})) \/
      (exists n_b. state_was_set_some_id tr bob (ReceivedMsg3 {alice; n_a; n_b}))
    )
  )
  (ensures principal_is_corrupt tr alice \/ principal_is_corrupt tr bob)
let n_a_secrecy tr alice bob n_a =
  attacker_only_knows_publishable_values tr n_a

/// The nonce n_b is unknown to the attacker,
/// unless the attacker corrupted Alice or Bob.

val n_b_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_b:bytes ->
  Lemma
  (requires
    attacker_knows tr n_b /\
    trace_invariant tr /\ (
      (exists n_a. state_was_set_some_id tr bob (SentMsg2 {alice; n_a; n_b})) \/
      (exists n_a. state_was_set_some_id tr bob (ReceivedMsg3 {alice; n_a; n_b})) \/
      (exists n_a. state_was_set_some_id tr alice (SentMsg3 {bob; n_a; n_b}))
    )
  )
  (ensures principal_is_corrupt tr alice \/ principal_is_corrupt tr bob)
let n_b_secrecy tr alice bob n_b =
  attacker_only_knows_publishable_values tr n_b


/// If Bob thinks he talks with Alice,
/// then Alice thinks she talks to Bob (with the same nonces),
/// unless the attacker corrupted Alice or Bob.

val initiator_authentication:
  tr:trace -> ts:timestamp ->
  alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes ->
  Lemma
  (requires
    event_triggered_at tr ts bob (Finishing {alice; bob; n_a; n_b}) /\
    trace_invariant tr
  )
  (ensures
    principal_is_corrupt tr alice \/
    principal_is_corrupt tr bob \/ (
      event_triggered_before tr ts alice (Responding2 {alice; bob; n_a; n_b}) /\
      event_triggered_before tr ts alice (Initiating {alice; bob; n_a})
    )
  )
let initiator_authentication tr ts alice bob n_a n_b = ()

/// If Alice thinks she talks with Bob,
/// then Bob thinks he talks to Alice (with the same nonces),
/// unless the attacker corrupted Alice or Bob.

val responder_authentication:
  tr:trace -> ts:timestamp ->
  alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes ->
  Lemma
  (requires
    event_triggered_at tr ts alice (Responding2 {alice; bob; n_a; n_b}) /\
    trace_invariant tr
  )
  (ensures
    principal_is_corrupt tr alice \/
    principal_is_corrupt tr bob \/
    event_triggered_before tr ts bob (Responding1 {alice; bob; n_a; n_b})
  )
let responder_authentication tr ts alice bob n_a n_b = ()
