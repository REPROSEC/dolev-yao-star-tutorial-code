module DY.OnlineA.Properties

open Comparse
open DY.Core
open DY.Lib
open DY.Simplified
open DY.Extend

open DY.OnlineA.Data
open DY.OnlineA.Invariants

/// This is the new property, we want to show:
/// if Alice finishes a run identified by Bob and a nonce n_a,
/// then this Bob was involved in the run,
/// i.e., Bob sent n_a in an acknowledgement to Alice.
/// Unless one of Alice or Bob are corrupt.

val responder_authentication:
  tr:trace -> ts:timestamp ->
  alice:principal -> bob:principal ->
  n_a:bytes ->
  Lemma
  (requires
     trace_invariant tr /\
     event_triggered_at tr ts alice (Finishing {alice; bob; n_a})
  )
  (ensures
     principal_is_corrupt tr alice \/ principal_is_corrupt tr bob \/
     event_triggered (prefix tr ts) bob (Responding {alice; bob; n_a})
  )
let responder_authentication tr ts alice bob n_a = ()


/// We still have nonce secrecy:

val n_a_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes ->
  Lemma
  (requires
    trace_invariant tr /\ (
      (state_was_set_some_id tr alice (SentPing {bob; n_a})) \/
      (state_was_set_some_id tr alice (ReceivedAck {bob; n_a} ))
    ) /\
    attacker_knows tr n_a
  )
  (ensures principal_is_corrupt tr alice \/ principal_is_corrupt tr bob)
let n_a_secrecy tr alice bob n_a =
  attacker_only_knows_publishable_values tr n_a
