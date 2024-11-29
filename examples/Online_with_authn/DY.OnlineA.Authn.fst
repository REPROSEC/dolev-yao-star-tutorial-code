module DY.OnlineA.Authn

open Comparse
open DY.Core
open DY.Lib

open DY.Extend

open DY.OnlineA.Data
open DY.OnlineA.Invariants

val authn:
  tr:trace -> 
  alice:principal -> bob:principal ->
  n_a:bytes ->
  Lemma
  (requires
     trace_invariant tr /\
     state_was_set_some_id tr alice (ReceivedAck {bob; n_a})
  )
  (ensures
     is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
     state_was_set_some_id tr bob (SendingAck {alice; n_a})
  )
let authn tr alice bob n_a = ()
