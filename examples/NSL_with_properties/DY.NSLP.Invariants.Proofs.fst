module DY.NSLP.Invariants.Proofs

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.NSLP.Data
open DY.NSLP.Protocol
open DY.NSLP.Invariants

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

/// In this module, we show that
/// the protocol steps maintain the protocol invariants.
///
/// For every step s we show a lemma of the form:
/// trace_invariant tr ==> trace_invariant ( trace after step s )

(*** Sending the First Message ***)


val send_msg1_invariant:
  alice:principal -> bob:principal -> alice_public_keys_sid:state_id ->
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = send_msg1 alice bob alice_public_keys_sid tr in
    trace_invariant tr_out
  ))
let send_msg1_invariant alice bob alice_public_keys_sid tr =
  let (n_a, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
  let (_, tr_ev) = trigger_event alice (Initiating {alice; bob; n_a}) tr_rand in
  let msg1 = Msg1 {alice; n_a} in 
  serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_ev) msg1;
  pke_enc_for_is_publishable tr_ev alice bob alice_public_keys_sid key_tag msg1

(*** Sending the Second Message ***)


val decode_msg1_invariant:
  bob:principal -> bob_private_keys_sid:state_id ->
  msg:bytes ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = decode_msg1 bob bob_private_keys_sid msg tr in
    trace_invariant tr_out
  ))
let decode_msg1_invariant bob bob_private_keys_sid msg tr = ()


val receive_msg1_and_send_msg2_invariant:
  bob:principal -> 
  bob_private_keys_sid:state_id -> bob_public_keys_sid:state_id ->
  msg_ts:timestamp -> 
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = receive_msg1_and_send_msg2 bob bob_private_keys_sid bob_public_keys_sid msg_ts tr in
    trace_invariant tr_out
  ))
let receive_msg1_and_send_msg2_invariant bob bob_private_keys_sid bob_public_keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _ ) -> ()
  | (Some msg, _) -> (
      match decode_msg1 bob bob_private_keys_sid msg tr with
      | (None, _) -> ()
      | (Some {alice; n_a}, tr_decode) -> (
          assert(trace_invariant tr_decode);
          let (n_b, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
          assert(trace_invariant tr_rand);
          let (_, tr_ev) = trigger_event bob (Responding1 {alice; bob; n_a; n_b}) tr_rand in
          assert(trace_invariant tr_ev);
          let msg2 = Msg2 {bob; n_a; n_b} in
          match pke_enc_for bob alice bob_public_keys_sid key_tag msg2 tr_ev with
          | (None, _) -> ()
          | (Some msg2_encrypted, tr_msg2) ->(
              assert(trace_invariant tr_msg2);
              let (msg2_ts, tr_msg2) = send_msg msg2_encrypted tr_msg2 in
              assume(trace_invariant tr_msg2);
              let state = SentMsg2 {alice; n_a; n_b} in
              let (sess_id, tr_sess) = start_new_session bob state tr_msg2 in
              assume(trace_invariant tr_sess)
          )
      )
  )

(*** Sending the Third Message ***)

(*** Receiving the Final Message ***)
