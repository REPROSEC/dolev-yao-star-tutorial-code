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


val decode_msg1_proof:
  bob:principal -> bob_private_keys_sid:state_id ->
  msg:bytes ->
  tr:trace ->
  Lemma
    (requires 
       trace_invariant tr /\
       bytes_invariant tr msg
    )
    (ensures (
      match decode_msg1 bob bob_private_keys_sid msg tr with
      | (None, _) -> True
      | (Some msg1, _) -> (
          let n_a = msg1.n_a in
          let alice = msg1.alice in
          is_knowable_by (nonce_label alice bob) tr n_a
        )
    ))
let decode_msg1_proof bob bob_private_keys_sid msg tr =
      match decode_msg1 bob bob_private_keys_sid msg tr with
      | (None, _) -> ()
      | (Some msg1, _) -> (
          bytes_invariant_pke_dec_with_key_lookup tr #message_t #parseable_serializeable_bytes_message_t bob bob_private_keys_sid key_tag msg;
          let plain = serialize message_t (Msg1 msg1) in
          parse_wf_lemma message_t (bytes_invariant tr) plain;
          FStar.Classical.move_requires (parse_wf_lemma message_t (is_publishable tr)) plain
  )

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
      | (Some {alice; n_a}, _) -> (
          let (n_b, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
          assert(trace_invariant tr_rand);
          let (_, tr_ev) = trigger_event bob (Responding1 {alice; bob; n_a; n_b}) tr_rand in
          assert(trace_invariant tr_ev);
          let msg2 = Msg2 {bob; n_a; n_b} in
          match pke_enc_for bob alice bob_public_keys_sid key_tag msg2 tr_ev with
          | (None, _) -> ()
          | (Some msg2_encrypted, tr_msg2) ->(
              assert(trace_invariant tr_msg2);
              let (msg2_ts, tr_msg2_) = send_msg msg2_encrypted tr_msg2 in
              decode_msg1_proof bob bob_private_keys_sid msg tr;
              serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_rand) msg2;
              pke_enc_for_is_publishable tr_ev bob alice bob_public_keys_sid key_tag msg2;
              assert(trace_invariant tr_msg2_);
              let state = SentMsg2 {alice; n_a; n_b} in
              let (sess_id, tr_sess) = start_new_session bob state tr_msg2_ in
              assert(trace_invariant tr_sess)
          )
      )
  )

(*** Sending the Third Message ***)

val decode_msg2_invariant:
  alice:principal -> alice_private_keys_sid:state_id ->
  msg:bytes ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = decode_msg2 alice alice_private_keys_sid msg tr in
    trace_invariant tr_out
  ))
let decode_msg2_invariant alice alice_private_keys_sid msg tr = ()

val decode_msg2_proof:
  alice:principal -> alice_private_keys_sid:state_id ->
  msg:bytes ->
  tr:trace ->
  Lemma
    (requires 
       trace_invariant tr /\
       bytes_invariant tr msg
    )
    (ensures (
      match decode_msg2 alice alice_private_keys_sid msg tr with
      | (None, _) -> True
      | (Some msg2, _) -> (
          let bob = msg2.bob in
          let n_a = msg2.n_a in
          let n_b = msg2.n_b in
          is_knowable_by (nonce_label alice bob) tr n_b /\
          ( is_publishable tr n_a \/
            event_triggered tr bob (Responding1 {alice; bob; n_a; n_b}))
       )
    ))
let decode_msg2_proof alice alice_private_keys_sid msg tr =
  match decode_msg2 alice alice_private_keys_sid msg tr with
  | (None, _) -> ()
  | (Some msg2, _) -> (
      bytes_invariant_pke_dec_with_key_lookup tr #message_t #parseable_serializeable_bytes_message_t alice alice_private_keys_sid key_tag msg;
      let plain = serialize message_t (Msg2 msg2) in
      parse_wf_lemma message_t (bytes_invariant tr) plain;
      FStar.Classical.move_requires (parse_wf_lemma message_t (is_publishable tr)) plain
  )  

#push-options "--z3rlimit 50"
val receive_msg2_and_send_msg3_invariant:
  alice:principal -> 
  alice_private_keys_sid:state_id -> alice_public_keys_sid:state_id ->
  msg_ts:timestamp -> 
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = receive_msg2_and_send_msg3 alice alice_private_keys_sid alice_public_keys_sid msg_ts tr in
    trace_invariant tr_out
  ))
let receive_msg2_and_send_msg3_invariant alice alice_private_keys_sid alice_public_keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _) -> ()
  | (Some msg2_, _) -> (
      match decode_msg2 alice alice_private_keys_sid msg2_ tr with
      | (None, _ ) -> ()
      | (Some msg2, _) -> (
            let bob = msg2.bob in
            let n_a = msg2.n_a in
            let n_b = msg2.n_b in

            let p = (fun (st:state_t) -> 
                        SentMsg1? st
                    && (SentMsg1?.sentmsg1 st).n_a = n_a
                    && (SentMsg1?.sentmsg1 st).bob = bob
                    ) in
            match lookup_state #state_t alice p tr with
            | (None, _) -> ()
            | (Some (sid, st), _ ) -> (
                 let ((), tr_ev) = trigger_event alice (Responding2 {alice; bob; n_a; n_b}) tr in
                 decode_msg2_proof alice alice_private_keys_sid msg2_ tr;
                 assert(trace_invariant tr_ev);
                 let msg3 = Msg3 {n_b} in
                 match pke_enc_for alice bob alice_public_keys_sid key_tag msg3 tr_ev with
                 | (None, _ ) -> ()
                 | (Some msg3_encrypted, tr_enc) -> (
                      assert(trace_invariant tr_enc);
                      let (_, tr_msg3) = send_msg msg3_encrypted tr_enc in
                      serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr) msg3;
                      pke_enc_for_is_publishable tr_ev alice bob alice_public_keys_sid key_tag msg3; 
                      assert(trace_invariant tr_msg3);
                      let state = SentMsg3 {bob; n_a; n_b} in
                      let ((), tr_st) = set_state alice sid state tr_msg3 in
                      assert(trace_invariant tr_st)
                 )
            )
      )
  )
#pop-options

(*** Receiving the Final Message ***)


val decode_msg3_invariant:
  bob:principal -> bob_private_keys_sid:state_id ->
  msg:bytes ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = decode_msg3 bob bob_private_keys_sid msg tr in
    trace_invariant tr_out
  ))
let decode_msg3_invariant bob bob_private_keys_sid msg tr = ()

val decode_msg3_proof:
  bob:principal -> bob_private_keys_sid:state_id ->
  msg:bytes ->
  tr:trace ->
  Lemma
    (requires 
       trace_invariant tr /\
       bytes_invariant tr msg
    )
    (ensures (
      match decode_msg3 bob bob_private_keys_sid msg tr with
      | (None, _) -> True
      | (Some msg3, _) -> (
           let n_b = msg3.n_b in
           is_publishable tr n_b \/ (
              exists alice n_a.
                  get_label tr n_b `can_flow tr` (nonce_label alice bob) /\
                  event_triggered tr alice (Responding2 {alice; bob; n_a; n_b})
           )
        )
    ))
let decode_msg3_proof bob bob_private_keys_sid msg tr = 
  match decode_msg3 bob bob_private_keys_sid msg tr with
  | (None, _) -> ()
  | (Some msg3, _) -> (
      bytes_invariant_pke_dec_with_key_lookup tr #message_t #parseable_serializeable_bytes_message_t bob bob_private_keys_sid key_tag msg;
      let plain = serialize message_t (Msg3 msg3) in
      parse_wf_lemma message_t (bytes_invariant tr) plain;
      FStar.Classical.move_requires (parse_wf_lemma message_t (is_publishable tr)) plain
  )  

val receive_msg3_invariant:
  bob:principal ->
  bob_private_keys_sid:state_id ->
  msg_ts:timestamp ->
  tr:trace ->
  Lemma
    (requires
      trace_invariant tr
    )
    (ensures (
      let (_, tr_out) = receive_msg3 bob bob_private_keys_sid msg_ts tr in
      trace_invariant tr_out
    ))
let receive_msg3_invariant bob bob_private_keys_sid msg_ts tr = 
  match recv_msg msg_ts tr with
  | (None, _ ) -> ()
  | (Some msg3_, _) -> (
       match decode_msg3 bob bob_private_keys_sid msg3_ tr with
       | (None, _ ) -> ()
       | (Some msg3, _) -> (
            let n_b = msg3.n_b in
            let p = (fun (st:state_t) -> 
                        SentMsg2? st
                    && (SentMsg2?.sentmsg2 st).n_b = n_b
                    ) in
            match lookup_state #state_t bob p tr with
            | (None, _ ) -> ()
            | (Some (sid, st), _ ) -> (
                 let alice = (SentMsg2?.sentmsg2 st).alice in
                 let n_a = (SentMsg2?.sentmsg2 st).n_a in

                 let (_, tr_ev) = trigger_event bob (Finishing {alice; bob; n_a; n_b}) tr in
                 decode_msg3_proof bob bob_private_keys_sid msg3_ tr;
                 assert(trace_invariant tr_ev);
                 let (_, tr_st) = set_state bob sid (ReceivedMsg3 {alice; n_a; n_b}) tr_ev in
                 assert(trace_invariant tr_st)
            )
       )
  )
