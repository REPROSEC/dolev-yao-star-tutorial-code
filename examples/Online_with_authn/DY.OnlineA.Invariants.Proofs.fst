module DY.OnlineA.Invariants.Proofs

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.OnlineA.Data
open DY.OnlineA.Protocol
open DY.OnlineA.Invariants

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

/// In this module, we show that
/// the three protocol steps (send_ping, receive_ping_and_send_ack, and receive_ack)
/// maintain the protocol invariants.
///
/// For every step s we show a lemma of the form:
/// trace_invariant tr ==> trace_invariant ( trace after step s )

/// Again, we only highlight the differences to the previous model
/// for nonce secrecy.

(*** Sending a Ping maintains the invariants ***)

val send_ping_invariant_short_version:
  alice:principal -> bob:principal -> alice_public_keys_sid:state_id ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_ , tr_out) = send_ping alice bob alice_public_keys_sid tr in
    trace_invariant tr_out
  ))
let send_ping_invariant_short_version alice bob alice_public_keys_sid tr =
  let (n_a, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
  (* We need to adapt the proof to the new send_ping function,
     where we trigger the Initiating event right after nonce generation.
  *)
  let (_, tr_ev) = trigger_event alice (Initiating {alice; bob; n_a}) tr_rand in
  let ping = Ping {alice; n_a} in 
  serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_ev) ping;
  pke_enc_for_is_publishable tr_ev alice bob alice_public_keys_sid key_tag ping


(*** Replying to a Ping maintains the invariants ***)

val decode_ping_invariant:
  bob:principal -> bob_private_keys_sid:state_id ->
  msg:bytes ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = decode_ping bob bob_private_keys_sid msg tr in
    trace_invariant tr_out
  ))
let decode_ping_invariant bob bob_private_keys_sid msg tr = ()

(* For the second protocol step (`receive_ping_and_send_ack`),
   we need a helper lemma: `decode_ping_proof`.

   Ignore this for now, and jump to the next lemma 
   `receive_ping_and_send_ack_invariant`
*)

val decode_ping_proof:
  tr:trace ->
  bob:principal -> bob_private_keys_sid:state_id ->
  msg:bytes ->
  Lemma
  (requires (
    trace_invariant tr /\
    bytes_invariant tr msg
  ))
  (ensures (
    match decode_ping bob bob_private_keys_sid msg tr with
    | (None, _) -> True
    | (Some {alice; n_a}, _) -> (
        is_knowable_by (nonce_label alice bob) tr n_a /\
        ( is_publishable tr n_a \/ 
          event_triggered tr alice (Initiating {alice; bob; n_a}) 
        )
    )
  ))
let decode_ping_proof tr bob bob_private_keys_sid msg =
    match decode_ping bob bob_private_keys_sid msg tr with
    | (None, _) -> ()
    | (Some png, _) -> (
        bytes_invariant_pke_dec_with_key_lookup tr #message_t #parseable_serializeable_bytes_message_t bob bob_private_keys_sid key_tag msg;
        let plain = serialize message_t (Ping png) in
        parse_wf_lemma message_t (bytes_invariant tr) plain;
        FStar.Classical.move_requires (parse_wf_lemma message_t (is_publishable tr)) plain
    )
  

/// The invariant lemma for the `receive_ping_and_send_ack` step

val receive_ping_and_send_ack_invariant:
  bob:principal -> bob_private_keys_sid:state_id -> bob_public_keys_sid:state_id -> ts:timestamp ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_ , tr_out) = receive_ping_and_send_ack bob bob_private_keys_sid bob_public_keys_sid ts tr in
    trace_invariant tr_out
  ))
let receive_ping_and_send_ack_invariant bob bob_private_keys_sid bob_public_keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _ ) -> ()
  | (Some msg, _) -> (
      match decode_ping bob bob_private_keys_sid msg tr with
      | (None, _) -> ()
      | (Some {alice; n_a}, _) -> (          
          let ack = Ack {n_a} in

          (* We need to adapt the proof to the new receive_ping_and_send_ack function,
             where Bob triggers a Responding event.
          *)
          let (_, tr_ev) = trigger_event bob (Responding {alice; bob; n_a}) tr in

          (* We have to show,
             that the new trace tr_ev satisfies the trace invariants, i.e.,
             that the event prediate is satisfied for the Responding event.

             The event prediate says:
             if the nonce n_a has not leaked,
             alice should have triggered an Initiating event.

             We get this guarantee from our helper lemma decode_ping_proof
          *)
          decode_ping_proof tr bob bob_private_keys_sid msg;
          (* We thus get that the trace invariant is satisfied after triggering the event.
          *)
          assert(trace_invariant tr_ev);

          match pke_enc_for bob alice bob_public_keys_sid key_tag ack tr_ev with
          | (None, _) -> ()
          | (Some ack_encrypted, tr_ack) ->(
                assert(trace_invariant tr_ack);

                let (ack_ts, tr_msg) = send_msg ack_encrypted tr_ack in
                  serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr) ack;

                  (* The final requirement for the pke_enc_for_is_publishable lemma is
                     that the pke_pred for the Ack is satisfied.
                     Previously this was trivially true, since we didn't have any restrictions.

                     Now, we need to show that
                     there is some Bob that triggered a Responding event.
                     We did that just before the call to the encryption.
                     Hence this is again immediately satisfied.

                     You can check:
                     assert(pke_pred.pred tr (long_term_key_type_to_usage (LongTermPkeKey key_tag) alice) (serialize message_t ack));
                  *)
                pke_enc_for_is_publishable tr_ev bob alice bob_public_keys_sid key_tag ack;
                assert(trace_invariant tr_msg);

                let st = (SentAck {alice; n_a}) in
                let (sess_id, tr_sess) = start_new_session bob st tr_msg in
                assert(trace_invariant tr_sess)
           )
      )
  )


(*** Receiving an Ack maintains the invariants ***)

val decode_ack_invariant:
  alice:principal -> alice_private_keys_sid:state_id -> cipher:bytes ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = decode_ack alice alice_private_keys_sid cipher tr in
    trace_invariant tr_out
  ))
let decode_ack_invariant alice alice_private_keys_sid msg tr = ()


/// Since we now have a non-trivial property for the ReceivedAck state,
/// the proof does not work automatically anymore (as it did for the secrecy model).
///
/// In the same manner as for the other functions,
/// we need a helper lemma for decoding an ack.

val decode_ack_proof:
  tr:trace ->
  alice:principal -> alice_private_keys_sid:state_id ->
  msg:bytes ->
  Lemma
  (requires (
    trace_invariant tr /\ 
    bytes_invariant tr msg
  ))
  (ensures (
    match decode_ack alice alice_private_keys_sid msg tr with
    | (None, _) -> True
    | (Some {n_a}, _) -> (
        is_publishable tr n_a \/ 
        exists bob. event_triggered tr bob (Responding {alice; bob; n_a})
    )
  ))
let decode_ack_proof tr alice alice_private_keys_sid msg =
    match decode_ack alice alice_private_keys_sid msg tr with
    | (None, _) -> ()
    | (Some ack, _) -> (
        bytes_invariant_pke_dec_with_key_lookup tr #message_t #parseable_serializeable_bytes_message_t alice alice_private_keys_sid key_tag msg;
        let plain = serialize message_t (Ack ack) in
        parse_wf_lemma message_t (bytes_invariant tr) plain;
        FStar.Classical.move_requires (parse_wf_lemma message_t (is_publishable tr)) plain
    )
  

/// Additionally,
/// we need an injectivity lemma.
/// The goal is to show that Alice uses the nonces n_a
/// only once, i.e., the nonces n_a are unique for every run.
///
/// We show this with the help of the Initiating event:
/// If there are two events triggered by the same Alice
/// using the same nonce n_a,
/// then the contained other participants (Bob) must also be the same.
///
/// The proof is automatic from the event prediate,
/// which says that the contained nonce n_a
/// was generated right before the event.
/// Since nonces are uniquely identified by their time of creation,
/// this immediately shows that
/// two events referring to the same nonce,
/// must be the same event.

val event_initiating_injective:
  tr:trace ->
  alice:principal -> bob:principal -> bob':principal ->
  n_a:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr alice (Initiating {alice; bob; n_a} ) /\
    event_triggered tr alice (Initiating {alice; bob = bob'; n_a} )
  )
  (ensures
    bob == bob'
  )
let event_initiating_injective tr alice bob bob' n_a = ()


/// The invariant lemma for the final protocol step `receive_ack_invariant`

val receive_ack_invariant:
  alice:principal -> alice_private_keys_sid:state_id -> msg_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = receive_ack alice alice_private_keys_sid msg_ts tr in
    trace_invariant tr_out
  ))
let receive_ack_invariant alice alice_private_keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _) -> ()
  | (Some msg, _) -> (
      match decode_ack alice alice_private_keys_sid msg tr with
      | (None, _) -> ()
      | (Some ack, _) -> (
          let n_a = ack.n_a in
          let p = (fun (st:state_t) -> SentPing? st && (SentPing?.ping st).n_a = n_a) in
          match lookup_state #state_t alice p tr with
          | (None, _) -> ()
          | (Some (sid, st), _) -> (
              let bob = (SentPing?.ping st).bob in
              let ((), tr_ev) = trigger_event alice (Finishing {alice; bob; n_a}) tr in
              decode_ack_proof tr alice alice_private_keys_sid msg;
              assert(trace_invariant tr_ev);
                                                   
              let newst = ReceivedAck {bob; n_a} in
              let ((), tr_st) = set_state alice sid newst tr_ev in
              assert(trace_invariant tr_st)
          )
      )
  )
