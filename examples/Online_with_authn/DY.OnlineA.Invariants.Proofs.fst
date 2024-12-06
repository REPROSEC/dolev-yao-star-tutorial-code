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

/// Again, we will only highlight the differences to the proofs for the secrecy model.

(*** Sending a Ping maintains the invariants ***)

val send_ping_invariant_short_version:
  alice:principal -> bob:principal -> keys_sid:state_id ->
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = send_ping alice bob keys_sid tr in
    trace_invariant tr_out
  ))
let send_ping_invariant_short_version alice bob keys_sid  tr =
  let (n_a, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
  (* We have to adapt the proof to the new send_ping function,
     i.e., we triggered an event and
     swapped the order of storing the state and sending the message
  *)
  let (_, tr_ev) = trigger_event alice (Initiating {alice; bob; n_a}) tr_rand in
  let (_, tr_sess) = start_new_session alice (SendingPing {bob; n_a}) tr_ev in  
  let ping = Ping {alice; n_a} in 
  serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_sess) ping;
  pke_enc_for_is_publishable tr_sess alice bob keys_sid key_tag ping


(*** Replying to a Ping maintains the invariants ***)


val decode_ping_invariant:
  bob:principal -> keys_sid:state_id ->
  msg:bytes ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = decode_ping bob keys_sid msg tr in
    trace_invariant tr_out
  ))
let decode_ping_invariant bob keys_sid msg tr = ()


val decode_ping_proof:
  tr:trace ->
  bob:principal -> keys_sid:state_id ->
  msg:bytes ->
  Lemma
  (requires (
    trace_invariant tr
    /\ bytes_invariant tr msg
  ))
  (ensures (
    match decode_ping bob keys_sid msg tr with
    | (None, _) -> True
    | (Some png, _) -> (
        let n_a = png.n_a in
        bytes_invariant tr n_a /\
        is_knowable_by (nonce_label png.alice bob) tr n_a /\
        ( is_publishable tr n_a
        \/ (pke_pred.pred tr (long_term_key_type_to_usage (LongTermPkeKey key_tag) bob) (serialize message_t (Ping png)))
        )
    )
  ))
let decode_ping_proof tr bob keys_sid msg =
    match decode_ping bob keys_sid msg tr with
    | (None, _) -> ()
    | (Some png, _) -> (
        bytes_invariant_pke_dec_with_key_lookup tr #message_t #parseable_serializeable_bytes_message_t bob keys_sid key_tag msg;
        let plain = serialize message_t (Ping png) in
        parse_wf_lemma message_t (bytes_invariant tr) plain;
        FStar.Classical.move_requires (parse_wf_lemma message_t (is_publishable tr)) plain
    )
  


/// The invariant lemma for the `receive_ping_and_send_ack` step

val receive_ping_and_send_ack_invariant:
  bob:principal -> keys_sid:global_sess_ids -> ts:timestamp ->
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = receive_ping_and_send_ack bob keys_sid ts tr in
    trace_invariant tr_out
  ))
let receive_ping_and_send_ack_invariant bob bob_keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _ ) -> ()
  | (Some msg, _) -> (
      match decode_ping bob bob_keys_sid.private_keys msg tr with
      | (None, _) -> ()
      | (Some png, _) -> (
          let n_a = png.n_a in
          let alice = png.alice in
          
          let ack = Ack {n_a} in

          (* Again, we have to adapt the proof to the new order of
             first storing the state and then sending the message.

             The proof that this step maintains the invariant,
             is the same as before:
             
             starting a new session maintains the trace invariant,
             if the new state satisfies the state predicate.

             For the new SendingAck state, this means that
             the stored nonce
             must be readble by
             the storing principal (here bob).

             And that there is some alice, that
             stored a SendinPing state,
             unless the nonce n_a is publishable.

             We get this property from our helper lemma `decode_ping_proof`:
             which says:
             the nonce n_a is publishable,
             or we get the guarantees from the pke_pred for the decoded Ping.
             From the pke_pred, we get that 
             alice contained in the Ping stored a SendingPing state.
          *)
          let st = (SendingAck {alice = png.alice; n_a = png.n_a}) in
          let (sess_id, tr_sess) = start_new_session bob st tr in
          decode_ping_proof tr bob bob_keys_sid.private_keys msg;
          assert(trace_invariant tr_sess);

          (* The rest of the proof is the same as before. *)
          match pke_enc_for bob alice bob_keys_sid.pki key_tag ack tr_sess with
          | (None, _) -> ()
          | (Some ack_encrypted, tr_ack) ->(
                assert(trace_invariant tr_ack);

                let (ack_ts, tr_msg) = send_msg ack_encrypted tr_ack in
                  serialize_wf_lemma message_t (bytes_invariant tr) (ack);
                  assert(bytes_invariant tr (serialize message_t ack));                  
                  assert(is_knowable_by (nonce_label alice bob) tr n_a);
                  serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr) ack;
                pke_enc_for_is_publishable tr_sess bob alice bob_keys_sid.pki key_tag ack;
                assert(trace_invariant tr_msg);
               ()
           )
      )
  )



(*** Receiving an Ack maintains the invariants ***)


val decode_ack_invariant:
  alice:principal -> keys_sid:state_id -> cipher:bytes ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = decode_ack alice keys_sid cipher tr in
    trace_invariant tr_out
  ))
let decode_ack_invariant alice keys_sid msg tr = ()


/// Since we now have a non-trivial property for the ReceivedAck state,
/// the proof does not work automatically anymore (as it did for the secrecy model).
///
/// In the same manner as for the other functions,
/// we need a helper lemma for decoding an ack.

val decode_ack_proof:
  tr:trace ->
  alice:principal -> keys_sid:state_id ->
  msg:bytes ->
  Lemma
  (requires (
    trace_invariant tr
    /\ bytes_invariant tr msg
  ))
  (ensures (
    match decode_ack alice keys_sid msg tr with
    | (None, _) -> True
    | (Some ack, _) -> (
        let n_a = ack.n_a in
        bytes_invariant tr n_a /\
        ( is_publishable tr n_a
        \/ (pke_pred.pred tr (long_term_key_type_to_usage (LongTermPkeKey key_tag) alice) (serialize message_t (Ack ack)))
        )
    )
  ))
let decode_ack_proof tr alice keys_sid msg =
    match decode_ack alice keys_sid msg tr with
    | (None, _) -> ()
    | (Some ack, _) -> (
        bytes_invariant_pke_dec_with_key_lookup tr #message_t #parseable_serializeable_bytes_message_t alice keys_sid key_tag msg;
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

val event_initiating_injective_:
  tr:trace ->
  alice:principal -> alice':principal -> bob:principal -> bob':principal ->
  n_a:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr alice (Initiating {alice; bob; n_a} ) /\
    event_triggered tr alice' (Initiating {alice =alice'; bob =bob'; n_a} )
  )
  (ensures
    alice == alice' /\
    bob == bob'
  )
let event_initiating_injective_ tr alice alice' bob bob' n_a = ()


/// The invariant lemma for the final protocol step `receive_ack_invariant`

#push-options "--ifuel 2"
val receive_ack_invariant:
  alice:principal -> keys_sid:state_id -> msg_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = receive_ack alice keys_sid msg_ts tr in
    trace_invariant tr_out
  ))
let receive_ack_invariant alice keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _) -> ()
  | (Some msg, _) -> (
      match decode_ack alice keys_sid msg tr with
      | (None, _) -> ()
      | (Some ack, _) -> (
          let n_a = ack.n_a in
          let p = (fun (st:state_t) -> SendingPing? st && (SendingPing?.ping st).n_a = n_a) in
          match lookup_state #state_t alice p tr with
          | (None, _) -> ()
          | (Some (st, sid), _) -> (
              let bob = (SendingPing?.ping st).bob in
              let newst = ReceivedAck {bob; n_a} in

              let ((), tr_st) = set_state alice sid newst tr in
              // We show the state predicate for the new ReceivedAck state in the following

              // from the SendPing state predicate
              assert(is_secret (nonce_label alice bob) tr n_a);
              // immediate consequence of the exact label of n_a
              assert(is_publishable tr n_a ==> is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob));

              (* the more difficult case is the honest case,
                 when the nonce is not publishable
              *)
              introduce ~(is_publishable tr n_a) ==> state_was_set_some_id tr bob (SendingAck {alice; n_a} )
              with _. (
                decode_ack_proof tr alice keys_sid msg;
                (* From the pke_pred for the decoded Ack,
                   we get that there is some bob' that set a SendingAck state.
                   So, we need to show, that this bob' is 
                   the same as the bob stored in Alice's SendPing state.

                   We get this from the nonce injectivity from above.
                *)
                assert(pke_pred.pred tr (long_term_key_type_to_usage (LongTermPkeKey key_tag) alice) (serialize message_t (Ack ack)));
                eliminate exists bob'. state_was_set_some_id tr bob' (SendingAck {alice; n_a})
                returns _
                with _. (
                  // from the state predicate of the looked up SendingPing state of Alice:
                  assert(event_triggered tr alice (Initiating {alice; bob;n_a}));

                  // from the state predicate of the SendingAck state of bob'
                  // (via the state prediate for the SendinPing state of Alice with bob'):
                  assert(event_triggered tr alice (Initiating {alice; bob = bob'; n_a} ));

                  // the injectivity lemma from above, yields bob' = bob
                  event_initiating_injective tr alice bob bob' n_a
                )
              );
              assert(trace_invariant tr_st)
          )
      )
  )
#pop-options
