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


(*** Sending a Ping maintains the invariants ***)



(* The above proof was very detailed.
   In fact, most of the proof is done automatically by F*
   and we can remove all of the asserts.

   If we just keep the necessary calls to lemmas,
   we end up with the following very short proof.
*)
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
  let (_, tr_ev) = trigger_event alice (Initiating {alice; bob; n_a}) tr_rand in
  let ping = Ping {alice; n_a} in 
  serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_ev) ping;
  pke_enc_for_is_publishable tr_ev alice bob keys_sid key_tag ping


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

(* For the second protocol step (`receive_ping_and_send_ack`),
   we need a helper lemma: `decode_ping_proof`.

   Ignore this for now, and jump to the next lemma 
   `receive_ping_and_send_ack_invariant`
*)

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
//        is_knowable_by (nonce_label png.alice bob) tr n_a /\
        ( is_publishable tr n_a
        \/ (pke_pred.pred tr (long_term_key_type_to_usage (LongTermPkeKey key_tag) bob) (serialize message_t (Ping png)))
        )
     )
   )
  )
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
  (* As for the first protocol step,
     we need to show that every traceful action 
     maintains the trace invariant.
  *)
  match recv_msg msg_ts tr with // unfold the traceful + option let
  | (None, _ ) -> () // in this case the trace is not changed and hence the trace invariant is trivially satisfied
  | (Some msg, _) -> (
      (* From the lemma `recv_msg_same_trace` in `DY.Core.Trace.Manipulation` 
         we have that the receive function does not change the trace
         and hence the trace invariant is still satisfied. *)
      match decode_ping bob bob_keys_sid.private_keys msg tr with // unfold the next monadic let
      | (None, _) -> () // Again, if decoding fails, the trace is not changed and hence nothing left to show
      | (Some png, _) -> (
          (* Decoding the ping message does not change the trace.
             So we are still working on the input trace tr,
             for which we know the trace invariant.

             That decoding doesn't change the trace,
             is shown automatically 
             with corresponding SMT patterns for the individual steps of the function.
             I.e., try uncommenting the following lemma:
           *) 
             // let decode_ping_same_trace
             //    (p:principal) (keys_sid:state_id) (msg:bytes) (tr:trace) :
             //    Lemma (
             //       let (_, tr_out) = decode_ping p keys_sid msg tr in
             //       tr_out == tr )
             //    = () in
          
          let n_a = png.n_a in
          let alice = png.alice in
          
          let ack = Ack {n_a} in

          let (_, tr_ev) = trigger_event bob (Responding {alice; bob; n_a}) tr in
          decode_ping_proof tr bob bob_keys_sid.private_keys msg;
          assert(trace_invariant tr_ev);

          match pke_enc_for bob alice bob_keys_sid.pki key_tag ack tr_ev with
          | (None, _) -> ()
          | (Some ack_encrypted, tr_ack) ->(
                (* As before, encryption maintains the trace invariant 
                   (see `pke_enc_for_invariant` in `DY.simplified`) *)
                assert(trace_invariant tr_ack);

                let (ack_ts, tr_msg) = send_msg ack_encrypted tr_ack in
                (* The same as in the first protocol step:
                   we want to use the lemma `send_msg_invariant` from `DY.Core.Trace.Manipulation`
                   to show that sending the encrypted ack maintains the invariant.

                   For this, we need to show that the encrypted ack is publishable.
                   Again, we want to apply the lemma `pke_enc_for_is_publishable` from `DY.Simplified`.
                   So we have to show all of the pre-conditions of this lemma.
                *)
                  (* `trace_invariant tr` and `has_pki_invariant` are satisfied *)
                  (* For `bytes_invariant` of the serialized ack,
                     we need a helper lemma.

                     TODO ....
                  *)
                  decode_ping_proof tr bob bob_keys_sid.private_keys msg;
                  serialize_wf_lemma message_t (bytes_invariant tr) (ack);
                  assert(bytes_invariant tr (serialize message_t ack));
                  (* From this helper lemma, we also get
                     that the nonce is readable by alice and bob.

                     We use this fact together with a comparse lemma,
                     to show the next two requirements:
                     the serialized ack is readable by alice and bob 
                     (again ignoring the `long_term_key_label`) *)
                  assert(is_knowable_by (nonce_label alice bob) tr n_a);
                  serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr) ack;

                  (* The final requirement is trivially satisfied, 
                     since the pke_pred for an Ack is just True

                     You can check:
                     assert(pke_pred.pred tr (long_term_key_type_to_usage (LongTermPkeKey key_tag) alice) (serialize message_t ack));
                  *)
                  assert(is_publishable tr n_a \/ event_triggered tr alice (Initiating {alice; bob; n_a}));
                  assert(pke_pred.pred tr_ev (long_term_key_type_to_usage (LongTermPkeKey key_tag) alice) (serialize message_t ack));
                (* Thus, we can call `pke_enc_for_is_publishable`
                   to get the missing pre-condition for `send_msg_invariant`.*)
                pke_enc_for_is_publishable tr_ev bob alice bob_keys_sid.pki key_tag ack;
                assert(trace_invariant tr_msg);

                (* As in the first protocol step,
                   starting a new session maintains the trace invariant,
                   if the new state satisfies the state predicate.

                   For the new SentAck state, this means that
                   the stored nonce
                   must be readble by
                   the storing principal (here bob).

                   We get this property from our helper lemma `decode_ping_proof`.
                *)
                let st = (SentAck {alice = png.alice; n_a = png.n_a}) in
                let (sess_id, tr_sess) = start_new_session bob st tr_msg in
                assert(trace_invariant tr_sess)
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


/// The invariant lemma for the final protocol step `receive_ack_invariant`

#push-options "--ifuel 2 --z3rlimit 30"
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
          let p = (fun (st:state_t) -> SentPing? st && (SentPing?.ping st).n_a = n_a) in
          match lookup_state #state_t alice p tr with
          | (None, _) -> ()
          | (Some (st, sid), _) -> (
              let bob = (SentPing?.ping st).bob in
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
              introduce ~(is_publishable tr n_a) ==> 
                // state_was_set_some_id tr bob (SentAck {alice; n_a})
                event_triggered tr bob (Responding {alice; bob; n_a})
              with _. (
                decode_ack_proof tr alice keys_sid msg;
                (* From the pke_pred for the decoded Ack,
                   we get that there is some bob' that set a SendingAck state.
                   So, we need to show, that this bob' is 
                   the same as the bob stored in Alice's SendPing state.

                   We get this from the nonce injectivity from above.
                *)
                assert(pke_pred.pred tr (long_term_key_type_to_usage (LongTermPkeKey key_tag) alice) (serialize message_t (Ack ack)));
                assert(~((get_label tr n_a) `can_flow tr` public));
                assert(exists bob'. event_triggered tr bob (Responding {alice; bob = bob'; n_a}));
                assert(exists bob'. event_triggered tr alice (Initiating {alice; bob = bob'; n_a}));
                eliminate exists bob'. event_triggered tr alice (Initiating {alice; bob = bob'; n_a})
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
