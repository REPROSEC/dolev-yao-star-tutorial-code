module DY.OnlineS.Invariants.Proofs

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.OnlineS.Data
open DY.OnlineS.Protocol
open DY.OnlineS.Invariants

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

/// In this module, we show that
/// the three protocol steps (send_ping, receive_ping_and_send_ack, and receive_ack)
/// maintain the protocol invariants.
///
/// For every step s we show a lemma of the form:
/// trace_invariant tr ==> trace_invariant ( trace after step s )


(*** Sending a Ping maintains the invariants ***)


/// The invariant lemma for the first step `send_ping`

val send_ping_invariant:
  alice:principal -> bob:principal -> keys_sid:state_id ->
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = send_ping alice bob keys_sid tr in
    trace_invariant tr_out
  ))
(* The proof works by showing that the trace invariant is maintained
   by every traceful action in the step.
   So we replicate the actions of the step and show trace_invariant after each.
   
   (Note that we are now in the "Lemma context",
   so we have to unfold the monadic lets and sequences.)
*)
let send_ping_invariant alice bob keys_sid  tr =
  (* The first action is generating the nonce n_a.
  
     Note that we can't use let* here since we are not in the traceful monad.
     Thus, we have to pass the trace `tr` explicitly as last argument.
     And we get back the new trace `tr_rand`.
  *)
  let (n_a, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
  (* That the trace invariant holds after this action,
     can be shown automatically.

     There is a corresponding lemma in `DY.Core.Trace.Manipulation`:
     `mk_rand_trace_invariant`.
     It comes with an SMT Pattern an hence is applied automatically.
  *)
  assert(trace_invariant tr_rand);

  // Defining the abstract message does not change the trace,
  // so we don't have to show anything.
  let ping = Ping {alice; n_a} in 

  (* The call of `pk_enc_for` in the traceful + option monad 
     has to be unfolded:
     * We pass the current trace `tr_rand` as las argument
     * We need to make a case distinction on the resulting option
       and show trace_invariant in each case separately
  *)
  match pk_enc_for alice bob keys_sid key_tag ping tr_rand with
  | (None, _) -> ( 
      (* If encryption fails, the trace is not changed,
         and hence the resulting trace after send_ping is tr_rand.
         Since we already showed trace_invariant for tr_rand,
         we don't have to show anything else in this case.

        If you want to check this,
        you can uncomment the next lines
      *)
      // let (_ , tr_out) = send_ping alice bob keys_sid tr in 
      // assert(tr_out == tr_rand);
      // assert(trace_invariant tr_out);
      ()
    )
  | (Some ping_encrypted, tr_enc) -> (
      (* If encryption succeeds, we get a new trace `tr_enc`.
         With the lemma `pk_enc_for_invariant` in `DY.Simplified`,
         we have that trace_invariant holds for tr_enc.

         Observe, that this lemma can be shown automatically.
         Hence, we don't even have to call it here.
      *)
      assert(trace_invariant tr_enc);

      (* The next traceful action is sending the encrypted message.

         Again, we have to pass the current trace `tr_enc` as last argument.
      *)
      let (msg_ts, tr_msg) = send_msg ping_encrypted tr_enc in
      (* To show trace_invariant after sending the message (for `tr_msg`),
         we look at the lemma `send_msg_invariant` in `DY.Core.Trace.Manipulation`
         which looks very promising.
         However, that lemma has an additional pre-condition requiring that
         the message needs to be publishable.
         (That corresponds to the intuition that everything on the trace 
         is readable by the attacker.)

         So to call this lemma, we have to show `is_publishable tr_enc ping_encrypted`.
         Looking at `DY.Simplified`, we find the lemma `pk_enc_for_is_publishable`,
         which gives a bunch of pre-conditions for the plaintext (serialized `ping`) 
         under which the ciphertext `ping_encrypted` is publishable.
         We show each of those pre-conditions.
      *)
          (* The first is `has_pki_invariant`.

             It is a technical requirement on the protocol invariants 
             which we are not explaining here.

             In `DY.OnlineS.Invariants` we have the lemma `protocol_invariants_p_has_pki_invariant`
             showing this requirement.
          *)
          assert(has_pki_invariant);

          (* The next requirement for `pk_enc_for_is_publishable` is `bytes_invariant tr_enc (serialize ping)`.

             TODO              
          *)
          serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_rand) ping;

          (* The next two pre-conditions say
             that the serialized ping should be readable by Alice and Bob.
             (Ignore the `long_term_key_label` for now.)

             TODO: they are resolved with the same serialize_wf_lemma
          *)

          (* Finally, we need to show the disjunction of
             * the pkenc_pred holds for the serialized ping or
             * the serialized ping is publishable

             In our case, the first is true, i.e., the encryption prediate is satisfied.
             The predicate requires that the nonce contained in the ping
             has the label `nonce_label alice' bob'`, where
             * alice' is the name in the first component of the ping and
             * bob' is the participant whos key is used for encryption.

             Since we generate the nonce n_a in the beginning of this step
             with the label `nonce_label alice bob`,
             put the same alice in the first component of the ping
             and use the key of bob for encryption (in pk_enc_for),
             we satisfy the predicate.
          *)
          assert(pkenc_pred.pred tr_rand (long_term_key_type_to_usage (LongTermPkEncKey key_tag) bob) (serialize message_t ping));
      (* Now we showed all pre-conditions of `pk_enc_for_is_publishable`
         and can call this lemma to show that ping_encrypted is publishable.

         Together with the `send_msg_invariant` lemma, 
         we then obtain that `tr_msg` satisfies the trace invariant.
      *)
      pk_enc_for_is_publishable tr_rand alice bob keys_sid key_tag ping;
      assert(trace_invariant tr_msg);

      (* The last traceful action in this step is starting a new session *)
      let st = SentPing {bob; n_a} in
      let (sid, tr_sess) = start_new_session alice st tr_msg in
      (* `start_new_session` is just calling `new_session_id` and then `set_state`.
         So we have to check that both of those maintain the trace invariant.

         For `new_session_id` we find the lemma 
         `new_session_id_same_trace` in `DY.Core.Trace.Manipulation`
         which says that the trace is not changed.
         Hence it trivially maintains the trace invariant.
         It comes with an SMT pattern, so it is applied automatically.

         In the same file, we have the lemma `set_state_invariant`,
         which gives an additional pre-condition 
         for when the trace after the state was set satisfies the trace invariant.
         This pre-condition is that the new state must satisfy the state predicate.

         The state predicate for the SentPing state requires that
         the nonce stored in the state has the label `nonce_label alice' bob'`, where
         * alice' is the storing principal
         * bob' is the name stored in the first component of the state

         Similarly to above,
         we generated the nonce wit the label `nonce_label alice bob` and
         alice is storing the new state, and
         bob is stored in the first component of the state.
         So the state prediate is satisfied:
      *)
      assert(state_predicate_p.pred tr_msg alice sid st);
      (* With this, we have all pre-conditions of `set_state_invariant`.
         Since that lemma comes with an SMT pattern,
         it is applied automatically.
      *)
      assert(trace_invariant tr_sess)
  )

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
  let ping = Ping {alice; n_a} in 
  serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_rand) ping;
  pk_enc_for_is_publishable tr_rand alice bob keys_sid key_tag ping


(*** Replying to a Ping maintains the invariants ***)


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
        is_knowable_by (nonce_label png.alice bob) tr n_a /\
        ( is_publishable tr n_a
        \/ (pkenc_pred.pred tr (long_term_key_type_to_usage (LongTermPkEncKey key_tag) bob) (serialize message_t (Ping png)))
        )
    )
  ))
let decode_ping_proof tr bob keys_sid msg =
    match decode_ping bob keys_sid msg tr with
    | (None, _) -> ()
    | (Some png, _) -> (
        bytes_invariant_pk_dec_with_key_lookup tr #message_t #parseable_serializeable_bytes_message_t bob keys_sid key_tag msg;
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
          
          match pk_enc_for bob alice bob_keys_sid.pki key_tag ack tr with
          | (None, _) -> ()
          | (Some ack_encrypted, tr_ack) ->(
                (* As before, encryption maintains the trace invariant 
                   (see `pk_enc_for_invariant` in `DY.simplified`) *)
                assert(trace_invariant tr_ack);

                let (ack_ts, tr_msg) = send_msg ack_encrypted tr_ack in
                (* The same as in the first protocol step:
                   we want to use the lemma `send_msg_invariant` from `DY.Core.Trace.Manipulation`
                   to show that sending the encrypted ack maintains the invariant.

                   For this, we need to show that the encrypted ack is publishable.
                   Again, we want to apply the lemma `pk_enc_for_is_publishable` from `DY.Simplified`.
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
                     since the pkenc_pred for an Ack is just True

                     You can check:
                     assert(pkenc_pred.pred tr (long_term_key_type_to_usage (LongTermPkEncKey key_tag) alice) (serialize message_t ack));
                  *)
                (* Thus, we can call `pk_enc_for_is_publishable`
                   to get the missing pre-condition for `send_msg_invariant`.*)
                pk_enc_for_is_publishable tr bob alice bob_keys_sid.pki key_tag ack;
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
(* The proof for this last step is automatic. *)
let receive_ack_invariant alice keys_sid msg_ts tr = ()
#pop-options
