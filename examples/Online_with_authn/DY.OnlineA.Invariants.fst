module DY.OnlineA.Invariants

open Comparse 
open DY.Core
open DY.Lib

open DY.Extend

open DY.OnlineA.Data
open DY.OnlineA.Protocol

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25"

/// In this module, we define the protocol invariants.
/// They consist of
/// * crypto invariants and
/// * trace invariants which in turn consist of
///   * state invariants and
///   * event invariants
///
/// We then have to show
/// * these invariants imply the secrecy property (see DY.OnlineS.Secrecy) and
/// * every protocol step maintains these invariants (see DY.OnlineS.Invariants.Proofs)
/// With this, we then know that
/// the protocol model satisfies the secrecy property.

/// We highlight only the differences to
/// the invariants for the nonce secrecy proof (Online_with_secrecy/DY.OnlineS.Invariants.fst)
/// 

(*** Crypto Invariants ***)


%splice [ps_ping_t_is_well_formed] (gen_is_well_formed_lemma (`ping_t))
%splice [ps_ack_t_is_well_formed] (gen_is_well_formed_lemma (`ack_t))
%splice [ps_message_t_is_well_formed] (gen_is_well_formed_lemma (`message_t))

instance crypto_usages_p : crypto_usages = default_crypto_usages

#push-options "--ifuel 2"
let crypto_p : crypto_predicates = { 
  default_crypto_predicates with 
  pke_pred = { 
    pred = (fun tr sk_usage msg ->
    exists prin.
    (
      sk_usage == long_term_key_type_to_usage (LongTermPkeKey key_tag) prin /\
      (match parse message_t msg with
      | Some (Ping ping) ->
          let bob = prin in
          let alice = ping.alice in
          let n_a = ping.n_a in
          get_label tr n_a == nonce_label alice bob
          (* additionally, we here also require/guarantee
             that the principal in the message (alice)
             stored a SendingPing state before sendind the message,
             containing:
             * the intended receiver (bob) and
             * the nonce in the message (n_a)
          *)
          /\ state_was_set_some_id tr alice (SendingPing {bob; n_a})
      | Some (Ack ack) ->
          let alice = prin in
          let n_a = ack.n_a in
          (* In contrast to the secrecy proof,
             where we didn't need any guarantees for an Ack message,
             we here have the property that
             there is some principal bob that 
             stored a SendingAck state with 
             * the intended receiver of the Ack (alice) and
             * the nonce in the Ack (n_a)
          *)
          exists bob.
            state_was_set_some_id tr bob (SendingAck {alice = prin; n_a = ack.n_a})
      | _ -> False
      ))
      ); 
    pred_later = (fun tr1 tr2 pk msg -> 
      parse_wf_lemma message_t (bytes_well_formed tr1) msg
    ) 
  } 
}
#pop-options

/// Collecting the usages and prediates in the final crypto invariants

instance crypto_invariants_p: crypto_invariants = {
  usages = crypto_usages_p;
  preds =  crypto_p
}


(*** State Invariant ***)

%splice [ps_sent_ping_t_is_well_formed] (gen_is_well_formed_lemma (`sent_ping_t))
%splice [ps_sent_ack_t_is_well_formed] (gen_is_well_formed_lemma (`sent_ack_t))
%splice [ps_received_ack_t_is_well_formed] (gen_is_well_formed_lemma (`received_ack_t))
%splice [ps_state_t_is_well_formed] (gen_is_well_formed_lemma (`state_t))

#push-options "--ifuel 2 --z3cliopt 'smt.qi.eager_threshold=50'"
let state_predicate_p: local_state_predicate state_t = {
  pred = (fun tr prin sess_id st ->
    match st with
    | SendingPing ping -> (
        let alice = prin in
        let bob = ping.bob in
        let n_a = ping.n_a in
        is_secret (nonce_label alice bob) tr n_a
        (* additionally to the secrecy proof,
           we add the property that 
           the storing principal (alice)
           triggered in Initiating event containing:
           * her own name
           * the principal stored in the state (bob) and
           * the nonce stored in the state (n_a)
        *) 
        /\ event_triggered tr alice (Initiating {alice = alice; bob = bob; n_a = n_a})
    )
    | SendingAck ack -> (
        let bob = prin in
        let n_a = ack.n_a in
        is_knowable_by (principal_label bob) tr n_a
        (* here we add,
           that the stored other principal (alice)
           stored a SendingPing state containing
           * the current storing principal (bob) and
           * the nonce stored in the state (n_a)
           except, if we are in the case that 
           the stored nonce (n_a) has leaked to the attacker.
        *)
        /\ (
          is_publishable tr n_a \/
          state_was_set_some_id tr ack.alice (SendingPing {bob; n_a})
        )
    )
    | ReceivedAck rack  -> (
        (* a ReceivedAck state may only be stored if
           the stored nonce is labeled for
           * the storing principal (alice)
           * the principal stored in the state
             (the expected sender of the Ack)
        *)
        let alice = prin in
        let bob = rack.bob in
        let n_a = rack.n_a in
        is_secret (nonce_label alice bob) tr n_a /\

        (* this is already the authentication property we want to show:
           alice stores a ReceivedAck state only, if
           the stored principal (bob) stored a SendingAck state containing:
           * alice and
           * the nonce n_a
           unless,
           one of alice or bob are corrupt
        *)
        (state_was_set_some_id tr bob (SendingAck {alice; n_a})
        \/ (is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob)))
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> () );
  pred_knowable = (fun tr prin sess_id st -> () );
}
#pop-options

(*** Event Pred ***)

/// As for messages and states,
/// we also have prediates on events.
/// The intuition is similar:
/// They say when an event is allowed to be triggered, or
/// what guarantees we obtain, if we observe an event on the trace.

let event_predicate_event_t: event_predicate event_t =
  fun tr prin e ->
  // prin is the principal triggering the event
    match e with    
    | Initiating init -> (
        let alice = init.alice in
        let bob = init.bob in
        let n_a = init.n_a in
        (* We may trigger the Initiating event only if,
           * the triggering principal is the first principal stored in the event (alice)
           * the nonce (n_a) in the event is labelled for 
             the two principals stored in the event (alice and bob)
           * the stored nonce (n_a) was generated right before the event is triggered
             (this is crucial and will be used to show an injectivity property,
             that there will be only one such event for a fixed nonce n_a)
        *)
        prin == alice /\
        is_secret (nonce_label alice bob) tr n_a /\
        0 < DY.Core.Trace.Base.length tr /\
        rand_generated_at tr (DY.Core.Trace.Base.length tr - 1) n_a
    )

(*** Trace invariants ***)

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (|local_state_state.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_p|);
]

/// Now we have an event type
let all_events = [(event_event_t.tag, compile_event_pred event_predicate_event_t)]


/// The final trace invariants
/// consisting of
/// * the state invariant and
/// * the event invariant

let trace_invariants_p: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}


(*** Protocol Invariants ***)

/// The final protocol invariants
/// consisting of
/// * the crypto invariants and
/// * the trace invariants

instance protocol_invariants_p: protocol_invariants = {
  crypto_invs = crypto_invariants_p;
  trace_invs = trace_invariants_p;
}


(*** Helper Lemmas ***)

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_sessions)));
  mk_state_pred_correct all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions)

val protocol_invariants_p_has_p_session_invariant: squash (has_local_state_predicate state_predicate_p)
let protocol_invariants_p_has_p_session_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_pki_invariant: squash (has_pki_invariant #protocol_invariants_p)
let protocol_invariants_p_has_pki_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_private_keys_invariant: squash (has_private_keys_invariant #protocol_invariants_p)
let protocol_invariants_p_has_private_keys_invariant = all_sessions_has_all_sessions ()

/// We need similar lemmas for our event type

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_p) all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct #protocol_invariants_p all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_p) all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP (has_compiled_event_pred #protocol_invariants_p) all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_p) all_events))

val protocol_invariants_p_has_event_t_invariant: squash (has_event_pred event_predicate_event_t)
let protocol_invariants_p_has_event_t_invariant = all_events_has_all_events ()
