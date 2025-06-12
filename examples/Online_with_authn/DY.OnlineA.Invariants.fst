module DY.OnlineA.Invariants

open Comparse 
open DY.Core
open DY.Lib
open DY.Extend

open DY.OnlineA.Data
open DY.OnlineA.Protocol

open FStar.List.Tot.Base

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

/// We only highlight the differences to the previous model
/// for showing nonce secrecy.

(*** Crypto Invariants ***)


%splice [ps_ping_t_is_well_formed] (gen_is_well_formed_lemma (`ping_t))
%splice [ps_ack_t_is_well_formed] (gen_is_well_formed_lemma (`ack_t))
%splice [ps_message_t_is_well_formed] (gen_is_well_formed_lemma (`message_t))

instance crypto_usages_online : crypto_usages = default_crypto_usages

#push-options "--ifuel 3"
let crypto_predicates_online : crypto_predicates = { 
  default_crypto_predicates with 
  pke_pred = { 
    pred = (fun tr sk_usage pk msg ->
    exists prin. (
      sk_usage == long_term_key_type_to_usage (LongTermPkeKey key_tag) prin /\
      (match parse message_t msg with
      | Some (Ping {alice; n_a}) ->
          let bob = prin in
          get_label tr n_a == nonce_label alice bob

          (* We add, that the Alice specified in the Ping message,
             must have triggered an Initiating event
             with 
             * her own name (alice)
             * the intended receiver of the Ping (bob) and
             * the nonce n_a in the Ping
          *)
          /\ event_triggered tr alice (Initiating {alice; bob; n_a})
      | Some (Ack {n_a}) ->
          (* For nonce secrecy,
             we didn't have any conditions/guarantees in the Ack case.
             Now, we add that 
             some Bob must have triggered a Responding event with
             * the intended receiver of the Ack (alice)
             * his own name (bob) and
             * the nonce (n_a) in the Ack
          *)
          let alice = prin in
          exists bob. event_triggered tr bob (Responding {alice; bob; n_a})
      | _ -> False
      ))
      ); 
    pred_later = (fun tr1 tr2 sk_usage pk msg -> 
      parse_wf_lemma message_t (bytes_well_formed tr1) msg
    ) 
  } 
}
#pop-options

/// Collecting the usages and prediates in the final crypto invariants

instance crypto_invariants_online: crypto_invariants = {
  usages = crypto_usages_online;
  preds =  crypto_predicates_online
}


(*** State Invariant ***)

%splice [ps_sent_ping_t_is_well_formed] (gen_is_well_formed_lemma (`sent_ping_t))
%splice [ps_sent_ack_t_is_well_formed] (gen_is_well_formed_lemma (`sent_ack_t))
%splice [ps_received_ack_t_is_well_formed] (gen_is_well_formed_lemma (`received_ack_t))
%splice [ps_state_t_is_well_formed] (gen_is_well_formed_lemma (`state_t))

#push-options "--ifuel 2 --z3cliopt 'smt.qi.eager_threshold=50'"
let state_predicate_online: local_state_predicate state_t = {
  pred = (fun tr prin sess_id st ->
    match st with
    | SentPing {bob; n_a} -> (
        let alice = prin in
        is_secret (nonce_label alice bob) tr n_a
        (* We add, that the storing principal (alice),
           must have triggered an Initiating event with:
           * her own name
           * the bob stored in the state and
           * the nonce stored in the state
        *)
        /\ event_triggered tr alice (Initiating {alice; bob; n_a})
    )
    | SentAck {alice; n_a} -> (
        let bob = prin in
        is_knowable_by (principal_label bob) tr n_a
        (* Additionally, we enforce that
           the storing principal (bob) 
           must have triggered e Responding event with:
           * the stored name (alice)
           * his own name (bob)
           * the stored nonce (n_a)
        *)
        /\ event_triggered tr bob (Responding {alice; bob; n_a})
    )
    | ReceivedAck {bob; n_a}  -> (
        let alice = prin in
        is_secret (nonce_label alice bob) tr n_a

        (* We add, that the storing principal (alice),
          must have triggered a Finishing event with:
          * her own name
          * the bob stored in the state and
          * the nonce stored in the state
        *)
        /\ event_triggered tr alice (Finishing {alice; bob; n_a})
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> () );
  pred_knowable = (fun tr prin sess_id st -> () );
}
#pop-options


(*** Event Predicates ***)

/// As for messages and states,
/// we also have predicates on events.
/// The intuition is similar:
/// They say when an event is allowed to be triggered, or
/// what guarantees we obtain, if we observe a specific event on the trace.

let event_predicate_online: event_predicate event_t =
  fun tr prin e ->
  // prin is the principal triggering the event
    match e with    
    | Initiating {alice; bob; n_a} -> (
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
        rand_just_generated tr n_a
    )
    | Responding {alice; bob; n_a} -> (
        (* A Responding event may only be triggered if,
           * the triggering principal is the second principal stored in the event (bob)
           * if the stored nonce n_a has not leaked,
             then the first stored principal (alice)
             must have triggered an Initiating event with the same data
             as the Responding event
        *)
        prin == bob /\ 
        ( is_publishable tr n_a \/
          event_triggered tr alice (Initiating {alice; bob; n_a}))
    )
    | Finishing {alice; bob; n_a} -> (
        (* A Finishing event may only be triggered if,
           * the triggering principal is the first principal stored in the event (alice)
           * the same principal triggered an Initiating event with the same bob and n_a
           * if the stored nonce n_a has not leaked,
             then the second stored principal (bob)
             must have triggered a Responding event with the same data
        *)
        prin == alice /\
        event_triggered tr alice (Initiating {alice; bob; n_a}) /\
        ( is_publishable tr n_a \/
          event_triggered tr bob (Responding {alice; bob; n_a}))
    )


(*** Trace invariants ***)

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (|local_state_state_t.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_online|);
]

/// Now we have an event type
let all_events = [(event_event_t.tag, compile_event_pred event_predicate_online)]

let trace_invariants_online: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}


(*** Protocol Invariants ***)

instance protocol_invariants_online: protocol_invariants = {
  crypto_invs = crypto_invariants_online;
  trace_invs = trace_invariants_online;
}

/// Lemmas that the global state predicate contains all the local ones

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_sessions)));
  mk_state_pred_correct all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions)

val protocol_invariants_p_has_p_session_invariant: squash (has_local_state_predicate state_predicate_online)
let protocol_invariants_p_has_p_session_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_pki_invariant: squash (has_pki_invariant #protocol_invariants_online)
let protocol_invariants_p_has_pki_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_private_keys_invariant: squash (has_private_keys_invariant #protocol_invariants_online)
let protocol_invariants_p_has_private_keys_invariant = all_sessions_has_all_sessions ()

/// Lemmas that the global event predicate contains all the local ones

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_online) all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct #protocol_invariants_online all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_online) all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP (has_compiled_event_pred #protocol_invariants_online) all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_online) all_events))

val protocol_invariants_p_has_event_t_invariant: squash (has_event_pred event_predicate_online)
let protocol_invariants_p_has_event_t_invariant = all_events_has_all_events ()
