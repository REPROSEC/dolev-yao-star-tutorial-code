module DY.Example.NSL.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib

open DY.Extend

open DY.Example.NSL.Protocol.Total
open DY.Example.NSL.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module proves lemmas for the functions in DY.Example.NSL.Protocol.Total.
/// They will in turn be used in the stateful invariant proofs
/// in DY.Example.NSL.Protocol.Stateful.Proofs.

(*** Cryptographic invariants ***)

let state_was_set_some_id (#a:Type) {|local_state a|} tr prin (cont : a) =
  exists sid. state_was_set tr prin sid cont

val state_was_set_some_id_grows:
  #a:Type -> {|lsa:local_state a|} ->
  tr1:trace -> tr2:trace -> 
  prin:principal -> content:a ->
  Lemma
  (requires tr1 <$ tr2
    /\ state_was_set_some_id tr1 prin content
  )
  (ensures
    state_was_set_some_id tr2 prin content
  )
  [SMTPat (state_was_set_some_id #a #lsa tr1 prin content); SMTPat (tr1 <$ tr2)]
let state_was_set_some_id_grows #a #ls tr1 tr2 prin content  = admit()


instance crypto_usages_nsl : crypto_usages = default_crypto_usages

#push-options "--ifuel 2 --fuel 0"
val crypto_predicates_nsl: crypto_predicates
let crypto_predicates_nsl = {
  default_crypto_predicates with

  pke_pred = {
    pred = (fun tr sk_usage pk msg ->
      (exists prin. 
      sk_usage == long_term_key_type_to_usage (LongTermPkeKey "NSL.PublicKey") prin
      /\ (
        match parse message msg with
        | Some (Msg1 msg1) -> (
          let (alice, bob) = (msg1.alice, prin) in
          state_was_set_some_id tr alice (InitiatorSendingMsg1 bob msg1.n_a)/\
          get_label tr msg1.n_a == nonce_label alice bob
        )
        | Some (Msg2 msg2) -> (
          let (alice, bob) = (prin, msg2.bob) in
          state_was_set_some_id tr bob (ResponderSendingMsg2 alice msg2.n_a msg2.n_b) /\
          get_label tr msg2.n_b == nonce_label alice bob
        )
        | Some (Msg3 msg3) -> (
          let bob = prin in
          exists alice n_a.
            get_label tr msg3.n_b `can_flow tr` (principal_label alice) /\
            state_was_set_some_id tr alice (InitiatorSendingMsg3 bob n_a msg3.n_b)
        )
        | None -> False
      ))
    );
    pred_later = (fun tr1 tr2 sk_usage pk msg ->
      parse_wf_lemma message (bytes_well_formed tr1) msg
      );
  };
}
#pop-options

instance crypto_invariants_nsl : crypto_invariants = {
  usages = crypto_usages_nsl;
  preds = crypto_predicates_nsl;
}

(*** Proofs ***)

val compute_message1_proof:
  tr:trace ->
  alice:principal -> bob:principal -> pk_b:bytes -> n_a:bytes -> nonce:bytes ->
  Lemma
  (requires
    // From the stateful code
    state_was_set_some_id tr alice (InitiatorSendingMsg1 bob n_a)/\
    // From random generation
    is_secret (nonce_label alice bob) tr n_a  /\
    // From random generation
    is_secret (long_term_key_label alice) tr nonce /\
    // From random generation
    nonce `has_usage tr` PkeNonce /\
    // From PKI invariants
    is_public_key_for tr pk_b (LongTermPkeKey "NSL.PublicKey") bob
  )
  (ensures is_publishable tr (compute_message1 alice bob pk_b n_a nonce))
let compute_message1_proof tr alice bob pk_b n_a nonce =
  let msg = Msg1 {n_a; alice;} in
  serialize_wf_lemma message (is_knowable_by (long_term_key_label alice) tr) msg;
  serialize_wf_lemma message (is_knowable_by (long_term_key_label bob) tr) msg

// If bob successfully decrypt the first message,
// then n_a is knownable both by alice (in the message) and bob (the principal)
// This is because:
// - if the message was encrypted by the attacker, then n_a is publishable hence knowable by alice and bob
// - if the message was encrypted by an honest principal, this follows from the encryption predicate
#push-options "--ifuel 1 --fuel 0 --z3rlimit 25"
val decode_message1_proof:
  tr:trace ->
  bob:principal -> msg_cipher:bytes -> sk_b:bytes ->
  Lemma
  (requires
    // From PrivateKeys invariants
    is_private_key_for tr sk_b (LongTermPkeKey "NSL.PublicKey") bob /\
    // From the network
    bytes_invariant tr msg_cipher
  )
  (ensures (
    match decode_message1 bob msg_cipher sk_b with
    | None -> True
    | Some msg1 -> (
      is_knowable_by (nonce_label msg1.alice bob) tr msg1.n_a
      /\ (
        is_publishable tr msg1.n_a
        \/ state_was_set_some_id tr msg1.alice (InitiatorSendingMsg1 bob msg1.n_a)
      )
    )
  ))
let decode_message1_proof tr bob msg_cipher sk_b =
  match decode_message1 bob msg_cipher sk_b with
  | None -> ()
  | Some msg1 ->
    let Some msg = pke_dec sk_b msg_cipher in
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) msg;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) msg
#pop-options

val compute_message2_proof:
  tr:trace ->
  bob:principal -> msg1:message1 -> pk_a:bytes -> n_b:bytes -> nonce:bytes ->
  Lemma
  (requires
    // From the stateful code
    state_was_set_some_id tr bob (ResponderSendingMsg2 msg1.alice msg1.n_a n_b) /\
    // From decode_message1_proof
    is_knowable_by (nonce_label msg1.alice bob) tr msg1.n_a /\
    // From the random generation
    is_secret (nonce_label msg1.alice bob) tr n_b /\
    // From the random generation
    is_secret (long_term_key_label bob) tr nonce /\
    // From the random generation
    nonce `has_usage tr` PkeNonce /\
    // From the PKI
    is_public_key_for tr pk_a (LongTermPkeKey "NSL.PublicKey") msg1.alice
  )
  (ensures
    is_publishable tr (compute_message2 bob msg1 pk_a n_b nonce)
  )
let compute_message2_proof tr bob msg1 pk_a n_b nonce =
  let msg = Msg2 {n_a = msg1.n_a;  n_b; bob;} in
  serialize_wf_lemma message (is_knowable_by (principal_label msg1.alice) tr) msg;
  serialize_wf_lemma message (is_knowable_by (principal_label bob) tr) msg

// If alice successfully decrypt the second message,
// then n_b is knownable both by alice (in the message) and bob (the principal)
// (for the same reasons with decode_message1)
// Furthermore, either alice or bob are corrupt, or bob triggered the Responding event
// (proved with the encryption predicate)
#push-options "--ifuel 1 --fuel 0 --z3rlimit 25"
val decode_message2_proof:
  tr:trace ->
  alice:principal -> bob:principal -> msg_cipher:bytes -> sk_a:bytes -> n_a:bytes ->
  Lemma
  (requires
    // From the NSL state invariant
    is_secret (nonce_label alice bob) tr n_a /\
    // From the PrivateKeys invariant
    is_private_key_for tr sk_a (LongTermPkeKey "NSL.PublicKey") alice /\
    // From the network
    bytes_invariant tr msg_cipher
  )
  (ensures (
    match decode_message2 alice bob msg_cipher sk_a n_a with
    | None -> True
    | Some msg2 -> (
      is_knowable_by (nonce_label alice bob) tr msg2.n_b 
      /\ (
      (is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob)) 
      \/ (
      is_secret (nonce_label alice bob) tr msg2.n_b /\
        state_was_set_some_id tr bob (ResponderSendingMsg2 alice n_a msg2.n_b)
      )
      )
    )
  ))
let decode_message2_proof tr alice bob msg_cipher sk_a n_a =
  match decode_message2 alice bob msg_cipher sk_a n_a with
  | None -> ()
  | Some msg2 -> (
    let Some msg = pke_dec sk_a msg_cipher in
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) msg;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) msg
    ; assert(is_publishable tr msg ==> is_publishable tr msg2.n_a)
    ; assert(n_a = msg2.n_a)
    ; assert(is_publishable tr msg ==> is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob))

  )
#pop-options

val compute_message3_proof:
  tr:trace ->
  alice:principal -> bob:principal -> pk_b:bytes -> n_b:bytes -> nonce:bytes ->
  Lemma
  (requires
    // From the stateful code
    (exists n_a. state_was_set_some_id tr alice (InitiatorSendingMsg3 bob n_a n_b)) /\
    // From decode_message2_proof
     is_knowable_by (nonce_label alice bob) tr n_b /\
    // From the random generation
    is_secret (long_term_key_label alice) tr nonce /\
    // From the random generation
    nonce `has_usage tr` PkeNonce /\
    // From the PKI
    is_public_key_for tr pk_b (LongTermPkeKey "NSL.PublicKey") bob
  )
  (ensures
    is_publishable tr (compute_message3 alice bob pk_b n_b nonce)
  )
let compute_message3_proof tr alice bob pk_b n_b nonce =
  let msg = Msg3 {n_b;} in
  serialize_wf_lemma message (is_knowable_by (principal_label alice) tr) msg;
  serialize_wf_lemma message (is_knowable_by (principal_label bob) tr) msg;
  let msg3: message3 = {n_b;} in
  assert(msg3.n_b == n_b)

// If bob successfully decrypt the third message,
// Then either alice or bob are corrupt, or alice triggered the Initiate2 event
// (proved with the encryption predicate)
#push-options "--ifuel 1 --fuel 0 --z3rlimit 25"
val decode_message3_proof:
  tr:trace ->
  alice:principal -> bob:principal -> msg_cipher:bytes -> sk_b:bytes -> n_b:bytes ->
  Lemma
  (requires
    // From the NSL state invariant
    get_label tr n_b == nonce_label alice bob /\
    // From the PrivateKeys invariant
    is_private_key_for tr sk_b (LongTermPkeKey "NSL.PublicKey") bob /\
    // From the network
    bytes_invariant tr msg_cipher
  )
  (ensures (
    match decode_message3 alice bob msg_cipher sk_b n_b with
    | None -> True
    | Some msg3 -> (
      (is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob)) \/ (
        (exists alice n_a.
           get_label tr msg3.n_b `can_flow tr` (principal_label alice) /\
           state_was_set_some_id tr alice (InitiatorSendingMsg3 bob n_a n_b)
      ))
    )
  ))
let decode_message3_proof tr alice bob msg_cipher sk_b n_b =
  match decode_message3 alice bob msg_cipher sk_b n_b with
  | None -> ()
  | Some msg3 -> (
    let Some msg = pke_dec sk_b msg_cipher in
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) msg;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) msg
  )
#pop-options

#push-options "--ifuel 1 --fuel 0 --z3rlimit 25"
val decode_message3__proof:
  tr:trace ->
  alice:principal -> bob:principal -> msg_cipher:bytes -> sk_b:bytes ->
  Lemma
  (requires
    // From the PrivateKeys invariant
    is_private_key_for tr sk_b (LongTermPkeKey "NSL.PublicKey") bob /\
    // From the network
    bytes_invariant tr msg_cipher
  )
  (ensures (
    match decode_message3_ msg_cipher sk_b with
    | None -> True
    | Some msg3 -> (
      (is_publishable tr msg3.n_b)
      \/ (
        (exists alice (n_a:bytes).
          get_label tr msg3.n_b `can_flow tr` (principal_label alice) /\
          state_was_set_some_id tr alice (InitiatorSendingMsg3 bob n_a msg3.n_b)
      ))
    )
  ))
let decode_message3__proof tr alice bob msg_cipher sk_b =
  match decode_message3_ msg_cipher sk_b with
  | None -> ()
  | Some msg3 -> (
    let Some msg = pke_dec sk_b msg_cipher in
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) msg;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) msg
  )
#pop-options
