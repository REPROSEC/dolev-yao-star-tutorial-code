module DY.Simplified

open Comparse
open DY.Core
open DY.Lib

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

let gen_rand =
  mk_rand NoUsage public 32

let gen_rand_labeled l =
    mk_rand NoUsage l 32

val start_new_session:
  #a:Type -> {| local_state a |} ->
  principal -> a ->
  traceful state_id
let start_new_session prin cont =
  let* sid = new_session_id prin in
  set_state prin sid cont;*
  return sid

val pk_enc_for:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> principal ->
  state_id -> string -> 
  a -> 
  traceful (option bytes)
let pk_enc_for #a alice bob key_sid key_tag plaintext =
  let*? pk_bob = get_public_key alice key_sid (LongTermPkEncKey key_tag) bob in
  let* nonce = mk_rand PkNonce (long_term_key_label alice) 32 in
  return ( Some (pk_enc pk_bob nonce (serialize a plaintext)))

val pk_enc_for_invariant:
  {|protocol_invariants|}->
  tr:trace ->
  #a:Type -> {|parseable_serializeable bytes a|} ->
  alice:principal -> bob:principal ->
  alice_pki_sid:state_id ->
  key_tag:string ->
  msg:a ->
  Lemma
  (requires
      trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = pk_enc_for #a alice bob alice_pki_sid key_tag msg tr in
    trace_invariant tr_out
  ))
let pk_enc_for_invariant tr #a alice bob alice_pki_sid key_tag msg = ()

val pk_enc_for_is_publishable:
  {|protocol_invariants|} ->
  tr:trace ->
  #a:Type -> {|parseable_serializeable bytes a|} ->
  alice:principal -> bob:principal ->
  alice_pki_sid:state_id ->
  key_tag:string ->
  msg:a ->
  Lemma
  (requires (
    let msg_b = serialize #bytes a msg in
      trace_invariant tr
    /\ has_pki_invariant
    /\ bytes_invariant tr msg_b
    /\ (get_label tr msg_b) `can_flow tr` (long_term_key_label bob)
    /\ (get_label tr msg_b) `can_flow tr` (long_term_key_label alice)
    /\ (pkenc_pred.pred tr (long_term_key_type_to_usage (LongTermPkEncKey key_tag) bob) msg_b
      \/ (get_label tr msg_b) `can_flow tr` public
    )
    ))
  (ensures (
    match pk_enc_for alice bob alice_pki_sid key_tag msg tr with
    | (None, _) -> True
    | (Some cipher, tr_out) -> 
        is_publishable tr_out cipher
  ))
let pk_enc_for_is_publishable tr #a alice bob alice_pki_sid key_tag msg =
  match pk_enc_for alice bob alice_pki_sid key_tag msg tr with
  | (None, _) -> ()
  | (Some cipher, tr_out) -> (
      let pk_type = LongTermPkEncKey key_tag in
      let (Some pk_bob, _) = get_public_key alice alice_pki_sid pk_type bob tr in
      let (nonce, tr_nonce) = mk_rand PkNonce (long_term_key_label alice) 32 tr in
      let msg = serialize #bytes a msg in
      assert(is_public_key_for tr_out pk_bob pk_type bob);
      let sk_usg = long_term_key_type_to_usage (LongTermPkEncKey key_tag) bob in
      introduce pkenc_pred.pred tr sk_usg msg ==> is_publishable tr_out cipher
      with _ .
        pkenc_pred.pred_later tr tr_nonce sk_usg msg;
      ()
)  

val pk_dec_with_key_lookup:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> 
  state_id -> string ->
  bytes ->
  traceful (option a)
let pk_dec_with_key_lookup #a prin keys_sid key_tag cipher =
  let*? sk_a = get_private_key prin keys_sid (LongTermPkEncKey key_tag) in
  let*? plaintext = return (pk_dec sk_a cipher) in 
  // guard_tr ( Some? (parse a plaintext));*?
  return (parse a plaintext)

val bytes_invariant_pk_dec_with_key_lookup:
  {|protocol_invariants|} ->
  tr:trace ->
  #a:Type -> {|parseable_serializeable bytes a|} ->
  alice:principal -> keys_sid:state_id -> key_tag:string ->
  cipher:bytes ->
  Lemma
  (requires (
      trace_invariant tr
    /\ has_private_keys_invariant
    /\ bytes_invariant tr cipher
  ))
  (ensures(
    match pk_dec_with_key_lookup #a alice keys_sid key_tag cipher tr with
    | (None, _) -> True
    | (Some plaintext, _) -> (
        let plain_b = serialize #bytes a plaintext in
        is_knowable_by (long_term_key_label alice ) tr plain_b /\
      ( let sk_usg = (long_term_key_type_to_usage (LongTermPkEncKey key_tag) alice) in
        ((
          //PkKey? sk_usg /\
          pkenc_pred.pred tr sk_usg plain_b )
          \/ (
          (get_label tr plain_b `can_flow tr` public)
        )
      )
    )
  )))
let bytes_invariant_pk_dec_with_key_lookup tr #a alice keys_sid key_tag cipher = 
  match pk_dec_with_key_lookup #a alice keys_sid key_tag cipher tr with
  | (None, _) -> ()
  | (Some plaintext, _) -> (
      let (Some sk_alice, _) = get_private_key alice keys_sid (LongTermPkEncKey key_tag) tr in
      let Some cipher_dec = pk_dec sk_alice cipher in 
       let sk_usg = (long_term_key_type_to_usage (LongTermPkEncKey key_tag) alice) in
      bytes_invariant_pk_dec tr sk_alice sk_usg cipher;
      serialize_parse_inv_lemma a cipher_dec
  )
