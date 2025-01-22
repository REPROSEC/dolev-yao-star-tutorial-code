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

val pke_enc_for:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> principal ->
  state_id -> string -> 
  a -> 
  traceful (option bytes)
let pke_enc_for #a alice bob key_sid key_tag plaintext =
  let*? pk_bob = get_public_key alice key_sid (LongTermPkeKey key_tag) bob in
  let* nonce = mk_rand PkeNonce (long_term_key_label alice) 32 in
  return ( Some (pke_enc pk_bob nonce (serialize a plaintext)))

val pke_enc_for_invariant:
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
    let (_, tr_out) = pke_enc_for #a alice bob alice_pki_sid key_tag msg tr in
    trace_invariant tr_out
  ))
let pke_enc_for_invariant tr #a alice bob alice_pki_sid key_tag msg = ()

val pke_enc_for_is_publishable:
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
    let enc_key_usage = (long_term_key_type_to_usage (LongTermPkeKey key_tag) bob) in
    let (pk_bob, _) = get_public_key alice alice_pki_sid (LongTermPkeKey key_tag) bob tr in
    None? pk_bob \/ (
        trace_invariant tr
      /\ has_pki_invariant
      /\ bytes_invariant tr msg_b
      /\ (get_label tr msg_b) `can_flow tr` (long_term_key_label bob)
      /\ (get_label tr msg_b) `can_flow tr` (long_term_key_label alice)
      /\ (pke_pred.pred tr enc_key_usage (Some?.v pk_bob) msg_b
        \/ (get_label tr msg_b) `can_flow tr` public)
      )
    ))
  (ensures (
    match pke_enc_for alice bob alice_pki_sid key_tag msg tr with
    | (None, _) -> True
    | (Some cipher, tr_out) -> 
        is_publishable tr_out cipher
  ))
let pke_enc_for_is_publishable tr #a alice bob alice_pki_sid key_tag msg =
  match pke_enc_for alice bob alice_pki_sid key_tag msg tr with
  | (None, _) -> ()
  | (Some cipher, tr_out) -> (
      let pk_type = LongTermPkeKey key_tag in
      let (Some pk_bob, _) = get_public_key alice alice_pki_sid pk_type bob tr in
      let (nonce, tr_nonce) = mk_rand PkeNonce (long_term_key_label alice) 32 tr in
      let msg = serialize #bytes a msg in
      assert(is_public_key_for tr_out pk_bob pk_type bob);
      let sk_usg = long_term_key_type_to_usage (LongTermPkeKey key_tag) bob in
      introduce pke_pred.pred tr sk_usg pk_bob msg ==> is_publishable tr_out cipher
      with _ .
        pke_pred.pred_later tr tr_nonce sk_usg pk_bob msg;
      ()
)  

val pke_dec_with_key_lookup:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> 
  state_id -> string ->
  bytes ->
  traceful (option a)
let pke_dec_with_key_lookup #a prin keys_sid key_tag cipher =
  let*? sk_a = get_private_key prin keys_sid (LongTermPkeKey key_tag) in
  let*? plaintext = return (pke_dec sk_a cipher) in 
  // guard_tr ( Some? (parse a plaintext));*?
  return (parse a plaintext)

val bytes_invariant_pke_dec_with_key_lookup:
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
    match pke_dec_with_key_lookup #a alice keys_sid key_tag cipher tr with
    | (None, _) -> True
    | (Some plaintext, _) -> (
        let plain_b = serialize #bytes a plaintext in
        is_knowable_by (long_term_key_label alice ) tr plain_b /\
      ( let sk_usg = (long_term_key_type_to_usage (LongTermPkeKey key_tag) alice) in
        let (sk_alice, _) = get_private_key alice keys_sid (LongTermPkeKey key_tag) tr in
        Some? sk_alice /\
        ((
          //PkKey? sk_usg /\
          pke_pred.pred tr sk_usg (pk (Some?.v sk_alice)) plain_b )
          \/ (
          (get_label tr plain_b `can_flow tr` public)
        )
      )
    )
  )))
let bytes_invariant_pke_dec_with_key_lookup tr #a alice keys_sid key_tag cipher = 
  match pke_dec_with_key_lookup #a alice keys_sid key_tag cipher tr with
  | (None, _) -> ()
  | (Some plaintext, _) -> (
      let (Some sk_alice, _) = get_private_key alice keys_sid (LongTermPkeKey key_tag) tr in
      let Some cipher_dec = pke_dec sk_alice cipher in 
       let sk_usg = (long_term_key_type_to_usage (LongTermPkeKey key_tag) alice) in
      bytes_invariant_pke_dec tr sk_alice sk_usg cipher;
      serialize_parse_inv_lemma a cipher_dec
  )



// generate a private LongTermPkeKey with a given tag
// (this hides the LongTermPkeKey constructor from the user)
val generate_private_pke_key: principal -> state_id -> string -> traceful (option unit)
let generate_private_pke_key prin private_keys_sid key_tag =
  generate_private_key prin private_keys_sid (LongTermPkeKey key_tag)


// Store Bob's public Pke key in Alice's state
// Bob's public key is computed from his private key
// 1. Retrieve Bob's private key from his private key session (using the tag)
// 2. Compute the public key from the private key
// 3. Install Bob's public key in Alice's public key store (under the same tag)
val install_public_pke_key:
  (alice:principal) -> (alice_public_keys_sid:state_id) ->
  (key_tag:string) ->
  (bob:principal) -> (bob_private_keys_sid:state_id) ->
  traceful (option unit)
let install_public_pke_key alice alice_public_keys_sid key_tag bob bob_private_keys_sid =
  let*? priv_key_bob = get_private_key bob bob_private_keys_sid (LongTermPkeKey key_tag) in
  let pub_key_bob = pk priv_key_bob in
  install_public_key alice alice_public_keys_sid (LongTermPkeKey key_tag) bob pub_key_bob



(*** Printing PkeKeys ***)

(* For the first example protocol using public key encryption (the Online? protocol),
   I want a simple to understand printing of the trace.

   The following functions simplify printing of Pke Keys:
   * The LongTermPkeKey constructor is hidden
   * For public keys, the lookup key for the dictionary is written as pair 
     (of key tag and principal)
*)

val long_term_key_type_to_string_: DY.Lib.State.PrivateKeys.long_term_key_type -> string
let long_term_key_type_to_string_ t =
  match t with
  | DY.Lib.State.PrivateKeys.LongTermPkeKey u -> u
  | DY.Lib.State.PrivateKeys.LongTermSigKey u -> "LongTermSigKey " ^ u

val private_keys_types_to_string_: (list (map_elem DY.Lib.State.PrivateKeys.private_key_key DY.Lib.State.PrivateKeys.private_key_value)) -> string
let rec private_keys_types_to_string_ m =
  match m with
  | [] -> ""
  | hd :: tl -> (
    (private_keys_types_to_string_ tl) ^ 
    Printf.sprintf "%s = (%s)," (long_term_key_type_to_string_ hd.key.ty) (bytes_to_string hd.value.private_key)
  )

val private_keys_state_to_string: bytes -> option string
let private_keys_state_to_string content_bytes =
  let? state = parse (map DY.Lib.State.PrivateKeys.private_key_key DY.Lib.State.PrivateKeys.private_key_value) content_bytes in
  Some (Printf.sprintf "[%s]" (private_keys_types_to_string_ state.key_values))



val pki_types_to_string: (list (map_elem DY.Lib.State.PKI.pki_key DY.Lib.State.PKI.pki_value)) -> string
let rec pki_types_to_string m =
  match m with
  | [] -> ""
  | hd :: tl -> (
    (pki_types_to_string tl) ^ 
    Printf.sprintf "(%s, %s) = (%s)," (long_term_key_type_to_string_ hd.key.ty) hd.key.who (bytes_to_string hd.value.public_key)
  )
  
val pki_state_to_string: bytes -> option string
let pki_state_to_string content_bytes =
  let? state = parse (map DY.Lib.State.PKI.pki_key DY.Lib.State.PKI.pki_value) content_bytes in
  Some (Printf.sprintf "[%s]" (pki_types_to_string state.key_values))

let default_pke_keys_printer =
 [ (DY.Lib.State.PrivateKeys.map_types_private_keys.tag, private_keys_state_to_string)
 ; (DY.Lib.State.PKI.map_types_pki.tag, pki_state_to_string)
 ]

let default_state_to_string = default_pke_keys_printer

let default_trace_to_string_printers =
  trace_to_string_printers_builder 
    default_message_to_string
    default_state_to_string
    default_event_to_string
