module DY.OnlineSB.Run

open DY.Core
open DY.Lib

open DY.OnlineSB.Run.Printing
open DY.OnlineSB.Protocol

let run () : traceful (option unit ) =
  let _ = IO.debug_print_string "************* Trace *************\n" in


  let alice = "alice" in
  let bob = "bob" in

  (*** PKI setup ***)

  // Generate private key for Alice
  let* alice_global_session_priv_key_id = initialize_private_keys alice in
  generate_private_key alice alice_global_session_priv_key_id (LongTermPkeKey key_tag);*
  
  // Generate private key for Bob
  let* bob_global_session_priv_key_id = initialize_private_keys bob in
  generate_private_key bob bob_global_session_priv_key_id (LongTermPkeKey key_tag);*

  // Store Bob's public key in Alice's state
  // 1. Initialize Alice's session to store public keys
  // 2. Retrieve Bob's private key from his session
  // 3. Compute the public key from the private key
  // 4. Install Bob's public key in Alice's public key store
  let* alice_global_session_pub_key_id = initialize_pki alice in
  let*? priv_key_bob = get_private_key bob bob_global_session_priv_key_id (LongTermPkeKey key_tag) in
  let pub_key_bob = pk priv_key_bob in
  install_public_key alice alice_global_session_pub_key_id (LongTermPkeKey key_tag) bob pub_key_bob;*

  // Store Alice's public key in Bob's state
  let* bob_global_session_pub_key_id = initialize_pki bob in
  let*? priv_key_alice = get_private_key alice alice_global_session_priv_key_id (LongTermPkeKey key_tag) in
  let pub_key_alice = pk priv_key_alice in
  install_public_key bob bob_global_session_pub_key_id (LongTermPkeKey key_tag) alice pub_key_alice;*

  let alice_global_session_ids: global_sess_ids = {pki=alice_global_session_pub_key_id; private_keys=alice_global_session_priv_key_id} in
  let bob_global_session_ids: global_sess_ids = {pki=bob_global_session_pub_key_id; private_keys=bob_global_session_priv_key_id} in


  (*** The actual protocol run ***)
  let*? (alice_sid, ping_ts) = send_ping alice bob alice_global_session_pub_key_id in
  let*? (bob_sid, ack_ts) = receive_ping_and_send_ack bob bob_global_session_ids ping_ts in
  let*? _ = receive_ack alice alice_global_session_priv_key_id ack_ts in


 (*** Printing the Trace ***)

  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string get_trace_to_string_printers tr
    ) in

  return (Some ())

let _ = run () Nil
