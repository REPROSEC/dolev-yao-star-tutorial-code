module DY.Online.Run

open DY.Core
open DY.Lib

open DY.Online.Run.Printing
open DY.Online.Data
open DY.Online.Protocol

/// Here, we print the trace after a successful run of the Two Message protocol.


let run () : traceful (option unit ) =
  let _ = IO.debug_print_string "************* Trace *************\n" in

  (*** Protocol Setup ***)

  // the names of the participants
  let alice = "Alice" in
  let bob = "Bob" in

  (*** PKI setup ***)

  // Initialize key storage for Alice
  // private and public keys are stored in separate sessions
  let* alice_priv_keys_sid = initialize_private_keys alice in
  let* alice_pub_keys_sid = initialize_pki alice in
  // we collect both session ids in a global record
  let alice_global_session_ids : global_sess_ids = 
    { pki = alice_pub_keys_sid; 
      private_keys = alice_priv_keys_sid
    } in

  // Initialize key storage for Bob
  let* bob_priv_keys_sid = initialize_private_keys bob in
  let* bob_pub_keys_sid = initialize_pki bob in  
  let bob_global_session_ids: global_sess_ids = 
    { pki = bob_pub_keys_sid; 
      private_keys = bob_priv_keys_sid
    } in

  // Generate private key for Alice and store it in her private keys session
  generate_private_key alice alice_global_session_ids.private_keys (LongTermPkeKey key_tag);*
  
  // Generate private key for Bob and store it in his private keys session
  generate_private_key bob bob_global_session_ids.private_keys (LongTermPkeKey key_tag);*

  // Store Bob's public key in Alice's state
  // Bob's public key is computed from his private key
  // 1. Retrieve Bob's private key from his private key session
  // 2. Compute the public key from the private key
  // 3. Install Bob's public key in Alice's public key store
  let*? priv_key_bob = get_private_key bob bob_global_session_ids.private_keys (LongTermPkeKey key_tag) in
  let pub_key_bob = pk priv_key_bob in
  install_public_key alice alice_global_session_ids.pki (LongTermPkeKey key_tag) bob pub_key_bob;*

  // Store Alice's public key in Bob's state in the same way
  let*? priv_key_alice = get_private_key alice alice_global_session_ids.private_keys (LongTermPkeKey key_tag) in
  let pub_key_alice = pk priv_key_alice in
  install_public_key bob bob_global_session_ids.pki (LongTermPkeKey key_tag) alice pub_key_alice;*



  (*** The actual protocol run ***)

  // Alice sends a Ping to Bob
  let*? (alice_sid, ping_ts) = send_ping alice bob alice_global_session_ids.pki in
  // Bob replies with an Ack (reading the ping at the given timestamp)
  let*? (bob_sid, ack_ts) = receive_ping_and_send_ack bob bob_global_session_ids ping_ts in
  // Alice receives the Ack (at the given ack timestamp)
  let*? _ = receive_ack alice alice_global_session_ids.private_keys ack_ts in


 (*** Printing the Trace ***)

  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string get_trace_to_string_printers tr
    ) in

  return (Some ())

let _ = run () empty_trace
