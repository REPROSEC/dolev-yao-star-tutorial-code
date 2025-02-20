module DY.NSL.Run

open DY.Core
open DY.Lib

open DY.Simplified

open DY.NSL.Run.Printing
open DY.NSL.Data
open DY.NSL.Protocol

/// Here, we print the trace after a successful run of the NSL protocol.


let run () : traceful (option unit ) =
  let _ = IO.debug_print_string "************* Trace *************\n" in

  (*** Protocol Setup ***)

  // the names of the participants
  let alice = "Alice" in
  let bob = "Bob" in

  (*** PKI setup ***)

  // Initialize key storage for Alice
  // private and public keys are stored in separate sessions
  let* alice_private_keys_sid = initialize_private_keys alice in
  let* alice_public_keys_sid = initialize_pki alice in

  // Initialize key storage for Bob
  let* bob_private_keys_sid = initialize_private_keys bob in
  let* bob_public_keys_sid = initialize_pki bob in  

  // Generate private key for Alice and store it in her private keys session
  generate_private_pke_key alice alice_private_keys_sid key_tag;*
  
  // Generate private key for Bob and store it in his private keys session
  generate_private_pke_key bob bob_private_keys_sid key_tag;*

  // Store Bob's public key in Alice's state
  install_public_pke_key alice alice_public_keys_sid key_tag bob bob_private_keys_sid;*

  // Store Alice's public key in Bob's state
  install_public_pke_key bob bob_public_keys_sid key_tag alice alice_private_keys_sid;*

  (*** The actual protocol run ***)

  // Alice sends a Ping to Bob
  let*? (alice_sid, msg1_ts) = send_msg1 alice bob alice_public_keys_sid in
  // Bob replies with an Ack (reading the ping at the given timestamp)
  let*? (bob_sid, msg2_ts) = receive_msg1_and_send_msg2 bob bob_private_keys_sid bob_public_keys_sid msg1_ts in
  let*? (bob_sid, msg3_ts) = receive_msg2_and_send_msg3 alice alice_private_keys_sid alice_public_keys_sid msg2_ts in
  // Alice receives the Ack (at the given ack timestamp)
  receive_msg3 bob bob_private_keys_sid msg3_ts;*?


 (*** Printing the Trace ***)

  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string get_trace_to_string_printers tr
    ) in

  return (Some ())

let _ = run () empty_trace
