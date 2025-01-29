module DY.TwoMessage.Run

open DY.Core
open DY.Lib
open DY.Simplified

open DY.TwoMessage.Run.Printing
open DY.TwoMessage.Protocol

/// Here, we print the trace after a successful run of the Two-Message protocol.

let run () : traceful (option unit ) =
  let _ = IO.debug_print_string "************* Trace *************\n" in

  (*** Protocol Setup ***)

  // define the names of the two participants
  let alice = "Alice" in
  let bob = "Bob" in


  (*** Protocol Run ***)

  // Alice sends a Ping to Bob
  let* (alice_sid, ping_ts) = send_ping alice bob in
  
  // Bob replies with an Ack
  // (we pass the timestamp of Alice's ping to the receive function of Bob)
  let*? (bob_sid, ack_ts) = receive_ping_and_send_ack bob ping_ts in

  // Alice receives the Ack
  // (we pass the timestamp of Bob's response to the receive function of Alice)
  receive_ack alice ack_ts;*?


  (*** Printing the Trace ***)
  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string get_trace_to_string_printers tr
    ) in

  return (Some ())


/// Call `run` when the module loads

let _ = run () empty_trace
