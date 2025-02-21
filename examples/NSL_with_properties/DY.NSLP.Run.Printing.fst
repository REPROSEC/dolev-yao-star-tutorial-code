module DY.NSLP.Run.Printing

open DY.Core
open DY.Lib
open Comparse

open DY.Simplified

open DY.NSLP.Data

/// Helper functions for trace printing.
/// Here we define how our abstract message and state types
/// should be printed.


val message_to_string: bytes -> option string
let message_to_string b =
  match? parse message_t b with
  | Msg1 m -> Some (Printf.sprintf "Msg1 [name = (%s), n_a = (%s)]" (m.alice) (bytes_to_string m.n_a))
  | Msg2 m -> Some (Printf.sprintf "Msg2 [name = (%s), n_a = (%s), n_b = (%s)]" (m.bob) (bytes_to_string m.n_a) (bytes_to_string m.n_b))
  | Msg3 m -> Some (Printf.sprintf "Msg3 [n_b = (%s)]" (bytes_to_string m.n_b))


val state_to_string: bytes -> option string
let state_to_string b =
  match? parse state_t b with
  | SentMsg1 s -> Some (Printf.sprintf "SentMsg1 [n_a = (%s), to = (%s)]" (bytes_to_string s.n_a) s.bob)
  | SentMsg2 s -> Some (Printf.sprintf "SentMsg2 [n_a = (%s), n_b = (%s), to = (%s)]" (bytes_to_string s.n_a) (bytes_to_string s.n_b) s.alice)
  | SentMsg3 s -> Some (Printf.sprintf "SentMsg3 [n_a = (%s), n_b = (%s), to = (%s)]" (bytes_to_string s.n_a) (bytes_to_string s.n_b) s.bob)
  | ReceivedMsg3 s -> Some (Printf.sprintf "ReceivedMsg3 [n_a = (%s), n_b = (%s), from = (%s)]" (bytes_to_string s.n_a) (bytes_to_string s.n_b) s.alice)

val event_to_string: bytes -> option string
let event_to_string b =
  match? parse event_t b with
  | Initiating {alice; bob; n_a} -> Some (Printf.sprintf "Initiating [alice = (%s), n_a = (%s), with = (%s)]" alice (bytes_to_string n_a) bob)
  | Responding1 {alice; bob; n_a; n_b} -> Some (Printf.sprintf "Responding1 [bob = (%s), n_a = (%s), n_b = (%s), to = (%s)]" bob (bytes_to_string n_a) (bytes_to_string n_b) alice)
  | Responding2 {alice; bob; n_a; n_b} -> Some (Printf.sprintf "Responding2 [alice = (%s), n_a = (%s), n_b = (%s), to = (%s)]" alice (bytes_to_string n_a) (bytes_to_string n_b) bob)
    | Finishing {alice; bob; n_a; n_b} -> Some (Printf.sprintf "Finishing [bob = (%s), n_a = (%s), n_b = (%s), with = (%s)]" bob (bytes_to_string n_a) (bytes_to_string n_b) alice)



val get_trace_to_string_printers: trace_to_string_printers
let get_trace_to_string_printers  = 
  trace_to_string_printers_builder 
    message_to_string
    ((local_state_state.tag, state_to_string) :: default_state_to_string)
    [(event_event_t.tag, event_to_string)]
