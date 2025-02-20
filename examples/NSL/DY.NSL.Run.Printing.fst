module DY.NSL.Run.Printing

open DY.Core
open DY.Lib
open Comparse

open DY.Simplified

open DY.NSL.Data

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


val get_trace_to_string_printers: trace_to_string_printers
let get_trace_to_string_printers  = 
  trace_to_string_printers_builder 
    message_to_string
    ((local_state_state.tag, state_to_string) :: default_state_to_string)
    []
