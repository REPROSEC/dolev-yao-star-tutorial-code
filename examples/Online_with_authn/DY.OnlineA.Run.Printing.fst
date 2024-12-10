module DY.OnlineA.Run.Printing

open DY.Core
open DY.Lib
open Comparse

open DY.OnlineA.Data

/// Helper functions for trace printing.
/// Here we define how our abstract message and state types
/// should be printed.


val message_to_string: bytes -> option string
let message_to_string b =
  match? parse message_t b with
  | Ping p -> Some (Printf.sprintf "Ping [name = (%s), n_a = (%s)]" (p.alice) (bytes_to_string p.n_a))
  | Ack a -> Some (Printf.sprintf "Ping [n_a = (%s)]" (bytes_to_string a.n_a))


val state_to_string: bytes -> option string
let state_to_string b =
  match? parse state_t b with
  | SentPing p -> Some (Printf.sprintf "SentPing [n_a = (%s), to = (%s)]" (bytes_to_string p.n_a) p.bob)
  | SentAck a -> Some (Printf.sprintf "SentAck [n_a = (%s), to = (%s)]" (bytes_to_string a.n_a) a.alice)
  | ReceivedAck r -> Some (Printf.sprintf "ReceivedAck [n_a = (%s), from = (%s)]" (bytes_to_string r.n_a) r.bob)




val get_trace_to_string_printers: trace_to_string_printers
let get_trace_to_string_printers  = 
  trace_to_string_printers_builder 
    message_to_string
    [(local_state_state.tag, state_to_string)]
    []
