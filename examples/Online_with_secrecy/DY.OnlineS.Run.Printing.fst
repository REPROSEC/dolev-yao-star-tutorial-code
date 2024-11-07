module DY.OnlineS.Run.Printing

open DY.Core
open DY.Lib
open Comparse

open DY.OnlineS.Data

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
  | SentPing p -> Some (Printf.sprintf "SentPing [to = (%s), n_a = (%s)]" p.bob (bytes_to_string p.n_a))
  | SentAck a -> Some (Printf.sprintf "SentAck [to = (%s), n_a = (%s)]" a.alice (bytes_to_string a.n_a))
  | ReceivedAck r -> Some (Printf.sprintf "ReceivedAck [from = (%s), n_a = (%s)]" r.bob (bytes_to_string r.n_a))




val get_trace_to_string_printers: trace_to_string_printers
let get_trace_to_string_printers  = 
  trace_to_string_printers_builder 
    message_to_string
    [(local_state_state.tag, state_to_string)]
    []
