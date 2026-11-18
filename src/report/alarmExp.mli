(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
(** Alarm sites parameterized by the operand representation (CIL expressions or
    a client's own). *)
type ('exp, 'lval) expression =
  | ArrayExp of 'lval * 'exp * Sparrow_cil.location
  | DerefExp of 'exp * Sparrow_cil.location
  | DivExp of 'exp * 'exp * Sparrow_cil.location
  | Strcpy of 'exp * 'exp * Sparrow_cil.location
  | Strcat of 'exp * 'exp * Sparrow_cil.location
  | Strncpy of 'exp * 'exp * 'exp * Sparrow_cil.location
  | Memcpy of 'exp * 'exp * 'exp * Sparrow_cil.location
  | Memmove of 'exp * 'exp * 'exp * Sparrow_cil.location
  | AllocSize of 'exp * Sparrow_cil.location

type t = (Sparrow_cil.exp, Sparrow_cil.lval) expression

val collect : IntraCfg.cmd -> t list
val to_string : t -> string
val location_of : ('exp, 'lval) expression -> Sparrow_cil.location
