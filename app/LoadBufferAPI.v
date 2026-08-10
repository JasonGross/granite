(* From stdpp Require Import base finite. *)
(* From granite.core Require Import *)
(*   Bits *)
(*   Program. *)

(* Section WithContext. *)
(*   Context {width: N}. *)
(*   Context {Val : Type}. *)

(*   Notation addr_t := (bv width). *)

(*   Inductive ActionMethod : Type -> Type := *)
(*   | LoadReq (addr: addr_t) : ActionMethod unit *)
(*   | ForgetResp (addr: addr_t) : ActionMethod unit *)
(*   (* | StoreReq (addr: addr_t)  *) *)
(*   | LoadResp (addr: addr_t) (data: Val) : ActionMethod unit *)
(*   | Downgrade (addr: addr_t) : ActionMethod unit *)
(*   . *)

(*   Inductive ValueMethod : Type -> Type := *)
(*   | Lookup (addr: addr_t) : ValueMethod (option Val).  *)

(* End WithContext. *)



