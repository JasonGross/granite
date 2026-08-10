(* Memory *)
From stdpp Require Import base finite nmap.
From stdpp.bitvector Require Import definitions.
From granite.core Require Import
  Array
  Pair
  Program
  ProgramOps
  Object
  Reg.

Section API.
  Context {width : N}.
  Notation data_t := (bv width).
  Inductive ActionMethod : Type -> Type :=
  | Store (idx: N) (value: data_t) : ActionMethod unit.

  Inductive ValueMethod : Type -> Type :=
  | Load (idx: N) : ValueMethod data_t.

End API.
Arguments ActionMethod : clear implicits.
Arguments ValueMethod: clear implicits.

Section WithContext.
  Context {width: N}.
  Notation data_t := (bv width).
  Definition MemSt := Nmap data_t.

  Definition mem_load (mem: MemSt) (addr: N) : data_t :=
    mem !!! addr.
  Definition mem_store (mem: MemSt) (addr: N) (data: data_t)  : MemSt :=
    <[ addr := data ]> mem.

  Definition EvalMemVMethod {T} (met: ValueMethod width T) (st: MemSt) : T :=
    match met with
    | Load idx => mem_load st idx
    end.

  Definition EvalMemMethod {T} (met: ActionMethod width T) (st: MemSt) : T * MemSt :=
    match met with
    | Store idx value => ((), mem_store st idx value)
    end.
  Definition MemSpec (initSt: MemSt) : Spec (ValueMethod width) (ActionMethod width) :=
    {| State := MemSt;
       EvalVMethod A := EvalMemVMethod;
       EvalMethod A := EvalMemMethod;
       initialState := initSt
    |}.

End WithContext.

Arguments MemSt : clear implicits.
