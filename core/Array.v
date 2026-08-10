From stdpp Require Import base vector.
From granite.core Require Import
  Program.

Section Array.
  Context {VMethod Method} (spec: Spec VMethod Method).
  Context (sz: nat).

  Definition ArraySt := vec spec.(State) sz.

  Definition ArrayMethod (Ret: Type) : Type :=
    prod (fin sz) (Method Ret).
  Definition ArrayVMethod (Ret: Type) : Type :=
    prod (fin sz) (VMethod Ret).

  Definition EvalArrayVMethod A (met: ArrayVMethod A) (st: ArraySt) : A :=
    let '(idx, m) := met in
    spec.(EvalVMethod) m (st !!! idx).

  Definition EvalArrayMethod A (met: ArrayMethod A) (st: ArraySt) : A * ArraySt :=
    let '(idx, m) := met in
    let '(a, st_idx) := spec.(EvalMethod) m (st !!! idx) in 
    (a, vinsert idx st_idx st).

  Definition ArraySpec : Spec ArrayVMethod ArrayMethod :=
    {| State := ArraySt;
       EvalVMethod := EvalArrayVMethod;
       EvalMethod := EvalArrayMethod;
       initialState := fun_to_vec (fun _ => spec.(initialState))
    |}.

End Array.
Arguments ArrayVMethod: clear implicits.
Arguments ArrayMethod: clear implicits.

