From granite.core Require Import
  Program.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section WithContext.
  Context {Val: Type}. (* TODO: ensure Val is synthesizable. *)
  Context [initVal : Val].

  Definition RegSt := Val.

  Inductive ValueMethod: Type -> Type :=
  | Read : ValueMethod Val.

  Inductive ActionMethod: Type -> Type :=
  | Write: Val -> ActionMethod unit.

  Definition EvalValueMethod [T] (met: ValueMethod T) (st: RegSt) : T :=
    match met with
    | Read => st 
    end.

  Definition EvalActionMethod [T] (met: ActionMethod T) (st: RegSt) : T * RegSt :=
    match met with
    | Write val => (tt, val)
    end.

  Definition RegSpec : Spec ValueMethod ActionMethod :=
    {| State := RegSt;
       EvalVMethod := EvalValueMethod;
       EvalMethod := EvalActionMethod;
       initialState := initVal 
    |}.

End WithContext.
Arguments RegSt : clear implicits.
Arguments ValueMethod: clear implicits.
Arguments ActionMethod: clear implicits.

Notation "'RegAction(' m ',' proj ',' st ')' " :=
      (let '(v, mst') := Reg.EvalActionMethod m (proj%function st) in
       (v, st <| proj := mst' |>)) (at level 100, only parsing).
Notation "'RegValue(' m ',' proj ',' st ')' " :=
      (Reg.EvalValueMethod m (proj%function st)) (at level 100, only parsing). 


