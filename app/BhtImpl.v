From stdpp Require Import base finite.
From granite.core Require Import Bits.
From RecordUpdate Require Import RecordSet.
From granite.core Require Import
  Bits
  Object
  Program
  ProgramOps.
From granite.app Require Import 
  Rf
  BhtAPI.

Set Primitive Projections.
Import RecordSetNotations.

Section WithContext.
  Context {params: Bht_sig} `{Hfin : Finite (bits idx_sz)}.

  Definition dirsSpec := rfSpec (Val := bits 2) (initVal := zeroes) (log_nregs := idx_sz).
  Record St : Type := 
    { Dirs: State dirsSpec }.

  Definition initialSt : St := {| Dirs := initialState dirsSpec |}.

  Inductive BaseMethod : Type -> Type := 
  | dirs : forall {R}, Rf.ActionMethod (Val := bits 2) (log_nregs := idx_sz) R -> BaseMethod R.
  Inductive BaseVMethod : Type -> Type := 
  | _dirs : forall {R}, Rf.ValueMethod (Val := bits 2) (log_nregs := idx_sz) R -> BaseVMethod R.

  Definition evalBaseMethod {A} (m: BaseMethod A) (st: St) : A * St :=
    match m with
    | dirs m =>
        let '(v, mst') := EvalMethod dirsSpec m st.(Dirs) in
        (v, {| Dirs := mst' |})
    end.
  Definition evalBaseVMethod {A} (m: BaseVMethod A) (st: St) : A :=
    match m with
    | _dirs m =>
        EvalVMethod dirsSpec m st.(Dirs)
    end.

  Definition base : Spec _ _ := 
    {| State := St;
       EvalVMethod A := evalBaseVMethod;
       EvalMethod A := evalBaseMethod;
       initialState := initialSt |}.

  Definition defaultNextPc (pc: bits addr_sz) : bits addr_sz:=
      Zmod.add pc (bits.of_Z addr_sz 4).

  (* (* TODO: shiftr by 2 *) *)
  Definition getIndex (pc: bits addr_sz) : bits idx_sz :=
    bits.of_Z idx_sz (Zmod.unsigned (Zmod.sru pc 2)).
  Definition computeTarget (pc: bits addr_sz) (targetPc: bits addr_sz) (taken: bool) :=
    if taken then targetPc else defaultNextPc pc.

  Definition extractDir (dp: bits 2) : bool :=
    bool_decide (dp = bits.of_Z _ 3 \/ dp = bits.of_Z _ 2).

  Definition newDP (dpBits: bits 2) (taken: bool) : bits 2 :=
    if taken then
      (if bool_decide (dpBits = bits.of_Z _ 3) then dpBits else (Zmod.add dpBits (bits.of_Z _ 1)))
    else
      (if bool_decide (dpBits = zeroes) then dpBits else (Zmod.sub dpBits (bits.of_Z _ 1))).

  Notation prog := (prog BaseVMethod BaseMethod).
  Notation expr := (expr BaseVMethod).
        
  Definition ppcDP (pc: bits addr_sz) (targetPc: bits addr_sz): expr (bits addr_sz) :=
    (let index := getIndex pc in
     let/vmet entry := _dirs (Rf.Read index) in
     let direction := extractDir entry in
     return (computeTarget pc targetPc direction))%expr.

  Definition update (pc: bits addr_sz) (taken: bool): prog unit :=
    (let index := getIndex pc in
     let/vmet entry := _dirs (Rf.Read index) in
     let newDp := newDP entry taken in
     dirs (Rf.Write index newDp);;
     pass)%prog.

  Definition impl_VM [R] (m: ValueMethod R) : expr R :=
    match m with
    | PpcDP pc targetPc => ppcDP pc targetPc
    end.

  Definition impl_AM [R] (m: ActionMethod R) : prog R :=
    match m with
    | Update pc taken => update pc taken
    end.

  Definition btb := object base impl_VM impl_AM.
  Definition btb_spec := coarsen btb.
End WithContext. 
