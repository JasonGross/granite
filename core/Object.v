From granite.core Require Import
  Program
  ProgramOps.

Definition coarsen {VMethod Method} (impl: Object VMethod Method) 
  : Spec VMethod Method :=
  mapSpec (programSpec impl.(objBase)) impl.(objExpr) impl.(objProgram).

Definition mapImplExpr
           {VBaseMethod VMethod VMethod'}
           (f : forall Ret, VMethod' Ret -> VMethod Ret)
           (impl : forall Ret, VMethod Ret -> expr VBaseMethod Ret)
           Ret (m : VMethod' Ret) :
  expr VBaseMethod Ret :=
  impl Ret (f Ret m).

Definition mapImplProg
           {VBaseMethod BaseMethod Method Method'}
           (f : forall Ret, Method' Ret -> Method Ret)
           (impl : forall Ret, Method Ret -> prog VBaseMethod BaseMethod Ret)
           Ret (m : Method' Ret) :
  prog VBaseMethod BaseMethod Ret :=
  impl Ret (f Ret m).

Definition mapObject
           {VMethod Method VMethod' Method'}
           (vf : forall Ret, VMethod' Ret -> VMethod Ret)
           (f : forall Ret, Method' Ret -> Method Ret)
           (impl : Object VMethod Method) :
  Object VMethod' Method' :=
  {|
    objBase := impl.(objBase);
    objExpr := mapImplExpr vf impl.(objExpr);
    objProgram := mapImplProg f impl.(objProgram)
  |}.


