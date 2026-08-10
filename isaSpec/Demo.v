From granite.isaSpec Require Import
  LeakageRefinement
  Memory
  PipelineRefines
  QuartzImpl
  TopLevelSpec.
From granite.isaSpec Require IFC QuartzImpl_helpers StaticAnalysis StaticAnalysisTest.

Module SoftwareTopLevelTheorem := SoftwareTopLevelTheorem PipelineRefines.
Section WithContext.
  Import RefinementTheorem.
  Context {imemParams: memSpec.SpecParams}.
  Context {dmemParams: memSpec.SpecParams}.
  Notation implMachine' :=
      (@QuartzTop.machine' exampleMultiplierParams (@QuartzImpl_helpers.q_isMMIOAddr) imemParams dmemParams).

  Theorem noninterference : 
      forall tr1 tr2 (sec_init1 sec_init2: IFC.SecInit),
      let pub_init := StaticAnalysis.SymbExec.MkPubInit 
                        StaticAnalysisTest.Salsa20.prog__salsa20_bin in  
      Machine.in_traces (implMachine' pub_init sec_init1) tr1 ->
      Machine.in_traces (implMachine' pub_init sec_init2) tr2 ->
      SamePublicInputs tr1 tr2 ->
      SamePublicOutputs tr1 tr2.
  Proof.
    cbn. intros. 
    eapply (@SoftwareTopLevelTheorem.noninterference exampleMultiplierParams imemParams dmemParams); eauto.
    exists (10000)%nat. vm_compute. reflexivity.
  Qed.
  Print Assumptions noninterference.
  (*
    Section Variables:
    imemParams
    : memSpec.SpecParams
    dmemParams
    : memSpec.SpecParams
    Axioms:
    FunctionalExtensionality.functional_extensionality_dep :
      forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
      (forall x : A, f x = g x) -> f = g
  *)

End WithContext.



