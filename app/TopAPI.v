From stdpp Require Import base finite nmap.
From stdpp.bitvector Require Import definitions.
From RecordUpdate Require Import RecordSet.
From granite.core Require Import
  Bits 
  Object
  Program 
  ProgramOps.

From granite.app Require Import 
  MemoryAPI
  MMIO
  Pipelined
  PipelinedAPI.
Set Primitive Projections.
Import RecordSetNotations.


From granite.core Require Import
  Program.                  

Section WithContext.
  Context {memParams: MemoryAPI.Params.Params}.
  Inductive VMethod : Type -> Type :=
  | MMIO_TRACE: VMethod (MMIO.trace_t).
  
  Inductive Method : Type -> Type :=
  | Tick : Method unit.
End WithContext.
