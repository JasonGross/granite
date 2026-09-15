From stdpp Require Import base finite nmap.
From granite.core Require Import
  Bits
  Program.
From granite.app Require Import
  Fifo1Spec
  MemoryAPI
  MultiplierSpec.                

Module Params.
  Class Params :=
  { log_nregs : Z
  ; width : Z
  }.
End Params.

Section WithContext.
  Context {params: Params.Params}.
  #[export] Instance memParams : MemoryAPI.Params.Params := 
    { width := Params.width}.

  Inductive mem_type :=
  | IMEM
  | DMEM.

  Inductive ActionMethod: Type -> Type :=
  | EnqResp (mem: mem_type) (arg: mem_resp_t) : ActionMethod unit
  | DeqReq (mem: mem_type) : ActionMethod unit
  | Tick : ActionMethod unit.
 
  Inductive ValueMethod : Type -> Type :=
  | CanEnqResp: mem_type -> ValueMethod bool
  | CanDeqReq : mem_type -> ValueMethod bool
  | Peek : mem_type -> ValueMethod mem_req_t.

End WithContext.

