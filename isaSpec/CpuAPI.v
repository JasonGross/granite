From stdpp Require Import base finite nmap.
From granite.core Require Import
  Bits
  Program.
From granite.isaSpec Require Import
  Common
  Memory.

Section WithContext.

  Inductive mem_type :=
  | IMEM
  | DMEM
  | MMIO.

  Import memModuleAPI.

  Inductive ActionMethod: Type -> Type :=
  | EnqResp (mem: mem_type) (arg: mem_resp_t) : ActionMethod unit
  | DeqReq (mem: mem_type) : ActionMethod unit
  | SetInterrupt (status: bool) (source: mword): ActionMethod unit
  | AddLeakage (leakage: (list LeakageEvent)) : ActionMethod unit
  | Tick (* (useLeakage: bool *): ActionMethod unit.
 
  Inductive ValueMethod : Type -> Type :=
  | CanEnqResp: mem_type -> ValueMethod bool
  | CanDeqReq : mem_type -> ValueMethod bool
  | Peek : mem_type -> ValueMethod (mem_req_t).

End WithContext.

