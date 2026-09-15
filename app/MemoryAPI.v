From stdpp Require Import base nmap.
From granite.core Require Import
  Bits
  Program.

Module Params.
  Class Params := {
    width: Z;
  }.
End Params.

Section WithContext.
  Context {params: Params.Params}.

  Record mem_req_t :=
    { mem_req_is_store: bool
    ; mem_req_addr: bits Params.width
    ; mem_req_data: bits Params.width
    }.

  #[export] Instance Inhabited_mem_req_t : Inhabited mem_req_t.
  Proof. repeat constructor; exact inhabitant. Defined.

  Record mem_resp_t :=
    { mem_resp_addr: bits Params.width;
      mem_resp_data: bits Params.width
    }.
  #[export] Instance Inhabited_mem_resp_t : Inhabited mem_resp_t.
  Proof. repeat constructor; exact inhabitant. Defined.


  Inductive ActionMethod: Type -> Type :=
  | Enq (arg: mem_req_t) : ActionMethod unit 
  | Deq : ActionMethod unit
  | Tick : ActionMethod unit.
  
  Inductive ValueMethod : Type -> Type :=
  | RespReady : ValueMethod bool
  | Full : ValueMethod bool 
  | Peek : ValueMethod mem_resp_t.
  
End WithContext.
