Require Import Lia Setoid Program.Basics.
Require Import AuxDef AuxRel.
Require Import ThreadTrace.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import imm_s.
From imm Require Import SubExecution.
From imm Require Import FinExecution.
From imm Require Import FinThreads.

Open Scope nat_scope.

Module I2Exec.

Section MainDefs.

Definition instr_id : Set := nat.

Record intr_info : Set := {
  instr : instr_id;
  tick : nat;
}.

Variable G : execution.
Variable e2instr : actid -> intr_info.

Definition rmw_end := codom_rel (rmw G).

Definition nrmw_ord := restr_rel (set_compl is_init) (sb G \ rmw G).

Definition rmw_ord := restr_rel (set_compl is_init) (rmw G).

Inductive lab_ty : Set :=
| TyLoad : lab_ty
| TyStore : lab_ty
| TyFence : lab_ty.

Definition e_type e :=
  match lab G e with
  | Aload _ _ _ _ => TyLoad
  | Astore _ _ _ _ => TyStore
  | Afence _ => TyFence
  end.

Definition same_instr x y : Prop :=
  instr (e2instr x) = instr (e2instr y).

Record E2InstrWf : Prop := {
  e2instr_inj : inj_dom (acts_set G ∩₁ set_compl is_init) e2instr;
  nrmwend_even_tick : forall ins,
    tick ↑ restr_rel (fun x => instr x = ins) (e2instr ↑ nrmw_ord)
      ⊆ (fun x y => y = 2 + x)⁺;
  rmw_ticks : forall ins,
    tick ↑ restr_rel (fun x => instr x = ins) (e2instr ↑ rmw_ord)
      ⊆ (fun x y => y = 1 + x)⁺;
  (* instr_ty : funeq e_type same_instr; *)
}.

End MainDefs.

Section SameProg.

Variable G G' : execution.
Variable e2instr e2instr' : actid -> intr_info.

Definition same_prog : Prop :=
  forall e e'
    (SAME_INSTR : instr (e2instr e) = instr (e2instr' e')),
      e_type G = e_type G'.

End SameProg.

End I2Exec.