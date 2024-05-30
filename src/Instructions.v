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

Record instruction_id : Set := {
  instr_id : nat;
  tick : nat;
}.

Variable G : execution.
Variable e2instr : actid -> instruction_id.

Definition rmw_end := codom_rel (rmw G).

Definition nrmw_ord := restr_rel (set_compl is_init) (sb G \ rmw G).

Definition rmw_ord := restr_rel (set_compl is_init) (rmw G).

(* TODO: express via inclusion stuff *)
Record E2InstrWf : Prop := {
  e2instr_inj : inj_dom (acts_set G ∩₁ set_compl is_init) e2instr;
  nrmwend_even_tick : forall instr,
    tick ↑ restr_rel (fun x => instr_id x = instr) (e2instr ↑ nrmw_ord)
      ⊆ (fun x y => y = 2 + x);
  rmw_ticks : forall instr,
    tick ↑ restr_rel (fun x => instr_id x = instr) (e2instr ↑ rmw_ord)
      ⊆ (fun x y => y = 1 + x);
}.

End MainDefs.

End I2Exec.