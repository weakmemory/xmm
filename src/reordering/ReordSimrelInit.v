Require Import ReordSimrel.
Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
(* Require Import ThreadTrace. *)
Require Import Core.
(* Require Import TraceSwap. *)
Require Import SubToFullExec.
Require Import AuxRel.
Require Import AuxRel2.
Require Import StepOps.
Require Import Srf Rhb SrfProps.
Require Import AuxInj.
(* Require Import Instructions. *)
Require Import Setoid Morphisms.
Require Import SimrelCommon.
Require Import AddEvent.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
(* From imm Require Import SubExecution. *)
From imm Require Import CombRelations.

Section SimrelInit.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t a_t' b_t' : actid.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_t''" := (WCore.G X_t').
Notation "'G_s'" := (WCore.G X_s).

Notation "'R' G" := (fun e => is_true (is_r (lab G) e)) (at level 1).
Notation "'F' G" := (fun e => is_true (is_f (lab G) e)) (at level 1).
Notation "'W' G" := (fun e => is_true (is_w (lab G) e)) (at level 1).
Notation "'Acq' G" := (fun e => is_true (is_acq (lab G) e)) (at level 1).
Notation "'Rlx' G" := (fun e => is_true (is_rlx (lab G) e)) (at level 1).
Notation "'Rel' G" := (fun e => is_true (is_rel (lab G) e)) (at level 1).

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'W_t'" := (fun x => is_true (is_w lab_t x)).
Notation "'R_t'" := (fun x => is_true (is_r lab_t x)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).

Notation "'lab_t''" := (lab G_t').
Notation "'val_t''" := (val lab_t').
Notation "'loc_t''" := (loc lab_t').
Notation "'same_loc_t''" := (same_loc lab_t').
Notation "'E_t''" := (acts_set G_t').
Notation "'sb_t''" := (sb G_t').
Notation "'rf_t''" := (rf G_t').
Notation "'co_t''" := (co G_t').
Notation "'rmw_t''" := (rmw G_t').
Notation "'rpo_t''" := (rpo G_t').
Notation "'rmw_dep_t''" := (rmw_dep G_t').
Notation "'data_t''" := (data G_t').
Notation "'ctrl_t''" := (ctrl G_t').
Notation "'addr_t''" := (addr G_t').
Notation "'W_t''" := (fun x => is_true (is_w lab_t' x)).
Notation "'R_t''" := (fun x => is_true (is_r lab_t' x)).
Notation "'Loc_t_'' l" := (fun e => loc_t' e = l) (at level 1).

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun x => is_true (is_w lab_s x)).
Notation "'R_s'" := (fun x => is_true (is_r lab_s x)).
Notation "'F_s'" := (F G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (Rlx G_s).
Notation "'Acq_s'" := (Acq G_s).
Notation "'Rel_s'" := (Rel G_s).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Lemma sim_rel_init threads
    (TIDA : tid a_t <> tid_init)
    (NINA : ~is_init a_t)
    (NINB : ~is_init b_t)
    (TIDAB : tid a_t = tid b_t)
    (NEQ : a_t <> b_t)
    (INIT : threads tid_init)
    (ABSB : ext_sb b_t a_t) :
  << SIMREL : reord_simrel
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    a_t b_t
    id >> /\
  << INV : reord_step_pred
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    a_t b_t >>.
Proof using.
  assert (IWF : Wf (WCore.init_exec threads)).
  { now apply WCore.wf_init_exec. }
  assert (AI : eq a_t ∩₁ is_init ≡₁ ∅) by basic_solver.
  assert (BI : eq b_t ∩₁ is_init ≡₁ ∅) by basic_solver.
  split; red.
  all: constructor; ins.
  all: rewrite ?extra_a_none_r by ins.
  { clear; basic_solver. }
  { clear; basic_solver. }
  { clear; basic_solver. }
  { now rewrite cross_false_l,
            cross_false_r, AI, BI, !union_false_r,
            swap_rel_empty_l, collect_rel_id. }
  { clear; basic_solver. }
  { clear; basic_solver. }
  { clear; basic_solver. }
  { rewrite AI, BI, set_collect_empty. clear. basic_solver. }
  { rewrite BI. clear. basic_solver. }
  { rewrite AI. clear. basic_solver. }
  { red. ins. unfold is_r, WCore.init_lab.
    clear. basic_solver. }
  all: rewrite ?AI, ?BI, ?set_minusK.
  all: try now apply set_finite_empty.
  all: rewrite ?dom_empty, ?codom_empty, ?set_union_empty_r.
  all: clear - NINA; try basic_solver.
  unfold ext_sb. unfolder. ins. desf.
Qed.

End SimrelInit.