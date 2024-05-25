From imm Require Import Events Execution imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

Section ExecEqv.

Variable G G' : execution.

Set Implicit Arguments.

Record exec_equiv : Prop := {
  exeeqv_acts : acts_set G ≡₁ acts_set G';
  exeeqv_threads : threads_set G ≡₁ threads_set G';
  exeeqv_lab : lab G = lab G';
  exeeqv_rmw : rmw G ≡ rmw G';
  exeeqv_data : data G ≡ data G';
  exeeqv_addr : addr G ≡ addr G';
  exeeqv_ctrl : ctrl G ≡ ctrl G';
  exeeqv_rmw_dep : rmw_dep G ≡ rmw_dep G';
  exeeqv_rf : rf G ≡ rf G';
  exeeqv_co : co G ≡ co G';
}.

Lemma exeeqv_eq (EQV : exec_equiv) : G = G'.
Proof using.
  (* NOTE: f_equal call is weirdly slow *)
  destruct EQV. destruct G, G'. ins. f_equal.
  all: try apply set_extensionality.
  all: try apply rel_extensionality.
  all: assumption.
Qed.

Lemma exeeqv_sub_sub sc sc'
    (WF : Wf G')
    (SUB : sub_execution G G' sc sc')
    (SUB' : sub_execution G' G sc' sc) :
  exec_equiv.
Proof using.
  assert (HEQ : acts_set G ≡₁ acts_set G').
  { split; eauto using sub_E. }
  constructor; eauto using sub_lab, sub_threads.
  all: rewrite 1?SUB'.(sub_rmw),
               1?SUB'.(sub_data),
               1?SUB'.(sub_addr),
               1?SUB'.(sub_ctrl),
               1?SUB'.(sub_frmw),
               1?SUB'.(sub_rf),
               1?SUB'.(sub_co).
  all: rewrite 1?(wf_rmwE WF),
               1?(wf_dataE WF),
               1?(wf_addrE WF),
               1?(wf_ctrlE WF),
               1?(wf_rmw_depE WF),
               1?WF.(wf_rfE),
               1?WF.(wf_coE) at 2.
  all: repeat apply seq_more; ins.
  all: now apply eqv_rel_more.
Qed.

Lemma exeeqv_sub_same_acts
    (WF : Wf G')
    (SUB : sub_execution G' G ∅₂ ∅₂)
    (ENUM_D : acts_set G' \₁ acts_set G ≡₁ ∅) :
  exec_equiv.
Proof using.
  assert (E_EQ : acts_set G' ≡₁ acts_set G).
  { split; [ now apply set_subsetE | apply SUB.(sub_E)]. }
  constructor; try now apply SUB.
  all: rewrite 1?(wf_rmwE WF),
               1?(wf_dataE WF),
               1?(wf_addrE WF),
               1?(wf_ctrlE WF),
               1?(wf_rmw_depE WF),
               1?WF.(wf_rfE),
               1?WF.(wf_coE).
  all: rewrite 1?SUB.(sub_rmw),
               1?SUB.(sub_data),
               1?SUB.(sub_addr),
               1?SUB.(sub_ctrl),
               1?SUB.(sub_frmw),
               1?SUB.(sub_rf),
               1?SUB.(sub_co).
  all: try now (repeat apply seq_more; ins; now apply eqv_rel_more).
  now symmetry.
Qed.

Lemma sub_eq
    (WF_G : Wf G')
    (PREFIX : sub_execution G' G ∅₂ ∅₂)
    (ENUM_D : acts_set G' \₁ acts_set G ≡₁ ∅) :
  G = G'.
Proof using.
  apply exeeqv_eq. now apply exeeqv_sub_same_acts.
Qed.

End ExecEqv.