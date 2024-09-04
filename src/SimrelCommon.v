From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Program.Basics.

Require Import Core.

Open Scope program_scope.

Set Implicit Arguments.

Section SimRel.

Variable X_s X_t : WCore.t.
Variable a_t b_t : actid.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'W_t'" := (fun e => is_true (is_w lab_t e)).
Notation "'R_t'" := (fun e => is_true (is_r lab_t e)).
Notation "'F_t'" := (fun e => is_true (is_f lab_t e)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).
Notation "'Val_t_' l" := (fun e => val_t e = l) (at level 1).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'same_val_t'" := (same_val lab_t).

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'W_s'" := (fun e => is_true (is_w lab_s e)).
Notation "'R_s'" := (fun e => is_true (is_r lab_s e)).
Notation "'F_s'" := (fun e => is_true (is_f lab_s e)).
Notation "'b_s'" := (mapper b_t).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'same_val_s'" := (same_val lab_s).

Record simrel_common : Prop := {
  sico_init : fixset is_init mapper;
  sico_inj : inj_dom E_t mapper;
  sico_codom : mapper ↑₁ E_t ⊆₁ E_s;
  sico_lab : eq_dom E_t (lab_s ∘ mapper) lab_t;
}.

Hypothesis WF_T : Wf G_t.
Hypothesis SICO : simrel_common.

Lemma sico_init_acts_s
    (INIT : is_init ⊆₁ E_t) :
  is_init ⊆₁ E_s.
Proof using SICO.
  rewrite <- (sico_codom SICO), <- INIT.
  apply (fixset_set_fixpoint (sico_init SICO)).
Qed.

Lemma sico_rfE :
  mapper ↑ rf_t ⊆ E_s × E_s.
Proof using SICO WF_T.
  rewrite (wf_rfE WF_T), <- (sico_codom SICO).
  basic_solver.
Qed.

Lemma sico_coE :
  mapper ↑ co_t ⊆ E_s × E_s.
Proof using SICO WF_T.
  rewrite (wf_coE WF_T), <- (sico_codom SICO).
  basic_solver.
Qed.

Lemma sico_rmwE :
  mapper ↑ rmw_t ⊆ E_s × E_s.
Proof using SICO WF_T.
  rewrite (wf_rmwE WF_T), <- (sico_codom SICO).
  basic_solver.
Qed.

Lemma sico_lab' e
    (INE : E_t e) :
  lab_t e = lab_s (mapper e).
Proof using SICO.
  rewrite <- (sico_lab SICO); [| exact INE].
  unfold compose. reflexivity.
Qed.

Lemma sico_rfD :
  mapper ↑ rf_t ⊆ W_s × R_s.
Proof using SICO WF_T.
  rewrite (wf_rfE WF_T), (wf_rfD WF_T).
  unfolder. ins. desf. unfold is_w, is_r in *.
  rewrite <- !sico_lab'; auto.
Qed.

Lemma sico_coD :
  mapper ↑ co_t ⊆ W_s × W_s.
Proof using SICO WF_T.
  rewrite (wf_coE WF_T), (wf_coD WF_T).
  unfolder. ins. desf. unfold is_w in *.
  rewrite <- !sico_lab'; auto.
Qed.

Lemma sico_rmwD :
  mapper ↑ rmw_t ⊆ R_s × W_s.
Proof using SICO WF_T.
  rewrite (wf_rmwE WF_T), (wf_rmwD WF_T).
  unfolder. ins. desf. unfold is_w, is_r in *.
  rewrite <- !sico_lab'; auto.
Qed.

Lemma sico_col :
  mapper ↑ co_t ⊆ same_loc_s.
Proof using SICO WF_T.
  rewrite (wf_coE WF_T), (wf_col WF_T).
  unfolder. ins. desf. unfold same_loc, loc in *.
  rewrite <- !sico_lab'; auto.
Qed.

Lemma sico_rmwl :
  mapper ↑ rmw_t ⊆ same_loc_s.
Proof using SICO WF_T.
  rewrite (wf_rmwE WF_T), (wf_rmwl WF_T).
  unfolder. ins. desf. unfold same_loc, loc in *.
  rewrite <- !sico_lab'; auto.
Qed.

Lemma sico_rfv :
  mapper ↑ rf_t ⊆ same_val_s.
Proof using SICO WF_T.
  rewrite (wf_rfE WF_T).
  unfolder. ins. desf. unfold same_val, val in *.
  rewrite <- !sico_lab'; auto.
  now apply WF_T.
Qed.

Lemma sico_co_total ol :
  is_total
    (mapper ↑₁ E_t ∩₁ W_s ∩₁ Loc_s_ ol)
    (mapper ↑ co_t).
Proof using SICO WF_T.
  rewrite !set_interA. unfolder.
  intros x ((x' & XINE & XEQ) & XW & XL)
          y ((y' & YINE & YEQ) & YW & YL)
          NEQ.
  subst x. subst y.
  assert (NEQ' : x' <> y') by congruence.
  destruct (wf_co_total WF_T) with (ol := ol) (a := x') (b := y').
  all: unfold is_w, loc in *; unfolder.
  all: rewrite ?sico_lab'; eauto 11.
Qed.

Lemma sico_rff :
  functional (mapper ↑ rf_t)⁻¹.
Proof using SICO WF_T.
  rewrite (wf_rfE WF_T).
  rewrite <- collect_rel_transp, <- restr_relE,
          <- restr_transp.
  apply functional_collect_rel_inj; [apply SICO|].
  rewrite restr_transp, restr_relE, <- (wf_rfE WF_T).
  apply WF_T.
Qed.

Lemma sico_co_irr :
  irreflexive (mapper ↑ co_t).
Proof using SICO WF_T.
  rewrite (wf_coE WF_T), <- restr_relE.
  apply collect_rel_irr_inj; [apply SICO|].
  rewrite restr_relE, <- (wf_coE WF_T).
  apply WF_T.
Qed.

Lemma sico_co_trans :
  transitive (mapper ↑ co_t).
Proof using SICO WF_T.
  rewrite (wf_coE WF_T), <- restr_relE.
  apply transitive_collect_rel_inj; [apply SICO|].
  rewrite restr_relE, <- (wf_coE WF_T).
  apply WF_T.
Qed.

Lemma sico_mapper_swap e e' r
    (NINE : ~E_t e)
    (REL : r ≡ ⦗E_t⦘ ⨾ r ⨾ ⦗E_t⦘) :
  (upd mapper e e') ↑ r ≡ mapper ↑ r.
Proof using.
  rewrite REL. clear - NINE.
  unfolder; split; intros x y (x' & y' & HREL).
  all: eexists x', y'; desf.
  all: rewrite !updo by congruence.
  all: eauto 11.
Qed.

End SimRel.