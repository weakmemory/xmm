Require Import ReordSimrel ReorderingEq ReorderingMapper.
Require Import ReorderingRpo ReorderingNewGraph ReorderingFakeSrf.
Require Import AuxDef.
Require Import Core MapDoms.
Require Import AuxRel AuxRel2 AuxRel3.
Require Import Srf Rhb.
Require Import HbPrefix.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import SubToFullExec.
Require Import ReorderingFakeSrf.
Require Import Thrdle.
Require Import StepOps.
Require Import ConsistencyReadExtentGen.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco SubExecution.
Require Import Setoid Morphisms Program.Basics.
Require Import xmm_s_hb.

Set Implicit Arguments.

Section ReordGraphs.

Variable X_t : WCore.t.
Variable a_t b_t : actid.
Variable l_a : label.

Notation "'G_t'" := (WCore.G X_t).

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'same_val_t'" := (same_val lab_t).
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
Notation "'hb_t'" := (hb G_t).
Notation "'rhb_t'" := (rhb G_t).
Notation "'W_t'" := (fun x => is_true (is_w lab_t x)).
Notation "'R_t'" := (fun x => is_true (is_r lab_t x)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).
Notation "'Rlx_t'" := (fun e => is_true (is_rlx lab_t e)).
Notation "'Acq_t'" := (fun e => is_true (is_acq lab_t e)).
Notation "'Rel_t'" := (fun e => is_true (is_rel lab_t e)).

Notation "'mapper'" := (mapper a_t b_t).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'A_s'" := (extra_a X_t a_t b_t b_t).
Notation "'B_s''" := (extra_a X_t a_t b_t a_t).

Notation "'X_s'''" := (rsr_immx X_t a_t b_t).
Notation "'G_s'''" := (WCore.G X_s'').
Notation "'lab_s'''" := (lab G_s'').
Notation "'val_s'''" := (val lab_s'').
Notation "'loc_s'''" := (loc lab_s'').
Notation "'same_loc_s'''" := (same_loc lab_s'').
Notation "'same_val_s'''" := (same_val lab_s'').
Notation "'E_s'''" := (acts_set G_s'').
Notation "'loc_s'''" := (loc lab_s'').
Notation "'sb_s'''" := (sb G_s'').
Notation "'rf_s'''" := (rf G_s'').
Notation "'co_s'''" := (co G_s'').
Notation "'rmw_s'''" := (rmw G_s'').
Notation "'rpo_imm_s'''" := (rpo_imm G_s'').
Notation "'rpo_s'''" := (rpo G_s'').
Notation "'sw_s'''" := (sw G_s'').
Notation "'rmw_dep_s'''" := (rmw_dep G_s'').
Notation "'data_s'''" := (data G_s'').
Notation "'ctrl_s'''" := (ctrl G_s'').
Notation "'addr_s'''" := (addr G_s'').
Notation "'W_s'''" := (fun x => is_true (is_w lab_s'' x)).
Notation "'R_s'''" := (fun x => is_true (is_r lab_s'' x)).
Notation "'F_s'''" := (fun x => is_true (is_f lab_s'' x)).
Notation "'vf_s'''" := (vf G_s'').
Notation "'srf_s'''" := (srf G_s'').
Notation "'rhb_s'''" := (rhb G_s'').
Notation "'Loc_s_''' l" := (fun e => loc_s'' e = l) (at level 1).
Notation "'Val_s_''' l" := (fun e => val_s'' e = l) (at level 1).
Notation "'Rlx_s'''" := (fun e => is_true (is_rlx lab_s'' e)).
Notation "'Acq_s'''" := (fun e => is_true (is_acq lab_s'' e)).
Notation "'Rel_s'''" := (fun e => is_true (is_rel lab_s'' e)).
Notation "'drf_s'''" := (fake_srf G_s'' b_t l_a ⨾ ⦗A_s ∩₁ WCore.lab_is_r l_a⦘).

Notation "'X_s'" := (rsr_Xs X_t a_t b_t l_a).
Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'same_val_s'" := (same_val lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_imm_s'" := (rpo_imm G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'sw_s'" := (sw G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun x => is_true (is_w lab_s x)).
Notation "'R_s'" := (fun x => is_true (is_r lab_s x)).
Notation "'F_s'" := (fun x => is_true (is_f lab_s x)).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).
Notation "'Acq_s'" := (fun e => is_true (is_acq lab_s e)).
Notation "'Rel_s'" := (fun e => is_true (is_rel lab_s e)).

Hypothesis INV : reord_step_pred X_t a_t b_t.

Hypothesis LVAL : dom_rel drf_s'' ⊆₁ Val_s_'' (WCore.lab_val l_a).
Hypothesis NLOC : A_s ⊆₁ set_compl (Loc_t_ (WCore.lab_loc l_a)).
Hypothesis ARW : A_s ⊆₁ WCore.lab_is_r l_a ∪₁ WCore.lab_is_w l_a.
Hypothesis ARLX : A_s ⊆₁ fun _ => mode_le (WCore.lab_mode l_a) Orlx.

Lemma rsr_rex_a_rlx :
  A_s ⊆₁ set_compl (Acq_s ∪₁ Rel_s).
Proof using INV ARLX.
  clear - INV ARLX.
  unfold extra_a; desf.
  assert (RLX : mode_le (WCore.lab_mode l_a) Orlx).
  { apply (ARLX b_t), extra_a_some; desf. }
  unfolder in *. intros x XEQ. subst x.
  simpl. unfold lab_s_. desf; [| tauto].
  unfold is_acq, is_rel, mod, compose.
  rewrite rsr_mapper_bt, upds by apply INV.
  unfold WCore.lab_mode in RLX.
  destruct l_a; ins; desf.
  all: unfold is_true; apply and_not_or.
  all: split; congruence.
Qed.

Lemma rsr_rex_nsloc :
  A_s ⊆₁ fun x => ~same_loc_s a_t x.
Proof using INV NLOC.
  clear - NLOC INV.
  unfold extra_a; desf.
  unfolder in *. intros x XEQ. subst x.
  simpl. unfold lab_s_. desf; [| tauto].
  unfold same_loc, loc, compose.
  rewrite rsr_mapper_bt, rsr_mapper_at by apply INV.
  rewrite updo, upds by (symmetry; apply INV).
  apply NLOC, extra_a_some; desf.
Qed.

Lemma rsr_rex_a_rw :
  A_s ⊆₁ R_s ∪₁ W_s.
Proof using INV ARW.
  clear - ARW INV.
  unfold extra_a; desf.
  unfolder in *. intros x XEQ. subst x.
  simpl. unfold lab_s_. desf; [| tauto].
  unfold is_r, is_w, compose.
  rewrite rsr_mapper_bt, upds by apply INV.
  unfold WCore.lab_is_r, WCore.lab_is_w in *.
  desf; eauto. forward apply (ARW b_t); [| basic_solver].
  apply extra_a_some; auto.
Qed.

Lemma rsr_rex_b_rlx :
  E_s ∩₁ eq a_t ⊆₁ set_compl (Acq_s ∪₁ Rel_s).
Proof using INV ARLX.
  clear - INV ARLX.
  assert (NEQ : a_t <> b_t) by apply INV.
  change E_s with (E_s'' ∪₁ A_s).
  rewrite set_inter_union_l.
  arewrite (A_s ∩₁ eq a_t ⊆₁ ∅).
  { unfold extra_a; desf; basic_solver. }
  rewrite set_union_empty_r.
  intros x (XIN & XEQ). subst x.
  enough (RLX : set_compl (Acq_s'' ∪₁ Rel_s'') a_t).
  { forward apply RLX. unfolder.
    unfold is_acq, is_rel, mod in *.
    rewrite <- rsr_rexi; auto. }
  enough (RLX : set_compl (Acq_t ∪₁ Rel_t) b_t).
  { forward apply RLX. unfolder. simpl.
    unfold is_acq, is_rel, mod, compose.
    now rewrite (rsr_mapper_at NEQ). }
  apply set_subset_single_l. rewrite set_unionC.
  rewrite <- (rsr_bt_rlx INV). apply set_subset_single_l.
  split; auto. ins. unfolder in XIN. desf.
  enough (y = b_t) by congruence.
  now apply (rsr_mapper_inv_at _ NEQ).
Qed.

Lemma rsr_rex_b_rw :
  E_s ∩₁ eq a_t ⊆₁ R_s ∪₁ W_s.
Proof using INV ARW.
  clear - INV ARW.
  assert (NEQ : a_t <> b_t) by apply INV.
  change E_s with (E_s'' ∪₁ A_s).
  rewrite set_inter_union_l.
  arewrite (A_s ∩₁ eq a_t ⊆₁ ∅).
  { unfold extra_a; desf; basic_solver. }
  rewrite set_union_empty_r.
  intros x (XIN & XEQ). subst x.
  enough (RW : (R_s'' ∪₁ W_s'') a_t).
  { forward apply RW. unfolder.
    unfold is_w, is_r in *.
    rewrite <- rsr_rexi; auto. }
  enough (RW : (R_t ∪₁ W_t) b_t).
  { forward apply RW. unfolder. simpl.
    unfold is_r, is_w, compose.
    now rewrite (rsr_mapper_at NEQ). }
  apply set_subset_single_l. rewrite set_unionC.
  rewrite <- (rsr_b_t_is_r_or_w INV). apply set_subset_single_l.
  split; auto. ins. unfolder in XIN. desf.
  enough (y = b_t) by congruence.
  now apply (rsr_mapper_inv_at _ NEQ).
Qed.

Lemma rsr_vfsb_helper
    (ISR : R_s b_t)
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  vf_s'' ⨾ sb_s ⨾ ⦗eq b_t⦘ ⊆
    vf_s ⨾ sb_s ⨾ ⦗eq b_t⦘.
Proof using.
Admitted.

Lemma rsr_vfsb
    (ISR : R_s b_t)
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  vf_s ⨾ sb_s ⨾ ⦗eq b_t⦘ ≡
    vf_s'' ⨾ sb_s ⨾ ⦗eq b_t⦘.
Proof using INV.
  assert (BIN : E_s a_t) by admit.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (RPOEX : codom_rel (⦗eq b_t⦘ ⨾ rpo_s) ≡₁ ∅).
  { split; auto with hahn.
    rewrite reord_rpo_emp with (b := b_t) (a := a_t).
    { clear. basic_solver. }
    { transitivity (set_compl (Acq_s ∪₁ Rel_s)); [| basic_solver].
      now rewrite <- rsr_rex_a_rlx, extra_a_some by auto. }
    { transitivity (set_compl (Acq_s ∪₁ Rel_s)); [| basic_solver].
      rewrite <- rsr_rex_b_rlx. basic_solver. }
    { rewrite <- rsr_rex_b_rw. basic_solver. }
    { now rewrite <- rsr_rex_a_rw, extra_a_some by auto. }
    now apply rsr_rex_froma. }
  assert (RPONA : rpo_s ⨾ ⦗E_s \₁ eq b_t⦘ ⊆ id ↑ rpo_s'').
  { apply reord_map_rpo with (a := a_t); auto.
    { now apply new_G_s_wf. }
    { simpl. right. apply extra_a_some; auto. }
    { arewrite (eq b_t ≡₁ A_s).
      { rewrite extra_a_some; auto. }
      change (E_s) with (E_s'' ∪₁ A_s).
      rewrite set_minus_union_l, set_minusK, set_collect_id.
      rewrite set_minus_disjoint; [basic_solver |].
      rewrite (rsr_exa_notin_imm INV). basic_solver. }
    { rewrite Combinators.compose_id_right.
      apply (rsr_rexi _ INV). }
    { clear. basic_solver. }
    { transitivity (set_compl (Acq_s ∪₁ Rel_s)); [| basic_solver].
      now rewrite <- rsr_rex_a_rlx, extra_a_some by auto. }
    { transitivity (set_compl (Acq_s ∪₁ Rel_s)); [| basic_solver].
      rewrite <- rsr_rex_b_rlx. basic_solver. }
    { rewrite <- rsr_rex_b_rw. basic_solver. }
    { now rewrite <- rsr_rex_a_rw, extra_a_some by auto. }
    { now apply rsr_rex_froma. }
    rewrite collect_rel_id.
    arewrite (eq b_t ≡₁ A_s).
    { unfold extra_a. desf. tauto. }
    arewrite (E_s \₁ A_s ≡₁ E_s'').
    { change E_s with (E_s'' ∪₁ A_s).
      rewrite set_minus_union_l, set_minusK.
      rewrite set_minus_disjoint; [basic_solver |].
      rewrite (rsr_exa_notin_imm INV). basic_solver. }
    unfold sb. basic_solver. }
  assert (INJ : inj_dom E_s'' id) by (clear; basic_solver).
  assert (EQACTS : E_s ≡₁ id ↑₁ E_s'' ∪₁ eq b_t).
  { change E_s with (E_s'' ∪₁ A_s).
    rewrite set_collect_id, extra_a_some; auto. }
  assert (EQRF : rf_s ≡ id ↑ rf_s'' ∪ drf_s'' ⨾ ⦗eq b_t⦘).
  { change rf_s with (rf_s'' ∪ drf_s'').
    rewrite collect_rel_id, extra_a_some by auto.
    basic_solver 11. }
  assert (EQCO : co_s ≡ id ↑ co_s'').
  { change co_s with (
      co_s'' ∪
          (E_s'' ∩₁ W_s'' ∩₁ Loc_s_'' (WCore.lab_loc l_a)) ×
          (A_s ∩₁ WCore.lab_is_w l_a)
    ).
    rewrite collect_rel_id.
    arewrite (A_s ∩₁ WCore.lab_is_w l_a ≡₁ ∅).
    { split; auto with hahn.
      rewrite extra_a_some; auto.
      rewrite <- (rsr_rex_isw_helper l_a INV); auto.
      forward apply ISR. clear.
      unfold is_r, is_w. basic_solver. }
    now rewrite cross_false_r, union_false_r. }
  assert (DISJ : set_disjoint (id ↑₁ E_s'') (eq b_t)).
  { rewrite set_collect_id. simpl.
    unfold set_disjoint. intros x XIN XEQ. subst x.
    apply NINA. red in XIN. desf.
    enough (y = a_t) by congruence.
    now apply (rsr_mapper_inv_bt _ NEQ). }
  assert (EQDOM : eq_dom E_s'' (lab_s ∘ id) lab_s'').
  { rewrite Combinators.compose_id_right.
    symmetry. apply (rsr_rexi l_a INV). }
  assert (EQRMW : rmw_s ≡ id ↑ rmw_s'').
  { rewrite collect_rel_id. reflexivity. }
  assert (ANACQ : ~ is_acq lab_s b_t).
  { enough (RLX : set_compl (Acq_s ∪₁ Rel_s) b_t).
    { forward apply RLX. clear. basic_solver. }
    now apply rsr_rex_a_rlx, extra_a_some. }
  assert (SUBINIT : is_init ∩₁ E_s ⊆₁ E_s'').
  { admit. }
  assert (SBLOCEX : codom_rel (⦗eq b_t⦘ ⨾ sb_s ∩ same_loc_s) ≡₁ ∅).
  { admit. }
  assert (SBLOCA : sb_s ∩ same_loc_s ⨾ ⦗E_s \₁ eq b_t⦘ ⊆ id ↑ (sb_s'' ∩ same_loc_s'')).
  { admit. }
  split; [| now apply rsr_vfsb_helper].
  seq_rewrite sbvf_as_rhb.
  arewrite (
    vf_s'' ⨾ sb_s ⨾ ⦗eq b_t⦘ ≡
      vf_rhb G_s'' ⨾ sb_s ⨾ ⦗eq b_t⦘
  ).
  { arewrite (sb_s ⨾ ⦗eq b_t⦘ ≡ sb_s'' ⨾ ⦗eq b_t⦘).
    { admit. }
    rewrite <- !seqA. apply seq_more; [| reflexivity].
    apply sbvf_as_rhb. }
  arewrite (
    sb_s ⨾ ⦗eq b_t⦘ ⊆
      ⦗E_s \₁ eq b_t⦘ ⨾ sb_s ⨾ ⦗eq b_t⦘
  ) at 1.
  { rewrite wf_sbE at 1.
    unfolder. intros x y (XIN & SB & YEQ & YIN).
    splits; auto. intro FALSO; desf.
    eapply sb_irr; eauto. }
  unfold vf_rhb. rewrite !seqA.
  arewrite (
    rhb_s^? ⨾ ⦗E_s \₁ eq b_t⦘ ⊆
      ⦗E_s \₁ eq b_t⦘ ⨾ rhb_s^? ⨾ ⦗E_s \₁ eq b_t⦘
  ).
  { rewrite !crE, !seq_union_l, !seq_union_r.
    apply union_mori; [basic_solver |].
    apply XmmCons.read_rhb_start
      with (m := id) (G_t := G_s'') (drf := drf_s'').
    all: eauto using new_G_s_wf, rsr_imm_Gs_wf. }
  arewrite (
    rf_s^? ⨾ ⦗E_s \₁ eq b_t⦘ ⊆
      ⦗E_s \₁ eq b_t⦘ ⨾ rf_s''^?
  ).
  { admit. }
  arewrite (
    ⦗E_s⦘ ⨾ ⦗W_s⦘ ⨾ ⦗E_s \₁ eq b_t⦘ ⊆
      ⦗E_s''⦘ ⨾ ⦗W_s''⦘
  ).
  { admit. }
  arewrite (
    rhb_s^? ⨾ ⦗E_s \₁ eq b_t⦘ ⊆
      rhb_s''^? ⨾ ⦗E_s \₁ eq b_t⦘
  ); [| do 3 (apply seq_mori; auto with hahn); basic_solver 7].
  rewrite !crE, !seq_union_l.
  apply union_mori; [reflexivity |].
  transitivity (rhb_s ⨾ ⦗E_s \₁ eq b_t⦘ ⨾ ⦗E_s \₁ eq b_t⦘ ).
  { clear. basic_solver. }
  rewrite <- seqA.
  rewrite XmmCons.read_rhb_sub
      with (m := id) (G_t := G_s'') (drf := drf_s'').
  all: auto.
  { now rewrite collect_rel_id. }
  { apply (rsr_imm_Gs_wf INV). }
  apply (new_G_s_wf INV LVAL).
Admitted.

Lemma rsr_srf_eq :
  drf_s'' ≡ srf_s ⨾ ⦗A_s ∩₁ R_s⦘.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold extra_a; desf; [| basic_solver].
  arewrite (
    eq b_t ∩₁ R_s ≡₁ eq b_t ∩₁ WCore.lab_is_r l_a
  ).
  { apply (rsr_rex_isr_helper l_a INV); desf. }
  apply fake_srf_is_srf.
  { apply (rsr_imm_Gs_wf INV). }
  { admit. }
  { admit. }
  { simpl. unfold lab_s_; desf; [| tauto].
    rewrite upd_compose; auto with xmm.
    now rewrite rsr_mapper_bt; auto. }
  { admit. }
  admit.
Admitted.

Lemma rsr_exa_correct :
  A_s ⊆₁ extra_a_pred X_s a_t b_t.
Proof using INV NLOC LVAL ARW ARLX.
  intros x XIN. constructor.
  { unfold extra_a in XIN. desf. }
  { transitivity rf_s; [| apply (new_G_s_wf INV LVAL)].
    arewrite (eq x ≡₁ A_s).
    { split; [basic_solver |].
      unfold extra_a in *. desf. }
    rewrite <- rsr_srf_eq.
    simpl. basic_solver. }
  { now apply rsr_rex_nsloc. }
  { apply set_subset_single_l.
    rewrite set_unionC.
    rewrite <- rsr_rex_a_rlx. basic_solver. }
  now apply rsr_rex_a_rw.
Qed.

End ReordGraphs.