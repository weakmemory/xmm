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
Notation "'hb_s'''" := (hb G_s'').
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
Notation "'hb_s'" := (hb G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).
Notation "'Acq_s'" := (fun e => is_true (is_acq lab_s e)).
Notation "'Rel_s'" := (fun e => is_true (is_rel lab_s e)).

Hypothesis INV : reord_step_pred X_t a_t b_t.

Hypothesis LVAL : dom_rel drf_s'' ⊆₁ Val_s_'' (WCore.lab_val l_a).
Hypothesis NLOC : A_s ⊆₁ fun _ => WCore.lab_loc l_a <> loc_t b_t.
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
  assert (NEQ : a_t <> b_t) by apply INV.
  clear - NLOC INV.
  unfold extra_a; desf.
  unfolder in *. intros x XEQ. subst x.
  intro FALSO. apply NLOC with b_t.
  { apply extra_a_some; desf. }
  unfold same_loc in FALSO.
  rewrite <- (rsr_rex_labloc_helper l_a INV) by desf.
  arewrite (loc_t b_t = loc_s a_t); [| congruence].
  simpl. unfold lab_s_, compose; desf; [| tauto].
  unfold loc. rewrite rsr_mapper_at, updo; congruence.
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
Proof using INV LVAL.
  clear - INV LVAL ISR INB NINA.
  assert (WF_s : Wf G_s'').
  { apply (rsr_imm_Gs_wf INV). }
  arewrite (
    sb_s ⨾ ⦗eq b_t⦘ ≡
      ⦗E_s''⦘ ⨾ sb_s ⨾ ⦗eq b_t⦘
  ).
  { arewrite (E_s'' ≡₁ E_s \₁ eq b_t).
    { change E_s with (E_s'' ∪₁ A_s).
      rewrite extra_a_some by auto.
      rewrite set_minus_union_l, set_minusK.
      rewrite set_union_empty_r, set_minus_disjoint; [reflexivity |].
      simpl. unfolder. intros x' (x & XIN & XEQ) XEQ'.
      subst x'. apply NINA.
      enough (x = a_t) by congruence.
      eapply rsr_mapper_inv_bt; eauto.
      apply INV. }
    split; [| basic_solver].
    clear. unfolder. intros x y (SB & YEQ).
    splits; auto.
    { apply wf_sbE in SB. unfolder in SB. desf. }
    intro XEQ. subst x y. eapply sb_irr; eauto. }
  rewrite <- !seqA with (r2 := ⦗E_s''⦘).
  apply seq_mori; [| reflexivity].
  unfold vf. rewrite !seqA.
  assert (SUBACTS : E_s'' ⊆₁ E_s).
  { apply rsr_imm_G_sub. }
  arewrite (⦗E_s''⦘ ⨾ ⦗W_s''⦘ ⊆ ⦗E_s''⦘ ⨾ ⦗W_s⦘).
  { rewrite <- !id_inter. apply eqv_rel_mori.
    rewrite 2!set_interC with (s := E_s'').
    eapply set_inter_is_w; try reflexivity.
    symmetry. apply (rsr_rexi l_a INV). }
  enough (HBSUB :
    hb_s''^? ⨾ ⦗E_s''⦘ ⊆ ⦗E_s''⦘ ⨾ hb_s^? ⨾ ⦗E_s''⦘
  ).
  { sin_rewrite HBSUB. rewrite <- !seqA.
    do 2 (apply seq_mori; [| basic_solver]).
    rewrite !seqA.
    rewrite !crE, !seq_union_l, !seq_union_r.
    apply union_mori; [basic_solver 11 |].
    change (rf_s) with (rf_s'' ∪ drf_s'').
    rewrite !seq_union_r.
    apply inclusion_union_r. left. basic_solver 11. }
  rewrite !crE.
  rewrite !seq_union_l, !seq_union_r.
  apply union_mori; [basic_solver |].
  enough (HBSUB : hb_s'' ⊆ hb_s).
  { rewrite (wf_hbE WF_s).
    rewrite HBSUB. clear. basic_solver 11. }
  unfold hb. apply clos_trans_mori.
  apply union_mori.
  { unfold sb. rewrite SUBACTS. reflexivity. }
  unfold sw.
  rewrite (wf_rfE WF_s), !seqA.
  arewrite (rf_s'' ⊆ rf_s).
  { simpl. apply inclusion_union_r. now left. }
  assert (RSE :
    rs G_s'' ⨾ ⦗E_s''⦘ ⊆
      ⦗E_s''⦘ ⨾ rs G_s'' ⨾ ⦗E_s''⦘
  ).
  { unfold rs. rewrite <- cr_of_ct.
    rewrite crE, !seq_union_r, !seq_union_l.
    rewrite !seq_union_r.
    apply union_mori; [basic_solver |].
    rewrite ct_begin at 1.
    arewrite (
      (rf_s'' ⨾ rmw_s'') ⊆
        ⦗E_s''⦘ ⨾ (rf_s'' ⨾ rmw_s'')
    ) at 1.
    { rewrite (wf_rfE WF_s). basic_solver 11. }
    arewrite (
      rf_s'' ⨾ rmw_s'' ⨾ (rf_s'' ⨾ rmw_s'')＊ ⊆
        (rf_s'' ⨾ rmw_s'')⁺
    ).
    { now rewrite <- seqA, <- ct_begin. }
    basic_solver 11. }
  assert (RS :
    rs G_s'' ⨾ ⦗E_s''⦘ ⊆
      ⦗E_s''⦘ ⨾ rs G_s ⨾ ⦗E_s''⦘
  ).
  { rewrite RSE. unfold rs. rewrite !seqA.
    arewrite (rf_s'' ⨾ rmw_s'' ⊆ rf_s ⨾ rmw_s).
    { change (rf_s) with (rf_s'' ∪ drf_s'').
      rewrite seq_union_l.
      apply inclusion_union_r. now left. }
    arewrite (⦗E_s''⦘ ⨾ ⦗W_s''⦘ ⊆ ⦗E_s''⦘ ⨾ ⦗W_s⦘).
    { rewrite <- !id_inter.
      apply eqv_rel_mori.
      rewrite 2!set_interC with (s := E_s'').
      eapply set_inter_is_w; try reflexivity.
      symmetry. apply (rsr_rexi l_a INV). }
    reflexivity. }
  assert (FSB' :
    ⦗F_s''⦘ ⨾ sb_s'' ⊆
      ⦗F_s⦘ ⨾ sb_s
  ).
  { unfold sb.
    arewrite (⦗F_s''⦘ ⨾ ⦗E_s''⦘ ⊆ ⦗F_s⦘ ⨾ ⦗E_s''⦘).
    { rewrite <- !id_inter. apply eqv_rel_mori.
      eapply set_inter_is_f; try reflexivity.
      symmetry. apply (rsr_rexi l_a INV). }
    rewrite SUBACTS. reflexivity. }
  assert (FSBE :
    (⦗F_s''⦘ ⨾ sb_s'')^? ⨾ ⦗Rlx_s''⦘ ⨾ ⦗E_s''⦘ ⊆
       ⦗E_s''⦘ ⨾ (⦗F_s''⦘ ⨾ sb_s'')^? ⨾ ⦗Rlx_s''⦘ ⨾ ⦗E_s''⦘
  ).
  { rewrite crE, !seq_union_l, !seq_union_r.
    apply union_mori; [basic_solver |].
    rewrite wf_sbE at 1. basic_solver 11. }
  assert (FSB :
    ⦗Rel_s''⦘ ⨾ (⦗F_s''⦘ ⨾ sb_s'')^? ⨾ ⦗Rlx_s''⦘ ⨾ ⦗E_s''⦘ ⊆
      ⦗Rel_s⦘ ⨾ (⦗F_s⦘ ⨾ sb_s)^? ⨾ ⦗Rlx_s⦘ ⨾ ⦗E_s''⦘
  ).
  { rewrite FSBE, FSB'.
    arewrite (⦗Rel_s''⦘ ⨾ ⦗E_s''⦘ ⊆ ⦗Rel_s⦘ ⨾ ⦗E_s''⦘).
    { rewrite <- !id_inter. apply eqv_rel_mori.
      eapply set_inter_rel; try reflexivity.
      symmetry. apply (rsr_rexi l_a INV). }
    arewrite (⦗Rlx_s''⦘ ⨾ ⦗E_s''⦘ ⊆ ⦗Rlx_s⦘ ⨾ ⦗E_s''⦘).
    { rewrite <- !id_inter. apply eqv_rel_mori.
      eapply set_inter_rlx; try reflexivity.
      symmetry. apply (rsr_rexi l_a INV). }
    clear. basic_solver 11. }
  arewrite (
    release G_s'' ⨾ ⦗E_s''⦘ ⊆ release G_s ⨾ ⦗E_s''⦘
  ).
  { unfold release. rewrite !seqA.
    sin_rewrite RS. sin_rewrite FSB.
    clear. basic_solver 11. }
  arewrite (
    ⦗E_s''⦘ ⨾ ⦗Rlx_s''⦘ ⨾ (sb_s'' ⨾ ⦗F_s''⦘)^? ⊆
      ⦗E_s''⦘ ⨾ ⦗Rlx_s''⦘ ⨾ (sb_s'' ⨾ ⦗F_s''⦘)^? ⨾ ⦗E_s''⦘
  ).
  { rewrite crE. rewrite !seq_union_l, !seq_union_r.
    apply union_mori; [basic_solver 11|].
    rewrite wf_sbE at 1. basic_solver 11. }
  arewrite (⦗E_s''⦘ ⨾ ⦗Rlx_s''⦘ ⊆ ⦗E_s''⦘ ⨾ ⦗Rlx_s⦘).
  { rewrite <- !id_inter. apply eqv_rel_mori.
    rewrite 2!set_interC with (s := E_s'').
    eapply set_inter_rlx; try reflexivity.
    symmetry. apply (rsr_rexi l_a INV). }
  arewrite (⦗E_s''⦘ ⨾ ⦗Acq_s''⦘ ⊆ ⦗E_s''⦘ ⨾ ⦗Acq_s⦘).
  { rewrite <- !id_inter. apply eqv_rel_mori.
    rewrite 2!set_interC with (s := E_s'').
    eapply set_inter_acq; try reflexivity.
    symmetry. apply (rsr_rexi l_a INV). }
  arewrite (sb_s'' ⨾ ⦗F_s''⦘ ⊆ sb_s ⨾ ⦗F_s⦘).
  { rewrite wf_sbE at 1.
    rewrite !seqA.
    rewrite <- id_inter.
    rewrite set_interC, set_inter_is_f with (G := G_s).
    all: try (reflexivity || (symmetry; apply (rsr_rexi l_a INV))).
    unfold sb. rewrite SUBACTS.
    clear. basic_solver 11. }
  clear. basic_solver 11.
Qed.

Lemma rsr_vfsb_sb_helper
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  sb_s'' ⨾ ⦗eq a_t⦘ ⨾ sb_s⁻¹ ⨾ ⦗eq b_t⦘ ⊆
    sb_s ⨾ ⦗eq b_t⦘.
Proof using INV.
  unfolder. intros x y (z & XZ & ZEQ & YZ & YEQ).
  subst z y. split; auto. unfold sb. unfolder.
  enough (SB : ext_sb x b_t).
  { splits; auto.
    { left. apply wf_sbE in XZ.
      unfolder in XZ. desf. }
    right. now apply extra_a_some. }
  assert (XZ' : ext_sb x a_t).
  { forward apply XZ. unfold sb. clear. basic_solver. }
  assert (XNA : x <> a_t).
  { intro FALSO. subst x. eapply sb_irr; eauto. }
  assert (XIN : E_s'' x).
  { forward apply XZ. clear. unfold sb. basic_solver. }
  assert (XNB : x <> b_t).
  { intro FALSO. subst x.
    apply NINA. simpl in XIN.
    unfolder in XIN. destruct XIN as (y & YIN & YEQ).
    enough (y = a_t) by congruence.
    eapply rsr_mapper_inv_bt; eauto. }
  apply (rsr_rex_extsb_inv_l INV); auto.
  unfolder in XIN. destruct XIN as (y & YIN & YEQ).
  subst x. rewrite rsr_mappero; auto.
  { intro YEQ. subst y. eauto. }
  intro YEQ. subst y.
  rewrite rsr_mapper_bt in XNA; congruence.
Qed.

Lemma rsr_vfsb
    (ISR : R_s b_t)
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  vf_s ⨾ sb_s ⨾ ⦗eq b_t⦘ ≡
    vf_s'' ⨾ sb_s ⨾ ⦗eq b_t⦘.
Proof using INV LVAL NLOC ARW ARLX.
  assert (BIN : E_s a_t).
  { left. exists b_t. split; auto.
    apply rsr_mapper_bt, INV. }
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
  { clear - INV NINA INB. unfolder. intros x (XINIT & XIN).
    destruct XIN as [XIN | EXA]; auto.
    apply extra_a_some in EXA; auto. subst x.
    exfalso. now apply (rsr_bt_ninit INV). }
  assert (NLOC' : ~same_loc_s b_t a_t).
  { intro SLOC. apply NLOC with b_t.
    { now apply extra_a_some. }
    rewrite <- (rsr_rex_labloc_helper l_a INV); auto.
    arewrite (loc_t b_t = loc_s a_t); [| apply SLOC].
    simpl. unfold lab_s_; desf; [| tauto].
    unfold loc, compose.
    rewrite rsr_mapper_at, updo; congruence. }
  assert (SBLOCEX' : ⦗eq b_t⦘ ⨾ sb_s ∩ same_loc_s ⊆ ∅₂).
  { rewrite <- seq_eqv_inter_ll, rsr_rex_froma.
    all: auto.
    forward apply NLOC'. clear. basic_solver. }
  assert (SBLOCEX : codom_rel (⦗eq b_t⦘ ⨾ sb_s ∩ same_loc_s) ≡₁ ∅).
  { split; auto with hahn.
    rewrite SBLOCEX'. clear. basic_solver. }
  assert (SBLOCA : sb_s ∩ same_loc_s ⨾ ⦗E_s \₁ eq b_t⦘ ⊆ id ↑ (sb_s'' ∩ same_loc_s'')).
  { rewrite collect_rel_id.
    arewrite (
      sb_s ⊆
        ⦗E_s \₁ eq b_t⦘ ⨾ sb_s ∪
        ⦗eq b_t⦘ ⨾ sb_s
    ).
    { rewrite wf_sbE at 1.
      rewrite set_union_minus
        with (s := E_s) (s' := eq b_t)
            ; [| rewrite EQACTS; clear; basic_solver].
      rewrite id_union, !seq_union_l.
      basic_solver 11. }
    rewrite inter_union_l, seq_union_l.
    rewrite seq_eqv_inter_ll
       with (r := sb_s) (S := eq b_t).
    rewrite SBLOCEX', seq_false_l, union_false_r.
    rewrite <- seq_eqv_inter_lr, seqA.
    arewrite (⦗E_s \₁ eq b_t⦘ ⨾ sb_s ⨾ ⦗E_s \₁ eq b_t⦘ ⊆ sb_s'').
    { unfold sb. rewrite EQACTS, set_collect_id.
      clear. basic_solver 11. }
    rewrite wf_sbE at 1.
    rewrite seq_eqv_inter_ll, <- seq_eqv_inter_rl.
    rewrite seq_eqv_inter_lr, <- seq_eqv_inter_rr.
    rewrite seqA.
    apply inter_rel_mori; [reflexivity |].
    unfold same_loc, loc. unfolder.
    intros x y (XIN & SLOC & YIN).
    rewrite 2!(rsr_rexi l_a INV); auto. }
  split; [| now apply rsr_vfsb_helper].
  seq_rewrite sbvf_as_rhb.
  rewrite <- rsr_vfsb_sb_helper; auto.
  seq_rewrite sbvf_as_rhb. rewrite !seqA.
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
  assert (EQACTS' : E_s'' ≡₁ E_s \₁ eq b_t).
  { change E_s with (E_s'' ∪₁ A_s).
    rewrite extra_a_some; auto.
    rewrite set_minus_union_l, set_minusK.
    rewrite set_union_empty_r, set_minus_disjoint; [reflexivity |].
    now rewrite <- set_collect_id with (s := E_s''). }
  arewrite (
    rf_s^? ⨾ ⦗E_s \₁ eq b_t⦘ ⊆
      ⦗E_s \₁ eq b_t⦘ ⨾ rf_s''^?
  ).
  { rewrite !crE, seq_union_l, seq_union_r.
    apply union_mori; [basic_solver |].
    change rf_s with (rf_s'' ∪ drf_s'').
    rewrite seq_union_l.
    arewrite_false (drf_s'' ⨾ ⦗E_s \₁ eq b_t⦘).
    { rewrite extra_a_some; auto. basic_solver. }
    rewrite union_false_r.
    rewrite (wf_rfE (rsr_imm_Gs_wf INV)).
    rewrite EQACTS'. clear. basic_solver 7. }
  arewrite (
    ⦗E_s⦘ ⨾ ⦗W_s⦘ ⨾ ⦗E_s \₁ eq b_t⦘ ⊆
      ⦗E_s''⦘ ⨾ ⦗W_s''⦘
  ).
  { rewrite <- !id_inter. apply eqv_rel_mori.
    rewrite <- EQACTS'.
    rewrite set_inter_is_w with (G := G_s'').
    all: try reflexivity.
    { basic_solver. }
    apply (rsr_rexi l_a INV). }
  arewrite (
    rhb_s^? ⨾ ⦗E_s \₁ eq b_t⦘ ⊆
      rhb_s''^? ⨾ ⦗E_s \₁ eq b_t⦘
  ).
  { rewrite !crE, !seq_union_l.
    apply union_mori; [reflexivity |].
    transitivity (rhb_s ⨾ ⦗E_s \₁ eq b_t⦘ ⨾ ⦗E_s \₁ eq b_t⦘ ).
    { clear. basic_solver. }
    rewrite <- seqA.
    rewrite XmmCons.read_rhb_sub
        with (m := id) (G_t := G_s'') (drf := drf_s'').
    all: auto.
    { now rewrite collect_rel_id. }
    { apply (rsr_imm_Gs_wf INV). }
    apply (new_G_s_wf INV LVAL). }
  enough (INVTRICK :
      sb_s ⨾ ⦗eq b_t⦘ ⊆
      sb_s'' ⨾ ⦗eq a_t⦘ ⨾ sb_s⁻¹ ⨾ ⦗eq b_t⦘
  ).
  { sin_rewrite INVTRICK.
    do 4 (apply seq_mori; [reflexivity |]).
    clear. basic_solver 11. }
  clear - INV NINA INB EQACTS BIN.
  rewrite set_collect_id in EQACTS.
  unfolder. intros x y (XY & YEQ). subst y.
  exists a_t. splits; auto.
  { unfold sb in *. unfolder. unfolder in XY.
    destruct XY as (XIN & SB & _).
    splits; auto.
    { apply EQACTS in XIN.
      destruct XIN as [XIN|XEQ]; auto.
      subst x. exfalso. eapply ext_sb_irr; eauto. }
    { apply ext_sb_trans with b_t; auto.
      apply INV. }
    exists b_t. split; auto.
    apply rsr_mapper_bt, INV. }
  unfold sb. unfolder. splits; auto; [| apply INV].
  right. apply extra_a_some; auto.
Qed.

Lemma rsr_srf_eq :
  drf_s'' ≡ srf_s ⨾ ⦗A_s ∩₁ R_s⦘.
Proof using INV LVAL NLOC ARW ARLX.
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold extra_a; desf; [| basic_solver].
  destruct classic with (~R_s b_t) as [NINR|ISR'].
  { rewrite <- (rsr_rex_isr_helper l_a INV); desf.
    arewrite (eq b_t ∩₁ R_s ≡₁ ∅) by basic_solver.
    now rewrite eqv_empty, !seq_false_r. }
  assert (ISR : R_s b_t) by tauto.
  arewrite (
    eq b_t ∩₁ R_s ≡₁ eq b_t ∩₁ WCore.lab_is_r l_a
  ).
  { apply (rsr_rex_isr_helper l_a INV); desf. }
  apply fake_srf_is_srf.
  { apply (rsr_imm_Gs_wf INV). }
  { unfold sb, fake_sb.
    change (E_s) with (E_s'' ∪₁ A_s).
    rewrite extra_a_some by desf.
    reflexivity. }
  { intros (x & XIN & XEQ).
    enough (x = a_t) by (desf; congruence).
    eapply rsr_mapper_inv_bt; [apply INV | eauto]. }
  { simpl. unfold lab_s_; desf; [| tauto].
    rewrite upd_compose; auto with xmm.
    now rewrite rsr_mapper_bt; auto. }
  { apply rsr_vfsb; auto; desf. }
  change co_s with (co_s'' ∪
    (E_s'' ∩₁ W_s'' ∩₁ Loc_s_'' (WCore.lab_loc l_a)) ×
    (A_s ∩₁ WCore.lab_is_w l_a)
  ).
  rewrite seq_union_l, <- cross_inter_r.
  arewrite (
    A_s ∩₁ WCore.lab_is_w l_a ∩₁ E_s'' ≡₁
      WCore.lab_is_w l_a ∩₁ (A_s ∩₁ E_s'')
  ) by basic_solver.
  arewrite (A_s ∩₁ E_s'' ≡₁ ∅).
  { apply set_disjointE. unfolder.
    intros x XIN XIN'.
    now apply (rsr_exa_notin_imm INV) with x. }
  now rewrite set_inter_empty_r, cross_false_r,
          union_false_r.
Qed.

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