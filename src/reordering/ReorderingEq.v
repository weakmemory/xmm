Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import SimrelCommon ReordSimrel.
Require Import Lia.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Set Implicit Arguments.

Section ReordEquivLemmas.

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
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'W_t'" := (fun e => is_true (is_w lab_t e)).
Notation "'R_t'" := (fun e => is_true (is_r lab_t e)).
Notation "'F_t'" := (fun e => is_true (is_f lab_t e)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).
Notation "'Val_t_' l" := (fun e => val_t e = l) (at level 1).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'same_val_t'" := (same_val lab_t).
Notation "'Acq_t'" := (fun e => is_true (is_acq lab_t e)).
Notation "'Rel_t'" := (fun e => is_true (is_rel lab_t e)).
Notation "'Rlx_t'" := (fun e => is_true (is_rlx lab_t e)).

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun e => is_true (is_w lab_s e)).
Notation "'R_s'" := (fun e => is_true (is_r lab_s e)).
Notation "'F_s'" := (fun e => is_true (is_f lab_s e)).
Notation "'b_s'" := (mapper b_t).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'same_val_s'" := (same_val lab_s).
Notation "'Acq_s'" := (fun e => is_true (is_acq lab_s e)).
Notation "'Rel_s'" := (fun e => is_true (is_rel lab_s e)).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'extra_a'" := (extra_a X_t a_t b_t).

Hypothesis PRED : reord_step_pred X_t a_t b_t.
Hypothesis SIMREL : reord_simrel X_s X_t a_t b_t mapper.

Lemma rsr_actsE :
  E_s ≡₁ E_t ∪₁ extra_a a_t.
Proof using SIMREL PRED.
  rewrite (rsr_acts SIMREL).
  destruct classic with (E_t a_t) as [INA|NINA],
           classic with (E_t b_t) as [INB|NINB].
  { rewrite !extra_a_none_l, !set_union_empty_r; auto.
    rewrite set_union_minus
      with (s := E_t) (s' := eq a_t ∪₁ eq b_t); [| basic_solver].
    rewrite !set_collect_union, <- set_minus_minus_l.
    rewrite set_collect_eq_dom with (g := id); [| apply SIMREL].
    rewrite <- set_inter_absorb_r
       with (s := eq a_t) (s' := E_t)
         at 2
         by basic_solver.
    rewrite <- set_inter_absorb_r
       with (s := eq b_t) (s' := E_t)
         at 2
         by basic_solver.
    rewrite !set_inter_absorb_r by basic_solver.
    arewrite (mapper ↑₁ eq a_t ≡₁ eq b_t).
    { unfolder. split; ins; desf.
      all: eauto using rsr_map_at.
      symmetry; eauto using rsr_map_at. }
    arewrite (mapper ↑₁ eq b_t ≡₁ eq a_t).
    { unfolder. split; ins; desf.
      all: eauto using rsr_map_bt.
      symmetry; eauto using rsr_map_bt. }
    basic_solver 11. }
  { exfalso. now apply NINB, (rsr_at_bt_ord PRED). }
  { rewrite !extra_a_some by auto.
    rewrite set_union_minus
      with (s := E_t) (s' := eq b_t); [| basic_solver].
    arewrite (E_t ≡₁ E_t \₁ eq a_t).
    { rewrite set_minus_disjoint; basic_solver. }
    rewrite set_collect_union.
    rewrite set_collect_eq_dom with (g := id); [| apply SIMREL].
    rewrite <- set_inter_absorb_r
       with (s := eq b_t) (s' := E_t)
         at 2
         by basic_solver.
    rewrite !set_inter_absorb_r by basic_solver.
    arewrite (mapper ↑₁ eq b_t ≡₁ eq a_t).
    { unfolder. split; ins; desf.
      all: eauto using rsr_map_bt.
      symmetry; eauto using rsr_map_bt. }
    basic_solver 11. }
  rewrite 2!extra_a_none_r, 2!set_union_empty_r; auto.
  arewrite (E_t ≡₁ E_t \₁ eq a_t \₁ eq b_t).
  { rewrite 2!set_minus_disjoint; basic_solver. }
  rewrite set_collect_eq_dom with (g := id); [| apply SIMREL].
  basic_solver 11.
Qed.

Lemma rsr_sbs_dom_disjunct :
  mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘) ≡₁
    dom_rel (sb_t ⨾ ⦗eq b_t⦘).
Proof using SIMREL PRED.
  rewrite set_collect_eq_dom
     with (g := id); [basic_solver 11 |].
  unfolder. intros x (y & SB & YEQ). subst y.
  assert (XIN : E_t x).
  { apply wf_sbE in SB. unfolder in SB. desf. }
  rewrite (rsr_mapper SIMREL); auto.
  rewrite updo; [| intro FALSO; desf; eapply sb_irr; eauto].
  rewrite updo; auto.
  intro FALSO. subst x.
  apply ext_sb_irr with a_t.
  apply ext_sb_trans with b_t.
  { unfold sb in SB; unfolder in SB; desf. }
  apply PRED.
Qed.

Lemma rsr_sbt_map1
    (INB : E_t b_t)
    (NINA : ~E_t a_t) :
  mapper ↑ sb_t ≡
    dom_rel (sb_t ⨾ ⦗eq b_t⦘) × eq a_t ∪
    sb_t ⨾ ⦗set_compl (eq b_t)⦘.
Proof using SIMREL PRED.
  arewrite (
    sb_t ≡
      sb_t ⨾ ⦗eq b_t⦘ ∪
        sb_t ⨾ ⦗set_compl (eq b_t)⦘
  ) at 1.
  { clear. unfolder; split; ins; desf. tauto. }
  rewrite collect_rel_union.
  arewrite (
    sb_t ⨾ ⦗eq b_t⦘ ≡
      dom_rel (sb_t ⨾ ⦗eq b_t⦘) × eq b_t
  ) at 1.
  { basic_solver. }
  rewrite collect_rel_cross,
          rsr_sbs_dom_disjunct,
          set_collect_eq; auto.
  rewrite (rsr_map_bt INB SIMREL); auto.
  apply union_more; auto with hahn.
  rewrite collect_rel_eq_dom
     with (g := id); [basic_solver 11 |].
  arewrite (
    dom_rel (sb_t ⨾ ⦗set_compl (eq b_t)⦘) ⊆₁
      E_t \₁ (eq a_t ∪₁ eq b_t)
  ).
  { rewrite wf_sbE, !seqA.
    unfolder.
    intros x (y & XIN & SB & YIN & NEQ).
    split; auto. intro FALSO; desf.
    eapply (rsr_bt_max PRED); eauto.
    unfolder. splits; eauto. }
  arewrite (
    codom_rel (sb_t ⨾ ⦗set_compl (eq b_t)⦘) ⊆₁
      E_t \₁ (eq a_t ∪₁ eq b_t)
  ).
  { rewrite wf_sbE, !seqA.
    rewrite 2!codom_seq.
    unfolder. ins. desf.
    split; auto. intro FALSO; desf. }
  rewrite set_unionK. unfolder.
  intros x (XIN & NEQ).
  rewrite (rsr_mapper SIMREL); auto.
  assert (NEQ': a_t <> x /\ b_t <> x) by tauto.
  desf. now rewrite !updo by congruence.
Qed.

Lemma rsr_sbt_map2
    (INB : E_t b_t)
    (INA : E_t a_t) :
  mapper ↑ swap_rel
      sb_t
      (eq b_t ∩₁ E_t)
      (eq a_t ∩₁ E_t)
    ≡ sb_t.
Proof using SIMREL PRED.
  arewrite (eq b_t ∩₁ E_t ≡₁ eq b_t) by basic_solver.
  arewrite (eq a_t ∩₁ E_t ≡₁ eq a_t) by basic_solver.
  unfold swap_rel. rewrite collect_rel_union.
  rewrite collect_rel_cross, !set_collect_eq.
  rewrite (rsr_map_bt INB SIMREL),
          (rsr_map_at INA SIMREL); auto.
  assert (NEQ : a_t <> b_t) by apply PRED.
  assert (ABSB : sb_t b_t a_t).
  { unfold sb. unfolder; splits; auto.
    apply PRED. }
  assert (ABIMM : immediate sb_t b_t a_t).
  { apply (rsr_at_bt_imm PRED). basic_solver. }
  split; intros x y;
    [intros [HREL | BA] | intro SB].
  { unfolder in HREL.
      destruct HREL as
        (x' & y' & (SB & NEQ') & EQX & EQY).
    assert (INX' : E_t x').
    { apply wf_sbE in SB; unfolder in SB; desf. }
    assert (INY' : E_t y').
    { apply wf_sbE in SB; unfolder in SB; desf. }
    destruct
      classic with (x' = a_t) as [XEA|XNA],
      classic with (x' = b_t) as [XEB|XNB],
      classic with (y' = a_t) as [YEA|YNA],
      classic with (y' = b_t) as [YEB|YNB].
    all: desf.
    { exfalso. now apply sb_irr with G_t a_t. }
    all: rewrite ?(rsr_map_at INA SIMREL), ?(rsr_map_bt INB SIMREL).
    all: rewrite ?(rsr_mapper SIMREL), ?updo; auto.
    all: unfold id; ins.
    all: try now (solve [eapply sb_trans; eauto] || tauto).
    { exfalso. eapply sb_irr; eauto. }
    { destruct sb_semi_total_l
          with (x := b_t) (y := a_t) (z := y') (G := G_t)
            as [LSB | RSB].
      all: auto; try now apply PRED.
      exfalso. now apply ABIMM with y'. }
    destruct sb_semi_total_r
        with (x := a_t) (y := x') (z := b_t) (G := G_t)
          as [LSB | RSB].
    all: auto; try now apply PRED.
    exfalso. now apply ABIMM with x'. }
  { unfolder in BA. desf. }
  assert (INX : E_t x).
  { apply wf_sbE in SB; unfolder in SB; desf. }
  assert (INY : E_t y).
  { apply wf_sbE in SB; unfolder in SB; desf. }
  destruct
    classic with (x = a_t) as [XEA|XNA],
    classic with (x = b_t) as [XEB|XNB],
    classic with (y = a_t) as [YEA|YNA],
    classic with (y = b_t) as [YEB|YNB].
  all: desf.
  all: try now (exfalso; eapply sb_irr; eauto).
  { exfalso; eapply sb_irr, sb_trans; eauto. }
  { left. exists b_t, y.
    rewrite (rsr_map_bt INB SIMREL); auto.
    rewrite (rsr_mapper SIMREL); auto.
    rewrite !updo by congruence.
    unfold id. splits; auto.
    split; [eapply sb_trans; eauto|].
    unfolder; apply or_not_and; now right. }
  { basic_solver. }
  { left. exists a_t, y.
    rewrite (rsr_map_at INA SIMREL); auto.
    rewrite (rsr_mapper SIMREL); auto.
    rewrite !updo by congruence.
    unfold id. splits; auto.
    split; [|
      unfolder; apply or_not_and; now right].
    destruct sb_semi_total_l
        with (x := b_t) (y := a_t) (z := y) (G := G_t)
          as [LSB | RSB].
    all: auto; try now apply PRED.
    exfalso. now apply ABIMM with y. }
  { left. exists x, b_t.
    rewrite (rsr_map_bt INB SIMREL); auto.
    rewrite (rsr_mapper SIMREL); auto.
    rewrite !updo by congruence.
    unfold id. splits; auto.
    split; [|
      unfolder; apply or_not_and; now right].
    destruct sb_semi_total_r
        with (x := a_t) (y := x) (z := b_t) (G := G_t)
          as [LSB | RSB].
    all: auto; try now apply PRED.
    exfalso. now apply ABIMM with x. }
  { left. exists x, a_t.
    rewrite (rsr_map_at INA SIMREL); auto.
    rewrite (rsr_mapper SIMREL); auto.
    rewrite !updo by congruence.
    unfold id. splits; auto.
    split; [eapply sb_trans; eauto|].
    unfolder; apply or_not_and; now left. }
  left. exists x, y; split.
  { unfolder. split; auto.
    apply or_not_and. now left. }
  rewrite !(rsr_mapper SIMREL); auto.
  now rewrite !updo by auto.
Qed.

Lemma rsr_sbE :
  sb_s ≡ sb_t ∪
    (is_init ∪₁ E_t ∩₁ Tid_ (tid b_t)) × extra_a a_t.
Proof using PRED SIMREL.
  rewrite (rsr_sb SIMREL).
  destruct classic with (~ E_t b_t) as [NINB|INB'].
  { rewrite !extra_a_none_r; auto.
    arewrite (eq b_t ∩₁ E_t ≡₁ ∅) by basic_solver.
    rewrite !cross_false_r, cross_false_l, !union_false_r.
    rewrite swap_rel_empty_l.
    rewrite collect_rel_eq_dom
       with (g := id); [basic_solver 11 |].
    arewrite (
      dom_rel sb_t ∪₁ codom_rel sb_t ⊆₁
        E_t
    ).
    { rewrite wf_sbE. basic_solver. }
    unfolder. intros x XIN.
    rewrite (rsr_mapper SIMREL); auto.
    rewrite updo by congruence.
    rewrite updo; auto. intro FALSO.
    subst x.
    now apply NINB, (rsr_at_bt_ord PRED). }
  assert (INB : E_t b_t) by tauto. clear INB'.
  rewrite rsr_sbs_dom_disjunct; auto.
  rewrite (rsr_map_bt INB SIMREL); auto.
  unfold extra_a; desf; [desf |].
  { arewrite (eq a_t ∩₁ E_t ≡₁ ∅) by basic_solver.
    rewrite swap_rel_empty_r.
    arewrite (
      dom_rel (sb_t ⨾ ⦗eq b_t⦘) × eq b_t ≡
        sb_t ⨾ ⦗eq b_t⦘
    ) by basic_solver.
    rewrite rsr_sbt_map1; auto.
    split; repeat apply inclusion_union_l.
    { arewrite (
        dom_rel (sb_t ⨾ ⦗eq b_t⦘) ⊆₁
          is_init ∪₁ E_t ∩₁ Tid_ (tid b_t)
      ); [| auto with hahn].
      unfold sb, ext_sb. unfolder.
      ins; desf; ins; desf; eauto. }
    { basic_solver. }
    { basic_solver. }
    { basic_solver 7. }
    { arewrite (
        sb_t ≡
          sb_t ⨾ ⦗set_compl (eq b_t)⦘ ∪
            sb_t ⨾ ⦗eq b_t⦘
      ) at 1.
      { clear. unfolder; split; ins; desf.
        tauto. }
      basic_solver 11. }
    transitivity (
      dom_rel (sb_t ⨾ ⦗eq b_t⦘) × eq a_t ∪
        eq b_t × eq a_t
    ); auto with hahn.
    rewrite <- cross_union_l.
    apply cross_mori; auto with hahn.
    arewrite (E_t ≡₁ E_t \₁ eq b_t ∪₁ eq b_t).
    { split; [| basic_solver].
      unfolder. ins. desf. tauto. }
    rewrite set_inter_union_l, <- set_unionA.
    arewrite (eq b_t ∩₁ Tid_ (tid b_t) ≡₁ eq b_t).
    { unfold tid. basic_solver. }
    apply set_subset_union; auto with hahn.
    apply set_subset_union_l. split.
    { unfold sb, ext_sb, is_init. unfolder.
      ins. desf. exists b_t. splits; auto.
      { now apply (rsr_init_acts PRED). }
      desf. apply (rsr_bt_ninit PRED).
      unfold is_init. desf. }
    unfolder. intros x ((XIN & NEQ) & TID).
    destruct (rsr_bt_max' x PRED INB)
          as [EQ | SB].
    all: eauto || congruence. }
  rewrite cross_false_l, !cross_false_r,
          !union_false_r.
  assert (INA : E_t a_t) by tauto.
  now apply rsr_sbt_map2.
Qed.

Definition extra_sb :=
  (E_t ∩₁ Tid_ (tid b_t)) × extra_a a_t.

Lemma rsr_ninsbE :
  nin_sb G_s ≡ nin_sb G_t ∪ extra_sb.
Proof using PRED SIMREL.
  unfold nin_sb.
  rewrite rsr_sbE; eauto.
  rewrite !seq_union_r.
  apply union_more; [reflexivity |].
  rewrite <- cross_inter_l, set_inter_union_r.
  arewrite ((fun x => ~is_init x) ∩₁ is_init ≡₁ ∅).
  { basic_solver. }
  rewrite set_union_empty_l.
  unfold extra_sb. apply cross_more; [| reflexivity].
  split; [basic_solver |].
  unfolder. ins. desf. splits; auto.
  unfold tid, is_init in *. desf.
  { exfalso. apply (rsr_bt_ninit PRED).
    unfold is_init; desf. }
  exfalso. apply (rsr_bt_tid PRED).
  unfold tid. desf.
Qed.

Lemma extra_sb_some
    (NINA : ~E_t a_t)
    (INB : E_t b_t) :
  extra_sb ≡
    (E_t ∩₁ Tid_ (tid b_t)) × eq a_t.
Proof using.
  unfold extra_sb.
  rewrite extra_a_some; auto with hahn.
Qed.

Lemma extra_sb_none_l
    (INA : E_t a_t) :
  extra_sb ≡ ∅₂.
Proof using.
  unfold extra_sb.
  rewrite extra_a_none_l; auto.
  basic_solver.
Qed.

Lemma extra_sb_none_r
    (INA : ~E_t b_t) :
  extra_sb ≡ ∅₂.
Proof using.
  unfold extra_sb.
  rewrite extra_a_none_r; auto.
  basic_solver.
Qed.

Lemma extra_sbE :
  extra_sb \ (nin_sb G_t) ⨾ extra_sb ≡
    extra_a b_t × eq a_t.
Proof using PRED SIMREL.
  assert (ABSB : sb_t b_t a_t).
  { admit. }
  assert (NIB : ~is_init b_t).
  { admit. }
  unfold extra_sb, extra_a.
  desf; [| clear; basic_solver].
  split.
  { intros x y (EQ & MAX).
    assert (NIX : ~is_init x).
    { admit. }
    unfolder in EQ.
    destruct EQ as ((XIN & XT) & YEQ).
    subst y. unfolder. split; auto.
    destruct (rsr_bt_max' x PRED) as [SB | EQ].
    all: desf.
    exfalso. apply MAX.
    unfolder. exists b_t; splits; desf.
    unfold nin_sb. unfolder; split; auto. }
  intros x y (XEQ & YEQ); subst.
  split; [basic_solver |].
  unfold nin_sb. unfolder. intros FALSO; desf.
  eapply (rsr_bt_max PRED); eauto.
  unfolder; splits; eauto.
Admitted.

Lemma rsr_sbE_imm :
  immediate (nin_sb G_s) ≡
    immediate (nin_sb G_t) ∪
      extra_sb \ (nin_sb G_t) ⨾ extra_sb.
Proof using PRED SIMREL.
  assert (NINA : ~is_init a_t) by apply PRED.
  rewrite rsr_ninsbE; auto.
  rewrite immediate_union.
  { arewrite (immediate extra_sb ≡ extra_sb).
    { rewrite immediateE.
      arewrite_false (extra_sb ⨾ extra_sb); [| basic_solver].
      unfold extra_sb. unfold extra_a; desf; basic_solver. }
    arewrite (
      extra_sb ∩ (extra_sb \ (nin_sb G_t) ⨾ extra_sb) ≡
        extra_sb \ (nin_sb G_t) ⨾ extra_sb
    ); [| reflexivity].
    rewrite inter_absorb_l; [reflexivity |].
    basic_solver. }
  { unfold extra_sb.
    unfold extra_a; desf; [| basic_solver].
    unfold nin_sb.
    rewrite wf_sbE. basic_solver. }
  { unfold nin_sb.
    rewrite wf_sbE. unfold extra_sb.
    unfold extra_a; desf; [| basic_solver].
    basic_solver 11. }
  unfold nin_sb.
  rewrite wf_sbE. unfold extra_sb.
  unfold extra_a; desf; [| basic_solver].
  basic_solver 11.
Qed.

End ReordEquivLemmas.