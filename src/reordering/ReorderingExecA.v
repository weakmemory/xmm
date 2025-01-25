Require Import ReordSimrel.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2 AuxRel3 MapDoms.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import SubToFullExec.
Require Import xmm_s_hb.
Require Import Thrdle.
Require Import ReorderingRpo ReorderingMapper.
Require Import ReorderingEq ReorderingCons.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution SubExecution.
Require Import Setoid Morphisms Program.Basics.

Section ExecA.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t : actid.
Variable l_a : label.

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_t''" := (WCore.G X_t').
Notation "'G_s'" := (WCore.G X_s).

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
Notation "'sw_t''" := (sw G_t').
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
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (fun x => is_true (is_rlx lab_s x)).
Notation "'Acq_s'" := (fun x => is_true (is_acq lab_s x)).
Notation "'Rel_s'" := (fun x => is_true (is_rel lab_s x)).

Notation "'is_init'" := (fun e => is_true (is_init e)).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'mapper'" := (mapper a_t b_t).

Notation "'A_s'" := (extra_a X_t a_t b_t b_t).
Notation "'B_s'" := (extra_a X_t a_t b_t a_t).
Notation "'B_s''" := (extra_a X_t' a_t b_t a_t).
Notation "'A_s''" := (extra_a X_t' a_t b_t b_t).

Definition rsr_a_Gs_prime := {|
  acts_set := E_s;
  threads_set := threads_set G_s;
  lab := upd lab_s b_t l_a;
  rf := rf_s ⨾ ⦗E_s \₁ eq b_t⦘ ∪
        mapper ↑ (rf_t' ⨾ ⦗eq a_t⦘);
  co := restr_rel (E_s \₁ eq b_t) co_s ∪
        mapper ↑ (⦗eq a_t⦘ ⨾ co_t' ∪ co_t' ⨾ ⦗eq a_t⦘);
  rmw := mapper ↑ rmw_t';
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.

Definition rsr_a_Xs_prime := {|
  WCore.G := rsr_a_Gs_prime;
  WCore.sc := WCore.sc X_s;
|}.

Notation "'X_s''" := rsr_a_Xs_prime.
Notation "'G_s''" := (WCore.G X_s').
Notation "'lab_s''" := (lab G_s').
Notation "'val_s''" := (val lab_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'same_loc_s''" := (same_loc lab_s').
Notation "'E_s''" := (acts_set G_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'sb_s''" := (sb G_s').
Notation "'rf_s''" := (rf G_s').
Notation "'co_s''" := (co G_s').
Notation "'rmw_s''" := (rmw G_s').
Notation "'rpo_imm_s''" := (rpo_imm G_s').
Notation "'rpo_s''" := (rpo G_s').
Notation "'sw_s''" := (sw G_s').
Notation "'rmw_dep_s''" := (rmw_dep G_s').
Notation "'data_s''" := (data G_s').
Notation "'ctrl_s''" := (ctrl G_s').
Notation "'addr_s''" := (addr G_s').
Notation "'W_s''" := (fun x => is_true (is_w lab_s' x)).
Notation "'R_s''" := (fun x => is_true (is_r lab_s' x)).
Notation "'F_s''" := (fun x => is_true (is_f lab_s' x)).
Notation "'vf_s''" := (vf G_s').
Notation "'srf_s''" := (srf G_s').
Notation "'Loc_s_'' l" := (fun e => loc_s' e = l) (at level 1).
Notation "'Val_s_'' l" := (fun e => val_s' e = l) (at level 1).
Notation "'Rlx_s''" := (fun e => is_true (is_rlx lab_s' e)).
Notation "'Acq_s''" := (fun e => is_true (is_acq lab_s' e)).
Notation "'Rel_s''" := (fun e => is_true (is_rel lab_s' e)).

Hypothesis ADD : WCore.add_event X_t X_t' a_t l_a.

Lemma rsr_step_acts : E_t' ≡₁ E_t ∪₁ eq a_t.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_at_tid : tid a_t <> tid_init.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_at_ninit : ~is_init a_t.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_at_notin : ~E_t a_t.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_at_in' : E_t' a_t.
Proof using ADD.
  apply rsr_step_acts. now right.
Qed.

Lemma rsr_step_lab : lab_t' = upd lab_t a_t l_a.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Hint Resolve rsr_at_tid rsr_at_notin rsr_at_ninit
             rsr_at_in' : xmm.

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t b_t.
Hypothesis CONS : WCore.is_cons G_t'.

Lemma rsr_bt_in' : E_t' b_t.
Proof using ADD INV'.
  apply (rsr_at_bt_ord INV'), rsr_at_in'.
Qed.

Lemma rsr_bt_in : E_t b_t.
Proof using ADD INV'.
  clear - ADD INV'.
  assert (NEQ : a_t <> b_t) by apply INV'.
  assert (IN' : E_t' b_t) by apply rsr_bt_in'.
  apply rsr_step_acts in IN'.
  unfolder in IN'. desf.
Qed.

Lemma rsr_old_exa : A_s ≡₁ eq b_t.
Proof using ADD INV'.
  apply extra_a_some; auto with xmm.
  apply rsr_bt_in.
Qed.

Lemma rsr_new_exa : A_s' ≡₁ ∅.
Proof using ADD INV'.
  apply extra_a_none_l; auto with xmm.
Qed.

Hint Resolve rsr_bt_in' rsr_bt_in : xmm.

Hypothesis SIMREL : reord_simrel X_s X_t a_t b_t mapper.

Lemma rsr_nanb_lab : eq_dom E_t' lab_t' (lab_s' ∘ mapper).
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl.
  rewrite <- rsr_mapper_at with (a_t := a_t) (b_t := b_t) at 1.
  all: auto.
  rewrite rsr_step_lab, <- upd_compose; auto with xmm.
  rewrite rsr_step_acts. apply eq_dom_union. split.
  { apply eq_dom_upd; auto with xmm.
    symmetry. apply SIMREL. }
  apply eq_dom_eq. now rewrite !upds.
Qed.

Lemma rsr_nanb_lab' : eq_dom E_t' (lab_s' ∘ mapper) lab_t'.
Proof using ADD SIMREL INV INV'.
  symmetry. exact rsr_nanb_lab.
Qed.

Lemma rsr_nanb_mapinj : inj_dom E_t' mapper.
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  eapply inj_dom_mori; auto with xmm.
  red; auto with hahn.
Qed.

Hint Resolve rsr_nanb_lab rsr_nanb_lab'
            rsr_nanb_mapinj rsr_Gt_wf : xmm.

Definition f := @id actid.
Definition cmt := E_s \₁ eq b_t.
Definition dtrmt := E_s \₁ (eq b_t ∪₁ eq a_t).
Definition thrdle :=
  eq tid_init × set_compl (eq tid_init) ∪
  set_compl (eq (tid b_t)) × eq (tid b_t).

Lemma rsr_a_labeq : eq_dom cmt lab_s' lab_s.
Proof using.
  simpl.
  apply eq_dom_upd_l; [| reflexivity].
  unfold cmt. clear. unfolder. tauto.
Qed.

Lemma rsr_a_labeq' : eq_dom cmt lab_s lab_s'.
Proof using.
  symmetry. exact rsr_a_labeq.
Qed.

Lemma rsr_a_ain : E_s b_t.
Proof using ADD INV' SIMREL.
  apply (rsr_acts SIMREL). right.
  now apply rsr_old_exa.
Qed.

Lemma rsr_a_bin : E_s a_t.
Proof using ADD INV' SIMREL.
  assert (NEQ : a_t <> b_t) by apply (rsr_at_neq_bt INV').
  apply (rsr_acts SIMREL). left.
  exists b_t; split; auto with xmm.
Qed.

Lemma rsr_a_sb_same : sb_s' ≡ sb_s.
Proof using ADD SIMREL INV INV'.
  unfold sb at 1. simpl.
  now change (⦗E_s⦘ ⨾ ext_sb ⨾ ⦗E_s⦘) with sb_s.
Qed.

Lemma rsr_a_sb_helper :
  dom_rel (sb_t ⨾ ⦗eq b_t⦘) × eq a_t ≡
    WCore.sb_delta a_t (E_t \₁ eq b_t).
Proof using ADD SIMREL INV INV'.
  assert (BNINI : ~is_init b_t) by apply INV.
  assert (BTID : tid b_t <> tid_init) by apply (rsr_bt_tid INV).
  unfold WCore.sb_delta. apply cross_more; [| reflexivity].
  rewrite sb_tid_init', unionC.
  rewrite !seq_union_l, seqA, dom_union.
  arewrite (same_tid a_t ≡₁ same_tid b_t).
  { unfold same_tid. now rewrite (rsr_at_bt_tid INV). }
  split.
  { apply set_union_mori; [basic_solver |].
    rewrite <- seq_eqv_inter_lr.
    arewrite (sb_t ⨾ ⦗eq b_t⦘ ⊆ ⦗E_t \₁ eq b_t⦘ ⨾ sb_t ⨾ ⦗eq b_t⦘)
      ; [| basic_solver].
    rewrite wf_sbE at 1. rewrite !seqA.
    unfolder. ins. desf. splits; auto.
    intro FALSO. desf. eapply sb_irr; eauto. }
  apply set_union_mori.
  { unfold sb, ext_sb. unfolder.
    ins. desf. eexists; splits.
    all: desf; eauto with xmm.
    now apply (rsr_init_acts INV). }
  intros x XIN.
  destruct sb_total
      with (G := G_t) (t := tid b_t)
           (a := b_t) (b := x)
        as [SB|SB].
  { unfolder; splits; auto with xmm. }
  { assert (TEQ : tid b_t = tid x) by apply XIN.
    unfolder; splits; auto; try apply XIN.
    unfold is_init; desf. }
  { apply XIN. }
  { exfalso. apply (rsr_bt_max INV) with b_t x.
    all: auto with xmm.
    assert (BIN : E_t b_t) by auto with xmm.
    basic_solver. }
  exists b_t.
  enough (same_tid b_t x) by basic_solver.
  apply XIN.
Qed.

Lemma rsr_a_sb_fromb : ⦗eq a_t⦘ ⨾ sb_s ⊆ ∅₂.
Proof using ADD SIMREL INV INV'.
  assert (ANIN : ~E_t a_t) by auto with xmm.
  assert (ANINI : ~is_init a_t) by apply INV.
  rewrite (rsr_sbE INV SIMREL), seq_union_r.
  apply inclusion_union_l.
  { rewrite wf_sbE. basic_solver. }
  basic_solver.
Qed.

Lemma rsr_a_sb :
  sb_s' ≡ mapper ↑ swap_rel sb_t' (eq b_t ∩₁ E_t') (eq a_t ∩₁ E_t').
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (BNINI : ~is_init b_t) by apply INV.
  assert (ANIN : ~E_t a_t) by auto with xmm.
  assert (STID : same_tid a_t b_t) by apply INV.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  rewrite (WCore.add_event_sb ADD'), swap_rel_unionE.
  rewrite rsr_a_sb_same, (rsr_sb SIMREL).
  arewrite (eq a_t ∩₁ E_t ≡₁ ∅).
  { split; auto with hahn.
    unfolder. intros x (XEQ & XIN). subst x.
    auto with xmm. }
  rewrite !set_inter_absorb_r, swap_rel_empty_r.
  all: try (red; ins; subst x; auto with xmm).
  rewrite rsr_old_exa; auto.
  rewrite <- rsr_mapper_at
     with (a_t := a_t) (b_t := b_t)
       at 4 5; auto.
  rewrite <- !set_collect_eq, <- !collect_rel_cross,
          <- !collect_rel_union.
  apply collect_rel_more; auto.
  unfold swap_rel.
  arewrite (
    WCore.sb_delta a_t E_t \ eq b_t × eq a_t ≡
      WCore.sb_delta a_t (E_t \₁ eq b_t)
  ).
  { unfold WCore.sb_delta. rewrite <- cross_minus_l.
    apply cross_more; [| reflexivity].
    rewrite set_minus_union_l.
    apply set_union_more; [| basic_solver].
    rewrite set_minus_disjoint; basic_solver. }
  arewrite (sb_t \ eq b_t × eq a_t ≡ sb_t).
  { rewrite minus_disjoint; [reflexivity |].
    rewrite wf_sbE. basic_solver. }
  rewrite <- rsr_a_sb_helper. basic_solver 11.
Qed.

Lemma rsr_oldacts : mapper ↑₁ E_t ⊆₁ E_s \₁ eq b_t.
Proof using ADD SIMREL INV INV'.
  now rewrite (rsr_codom SIMREL), rsr_old_exa.
Qed.

Lemma rsr_a_rf : rf_s' ≡ mapper ↑ rf_t'.
Proof using ADD SIMREL INV INV'.
  assert (WF_t : Wf G_t) by apply INV.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  simpl.
  rewrite (rsr_rf SIMREL), (rf_delta_RE WF_t ADD'),
          !seq_union_l.
  arewrite_false ((srf_s ⨾ ⦗A_s ∩₁ R_s⦘) ⨾ ⦗E_s \₁ eq b_t⦘).
  { rewrite rsr_old_exa. basic_solver. }
  rewrite (WCore.add_event_rf ADD'),
          (add_event_to_rf_complete ADD' WF_t (rsr_Gt_rfc INV)).
  rewrite !union_false_r, collect_rel_union.
  apply union_more; [| reflexivity].
  split; [basic_solver 11 |].
  rewrite (wf_rfE WF_t) at 1.
  rewrite !collect_rel_seqi, !collect_rel_eqv,
          rsr_oldacts.
  basic_solver 11.
Qed.

Lemma rsr_a_co : co_s' ≡ mapper ↑ co_t'.
Proof using ADD SIMREL INV INV'.
  assert (WF_t : Wf G_t) by apply INV.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  simpl.
  rewrite (rsr_co SIMREL), (co_deltaE WF_t ADD'),
          restr_union.
  arewrite_false (
    restr_rel
      (E_s \₁ eq b_t)
      (add_max
        (extra_co_D E_s lab_s (loc_s b_t))
        (A_s ∩₁ W_s))
  ).
  { rewrite rsr_old_exa. basic_solver. }
  rewrite (WCore.add_event_co ADD').
  rewrite union_false_r, collect_rel_union.
  apply union_more; [| reflexivity].
  split; [basic_solver 11 |].
  rewrite (wf_coE WF_t) at 1.
  rewrite !collect_rel_seqi, !collect_rel_eqv,
          rsr_oldacts.
  basic_solver 11.
Qed.

Lemma rsr_a_acts : E_s' ≡₁ mapper ↑₁ E_t'.
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply (rsr_at_neq_bt INV).
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  simpl.
  rewrite (rsr_acts SIMREL), (WCore.add_event_acts ADD'),
          set_collect_union, set_collect_eq, rsr_old_exa.
  rewrite rsr_mapper_at; auto with hahn.
Qed.

Lemma rsr_a_acts_same : E_s' ≡₁ E_s.
Proof using.
  simpl. reflexivity.
Qed.

Lemma rsr_a_dtrmt_sub : dtrmt ⊆₁ E_s.
Proof using.
  unfold dtrmt. basic_solver.
Qed.

Lemma rsr_a_cmt_sub : cmt ⊆₁ E_s.
Proof using.
  unfold cmt. basic_solver.
Qed.

Lemma rsr_a_dtrmt_in_cmt : dtrmt ⊆₁ cmt.
Proof using.
  unfold dtrmt, cmt. basic_solver.
Qed.

Lemma rsr_a_dtrmt_init : is_init ⊆₁ dtrmt.
Proof using ADD SIMREL INV INV'.
  assert (ANINI : ~is_init b_t) by apply INV.
  assert (BNINI : ~is_init a_t) by apply INV.
  unfold dtrmt.
  rewrite <- (rsr_init_acts_s INV SIMREL).
  rewrite set_minus_disjoint; basic_solver.
Qed.

Hint Resolve rsr_a_labeq rsr_a_labeq' rsr_a_ain rsr_a_bin
              rsr_a_cmt_sub rsr_a_dtrmt_sub rsr_a_dtrmt_in_cmt
              rsr_a_dtrmt_init : xmm.

Lemma rsr_a_sim :
  reord_simrel X_s' X_t' a_t b_t mapper.
Proof using ADD SIMREL INV INV'.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  assert (ANINI : ~is_init a_t) by apply INV.
  assert (BNINI : ~is_init b_t) by apply INV.
  assert (WF_t : Wf G_t) by apply INV.
  assert (NEQ : a_t <> b_t) by apply (rsr_at_neq_bt INV).
  assert (TEQ : tid a_t = tid b_t) by apply (rsr_at_bt_tid INV).
  constructor.
  all: rewrite ?rsr_new_exa.
  all: rewrite ?set_minus_empty_r, ?set_union_empty_r,
               ?set_inter_empty_l, ?cross_false_l, ?cross_false_r,
               ?eqv_empty,
               ?seq_false_r, ?add_max_empty_r, ?union_false_r.
  all: auto with xmm hahn.
  { apply rsr_a_acts. }
  { eapply eq_dom_mori; eauto with xmm.
    red. auto with hahn. }
  { apply rsr_a_acts. }
  { apply rsr_a_sb. }
  { apply rsr_a_rf. }
  { apply rsr_a_co. }
  { now rewrite (WCore.add_event_threads ADD'), <- (rsr_threads SIMREL). }
  all: simpl.
  all: rewrite ?(WCore.add_event_ctrl ADD'), ?(WCore.add_event_data ADD'),
               ?(WCore.add_event_addr ADD'), ?(WCore.add_event_rmw_dep ADD').
  all: try now apply SIMREL.
  { rewrite rsr_step_acts, !set_minus_minus_l.
    arewrite ((E_t ∪₁ eq a_t) \₁ (eq a_t ∪₁ eq b_t) ≡₁ E_t \₁ eq b_t).
    { rewrite set_minus_union_l, set_unionC.
      rewrite !set_minus_union_r, set_minusK.
      rewrite set_minus_disjoint
         with (s1 := E_t) (s2 := eq a_t)
            ; [basic_solver |].
      unfolder. intros x XIN XEQ. subst x. auto with xmm. }
    intros x XIN. rewrite rsr_mappero.
    all: forward apply XIN; unfold id.
    all: try (clear; basic_solver).
    unfolder. ins. desf. intro FALSO. subst x.
    auto with xmm. }
  all: rewrite set_inter_absorb_r.
  all: try (red; ins; subst x; auto with xmm).
  all: rewrite set_collect_eq, ?rsr_mapper_bt,
               ?rsr_mapper_at.
  all: auto with hahn.
Qed.

Lemma rsr_a_ndtrmt : E_s' \₁ dtrmt ≡₁ eq b_t ∪₁ eq a_t.
Proof using SIMREL INV' ADD.
  simpl. unfold dtrmt.
  rewrite set_minus_minus_r, set_minusK.
  rewrite set_union_empty_l, set_inter_absorb_l.
  { basic_solver. }
  unfolder. intros x [XEQ | XEQ]; subst x.
  all: auto with xmm.
Qed.

Lemma rsr_a_ncmt : E_s' \₁ cmt ≡₁ eq b_t.
Proof using SIMREL INV' ADD.
  simpl. unfold cmt.
  rewrite set_minus_minus_r, set_minusK.
  rewrite set_union_empty_l, set_inter_absorb_l.
  { basic_solver. }
  unfolder. intros x XEQ; subst x.
  all: auto with xmm.
Qed.

Lemma rsr_a_ndtrmt_cmt : cmt \₁ dtrmt ≡₁ eq a_t.
Proof using ADD INV INV' SIMREL.
  assert (BIN : E_s a_t) by apply rsr_a_bin.
  assert (NEQ : a_t <> b_t) by apply INV'.
  unfold cmt, dtrmt.
  rewrite set_minus_union_r, set_minus_inter_r.
  rewrite set_minusK, set_union_empty_l.
  rewrite set_minus_minus_r.
  arewrite ((E_s \₁ eq b_t) \₁ E_s ≡₁ ∅).
  { basic_solver. }
  rewrite set_union_empty_l, set_inter_absorb_l.
  { reflexivity. }
  basic_solver.
Qed.

Lemma rsr_a_rex_thread :
  WCore.reexec_thread X_s' dtrmt ≡₁ eq (tid b_t).
Proof using SIMREL INV' ADD.
  unfold WCore.reexec_thread.
  rewrite rsr_a_ndtrmt.
  rewrite set_collect_union, !set_collect_eq.
  rewrite set_union_absorb_r; [reflexivity |].
  unfolder. ins. desf. symmetry. apply INV'.
Qed.

Lemma rsr_a_thrdle :
  strict_partial_order thrdle.
Proof using INV.
  assert (BTID : tid b_t <> tid_init) by apply (rsr_bt_tid INV).
  constructor; unfold thrdle.
  { basic_solver. }
  unfolder. intros x y z HXY HYZ.
  desf; eauto. congruence.
Qed.

Lemma rsr_a_surg :
  WCore.stable_uncmt_reads_gen X_s' cmt thrdle.
Proof using ADD SIMREL INV INV'.
  assert (BTID : tid b_t <> tid_init) by apply (rsr_bt_tid INV).
  constructor.
  { unfold thrdle. basic_solver. }
  { unfold thrdle. unfolder.
    intros b [(EQ & NIN) | (NB & IN)]; [congruence |].
    now apply (rsr_bt_tid INV). }
  { apply rsr_a_thrdle. }
  rewrite rsr_a_ncmt.
  seq_rewrite (
    split_rel ⊤₁ ⊤₁
      (vf_s' ⨾ same_tid)
      same_tid
  ).
  rewrite unionC, seq_union_l.
  apply union_mori; [| basic_solver].
  remember (vf_s' ⨾ same_tid \ same_tid) as vfsbt.
  arewrite (vfsbt ⊆ ⦗is_init⦘ ⨾ vfsbt ∪ ⦗set_compl is_init⦘ ⨾ vfsbt).
  { rewrite <- seq_union_l, <- id_union.
    now rewrite set_compl_union_id, seq_id_l. }
  unfold thrdle.
  rewrite seq_union_l, map_rel_union.
  apply union_mori.
  { unfold is_init. basic_solver. }
  subst vfsbt.
  unfold same_tid. basic_solver.
Qed.

Lemma rsr_a_restr_rpoimm :
  restr_rel cmt rpo_imm_s' ⊆ rpo_imm_s.
Proof using ADD SIMREL INV INV'.
  unfold rpo_imm. rewrite rsr_a_sb_same.
  rewrite !restr_union, !restr_relE, !seqA.
  seq_rewrite (seq_eqvC cmt (F_s' ∩₁ Rel_s')).
  seq_rewrite (seq_eqvC cmt (R_s' ∩₁ Rlx_s')).
  seq_rewrite (seq_eqvC cmt Acq_s').
  seq_rewrite <- !id_inter.
  rewrite !set_interA.
  rewrite !set_inter_rlx with (G' := G_s') (G := G_s),
          !set_inter_rel with (G' := G_s') (G := G_s),
          !set_inter_acq with (G' := G_s') (G := G_s),
          !set_inter_is_r with (G' := G_s') (G := G_s) (s' := cmt),
          !set_inter_is_w with (G' := G_s') (G := G_s) (s' := cmt),
          !set_inter_is_f with (G' := G_s') (G := G_s) (s' := cmt).
  all: auto with xmm.
  { repeat apply union_mori.
    all: basic_solver. }
  all: basic_solver 2.
Qed.

Lemma rsr_a_sb_froma :
  ⦗eq b_t⦘ ⨾ sb_s' ⊆ eq b_t × eq a_t.
Proof using ADD SIMREL INV INV'.
  rewrite rsr_a_sb_same.
  apply (rsr_sb_froma INV SIMREL).
  all: auto with xmm.
Qed.

Lemma rsr_a_rpoimm_upward :
  upward_closed (rpo_imm G_s') cmt.
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold upward_closed, cmt.
  intros x y RPO CMT.
  split.
  { apply (wf_rpo_immE (G_s_wf INV' rsr_a_sim)) in RPO.
    unfolder in RPO. desf. }
  intro FALSO. subst x.
  assert (SB : (⦗eq b_t⦘ ⨾ sb_s') b_t y).
  { exists b_t. split; [basic_solver 1|].
    now apply rpo_imm_in_sb. }
  assert (YEQ : y = a_t).
  { apply rsr_a_sb_froma in SB.
    unfolder in SB. desf. }
  subst y.
  apply (rsr_nrpo INV' rsr_a_sim) with b_t a_t.
  unfolder. splits; eauto with xmm.
  unfold rpo. now apply ct_step.
Qed.

Lemma rsr_rpo_emb :
  restr_rel cmt rpo_s' ⊆ rpo_s.
Proof using ADD SIMREL INV INV'.
  assert (AIN : E_s b_t) by apply rsr_a_ain.
  assert (BIN : E_s a_t) by apply rsr_a_bin.
  unfold rpo at 1.
  rewrite restr_rel_ct; [| apply rsr_a_rpoimm_upward].
  now rewrite rsr_a_restr_rpoimm.
Qed.

Lemma rsr_embed :
  WCore.commit_embedded X_s X_s' f cmt.
Proof using ADD SIMREL INV INV'.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  assert (NEQ : a_t <> b_t) by apply INV.
  constructor.
  all: unfold f.
  all: rewrite ?collect_rel_id, ?set_collect_id.
  { basic_solver. }
  { basic_solver. }
  { intros e EIN. unfold id.
    now apply rsr_a_labeq. }
  { apply rsr_rpo_emb. }
  { simpl. rewrite restr_union.
    apply inclusion_union_l; [basic_solver |].
    rewrite collect_rel_seqi, collect_rel_eqv.
    rewrite set_collect_eq, rsr_mapper_at; auto.
    unfold cmt. basic_solver. }
  { simpl. rewrite restr_union.
    apply inclusion_union_l; [basic_solver |].
    rewrite collect_rel_union, !collect_rel_seqi.
    rewrite collect_rel_eqv, set_collect_eq, rsr_mapper_at; auto.
    unfold cmt. basic_solver. }
  { simpl. rewrite (WCore.add_event_rmw ADD'), (rsr_rmw SIMREL).
    rewrite collect_rel_union, restr_union.
    apply inclusion_union_l; [basic_solver 7 |].
    unfold WCore.rmw_delta.
    rewrite collect_rel_cross, set_collect_eq.
    rewrite rsr_mapper_at; auto.
    unfold cmt. basic_solver. }
  unfold cmt. basic_solver.
Qed.

Lemma rsr_a_rex_acts :
  E_s ≡₁ dtrmt ∪₁
    E_s ∩₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt.
Proof using ADD SIMREL INV INV' CONS.
  assert (AIN : E_s b_t) by apply rsr_a_ain.
  assert (BIN : E_s a_t) by apply rsr_a_bin.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  rewrite set_unionC, rsr_a_rex_thread.
  rewrite set_union_minus
      with (s := E_s) (s' := dtrmt).
  all: auto with xmm.
  rewrite set_inter_union_l, set_unionA.
  rewrite set_union_absorb_l
     with (s' := dtrmt) (s := dtrmt ∩₁ _)
       by basic_solver.
  apply set_union_more; [| reflexivity].
  rewrite rsr_a_ndtrmt. basic_solver.
Qed.

Lemma rsr_a_dt_sb_closed :
  sb_s ⨾ ⦗dtrmt⦘ ⊆ ⦗dtrmt⦘ ⨾ sb_s ⨾ ⦗dtrmt⦘.
Proof using ADD SIMREL INV INV'.
  arewrite (
    sb_s ⨾ ⦗dtrmt⦘ ⊆
      ⦗dtrmt⦘ ⨾ sb_s ⨾ ⦗dtrmt⦘ ∪
      ⦗E_s \₁ dtrmt⦘ ⨾ sb_s ⨾ ⦗dtrmt⦘
  ) at 1.
  { rewrite <- seq_union_l, <- id_union.
    rewrite set_unionC, <- set_union_minus; auto with xmm.
    rewrite wf_sbE, !seqA. basic_solver. }
  arewrite_false (⦗E_s \₁ dtrmt⦘ ⨾ sb_s ⨾ ⦗dtrmt⦘).
  all: try now rewrite union_false_r.
  rewrite rsr_a_ndtrmt, id_union, seq_union_l.
  sin_rewrite (rsr_sb_froma INV SIMREL); auto with xmm.
  sin_rewrite rsr_a_sb_fromb.
  unfold dtrmt. basic_solver.
Qed.

Lemma rsr_a_ninsb_tob :
  immediate (nin_sb G_s') ⨾ ⦗eq a_t⦘ ⊆
    eq b_t × eq a_t.
Proof using ADD SIMREL INV INV'.
  assert (BNINI : ~is_init b_t) by apply INV.
  intros x y (y' & SB & (EQ1 & EQ2)).
  subst y' y. split; auto.
  eapply (nin_sb_functional_l (G_s_wf INV' rsr_a_sim)).
  all: unfold transp; eauto.
  enough (RR : singl_rel b_t a_t ⊆ immediate (nin_sb G_s')).
  { now apply RR. }
  rewrite imm_nin_sbE, (rsr_sbE INV' rsr_a_sim).
  rewrite extra_a_none_l, cross_false_r, union_false_r; auto with xmm.
  rewrite <- (rsr_at_bt_imm INV').
  rewrite !set_inter_absorb_r.
  all: try now (intros x' XEQ; subst x'; auto with xmm).
  basic_solver.
Qed.

Lemma rsr_a_dt_sbmax :
  ⦗dtrmt⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗cmt⦘ ⊆
    ⦗dtrmt⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗dtrmt⦘.
Proof using ADD SIMREL INV INV' CONS.
  rewrite set_union_minus
     with (s := cmt) (s' := dtrmt).
  all: auto with xmm.
  rewrite id_union, !seq_union_r.
  apply inclusion_union_l; [| reflexivity].
  rewrite rsr_a_ndtrmt_cmt, rsr_a_ninsb_tob.
  rewrite <- cross_inter_l.
  arewrite (dtrmt ∩₁ eq b_t ⊆₁ ∅).
  { unfold dtrmt. basic_solver. }
  basic_solver.
Qed.

Hypothesis NSC : WCore.sc X_s ≡ ∅₂.

Lemma rsr_a_pfx :
  SubToFullExec.prefix (WCore.X_start X_s dtrmt) X_s'.
Proof using ADD SIMREL INV INV' NSC.
  clear CONS.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (BNINI : ~is_init b_t) by apply INV.
  constructor; ins.
  { rewrite <- rsr_a_dtrmt_init, <- (rsr_init_acts_s INV SIMREL).
    basic_solver. }
  { basic_solver. }
  { rewrite set_inter_absorb_r; auto with xmm.
    unfold dtrmt. rewrite set_minus_union_r.
    apply eq_dom_upd_r; [| reflexivity].
    unfolder. intro FALSO. desf. }
  { apply eq_dom_upd_r; [| reflexivity].
    unfolder. enough (E_s b_t); auto with xmm. }
  all: rewrite 1?set_inter_absorb_r; auto with xmm.
  all: rewrite ?restr_union.
  { arewrite_false (restr_rel dtrmt (mapper ↑ (rf_t' ⨾ ⦗eq a_t⦘))).
    { rewrite restr_relE, collect_rel_seqi.
      rewrite collect_rel_eqv, set_collect_eq.
      rewrite rsr_mapper_at; auto.
      unfold dtrmt. basic_solver. }
    rewrite restr_relE, union_false_r, !seqA.
    unfold dtrmt. basic_solver 11. }
  { arewrite_false (
      restr_rel dtrmt (
          mapper ↑ (⦗eq a_t⦘ ⨾ co_t' ∪
          co_t' ⨾ ⦗eq a_t⦘)
      )
    ).
    { rewrite collect_rel_union, !collect_rel_seqi.
      rewrite collect_rel_eqv, set_collect_eq.
      rewrite rsr_mapper_at; auto.
      unfold dtrmt. basic_solver. }
    rewrite !restr_relE, union_false_r, !seqA.
    unfold dtrmt. basic_solver 15. }
  { rewrite (WCore.add_event_rmw ADD'), collect_rel_union.
    rewrite (rsr_rmw SIMREL), restr_union.
    arewrite_false (restr_rel dtrmt (mapper ↑ WCore.rmw_delta a_t r)).
    { unfold WCore.rmw_delta, dtrmt.
      rewrite collect_rel_cross, set_collect_eq.
      rewrite rsr_mapper_at; auto. basic_solver. }
    now rewrite union_false_r, restr_relE. }
  all: rewrite ?(rsr_data SIMREL), ?(rsr_addr SIMREL), ?(rsr_ctrl SIMREL),
               ?(rsr_rmw_dep SIMREL).
  all: rewrite ?(rsr_ndata INV), ?(rsr_naddr INV), ?(rsr_nctrl INV),
               ?(rsr_nrmw_dep INV).
  all: try now rewrite seq_false_l, seq_false_r.
  { rewrite NSC. basic_solver. }
  rewrite rsr_a_sb_same. unfold sb at 2.
  ins. rewrite id_inter.
  rewrite seq_eqvC with (doma := dtrmt) at 2.
  rewrite seqA.
  arewrite (⦗E_s⦘ ⨾ ext_sb ⨾ ⦗E_s⦘ ≡ sb_s).
  apply rsr_a_dt_sb_closed.
Qed.

Lemma rsr_a_restr_eq :
  WCore.exec_restr_eq (WCore.X_start X_s dtrmt) X_s' dtrmt.
Proof using ADD SIMREL INV INV' NSC.
  assert (SUB : dtrmt ⊆₁ dtrmt ∩₁ E_s).
  { rewrite set_inter_absorb_r; auto with xmm hahn. }
  assert (NEQ : a_t <> b_t) by apply INV'.
  assert (NEQ' : b_t <> a_t) by now symmetry.
  constructor; ins.
  { rewrite set_inter_absorb_r; basic_solver. }
  { unfold dtrmt. rewrite set_minus_union_r.
    apply eq_dom_upd_r; [| reflexivity].
    unfolder. intro FALSO; desf. }
  { now rewrite (prf_rf rsr_a_pfx), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_co rsr_a_pfx), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_rmw rsr_a_pfx), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_data rsr_a_pfx). }
  { now rewrite (prf_ctrl rsr_a_pfx). }
  now rewrite (prf_rmw_dep rsr_a_pfx).
Qed.

Lemma rsr_a_cfg_wf :
  WCore.wf (WCore.X_start X_s dtrmt) X_s' cmt.
Proof using ADD SIMREL INV INV' NSC.
  constructor.
  { apply sub_WF with (G := G_s) (sc := ∅₂) (sc' := ∅₂).
    { ins. now rewrite <- rsr_a_dtrmt_init. }
    { apply (G_s_wf INV SIMREL). }
    apply restrict_sub; [basic_solver |].
    auto with xmm. }
  { ins. rewrite set_interA, set_inter_absorb_r.
    { apply rsr_a_restr_eq. }
    rewrite set_inter_absorb_l; auto with xmm. }
  { admit. }
  ins. rewrite <- rsr_a_dtrmt_in_cmt.
  basic_solver.
Admitted.

Lemma rsr_a_step_helper :
  (WCore.guided_step cmt X_s')＊
    (WCore.X_start X_s dtrmt) X_s'.
Proof using ADD SIMREL INV INV' CONS NSC.
  assert (ATID : tid a_t <> tid_init) by apply INV.
  assert (BTID : tid b_t <> tid_init) by apply (rsr_bt_tid INV).
  apply sub_to_full_exec_listless with (thrdle := thrdle).
  { apply rsr_a_cfg_wf. }
  { apply (G_s_rfc INV' rsr_a_sim). }
  { eapply rsr_cons with (X_t := X_t'); eauto.
    apply rsr_a_sim. }
  { ins.
    arewrite (E_s \₁ dtrmt ∩₁ E_s ⊆₁ E_s \₁ dtrmt).
    { basic_solver. }
    rewrite rsr_a_ndtrmt. apply set_finite_union.
    split; auto with hahn. }
  { apply rsr_a_pfx. }
  { apply (G_s_wf INV' rsr_a_sim). }
  { ins.
    arewrite (E_s \₁ dtrmt ∩₁ E_s ⊆₁ E_s \₁ dtrmt).
    { basic_solver. }
    rewrite rsr_a_ndtrmt. apply set_subset_union_l.
    split; basic_solver. }
  all: simpl.
  all: rewrite ?(rsr_data SIMREL), ?(rsr_addr SIMREL),
               ?(rsr_ctrl SIMREL), ?(rsr_rmw_dep SIMREL).
  all: try now apply INV.
  apply rsr_a_surg.
Qed.

Lemma rsr_a_step :
  WCore.reexec X_s X_s' f dtrmt cmt.
Proof using ADD SIMREL INV INV' CONS NSC.
  assert (AIN : E_s b_t) by apply rsr_a_ain.
  assert (BIN : E_s a_t) by apply rsr_a_bin.
  red. exists thrdle. constructor.
  all: auto with xmm.
  { clear. unfold f. basic_solver. }
  { apply rsr_a_surg. }
  { apply rsr_a_dt_sb_closed. }
  { apply rsr_a_dt_sbmax. }
  { rewrite rsr_a_ndtrmt.
    apply set_subset_union_l. split.
    { rewrite <- 1?(rsr_as_rlx INV' rsr_a_sim).
      basic_solver. }
    rewrite <- 1?(rsr_bs_rlx INV' rsr_a_sim).
    basic_solver. }
  { apply rsr_embed. }
  { apply (G_s_rfc INV' rsr_a_sim). }
  { apply rsr_a_cfg_wf. }
  { eapply rsr_cons with (X_t := X_t'); eauto.
    apply rsr_a_sim. }
  { apply rsr_a_rex_acts. }
  apply rsr_a_step_helper.
Qed.

End ExecA.