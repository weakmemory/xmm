Require Import ReordSimrel ReorderingEq ReorderingMapper ReorderingRpo.
Require Import AuxDef.
Require Import Core MapDoms.
Require Import AuxRel AuxRel2 AuxRel3.
Require Import Srf Rhb.
Require Import HbPrefix.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import SubToFullExec.
Require Import ReorderingFakeSrf ReorderingNewGraph ReorderingNewGraphSim.
Require Import Thrdle.
Require Import StepOps.
Require Import ConsistencyReadExtentGen.
Require Import ReorderingCons.
Require Import ConsistencyMonotonicity ConsistencyReadExtentGen.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco SubExecution.
Require Import Setoid Morphisms Program.Basics.
Require Import xmm_s_hb.

Set Implicit Arguments.

(*
NOTE: we assume that a and b do NOT change their
indices between re-executions. This simplfication
makes the formalisation somewhat more conservative.
*)

Section ReorderingReexec.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t : actid.
Variable l_a : label.
Variable f_t : actid -> actid.
Variable dtrmt_t cmt_t : actid -> Prop.
Variable thrdle : relation thread_id.

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
Notation "'hb_t'" := (hb G_t).
Notation "'rhb_t'" := (rhb G_t).
Notation "'W_t'" := (fun x => is_true (is_w lab_t x)).
Notation "'R_t'" := (fun x => is_true (is_r lab_t x)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).
Notation "'Acq_t'" := (fun e => is_true (is_acq lab_t e)).
Notation "'Rel_t'" := (fun e => is_true (is_rel lab_t e)).
Notation "'Rlx_t'" := (fun e => is_true (is_rlx lab_t e)).

Notation "'lab_t''" := (lab G_t').
Notation "'val_t''" := (val lab_t').
Notation "'loc_t''" := (loc lab_t').
Notation "'same_loc_t''" := (same_loc lab_t').
Notation "'same_val_t''" := (same_val lab_t').
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
Notation "'hb_t''" := (hb G_t').
Notation "'rhb_t''" := (rhb G_t').
Notation "'W_t''" := (fun x => is_true (is_w lab_t' x)).
Notation "'R_t''" := (fun x => is_true (is_r lab_t' x)).
Notation "'vf_t''" := (vf G_t').
Notation "'vf_rhb_t''" := (vf_rhb G_t').
Notation "'Loc_t_'' l" := (fun e => loc_t' e = l) (at level 1).
Notation "'Acq_t''" := (fun e => is_true (is_acq lab_t' e)).
Notation "'Rel_t''" := (fun e => is_true (is_rel lab_t' e)).
Notation "'Rlx_t''" := (fun e => is_true (is_rlx lab_t' e)).

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
Notation "'hb_s'" := (hb G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'W_s'" := (fun x => is_true (is_w lab_s x)).
Notation "'R_s'" := (fun x => is_true (is_r lab_s x)).
Notation "'F_s'" := (fun x => is_true (is_f lab_s x)).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).
Notation "'Acq_s'" := (fun e => is_true (is_acq lab_s e)).
Notation "'Rel_s'" := (fun e => is_true (is_rel lab_s e)).

Notation "'mapper'" := (mapper a_t b_t).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'A_s'" := (extra_a X_t a_t b_t b_t).
Notation "'A_s''" := (extra_a X_t' a_t b_t b_t).
Notation "'B_s''" := (extra_a X_t' a_t b_t a_t).

Notation "'X_s'''" := (rsr_immx X_t' a_t b_t).
Notation "'G_s'''" := (WCore.G X_s'').
Notation "'lab_s'''" := (lab G_s'').
Notation "'val_s'''" := (val lab_s'').
Notation "'loc_s'''" := (loc lab_s'').
Notation "'same_loc_s'''" := (same_loc lab_s'').
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
Notation "'vf_rhb_s'''" := (vf_rhb G_s'').
Notation "'srf_s'''" := (srf G_s'').
Notation "'rhb_s'''" := (rhb G_s'').
Notation "'Loc_s_''' l" := (fun e => loc_s'' e = l) (at level 1).
Notation "'Val_s_''' l" := (fun e => val_s'' e = l) (at level 1).
Notation "'Rlx_s'''" := (fun e => is_true (is_rlx lab_s'' e)).
Notation "'Acq_s'''" := (fun e => is_true (is_acq lab_s'' e)).
Notation "'Rel_s'''" := (fun e => is_true (is_rel lab_s'' e)).
Notation "'drf_s'''" := (fake_srf G_s'' b_t l_a ⨾ ⦗A_s' ∩₁ WCore.lab_is_r l_a⦘).
Notation "'dco_s'''" := (
  (E_s'' ∩₁ W_s'' ∩₁ Loc_s_'' (WCore.lab_loc l_a)) ×
    (A_s' ∩₁ WCore.lab_is_w l_a)).

Notation "'X_s''" := (rsr_Xs X_t' a_t b_t l_a).
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
Notation "'vf_rhb_s''" := (vf_rhb G_s').
Notation "'srf_s''" := (srf G_s').
Notation "'rhb_s''" := (rhb G_s').
Notation "'Loc_s_'' l" := (fun e => loc_s' e = l) (at level 1).
Notation "'Val_s_'' l" := (fun e => val_s' e = l) (at level 1).
Notation "'Rlx_s''" := (fun e => is_true (is_rlx lab_s' e)).
Notation "'Acq_s''" := (fun e => is_true (is_acq lab_s' e)).
Notation "'Rel_s''" := (fun e => is_true (is_rel lab_s' e)).
Notation "'hb_s''" := (hb G_s').

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t b_t.
Hypothesis SIMREL : reord_simrel X_s X_t a_t b_t mapper.
Hypothesis CONS : WCore.is_cons G_t'.
Hypothesis RCFBT : forall (ACMT : cmt_t b_t), f_t b_t = b_t.
Hypothesis RCFAT : forall (ACMT : cmt_t a_t), f_t a_t = a_t.
Hypothesis STEP : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle.

Hypothesis LVAL : dom_rel drf_s'' ⊆₁ Val_s_'' (WCore.lab_val l_a).
Hypothesis NLOC : A_s' ⊆₁ fun _ => WCore.lab_loc l_a <> loc_t' b_t.
Hypothesis ARW : A_s' ⊆₁ WCore.lab_is_r l_a ∪₁ WCore.lab_is_w l_a.
Hypothesis ARLX : A_s' ⊆₁ fun _ => mode_le (WCore.lab_mode l_a) Orlx.

Definition a_s := b_t.
Definition b_s := a_t.

Lemma reexec_simrel :
  reord_simrel X_s' X_t' a_t b_t mapper.
Proof using INV' LVAL NLOC ARW ARLX.
  apply (rsr_new_Gs_sim INV'); auto.
Qed.

Lemma rsr_rex_imm_wf : Wf G_s''.
Proof using INV'.
  now apply rsr_imm_Gs_wf.
Qed.

Lemma rsr_rex_imm_eqlab :
  eq_dom E_t' lab_t' (lab_s'' ∘ mapper).
Proof using INV'.
  assert (NEQ : a_t <> b_t) by apply INV'.
  simpl.
  rewrite Combinators.compose_assoc.
  rewrite rsr_mapper_compose, Combinators.compose_id_right; auto.
  reflexivity.
Qed.

Hint Resolve rsr_rex_imm_wf rsr_rex_imm_eqlab : xmm.

Lemma rsr_rex_imm_sbloc :
  sb_s'' ∩ same_loc_s'' ⊆ mapper ↑ (sb_t' ∩ same_loc_t').
Proof using INV'.
  apply reord_sbloc' with (a := a_t) (b := b_t).
  all: auto with xmm.
  { apply INV'. }
  apply (imm_G_s_sb INV').
Qed.

Lemma rsr_rex_imm_rpo :
  rpo_s'' ⊆ mapper ↑ rpo_t'.
Proof using INV'.
  assert (NEQ : a_t <> b_t) by apply INV'.
  apply reord_rpo_map' with (a := a_t) (b := b_t).
  all: auto with xmm.
  { eapply inj_dom_mori; auto with xmm.
    red; auto with hahn. }
  { apply (imm_G_s_sb INV'). }
  { transitivity (set_compl (Rel_t' ∪₁ Acq_t'))
      ; [apply INV' | basic_solver]. }
  { transitivity (set_compl (Rel_t' ∪₁ Acq_t'))
      ; [apply INV' | basic_solver]. }
  all: rewrite set_unionC; apply INV'.
Qed.

Hint Resolve rsr_rex_imm_sbloc rsr_rex_imm_rpo
             rsr_rex_imm_eqlab : xmm.

Lemma rsr_rex_vf_nesting :
  vf_rhb_s'' ⊆ mapper ↑ vf_rhb_t'.
Proof using INV'.
  assert (NEQ : a_t <> b_t) by apply INV'.
  assert (WF : Wf G_t') by apply INV'.
  unfold vf_rhb.
  rewrite XmmCons.monoton_rhb_sub
     with (G_t := G_t') (m := mapper).
  { change rf_s'' with (mapper ↑ rf_t').
    change E_s'' with (mapper ↑₁ E_t').
    seq_rewrite mapdom_rewrite_l'.
    rewrite set_collect_is_w
       with (G := G_t'); auto with xmm.
    rewrite !crE.
    rewrite !seq_union_l, !seq_union_r.
    rewrite !seq_id_l, !seq_id_r.
    rewrite !collect_rel_union.
    repeat apply union_mori.
    { rewrite <- id_inter, collect_rel_eqv.
      basic_solver. }
    all: rewrite <- 1?collect_rel_eqv.
    all: seq_rewrite <- id_inter.
    all: rewrite <- ?collect_rel_seq.
    all: try now (
      apply collect_rel_mori; auto;
        basic_solver
    ).
    all: eapply inj_dom_mori; eauto with xmm.
    all: unfold flip; auto with hahn. }
  all: auto with xmm.
  all: ins.
  { eapply inj_dom_mori; eauto with xmm.
    unfold flip. auto with hahn. }
  rewrite Combinators.compose_assoc.
  rewrite rsr_mapper_compose, Combinators.compose_id_right; auto.
  reflexivity.
Qed.

Lemma rsr_rex_rf_helper :
  rf_s' ⨾ ⦗A_s'⦘ ≡ srf_s' ⨾ ⦗A_s' ∩₁ R_s'⦘.
Proof using INV' LVAL NLOC ARW ARLX.
  rewrite (rsr_rf reexec_simrel).
  rewrite seq_union_l, seqA.
  rewrite <- id_inter, set_inter_absorb_r
    ; [| basic_solver].
  arewrite_false (mapper ↑ rf_t' ⨾ ⦗A_s'⦘)
    ; [| now rewrite union_false_l].
  unfold extra_a; desf; [| basic_solver].
  rewrite (wf_rfE (rsr_Gt_wf INV')).
  rewrite !collect_rel_seqi, !seqA.
  rewrite collect_rel_eqv, <- id_inter.
  arewrite (mapper ↑₁ E_t' ∩₁ eq b_t ⊆₁ ∅)
    ; [| now rewrite eqv_empty, !seq_false_r].
  unfolder. intros x ((y & YIN & XEQ) & XEQ').
  subst x. enough (y = a_t) by desf.
  eapply rsr_mapper_inv_bt; eauto.
  apply INV'.
Qed.

Lemma rsr_rex_rf_helper' :
  rf_s' ⨾ ⦗E_s' \₁ A_s'⦘ ≡ rf_s'' ⨾ ⦗E_s' \₁ A_s'⦘.
Proof using INV'.
  change rf_s' with (rf_s'' ∪ drf_s'').
  rewrite seq_union_l.
  arewrite_false (drf_s'' ⨾ ⦗E_s' \₁ A_s'⦘).
  { basic_solver. }
  now rewrite union_false_r.
Qed.

Lemma rsr_rex_vf_nesting' :
  vf_rhb_s' ⨾ ⦗E_s' \₁ A_s'⦘ ⊆ vf_rhb_s'' ⨾ ⦗E_s' \₁ A_s'⦘.
Proof using INV'.
  destruct classic
      with (~ (~E_t' a_t /\ E_t' b_t))
        as [EMP | NEMP'].
  { rewrite extra_a_none; auto.
    rewrite set_minus_empty_r.
    admit. (* Same execs *) }
  assert (NEMP : ~ E_t' a_t /\ E_t' b_t) by tauto.
  unfold extra_a.
  assert (NEQ : a_t <> b_t) by apply INV'.
  assert (WF : Wf G_s'') by admit.
  unfold vf_rhb. rewrite !seqA.
  arewrite (
    rhb_s'^? ⨾ ⦗E_s' \₁ A_s'⦘ ≡
      (rhb_s' ⨾ ⦗E_s' \₁ A_s'⦘)^?
        ⨾ ⦗E_s' \₁ A_s'⦘
  ).
  { clear. basic_solver 11. }
  arewrite (
    rhb_s''^? ⨾ ⦗E_s' \₁ A_s'⦘ ≡
      (rhb_s'' ⨾ ⦗E_s' \₁ A_s'⦘)^?
        ⨾ ⦗E_s' \₁ A_s'⦘
  ).
  { clear. basic_solver 11. }
  rewrite extra_a_some by desf.
  assert (ACTS : E_s' ≡₁ E_s'' ∪₁ eq b_t).
  { simpl. now rewrite extra_a_some. }
  assert (DISJ : set_disjoint E_s'' (eq b_t)).
  { unfolder. intros x XIN XEQ. subst x.
    simpl in XIN. unfolder in XIN.
    destruct XIN as (y & YIN & YEQ).
    enough (y = a_t) by desf.
    eapply rsr_mapper_inv_bt; eauto. }
  assert (RF : rf_s' ⨾ ⦗E_s' \₁ eq b_t⦘ ⊆ rf_s'').
  { change rf_s' with (rf_s'' ∪ drf_s'').
    rewrite seq_union_l.
    arewrite_false (drf_s'' ⨾ ⦗E_s' \₁ eq b_t⦘).
    { rewrite extra_a_some by desf.
      basic_solver. }
    rewrite union_false_r. basic_solver. }
  assert (CO : co_s' ⨾ ⦗E_s' \₁ eq b_t⦘ ⊆ co_s'').
  { change co_s' with (co_s'' ∪ dco_s'').
    rewrite seq_union_l.
    arewrite_false (dco_s'' ⨾ ⦗E_s' \₁ eq b_t⦘).
    { rewrite extra_a_some by desf.
      basic_solver. }
    rewrite union_false_r. basic_solver. }
  assert (EQA : E_s'' ≡₁ E_s' \₁ eq b_t).
  { rewrite ACTS, set_minus_union_l, set_minusK.
    rewrite set_minus_disjoint, set_union_empty_r.
    all: auto with hahn. }
  assert (RFF : rf_s' ⊆ ⦗E_s' \₁ eq b_t⦘ ⨾ rf_s').
  { change rf_s' with (rf_s'' ∪ drf_s'').
    rewrite (wf_rfE WF) at 1.
    rewrite fake_srfE_left at 1.
    rewrite !seqA, EQA.
    clear. basic_solver. }
  assert (NRPO : ⦗eq b_t⦘ ⨾ rpo_s' ⊆ ∅₂).
  { admit. }
  assert (NSBLOC : ⦗eq b_t⦘ ⨾ sb_s' ∩ same_loc_s' ⊆ ∅₂).
  { admit. }
  assert (RMW : rmw_s' ⊆ rmw_s'') by basic_solver.
  rewrite XmmCons.read_rhb_sub
     with (G_t := G_s'') (G_s := G_s') (m := id).
  all: rewrite ?collect_rel_id, ?set_collect_id.
  all: auto with xmm.
Admitted.

Lemma rsr_rex_vfexa' :
  vf_rhb_s' ⨾ ⦗A_s'⦘ ⊆ ⦗A_s' ∩₁ W_s'⦘ ∪ vf_rhb_s' ⨾ ⦗E_s' \₁ A_s'⦘ ⨾ sb_s' ⨾ ⦗A_s'⦘.
Proof using INV' LVAL NLOC ARW ARLX.
  clear STEP RCFAT RCFBT.
  clear f_t cmt_t X_t X_s SIMREL INV.
  assert (SUBHELP :
    sb_s' ⨾ ⦗A_s'⦘ ⊆
      ⦗E_s' \₁ A_s'⦘ ⨾ sb_s' ⨾ ⦗A_s'⦘
  ).
  { unfold extra_a. desf; [| basic_solver].
    rewrite wf_sbE at 1. rewrite !seqA.
    unfolder. ins. desf. splits; auto.
    intro FALSO. desf. eapply sb_irr; eauto. }
  unfold vf_rhb at 1.
  rewrite crE with (r := rhb_s').
  rewrite !seq_union_r, seq_id_r.
  rewrite seq_union_l. apply inclusion_union_l.
  { rewrite crE.
    rewrite !seq_union_r, seq_id_r.
    rewrite seq_union_l, !seqA.
    apply union_mori; [basic_solver |].
    rewrite rsr_rex_rf_helper.
    rewrite srf_as_rhb, srf_rhb_vf_rhb_sb,
            !seqA, id_inter.
    sin_rewrite SUBHELP.
    rewrite !seqA. clear. basic_solver 11. }
  apply inclusion_union_r. right.
  rewrite !seqA.
  unfold rhb. rewrite ct_end.
  rewrite <- cr_of_ct.
  change ((sb_s' ∩ same_loc_s' ∪ rpo_s' ∪ sw_s')⁺) with rhb_s'.
  rewrite !seqA.
  arewrite (⦗E_s'⦘ ⨾ ⦗W_s'⦘ ⨾ rf_s'^? ⨾ rhb_s'^? ≡ vf_rhb_s').
  rewrite !seq_union_l.
  arewrite_false (sw_s' ⨾ ⦗A_s'⦘).
  { rewrite (wf_swD (new_G_s_wf INV' LVAL)).
    rewrite (rsr_rex_a_rlx l_a INV' ARLX).
    clear. basic_solver. }
  arewrite (
    sb_s' ∩ same_loc_s' ⨾ ⦗A_s'⦘ ⊆
      ⦗E_s' \₁ A_s'⦘ ⨾ sb_s' ∩ same_loc_s' ⨾ ⦗A_s'⦘).
  { rewrite <- seq_eqv_inter_lr, <- seq_eqv_inter_ll.
    now rewrite SUBHELP at 1. }
  arewrite (
    rpo_s' ⨾ ⦗A_s'⦘ ⊆
      ⦗E_s' \₁ A_s'⦘ ⨾ rpo_s' ⨾ ⦗A_s'⦘
  ).
  { remember (E_s' \₁ A_s') as NA.
    unfolder. intros x y (RPO & NEXA).
    splits; auto. subst NA.
    apply rpo_in_sb in RPO.
    forward apply (SUBHELP x y)
      ; [basic_solver |].
    clear - RPO NEXA. basic_solver. }
  rewrite union_false_r.
  rewrite <- seq_union_r.
  rewrite rpo_in_sb.
  clear. basic_solver 11.
Qed.

Definition extra_b :=
  ifP ~dtrmt_t a_t /\ dtrmt_t b_t /\ E_t' a_t then eq b_t
  else ∅.
Definition exa_d :=
  ifP dtrmt_t b_t /\ ~E_t' a_t then eq a_s
  else ∅.
Definition extra_d :=
  ifP
    ~cmt_t b_t /\
    cmt_t a_t /\
    ~dtrmt_t a_t /\
    dom_rel (immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘) ⊆₁ dtrmt_t
  then eq a_s
  else ∅.
Definition cmt_s := mapper ↑₁ cmt_t ∪₁ exa_d.
Definition dtrmt_s := mapper ↑₁ (dtrmt_t \₁ extra_b) ∪₁ extra_d ∪₁ exa_d.
Definition f_s := (mapper ∘ f_t) ∘ mapper.

Lemma dtrmt_t_sb_closed' :
  sb_t' ⨾ ⦗dtrmt_t⦘ ⊆ ⦗dtrmt_t⦘ ⨾ sb_t' ⨾ ⦗dtrmt_t⦘.
Proof using STEP.
  eapply sb_closure_preserve_guided_trans.
  all: try now apply STEP.
  { ins. rewrite set_inter_absorb_r; auto.
    apply (rexec_dtrmt_in_start STEP). }
  unfold sb. ins. clear. basic_solver.
Qed.

Lemma dtrmt_t_sb_closed :
  dom_rel (sb_t' ⨾ ⦗dtrmt_t⦘) ⊆₁ dtrmt_t.
Proof using STEP.
  rewrite dtrmt_t_sb_closed'.
  clear. basic_solver.
Qed.

Lemma exa_d_some_helper
    (BD : dtrmt_t b_t)
    (NINA : ~E_t' a_t) :
  ~E_t a_t.
Proof using STEP INV'.
  intro FALSO.
  apply (WCore.rexec_acts STEP) in FALSO.
  destruct FALSO as [DA | DR].
  { now apply (rexec_dtrmt_in_fin STEP) in DA. }
  destruct DR as (INA & e & ((EIN & ENOTD) & ETHR)).
  assert (NEQ : e <> a_t) by congruence.
  assert (ATID : tid a_t <> tid_init) by apply INV'.
  assert (ENINI : ~is_init e).
  { intro FALSO. destruct e; ins. congruence. }
  assert (BNINI : ~is_init b_t) by apply INV'.
  assert (BIN : E_t' b_t).
  { now apply (rexec_dtrmt_in_fin STEP). }
  destruct sb_total
      with (G := G_t') (t := tid a_t)
           (a := e) (b := b_t)
        as [LSB|RSB].
  { basic_solver. }
  { rewrite (rsr_at_bt_tid INV').
    basic_solver. }
  { congruence. }
  all: try now (eapply (rsr_bt_max INV'); basic_solver 3).
  apply ENOTD, dtrmt_t_sb_closed.
  exists b_t. basic_solver.
Qed.

Lemma extra_cases :
  (extra_b ≡₁ eq b_t /\ exa_d ≡₁ ∅      /\ extra_d ≡₁ ∅     ) \/
  (extra_b ≡₁ ∅      /\ exa_d ≡₁ eq b_t /\ extra_d ≡₁ ∅     ) \/
  (extra_b ≡₁ ∅      /\ exa_d ≡₁ ∅      /\ extra_d ≡₁ eq b_t) \/
  (extra_b ≡₁ ∅      /\ exa_d ≡₁ ∅      /\ extra_d ≡₁ ∅     ).
Proof using STEP INV'.
  clear - STEP INV'.
  unfold extra_b, exa_d, extra_d, a_s; desf.
  all: desf; eauto 7.
  { exfalso. enough (cmt_t b_t) by auto.
    now apply (WCore.dtrmt_cmt STEP). }
  exfalso. enough (cmt_t b_t) by auto.
  now apply (WCore.dtrmt_cmt STEP).
Qed.

Lemma exa_d_exas
    (SOME : exa_d ≡₁ eq b_t) :
  A_s ≡₁ eq b_t /\ A_s' ≡₁ eq b_t.
Proof using STEP INV'.
  unfold exa_d, a_s in SOME.
  desf; [| exfalso; eapply SOME; eauto].
  assert (BIN : E_t b_t).
  { now apply (rexec_dtrmt_in_start STEP). }
  assert (BIN' : E_t' b_t).
  { now apply (rexec_dtrmt_in_fin STEP). }
  assert (NINA' : ~E_t a_t).
  { now apply exa_d_some_helper. }
  unfold extra_a; desf.
  all: exfalso; tauto.
Qed.

Lemma extra_db_nexa
    (ORG : extra_d ≡₁ eq b_t \/ extra_b ≡₁ eq b_t) :
  A_s' ≡₁ ∅.
Proof using STEP INV'.
  unfold extra_d, extra_b in ORG; desf.
  all: try now exfalso; eapply ORG; eauto.
  { apply extra_a_none_l, (WCore.reexec_embd_dom STEP).
    desf. }
  apply extra_a_none_l. desf.
Qed.

Lemma extra_b_exa_d_dtrmt_helper
    (EXB : extra_b ≡₁ ∅)
    (EXA : exa_d ≡₁ ∅)
    (NDB : dtrmt_t b_t) :
  dtrmt_t a_t.
Proof using.
  unfold extra_b in EXB; desf.
  all: try now exfalso; eapply EXB; eauto.
  unfold exa_d in EXA; desf.
  all: try now exfalso; eapply EXA; eauto.
  assert (AIN : E_t' a_t) by tauto.
  tauto.
Qed.

Lemma extra_b_exa_d_cases
    (EXB : extra_b ≡₁ ∅)
    (EXA : exa_d ≡₁ ∅) :
  ( dtrmt_t b_t /\  dtrmt_t a_t) \/
  (~dtrmt_t b_t /\ ~dtrmt_t a_t).
Proof using INV' STEP.
  destruct classic with (dtrmt_t a_t) as [DA|NDA].
  { enough (DB : dtrmt_t b_t) by eauto.
    assert (INA : E_t' a_t).
    { now apply (rexec_dtrmt_in_fin STEP). }
    assert (INB : E_t' b_t).
    { now apply (rsr_at_bt_ord INV'). }
    apply dtrmt_t_sb_closed.
    exists a_t, a_t. split; [| basic_solver].
    unfold sb. unfolder. splits; auto.
    apply INV'. }
  destruct classic with (dtrmt_t b_t) as [DB|NDB]; eauto.
  exfalso. apply NDA.
  now apply extra_b_exa_d_dtrmt_helper.
Qed.

Lemma extra_cases_ext :
  (extra_b ≡₁ eq b_t /\ exa_d ≡₁ ∅      /\ extra_d ≡₁ ∅      /\ A_s' ≡₁ ∅     ) \/
  (extra_b ≡₁ ∅      /\ exa_d ≡₁ eq b_t /\ extra_d ≡₁ ∅      /\ A_s' ≡₁ eq b_t) \/
  (extra_b ≡₁ ∅      /\ exa_d ≡₁ ∅      /\ extra_d ≡₁ eq b_t /\ A_s' ≡₁ ∅     ) \/
  (extra_b ≡₁ ∅      /\ exa_d ≡₁ ∅      /\ extra_d ≡₁ ∅     ).
Proof using STEP INV'.
  clear - STEP INV'.
  destruct extra_cases
        as [(EXB & EXA & EXD) |
           [(EXB & EXA & EXD) |
           [(EXB & EXA & EXD) |
            (EXB & EXA & EXD) ]]].
  all: eauto 7.
  { left. splits; auto.
    apply extra_db_nexa; eauto. }
  { right; left. splits; auto.
    apply exa_d_exas; eauto. }
  right; right; left. splits; auto.
  apply extra_db_nexa; eauto.
Qed.

Lemma reexec_acts_s_helper1
    (NDA : ~dtrmt_t a_t)
    (INA : E_t' a_t) :
  tid ↑₁ (E_t' \₁ (dtrmt_t \₁ eq b_t)) ≡₁
    tid ↑₁ (E_t' \₁ dtrmt_t).
Proof using INV'.
  clear - INV' NDA INA.
  rewrite set_minus_minus_r, set_collect_union.
  rewrite set_union_absorb_r; [reflexivity |].
  enough (tid a_t = tid b_t) by basic_solver.
  apply INV'.
Qed.

Lemma reexec_threads_s :
  WCore.reexec_thread X_s' dtrmt_s ≡₁
    WCore.reexec_thread X_t' dtrmt_t.
Proof using STEP INV' STEP.
  destruct extra_cases_ext
        as [(EXB & EXA & EXD & EXA') |
           [(EXB & EXA & EXD & EXA') |
           [(EXB & EXA & EXD & EXA') |
            (EXB & EXA & EXD) ]]].
  all: unfold dtrmt_s.
  all: rewrite EXB, EXA, EXD.
  all: rewrite ?set_union_empty_r, ?set_minus_empty_r.
  all: unfold WCore.reexec_thread.
  all: change E_s' with (mapper ↑₁ E_t' ∪₁ A_s').
  all: rewrite 1?EXA', 1?set_union_empty_r.
  { admit. }
  { rewrite set_minus_union_l.
    arewrite (eq b_t \₁ (mapper ↑₁ dtrmt_t ∪₁ eq b_t) ≡₁ ∅).
    { rewrite set_minus_union_r, set_minusK.
      now rewrite set_inter_empty_r. }
    rewrite set_union_empty_r, <- set_minus_minus_l.
    (* b_t is not the set since A_s' is some,
        which means a_t is absent. *)
    admit. }
  { admit. }
  (* Second case trivial, because it's mapper and tid stuff *)
  unfold extra_a; desf; [| admit].
  (* by lemma both b_t and a_t not in dtrmt_t *)
  (* absorb rule works for the b_t *)
Admitted.

Lemma reexec_thread_mapper
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  mapper ↑₁ (tid ↓₁ WCore.reexec_thread X_t' dtrmt_t) ≡₁
    tid ↓₁ WCore.reexec_thread X_t' dtrmt_t.
Proof using INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TID : tid a_t = tid b_t) by apply INV.
  eapply rsr_setE_iff; eauto.
  destruct classic
      with ((tid ↓₁ WCore.reexec_thread X_t' dtrmt_t) a_t)
        as [INA|NINA].
  all: unfolder; rewrite <- TID; auto.
Qed.

Lemma reexec_acts_s_helper
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  A_s ⊆₁ tid ↓₁ WCore.reexec_thread X_t' dtrmt_t ∪₁
            tid ↓₁ (tid ↑₁ A_s').
Proof using INV INV'.
  clear - INV INV' GREEXEC.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  unfold extra_a at 1; desf.
  assert (NDA : ~ dtrmt_t a_t).
  { intro FALSO. enough (E_t a_t) by desf.
    eapply rexec_dtrmt_in_start; eauto. }
  destruct classic with (dtrmt_t b_t) as [DB|NDB].
  { unfold extra_a; desf; [basic_solver |].
    assert (INB : E_t' b_t).
    { eapply rexec_dtrmt_in_fin; eauto. }
    assert (INA : E_t' a_t) by tauto.
    apply set_subset_union_r. left.
    unfold WCore.reexec_thread. basic_solver. }
  assert (INB : E_t b_t) by desf.
  apply (WCore.rexec_acts GREEXEC) in INB.
  destruct INB as [DB | [_ OK]]; basic_solver.
Qed.

Lemma reexec_acts_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  E_s ≡₁ dtrmt_s ∪₁ E_s ∩₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt_s.
Proof using INV INV' SIMREL RCFAT.
  clear - INV INV' GREEXEC SIMREL RCFAT.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TID : tid a_t = tid b_t) by apply INV.
  enough (SUB : E_s \₁ dtrmt_s ⊆₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt_s).
  { split; [|
      rewrite (dtrmt_in_E_s GREEXEC) at 1;
        basic_solver].
    rewrite set_union_minus
       with (s := E_s) (s' := dtrmt_s)
         at 1
         by eauto using dtrmt_in_E_s.
    rewrite <- SUB. basic_solver. }
  arewrite (E_s \₁ dtrmt_s ⊆₁ E_s \₁ mapper ↑₁ (dtrmt_t \₁ extra_b)).
  { unfold dtrmt_s. basic_solver. }
  rewrite reexec_threads_s; eauto.
  rewrite (rsr_acts SIMREL), set_minus_union_l.
  rewrite set_map_union.
  arewrite (
    A_s \₁ (mapper ↑₁ (dtrmt_t \₁ extra_b)) ≡₁ A_s
  ).
  { unfold extra_a; desf; [| basic_solver].
    split; [clear; basic_solver |].
    unfolder. intros x XEQ. subst. split; auto.
    unfold extra_b; intro FALSO; do 2 desf.
    all: enough (E_t a_t) by eauto.
    all: eapply rexec_dtrmt_in_start; eauto.
    { erewrite <- (rsr_mapper_inv_bt y NEQ); eauto. }
    erewrite <- rsr_mapper_inv_bt; eauto. }
  apply set_subset_union_l.
  split; eauto using reexec_acts_s_helper.
  rewrite <- set_collect_minus;
    [| eapply inj_dom_mori; eauto with xmm; red; auto with hahn].
  rewrite <- reexec_thread_mapper; eauto.
  rewrite set_minus_minus_r, set_collect_union.
  apply set_subset_union_l. split.
  { apply set_subset_union_r. left.
    rewrite (WCore.rexec_acts GREEXEC). basic_solver. }
  unfold extra_b. desf; [| basic_solver].
  destruct classic with (E_t' a_t) as [INA | NINA].
  { apply set_subset_union_r. left.
    apply set_collect_mori; auto.
    unfolder. ins. desf.
    rewrite <- TID. unfold WCore.reexec_thread.
    basic_solver. }
  assert (INB' : E_t' b_t).
  { eapply rexec_dtrmt_in_fin; eauto. desf. }
  rewrite extra_a_some; auto.
  assert (INB : E_t b_t).
  { eapply rexec_dtrmt_in_start; eauto. desf. }
  rewrite set_inter_absorb_l by basic_solver.
  apply set_subset_union_r. right.
  rewrite set_collect_eq, rsr_mapper_bt; auto.
  basic_solver.
Qed.

Lemma reexec_extra_a_ncmt
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  extra_a X_t' a_t b_t b_t ⊆₁ set_compl cmt_s.
Proof using INV.
  clear - INV GREEXEC.
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold extra_a, cmt_s. desf.
  unfolder. ins. desf.
  intros (y & CMT & MAP).
  assert (YIN : E_t' y).
  { now apply (WCore.reexec_embd_dom GREEXEC). }
  enough (E_t' a_t) by desf.
  erewrite <- (rsr_mapper_inv_bt _ NEQ); eauto.
Qed.

Lemma dtrmt_in_cmt
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  dtrmt_s ⊆₁ cmt_s.
Proof using INV.
  unfold dtrmt_s.
  rewrite extra_d_cmt; eauto.
  apply set_subset_union_l. split; auto with hahn.
  unfold cmt_s.
  apply set_collect_mori; auto.
  transitivity dtrmt_t; [basic_solver |].
  exact (WCore.dtrmt_cmt GREEXEC).
Qed.

Lemma imm_sb_d_s_refl_helper x :
  ⦗eq x⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq x⦘ ⊆ ∅₂.
Proof using.
  unfold nin_sb. rewrite immediateE.
  transitivity (⦗eq x⦘ ⨾ sb_t' ⨾ ⦗eq x⦘); [basic_solver|].
  unfolder. ins. desf. eapply sb_irr; eauto.
Qed.

Lemma imm_sb_d_s_to_a_helper :
  immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘ ⊆
    ⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘.
Proof using INV INV'.
  clear - INV INV'.
  assert (NINIT : ~is_init b_t) by apply INV.
  assert (IMM :
    (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⊆
      immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘
  ).
  { transitivity (
      ⦗set_compl is_init⦘ ⨾ (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⨾ ⦗eq a_t⦘
    ); [basic_solver |].
    rewrite (rsr_at_bt_imm INV').
    unfold nin_sb. basic_solver. }
  intros x y HREL.
  exists x. split; [| apply HREL]. unfolder.
  split; auto.
  destruct HREL as (a' & SB & EQ).
  unfolder in EQ. destruct EQ as (EQ & EQ').
  subst y a'.
  assert (INA : E_t' a_t).
  { enough (SB' : sb_t' x a_t).
    { hahn_rewrite wf_sbE in SB'.
      forward apply SB'. clear. basic_solver. }
    unfold nin_sb in SB.
    forward apply SB. basic_solver. }
  assert (INB : E_t' b_t).
  { now apply (rsr_at_bt_ord INV'). }
  eapply nin_sb_functional_l with (G := G_t').
  { apply INV'. }
  { unfold transp.
    enough (SB' : (immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘) b_t a_t).
    { forward apply SB'. basic_solver. }
    apply (IMM b_t a_t). basic_solver. }
  unfold transp. auto.
Qed.

Lemma imm_sb_d_s_from_b_helper :
  ⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⊆
    ⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘.
Proof using INV INV'.
  clear - INV INV'.
  assert (NINIT : ~is_init b_t) by apply INV.
  assert (IMM :
    (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⊆
      immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘
  ).
  { transitivity (
      ⦗set_compl is_init⦘ ⨾ (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⨾ ⦗eq a_t⦘
    ); [basic_solver |].
    rewrite (rsr_at_bt_imm INV').
    unfold nin_sb. basic_solver. }
  rewrite <- seqA. intros x y HREL.
  exists y. split; [apply HREL |]. unfolder.
  split; auto.
  assert (INB : E_t' b_t).
  { enough (SB' : sb_t' b_t y).
    { hahn_rewrite wf_sbE in SB'.
      forward apply SB'. clear. basic_solver. }
    unfold nin_sb in HREL.
    forward apply HREL. basic_solver. }
  destruct classic with (~E_t' a_t) as [NINA|INA'].
  { exfalso.
    eapply (rsr_bt_max INV'); eauto.
    enough (SB : sb_t' b_t y).
    { unfolder. splits; eauto. }
    forward apply HREL. clear.
    unfold nin_sb. basic_solver. }
  assert (INA : E_t' a_t) by tauto. clear INA'.
  destruct HREL as (a' & EQ & SB).
  unfolder in EQ. destruct EQ as (EQ & EQ').
  subst a' x.
  eapply nin_sb_functional_r with (G := G_t').
  { apply INV'. }
  { unfold transp.
    enough (SB' : (immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘) b_t a_t).
    { forward apply SB'. basic_solver. }
    apply (IMM b_t a_t). basic_solver. }
  auto.
Qed.

Lemma imm_sb_d_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  ⦗dtrmt_s⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗cmt_s⦘ ⊆
    ⦗dtrmt_s⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗dtrmt_s⦘.
Proof using INV INV' LVAL NLOC ARW ARLX.
  clear - INV INV' GREEXEC LVAL NLOC ARW ARLX.
  assert (NB : ~is_init b_t) by apply INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (NEQ' : b_t <> a_t) by congruence.
  rewrite rsr_sbE_imm
     with (X_s := X_s') (X_t := X_t') (a_t := a_t) (b_t := b_t).
  all: eauto using reexec_simrel.
  rewrite !seq_union_l, !seq_union_r.
  rewrite extra_sbE; eauto using reexec_simrel.
  seq_rewrite <- cross_inter_l.
  arewrite (dtrmt_s ∩₁ extra_a X_t' a_t b_t b_t ≡₁ ∅).
  { split; [| auto with hahn].
    rewrite reexec_extra_a_ncmt, dtrmt_in_cmt; eauto.
    clear. basic_solver. }
  apply union_mori; [| basic_solver].
  destruct classic with (dtrmt_t a_t) as [AD | AND].
  { assert (ACMT : cmt_t a_t).
    { now apply (WCore.dtrmt_cmt GREEXEC). }
    assert (AIN : E_t a_t).
    { eapply rexec_dtrmt_in_start; eauto. }
    assert (BIN : E_t b_t).
    { now apply (rsr_at_bt_ord INV). }
    assert (BDA : dtrmt_t b_t).
    { eapply rexec_dtrmt_sb_dom; eauto.
      exists a_t; unfolder. split; auto.
      unfold sb; unfolder; splits; auto.
      apply INV. }
    assert (BCMT : cmt_t b_t).
    { now apply (WCore.dtrmt_cmt GREEXEC). }
    unfold cmt_s, dtrmt_s, extra_d, extra_b; desf; desf.
    rewrite set_union_empty_r.
    arewrite (dtrmt_t \₁ ∅ ≡₁ dtrmt_t) by basic_solver.
    do 2 (rewrite rsr_setE_iff; eauto).
    apply (WCore.dtrmt_sb_max GREEXEC). }
  destruct classic with (cmt_t a_t) as [AC | NAC].
  { assert (AIN : E_t' a_t).
    { now apply (WCore.reexec_embd_dom GREEXEC). }
    assert (BIN : E_t' b_t).
    { now apply (rsr_at_bt_ord INV'). }
    assert (SBA : immediate (nin_sb G_t') b_t a_t).
    { unfold nin_sb.
      enough (SB : immediate sb_t' b_t a_t).
      { apply seq_eqv_imm. forward apply SB. basic_solver. }
      apply (rsr_at_bt_imm INV'). basic_solver. }
    assert (ND : ~dtrmt_t b_t).
    { intro FALSO. apply AND.
      eapply rexec_dtrmt_sbimm_codom; eauto.
      exists b_t. forward apply SBA. basic_solver 11. }
    unfold dtrmt_s, cmt_s, extra_b; desf; desf.
    arewrite (dtrmt_t \₁ ∅ ≡₁ dtrmt_t) by basic_solver.
    unfold extra_d; desf; [| rewrite set_union_empty_r].
    { unfold a_s. desf.
      rewrite rsr_setE_iff, rsr_setE_ex; eauto.
      rewrite !id_union, !seq_union_l, !seq_union_r.
      arewrite_false (⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘).
      { apply imm_sb_d_s_refl_helper. }
      arewrite_false (⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt_t \₁ eq a_t⦘).
      { sin_rewrite imm_sb_d_s_from_b_helper.
        clear. basic_solver. }
      rewrite !union_false_r. apply inclusion_union_r. left.
      apply union_mori; [| reflexivity].
      arewrite (
        ⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt_t \₁ eq a_t⦘ ≡
        ⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt_t⦘ ⨾ ⦗cmt_t \₁ eq a_t⦘
      ).
      { clear. basic_solver. }
      sin_rewrite (WCore.dtrmt_sb_max GREEXEC).
      clear. basic_solver. }
    rewrite rsr_setE_iff; eauto.
    destruct classic with (cmt_t b_t) as [BC|NBC].
    { rewrite rsr_setE_iff; eauto.
      apply (WCore.dtrmt_sb_max GREEXEC). }
    assert (NBD :
      ~ dom_rel (immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘) ⊆₁ dtrmt_t
    ) by tauto.
    rewrite rsr_setE_ex, id_union, !seq_union_r; eauto.
    arewrite (
      ⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt_t \₁ eq a_t⦘ ≡
      ⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt_t⦘ ⨾ ⦗cmt_t \₁ eq a_t⦘
    ).
    { clear. basic_solver. }
    sin_rewrite (WCore.dtrmt_sb_max GREEXEC).
    apply inclusion_union_l; [basic_solver |].
    arewrite_false (⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘);
      [| basic_solver].
    enough (HH : dom_rel (⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘) ⊆₁ ∅).
    { forward apply HH. clear. basic_solver 7. }
    intros x1 (b' & HSET). apply NBD.
    intros x2 (b'' & IMMSB).
    assert (b' = b_t); desf.
    { forward apply HSET. clear. basic_solver. }
    assert (b'' = b_t); desf.
    { forward apply IMMSB. clear. basic_solver. }
    enough (EQ : x1 = x2).
    { subst x1. forward apply HSET. basic_solver. }
    eapply nin_sb_functional_l with (G := G_t').
    { apply INV'. }
    { forward apply HSET. clear. basic_solver. }
    forward apply IMMSB. clear. basic_solver. }
  destruct classic with (dtrmt_t b_t) as [DB|NDB].
  { assert (BC : cmt_t b_t).
    { now apply (WCore.dtrmt_cmt GREEXEC). }
    unfold dtrmt_s, cmt_s, extra_b, extra_d.
    desf; desf; rewrite set_union_empty_r.
    { rewrite rsr_setE_iff; eauto; [| unfolder; tauto].
      rewrite rsr_setE_niff; eauto.
      rewrite id_union, !seq_union_r.
      arewrite_false (⦗dtrmt_t \₁ eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘).
      { sin_rewrite imm_sb_d_s_to_a_helper.
        clear. basic_solver. }
      rewrite union_false_r.
      arewrite (
        ⦗dtrmt_t \₁ eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt_t \₁ eq b_t⦘ ≡
        ⦗dtrmt_t \₁ eq b_t⦘ ⨾ ⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt_t⦘ ⨾ ⦗cmt_t \₁ eq b_t⦘
      ).
      { clear. basic_solver. }
      sin_rewrite (WCore.dtrmt_sb_max GREEXEC).
      clear. basic_solver. }
    exfalso. tauto. }
  destruct classic with (cmt_t b_t) as [CB|NCB].
  { unfold dtrmt_s, cmt_s, extra_b, extra_d.
    desf; desf.
    rewrite set_union_empty_r.
    arewrite (dtrmt_t \₁ ∅ ≡₁ dtrmt_t) by basic_solver.
    rewrite rsr_setE_iff; eauto.
    rewrite rsr_setE_niff; eauto.
    rewrite id_union, !seq_union_r.
    arewrite_false (⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘).
    { sin_rewrite imm_sb_d_s_to_a_helper.
      clear - NDB. basic_solver. }
    rewrite union_false_r.
    arewrite (
      ⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt_t \₁ eq b_t⦘ ≡
      ⦗dtrmt_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt_t⦘ ⨾ ⦗cmt_t \₁ eq b_t⦘
    ).
    { clear. basic_solver. }
    sin_rewrite (WCore.dtrmt_sb_max GREEXEC).
    clear. basic_solver. }
  unfold dtrmt_s, cmt_s, extra_b, extra_d.
  desf; desf.
  rewrite set_union_empty_r.
  arewrite (dtrmt_t \₁ ∅ ≡₁ dtrmt_t) by basic_solver.
  do 2 (rewrite rsr_setE_iff; eauto).
  apply (WCore.dtrmt_sb_max GREEXEC).
Qed.

Hypothesis GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle.

Lemma reexec_step :
  WCore.reexec X_s X_s' f_s dtrmt_s cmt_s.
Proof using INV INV' LVAL NLOC ARW ARLX RCFAT.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  assert (MEQA : mapper a_t = b_t).
  { now apply rsr_mapper_at. }
  assert (INJHELPER : inj_dom (codom_rel (⦗E_t' \₁ dtrmt_t⦘ ⨾ rf_t') ∪₁ dom_rel rhb_t'^?) mapper).
  { eapply inj_dom_mori; eauto with xmm.
    red. auto with hahn. }
  assert (EXNCMT : A_s' ∩₁ cmt_s ≡₁ ∅).
  { split; vauto.
    rewrite (reexec_extra_a_ncmt GREEXEC).
    clear. basic_solver. }
  assert (SURG :
    WCore.stable_uncmt_reads_gen X_s' cmt_s thrdle
  ).
  { constructor; try now apply GREEXEC.
    admit. }
  assert (WF_START :
    WCore.wf (WCore.X_start X_s dtrmt_s) X_s' cmt_s
  ).
  { admit. (* TODO *) }
  (**)
  red. exists thrdle.
  constructor.
  { admit. }
  { eapply dtrmt_in_cmt; eauto. }
  { unfold f_s, dtrmt_s.
    apply fixset_union. split.
    { rewrite Combinators.compose_assoc.
      apply fixset_swap.
      rewrite Combinators.compose_assoc,
              rsr_mapper_compose,
              Combinators.compose_id_right.
      all: auto.
      eapply fixset_mori; auto; try now apply GREEXEC.
      clear. red. basic_solver. }
    unfold extra_d. desf. unfold a_s.
    unfolder. unfold compose. ins. desf.
    rewrite (rsr_mapper_bt NEQ).
    rewrite RCFAT; auto. }
  { unfold cmt_s.
    admit. }
  { exact SURG. }
  { admit. (* sb-clos *) }
  { eapply imm_sb_d_s; eauto. }
  { admit. (* rpo edges *) }
  { constructor.
    { intros x' y'; unfold cmt_s, f_s.
      intros [x [Hx]] [y [Hy]]; subst x' y'.
      unfold compose.
      change (mapper (mapper x)) with ((mapper ∘ mapper) x).
      change (mapper (mapper y)) with ((mapper ∘ mapper) y).
      rewrite !rsr_mapper_compose; auto; unfold id; intro EQf.
      enough (EQxy: x = y); [by rewrite EQxy|].
      apply (WCore.reexec_embd_inj (WCore.reexec_embd_corr GREEXEC)); auto.
      apply (rsr_inj SIMREL).
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      done. }
    { intros e CMT.
      change (tid (f_s e)) with ((tid ∘ f_s) e).
      unfold f_s.
      rewrite <- !Combinators.compose_assoc.
      change ((tid ∘ mapper ∘ f_t ∘ mapper) e)
        with ((tid ∘ mapper) ((f_t ∘ mapper) e)).
      unfold cmt_s in CMT. unfolder in CMT.
      destruct CMT as (e' & CMT & EQ); subst e.
      assert (INE : E_t ((f_t ∘ mapper) (mapper e'))).
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
        unfolder. exists e'. split; auto.
        change ((f_t ∘ mapper) (mapper e'))
          with (f_t ((mapper ∘ mapper) e')).
        rewrite rsr_mapper_compose; now unfold id. }
      rewrite (rsr_tid SIMREL); auto.
      unfold compose.
      rewrite rsr_mapper_self_inv, rsr_mapper_tid'; auto.
      now apply GREEXEC. }
    { intros e CMT.
      change (lab_s (f_s e)) with ((lab_s ∘ f_s) e).
      unfold f_s.
      rewrite <- !Combinators.compose_assoc.
      unfold cmt_s in CMT. unfolder in CMT.
      destruct CMT as (e' & CMT & EQ); subst e.
      change ((lab_s ∘ mapper ∘ f_t ∘ mapper) (mapper e'))
        with ((lab_s ∘ mapper) ((f_t ∘ (mapper ∘ mapper)) e')).
      change (lab_s' (mapper e')) with ((lab_s' ∘ mapper) e').
      rewrite rsr_mapper_compose, Combinators.compose_id_right; auto.
      rewrite (rsr_lab SIMREL);
        [| apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver].
      rewrite (rsr_lab reexec_simrel);
        [| apply (WCore.reexec_embd_dom GREEXEC); auto].
      now apply GREEXEC. }
    { admit. }
    { rewrite (rsr_rf reexec_simrel),
              restr_union, collect_rel_union.
      arewrite_false (restr_rel cmt_s
        (srf_s' ⨾ ⦗extra_a X_t' a_t b_t b_t ∩₁ R_s'⦘)).
      { rewrite restr_relE, !seqA, <- id_inter.
        rewrite (reexec_extra_a_ncmt GREEXEC).
        clear. basic_solver. }
      rewrite collect_rel_empty, union_false_r.
      unfold cmt_s, f_s.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto with xmm;
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite rsr_mapper_compose; auto.
      rewrite Combinators.compose_assoc,
              Combinators.compose_id_right.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_rf (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_rf SIMREL); auto with hahn. }
    { rewrite (rsr_co reexec_simrel),
              restr_union, collect_rel_union.
      arewrite_false (restr_rel cmt_s
        (add_max (extra_co_D E_s' lab_s' (loc_s' b_t))
          (extra_a X_t' a_t b_t b_t ∩₁ W_s'))).
      { rewrite restr_add_max. unfold add_max.
        rewrite (reexec_extra_a_ncmt GREEXEC) at 2.
        clear. basic_solver. }
      rewrite collect_rel_empty, union_false_r.
      unfold cmt_s, f_s.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto with xmm;
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite rsr_mapper_compose; auto.
      rewrite Combinators.compose_assoc,
              Combinators.compose_id_right.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_co (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_co SIMREL); auto with hahn. }
    { rewrite (rsr_rmw reexec_simrel).
      unfold cmt_s, f_s.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto with xmm;
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite rsr_mapper_compose; auto.
      rewrite Combinators.compose_assoc,
              Combinators.compose_id_right.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_rmw (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_rmw SIMREL); auto with hahn. }
    unfold cmt_s, f_s.
    rewrite <- !set_collect_compose.
    rewrite Combinators.compose_assoc.
    rewrite rsr_mapper_compose; auto.
    rewrite Combinators.compose_assoc,
            Combinators.compose_id_right.
    rewrite set_collect_compose.
    rewrite (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
    rewrite (rsr_acts SIMREL); auto with hahn. }
  { apply (G_s_rfc INV' reexec_simrel). }
  { exact WF_START. (* wf start *) }
  { apply (rsr_cons INV' CONS reexec_simrel). }
  { eapply reexec_acts_s; eauto. }
  apply sub_to_full_exec_listless
   with (thrdle := thrdle).
  { exact WF_START. }
  { eapply G_s_rfc with (X_t := X_t').
    { apply INV'. }
    now apply reexec_simrel. }
  { apply (rsr_cons INV' CONS reexec_simrel). }
  { admit. (* difference between acts and dtrmt is fin *) }
  { admit. (* Prefix. Trivial? *) }
  { eapply G_s_wf with (X_t := X_t').
    { apply INV'. }
    now apply reexec_simrel. }
  { admit. (* init acts *) }
  { now rewrite (rsr_ndata INV'). }
  { now rewrite (rsr_naddr INV'). }
  { now rewrite (rsr_nctrl INV'). }
  { now rewrite (rsr_nrmw_dep INV'). }
  exact SURG.
Admitted.

End ReorderingReexec.