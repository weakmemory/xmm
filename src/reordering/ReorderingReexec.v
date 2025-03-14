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
Notation "'is_init'" := (fun e => is_true (is_init e)).

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

Lemma rsr_rex_disj_helper :
  set_disjoint E_s'' A_s'.
Proof using INV'.
  assert (NEQ : a_t <> b_t) by apply INV'.
  unfold extra_a. desf. simpl.
  unfolder. intros x (y & YIN & XEQ') XEQ. subst x.
  enough (y = a_t) by desf.
  eapply rsr_mapper_inv_bt; eauto.
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
  { rewrite <- extra_a_some
       with (a_t := a_t) (b_t := b_t)
            (a_s := b_t) (X_t := X_t').
    apply rsr_rex_disj_helper.
    all: desf. }
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
Definition f_s :=
  let f_s_ := (mapper ∘ f_t) ∘ mapper in
  ifP ~E_t' a_t /\ E_t' b_t then upd f_s_ b_t b_t
  else f_s_.

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

Lemma dtrmt_in_cmt :
  dtrmt_s ⊆₁ cmt_s.
Proof using INV STEP.
Admitted.

Lemma cmt_in_E_s :
  cmt_s ⊆₁ E_s'.
Proof using INV INV' STEP LVAL NLOC ARW ARLX.
Admitted.

Lemma dtrmt_in_E_s :
  dtrmt_s ⊆₁ E_s.
Proof using.
Admitted.

Lemma rex_dtrmt_init :
  is_init ⊆₁ dtrmt_s.
Proof using INV INV' STEP LVAL NLOC ARW ARLX.
Admitted.

Hint Resolve dtrmt_in_E_s dtrmt_in_cmt
             cmt_in_E_s rex_dtrmt_init : xmm.

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

Lemma rsr_rex_vf_helper1 :
  ⦗is_init⦘ ⨾ sb_s' ⨾ ⦗A_s'⦘ ⨾
    same_tid ⨾ ⦗E_s'' \₁ cmt_s ∪₁ A_s' \₁ cmt_s⦘
      ⊆ tid ↓ thrdle.
Proof using INV' STEP.
  unfold extra_a. desf; [| basic_solver].
  assert (TID : tid b_t <> tid_init).
  { apply (rsr_bt_tid INV'). }
  remember (E_s'' \₁ cmt_s ∪₁ eq b_t \₁ cmt_s) as s.
  unfolder.
  intros x y (XINI & z & (_ & EQ & SAME & _)).
  subst z. destruct x as [xl | xt xn]; ins.
  apply (WCore.surg_init_least (WCore.reexec_sur STEP)).
  rewrite <- SAME. auto.
Qed.

Lemma rsr_rex_vf_helper2 :
  mapper ↑ vf_rhb_t' ⨾ same_tid ⨾
    ⦗E_s'' \₁ cmt_s ∪₁ A_s' \₁ cmt_s⦘ ⊆
      mapper ↑ vf_rhb_t' ⨾ same_tid ⨾
        ⦗E_s'' \₁ cmt_s⦘ ⨾ same_tid ⨾
          ⦗E_s'' \₁ cmt_s ∪₁ A_s' \₁ cmt_s⦘.
Proof using INV' STEP.
  assert (NEQ : a_t <> b_t) by apply INV'.
  assert (TIDE : tid a_t = tid b_t) by apply INV'.
  apply seq_mori; [reflexivity |].
  rewrite id_union, !seq_union_r.
  apply union_mori.
  { remember (E_s'' \₁ cmt_s) as s.
    clear. unfold same_tid.
    basic_solver 11. }
  unfold extra_a. desf; [| clear; basic_solver].
  destruct classic
      with (exists e, ~cmt_t e /\ tid e = tid b_t /\ E_t' e)
        as [(e & NCMT & TID & EIN)| NON].
  { unfolder. intros x y (SAME & EQ & BNCMT).
    subst y. exists (mapper e). splits; auto.
    all: unfold same_tid.
    all: rewrite 1?rsr_mapper_tid'; auto.
    { rewrite SAME. congruence. }
    { simpl. unfolder. eauto. }
    unfold cmt_s. intros [(e' & XEQ & XIN) | EXA].
    { enough (e' = e) by congruence.
      apply (rsr_mapper_inj NEQ).
      all: try red; auto. }
    unfold exa_d in EXA. desf.
    unfold a_s in *.
    enough (E_t' a_t) by desf.
    enough (e = a_t) by congruence.
    eapply rsr_mapper_inv_bt; eauto. }
  assert (FOR' :
    forall e, ~(~cmt_t e /\ tid e = tid b_t /\ E_t' e)
  ).
  { now apply not_ex_all_not. }
  assert (FOR :
    forall e, cmt_t e \/ tid e <> tid b_t \/ ~E_t' e
  ).
  { intro e. specialize FOR' with e.
    clear - FOR'. tauto. }
  assert (ALCMT :
    forall e (EIN : E_t' e) (TEQ : tid e = tid b_t),
      cmt_t e).
  { intros e EIN TEQ.
    destruct FOR with e as [CMT' | [TEQ' | EIN']].
    all: auto; try congruence. }
  assert (BDT : dtrmt_t b_t).
  { admit. }
  unfold cmt_s.
  arewrite (exa_d ≡₁ eq b_t).
  { unfold exa_d. desf. tauto. }
  arewrite (eq b_t \₁ (mapper ↑₁ cmt_t ∪₁ eq b_t) ≡₁ ∅).
  { split; [| auto with hahn].
    rewrite set_minus_union_r, set_minusK.
    now rewrite set_inter_empty_r. }
  clear. rewrite eqv_empty. basic_solver.
Admitted.

Lemma rsr_rex_vf_helper3 :
  E_s'' \₁ cmt_s ⊆₁ mapper ↑₁ (E_t' \₁ cmt_t).
Proof using INV' STEP.
  assert (NEQ : a_t <> b_t) by apply INV'.
  unfold cmt_s.
  rewrite set_minus_union_r. simpl.
  rewrite set_minus_disjoint with (s2 := exa_d).
  { rewrite set_inter_minus_l, set_interK.
    rewrite <- set_collect_minus
      ; [| eapply inj_dom_mori; eauto with xmm].
    all: unfold flip; auto with hahn. }
  unfold exa_d, a_s. desf. unfolder.
  intros x (y & YIN & YEQ) XEQ. subst x.
  enough (y = a_t) by desf.
  now apply (rsr_mapper_inv_bt _ NEQ).
Qed.

Lemma rsr_rex_vf :
  vf_s' ⨾ same_tid ⨾ ⦗E_s' \₁ cmt_s⦘ ⊆ tid ↓ thrdle ∪ same_tid.
Proof using INV' STEP LVAL.
  assert (WF_S : Wf G_s').
  { now apply new_G_s_wf. }
  assert (ANIN : ~is_init a_t).
  { apply INV'. }
  assert (BNIN : ~is_init b_t).
  { apply INV'. }
  apply thrdle_with_rhb; try now apply STEP.
  { exact WF_S. }
  { apply (rsr_ninit_acts_s INV' reexec_simrel). }
  assert (NEQ : a_t <> b_t) by apply INV'.
  change E_s' with (E_s'' ∪₁ A_s').
  rewrite set_minus_union_l.
  arewrite (
    vf_rhb_s' ⊆
      vf_rhb_s' ⨾ ⦗E_s' \₁ A_s'⦘ ∪
        vf_rhb_s' ⨾ ⦗A_s'⦘
  ).
  { rewrite (wf_vfrhbE WF_S) at 1.
    rewrite set_union_minus
       with (s := E_s') (s' := A_s')
         at 2; [| simpl; basic_solver].
    rewrite id_union. clear. basic_solver. }
  rewrite rsr_rex_vfexa'.
  do 2 sin_rewrite rsr_rex_vf_nesting'.
  do 2 sin_rewrite rsr_rex_vf_nesting.
  rewrite <- unionA, !seqA.
  rewrite !seq_union_l, !seqA.
  do 2 arewrite (
    mapper ↑ vf_rhb_t' ⨾ ⦗E_s' \₁ A_s'⦘ ⊆
      mapper ↑ vf_rhb_t'
  ).
  rewrite sb_tid_init'.
  rewrite !seq_union_l, !seq_union_r.
  arewrite (
    sb_s' ∩ same_tid ⨾ ⦗A_s'⦘ ⨾ same_tid ⊆
      same_tid
  ).
  { transitivity (same_tid ⨾ same_tid)
      ; [basic_solver |].
    clear. rewrite rewrite_trans; auto with hahn.
    unfold same_tid. unfolder. ins. congruence. }
  arewrite (
    mapper ↑ vf_rhb_t' ⨾ ⦗is_init⦘ ⊆ ⦗is_init⦘
  ).
  { rewrite fixset_set_fixpoint
       with (f := mapper) (s := is_init)
         at 1; [| auto with xmm].
    rewrite <- collect_rel_eqv.
    rewrite <- collect_rel_seq
          ; [| eapply inj_dom_mori; eauto with xmm].
    all: unfold flip; auto with hahn.
    rewrite vf_rhb_to_init, collect_rel_eqv.
    all: try now apply INV'.
    rewrite <- fixset_set_fixpoint.
    all: auto with xmm hahn. }
  arewrite (
    ⦗A_s' ∩₁ W_s'⦘ ⨾ same_tid ⨾ ⦗E_s'' \₁ cmt_s ∪₁ A_s' \₁ cmt_s⦘ ⊆
      same_tid
  ).
  { basic_solver. }
  arewrite (
    ⦗is_init⦘ ⨾ sb_s' ⨾ ⦗A_s'⦘ ⨾ same_tid
       ⨾ ⦗E_s'' \₁ cmt_s ∪₁ A_s' \₁ cmt_s⦘ ⊆
        tid ↓ thrdle).
  { apply rsr_rex_vf_helper1. }
  arewrite (
    mapper ↑ vf_rhb_t' ⨾ same_tid ⨾
      ⦗E_s'' \₁ cmt_s ∪₁ A_s' \₁ cmt_s⦘ ⊆
        mapper ↑ vf_rhb_t' ⨾ same_tid ⨾ ⦗E_s'' \₁ cmt_s⦘ ⨾
          same_tid ⨾ ⦗E_s'' \₁ cmt_s ∪₁ A_s' \₁ cmt_s⦘
  ).
  { apply rsr_rex_vf_helper2. }
  arewrite (E_s'' \₁ cmt_s ⊆₁ mapper ↑₁ (E_t' \₁ cmt_t)).
  { apply rsr_rex_vf_helper3. }
  rewrite <- collect_rel_eqv.
  assert (
    MAP : mapper ↑ vf_rhb_t' ⨾ same_tid ⨾ mapper ↑ ⦗E_t' \₁ cmt_t⦘ ⊆
      mapper ↑ (vf_rhb_t' ⨾ same_tid ⨾ ⦗E_t' \₁ cmt_t⦘)
  ).
  { admit. }
  do 2 sin_rewrite MAP.
  arewrite (
    vf_rhb_t' ⨾ same_tid ⨾ ⦗E_t' \₁ cmt_t⦘ ⊆
     tid ↓ thrdle ∪ same_tid
  ).
  { apply thrdle_with_rhb; try now apply STEP.
    all: apply INV'. }
  admit.
Admitted.

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

Lemma reexec_thread_mapper :
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

Lemma reexec_acts_s :
  E_s ≡₁ dtrmt_s ∪₁ E_s ∩₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt_s.
Proof using INV INV' SIMREL RCFAT STEP.
  clear - INV INV' STEP SIMREL RCFAT.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TID : tid a_t = tid b_t) by apply INV.
  enough (SUB : E_s \₁ dtrmt_s ⊆₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt_s).
  { split; [| rewrite dtrmt_in_E_s at 1; basic_solver].
    rewrite set_union_minus
       with (s := E_s) (s' := dtrmt_s)
         at 1
         by eauto using dtrmt_in_E_s.
    rewrite <- SUB. basic_solver. }
  rewrite (rsr_acts SIMREL), set_minus_union_l.
  arewrite (
    mapper ↑₁ E_t \₁ (
      mapper ↑₁ (dtrmt_t \₁ extra_b) ∪₁
      extra_d ∪₁
      exa_d
    ) ⊆₁
    mapper ↑₁ E_t \₁ (
      mapper ↑₁ (dtrmt_t \₁ extra_b) ∪₁
      extra_d
    )
  ).
  { clear. basic_solver. }
  arewrite (
    A_s \₁ dtrmt_s ⊆₁
      A_s \₁ exa_d
  ).
  { clear. unfold dtrmt_s. basic_solver. }
  apply set_subset_union_l. split.
  { unfold dtrmt_s.
    transitivity (
      mapper ↑₁ E_t \₁ (mapper ↑₁ (dtrmt_t \₁ extra_b))
    ); [basic_solver |].
    rewrite set_collect_minus at 1
      ; [| eapply inj_dom_mori; eauto with xmm].
    all: unfold flip; auto with hahn.
    rewrite set_minus_minus_r, reexec_threads_s.
    apply set_subset_union_l. split.
    { rewrite <- set_collect_minus
      ; [| eapply inj_dom_mori; eauto with xmm].
      all: unfold flip; auto with hahn.
      rewrite <- reexec_thread_mapper.
      apply set_collect_mori; auto.
      rewrite (WCore.rexec_acts STEP), set_minus_union_l.
      rewrite set_minusK, set_union_empty_l.
      clear. basic_solver. }
    unfold extra_b; desf; [| basic_solver].
    rewrite set_collect_eq, rsr_mapper_bt; auto.
    unfold WCore.reexec_thread.
    transitivity (eq a_t); [basic_solver |].
    desf. basic_solver. }
  unfold exa_d, a_s; desf.
  { unfold extra_a; desf; [| basic_solver].
    rewrite set_minusK. auto with hahn. }
  rewrite set_minus_disjoint; [| basic_solver].
  unfold extra_a; desf; auto with hahn.
  assert (BIN : E_t b_t) by desf.
  rewrite reexec_threads_s.
  apply (WCore.rexec_acts STEP) in BIN.
  destruct BIN as [BD | NBD]
    ; [| forward apply NBD; desf; basic_solver].
  assert (INA : E_t' a_t) by tauto.
  assert (NDA : ~dtrmt_t a_t).
  { intro FALSO. enough (E_t a_t) by tauto.
    now apply (rexec_dtrmt_in_start STEP). }
  unfold WCore.reexec_thread. basic_solver.
Qed.

Lemma imm_sb_d_s :
  ⦗dtrmt_s⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗cmt_s⦘ ⊆
    ⦗dtrmt_s⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗dtrmt_s⦘.
Proof using INV INV' STEP LVAL NLOC ARW ARLX.
  rewrite (rsr_sbE_imm INV' reexec_simrel),
          (extra_sbE INV' reexec_simrel).
  rewrite !seq_union_l, !seq_union_r.
  arewrite (
    immediate (nin_sb G_t') ≡
      ⦗E_t'⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗E_t'⦘
  ).
  { admit. }
  seq_rewrite <- !id_inter.
  rewrite <- 2!cross_inter_r, <- 2!cross_inter_l.
  arewrite (dtrmt_s ∩₁ A_s' ≡₁ exa_d).
  { admit. }
Admitted.

Lemma sb_d_closed :
  sb_s ⨾ ⦗dtrmt_s⦘ ⊆
    ⦗dtrmt_s⦘ ⨾ sb_s ⨾ ⦗dtrmt_s⦘.
Proof using INV INV' STEP LVAL NLOC ARW ARLX.
Admitted.

Lemma sb_d_closed' :
  sb_s' ⨾ ⦗dtrmt_s⦘ ⊆
    ⦗dtrmt_s⦘ ⨾ sb_s' ⨾ ⦗dtrmt_s⦘.
Proof using INV INV' STEP LVAL NLOC ARW ARLX.
Admitted.

Lemma rex_pfx :
  SubToFullExec.prefix (WCore.X_start X_s dtrmt_s) X_s'.
Proof using INV INV' STEP LVAL NLOC ARW ARLX.
  constructor; ins.
  { rewrite set_inter_absorb_r; auto with xmm. }
  { rewrite dtrmt_in_cmt, cmt_in_E_s.
    change (mapper ↑₁ E_t' ∪₁ A_s') with E_s'.
    basic_solver. }
  { admit. }
  { admit. }
  { admit. (* FIXME: lab oddity *) }
  { rewrite set_inter_absorb_r; auto with xmm.
    change (
      mapper ↑ rf_t' ∪
      fake_srf (rsr_imm_g X_t' a_t b_t) b_t l_a ⨾ ⦗A_s' ∩₁ WCore.lab_is_r l_a⦘
    ) with rf_s'.
    rewrite <- restr_relE.
    rewrite (rsr_rf SIMREL), (rsr_rf reexec_simrel).
    admit. }
Admitted.

Lemma rsr_rex_restr_eq :
  WCore.exec_restr_eq (WCore.X_start X_s dtrmt_s) X_s' dtrmt_s.
Proof using INV INV' STEP LVAL NLOC ARW ARLX.
  assert (SUB : dtrmt_s ⊆₁ dtrmt_s ∩₁ E_s).
  { rewrite set_inter_absorb_r; auto with xmm hahn. }
  assert (NEQ : a_t <> b_t) by apply INV'.
  assert (NEQ' : b_t <> a_t) by now symmetry.
  constructor; ins.
  { admit. }
  { apply rex_pfx. }
  { eapply eq_dom_mori; try now apply rex_pfx.
    all: ins.
    unfold flip. rewrite set_inter_absorb_r; [basic_solver |].
    auto with xmm. }
  { now rewrite (prf_rf rex_pfx), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_co rex_pfx), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_rmw rex_pfx), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_data rex_pfx). }
  { now rewrite (prf_ctrl rex_pfx). }
  now rewrite (prf_rmw_dep rex_pfx).
Admitted.

Lemma rsr_rex_embd :
  WCore.commit_embedded X_s X_s' f_s cmt_s.
Proof using INV INV' LVAL STEP NLOC ARW ARLX RCFAT.
Admitted.

Lemma rsr_rex_ndtrmt_rlx :
  E_s' \₁ dtrmt_s ⊆₁
    set_compl (Rel_s' ∪₁ Acq_s').
Proof using SIMREL INV INV' LVAL STEP NLOC ARW ARLX RCFAT.
  assert (NEQ : a_t <> b_t) by apply INV.
  change E_s' with (mapper ↑₁ E_t' ∪₁ A_s').
  rewrite set_minus_union_l.
  arewrite (A_s' ⊆₁ set_compl (Rel_s' ∪₁ Acq_s')).
  { remember (set_compl (Rel_s' ∪₁ Acq_s')) as st.
    unfolder. intros x XIN. desf.
    now eapply eba_rlx, (rsr_as reexec_simrel). }
  apply set_subset_union_l. split; [| basic_solver].
  unfold dtrmt_s.
  transitivity (mapper ↑₁ E_t' \₁ (mapper ↑₁ (dtrmt_t \₁ extra_b)))
    ; [basic_solver 11 |].
  rewrite <- set_collect_minus
    ; [| eapply inj_dom_mori; auto with xmm
         ; unfold flip; auto with hahn].
  rewrite set_minus_minus_r, set_collect_union.
  apply set_subset_union_l. split.
  { arewrite (
      E_t' \₁ dtrmt_t ⊆₁
        (E_t' \₁ dtrmt_t) ∩₁ E_t'
    ) by basic_solver.
    rewrite (WCore.reexec_dtrmt_rpo STEP).
    unfolder. intros x' (x & RLX & XEQ). subst x'.
    unfold is_rel, is_acq, mod in *.
    change (lab_s' (mapper x)) with ((lab_s' ∘ mapper) x).
    now rewrite (rsr_lab reexec_simrel). }
  unfold extra_b. desf; [| basic_solver].
  rewrite <- (rsr_bs_rlx INV' reexec_simrel).
  rewrite set_interC, (rsr_bt reexec_simrel).
  enough (E_s' a_t) by basic_solver.
  left. exists b_t. splits; auto with xmm.
  apply (rexec_dtrmt_in_fin STEP); desf.
Qed.

Lemma rsr_sw_in_d :
  sw_s' ≡ ⦗dtrmt_s⦘ ⨾ sw_s' ⨾ ⦗dtrmt_s⦘.
Proof using SIMREL INV INV' LVAL STEP NLOC ARW ARLX RCFAT.
  apply dom_helper_3.
  assert (WF : Wf G_s').
  { apply (new_G_s_wf INV' LVAL). }
  rewrite (wf_swE WF).
  assert (DIN : dtrmt_s ⊆₁ E_s').
  { transitivity cmt_s; auto with xmm. }
  rewrite set_union_minus
     with (s := E_s') (s' := dtrmt_s)
       at 1; auto.
  rewrite id_union, seq_union_l.
  arewrite_false (⦗E_s' \₁ dtrmt_s⦘ ⨾ sw_s').
  { rewrite (wf_swD WF), rsr_rex_ndtrmt_rlx.
    clear. basic_solver. }
  rewrite seq_false_l, union_false_l.
  rewrite set_union_minus
     with (s := E_s') (s' := dtrmt_s)
       at 1; auto.
  rewrite id_union, seq_union_r.
  arewrite_false (sw_s' ⨾ ⦗E_s' \₁ dtrmt_s⦘).
  { rewrite (wf_swD WF), rsr_rex_ndtrmt_rlx.
    clear. basic_solver. }
  rewrite union_false_l. basic_solver.
Qed.

Lemma rsr_hb_in_d :
  hb_s' ⨾ ⦗dtrmt_s⦘ ⊆
    ⦗dtrmt_s⦘ ⨾ hb_s' ⨾ ⦗dtrmt_s⦘.
Proof using SIMREL INV INV' LVAL STEP NLOC ARW ARLX RCFAT.
  enough (DOM :
    dom_rel (hb_s' ⨾ ⦗dtrmt_s⦘) ⊆₁ dtrmt_s
  ).
  { unfolder. intros x y (HB & DX). splits; auto.
    apply DOM. exists y. basic_solver. }
  unfold hb.
  rewrite clos_trans_doma_r_strong,
          ct_begin; [clear; basic_solver |].
  rewrite seq_union_l, rsr_sw_in_d, sb_d_closed'.
  apply union_doma.
  all: basic_solver.
Qed.

Lemma rsr_rex_crfc_vf :
  dom_rel (vf_s' ⨾ ⦗dtrmt_s⦘ ⨾ sb_s' ⨾ ⦗A_s'⦘) ⊆₁ cmt_s.
Proof using SIMREL INV INV' LVAL STEP NLOC ARW ARLX RCFAT.
  unfold vf.
  rewrite !seqA.
  arewrite (
    ⦗dtrmt_s⦘ ⨾ sb_s' ⨾ ⦗A_s'⦘ ⊆
      ⦗dtrmt_s \₁ (eq a_t ∪₁ A_s')⦘ ⨾ sb_s' ⨾ ⦗A_s'⦘
  ).
  { admit. }
  arewrite (
    hb_s'^? ⨾ ⦗dtrmt_s \₁ (eq a_t ∪₁ A_s')⦘ ⨾ sb_s' ⨾ ⦗A_s'⦘ ⊆
      ⦗dtrmt_s \₁ (eq a_t ∪₁ A_s')⦘ ⨾ hb_s'^? ⨾ sb_s' ⨾ ⦗A_s'⦘
  ).
  { rewrite crE, !seq_union_l, !seq_union_r.
    apply union_mori; [basic_solver |].
    (* apply rsr_hb_in_d. *) admit. }
  arewrite (
    rf_s'^? ⨾ ⦗dtrmt_s \₁ (eq a_t ∪₁ A_s')⦘ ⊆
    (mapper ↑ rf_t')^? ⨾ ⦗dtrmt_s \₁ (eq a_t ∪₁ A_s')⦘
  ).
  { rewrite !crE, !seq_union_l.
    apply union_mori; [reflexivity |].
    rewrite (rsr_rf reexec_simrel), seq_union_l.
    rewrite seqA. seq_rewrite <- id_inter.
    arewrite (
      A_s' ∩₁ R_s' ∩₁
        (dtrmt_s \₁ (eq a_t ∪₁ A_s')) ⊆₁ ∅
    ); [clear; basic_solver|].
    now rewrite eqv_empty, seq_false_r, union_false_r. }
  arewrite (
    dtrmt_s \₁ (eq a_t ∪₁ A_s') ⊆₁
      mapper ↑₁ dtrmt_t
  ).
  { admit. }
  arewrite (
    (mapper ↑ rf_t')^? ⨾ ⦗mapper ↑₁ dtrmt_t⦘ ⊆
      ⦗cmt_s⦘ ⨾ (mapper ↑ rf_t')^?
  ).
  { rewrite crE, !seq_union_l, !seq_union_r.
    apply union_mori.
    { rewrite seq_id_l, <- id_inter. apply eqv_rel_mori.
      apply set_subset_inter_r. split; auto with hahn.
      rewrite (WCore.dtrmt_cmt STEP).
      unfold cmt_s. basic_solver. }
    admit. }
  clear. basic_solver.
Admitted.

Lemma rsr_rex_crfc_helper
    (DB : dtrmt_t b_t)
    (NINA : ~E_t' a_t) :
  R_s' ∩₁ eq a_s ⊆₁
    codom_rel (
      restr_rel cmt_s (srf_s' ⨾ ⦗A_s' ∩₁ R_s'⦘)
    ).
Proof using INV INV' LVAL STEP NLOC ARW ARLX RCFAT.
  assert (WF : Wf G_s').
  { apply (new_G_s_wf INV' LVAL). }
  assert (BIN : E_t' b_t).
  { now apply (rexec_dtrmt_in_fin STEP). }
  assert (BCMT : cmt_s b_t).
  { unfold cmt_s. right. unfold exa_d; desf.
    tauto. }
  rewrite extra_a_some; auto. unfold a_s.
  unfolder. intros x (ISR & XEQ). subst x.
  assert (HLOC : exists l, loc_s' b_t = Some l).
  { unfold is_r in ISR. unfold loc. desf.
    eauto. }
  destruct HLOC as (l & HLOC).
  destruct srf_exists
      with (G := G_s') (r := b_t) (l := l)
        as (w & SRF).
  all: auto.
  { right. now apply extra_a_some. }
  { apply INV'. }
  { now apply (rsr_init_acts_s INV' reexec_simrel). }
  all: try now apply WF.
  { apply (rsr_fin_s INV' reexec_simrel). }
  exists w. splits; auto.
  destruct SRF as ((r & ((VFSB & _) & ISR')) & _).
  red in ISR'. destruct ISR' as (REQ & _). subst r.
  destruct VFSB as (e & VF & SB).
  assert (ED : dtrmt_s e).
  { admit. }
  apply rsr_rex_crfc_vf, set_subset_single_l.
  rewrite extra_a_some; auto. basic_solver 11.
Admitted.

Lemma rsr_rex_crfc :
  rf_complete (restrict G_s' cmt_s).
Proof using INV INV' LVAL STEP NLOC ARW ARLX RCFAT.
  assert (NEQ : a_t <> b_t) by apply INV'.
  assert (RFCT : rf_complete (restrict G_t' cmt_t)) by apply STEP.
  unfold rf_complete.
  arewrite (rf (restrict G_s' cmt_s) ≡ restr_rel cmt_s rf_s').
  { simpl. now rewrite restr_relE. }
  arewrite (acts_set (restrict G_s' cmt_s) ≡₁ cmt_s).
  { simpl. rewrite set_inter_absorb_r; auto with hahn xmm. }
  rewrite set_interC, set_inter_is_r with (G := G_s') (s' := E_s').
  all: auto with xmm; try reflexivity.
  unfold cmt_s at 1. rewrite set_inter_union_r.
  rewrite set_collect_is_r
     with (s := cmt_t) (G := G_t')
        ; [
          | apply STEP
          | symmetry; apply reexec_simrel].
  arewrite (R_t' ∩₁ cmt_t ⊆₁ codom_rel (restr_rel cmt_t rf_t')).
  { rewrite restr_relE.
    change (⦗cmt_t⦘ ⨾ rf_t' ⨾ ⦗cmt_t⦘) with (rf (restrict G_t' cmt_t)).
    unfold rf_complete in RFCT. rewrite <- RFCT.
    ins. rewrite set_inter_absorb_r with (s' := E_t').
    { clear. basic_solver. }
    apply STEP. }
  rewrite (rsr_rf reexec_simrel).
  rewrite restr_union, codom_union.
  apply set_subset_union.
  { unfold cmt_s.
    transitivity (
      codom_rel (
        restr_rel (mapper ↑₁ cmt_t) (mapper ↑ rf_t')
      )
    ); [| apply codom_rel_mori; clear; basic_solver 11].
    rewrite collect_rel_restr
      ; [| eapply inj_dom_mori; auto with xmm].
    all: unfold flip; auto with hahn.
    now rewrite set_collect_codom. }
  unfold exa_d. desf; [| basic_solver].
  apply rsr_rex_crfc_helper; desf.
Qed.

Lemma reexec_fixset_helper :
  fixset
    (mapper ↑₁ (dtrmt_t \₁ extra_b) ∪₁ extra_d)
    (mapper ∘ f_t ∘ mapper).
Proof using INV INV' LVAL STEP NLOC ARW ARLX RCFBT RCFAT SIMREL.
  assert (NEQ : a_t <> b_t) by apply INV.
  apply fixset_union; split.
  { rewrite Combinators.compose_assoc.
    apply fixset_swap.
    rewrite Combinators.compose_assoc,
            rsr_mapper_compose,
            Combinators.compose_id_right.
    all: auto.
    eapply fixset_mori; auto; try now apply STEP.
    clear. red. basic_solver. }
  unfold extra_d. desf. unfold a_s.
  unfolder. unfold compose. ins. desf.
  rewrite (rsr_mapper_bt NEQ).
  rewrite RCFAT; auto with xmm.
Qed.

Lemma reexec_step :
  WCore.reexec X_s X_s' f_s dtrmt_s cmt_s.
Proof using INV INV' LVAL STEP NLOC ARW ARLX RCFAT SIMREL RCFBT CONS.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  assert (MEQA : mapper a_t = b_t).
  { now apply rsr_mapper_at. }
  assert (INJHELPER : inj_dom (codom_rel (⦗E_t' \₁ dtrmt_t⦘ ⨾ rf_t') ∪₁ dom_rel rhb_t'^?) mapper).
  { eapply inj_dom_mori; eauto with xmm.
    red. auto with hahn. }
  assert (SURG :
    WCore.stable_uncmt_reads_gen X_s' cmt_s thrdle
  ).
  { constructor; try now apply STEP.
    apply rsr_rex_vf. }
  assert (WF_START :
    WCore.wf (WCore.X_start X_s dtrmt_s) X_s' cmt_s
  ).
  { constructor; ins.
    { apply sub_WF with (G := G_s) (sc := ∅₂) (sc' := ∅₂).
      { ins. now rewrite <- rex_dtrmt_init. }
      { apply (G_s_wf INV SIMREL). }
      apply restrict_sub; [basic_solver |].
      auto with xmm. }
    { ins. rewrite set_interA, set_inter_absorb_r.
      { apply rsr_rex_restr_eq. }
      apply set_subset_inter_r. split; auto with xmm. }
    { apply rsr_rex_crfc. }
    rewrite <- dtrmt_in_cmt.
    clear. basic_solver. }
  (**)
  red. exists thrdle.
  constructor; auto with xmm.
  { unfold f_s, dtrmt_s. apply fixset_union; split.
    { apply fixset_eq_dom
       with (f := mapper ∘ f_t ∘ mapper)
          ; [| apply reexec_fixset_helper].
      desf. apply eq_dom_upd_r; [| reflexivity].
      intros [MAPD | EXD].
      { enough (E_t' a_t) by desf.
        assert (BIN : (mapper ↑₁ E_t') b_t).
        { apply set_subset_single_l.
          rewrite <- (rexec_dtrmt_in_fin STEP).
          forward apply MAPD. clear. basic_solver. }
        destruct BIN as (y & YIN & YEQ).
        enough (y = a_t) by congruence.
        eapply rsr_mapper_inv_bt; eauto. }
      unfold extra_d, a_s in EXD; desf.
      enough (E_t' a_t) by desf.
      apply (WCore.reexec_embd_dom STEP). desf. }
    unfold exa_d, a_s; desf.
    { unfolder. ins. desf. now rewrite upds. }
    exfalso. assert (BNIN : ~E_t' b_t) by tauto.
    enough (E_t' b_t) by desf.
    now apply (rexec_dtrmt_in_fin STEP). }
  { apply sb_d_closed. }
  { eapply imm_sb_d_s; eauto. }
  { apply rsr_rex_ndtrmt_rlx. }
  { apply rsr_rex_embd. }
  { apply (G_s_rfc INV' reexec_simrel). }
  { apply (rsr_cons INV' CONS reexec_simrel). }
  { eapply reexec_acts_s; eauto. }
  apply sub_to_full_exec_listless
   with (thrdle := thrdle).
  all: auto with xmm.
  { eapply G_s_rfc with (X_t := X_t').
    { apply INV'. }
    now apply reexec_simrel. }
  { apply (rsr_cons INV' CONS reexec_simrel). }
  { ins. change (mapper ↑₁ E_t' ∪₁ A_s') with E_s'.
    arewrite (E_s' \₁ dtrmt_s ∩₁ E_s ⊆₁ E_s' \₁ dtrmt_s).
    { rewrite set_inter_absorb_r; auto with xmm hahn. }
    rewrite <- rex_dtrmt_init. apply (rsr_fin_s INV' reexec_simrel). }
  { apply rex_pfx. }
  { eapply G_s_wf with (X_t := X_t').
    { apply INV'. }
    now apply reexec_simrel. }
  { ins. change (mapper ↑₁ E_t' ∪₁ A_s') with E_s'.
    arewrite (E_s' \₁ dtrmt_s ∩₁ E_s ⊆₁ E_s' \₁ dtrmt_s).
    { rewrite set_inter_absorb_r; auto with xmm hahn. }
    rewrite <- rex_dtrmt_init, set_minusE.
    rewrite <- (rsr_ninit_acts_s INV' reexec_simrel).
    clear. basic_solver. }
  { now rewrite (rsr_ndata INV'). }
  { now rewrite (rsr_naddr INV'). }
  { now rewrite (rsr_nctrl INV'). }
  now rewrite (rsr_nrmw_dep INV').
Qed.

End ReorderingReexec.