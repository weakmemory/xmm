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
Notation "'srf_s'''" := (srf G_s'').
Notation "'rhb_s'''" := (rhb G_s'').
Notation "'Loc_s_''' l" := (fun e => loc_s'' e = l) (at level 1).
Notation "'Val_s_''' l" := (fun e => val_s'' e = l) (at level 1).
Notation "'Rlx_s'''" := (fun e => is_true (is_rlx lab_s'' e)).
Notation "'Acq_s'''" := (fun e => is_true (is_acq lab_s'' e)).
Notation "'Rel_s'''" := (fun e => is_true (is_rel lab_s'' e)).
Notation "'drf_s'''" := (fake_srf G_s'' b_t l_a ⨾ ⦗A_s' ∩₁ WCore.lab_is_r l_a⦘).

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
Notation "'srf_s''" := (srf G_s').
Notation "'rhb_s''" := (rhb G_s').
Notation "'Loc_s_'' l" := (fun e => loc_s' e = l) (at level 1).
Notation "'Val_s_'' l" := (fun e => val_s' e = l) (at level 1).
Notation "'Rlx_s''" := (fun e => is_true (is_rlx lab_s' e)).
Notation "'Acq_s''" := (fun e => is_true (is_acq lab_s' e)).
Notation "'Rel_s''" := (fun e => is_true (is_rel lab_s' e)).

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

Definition extra_b :=
  ifP ~dtrmt_t a_t /\ dtrmt_t b_t then eq b_t
  else ∅.
Definition extra_d :=
  ifP
    ~cmt_t b_t /\
    cmt_t a_t /\
    ~dtrmt_t a_t /\
    dom_rel (immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘) ⊆₁ dtrmt_t
  then eq a_s
  else ∅.
Definition cmt' := mapper ↑₁ cmt_t.
Definition dtrmt' := mapper ↑₁ (dtrmt_t \₁ extra_b) ∪₁ extra_d.
Definition f' := (mapper ∘ f_t) ∘ mapper.

Lemma extra_d_in_E_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  extra_d ⊆₁ E_s.
Proof using INV SIMREL RCFAT.
  clear - GREEXEC INV SIMREL RCFAT.
  unfold extra_d. desf.
  transitivity (mapper ↑₁ E_t);
    [| rewrite (rsr_acts SIMREL); basic_solver].
  rewrite <- (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
  assert (INA : E_t' a_t).
  { now apply (WCore.reexec_embd_dom GREEXEC). }
  assert (NEQ : a_t <> b_t) by apply INV.
  arewrite (
    eq a_s ≡₁ mapper ↑₁ (f_t ↑₁ eq a_t)
  ).
  { rewrite set_collect_eq, RCFAT; [| desf].
    rewrite set_collect_eq, rsr_mapper_at; auto. }
  do 2 (apply set_collect_mori; auto).
  basic_solver.
Qed.

Lemma dtrmt_in_E_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  dtrmt' ⊆₁ E_s.
Proof using INV SIMREL RCFAT.
  unfold dtrmt'.
  arewrite (dtrmt_t \₁ extra_b ⊆₁ dtrmt_t).
  { basic_solver. }
  rewrite extra_d_in_E_s, (rexec_dtrmt_in_start GREEXEC); eauto.
  apply set_subset_union_l; split; [| reflexivity].
  rewrite (rsr_acts SIMREL); basic_solver.
Qed.

Lemma extra_d_cmt : extra_d ⊆₁ cmt'.
Proof using INV.
  unfold extra_d, cmt', a_s. desf.
  unfolder. intros x XEQ. subst x.
  exists a_t. split; [desf |].
  apply rsr_mapper_at, INV.
Qed.

Lemma reexec_threads_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  WCore.reexec_thread X_s' dtrmt' ≡₁
    WCore.reexec_thread X_t' dtrmt_t ∪₁ tid ↑₁ A_s'.
Proof using INV' INV.
  clear - INV' INV GREEXEC.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  unfold WCore.reexec_thread, dtrmt'.
  arewrite (E_s' ≡₁ mapper ↑₁ E_t' ∪₁ A_s').
  rewrite set_minus_union_l, set_collect_union.
  arewrite (
    A_s' \₁ (mapper ↑₁ (dtrmt_t \₁ extra_b) ∪₁ extra_d) ≡₁ A_s'
  ).
  { unfold extra_a; desf; [| basic_solver].
    split; [clear; basic_solver |].
    unfolder. intros x XEQ. subst. split; auto.
    unfold extra_b, extra_d; intro FALSO; do 2 desf.
    all: enough (E_t' a_t) by eauto.
    all: try now apply (WCore.reexec_embd_dom GREEXEC).
    all: eapply rexec_dtrmt_in_fin; eauto.
    all: erewrite <- (rsr_mapper_inv_bt y); eauto. }
  unfold extra_d; desf.
  { assert (INA : E_t' a_t).
    { apply (WCore.reexec_embd_dom GREEXEC). desf. }
    assert (INB : E_t' b_t).
    { now apply (rsr_at_bt_ord INV'). }
    rewrite rsr_setE_iff; eauto.
    assert (ND : ~dtrmt_t b_t).
    { intro FALSO. enough (cmt_t b_t) by desf.
      now apply (WCore.dtrmt_cmt GREEXEC). }
    unfold extra_b; desf; [exfalso; tauto |].
    arewrite (dtrmt_t \₁ ∅ ≡₁ dtrmt_t) by basic_solver.
    rewrite rsr_setE_iff; eauto.
    unfold a_s.
    apply set_union_more; [apply tid_map_replace | reflexivity].
    { clear. basic_solver 11. }
    rewrite set_minus_union_r.
    unfolder. intros x (XIN & NDX).
    exists (ifP x = b_t then a_t else x).
    desf; auto. }
  rewrite set_union_empty_r.
  unfold extra_b; desf.
  { assert (INB : E_t' b_t).
    { eapply rexec_dtrmt_in_fin; eauto. desf. }
    destruct classic with (E_t' a_t) as [INA|NINA].
    { apply set_union_more; [| reflexivity].
      rewrite rsr_setE_iff; desf; eauto.
      rewrite rsr_setE_iff; eauto;
        [| desf; unfolder; tauto].
      rewrite set_minus_minus_r, set_collect_union.
      split; [| auto with hahn].
      apply set_subset_union_l; split; auto.
      transitivity (eq (tid a_t)); basic_solver. }
    rewrite <- set_collect_minus;
      [| eapply inj_dom_mori; eauto with xmm; red; auto with hahn].
    rewrite set_minus_minus_r, !set_collect_union.
    arewrite (tid ↑₁ (mapper ↑₁ (E_t' ∩₁ eq b_t)) ≡₁ tid ↑₁ A_s').
    { rewrite extra_a_some by auto.
      rewrite set_inter_absorb_l by (clear - INB; basic_solver).
      rewrite set_collect_eq, rsr_mapper_bt; eauto.
      clear - TEQ. basic_solver. }
    rewrite rsr_setE_iff; eauto.
    { clear. basic_solver 11. }
    right. unfolder; tauto. }
  arewrite (dtrmt_t \₁ ∅ ≡₁ dtrmt_t) by basic_solver.
  rewrite <- set_collect_minus;
    [| eapply inj_dom_mori; eauto with xmm; red; auto with hahn].
  rewrite <- set_collect_compose.
  rewrite set_collect_eq_dom with (g := tid); [reflexivity |].
  eapply eq_dom_mori; eauto with xmm.
  red; auto with hahn.
Qed.

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
  E_s ≡₁ dtrmt' ∪₁ E_s ∩₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt'.
Proof using INV INV' SIMREL RCFAT.
  clear - INV INV' GREEXEC SIMREL RCFAT.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TID : tid a_t = tid b_t) by apply INV.
  enough (SUB : E_s \₁ dtrmt' ⊆₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt').
  { split; [|
      rewrite (dtrmt_in_E_s GREEXEC) at 1;
        basic_solver].
    rewrite set_union_minus
       with (s := E_s) (s' := dtrmt')
         at 1
         by eauto using dtrmt_in_E_s.
    rewrite <- SUB. basic_solver. }
  arewrite (E_s \₁ dtrmt' ⊆₁ E_s \₁ mapper ↑₁ (dtrmt_t \₁ extra_b)).
  { unfold dtrmt'. basic_solver. }
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
  extra_a X_t' a_t b_t b_t ⊆₁ set_compl cmt'.
Proof using INV.
  clear - INV GREEXEC.
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold extra_a, cmt'. desf.
  unfolder. ins. desf.
  intros (y & CMT & MAP).
  assert (YIN : E_t' y).
  { now apply (WCore.reexec_embd_dom GREEXEC). }
  enough (E_t' a_t) by desf.
  erewrite <- (rsr_mapper_inv_bt _ NEQ); eauto.
Qed.

Lemma dtrmt_in_cmt
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  dtrmt' ⊆₁ cmt'.
Proof using INV.
  unfold dtrmt'.
  rewrite extra_d_cmt; eauto.
  apply set_subset_union_l. split; auto with hahn.
  unfold cmt'.
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
  ⦗dtrmt'⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗cmt'⦘ ⊆
    ⦗dtrmt'⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗dtrmt'⦘.
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
  arewrite (dtrmt' ∩₁ extra_a X_t' a_t b_t b_t ≡₁ ∅).
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
    unfold cmt', dtrmt', extra_d, extra_b; desf; desf.
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
    unfold dtrmt', cmt', extra_b; desf; desf.
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
    unfold dtrmt', cmt', extra_b, extra_d.
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
  { unfold dtrmt', cmt', extra_b, extra_d.
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
  unfold dtrmt', cmt', extra_b, extra_d.
  desf; desf.
  rewrite set_union_empty_r.
  arewrite (dtrmt_t \₁ ∅ ≡₁ dtrmt_t) by basic_solver.
  do 2 (rewrite rsr_setE_iff; eauto).
  apply (WCore.dtrmt_sb_max GREEXEC).
Qed.

Hypothesis GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle.

Lemma reexec_step :
  WCore.reexec X_s X_s' f' dtrmt' cmt'.
Proof using INV INV' LVAL NLOC ARW ARLX RCFAT.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  assert (MEQA : mapper a_t = b_t).
  { now apply rsr_mapper_at. }
  assert (INJHELPER : inj_dom (codom_rel (⦗E_t' \₁ dtrmt_t⦘ ⨾ rf_t') ∪₁ dom_rel rhb_t'^?) mapper).
  { eapply inj_dom_mori; eauto with xmm.
    red. auto with hahn. }
  assert (EXNCMT : A_s' ∩₁ cmt' ≡₁ ∅).
  { split; vauto.
    rewrite (reexec_extra_a_ncmt GREEXEC).
    clear. basic_solver. }
  assert (SURG :
    WCore.stable_uncmt_reads_gen X_s' cmt' thrdle
  ).
  { constructor; try now apply GREEXEC.
    admit. }
  assert (WF_START :
    WCore.wf (WCore.X_start X_s dtrmt') X_s' cmt'
  ).
  { admit. (* TODO *) }
  (**)
  red. exists thrdle.
  constructor.
  { admit. }
  { eapply dtrmt_in_cmt; eauto. }
  { unfold f', dtrmt'.
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
  { unfold cmt'.
    admit. }
  { exact SURG. }
  { admit. (* sb-clos *) }
  { eapply imm_sb_d_s; eauto. }
  { admit. (* rpo edges *) }
  { constructor.
    { intros x' y'; unfold cmt', f'.
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
      change (tid (f' e)) with ((tid ∘ f') e).
      unfold f'.
      rewrite <- !Combinators.compose_assoc.
      change ((tid ∘ mapper ∘ f_t ∘ mapper) e)
        with ((tid ∘ mapper) ((f_t ∘ mapper) e)).
      unfold cmt' in CMT. unfolder in CMT.
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
      change (lab_s (f' e)) with ((lab_s ∘ f') e).
      unfold f'.
      rewrite <- !Combinators.compose_assoc.
      unfold cmt' in CMT. unfolder in CMT.
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
      arewrite_false (restr_rel cmt'
        (srf_s' ⨾ ⦗extra_a X_t' a_t b_t b_t ∩₁ R_s'⦘)).
      { rewrite restr_relE, !seqA, <- id_inter.
        rewrite (reexec_extra_a_ncmt GREEXEC).
        clear. basic_solver. }
      rewrite collect_rel_empty, union_false_r.
      unfold cmt', f'.
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
      arewrite_false (restr_rel cmt'
        (add_max (extra_co_D E_s' lab_s' (loc_s' b_t))
          (extra_a X_t' a_t b_t b_t ∩₁ W_s'))).
      { rewrite restr_add_max. unfold add_max.
        rewrite (reexec_extra_a_ncmt GREEXEC) at 2.
        clear. basic_solver. }
      rewrite collect_rel_empty, union_false_r.
      unfold cmt', f'.
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
      unfold cmt', f'.
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
    unfold cmt', f'.
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