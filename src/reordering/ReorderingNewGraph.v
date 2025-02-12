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

Section ReordGraph.

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

Notation "'mapper'" := (mapper a_t b_t).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'A_s'" := (extra_a X_t a_t b_t b_t).
Notation "'B_s''" := (extra_a X_t a_t b_t a_t).

Definition rsr_imm_g : execution := {|
  acts_set := mapper ↑₁ E_t;
  threads_set := threads_set G_t;
  lab := lab_t ∘ mapper;
  rf := mapper ↑ rf_t;
  co := mapper ↑ co_t;
  rmw := mapper ↑ rmw_t;
  rmw_dep := rmw_dep_t;
  ctrl := ctrl_t;
  data := data_t;
  addr := addr_t;
|}.
Definition rsr_immx := {|
  WCore.sc := WCore.sc X_t;
  WCore.G := rsr_imm_g;
|}.

Notation "'X_s'''" := rsr_immx.
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

Definition lab_s_ :=
  (ifP ~E_t a_t /\ E_t b_t then upd lab_t a_t l_a
  else lab_t) ∘ mapper.

Definition rsr_Gs : execution := {|
  acts_set := mapper ↑₁ E_t ∪₁ A_s;
  threads_set := threads_set G_t;
  lab := lab_s_;
  rf := mapper ↑ rf_t ∪ drf_s'';
  co := mapper ↑ co_t ∪
          (E_s'' ∩₁ W_s'' ∩₁ Loc_s_'' (WCore.lab_loc l_a)) ×
          (A_s ∩₁ WCore.lab_is_w l_a);
  rmw := mapper ↑ rmw_t;
  rmw_dep := rmw_dep_t;
  ctrl := ctrl_t;
  data := data_t;
  addr := addr_t;
|}.
Definition rsr_Xs := {|
  WCore.sc := WCore.sc X_t;
  WCore.G := rsr_Gs;
|}.

Notation "'X_s'" := rsr_Xs.
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

Hint Resolve rsr_at_neq_bt : xmm.

Lemma rsr_rex_anin_imm
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  ~ E_s'' b_t.
Proof using INV.
  unfolder. intros (y & YIN & YEQ).
  enough (y = a_t) by desf.
  eapply rsr_mapper_inv_bt; eauto with xmm.
Qed.

Lemma rsr_exa_notin_imm :
  A_s ⊆₁ set_compl E_s''.
Proof using INV.
  unfold extra_a; desf. simpl.
  unfolder. intros x XEQ. subst x.
  intro FALSO. desf.
  enough (y = a_t) by desf.
  eapply rsr_mapper_inv_bt; eauto with xmm.
Qed.

Lemma rsr_rex : eq_dom E_t (lab_s ∘ mapper) lab_t.
Proof using INV.
  simpl. unfold lab_s_.
  rewrite Combinators.compose_assoc, rsr_mapper_compose,
          Combinators.compose_id_right; eauto with xmm.
  desf. now apply eq_dom_upd_l.
Qed.

Lemma rsr_imm_Gs_rmw : rmw_s'' ⊆ immediate sb_s''.
Proof using INV.
  assert (WF_t : Wf G_t) by apply INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. unfolder.
  intros x' y' (x & y & RMW & XEQ & YEQ).
  apply (wf_rmwE WF_t) in RMW.
  unfolder in RMW.
  destruct RMW as (XIN & RMW & YIN).
  subst x' y'. unfold sb. simpl.
  assert (XNB : x <> b_t).
  { intro FALSO. subst x.
    apply (rsr_nrmw INV) in RMW.
    unfolder in RMW. desf. }
  assert (XNA : x <> a_t).
  { intro FALSO. subst x.
    apply (rsr_nrmw INV) in RMW.
    unfolder in RMW. desf. }
  assert (YNB : y <> b_t).
  { intro FALSO. subst y.
    apply (rsr_nrmw INV) in RMW.
    unfolder in RMW. desf. }
  assert (YNA : y <> a_t).
  { intro FALSO. subst y.
    apply (rsr_nrmw INV) in RMW.
    unfolder in RMW. desf. }
  assert (XNIN : ~is_init x).
  { apply (rmw_from_non_init WF_t) in RMW.
    forward apply RMW. basic_solver. }
  assert (ANINI : ~is_init a_t) by apply INV.
  assert (BNINI : ~is_init b_t) by apply INV.
  apply (wf_rmwi WF_t) in RMW.
  split.
  { unfolder. splits; eauto.
    rewrite !rsr_mappero by congruence.
    assert (SB : sb_t x y) by apply RMW.
    forward apply SB. unfold sb. basic_solver. }
  intros c' XC CY. unfolder in XC. unfolder in CY.
  destruct XC as (_ & XC & CIN).
  destruct CY as (_ & CY & _).
  destruct CIN as (c & CIN & CEQ). subst c'.
  rewrite rsr_mappero with (x := x) in XC; auto.
  rewrite rsr_mappero with (x := y) in CY; auto.
  assert (ABSB : ext_sb b_t a_t) by apply INV.
  destruct classic with (c = b_t) as [EQ|CNB].
  { subst c. rewrite rsr_mapper_bt in *; auto.
    apply RMW with b_t
      ; [| unfold sb; unfolder; splits; eauto using ext_sb_trans].
    destruct classic with (~E_t a_t) as [NINA | INA'].
    { exfalso. apply (rsr_nat_spot INV) with a_t y; auto.
      basic_solver. }
    assert (INA : E_t a_t) by tauto. clear INA'.
    exfalso. apply RMW with a_t.
    all: unfold sb; basic_solver. }
  destruct classic with (c = a_t) as [EQ|CNA].
  { subst c. rewrite rsr_mapper_at in *; auto.
    assert (INB : E_t b_t) by now apply (rsr_at_bt_ord INV).
    apply RMW with b_t.
    all: unfold sb; basic_solver. }
  rewrite rsr_mappero in *; auto.
  apply RMW with c.
  all: unfold sb; basic_solver.
Qed.

Lemma rsr_imm_G_s_wf_idx :
  E_s'' ∩₁ Tid_ tid_init ⊆₁ is_init.
Proof using INV.
  simpl.
  unfolder. intros x' ((x & XIN & XEQ) & TEQ).
  subst x'.
  rewrite rsr_mapper_tid' in TEQ by apply INV.
  rewrite rsr_mapper_init; try now apply INV.
Qed.

Lemma rsr_imm_Gs_wf : Wf G_s''.
Proof using INV.
  assert (ANINI : ~is_init a_t) by apply INV.
  assert (BNINI : ~is_init b_t) by apply INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  assert (WF_t : Wf G_t) by apply INV.
  constructor.
  { intros x y (XIN & YIN & XNY & XYT & NINA).
    assert (YINIT : ~ is_init y).
    { intro FALSO. apply NINA, rsr_imm_G_s_wf_idx.
      split; auto. destruct y; ins. }
    destruct x, y; ins. congruence. }
  all: ins.
  all: rewrite ?(rsr_ndata INV), ?(rsr_naddr INV),
               ?(rsr_nctrl INV), ?(rsr_nrmw_dep INV).
  all: try now rewrite ?seq_false_l, ?seq_false_r.
  all: try apply dom_helper_3.
  { rewrite (wf_rmwD WF_t).
    unfolder. ins. desf. unfold compose, is_r, is_w.
    now rewrite !(rsr_mapper_self_inv _ NEQ). }
  { rewrite (wf_rmwl WF_t).
    unfolder. ins. desf. unfold compose, same_loc, loc.
    now rewrite !(rsr_mapper_self_inv _ NEQ). }
  { apply rsr_imm_Gs_rmw. }
  { rewrite (wf_rfE WF_t), <- collect_rel_cross.
    apply collect_rel_mori; basic_solver. }
  { rewrite (wf_rfD WF_t).
    unfolder. ins. desf. unfold compose, is_r, is_w.
    now rewrite !(rsr_mapper_self_inv _ NEQ). }
  { rewrite (wf_rfl WF_t).
    unfolder. ins. desf. unfold compose, same_loc, loc.
    now rewrite !(rsr_mapper_self_inv _ NEQ). }
  { enough (VV : mapper ↑ rf_t ⊆ same_val (lab_t ∘ mapper)).
    { apply VV. }
    arewrite (mapper ↑ rf_t ⊆ mapper ↑ (same_val lab_t)).
    { apply collect_rel_mori; auto. apply WF_t. }
    unfolder. ins. desf. unfold compose, same_val, val.
    now rewrite !(rsr_mapper_self_inv _ NEQ). }
  { rewrite <- collect_rel_transp.
    arewrite (mapper ↑ rf_t⁻¹ ≡ mapper ↑ (restr_rel ⊤₁ (rf_t⁻¹))).
    { basic_solver 11. }
    apply functional_collect_rel_inj; auto with xmm.
    arewrite (restr_rel ⊤₁ rf_t⁻¹ ≡ rf_t⁻¹).
    { basic_solver. }
    apply WF_t. }
  { rewrite (wf_coE WF_t), <- collect_rel_cross.
    apply collect_rel_mori; basic_solver. }
  { rewrite (wf_coD WF_t).
    unfolder. ins. desf. unfold compose, is_w.
    now rewrite !(rsr_mapper_self_inv _ NEQ). }
  { rewrite (wf_col WF_t).
    unfolder. ins. desf. unfold compose, same_loc, loc.
    now rewrite !(rsr_mapper_self_inv _ NEQ). }
  { arewrite (mapper ↑ co_t ≡ mapper ↑ (restr_rel ⊤₁ co_t)).
    { basic_solver 11. }
    apply transitive_collect_rel_inj; auto with xmm.
    arewrite (restr_rel ⊤₁ co_t ≡ co_t).
    { basic_solver. }
    apply WF_t. }
  { arewrite (
      E_s'' ∩₁ W_s'' ∩₁ Loc_s_'' ol ⊆₁
        mapper ↑₁ (E_t ∩₁ W_t ∩₁ Loc_t_ ol)
    ).
    { simpl. unfolder. ins. desf.
      eexists; splits; eauto.
      all: unfold is_w, loc, compose in *.
      all: now rewrite (rsr_mapper_self_inv _ NEQ) in *. }
    apply total_collect_rel, WF_t. }
  { arewrite (mapper ↑ co_t ≡ mapper ↑ (restr_rel ⊤₁ co_t)).
    { basic_solver 11. }
    apply collect_rel_irr_inj; auto with xmm.
    arewrite (restr_rel ⊤₁ co_t ≡ co_t).
    { basic_solver. }
    apply WF_t. }
  { exists (InitEvent l).
    rewrite rsr_mapper_init; auto. split; auto.
    apply (wf_init WF_t). unfolder in *.
    desf. eexists; split; eauto.
    unfold compose, loc in *.
    now rewrite (rsr_mapper_self_inv _ NEQ) in *. }
  { unfold compose.
    rewrite rsr_mapper_init; auto.
    apply WF_t. }
  unfolder in EE. desf.
  rewrite rsr_mapper_tid'; auto.
  now apply (wf_threads WF_t).
Qed.

Lemma rsr_rexi : eq_dom E_s'' lab_s'' lab_s.
Proof using INV.
  simpl. unfold lab_s_.
  apply eq_dom_compose; [reflexivity |].
  rewrite <- set_collect_compose, rsr_mapper_compose,
          set_collect_id; eauto with xmm.
  desf. now apply eq_dom_upd_r.
Qed.

Hint Resolve rsr_rex rsr_rexi rsr_rex_anin_imm : xmm.

Lemma rsr_rex_isr_helper
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  eq b_t ∩₁ R_s ≡₁ eq b_t ∩₁ WCore.lab_is_r l_a.
Proof using INV.
  simpl. unfold lab_s_; desf; [| tauto].
  simpl. unfold is_r, WCore.lab_is_r, compose.
  unfolder. split.
  all: intros x (XEQ & ISR); subst x.
  all: rewrite rsr_mapper_bt, upds in *; desf.
  all: eauto with xmm.
Qed.

Lemma rsr_rex_isw_helper
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  eq b_t ∩₁ W_s ≡₁ eq b_t ∩₁ WCore.lab_is_w l_a.
Proof using INV.
  simpl. unfold lab_s_; desf; [| tauto].
  simpl. unfold is_w, WCore.lab_is_w, compose.
  unfolder. split.
  all: intros x (XEQ & ISR); subst x.
  all: rewrite rsr_mapper_bt, upds in *; desf.
  all: eauto with xmm.
Qed.

Lemma rsr_rex_labloc_helper
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  loc_s b_t = WCore.lab_loc l_a.
Proof using INV.
  simpl. unfold lab_s_; desf; [| tauto].
  unfold loc, WCore.lab_loc, compose.
  now rewrite rsr_mapper_bt, upds; eauto with xmm.
Qed.

Lemma rsr_rex_labval_helper
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  val_s b_t = WCore.lab_val l_a.
Proof using INV.
  simpl. unfold lab_s_; desf; [| tauto].
  unfold val, WCore.lab_val, compose.
  now rewrite rsr_mapper_bt, upds; eauto with xmm.
Qed.

Lemma rsr_trans_co : transitive co_s.
Proof using INV.
  assert (WF_s : Wf G_s'').
  { apply rsr_imm_Gs_wf. }
  apply expand_transitive.
  { apply WF_s. }
  { apply (co_upward_closed WF_s). }
  rewrite (wf_coE WF_s), dom_seq, dom_eqv.
  rewrite rsr_exa_notin_imm. basic_solver.
Qed.

Lemma rsr_extra_a_co ol
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  eq b_t ∩₁ W_s ∩₁ Loc_s_ ol ⊆₁
    eq b_t ∩₁ WCore.lab_is_w l_a ∩₁
      (fun _ => WCore.lab_loc l_a = ol).
Proof using INV.
  simpl. unfold lab_s_. desf; [| tauto].
  unfolder. intros x ((ISW & XEQ) & HLOC). subst x.
  unfold WCore.lab_loc, WCore.lab_is_w.
  unfold loc, is_w, lab_s_, compose in *.
  rewrite rsr_mapper_bt, upds in *; desf.
  all: eauto with xmm.
Qed.

Lemma rsr_extra_a_coE' ol :
  E_s'' ∩₁ W_s ∩₁ Loc_s_ ol ⊆₁
    E_s'' ∩₁ W_s'' ∩₁ Loc_s_'' ol.
Proof using INV.
  unfolder.
  unfold is_w, loc. intros x ((XIN & ISW) & LOC).
  splits; auto; rewrite rsr_rexi; auto.
Qed.

Lemma rsr_extra_a_coE ol :
  E_s ∩₁ W_s ∩₁ Loc_s_ ol ⊆₁
    E_s'' ∩₁ W_s'' ∩₁ Loc_s_'' ol ∪₁
    eq b_t ∩₁ WCore.lab_is_w l_a ∩₁
      (fun _ => WCore.lab_loc l_a = ol).
Proof using INV.
  arewrite (E_s ≡₁ E_s'' ∪₁ A_s).
  rewrite !set_inter_union_l.
  rewrite rsr_extra_a_coE'.
  apply set_subset_union; [reflexivity |].
  unfold extra_a; desf; [| basic_solver].
  apply rsr_extra_a_co; desf.
Qed.

Lemma rsr_total_co ol :
  is_total (E_s ∩₁ W_s ∩₁ Loc_s_ ol) co_s.
Proof using INV.
  assert (WF_s : Wf G_s'').
  { apply rsr_imm_Gs_wf. }
  destruct classic
      with (~ (~E_t a_t /\ E_t b_t))
        as [EMP|NEMP'].
  { simpl. unfold lab_s_; desf.
    rewrite extra_a_none, set_union_empty_r by auto.
    rewrite set_inter_empty_l, cross_false_r, union_false_r.
    apply WF_s. }
  assert (NEMP : ~ E_t a_t /\ E_t b_t) by tauto.
  desf.
  assert (NIN : ~ E_s'' b_t) by auto with xmm.
  rewrite rsr_extra_a_coE.
  destruct classic
      with (WCore.lab_loc l_a = ol)
        as [EQL | NEQL].
  { eapply is_total_mori,
          is_total_union_ext with (a := b_t)
                                  (s' := eq b_t ∩₁ WCore.lab_is_w l_a).
    all: try now apply (@wf_co_total _ WF_s ol).
    { unfold flip. basic_solver. }
    { subst ol. apply union_mori; [reflexivity |].
      rewrite extra_a_some; auto with hahn. }
    all: unfold not; basic_solver. }
  arewrite ((fun _ : actid => WCore.lab_loc l_a = ol) ≡₁ ∅).
  { basic_solver. }
  rewrite !set_inter_empty_r, set_union_empty_r.
  eapply is_total_mori; [red; reflexivity| | apply WF_s].
  apply inclusion_union_r. left. reflexivity.
Qed.

Lemma rsr_func_rf : functional rf_s⁻¹.
Proof using INV.
  assert (WF_s : Wf G_s'').
  { apply rsr_imm_Gs_wf. }
  destruct classic
      with (~ (~E_t a_t /\ E_t b_t))
        as [EMP|NEMP'].
  { eapply functional_mori; [| apply WF_s].
    unfold flip. simpl. rewrite extra_a_none by auto.
    basic_solver 11. }
  assert (NEMP : ~ E_t a_t /\ E_t b_t) by tauto.
  desf.
  assert (NIN : ~ E_s'' b_t) by auto with xmm.
  change rf_s with (rf_s'' ∪ drf_s'').
  rewrite transp_union. apply functional_union.
  { apply WF_s. }
  { eapply functional_mori; [| apply fake_srff, WF_s].
    unfold flip. apply transp_mori. basic_solver. }
  enough (DISJ : set_disjoint (dom_rel rf_s''⁻¹) (dom_rel drf_s''⁻¹)).
  { apply DISJ. }
  rewrite !dom_transp, (wf_rfE WF_s).
  arewrite (codom_rel drf_s'' ⊆₁ eq b_t).
  { rewrite extra_a_some; auto. basic_solver. }
  rewrite 2!codom_seq, codom_eqv. basic_solver.
Qed.

Lemma new_G_s_wf_idx :
  E_s ∩₁ Tid_ tid_init ⊆₁ is_init.
Proof using INV.
  simpl.
  rewrite set_unionC, set_inter_union_l.
  apply set_subset_union_l. split.
  { unfold extra_a; desf; [| basic_solver].
    unfolder. intros x (XEQ & TID). subst x.
    exfalso. now apply (rsr_bt_tid INV). }
  unfolder. intros x' ((x & XIN & XEQ) & TEQ).
  subst x'.
  rewrite rsr_mapper_tid' in TEQ by apply INV.
  rewrite rsr_mapper_init; try now apply INV.
  all: apply (rsr_ninit_acts INV').
  all: basic_solver.
Qed.

Lemma rsr_rex_sbniff :
  mapper ↑ (
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾
      ext_sb ⨾
        ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘
  ) ≡
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾
      ext_sb ⨾
        ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘.
Proof using INV.
  split; unfolder.
  all: intros x y; ins; desf.
  { rewrite !rsr_mappero by congruence.
    splits; auto. }
  exists x, y.
  rewrite !rsr_mappero by eauto.
  splits; auto.
Qed.

Lemma rsr_rex_sb_split :
  sb_t ≡
    ⦗E_t \₁ eq b_t \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗E_t \₁ eq b_t \₁ eq a_t⦘ ∪
    ⦗E_t \₁ eq b_t \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗eq b_t ∩₁ E_t⦘ ∪
    ⦗E_t \₁ eq b_t \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t ∩₁ E_t⦘ ∪
    ⦗eq b_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗E_t \₁ eq b_t \₁ eq a_t⦘ ∪
    ⦗eq a_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗E_t \₁ eq b_t \₁ eq a_t⦘ ∪
    ⦗eq b_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t ∩₁ E_t⦘.
Proof using INV.
  assert (NSBB : ~ ext_sb a_t b_t).
  { intro SB.
    eapply ext_sb_irr, ext_sb_trans with b_t; eauto.
    apply INV. }
  unfold sb.
  rewrite set_union_minus
      with (s := E_t) (s' := E_t ∩₁ (eq b_t ∪₁ eq a_t))
        at 1 2; [| basic_solver].
  rewrite id_union, !seq_union_l, !seq_union_r.
  arewrite (
    E_t \₁ E_t ∩₁ (eq b_t ∪₁ eq a_t) ≡₁
      (E_t \₁ eq b_t) \₁ eq a_t
  ).
  { rewrite set_minus_inter_r, set_minusK, set_union_empty_l.
    now rewrite set_minus_minus_l. }
  rewrite set_inter_union_r.
  rewrite id_union, !seq_union_l, !seq_union_r.
  rewrite <- !unionA.
  rewrite set_interC with (s' := eq b_t) (s := E_t).
  rewrite set_interC with (s' := eq a_t) (s := E_t).
  arewrite_false (⦗eq a_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t ∩₁ E_t⦘).
  { unfolder. intros. desf. eapply ext_sb_irr; eauto. }
  arewrite_false (⦗eq b_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗eq b_t ∩₁ E_t⦘).
  { unfolder. intros. desf. eapply ext_sb_irr; eauto. }
  arewrite_false (⦗eq a_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗eq b_t ∩₁ E_t⦘).
  { unfolder. intros. desf. }
  rewrite !union_false_r. reflexivity.
Qed.

Lemma rsr_rex_extsb_inv_l x
    (NB : x <> b_t)
    (EIN : E_t x)
    (IN : E_t b_t)
    (EXT : ext_sb x a_t) :
  ext_sb x b_t.
Proof using INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  assert (ANINI : ~is_init b_t) by apply INV.
  destruct classic with (is_init x) as [INI|NINI].
  { destruct x, b_t; ins. }
  assert (ABSB : ext_sb b_t a_t) by apply INV.
  destruct ext_sb_semi_total_r
      with (x := a_t) (y := x) (z := b_t).
  all: auto.
  { destruct x, b_t; ins.
    desf; ins. desf. congruence. }
  destruct classic with (E_t a_t) as [INA|NINA]; exfalso.
  { eapply (rsr_at_bt_imm INV).
    all: unfold sb; basic_solver. }
  apply (rsr_bt_max INV) with b_t x.
  all: auto.
  unfold sb. basic_solver.
Qed.

Lemma rsr_rex_extsb_inv_r x
    (NB : x <> a_t)
    (EIN : E_t x)
    (IN : E_t b_t)
    (EXT : ext_sb b_t x) :
  ext_sb a_t x.
Proof using INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  assert (XNINI : ~is_init x).
  { destruct b_t, x; desf. }
  assert (ANINI : ~is_init a_t) by apply INV.
  assert (BNINI : ~is_init b_t) by apply INV.
  assert (ABSB : ext_sb b_t a_t) by apply INV.
  destruct ext_sb_semi_total_l
      with (x := b_t) (y := x) (z := a_t).
  all: auto.
  { destruct x, a_t, b_t; ins.
    desf; ins. desf. congruence. }
  destruct classic with (E_t a_t) as [INA|NINA]; exfalso.
  { clear ABSB.
    eapply (rsr_at_bt_imm INV).
    all: unfold sb; basic_solver. }
  apply (rsr_bt_max INV) with b_t x.
  all: auto.
  unfold sb. basic_solver.
Qed.

Lemma rsr_rex_dom_b :
  mapper ↑ (⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗eq b_t ∩₁ E_t⦘) ≡
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  split; unfolder.
  { intros x' y' (x & y & (((XIN & BNX) & ANX) & SB & YEQ & YIN) & XEQ' & YEQ').
    subst x' y' y. rewrite rsr_mappero, rsr_mapper_bt by congruence.
    splits; auto; [eapply ext_sb_trans; eauto; apply INV |].
    exists b_t; splits; auto. now apply rsr_mapper_bt. }
  intros x y' (((XIN & BNX) & ANX) & SB & (y & (YEQ & YIN) & YEQ')).
  subst y y'. exists x, b_t. rewrite rsr_mappero, rsr_mapper_bt in * by congruence.
  splits; auto. apply rsr_rex_extsb_inv_l; auto.
Qed.

Lemma rsr_rex_dom_a :
  mapper ↑ (⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t ∩₁ E_t⦘) ≡
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  split; unfolder.
  { intros x' y' (x & y & (((XIN & BNX) & ANX) & SB & YEQ & YIN) & XEQ' & YEQ').
    subst x' y' y. rewrite rsr_mappero, rsr_mapper_at by congruence.
    splits; auto; [apply rsr_rex_extsb_inv_l; auto; now apply (rsr_at_bt_ord INV) |].
    exists a_t; splits; auto. now apply rsr_mapper_at. }
  intros x y' (((XIN & BNX) & ANX) & SB & (y & (YEQ & YIN) & YEQ')).
  subst y y'. exists x, a_t. rewrite rsr_mapper_at, rsr_mappero in * by congruence.
  splits; auto. eapply ext_sb_trans; eauto; apply INV.
Qed.

Lemma rsr_rex_codom_b :
  mapper ↑ (⦗eq b_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘) ≡
    ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  split; unfolder.
  { intros x' y' (x & y & ((XEQ & XIN) & SB & (YIN & YNB) & ANY) & XEQ' & YEQ').
    subst x' y' x. rewrite rsr_mapper_bt, rsr_mappero by congruence.
    splits; auto; [| apply rsr_rex_extsb_inv_r; auto].
    exists b_t; splits; auto. now apply rsr_mapper_bt. }
  intros x' y ((x & (XEQ & XIN) & XEQ') & SB & ((YIN & BNY) & ANY)).
  subst x x'. exists b_t, y. rewrite rsr_mapper_bt, rsr_mappero in * by congruence.
  splits; auto. eapply ext_sb_trans; eauto; apply INV.
Qed.

Lemma rsr_rex_codom_a :
  mapper ↑ (⦗eq a_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘) ≡
    ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  split; unfolder.
  { intros x' y' (x & y & ((XEQ & XIN) & SB & (YIN & YNB) & ANY) & XEQ' & YEQ').
    subst x' y' x. rewrite rsr_mapper_at, rsr_mappero by congruence.
    splits; auto; [| eapply ext_sb_trans; eauto; apply INV].
    exists a_t; splits; auto. now apply rsr_mapper_at. }
  intros x' y ((x & (XEQ & XIN) & XEQ') & SB & ((YIN & BNY) & ANY)).
  subst x x'. exists a_t, y. rewrite rsr_mapper_at, rsr_mappero in * by congruence.
  splits; auto. apply rsr_rex_extsb_inv_r; auto. now apply (rsr_at_bt_ord INV).
Qed.

Lemma mapped_swap_rel :
  mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t) ≡
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ∪
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ∪
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ∪
    ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ∪
    ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ∪
    ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘.
Proof using INV.
  rewrite rsr_rex_sb_split.
  unfold swap_rel. rewrite !minus_union_l.
  do 5 (rewrite minus_disjoint; [| basic_solver]).
  arewrite_false (⦗eq b_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t ∩₁ E_t⦘ \ (eq b_t ∩₁ E_t) × (eq a_t ∩₁ E_t)).
  { basic_solver 11. }
  rewrite union_false_r, !collect_rel_union.
  rewrite rsr_rex_codom_a, rsr_rex_codom_b.
  rewrite rsr_rex_dom_a, rsr_rex_dom_b.
  rewrite rsr_rex_sbniff.
  repeat apply union_more; try reflexivity.
  rewrite collect_rel_cross.
  split; [| basic_solver].
  unfolder. intros x' y' ((x & (XEQ & XIN) & XEQ') & (y & (YEQ & YIN) & YEQ')).
  subst x y x' y'. splits; eauto.
  rewrite rsr_mapper_at, rsr_mapper_bt; apply INV.
Qed.

Lemma new_G_s_sb_helper
    (EMP : ~ (~ E_t a_t /\ E_t b_t)) :
  ⦗E_t⦘ ⨾ ext_sb ⨾ ⦗E_t⦘ ≡
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ∪
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ∪
    ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ∪
    ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ∪
    ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘ ∪
    ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (ORG : (E_t a_t \/ ~E_t b_t)) by tauto.
  destruct ORG as [INA | NINB].
  { assert (INB : E_t b_t) by now apply (rsr_at_bt_ord INV).
    rewrite !set_inter_absorb_r by basic_solver.
    rewrite !set_collect_eq.
    rewrite rsr_mapper_at, rsr_mapper_bt; auto.
    change (⦗E_t⦘ ⨾ ext_sb ⨾ ⦗E_t⦘) with sb_t.
    rewrite rsr_rex_sb_split.
    rewrite !set_inter_absorb_r by basic_solver.
    basic_solver 20. }
  assert (NINA : ~ E_t a_t).
  { intro FALSO. now apply NINB, (rsr_at_bt_ord INV). }
  arewrite (eq a_t ∩₁ E_t ≡₁ ∅) by basic_solver.
  arewrite (eq b_t ∩₁ E_t ≡₁ ∅) by basic_solver.
  rewrite set_collect_empty, eqv_empty.
  rewrite !seq_false_l, !seq_false_r, !union_false_r.
  rewrite set_minus_minus_l, set_minus_disjoint; [reflexivity |].
  apply set_disjoint_union_r; split; basic_solver.
Qed.

Lemma new_G_s_sb_helper'
    (NEMP : ~ E_t a_t /\ E_t b_t) :
  ⦗E_t ∪₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗E_t ∪₁ eq a_t⦘ ≡
    ⦗E_t \₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗E_t \₁ eq b_t⦘ ∪
    ⦗E_t \₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t⦘ ∪
    ⦗eq a_t⦘         ⨾ ext_sb ⨾ ⦗E_t \₁ eq b_t⦘ ∪
                       sb_t ⨾ ⦗eq b_t⦘ ∪
                  eq b_t × eq a_t.
Proof using INV.
  rewrite id_union, !seq_union_l, !seq_union_r.
  arewrite_false (⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗E_t⦘).
  { apply INV. desf. }
  arewrite_false (⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t⦘).
  { unfolder. ins. desf. eapply ext_sb_irr. eauto. }
  rewrite !union_false_r.
  change (⦗E_t⦘ ⨾ ext_sb ⨾ ⦗E_t⦘) with sb_t.
  rewrite rsr_rex_sb_split at 1.
  arewrite (eq a_t ∩₁ E_t ≡₁ ∅) by basic_solver.
  rewrite eqv_empty.
  arewrite_false (⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗E_t \₁ eq b_t⦘).
  { arewrite (E_t \₁ eq b_t ⊆₁ E_t) by basic_solver.
    now apply INV. }
  arewrite_false (⦗eq b_t ∩₁ E_t⦘ ⨾ ext_sb ⨾ ⦗(E_t \₁ eq b_t) \₁ eq a_t⦘).
  { arewrite ((E_t \₁ eq b_t) \₁ eq a_t ⊆₁ E_t) by basic_solver.
    transitivity (⦗eq b_t ∩₁ E_t⦘ ⨾ sb_t); [| now apply INV].
    unfold sb. basic_solver. }
  arewrite (eq b_t ∩₁ E_t ≡₁ eq b_t) by basic_solver.
  rewrite !seq_false_l, !seq_false_r, !union_false_r.
  transitivity (
    ⦗E_t \₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗E_t \₁ eq b_t⦘ ∪
    sb_t ⨾ ⦗eq b_t⦘ ∪
    (⦗E_t \₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t⦘ ∪ eq b_t × eq a_t)
  ); [| basic_solver 11].
  arewrite (
    ⦗E_t \₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t⦘ ∪ eq b_t × eq a_t ≡
    ⦗E_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t⦘
  ).
  { rewrite set_union_minus
       with (s := E_t) (s' := eq b_t)
         at 2; [| basic_solver].
    rewrite id_union, !seq_union_l.
    apply union_more; [reflexivity |].
    split; [| basic_solver].
    unfolder. ins. desf. splits; auto. apply INV. }
  arewrite ((E_t \₁ eq b_t) \₁ eq a_t ≡₁ E_t \₁ eq b_t).
  { apply set_minus_disjoint. basic_solver. }
  arewrite (sb_t ⨾ ⦗eq b_t⦘ ≡ ⦗E_t \₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗eq b_t⦘).
  { unfold sb. split; [| basic_solver].
    unfolder. ins. desf. splits; auto.
    intro FALSO. desf. eapply ext_sb_irr; eauto. }
  reflexivity.
Qed.

Lemma imm_G_s_sb :
  sb_s'' ≡
    mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t).
Proof using INV.
  assert (NSBAB : ~ext_sb a_t b_t).
  { intro FALSO.
    now eapply ext_sb_irr, ext_sb_trans, (rsr_at_bt_sb INV). }
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold sb at 1. simpl.
  rewrite mapped_swap_rel.
  rewrite set_union_minus
      with (s := E_t) (s' := eq b_t ∩₁ E_t ∪₁ eq a_t ∩₁ E_t)
        at 1 2
        by basic_solver.
  rewrite !set_collect_union.
  arewrite (
    E_t \₁ (eq b_t ∩₁ E_t ∪₁ eq a_t ∩₁ E_t) ≡₁
      (E_t \₁ eq b_t) \₁ eq a_t
  ).
  { rewrite <- set_minus_minus_l.
    rewrite !set_minus_inter_r.
    rewrite set_minusK, set_union_empty_r.
    arewrite ((E_t \₁ eq b_t) \₁ E_t ≡₁ ∅).
    { basic_solver. }
    now rewrite set_union_empty_r. }
  rewrite !id_union.
  rewrite !seq_union_l, !seq_union_r.
  rewrite <- !unionA.
  arewrite_false (
    ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⨾
      ext_sb ⨾
        ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘
  ).
  { unfolder. ins. desf.
    eapply ext_sb_irr; eauto. }
  arewrite_false (
    ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ⨾
      ext_sb ⨾
        ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘
  ).
  { unfolder. ins. desf.
    eapply ext_sb_irr; eauto. }
  arewrite_false (
    ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⨾
      ext_sb ⨾
        ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘
  ).
  { unfolder.
    intros x y
      ((x' & (XEQ & XIN) & XEQ') &
       SB &
       (y' & (YEQ & YIN) & YEQ')).
    subst x' y'. apply NSBAB.
    rewrite (rsr_mapper_at NEQ), (rsr_mapper_bt NEQ) in *.
    now subst x y. }
  rewrite !union_false_r.
  rewrite rsr_setE_iff
     with (s := (E_t \₁ eq b_t) \₁ eq a_t)
       by (auto || (right; unfold not; basic_solver)).
  reflexivity.
Qed.

Lemma new_G_s_sb :
  sb_s ≡
    mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t) ∪
      (mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘)) × A_s ∪
        A_s × eq (mapper b_t).
Proof using INV.
  unfold sb at 1. simpl.
  destruct classic
      with (~(~E_t a_t /\ E_t b_t))
        as [EMP|NEMP'].
  { rewrite !extra_a_none; auto.
    rewrite set_union_empty_r.
    rewrite cross_false_l, cross_false_r, !union_false_r.
    arewrite (mapper ↑₁ E_t ≡₁ E_t).
    { apply rsr_setE_iff; [apply INV |].
      assert (ORG : E_t a_t \/ ~E_t b_t) by tauto.
      destruct ORG as [INA | NINB].
      { left. split; auto. now apply (rsr_at_bt_ord INV). }
      right. split; auto. intro FALSO.
      now apply NINB, (rsr_at_bt_ord INV). }
    rewrite mapped_swap_rel.
    now apply new_G_s_sb_helper. }
  assert (NEMP : ~E_t a_t /\ E_t b_t) by tauto.
  rewrite extra_a_some by desf.
  rewrite rsr_mapper_bt by apply INV.
  rewrite mapped_swap_rel.
  arewrite ((E_t \₁ eq b_t) \₁ eq a_t ≡₁ E_t \₁ eq b_t).
  { rewrite set_minus_disjoint; [reflexivity |].
    basic_solver. }
  arewrite (eq a_t ∩₁ E_t ≡₁ ∅).
  { basic_solver. }
  rewrite set_collect_empty, eqv_empty,
          !seq_false_r, !seq_false_l.
  rewrite !union_false_r.
  arewrite (eq b_t ∩₁ E_t ≡₁ eq b_t).
  { basic_solver. }
  rewrite set_collect_eq, rsr_mapper_bt by apply INV.
  arewrite (mapper ↑₁ E_t ∪₁ eq b_t ≡₁ E_t ∪₁ eq a_t).
  { rewrite rsr_setE_niff; try apply INV; desf.
    rewrite set_union_minus
       with (s := E_t) (s' := eq b_t)
         at 2; basic_solver. }
  arewrite (
    mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘) ≡₁
    dom_rel (sb_t ⨾ ⦗eq b_t⦘)
  ).
  { apply rsr_setE_iff; [apply INV |].
    right. split; unfolder; intro FALSO; desf.
    { eapply sb_irr; eauto. }
    unfold sb in FALSO. unfolder in FALSO. desf. }
  arewrite (
    dom_rel (sb_t ⨾ ⦗eq b_t⦘) × eq b_t ≡ sb_t ⨾ ⦗eq b_t⦘
  ).
  { basic_solver. }
  now apply new_G_s_sb_helper'.
Qed.

Lemma rsr_rex_codom :
  mapper ↑₁ E_t ⊆₁ E_s \₁ A_s.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl.
  rewrite set_minus_union_l, set_minusK,
          set_union_empty_r.
  rewrite set_minus_disjoint; [reflexivity |].
  unfold extra_a; desf.
  unfolder. ins. desf.
  enough (y = a_t) by desf.
  now apply (rsr_mapper_inv_bt _ NEQ).
Qed.

Lemma rsr_rex_froma
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  ⦗eq b_t⦘ ⨾ sb_s ⊆ eq b_t × eq a_t.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  transitivity (⦗eq b_t⦘ ⨾ sb_s ⨾ ⦗E_s \₁ eq b_t⦘).
  { rewrite wf_sbE at 1. clear. unfolder.
    ins. desf.
    splits; auto.
    intro FALSO; desf; eapply sb_irr; eauto. }
  rewrite new_G_s_sb.
  rewrite extra_a_some by assumption.
  rewrite rsr_mapper_bt; auto.
  arewrite (eq a_t ∩₁ E_t ≡₁ ∅) by basic_solver.
  rewrite swap_rel_empty_r.
  rewrite !seq_union_l, !seq_union_r.
  repeat apply inclusion_union_l.
  { rewrite wf_sbE, collect_rel_seqi.
    rewrite collect_rel_eqv, rsr_rex_codom.
    rewrite extra_a_some by assumption.
    clear. basic_solver. }
  all: clear; basic_solver.
Qed.

Lemma rsr_imm_G_sub : E_s'' ⊆₁ E_s.
Proof using.
  simpl. basic_solver.
Qed.

Hypothesis LVAL : dom_rel drf_s'' ⊆₁ Val_s_'' (WCore.lab_val l_a).

Lemma rsr_drf_doms :
  drf_s'' ⊆
    (E_s'' ∩₁
     W_s'' ∩₁
     Loc_s_'' (WCore.lab_loc l_a) ∩₁
     Val_s_'' (WCore.lab_val l_a)
    ) × (A_s ∩₁ WCore.lab_is_r l_a).
Proof using INV LVAL.
  enough (RFV : drf_s'' ⊆ ⦗Val_s_'' (WCore.lab_val l_a)⦘ ⨾ drf_s'').
  { rewrite RFV, fake_srfD_left, fake_srfE_left,
          fake_srfl.
    basic_solver. }
  unfolder. ins. desf. splits; auto.
  apply LVAL. do 2 eexists. split; eauto.
  basic_solver.
Qed.

Lemma rsr_wf_w_helper :
  W_s'' ∩₁ E_s'' ⊆₁ W_s.
Proof using INV.
  unfold is_w. unfolder. intros x (ISW & XIN).
  rewrite rsr_rexi in ISW; auto.
Qed.

Lemma rsr_wf_r_helper :
  R_s'' ∩₁ E_s'' ⊆₁ R_s.
Proof using INV.
  unfold is_r. unfolder. intros x (ISR & XIN).
  rewrite rsr_rexi in ISR; auto.
Qed.

Lemma rsr_wf_loc_helper :
  ⦗E_s''⦘ ⨾ same_loc_s'' ⨾ ⦗E_s''⦘ ⊆ same_loc_s.
Proof using INV.
  unfold same_loc, loc. unfolder.
  intros x y (XIN & EQLOC & YIN).
  rewrite !rsr_rexi in EQLOC; auto.
Qed.

Lemma rsr_wf_val_helper :
  ⦗E_s''⦘ ⨾ same_val_s'' ⨾ ⦗E_s''⦘ ⊆ same_val_s.
Proof using INV.
  unfold same_val, val. unfolder.
  intros x y (XIN & EQVAL & YIN).
  rewrite !rsr_rexi in EQVAL; auto.
Qed.

Lemma exa_isr_helper :
  A_s ∩₁ WCore.lab_is_r l_a ⊆₁ R_s.
Proof using INV.
  unfold extra_a; desf; [| basic_solver].
  rewrite <- rsr_rex_isr_helper by desf.
  basic_solver.
Qed.

Lemma exa_isw_helper :
  A_s ∩₁ WCore.lab_is_w l_a ⊆₁ W_s.
Proof using INV.
  unfold extra_a; desf; [| basic_solver].
  rewrite <- rsr_rex_isw_helper by desf.
  basic_solver.
Qed.

Lemma G_s_wf_rmwD :
  rmw_s ≡
    ⦗E_s \₁ (eq b_t ∪₁ eq a_t)⦘ ⨾
      rmw_s ⨾
        ⦗E_s \₁ (eq b_t ∪₁ eq a_t)⦘.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (WF_s : Wf G_s'') by apply rsr_imm_Gs_wf.
  enough (RMW : rmw_s ≡
    ⦗set_compl (eq b_t ∪₁ eq a_t)⦘ ⨾
      rmw_s ⨾
        ⦗set_compl (eq b_t ∪₁ eq a_t)⦘
  ).
  { apply dom_helper_3.
    rewrite RMW, (wf_rmwE WF_s).
    rewrite rsr_imm_G_sub.
    basic_solver 11. }
  apply dom_helper_3.
  intros x' y' (x & y & (RMW & XEQ & YEQ)).
  apply (rsr_nrmw INV) in RMW. subst x' y'.
  split.
  all: unfolder.
  all: intro FALSO; desf.
  { symmetry in FALSO.
    apply rsr_mapper_inv_bt in FALSO; auto.
    subst x. forward apply RMW. basic_solver. }
  { symmetry in FALSO.
    apply rsr_mapper_inv_at in FALSO; auto.
    subst x. forward apply RMW. basic_solver. }
  { symmetry in FALSO.
    apply rsr_mapper_inv_bt in FALSO; auto.
    subst y. forward apply RMW. basic_solver. }
  symmetry in FALSO.
  apply rsr_mapper_inv_at in FALSO; auto.
  subst y. forward apply RMW. basic_solver.
Qed.

Lemma new_G_s_wf_rmw : rmw_s ⊆ immediate sb_s.
Proof using INV.
  assert (WF_s : Wf G_s'') by apply rsr_imm_Gs_wf.
  arewrite (
    rmw_s ≡
      ⦗E_s \₁ (eq b_t ∪₁ eq a_t)⦘ ⨾
        rmw_s ⨾
          ⦗E_s \₁ (eq b_t ∪₁ eq a_t)⦘
  ).
  { apply G_s_wf_rmwD. }
  rewrite (wf_rmwi WF_s).
  rewrite !immediateE.
  remember (E_s \₁ (eq b_t ∪₁ eq a_t)) as DD.
  rewrite <- seq_eqv_minus_lr, <- seq_eqv_minus_ll.
  assert (HELP :
    ⦗DD⦘ ⨾ sb_s'' ⨾ ⦗DD⦘ \ sb_s ⨾ sb_s ⊆
      sb_s \ sb_s ⨾ sb_s
  ).
  { apply minus_rel_mori; [| unfold flip; reflexivity].
    unfold sb. rewrite rsr_imm_G_sub. basic_solver. }
  rewrite <- HELP.
  intros x y (SB & NSB). split; auto.
  intro FALSO. apply NSB.
  destruct FALSO as (z & F1 & F2).
  assert (XIN : E_s'' x).
  { forward apply SB.
    unfold sb. clear. basic_solver. }
  assert (YIN : E_s'' y).
  { forward apply SB.
    unfold sb. clear. basic_solver. }
  enough (ZIN : E_s'' z).
  { exists z. forward apply F1. forward apply F2.
    unfold sb. basic_solver 11. }
  assert (ZIN : E_s z).
  { forward apply F1. unfold sb. basic_solver. }
  destruct ZIN as [ZIN|ZIN]; auto.
  unfold extra_a in ZIN; desf.
  exfalso.
  assert (YNB : y <> b_t).
  { intro FALSO. subst y.
    forward apply SB. basic_solver. }
  assert (YNA : y <> a_t).
  { intro FALSO. subst y.
    forward apply SB. basic_solver. }
  apply (rsr_bt_max INV) with b_t y; desf.
  unfolder. splits; auto.
  unfold sb. unfolder. splits; auto.
  { forward apply F2. unfold sb. basic_solver. }
  destruct YIN as (y' & YIN & YEQ). subst y.
  rewrite rsr_mappero; auto.
  { intro FALSO. subst y'.
    rewrite rsr_mapper_at in YNB; auto. }
  intro FALSO. subst y'.
  rewrite rsr_mapper_bt in YNA; auto.
  apply INV.
Qed.

Lemma new_G_s_wf : Wf G_s.
Proof using INV LVAL.
  assert (WF_s : Wf G_s'') by apply rsr_imm_Gs_wf.
  assert (WF_t : Wf G_t) by apply INV.
  assert (NINIB : ~is_init b_t) by apply INV.
  assert (NINIA : ~is_init a_t) by apply INV.
  assert (EXAIM : A_s ⊆₁ E_s).
  { simpl. basic_solver. }
  constructor.
  { intros x y (XIN & YIN & NEQ & TEQ & NINI).
    enough (NIN : ~is_init y).
    { destruct x, y; ins; desf; congruence. }
    destruct y as [yl | yt yn]; ins.
    exfalso. apply NINI, new_G_s_wf_idx.
    basic_solver. }
  { rewrite (rsr_ndata INV). basic_solver. }
  { rewrite (rsr_ndata INV). basic_solver. }
  { rewrite (rsr_naddr INV). basic_solver. }
  { rewrite (rsr_naddr INV). basic_solver. }
  { rewrite (rsr_nctrl INV). basic_solver. }
  { rewrite (rsr_nctrl INV). basic_solver. }
  { rewrite (rsr_nctrl INV). basic_solver. }
  { apply dom_helper_3. simpl.
    rewrite (wf_rmwE WF_s), (wf_rmwD WF_s).
    rewrite !seqA. seq_rewrite <- !id_inter.
    rewrite set_interC, rsr_wf_r_helper, rsr_wf_w_helper.
    basic_solver. }
  { rewrite (wf_rmwE WF_s), (wf_rmwl WF_s).
    apply rsr_wf_loc_helper. }
  { apply new_G_s_wf_rmw. }
  { apply dom_helper_3, inclusion_union_l.
    { rewrite <- rsr_imm_G_sub.
      rewrite (wf_rfE WF_s). basic_solver. }
    rewrite rsr_drf_doms, rsr_imm_G_sub, EXAIM.
    basic_solver. }
  { apply dom_helper_3, inclusion_union_l.
    { rewrite (wf_rfE WF_s), (wf_rfD WF_s).
      rewrite !seqA. seq_rewrite <- !id_inter.
      rewrite set_interC, rsr_wf_r_helper, rsr_wf_w_helper.
      basic_solver. }
    rewrite rsr_drf_doms, set_interC with (s := E_s'').
    rewrite rsr_wf_w_helper, exa_isr_helper.
    basic_solver. }
  { apply inclusion_union_l.
    { rewrite (wf_rfE WF_s), (wf_rfl WF_s).
      apply rsr_wf_loc_helper. }
    rewrite rsr_drf_doms.
    unfold extra_a in *. desf; [| basic_solver].
    unfolder. intros. desf.
    unfold same_loc, loc in *.
    rewrite <- rsr_rex_labloc_helper in *; auto.
    rewrite rsr_rexi in *; auto. }
  { enough (VAL : rf_s ⊆ same_val_s).
    { apply VAL. }
    apply inclusion_union_l.
    { rewrite (wf_rfE WF_s).
      arewrite (rf_s'' ⊆ same_val_s'').
      { apply WF_s. }
      apply rsr_wf_val_helper. }
    rewrite rsr_drf_doms.
    unfold extra_a in *. desf; [| basic_solver].
    unfolder. intros. desf.
    unfold val in *.
    rewrite <- rsr_rex_labval_helper in *; auto.
    rewrite rsr_rexi in *; auto. }
  { apply rsr_func_rf. }
  { apply dom_helper_3, inclusion_union_l.
    { rewrite <- rsr_imm_G_sub.
      rewrite (wf_coE WF_s). basic_solver. }
    rewrite rsr_imm_G_sub, EXAIM.
    basic_solver. }
  { apply dom_helper_3, inclusion_union_l.
    { rewrite (wf_coE WF_s), (wf_coD WF_s).
      rewrite !seqA. seq_rewrite <- !id_inter.
      rewrite set_interC, rsr_wf_w_helper.
      basic_solver. }
    rewrite set_interC with (s := E_s'').
    rewrite rsr_wf_w_helper, exa_isw_helper.
    basic_solver. }
  { apply inclusion_union_l.
    { rewrite (wf_coE WF_s), (wf_col WF_s).
      apply rsr_wf_loc_helper. }
    unfold extra_a in *. desf; [| basic_solver].
    unfolder. intros. desf.
    unfold same_loc, loc in *.
    rewrite <- rsr_rex_labloc_helper in *; auto.
    rewrite rsr_rexi in *; auto. }
  { apply rsr_trans_co. }
  { apply rsr_total_co. }
  { apply irreflexive_union.
    split; [apply rsr_imm_Gs_wf |].
    unfold extra_a; desf; [| basic_solver].
    assert (NINB' : ~E_s'' b_t) by (desf; eauto with xmm).
    unfolder. ins. desf. }
  { intros l _. left. exists (InitEvent l).
    split; [now apply (rsr_init_acts INV) |].
    rewrite rsr_mapper_init; auto. }
  { simpl. unfold lab_s_, compose. intro l.
    rewrite rsr_mapper_init; auto.
    transitivity (lab_t (InitEvent l)).
    { desf. rewrite updo; [reflexivity |].
      intro FALSO. rewrite <- FALSO in NINIA. ins. }
    apply WF_t. }
  { rewrite (rsr_nrmw_dep INV). basic_solver. }
  { rewrite (rsr_nrmw_dep INV). basic_solver. }
  simpl. intros e [EIN | EX].
  { apply (wf_threads (rsr_imm_Gs_wf)).
    simpl. auto. }
  unfold extra_a in EX. desf.
  now apply (wf_threads WF_t).
Qed.

End ReordGraph.