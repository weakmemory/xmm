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

(* Id aliases for better readability *)
Definition a_s := b_t.
Definition b_s := a_t.

Definition mapper_inv := mapper.

Definition rsr_rex_imm_g : execution := {|
  acts_set := mapper ↑₁ E_t';
  threads_set := threads_set G_t';
  lab := lab_t' ∘ mapper;
  rf := mapper ↑ rf_t';
  co := mapper ↑ co_t';
  rmw := mapper ↑ rmw_t';
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.
Definition rsr_rex_immx := {|
  WCore.sc := WCore.sc X_s;
  WCore.G := rsr_rex_imm_g;
|}.

Notation "'X_s'''" := rsr_rex_immx.
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

Definition lab_s_' :=
  ifP ~E_t' a_t /\ E_t' b_t then upd (lab_t' ∘ mapper_inv) b_t l_a
  else (lab_t' ∘ mapper).

Definition rsr_rex_Gs_prime : execution := {|
  acts_set := mapper ↑₁ E_t' ∪₁ A_s';
  threads_set := threads_set G_t';
  lab := lab_s_';
  rf := mapper ↑ rf_t' ∪ drf_s'';
  co := mapper ↑ co_t' ∪
          (W_s'' ∩₁ E_s'' ∩₁ Loc_s_'' (WCore.lab_loc l_a)) ×
          (A_s' ∩₁ WCore.lab_is_w l_a);
  rmw := mapper ↑ rmw_t';
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.
Definition rsr_rex_Xs_prime := {|
  WCore.sc := WCore.sc X_s;
  WCore.G := rsr_rex_Gs_prime;
|}.

Notation "'X_s''" := rsr_rex_Xs_prime.
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

Lemma rsr_rex_anin_imm
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t) :
  ~ (mapper ↑₁ E_t') b_t.
Proof using INV.
  unfolder. intros (y & YIN & YEQ).
  enough (y = a_t) by desf.
  eapply rsr_mapper_inv_bt; eauto.
  apply INV.
Qed.

Lemma mapinj : inj_dom E_t' mapper.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  eapply inj_dom_mori; eauto with xmm.
  red; auto with hahn.
Qed.

Lemma mapinj_inv' :
  inj_dom ⊤₁ mapper_inv.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold mapper_inv. auto with xmm.
Qed.

Lemma mapinj_inv : inj_dom E_t' mapper_inv.
Proof using INV.
  eapply inj_dom_mori; eauto using mapinj_inv'.
  red. auto with hahn.
Qed.

Lemma mapper_inv_l_inv :
  mapper ∘ mapper_inv = id.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold mapper_inv. now apply rsr_mapper_compose.
Qed.

Lemma mapper_inv_r_inv :
  mapper_inv ∘ mapper = id.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold mapper_inv. now apply rsr_mapper_compose.
Qed.

Lemma rsr_exa_notin_imm :
  A_s' ⊆₁ set_compl E_s''.
Proof using INV.
  unfold extra_a; desf. simpl.
  unfolder. intros x XEQ. subst x.
  intro FALSO. desf.
  enough (y = a_t) by desf.
  assert (NEQ : a_t <> b_t) by apply INV.
  now apply (rsr_mapper_inv_bt _ NEQ).
Qed.

Lemma imm_fin_acts_minus : E_s'' ≡₁ E_s' \₁ A_s'.
Proof using INV.
  simpl.
  rewrite set_minus_union_l.
  rewrite set_minusK, set_union_empty_r.
  rewrite set_minus_disjoint; [reflexivity |].
  rewrite rsr_exa_notin_imm. basic_solver.
Qed.

Lemma rsr_rex : eq_dom E_t' (lab_s' ∘ mapper) lab_t'.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. unfold lab_s_', mapper_inv. desf.
  { rewrite <- (rsr_mapper_at NEQ)
         at 2.
    rewrite <- upd_compose; auto with xmm.
    apply eq_dom_upd_l; [desf |].
    rewrite Combinators.compose_assoc.
    rewrite rsr_mapper_compose by auto.
    now rewrite Combinators.compose_id_right. }
  rewrite Combinators.compose_assoc.
  rewrite rsr_mapper_compose by auto.
  now rewrite Combinators.compose_id_right.
Qed.

Lemma rsr_imm_Gs_wf : Wf G_s''.
Proof using INV.
Admitted.

Lemma rsr_rexi : eq_dom E_s'' lab_s'' lab_s'.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. unfold lab_s_', mapper_inv. desf.
  apply eq_dom_upd_r; [| reflexivity].
  now apply rsr_rex_anin_imm.
Qed.

Hint Resolve rsr_rex rsr_rexi : xmm.

Lemma rsr_rex_isr_helper
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t) :
  eq b_t ∩₁ R_s' ≡₁ eq b_t ∩₁ WCore.lab_is_r l_a.
Proof using INV.
  simpl. unfold lab_s_'; desf; [| tauto].
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. unfold is_r, WCore.lab_is_r.
  unfolder. split.
  all: intros x (XEQ & ISR); subst x.
  all: rewrite upds in *; desf.
Qed.

Lemma rsr_b_isw_helper
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t) :
  eq b_t ∩₁ W_s' ≡₁ eq b_t ∩₁ WCore.lab_is_w l_a.
Proof using INV.
  simpl. unfold lab_s_'; desf; [| tauto].
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. unfold is_w, WCore.lab_is_w.
  unfolder. split.
  all: intros x (XEQ & ISW); subst x.
  all: rewrite upds in *; desf.
Qed.

Lemma rsr_rex_labloc_helper
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t) :
  loc_s' b_t = WCore.lab_loc l_a.
Proof using INV.
  simpl. unfold lab_s_'; desf; [| tauto].
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold loc, WCore.lab_loc.
  now rewrite upds.
Qed.

Lemma rsr_rex_labval_helper
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t) :
  val_s' b_t = WCore.lab_val l_a.
Proof using INV.
  simpl. unfold lab_s_'; desf; [| tauto].
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold val, WCore.lab_val.
  now rewrite upds.
Qed.

Lemma rsr_trans_co : transitive co_s'.
Proof using SIMREL INV INV'.
  assert (WF_s : Wf G_s'').
  { apply rsr_imm_Gs_wf. }
  apply expand_transitive.
  { apply WF_s. }
  { apply (co_upward_closed WF_s). }
  rewrite (wf_coE WF_s), dom_seq, dom_eqv.
  rewrite rsr_exa_notin_imm. basic_solver.
Qed.

Lemma rsr_total_co ol :
  is_total
    (E_s' ∩₁ W_s' ∩₁ Loc_s_' ol)
    co_s'.
Proof using SIMREL INV INV'.
  assert (WF_s : Wf G_s'').
  { apply rsr_imm_Gs_wf. }
  destruct classic
      with (~ (~E_t' a_t /\ E_t' b_t))
        as [EMP|NEMP'].
  { simpl. unfold lab_s_'; desf.
    rewrite extra_a_none, set_union_empty_r by auto.
    rewrite set_inter_empty_l, cross_false_r, union_false_r.
    apply WF_s. }
  assert (NEMP : ~ E_t' a_t /\ E_t' b_t) by tauto.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (NIN : ~ E_s'' b_t).
  { simpl. unfolder. intros FALSO. desf.
    enough (y = a_t) by desf.
    now apply (rsr_mapper_inv_bt _ NEQ). }
  assert (EQ :
    E_s'' ∩₁ W_s' ∩₁ Loc_s_' ol ⊆₁
      E_s'' ∩₁ W_s'' ∩₁ Loc_s_'' ol
  ).
  { rewrite set_interA, set_interC with (s := E_s'').
    rewrite set_interA.
    rewrite set_inter_loc with (G := G_s''),
            set_inter_is_w with (G := G_s'').
    all: eauto with xmm.
    { basic_solver. }
    eapply eq_dom_mori; auto with xmm.
    unfold flip; basic_solver. }
  assert (EQ' :
    eq b_t ∩₁ W_s' ∩₁ Loc_s_' ol ⊆₁
      eq b_t ∩₁ WCore.lab_is_w l_a
  ).
  { simpl. unfold lab_s_'; desf.
    unfolder. unfold is_w, WCore.lab_is_w.
    intros x ((XEQ & ISW) & _).
    subst x. rewrite upds in ISW. desf. }
  destruct classic
      with (WCore.lab_loc l_a = ol)
        as [EQL | NEQL].
  { eapply is_total_mori,
          is_total_union_ext with (a := b_t)
                                  (s' := eq b_t ∩₁ WCore.lab_is_w l_a).
    all: try now apply (@wf_co_total _ WF_s ol).
    { unfold flip. simpl.
      rewrite !set_inter_union_l, EQ.
      rewrite extra_a_some, EQ'; desf. }
    { simpl. rewrite EQL, extra_a_some; desf.
      basic_solver 11. }
    { unfolder. intro FALSO. desf. }
    basic_solver. }
  arewrite (E_s' ≡₁ E_s'' ∪₁ A_s').
  rewrite !set_inter_union_l, extra_a_some by desf.
  arewrite (eq b_t ∩₁ W_s' ∩₁ Loc_s_' ol ≡₁ ∅).
  { split; [| auto with hahn].
    transitivity (eq b_t ∩₁ Loc_s_' ol); [basic_solver |].
    simpl. unfold lab_s_', mapper_inv; desf.
    unfolder. intros x (XEQ & LOC). subst x.
    unfold loc in LOC. rewrite upds in LOC.
    apply NEQL, LOC. }
  rewrite set_union_empty_r, EQ.
  eapply is_total_mori;
    [| | apply WF_s].
  { red. reflexivity. }
  simpl. apply inclusion_union_r.
  left. reflexivity.
Qed.

Lemma rsr_func_rf : functional rf_s'⁻¹.
Proof using SIMREL INV INV'.
  assert (WF_s : Wf G_s'').
  { apply rsr_imm_Gs_wf. }
  destruct classic
      with (~ (~E_t' a_t /\ E_t' b_t))
        as [EMP|NEMP'].
  { simpl. unfold lab_s_'; desf.
    rewrite extra_a_none by auto.
    rewrite set_inter_empty_l, eqv_empty,
            seq_false_r, union_false_r.
    apply WF_s. }
  assert (NEMP : ~ E_t' a_t /\ E_t' b_t) by tauto.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (NIN : ~ E_s'' b_t).
  { simpl. unfolder. intros FALSO. desf.
    enough (y = a_t) by desf.
    now apply (rsr_mapper_inv_bt _ NEQ). }
  simpl. apply functional_union.
  { apply WF_s. }
  { arewrite (drf_s''⁻¹ ⊆ (fake_srf G_s'' b_t l_a)⁻¹).
    { apply transp_mori. basic_solver. }
    now eapply fake_srff. }
  intros x HIN1' HIN2'.
  assert (HIN1 : codom_rel rf_s'' x) by now apply dom_transp.
  assert (HIN2 : codom_rel drf_s'' x) by now apply dom_transp.
  enough (E_s'' b_t) by desf.
  assert (XIN : E_s'' x).
  { red in HIN1. destruct HIN1 as (y & RF).
    eapply dom_helper_3 with (r := rf_s'') (d := E_s''); eauto.
    apply WF_s. }
  enough (x = b_t) by desf.
  enough (XIN' : A_s' x).
  { apply extra_a_some in XIN'; desf. }
  forward apply HIN2. basic_solver.
Qed.

Lemma new_G_s_wf_idx :
  E_s' ∩₁ Tid_ tid_init ⊆₁ is_init.
Proof using INV INV'.
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

Hypothesis LVAL : dom_rel drf_s'' ⊆₁ Val_s_'' (WCore.lab_val l_a).

Lemma new_G_s_actsE :
  E_s' ≡₁ E_t' ∪₁ B_s'.
Proof using INV'.
  assert (NEQ : a_t <> b_t) by apply INV'.
  simpl. unfold extra_a; desf.
  { rewrite (rsr_setE_niff); try tauto.
    rewrite set_union_minus
       with (s := E_t') (s' := eq b_t)
         at 2; [| basic_solver].
    basic_solver. }
  rewrite !set_union_empty_r.
  rewrite rsr_setE_iff; auto with hahn.
  assert (ORG : E_t' a_t \/ ~E_t' b_t) by tauto.
  destruct ORG as [INA | NINB].
  { left. split; auto.
    now apply (rsr_at_bt_ord INV'). }
  right. split; auto. intro FALSO.
  now apply NINB, (rsr_at_bt_ord INV').
Qed.

Lemma new_G_s_sb_helper
    (EMP : ~ (~ E_t' a_t /\ E_t' b_t)) :
  ⦗mapper ↑₁ E_t'⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ E_t'⦘ ≡
    mapper ↑ swap_rel sb_t' (eq b_t ∩₁ E_t') (eq a_t ∩₁ E_t').
Proof using INV'.
Admitted.

Lemma new_G_s_sb :
  sb_s' ≡
    mapper ↑ swap_rel sb_t' (eq b_t ∩₁ E_t') (eq a_t ∩₁ E_t') ∪
      (mapper ↑₁ dom_rel (sb_t' ⨾ ⦗eq b_t⦘)) × A_s' ∪
        A_s' × eq (mapper b_t).
Proof using INV'.
  unfold sb at 1. simpl.
  destruct classic
      with (~(~E_t' a_t /\ E_t' b_t))
        as [EMP|NEMP'].
  { rewrite !extra_a_none; auto.
    rewrite set_union_empty_r.
    rewrite cross_false_l, cross_false_r, !union_false_r.
    now apply new_G_s_sb_helper. }
Admitted.

Lemma rsr_rex_codom :
  mapper ↑₁ E_t' ⊆₁ E_s' \₁ A_s'.
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
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t) :
  ⦗eq b_t⦘ ⨾ sb_s' ⊆ eq b_t × eq a_t.
Proof using INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  transitivity (⦗eq b_t⦘ ⨾ sb_s' ⨾ ⦗E_s' \₁ eq b_t⦘).
  { rewrite wf_sbE at 1. clear. unfolder.
    ins. desf.
    splits; auto.
    intro FALSO; desf; eapply sb_irr; eauto. }
  rewrite new_G_s_sb.
  rewrite extra_a_some by assumption.
  rewrite rsr_mapper_bt; auto.
  arewrite (eq a_t ∩₁ E_t' ≡₁ ∅) by basic_solver.
  rewrite swap_rel_empty_r.
  rewrite !seq_union_l, !seq_union_r.
  repeat apply inclusion_union_l.
  { rewrite wf_sbE, collect_rel_seqi.
    rewrite collect_rel_eqv, rsr_rex_codom.
    rewrite extra_a_some by assumption.
    clear. basic_solver. }
  all: clear; basic_solver.
Qed.

Lemma new_G_s_wf
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t) :
  Wf G_s'.
Proof using INV INV' SIMREL LVAL.
  assert (WF_t : Wf G_t') by apply INV'.
  assert (BIN : ~E_s'' b_t) by admit.
  assert (NINIB : ~is_init b_t) by apply INV.
  assert (NINIA : ~is_init a_t) by apply INV.
  constructor.
  { intros x y (XIN & YIN & NEQ & TEQ & NINI).
    enough (NIN : ~is_init y).
    { destruct x, y; ins; desf; congruence. }
    destruct y as [yl | yt yn]; ins.
    exfalso. apply NINI, new_G_s_wf_idx.
    basic_solver. }
  { rewrite (rsr_data SIMREL), (rsr_ndata INV).
    basic_solver. }
  { apply dom_helper_3.
    rewrite (rsr_data SIMREL), (rsr_ndata INV).
    basic_solver. }
  { rewrite (rsr_addr SIMREL), (rsr_naddr INV).
    basic_solver. }
  { apply dom_helper_3.
    rewrite (rsr_addr SIMREL), (rsr_naddr INV).
    basic_solver. }
  { rewrite (rsr_ctrl SIMREL), (rsr_nctrl INV).
    basic_solver. }
  { rewrite (rsr_ctrl SIMREL), (rsr_nctrl INV).
    basic_solver. }
  { rewrite (rsr_ctrl SIMREL), (rsr_nctrl INV).
    basic_solver. }
  { apply dom_helper_3. simpl.
    rewrite (wf_rmwE WF_t), (wf_rmwD WF_t).
    rewrite !seqA. unfolder. ins. desf.
    unfold is_r, is_w in *.
    rewrite <- rsr_rex in *; auto. }
  { simpl.
    rewrite (wf_rmwE WF_t), (wf_rmwl WF_t).
    unfolder. ins. desf.
    unfold same_loc, loc in *.
    rewrite <- 2!rsr_rex in *; auto. }
  { admit. }
  { apply dom_helper_3. simpl.
    apply inclusion_union_l.
    { rewrite (wf_rfE WF_t).
      unfolder. ins. desf. eauto 8. }
    rewrite extra_a_some; auto.
    rewrite fake_srfE_left. basic_solver. }
  { apply dom_helper_3. simpl.
    rewrite extra_a_some; auto.
    rewrite <- rsr_rex_isr_helper; auto.
    apply inclusion_union_l.
    { rewrite (wf_rfE WF_t), (wf_rfD WF_t).
      rewrite !seqA. unfolder. ins. desf.
      unfold is_r, is_w in *.
      rewrite <- rsr_rex in *; auto. }
    rewrite fake_srfD_left, fake_srfE_left.
    rewrite seqA. unfolder. ins. desf.
    unfold is_w, is_r in *.
    rewrite <- rsr_rexi; auto. }
  { simpl.
    rewrite extra_a_some; auto.
    apply inclusion_union_l.
    { rewrite (wf_rfE WF_t), (wf_rfl WF_t).
      unfolder. ins. desf.
      unfold same_loc, loc in *.
      rewrite <- 2!rsr_rex in *; auto. }
    rewrite fake_srfl, fake_srfE_left.
    rewrite seqA. unfolder. ins. desf.
    unfold same_loc, loc in *.
    change (lab_t' ∘ mapper) with lab_s'' in *.
    rewrite rsr_rexi in *; auto.
    rewrite <- rsr_rex_labloc_helper in *; auto. }
  { simpl.
    rewrite extra_a_some; auto.
    apply funeq_union.
    { rewrite (wf_rfE WF_t).
      arewrite (rf_t' ⊆ same_val_t').
      { unfolder. ins. now apply (wf_rfv WF_t). }
      unfolder. ins. desf.
      unfold same_val, val in *.
      rewrite <- 2!rsr_rex in *; auto. }
    rewrite fake_srfE_left.
    unfold funeq. intros a b SRF.
    assert (BEQ : b = b_t); [| subst b].
    { forward apply SRF. basic_solver. }
    assert (AIN : E_s'' a).
    { forward apply SRF. basic_solver. }
    change (val lab_s_') with val_s'.
    rewrite rsr_rex_labval_helper; auto.
    unfold val. rewrite <- rsr_rexi; auto.
    apply LVAL; auto. admit. }
  { apply rsr_func_rf. }
  { apply dom_helper_3. simpl.
    apply inclusion_union_l.
    { rewrite (wf_coE WF_t).
      unfolder. ins. desf. eauto 8. }
    rewrite extra_a_some; auto.
    basic_solver. }
  { apply dom_helper_3. simpl.
    apply inclusion_union_l.
    { rewrite (wf_coE WF_t), (wf_coD WF_t).
      rewrite !seqA. unfolder. ins. desf.
      unfold is_w in *.
      rewrite <- rsr_rex in *; auto. }
    rewrite extra_a_some; auto.
    rewrite <- rsr_b_isw_helper; auto.
    unfolder. ins. desf.
    unfold is_w in *.
    rewrite <- rsr_rexi; auto.
    simpl. basic_solver. }
  { simpl.
    rewrite extra_a_some; auto.
    apply inclusion_union_l.
    { rewrite (wf_coE WF_t), (wf_col WF_t).
      unfolder. ins. desf.
      unfold same_loc, loc in *.
      rewrite <- 2!rsr_rex in *; auto. }
    unfolder. ins. desf.
    unfold same_loc, loc in *.
    change (lab_t' ∘ mapper) with lab_s'' in *.
    rewrite rsr_rexi in *; auto.
    rewrite <- rsr_rex_labloc_helper in *; auto.
    simpl. basic_solver. }
  { apply rsr_trans_co. }
  { apply rsr_total_co. }
  { apply irreflexive_union.
    split; [apply rsr_imm_Gs_wf |].
    rewrite extra_a_some; auto.
    unfolder. ins. desf. }
  { intros l _. left. exists (InitEvent l).
    split; [now apply (rsr_init_acts INV') |].
    rewrite rsr_mapper_init; auto. }
  { simpl. unfold lab_s_'; desf; [| tauto].
    ins. rewrite updo by (destruct b_t; desf).
    unfold compose, mapper_inv.
    rewrite rsr_mapper_init; auto.
    apply WF_t. }
  { simpl.
    rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep INV).
    basic_solver. }
  { simpl.
    rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep INV).
    basic_solver. }
  simpl. intros e [EIN | EX].
  { apply (wf_threads (rsr_imm_Gs_wf)).
    simpl. auto. }
  apply extra_a_some in EX; auto. subst e.
  now apply (wf_threads WF_t).
Admitted.

Hypothesis NLOC : A_s' ⊆₁ set_compl (Loc_t_' (WCore.lab_loc l_a)).
Hypothesis ARW : A_s' ⊆₁ WCore.lab_is_r l_a ∪₁ WCore.lab_is_w l_a.
Hypothesis ARLX : A_s' ⊆₁ fun _ => mode_le (WCore.lab_mode l_a) Orlx.

Lemma rsr_rex_a_rlx :
  A_s' ⊆₁ set_compl (Acq_s' ∪₁ Rel_s').
Proof using ARLX.
  clear - ARLX.
  unfold extra_a; desf.
  assert (RLX : mode_le (WCore.lab_mode l_a) Orlx).
  { apply (ARLX b_t), extra_a_some; desf. }
  unfolder in *. intros x XEQ. subst x.
  simpl. unfold lab_s_'. desf; [| tauto].
  unfold is_acq, is_rel, mod. rewrite upds.
  unfold WCore.lab_mode in RLX.
  destruct l_a; ins; desf.
  all: unfold is_true; apply and_not_or.
  all: split; congruence.
Qed.

Lemma rsr_rex_nsloc :
  A_s' ⊆₁ fun x => ~same_loc_s' a_t x.
Proof using NLOC INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  clear - NLOC NEQ.
  unfold extra_a; desf.
  unfolder in *. intros x XEQ. subst x.
  simpl. unfold lab_s_'. desf; [| tauto].
  unfold same_loc, loc.
  rewrite updo, upds by auto.
  unfold mapper_inv, compose.
  rewrite rsr_mapper_at; auto.
  apply NLOC, extra_a_some; desf.
Qed.

Lemma rsr_rex_wr :
  A_s' ⊆₁ R_s' ∪₁ W_s'.
Proof using ARW INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  clear - ARW NEQ.
  unfold extra_a; desf.
  unfolder in *. intros x XEQ. subst x.
  simpl. unfold lab_s_'. desf; [| tauto].
  unfold is_r, is_w.
  rewrite upds.
  unfold WCore.lab_is_r, WCore.lab_is_w in ARW.
  desf; eauto.
  destruct ARW with b_t; desf.
  now apply extra_a_some.
Qed.

Lemma rsr_b_rlx :
  E_s' ∩₁ eq a_t ⊆₁ set_compl (Acq_s' ∪₁ Rel_s').
Proof using INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. rewrite set_inter_union_l.
  arewrite (A_s' ∩₁ eq a_t ⊆₁ ∅).
  { unfold extra_a; desf; basic_solver. }
  rewrite set_union_empty_r.
  intros x (XIN & XEQ). subst x.
  red in XIN. unfolder.
  enough (RLX : ~ (is_rel lab_s'' a_t \/ is_acq lab_s'' a_t)).
  { unfold lab_s_'; desf; [| tauto].
    unfold is_acq, is_rel, mod.
    rewrite updo by congruence.
    tauto. }
  destruct XIN as (y & XIN & XEQ).
  simpl. unfold is_acq, is_rel, mod, compose.
  rewrite rsr_mapper_at; auto.
  apply (rsr_bt_rlx INV'). split; auto.
  enough (y = b_t) by congruence.
  now apply (rsr_mapper_inv_at _ NEQ).
Qed.

Lemma rsr_b_rw :
  E_s' ∩₁ eq a_t ⊆₁ R_s' ∪₁ W_s'.
Proof using INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. rewrite set_inter_union_l.
  arewrite (A_s' ∩₁ eq a_t ⊆₁ ∅).
  { unfold extra_a; desf; basic_solver. }
  rewrite set_union_empty_r.
  intros x (XIN & XEQ). subst x.
  red in XIN. unfolder.
  enough (RW : is_w lab_s'' a_t \/ is_r lab_s'' a_t).
  { unfold lab_s_'; desf; eauto.
    all: unfold is_r, is_w.
    all: rewrite updo by congruence.
    all: eauto. }
  destruct XIN as (y & XIN & XEQ).
  simpl. unfold is_r, is_w, compose.
  rewrite rsr_mapper_at; auto.
  apply (rsr_b_t_is_r_or_w INV'). split; auto.
  enough (y = b_t) by congruence.
  now apply (rsr_mapper_inv_at _ NEQ).
Qed.

Lemma rc_vf
    (ISR : R_s' a_s)
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t) :
  vf_s' ⨾ sb_s' ⨾ ⦗eq a_s⦘ ≡
    vf G_s'' ⨾ sb_s' ⨾ ⦗eq a_s⦘.
Proof using INV SIMREL.
  assert (RPOEX : codom_rel (⦗eq a_s⦘ ⨾ rpo_s') ≡₁ ∅).
  { split; auto with hahn.
    rewrite reord_rpo_emp; eauto.
    clear. basic_solver.
    all: admit. }
  assert (RPONA : rpo_s' ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆ id ↑ rpo G_s'').
  { apply reord_map_rpo with (a := a_t); auto.
    { now apply new_G_s_wf. }
    all: admit. }
  assert (SUBINIT : is_init ∩₁ E_s' ⊆₁ E_s'').
  { admit. }
  assert (SBLOCEX : codom_rel (⦗eq a_s⦘ ⨾ sb_s' ∩ same_loc_s') ≡₁ ∅).
  { admit. }
  assert (SBLOCA : sb_s' ∩ same_loc_s' ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆ id ↑ (sb G_s'' ∩ same_loc (lab G_s''))).
  { admit. }
  split; [| admit].
  seq_rewrite sbvf_as_rhb.
  arewrite (
    vf G_s'' ⨾ sb_s' ⨾ ⦗eq a_s⦘ ≡
      vf_rhb G_s'' ⨾ sb_s' ⨾ ⦗eq a_s⦘
  ).
  { admit. }
  arewrite (
    sb_s' ⨾ ⦗eq a_s⦘ ⊆
      ⦗E_s' \₁ eq a_s⦘ ⨾ sb_s' ⨾ ⦗eq a_s⦘
  ) at 1.
  { rewrite wf_sbE at 1.
    unfolder. intros x y (XIN & SB & YEQ & YIN).
    splits; auto. intro FALSO; desf.
    eapply sb_irr; eauto. }
  unfold vf_rhb. rewrite !seqA.
  arewrite (
    rhb_s'^? ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆
      ⦗E_s' \₁ eq a_s⦘ ⨾ rhb_s'^? ⨾ ⦗E_s' \₁ eq a_s⦘
  ).
  { rewrite !crE, !seq_union_l, !seq_union_r.
    apply union_mori; [basic_solver |].
    apply XmmCons.read_rhb_start
      with (m := id) (G_t := G_s'') (drf := fake_srf G_s'' a_s (lab_s' a_s)).
    all: eauto using new_G_s_wf.
    all: admit. }
  arewrite (
    rf_s'^? ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆
      ⦗E_s' \₁ eq a_s⦘ ⨾ (rf G_s'')^?
  ).
  { admit. }
  arewrite (
    ⦗E_s'⦘ ⨾ ⦗W_s'⦘ ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆
      ⦗E_s''⦘ ⨾ ⦗W_s''⦘
  ).
  { admit. }
  arewrite (
    rhb_s'^? ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆
      (rhb G_s'')^? ⨾ ⦗E_s' \₁ eq a_s⦘
  ); [| do 3 (apply seq_mori; auto with hahn); basic_solver 7].
  rewrite !crE, !seq_union_l.
  apply union_mori; [reflexivity |].
  transitivity (rhb_s' ⨾ ⦗E_s' \₁ eq a_s⦘ ⨾ ⦗E_s' \₁ eq a_s⦘ ).
  { clear. basic_solver. }
  rewrite <- seqA.
  rewrite XmmCons.read_rhb_sub
      with (m := id) (G_t := G_s'') (drf := fake_srf G_s'' a_s (lab_s' a_s)).
  all: auto.
  { now rewrite collect_rel_id. }
Admitted.

Lemma reexec_simrel :
  reord_simrel X_s' X_t' a_t b_t mapper.
Proof using INV.
  assert (EQ : a_t <> b_t) by apply INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  assert (EXAR : eq b_t ∩₁ R_s' ≡₁ eq b_t ∩₁ WCore.lab_is_r (lab_s' a_s)).
  { unfold a_s, is_r, WCore.lab_is_r.
    unfolder; split; ins; desf. }
  assert (SRF :
    fake_srf G_s'' a_s (lab_s' a_s) ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s)⦘ ≡
    srf_s' ⨾ ⦗extra_a X_t' a_t b_t b_t ∩₁ R_s'⦘
  ).
  { unfold extra_a; desf; [desf | basic_solver 11].
    rewrite EXAR, <- fake_srf_is_srf with (G_s := G_s'').
    all: ins.
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { apply rc_vf; auto.
      admit. }
    admit. }
  constructor; ins.
  { apply mapinj. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { rewrite <- SRF. admit. }
  { admit. }
Admitted.

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
Definition f' := (mapper ∘ f_t) ∘ mapper_inv.

Lemma extra_d_in_E_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  extra_d ⊆₁ E_s.
Proof using.
  unfold extra_d. desf.
  transitivity (mapper ↑₁ E_t);
    [| admit].
  rewrite <- (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
  assert (INA : E_t' a_t).
  { now apply (WCore.reexec_embd_dom GREEXEC). }
  assert (NEQ : a_t <> b_t) by admit.
  arewrite (
    eq a_s ≡₁ mapper ↑₁ (f_t ↑₁ eq a_t)
  ).
  { admit. }
  do 2 (apply set_collect_mori; auto).
  basic_solver.
Admitted.

Lemma dtrmt_in_E_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  dtrmt' ⊆₁ E_s.
Proof using.
  unfold dtrmt'.
  arewrite (dtrmt_t \₁ extra_b ⊆₁ dtrmt_t).
  { basic_solver. }
  rewrite extra_d_in_E_s, (rexec_dtrmt_in_start GREEXEC); eauto.
  apply set_subset_union_l; split; [| reflexivity].
Admitted.

Lemma extra_d_cmt
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  extra_d ⊆₁ cmt'.
Proof using.
Admitted.

Lemma reexec_threads_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  WCore.reexec_thread X_s' dtrmt' ≡₁
    WCore.reexec_thread X_t' dtrmt_t ∪₁ tid ↑₁ A_s'.
Proof using.
  assert (NEQ : a_t <> b_t) by admit.
  assert (TEQ : tid a_t = tid b_t) by admit.
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
    { admit. }
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
Admitted.

Lemma reexec_thread_mapper
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  mapper ↑₁ (tid ↓₁ WCore.reexec_thread X_t' dtrmt_t) ≡₁
    tid ↓₁ WCore.reexec_thread X_t' dtrmt_t.
Proof using.
  assert (NEQ : a_t <> b_t) by admit.
  assert (TID : tid a_t = tid b_t) by admit.
  eapply rsr_setE_iff; eauto.
  destruct classic
      with ((tid ↓₁ WCore.reexec_thread X_t' dtrmt_t) a_t)
        as [INA|NINA].
  all: unfolder; rewrite <- TID; auto.
Admitted.

Lemma reexec_acts_s_helper
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  A_s ⊆₁ tid ↓₁ WCore.reexec_thread X_t' dtrmt_t ∪₁
            tid ↓₁ (tid ↑₁ A_s').
Proof using.
  assert (TEQ : tid a_t = tid b_t) by admit.
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
Admitted.

Lemma reexec_acts_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  E_s ≡₁ dtrmt' ∪₁ E_s ∩₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt'.
Proof using.
  assert (NEQ : a_t <> b_t) by admit.
  assert (TID : tid a_t = tid b_t) by admit.
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
Admitted.

Lemma reexec_extra_a_ncmt
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  extra_a X_t' a_t b_t b_t ⊆₁ set_compl cmt'.
Proof using.
  assert (NEQ : a_t <> b_t) by admit.
  unfold extra_a, cmt'. desf.
  unfolder. ins. desf.
  intros (y & CMT & MAP).
  assert (YIN : E_t' y).
  { now apply (WCore.reexec_embd_dom GREEXEC). }
  enough (E_t' a_t) by desf.
  erewrite <- (rsr_mapper_inv_bt _ NEQ); eauto.
Admitted.

Lemma dtrmt_in_cmt
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  dtrmt' ⊆₁ cmt'.
Proof using.
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
Proof using.
  assert (NINIT : ~is_init b_t) by admit.
  assert (IMM :
    (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⊆
      immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘
  ).
  { transitivity (
      ⦗set_compl is_init⦘ ⨾ (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⨾ ⦗eq a_t⦘
    ); [basic_solver |].
    (* rewrite (rsr_at_bt_imm (rc_inv_end CTX)).
    unfold nin_sb. basic_solver. *)
    admit. }
  intros x y HREL.
  exists x. split; [| apply HREL]. unfolder.
  split; auto.
  destruct HREL as (a' & SB & EQ).
  unfolder in EQ; desf.
  assert (INA : E_t' a_t).
  { enough (SB' : sb_t' x a_t).
    { hahn_rewrite wf_sbE in SB'.
      forward apply SB'. clear. basic_solver. }
    unfold nin_sb in SB.
    forward apply SB. basic_solver. }
  assert (INB : E_t' b_t).
  {
    (* now apply (rsr_at_bt_ord (rc_inv_end CTX)).  *)
    admit.
    }
  eapply nin_sb_functional_l with (G := G_t').
  { admit. }
  { unfold transp.
    enough (SB' : (immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘) b_t a_t).
    { forward apply SB'. basic_solver. }
    apply (IMM b_t a_t). basic_solver. }
  unfold transp. auto.
Admitted.

Lemma imm_sb_d_s_from_b_helper :
  ⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⊆
    ⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘.
Proof using.
  assert (NINIT : ~is_init b_t) by admit.
  assert (IMM :
    (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⊆
      immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘
  ).
  { transitivity (
      ⦗set_compl is_init⦘ ⨾ (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⨾ ⦗eq a_t⦘
    ); [basic_solver |].
    (* rewrite (rsr_at_bt_imm (rc_inv_end CTX)).
    unfold nin_sb. basic_solver. *)
    admit.
     }
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
  { exfalso. admit.
  (* eapply (rsr_bt_max (rc_inv_end CTX)); eauto.
    enough (SB : sb_t' b_t y).
    { unfolder. splits; eauto. }
    forward apply HREL. clear.
    unfold nin_sb. basic_solver.  *)
    }
  assert (INA : E_t' a_t) by tauto. clear INA'.
  destruct HREL as (a' & EQ & SB).
  unfolder in EQ; desf.
  eapply nin_sb_functional_r with (G := G_t').
  { admit. }
  { unfold transp.
    enough (SB' : (immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘) b_t a_t).
    { forward apply SB'. basic_solver. }
    apply (IMM b_t a_t). basic_solver. }
  auto.
Admitted.

Lemma imm_sb_d_s
    (GREEXEC : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle) :
  ⦗dtrmt'⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗cmt'⦘ ⊆
    ⦗dtrmt'⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗dtrmt'⦘.
Proof using.
  assert (NB : ~is_init b_t) by admit.
  assert (NEQ : a_t <> b_t) by admit.
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
    { admit. }
    assert (BDA : dtrmt_t b_t).
    { eapply rexec_dtrmt_sb_dom; eauto.
      exists a_t; unfolder. split; auto.
      unfold sb; unfolder; splits; auto.
      admit. }
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
    { admit. }
    assert (SBA : immediate (nin_sb G_t') b_t a_t).
    { unfold nin_sb.
      enough (SB : immediate sb_t' b_t a_t).
      { apply seq_eqv_imm. forward apply SB. basic_solver. }
      (* apply (rsr_at_bt_imm (rc_inv_end CTX)). basic_solver. *)
      admit. }
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
    { admit. }
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
Admitted.

Lemma reexec_step :
  WCore.reexec X_s X_s' f' dtrmt' cmt'.
Proof using.
  assert (NEQ : a_t <> b_t).
  { admit. }
  assert (GREEXEC :
    WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle
  ).
  { admit. }
  assert (MEQA : mapper a_t = b_t).
  { unfold mapper.
    rewrite updo, upds; [done |].
    admit. }
  assert (INJHELPER : inj_dom (codom_rel (⦗E_t' \₁ dtrmt_t⦘ ⨾ rf_t') ∪₁ dom_rel rhb_t'^?) mapper).
  { eapply inj_dom_mori; eauto with xmm.
    red. auto with hahn. }
  assert (EXNCMT : extra_a X_t' a_t b_t b_t ∩₁ cmt' ≡₁ ∅).
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
              mapper_inv_r_inv,
              Combinators.compose_id_right.
      all: auto.
      eapply fixset_mori; auto; try now apply GREEXEC.
      clear. red. basic_solver. }
    unfold extra_d. desf. unfold a_s.
    unfolder. unfold compose. ins. desf.
    unfold mapper_inv.
    rewrite (rsr_mapper_bt NEQ).
    admit. }
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
      change (mapper_inv (mapper x)) with ((mapper_inv ∘ mapper) x).
      change (mapper_inv (mapper y)) with ((mapper_inv ∘ mapper) y).
      rewrite !mapper_inv_r_inv; auto; unfold id; intro EQf.
      enough (EQxy: x = y); [by rewrite EQxy|].
      apply (WCore.reexec_embd_inj (WCore.reexec_embd_corr GREEXEC)); auto.
      (* apply (rsr_inj (rc_simrel CTX)).
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      done. *)
      admit. }
    { intros e CMT.
      change (tid (f' e)) with ((tid ∘ f') e).
      unfold f'.
      rewrite <- !Combinators.compose_assoc.
      change ((tid ∘ mapper ∘ f_t ∘ mapper_inv) e)
        with ((tid ∘ mapper) ((f_t ∘ mapper_inv) e)).
      unfold cmt' in CMT. unfolder in CMT.
      destruct CMT as (e' & CMT & EQ); subst e.
      assert (INE : E_t ((f_t ∘ mapper_inv) (mapper e'))).
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
        unfolder. exists e'. split; auto.
        change ((f_t ∘ mapper_inv) (mapper e'))
          with (f_t ((mapper_inv ∘ mapper) e')).
        (* rewrite mapper_inv_r_inv; [now unfold id | admit].i *)
        admit. }
      rewrite (rsr_tid SIMREL); auto.
      unfold compose.
      admit. }
    { intros e CMT.
      change (lab_s (f' e)) with ((lab_s ∘ f') e).
      unfold f'.
      rewrite <- !Combinators.compose_assoc.
      unfold cmt' in CMT. unfolder in CMT.
      destruct CMT as (e' & CMT & EQ); subst e.
      change ((lab_s ∘ mapper ∘ f_t ∘ mapper_inv) (mapper e'))
        with ((lab_s ∘ mapper) ((f_t ∘ (mapper_inv ∘ mapper)) e')).
      change (lab_s' (mapper e')) with ((lab_s' ∘ mapper) e').
      rewrite mapper_inv_r_inv by apply CTX.
      arewrite (f_t ∘ id = f_t) by done.
      (* rewrite (rsr_lab (rc_simrel CTX));
        [| apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver].
      rewrite (rsr_lab (reexec_simrel CTX));
        [| apply (WCore.reexec_embd_dom GREEXEC); auto].
      now apply GREEXEC.  *)
      admit. }
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
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f_t ∘ id = f_t) by done.
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
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f_t ∘ id = f_t) by done.
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
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f_t ∘ id = f_t) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_rmw (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_rmw SIMREL); auto with hahn. }
    unfold cmt', f'.
    rewrite <- !set_collect_compose.
    rewrite Combinators.compose_assoc.
    rewrite mapper_inv_r_inv; auto.
    rewrite Combinators.compose_assoc.
    arewrite (f_t ∘ id = f_t) by done.
    rewrite set_collect_compose.
    rewrite (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
    rewrite (rsr_acts SIMREL); auto with hahn. }
  { apply (G_s_rfc INV' reexec_simrel). }
  { exact WF_START. (* wf start *) }
  { admit. (* Consistency *) }
  { eapply reexec_acts_s; eauto. }
  apply sub_to_full_exec_listless
   with (thrdle := thrdle).
  { exact WF_START. }
  { eapply G_s_rfc with (X_t := X_t').
    { admit. }
    now apply reexec_simrel. }
  { admit. }
  { admit. (* difference between acts and dtrmt is fin *) }
  { admit. (* Prefix. Trivial? *) }
  { eapply G_s_wf with (X_t := X_t').
    { admit. }
    now apply reexec_simrel. }
  { admit. (* init acts *) }
  (* { now rewrite (rc_data CTX), (rsr_ndata INV'). }
  { now rewrite (rc_addr CTX), (rsr_naddr INV'). }
  { now rewrite (rc_ctrl CTX), (rsr_nctrl INV'). }
  { now rewrite (rc_rmw_dep CTX), (rsr_nrmw_dep (rc_inv_end CTX)). }
  ins. *)
Admitted.

End ReorderingReexec.