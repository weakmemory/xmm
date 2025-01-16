Require Import ReordSimrel ReorderingEq ReorderingMapper.
Require Import AuxDef.
Require Import Core.
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

Module ReorderingReexecInternal.

Section ReorderingReexecInternal.

Variable X_t X_t' X_s X_s' : WCore.t.
Variable a_t b_t : actid.
Variable l_a : label.
Variable f : actid -> actid.
Variable dtrmt cmt : actid -> Prop.

Notation "'R' G" := (fun e => is_true (is_r (lab G) e)) (at level 1).
Notation "'F' G" := (fun e => is_true (is_f (lab G) e)) (at level 1).
Notation "'W' G" := (fun e => is_true (is_w (lab G) e)) (at level 1).
Notation "'Acq' G" := (fun e => is_true (is_acq (lab G) e)) (at level 1).
Notation "'Rlx' G" := (fun e => is_true (is_rlx (lab G) e)) (at level 1).
Notation "'Rel' G" := (fun e => is_true (is_rel (lab G) e)) (at level 1).

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_t''" := (WCore.G X_t').
Notation "'G_s'" := (WCore.G X_s).
Notation "'G_s''" := (WCore.G X_s').

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
Notation "'F_s'" := (F G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (Rlx G_s).
Notation "'Acq_s'" := (Acq G_s).
Notation "'Rel_s'" := (Rel G_s).

Notation "'lab_s''" := (lab G_s').
Notation "'val_s''" := (val lab_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'same_loc_s''" := (same_loc lab_s').
Notation "'same_val_s''" := (same_val lab_s').
Notation "'E_s''" := (acts_set G_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'sb_s''" := (sb G_s').
Notation "'rf_s''" := (rf G_s').
Notation "'co_s''" := (co G_s').
Notation "'rmw_s''" := (rmw G_s').
Notation "'rpo_s''" := (rpo G_s').
Notation "'rmw_dep_s''" := (rmw_dep G_s').
Notation "'data_s''" := (data G_s').
Notation "'ctrl_s''" := (ctrl G_s').
Notation "'addr_s''" := (addr G_s').
Notation "'hb_s''" := (hb G_s').
Notation "'rhb_s''" := (rhb G_s').
Notation "'eco_s''" := (eco G_s').
Notation "'W_s''" := (fun x => is_true (is_w lab_s' x)).
Notation "'R_s''" := (fun x => is_true (is_r lab_s' x)).
Notation "'F_s''" := (F G_s').
Notation "'vf_s''" := (vf G_s').
Notation "'srf_s''" := (srf G_s').
Notation "'Loc_s_'' l" := (fun e => loc_s' e = l) (at level 1).
Notation "'Val_s_'' l" := (fun e => val_s' e = l) (at level 1).
Notation "'Rlx_s''" := (Rlx G_s').
Notation "'Acq_s''" := (Acq G_s').
Notation "'Rel_s''" := (Rel G_s').

Notation "'mapper'" := (mapper a_t b_t).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'A_s'" := (extra_a X_t a_t b_t b_t).
Notation "'A_s''" := (extra_a X_t' a_t b_t b_t).

(* Id aliases for better readability *)
Definition a_s := b_t.
Definition b_s := a_t.

Definition mapper_inv := mapper.

Definition G_s'' : execution := {|
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

Definition lab_s_' :=
  ifP ~E_t' a_t /\ E_t' b_t then upd (lab_t' ∘ mapper_inv) b_t l_a
  else (lab_t' ∘ mapper).

Record reexec_conds : Prop := {
  rc_simrel : reord_simrel X_s X_t a_t b_t mapper;
  rc_step : WCore.reexec X_t X_t' f dtrmt cmt;
  rc_inv_start : reord_step_pred X_t a_t b_t;
  rc_inv_end : reord_step_pred X_t' a_t b_t;
  rc_end_cons : WCore.is_cons G_t' ∅₂;
  (**)
  rc_as : A_s' ⊆₁ extra_a_pred X_s' a_t b_t;
  rc_extra_lab : fake_srf G_s'' a_s (lab_s' a_s) ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s)⦘ ⊆ same_val_s';
  rc_lab : lab_s' = lab_s_';
  rc_acts : E_s' ≡₁ mapper ↑₁ E_t' ∪₁ extra_a X_t' a_t b_t a_s;
  rc_rf : rf_s' ≡ mapper ↑ rf_t' ∪ fake_srf G_s'' a_s (lab_s' a_s) ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s)⦘;
  rc_co : co_s' ≡ mapper ↑ co_t' ∪
          add_max
            (extra_co_D (mapper ↑₁ E_t') lab_s' (WCore.lab_loc (lab_s' a_s)))
            (A_s' ∩₁ WCore.lab_is_w (lab_s' a_s));
  rc_rmw : rmw_s' ≡ mapper ↑ rmw_t';
  rc_threads : threads_set G_s' ≡₁ threads_set G_t';
  rc_ctrl : ctrl_s' ≡ ctrl_t';
  rc_data : data_s' ≡ data_t';
  rc_addr : addr_s' ≡ addr_t';
  rc_rmw_dep : rmw_dep_s' ≡ rmw_dep_t';
  rc_f_b_t : forall (ACMT : cmt b_t), f b_t = b_t;
  rc_f_a_t : forall (ACMT : cmt a_t), f a_t = a_t;
}.

Lemma mapinj
    (NEQ : a_t <> b_t) :
  inj_dom E_t' mapper.
Proof using.
  eapply inj_dom_mori; eauto with xmm.
  red; auto with hahn.
Qed.

Lemma mapinj_inv'
    (NEQ : a_t <> b_t) :
  inj_dom ⊤₁ mapper_inv.
Proof using.
  unfold mapper_inv. auto with xmm.
Qed.

Lemma mapinj_inv
    (NEQ : a_t <> b_t) :
  inj_dom E_t' mapper_inv.
Proof using.
  eapply inj_dom_mori; eauto using mapinj_inv'.
  red. auto with hahn.
Qed.

Lemma mapper_inv_l_inv
    (NEQ : a_t <> b_t) :
  mapper ∘ mapper_inv = id.
Proof using.
  unfold mapper_inv. now apply rsr_mapper_compose.
Qed.

Lemma mapper_inv_r_inv
    (NEQ : a_t <> b_t) :
  mapper_inv ∘ mapper = id.
Proof using.
  unfold mapper_inv. now apply rsr_mapper_compose.
Qed.

Lemma new_G_s_wf
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t)
    (CTX : reexec_conds) :
  Wf G_s'.
Proof using.
Admitted.

Lemma rc_vf
    (ISR : R_s' a_s)
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t)
    (CTX : reexec_conds) :
  vf_s' ⨾ sb_s' ⨾ ⦗eq a_s⦘ ≡
    vf G_s'' ⨾ sb_s' ⨾ ⦗eq a_s⦘.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  assert (EQE : acts_set G_s'' ≡₁ E_s' \₁ eq a_s).
  { admit. }
  assert (SUB : sub_execution G_s' G_s'' ∅₂ ∅₂).
  { admit. }
  assert (RF :
    rf_s' ≡
      id ↑ rf G_s'' ∪
      fake_srf G_s'' a_s (lab_s' a_s) ⨾ ⦗eq a_s⦘
  ).
  { rewrite collect_rel_id, (rc_rf CTX).
    apply union_more; [reflexivity |].
    rewrite extra_a_some; auto.
    unfold WCore.lab_is_r, is_r in *.
    clear - ISR. basic_solver. }
  assert (INJ : inj_dom (acts_set G_s'') id).
  { clear. basic_solver. }
  assert (ACTS : E_s' ≡₁ id ↑₁ acts_set G_s'' ∪₁ eq a_s).
  { rewrite (rc_acts CTX), extra_a_some; eauto.
    clear. rewrite set_collect_id. basic_solver. }
  assert (DISJ : set_disjoint (id ↑₁ acts_set G_s'') (eq a_s)).
  { rewrite set_collect_id, EQE.
    clear. basic_solver. }
  assert (NACQ : ~is_acq lab_s' a_s).
  { apply CTX. now apply extra_a_some. }
  assert (CO : co_s' ≡ id ↑ co G_s'').
  { rewrite collect_rel_id, (rc_co CTX).
    rewrite extra_a_some; auto.
    arewrite (eq b_t ∩₁ WCore.lab_is_w (lab_s' a_s) ≡₁ ∅).
    { unfold WCore.lab_is_w, is_r in *.
      clear - ISR. basic_solver. }
    rewrite add_max_empty_r, union_false_r.
    reflexivity. }
  assert (NINA' : ~(acts_set G_s'') a_s).
  { simpl. unfold a_s. intros (x & XIN & FALSO).
    enough (x = a_t) by desf.
    now apply (rsr_mapper_inv_bt _ NEQ). }
  assert (LAB : eq_dom (acts_set G_s'') lab_s' (lab G_s'')).
  { rewrite (rc_lab CTX). unfold lab_s_'; desf.
    unfolder. ins. unfold mapper_inv.
    now rewrite updo by (unfold a_s in NINA'; congruence). }
  assert (RPOEX : codom_rel (⦗eq a_s⦘ ⨾ rpo_s') ≡₁ ∅).
  { admit. }
  assert (RPONA : rpo_s' ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆ id ↑ rpo G_s'').
  { admit. }
  assert (RMW : rmw_s' ≡ id ↑ rmw G_s'').
  { rewrite collect_rel_id, (rc_rmw CTX). reflexivity. }
  assert (SBLOCEX : codom_rel (⦗eq a_s⦘ ⨾ sb_s' ∩ same_loc_s') ≡₁ ∅).
  { admit. }
  assert (SBLOCA : sb_s' ∩ same_loc_s' ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆ id ↑ (sb G_s'' ∩ same_loc (lab G_s''))).
  { admit. }
  split; [| rewrite (sub_vf_in SUB); reflexivity].
  seq_rewrite sbvf_as_rhb.
  arewrite (
    vf G_s'' ⨾ sb_s' ⨾ ⦗eq a_s⦘ ≡
      vf_rhb G_s'' ⨾ sb_s' ⨾ ⦗eq a_s⦘
  ).
  { rewrite vf_as_rhb, !seq_union_l.
    split; [| auto with hahn].
    apply inclusion_union_l; [reflexivity |].
    unfold vf_rhb. rewrite !seqA.
    rewrite (sub_sb SUB), !seqA.
    arewrite (
      ⦗acts_set G_s''⦘ ⨾ sb_s' ⨾ ⦗acts_set G_s''⦘ ⨾ sb_s' ⊆
        sb_s' ⨾ sb_s'
    ) by basic_solver.
    sin_rewrite sb_sb.
    clear. basic_solver 11. }
  arewrite (
    sb_s' ⨾ ⦗eq a_s⦘ ⊆
      ⦗E_s' \₁ eq a_s⦘ ⨾ sb_s' ⨾ ⦗eq a_s⦘
  ) at 1.
  { rewrite wf_sbE at 1.
    unfolder. intros x y (XIN & SB & YEQ & YIN).
    splits; auto.
    intro FALSO; desf.
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
    all: auto.
    { eapply sub_WF; eauto using new_G_s_wf.
      admit. }
    eapply new_G_s_wf; eauto. }
  arewrite (
    rf_s'^? ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆
      ⦗E_s' \₁ eq a_s⦘ ⨾ (rf G_s'')^?
  ).
  { admit. }
  arewrite (
    ⦗E_s'⦘ ⨾ ⦗W_s'⦘ ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆
      ⦗acts_set G_s''⦘ ⨾ ⦗W G_s''⦘
  ).
  { admit. }
  arewrite (
    rhb_s'^? ⨾ ⦗E_s' \₁ eq a_s⦘ ⊆
      (rhb G_s'')^? ⨾ ⦗E_s' \₁ eq a_s⦘
  ); [| do 3 (apply seq_mori; auto with hahn); basic_solver 7].
  rewrite !crE, !seq_union_l.
  apply union_mori; [reflexivity |].
  rewrite XmmCons.read_rhb_sub
      with (m := id) (G_t := G_s'') (drf := fake_srf G_s'' a_s (lab_s' a_s)).
  all: auto.
  { rewrite collect_rel_id.
    admit. }
  { eapply sub_WF; eauto using new_G_s_wf.
    admit. }
  eapply new_G_s_wf; eauto.
Admitted.

Lemma reexec_simrel
    (CTX : reexec_conds) :
  reord_simrel X_s' X_t' a_t b_t mapper.
Proof using.
  assert (EQ : a_t <> b_t) by apply CTX.
  assert (TEQ : tid a_t = tid b_t) by apply CTX.
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
    { unfold fake_sb, G_s'', sb. ins.
      rewrite (rc_acts CTX), extra_a_some; auto. }
    { unfold G_s''.
      intros (x & XIN & XEQ). enough (x = a_t); desf.
      eapply rsr_mapper_inv_bt; eauto. }
    { rewrite (rc_lab CTX).
      unfold lab_s_'; desf; [| exfalso; eauto].
      now unfold a_s; rewrite upds. }
    { apply rc_vf; auto.
      admit. }
    rewrite (rc_co CTX), seq_union_l.
    rewrite extra_a_some; auto.
    rewrite add_max_seq_r, set_interC, set_interA.
    arewrite (eq a_s ∩₁ mapper ↑₁ E_t' ≡₁ ∅).
    { split; [| basic_solver]. unfold a_s.
      intros x (XEQ & y & YIN & YEQ). enough (y = a_t); desf.
      eapply rsr_mapper_inv_bt; eauto. }
    rewrite set_inter_empty_r, add_max_empty_r.
    now rewrite union_false_r. }
  constructor; ins.
  all: try now apply CTX.
  { apply mapinj. apply CTX. }
  { rewrite (rc_acts CTX), set_minus_union_l.
    unfold a_s. rewrite set_minusK, set_union_empty_r.
    unfold extra_a; desf; [| clear; basic_solver].
    rewrite set_minus_disjoint; auto with hahn.
    unfolder. intros x (y & YIN & YEQ) XEQ. desf.
    enough (y = a_t); desf. eapply rsr_mapper_inv_bt; eauto. }
  { eapply eq_dom_mori; eauto with xmm.
    red. auto with hahn. }
  { rewrite (rc_lab CTX). unfold lab_s_'. desf.
    { rewrite <- rsr_mapper_at with (a_t := a_t) (b_t := b_t) at 1.
      all: auto.
      rewrite <- upd_compose; eauto with xmm.
      rewrite Combinators.compose_assoc, mapper_inv_r_inv,
              Combinators.compose_id_right; auto.
      unfolder. ins. rewrite updo; auto.
      desf. congruence. }
    rewrite Combinators.compose_assoc, rsr_mapper_compose,
            Combinators.compose_id_right; auto.
    reflexivity. }
  { admit. }
  { rewrite <- SRF, (rc_rf CTX). auto. }
  { rewrite (rc_co CTX), (rc_acts CTX).
    apply union_more; auto.
    arewrite (WCore.lab_loc (lab_s' a_s) = loc_s' b_t).
    arewrite (A_s' ∩₁ W_s' ≡₁
              A_s' ∩₁ WCore.lab_is_w (lab_s' a_s)).
    { unfold extra_a, a_s. desf; [| basic_solver].
      clear. unfold is_w, WCore.lab_is_w.
      unfolder. split; ins; desf. }
    destruct classic
        with (WCore.lab_is_w (lab_s' a_s) ≡₁ ∅)
          as [EMP | NEMP].
    { rewrite EMP, set_inter_empty_r.
      now rewrite !add_max_empty_r. }
    arewrite (WCore.lab_is_w (lab_s' a_s) ≡₁ ⊤₁).
    { unfold WCore.lab_is_w in *. desf. }
    rewrite set_inter_full_r,
            add_max_a with (A := extra_co_D (mapper ↑₁ E_t') lab_s' (loc_s' b_t)),
            add_max_a with (A := extra_co_D (mapper ↑₁ E_t' ∪₁ A_s') lab_s' (loc_s' b_t)).
    rewrite !extra_co_D_minus, set_minus_union_l.
    now rewrite set_minusK, set_union_empty_r. }
  { admit. (* rpo *) }
  { clear. unfold mapper. unfolder.
    ins. desf. now rewrite !updo by auto. }
  { clear. unfold mapper. unfolder.
    ins. desf. now rewrite upds. }
  clear - CTX. unfold mapper. unfolder.
  ins. desf. rewrite updo, upds; [done |].
  apply CTX.
Admitted.

Definition extra_b :=
  ifP ~dtrmt a_t /\ dtrmt b_t then eq b_t
  else ∅.
Definition extra_d :=
  ifP
    ~cmt b_t /\
    cmt a_t /\
    ~dtrmt a_t /\
    dom_rel (immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘) ⊆₁ dtrmt
  then eq a_s
  else ∅.
Definition cmt' := mapper ↑₁ cmt.
Definition dtrmt' := mapper ↑₁ (dtrmt \₁ extra_b) ∪₁ extra_d.
Definition f' := (mapper ∘ f) ∘ mapper_inv.

Lemma extra_d_in_E_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  extra_d ⊆₁ E_s.
Proof using.
  unfold extra_d. desf.
  transitivity (mapper ↑₁ E_t);
    [| rewrite (rsr_acts (rc_simrel CTX)); basic_solver].
  rewrite <- (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
  assert (INA : E_t' a_t).
  { now apply (WCore.reexec_embd_dom GREEXEC). }
  assert (NEQ : a_t <> b_t) by apply CTX.
  arewrite (
    eq a_s ≡₁ mapper ↑₁ (f ↑₁ eq a_t)
  ).
  { unfold a_s. rewrite set_collect_eq.
    rewrite (rc_f_a_t CTX); desf.
    rewrite set_collect_eq, rsr_mapper_at.
    all: auto with hahn. }
  do 2 (apply set_collect_mori; auto).
  basic_solver.
Qed.

Lemma dtrmt_in_E_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  dtrmt' ⊆₁ E_s.
Proof using.
  unfold dtrmt'.
  arewrite (dtrmt \₁ extra_b ⊆₁ dtrmt).
  { basic_solver. }
  rewrite extra_d_in_E_s, (rexec_dtrmt_in_start GREEXEC); eauto.
  apply set_subset_union_l; split; [| reflexivity].
  rewrite (rsr_acts (rc_simrel CTX)); auto with hahn.
Qed.

Lemma extra_d_cmt thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  extra_d ⊆₁ cmt'.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  unfold extra_d, cmt', a_s; desf.
  rewrite <- (rsr_mapper_at NEQ) at 1.
  rewrite <- set_collect_eq.
  apply set_collect_mori; basic_solver.
Qed.

Lemma reexec_threads_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  WCore.reexec_thread X_s' dtrmt' ≡₁
    WCore.reexec_thread X_t' dtrmt ∪₁ tid ↑₁ A_s'.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  assert (TEQ : tid a_t = tid b_t) by apply CTX.
  unfold WCore.reexec_thread, dtrmt'.
  rewrite (rsr_acts (reexec_simrel CTX)).
  rewrite set_minus_union_l, set_collect_union.
  arewrite (
    A_s' \₁ (mapper ↑₁ (dtrmt \₁ extra_b) ∪₁ extra_d) ≡₁ A_s'
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
    { now apply (rsr_at_bt_ord (rc_inv_end CTX)). }
    rewrite rsr_setE_iff; eauto.
    assert (ND : ~dtrmt b_t).
    { intro FALSO. enough (cmt b_t) by desf.
      now apply (WCore.dtrmt_cmt GREEXEC). }
    unfold extra_b; desf; [exfalso; tauto |].
    arewrite (dtrmt \₁ ∅ ≡₁ dtrmt) by basic_solver.
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
  arewrite (dtrmt \₁ ∅ ≡₁ dtrmt) by basic_solver.
  rewrite <- set_collect_minus;
    [| eapply inj_dom_mori; eauto with xmm; red; auto with hahn].
  rewrite <- set_collect_compose.
  rewrite set_collect_eq_dom with (g := tid); [reflexivity |].
  eapply eq_dom_mori; eauto with xmm.
  red; auto with hahn.
Qed.

Lemma reexec_thread_mapper thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  mapper ↑₁ (tid ↓₁ WCore.reexec_thread X_t' dtrmt) ≡₁
    tid ↓₁ WCore.reexec_thread X_t' dtrmt.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  assert (TID : tid a_t = tid b_t) by apply CTX.
  eapply rsr_setE_iff; eauto.
  destruct classic
      with ((tid ↓₁ WCore.reexec_thread X_t' dtrmt) a_t)
        as [INA|NINA].
  all: unfolder; rewrite <- TID; auto.
Qed.

Lemma reexec_acts_s_helper thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  A_s ⊆₁ tid ↓₁ WCore.reexec_thread X_t' dtrmt ∪₁
            tid ↓₁ (tid ↑₁ A_s').
Proof using.
  assert (TEQ : tid a_t = tid b_t) by apply CTX.
  unfold extra_a at 1; desf.
  assert (NDA : ~ dtrmt a_t).
  { intro FALSO. enough (E_t a_t) by desf.
    eapply rexec_dtrmt_in_start; eauto. }
  destruct classic with (dtrmt b_t) as [DB|NDB].
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

Lemma reexec_acts_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  E_s ≡₁ dtrmt' ∪₁ E_s ∩₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt'.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  assert (TID : tid a_t = tid b_t) by apply CTX.
  enough (SUB : E_s \₁ dtrmt' ⊆₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt').
  { split; [|
      rewrite (dtrmt_in_E_s GREEXEC CTX) at 1;
        basic_solver].
    rewrite set_union_minus
       with (s := E_s) (s' := dtrmt')
         at 1
         by eauto using dtrmt_in_E_s.
    rewrite <- SUB. basic_solver. }
  arewrite (E_s \₁ dtrmt' ⊆₁ E_s \₁ mapper ↑₁ (dtrmt \₁ extra_b)).
  { unfold dtrmt'. basic_solver. }
  rewrite reexec_threads_s; eauto.
  rewrite (rsr_acts (rc_simrel CTX)), set_minus_union_l.
  rewrite set_map_union.
  arewrite (
    A_s \₁ (mapper ↑₁ (dtrmt \₁ extra_b)) ≡₁ A_s
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

Lemma reexec_extra_a_ncmt thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  extra_a X_t' a_t b_t b_t ⊆₁ set_compl cmt'.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  unfold extra_a, cmt'. desf.
  unfolder. ins. desf.
  intros (y & CMT & MAP).
  assert (YIN : E_t' y).
  { now apply (WCore.reexec_embd_dom GREEXEC). }
  enough (E_t' a_t) by desf.
  erewrite <- (rsr_mapper_inv_bt _ NEQ); eauto.
Qed.

Lemma dtrmt_in_cmt thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  dtrmt' ⊆₁ cmt'.
Proof using.
  unfold dtrmt'.
  rewrite extra_d_cmt; eauto.
  apply set_subset_union_l. split; auto with hahn.
  unfold cmt'.
  apply set_collect_mori; auto.
  transitivity dtrmt; [basic_solver |].
  exact (WCore.dtrmt_cmt GREEXEC).
Qed.

Lemma imm_sb_d_s_refl_helper x :
  ⦗eq x⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq x⦘ ⊆ ∅₂.
Proof using.
  unfold nin_sb. rewrite immediateE.
  transitivity (⦗eq x⦘ ⨾ sb_t' ⨾ ⦗eq x⦘); [basic_solver|].
  unfolder. ins. desf. eapply sb_irr; eauto.
Qed.

Lemma imm_sb_d_s_to_a_helper
    (CTX : reexec_conds) :
  immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘ ⊆
    ⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘.
Proof using.
  assert (NINIT : ~is_init b_t) by apply CTX.
  assert (IMM :
    (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⊆
      immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘
  ).
  { transitivity (
      ⦗set_compl is_init⦘ ⨾ (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⨾ ⦗eq a_t⦘
    ); [basic_solver |].
    rewrite (rsr_at_bt_imm (rc_inv_end CTX)).
    unfold nin_sb. basic_solver. }
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
  { now apply (rsr_at_bt_ord (rc_inv_end CTX)). }
  eapply nin_sb_functional_l with (G := G_t').
  { apply CTX. }
  { unfold transp.
    enough (SB' : (immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘) b_t a_t).
    { forward apply SB'. basic_solver. }
    apply (IMM b_t a_t). basic_solver. }
  unfold transp. auto.
Qed.

Lemma imm_sb_d_s_from_b_helper
    (CTX : reexec_conds) :
  ⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⊆
    ⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘.
Proof using.
  assert (NINIT : ~is_init b_t) by apply CTX.
  assert (IMM :
    (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⊆
      immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘
  ).
  { transitivity (
      ⦗set_compl is_init⦘ ⨾ (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⨾ ⦗eq a_t⦘
    ); [basic_solver |].
    rewrite (rsr_at_bt_imm (rc_inv_end CTX)).
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
  { exfalso. eapply (rsr_bt_max (rc_inv_end CTX)); eauto.
    enough (SB : sb_t' b_t y).
    { unfolder. splits; eauto. }
    forward apply HREL. clear.
    unfold nin_sb. basic_solver. }
  assert (INA : E_t' a_t) by tauto. clear INA'.
  destruct HREL as (a' & EQ & SB).
  unfolder in EQ; desf.
  eapply nin_sb_functional_r with (G := G_t').
  { apply CTX. }
  { unfold transp.
    enough (SB' : (immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘) b_t a_t).
    { forward apply SB'. basic_solver. }
    apply (IMM b_t a_t). basic_solver. }
  auto.
Qed.

Lemma imm_sb_d_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  ⦗dtrmt'⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗cmt'⦘ ⊆
    ⦗dtrmt'⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗dtrmt'⦘.
Proof using.
  assert (NB : ~is_init b_t) by apply CTX.
  assert (NEQ : a_t <> b_t) by apply CTX.
  assert (NEQ' : b_t <> a_t) by congruence.
  rewrite rsr_sbE_imm
     with (X_s := X_s') (X_t := X_t') (a_t := a_t) (b_t := b_t).
  all: eauto using rc_inv_end, reexec_simrel.
  rewrite !seq_union_l, !seq_union_r.
  rewrite extra_sbE; eauto using rc_inv_end, reexec_simrel.
  seq_rewrite <- cross_inter_l.
  arewrite (dtrmt' ∩₁ extra_a X_t' a_t b_t b_t ≡₁ ∅).
  { split; [| auto with hahn].
    rewrite reexec_extra_a_ncmt, dtrmt_in_cmt; eauto.
    clear. basic_solver. }
  apply union_mori; [| basic_solver].
  destruct classic with (dtrmt a_t) as [AD | AND].
  { assert (ACMT : cmt a_t).
    { now apply (WCore.dtrmt_cmt GREEXEC). }
    assert (AIN : E_t a_t).
    { eapply rexec_dtrmt_in_start; eauto. }
    assert (BIN : E_t b_t).
    { now apply (rsr_at_bt_ord (rc_inv_start CTX)). }
    assert (BDA : dtrmt b_t).
    { eapply rexec_dtrmt_sb_dom; eauto.
      exists a_t; unfolder. split; auto.
      unfold sb; unfolder; splits; auto.
      apply (rsr_at_bt_sb (rc_inv_start CTX)). }
    assert (BCMT : cmt b_t).
    { now apply (WCore.dtrmt_cmt GREEXEC). }
    unfold cmt', dtrmt', extra_d, extra_b; desf; desf.
    rewrite set_union_empty_r.
    arewrite (dtrmt \₁ ∅ ≡₁ dtrmt) by basic_solver.
    do 2 (rewrite rsr_setE_iff; eauto).
    apply (WCore.dtrmt_sb_max GREEXEC). }
  destruct classic with (cmt a_t) as [AC | NAC].
  { assert (AIN : E_t' a_t).
    { now apply (WCore.reexec_embd_dom GREEXEC). }
    assert (BIN : E_t' b_t).
    { now apply (rsr_at_bt_ord (rc_inv_end CTX)). }
    assert (SBA : immediate (nin_sb G_t') b_t a_t).
    { unfold nin_sb.
      enough (SB : immediate sb_t' b_t a_t).
      { apply seq_eqv_imm. forward apply SB. basic_solver. }
      apply (rsr_at_bt_imm (rc_inv_end CTX)). basic_solver. }
    assert (ND : ~dtrmt b_t).
    { intro FALSO. apply AND.
      eapply rexec_dtrmt_sbimm_codom; eauto.
      exists b_t. forward apply SBA. basic_solver 11. }
    unfold dtrmt', cmt', extra_b; desf; desf.
    arewrite (dtrmt \₁ ∅ ≡₁ dtrmt) by basic_solver.
    unfold extra_d; desf; [| rewrite set_union_empty_r].
    { unfold a_s. desf.
      rewrite rsr_setE_iff, rsr_setE_ex; eauto.
      rewrite !id_union, !seq_union_l, !seq_union_r.
      arewrite_false (⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘).
      { apply imm_sb_d_s_refl_helper. }
      arewrite_false (⦗eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt \₁ eq a_t⦘).
      { sin_rewrite (imm_sb_d_s_from_b_helper CTX).
        clear. basic_solver. }
      rewrite !union_false_r. apply inclusion_union_r. left.
      apply union_mori; [| reflexivity].
      arewrite (
        ⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt \₁ eq a_t⦘ ≡
        ⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt⦘ ⨾ ⦗cmt \₁ eq a_t⦘
      ).
      { clear. basic_solver. }
      sin_rewrite (WCore.dtrmt_sb_max GREEXEC).
      clear. basic_solver. }
    rewrite rsr_setE_iff; eauto.
    destruct classic with (cmt b_t) as [BC|NBC].
    { rewrite rsr_setE_iff; eauto.
      apply (WCore.dtrmt_sb_max GREEXEC). }
    assert (NBD :
      ~ dom_rel (immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘) ⊆₁ dtrmt
    ) by tauto.
    rewrite rsr_setE_ex, id_union, !seq_union_r; eauto.
    arewrite (
      ⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt \₁ eq a_t⦘ ≡
      ⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt⦘ ⨾ ⦗cmt \₁ eq a_t⦘
    ).
    { clear. basic_solver. }
    sin_rewrite (WCore.dtrmt_sb_max GREEXEC).
    apply inclusion_union_l; [basic_solver |].
    arewrite_false (⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘);
      [| basic_solver].
    enough (HH : dom_rel (⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq b_t⦘) ⊆₁ ∅).
    { forward apply HH. clear. basic_solver 7. }
    clear - CTX NBD. intros x1 (b' & HSET). apply NBD.
    intros x2 (b'' & IMMSB).
    assert (b' = b_t); desf.
    { forward apply HSET. clear. basic_solver. }
    assert (b'' = b_t); desf.
    { forward apply IMMSB. clear. basic_solver. }
    enough (EQ : x1 = x2).
    { subst x1. forward apply HSET. basic_solver. }
    eapply nin_sb_functional_l with (G := G_t').
    { apply CTX. }
    { forward apply HSET. clear. basic_solver. }
    forward apply IMMSB. clear. basic_solver. }
  destruct classic with (dtrmt b_t) as [DB|NDB].
  { assert (BC : cmt b_t).
    { now apply (WCore.dtrmt_cmt GREEXEC). }
    unfold dtrmt', cmt', extra_b, extra_d.
    desf; desf; rewrite set_union_empty_r.
    { rewrite rsr_setE_iff; eauto; [| unfolder; tauto].
      rewrite rsr_setE_niff; eauto.
      rewrite id_union, !seq_union_r.
      arewrite_false (⦗dtrmt \₁ eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘).
      { sin_rewrite (imm_sb_d_s_to_a_helper CTX).
        clear. basic_solver. }
      rewrite union_false_r.
      arewrite (
        ⦗dtrmt \₁ eq b_t⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt \₁ eq b_t⦘ ≡
        ⦗dtrmt \₁ eq b_t⦘ ⨾ ⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt⦘ ⨾ ⦗cmt \₁ eq b_t⦘
      ).
      { clear. basic_solver. }
      sin_rewrite (WCore.dtrmt_sb_max GREEXEC).
      clear. basic_solver. }
    exfalso. tauto. }
  destruct classic with (cmt b_t) as [CB|NCB].
  { unfold dtrmt', cmt', extra_b, extra_d.
    desf; desf.
    rewrite set_union_empty_r.
    arewrite (dtrmt \₁ ∅ ≡₁ dtrmt) by basic_solver.
    rewrite rsr_setE_iff; eauto.
    rewrite rsr_setE_niff; eauto.
    rewrite id_union, !seq_union_r.
    arewrite_false (⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗eq a_t⦘).
    { sin_rewrite (imm_sb_d_s_to_a_helper CTX).
      clear - NDB. basic_solver. }
    rewrite union_false_r.
    arewrite (
      ⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt \₁ eq b_t⦘ ≡
      ⦗dtrmt⦘ ⨾ immediate (nin_sb G_t') ⨾ ⦗cmt⦘ ⨾ ⦗cmt \₁ eq b_t⦘
    ).
    { clear. basic_solver. }
    sin_rewrite (WCore.dtrmt_sb_max GREEXEC).
    clear. basic_solver. }
  unfold dtrmt', cmt', extra_b, extra_d.
  desf; desf.
  rewrite set_union_empty_r.
  arewrite (dtrmt \₁ ∅ ≡₁ dtrmt) by basic_solver.
  do 2 (rewrite rsr_setE_iff; eauto).
  apply (WCore.dtrmt_sb_max GREEXEC).
Qed.

Lemma reexec_step
    (CTX : reexec_conds) :
  WCore.reexec X_s X_s' f' dtrmt' cmt'.
Proof using.
  assert (NEQ : a_t <> b_t).
  { apply CTX. }
  assert (GREEXEC :
    WCore.reexec X_t X_t' f dtrmt cmt
  ).
  { apply (rc_step CTX). }
  red in GREEXEC. destruct GREEXEC as (thrdle & GREEXEC).
  assert (MEQA : mapper a_t = b_t).
  { unfold mapper.
    rewrite updo, upds; [done |].
    apply CTX. }
  assert (INJHELPER : inj_dom (codom_rel (⦗E_t' \₁ dtrmt⦘ ⨾ rf_t') ∪₁ dom_rel rhb_t'^?) mapper).
  { eapply inj_dom_mori; eauto with xmm.
    red. auto with hahn. }
  assert (EXNCMT : extra_a X_t' a_t b_t b_t ∩₁ cmt' ≡₁ ∅).
  { split; vauto.
    rewrite (reexec_extra_a_ncmt GREEXEC CTX).
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
    rewrite (rc_f_a_t CTX); auto. }
  { unfold cmt'.
    rewrite (rc_acts CTX), (WCore.reexec_embd_dom GREEXEC).
    auto with hahn. }
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
      apply (rsr_inj (rc_simrel CTX)).
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      done. }
    { intros e CMT.
      change (tid (f' e)) with ((tid ∘ f') e).
      unfold f'.
      rewrite <- !Combinators.compose_assoc.
      change ((tid ∘ mapper ∘ f ∘ mapper_inv) e)
        with ((tid ∘ mapper) ((f ∘ mapper_inv) e)).
      unfold cmt' in CMT. unfolder in CMT.
      destruct CMT as (e' & CMT & EQ); subst e.
      assert (INE : E_t ((f ∘ mapper_inv) (mapper e'))).
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
        unfolder. exists e'. split; auto.
        change ((f ∘ mapper_inv) (mapper e'))
          with (f ((mapper_inv ∘ mapper) e')).
        rewrite mapper_inv_r_inv; [now unfold id | apply CTX]. }
      rewrite (rsr_tid (rc_simrel CTX)); auto.
      unfold compose.
      rewrite (WCore.reexec_embd_tid (WCore.reexec_embd_corr GREEXEC));
        [| change (mapper_inv (mapper e')) with ((mapper_inv ∘ mapper) e');
           rewrite mapper_inv_r_inv; [now unfold id | apply CTX]].
      change (mapper_inv (mapper e'))
        with ((mapper_inv ∘ mapper) e').
      rewrite mapper_inv_r_inv by apply CTX.
      unfold id.
      apply rsr_tid' with (X_s := X_s') (X_t := X_t')
                          (a_t := a_t) (b_t := b_t).
      { now apply reexec_simrel. }
      now apply (WCore.reexec_embd_dom GREEXEC). }
    { intros e CMT.
      change (lab_s (f' e)) with ((lab_s ∘ f') e).
      unfold f'.
      rewrite <- !Combinators.compose_assoc.
      unfold cmt' in CMT. unfolder in CMT.
      destruct CMT as (e' & CMT & EQ); subst e.
      change ((lab_s ∘ mapper ∘ f ∘ mapper_inv) (mapper e'))
        with ((lab_s ∘ mapper) ((f ∘ (mapper_inv ∘ mapper)) e')).
      change (lab_s' (mapper e')) with ((lab_s' ∘ mapper) e').
      rewrite mapper_inv_r_inv by apply CTX.
      arewrite (f ∘ id = f) by done.
      rewrite (rsr_lab (rc_simrel CTX));
        [| apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver].
      rewrite (rsr_lab (reexec_simrel CTX));
        [| apply (WCore.reexec_embd_dom GREEXEC); auto].
      now apply GREEXEC. }
    { admit. }
    { rewrite (rsr_rf (reexec_simrel CTX)),
              restr_union, collect_rel_union.
      arewrite_false (restr_rel cmt'
        (srf_s' ⨾ ⦗extra_a X_t' a_t b_t b_t ∩₁ R_s'⦘)).
      { rewrite restr_relE, !seqA, <- id_inter.
        rewrite (reexec_extra_a_ncmt GREEXEC CTX).
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
      arewrite (f ∘ id = f) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_rf (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_rf (rc_simrel CTX)); auto with hahn. }
    { rewrite (rsr_co (reexec_simrel CTX)),
              restr_union, collect_rel_union.
      arewrite_false (restr_rel cmt'
        (add_max (extra_co_D E_s' lab_s' (loc_s' b_t))
          (extra_a X_t' a_t b_t b_t ∩₁ W_s'))).
      { rewrite restr_add_max. unfold add_max.
        rewrite (reexec_extra_a_ncmt GREEXEC CTX) at 2.
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
      arewrite (f ∘ id = f) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_co (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_co (rc_simrel CTX)); auto with hahn. }
    { rewrite (rsr_rmw (reexec_simrel CTX)).
      unfold cmt', f'.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto with xmm;
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f ∘ id = f) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_rmw (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_rmw (rc_simrel CTX)); auto with hahn. }
    unfold cmt', f'.
    rewrite <- !set_collect_compose.
    rewrite Combinators.compose_assoc.
    rewrite mapper_inv_r_inv; auto.
    rewrite Combinators.compose_assoc.
    arewrite (f ∘ id = f) by done.
    rewrite set_collect_compose.
    rewrite (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
    rewrite (rsr_acts (rc_simrel CTX)); auto with hahn. }
  { exact WF_START. (* wf start *) }
  { admit. (* Consistency *) }
  { eapply reexec_acts_s; eauto. }
  apply sub_to_full_exec_listless
   with (thrdle := thrdle).
  { exact WF_START. }
  { eapply G_s_rfc with (X_t := X_t').
    { apply CTX. }
    now apply reexec_simrel. }
  { admit. }
  { admit. (* difference between acts and dtrmt is fin *) }
  { admit. (* Prefix. Trivial? *) }
  { eapply G_s_wf with (X_t := X_t').
    { apply CTX. }
    now apply reexec_simrel. }
  { admit. (* init acts *) }
  { admit. (* Unprovable SC *) }
  { now rewrite (rc_data CTX), (rsr_ndata (rc_inv_end CTX)). }
  { now rewrite (rc_addr CTX), (rsr_naddr (rc_inv_end CTX)). }
  { now rewrite (rc_ctrl CTX), (rsr_nctrl (rc_inv_end CTX)). }
  { now rewrite (rc_rmw_dep CTX), (rsr_nrmw_dep (rc_inv_end CTX)). }
  ins.
Admitted.

End ReorderingReexecInternal.

End ReorderingReexecInternal.

Section ReorderingReexec.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t a_t' b_t' : actid.
Variable mapper : actid -> actid.
Variable f : actid -> actid.
Variable dtrmt cmt : actid -> Prop.
Variable l_a' : label. (* The 'desired' label for phantom a_s *)

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_t''" := (WCore.G X_t').
Notation "'G_s'" := (WCore.G X_s).

Notation "'R' G" := (fun e => is_true (is_r (lab G) e)) (at level 1).
Notation "'F' G" := (fun e => is_true (is_f (lab G) e)) (at level 1).
Notation "'W' G" := (fun e => is_true (is_w (lab G) e)) (at level 1).
Notation "'Acq' G" := (fun e => is_true (is_acq (lab G) e)) (at level 1).
Notation "'Rlx' G" := (fun e => is_true (is_rlx (lab G) e)) (at level 1).
Notation "'Rel' G" := (fun e => is_true (is_rel (lab G) e)) (at level 1).

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
Notation "'rpo_s'" := (rpo G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun x => is_true (is_w lab_s x)).
Notation "'R_s'" := (fun x => is_true (is_r lab_s x)).
Notation "'F_s'" := (F G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (Rlx G_s).
Notation "'Acq_s'" := (Acq G_s).
Notation "'Rel_s'" := (Rel G_s).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

(* Conditions for the re-execution lemma *)
Record reexec_conds : Prop := {
  rc_a_dtrmt : dtrmt a_t <-> dtrmt a_t';
  rc_b_dtrmt : dtrmt b_t <-> dtrmt b_t';
  rc_a_eq : dtrmt a_t -> a_t = a_t';
  rc_b_eq : dtrmt b_t -> b_t = b_t';
  rc_pres : b_t = b_t' -> a_t = a_t';
  rc_simrel : reord_simrel X_s X_t a_t b_t mapper;
  rc_step : WCore.reexec X_t X_t' f dtrmt cmt;
  rc_inv_start : reord_step_pred X_t a_t b_t;
  rc_inv_end : reord_step_pred X_t' a_t' b_t';
  rc_l_a_nacq : mode_le (WCore.lab_mode l_a') Orlx;
}.

Hypothesis CTX : reexec_conds.

(* Id aliases for better readability *)
Definition a_s := b_t.
Definition b_s := a_t.
Definition a_s' := b_t'.
Definition b_s' := a_t'.

(* Intermediate graph for locating the srf edge for for a_s *)

Definition A_s'' := extra_a X_t' a_t' b_t' a_s'.
Definition E_s' := mapper ↑₁ E_t' ∪₁ A_s''.

Lemma simrel_reexec :
  exists mapper X_s' f' dtrmt' cmt',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper >> /\
    << STEP : WCore.reexec X_s X_s' f' dtrmt' cmt' >>.
Proof using CTX.
Admitted.

End ReorderingReexec.

(* DRAFTS FOR FINAL THEOREM *)

(* Lemma simrel_term
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel G_t G_s a_t b_t mapper)
    (TERM : machine_terminated G_t traces) :
  << TERM' : machine_terminated G_s traces' >> /\
  << SIM' : ReordCommon.reord G_s G_t traces traces' a b >>.
Proof using.
  admit.
Admitted.

Lemma simrel_implies_cons
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel X_s X_t a_t b_t mapper) :
  WCore.is_cons G_s (WCore.sc X_s).
Proof using.
  admit.
Admitted.

*)

(* Lemma sim_rel_step : about any step *)

(*
 forall traces P_src, P_trgt. If target is a reordereing of src, then
 <..> (clarify cuz the theorem statement looks weird)
*)
(* Theorem reordering_rw : TODO.
Proof using.
  admit.
Admitted. *)