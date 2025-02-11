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

Section ReordMapper.

Variable X_s X_t : WCore.t.
Variable a_t b_t : actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_t'" := (rmw G_t).
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
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun e => is_true (is_w lab_s e)).
Notation "'R_s'" := (fun e => is_true (is_r lab_s e)).
Notation "'F_s'" := (fun e => is_true (is_f lab_s e)).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'same_val_s'" := (same_val lab_s).
Notation "'Acq_s'" := (fun e => is_true (is_acq lab_s e)).
Notation "'Rel_s'" := (fun e => is_true (is_rel lab_s e)).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Definition mapper := upd (upd id a_t b_t) b_t a_t.

Lemma rsr_extend_mapper mapper'
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper')
    (PRED : reord_step_pred X_t a_t b_t) :
  reord_simrel X_s X_t a_t b_t mapper.
Proof using.
  assert (EQ1 : eq_dom E_t mapper mapper').
  { unfold eq_dom. intros x XIN.
    rewrite (rsr_mapper SIMREL); auto. }
  constructor; try now apply SIMREL.
  { eapply eq_dom_inj_dom; eauto using rsr_inj. }
  all: try rewrite set_collect_eq_dom with (f := mapper) (g := mapper').
  all: try rewrite collect_rel_eq_dom with (f := mapper) (g := mapper').
  all: try now apply SIMREL.
  all: rewrite 1?(wf_coE (rsr_Gt_wf PRED)), 1?wf_sbE,
                1?(wf_rmwE (rsr_Gt_wf PRED)), 1?(wf_rfE (rsr_Gt_wf PRED)).
  all: try now (eapply eq_dom_mori; eauto; unfold flip; basic_solver 11).
  { eapply fixset_eq_dom with (g := mapper'); eauto using rsr_init.
    eapply eq_dom_mori; eauto. unfold flip.
    apply PRED. }
  { transitivity (tid ∘ mapper'); [| apply SIMREL].
    now apply eq_dom_compose_r. }
  { transitivity (lab_s ∘ mapper'); [| apply SIMREL].
    now apply eq_dom_compose_r. }
  { rewrite <- wf_sbE.
    rewrite (rsr_sb SIMREL). apply union_more; auto.
    unfold extra_a; desf; [| basic_solver].
    rewrite EQ1; desf. }
  transitivity mapper'; [| apply SIMREL].
  eapply eq_dom_mori; eauto.
  unfold flip; basic_solver.
Qed.

Lemma rsr_mapper_at
    (NEQ : a_t <> b_t) :
  mapper a_t = b_t.
Proof using.
  unfold mapper.
  rewrite updo, upds; auto.
Qed.

Lemma rsr_mapper_bt
    (NEQ : a_t <> b_t) :
  mapper b_t = a_t.
Proof using.
  unfold mapper.
  rewrite upds; auto.
Qed.

Lemma rsr_mappero x
    (NA : x <> a_t)
    (NB : x <> b_t) :
  mapper x = x.
Proof using.
  unfold mapper.
  rewrite !updo; auto.
Qed.

Lemma rsr_mapper_tid' x
    (TID : tid a_t = tid b_t) :
  tid (mapper x) = tid x.
Proof using.
  unfold mapper.
  destruct classic with (x = b_t) as [EQ|XNB].
  { subst. now rewrite upds. }
  rewrite updo; auto.
  destruct classic with (x = a_t) as [EQ|XNA].
  { subst. now rewrite upds. }
  rewrite updo; auto.
Qed.

Lemma rsr_mapper_tid
    (TID : tid a_t = tid b_t) :
  eq_dom ⊤₁ (tid ∘ mapper) tid.
Proof using.
  unfold eq_dom, compose.
  intros x _.
  now apply rsr_mapper_tid'.
Qed.

Lemma rsr_mapper_sametid e s
    (TID : tid a_t = tid b_t) :
  mapper ↑₁ (s ∩₁ same_tid e) ≡₁
    mapper ↑₁ s ∩₁ same_tid e.
Proof using.
  unfolder. split; ins; desf.
  all: eexists; splits; eauto.
  all: unfold same_tid in *.
  all: rewrite rsr_mapper_tid' in *; auto.
Qed.

Lemma rsr_mapper_inj
    (NEQ : a_t <> b_t) :
  inj_dom ⊤₁ mapper.
Proof using.
  unfold inj_dom, mapper.
  intros x y _ _ FEQ.
  destruct classic with (x = b_t) as [XB|XNB],
           classic with (y = b_t) as [YB|YNB],
           classic with (x = a_t) as [XA|XNA],
           classic with (y = a_t) as [YA|YNA].
  all: desf.
  all: do 4 (
    rewrite ?upds, 1?updo in FEQ by congruence
  ).
  all: unfold id in *; ins; try congruence.
Qed.

Lemma rsr_mapper_inv_at x
    (NEQ : a_t <> b_t)
    (EQ : mapper x = a_t) :
  x = b_t.
Proof using.
  apply rsr_mapper_inj; try red; auto.
  now rewrite EQ, rsr_mapper_bt.
Qed.

Lemma rsr_mapper_inv_bt x
    (NEQ : a_t <> b_t)
    (EQ : mapper x = b_t) :
  x = a_t.
Proof using.
  apply rsr_mapper_inj; try red; auto.
  now rewrite EQ, rsr_mapper_at.
Qed.

Lemma rsr_mapper_self_inv x
    (NEQ : a_t <> b_t) :
  mapper (mapper x) = x.
Proof using.
  unfold mapper at 2.
  unfold id at 1.
  destruct classic with (x = b_t) as [XB|XNB].
  { desf. rewrite upds, rsr_mapper_at; auto. }
  destruct classic with (x = a_t) as [XA|XNA].
  { desf. rewrite updo, upds, rsr_mapper_bt; auto. }
  rewrite !updo, rsr_mappero; auto.
Qed.

Lemma rsr_mapper_compose
    (NEQ : a_t <> b_t) :
  mapper ∘ mapper = id.
Proof using.
  apply functional_extensionality. ins.
  now apply rsr_mapper_self_inv.
Qed.

Lemma rsr_setE_iff s
    (NEQ : a_t <> b_t)
    (IFF : (s b_t /\ s a_t) \/ (~s b_t /\ ~s a_t)) :
  mapper ↑₁ s ≡₁ s.
Proof using.
  rewrite set_union_minus
     with (s := s) (s' := s ∩₁ (eq b_t ∪₁ eq a_t))
       by basic_solver.
  rewrite set_collect_union. apply set_union_more.
  { rewrite set_collect_eq_dom
       with (g := id); [basic_solver|].
    unfold mapper.
    unfolder. ins. rewrite !updo; auto.
    all: symmetry; tauto. }
  rewrite set_inter_union_r, set_collect_union.
  destruct IFF as [BOTH | NON].
  { unfold mapper.
    rewrite !set_inter_absorb_l,
            !set_collect_eq, upds,
            updo, upds.
    all: desf; basic_solver. }
  arewrite (s ∩₁ eq b_t ≡₁ ∅) by basic_solver.
  arewrite (s ∩₁ eq a_t ≡₁ ∅) by basic_solver.
  basic_solver.
Qed.

Lemma rsr_setE_niff s
    (NEQ : a_t <> b_t)
    (NIFF : s b_t /\ ~s a_t) :
  mapper ↑₁ s ≡₁ s \₁ eq b_t ∪₁ eq a_t.
Proof using.
  rewrite set_union_minus
     with (s := s) (s' := s ∩₁ (eq b_t ∪₁ eq a_t))
       by basic_solver.
  rewrite set_collect_union. apply set_union_more.
  { arewrite (s ∩₁ (eq b_t ∪₁ eq a_t) ≡₁ s ∩₁ eq b_t).
    { basic_solver. }
    rewrite set_minus_union_l.
    arewrite (s ∩₁ eq b_t \₁ eq b_t ≡₁ ∅).
    { basic_solver. }
    rewrite set_union_empty_r.
    arewrite ((s \₁ s ∩₁ eq b_t) \₁ eq b_t ≡₁ s \₁ s ∩₁ eq b_t).
    { basic_solver 11. }
    rewrite set_collect_eq_dom
       with (g := id); [basic_solver|].
    unfolder. ins. unfold mapper.
    rewrite !updo; auto.
    all: symmetry; tauto || (desf; congruence). }
  destruct NIFF as (INB & NINA).
  rewrite set_inter_union_r, set_collect_union.
  rewrite set_inter_absorb_l by basic_solver.
  arewrite (s ∩₁ eq a_t ≡₁ ∅) by basic_solver.
  rewrite set_collect_empty, set_union_empty_r.
  unfold mapper. now rewrite set_collect_eq, upds.
Qed.

Lemma rsr_setE_ex s
    (NEQ : a_t <> b_t)
    (EX : ~s b_t /\ s a_t) :
  mapper ↑₁ s ≡₁ s \₁ eq a_t ∪₁ eq b_t.
Proof using.
  rewrite set_union_minus
     with (s := s) (s' := s ∩₁ (eq b_t ∪₁ eq a_t))
       by basic_solver.
  rewrite set_collect_union. apply set_union_more.
  { arewrite (s ∩₁ (eq b_t ∪₁ eq a_t) ≡₁ s ∩₁ eq a_t).
    { basic_solver. }
    rewrite set_minus_union_l.
    arewrite (s ∩₁ eq a_t \₁ eq a_t ≡₁ ∅).
    { basic_solver. }
    rewrite set_union_empty_r.
    arewrite ((s \₁ s ∩₁ eq a_t) \₁ eq a_t ≡₁ s \₁ s ∩₁ eq a_t).
    { basic_solver 11. }
    rewrite set_collect_eq_dom
       with (g := id); [basic_solver|].
    unfold mapper.
    unfolder. ins. rewrite !updo; auto.
    all: symmetry; tauto || (desf; congruence). }
  destruct EX as (NINB & INA).
  rewrite set_inter_union_r, set_collect_union.
  arewrite (s ∩₁ eq b_t ≡₁ ∅) by basic_solver.
  rewrite set_inter_absorb_l by basic_solver.
  rewrite set_collect_empty, set_union_empty_l.
  unfold mapper.
  rewrite set_collect_eq, updo, upds.
  all: auto with hahn.
Qed.

Lemma rsr_mapper_init
    (ANIN : ~is_init a_t)
    (BNIN : ~is_init b_t) :
  fixset is_init mapper.
Proof using.
  unfolder. ins.
  rewrite rsr_mappero; congruence.
Qed.

End ReordMapper.

#[global]
Hint Resolve rsr_mapper_at rsr_mapper_bt
  rsr_mappero rsr_mapper_tid rsr_mapper_inj
  rsr_mapper_inv_at rsr_mapper_bt
  rsr_mapper_tid' rsr_mapper_tid
  rsr_mapper_self_inv rsr_mapper_init : xmm.