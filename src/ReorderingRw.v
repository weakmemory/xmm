Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.
(* Require Import ReorderingCommon. *)
Require Import AuxRel.
(* Require Import ExecEquiv.
Require Import ExecOps.
Require Import CfgOps.
Require Import Steps. *)
Require Import StepOps.
Require Import SrfProps.
Require Import Instructions.
Require Import Setoid Morphisms.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
(* From imm Require Import SubExecution. *)
From imm Require Import CombRelations.

Set Implicit Arguments.

Section SimRel.

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
Notation "'rpo_t'" := (rpo G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'W_t'" := (is_w lab_t).
Notation "'R_t'" := (is_r lab_t).
Notation "'F_t'" := (is_f lab_t).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).
Notation "'Val_t_' l" := (fun e => val_t e = l) (at level 1).
Notation "'same_loc_t'" := (same_loc lab_t).

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (is_w lab_s).
Notation "'R_s'" := (is_r lab_s).
Notation "'F_s'" := (is_f lab_s).
Notation "'b_s'" := (mapper b_t).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'same_loc_s'" := (same_loc lab_s).

Record extra_a_pred x : Prop := {
  eba_tid : same_tid b_t x;
}.

Definition extra_a (a_s : actid) :=
  ifP ~E_t a_t /\ E_t b_t then eq a_s
  else ∅.

Lemma extra_a_some a_s
    (NINA : ~E_t a_t)
    (INB : E_t b_t) :
  extra_a a_s ≡₁ eq a_s.
Proof using.
  unfold extra_a; desf. exfalso; eauto.
Qed.

Lemma extra_a_none_l a_s
    (INA : E_t a_t) :
  extra_a a_s ≡₁ ∅.
Proof using.
  unfold extra_a; desf. exfalso; desf.
Qed.

Lemma extra_a_none_r a_s
    (INA : ~E_t b_t) :
  extra_a a_s ≡₁ ∅.
Proof using.
  unfold extra_a; desf. exfalso; desf.
Qed.

Definition swap_rel {T : Type} (r : relation T) A B :=
  r \ A × B ∪ B × A.

Definition add_max {T : Type} (A B : T -> Prop) := (A \₁ B) × B.

Definition extra_co_D (s : actid -> Prop) ll l :=
  (s ∩₁ is_w ll ∩₁ (fun e => loc ll e = l)).

Record reord_step_pred : Prop := {
  rsr_at_tid : tid a_t <> tid_init;
  rsr_at_ninit : ~is_init a_t;
  rsr_bt_ninit : ~is_init b_t;
  rsr_Gt_wf : Wf G_t;
  rsr_Gt_rfc : rf_complete G_t;
  rsr_a_t_is_r_or_w : eq a_t ∩₁ E_t ⊆₁ W_t ∪₁ R_t;
  rsr_b_t_is_r_or_w : eq b_t ∩₁ E_t ⊆₁ W_t ∪₁ R_t;
  rsr_init_acts : is_init ⊆₁ E_t;
  rsr_at_bt_tid : tid a_t = tid b_t;
  rsr_fin_t : set_finite (E_t \₁ is_init);
  rsr_at_bt_loc : ⦗eq a_t ∩₁ E_t⦘ ⨾ same_loc_t ⨾ ⦗eq b_t ∩₁ E_t⦘ ⊆ ∅₂;
  rsr_at_bt_ord : forall (INA : E_t a_t), E_t b_t;
  rsr_bt_max : forall (INB : E_t b_t) (NINA : ~E_t a_t),
                    ⦗eq b_t ∩₁ E_t⦘ ⨾ sb_t ⊆ ∅₂;
  rsr_at_nrmw : eq a_t ⊆₁ set_compl (dom_rel rmw_t ∪₁ codom_rel rmw_t);
  rsr_bt_nrmw : eq b_t ⊆₁ set_compl (dom_rel rmw_t ∪₁ codom_rel rmw_t);
  rsr_at_neq_bt : a_t <> b_t;
}.

Record reord_simrel_gen a_s : Prop := {
  rsr_inj : inj_dom E_t mapper;
  rsr_as : extra_a a_s ⊆₁ extra_a_pred;
  rsr_codom : mapper ↑₁ E_t ⊆₁ E_s \₁ extra_a a_s;
  rsr_init : fixset is_init mapper;
  rsr_tid : eq_dom E_t (tid ∘ mapper) tid;
  rsr_lab : eq_dom E_t (lab_s ∘ mapper) lab_t;
  rsr_acts : E_s ≡₁ mapper ↑₁ E_t ∪₁ extra_a a_s;
  rsr_sb : sb_s ≡
    mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t) ∪
    (mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘)) × (extra_a a_s) ∪
    (extra_a a_s) × eq b_s;
  rsr_rf : rf_s ≡ mapper ↑ rf_t ∪ srf_s ⨾ ⦗extra_a a_s ∩₁ R_s⦘;
  rsr_co : co_s ≡ mapper ↑ co_t ∪
    add_max
      (extra_co_D E_s lab_s (loc_s a_s))
      (extra_a a_s ∩₁ W_s);
  rsr_rmw : rmw_s ≡ mapper ↑ rmw_t;
  rsr_threads : threads_set G_s ≡₁ threads_set G_t;
  rsr_ctrl : ctrl_s ≡ ctrl_t;
}.

Definition reord_simrel := exists a_s, reord_simrel_gen a_s.

Lemma rsr_init_acts_s
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  is_init ⊆₁ E_s.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_acts SIMREL), <- (rsr_init_acts PRED).
  rewrite <- (fixset_set_fixpoint (rsr_init SIMREL)).
  basic_solver.
Qed.

Lemma rsr_as_ninit a_s
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel_gen a_s) :
  extra_a a_s ⊆₁ set_compl is_init.
Proof using.
  transitivity (same_tid b_t).
  { rewrite (rsr_as SIMREL). intros x HSET.
    apply HSET. }
  assert (NTID : tid b_t <> tid_init).
  { rewrite <- (rsr_at_bt_tid PRED). apply PRED. }
  unfold same_tid, is_init. basic_solver.
Qed.

Lemma rsr_map_inits
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  mapper ↑₁ E_t \₁ is_init ≡₁ mapper ↑₁ (E_t \₁ is_init).
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite set_collect_minus, <- (fixset_set_fixpoint (rsr_init SIMREL)).
  all: ins.
  eapply inj_dom_mori; ins; try now apply SIMREL.
  rewrite (rsr_init_acts PRED). red. basic_solver.
Qed.

Lemma rsr_fin_s
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  set_finite (E_s \₁ is_init).
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_acts SIMREL). rewrite set_minus_union_l.
  arewrite (extra_a a_s \₁ is_init ⊆₁ eq a_s).
  { unfold extra_a. desf; basic_solver. }
  apply set_finite_union. split; [| apply set_finite_eq].
  arewrite (mapper ↑₁ E_t \₁ is_init ≡₁ mapper ↑₁ (E_t \₁ is_init)).
  { apply rsr_map_inits; try red; eauto. }
  apply set_finite_set_collect, PRED.
Qed.

Lemma rsr_sub_e s
    (SIMREL : reord_simrel)
    (SUB : s ⊆₁ E_t) :
  mapper ↑₁ s ⊆₁ E_s.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_acts SIMREL). apply set_subset_union_r.
  left. now apply set_collect_mori.
Qed.

Lemma rsr_is_w s
    (SIMREL : reord_simrel)
    (SUB : s ⊆₁ E_t ∩₁ W_t) :
  mapper ↑₁ s ⊆₁ W_s.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  unfolder. intros x (y & YIN & XEQ).
  subst x. unfold is_w.
  change (lab_s (mapper y))
    with ((lab_s ∘ mapper) y).
  rewrite (rsr_lab SIMREL); now apply SUB.
Qed.

Lemma rsr_is_r s
    (SIMREL : reord_simrel)
    (SUB : s ⊆₁ E_t ∩₁ R_t) :
  mapper ↑₁ s ⊆₁ R_s.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  unfolder. intros x (y & YIN & XEQ).
  subst x. unfold is_r.
  change (lab_s (mapper y))
    with ((lab_s ∘ mapper) y).
  rewrite (rsr_lab SIMREL); now apply SUB.
Qed.

Lemma rsr_loc s l
    (SIMREL : reord_simrel)
    (SUB : s ⊆₁ E_t ∩₁ Loc_t_ l) :
  mapper ↑₁ s ⊆₁ Loc_s_ l.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  unfolder. intros x (y & YIN & XEQ).
  subst x. unfold loc.
  change (lab_s (mapper y))
    with ((lab_s ∘ mapper) y).
  rewrite (rsr_lab SIMREL); now apply SUB.
Qed.

Lemma rsr_val s v
    (SIMREL : reord_simrel)
    (SUB : s ⊆₁ E_t ∩₁ Val_t_ v) :
  mapper ↑₁ s ⊆₁ Val_s_ v.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  unfolder. intros x (y & YIN & XEQ).
  subst x. unfold val.
  change (lab_s (mapper y))
    with ((lab_s ∘ mapper) y).
  rewrite (rsr_lab SIMREL); now apply SUB.
Qed.

Lemma rsr_same_tid' t
    (SIMREL : reord_simrel) :
  mapper ↑₁ (E_t ∩₁ (fun e => tid e = t)) ≡₁
    mapper ↑₁ E_t ∩₁ (fun e => tid e = t).
Proof using.
  destruct SIMREL as (a_s & SIMREL).
  unfold same_tid. unfolder.
  split; intros x XIN.
  { destruct XIN as (y & (YINE & TID) & XEQ). subst x.
    rewrite <- (rsr_tid SIMREL) in TID; ins.
    split; ins. exists y; split; ins. }
  destruct XIN as ((y & YINE & XEQ) & TID).
  exists y; splits; ins. subst x.
  rewrite <- (rsr_tid SIMREL); ins.
Qed.

Lemma rsr_same_tid e
    (SIMREL : reord_simrel) :
  mapper ↑₁ (E_t ∩₁ same_tid e) ≡₁
    mapper ↑₁ E_t ∩₁ same_tid e.
Proof using.
  arewrite (same_tid e ≡₁ (fun e' => tid e' = tid e)).
  { unfold same_tid. basic_solver. }
  now apply rsr_same_tid'.
Qed.

Lemma swap_rel_union {T : Type} (r1 r2 : relation T) A B :
  swap_rel (r1 ∪ r2) A B ≡
    swap_rel r1 A B ∪ swap_rel r2 A B.
Proof using.
  unfold swap_rel. basic_solver 11.
Qed.

Lemma swap_rel_unionE {T : Type} (r1 r2 : relation T) A B :
  swap_rel (r1 ∪ r2) A B ≡ swap_rel r1 A B ∪ r2 \ A × B.
Proof using.
  rewrite swap_rel_union. unfold swap_rel. basic_solver 11.
Qed.

Lemma swap_rel_empty_l {T : Type} (r : relation T) B :
  swap_rel r ∅ B ≡ r.
Proof using.
  unfold swap_rel. rewrite cross_false_l, cross_false_r.
  basic_solver.
Qed.

Lemma swap_rel_empty_r {T : Type} (r : relation T) A :
  swap_rel r A ∅ ≡ r.
Proof using.
  unfold swap_rel. rewrite cross_false_l, cross_false_r.
  basic_solver.
Qed.

Lemma swap_rel_imm {T : Type} (r : relation T) A B x y
    (XNA : ~A x)
    (XNB : ~B x)
    (YNA : ~A y)
    (YNB : ~B y)
    (IN : singl_rel x y ⊆ immediate r) :
  singl_rel x y ⊆ immediate (swap_rel r A B).
Proof using.
  unfold swap_rel. rewrite immediateE in *.
  intros x' y' EQ. unfolder in EQ. desf.
  split.
  { assert (IN' : r x y) by now apply IN.
    unfolder. left; split; eauto using or_not_and. }
  assert (IN' : ~ (r ⨾ r) x y) by now apply IN.
  unfolder. intros FALSO. desf.
  apply IN'. basic_solver.
Qed.

Lemma immediate_union_ignore {T : Type} (r1 r2 r3 : relation T)
    (NOX : set_disjoint (dom_rel r1) (dom_rel r3))
    (NOY : set_disjoint (codom_rel r1) (codom_rel r3))
    (IN : r1 ⊆ immediate r2) :
  r1 ⊆ immediate (r2 ∪ r3).
Proof using.
  rewrite immediateE in *.
  intros x y REL. split.
  { left. now apply IN. }
  unfolder. intros FALSE. desf.
  { assert (IN' : ~ (r2 ⨾ r2) x y) by now apply IN.
    apply IN'. basic_solver. }
  { apply NOX with x; basic_solver. }
  { apply NOY with y; basic_solver. }
  apply NOY with y; basic_solver.
Qed.

Lemma extra_co_D_eq_dom s ll1 ll2 l
    (EQ : eq_dom s ll1 ll2) :
  extra_co_D s ll1 l ≡₁ extra_co_D s ll2 l.
Proof.
  assert (U2V : same_lab_u2v_dom s ll1 ll2).
  { unfold same_lab_u2v_dom. ins. rewrite EQ; ins.
    unfold same_label_u2v. desf. }
  unfold extra_co_D.
  rewrite same_lab_u2v_dom_is_w
     with (s := s) (lab2 := ll2),
          same_lab_u2v_dom_eq_loc
     with (s := s ∩₁ is_w ll2) (lab2 := ll2).
  all: ins.
  apply same_lab_u2v_dom_inclusion with (s := s); ins.
  basic_solver.
Qed.

Lemma extra_co_eq e ll l :
  extra_co_D (eq e) ll l ≡₁
    eq e ∩₁ WCore.lab_is_w (ll e) ∩₁
      (fun _ => WCore.lab_loc (ll e) = l).
Proof using.
  rewrite <- lab_is_wE', set_interC with (s := eq e),
          set_interA, <- lab_loc'.
  unfold extra_co_D. basic_solver.
Qed.

Lemma add_max_union T (A1 A2 B : T -> Prop) :
  add_max (A1 ∪₁ A2) B ≡ add_max A1 B ∪ add_max A2 B.
Proof using.
  unfold add_max. basic_solver 11.
Qed.

Lemma add_max_empty_r T (A : T -> Prop) :
  add_max A ∅ ≡ ∅₂.
Proof using.
  unfold add_max. now rewrite cross_false_r.
Qed.

Lemma add_max_empty_l T (B : T -> Prop) :
  add_max ∅ B ≡ ∅₂.
Proof using.
  unfold add_max. basic_solver.
Qed.

Lemma add_max_sub T (A B : T -> Prop)
    (SUB : A ⊆₁ B) :
  add_max A B ≡ ∅₂.
Proof using.
  unfold add_max. basic_solver.
Qed.

Lemma add_max_disjoint T (A B : T -> Prop)
    (DISJ : set_disjoint A B) :
  add_max A B ≡ A × B.
Proof using.
  unfold add_max. now rewrite set_minus_disjoint.
Qed.

Lemma restr_add_max T (A B C : T -> Prop) :
  restr_rel C (add_max A B) ≡ add_max (A ∩₁ C) (B ∩₁ C).
Proof using.
  unfold add_max.
  rewrite restr_relE, <- cross_inter_r, <- cross_inter_l.
  arewrite (C ∩₁ (A \₁ B) ≡₁ A ∩₁ C \₁ B ∩₁ C); ins.
  unfolder. split; ins; desf; splits; eauto.
  apply or_not_and; eauto.
Qed.

Lemma extra_co_D_union s1 s2 ll l :
  extra_co_D (s1 ∪₁ s2) ll l ≡₁
    extra_co_D s1 ll l ∪₁ extra_co_D s2 ll l.
Proof using.
  unfold extra_co_D. basic_solver 11.
Qed.

Lemma extra_co_D_minus s1 s2 ll l :
  extra_co_D s1 ll l \₁ s2 ≡₁ extra_co_D (s1 \₁ s2) ll l.
Proof using.
  unfold extra_co_D. basic_solver 12.
Qed.

Lemma set_minus_inter {A : Type} (s1 s2 s3 : A -> Prop) :
  (s1 \₁ s2 ∩₁ s3) ∩₁ s3 ≡₁ (s1 \₁ s2) ∩₁ s3.
Proof using.
  unfolder. split; intros x ((S1 & S2) & S3).
  { split; eauto. }
  splits; eauto. apply or_not_and. eauto.
Qed.

Lemma extra_co_DE a_s
    (GSIM : reord_simrel_gen a_s) :
  extra_co_D E_s lab_s (loc_s a_s) \₁ extra_a a_s ∩₁ W_s ≡₁
    mapper ↑₁ (E_t ∩₁ W_t ∩₁ Loc_t_ (loc_s a_s)).
Proof using.
  assert (DISJ : set_disjoint (mapper ↑₁ E_t) (extra_a a_s)).
  { apply set_disjointE. split; [| basic_solver].
    rewrite (rsr_codom GSIM). basic_solver. }
  rewrite extra_co_D_minus. unfold extra_co_D.
  rewrite set_minus_inter, (rsr_acts GSIM).
  rewrite set_minus_union_l, set_minusK, set_union_empty_r.
  rewrite set_minus_disjoint; ins.
  unfolder. split; intros x HSET.
  { destruct HSET as (((y & INE & XEQ) & ISW) & LOC).
    subst x. exists y; splits; eauto.
    { unfold is_w in *. rewrite <- (rsr_lab GSIM); ins. }
    unfold loc in *. rewrite <- (rsr_lab GSIM); ins. }
  destruct HSET as (y & ((INE & ISW) & LOC) & XEQ).
  subst x. splits; eauto.
  { unfold is_w in *. rewrite <- (rsr_lab GSIM) in ISW; ins. }
  unfold loc in *. rewrite <- (rsr_lab GSIM) in LOC; ins.
Qed.

Add Parametric Morphism T : (@swap_rel T) with signature
  same_relation ==> set_equiv ==> set_equiv
    ==> same_relation as swap_rel_more.
Proof using.
  intros r1 r2 REQ A1 A2 AEQ B1 B2 BEQ.
  unfold swap_rel. now rewrite REQ, AEQ, BEQ.
Qed.

Add Parametric Morphism T : (@add_max T) with signature
  set_equiv ==> set_equiv ==> same_relation as add_max_more.
Proof using.
  intros A1 A2 AEQ B1 B2 BEQ. unfold add_max.
  now rewrite AEQ, BEQ.
Qed.

Add Parametric Morphism : extra_co_D with signature
  set_equiv ==> eq ==> eq ==> set_equiv as extra_co_D_more.
Proof using.
  intros s1 s2 SEQ ll l. unfold extra_co_D.
  now rewrite SEQ.
Qed.

#[export]
Instance swap_rel_Propere T : Proper (_ ==> _ ==> _ ==> _) _ := swap_rel_more (T:=T).
#[export]
Instance add_max_Propere T : Proper (_ ==> _ ==> _) _ := add_max_more (T:=T).
#[export]
Instance extra_co_D_Propere : Proper (_ ==> _ ==> _ ==> _) _ := extra_co_D_more.

Lemma cross_minus_l {T : Type} (A1 A2 B : T -> Prop) :
  (A1 \₁ A2) × B ≡ A1 × B \ A2 × B.
Proof using.
  clear.
  unfolder. split; ins; desf; splits; tauto.
Qed.

Lemma G_s_co_total ol
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  is_total (E_s ∩₁ W_s ∩₁ (fun x => loc_s x = ol)) co_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  assert (TOT : is_total
                  (mapper ↑₁ E_t ∩₁ W_s ∩₁ Loc_s_ ol)
                  (mapper ↑ co_t)
  ).
  { arewrite (mapper ↑₁ E_t ∩₁ W_s ∩₁ Loc_s_ ol ≡₁
              mapper ↑₁ (E_t ∩₁ W_t ∩₁ Loc_t_ ol)).
    all: try now apply total_collect_rel, WF.
    split; intros x XIN.
    { destruct XIN as (((y & YIN & MAP) & XW) & XL).
      unfold is_w in XW. unfold loc in XL.
      rewrite <- MAP in XW, XL.
      change (lab_s (mapper y))
        with ((lab_s ∘ mapper) y) in XW, XL.
      rewrite (rsr_lab SIMREL) in XW, XL; ins.
      unfolder. exists y; splits; ins. }
    destruct XIN as (y & (((YIN & MAP) & XW) & XL)).
    unfolder.
    unfold is_w, loc; subst x.
    change (lab_s (mapper y)) with ((lab_s ∘ mapper) y).
    rewrite (rsr_lab SIMREL); eauto. }
  assert (MAPIN : mapper ↑₁ E_t ⊆₁ E_s).
  { rewrite (rsr_acts SIMREL). basic_solver. }
  rewrite (rsr_acts SIMREL), (rsr_co SIMREL).
  rewrite !set_inter_union_l.
  unfold is_total. intros x XIN y YIN NEQ.
  destruct XIN as [XIN | XEQA],
           YIN as [YIN | YEQA].
  { destruct TOT with x y as [ORD | ORD]; ins.
    { now do 2 left. }
    now right; left. }
  { unfold extra_a in *; desf.
    all: try now exfalso; apply YEQA.
    unfolder in YEQA; desf.
    left; right. unfold add_max, extra_co_D.
    split; [| basic_solver].
    unfolder; splits; ins.
    all: try now apply XIN.
    { apply MAPIN, XIN. }
    intro FALSO; desf. }
  { unfold extra_a in *; desf.
    all: try now exfalso; apply XEQA.
    unfolder in XEQA; desf.
    right; right. unfold add_max, extra_co_D.
    split; [|basic_solver].
    unfolder; splits; ins.
    all: try now apply YIN.
    { apply MAPIN, YIN. }
    intro FALSO; desf. }
  unfold extra_a in *; desf.
  all: try now exfalso; apply XEQA.
  unfolder in XEQA. unfolder in YEQA.
  desf.
Qed.

Lemma G_s_rff
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  functional rf_s⁻¹.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_rf SIMREL), transp_union.
  apply functional_union.
  { rewrite <- collect_rel_transp, (wf_rfE WF),
            <- restr_relE, <- restr_transp.
    apply functional_collect_rel_inj; [apply SIMREL|].
    rewrite restr_transp, restr_relE, <- (wf_rfE WF).
    apply WF. }
  { rewrite transp_seq, transp_eqv_rel.
    apply functional_seq; [basic_solver |].
    apply wf_srff'.
    intros ol. apply (@G_s_co_total ol PRED).
    now exists a_s. }
  intros x DOM1 DOM2.
  assert (XIN : extra_a a_s x).
  { unfolder in DOM2. desf. }
  apply (rsr_codom SIMREL) with x; ins.
  unfolder. unfolder in DOM1.
  destruct DOM1 as (y & y' & x' & RF & XEQ & YEQ).
  exists x'. split; ins.
  apply (wf_rfE WF) in RF.
  unfolder in RF. desf.
Qed.

Lemma G_s_rfE
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  rf_s ≡ ⦗E_s⦘ ⨾ rf_s ⨾ ⦗E_s⦘.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite <- restr_relE, (rsr_rf SIMREL),
          restr_union.
  apply union_more.
  { rewrite (wf_rfE WF), <- restr_relE.
    rewrite <- collect_rel_restr, restr_restr, (rsr_acts SIMREL).
    { rewrite set_inter_absorb_r; ins. basic_solver. }
    eapply inj_dom_mori; ins; [| apply SIMREL].
    rewrite (wf_rfE WF). unfold flip.
    basic_solver. }
  rewrite restr_seq_eqv_r. apply seq_more; ins.
  rewrite restr_relE. apply wf_srfE.
Qed.

Lemma G_s_co_trans
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  transitive co_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  assert (COL : co_t ⊆ same_loc_t) by apply WF.
  assert (COE : co_t ⊆ ⦗E_t⦘ ⨾ co_t ⨾ ⦗E_t⦘) by apply WF.
  assert (COD : co_t ⊆ ⦗W_t⦘ ⨾ co_t ⨾ ⦗W_t⦘) by apply WF.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_co SIMREL).
  apply expand_transitive.
  { arewrite (co_t ≡ restr_rel E_t co_t).
    { rewrite restr_relE. apply WF. }
    apply transitive_collect_rel_inj.
    { apply SIMREL. }
    rewrite restr_relE, <- (wf_coE WF).
    apply WF. }
  { unfold upward_closed. intros x y REL XIN.
    apply (extra_co_DE SIMREL).
    apply (extra_co_DE SIMREL) in XIN.
    unfolder in *.
    destruct REL as (x' & y' & CO & XEQ & YEQ).
    subst x. subst y.
    destruct XIN as (y & ((YINE & ISW) & HLOC) & YMAP).
    exists x'. splits; ins.
    { eapply (COE x' y'); eauto. }
    { eapply (COD x' y'); eauto. }
    rewrite <- HLOC.
    rewrite <- (rsr_inj SIMREL) with (x := y') (y := y); eauto.
    { eapply (COL x' y'); eauto. }
    eapply (COE x' y'); eauto. }
  rewrite <- set_collect_dom.
  arewrite (dom_rel co_t ⊆₁ E_t).
  { rewrite COE. basic_solver. }
  rewrite (rsr_codom SIMREL), set_compl_minus.
  basic_solver.
Qed.

Lemma G_s_co_irr
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  irreflexive co_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_co SIMREL).
  apply irreflexive_union. split.
  { arewrite (co_t ≡ restr_rel E_t co_t).
    { rewrite restr_relE. apply WF. }
    apply collect_rel_irr_inj.
    { apply SIMREL. }
    rewrite restr_relE, <- (wf_coE WF).
    apply WF. }
  unfold add_max. unfolder. ins. desf. eauto.
Qed.

Lemma G_s_co_l
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  co_s ⊆ same_loc_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  assert (COL : co_t ⊆ same_loc_t) by apply WF.
  assert (COE : co_t ⊆ ⦗E_t⦘ ⨾ co_t ⨾ ⦗E_t⦘) by apply WF.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_co SIMREL).
  apply inclusion_union_l.
  { unfolder. intros x y (x' & y' & CO & XEQ & YEQ).
    subst x. subst y. unfold same_loc, loc in *.
    change (lab_s (mapper x')) with ((lab_s ∘ mapper) x').
    change (lab_s (mapper y')) with ((lab_s ∘ mapper) y').
    rewrite !(rsr_lab SIMREL).
    all: try now apply COE in CO; unfolder in CO; desf.
    now apply COL. }
  unfold add_max, extra_co_D. unfold same_loc, extra_a.
  desf; basic_solver.
Qed.

Lemma G_s_coE
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  co_s ≡ ⦗E_s⦘ ⨾ co_s ⨾ ⦗E_s⦘.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite <- restr_relE, (rsr_co SIMREL),
          restr_union.
  apply union_more.
  { rewrite (wf_coE WF), <- restr_relE.
    rewrite <- collect_rel_restr, restr_restr, (rsr_acts SIMREL).
    { rewrite set_inter_absorb_r; ins. basic_solver. }
    eapply inj_dom_mori; ins; [| apply SIMREL].
    rewrite (wf_coE WF). unfold flip.
    basic_solver. }
  rewrite restr_add_max. apply add_max_more.
  { unfold extra_co_D. basic_solver. }
  rewrite (rsr_acts SIMREL). basic_solver.
Qed.

Lemma G_s_coD
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  co_s ≡ ⦗W_s⦘ ⨾ co_s ⨾ ⦗W_s⦘.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  assert (COE : co_t ⊆ ⦗E_t⦘ ⨾ co_t ⨾ ⦗E_t⦘) by apply WF.
  assert (COD : co_t ⊆ ⦗W_t⦘ ⨾ co_t ⨾ ⦗W_t⦘) by apply WF.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_co SIMREL), seq_union_l, seq_union_r.
  apply union_more.
  { split; [| basic_solver 11].
    unfolder. intros x y (x' & y' & CO & XEQ & YEQ).
    subst x. subst y. splits; eauto; unfold is_w.
    all: hahn_rewrite COE in CO; hahn_rewrite COD in CO.
    { change (lab_s (mapper x')) with ((lab_s ∘ mapper) x').
      rewrite (rsr_lab SIMREL).
      all: unfolder in CO; desf. }
    change (lab_s (mapper y')) with ((lab_s ∘ mapper) y').
    rewrite (rsr_lab SIMREL).
    all: unfolder in CO; desf. }
  rewrite <- restr_relE, restr_add_max.
  unfold add_max. apply cross_more; [| basic_solver].
  rewrite set_interA, set_interK. apply set_minus_more; ins.
  unfold extra_co_D. basic_solver.
Qed.

Lemma G_s_rfc
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  rf_complete G_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  assert (RFC : rf_complete G_t) by apply PRED.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  unfold rf_complete in *.
  rewrite (rsr_acts SIMREL), set_inter_union_l,
          (rsr_rf SIMREL), codom_union,
          <- set_collect_codom.
  apply set_union_mori.
  { intros x (INE & ISR). eapply set_collect_mori; eauto.
    unfolder. unfolder in INE. destruct INE as (y & INE & YEQ).
    subst x. exists y; splits; ins.
    unfold is_r in *. now rewrite <- (rsr_lab SIMREL). }
  unfold extra_a. desf; [| basic_solver].
  intros r (EXA & ISR). subst r.
  assert (RIN : E_s a_s).
  { apply (rsr_acts SIMREL). unfold extra_a.
    basic_solver. }
  assert (RLOC : exists l, loc_s a_s = Some l); desf.
  { unfold is_r, loc, is_r in *; desf; eauto. }
  destruct srf_exists
      with (G := G_s) (r := a_s) (l := l)
        as (w & SRF).
  all: eauto.
  { eapply (rsr_as_ninit PRED SIMREL).
    now apply extra_a_some. }
  { apply (rsr_init_acts_s PRED); ins. red; eauto. }
  { intro l'. rewrite <- (rsr_init SIMREL) by ins.
    change (lab_s (mapper (InitEvent l')))
      with ((lab_s ∘ mapper) (InitEvent l')).
    rewrite (rsr_lab SIMREL); [apply WF |].
    now apply (rsr_init_acts PRED). }
  { apply rsr_fin_s; ins. red; eauto. }
  { apply G_s_co_l; ins. red; eauto. }
  { apply G_s_co_trans; ins. red; eauto. }
  { apply G_s_coD; ins. red; eauto. }
  { apply G_s_coE; ins. red; eauto. }
  { apply G_s_co_irr; ins. red; eauto. }
  unfolder. exists w, a_s. splits; ins.
Qed.

End SimRel.

#[export]
Hint Unfold swap_rel add_max extra_co_D : unfolderDb.

Module ReordRwSimRelProps.

Section XmmSteps.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t a_t' b_t' : actid.
Variable mapper : actid -> actid.

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
Notation "'W_t'" := (is_w lab_t).
Notation "'R_t'" := (is_r lab_t).
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
Notation "'W_t''" := (is_w lab_t').
Notation "'R_t''" := (is_r lab_t').
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
Notation "'W_s'" := (is_w lab_s).
Notation "'R_s'" := (is_r lab_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t' b_t'.

Lemma sim_rel_init threads
    (TIDA : tid a_t <> tid_init)
    (NINA : ~is_init a_t)
    (NINB : ~is_init b_t)
    (TIDAB : tid a_t = tid b_t)
    (NEQ : a_t <> b_t)
    (INIT : threads tid_init) :
  << SIMREL : reord_simrel
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    a_t b_t
    id >> /\
  << INV : reord_step_pred
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    a_t b_t >>.
Proof using.
  clear INV INV'.
  assert (IWF : Wf (WCore.init_exec threads)).
  { now apply WCore.wf_init_exec. }
  assert (AI : eq a_t ∩₁ is_init ≡₁ ∅) by basic_solver.
  assert (BI : eq b_t ∩₁ is_init ≡₁ ∅) by basic_solver.
  split; red; [exists a_t |].
  all: constructor; ins.
  { rewrite extra_a_none_r; [basic_solver|ins]. }
  { rewrite extra_a_none_r; [basic_solver|ins]. }
  { rewrite extra_a_none_r; [basic_solver|ins]. }
  { rewrite extra_a_none_r, cross_false_l,
            cross_false_r, AI, BI, !union_false_r,
            swap_rel_empty_l, collect_rel_id.
    all: ins. }
  { rewrite extra_a_none_r; [basic_solver|ins]. }
  { rewrite extra_a_none_r, set_inter_empty_l,
            add_max_empty_r; [|ins].
    basic_solver. }
  { basic_solver. }
  { red. ins. unfold is_r, WCore.init_lab.
    basic_solver. }
  all: rewrite ?AI, ?BI, ?set_minusK.
  all: try now apply set_finite_empty.
  all: rewrite ?dom_empty, ?codom_empty, ?set_union_empty_r.
  all: basic_solver.
Qed.

Lemma simrel_exec_not_a_not_b e l
    (EQA : a_t = a_t')
    (EQB : b_t = b_t')
    (E_NOT_A : e <> a_t)
    (E_NOT_B : e <> b_t)
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using INV INV'.
  subst a_t'. subst b_t'.
  (* Generate new actid *)
  assert (NEWE : exists e',
  << NINIT : ~is_init e' >> /\
  << NOTIN : ~E_s e' >> /\
  << TID : tid e' = tid e >> /\
  << NEWSB : ⦗E_s ∪₁ eq e'⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq e'⦘ ≡
          sb_s ∪ WCore.sb_delta X_s e' >>).
  { admit. }
  assert (CORR : reord_step_pred X_t a_t b_t); ins.
  assert (CORR' : reord_step_pred X_t' a_t b_t); ins.
  assert (E_TID : tid e <> tid_init).
  { admit. }
  (* unfold hypotheses *)
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  desf.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  (* Asserts *)
  set (mapper' := upd mapper e e').
  assert (ENINIT : ~is_init e) by apply ADD.
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq e) by apply ADD.
  assert (WF' : Wf G_t').
  { eapply WCore.add_event_wf; eauto. apply CORR. }
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    rupd. congruence. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { split; unfolder; intros x (y & YINE & HEQ).
    { exists y; split; ins. rewrite <- MAPEQ; ins. }
    exists y. split; ins. subst mapper'. rupd; ins.
    congruence. }
  assert (LABSUB : eq_dom E_t lab_t' lab_t).
  { rewrite (WCore.add_event_lab ADD). unfolder.
    intros x XINE. rupd. congruence. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> e').
  { intros x XINE F. apply NOTIN, (rsr_codom SIMREL).
    basic_solver. }
  assert (A_PRESERVED : E_t' a_t <-> E_t a_t).
  { split; intros INA.
    { apply ADD in INA. destruct INA; congruence. }
    apply ADD. basic_solver. }
  assert (B_PRESERVED : E_t' b_t <-> E_t b_t).
  { split; intros INB.
    { apply ADD in INB. destruct INB; congruence. }
    apply ADD. basic_solver. }
  assert (ETID : forall (WITHA : tid e = tid b_t), ~(~E_t a_t /\ E_t b_t)).
  { intros ETID (NINA & INB).
    eapply (rsr_bt_max CORR') with b_t e; try tauto.
    enough (HIN : singl_rel b_t e ⊆ ⦗eq b_t ∩₁ E_t'⦘ ⨾ sb_t') by now apply HIN.
    rewrite (WCore.add_event_sb ADD), seq_union_r.
    transitivity (⦗eq b_t ∩₁ E_t'⦘ ⨾ WCore.sb_delta X_t e).
    all: basic_solver 12. }
  assert (MAPER_E : mapper' ↑₁ eq e ≡₁ eq e').
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (EXEQ : extra_a X_t a_t b_t a_s ≡₁ extra_a X_t' a_t b_t a_s).
  { unfold extra_a; do 2 desf; exfalso; eauto.
    all: apply n; split; try intro F.
    { apply a. apply EQACTS in F. destruct F; congruence. }
    { apply EQACTS. basic_solver. }
    { apply a, EQACTS. basic_solver. }
    apply EQACTS in a0. destruct a0; congruence. }
  assert (EXIN : extra_a X_t a_t b_t a_s ⊆₁ E_s).
  { rewrite (rsr_acts SIMREL). basic_solver. }
  assert (LABEQ : eq_dom E_s (upd lab_s e' l) lab_s).
  { unfolder. ins. rupd. congruence. }
  assert (NEWCODOM : mapper' ↑₁ E_t' ⊆₁ (E_s ∪₁ eq e') \₁ extra_a X_t a_t b_t a_s).
  { rewrite (WCore.add_event_acts ADD), set_collect_union, MAPSUB,
            (rsr_codom SIMREL), MAPER_E.
    basic_solver. }
  assert (U2V : same_lab_u2v_dom E_s (upd lab_s e' l) lab_s).
  { unfold same_lab_u2v_dom. ins. rewrite LABEQ; ins.
    unfold same_label_u2v. desf. }
  set (G_s' := {|
    acts_set := E_s ∪₁ eq e';
    threads_set := threads_set G_s;
    lab := upd lab_s e' l;
    rf := rf_s ∪ mapper' ↑ (rf_t' ⨾ ⦗eq e ∩₁ R_t'⦘);
    co := co_s ∪
          mapper' ↑ (⦗eq e ∩₁ W_t'⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq e ∩₁ W_t'⦘) ∪
          add_max (eq e' ∩₁ WCore.lab_is_w l)
            (extra_a X_t' a_t b_t a_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l));
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_s;
    ctrl := ctrl_s;
    data := data_s;
    addr := addr_s;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).
  assert (SAMETID : same_tid e' ≡₁ same_tid e).
  { unfold same_tid. now rewrite TID. }
  assert (OLDSIMREL : reord_simrel X_s X_t a_t b_t mapper).
  { exists a_s. ins. }
  assert (AS_TID : extra_a X_t a_t b_t a_s ⊆₁ same_tid b_t).
  { rewrite (rsr_as SIMREL). unfolder. intros x XIN. apply XIN. }
  assert (SIMREL' : reord_simrel_gen X_s' X_t' a_t b_t mapper' a_s).
  { constructor; ins.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
        now apply SIMREL. }
      { basic_solver. }
      rewrite MAPER_E, MAPSUB, (rsr_codom SIMREL). basic_solver. }
    { rewrite <- EXEQ. apply SIMREL. }
    { rewrite <- EXEQ. ins. }
    { unfolder. unfold mapper'. ins. rupd; [| congruence].
      now apply (rsr_init SIMREL). }
    { rewrite EQACTS. apply eq_dom_union. split.
      all: unfolder; unfold compose.
      { intros x XIN. rewrite MAPEQ; ins. now apply SIMREL. }
      now subst mapper'; ins; desf; rupd. }
    { rewrite EQACTS, (WCore.add_event_lab ADD).
      apply eq_dom_union; split; subst mapper'.
      { unfolder. intros x XIN.
        unfold compose. rupd; try congruence; eauto.
        now rewrite <- (rsr_lab SIMREL) by basic_solver. }
      unfolder. ins. desf. unfold compose. now rupd. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB.
      rewrite (rsr_acts SIMREL), EXEQ. basic_solver 11. }
    { unfold sb at 1. ins. rewrite NEWSB, <- EXEQ.
      arewrite (sb_t' ⨾ ⦗eq b_t⦘ ≡ sb_t ⨾ ⦗eq b_t⦘).
      { rewrite (WCore.add_event_sb ADD), seq_union_l.
        basic_solver. }
      arewrite (mapper' b_t = mapper b_t).
      { unfold mapper'. now rupd. }
      arewrite (swap_rel sb_t' (eq b_t ∩₁ E_t') (eq a_t ∩₁ E_t') ≡
                WCore.sb_delta X_t e ∪
                swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t)).
      { rewrite (WCore.add_event_sb ADD), swap_rel_unionE.
        arewrite (eq a_t ∩₁ E_t' ≡₁ eq a_t ∩₁ E_t) by basic_solver.
        arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t) by basic_solver.
        rewrite minus_disjoint, unionC.
        all: basic_solver 7. }
      rewrite collect_rel_union.
      arewrite (mapper' ↑ WCore.sb_delta X_t e ≡
                WCore.sb_delta X_s e').
      { unfold WCore.sb_delta.
        rewrite collect_rel_cross, set_collect_eq.
        apply cross_more; [| unfold mapper'; now rupd].
        rewrite set_collect_union.
        apply set_union_more.
        { rewrite <- fixset_set_fixpoint; ins.
          unfolder. unfold mapper'. ins. rupd; [| congruence].
          now apply (rsr_init SIMREL). }
        rewrite set_collect_eq_dom with (g := mapper),
                (rsr_same_tid e OLDSIMREL), SAMETID,
                (rsr_acts SIMREL), set_inter_union_l.
        all: try now eapply eq_dom_mori; eauto; unfold flip; basic_solver.
        arewrite (extra_a X_t a_t b_t a_s ∩₁ same_tid e ≡₁ ∅).
        all: try now rewrite set_union_empty_r.
        split; [| basic_solver].
        destruct classic with (same_tid b_t e) as [WA|NWA].
        { unfold extra_a.
          desf; [exfalso; apply ETID; eauto | basic_solver]. }
        rewrite AS_TID. unfolder. unfold same_tid in *.
        ins. desf. congruence. }
      arewrite (mapper' ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘) ≡₁
                mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘)).
      { apply set_collect_eq_dom. eapply eq_dom_mori with (x := E_t).
        all: eauto.
        unfold sb, flip. basic_solver. }
      arewrite (mapper' ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t) ≡
                mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t)).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        unfold swap_rel, sb. basic_solver 11. }
      rewrite (rsr_sb SIMREL). basic_solver 12. }
    { arewrite (extra_a X_t' a_t b_t a_s ∩₁ is_r (upd lab_s e' l) ≡₁
                extra_a X_t a_t b_t a_s ∩₁ R_s).
      { rewrite <- EXEQ. apply same_lab_u2v_dom_is_r.
        eapply same_lab_u2v_dom_inclusion with (s := E_s); eauto. }
      arewrite (srf G_s' ⨾ ⦗extra_a X_t a_t b_t a_s ∩₁ R_s⦘ ≡
                srf G_s' ⨾ ⦗E_s⦘ ⨾ ⦗extra_a X_t a_t b_t a_s ∩₁ R_s⦘).
      { basic_solver 11. }
      arewrite (srf G_s' ⨾ ⦗E_s⦘ ≡ srf G_s ⨾ ⦗E_s⦘).
      { apply (srf_add_event X_s X_s'); ins.
        { admit. }
        { basic_solver. }
        { unfold sb at 1. ins. rewrite NEWSB.
          rewrite seq_union_l. basic_solver 11. }
        { rewrite seq_union_l.
          assert (EEQ : mapper' e = e').
          { unfold mapper'. now rupd. }
          arewrite_false (mapper' ↑ (rf_t' ⨾ ⦗eq e ∩₁ R_t'⦘) ⨾ ⦗E_s⦘); [| basic_solver].
          unfolder. ins. desf. congruence. }
        { rewrite !seq_union_l, !seq_union_r.
          assert (EEQ : mapper' e = e').
          { unfold mapper'. now rupd. }
          arewrite_false (⦗E_s⦘ ⨾ mapper' ↑ (⦗eq e ∩₁ W_t'⦘ ⨾ co_t')).
          { unfolder. ins. desf. congruence. }
          arewrite_false (mapper' ↑ (co_t' ⨾ ⦗eq e ∩₁ W_t'⦘) ⨾ ⦗E_s⦘).
          { unfolder. ins. desf. congruence. }
          arewrite_false (⦗E_s⦘ ⨾ add_max
            (eq e' ∩₁ WCore.lab_is_w l)
            (extra_a X_t' a_t b_t a_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l))
          ).
          { unfolder. ins. desf. congruence. }
          basic_solver 11. }
        rewrite (WCore.add_event_rmw ADD), (rsr_rmw SIMREL),
                collect_rel_union, seq_union_l.
        arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
        { apply collect_rel_eq_dom' with (s := E_t); ins.
          apply (wf_rmwE (rsr_Gt_wf CORR)). }
        arewrite_false (mapper' ↑ WCore.rmw_delta e l r ⨾ ⦗E_s⦘); [| basic_solver 11].
        assert (EEQ : mapper' e = e').
        { unfold mapper'. now rupd. }
        unfolder. ins. desf. congruence. }
      arewrite (⦗E_s⦘ ⨾ ⦗extra_a X_t a_t b_t a_s ∩₁ R_s⦘ ≡
                      ⦗extra_a X_t a_t b_t a_s ∩₁ R_s⦘).
      { basic_solver 11. }
      arewrite (rf_t' ⨾ ⦗eq e ∩₁ R_t'⦘ ≡ WCore.rf_delta_R e l w).
      { rewrite (lab_is_rE ADD), id_inter, <- seqA,
                (rf_delta_RE (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      rewrite (rsr_rf SIMREL), (WCore.add_event_rf ADD),
              !collect_rel_union.
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE (rsr_Gt_wf CORR)). }
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, !union_false_r.
      basic_solver 12. }
    arewrite (⦗eq e ∩₁ W_t'⦘ ⨾ co_t' ≡ (eq e ∩₁ WCore.lab_is_w l) × W1).
    { rewrite (lab_is_wE ADD), set_interC, id_inter, seqA,
              (co_deltaE1 (rsr_Gt_wf CORR) ADD).
      basic_solver. }
    { arewrite (co_t' ⨾ ⦗eq e ∩₁ W_t'⦘ ≡ W2 × (eq e ∩₁ WCore.lab_is_w l)).
      { rewrite (lab_is_wE ADD), id_inter, <- seqA,
                (co_deltaE2 (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      rewrite (WCore.add_event_co ADD), !collect_rel_union,
              (rsr_co SIMREL).
      arewrite (mapper' ↑ co_t ≡ mapper ↑ co_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_coE (rsr_Gt_wf CORR)). }
      rewrite <- EXEQ, extra_co_D_union, add_max_union.
      rewrite extra_co_D_eq_dom with (ll1 := upd lab_s e' l),
              same_lab_u2v_dom_is_w with (lab1 := upd lab_s e' l).
      all: eauto using same_lab_u2v_dom_inclusion.
      rewrite extra_co_eq, upds.
      rewrite !add_max_disjoint with (A := eq e' ∩₁ _) by basic_solver.
      rewrite !add_max_disjoint with (A := eq e' ∩₁ _ ∩₁ _) by basic_solver.
      rewrite <- unionA. unfold extra_a; desf; [| basic_solver 11].
      arewrite (loc (upd lab_s e' l) a_s = loc lab_s a_s).
      { unfold loc. rupd. intro FALSO. subst e'.
        apply ETID; ins. rewrite <- TID. symmetry. apply AS_TID.
        unfold extra_a. desf. exfalso. eauto. }
      basic_solver 11. }
    { rewrite (WCore.add_event_threads ADD). apply SIMREL. }
    rewrite (WCore.add_event_ctrl ADD). apply SIMREL. }
  assert (SIMREL'' : reord_simrel X_s' X_t' a_t b_t mapper').
  { now exists a_s. }
  (* Actual proof *)
  exists mapper', X_s'.
  split; red; ins.
  constructor.
  { exists (option_map mapper' r), (mapper' ↑₁ R1),
           (option_map mapper' w),
           (extra_a X_t' a_t b_t a_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l) ∪₁ mapper' ↑₁ W1),
           (mapper' ↑₁ W2).
    constructor; ins.
    { subst mapper'. now rupd. }
    { subst mapper'. now rupd. }
    { subst mapper'. rupd. congruence. }
    { rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_is_w with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins; try now apply ADD.
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_loc with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t)
                           (l := WCore.lab_loc l).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_val with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t)
                           (v := WCore.lab_val l).
      all: ins; try now apply ADD.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_is_r with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins; try now apply ADD.
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_loc with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t)
                           (l := WCore.lab_loc l).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { destruct r as [r|]; [| basic_solver].
      destruct classic
          with (WCore.lab_is_w l (mapper' e))
          as [ISW|NINS]; [| basic_solver].
      assert (IN : WCore.lab_is_w l e).
      { unfold WCore.lab_is_w. desf. }
      assert (SB : sb_t' r e).
      { apply immediate_in, ADD. basic_solver. }
      assert (RNINIT : ~is_init r).
      { eapply read_or_fence_is_not_init with G_t.
        all: try now apply CORR.
        left. now apply ADD. }
      assert (RTID : tid r = tid e).
      { apply sb_tid_init in SB. desf. }
      assert (RNB : b_t <> r).
      { intro FALSO. eapply (rsr_bt_nrmw CORR'); eauto.
        apply set_subset_single_l. rewrite (WCore.add_event_rmw ADD).
        basic_solver 11. }
      assert (RNA : a_t <> r).
      { intro FALSO. eapply (rsr_at_nrmw CORR'); eauto.
        apply set_subset_single_l. rewrite (WCore.add_event_rmw ADD).
        basic_solver 11. }
      assert (INJ' : inj_dom
        (dom_rel
          (swap_rel sb_t'
              (eq b_t ∩₁ E_t')
              (eq a_t ∩₁ E_t'))
        ∪₁ codom_rel
              (swap_rel sb_t'
                (eq b_t ∩₁ E_t')
                (eq a_t ∩₁ E_t')))
        mapper').
      { eapply inj_dom_mori; eauto.
        all: try now apply SIMREL'.
        unfold flip, sb, swap_rel. basic_solver 11. }
      transitivity (singl_rel (mapper' r) (mapper' e)); [basic_solver |].
      rewrite <- collect_rel_singl.
      change G_s' with (WCore.G X_s').
      rewrite (rsr_sb SIMREL').
      destruct classic with (tid e = tid b_t) as [ST|NT].
      { rewrite <- EXEQ.
        arewrite (extra_a X_t a_t b_t a_s ≡₁ ∅).
        { unfold extra_a. desf.
          exfalso. apply ETID; eauto. }
        rewrite cross_false_l, cross_false_r, !union_false_r.
        rewrite collect_rel_immediate; ins.
        apply collect_rel_mori; ins.
        apply swap_rel_imm.
        all: try now intros (FALSO & _); congruence.
        enough (HIN : immediate sb_t' r e).
        { unfolder. unfolder in HIN. ins. desf. }
        apply (WCore.add_event_ri ADD). basic_solver. }
      apply immediate_union_ignore.
      { rewrite collect_rel_singl, dom_singl_rel,
                dom_cross, <- EXEQ.
        { unfold extra_a. desf. unfolder.
          intros x XEQ XEQ'. subst x.
          apply NEWCODOM with (mapper' r).
          { unfolder. exists r; split; ins.
            apply (WCore.add_event_acts ADD). left.
            apply (WCore.add_event_rE ADD). basic_solver. }
          rewrite <- XEQ'. unfold extra_a. desf.
          exfalso. eauto. }
        apply set_nonemptyE. eauto. }
      { rewrite collect_rel_singl, codom_singl_rel.
        unfold extra_a; desf; [| basic_solver].
        rewrite codom_cross; [| apply set_nonemptyE; eauto].
        unfolder. ins. apply E_NOT_B.
        apply (rsr_inj SIMREL'); try now desf.
        now (apply (WCore.add_event_acts ADD); right). }
      apply immediate_union_ignore.
      { rewrite collect_rel_singl, dom_singl_rel.
        unfold extra_a; desf; [| basic_solver].
        rewrite dom_cross; [| apply set_nonemptyE; eauto].
        rewrite <- set_collect_eq.
        apply collect_set_disjoint.
        { eapply inj_dom_mori; try (now apply SIMREL'); ins.
          unfold flip. apply set_subset_union_l.
          split; [| unfold sb; basic_solver].
          rewrite (WCore.add_event_acts ADD),
                  <- (WCore.add_event_rE ADD).
          basic_solver. }
        apply set_disjointE. split; [| basic_solver].
        unfolder. intros x (EQR & (y & SB' & EQ)).
        subst y. subst x. apply sb_tid_init in SB'.
        desf. congruence. }
      { rewrite collect_rel_singl, codom_singl_rel.
        destruct classic with (dom_rel (sb_t' ⨾ ⦗eq b_t⦘) ≡₁ ∅) as [EMP|NEMP].
        { rewrite EMP. basic_solver. }
        rewrite codom_cross, <- EXEQ.
        { unfold extra_a. desf. unfolder.
          intros x XEQ XEQ'. subst x.
          apply NEWCODOM with (mapper' e).
          { unfolder. exists e; split; ins.
            apply (WCore.add_event_acts ADD). now right. }
          rewrite <- XEQ'. unfold extra_a. desf.
          exfalso. eauto. }
        apply set_nonemptyE. apply set_nonemptyE in NEMP.
        desf. basic_solver. }
      rewrite collect_rel_immediate; ins.
      apply collect_rel_mori; ins.
      apply swap_rel_imm.
      all: try now intros (FALSO & _); congruence.
      enough (HIN : immediate sb_t' r e).
      { unfolder. unfolder in HIN. ins. desf. }
      apply (WCore.add_event_ri ADD). basic_solver. }
    { apply set_subset_union_l; split.
      { basic_solver. }
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_is_w with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply set_subset_union_l; split.
      { rewrite <- EXEQ. basic_solver. }
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins; try now apply ADD.
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply set_subset_union_l; split.
      { basic_solver. }
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_loc with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t)
                           (l := WCore.lab_loc l).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite set_collect_eq_dom with (g := mapper),
              rsr_is_w with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins; try now apply ADD.
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite set_collect_eq_dom with (g := mapper),
              rsr_loc with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t)
                           (l := WCore.lab_loc l).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite set_collect_eq_dom with (g := mapper),
              rsr_is_r with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                            (a_t := a_t) (b_t := b_t).
      all: ins; try now apply ADD.
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite set_collect_eq_dom with (g := mapper),
              rsr_loc with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t)
                           (l := WCore.lab_loc l).
      all: ins.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite set_collect_eq_dom with (g := mapper),
              rsr_val with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t)
                           (v := WCore.lab_val l).
      all: ins; try now apply ADD.
      { apply set_subset_inter_r. split; apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { eapply G_s_co_trans with (X_s := X_s'); eauto. }
    { eapply G_s_rff with (X_s := X_s'); eauto. }
    { eapply G_s_co_total with (X_s := X_s'); eauto. }
    { eapply rsr_init_acts_s with (X_s := X_s) (X_t := X_t); eauto. }
    { apply (rsr_threads SIMREL).
      unfold mapper'. rupd. rewrite TID.
      apply ADD. }
    { admit. }
    { unfold mapper'. now rupd. }
    { unfold mapper'. now rupd. }
    { rewrite <- mapped_rf_delta_R,
              <- mapped_rf_delta_W.
      arewrite (rf_t' ⨾ ⦗eq e ∩₁ R_t'⦘ ≡ WCore.rf_delta_R e l w).
      { rewrite (lab_is_rE ADD), id_inter, <- seqA,
                (rf_delta_RE (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      now rewrite collect_rel_empty, union_false_r. }
    { arewrite (⦗eq e ∩₁ W_t'⦘ ⨾ co_t' ≡ (eq e ∩₁ WCore.lab_is_w l) × W1).
      { rewrite (lab_is_wE ADD), set_interC, id_inter,
                seqA, (co_deltaE1 (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      arewrite (co_t' ⨾ ⦗eq e ∩₁ W_t'⦘ ≡ W2 × (eq e ∩₁ WCore.lab_is_w l)).
      { rewrite (lab_is_wE ADD), id_inter, <- seqA,
                (co_deltaE2 (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      unfold mapper'.
      rewrite co_delta_union_W1, <- mapped_co_delta,
              upds, <- EXEQ.
      rewrite add_max_disjoint.
      all: basic_solver 11. }
    { rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD),
              collect_rel_union.
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rmwE (rsr_Gt_wf CORR)). }
      now rewrite (rsr_rmw SIMREL). }
    unfold sb at 1. ins. rewrite NEWSB.
    unfold mapper'. now rupd. }
  { eapply G_s_rfc; eauto. }
  admit.
Admitted.

Lemma simrel_exec_b_step_1 l_a
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (BNOTIN : ~E_t b_t) :
  exists a_s X_s'',
    << ATID : same_tid b_t a_s >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a >> /\
    << RF : rf (WCore.G X_s'') ≡
            rf_s ∪ srf (WCore.G X_s'') ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘ >> /\
    << CO : co (WCore.G X_s'') ≡
            co_s ∪ (E_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
                (eq a_s ∩₁ WCore.lab_is_w l_a) >> /\
    << RMW : rmw (WCore.G X_s'') ≡ rmw_s >>.
Proof using INV INV'.
  (* Generate new actid *)
  assert (NEWE : exists a_s,
  << NINIT : ~is_init a_s >> /\
  << NOTIN : ~E_s a_s >> /\
  << TID : tid a_s = tid b_t >> /\
  << NEWSB : ⦗E_s ∪₁ eq a_s⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq a_s⦘ ≡
          sb_s ∪ WCore.sb_delta X_s a_s >>).
  { admit. }
  (* unfold hypotheses *)
  red in SIMREL. destruct SIMREL as (a_s' & SIMREL).
  desf.
  (* The proof *)
Admitted.

Lemma simrel_exec_b l l_a
    (NEQLOC : WCore.lab_loc l <> WCore.lab_loc l_a)
    (EQA : a_t = a_t')
    (EQB : b_t = b_t')
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' b_t l) :
  exists a_s X_s'' mapper' X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a >> /\
    << STEP2 : WCore.exec_inst X_s'' X_s' (mapper' b_t) l >>.
Proof using.
  assert (CORR : reord_step_pred X_t a_t b_t); ins.
  assert (CORR' : reord_step_pred X_t' a_t b_t) by congruence.
  (* unfold hypotheses *)
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  (* Do step 1 *)
  destruct (simrel_exec_b_step_1 l_a SIMREL)
        as (a_s & X_s'' & ATID & STEP1 & RF' & CO' & RMW').
  all: try congruence.
  { apply ADD. }
  subst a_t'. subst b_t'.
  exists a_s, X_s''.
  destruct STEP1 as [ADD' RFC' CONS'].
  destruct ADD' as (r' & R1' & w' & W1' & W2' & ADD').
  (* Generate new actid *)
  assert (NEWE : exists b_s,
  << NINIT : ~is_init b_s >> /\
  << NOTIN : ~(E_s ∪₁ eq a_s) b_s >> /\
  << TID : tid b_s = tid b_t >> /\
  << NEWSB : ⦗E_s ∪₁ eq a_s ∪₁ eq b_s⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq a_s ∪₁ eq b_s⦘ ≡
          sb (WCore.G X_s'') ∪ WCore.sb_delta X_s'' b_s >>).
  { admit. }
  red in SIMREL. destruct SIMREL as (a_s' & SIMREL).
  red in RF', CO', RMW'.
  desf.
  set (mapper' := upd mapper b_t b_s).
  set (G_s' := {|
    acts_set := E_s ∪₁ eq a_s ∪₁ eq b_s;
    threads_set := threads_set G_s;
    lab := upd (upd lab_s a_s l_a) b_s l;
    rf := rf_s ∪
          mapper' ↑ (rf_t' ⨾ ⦗eq b_t ∩₁ R_t'⦘) ∪
          srf (WCore.G X_s'') ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘;
    co := co_s ∪
          mapper' ↑ (⦗eq b_t ∩₁ W_t'⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq b_t ∩₁ W_t'⦘) ∪
          (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) × (eq a_s ∩₁ WCore.lab_is_w l_a);
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_s;
    ctrl := ctrl_s;
    data := data_s;
    addr := addr_s;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).
  set (extra_W2 := extra_a X_t' a_t b_t a_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l));
  (* Asserts *)
  assert (WF' : Wf G_t').
  { eapply WCore.add_event_wf; eauto.
    apply CORR. }
  assert (ENINIT : ~is_init b_t) by apply ADD.
  assert (ENOTIN : ~E_t b_t) by apply ADD.
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq b_t) by apply ADD.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    rupd. congruence. }
  assert (ANOTB : a_s <> b_s).
  { intro FALSO. apply NOTIN. basic_solver. }
  assert (ANOTINS : ~E_s a_s).
  { intro FALSO. now apply (WCore.add_event_new ADD'). }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { split; unfolder; intros x (y & YINE & HEQ).
    { exists y; split; ins. rewrite <- MAPEQ; ins. }
    exists y. split; ins. subst mapper'. rupd; ins.
    congruence. }
  assert (LABSUB : eq_dom E_t lab_t' lab_t).
  { rewrite (WCore.add_event_lab ADD). unfolder.
    intros x XINE. rupd. congruence. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> b_s).
  { intros x XINE F. apply NOTIN. left.
    apply (rsr_codom SIMREL). basic_solver. }
  assert (MAPNEQ' : forall x (IN : E_t x), mapper x <> a_s).
  { intros x XINE F. apply ANOTINS.
    apply (rsr_codom SIMREL). basic_solver. }
  assert (ANOTIN : ~E_t a_t).
  { intro FALSO. now apply ENOTIN, (rsr_at_bt_ord CORR). }
  assert (ANOTIN' : ~E_t' a_t).
  { intro FALSO. apply (WCore.add_event_acts ADD) in FALSO.
    destruct FALSO as [INE|EQ]; eauto.
    now apply (rsr_at_neq_bt CORR). }
  assert (FMAP : fixset is_init mapper').
  { unfold mapper'. unfolder. ins. rupd; [| congruence].
    now apply (rsr_init SIMREL). }
  assert (MTID : mapper' ↑₁ (E_t ∩₁ same_tid b_t) ≡₁
                 mapper' ↑₁ E_t ∩₁ same_tid (mapper' b_t)).
  { unfolder. split; intros x HSET.
    { destruct HSET as (y & (INE & HTID) & XEQ). subst x.
      unfold same_tid. split; eauto.
      unfold mapper'; rupd; [| congruence].
      change (tid (mapper y)) with ((tid ∘ mapper) y).
      rewrite (rsr_tid SIMREL), TID; ins. }
    destruct HSET as ((y & INE & XEQ) & HTID).
    exists y; splits; eauto. subst x.
    unfold same_tid. rewrite <- (rsr_tid SIMREL) with y; ins.
    unfold mapper' in HTID. rewrite upds, updo in HTID by congruence.
    unfold compose. now rewrite <- TID, <- HTID. }
  assert (MAPER_E : mapper' ↑₁ eq b_t ≡₁ eq b_s).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (OLDEXA : extra_a X_t a_t b_t a_s' ≡₁ ∅).
  { unfold extra_a; do 2 desf; exfalso; eauto. }
  assert (NEWEXA : extra_a X_t' a_t b_t a_s ≡₁ eq a_s).
  { unfold extra_a; do 2 desf; exfalso; eauto.
    apply n; split; ins. apply (WCore.add_event_acts ADD).
    basic_solver. }
  assert (OLDSIMREL : reord_simrel X_s X_t a_t b_t mapper).
  { exists a_s'. ins. }
  assert (LABEQ : eq_dom E_s (lab (WCore.G X_s'')) lab_s).
  { rewrite (WCore.add_event_lab ADD'). unfolder.
    intros x XINE. rupd; ins. congruence. }
  assert (LABEQ' : eq_dom E_s (upd (upd lab_s a_s l_a) b_s l) lab_s).
  { rewrite (WCore.add_event_lab ADD') in LABEQ. unfolder.
    intros x XINE. rupd; ins; try congruence.
    intro FALSO. eapply NOTIN. left; congruence. }
  assert (SIMREL'' : reord_simrel_gen X_s' X_t' a_t b_t mapper' a_s).
  { constructor; ins.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
        now apply SIMREL. }
      { basic_solver. }
      rewrite MAPER_E, MAPSUB, (rsr_codom SIMREL), OLDEXA.
      apply set_disjointE. split; [| basic_solver].
      unfolder. ins. apply NOTIN. desf. basic_solver. }
    { rewrite NEWEXA. unfolder. intros x XEQ. subst x.
      constructor; ins. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB,
              (rsr_codom SIMREL), NEWEXA, set_minus_union_l,
              OLDEXA, set_minus_union_l, set_minusK.
      rewrite !set_minus_disjoint; basic_solver. }
    { rewrite EQACTS. apply eq_dom_union. split.
      all: unfolder; unfold compose.
      { intros x XIN. rewrite MAPEQ; ins. now apply SIMREL. }
      now subst mapper'; ins; desf; rupd. }
    { rewrite EQACTS, (WCore.add_event_lab ADD).
      apply eq_dom_union; split; subst mapper'.
      { unfolder. intros x XIN.
        unfold compose. rupd; try congruence; eauto.
        now rewrite <- (rsr_lab SIMREL) by basic_solver. }
      unfolder. ins. desf. unfold compose. now rupd. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB.
      rewrite (rsr_acts SIMREL), NEWEXA, OLDEXA.
      basic_solver 11. }
    { rewrite NEWEXA. unfold sb at 1.
      ins. rewrite NEWSB, (WCore.add_event_sb ADD').
      arewrite (swap_rel sb_t' (eq b_t ∩₁ E_t') (eq a_t ∩₁ E_t') ≡ sb_t').
      { arewrite (eq a_t ∩₁ E_t' ≡₁ ∅) by basic_solver.
        now rewrite swap_rel_empty_r. }
      rewrite (sb_deltaE ADD), set_collect_dom.
      rewrite (WCore.add_event_sb ADD), collect_rel_union.
      rewrite (rsr_sb SIMREL), OLDEXA, cross_false_l,
              cross_false_r, !union_false_r.
      arewrite (swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t) ≡ sb_t).
      { arewrite (eq a_t ∩₁ E_t ≡₁ ∅) by basic_solver.
        now rewrite swap_rel_empty_r. }
      arewrite (mapper' ↑ sb_t ≡ mapper ↑ sb_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        unfold sb. basic_solver 11. }
      rewrite mapped_sb_delta, dom_cross; ins.
      all: try now (apply set_nonemptyE; eauto).
      unfold WCore.sb_delta.
      rewrite (WCore.add_event_acts ADD'), (rsr_acts SIMREL).
      rewrite OLDEXA, set_union_empty_r, MAPSUB.
      unfold mapper'. rupd. rewrite set_inter_union_l.
      arewrite (same_tid b_s ≡₁ same_tid a_s).
      { unfold same_tid. rewrite TID, eba_tid with (x := a_s); ins. }
      arewrite (eq a_s ∩₁ same_tid a_s ≡₁ eq a_s) by basic_solver.
      basic_solver 12. }
    { arewrite (rf_t' ⨾ ⦗eq b_t ∩₁ R_t'⦘ ≡ WCore.rf_delta_R b_t l w).
      { rewrite (lab_is_rE ADD), id_inter, <- seqA,
                (rf_delta_RE (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      rewrite NEWEXA.
      arewrite (eq a_s ∩₁ is_r (upd (upd lab_s a_s l_a) b_s l) ≡₁
                eq a_s ∩₁ WCore.lab_is_r l_a).
      { admit. }
      arewrite (srf G_s' ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘ ≡
                srf G_s' ⨾ ⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      arewrite (srf G_s' ⨾ ⦗acts_set (WCore.G X_s'')⦘ ≡
                srf (WCore.G X_s'') ⨾ ⦗acts_set (WCore.G X_s'')⦘).
      { apply (srf_add_event X_s'' X_s'); ins.
        { admit. }
        { rewrite (WCore.add_event_acts ADD'). basic_solver. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        admit. }
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘ ≡
                ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      rewrite (rsr_rf SIMREL), (WCore.add_event_rf ADD),
              !collect_rel_union.
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE (rsr_Gt_wf CORR)). }
      rewrite OLDEXA.
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, !union_false_r.
      basic_solver 12. }
    { arewrite (⦗eq b_t ∩₁ W_t'⦘ ⨾ co_t' ≡ (eq b_t ∩₁ WCore.lab_is_w l) × W1).
      { rewrite (lab_is_wE ADD), set_interC, id_inter, seqA,
                (co_deltaE1 (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      arewrite (co_t' ⨾ ⦗eq b_t ∩₁ W_t'⦘ ≡ W2 × (eq b_t ∩₁ WCore.lab_is_w l)).
      { rewrite (lab_is_wE ADD), id_inter, <- seqA,
                (co_deltaE2 (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      rewrite (WCore.add_event_co ADD), !collect_rel_union,
              (rsr_co SIMREL).
      arewrite (mapper' ↑ co_t ≡ mapper ↑ co_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_coE (rsr_Gt_wf CORR)). }
      rewrite OLDEXA, set_inter_empty_l, add_max_empty_r, union_false_r.
      rewrite NEWEXA, !extra_co_D_union, !add_max_union.
      arewrite (extra_co_D (eq b_s) (upd (upd lab_s a_s l_a) b_s l)
                (loc (upd (upd lab_s a_s l_a) b_s l) a_s) ≡₁ ∅).
      { split; [| basic_solver].
        unfolder. unfold loc. rupd.
        intros x ((BEQ & _) & LOC). subst x.
        rewrite upds in LOC. unfold WCore.lab_loc in NEQLOC.
        desf. }
      rewrite add_max_empty_l, union_false_r.
      rewrite add_max_sub
         with (A := extra_co_D (eq a_s) _ _)
           by basic_solver 11.
      rewrite union_false_r.
      rewrite extra_co_D_eq_dom with (ll1 := upd (upd lab_s a_s l_a) b_s l).
      all: eauto using same_lab_u2v_dom_inclusion.
      arewrite (eq a_s ∩₁ is_w (upd (upd lab_s a_s l_a) b_s l) ≡₁
                eq a_s ∩₁ WCore.lab_is_w l_a).
      { unfold is_w, WCore.lab_is_w. unfolder.
        split; intros x (EQ & LAB); split; ins; subst x.
        all: rewrite updo, upds in *; ins.
        all: desf. }
      arewrite (loc (upd (upd lab_s a_s l_a) b_s l) a_s = WCore.lab_loc l_a).
      { unfold loc, WCore.lab_loc. now rupd. }
      unfold add_max.
      arewrite (extra_co_D E_s lab_s (WCore.lab_loc l_a) \₁ eq a_s ∩₁ WCore.lab_is_w l_a
                ≡₁ extra_co_D E_s lab_s (WCore.lab_loc l_a)).
      { rewrite set_minus_disjoint; ins.
        apply set_disjointE. unfold extra_co_D. basic_solver 11. }
      unfold WCore.co_delta. rewrite collect_rel_union.
      basic_solver 11. }
    { rewrite (WCore.add_event_threads ADD). apply SIMREL. }
    rewrite (WCore.add_event_ctrl ADD). apply SIMREL. }
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper').
  { now exists a_s. }
  (* The proof *)
  exists mapper', X_s'.
  splits; ins.
  { constructor; ins.
    now exists r', R1', w', W1', W2'. }
  constructor; ins.
  { exists (option_map mapper' r), (mapper' ↑₁ R1),
         (option_map mapper' w), (mapper' ↑₁ W1), (mapper' ↑₁ W2).
    constructor; ins.
    { intro FALSO. apply (WCore.add_event_acts ADD') in FALSO.
      unfold mapper' in FALSO. rewrite upds in FALSO.
      apply NOTIN, FALSO. }
    { unfold mapper'. now rupd. }
    { unfold mapper'. rupd. rewrite TID.
      rewrite <- (rsr_at_bt_tid CORR). apply CORR. }
    { apply eq_dom_is_w with (lab := lab_s).
      { rewrite <- set_collect_eq_opt,
                set_collect_eq_dom with (g := mapper),
                rsr_is_w with (X_s := X_s) (X_t := X_t)
                              (a_t := a_t) (b_t := b_t).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite (WCore.add_event_acts ADD').
      transitivity E_s; [| basic_solver].
      rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_loc with (lab := lab_s).
      { rewrite <- set_collect_eq_opt,
                set_collect_eq_dom with (g := mapper),
                rsr_loc with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t)
                             (l := WCore.lab_loc l).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_val with (lab := lab_s).
      { rewrite <- set_collect_eq_opt,
                set_collect_eq_dom with (g := mapper),
                rsr_val with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t)
                             (v := WCore.lab_val l).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_is_r with (lab := lab_s).
      { rewrite <- set_collect_eq_opt,
                set_collect_eq_dom with (g := mapper),
                rsr_is_r with (X_s := X_s) (X_t := X_t)
                              (a_t := a_t) (b_t := b_t).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite (WCore.add_event_acts ADD').
      transitivity E_s; [| basic_solver].
      rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_loc with (lab := lab_s).
      { rewrite <- set_collect_eq_opt,
                set_collect_eq_dom with (g := mapper),
                rsr_loc with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t)
                             (l := WCore.lab_loc l).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite <- set_collect_eq_opt,
              set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { destruct r as [r|]; [| basic_solver].
      destruct classic
          with (WCore.lab_is_w l ≡₁ ∅)
            as [NISW|ISW].
      { unfold WCore.rmw_delta. rewrite NISW.
        basic_solver. }
      assert (IS_W : WCore.lab_is_w l b_t).
      { unfold WCore.lab_is_w in *. desf. }
      exfalso. apply (rsr_bt_nrmw CORR') with b_t; ins.
      right. apply set_subset_single_l.
      rewrite (WCore.add_event_rmw ADD). basic_solver 11. }
    { apply eq_dom_is_w with (lab := lab_s).
      { rewrite set_collect_eq_dom with (g := mapper),
                rsr_is_w with (X_s := X_s) (X_t := X_t)
                              (a_t := a_t) (b_t := b_t).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite (WCore.add_event_acts ADD').
      transitivity E_s; [| basic_solver].
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_loc with (lab := lab_s).
      { rewrite set_collect_eq_dom with (g := mapper),
                rsr_loc with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t)
                             (l := WCore.lab_loc l).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_is_w with (lab := lab_s).
      { rewrite set_collect_eq_dom with (g := mapper),
                rsr_is_w with (X_s := X_s) (X_t := X_t)
                              (a_t := a_t) (b_t := b_t).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite (WCore.add_event_acts ADD').
      transitivity E_s; [| basic_solver].
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_loc with (lab := lab_s).
      { rewrite set_collect_eq_dom with (g := mapper),
                rsr_loc with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t)
                             (l := WCore.lab_loc l).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_is_r with (lab := lab_s).
      { rewrite set_collect_eq_dom with (g := mapper),
                rsr_is_r with (X_s := X_s) (X_t := X_t)
                              (a_t := a_t) (b_t := b_t).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { rewrite (WCore.add_event_acts ADD').
      transitivity E_s; [| basic_solver].
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_loc with (lab := lab_s).
      { rewrite set_collect_eq_dom with (g := mapper),
                rsr_loc with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t)
                             (l := WCore.lab_loc l).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { apply eq_dom_val with (lab := lab_s).
      { rewrite set_collect_eq_dom with (g := mapper),
                rsr_val with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t)
                             (v := WCore.lab_val l).
        all: ins.
        { apply set_subset_inter_r. split; apply ADD. }
        eapply eq_dom_mori with (x := E_t); eauto.
        unfold flip. apply ADD. }
      eapply eq_dom_mori; eauto. unfold flip.
      rewrite set_collect_eq_dom with (g := mapper),
              rsr_sub_e with (X_s := X_s) (X_t := X_t)
                             (a_t := a_t) (b_t := b_t).
      all: ins.
      { apply ADD. }
      eapply eq_dom_mori with (x := E_t); eauto.
      unfold flip. apply ADD. }
    { eapply G_s_co_trans with (X_s := X_s'); eauto. }
    { eapply G_s_rff with (X_s := X_s'); eauto. }
    { eapply G_s_co_total with (X_s := X_s'); eauto. }
    { rewrite (WCore.add_event_acts ADD').
      transitivity E_s; [| basic_solver].
      apply (rsr_init_acts_s CORR OLDSIMREL). }
    { unfold mapper'. rupd. rewrite TID.
      apply (WCore.add_event_threads ADD'), (rsr_threads SIMREL),
            (WCore.add_event_threads ADD), (wf_threads WF').
      unfold mapper'. rupd. apply (WCore.add_event_acts ADD). now right. }
    { now rewrite (rsr_ctrl SIMREL), <- (WCore.add_event_ctrl ADD),
              (WCore.add_event_nctrl ADD). }
    { rewrite (WCore.add_event_acts ADD'). unfold mapper'.
      now rupd. }
    { now rewrite (WCore.add_event_threads ADD'). }
    { rewrite (WCore.add_event_lab ADD'). unfold mapper'.
      now rupd. }
    { rewrite <- mapped_rf_delta_R,
              <- mapped_rf_delta_W.
      arewrite (rf_t' ⨾ ⦗eq b_t ∩₁ R_t'⦘ ≡ WCore.rf_delta_R b_t l w).
      { rewrite (lab_is_rE ADD), id_inter, <- seqA,
                (rf_delta_RE (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, union_false_r,
              RF'.
      basic_solver 11. }
    { arewrite (⦗eq b_t ∩₁ W_t'⦘ ⨾ co_t' ≡ (eq b_t ∩₁ WCore.lab_is_w l) × W1).
      { rewrite (lab_is_wE ADD), set_interC, id_inter,
                seqA, (co_deltaE1 (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      arewrite (co_t' ⨾ ⦗eq b_t ∩₁ W_t'⦘ ≡ W2 × (eq b_t ∩₁ WCore.lab_is_w l)).
      { rewrite (lab_is_wE ADD), id_inter, <- seqA,
                (co_deltaE2 (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      unfold mapper'.
      rewrite <- mapped_co_delta, CO'.
      basic_solver 11. }
    { rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD),
              collect_rel_union.
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rmwE (rsr_Gt_wf CORR)). }
      now rewrite RMW', (rsr_rmw SIMREL). }
    { now rewrite (WCore.add_event_data ADD'). }
    { now rewrite (WCore.add_event_addr ADD'). }
    { now rewrite (WCore.add_event_ctrl ADD'). }
    { now rewrite (WCore.add_event_rmw_dep ADD'). }
    unfold sb at 1. ins. rewrite NEWSB.
    unfold mapper'. now rupd. }
  { eapply G_s_rfc with (X_s := X_s') (X_t := X_t'); eauto. }
  admit. (* is_cons *)
Admitted.

Lemma simrel_exec_a l
    (EQA : a_t = a_t')
    (EQB : b_t = b_t')
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' a_t l) :
  exists mapper' X_s' dtrmt' cmt',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP : WCore.reexec X_s X_s' dtrmt' cmt' >>.
Proof using INV INV'.
  subst a_t'. subst b_t'.
  assert (CORR : reord_step_pred X_t a_t b_t); ins.
  assert (CORR' : reord_step_pred X_t' a_t b_t); ins.
  (* Setup vars *)
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper a_t a_s).
  set (G_s' := {|
    acts_set := E_s;
    threads_set := threads_set G_s;
    lab := upd lab_s a_s l;
    rf := rf_s ⨾ ⦗E_s \₁ eq a_s⦘ ∪
          mapper' ↑ (rf_t' ⨾ ⦗eq a_t ∩₁ R_t'⦘);
    co := restr_rel (E_s \₁ eq a_s) co_s ∪
          mapper' ↑ (⦗eq a_t ∩₁ W_t'⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq a_t ∩₁ W_t'⦘);
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_s;
    ctrl := ctrl_s;
    data := data_s;
    addr := addr_s;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).
  set (cmt' := E_s \₁ eq a_s).
  set (dtrmt' := E_s \₁ eq a_s \₁ eq (mapper b_t)).
  set (thrdle' := fun x y =>
    << YNINIT : y <> tid_init >> /\
    << XNOTA : x <> tid a_s >> /\
    << XYVAL : x = tid_init \/ y = tid a_s >>
  ).
  assert (INB' : E_t' b_t).
  { apply (rsr_at_bt_ord CORR'), (WCore.add_event_acts ADD).
    now right. }
  assert (INB : E_t b_t).
  { apply (WCore.add_event_acts ADD) in INB'.
    destruct INB' as [INB' | EQ]; ins.
    exfalso. now apply (rsr_at_neq_bt CORR). }
  assert (WF : Wf G_t) by apply CORR.
  assert (WF' : Wf G_t').
  { apply CORR'. }
  assert (ENINIT : ~is_init a_t) by apply ADD.
  assert (NOTINA : ~E_t a_t).
  { apply ADD. }
  assert (INA : E_t' a_t) by (apply ADD; now right).
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    rupd. congruence. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { split; unfolder; intros x (y & YINE & HEQ).
    { exists y; split; ins. rewrite <- MAPEQ; ins. }
    exists y. split; ins. subst mapper'. rupd; ins.
    congruence. }
  assert (AINS : E_s a_s).
  { apply (rsr_acts SIMREL). unfold extra_a. desf.
    { basic_solver. }
    exfalso; eauto. }
  assert (NOEXA : extra_a X_t' a_t b_t a_s ≡₁ ∅).
  { unfold extra_a; desf. desf. }
  assert (OLDEXA : extra_a X_t a_t b_t a_s ≡₁ eq a_s).
  { unfold extra_a; desf. exfalso; eauto. }
  assert (MAPER_E : mapper' ↑₁ eq a_t ≡₁ eq a_s).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (ANCODOM : ~ (mapper ↑₁ E_t) a_s).
  { intro FALSO. apply (rsr_codom SIMREL) in FALSO.
    now apply FALSO, OLDEXA. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> a_s).
  { intros x XIN EQ. apply (rsr_codom SIMREL) with (x := a_s).
    { basic_solver. }
    now apply OLDEXA. }
  assert (FMAP : fixset is_init mapper').
  { unfold mapper'. unfolder. ins. rupd; [| congruence].
    now apply (rsr_init SIMREL). }
  assert (SIMREL' : reord_simrel_gen X_s' X_t' a_t b_t mapper' a_s).
  { constructor; ins.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
        now apply SIMREL. }
      { basic_solver. }
      rewrite MAPSUB, MAPER_E. apply set_disjointE.
      split; [| basic_solver]. intros x (IN & EQ).
      subst x. now apply ANCODOM. }
    { rewrite NOEXA. basic_solver. }
    { rewrite (WCore.add_event_acts ADD), set_collect_union,
              MAPSUB, MAPER_E, (rsr_codom SIMREL), NOEXA, OLDEXA.
      basic_solver. }
    { rewrite (WCore.add_event_acts ADD). apply eq_dom_union.
      split; unfold compose; unfolder; intros x XINE.
      { rewrite MAPEQ; ins. now apply SIMREL. }
      subst x. unfold mapper'. rupd.
      rewrite (rsr_at_bt_tid CORR).
      symmetry. now apply eba_tid, SIMREL, OLDEXA. }
    { rewrite (WCore.add_event_acts ADD), (WCore.add_event_lab ADD).
      apply eq_dom_union; split; subst mapper'.
      { unfolder. intros x XIN.
        unfold compose. rupd; try congruence; eauto.
        rewrite <- (rsr_lab SIMREL); ins. }
      unfolder. ins. desf. unfold compose. now rupd. }
    { rewrite (WCore.add_event_acts ADD), NOEXA,
              set_union_empty_r, set_collect_union,
              MAPSUB, MAPER_E, (rsr_acts SIMREL).
      now rewrite OLDEXA. }
    { rewrite NOEXA, cross_false_l, cross_false_r,
              !union_false_r.
      change (sb G_s') with sb_s.
      rewrite (rsr_sb SIMREL), OLDEXA.
      arewrite (eq a_t ∩₁ E_t ≡₁ ∅) by basic_solver.
      arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t) by basic_solver.
      arewrite (eq a_t ∩₁ E_t' ≡₁ eq a_t).
      { rewrite (WCore.add_event_acts ADD). basic_solver. }
      rewrite swap_rel_empty_r, (WCore.add_event_sb ADD),
              swap_rel_union.
      unfold swap_rel. rewrite !collect_rel_union.
      arewrite (sb_t \ eq b_t × eq a_t ≡ sb_t).
      { rewrite minus_disjoint; ins. unfold sb.
        rewrite <- restr_relE, restr_relEE.
        basic_solver. }
      unfold WCore.sb_delta. rewrite <- cross_minus_l.
      rewrite !collect_rel_cross, MAPER_E.
      arewrite (mapper' ↑₁ eq b_t ≡₁ eq (mapper b_t)).
      { rewrite set_collect_eq. unfold mapper'. rupd; ins.
        symmetry. apply CORR. }
      arewrite ((is_init ∪₁ E_t ∩₁ same_tid a_t) \₁ eq b_t ≡₁
                dom_rel (sb_t ⨾ ⦗eq b_t⦘)).
      { admit. }
      arewrite (mapper' ↑ sb_t ≡ mapper ↑ sb_t).
      { apply collect_rel_eq_dom.
        eapply eq_dom_mori; eauto. unfold flip.
        unfold sb. basic_solver 11. }
      arewrite (mapper' ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘) ≡₁
                mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘)).
      { apply set_collect_eq_dom.
        eapply eq_dom_mori; eauto. unfold flip.
        unfold sb. basic_solver 11. }
      basic_solver 12. }
    { rewrite NOEXA, set_inter_empty_l,
              (rsr_rf SIMREL), seq_union_l, OLDEXA.
      arewrite (rf_t' ⨾ ⦗eq a_t ∩₁ R_t'⦘ ≡
                WCore.rf_delta_R a_t l w ⨾ ⦗eq a_t ∩₁ R_t'⦘).
      { rewrite (WCore.add_event_rf ADD), !seq_union_l.
        arewrite (rf_t ⨾ ⦗eq a_t ∩₁ R_t'⦘ ≡ ∅₂).
        { rewrite (wf_rfE (rsr_Gt_wf CORR)). basic_solver. }
        arewrite (WCore.rf_delta_W a_t l R1 ⨾ ⦗eq a_t ∩₁ R_t'⦘ ≡ ∅₂).
        all: try now rewrite union_false_r, union_false_l.
        unfold WCore.rf_delta_W.
        arewrite (eq a_t ∩₁ WCore.lab_is_w l ≡₁ eq a_t ∩₁ W_t').
        { unfold WCore.lab_is_w, is_w. rewrite (WCore.add_event_lab ADD).
          unfolder. split; intros x (EQ & LAB).
          all: subst x; rewrite upds in *; desf. }
        split; [| basic_solver].
        unfolder. unfold is_r, is_w. ins. desf. }
      arewrite (srf_s ⨾ ⦗eq a_s ∩₁ R_s⦘ ⨾ ⦗E_s \₁ eq a_s⦘ ≡ ∅₂).
      { basic_solver. }
      arewrite (srf G_s' ⨾ ⦗∅⦘ ≡ ∅₂).
      { basic_solver. }
      arewrite (mapper ↑ rf_t ⨾ ⦗E_s \₁ eq a_s⦘ ≡ mapper ↑ rf_t).
      { split; [basic_solver 11|].
        unfolder. intros x y (x' & y' & RF & XEQ & YEQ).
        assert (INE : E_t y').
        { apply (wf_rfE (rsr_Gt_wf CORR)) in RF.
          unfolder in RF; desf. }
        splits; eauto.
        { apply (rsr_acts SIMREL). basic_solver. }
        intro FALSO. apply ANCODOM.
        basic_solver. }
      arewrite (WCore.rf_delta_R a_t l w ⨾ ⦗eq a_t ∩₁ R_t'⦘ ≡
                WCore.rf_delta_R a_t l w).
      { unfold WCore.rf_delta_R.
        rewrite (lab_is_rE ADD). basic_solver. }
      rewrite (WCore.add_event_rf ADD), !collect_rel_union.
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE (rsr_Gt_wf CORR)). }
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      now rewrite collect_rel_empty, !union_false_r. }
    { rewrite NOEXA, set_inter_empty_l, add_max_empty_r,
              union_false_r.
      rewrite set_interC with (s := eq a_t) at 1.
      rewrite !id_inter, !seqA.
      rewrite (co_deltaE1 WF ADD).
      seq_rewrite (co_deltaE2 WF ADD).
      rewrite <- cross_inter_l, <- cross_inter_r, <- !set_interA.
      arewrite (W_t' ∩₁ eq a_t ∩₁ WCore.lab_is_w l ≡₁ eq a_t ∩₁ WCore.lab_is_w l).
      { admit. }
      arewrite (eq a_t ∩₁ WCore.lab_is_w l ∩₁ W_t' ≡₁ eq a_t ∩₁ WCore.lab_is_w l).
      { admit. }
      rewrite (WCore.add_event_co ADD). unfold WCore.co_delta.
      rewrite !collect_rel_union, <- !unionA.
      repeat apply union_more; ins.
      rewrite (rsr_co SIMREL), restr_union.
      arewrite (restr_rel (E_s \₁ eq a_s) (mapper ↑ co_t) ≡ mapper ↑ co_t).
      { rewrite restr_relE. split; [basic_solver 11 |].
        unfolder. intros x y (x' & y' & (CO & XEQ & YEQ)).
        apply (wf_coE WF) in CO. unfolder in CO. desf.
        splits; eauto.
        all: try now apply (rsr_acts SIMREL); basic_solver.
        all: symmetry; eauto. }
      admit. }
    { now rewrite (rsr_threads SIMREL), (WCore.add_event_threads ADD). }
    now rewrite (rsr_ctrl SIMREL), (WCore.add_event_ctrl ADD). }
  assert (STARTWF : WCore.wf (WCore.X_start X_s dtrmt') X_s' cmt').
  { admit. }
  assert (STAB : WCore.stable_uncmt_reads_gen X_s' cmt' thrdle').
  { constructor; ins.
    { unfolder. subst thrdle'. ins.
      splits; try red; eauto. intro FALSO.
      apply (rsr_at_tid CORR).
      rewrite (rsr_at_bt_tid CORR), FALSO.
      now apply eba_tid, SIMREL, OLDEXA. }
    { unfolder. subst thrdle'. ins. desf. }
    { constructor; unfolder; subst thrdle'.
      { ins; desf. }
      ins; desf. splits; ins; eauto. }
    arewrite (E_s \₁ cmt' ≡₁ eq a_s).
    { subst cmt'. rewrite set_minus_minus_r.
      basic_solver. }
    rewrite seq_union_l.
    arewrite ((rf_s ⨾ ⦗E_s \₁ eq a_s⦘) ⨾ ⦗eq a_s⦘ ≡ ∅₂).
    { basic_solver. }
    rewrite union_false_l. unfolder.
    intros x y ((x' & y' & RF & XEQ & YEQ) & EQ).
    destruct RF as (z & RF & YEQ' & ZEQ & ISR).
    subst y. subst y'. subst z. subst x.
    assert (XIN : E_t x').
    { apply (wf_rfE WF') in RF. unfolder in RF. desf.
      apply ADD in RF. destruct RF; ins.
      exfalso. apply (rf_irr WF') with x'.
      congruence. }
    destruct classic with (tid x' = tid a_s) as [TID | NTID].
    { left.
      enough (IN : singl_rel (mapper' x') (mapper' a_t) ⊆ sb G_s').
      { now apply IN. }
      change G_s' with (WCore.G X_s').
      rewrite (rsr_sb SIMREL'), NOEXA, cross_false_l, cross_false_r,
              !union_false_r, <- collect_rel_singl.
      apply collect_rel_mori; ins.
      rewrite (WCore.add_event_sb ADD), swap_rel_union.
      apply inclusion_union_r. right.
      assert (XNB : x' <> b_t).
      { intro FALSO. subst x'.
        eapply (rsr_at_bt_loc CORR') with a_t b_t.
        apply (wf_rfE WF') in RF. unfolder in RF. unfolder.
        desf. splits; ins. symmetry. now apply (wf_rfl WF'). }
      unfold WCore.sb_delta, swap_rel.
      unfolder. intros x y (XEQ & YEQ). subst x; subst y.
      left. splits; ins.
      { right. split; ins. unfold same_tid.
        rewrite TID, <- (rsr_tid SIMREL'); [| apply ADD; now right].
        unfold compose. congruence. }
      apply or_not_and. left.
      apply or_not_and. now left. }
    right. subst thrdle'; ins; splits; eauto.
    { change (tid (mapper' a_t)) with ((tid ∘ mapper') a_t).
      rewrite (rsr_tid SIMREL'); ins; try now apply SIMREL.
      apply CORR. }
    { change (tid (mapper' x')) with ((tid ∘ mapper') x').
      rewrite (rsr_tid SIMREL'); [congruence|].
      apply ADD. now left. }
    right. congruence. }
  (* The proof *)
  exists mapper', X_s', dtrmt', cmt'.
  split; red; ins.
  { now exists a_s. }
  red. exists id, thrdle'.
  constructor; ins.
  { subst dtrmt' cmt'. basic_solver. }
  { subst cmt'. basic_solver. }
  { constructor; ins.
    { unfold id; ins. rupd. intro FALSO.
      now apply CMT. }
    { admit. (* What happens with rpo? *) }
    { rewrite collect_rel_id, restr_union.
      apply inclusion_union_l; [basic_solver |].
      unfolder. intros x y ((x' & y' & (RF & EQ & ISR) & XEQ & YEQ) & CX & CY).
      exfalso. apply CY. rewrite <- YEQ, <- EQ.
      unfold mapper'. now rupd. }
    { rewrite collect_rel_id, !restr_union.
      repeat apply inclusion_union_l; [basic_solver | |].
      { unfolder. intros x y ((x' & y' & ((EQ & ISW) & CO) & XEQ & YEQ) & CX & CY).
        exfalso. apply CX. rewrite <- XEQ, <- EQ.
        unfold mapper'. now rupd. }
      unfolder. intros x y ((x' & y' & (CO & EQ & ISR) & XEQ & YEQ) & CX & CY).
      exfalso. apply CY. rewrite <- YEQ, <- EQ.
      unfold mapper'. now rupd. }
    rewrite collect_rel_id, (WCore.add_event_rmw ADD), collect_rel_union,
            restr_union.
    apply inclusion_union_l.
    { arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rmwE (rsr_Gt_wf CORR)). }
      rewrite (rsr_rmw SIMREL). basic_solver 11. }
    unfolder. intros x y ((x' & y' & (R & EQ & ISW) & XEQ & YEQ) & CX & CY).
    exfalso. apply CY. rewrite <- YEQ, <- EQ.
    unfold mapper'. now rupd. }
  { admit. (* TODO: cons *) }
  apply sub_to_full_exec_listless with (thrdle := thrdle'); ins.
  { eapply G_s_rfc with (X_s := X_s'); eauto.
    unfold reord_simrel; eauto 11. }
  { arewrite (E_s \₁ dtrmt' ∩₁ E_s ≡₁ eq a_s ∪₁ eq (mapper b_t)).
    { rewrite set_minus_inter_r, set_minusK, set_union_empty_r.
      subst dtrmt'.
      rewrite !set_minus_minus_r, set_minusK, set_union_empty_l.
      rewrite !set_inter_absorb_l; ins; [| basic_solver].
      rewrite (rsr_acts SIMREL). basic_solver. }
    apply set_finite_union. split; apply set_finite_eq. }
  { admit. }
  { admit. }
  { admit. (* might need to update correct graphs *) }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  admit.
Admitted.

Lemma simrel_reexec dtrmt cmt
    (PRESERVATION : a_t' = a_t <-> b_t' = b_t)
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.reexec X_t X_t' dtrmt cmt) :
  exists mapper' X_s' dtrmt',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP : WCore.reexec X_s X_s' dtrmt' (mapper' ↑₁ cmt) >>.
Proof using INV INV'.
  admit.
Admitted.

Lemma simrel_implies_cons
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel X_s X_t a_t b_t mapper) :
  WCore.is_cons G_s (WCore.sc X_s).
Proof using.
  admit.
Admitted.

(* Lemma simrel_term
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel G_t G_s a_t b_t mapper)
    (TERM : machine_terminated G_t traces) :
  << TERM' : machine_terminated G_s traces' >> /\
  << SIM' : ReordCommon.reord G_s G_t traces traces' a b >>.
Proof using.
  admit.
Admitted. *)

End XmmSteps.

(* Lemma sim_rel_step : about any step *)

(*
 forall traces P_src, P_trgt. If target is a reordereing of src, then
 <..> (clarify cuz the theorem statement looks weird)
*)
(* Theorem reordering_rw : TODO.
Proof using.
  admit.
Admitted. *)


End ReordRwSimRelProps.