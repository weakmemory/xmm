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
Require Import AuxDef2.
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
Notation "'same_val_t'" := (same_val lab_t).

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
Notation "'same_val_s'" := (same_val lab_s).
Notation "'Acq_t'" := (fun e => is_true (is_acq lab_t e)).
Notation "'Rel_t'" := (fun e => is_true (is_rel lab_t e)).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Record extra_a_pred x : Prop := {
  eba_tid : same_tid b_t x;
  eba_val : srf_s ⨾ ⦗eq x ∩₁ R_s⦘ ⊆ same_val lab_s;
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
  rsr_nctrl : ctrl_t ≡ ∅₂;
  rsr_ndata : data_t ≡ ∅₂;
  rsr_naddr : addr_t ≡ ∅₂;
  rsr_nrmw_dep : rmw_dep_t ≡ ∅₂;
  rsr_ninit_acts : E_t ∩₁ Tid_ tid_init ⊆₁ is_init;
  rsr_at_nacq : eq a_t ∩₁ E_t ⊆₁ set_compl Acq_t;
  rsr_bt_nrel : eq b_t ∩₁ E_t ⊆₁ set_compl Rel_t;
  rsr_at_bt_imm : (eq b_t ∩₁ E_t) × (eq a_t ∩₁ E_t) ⊆ immediate sb_t;
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
  rsr_data : data_s ≡ data_t;
  rsr_addr : addr_s ≡ addr_t;
  rsr_rmw_dep : rmw_dep_s ≡ rmw_dep_t;
  rsr_nrpo : ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ⨾ rpo_s ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⊆ ∅₂;
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

(* Lemma rsr_sub_e s
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
Qed. *)

Lemma rsr_same_tid' t
    (SIMREL : reord_simrel) :
  mapper ↑₁ (E_t ∩₁ Tid_ t) ≡₁
    mapper ↑₁ E_t ∩₁ Tid_ t.
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

Lemma rsr_ninit_exa_tid a_s
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel_gen a_s) :
  extra_a a_s ∩₁ Tid_ tid_init ⊆₁ ∅.
Proof using.
  unfold extra_a; desf; [| basic_solver].
  unfolder. intros x (XEQ & TID). subst x.
  apply (rsr_at_tid PRED).
  rewrite (rsr_at_bt_tid PRED), <- TID.
  apply SIMREL, extra_a_some; desf.
Qed.

Lemma rsr_ninit_acts_s
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  E_s ∩₁ Tid_ tid_init ⊆₁ is_init.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_acts SIMREL), set_inter_union_l.
  rewrite <- rsr_same_tid'; [| red; eauto].
  rewrite rsr_ninit_exa_tid; ins.
  rewrite (rsr_ninit_acts PRED),
          <- (fixset_set_fixpoint (rsr_init SIMREL)).
  basic_solver.
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

Add Parametric Morphism : extra_co_D with signature
  set_equiv ==> eq ==> eq ==> set_equiv as extra_co_D_more.
Proof using.
  intros s1 s2 SEQ ll l. unfold extra_co_D.
  now rewrite SEQ.
Qed.

#[export]
Instance extra_co_D_Propere : Proper (_ ==> _ ==> _ ==> _) _ := extra_co_D_more.

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

Lemma immediate_union_ignore_alt {T : Type} (r1 r2 r3 : relation T)
    (NOX : set_disjoint (dom_rel r1) (codom_rel r3))
    (NOY : set_disjoint (codom_rel r1) (codom_rel r3))
    (EDGE : set_disjoint (codom_rel r3) (dom_rel r2))
    (IN : r1 ⊆ immediate r2) :
  r1 ⊆ immediate (r2 ∪ r3).
Proof using.
  rewrite immediateE in *.
  intros x y REL. split.
  { left. now apply IN. }
  unfolder. intros FALSE. desf.
  { assert (IN' : ~ (r2 ⨾ r2) x y) by now apply IN.
    apply IN'. basic_solver. }
  { apply EDGE with z; basic_solver. }
  { apply NOY with y; basic_solver. }
  apply NOY with y; basic_solver.
Qed.

Lemma G_s_wf
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  Wf G_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  constructor.
  { intros x y (XIN & YIN & NEQ & TID & NINIT).
    destruct x as [xl | xt xn], y as [yl | yt yn]; try now ins.
    all: try now (ins; congruence).
    exfalso. apply NINIT, rsr_ninit_acts_s; ins.
    red; eauto. }
  { rewrite (rsr_data SIMREL), (rsr_ndata PRED).
    basic_solver. }
  { rewrite (rsr_data SIMREL), (rsr_ndata PRED).
    basic_solver. }
  { rewrite (rsr_addr SIMREL), (rsr_naddr PRED).
    basic_solver. }
  { rewrite (rsr_addr SIMREL), (rsr_naddr PRED).
    basic_solver. }
  { rewrite (rsr_ctrl SIMREL), (rsr_nctrl PRED).
    basic_solver. }
  { rewrite (rsr_ctrl SIMREL), (rsr_nctrl PRED).
    basic_solver. }
  { rewrite (rsr_ctrl SIMREL), (rsr_nctrl PRED).
    basic_solver. }
  { apply dom_helper_3. rewrite (rsr_rmw SIMREL).
    unfolder. intros x y (x' & y' & RMW & HEQ).
    desf. unfold is_w, is_r.
    change (lab_s (mapper x')) with ((lab_s ∘ mapper) x').
    change (lab_s (mapper y')) with ((lab_s ∘ mapper) y').
    hahn_rewrite (wf_rmwD WF) in RMW.
    hahn_rewrite (wf_rmwE WF) in RMW.
    rewrite !(rsr_lab SIMREL).
    all: unfolder in RMW; desf. }
  { rewrite (rsr_rmw SIMREL).
    unfolder. intros x y (x' & y' & RMW & HEQ).
    desf. unfold same_loc, loc.
    change (lab_s (mapper x')) with ((lab_s ∘ mapper) x').
    change (lab_s (mapper y')) with ((lab_s ∘ mapper) y').
    assert (LOC : same_loc_t x' y') by now apply (wf_rmwl WF).
    hahn_rewrite (wf_rmwE WF) in RMW.
    rewrite !(rsr_lab SIMREL).
    all: unfolder in RMW; desf. }
  { rewrite (rsr_rmw SIMREL), (rsr_sb SIMREL).
    assert (NEXA : extra_a a_s ⊆₁ set_compl (mapper ↑₁ E_t)).
    { rewrite (rsr_codom SIMREL), set_compl_minus. basic_solver. }
    apply immediate_union_ignore.
    { rewrite (wf_rmwE WF), <- restr_relE.
      rewrite dom_cross; [| apply set_nonemptyE; basic_solver].
      apply set_disjointE. split; [| basic_solver].
      arewrite (dom_rel (mapper ↑ restr_rel E_t rmw_t) ⊆₁ mapper ↑₁ E_t).
      { basic_solver 11. }
      rewrite NEXA. basic_solver. }
    { unfold extra_a; desf; [| rewrite cross_false_l; basic_solver].
      rewrite codom_cross; [| apply set_nonemptyE; basic_solver].
      apply set_disjointE. split; [| basic_solver].
      unfolder. intros x ((x0 & x' & y' & RMW & XEQ & YEQ) & XEQ').
      subst. apply (wf_rmwE WF) in RMW. unfolder in RMW.
      destruct RMW as (DOM & RMW & CODOM).
      apply (rsr_inj SIMREL) in XEQ'; desf.
      apply (rsr_bt_nrmw PRED) with b_t; ins.
      basic_solver. }
    assert (NEMPTY : forall (INB : E_t b_t),
      ~ mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘) ≡₁ ∅).
    { ins. apply set_nonemptyE.
      assert (LOC : location) by constructor.
      exists (InitEvent LOC). apply set_subset_single_l.
      arewrite (eq (InitEvent LOC) ≡₁ mapper ↑₁ eq (InitEvent LOC)).
      { rewrite <- fixset_set_fixpoint; ins.
        eapply fixset_mori with (x := is_init); ins.
        { unfold flip. basic_solver. }
        apply SIMREL. }
      apply set_collect_mori; ins.
      unfold sb, ext_sb. rewrite !seqA.
      rewrite <- id_inter, set_inter_absorb_l; [| basic_solver].
      unfolder. ins; desf. exists b_t; splits; ins.
      { now apply (rsr_init_acts PRED). }
      assert (NINIT : ~is_init b_t) by apply PRED.
      destruct b_t; ins. }
    apply immediate_union_ignore_alt.
    { apply set_disjointE. split; [| basic_solver].
      unfold extra_a; desf; [| basic_solver].
      rewrite codom_cross; [| desf; eauto].
      unfolder. intros x ((x0 & x' & y' & RMW & XEQ & YEQ) & XEQ').
      apply (wf_rmwE WF) in RMW. unfolder in RMW.
      destruct RMW as (DOM & RMW & CODOM).
      eapply (rsr_codom SIMREL) with a_s; [basic_solver 11 |].
      apply extra_a_some; desf. }
    { apply set_disjointE. split; [| basic_solver].
      unfold extra_a; desf; [| basic_solver].
      rewrite codom_cross; [| desf; eauto].
      unfolder. intros x ((x0 & x' & y' & RMW & XEQ & YEQ) & XEQ').
      apply (wf_rmwE WF) in RMW. unfolder in RMW.
      destruct RMW as (DOM & RMW & CODOM).
      eapply (rsr_codom SIMREL) with a_s; [basic_solver 11 |].
      apply extra_a_some; desf. }
    { apply set_disjointE. split; [| basic_solver].
      unfold extra_a; desf; [| basic_solver].
      rewrite codom_cross; [| desf; eauto].
      unfold sb, swap_rel. unfolder. ins. desf.
      eapply NEXA with (mapper x'); [| basic_solver].
      apply extra_a_some; ins. }
    intros x y HREL.
    enough (HIN : singl_rel x y ⊆
      immediate (mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t))).
    { now apply HIN. }
    arewrite (mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t) ≡
              swap_rel
                (mapper ↑ sb_t)
                (mapper ↑₁ (eq b_t ∩₁ E_t))
                (mapper ↑₁ (eq a_t ∩₁ E_t))).
    { unfold swap_rel.
      rewrite collect_rel_union, collect_rel_minusE,
              !collect_rel_cross; ins.
      eapply inj_dom_mori with (x := E_t); ins; try now apply SIMREL.
      unfold flip. rewrite wf_sbE. basic_solver 11. }
    apply swap_rel_imm.
    { intro FALSO. apply (rsr_bt_nrmw PRED) with b_t; ins.
      unfolder in HREL. unfolder in FALSO.
      destruct HREL as (x' & y' & RMW & XEQ & YEQ).
      destruct FALSO as (b_t' & (BEQ & BINE) & BEQ'); subst b_t'.
      subst. apply (rsr_inj SIMREL) in BEQ'; ins.
      all: try now (left; desf; basic_solver).
      apply (wf_rmwE WF) in RMW. unfolder in RMW. desf. }
    { intro FALSO. apply (rsr_at_nrmw PRED) with a_t; ins.
      unfolder in HREL. unfolder in FALSO.
      destruct HREL as (x' & y' & RMW & XEQ & YEQ).
      destruct FALSO as (b_t' & (BEQ & BINE) & BEQ'); subst b_t'.
      subst. apply (rsr_inj SIMREL) in BEQ'; ins.
      all: try now (left; desf; basic_solver).
      apply (wf_rmwE WF) in RMW. unfolder in RMW. desf. }
    { intro FALSO. apply (rsr_bt_nrmw PRED) with b_t; ins.
      unfolder in HREL. unfolder in FALSO.
      destruct HREL as (x' & y' & RMW & XEQ & YEQ).
      destruct FALSO as (b_t' & (BEQ & BINE) & BEQ'); subst b_t'.
      subst. apply (rsr_inj SIMREL) in BEQ'; ins.
      all: try now (right; desf; basic_solver).
      apply (wf_rmwE WF) in RMW. unfolder in RMW. desf. }
    { intro FALSO. apply (rsr_at_nrmw PRED) with a_t; ins.
      unfolder in HREL. unfolder in FALSO.
      destruct HREL as (x' & y' & RMW & XEQ & YEQ).
      destruct FALSO as (b_t' & (BEQ & BINE) & BEQ'); subst b_t'.
      subst. apply (rsr_inj SIMREL) in BEQ'; ins.
      all: try now (right; desf; basic_solver).
      apply (wf_rmwE WF) in RMW. unfolder in RMW. desf. }
    rewrite collect_rel_immediate, <- (wf_rmwi WF); [basic_solver |].
    eapply inj_dom_mori with (x := E_t); ins; try now apply SIMREL.
    unfold flip. rewrite wf_sbE. basic_solver. }
  { apply G_s_rfE; ins. red; eauto. }
  { apply dom_helper_3. rewrite (rsr_rf SIMREL).
    apply inclusion_union_l.
    { unfolder. intros x y (x' & y' & RF & HEQ).
      desf. unfold is_w, is_r.
      change (lab_s (mapper x')) with ((lab_s ∘ mapper) x').
      change (lab_s (mapper y')) with ((lab_s ∘ mapper) y').
      hahn_rewrite (wf_rfD WF) in RF.
      hahn_rewrite (wf_rfE WF) in RF.
      rewrite !(rsr_lab SIMREL).
      all: unfolder in RF; desf. }
    transitivity srf_s; [basic_solver |].
    apply dom_helper_3, wf_srfD. }
  { rewrite (rsr_rf SIMREL). apply inclusion_union_l.
    { unfolder. intros x y (x' & y' & RF & HEQ).
      desf. unfold same_loc, loc.
      change (lab_s (mapper x')) with ((lab_s ∘ mapper) x').
      change (lab_s (mapper y')) with ((lab_s ∘ mapper) y').
      assert (LOC : same_loc_t x' y') by now apply (wf_rfl WF).
      hahn_rewrite (wf_rfE WF) in RF.
      rewrite !(rsr_lab SIMREL).
      all: unfolder in RF; desf. }
    transitivity srf_s; [basic_solver |].
    apply wf_srf_loc. }
  { rewrite (rsr_rf SIMREL).
    apply funeq_union.
    { unfolder. intros x y (x' & y' & RF & HEQ).
      desf. unfold val.
      change (lab_s (mapper x')) with ((lab_s ∘ mapper) x').
      change (lab_s (mapper y')) with ((lab_s ∘ mapper) y').
      assert (LOC : same_val_t x' y') by now apply (wf_rfv WF).
      hahn_rewrite (wf_rfE WF) in RF.
      rewrite !(rsr_lab SIMREL).
      all: unfolder in RF; desf. }
    unfolder. intros x y (SRF & EXA & IS_W).
    eapply eba_val with (x := y); ins.
    { now apply SIMREL. }
    basic_solver. }
  { rewrite (rsr_rf SIMREL), transp_union.
    apply functional_union.
    { rewrite <- collect_rel_transp,
              (wf_rfE WF), <- restr_relE,
              <- restr_transp.
      apply functional_collect_rel_inj; [apply SIMREL|].
      rewrite restr_transp, restr_relE, <- (wf_rfE WF).
      apply WF. }
    { apply functional_mori with srf_s⁻¹; [unfold flip; basic_solver |].
      apply wf_srff'. intros ol.
      apply G_s_co_total with (ol := ol); ins.
      red; eauto. }
    intros x DOM1 DOM2. unfolder in DOM2. desf.
    eapply (rsr_codom SIMREL); eauto.
    unfolder in DOM1. unfolder.
    destruct DOM1 as (y0 & x' & y' & RF & XEQ & YEQ).
    apply (wf_rfE WF) in RF. unfolder in RF; desf.
    eauto 11. }
  { apply G_s_coE; ins. red; eauto. }
  { apply G_s_coD; ins. red; eauto. }
  { apply G_s_co_l; ins. red; eauto. }
  { apply G_s_co_trans; ins. red; eauto. }
  { ins; apply G_s_co_total with (ol := ol); ins.
    red; eauto. }
  { apply G_s_co_irr; ins. red; eauto. }
  { ins. apply rsr_init_acts_s; ins. red; eauto. }
  { intros l. rewrite <- (rsr_init SIMREL); ins.
    change (lab_s (mapper (InitEvent l)))
      with ((lab_s ∘ mapper) (InitEvent l)).
    rewrite (rsr_lab SIMREL); try now apply WF.
    now apply (rsr_init_acts PRED). }
  { rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep PRED).
    basic_solver. }
  { rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep PRED).
    basic_solver. }
  intros x XIN. apply (rsr_acts SIMREL) in XIN.
  destruct XIN as [XIN | EQ]; apply (rsr_threads SIMREL).
  { unfolder in XIN. desf.
    change (tid (mapper y)) with ((tid ∘ mapper) y).
    rewrite (rsr_tid SIMREL); [apply WF|]; ins. }
  unfold extra_a in EQ; desf.
  arewrite (tid x = tid b_t).
  { symmetry. apply eba_tid, (rsr_as SIMREL).
    desf. apply extra_a_some; ins. }
  apply WF; desf.
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

Lemma rsr_as_bs_imm
    (INB : E_t b_t)
    (INA : E_t a_t)
    (PRED : reord_step_pred)
    (INJ : inj_dom E_t mapper)
    (SIMREL : sb_s ≡ mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t)) :
  immediate sb_s (mapper a_t) (mapper b_t).
Proof using.
  enough (HIN : singl_rel (mapper a_t) (mapper b_t) ⊆ immediate sb_s).
  { now apply HIN. }
  assert (NEQ : a_t <> b_t) by apply PRED.
  assert (IMM : immediate sb_t b_t a_t).
  { apply (rsr_at_bt_imm PRED). basic_solver. }
  assert (NAB : ~sb_t a_t b_t).
  { intro FALSO. eapply sb_irr, sb_trans; eauto.
    apply IMM. }
  rewrite SIMREL.
  rewrite <- collect_rel_singl, collect_rel_immediate.
  { apply collect_rel_mori; ins.
    rewrite !set_inter_absorb_r by basic_solver.
    unfold swap_rel. rewrite immediateE. unfolder.
    ins; desf; splits; eauto.
    intro FALSO; desf.
    all: try now (eapply sb_irr; eauto).
    apply NAB; eapply sb_trans; eauto. }
  eapply inj_dom_mori with (x := E_t); eauto.
  unfold flip, swap_rel. rewrite wf_sbE. basic_solver 11.
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
  { rewrite AI, BI, set_collect_empty. basic_solver. }
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
  assert (E_TID : tid e <> tid_init).
  { intro FALSO. apply ENINIT.
    apply (rsr_ninit_acts CORR'). split; ins.
    apply EQACTS. now right. }
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
  { intros x XINE FALSO. apply NOTIN, (rsr_codom SIMREL).
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
    all: apply n; split; try intro FALSO.
    { apply a. apply EQACTS in FALSO.
      destruct FALSO; congruence. }
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
    rf := rf_s ∪ mapper' ↑ (rf_t' ⨾ ⦗eq e⦘);
    co := co_s ∪
          mapper' ↑ (⦗eq e⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq e⦘) ∪
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
  assert (SRF' : srf G_s' ⨾ ⦗E_s⦘ ≡ srf G_s ⨾ ⦗E_s⦘).
  { apply (srf_add_event X_s X_s'); ins.
    { eapply G_s_wf with (X_t := X_t); eauto. }
    { basic_solver. }
    { unfold sb at 1. ins. rewrite NEWSB.
      rewrite seq_union_l. basic_solver 11. }
    { rewrite seq_union_l.
      assert (EEQ : mapper' e = e').
      { unfold mapper'. now rupd. }
      arewrite_false (mapper' ↑ (rf_t' ⨾ ⦗eq e⦘) ⨾ ⦗E_s⦘); [| basic_solver].
      unfolder. ins. desf. congruence. }
    { rewrite !seq_union_l, !seq_union_r.
      assert (EEQ : mapper' e = e').
      { unfold mapper'. now rupd. }
      arewrite_false (⦗E_s⦘ ⨾ mapper' ↑ (⦗eq e⦘ ⨾ co_t')).
      { unfolder. ins. desf. congruence. }
      arewrite_false (mapper' ↑ (co_t' ⨾ ⦗eq e⦘) ⨾ ⦗E_s⦘).
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
    arewrite_false (mapper' ↑ WCore.rmw_delta e r ⨾ ⦗E_s⦘); [| basic_solver 11].
    assert (EEQ : mapper' e = e').
    { unfold mapper'. now rupd. }
    unfolder. ins. desf. congruence. }
  assert (SIMREL' : reord_simrel_gen X_s' X_t' a_t b_t mapper' a_s).
  { constructor; ins.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
        now apply SIMREL. }
      { basic_solver. }
      rewrite MAPER_E, MAPSUB, (rsr_codom SIMREL). basic_solver. }
    { rewrite <- EXEQ.
      unfold extra_a. desf.
      unfolder. intros x HIN. subst x.
      constructor.
      { desf. apply (rsr_as SIMREL), extra_a_some; eauto. }
      unfold X_s' at 2. ins.
      arewrite (eq a_s ∩₁ is_r (upd lab_s e' l) ≡₁ eq a_s ∩₁ R_s).
      { apply same_lab_u2v_dom_is_r.
        eapply same_lab_u2v_dom_inclusion with (s := E_s); eauto.
        desf. rewrite <- EXIN, extra_a_some; ins. }
      arewrite (srf G_s' ⨾ ⦗eq a_s ∩₁ R_s⦘ ≡
                srf G_s' ⨾ ⦗E_s⦘ ⨾ ⦗eq a_s ∩₁ R_s⦘).
      { rewrite <- id_inter, <- set_interA.
        rewrite set_inter_absorb_l with (s' := E_s); ins.
        desf. rewrite <- EXIN, extra_a_some; ins. }
      seq_rewrite SRF'. rewrite seqA.
      arewrite (⦗E_s⦘ ⨾ ⦗eq a_s ∩₁ R_s⦘ ≡ ⦗eq a_s ∩₁ R_s⦘).
      { rewrite <- id_inter, <- set_interA.
        rewrite set_inter_absorb_l with (s' := E_s); ins.
        desf. rewrite <- EXIN, extra_a_some; ins. }
      unfolder. intros x y (SRF & YEQ & ISR). subst y.
      apply wf_srfE in SRF. unfolder in SRF. desf.
      unfold same_val, val. rupd; try congruence.
      eapply eba_val with (x := a_s); [| basic_solver].
      apply SIMREL, extra_a_some; ins. }
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
      seq_rewrite SRF'. rewrite seqA.
      arewrite (⦗E_s⦘ ⨾ ⦗extra_a X_t a_t b_t a_s ∩₁ R_s⦘ ≡
                      ⦗extra_a X_t a_t b_t a_s ∩₁ R_s⦘).
      { basic_solver 11. }
      rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      rewrite (rsr_rf SIMREL), (WCore.add_event_rf ADD),
              !collect_rel_union.
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE (rsr_Gt_wf CORR)). }
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, !union_false_r.
      basic_solver 12. }
    { rewrite (co_deltaE1 (rsr_Gt_wf CORR) ADD),
            (co_deltaE2 (rsr_Gt_wf CORR) ADD).
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
      rewrite <- unionA. unfold extra_a; desf; [| basic_solver 12].
      arewrite (loc (upd lab_s e' l) a_s = loc lab_s a_s).
      { unfold loc. rupd. intro FALSO. subst e'.
        apply ETID; ins. rewrite <- TID. symmetry. apply AS_TID.
        unfold extra_a. desf. exfalso. eauto. }
      basic_solver 12. }
    { rewrite (WCore.add_event_threads ADD). apply SIMREL. }
    { rewrite (WCore.add_event_ctrl ADD). apply SIMREL. }
    { rewrite (WCore.add_event_data ADD). apply SIMREL. }
    { rewrite (WCore.add_event_addr ADD). apply SIMREL. }
    { rewrite (WCore.add_event_rmw_dep ADD). apply SIMREL. }
    destruct classic with (E_t' b_t)
          as [INB|NINB]; [| basic_solver].
    destruct classic with (E_t' a_t)
          as [INA|NINA]; [| basic_solver].
    arewrite (eq a_t ∩₁ E_t' ≡₁ eq a_t ∩₁ E_t).
    { basic_solver. }
    arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t).
    { basic_solver. }
    rewrite !set_collect_eq_dom with (f := mapper') (g := mapper).
    all: try (eapply eq_dom_mori with (x := E_t); eauto).
    all: unfold flip; try basic_solver.
    assert (INBS : mapper ↑₁ (eq b_t ∩₁ E_t) ⊆₁ E_s).
    { transitivity (mapper' ↑₁ E_t); [basic_solver |].
      rewrite MAPSUB, (rsr_codom SIMREL). basic_solver. }
    arewrite (rpo G_s' ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⊆
              rpo G_s' ⨾ ⦗E_s⦘ ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘).
    { rewrite <- id_inter, set_inter_absorb_l with (s' := E_s).
      all: ins. }
    arewrite (rpo G_s' ⨾ ⦗E_s⦘ ≡ rpo_s ⨾ ⦗E_s⦘).
    { apply (add_event_rpo X_s X_s'); ins.
      { eapply G_s_wf with (X_t := X_t); eauto. }
      unfold sb at 1. ins. rewrite NEWSB.
      rewrite seq_union_l. basic_solver 11. }
    rewrite <- id_inter, set_inter_absorb_l with (s' := E_s).
    all: apply SIMREL || ins. }
  assert (SIMREL'' : reord_simrel X_s' X_t' a_t b_t mapper').
  { now exists a_s. }
  (* Actual proof *)
  exists mapper', X_s'.
  split; red; ins.
  constructor.
  { exists (option_map mapper' r), (mapper' ↑₁ R1),
           (option_map mapper' w),
           ((extra_a X_t' a_t b_t a_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l) ∩₁ WCore.lab_is_w l)
            ∪₁ mapper' ↑₁ W1),
           (mapper' ↑₁ W2).
    apply add_event_to_wf; ins.
    { eapply rsr_init_acts_s with (X_s := X_s) (X_t := X_t); eauto. }
    { subst mapper'. now rupd. }
    { subst mapper'. now rupd. }
    { subst mapper'. rupd. congruence. }
    { subst mapper'. now rupd. }
    { subst mapper'. now rupd. }
    { rewrite <- mapped_rf_delta_R,
              <- mapped_rf_delta_W.
      rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD),
              (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      now rewrite collect_rel_empty, union_false_r. }
    { rewrite (co_deltaE1 (rsr_Gt_wf CORR) ADD),
              (co_deltaE2 (rsr_Gt_wf CORR) ADD).
      rewrite co_delta_union_W1, <- mapped_co_delta.
      unfold WCore.co_delta. rewrite collect_rel_union.
      rewrite <- !unionA. repeat apply union_more; ins.
      destruct classic with (WCore.lab_is_w l ≡₁ ∅) as [EMP|NEMP].
      { now rewrite EMP, !set_inter_empty_r, add_max_empty_l, cross_false_r. }
      unfold WCore.lab_is_w in *. desf.
      rewrite !set_inter_full_r. ins.
      unfold mapper'. rewrite upds, add_max_disjoint; ins.
      rewrite <- EXEQ. basic_solver. }
    { rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD),
              collect_rel_union.
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rmwE (rsr_Gt_wf CORR)). }
      now rewrite (rsr_rmw SIMREL). }
    { unfold sb at 1. ins. rewrite NEWSB.
      unfold mapper'. now rupd. }
    { rewrite (rsr_ctrl SIMREL), <- (WCore.add_event_ctrl ADD).
    apply ADD. }
    eapply G_s_wf with (X_s := X_s') (X_t := X_t'); eauto. }
  { eapply G_s_rfc; eauto. }
  admit.
Admitted.

Lemma simrel_exec_b_step_1 l_a
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (THREADS : threads_set G_t (tid b_t))
    (BNOTIN : ~E_t b_t) :
  exists l_a' a_s X_s'',
    << LABU2V : same_label_u2v l_a' l_a >> /\
    << ATID : same_tid b_t a_s >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a' >> /\
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
  assert (WF_S : Wf G_s).
  { eapply G_s_wf with (X_t := X_t); eauto.
    red; eauto. }
  set (sb_s' := ⦗E_s ∪₁ eq a_s⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq a_s⦘).
  set (srf_s' := (⦗Loc_s_ (WCore.lab_loc l_a)⦘ ⨾ vf_s ⨾ sb_s') \ (co_s ⨾ vf_s ⨾ sb_s')).
  assert (SRFE : srf_s' ⊆ ⦗E_s⦘ ⨾ srf_s').
  { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; ins.
    rewrite (wf_vfE WF_S). basic_solver 11. }
  assert (SRFD : srf_s' ⊆ ⦗W_s⦘ ⨾ srf_s').
  { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; ins.
    rewrite vf_d_left. basic_solver 11. }
  assert (SRFL : srf_s' ⊆ ⦗Loc_s_ (WCore.lab_loc l_a)⦘ ⨾ srf_s').
  { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; ins.
    basic_solver 11. }
  assert (SRFVF : srf_s' ⊆ vf_s ⨾ sb_s').
  { unfold srf_s'. basic_solver. }
  assert (FUN : functional srf_s'⁻¹).
  { rewrite SRFE, SRFD, SRFL.
    unfolder. intros x y z (((YINE & YW) & YL) & SRF1) (((ZINE & ZW) & ZL) & SRF2).
    destruct (classic (y = z)) as [EQ|NEQ]; ins.
    destruct (wf_co_total WF_S) with (a := y) (b := z)
                        (ol := WCore.lab_loc l_a) as [CO|CO].
    { unfolder; splits; ins. }
    { unfolder; splits; ins. }
    { assumption. }
    { exfalso. apply SRF1.
      apply SRFVF in SRF2.
      basic_solver. }
    exfalso. apply SRF2.
    apply SRFVF in SRF1.
    basic_solver. }
  assert (SRF_W : exists w,
    eq_opt w ≡₁ dom_rel (srf_s' ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘)).
  { destruct classic
        with (dom_rel (srf_s' ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘) ≡₁ ∅)
          as [EMP|NEMP].
    { exists None. rewrite EMP. basic_solver. }
    apply set_nonemptyE in NEMP. destruct NEMP as (x & DOM).
    exists (Some x). rewrite eq_opt_someE. split.
    { intros x' XEQ. now subst x'. }
    intros x' DOM'.
    eapply FUN with (x := a_s).
    all: unfold transp; ins.
    { unfolder in DOM; desf. }
    unfolder in DOM'; desf. }
  destruct SRF_W as (w & SRF_W).
  assert (ALAB : exists l_a',
    << U2V : same_label_u2v l_a' l_a >> /\
    << VAL : dom_rel (srf_s' ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘) ⊆₁ Val_s_ (WCore.lab_val l_a') >>
  ); desf.
  { destruct w as [w|].
    { assert (ISR : WCore.lab_is_r l_a a_s).
      { unfolder in SRF_W. destruct SRF_W as [ISR _].
        destruct ISR with w; desf. }
      assert (ISW : W_s w).
      { unfold srf_s', vf in SRF_W.
        unfolder in SRF_W. destruct SRF_W as [ISW _].
        destruct ISW with w; desf. }
      red in ISR.
      destruct l_a
           as [aex amo al av | axmo amo al av | amo]
           eqn:HEQA; ins.
      unfold is_w in ISW.
      destruct (lab_s w)
           as [wex wmo wl wv | wxmo wmo wl wv | wmo]
           eqn:HEQW; ins.
      exists (Aload aex amo al wv).
      split; red.
      { red. desf. }
      arewrite (dom_rel (srf_s' ⨾ ⦗eq a_s ∩₁ ⊤₁⦘) ⊆₁ Val_s_ (val_s w)).
      { rewrite <- SRF_W. basic_solver. }
      unfold val. rewrite HEQW; ins. }
    exists l_a. split; red.
    { red. desf. }
    rewrite <- SRF_W. basic_solver. }
  set (G_s'' := {|
    acts_set := E_s ∪₁ eq a_s;
    threads_set := threads_set G_s;
    lab := upd lab_s a_s l_a';
    rf := rf_s ∪
          srf_s' ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘;
    co := co_s ∪
          (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) × (eq a_s ∩₁ WCore.lab_is_w l_a);
    rmw := mapper ↑ rmw_t;
    rmw_dep := rmw_dep_s;
    ctrl := ctrl_s;
    data := data_s;
    addr := addr_s;
  |}).
  set (X_s'' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s'';
  |}).
  assert (LOCEQ : WCore.lab_loc l_a = WCore.lab_loc l_a').
  { unfold WCore.lab_loc, same_label_u2v in *. do 2 desf. }
  assert (SRF' :
    srf_s' ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘ ≡
    srf (WCore.G X_s'') ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘
  ).
  { unfold X_s'' at 1. ins. unfold srf.
    seq_rewrite seq_eqv_minus_lr. rewrite !seqA.
    seq_rewrite <- id_inter.
    arewrite (is_r (lab G_s'') ∩₁ (eq a_s ∩₁ WCore.lab_is_r l_a) ≡₁
              eq a_s ∩₁ WCore.lab_is_r l_a).
    { split; [basic_solver |].
      unfold is_r, WCore.lab_is_r. unfolder.
      intros x XIN. destruct XIN; subst; ins.
      rewrite upds. splits; ins; desf. }
    rewrite id_inter.
    rewrite <- !seqA with (r2 := ⦗eq a_s⦘).
    apply seq_more; try easy.
    rewrite minus_inter_l, <- seq_eqv_inter_rr.
    arewrite (same_loc (lab G_s'') ⨾ ⦗eq a_s⦘ ≡
              (fun x y => loc (lab G_s'') x = WCore.lab_loc l_a) ⨾ ⦗eq a_s⦘).
    { rewrite LOCEQ. unfolder; split; ins.
      all: desf; unfold same_loc, loc, WCore.lab_loc in *.
      all: splits; ins.
      all: rewrite upds in *; ins. }
    rewrite seq_eqv_inter_rr.
    arewrite ((vf G_s'' ⨾ sb G_s'' \ co G_s'' ⨾ vf G_s'' ⨾ sb G_s'') ∩ (fun x _ : actid => loc (lab G_s'') x = WCore.lab_loc l_a) ≡
              ⦗fun x => loc (lab G_s'') x = (WCore.lab_loc l_a)⦘ ;; (vf G_s'' ⨾ sb G_s'' \ co G_s'' ⨾ vf G_s'' ⨾ sb G_s'')).
    { basic_solver 11. }
    unfold srf_s'.
    arewrite (sb_s' ≡ sb G_s'').
    rewrite !seq_eqv_minus_r, !seqA.
    arewrite (sb G_s'' ⨾ ⦗eq a_s⦘ ≡ ⦗E_s⦘ ⨾ sb G_s'' ⨾ ⦗eq a_s⦘).
    { unfold sb. ins. rewrite NEWSB.
      rewrite seq_union_l, seq_union_r. rewrite wf_sbE, !seqA.
      seq_rewrite <- !id_inter. rewrite set_interK.
      apply union_more; ins.
      split; [| basic_solver 11].
      unfold WCore.sb_delta.
      seq_rewrite <- cross_inter_l.
      apply seq_more; ins.
      apply cross_more; ins.
      rewrite set_inter_union_r.
      apply set_union_more; [| basic_solver].
      rewrite set_inter_absorb_l; ins.
      eapply rsr_init_acts_s with (X_t := X_t); eauto.
      red; eauto. }
    arewrite (vf G_s'' ⨾ ⦗E_s⦘ ≡ vf_s ⨾ ⦗E_s⦘).
    { apply (vf_add_event X_s X_s''); ins.
      { basic_solver. }
      { unfolder. ins; desf. rupd. congruence. }
      { unfold sb at 1. ins. rewrite NEWSB.
        rewrite seq_union_l. basic_solver 11. }
      { basic_solver 11. }
      now rewrite (rsr_rmw SIMREL). }
    rewrite <- seq_eqv_minus_ll.
    apply minus_rel_more; rewrite <- !seqA.
    all: do 3 (apply seq_more; try easy).
    all: rewrite (wf_vfE WF_S), <- !seqA.
    all: do 2 (apply seq_more; try easy).
    { rewrite <- !id_inter. apply eqv_rel_more.
      unfold loc. unfolder. split; intros x (HSET & HIN).
      all: split; ins.
      all: rewrite updo in *; ins.
      all: congruence. }
    subst G_s''. ins. basic_solver. }
  assert (TOT : forall ol,
    is_total
    ((E_s ∪₁ eq a_s)
    ∩₁ (is_w (upd lab_s a_s l_a'))
    ∩₁ (fun e => loc (upd lab_s a_s l_a') e = ol))
    (co_s ∪
      (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) × (eq a_s ∩₁ WCore.lab_is_w l_a))
  ).
  { ins.
    rewrite !set_inter_union_l.
    unfold is_total. intros x XIN y YIN NEQ.
    destruct XIN as [XIN | XEQA],
            YIN as [YIN | YEQA].
    { destruct (wf_co_total WF_S) with ol x y as [ORF | ORF]; ins.
      all: try now do 2 left.
      all: try now right; left.
      { unfolder in XIN.
        unfolder. desf. splits; ins.
        all: unfold is_w, loc in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      unfolder in YIN.
      unfolder. desf. splits; ins.
      all: unfold is_w, loc in *.
      all: rewrite updo in *; ins.
      all: congruence. }
    { unfolder in YEQA. unfolder in XIN.
      desf.
      unfold loc, is_w in *.
      rewrite upds in *.
      rewrite updo in * by congruence.
      left; right.
      split; [| unfold WCore.lab_is_w; basic_solver].
      unfolder. splits; ins.
      rewrite LOCEQ. unfold WCore.lab_loc. desf. }
    { unfolder in XEQA. unfolder in YIN.
      desf.
      unfold loc, is_w in *.
      rewrite upds in *.
      rewrite updo in * by congruence.
      right; right.
      split; [| unfold WCore.lab_is_w; basic_solver].
      unfolder. splits; ins.
      rewrite LOCEQ. unfold WCore.lab_loc. desf. }
    unfolder in XEQA. unfolder in YEQA. desf. }
  assert (STEP : WCore.add_event X_s X_s'' a_s l_a').
  { red. exists None, ∅, w, ∅,
      (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a) ∩₁ WCore.lab_is_w l_a).
    constructor; ins.
    { rewrite TID, <- (rsr_at_bt_tid INV).
      apply INV. }
    { rewrite SRF_W, SRF', wf_srfD.
      rewrite !seqA.
      seq_rewrite (seq_eqvC (is_r (lab G_s''))).
      seq_rewrite <- SRF'. rewrite seqA.
      unfold srf_s'.
      transitivity (dom_rel (⦗is_w (lab G_s'')⦘ ⨾ (
          ⦗Loc_s_ (WCore.lab_loc l_a)⦘ ⨾ vf_s ⨾ sb_s'
        ) ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘
          ⨾ ⦗is_r (lab G_s'')⦘
      )); [basic_solver 11|].
      rewrite !seqA.
      seq_rewrite (seq_eqvC (is_w (lab G_s''))).
      rewrite seqA, (wf_vfE WF_S), !seqA.
      arewrite (⦗is_w (lab G_s'')⦘ ⨾ ⦗E_s⦘ ≡ ⦗W_s⦘ ⨾ ⦗E_s⦘).
      { rewrite <- !id_inter. apply eqv_rel_more.
        unfold G_s''; ins. unfolder. split; ins; desf.
        all: splits; ins.
        all: unfold is_w in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      basic_solver 11. }
    { rewrite SRF_W.
      unfold srf_s'.
      rewrite (wf_vfE WF_S), !seqA.
      basic_solver 11. }
    { rewrite SRF_W.
      unfold srf_s'.
      rewrite <- LOCEQ.
      basic_solver 11. }
    { rewrite SRF_W; ins. }
    { basic_solver. }
    { basic_solver. }
    { basic_solver. }
    { rewrite <- LOCEQ.
      basic_solver. }
    { apply expand_transitive.
      { eapply G_s_co_trans with (X_t := X_t); eauto.
        red; eauto. }
      { unfold upward_closed. intros x y REL XIN.
        destruct XIN as ((YINE & ISW) & HLOC).
        unfolder.
        eapply G_s_coE with (X_t := X_t) in REL.
        all: eauto; try now (red; eauto).
        unfolder in REL. destruct REL as (EX & REL & EY).
        eapply G_s_coD with (X_t := X_t) in REL.
        all: eauto; try now (red; eauto).
        unfolder in REL. destruct REL as (DX & REL & DY).
        eapply G_s_co_l with (X_t := X_t) in REL.
        all: eauto; try now (red; eauto).
        unfold same_loc in REL.
        splits; ins. congruence. }
      rewrite G_s_coE with (X_t := X_t).
      all: eauto; try now (red; eauto).
      unfolder. ins. desf. intro FALSO; desf. }
    { rewrite transp_union. apply functional_union.
      { eapply G_s_rff with (X_t := X_t); eauto.
        red; eauto. }
      { rewrite SRF'. apply functional_mori with (x := (srf G_s'')⁻¹).
        { unfold flip; basic_solver. }
        apply wf_srff'; ins. }
      intros x RF SRF.
      unfolder in RF. destruct RF as (y & RF).
      apply (wf_rfE WF_S) in RF.
      unfolder in SRF. unfolder in RF. desf. }
    { eapply rsr_init_acts_s with (X_t := X_t); eauto.
      red; eauto. }
    { rewrite TID. now apply (rsr_threads SIMREL). }
    { now rewrite (rsr_ctrl SIMREL), (rsr_nctrl INV). }
    { enough (EMP : eq_opt w ⊆₁ ∅).
      { clear - EMP. unfolder in *. desf.
        exfalso. eauto. }
      rewrite SRF_W.
      clear - NR U2V. unfolder. ins. desf.
      unfold is_r, WCore.lab_is_r, same_label_u2v in *.
      rewrite upds in *. desf. }
    { split; [| basic_solver].
      clear - NW U2V. unfolder. ins. desf.
      unfold is_w, WCore.lab_is_w, same_label_u2v in *.
      rewrite upds in *. desf. }
    { unfold WCore.rf_delta_R. rewrite SRF_W.
      clear. basic_solver 11. }
    { apply union_more; ins.
      unfold WCore.co_delta.
      rewrite cross_false_r, union_false_l.
      destruct classic with (WCore.lab_is_w l_a ≡₁ ∅) as [EMP|NEMP].
      { now rewrite EMP, !set_inter_empty_r, cross_false_l,
                    cross_false_r. }
      unfold WCore.lab_is_w in *. desf.
      now rewrite !set_inter_full_r. }
    rewrite (rsr_rmw SIMREL).
    basic_solver 11. }
  assert (WF_S' : Wf G_s'').
  { red in STEP; desf.
    eapply WCore.add_event_wf with (X' := X_s''); eauto. }
  (* The proof *)
  exists l_a', a_s, X_s''.
  splits; ins.
  { constructor; ins.
    { assert (RFC_S : rf_complete G_s).
      { eapply G_s_rfc with (X_t := X_t); eauto.
        red; eauto. }
      unfold rf_complete. unfold G_s''; ins.
      rewrite set_inter_union_l, SRF', codom_union.
      apply set_union_mori.
      { intros x (XINE & ISR).
        apply RFC_S. split; ins.
        unfold is_r in *. rewrite updo in ISR; ins.
        congruence. }
      intros x (XEQ & ISR).
      assert (XLOC : exists ll, loc (upd lab_s a_s l_a') x = Some ll).
      { unfold is_r in ISR. subst x.
        rewrite upds in ISR. desf.
        eexists. unfold loc. now rewrite upds. }
      destruct XLOC as (ll & XLOC).
      subst x.
      destruct srf_exists
          with (G := G_s'') (r := a_s) (l := ll)
            as (w' & SRF).
      all: ins.
      all: try now apply WF_S'.
      { now right. }
      { left. eapply (rsr_init_acts_s INV); ins.
        red; eauto. }
      { rewrite set_minus_union_l.
        apply set_finite_union. split.
        { eapply (rsr_fin_s INV); eauto.
          red; eauto. }
        apply set_finite_mori with (x := eq a_s).
        { unfold flip; basic_solver. }
        apply set_finite_eq. }
      exists w'. unfolder; splits; ins.
      unfold is_r, WCore.lab_is_r in *.
      rewrite upds in ISR. desf. }
    admit. (* Cons *) }
  { apply union_more; ins. }
  { now rewrite set_interC with (s := E_s). }
  subst X_s''. subst G_s''. ins.
  now rewrite (rsr_rmw SIMREL).
Admitted.

Lemma simrel_exec_b l l_a
    (NEQLOC : WCore.lab_loc l <> WCore.lab_loc l_a)
    (EQA : a_t = a_t')
    (EQB : b_t = b_t')
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' b_t l) :
  exists l_a' a_s X_s'' mapper' X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a' >> /\
    << STEP2 : WCore.exec_inst X_s'' X_s' (mapper' b_t) l >>.
Proof using.
  assert (CORR : reord_step_pred X_t a_t b_t); ins.
  assert (CORR' : reord_step_pred X_t' a_t b_t) by congruence.
  (* unfold hypotheses *)
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  (* Do step 1 *)
  assert (NINB : ~E_t b_t) by apply ADD.
  assert (STEP1 : exists l_a' a_s X_s'',
    << LABU2V : same_label_u2v l_a' l_a >> /\
    << ATID : same_tid b_t a_s >> /\
    << STEPA : WCore.exec_inst X_s  X_s'' a_s l_a' >> /\
    << RF' : rf (WCore.G X_s'') ≡
            rf_s ∪ srf (WCore.G X_s'') ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘ >> /\
    << CO' : co (WCore.G X_s'') ≡
            co_s ∪ (E_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
                (eq a_s ∩₁ WCore.lab_is_w l_a) >> /\
    << RMW' : rmw (WCore.G X_s'') ≡ rmw_s >>).
  { apply simrel_exec_b_step_1; ins.
    apply (WCore.add_event_thrd ADD). }
  subst a_t'. subst b_t'. desf.
  exists l_a', a_s, X_s''.
  destruct STEPA as [ADD' RFC' CONS'].
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
  desf.
  set (mapper' := upd mapper b_t b_s).
  set (G_s' := {|
    acts_set := E_s ∪₁ eq a_s ∪₁ eq b_s;
    threads_set := threads_set G_s;
    lab := upd (upd lab_s a_s l_a') b_s l;
    rf := rf_s ∪
          mapper' ↑ (rf_t' ⨾ ⦗eq b_t⦘) ∪
          srf (WCore.G X_s'') ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘;
    co := co_s ∪
          mapper' ↑ (⦗eq b_t⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq b_t⦘) ∪
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
  assert (WF_S'' : Wf (WCore.G X_s'')).
  { apply (WCore.add_event_wf ADD').
    eapply G_s_wf with (X_t := X_t); eauto.
    red; eauto. }
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
  { intros x XINE FALSO. apply NOTIN. left.
    apply (rsr_codom SIMREL). basic_solver. }
  assert (MAPNEQ' : forall x (IN : E_t x), mapper x <> a_s).
  { intros x XINE FALSO. apply ANOTINS.
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
  assert (LABEQ' : eq_dom E_s (upd (upd lab_s a_s l_a') b_s l) lab_s).
  { rewrite (WCore.add_event_lab ADD') in LABEQ. unfolder.
    intros x XINE. rupd; ins; try congruence.
    intro FALSO. eapply NOTIN. left; congruence. }
  assert (MAPE : b_s = mapper' b_t).
  { unfold mapper'. now rewrite upds. }
  assert (SRF'': srf G_s' ⨾ ⦗acts_set (WCore.G X_s'')⦘ ≡
                srf (WCore.G X_s'') ⨾ ⦗acts_set (WCore.G X_s'')⦘).
  { apply (srf_add_event X_s'' X_s'); ins.
    { rewrite (WCore.add_event_acts ADD').
      basic_solver. }
    { rewrite (WCore.add_event_acts ADD'),
              (WCore.add_event_lab ADD').
      apply eq_dom_union. split; unfolder.
      all: intros x XIN; rupd; ins; try congruence.
      intro FALSO. apply NOTIN. left; congruence. }
    { unfold sb at 1. ins. rewrite NEWSB.
      rewrite (WCore.add_event_sb ADD'),
              (WCore.add_event_acts ADD').
      rewrite seq_union_l at 1.
      unfold WCore.sb_delta at 2.
      rewrite <- cross_inter_r.
      arewrite (eq b_s ∩₁ (E_s ∪₁ eq a_s) ≡₁ ∅).
      { generalize NOTIN. clear. basic_solver. }
      now rewrite cross_false_r, union_false_r. }
    { rewrite RF', (WCore.add_event_acts ADD'), !seq_union_l.
      rewrite MAPE in NOTIN. clear - NOTIN.
      arewrite_false (mapper' ↑ (rf_t' ⨾ ⦗eq b_t⦘) ⨾ ⦗E_s ∪₁ eq a_s⦘).
      { unfolder in NOTIN. basic_solver. }
      now rewrite union_false_r. }
    { rewrite CO', (WCore.add_event_acts ADD'), !seq_union_l,
              !seq_union_r.
      rewrite MAPE in NOTIN. clear - NOTIN.
      arewrite_false (⦗E_s ∪₁ eq a_s⦘ ⨾ mapper' ↑ (⦗eq b_t⦘ ⨾ co_t')).
      { unfolder in NOTIN. basic_solver. }
      arewrite_false (mapper' ↑ (co_t' ⨾ ⦗eq b_t⦘) ⨾ ⦗E_s ∪₁ eq a_s⦘).
      { unfolder in NOTIN. basic_solver. }
      now rewrite seq_false_l, seq_false_r, !union_false_r,
                  set_interC with (s := E_s). }
    rewrite RMW', (WCore.add_event_acts ADD'), (WCore.add_event_rmw ADD),
            collect_rel_union, seq_union_l.
    arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
    { apply collect_rel_eq_dom' with (s := E_t); ins.
      apply (wf_rmwE (rsr_Gt_wf CORR)). }
    arewrite_false (WCore.rmw_delta b_t r).
    { destruct r as [r|]; [| clear; basic_solver].
      exfalso. apply (rsr_bt_nrmw CORR') with b_t; ins.
      right. apply set_subset_single_l.
      rewrite (WCore.add_event_rmw ADD).
      clear. basic_solver. }
    now rewrite <- (rsr_rmw SIMREL), collect_rel_empty, seq_false_l,
                union_false_r. }
  assert (SIMREL'' : reord_simrel_gen X_s' X_t' a_t b_t mapper' a_s).
  { constructor; ins.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
        now apply SIMREL. }
      { clear. basic_solver. }
      rewrite MAPER_E, MAPSUB, (rsr_codom SIMREL), OLDEXA.
      clear - NOTIN. unfolder in NOTIN. basic_solver. }
    { rewrite NEWEXA. unfolder. intros x XEQ. subst x.
      constructor; ins.
      assert (SUBRF : rf (WCore.G X_s'') ⊆ same_val (upd (upd lab_s a_s l_a') b_s l)).
      { unfolder. unfold same_val. intros x y RF.
        apply (wf_rfE WF_S'') in RF. unfolder in RF.
        destruct RF as (DOM & RF & CODOM).
        apply (WCore.add_event_acts ADD') in DOM, CODOM.
        unfold val. rewrite !updo with (a := b_s).
        all: try congruence.
        apply (wf_rfv WF_S'') in RF.
        now rewrite (WCore.add_event_lab ADD') in RF. }
      rewrite <- SUBRF, RF'. apply inclusion_union_r. right.
      rewrite !id_inter.
      arewrite (⦗eq a_s⦘ ≡ ⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq a_s⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      seq_rewrite SRF''. rewrite seqA.
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq a_s⦘ ≡ ⦗eq a_s⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq a_s⦘ ≡ ⦗eq a_s⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      apply seq_more; ins. rewrite <- !id_inter.
      apply eqv_rel_more.
      arewrite (WCore.lab_is_r l_a ≡₁ WCore.lab_is_r l_a').
      { clear - LABU2V. unfold WCore.lab_is_r, same_label_u2v in *. desf. }
      rewrite <- (lab_is_rE ADD'), (WCore.add_event_lab ADD').
      clear - ANOTB. unfolder. split; ins; desf.
      all: split; ins; unfold is_r in *.
      all: rewrite upds, updo, ?upds in *; ins. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB,
              (rsr_codom SIMREL), NEWEXA, set_minus_union_l,
              OLDEXA, set_minus_union_l, set_minusK.
      clear - NOTIN ANOTB ANOTINS.
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
      arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
      { clear - ANOTIN'. basic_solver. }
      rewrite swap_rel_empty_r.
      rewrite (sb_deltaE ADD), set_collect_dom, (WCore.add_event_sb ADD),
              collect_rel_union, (rsr_sb SIMREL), OLDEXA,
              cross_false_l, cross_false_r, !union_false_r.
      arewrite (eq b_t ∩₁ E_t ≡₁ ∅).
      { clear - ENOTIN. basic_solver. }
      rewrite swap_rel_empty_l.
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
      { unfold same_tid. now rewrite TID, ATID. }
      arewrite (eq a_s ∩₁ same_tid a_s ≡₁ eq a_s).
      { clear. basic_solver. }
      clear. basic_solver 12. }
    { rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      rewrite NEWEXA.
      arewrite (eq a_s ∩₁ is_r (upd (upd lab_s a_s l_a') b_s l) ≡₁
                eq a_s ∩₁ WCore.lab_is_r l_a').
      { unfolder. split; intros x (EQ & ISR).
        all: split; ins; subst x; unfold is_r in *.
        all: rewrite updo, upds in *; try congruence.
        all: unfold WCore.lab_is_r in *; desf. }
      arewrite (srf G_s' ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a'⦘ ≡
                srf G_s' ⨾ ⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a'⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      seq_rewrite SRF''. rewrite seqA.
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a'⦘ ≡
                ⦗eq a_s ∩₁ WCore.lab_is_r l_a'⦘).
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
      arewrite (WCore.lab_is_r l_a ≡₁ WCore.lab_is_r l_a').
      { unfold WCore.lab_is_r, same_label_u2v in *. desf. }
      clear. basic_solver 12. }
    { rewrite (co_deltaE1 (rsr_Gt_wf CORR) ADD),
              (co_deltaE2 (rsr_Gt_wf CORR) ADD).
      rewrite (WCore.add_event_co ADD), !collect_rel_union,
              (rsr_co SIMREL).
      arewrite (mapper' ↑ co_t ≡ mapper ↑ co_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_coE (rsr_Gt_wf CORR)). }
      rewrite OLDEXA, set_inter_empty_l, add_max_empty_r, union_false_r.
      rewrite NEWEXA, !extra_co_D_union, !add_max_union.
      arewrite (extra_co_D (eq b_s) (upd (upd lab_s a_s l_a') b_s l)
                (loc (upd (upd lab_s a_s l_a') b_s l) a_s) ≡₁ ∅).
      { split; [| basic_solver].
        transitivity (same_loc (upd (upd lab_s a_s l_a') b_s l) a_s ∩₁ eq b_s).
        { clear. unfold same_loc. basic_solver. }
        clear - NEQLOC ANOTB LABU2V.
        unfolder. ins. desf.
        unfold same_loc, loc, WCore.lab_loc, same_label_u2v in *.
        rewrite upds, updo, upds in * by assumption.
        do 2 desf. }
      rewrite add_max_empty_l, union_false_r.
      rewrite add_max_sub
         with (A := extra_co_D (eq a_s) _ _)
           by basic_solver 11.
      rewrite union_false_r.
      rewrite extra_co_D_eq_dom with (ll1 := upd (upd lab_s a_s l_a') b_s l).
      all: eauto using same_lab_u2v_dom_inclusion.
      arewrite (eq a_s ∩₁ is_w (upd (upd lab_s a_s l_a') b_s l) ≡₁
                eq a_s ∩₁ WCore.lab_is_w l_a').
      { unfold is_w, WCore.lab_is_w. unfolder.
        split; intros x (EQ & LAB); split; ins; subst x.
        all: rewrite updo, upds in *; ins.
        all: desf. }
      arewrite (loc (upd (upd lab_s a_s l_a') b_s l) a_s = WCore.lab_loc l_a').
      { unfold loc, WCore.lab_loc. now rupd. }
      unfold add_max.
      arewrite (extra_co_D E_s lab_s (WCore.lab_loc l_a') \₁ eq a_s ∩₁ WCore.lab_is_w l_a'
                ≡₁ extra_co_D E_s lab_s (WCore.lab_loc l_a')).
      { rewrite set_minus_disjoint; ins.
        clear - ANOTINS. basic_solver. }
      unfold WCore.co_delta. rewrite collect_rel_union.
      arewrite (WCore.lab_is_w l_a ≡₁ WCore.lab_is_w l_a').
      { clear - LABU2V. unfold WCore.lab_is_w, same_label_u2v in *. desf. }
      arewrite (WCore.lab_loc l_a = (WCore.lab_loc l_a')).
      { clear - LABU2V. unfold WCore.lab_loc, same_label_u2v in *. do 2 desf. }
      clear. basic_solver 11. }
    { rewrite (WCore.add_event_threads ADD). apply SIMREL. }
    { rewrite (WCore.add_event_ctrl ADD). apply SIMREL. }
    { rewrite (WCore.add_event_data ADD). apply SIMREL. }
    { rewrite (WCore.add_event_addr ADD). apply SIMREL. }
    { rewrite (WCore.add_event_rmw_dep ADD). apply SIMREL. }
    arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
    { clear - ANOTIN'. basic_solver. }
    rewrite set_collect_empty. clear. basic_solver. }
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
    apply add_event_to_wf; ins.
    { rewrite (WCore.add_event_acts ADD').
      apply set_subset_union_r. left.
      eapply rsr_init_acts_s with (X_s := X_s) (X_t := X_t); eauto. }
    { rewrite <- MAPE.
      intro FALSO. apply (WCore.add_event_acts ADD') in FALSO.
      eauto. }
    { now rewrite <- MAPE. }
    { rewrite <- MAPE, TID, <- (rsr_at_bt_tid CORR). apply CORR. }
    { now rewrite (WCore.add_event_acts ADD'), MAPE. }
    { now rewrite (WCore.add_event_threads ADD'). }
    { now rewrite (WCore.add_event_lab ADD'), MAPE. }
    { rewrite <- mapped_rf_delta_R,
              <- mapped_rf_delta_W.
      rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, union_false_r,
              RF'.
      clear. basic_solver 11. }
    { rewrite (co_deltaE1 (rsr_Gt_wf CORR) ADD),
              (co_deltaE2 (rsr_Gt_wf CORR) ADD).
      rewrite <- mapped_co_delta, CO'.
      clear. basic_solver 11. }
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
    { unfold sb at 1. ins. now rewrite NEWSB, MAPE. }
    { now rewrite (rsr_ctrl SIMREL), (rsr_nctrl CORR). }
    eapply G_s_wf with (X_s := X_s') (X_t := X_t'); eauto. }
  { eapply G_s_rfc with (X_s := X_s') (X_t := X_t'); eauto. }
  admit. (* is_cons *)
Admitted.

Lemma prefix_exec_restr_eq X X' d
    (SUB : d ⊆₁ acts_set (WCore.G X))
    (PFX : SubToFullExec.prefix X X') :
  WCore.exec_restr_eq X X' d.
Proof using.
  constructor.
  all: try now apply PFX.
  { rewrite !set_inter_absorb_l; ins.
    now rewrite <- (prf_acts PFX). }
  { eapply eq_dom_mori; try now apply PFX.
    all: ins.
    unfold flip. rewrite SUB. basic_solver. }
  { now rewrite (prf_rf PFX), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_co PFX), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_rmw PFX), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_data PFX). }
  { now rewrite (prf_ctrl PFX). }
  now rewrite (prf_rmw_dep PFX).
Qed.

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
          mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘);
    co := restr_rel (E_s \₁ eq a_s) co_s ∪
          mapper' ↑ (⦗eq a_t⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq a_t⦘);
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
  assert (MAPEQ2 : eq_dom E_t mapper mapper').
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
  assert (INJ : inj_dom E_t' mapper').
  { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
    { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
      now apply SIMREL. }
    { basic_solver. }
    rewrite MAPSUB, MAPER_E. apply set_disjointE.
    split; [| basic_solver]. intros x (IN & EQ).
    subst x. now apply ANCODOM. }
  assert (NEWSBSIM : sb G_s' ≡ mapper' ↑ swap_rel sb_t' (eq b_t ∩₁ E_t') (eq a_t ∩₁ E_t')).
  { change (sb G_s') with sb_s.
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
    { rewrite sb_tid_init', seq_union_l, unionC, dom_union,
              set_minus_union_l.
      assert (NINIT : ~is_init b_t) by apply INV.
      arewrite (is_init \₁ eq b_t ≡₁ is_init).
      { split; [basic_solver|]. unfolder.
        ins. split; ins. intro FALSO; congruence. }
      arewrite (same_tid a_t ≡₁ same_tid b_t).
      { unfold same_tid. now rewrite (rsr_at_bt_tid INV). }
      apply set_union_more.
      { unfold sb. split; [|basic_solver 11].
        unfolder. ins. eexists. splits; eauto.
        { apply (rsr_init_acts INV); ins. }
        unfold ext_sb. desf; ins. }
      rewrite wf_sbE, <- seq_eqv_inter_lr, !seqA, <- id_inter.
      rewrite set_inter_absorb_l
          with (s := eq b_t)
            by basic_solver.
      unfolder. unfold same_tid.
      split; intros x HREL; desf; splits; ins.
      all: try now (intro FALSO; desf; eapply sb_irr; eauto).
      eexists; splits; eauto.
      destruct (sb_total G_t)
          with (tid b_t) x b_t
            as [RSB|LSB].
      all: ins; try congruence.
      { unfolder; splits; ins. intro FALSO; destruct x; ins.
        apply (rsr_at_tid CORR). now rewrite (rsr_at_bt_tid CORR). }
      exfalso. apply (rsr_bt_max CORR) with b_t x; ins.
      basic_solver 11. }
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
  assert (SIMREL' : reord_simrel_gen X_s' X_t' a_t b_t mapper' a_s).
  { constructor; ins.
    { rewrite NOEXA. basic_solver. }
    { rewrite (WCore.add_event_acts ADD), set_collect_union,
              MAPSUB, MAPER_E, (rsr_codom SIMREL), NOEXA, OLDEXA.
      basic_solver. }
    { rewrite (WCore.add_event_acts ADD). apply eq_dom_union.
      split; unfold compose; unfolder; intros x XINE.
      { rewrite MAPEQ; ins. now apply SIMREL. }
      subst x. unfold mapper'. rupd.
      rewrite (rsr_at_bt_tid CORR).
      symmetry. eapply eba_tid with (X_s := X_s).
      apply (rsr_as SIMREL), extra_a_some; ins. }
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
    { now rewrite NOEXA, cross_false_l, cross_false_r,
              !union_false_r. }
    { rewrite NOEXA, set_inter_empty_l,
              (rsr_rf SIMREL), seq_union_l, OLDEXA.
      rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      arewrite_false ((srf_s ⨾ ⦗eq a_s ∩₁ R_s⦘) ⨾ ⦗E_s \₁ eq a_s⦘).
      { clear. basic_solver. }
      rewrite eqv_empty, seq_false_r, !union_false_r,
              (WCore.add_event_rf ADD), !collect_rel_union.
      arewrite (mapper ↑ rf_t ⨾ ⦗E_s \₁ eq a_s⦘ ≡ mapper ↑ rf_t).
      { split; [clear; basic_solver 7|].
        rewrite (wf_rfE WF), <- OLDEXA, <- (rsr_codom SIMREL).
        clear. basic_solver. }
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE (rsr_Gt_wf CORR)). }
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      now rewrite collect_rel_empty, !union_false_r. }
    { rewrite NOEXA, set_inter_empty_l, add_max_empty_r,
              union_false_r.
      rewrite (co_deltaE1 WF ADD),
              (co_deltaE2 WF ADD).
      rewrite (WCore.add_event_co ADD). unfold WCore.co_delta.
      rewrite !collect_rel_union, <- !unionA.
      repeat apply union_more; ins.
      rewrite (rsr_co SIMREL), restr_union.
      arewrite (restr_rel (E_s \₁ eq a_s) (mapper ↑ co_t) ≡ mapper ↑ co_t).
      { split; [clear; basic_solver 11 |].
        rewrite <- OLDEXA, <- (rsr_codom SIMREL),
                collect_rel_restr, restr_relE.
        { apply collect_rel_mori; ins. apply WF. }
        eapply inj_dom_mori with (x := E_t); eauto; [| apply SIMREL].
        unfold flip. rewrite (wf_coE WF). clear. basic_solver. }
      rewrite restr_add_max, OLDEXA.
      arewrite (eq a_s ∩₁ W_s ∩₁ (E_s \₁ eq a_s) ≡₁ ∅).
      { clear. basic_solver. }
      rewrite add_max_empty_r, union_false_r.
      apply collect_rel_eq_dom' with (s := E_t); ins.
      apply (wf_coE (rsr_Gt_wf CORR)). }
    { now rewrite (rsr_threads SIMREL), (WCore.add_event_threads ADD). }
    { rewrite (WCore.add_event_ctrl ADD). apply SIMREL. }
    { rewrite (WCore.add_event_data ADD). apply SIMREL. }
    { rewrite (WCore.add_event_addr ADD). apply SIMREL. }
    { rewrite (WCore.add_event_rmw_dep ADD). apply SIMREL. }
    unfolder. intros x y (XINE & RPO & YINE).
    destruct XINE as (x' & (AEQ & XIN) & XEQ).
    destruct YINE as (y' & (BEQ & YIN) & YEQ).
    subst y. subst y'. subst x. subst x'.
    assert (RPOIMM : rpo_imm G_s' (mapper' a_t) (mapper' b_t)).
    { apply rpo_to_rpo_imm; ins.
      eapply rsr_as_bs_imm with (X_t := X_t'); eauto. }
    unfold rpo_imm in RPOIMM.
    assert (ANF : ~ (F G_s' (mapper' a_t))).
    { unfold is_f.
      arewrite (lab G_s' (mapper' a_t) = lab_t' a_t).
      { rewrite (WCore.add_event_lab ADD). unfold mapper'.
        ins. now rupd. }
      destruct (rsr_a_t_is_r_or_w CORR') with a_t.
      all: unfold is_r, is_w in *; desf. }
    assert (BNF : ~ (F G_s' (mapper' b_t))).
    { unfold is_f.
      arewrite (lab G_s' (mapper' b_t) = lab_t' b_t).
      { rewrite (WCore.add_event_lab ADD). unfold mapper'.
        ins. rupd; try congruence; eauto.
        change (lab_s (mapper b_t)) with ((lab_s ∘ mapper) b_t).
        rewrite (rsr_lab SIMREL); ins. }
      destruct (rsr_b_t_is_r_or_w CORR') with b_t.
      all: unfold is_r, is_w in *; desf. }
    assert (ANACQ : ~ (Acq G_s' (mapper' a_t))).
    { unfold is_acq, mod.
      arewrite (lab G_s' (mapper' a_t) = lab_t' a_t).
      { rewrite (WCore.add_event_lab ADD). unfold mapper'.
        ins. now rupd. }
      intro FALSO. apply (rsr_at_nacq CORR') with a_t.
      all: try split; ins. }
    assert (BNREL : ~ (Rel G_s' (mapper' b_t))).
    { unfold is_rel, mod.
      arewrite (lab G_s' (mapper' b_t) = lab_t' b_t).
      { rewrite (WCore.add_event_lab ADD). unfold mapper'.
        ins. rupd; try congruence; eauto.
        change (lab_s (mapper b_t)) with ((lab_s ∘ mapper) b_t).
        rewrite (rsr_lab SIMREL); ins. }
      intro FALSO. apply (rsr_bt_nrel CORR') with b_t.
      all: try split; ins. }
    unfolder in RPOIMM. desf. }
  assert (PFX : SubToFullExec.prefix (WCore.X_start X_s dtrmt') X_s').
  { assert (DT : dtrmt' ∩₁ E_s ≡₁ dtrmt').
    { unfold dtrmt'. basic_solver. }
    assert (INIT : is_init ⊆₁ dtrmt').
    { unfold dtrmt'. erewrite <- (rsr_init_acts_s INV).
      all: try red; eauto.
      unfolder. intros x XNIT.
      splits; ins.
      all: intro FALSO; subst x.
      { eapply rsr_as_ninit with (X_t := X_t); eauto.
        now apply OLDEXA. }
      assert (TID : (tid ∘ mapper) b_t = tid_init).
      { unfold compose. destruct (mapper b_t); ins. }
      rewrite (rsr_tid SIMREL) in TID; ins.
      apply (rsr_at_tid INV).
      now rewrite (rsr_at_bt_tid INV). }
    unfold X_s'. constructor; ins.
    { now rewrite DT, INIT. }
    { basic_solver. }
    { rewrite DT, INIT, set_unionK.
      unfold dtrmt'. unfolder; ins; desf.
      rupd. congruence. }
    { unfolder. ins. rupd. congruence. }
    { rewrite DT, restr_union, restr_relE,
              !seqA, <- id_inter.
      arewrite ((E_s \₁ eq a_s) ∩₁ dtrmt' ≡₁ dtrmt').
      { unfold dtrmt'. basic_solver. }
      arewrite_false (restr_rel dtrmt' (mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘))).
      { unfold dtrmt', mapper'. unfolder. ins; desf.
        rewrite upds, updo in *.
        all: congruence. }
      now rewrite union_false_r. }
    { rewrite DT, !restr_union, !restr_relE,
              !seqA, <- !id_inter.
      seq_rewrite <- !id_inter.
      rewrite set_interC.
      arewrite ((E_s \₁ eq a_s) ∩₁ dtrmt' ≡₁ dtrmt').
      { unfold dtrmt'. clear. basic_solver. }
      arewrite_false (⦗dtrmt'⦘ ⨾ mapper' ↑ (⦗eq a_t⦘ ⨾ co_t')).
      { unfold dtrmt', mapper'. unfolder. ins; desf.
        rewrite upds in *. congruence. }
      arewrite_false (mapper' ↑ (co_t' ⨾ ⦗eq a_t⦘) ⨾ ⦗dtrmt'⦘).
      { unfold dtrmt', mapper'. unfolder. ins; desf.
        rewrite upds in *. congruence. }
      now rewrite seq_false_l, seq_false_r, !union_false_r. }
    { rewrite DT, (WCore.add_event_rmw ADD),
              collect_rel_union, restr_union,
              !restr_relE, (rsr_rmw SIMREL).
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rmwE (rsr_Gt_wf CORR)). }
      arewrite_false (mapper' ↑ WCore.rmw_delta a_t r ⨾ ⦗dtrmt'⦘).
      { unfold dtrmt', mapper'. unfolder. ins; desf.
        rewrite upds in *. congruence. }
      now rewrite seq_false_r, union_false_r. }
    { rewrite (rsr_data SIMREL), (rsr_ndata CORR). basic_solver. }
    { rewrite (rsr_ctrl SIMREL), (rsr_nctrl CORR). basic_solver. }
    { rewrite (rsr_addr SIMREL), (rsr_naddr CORR). basic_solver. }
    { rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep CORR). basic_solver. }
    { now rewrite DT. }
    unfold SubExecution.restrict. rewrite wf_sbE; ins.
    unfold sb at 2. ins.
    rewrite !seqA, <- id_inter, set_interC, !DT.
    unfolder. intros x y (XINE & SB & YD).
    splits; ins; [| red in SB; unfolder in SB; desf].
    apply (rsr_sb SIMREL') in SB.
    destruct SB as [[SB | ESB] | ESB].
    { destruct SB as (x' & y' & SB & XEQ & YEQ).
      subst. unfold swap_rel in SB.
      assert (YNB : y' <> b_t).
      { intro FALSO. apply YD. subst y'.
        unfold mapper'. rupd. congruence. }
      assert (YNA : y' <> a_t).
      { intro FALSO. destruct YD as [YD _].
        apply YD. subst y'.
        unfold mapper'. now rupd. }
      destruct SB as [SB | EX]; [|unfolder in EX; desf].
      destruct SB as [SB BAN].
      assert (XNA : x' <> a_t).
      { intro FALSO; subst. apply (WCore.add_event_sb ADD) in SB.
        destruct SB as [SB|SB].
        all: unfold sb in SB; unfolder in SB.
        all: desf. }
      assert (XNB : x' <> b_t).
      { intro FALSO; subst. apply (WCore.add_event_sb ADD) in SB.
        destruct SB as [SB|SB].
        all: unfold sb in SB; unfolder in SB.
        all: desf.
        eapply (rsr_bt_max INV); ins.
        unfold sb; basic_solver. }
      assert (XIN : E_t x').
      { unfold sb in SB. unfolder in SB.
        destruct SB as (SB & _ & _).
        apply (WCore.add_event_acts ADD) in SB.
        destruct SB; congruence. }
      unfold mapper' in *. rewrite updo in *; ins.
      unfold dtrmt'. unfolder; splits; ins.
      { symmetry. eauto. }
      intro FALSO. apply (rsr_inj SIMREL) in FALSO.
      all: ins; congruence. }
    { unfolder in ESB.
      destruct ESB as (_ & FALSO).
      apply NOEXA in FALSO. desf. }
    unfolder in ESB.
    destruct ESB as (FALSO & _).
    apply NOEXA in FALSO. desf. }
  assert (STARTWF : WCore.wf (WCore.X_start X_s dtrmt') X_s' cmt').
  { constructor; ins.
    { apply prefix_wf with (X := WCore.X_start X_s dtrmt') (X' := X_s').
      all: ins.
      { rewrite (rsr_data SIMREL), (rsr_ndata INV). basic_solver. }
      { rewrite (rsr_addr SIMREL), (rsr_naddr INV). basic_solver. }
      { rewrite (rsr_ctrl SIMREL), (rsr_nctrl INV). basic_solver. }
      { rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep INV). basic_solver. }
      eapply G_s_wf with (X_s := X_s') (X_t := X_t'); eauto.
      red; eauto. }
    { apply prefix_exec_restr_eq; ins.
      basic_solver. }
    { unfold rf_complete, G_s', cmt'. ins.
      arewrite ((E_s \₁ eq a_s) ∩₁ E_s ≡₁ E_s \₁ eq a_s).
      { basic_solver. }
      arewrite ((E_s \₁ eq a_s) ∩₁ is_r (upd lab_s a_s l) ≡₁
                (E_s \₁ eq a_s) ∩₁ R_s).
      { unfolder. split; ins; desf; splits; ins.
        all: unfold is_r in *.
        all: rewrite updo in *; congruence. }
      rewrite seq_union_l, seq_union_r, !seqA.
      rewrite codom_union.
      arewrite_false (mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘) ⨾ ⦗E_s \₁ eq a_s⦘).
      { unfolder. intros x y HREL. desf.
        unfold mapper' in *.
        now rewrite upds in *. }
      rewrite seq_false_r, codom_empty, set_union_empty_r.
      seq_rewrite seq_eqvK. unfolder.
      intros x ((XINE & NEQ) & ISR).
      assert (RFC_S : rf_complete G_s).
      { eapply G_s_rfc with (X_t := X_t); eauto.
        red; eauto. }
      assert (WF_S : Wf G_s).
      { eapply G_s_wf with (X_t := X_t); eauto.
        red; eauto. }
      destruct RFC_S with x
            as (xw & RF); [split; ins|].
      exists xw; splits; ins.
      { apply (wf_rfE WF_S) in RF.
        unfolder in RF; desf. }
      intro FALSO; subst xw.
      apply (rsr_rf SIMREL) in RF.
      destruct RF as [RFT | SRF].
      { unfolder in RFT.
        destruct RFT as (x' & y' & RFT & EQ & _).
        apply MAPNEQ with x'; ins.
        apply (wf_rfE WF) in RFT.
        unfolder in RFT; desf. }
      unfolder in SRF. destruct SRF as (_ & EXA & _).
      apply OLDEXA in EXA. congruence. }
    { unfold dtrmt', cmt'. basic_solver 11. }
    admit. (* sc... *) }
  assert (STAB : WCore.stable_uncmt_reads_gen X_s' cmt' thrdle').
  { constructor; ins.
    { unfolder. subst thrdle'. ins.
      splits; try red; eauto. intro FALSO.
      apply (rsr_at_tid CORR).
      rewrite (rsr_at_bt_tid CORR), FALSO.
      now eapply eba_tid, SIMREL, extra_a_some. }
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
    destruct RF as (z & RF & YEQ' & ZEQ).
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
    { rewrite collect_rel_id. unfold rpo.
      arewrite (restr_rel cmt' (rpo_imm G_s')⁺ ⊆ (restr_rel cmt' (rpo_imm G_s'))⁺).
      { apply restr_rel_ct. unfold upward_closed, cmt'.
        intros x y RPOIMM CMT.
        assert (RPNEQ : forall (EQA : x = a_s) (EQB : y = mapper' b_t), False).
        { intros FALSO1 FALSO2; subst x; subst y.
          eapply (rsr_nrpo SIMREL') with a_s (mapper' b_t).
          unfold X_s'. ins.
          unfolder. splits; eauto.
          { exists a_t; splits; ins.
            unfold mapper'. now rupd. }
          unfold rpo. basic_solver. }
        apply rpo_imm_in_sb in RPOIMM. split.
        { unfold sb in RPOIMM; unfolder in RPOIMM; desf. }
        intro FALSO; subst x.
        apply (rsr_sb SIMREL') in RPOIMM.
        hahn_rewrite NOEXA in RPOIMM.
        hahn_rewrite cross_false_l in RPOIMM.
        hahn_rewrite cross_false_r in RPOIMM.
        do 2 hahn_rewrite union_false_r in RPOIMM.
        destruct RPOIMM as (x' & y' & RPOIMM & XEQ & YEQ).
        unfold swap_rel in RPOIMM.
        destruct RPOIMM as [[SB BAN] | SWP].
        { apply (WCore.add_event_sb ADD) in SB.
          destruct SB as [SB | DELTA].
          { unfold sb in SB. unfolder in SB. desf.
            unfold mapper' in XEQ.
            rewrite updo in XEQ by congruence.
            eapply MAPNEQ with x'; eauto. }
          unfolder in DELTA. destruct DELTA as (_ & HEQA).
          subst y'. unfold mapper' in YEQ.
          rewrite upds in YEQ. subst y.
          now apply CMT. }
        unfolder in SWP; desf. subst y'.
        apply RPNEQ; congruence. }
      apply clos_trans_mori. unfold rpo_imm.
      rewrite !restr_union, !restr_relE, !seqA.
      arewrite (⦗cmt'⦘ ⨾ ⦗R G_s' ∩₁ Rlx G_s'⦘ ≡ ⦗R_s ∩₁ Rlx_s⦘ ⨾ ⦗cmt'⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_r, is_rlx, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗cmt'⦘ ⨾ ⦗Acq G_s'⦘ ≡ ⦗Acq_s⦘ ⨾ ⦗cmt'⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_acq, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗cmt'⦘ ⨾ ⦗F G_s' ∩₁ Rel G_s'⦘ ≡ ⦗F_s ∩₁ Rel_s⦘ ⨾ ⦗cmt'⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_f, is_rel, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗F G_s' ∩₁ Acq G_s'⦘ ⨾ ⦗cmt'⦘ ≡ ⦗cmt'⦘ ⨾ ⦗F_s ∩₁ Acq_s⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_f, is_acq, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗Rel G_s'⦘ ⨾ ⦗cmt'⦘ ≡ ⦗cmt'⦘ ⨾ ⦗Rel_s⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_rel, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗W G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗cmt'⦘ ≡ ⦗cmt'⦘ ⨾ ⦗W_s ∩₁ Rlx_s⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_w, is_rlx, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      seq_rewrite <- !restr_relE.
      now arewrite (restr_rel cmt' (sb G_s') ⊆ sb_s). }
    { rewrite collect_rel_id, restr_union.
      apply inclusion_union_l; [basic_solver |].
      unfolder. intros x y ((x' & y' & (RF & EQ) & XEQ & YEQ) & CX & CY).
      exfalso. apply CY. rewrite <- YEQ, <- EQ.
      unfold mapper'. now rupd. }
    { rewrite collect_rel_id, !restr_union.
      repeat apply inclusion_union_l; [basic_solver | |].
      { unfolder. intros x y ((x' & y' & (EQ & CO) & XEQ & YEQ) & CX & CY).
        exfalso. apply CX. rewrite <- XEQ, <- EQ.
        unfold mapper'. now rupd. }
      unfolder. intros x y ((x' & y' & (CO & EQ) & XEQ & YEQ) & CX & CY).
      exfalso. apply CY. rewrite <- YEQ, <- EQ.
      unfold mapper'. now rupd. }
    rewrite collect_rel_id, (WCore.add_event_rmw ADD), collect_rel_union,
            restr_union.
    apply inclusion_union_l.
    { arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rmwE (rsr_Gt_wf CORR)). }
      rewrite (rsr_rmw SIMREL). basic_solver 11. }
    unfolder. intros x y ((x' & y' & (RO & EQ) & XEQ & YEQ) & CX & CY).
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
  { eapply G_s_wf with (X_s := X_s'); eauto.
    red; eauto. }
  { unfold dtrmt'.
    rewrite set_inter_absorb_r; [| basic_solver].
    rewrite !set_minus_minus_r, set_minusK, set_union_empty_l.
    apply set_subset_union_l. split.
    { unfolder. intros x (INE & XEQ) FALSO. subst x.
      eapply rsr_as_ninit with (x := a_s) (X_t := X_t); eauto.
      { apply extra_a_some; ins. }
      eapply rsr_ninit_acts_s with (X_t := X_t); eauto.
      { red; eauto. }
      split; ins. }
    unfolder. intros x (INE & XEQ) FALSO. subst x.
    assert (INIT : is_init b_t).
    { change (tid (mapper b_t)) with ((tid ∘ mapper) b_t) in FALSO.
      rewrite (rsr_tid SIMREL) in FALSO; ins.
      apply (rsr_ninit_acts CORR). split; ins. }
    apply (rsr_bt_ninit CORR); ins. }
  { admit. (* TODO: sc... *) }
  { now rewrite (rsr_data SIMREL), (rsr_ndata CORR). }
  { now rewrite (rsr_addr SIMREL), (rsr_naddr CORR). }
  { now rewrite (rsr_ctrl SIMREL), (rsr_nctrl CORR). }
  now rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep CORR).
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