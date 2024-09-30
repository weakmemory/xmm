Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
(* Require Import ThreadTrace. *)
Require Import Core.
(* Require Import TraceSwap. *)
Require Import SubToFullExec.
Require Import AuxRel.
Require Import AuxDef2.
Require Import StepOps.
Require Import Srf Rhb SrfProps.
Require Import AuxInj.
(* Require Import Instructions. *)
Require Import Setoid Morphisms.
Require Import SimrelCommon.
Require Import AddEvent.

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

Definition extra_co_D (s : actid -> Prop) ll l :=
  (s ∩₁ is_w ll ∩₁ (fun e => loc ll e = l)).

#[export]
Hint Unfold extra_co_D : unfolderDb.

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
  rsr_nrmw : rmw_t ⊆ (E_t \₁ eq a_t \₁ eq b_t) × (E_t \₁ eq a_t \₁ eq b_t);
  rsr_at_neq_bt : a_t <> b_t;
  rsr_nctrl : ctrl_t ≡ ∅₂;
  rsr_ndata : data_t ≡ ∅₂;
  rsr_naddr : addr_t ≡ ∅₂;
  rsr_nrmw_dep : rmw_dep_t ≡ ∅₂;
  rsr_ninit_acts : E_t ∩₁ Tid_ tid_init ⊆₁ is_init;
  rsr_at_nacq : eq a_t ∩₁ E_t ⊆₁ set_compl Acq_t;
  rsr_bt_nrel : eq b_t ∩₁ E_t ⊆₁ set_compl Rel_t;
  rsr_at_bt_imm : (eq b_t ∩₁ E_t) × (eq a_t ∩₁ E_t) ⊆ immediate sb_t;
  rsr_nat_spot : forall (NINA : ~E_t a_t),
                    ⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗E_t⦘ ⊆ ∅₂;
}.

Record reord_simrel : Prop := {
  rsr_inj : inj_dom E_t mapper;
  rsr_as : extra_a b_t ⊆₁ extra_a_pred;
  rsr_codom : mapper ↑₁ E_t ⊆₁ E_s \₁ extra_a b_t;
  rsr_init : fixset is_init mapper;
  rsr_tid : eq_dom E_t (tid ∘ mapper) tid;
  rsr_lab : eq_dom E_t (lab_s ∘ mapper) lab_t;
  rsr_acts : E_s ≡₁ mapper ↑₁ E_t ∪₁ extra_a b_t;
  rsr_sb : sb_s ≡
    mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t) ∪
    (mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘)) × (extra_a b_t) ∪
    (extra_a b_t) × eq b_s;
  rsr_rf : rf_s ≡ mapper ↑ rf_t ∪ srf_s ⨾ ⦗extra_a b_t ∩₁ R_s⦘;
  rsr_co : co_s ≡ mapper ↑ co_t ∪
    add_max
      (extra_co_D E_s lab_s (loc_s b_t))
      (extra_a b_t ∩₁ W_s);
  rsr_rmw : rmw_s ≡ mapper ↑ rmw_t;
  rsr_threads : threads_set G_s ≡₁ threads_set G_t;
  rsr_ctrl : ctrl_s ≡ ctrl_t;
  rsr_data : data_s ≡ data_t;
  rsr_addr : addr_s ≡ addr_t;
  rsr_rmw_dep : rmw_dep_s ≡ rmw_dep_t;
  rsr_nrpo : ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ⨾ rpo_s ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⊆ ∅₂;
  rsr_mid : eq_dom (E_t \₁ eq a_t \₁ eq b_t) mapper id;
  rsr_bt : mapper ↑₁ (eq b_t ∩₁ E_t) ⊆₁ eq a_t;
  rsr_at : mapper ↑₁ (eq a_t ∩₁ E_t) ⊆₁ eq b_t;
}.

Lemma rsr_common
    (SIMREL : reord_simrel) :
  simrel_common X_s X_t mapper.
Proof using.
  constructor; try now apply SIMREL.
  rewrite (rsr_acts SIMREL). clear. basic_solver.
Qed.

Lemma rsr_as_ninit
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  extra_a b_t ⊆₁ set_compl is_init.
Proof using.
  transitivity (same_tid b_t).
  { rewrite (rsr_as SIMREL). intros x HSET.
    apply HSET. }
  assert (NTID : tid b_t <> tid_init).
  { rewrite <- (rsr_at_bt_tid PRED). apply PRED. }
  unfold same_tid, is_init. clear - NTID.
  basic_solver.
Qed.

Lemma rsr_fin_s
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  set_finite (E_s \₁ is_init).
Proof using.
  rewrite (rsr_acts SIMREL), set_minus_union_l.
  apply set_finite_union. split.
  { eapply set_finite_mori with (x := mapper ↑₁ (E_t \₁ is_init)).
    { unfold flip. unfolder. ins. desf.
      eexists; splits; eauto. intro FAL.
      rewrite (rsr_init SIMREL) in *; auto. }
    apply set_finite_set_collect, PRED. }
  unfold extra_a; desf.
  all: eapply set_finite_mori with (x := eq b_t); auto with hahn.
  all: clear; unfold flip; basic_solver.
Qed.

Lemma rsr_tid' e
    (SIMREL : reord_simrel)
    (INE : E_t e) :
  tid e = tid (mapper e).
Proof using.
  rewrite <- (rsr_tid SIMREL); ins.
Qed.

Lemma rsr_same_tid' t
    (SIMREL : reord_simrel) :
  mapper ↑₁ (E_t ∩₁ Tid_ t) ≡₁
    mapper ↑₁ E_t ∩₁ Tid_ t.
Proof using.
  unfold same_tid. unfolder.
  split; ins; desf; splits; eauto.
  { symmetry. now apply rsr_tid'. }
  eexists; splits; eauto.
  now apply rsr_tid'.
Qed.

Lemma rsr_bt_tid
    (PRED : reord_step_pred) :
  tid b_t <> tid_init.
Proof using.
  rewrite <- (rsr_at_bt_tid PRED). apply PRED.
Qed.

Lemma rsr_ninit_exa_tid
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  extra_a b_t ∩₁ Tid_ tid_init ⊆₁ ∅.
Proof using.
  rewrite (rsr_as SIMREL).
  transitivity (same_tid b_t ∩₁ Tid_ tid_init).
  { apply set_subset_inter; [| ins].
    unfolder; ins. now apply eba_tid. }
  assert (NEQ : tid b_t <> tid_init).
  { now apply rsr_bt_tid. }
  clear - NEQ. unfold same_tid.
  unfolder. ins. desf. congruence.
Qed.

Lemma rsr_ninit_acts_s
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  E_s ∩₁ Tid_ tid_init ⊆₁ is_init.
Proof using.
  rewrite (rsr_acts SIMREL), set_inter_union_l.
  rewrite <- rsr_same_tid'; [| auto].
  rewrite rsr_ninit_exa_tid; ins.
  rewrite (rsr_ninit_acts PRED),
          <- (fixset_set_fixpoint (rsr_init SIMREL)).
  now rewrite set_union_empty_r.
Qed.

Lemma rsr_same_tid e
    (SIMREL : reord_simrel) :
  mapper ↑₁ (E_t ∩₁ same_tid e) ≡₁
    mapper ↑₁ E_t ∩₁ same_tid e.
Proof using.
  arewrite (same_tid e ≡₁ Tid_ (tid e)).
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
  unfold extra_co_D. now rewrite !set_inter_union_l.
Qed.

Lemma extra_co_D_minus s1 s2 ll l :
  extra_co_D s1 ll l \₁ s2 ≡₁ extra_co_D (s1 \₁ s2) ll l.
Proof using.
  unfold extra_co_D. now rewrite !set_inter_minus_l.
Qed.

Lemma extra_co_DE
    (GSIM : reord_simrel) :
  extra_co_D E_s lab_s (loc_s b_t) \₁ extra_a b_t ∩₁ W_s ≡₁
    mapper ↑₁ (E_t ∩₁ W_t ∩₁ Loc_t_ (loc_s b_t)).
Proof using.
  assert (DISJ : set_disjoint (mapper ↑₁ E_t) (extra_a b_t)).
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

Lemma rsr_as_val
    (SIMREL : reord_simrel) :
  srf_s ⨾ ⦗extra_a b_t ∩₁ R_s⦘ ⊆ same_val_s.
Proof using.
  unfolder. ins. desf. splits; ins.
  eapply eba_val; [| basic_solver].
  eapply rsr_as; eauto.
Qed.

Lemma G_s_co_total ol
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  is_total (E_s ∩₁ W_s ∩₁ (fun x => loc_s x = ol)) co_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  assert (TOT : is_total
                  (mapper ↑₁ E_t ∩₁ W_s ∩₁ Loc_s_ ol)
                  (mapper ↑ co_t)
  ).
  { apply sico_co_total; auto using rsr_common. }
  assert (MAPIN : mapper ↑₁ E_t ⊆₁ E_s).
  { auto using rsr_common, sico_codom. }
  rewrite (rsr_acts SIMREL), (rsr_co SIMREL).
  unfold extra_a; desf.
  all: try now (rewrite set_union_empty_r, set_inter_empty_l,
                        add_max_empty_r, union_false_r).
  rewrite !set_inter_union_l.
  unfold is_total. intros x XIN y YIN NEQ.
  assert (NEQ' : y <> x) by congruence.
  destruct XIN as [XIN | XIN],
           YIN as [YIN | YIN].
  { unfold union.
    destruct TOT with x y as [ORD | ORD].
    all: eauto. }
  all: clear - YIN XIN MAPIN NEQ.
  { left; right.
    unfolder in *. desf.
    eauto 11 using or_not_and. }
  { right; right.
    unfolder in *. desf.
    eauto 11 using or_not_and. }
  exfalso. unfolder in *. desf.
Qed.

Lemma G_s_rff
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  functional rf_s⁻¹.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  rewrite (rsr_rf SIMREL), transp_union.
  rewrite (wf_rfE WF).
  apply functional_union.
  { rewrite <- (wf_rfE WF).
    eapply sico_rff, rsr_common; try red; eauto. }
  { rewrite transp_seq, transp_eqv_rel.
    apply functional_seq; [basic_solver |].
    apply wf_srff'. auto using G_s_co_total. }
  clear - SIMREL. unfolder in *. ins. desf.
  eapply (rsr_codom SIMREL); basic_solver.
Qed.

Lemma G_s_rfE
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  rf_s ≡ ⦗E_s⦘ ⨾ rf_s ⨾ ⦗E_s⦘.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  apply dom_helper_3. rewrite (rsr_rf SIMREL).
  apply inclusion_union_l.
  { eapply sico_rfE, rsr_common; try red; eauto. }
  rewrite inclusion_seq_eqv_r.
  apply dom_helper_3, wf_srfE.
Qed.

Lemma G_s_co_trans
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  transitive co_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  assert (COL : forall ol, upward_closed co_t (Loc_t_ ol)).
  { unfold upward_closed. intros ol x y CO LOC.
    apply (wf_col WF) in CO. unfold same_loc in *.
    congruence. }
  assert (COE : upward_closed co_t E_t).
  { unfold upward_closed. intros x y CO YIN.
    apply (wf_coE WF) in CO. unfolder in CO; desf. }
  assert (COD : upward_closed co_t W_t).
  { unfold upward_closed. intros x y CO YD.
    apply (wf_coD WF) in CO. unfolder in CO; desf. }
  rewrite (rsr_co SIMREL).
  apply expand_transitive.
  { eapply sico_co_trans, rsr_common; try red; eauto. }
  { unfold upward_closed in *. intros x y REL XIN.
    apply (extra_co_DE SIMREL).
    apply (extra_co_DE SIMREL) in XIN.
    destruct REL as (x' & y' & CO & XEQ & YEQ). subst.
    destruct XIN as (y & ((YINE & ISW) & HLOC) & YMAP).
    apply (rsr_inj SIMREL) in YMAP; desf.
    { unfolder. eauto 11. }
    clear - CO WF.
    apply (wf_coE WF) in CO. unfolder in CO. desf. }
  arewrite (extra_a b_t ∩₁ W_s ⊆₁ set_compl (mapper ↑₁ E_t)).
  { rewrite (rsr_codom SIMREL). clear.
    unfolder. ins. desf. tauto. }
  rewrite (wf_coE WF). apply set_compl_mori.
  unfold flip. clear. basic_solver.
Qed.

Lemma G_s_co_irr
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  irreflexive co_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  rewrite (rsr_co SIMREL).
  apply irreflexive_union. split.
  { eapply sico_co_irr, rsr_common; try red; eauto. }
  unfold add_max. clear. basic_solver.
Qed.

Lemma G_s_co_l
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  co_s ⊆ same_loc_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  rewrite (rsr_co SIMREL).
  apply inclusion_union_l.
  { eapply sico_col, rsr_common; try red; eauto. }
  unfold extra_a. desf.
  { clear. basic_solver. }
  rewrite set_inter_empty_l, add_max_empty_r.
  clear. basic_solver.
Qed.

Lemma G_s_coE
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  co_s ≡ ⦗E_s⦘ ⨾ co_s ⨾ ⦗E_s⦘.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  apply dom_helper_3.
  rewrite (rsr_co SIMREL).
  apply inclusion_union_l.
  { eapply sico_coE, rsr_common; try red; eauto. }
  rewrite (rsr_acts SIMREL).
  unfold extra_a. desf.
  { basic_solver. }
  rewrite set_inter_empty_l, add_max_empty_r.
  clear. basic_solver.
Qed.

Lemma G_s_coD
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  co_s ≡ ⦗W_s⦘ ⨾ co_s ⨾ ⦗W_s⦘.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  apply dom_helper_3.
  rewrite (rsr_co SIMREL).
  apply inclusion_union_l.
  { eapply sico_coD, rsr_common; try red; eauto. }
  unfold extra_a. desf.
  { clear. basic_solver. }
  rewrite set_inter_empty_l, add_max_empty_r.
  clear. basic_solver.
Qed.

Lemma G_s_wf
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  Wf G_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  assert (NEXA : extra_a b_t ⊆₁ set_compl (mapper ↑₁ E_t)).
  { rewrite (rsr_codom SIMREL), set_compl_minus. basic_solver. }
  assert (IMM : mapper ↑ rmw_t ⊆
    immediate (mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t))).
  { rewrite collect_rel_immediate; [apply collect_rel_mori; ins|].
    { apply swap_rel_imm; [| apply WF].
      rewrite (rsr_nrmw PRED), set_compl_union. clear.
      unfolder. ins. desf. splits; tauto. }
    eapply inj_dom_mori; eauto using rsr_inj.
    unfold flip. rewrite wf_sbE. clear. basic_solver 11. }
  constructor.
  { intros x y (XIN & YIN & NEQ & TID & NINIT).
    destruct x as [xl | xt xn], y as [yl | yt yn]; try now ins.
    all: try now (ins; congruence).
    exfalso. apply NINIT, rsr_ninit_acts_s; ins. }
  { rewrite (rsr_data SIMREL), (rsr_ndata PRED).
    clear. basic_solver. }
  { rewrite (rsr_data SIMREL), (rsr_ndata PRED).
    clear. basic_solver. }
  { rewrite (rsr_addr SIMREL), (rsr_naddr PRED).
    clear. basic_solver. }
  { rewrite (rsr_addr SIMREL), (rsr_naddr PRED).
    clear. basic_solver. }
  { rewrite (rsr_ctrl SIMREL), (rsr_nctrl PRED).
    clear. basic_solver. }
  { rewrite (rsr_ctrl SIMREL), (rsr_nctrl PRED).
    clear. basic_solver. }
  { rewrite (rsr_ctrl SIMREL), (rsr_nctrl PRED).
    clear. basic_solver. }
  { apply dom_helper_3. rewrite (rsr_rmw SIMREL).
    eapply sico_rmwD, rsr_common; try red; eauto. }
  { rewrite (rsr_rmw SIMREL).
    eapply sico_rmwl, rsr_common; try red; eauto. }
  { rewrite (rsr_rmw SIMREL), (rsr_sb SIMREL).
    apply immediate_union_ignore.
    { rewrite (wf_rmwE WF), NEXA.
      clear. basic_solver. }
    { apply set_disjointE; split; [| clear; basic_solver].
      unfold extra_a. desf; [| clear; basic_solver].
      rewrite codom_cross; [| apply set_nonemptyE; eauto].
      rewrite (rsr_nrmw PRED), <- set_collect_codom, <- set_collect_eq.
      rewrite <- set_collect_interE.
      { clear. basic_solver. }
      eapply inj_dom_mori; eauto using rsr_inj.
      unfold flip. basic_solver. }
    apply immediate_union_ignore_alt; ins.
    all: apply set_disjointE; split; [| clear; basic_solver].
    all: rewrite 1?(rsr_nrmw PRED), NEXA, wf_sbE.
    all: clear; basic_solver. }
  { apply G_s_rfE; ins. }
  { apply dom_helper_3.
    rewrite (rsr_rf SIMREL).
    apply inclusion_union_l.
    { eapply sico_rfD, rsr_common; eauto. }
    rewrite inclusion_seq_eqv_r.
    apply dom_helper_3, wf_srfD. }
  { rewrite (rsr_rf SIMREL).
    apply inclusion_union_l.
    { eapply sico_rfl, rsr_common; eauto. }
    rewrite inclusion_seq_eqv_r.
    apply wf_srf_loc. }
  { rewrite (rsr_rf SIMREL).
    apply funeq_union.
    { eapply sico_rfv, rsr_common; eauto. }
    apply (rsr_as_val SIMREL). }
  { rewrite (rsr_rf SIMREL), transp_union, (wf_rfE WF).
    apply functional_union.
    { rewrite <- (wf_rfE WF).
      eapply sico_rff, rsr_common; eauto. }
    { rewrite transp_seq, transp_eqv_rel, inclusion_seq_eqv_l.
      apply wf_srff'. intros ol.
      apply G_s_co_total with (ol := ol); ins. }
    clear - NEXA. unfolder in *.
    ins; desf; eapply NEXA; eauto. }
  { apply G_s_coE; ins. }
  { apply G_s_coD; ins. }
  { apply G_s_co_l; ins. }
  { apply G_s_co_trans; ins. }
  { ins; apply G_s_co_total with (ol := ol); ins. }
  { apply G_s_co_irr; ins. }
  { intros. eapply sico_init_acts_s.
    { eapply rsr_common; eauto. }
    { apply PRED. }
    easy. }
  { intros l. rewrite <- (rsr_init SIMREL); ins.
    erewrite <- sico_lab' with (X_t := X_t).
    { apply (wf_init_lab WF). }
    { now apply rsr_common. }
    now apply (rsr_init_acts PRED). }
  { rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep PRED).
    clear. basic_solver. }
  { rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep PRED).
    clear. basic_solver. }
  intros x XIN. apply (rsr_acts SIMREL) in XIN.
  destruct XIN as [XIN | EQ]; apply (rsr_threads SIMREL).
  { unfolder in XIN. desf.
    rewrite <- rsr_tid'.
    all: try now (try red; eauto using wf_init_lab).
    now apply (wf_threads WF). }
  unfold extra_a in EQ; desf.
  now apply WF.
Qed.

Lemma G_s_rfc
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  rf_complete G_s.
Proof using.
  assert (WF : Wf G_t) by apply PRED.
  assert (RFC : rf_complete G_t) by apply PRED.
  unfold rf_complete.
  rewrite (rsr_acts SIMREL), set_inter_union_l,
          (rsr_rf SIMREL), codom_union.
  apply set_union_mori.
  { eapply sico_partial_rfc; [| assumption].
    now apply rsr_common. }
  clear RFC. unfolder.
  intros r. ins. desf.
  assert (WF_S : Wf G_s).
  { eapply G_s_wf; try red; eauto. }
  assert (HLOC : exists l, loc_s r = Some l); desf.
  { unfold loc, is_r in *. desf.
    eexists; eauto. }
  edestruct srf_exists
       with (G := G_s) (r := r) (l := l)
         as (w & SRF).
  all: try now apply WF_S.
  all: eauto 11.
  { apply (rsr_acts SIMREL). now right. }
  { eapply rsr_as_ninit; eauto. }
  { eapply sico_init_acts_s.
    { eapply rsr_common; try red; eauto. }
    { apply PRED. }
    easy. }
  apply rsr_fin_s; try red; eauto.
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

Lemma rsr_init_acts_s
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  is_init ⊆₁ E_s.
Proof using.
  rewrite (fixset_set_fixpoint (rsr_init SIMREL)).
  rewrite (rsr_init_acts PRED), (rsr_codom SIMREL).
  clear. basic_solver.
Qed.

Lemma rsr_map_bt
    (IN : E_t b_t)
    (SIMREL : reord_simrel) :
  mapper b_t = a_t.
Proof using.
  symmetry. apply (rsr_bt SIMREL).
  basic_solver.
Qed.

Lemma rsr_map_at
    (IN : E_t a_t)
    (SIMREL : reord_simrel) :
  mapper a_t = b_t.
Proof using.
  symmetry. apply (rsr_at SIMREL).
  basic_solver.
Qed.

Lemma rsr_actsE
    (CORR : reord_step_pred)
    (SIMREL : reord_simrel) :
  E_s ≡₁ E_t ∪₁ extra_a a_t.
Proof using.
  rewrite (rsr_acts SIMREL).
  destruct classic with (E_t a_t) as [INA|NINA],
           classic with (E_t b_t) as [INB|NINB].
  { rewrite !extra_a_none_l, !set_union_empty_r; auto.
    rewrite set_union_minus
      with (s := E_t) (s' := eq a_t ∪₁ eq b_t); [| basic_solver].
    rewrite !set_collect_union, <- set_minus_minus_l.
    rewrite set_collect_eq_dom with (g := id); [| apply SIMREL].
    rewrite <- set_inter_absorb_r
       with (s := eq a_t) (s' := E_t)
         at 2
         by basic_solver.
    rewrite <- set_inter_absorb_r
       with (s := eq b_t) (s' := E_t)
         at 2
         by basic_solver.
    rewrite !set_inter_absorb_r by basic_solver.
    arewrite (mapper ↑₁ eq a_t ≡₁ eq b_t).
    { unfolder. split; ins; desf.
      all: eauto using rsr_map_at.
      symmetry; eauto using rsr_map_at. }
    arewrite (mapper ↑₁ eq b_t ≡₁ eq a_t).
    { unfolder. split; ins; desf.
      all: eauto using rsr_map_bt.
      symmetry; eauto using rsr_map_bt. }
    basic_solver 11. }
  { exfalso. now apply NINB, (rsr_at_bt_ord CORR). }
  { rewrite !extra_a_some by auto.
    rewrite set_union_minus
      with (s := E_t) (s' := eq b_t); [| basic_solver].
    arewrite (E_t ≡₁ E_t \₁ eq a_t).
    { rewrite set_minus_disjoint; basic_solver. }
    rewrite set_collect_union.
    rewrite set_collect_eq_dom with (g := id); [| apply SIMREL].
    rewrite <- set_inter_absorb_r
       with (s := eq b_t) (s' := E_t)
         at 2
         by basic_solver.
    rewrite !set_inter_absorb_r by basic_solver.
    arewrite (mapper ↑₁ eq b_t ≡₁ eq a_t).
    { unfolder. split; ins; desf.
      all: eauto using rsr_map_bt.
      symmetry; eauto using rsr_map_bt. }
    basic_solver 11. }
  rewrite 2!extra_a_none_r, 2!set_union_empty_r; auto.
  arewrite (E_t ≡₁ E_t \₁ eq a_t \₁ eq b_t).
  { rewrite 2!set_minus_disjoint; basic_solver. }
  rewrite set_collect_eq_dom with (g := id); [| apply SIMREL].
  basic_solver 11.
Qed.

End SimRel.

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
    (INIT : threads tid_init)
    (ABSB : ext_sb b_t a_t) :
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
  split; red.
  all: constructor; ins.
  all: rewrite ?extra_a_none_r by ins.
  { clear; basic_solver. }
  { clear; basic_solver. }
  { clear; basic_solver. }
  { now rewrite cross_false_l,
            cross_false_r, AI, BI, !union_false_r,
            swap_rel_empty_l, collect_rel_id. }
  { clear; basic_solver. }
  { clear; basic_solver. }
  { clear; basic_solver. }
  { rewrite AI, BI, set_collect_empty. clear. basic_solver. }
  { rewrite BI. clear. basic_solver. }
  { rewrite AI. clear. basic_solver. }
  { red. ins. unfold is_r, WCore.init_lab.
    clear. basic_solver. }
  all: rewrite ?AI, ?BI, ?set_minusK.
  all: try now apply set_finite_empty.
  all: rewrite ?dom_empty, ?codom_empty, ?set_union_empty_r.
  all: clear - NINA; try basic_solver.
  unfold ext_sb. unfolder. ins. desf.
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
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  assert (CORR : reord_step_pred X_t a_t b_t); ins.
  assert (CORR' : reord_step_pred X_t' a_t b_t); ins.
  assert (ENINIT : ~is_init e) by apply ADD.
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq e) by apply ADD.
  assert (E_TID : tid e <> tid_init).
  { intro FALSO. apply ENINIT.
    apply (rsr_ninit_acts CORR'). split; ins.
    apply EQACTS. clear. now right. }
  assert (A_PRESERVED : E_t' a_t <-> E_t a_t).
  { clear - ADD E_NOT_A EQACTS. split; intros INA.
    { apply ADD in INA. destruct INA; congruence. }
    apply ADD. now left. }
  assert (B_PRESERVED : E_t' b_t <-> E_t b_t).
  { clear - ADD E_NOT_B EQACTS. split; intros INB.
    { apply ADD in INB. destruct INB; congruence. }
    apply ADD. now left. }
  assert (ETID : forall (WITHA : tid e = tid b_t), ~(~E_t a_t /\ E_t b_t)).
  { intros ETID (NINA & INB).
    enough (FSB : (⦗eq b_t ∩₁ E_t'⦘ ⨾ sb_t') b_t e).
    { eapply (rsr_bt_max CORR' _ _ FSB). }
    enough (FSB : sb_t' b_t e).
    { clear - FSB INB B_PRESERVED. basic_solver. }
    apply (WCore.add_event_sb ADD). clear - INB ETID.
    right. unfold WCore.sb_delta, same_tid.
    basic_solver. }
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (NEWE :
  << NINIT : ~is_init e >> /\
  << NOTIN : ~E_s e >> /\
  << TID : tid e = tid e >> /\
  << NEWSB : ⦗E_s ∪₁ eq e⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq e⦘ ≡
          sb_s ∪ WCore.sb_delta e E_s >>).
  { unfold NW. splits; auto; try now apply ADD'.
    { intro FALSO.
      eapply rsr_actsE
        with (X_t := X_t) (a_t := a_t) (b_t := b_t)
          in FALSO; eauto.
      destruct FALSO as [INE|EQEXA]; [now apply ADD|].
      unfold extra_a in EQEXA; desf. }
    destruct classic with (tid e = tid b_t)
          as [EQT|NQT].
    { unfold sb.
      rewrite (rsr_actsE CORR SIMREL).
      unfold extra_a; desf; [exfalso; now apply ETID|].
      rewrite set_union_empty_r.
      rewrite <- EQACTS. apply ADD. }
    unfold sb.
    rewrite rsr_actsE
      with (X_s := X_s) (X_t := X_t)
           (a_t := a_t) (b_t := b_t); eauto.
    unfold extra_a; desf.
    { rewrite <- (rsr_at_bt_tid CORR) in NQT.
      rewrite id_union, !seq_union_l, !seq_union_r.
      arewrite_false (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗eq e⦘).
      { clear. unfolder. ins. desf.
        eapply ext_sb_irr; eauto. }
      arewrite_false (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗E_t ∪₁ eq a_t⦘).
      { admit. }
      rewrite id_union at 3. rewrite seq_union_l.
      arewrite_false (⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗eq e⦘).
      { clear - NQT CORR. unfolder. unfold ext_sb.
        ins. desf; ins; [| desf].
        apply (rsr_at_ninit CORR). auto. }
      rewrite sb_delta_union.
      assert (SUB : WCore.sb_delta e (eq a_t) ⊆ WCore.sb_delta e E_t).
      { clear - NQT. unfolder. ins. desf. auto. }
      rewrite union_absorb_r with (r := WCore.sb_delta e (eq a_t)); auto.
      rewrite !union_false_r. apply union_more; [reflexivity |].
      arewrite (⦗E_t⦘ ⨾ ext_sb ⨾ ⦗eq e⦘ ≡ ⦗E_t⦘ ⨾ sb_t' ⨾ ⦗eq e⦘).
      { unfold sb. rewrite !seqA. seq_rewrite <- !id_inter.
        rewrite EQACTS. clear - ENOTIN. basic_solver 11. }
      rewrite (WCore.add_event_sb ADD), seq_union_l.
      arewrite_false (sb_t ⨾ ⦗eq e⦘).
      { clear - ENOTIN. rewrite wf_sbE. basic_solver. }
      rewrite union_false_l. unfold WCore.sb_delta.
      seq_rewrite <- cross_inter_l.
      rewrite set_inter_union_r, 2!set_inter_absorb_l.
      all: try now apply CORR.
      all: basic_solver 11. }
    rewrite !set_union_empty_r.
    rewrite <- EQACTS. apply ADD. }
  unfold NW in NEWE.
  destruct NEWE as (NINIT & NOTIN & TID & NEWSB).
  (* Asserts *)
  set (mapper' := upd mapper e e).
  assert (WF : Wf G_t) by apply INV.
  assert (WF' : Wf G_t') by apply INV'.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    clear - ENOTIN XINE. rewrite updo.
    all: congruence. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { clear - MAPEQ. now apply set_collect_eq_dom. }
  assert (LABSUB : eq_dom E_t lab_t' lab_t).
  { rewrite (WCore.add_event_lab ADD). clear - ENOTIN.
    unfold eq_dom. intros x XINE. rewrite updo.
    all: congruence. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> e).
  { intros x XINE FALSO. apply NOTIN, (rsr_codom SIMREL).
    red. exists x; split; [exact XINE | exact FALSO]. }
  assert (MAPER_E : mapper' ↑₁ eq e ≡₁ eq e).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (EXEQ : extra_a X_t a_t b_t b_t ≡₁ extra_a X_t' a_t b_t b_t).
  { clear - A_PRESERVED B_PRESERVED.
    unfold extra_a; do 2 desf; exfalso; tauto. }
  assert (EXIN : extra_a X_t a_t b_t b_t ⊆₁ E_s).
  { rewrite (rsr_acts SIMREL). auto with hahn. }
  assert (LABEQ : eq_dom E_s (upd lab_s e l) lab_s).
  { unfold eq_dom. intros. rupd. congruence. }
  assert (U2V : same_lab_u2v_dom E_s (upd lab_s e l) lab_s).
  { unfold same_lab_u2v_dom. ins. rewrite LABEQ; ins.
    unfold same_label_u2v. desf. }
  set (G_s' := {|
    acts_set := E_s ∪₁ eq e;
    threads_set := threads_set G_s;
    lab := upd lab_s e l;
    rf := rf_s ∪ mapper' ↑ (rf_t' ⨾ ⦗eq e⦘);
    co := co_s ∪
          mapper' ↑ (⦗eq e⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq e⦘) ∪
          add_max (eq e ∩₁ WCore.lab_is_w l)
            (extra_a X_t' a_t b_t b_t ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l));
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
  assert (SAMETID : same_tid e ≡₁ same_tid e).
  { unfold same_tid. reflexivity. }
  assert (AS_TID : extra_a X_t a_t b_t b_t ⊆₁ same_tid b_t).
  { rewrite (rsr_as SIMREL). unfolder. intros x XIN. apply XIN. }
  assert (NOTIN' : ~ E_s (mapper' e)).
  { unfold mapper'. now rewrite upds. }
  assert (ENEXA : ~ extra_a X_t' a_t b_t b_t e).
  { clear - EXEQ NOTIN EXIN.
    intro FALSO. now apply EXEQ, EXIN in FALSO. }
  assert (ASTID : forall (AS : ~ E_t a_t /\ E_t b_t), same_tid b_t b_t).
  { intros. eapply eba_tid, (rsr_as SIMREL). now apply extra_a_some. }
  assert (SRF' : srf G_s' ⨾ ⦗E_s⦘ ≡ srf G_s ⨾ ⦗E_s⦘).
  { apply (srf_add_event X_s X_s'); simpl.
    { eapply G_s_wf with (X_t := X_t); eauto. }
    { clear. auto with hahn. }
    { exact LABEQ. }
    { unfold sb at 1. simpl. rewrite NEWSB.
      clear - NOTIN. rewrite seq_union_l. basic_solver. }
    { clear - NOTIN'. basic_solver. }
    { clear - NOTIN NOTIN'. basic_solver 7. }
    rewrite (WCore.add_event_rmw ADD), (rsr_rmw SIMREL).
    rewrite collect_rel_union. unfold mapper'.
    rewrite sico_mapper_swap with (X_t := X_t); eauto; [| apply (wf_rmwE WF)].
    clear - NOTIN' NOTIN. basic_solver 7. }
  assert (SRF'' : srf G_s' ⨾ ⦗extra_a X_t a_t b_t b_t ∩₁ R_s⦘ ≡
                  srf G_s ⨾ ⦗extra_a X_t a_t b_t b_t ∩₁ R_s⦘).
  { arewrite (⦗extra_a X_t a_t b_t b_t ∩₁ R_s⦘ ≡ ⦗E_s⦘ ⨾ ⦗extra_a X_t a_t b_t b_t ∩₁ R_s⦘).
    { clear - EXIN. rewrite <- id_inter.
      apply eqv_rel_more. basic_solver. }
    seq_rewrite SRF'. now rewrite seqA. }
  assert (SRFE : srf_s ⨾ ⦗extra_a X_t a_t b_t b_t ∩₁ R_s⦘ ⊆ ⦗E_s⦘ ⨾ (srf_s ⨾ ⦗extra_a X_t a_t b_t b_t ∩₁ R_s⦘) ⨾ ⦗E_s⦘).
  { clear. rewrite wf_srfE at 1. basic_solver. }
  assert (TIDACTS : E_s ∩₁ same_tid e ≡₁ (mapper ↑₁ E_t) ∩₁ same_tid e).
  { split; [| rewrite (rsr_codom SIMREL); clear; basic_solver].
    rewrite (rsr_acts SIMREL), set_inter_union_l.
    apply set_subset_union_l. split; [reflexivity |].
    clear - ETID. unfold extra_a, same_tid in *.
    unfolder. ins. desf. split; [exfalso|]; tauto. }
  assert (EQTIDDOM : eq_dom (is_init ∪₁ E_t ∩₁ same_tid e) mapper' mapper).
  { eapply eq_dom_mori; eauto.
    unfold flip. rewrite (rsr_init_acts CORR).
    clear. basic_solver. }
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper').
  { constructor; simpl.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { clear - SIMREL MAPEQ.
        unfolder. ins. apply (rsr_inj SIMREL); ins.
        now rewrite <- !MAPEQ. }
      { clear. basic_solver. }
      rewrite MAPER_E, MAPSUB, (rsr_codom SIMREL).
      clear - NOTIN. basic_solver. }
    { rewrite <- EXEQ. unfolder.
      intros x XIN. ins. constructor.
      { now apply (rsr_as SIMREL). }
      change (WCore.G X_s') with G_s'.
      assert (XIN' : extra_a X_t' a_t b_t b_t x).
      { now apply EXEQ. }
      arewrite (⦗eq x ∩₁ R G_s'⦘ ⊆ ⦗extra_a X_t a_t b_t b_t ∩₁ R_s⦘).
      { apply eqv_rel_mori. clear - XIN XIN' ENEXA.
        unfolder. ins. desf. splits; ins.
        unfold is_r in *. now rewrite updo in * by congruence. }
      rewrite SRF'', SRFE, (rsr_as_val SIMREL).
      clear - NOTIN. unfolder. ins. desf.
      unfold same_val, val in *.
      now rewrite !updo by congruence. }
    { rewrite (WCore.add_event_acts ADD),
              set_collect_union, set_collect_eq.
      rewrite set_collect_eq_dom; [| eassumption].
      unfold mapper'. rewrite upds, (rsr_codom SIMREL), EXEQ.
      clear - ENEXA. basic_solver. }
    { unfold fixset, mapper'. intros.
      rupd; [| congruence].
      now apply (rsr_init SIMREL). }
    { rewrite EQACTS. apply eq_dom_union. split.
      all: unfold compose, eq_dom.
      { intros x XIN. rewrite MAPEQ; ins. now apply SIMREL. }
      now subst mapper'; ins; desf; rupd. }
    { rewrite EQACTS, (WCore.add_event_lab ADD).
      apply eq_dom_union; split; subst mapper'.
      { unfolder. intros x XIN.
        unfold compose. rupd; try congruence; eauto.
        now rewrite <- (rsr_lab SIMREL) by basic_solver. }
      unfolder. ins. desf. unfold compose. now rupd. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB.
      rewrite (rsr_acts SIMREL), EXEQ. clear. basic_solver 7. }
    { unfold sb at 1. ins. rewrite NEWSB, <- EXEQ.
      rewrite (rsr_sb SIMREL).
      arewrite (sb_t' ⨾ ⦗eq b_t⦘ ≡ sb_t ⨾ ⦗eq b_t⦘).
      { rewrite (WCore.add_event_sb ADD), seq_union_l.
        clear - E_NOT_B. basic_solver. }
      arewrite (mapper' b_t = mapper b_t).
      { unfold mapper'. now rupd. }
      arewrite (eq a_t ∩₁ E_t' ≡₁ eq a_t ∩₁ E_t).
      { clear - A_PRESERVED. basic_solver. }
      arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t).
      { clear - B_PRESERVED. basic_solver. }
      rewrite (WCore.add_event_sb ADD), swap_rel_unionE.
      arewrite (WCore.sb_delta e E_t \ (eq b_t ∩₁ E_t) × (eq a_t ∩₁ E_t) ≡
                WCore.sb_delta e E_t).
      { clear - E_NOT_A ENOTIN. split; [basic_solver 11 |].
        unfolder. ins. desf; splits; eauto using or_not_and. }
      rewrite collect_rel_union.
      unfold WCore.sb_delta. rewrite collect_rel_cross, set_collect_eq.
      rewrite set_collect_eq_dom with (g := mapper) (f := mapper'),
              set_collect_union, <- (fixset_set_fixpoint (rsr_init SIMREL)),
              rsr_same_tid, TIDACTS.
      all: eauto.
      unfold mapper'. rewrite upds.
      rewrite sico_mapper_swap with (X_t := X_t),
              sico_mapper_swap_set with (X_t := X_t).
      { clear. basic_solver 20. }
      all: eauto.
      { rewrite wf_sbE. clear. basic_solver. }
      rewrite wf_sbE at 1. basic_solver 11. }
    { arewrite (extra_a X_t' a_t b_t b_t ∩₁ is_r (upd lab_s e l) ≡₁
                extra_a X_t a_t b_t b_t ∩₁ R_s).
      { rewrite <- EXEQ. apply same_lab_u2v_dom_is_r.
        eapply same_lab_u2v_dom_inclusion with (s := E_s); eauto. }
      rewrite SRF'', (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      rewrite (rsr_rf SIMREL), (WCore.add_event_rf ADD),
              !collect_rel_union.
      rewrite (add_event_to_rf_complete ADD); try now apply CORR.
      rewrite collect_rel_empty, union_false_r.
      unfold mapper'.
      rewrite sico_mapper_swap with (X_t := X_t) (r := rf_t).
      all: eauto using wf_rfE.
      clear. basic_solver 12. }
    { rewrite (co_deltaE1 (rsr_Gt_wf CORR) ADD),
            (co_deltaE2 (rsr_Gt_wf CORR) ADD).
      rewrite (WCore.add_event_co ADD), !collect_rel_union,
              (rsr_co SIMREL).
      unfold mapper'.
      rewrite sico_mapper_swap with (r := co_t) (X_t := X_t).
      all: eauto using wf_coE.
      rewrite <- EXEQ, extra_co_D_union, add_max_union.
      rewrite extra_co_D_eq_dom with (ll1 := upd lab_s e l),
              same_lab_u2v_dom_is_w with (lab1 := upd lab_s e l).
      all: eauto using same_lab_u2v_dom_inclusion.
      rewrite extra_co_eq, upds.
      rewrite !add_max_disjoint with (A := eq e ∩₁ _) by basic_solver.
      rewrite !add_max_disjoint with (A := eq e ∩₁ _ ∩₁ _) by basic_solver.
      rewrite <- unionA. unfold extra_a; desf; [| clear; basic_solver 12].
      arewrite (loc (upd lab_s e l) b_t = loc lab_s b_t).
      { unfold loc. rupd. intro FALSO. desf. }
      clear. basic_solver 12. }
    { clear. reflexivity. }
    { rewrite (WCore.add_event_threads ADD). apply SIMREL. }
    { rewrite (WCore.add_event_ctrl ADD). apply SIMREL. }
    { rewrite (WCore.add_event_data ADD). apply SIMREL. }
    { rewrite (WCore.add_event_addr ADD). apply SIMREL. }
    { rewrite (WCore.add_event_rmw_dep ADD). apply SIMREL. }
    { destruct classic with (E_t' b_t)
            as [INB|NINB]; [| clear - NINB; basic_solver].
      destruct classic with (E_t' a_t)
            as [INA|NINA]; [| clear - NINA; basic_solver].
      arewrite (eq a_t ∩₁ E_t' ≡₁ eq a_t ∩₁ E_t).
      { clear - A_PRESERVED. basic_solver. }
      arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t).
      { clear - B_PRESERVED. basic_solver. }
      rewrite !set_collect_eq_dom with (f := mapper') (g := mapper).
      all: try (eapply eq_dom_mori with (x := E_t); eauto).
      all: unfold flip; try (clear; basic_solver).
      assert (INBS : mapper ↑₁ (eq b_t ∩₁ E_t) ⊆₁ E_s).
      { transitivity (mapper' ↑₁ E_t); [basic_solver |].
        rewrite MAPSUB, (rsr_codom SIMREL). clear. basic_solver. }
      arewrite (rpo G_s' ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⊆
                rpo G_s' ⨾ ⦗E_s⦘ ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘).
      { rewrite <- id_inter, set_inter_absorb_l with (s' := E_s).
        all: ins. }
      arewrite (rpo G_s' ⨾ ⦗E_s⦘ ≡ rpo_s ⨾ ⦗E_s⦘).
      { apply (add_event_rpo X_s X_s'); simpl.
        { eapply G_s_wf with (X_t := X_t); eauto. }
        { exact LABEQ. }
        unfold sb at 1. ins. rewrite NEWSB.
        rewrite seq_union_l. clear - NOTIN.
        basic_solver 11. }
      rewrite <- id_inter, set_inter_absorb_l with (s' := E_s).
      { apply SIMREL. }
      ins. }
    { rewrite EQACTS, !set_minus_union_l.
      apply eq_dom_union. split.
      { intros x XIN. desf. rewrite MAPEQ, (rsr_mid SIMREL).
        all: auto.
        clear - XIN. unfolder in XIN. desf. }
      unfold mapper'. clear. unfolder; ins; desf.
      now rewrite upds. }
    { arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t).
      { clear - B_PRESERVED. basic_solver. }
      rewrite set_collect_eq_dom with (g := mapper).
      { apply SIMREL. }
      eapply eq_dom_mori with (x := E_t); eauto.
      red. clear. basic_solver. }
    arewrite (eq a_t ∩₁ E_t' ≡₁ eq a_t ∩₁ E_t).
    { clear - A_PRESERVED. basic_solver. }
    rewrite set_collect_eq_dom with (g := mapper).
    { apply SIMREL. }
    eapply eq_dom_mori with (x := E_t); eauto.
    red. clear. basic_solver. }
  (* Actual proof *)
  exists mapper', X_s'.
  split; red; [exact SIMREL' |].
  constructor.
  { exists (option_map mapper' r), (mapper' ↑₁ R1),
           (option_map mapper' w),
           ((extra_a X_t' a_t b_t b_t ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l) ∩₁ WCore.lab_is_w l)
            ∪₁ mapper' ↑₁ W1),
           (mapper' ↑₁ W2).
    apply add_event_to_wf; simpl.
    { eapply sico_init_acts_s; [| apply CORR].
      eapply rsr_common; eauto. }
    { unfold mapper'. rewrite upds. exact NOTIN. }
    { unfold mapper'. rewrite upds. exact NINIT. }
    { unfold mapper'. rewrite upds. exact E_TID. }
    { unfold mapper'. rewrite upds. reflexivity. }
    { reflexivity. }
    { unfold mapper'. rewrite upds. reflexivity. }
    { rewrite <- mapped_rf_delta_R,
              <- mapped_rf_delta_W.
      rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD),
              (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, union_false_r.
      reflexivity. }
    { rewrite (co_deltaE1 (rsr_Gt_wf CORR) ADD),
              (co_deltaE2 (rsr_Gt_wf CORR) ADD).
      rewrite co_delta_union_W1, <- mapped_co_delta.
      unfold WCore.co_delta. rewrite collect_rel_union.
      rewrite <- !unionA. repeat apply union_more; ins.
      destruct classic with (WCore.lab_is_w l ≡₁ ∅) as [EMP|NEMP].
      { now rewrite EMP, !set_inter_empty_r, add_max_empty_l, cross_false_r. }
      clear - NEMP ENEXA.
      unfold WCore.lab_is_w in *. desf.
      rewrite !set_inter_full_r. ins.
      unfold mapper'. rewrite upds, add_max_disjoint; ins.
      basic_solver. }
    { rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD),
              collect_rel_union.
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rmwE (rsr_Gt_wf CORR)). }
      now rewrite (rsr_rmw SIMREL). }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { unfold sb at 1. unfold mapper'.
      simpl. rewrite NEWSB, upds.
      reflexivity. }
    { rewrite (rsr_ctrl SIMREL), <- (WCore.add_event_ctrl ADD).
      apply ADD. }
    eapply G_s_wf with (X_s := X_s') (X_t := X_t'); eauto. }
  { eapply G_s_rfc; eauto. }
  admit.
Admitted.

Lemma simrel_exec_b_step_1 l_a
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (THREADS : threads_set G_t (tid b_t))
    (TACTS : E_t' ≡₁ E_t ∪₁ eq b_t)
    (TSTEP : sb_t' ≡ sb_t ∪ WCore.sb_delta b_t E_t)
    (BNOTIN : ~E_t b_t) :
  exists l_a' X_s'',
    << LABU2V : same_label_u2v l_a' l_a >> /\
    << ATID : same_tid b_t b_t >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' b_t l_a' >> /\
    << RF : rf (WCore.G X_s'') ≡
            rf_s ∪ srf (WCore.G X_s'') ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ >> /\
    << CO : co (WCore.G X_s'') ≡
            co_s ∪ (E_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
                (eq b_t ∩₁ WCore.lab_is_w l_a) >> /\
    << RMW : rmw (WCore.G X_s'') ≡ rmw_s >>.
Proof using INV INV'.
  (* Generate new actid *)
  assert (NEWE :
  << NINIT : ~is_init b_t >> /\
  << NOTIN : ~E_s b_t >> /\
  << TID : tid b_t = tid b_t >> /\
  << NEWSB : ⦗E_s ∪₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq b_t⦘ ≡
          sb_s ∪ WCore.sb_delta b_t E_s >>).
  { unfold NW. splits; auto.
    { apply INV. }
    { intro FALSO. eapply (rsr_actsE INV) in FALSO.
      all: eauto.
      apply set_subset_single_l in FALSO.
      rewrite extra_a_none_r in FALSO by assumption.
      rewrite set_union_empty_r in FALSO.
      now apply -> set_subset_single_l in FALSO. }
    unfold sb.
    erewrite (rsr_actsE INV); eauto.
    rewrite extra_a_none_r by assumption.
    rewrite set_union_empty_r, <- TACTS.
    apply TSTEP. }
  (* unfold hypotheses *)
  assert (WF_S : Wf G_s).
  { eapply G_s_wf with (X_t := X_t); try red; eauto. }
  set (sb_s' := ⦗E_s ∪₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq b_t⦘).
  set (srf_s' := (⦗Loc_s_ (WCore.lab_loc l_a)⦘ ⨾ vf_s ⨾ sb_s') \ (co_s ⨾ vf_s ⨾ sb_s')).
  assert (VFE : vf_s ⊆ ⦗E_s⦘ ⨾ vf_s).
  { rewrite (wf_vfE WF_S) at 1.
    rewrite inclusion_seq_eqv_r. reflexivity. }
  assert (SRFE : srf_s' ⊆ ⦗E_s⦘ ⨾ srf_s').
  { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; [| red; auto with hahn].
    seq_rewrite seq_eqvC. rewrite VFE at 1.
    rewrite 2!seqA. reflexivity. }
  assert (SRFD : srf_s' ⊆ ⦗W_s⦘ ⨾ srf_s').
  { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; [| red; auto with hahn].
    seq_rewrite seq_eqvC. rewrite vf_d_left at 1.
    rewrite 2!seqA. reflexivity. }
  assert (SRFL : srf_s' ⊆ ⦗Loc_s_ (WCore.lab_loc l_a)⦘ ⨾ srf_s').
  { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; [| red; auto with hahn].
    seq_rewrite seq_eqvK. reflexivity. }
  assert (SRFVF : srf_s' ⊆ vf_s ⨾ sb_s').
  { unfold srf_s'. clear.
    rewrite inclusion_minus_rel, inclusion_seq_eqv_l.
    reflexivity. }
  assert (FUN : functional srf_s'⁻¹).
  { rewrite SRFE, SRFD, SRFL. clear - WF_S SRFVF.
    unfolder. intros x y z (((YINE & YW) & YL) & SRF1) (((ZINE & ZW) & ZL) & SRF2).
    destruct (classic (y = z)) as [EQ|NEQ]; ins.
    destruct (wf_co_total WF_S) with (a := y) (b := z)
                        (ol := WCore.lab_loc l_a) as [CO|CO].
    { unfold set_inter; splits; assumption. }
    { unfold set_inter; splits; assumption. }
    { exact NEQ. }
    { exfalso. apply SRF1. apply SRFVF in SRF2.
      clear - CO SRF2. red; eauto. }
    exfalso. apply SRF2. apply SRFVF in SRF1.
    clear - CO SRF1. red; eauto. }
  assert (SRF_W : exists w,
    eq_opt w ≡₁ dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘)).
  { clear - FUN.
    destruct classic
        with (dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘) ≡₁ ∅)
          as [EMP|NEMP].
    { exists None. rewrite EMP. clear. auto with hahn. }
    apply set_nonemptyE in NEMP. destruct NEMP as (x & DOM).
    exists (Some x). rewrite eq_opt_someE.
    split; red; [congruence|]. intros x' DOM'.
    apply FUN with b_t; red.
    { clear - DOM. unfolder in DOM. desf. }
    clear - DOM'. unfolder in DOM'. desf. }
  destruct SRF_W as (w & SRF_W).
  assert (ALAB : exists l_a',
    << U2V : same_label_u2v l_a' l_a >> /\
    << VAL : dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘) ⊆₁ Val_s_ (WCore.lab_val l_a') >>
  ); [| desf].
  { destruct w as [w|].
    { assert (ISR : WCore.lab_is_r l_a b_t).
      { unfolder in SRF_W. destruct SRF_W as [ISR _].
        clear - ISR. destruct ISR with w; desf. }
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
      arewrite (dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ ⊤₁⦘) ⊆₁ Val_s_ (val_s w)).
      { rewrite <- SRF_W. clear. basic_solver. }
      unfold val. rewrite HEQW; ins. }
    exists l_a. split; red.
    { red. desf. }
    rewrite <- SRF_W. clear. basic_solver. }
  set (G_s'' := {|
    acts_set := E_s ∪₁ eq b_t;
    threads_set := threads_set G_s;
    lab := upd lab_s b_t l_a';
    rf := rf_s ∪
          srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘;
    co := co_s ∪
          (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) × (eq b_t ∩₁ WCore.lab_is_w l_a);
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
    srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ ≡
    srf (WCore.G X_s'') ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘
  ).
  { unfold X_s'' at 1. ins. unfold srf.
    seq_rewrite seq_eqv_minus_lr. rewrite !seqA.
    seq_rewrite <- id_inter.
    arewrite (is_r (lab G_s'') ∩₁ (eq b_t ∩₁ WCore.lab_is_r l_a) ≡₁
              eq b_t ∩₁ WCore.lab_is_r l_a).
    { split; [basic_solver |].
      unfold is_r, WCore.lab_is_r. unfolder.
      intros x XIN. destruct XIN; subst; ins.
      rewrite upds. splits; ins; desf. }
    rewrite id_inter.
    rewrite <- !seqA with (r2 := ⦗eq b_t⦘).
    apply seq_more; try easy.
    rewrite minus_inter_l, <- seq_eqv_inter_rr.
    arewrite (same_loc (lab G_s'') ⨾ ⦗eq b_t⦘ ≡
              (fun x y => loc (lab G_s'') x = WCore.lab_loc l_a) ⨾ ⦗eq b_t⦘).
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
    arewrite (sb G_s'' ⨾ ⦗eq b_t⦘ ≡ ⦗E_s⦘ ⨾ sb G_s'' ⨾ ⦗eq b_t⦘).
    { unfold sb. ins. rewrite NEWSB.
      rewrite seq_union_l, seq_union_r. apply union_more.
      { unfold sb. clear - NOTIN. basic_solver. }
      unfold WCore.sb_delta.
      arewrite (E_s ≡₁ E_s ∪₁ is_init).
      { symmetry. apply set_union_absorb_r.
        eapply sico_init_acts_s; [| apply INV].
        eapply rsr_common; eauto. }
      clear. basic_solver 11. }
    arewrite (vf G_s'' ⨾ ⦗E_s⦘ ≡ vf_s ⨾ ⦗E_s⦘).
    { apply (vf_add_event X_s X_s''); ins.
      { clear. basic_solver. }
      { unfolder. ins; desf. rupd. congruence. }
      { unfold sb at 1. ins. rewrite NEWSB.
        clear - NOTIN. basic_solver 11. }
      { clear - NOTIN. basic_solver 11. }
      now rewrite (rsr_rmw SIMREL). }
    rewrite <- seq_eqv_minus_ll.
    apply minus_rel_more; rewrite <- !seqA.
    all: do 3 (apply seq_more; [| easy]).
    all: rewrite (wf_vfE WF_S), <- !seqA.
    all: do 2 (apply seq_more; [| easy]).
    { rewrite <- !id_inter. apply eqv_rel_more.
      unfold loc. unfolder. split; intros x (HSET & HIN).
      all: split; ins.
      all: rewrite updo in *; ins.
      all: congruence. }
    subst G_s''. ins. clear - NOTIN. basic_solver. }
  assert (TOT : forall ol,
    is_total
    ((E_s ∪₁ eq b_t)
    ∩₁ (is_w (upd lab_s b_t l_a'))
    ∩₁ (fun e => loc (upd lab_s b_t l_a') e = ol))
    (co_s ∪
      (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) × (eq b_t ∩₁ WCore.lab_is_w l_a))
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
  assert (STEP : WCore.add_event X_s X_s'' b_t l_a').
  { red. exists None, ∅, w, ∅,
      (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a) ∩₁ WCore.lab_is_w l_a).
    constructor; ins.
    { rewrite <- (rsr_at_bt_tid INV).
      apply INV. }
    { rewrite SRF_W, SRF', wf_srfD.
      rewrite !seqA.
      seq_rewrite (seq_eqvC (is_r (lab G_s''))).
      seq_rewrite <- SRF'. rewrite seqA.
      unfold srf_s'.
      transitivity (dom_rel (⦗is_w (lab G_s'')⦘ ⨾ (
          ⦗Loc_s_ (WCore.lab_loc l_a)⦘ ⨾ vf_s ⨾ sb_s'
        ) ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘
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
      { eapply G_s_co_trans with (X_t := X_t); eauto. }
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
      { eapply G_s_rff with (X_t := X_t); eauto. }
      { rewrite SRF'. apply functional_mori with (x := (srf G_s'')⁻¹).
        { unfold flip; basic_solver. }
        apply wf_srff'; ins. }
      intros x RF SRF.
      unfolder in RF. destruct RF as (y & RF).
      apply (wf_rfE WF_S) in RF.
      unfolder in SRF. unfolder in RF. desf. }
    { eapply sico_init_acts_s; [| apply INV].
      eapply rsr_common; eauto. }
    { now apply (rsr_threads SIMREL). }
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
  exists l_a', X_s''.
  splits; ins.
  { constructor; ins.
    { assert (RFC_S : rf_complete G_s).
      { eapply G_s_rfc with (X_t := X_t); eauto. }
      unfold rf_complete. unfold G_s''; ins.
      rewrite set_inter_union_l, SRF', codom_union.
      apply set_union_mori.
      { intros x (XINE & ISR).
        apply RFC_S. split; ins.
        unfold is_r in *. rewrite updo in ISR; ins.
        congruence. }
      intros x (XEQ & ISR).
      assert (XLOC : exists ll, loc (upd lab_s b_t l_a') x = Some ll).
      { unfold is_r in ISR. subst x.
        rewrite upds in ISR. desf.
        eexists. unfold loc. now rewrite upds. }
      destruct XLOC as (ll & XLOC).
      subst x.
      destruct srf_exists
          with (G := G_s'') (r := b_t) (l := ll)
            as (w' & SRF).
      all: ins.
      all: try now apply WF_S'.
      { now right. }
      { left. eapply sico_init_acts_s; [| apply INV | easy].
        eapply rsr_common; eauto. }
      { rewrite set_minus_union_l.
        apply set_finite_union. split.
        { eapply (rsr_fin_s INV); eauto. }
        apply set_finite_mori with (x := eq b_t).
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
  assert (STEP1 : exists l_a' X_s'',
    << LABU2V : same_label_u2v l_a' l_a >> /\
    << ATID : same_tid b_t b_t >> /\
    << STEPA : WCore.exec_inst X_s  X_s'' b_t l_a' >> /\
    << RF' : rf (WCore.G X_s'') ≡
            rf_s ∪ srf (WCore.G X_s'') ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ >> /\
    << CO' : co (WCore.G X_s'') ≡
            co_s ∪ (E_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
                (eq b_t ∩₁ WCore.lab_is_w l_a) >> /\
    << RMW' : rmw (WCore.G X_s'') ≡ rmw_s >>).
  { apply simrel_exec_b_step_1; ins.
    all: apply ADD. }
  subst a_t'. subst b_t'. desf.
  exists l_a', b_t, X_s''.
  destruct STEPA as [ADD' RFC' CONS'].
  destruct ADD' as (r' & R1' & w' & W1' & W2' & ADD').
  assert (ANOTB : b_t <> a_t).
  { intro FALSO. apply (rsr_at_neq_bt INV).
    congruence. }
  assert (ENOTIN : ~E_t b_t) by apply ADD.
  assert (ANOTIN : ~E_t a_t).
  { intro FALSO. now apply ENOTIN, (rsr_at_bt_ord CORR). }
  assert (ANOTIN' : ~E_t' a_t).
  { intro FALSO. apply (WCore.add_event_acts ADD) in FALSO.
    destruct FALSO as [INE|EQ]; eauto. }
  (* Generate new actid *)
  assert (NEWE :
  << NINIT : ~is_init a_t >> /\
  << NOTIN : ~(E_s ∪₁ eq b_t) a_t >> /\
  << TID : tid a_t = tid b_t >> /\
  << NEWSB : ⦗E_s ∪₁ eq b_t ∪₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq b_t ∪₁ eq a_t⦘ ≡
          sb (WCore.G X_s'') ∪ WCore.sb_delta a_t (acts_set (WCore.G X_s'')) >>).
  { unfold NW. splits; try now apply CORR.
    { intro FALSO. apply set_subset_single_l in FALSO.
      erewrite (rsr_actsE CORR) in FALSO; eauto.
      rewrite extra_a_none_r in FALSO by apply ADD.
      rewrite set_union_empty_r in FALSO.
      apply -> set_subset_single_l in FALSO.
      destruct FALSO as [INE | EQB].
      { now apply (WCore.add_event_new ADD), (rsr_at_bt_ord INV). }
      apply (rsr_at_neq_bt INV). auto. }
    unfold sb. rewrite (WCore.add_event_acts ADD').
    rewrite (rsr_actsE INV SIMREL), extra_a_none_r; auto.
    rewrite set_union_empty_r, <- (WCore.add_event_acts ADD).
    rewrite id_union, !seq_union_l, !seq_union_r, <- unionA.
    arewrite_false (⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t⦘).
    { clear. unfolder. ins. desf. eapply ext_sb_irr; eauto. }
    arewrite_false (⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗E_t'⦘).
    { apply INV'. intro FALSO. apply ADD in FALSO.
      destruct FALSO as [IN|EQ].
      { now apply NINB, (rsr_at_bt_ord INV). }
      now apply (rsr_at_neq_bt INV). }
    rewrite !union_false_r. apply union_more; auto.
    unfolder; split; intros x y HREL.
    { clear - HREL. unfold ext_sb in HREL.
      desf; eauto. unfold same_tid. desf; eauto. }
    assert (XIN : E_t' x).
    { clear - HREL INV'. desf.
      now apply (rsr_init_acts INV'). }
    splits; try now (auto; clear - HREL; desf).
    destruct HREL as [[INIT | [INE TID]] EQ]; subst y.
    { clear - INIT INV'. unfold ext_sb; desf.
      now apply (rsr_at_ninit INV'). }
    destruct PeanoNat.Nat.lt_total
        with (n := index a_t) (m := index x)
          as [LT | [EQ | GT]].
    { exfalso. apply (rsr_nat_spot INV') with a_t x; auto.
      unfolder; splits; auto. unfold ext_sb.
      desf; ins; desf; lia. }
    { exfalso. apply ANOTIN'.
      arewrite (a_t = x); auto.
      destruct a_t as [atl | att atn].
      { exfalso. now apply (rsr_at_ninit INV). }
      destruct x as [xl | xt xn].
      { exfalso. apply (rsr_at_tid INV).
        unfold same_tid in TID; desf. }
      unfold same_tid in TID. ins. congruence. }
    unfold ext_sb; desf; ins; lia. }
  desf.
  set (mapper' := upd mapper b_t a_t).
  set (G_s' := {|
    acts_set := E_s ∪₁ eq b_t ∪₁ eq a_t;
    threads_set := threads_set G_s;
    lab := upd (upd lab_s b_t l_a') a_t l;
    rf := rf_s ∪
          mapper' ↑ (rf_t' ⨾ ⦗eq b_t⦘) ∪
          srf (WCore.G X_s'') ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘;
    co := co_s ∪
          mapper' ↑ (⦗eq b_t⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq b_t⦘) ∪
          (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) × (eq b_t ∩₁ WCore.lab_is_w l_a);
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
  set (extra_W2 := extra_a X_t' a_t b_t b_t ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l));
  (* Asserts *)
  assert (WF' : Wf G_t').
  { eapply WCore.add_event_wf; eauto.
    apply CORR. }
  assert (WF_S'' : Wf (WCore.G X_s'')).
  { apply (WCore.add_event_wf ADD').
    eapply G_s_wf with (X_t := X_t); eauto. }
  assert (ENINIT : ~is_init b_t) by apply ADD.
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq b_t) by apply ADD.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    rupd. congruence. }
  assert (ANOTINS : ~E_s b_t).
  { intro FALSO. now apply (WCore.add_event_new ADD'). }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { split; unfolder; intros x (y & YINE & HEQ).
    { exists y; split; ins. rewrite <- MAPEQ; ins. }
    exists y. split; ins. subst mapper'. rupd; ins.
    congruence. }
  assert (LABSUB : eq_dom E_t lab_t' lab_t).
  { rewrite (WCore.add_event_lab ADD). unfolder.
    intros x XINE. rupd. congruence. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> a_t).
  { intros x XINE FALSO. apply NOTIN. left.
    apply (rsr_codom SIMREL). basic_solver. }
  assert (MAPNEQ' : forall x (IN : E_t x), mapper x <> b_t).
  { intros x XINE FALSO. apply ANOTINS.
    apply (rsr_codom SIMREL). basic_solver. }
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
  assert (MAPER_E : mapper' ↑₁ eq b_t ≡₁ eq a_t).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (OLDEXA : extra_a X_t a_t b_t b_t ≡₁ ∅).
  { unfold extra_a; do 2 desf; exfalso; eauto. }
  assert (NEWEXA : extra_a X_t' a_t b_t b_t ≡₁ eq b_t).
  { unfold extra_a; do 2 desf; exfalso; eauto.
    apply n; split; ins. apply (WCore.add_event_acts ADD).
    basic_solver. }
  assert (LABEQ : eq_dom E_s (lab (WCore.G X_s'')) lab_s).
  { rewrite (WCore.add_event_lab ADD'). unfolder.
    intros x XINE. rupd; ins. congruence. }
  assert (LABEQ' : eq_dom E_s (upd (upd lab_s b_t l_a') a_t l) lab_s).
  { rewrite (WCore.add_event_lab ADD') in LABEQ. unfolder.
    intros x XINE. rupd; ins; try congruence.
    intro FALSO. eapply NOTIN. left; congruence. }
  assert (MAPE : a_t = mapper' b_t).
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
      rewrite (WCore.add_event_sb ADD').
      unfold WCore.sb_delta.
      rewrite (WCore.add_event_acts ADD').
      rewrite seq_union_l at 1.
      rewrite <- cross_inter_r.
      arewrite (eq a_t ∩₁ (E_s ∪₁ eq b_t) ≡₁ ∅).
      { generalize NOTIN. clear. basic_solver. }
      now rewrite cross_false_r, union_false_r. }
    { rewrite RF', (WCore.add_event_acts ADD'), !seq_union_l.
      rewrite MAPE in NOTIN. clear - NOTIN.
      arewrite_false (mapper' ↑ (rf_t' ⨾ ⦗eq b_t⦘) ⨾ ⦗E_s ∪₁ eq b_t⦘).
      { unfolder in NOTIN. basic_solver. }
      now rewrite union_false_r. }
    { rewrite CO', (WCore.add_event_acts ADD'), !seq_union_l,
              !seq_union_r.
      rewrite MAPE in NOTIN. clear - NOTIN.
      arewrite_false (⦗E_s ∪₁ eq b_t⦘ ⨾ mapper' ↑ (⦗eq b_t⦘ ⨾ co_t')).
      { unfolder in NOTIN. basic_solver. }
      arewrite_false (mapper' ↑ (co_t' ⨾ ⦗eq b_t⦘) ⨾ ⦗E_s ∪₁ eq b_t⦘).
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
      exfalso. eapply (rsr_nrmw CORR') with (x := r) (y := b_t); auto.
      apply ADD. right. clear. basic_solver. }
    now rewrite <- (rsr_rmw SIMREL), collect_rel_empty, seq_false_l,
                union_false_r. }
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper').
  { constructor; ins.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
        now apply SIMREL. }
      { clear. basic_solver. }
      rewrite MAPER_E, MAPSUB, (rsr_codom SIMREL), OLDEXA.
      clear - NOTIN. unfolder in NOTIN. basic_solver. }
    { rewrite NEWEXA. unfolder. intros x XEQ. subst x.
      constructor; ins.
      assert (SUBRF : rf (WCore.G X_s'') ⊆ same_val (upd (upd lab_s b_t l_a') a_t l)).
      { unfolder. unfold same_val. intros x y RF.
        apply (wf_rfE WF_S'') in RF. unfolder in RF.
        destruct RF as (DOM & RF & CODOM).
        apply (WCore.add_event_acts ADD') in DOM, CODOM.
        unfold val. rewrite !updo with (a := a_t).
        all: try congruence.
        apply (wf_rfv WF_S'') in RF.
        now rewrite (WCore.add_event_lab ADD') in RF. }
      rewrite <- SUBRF, RF'. apply inclusion_union_r. right.
      rewrite !id_inter.
      arewrite (⦗eq b_t⦘ ≡ ⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      seq_rewrite SRF''. rewrite seqA.
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t⦘ ≡ ⦗eq b_t⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t⦘ ≡ ⦗eq b_t⦘).
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
      arewrite (same_tid a_t ≡₁ same_tid b_t).
      { unfold same_tid. now rewrite (rsr_at_bt_tid INV). }
      arewrite (eq b_t ∩₁ same_tid b_t ≡₁ eq b_t).
      { clear. basic_solver. }
      clear. basic_solver 12. }
    { rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      rewrite NEWEXA.
      arewrite (eq b_t ∩₁ is_r (upd (upd lab_s b_t l_a') a_t l) ≡₁
                eq b_t ∩₁ WCore.lab_is_r l_a').
      { unfolder. split; intros x (EQ & ISR).
        all: split; ins; subst x; unfold is_r in *.
        all: rewrite updo, upds in *; try congruence.
        all: unfold WCore.lab_is_r in *; desf. }
      arewrite (srf G_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a'⦘ ≡
                srf G_s' ⨾ ⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a'⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      seq_rewrite SRF''. rewrite seqA.
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a'⦘ ≡
                ⦗eq b_t ∩₁ WCore.lab_is_r l_a'⦘).
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
      arewrite (extra_co_D (eq a_t) (upd (upd lab_s b_t l_a') a_t l)
                (loc (upd (upd lab_s b_t l_a') a_t l) b_t) ≡₁ ∅).
      { split; [| basic_solver].
        transitivity (same_loc (upd (upd lab_s b_t l_a') a_t l) b_t ∩₁ eq a_t).
        { clear. unfold same_loc. basic_solver. }
        clear - NEQLOC ANOTB LABU2V.
        unfolder. ins. desf.
        unfold same_loc, loc, WCore.lab_loc, same_label_u2v in *.
        rewrite upds, updo, upds in * by assumption.
        do 2 desf. }
      rewrite add_max_empty_l, union_false_r.
      rewrite add_max_sub
         with (A := extra_co_D (eq b_t) _ _)
           by basic_solver 11.
      rewrite union_false_r.
      rewrite extra_co_D_eq_dom with (ll1 := upd (upd lab_s b_t l_a') a_t l).
      all: eauto using same_lab_u2v_dom_inclusion.
      arewrite (eq b_t ∩₁ is_w (upd (upd lab_s b_t l_a') a_t l) ≡₁
                eq b_t ∩₁ WCore.lab_is_w l_a').
      { unfold is_w, WCore.lab_is_w. unfolder.
        split; intros x (EQ & LAB); split; ins; subst x.
        all: rewrite updo, upds in *; ins.
        all: desf. }
      arewrite (loc (upd (upd lab_s b_t l_a') a_t l) b_t = WCore.lab_loc l_a').
      { unfold loc, WCore.lab_loc. now rupd. }
      unfold add_max.
      arewrite (extra_co_D E_s lab_s (WCore.lab_loc l_a') \₁ eq b_t ∩₁ WCore.lab_is_w l_a'
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
    { arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
      { clear - ANOTIN'. basic_solver. }
      rewrite set_collect_empty. clear. basic_solver. }
    { arewrite (E_t' \₁ eq a_t \₁ eq b_t ≡₁ E_t \₁ eq a_t \₁ eq b_t).
      { rewrite (WCore.add_event_acts ADD). clear. basic_solver. }
      clear - MAPEQ SIMREL. unfolder. intros x XIN.
      rewrite MAPEQ; [rewrite (rsr_mid SIMREL)|]; desf. }
    { rewrite EQACTS, set_inter_absorb_r by (clear; basic_solver).
      unfold mapper'. now rewrite set_collect_eq, upds. }
    rewrite EQACTS.
    assert (NEQ : a_t <> b_t) by apply INV.
    arewrite (eq a_t ∩₁ (E_t ∪₁ eq b_t) ≡₁ ∅).
    { rewrite set_inter_union_r. clear - NEQ ANOTIN.
      basic_solver. }
    rewrite set_collect_empty. auto with hahn. }
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
      eapply sico_init_acts_s; [| apply INV].
      eapply rsr_common; eauto. }
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
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper a_t b_t).
  set (G_s' := {|
    acts_set := E_s;
    threads_set := threads_set G_s;
    lab := upd lab_s b_t l;
    rf := rf_s ⨾ ⦗E_s \₁ eq b_t⦘ ∪
          mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘);
    co := restr_rel (E_s \₁ eq b_t) co_s ∪
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
  set (cmt' := E_s \₁ eq b_t).
  set (dtrmt' := E_s \₁ eq b_t \₁ eq (mapper b_t)).
  set (thrdle' := fun x y =>
    << YNINIT : y <> tid_init >> /\
    << XNOTA : x <> tid b_t >> /\
    << XYVAL : x = tid_init \/ y = tid b_t >>
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
  assert (AINS : E_s b_t).
  { apply (rsr_acts SIMREL). unfold extra_a. desf.
    { basic_solver. }
    exfalso; eauto. }
  assert (NOEXA : extra_a X_t' a_t b_t b_t ≡₁ ∅).
  { unfold extra_a; desf. desf. }
  assert (OLDEXA : extra_a X_t a_t b_t b_t ≡₁ eq b_t).
  { unfold extra_a; desf. exfalso; eauto. }
  assert (MAPER_E : mapper' ↑₁ eq a_t ≡₁ eq b_t).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (ANCODOM : ~ (mapper ↑₁ E_t) b_t).
  { intro FALSO. apply (rsr_codom SIMREL) in FALSO.
    now apply FALSO, OLDEXA. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> b_t).
  { intros x XIN EQ. apply (rsr_codom SIMREL) with (x := b_t).
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
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper').
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
      arewrite_false ((srf_s ⨾ ⦗eq b_t ∩₁ R_s⦘) ⨾ ⦗E_s \₁ eq b_t⦘).
      { clear. basic_solver. }
      rewrite eqv_empty, seq_false_r, !union_false_r,
              (WCore.add_event_rf ADD), !collect_rel_union.
      arewrite (mapper ↑ rf_t ⨾ ⦗E_s \₁ eq b_t⦘ ≡ mapper ↑ rf_t).
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
      arewrite (restr_rel (E_s \₁ eq b_t) (mapper ↑ co_t) ≡ mapper ↑ co_t).
      { split; [clear; basic_solver 11 |].
        rewrite <- OLDEXA, <- (rsr_codom SIMREL),
                collect_rel_restr, restr_relE.
        { apply collect_rel_mori; ins. apply WF. }
        eapply inj_dom_mori with (x := E_t); eauto; [| apply SIMREL].
        unfold flip. rewrite (wf_coE WF). clear. basic_solver. }
      rewrite restr_add_max, OLDEXA.
      arewrite (eq b_t ∩₁ W_s ∩₁ (E_s \₁ eq b_t) ≡₁ ∅).
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
    unfolder in RPOIMM. desf.
    { arewrite (E_t' \₁ eq a_t \₁ eq b_t ≡₁ E_t \₁ eq a_t \₁ eq b_t).
      { rewrite (WCore.add_event_acts ADD). clear. basic_solver. }
      clear - MAPEQ SIMREL. unfolder. intros x XIN.
      rewrite MAPEQ; [rewrite (rsr_mid SIMREL) |]; desf. }
    { arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t).
      { clear - INB' INB. basic_solver. }
      rewrite set_collect_eq_dom with (g := mapper); [apply SIMREL |].
      eapply eq_dom_mori; eauto. unfold flip. clear. basic_solver. }
    rewrite (WCore.add_event_acts ADD), set_inter_absorb_r by (clear; basic_solver).
    unfold mapper'. now rewrite set_collect_eq, upds. }
  assert (PFX : SubToFullExec.prefix (WCore.X_start X_s dtrmt') X_s').
  { assert (DT : dtrmt' ∩₁ E_s ≡₁ dtrmt').
    { unfold dtrmt'. basic_solver. }
    assert (INIT : is_init ⊆₁ dtrmt').
    { unfold dtrmt'.
      rewrite <- sico_init_acts_s; [| | apply INV].
      all: try now (eapply rsr_common; eauto).
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
      arewrite ((E_s \₁ eq b_t) ∩₁ dtrmt' ≡₁ dtrmt').
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
      arewrite ((E_s \₁ eq b_t) ∩₁ dtrmt' ≡₁ dtrmt').
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
      eapply G_s_wf with (X_s := X_s') (X_t := X_t'); eauto. }
    { apply prefix_exec_restr_eq; ins.
      basic_solver. }
    { unfold rf_complete, G_s', cmt'. ins.
      arewrite ((E_s \₁ eq b_t) ∩₁ E_s ≡₁ E_s \₁ eq b_t).
      { basic_solver. }
      arewrite ((E_s \₁ eq b_t) ∩₁ is_r (upd lab_s b_t l) ≡₁
                (E_s \₁ eq b_t) ∩₁ R_s).
      { unfolder. split; ins; desf; splits; ins.
        all: unfold is_r in *.
        all: rewrite updo in *; congruence. }
      rewrite seq_union_l, seq_union_r, !seqA.
      rewrite codom_union.
      arewrite_false (mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘) ⨾ ⦗E_s \₁ eq b_t⦘).
      { unfolder. intros x y HREL. desf.
        unfold mapper' in *.
        now rewrite upds in *. }
      rewrite seq_false_r, codom_empty, set_union_empty_r.
      seq_rewrite seq_eqvK. unfolder.
      intros x ((XINE & NEQ) & ISR).
      assert (RFC_S : rf_complete G_s).
      { eapply G_s_rfc with (X_t := X_t); eauto. }
      assert (WF_S : Wf G_s).
      { eapply G_s_wf with (X_t := X_t); eauto. }
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
    arewrite (E_s \₁ cmt' ≡₁ eq b_t).
    { subst cmt'. rewrite set_minus_minus_r.
      basic_solver. }
    rewrite seq_union_l.
    arewrite ((rf_s ⨾ ⦗E_s \₁ eq b_t⦘) ⨾ ⦗eq b_t⦘ ≡ ∅₂).
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
    destruct classic with (tid x' = tid b_t) as [TID | NTID].
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
        assert (RPNEQ : forall (EQA : x = b_t) (EQB : y = mapper' b_t), False).
        { intros FALSO1 FALSO2; subst x; subst y.
          eapply (rsr_nrpo SIMREL') with b_t (mapper' b_t).
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
  { eapply G_s_rfc with (X_s := X_s'); eauto. }
  { arewrite (E_s \₁ dtrmt' ∩₁ E_s ≡₁ eq b_t ∪₁ eq (mapper b_t)).
    { rewrite set_minus_inter_r, set_minusK, set_union_empty_r.
      subst dtrmt'.
      rewrite !set_minus_minus_r, set_minusK, set_union_empty_l.
      rewrite !set_inter_absorb_l; ins; [| basic_solver].
      rewrite (rsr_acts SIMREL). basic_solver. }
    apply set_finite_union. split; apply set_finite_eq. }
  { eapply G_s_wf with (X_s := X_s'); eauto. }
  { unfold dtrmt'.
    rewrite set_inter_absorb_r; [| basic_solver].
    rewrite !set_minus_minus_r, set_minusK, set_union_empty_l.
    apply set_subset_union_l. split.
    { unfolder. intros x (INE & XEQ) FALSO. subst x.
      eapply rsr_as_ninit with (x := b_t) (X_t := X_t); eauto.
      { apply extra_a_some; ins. }
      eapply rsr_ninit_acts_s with (X_t := X_t); eauto.
      red; eauto. }
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

Definition extra_b :=
  ifP ~E_t' a_t' /\ E_t' b_t' then ∅
  else eq b_t' ∩₁ E_t'.

Lemma simrel_reexec dtrmt cmt
    (ACMT : cmt a_t -> a_t = a_t')
    (BCMT : cmt b_t -> b_t = b_t')
    (PRESERVATION : b_t' = b_t <-> a_t' = a_t)
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.reexec X_t X_t' dtrmt cmt) :
  exists mapper' X_s' dtrmt' cmt',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP : WCore.reexec X_s X_s' dtrmt' cmt' >>.
Proof using INV INV'.
  destruct STEP as (f & thrdle & STEP).
  set (mapper' :=  upd (upd id a_t' b_t') b_t' a_t').
  set (cmt' := mapper' ↑₁ (cmt ∪₁ extra_b)).
  set (dtrmt' := mapper' ↑₁ (dtrmt \₁ extra_b)).
  set (G_s' := {|
    acts_set := mapper' ↑₁ E_t' ∪₁ extra_a X_t' a_t' b_t' b_t';
    threads_set := threads_set G_t';
    lab := lab_t' ∘ mapper';
    rf := mapper' ↑ rf_t' ∪
          srf_s ⨾ ⦗extra_a X_t' a_t' b_t' b_t' ∩₁ R_s⦘;
    co := mapper' ↑ co_t' ∪
          add_max
            (extra_co_D (mapper' ↑₁ E_t') lab_s (loc_s b_t))
            (extra_a X_t' a_t' b_t' b_t' ∩₁ W_s);
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
  assert (MAPEQ : eq_dom cmt mapper mapper').
  { unfolder. unfold mapper', id. intros x XIN.
    destruct classic with (x = a_t) as [XEQA|XNQA],
              classic with (x = b_t) as [XEQB|XNQB].
    all: try subst x.
    { exfalso; now apply (rsr_at_neq_bt INV). }
    { assert (EQA : a_t' = a_t) by (symmetry; auto).
      assert (EQB : b_t' = b_t) by now apply PRESERVATION.
      rewrite EQA, EQB, updo, upds by auto.
      symmetry. apply (rsr_at SIMREL).
      apply (WCore.reexec_embd_dom STEP) in XIN.
      admit. }
    { admit. }
    admit. }
  assert (MAPINJ : inj_dom E_t' mapper').
  { unfold inj_dom, mapper'. intros x y XIN YIN FEQ.
      destruct classic with (x = a_t') as [XEQA|XNQA],
               classic with (x = b_t') as [XEQB|XNQB],
               classic with (y = a_t') as [YEQA|YNQA],
               classic with (y = b_t') as [YEQB|YNQB].
      all: try subst x; try subst y.
      all: try congruence.
      all: try now (exfalso; apply (rsr_at_neq_bt INV'); congruence).
      all: rewrite ?upds in FEQ.
      all: rewrite 1?updo in FEQ; try congruence.
      all: rewrite ?upds in FEQ; try congruence.
      all: unfold id in FEQ.
      all: rewrite 2?updo in FEQ; try congruence.
      all: rewrite ?upds in FEQ; try congruence.
      rewrite updo in FEQ; try congruence. }
  assert (SIMREL' : reord_simrel X_s' X_t' a_t' b_t' mapper').
  { constructor; ins.
    { unfold extra_a; desf. intros x XEQ. subst x.
      constructor; ins.
      admit. }
    { rewrite set_minus_union_l, set_minusK, set_union_empty_r.
      rewrite set_minus_disjoint; [reflexivity |].
      apply set_disjointE. split; [| basic_solver].
      unfold extra_a; desf; [| clear; basic_solver].
      unfold mapper', id. unfolder.
      intros x ((y & YINE & MAP) & XEQ). subst x.
      destruct classic with (y = b_t') as [YEQB | YNQB].
      { subst y. rewrite upds in XEQ. apply (rsr_at_neq_bt INV').
        congruence. }
      rewrite updo in XEQ; [| congruence].
      destruct classic with (y = a_t') as [YEQA | YNQA].
      { subst y. desf. }
      rewrite updo in XEQ; congruence. }
    { unfolder. unfold mapper', id. intros x INIT.
      rewrite !updo; auto.
      all: intro FALSO; subst x.
      { now apply (rsr_at_ninit INV'). }
      now apply (rsr_bt_ninit INV'). }
    { unfold mapper', id, compose. unfolder.
      intros x XIN.
      destruct classic with (x = a_t') as [XEQA|XNQA],
               classic with (x = b_t') as [XEQB|XNQB].
      all: try subst x.
      all: rupd; try now apply INV'.
      all: symmetry; apply INV'. }
    { unfold mapper', id, compose. unfolder.
      intros x _.
      destruct classic with (x = a_t') as [XEQA|XNQA],
               classic with (x = b_t') as [XEQB|XNQB].
      all: try subst x.
      all: try now (exfalso; try now apply (rsr_at_neq_bt INV')).
      { rewrite updo with (c := a_t'); [| apply INV'].
        now rewrite !upds. }
      { rewrite upds, updo with (c := a_t'); [| apply INV'].
        now rewrite upds. }
      rewrite !updo with (c := x); auto. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { unfold mapper', id. clear. unfolder.
      ins. desf. rewrite !updo; congruence. }
    { unfold mapper', id. clear. unfolder.
      ins. desf. now rewrite upds. }
    unfold mapper', id. clear - INV'. unfolder.
    ins. desf. rewrite updo, upds; auto.
    apply INV'. }
  exists mapper', X_s', dtrmt', cmt'.
  unfold NW; split; auto.
  red.
  exists (mapper' ∘ f ∘ mapper'), thrdle.
  constructor; ins; unfold dtrmt', cmt'.
  { rewrite set_collect_compose.
    rewrite <- set_collect_compose with (f := mapper').
     }
  { rewrite (WCore.reexec_embd_dom STEP).
    unfold extra_b, extra_a; desf.
    all: rewrite ?set_union_empty_r.
    { auto with hahn. }
    destruct classic
        with (E_t' b_t')
          as [INB|NINB].
    { rewrite set_union_absorb_r; auto with hahn.
      clear. basic_solver. }
    arewrite (eq b_t' ∩₁ E_t' ≡₁ ∅).
    { clear - NINB. basic_solver. }
    clear. basic_solver. }
  { admit. }
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