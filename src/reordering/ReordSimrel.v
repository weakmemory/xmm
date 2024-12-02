Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import xmm_s_hb.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import Setoid Morphisms Program.Basics.

Open Scope program_scope.

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
Notation "'rhb_t'" := (rhb G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rpo_imm_t'" := (rpo_imm G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'hb_t'" := (hb G_t).
Notation "'eco_t'" := (eco G_t).
Notation "'sw_t'" := (sw G_t).
Notation "'vf_t'" := (vf G_t).
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
Notation "'rhb_s'" := (rhb G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rpo_imm_s'" := (rpo_imm G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun e => is_true (is_w lab_s e)).
Notation "'R_s'" := (fun e => is_true (is_r lab_s e)).
Notation "'F_s'" := (fun e => is_true (is_f lab_s e)).
Notation "'b_s'" := (mapper b_t).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'same_val_s'" := (same_val lab_s).
Notation "'Acq_s'" := (fun e => is_true (is_acq lab_s e)).
Notation "'Rel_s'" := (fun e => is_true (is_rel lab_s e)).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).

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
  rsr_at_bt_sb : ext_sb b_t a_t;
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

Lemma rsr_mapper
    (SIMREL : reord_simrel) :
  eq_dom E_t mapper (upd (upd id a_t b_t) b_t a_t).
Proof using.
  unfolder. intros x XIN.
  destruct classic with (x = b_t) as [XEQB|XNQB].
  { subst x. rewrite upds. symmetry.
    apply (rsr_bt SIMREL). basic_solver. }
  rewrite updo by exact XNQB.
  destruct classic with (x = a_t) as [XEQA|XNQA].
  { subst x. rewrite upds. symmetry.
    apply (rsr_at SIMREL). basic_solver. }
  rewrite updo by exact XNQA.
  rewrite (rsr_mid SIMREL); [reflexivity |].
  basic_solver.
Qed.

Lemma rsr_rf_from_exa
    (CORR : reord_step_pred)
    (SIMREL : reord_simrel)
    (INB : E_t b_t)
    (NINA : ~ E_t a_t) :
  ⦗eq b_t⦘ ⨾ rf_s ⊆ ∅₂.
Proof using.
  rewrite (rsr_rf SIMREL), extra_a_some; auto.
  rewrite seq_union_r.
  arewrite (srf_s ⨾ ⦗eq b_t ∩₁ R_s⦘ ⊆ rf_s ⨾ ⦗eq b_t ∩₁ R_s⦘).
  { rewrite (rsr_rf SIMREL), seq_union_l,
            !seqA, extra_a_some.
    all: auto.
    seq_rewrite seq_eqvK. auto with hahn. }
  assert (INJ :
    inj_dom (
      codom_rel ⦗E_t⦘ ∪₁ dom_rel
        (rf_t ⨾ ⦗E_t⦘)
    ) mapper
  ).
  { rewrite (wf_rfE (rsr_Gt_wf CORR)).
    eapply inj_dom_mori; [| reflexivity | apply (rsr_inj SIMREL)].
    unfold flip. basic_solver. }
  apply inclusion_union_l.
  { rewrite (wf_rfE (rsr_Gt_wf CORR)),
            collect_rel_seq, collect_rel_eqv,
            (rsr_codom SIMREL), extra_a_some.
    all: auto.
    seq_rewrite <- id_inter.
    arewrite (eq b_t ∩₁ (E_s \₁ eq b_t) ⊆₁ ∅).
    all: basic_solver 11. }
  rewrite id_inter.
  arewrite_false (⦗eq b_t⦘ ⨾ rf_s ⨾ ⦗eq b_t⦘); [| basic_solver].
  rewrite <- restr_relE.
  apply restr_irrefl_eq, (rf_irr (G_s_wf CORR SIMREL)).
Qed.

Lemma rsr_sbt_in
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  mapper ↑ (sb_t \ eq b_t × eq a_t) ⊆ sb_s.
Proof using.
  rewrite (rsr_sb SIMREL).
  arewrite (
    sb_t \ eq b_t × eq a_t ⊆
    sb_t \ (eq b_t ∩₁ E_t) × (eq a_t ∩₁ E_t)
  ).
  { apply minus_rel_mori; auto with hahn.
    unfold flip. basic_solver. }
  basic_solver 11.
Qed.

Lemma rsr_no_rfrhb_ba
    (PRED : reord_step_pred)
    (CONS : WCore.is_cons G_t ∅₂) :
  rf_t ⨾ rhb_t^? ⊆ rf_t ⨾ rhb_t^? \ eq b_t × eq a_t.
Proof using.
  unfolder.
  intros x y (z & RF & RHB).
  split; [eauto | intro FALSO].
  destruct RHB as [EQ | RHB]; desf.
  { apply (rsr_at_bt_loc PRED)
     with (x := a_t) (y := b_t).
    unfolder. splits; auto.
    { apply (wf_rfE (rsr_Gt_wf PRED)) in RF.
      unfolder in RF. desf. }
    { apply (wf_rfl (rsr_Gt_wf PRED)) in RF.
      unfold same_loc in *. congruence. }
    apply (wf_rfE (rsr_Gt_wf PRED)) in RF.
    unfolder in RF. desf. }
  assert (AIN : E_t a_t).
  { apply (wf_rhbE (rsr_Gt_wf PRED)) in RHB.
    unfolder in RHB. desf. }
  assert (BIN : E_t b_t).
  { apply (wf_rfE (rsr_Gt_wf PRED)) in RF.
    unfolder in RF. desf. }
  assert (ZIN : E_t z).
  { apply (wf_rfE (rsr_Gt_wf PRED)) in RF.
    unfolder in RF. desf. }
  assert (IMMSB : immediate sb_t b_t a_t).
  { apply (rsr_at_bt_imm PRED). basic_solver. }
  assert (ZNINIT : ~is_init z).
  { apply (no_rf_to_init (rsr_Gt_wf PRED)) in RF.
    unfolder in RF. desf. }
  assert (BNINIT : ~is_init b_t).
  { apply (rsr_bt_ninit PRED). }
  apply rhb_as_sb_swsb in RHB.
  destruct RHB as [SB | SBSW].
  { enough (SB' : sb_t z b_t).
    { apply (WCore.cons_coherence CONS) with z.
      exists b_t. split; [now apply sb_in_hb |].
      now apply r_step, rf_in_eco. }
    assert (ZTID : tid b_t = tid z).
    { rewrite <- (rsr_at_bt_tid PRED).
      unfold sb, ext_sb in SB.
      unfolder in SB. desf.
      ins. desf. }
    destruct PeanoNat.Nat.lt_total
        with (n := index z) (m := index b_t)
          as [ZB | [EQ | BZ]].
    { unfold sb, ext_sb, index in *.
      unfolder in *. desf. }
    { exfalso.
      apply (rf_irr (rsr_Gt_wf PRED)) with (x := b_t).
      unfold index, tid in *. desf. }
    exfalso.
    apply IMMSB with (c := z); auto.
    unfold sb, ext_sb. unfolder; splits; auto.
    unfold index, tid in *. desf. }
  hahn_rewrite <- seqA in SBSW.
  destruct SBSW as (z' & (w & RHB & SW) & SB).
  apply crE in SB. destruct SB as [EQ | SB].
  { unfolder in EQ. desf.
    apply (wf_swD (rsr_Gt_wf PRED)) in SW.
    apply (rsr_at_nacq PRED) with a_t.
    { basic_solver. }
    unfolder in SW. desf. }
  enough (SB' : sb_t z' b_t).
  { apply (WCore.cons_coherence CONS) with z.
    exists b_t.
    split; [| now apply r_step, rf_in_eco].
    apply hb_trans with z'; [| now apply sb_in_hb].
    enough (HB : (hb_t^? ⨾ hb_t) z z').
    { hahn_rewrite crE in HB.
      unfolder in HB; desf.
      eapply hb_trans; eauto. }
    exists w.
    split; [hahn_rewrite <- rhb_in_hb | apply sw_in_hb].
    all: auto. }
  assert (ZIN' : E_t z').
  { apply (wf_swE (rsr_Gt_wf PRED)) in SW.
    unfolder in SW. desf. }
  assert (ZNINIT' : ~is_init z').
  { apply (no_sw_to_init (rsr_Gt_wf PRED)) in SW.
    unfolder in SW. desf. }
  assert (ZTID : tid b_t = tid z').
  { rewrite <- (rsr_at_bt_tid PRED).
    unfold sb, ext_sb in SB.
    unfolder in SB. desf.
    ins. desf. }
  destruct PeanoNat.Nat.lt_total
      with (n := index z') (m := index b_t)
        as [ZB | [EQ | BZ]].
  { unfold sb, ext_sb, index in *.
    unfolder in *. desf. }
  { exfalso.
    apply (WCore.cons_coherence CONS) with z.
    exists b_t.
    split; [| now apply r_step, rf_in_eco].
    arewrite (b_t = z').
    { unfold tid, index in *. desf. }
    enough (HB : (hb_t^? ⨾ hb_t) z z').
    { hahn_rewrite crE in HB.
      unfolder in HB; desf.
      eapply hb_trans; eauto. }
    exists w.
    split; [hahn_rewrite <- rhb_in_hb | apply sw_in_hb].
    all: auto. }
  exfalso.
  apply IMMSB with (c := z'); auto.
  unfold sb, ext_sb. unfolder; splits; auto.
  unfold index, tid in *. desf.
Qed.

Lemma rsr_rhb
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  ⦗E_s \₁ extra_a b_t⦘ ⨾ rhb_s ⊆ mapper ↑ rhb_t.
Proof using.
  admit.
Admitted.

Lemma rsr_sb_nexa
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  ⦗extra_a b_t⦘ ⨾ sb_s ⊆ eq b_t × eq a_t.
Proof using.
  unfold extra_a. desf; [| basic_solver].
  rewrite (rsr_sb SIMREL).
  rewrite !seq_union_r.
  rewrite extra_a_some by desf.
  arewrite_false (⦗eq b_t⦘ ⨾ mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t)).
  { admit. }
  arewrite_false (⦗eq b_t⦘ ⨾ (mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘)) × eq b_t).
  { admit. }
  rewrite !union_false_l.
  arewrite (b_s = a_t).
  { symmetry. apply (rsr_bt SIMREL).
    basic_solver. }
  basic_solver.
Admitted.

Lemma nini_sb_imm_split G a
    (WF : Wf G) :
  immediate (nin_sb G) ≡
    immediate (⦗fun e => ~nin_sb G e a⦘ ⨾ nin_sb G ⨾ ⦗fun e => ~nin_sb G a e⦘) ∪
      immediate (⦗left_dom (nin_sb G) a⦘ ⨾ nin_sb G ⨾ ⦗left_dom (nin_sb G) a ∪₁ eq a⦘) ∪
        immediate (⦗right_dom (nin_sb G) a ∪₁ eq a⦘ ⨾ nin_sb G ⨾ ⦗right_dom (nin_sb G) a⦘).
Proof using.
  apply imm_split.
  { unfold semi_total_l. unfolder.
    ins. desf.
    destruct sb_semi_total_l with G x y z as [SB|SB]; auto.
    { forward apply XZ. unfold nin_sb. basic_solver. }
    { forward apply XZ. unfold nin_sb. basic_solver. }
    { forward apply YZ. unfold nin_sb. basic_solver. }
    { left. unfold nin_sb. unfolder.
      split; auto.
      unfold nin_sb in XZ. unfolder in XZ.
      destruct XZ as (_ & XZ).
      apply no_sb_to_init in XZ.
      forward apply XZ. basic_solver. }
    right. unfold nin_sb. unfolder.
    split; auto.
    unfold nin_sb in YZ. unfolder in YZ.
    destruct YZ as (_ & YZ).
    apply no_sb_to_init in YZ.
    forward apply YZ. basic_solver. }
  { unfold semi_total_r. unfolder.
    ins. desf.
    destruct sb_semi_total_r with G z x y as [SB|SB]; auto.
    { forward apply YZ. unfold nin_sb. basic_solver. }
    { forward apply XZ. unfold nin_sb. basic_solver. }
    { forward apply YZ. unfold nin_sb. basic_solver. }
    { left. unfold nin_sb. unfolder.
      split; auto.
      unfold nin_sb in XZ. unfolder in XZ.
      desf. }
    right. unfold nin_sb. unfolder.
    split; auto.
    unfold nin_sb in YZ. unfolder in YZ.
    desf. }
  unfolder. ins. desf.
  unfold nin_sb in *.
  unfolder in *. desf.
  split; [auto | eapply sb_trans; eauto].
Qed.

Lemma rsr_rhb_exa
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  ⦗extra_a b_t⦘ ⨾ rhb_s ⊆ ∅₂.
Proof using.
  unfold rhb.
  rewrite ct_begin, !seq_union_l,
          !seq_union_r.
  arewrite_false (⦗extra_a b_t⦘ ⨾ sb_s ∩ same_loc_s).
  { rewrite <- seq_eqv_inter_ll.
    rewrite (rsr_sb_nexa PRED SIMREL).
    admit. }
  unfold rpo. rewrite ct_begin, !seqA.
  arewrite_false (⦗extra_a b_t⦘ ⨾ rpo_imm_s).
  { unfold rpo_imm. admit. }
  arewrite_false (⦗extra_a b_t⦘ ⨾ sw G_s).
  { admit. }
  rewrite !seq_false_l. auto with hahn.
Admitted.

Lemma rsr_vfrhb
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  vf_rhb G_s ⊆ mapper ↑ (vf_rhb G_t).
Proof using.
  unfold vf_rhb.
  rewrite (rsr_rf SIMREL), cr_union_l,
          !seq_union_l, !seq_union_r.
  rewrite !seqA.
  arewrite (
    srf_s ⨾ ⦗extra_a b_t ∩₁ R_s⦘ ⨾ rhb_s^? ≡
      srf_s ⨾ ⦗extra_a b_t ∩₁ R_s⦘
  ).
  { admit. }
  arewrite (
    (mapper ↑ rf_t)^? ⨾ rhb_s^? ⊆
      (mapper ↑ rf_t)^? ⨾ ⦗E_s \₁ extra_a b_t⦘ ⨾ rhb_s^?
  ).
  { admit. }
  admit.
Admitted.

Lemma rsr_vf
    (PRED : reord_step_pred)
    (SIMREL : reord_simrel) :
  vf_s ⊆ mapper ↑ vf_t.
Proof using.
  admit.
Admitted.

End SimRel.