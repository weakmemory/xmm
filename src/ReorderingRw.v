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

Record extra_a_pred x : Prop := {
  eba_tid : same_tid b_t x;
}.

Definition extra_a (a_s : actid) :=
  ifP ~E_t a_t /\ E_t b_t then eq a_s
  else ∅.

Definition swap_rel {T : Type} (r : relation T) A B :=
  r \ A × B ∪ B × A.

Definition add_max {T : Type} (A B : T -> Prop) := (A \₁ B) × B.

Definition extra_co_D (s : actid -> Prop) ll l :=
  (s ∩₁ is_w ll ∩₁ (fun e => loc ll e = l)).

Record reord_simrel_gen a_s : Prop := {
  rsr_inj : inj_dom E_t mapper;
  rsr_as : extra_a a_s ⊆₁ extra_a_pred;
  rsr_codom : mapper ↑₁ E_t ⊆₁ E_s \₁ extra_a a_s;
  rsr_init : fixset (E_t ∩₁ is_init) mapper;
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
}.

Record reord_correct_graphs : Prop := {
  rsr_at_tid : tid a_t <> tid_init;
  rsr_at_ninit : ~is_init a_t;
  rsr_bt_ninit : ~is_init b_t;
  rsr_Gt_wf : Wf G_t;
  rsr_Gt_rfc : rf_complete G_t;
  rsr_a_t_is_r_or_w : eq a_t ∩₁ E_t ⊆₁ (W_t ∪₁ R_t);
  rsr_b_t_is_r_or_w : eq b_t ∩₁ E_t ⊆₁ (W_t ∪₁ R_t);
  rsr_init_lab : eq_dom (E_t ∩₁ is_init)
                  lab_s lab_t;
  rsr_init_acts : E_s ∩₁ is_init ≡₁ E_t ∩₁ is_init;
  rsr_at_bt_tid : tid a_t = tid b_t;
}.

Definition reord_simrel := exists a_s, reord_simrel_gen a_s.

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

Lemma add_max_disjoint T (A B : T -> Prop)
    (DISJ : set_disjoint A B) :
  add_max A B ≡ A × B.
Proof using.
  unfold add_max. now rewrite set_minus_disjoint.
Qed.

Lemma extra_co_D_union s1 s2 ll l :
  extra_co_D (s1 ∪₁ s2) ll l ≡₁
    extra_co_D s1 ll l ∪₁ extra_co_D s2 ll l.
Proof using.
  unfold extra_co_D. basic_solver 11.
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

(* Lemma G_t_niff_b_max
    (CONT : contigious_actids G_t)
    (INA : E_t a)
    (NINB : ~E_t b) :
  (fun x => ext_sb x b) ⊆₁ E_t ∩₁ same_tid b ∪₁ is_init.
Proof using RSRW_ACTIDS.
  assert (ANINIT : ~is_init a).
  { apply RSRW_ACTIDS. }
  assert (SMTID : tid a = tid b).
  { apply rsr_tid_a_tid_b. }
  unfolder. intros x SB.
  destruct (classic (x = a)) as [EQ|NEQ]; subst.
  { left. split; ins. }
  destruct (classic (is_init x)) as [INIT|NINIT]; eauto.
  assert (SMTID' : tid x = tid a).
  { rewrite SMTID. red in SB. desf. ins. desf. }
  destruct (ext_sb_semi_total_r) with (x := b) (y := a) (z := x)
                                 as [SB'|SB'].
  all: eauto.
  { destruct x as [xl | x_t x_n], a as [al | a_t a_n]; ins.
    congruence. }
  { apply RSRW_ACTIDS. }
  { exfalso. eapply (rsr_a_b_ord RSRW_ACTIDS); eauto. }
  left. split; [| red; congruence].
  apply ext_sb_dense with (e2 := a); ins.
  rewrite SMTID'. apply RSRW_ACTIDS.
Qed.
 *)

End SimRel.

#[export]
Hint Unfold swap_rel add_max extra_co_D : unfolderDb.

Section ReordSimRelInstrs.

Variable X_t : WCore.t.
Variable e2i_t : actid -> I2Exec.intr_info.
Variable rmwi : I2Exec.instr_id -> Prop.
Variable ai bi : I2Exec.intr_info.
Variable mapper : actid -> actid.
Variable a_t b_t : actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
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

Record program_coherent : Prop := {
  rwi_t_wf : I2Exec.E2InstrWf G_t e2i_t rmwi;
  rwi_at : e2i_t ↑₁ (eq a_t ∩₁ E_t) ⊆₁ eq ai;
  rwi_bt : e2i_t ↑₁ (eq b_t ∩₁ E_t) ⊆₁ eq bi;
  rwi_ai : ~rmwi (I2Exec.instr ai);
  rwi_bi : ~rmwi (I2Exec.instr bi);
}.

End ReordSimRelInstrs.

Module ReordRwSimRelProps.

Section XmmSteps.


Variable X_t X_t' X_s : WCore.t.

Variable G_t G_t' G_s : execution.
Variable a_t b_t : actid.
Variable e2i_s e2i_t : actid -> I2Exec.intr_info.
Variable rmwi : I2Exec.instr_id -> Prop.
Variable ai bi : I2Exec.intr_info.
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

Hypothesis CORR : reord_correct_graphs X_s X_t a_t b_t.

Lemma G_s_co_total ol
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper) :
  is_total (E_s ∩₁ W_s ∩₁ (fun x => loc_s x = ol)) co_s.
Proof using CORR.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  assert (TOT : is_total
                  (mapper ↑₁ E_t ∩₁ W_s ∩₁ Loc_s_ ol)
                  (mapper ↑ co_t)
  ).
  { arewrite (mapper ↑₁ E_t ∩₁ W_s ∩₁ Loc_s_ ol ≡₁
              mapper ↑₁ (E_t ∩₁ W_t ∩₁ Loc_t_ ol)).
    all: try now apply total_collect_rel, CORR.
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
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper) :
  functional rf_s⁻¹.
Proof using CORR.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_rf SIMREL), transp_union.
  apply functional_union.
  { rewrite <- collect_rel_transp, (wf_rfE (rsr_Gt_wf CORR)),
            <- restr_relE, <- restr_transp.
    apply functional_collect_rel_inj; [apply SIMREL|].
    rewrite restr_transp, restr_relE, <- (wf_rfE (rsr_Gt_wf CORR)).
    apply CORR. }
  { rewrite transp_seq, transp_eqv_rel.
    apply functional_seq; [basic_solver |].
    apply wf_srff'.
    intros ol. apply (@G_s_co_total ol).
    now exists a_s. }
  intros x DOM1 DOM2.
  assert (XIN : extra_a X_t a_t b_t a_s x).
  { unfolder in DOM2. desf. }
  apply (rsr_codom SIMREL) with x; ins.
  unfolder. unfolder in DOM1.
  destruct DOM1 as (y & y' & x' & RF & XEQ & YEQ).
  exists x'. split; ins.
  apply (wf_rfE (rsr_Gt_wf CORR)) in RF.
  unfolder in RF. desf.
Qed.

Lemma G_s_rfE
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper) :
  rf_s ≡ ⦗E_s⦘ ⨾ rf_s ⨾ ⦗E_s⦘.
Proof using CORR.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite <- restr_relE, (rsr_rf SIMREL),
          restr_union.
  apply union_more.
  { rewrite (wf_rfE (rsr_Gt_wf CORR)), <- restr_relE.
    rewrite <- collect_rel_restr, restr_restr, (rsr_acts SIMREL).
    { rewrite set_inter_absorb_r; ins. basic_solver. }
    eapply inj_dom_mori; ins; [| apply SIMREL].
    rewrite (wf_rfE (rsr_Gt_wf CORR)). unfold flip.
    basic_solver. }
  rewrite restr_seq_eqv_r. apply seq_more; ins.
  rewrite restr_relE. apply wf_srfE.
Qed.

Lemma sim_rel_init :
  reord_simrel
    (WCore.Build_t (WCore.init_exec G_s) ∅₂)
    (WCore.Build_t (WCore.init_exec G_t) ∅₂)
    a_t b_t
    id.
Proof using CORR.
  assert (EXA : extra_a
    {|
      WCore.G :=
        WCore.init_exec G_t;
      WCore.sc := ∅₂
    |} a_t b_t a_t ≡₁ ∅).
  { unfold extra_a. desf; ins.
    destruct a as (_ & INB). exfalso.
    apply (rsr_bt_ninit CORR), INB. }
  exists a_t.
  constructor; ins.
  { rewrite EXA. basic_solver. }
  { rewrite (rsr_init_acts CORR), EXA. basic_solver. }
  { rewrite Combinators.compose_id_right. apply CORR. }
  { rewrite EXA. rewrite (rsr_init_acts CORR). basic_solver 11. }
  { rewrite EXA, !cross_false_r, !cross_false_l, !union_false_r.
    unfold swap_rel.
    arewrite (eq a_t ∩₁ (E_t ∩₁ is_init) ≡₁ ∅).
    { split; [| basic_solver]. unfolder.
      ins. desf. now apply (rsr_at_ninit CORR). }
    arewrite (eq b_t ∩₁ (E_t ∩₁ is_init) ≡₁ ∅).
    { split; [| basic_solver]. unfolder.
      ins. desf. now apply (rsr_bt_ninit CORR). }
    rewrite !cross_false_r, !union_false_r.
    rewrite minus_disjoint; [| basic_solver].
    unfold sb. ins. rewrite (rsr_init_acts CORR).
    basic_solver 11. }
  { rewrite EXA. basic_solver. }
  { rewrite EXA. basic_solver. }
  basic_solver.
Qed.

Lemma simrel_exec_not_a_not_b e l
    (E_NOT_A : e <> a_t)
    (E_NOT_B : e <> b_t)
    (ETID : forall (WITHA : tid e = tid b_t), ~(~E_t a_t /\ E_t b_t) )
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t b_t mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  (* Generate new actid *)
  assert (NEWE : exists e',
  << NINIT : ~is_init e' >> /\
  << NOTIN : ~E_s e' >> /\
  << TID : tid e' = tid e >> /\
  << NEWSB : ⦗E_s ∪₁ eq e'⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq e'⦘ ≡
          sb_s ∪ WCore.sb_delta X_s e' >>).
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
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper').
  { exists a_s. constructor; ins.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
        now apply SIMREL. }
      { basic_solver. }
      rewrite MAPER_E, MAPSUB, (rsr_codom SIMREL). basic_solver. }
    { rewrite <- EXEQ. apply SIMREL. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB,
              (rsr_codom SIMREL), <- EXEQ, set_minus_union_l.
      apply set_union_mori; ins. rewrite EXIN. basic_solver. }
    { rewrite (WCore.add_event_acts ADD), set_inter_union_l.
      arewrite (eq e ∩₁ is_init ≡₁ ∅) by basic_solver.
      rewrite set_union_empty_r.
      apply fixset_eq_dom with (g := mapper), SIMREL.
      eapply eq_dom_mori; eauto. unfold flip. basic_solver. }
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
        rewrite !set_inter_union_r, set_collect_union.
        apply set_union_more.
        { rewrite set_collect_eq_dom with (g := mapper),
                  <- (fixset_set_fixpoint (rsr_init SIMREL)),
                  <- (rsr_init_acts CORR).
          all: ins.
          eapply eq_dom_mori; eauto. unfold flip. basic_solver. }
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
    { arewrite (srf G_s' ⨾ ⦗extra_a X_t' a_t b_t a_s ∩₁ is_r (upd lab_s e' l)⦘
                ≡ srf G_s ⨾ ⦗extra_a X_t a_t b_t a_s ∩₁ R_s⦘).
      { admit. }
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
    arewrite (co_t' ⨾ ⦗eq e ∩₁ W_t'⦘ ≡ W2 × (eq e ∩₁ WCore.lab_is_w l)).
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
    { admit. }
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
    { arewrite (⦗eq e ∩₁ W_t'⦘ ⨾ co_t' ≡ (eq e ∩₁ WCore.lab_is_w l) × W1).
      { rewrite (lab_is_wE ADD), set_interC, id_inter,
                seqA, (co_deltaE1 (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      arewrite (co_t' ⨾ ⦗eq e ∩₁ W_t'⦘ ≡ W2 × (eq e ∩₁ WCore.lab_is_w l)).
      { rewrite (lab_is_wE ADD), id_inter, <- seqA,
                (co_deltaE2 (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      rewrite (rsr_co SIMREL).
      arewrite (mapper ↑ co_t ≡ mapper' ↑ co_t).
      { symmetry.
        apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_coE (rsr_Gt_wf CORR)). }
      apply transitive_more
       with (y := mapper' ↑ co_t' ∪
              add_max
                (extra_co_D (E_s ∪₁ eq e') (upd lab_s e' l) (loc_s a_s))
                (extra_a X_t a_t b_t a_s ∩₁ (fun a : actid => W_s a))).
      { rewrite (WCore.add_event_co ADD), !collect_rel_union.
        rewrite <- EXEQ, extra_co_D_union, add_max_union.
        rewrite extra_co_D_eq_dom with (ll1 := upd lab_s e' l).
        all: eauto using same_lab_u2v_dom_inclusion.
        rewrite extra_co_eq, upds.
        rewrite !add_max_disjoint with (A := eq e' ∩₁ _) by basic_solver.
        rewrite !add_max_disjoint with (A := eq e' ∩₁ _ ∩₁ _) by basic_solver.
        rewrite <- unionA.
        unfold extra_a; desf; basic_solver 12. }
      assert (TRANS : transitive (mapper' ↑ co_t')).
      { admit. }
      destruct classic
          with (extra_a X_t a_t b_t a_s ∩₁ W_s ≡₁ eq a_s)
            as [EQ | NEQ].
      { rewrite EQ. unfold add_max.
        apply expand_transitive; ins.
        { unfolder. intro FALSO. desf. }
        { admit. }
        unfolder. unfolder in INX.
        destruct INX as (((_ & ISW) & LOC) & NEQ).
        splits.
        { admit. }
        { admit. }
        { admit. }
        admit. }
      arewrite (extra_a X_t a_t b_t a_s ∩₁ W_s ≡₁ ∅).
      { split; [| basic_solver]. intros x (XIN & ISW).
        red. apply NEQ. unfold extra_a. unfold extra_a in XIN.
        desf. basic_solver. }
      unfold extra_co_D.
      now rewrite add_max_empty_r, union_false_r. }
    { arewrite (rf_t' ⨾ ⦗eq e ∩₁ R_t'⦘ ≡ WCore.rf_delta_R e l w).
      { rewrite (lab_is_rE ADD), id_inter, <- seqA,
                (rf_delta_RE (rsr_Gt_wf CORR) ADD).
        basic_solver. }
      rewrite transp_union, mapped_rf_delta_R.
      apply functional_union.
      { now apply G_s_rff. }
      { basic_solver. }
      intros x DOM1 DOM2.
      assert (XEQ : x = e').
      { unfolder in DOM2. desf. subst mapper'. now rupd. }
      subst x. apply NOTIN.
      unfolder in DOM1. destruct DOM1 as (y & RF).
      apply (G_s_rfE OLDSIMREL) in RF.
      unfolder in RF. desf. }
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
  { admit. (* RFCOM *) }
  admit.
Admitted.

Lemma simrel_exec_b_step_1
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (BNOTIN : ~E_t b_t) :
  exists a_s l_a X_s'',
    << ATID : same_tid b_t a_s >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a >> /\
    << RF : rf (WCore.G X_s'') ≡
            rf_s ∪ srf (WCore.G X_s'') ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘ >> /\
    << CO : co (WCore.G X_s'') ≡
            co_s ∪ (E_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
                (eq a_s ∩₁ WCore.lab_is_w l_a) >> /\
    << RMW : rmw (WCore.G X_s'') ≡ rmw_s >>.
Proof using.
  (* Generate new actid *)
  assert (NEWE : exists a_s,
  << NOTIN : ~E_s a_s >> /\
  << TID : tid a_s = tid b_t >> /\
  << SB : ⦗E_s ∪₁ eq a_s⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq a_s⦘ ≡
          sb_s ∪ WCore.sb_delta X_s a_s >>).
  { admit. }
  (* unfold hypotheses *)
  red in SIMREL. destruct SIMREL as (a_s' & SIMREL).
  destruct NEWE as (a_s & NOTIN & NEWTID & NEWSB).
  red in NOTIN, NEWTID, NEWSB.
  (* The proof *)
Admitted.

Lemma simrel_exec_b l
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' b_t l) :
  exists a_s l_a X_s'' mapper' X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t b_t mapper' >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a >> /\
    << STEP2 : WCore.exec_inst X_s'' X_s' (mapper' b_t) l >>.
Proof using.
  (* unfold hypotheses *)
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  (* Do step 1 *)
  destruct (simrel_exec_b_step_1 SIMREL)
        as (a_s & l_a & X_s'' & ATID & STEP1 & RF' & CO' & RMW').
  { apply ADD. }
  exists a_s, l_a, X_s''.
  destruct STEP1 as [ADD' RFC' CONS'].
  destruct ADD' as (r' & R1' & w' & W1' & W2' & ADD').
  (* Generate new actid *)
  assert (NEWE : exists b_s,
  << NOTIN : ~(E_s ∪₁ eq a_s) b_s >> /\
  << TID : tid b_s = tid b_t >> /\
  << SB : ⦗E_s ∪₁ eq a_s ∪₁ eq b_s⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq a_s ∪₁ eq b_s⦘ ≡
          sb (WCore.G X_s'') ∪ WCore.sb_delta X_s'' b_s >>).
  { admit. }
  red in SIMREL. destruct SIMREL as (a_s' & SIMREL).
  destruct NEWE as (b_s & NOTIN & NEWTID & NEWSB).
  red in NOTIN, NEWTID, NEWSB, RF', CO', RMW'.
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
  { admit. }
  assert (ANOTIN' : ~E_t' a_t).
  { intro FALSO. apply (WCore.add_event_acts ADD) in FALSO.
    destruct FALSO as [INE|EQ]; eauto.
    admit. (* TODO a_t <> b_t *) }
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
  (* The proof *)
  exists mapper', X_s'.
  splits; ins.
  { exists a_s. constructor; ins.
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
    { admit. }
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
    { admit. }
    { arewrite (rf_t' ⨾ ⦗eq b_t ∩₁ R_t'⦘ ≡ WCore.rf_delta_R b_t l w).
      { admit. }
      rewrite NEWEXA.
      arewrite (srf G_s' ⨾ ⦗
          eq a_s ∩₁ is_r (upd (upd lab_s a_s l_a) b_s l)
        ⦘ ≡ srf (WCore.G X_s'') ⨾ ⦗eq a_s ∩₁ WCore.lab_is_r l_a⦘).
      { admit. }
      rewrite (rsr_rf SIMREL), (WCore.add_event_rf ADD),
              !collect_rel_union.
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { admit. }
      rewrite OLDEXA.
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, !union_false_r.
      basic_solver 12. }
    admit. }
  { constructor; ins.
    now exists r', R1', w', W1', W2'. }
  constructor; ins.
  { exists (option_map mapper' r), (mapper' ↑₁ R1),
         (option_map mapper' w), (mapper' ↑₁ W1), (mapper' ↑₁ W2).
    constructor; ins.
    { admit. }
    { admit. }
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
    { admit. }
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
    { admit. }
    { admit. }
    { rewrite (WCore.add_event_acts ADD'). unfold mapper'.
      now rupd. }
    { now rewrite (WCore.add_event_threads ADD'). }
    { rewrite (WCore.add_event_lab ADD'). unfold mapper'.
      now rupd. }
    { arewrite (WCore.rf_delta_R (mapper' b_t) l (option_map mapper' w) ≡
                mapper' ↑ WCore.rf_delta_R b_t l w).
      { admit. }
      arewrite (WCore.rf_delta_W (mapper' b_t) l (mapper' ↑₁ R1) ≡
                mapper' ↑ WCore.rf_delta_W b_t l R1).
      { admit. }
      arewrite (rf_t' ⨾ ⦗eq b_t ∩₁ R_t'⦘ ≡ WCore.rf_delta_R b_t l w).
      { admit. }
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, union_false_r.
      rewrite RF'. basic_solver 12. }
    { arewrite (⦗eq b_t ∩₁ W_t'⦘ ⨾ co_t' ≡ (eq b_t ∩₁ WCore.lab_is_w l) × W1).
      { admit. }
      arewrite (co_t' ⨾ ⦗eq b_t ∩₁ W_t'⦘ ≡ W2 × (eq b_t ∩₁ WCore.lab_is_w l)).
      { admit. }
      arewrite (WCore.co_delta (mapper' b_t) l (mapper' ↑₁ W1) (mapper' ↑₁ W2) ≡
                  mapper' ↑ (eq b_t ∩₁ WCore.lab_is_w l) × W1 ∪
                  mapper' ↑ W2 × (eq b_t ∩₁ WCore.lab_is_w l)).
      { admit. }
      rewrite CO'. basic_solver 12. }
    { arewrite (WCore.rmw_delta (mapper' b_t) l (option_map mapper' r) ≡
                mapper' ↑ WCore.rmw_delta b_t l r).
      { admit. }
      rewrite (WCore.add_event_rmw ADD), collect_rel_union.
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { admit. }
      now rewrite RMW', (rsr_rmw SIMREL). }
    { now rewrite (WCore.add_event_data ADD'). }
    { now rewrite (WCore.add_event_addr ADD'). }
    { now rewrite (WCore.add_event_ctrl ADD'). }
    { now rewrite (WCore.add_event_rmw_dep ADD'). }
    unfold sb at 1. ins. rewrite NEWSB.
    unfold mapper'. now rupd. }
  { admit. (* rfcom *) }
  admit. (* is_cons *)
Admitted.

Lemma simrel_exec_a l
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (INB : E_t b_t)
    (STEP : WCore.exec_inst X_t X_t' a_t l) :
  exists mapper' X_s' cmt',
    << SIM : reord_simrel X_s' X_t' a_t b_t mapper' >> /\
    << STEP : WCore.reexec X_s X_s' cmt' >>.
Proof using CORR.
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
  assert (NOTINA : ~E_t a_t).
  { apply ADD. }
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
  { unfold extra_a; desf. desf. exfalso. apply a.
    apply ADD. basic_solver. }
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
  (* The proof *)
  exists mapper', X_s', cmt'.
  split; red; ins.
  { exists a_s. constructor; ins.
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
    { admit. }
    { rewrite (WCore.add_event_acts ADD). apply eq_dom_union.
      split; unfold compose; unfolder; intros x XINE.
      { rewrite MAPEQ; ins. now apply SIMREL. }
      subst x. unfold mapper'. rupd. admit. }
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
    { admit. }
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
      { admit. }
      arewrite (mapper' ↑ (WCore.rf_delta_R a_t l w ⨾ ⦗eq a_t ∩₁ R_t'⦘)
                ≡ mapper' ↑ (WCore.rf_delta_R a_t l w)).
      { admit. }
      rewrite (WCore.add_event_rf ADD), !collect_rel_union.
      arewrite (mapper' ↑ (WCore.rf_delta_W a_t l R1) ≡ ∅₂).
      { admit. }
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { admit. }
      now rewrite !union_false_r. }
    admit. }
  red. exists id, thrdle', dtrmt'.
  constructor; ins.
  { subst dtrmt' cmt'. basic_solver. }
  { subst cmt'. basic_solver. }
  { constructor; ins.
    { unfolder. subst thrdle'. ins.
      splits; try red; eauto. intro FALSO.
      apply (rsr_at_tid CORR). admit. }
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
    rewrite union_false_l. unfolder. intros x y [_ EQ]. subst y.
    destruct classic with (tid x = tid a_s) as [TID | NTID].
    { admit. }
    right. subst thrdle'; ins; splits; eauto.
    admit. }
  { constructor; ins.
    all: admit. }
  { admit. (* TODO: wf *) }
  { admit. (* TODO: cons *) }
  admit. (* subtofull *)
Admitted.

Lemma simrel_reexec cmt a_t' b_t' e2i_t'
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (PROG  : program_coherent X_t  e2i_t  rmwi ai bi a_t  b_t )
    (PROG' : program_coherent X_t' e2i_t' rmwi ai bi a_t' b_t')
    (STEP : WCore.reexec X_t X_t' cmt) :
  exists mapper' X_s',
    << SIM : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP : WCore.reexec X_s X_s' (mapper' ↑₁ cmt) >>.
Proof using CORR.
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