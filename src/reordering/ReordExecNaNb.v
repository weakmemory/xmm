Require Import ReordSimrel ReorderingEq ReorderingMapper.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import PorfPrefix.
Require Import ReorderingCons.

Require Import SubToFullExec.
Require Import xmm_s_hb.
Require Import Thrdle.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Section ExecNotANotB.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t : actid.
Variable e : actid.
Variable l : label.

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
Notation "'sw_t''" := (sw G_t').
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
Notation "'sw_s'" := (sw G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun x => is_true (is_w lab_s x)).
Notation "'R_s'" := (fun x => is_true (is_r lab_s x)).
Notation "'F_s'" := (fun x => is_true (is_f G_s x)).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (fun x => is_true (is_rlx G_s x)).
Notation "'Acq_s'" := (fun x => is_true (is_acq G_s x)).
Notation "'Rel_s'" := (fun x => is_true (is_rel G_s x)).

Notation "'is_init'" := (fun e => is_true (is_init e)).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'mapper'" := (mapper a_t b_t).

Notation "'A_s'" := (extra_a X_t a_t b_t b_t).
Notation "'B_s'" := (extra_a X_t a_t b_t a_t).
Notation "'A_s''" := (extra_a X_t' a_t b_t b_t).

Definition rsr_nanb_Gs_prime := {|
  acts_set := E_s ∪₁ eq e;
  threads_set := threads_set G_s;
  lab := upd lab_s e l;
  rf := rf_s ∪ mapper ↑ (rf_t' ⨾ ⦗eq e⦘);
  co := co_s ∪
        mapper ↑ (⦗eq e⦘ ⨾ co_t' ∪ co_t' ⨾ ⦗eq e⦘) ∪
        add_max (eq e ∩₁ WCore.lab_is_w l)
          (A_s' ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l));
  rmw := mapper ↑ rmw_t';
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.

Definition rsr_nanb_Xs_prime := {|
  WCore.G := rsr_nanb_Gs_prime;
  WCore.sc := WCore.sc X_s;
|}.

Notation "'X_s''" := rsr_nanb_Xs_prime.
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
Notation "'Loc_s_'' l" := (fun e => loc_s' e = l) (at level 1).
Notation "'Val_s_'' l" := (fun e => val_s' e = l) (at level 1).
Notation "'Rlx_s''" := (fun e => is_true (is_rlx lab_s' e)).
Notation "'Acq_s''" := (fun e => is_true (is_acq lab_s' e)).
Notation "'Rel_s''" := (fun e => is_true (is_rel lab_s' e)).

Hypothesis ADD : WCore.add_event X_t X_t' e l.

Lemma rsr_step_acts : E_t' ≡₁ E_t ∪₁ eq e.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_e_tid : tid e <> tid_init.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_e_ninit : ~is_init e.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_e_notin : ~E_t e.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_step_lab : lab_t' = upd lab_t e l.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_ext_sb_to_at
    (EXTSB : ext_sb e a_t) :
  tid e = tid a_t.
Proof using ADD.
  destruct (ext_sb_tid_init _ _ EXTSB); auto.
  enough (HH : ~ is_init e) by desf.
  apply rsr_e_ninit.
Qed.

Hint Resolve rsr_e_tid rsr_e_notin rsr_ext_sb_to_at
             rsr_e_ninit : xmm.

Hypothesis E_NOT_A : e <> a_t.
Hypothesis E_NOT_B : e <> b_t.

Lemma rsr_a_preservedE : eq a_t ∩₁ E_t' ≡₁ eq a_t ∩₁ E_t.
Proof using a_t ADD E_NOT_A.
  clear E_NOT_B. rewrite rsr_step_acts. basic_solver.
Qed.

Lemma rsr_b_preservedE : eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t.
Proof using b_t ADD E_NOT_B.
  clear E_NOT_A. rewrite rsr_step_acts. basic_solver.
Qed.

Lemma rsr_a_preserved : E_t' a_t <-> E_t a_t.
Proof using a_t ADD E_NOT_A.
  split; intro AIN.
  all: apply rsr_a_preservedE; basic_solver.
Qed.

Lemma rsr_b_preserved : E_t' b_t <-> E_t b_t.
Proof using b_t ADD E_NOT_B.
  split; intro AIN.
  all: apply rsr_b_preservedE; basic_solver.
Qed.

Lemma rsr_same_exa : A_s ≡₁ A_s'.
Proof using b_t a_t ADD E_NOT_B E_NOT_A.
  set (APR := rsr_a_preserved).
  set (BPR := rsr_b_preserved).
  unfold extra_a; desf; tauto.
Qed.

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t b_t.
Hypothesis CONS : WCore.is_cons G_t'.

Lemma rsr_ext_sb_from_at
    (EXTSB : ext_sb a_t e) :
  tid e = tid a_t.
Proof using ADD INV.
  destruct (ext_sb_tid_init _ _ EXTSB); auto.
  enough (HH : ~ is_init a_t) by desf.
  apply (rsr_at_ninit INV).
Qed.

Lemma rsr_Et_restr'
    (ETID : tid e = tid b_t) :
  ~ (E_t' b_t /\ ~E_t' a_t).
Proof using b_t ADD E_NOT_B INV'.
  intros (INB' & NINA').
  apply (rsr_bt_max INV' INB' NINA') with b_t e.
  assert (INB : E_t b_t) by now apply rsr_b_preserved.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  hahn_rewrite (WCore.add_event_sb ADD').
  exists b_t. split; [basic_solver |].
  right. basic_solver.
Qed.

Lemma rsr_Et_restr
    (ETID : tid e = tid b_t) :
  ~ (E_t b_t /\ ~E_t a_t).
Proof using b_t ADD E_NOT_B E_NOT_A INV'.
  intros (INB' & NINA').
  apply rsr_Et_restr'; auto.
  set (APR := rsr_a_preserved).
  set (BPR := rsr_b_preserved).
  tauto.
Qed.

Hint Resolve rsr_ext_sb_from_at rsr_Et_restr'
             rsr_Et_restr : xmm.

Hypothesis SIMREL : reord_simrel X_s X_t a_t b_t mapper.

Lemma rsr_new_e_sb_delta :
  ⦗E_s⦘ ⨾ ext_sb ⨾ ⦗eq e⦘ ≡ WCore.sb_delta e E_s.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  rewrite (rsr_actsE INV SIMREL).
  arewrite (WCore.sb_delta e (E_t ∪₁ B_s) ≡
    WCore.sb_delta e E_t ∪ (B_s ∩₁ same_tid e) × eq e
  ).
  { unfold WCore.sb_delta.
    rewrite set_inter_union_l, !cross_union_l.
    now rewrite <- unionA. }
  rewrite id_union, !seq_union_l.
  apply union_more; [apply (sb_deltaEE ADD') |].
  unfold extra_a. desf; [| basic_solver].
  unfold same_tid. split.
  { unfolder. intros x y (EQ1 & SB & EQ2).
    subst x y. auto with xmm. }
  unfolder. intros x y ((EQ1 & TID) & EQ2). subst x y.
  exfalso. apply rsr_Et_restr; [| desf].
  now rewrite <- (rsr_at_bt_tid INV).
Qed.

Lemma rsr_new_e_sb :
  sb_s' ≡ sb_s ∪ WCore.sb_delta e E_s.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  unfold sb at 1. simpl.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  rewrite !id_union, !seq_union_l, !seq_union_r.
  change (⦗E_s⦘ ⨾ ext_sb ⨾ ⦗E_s⦘) with sb_s.
  rewrite (rsr_actsE INV SIMREL) at 2.
  rewrite !id_union, !seq_union_r.
  arewrite_false (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗eq e⦘).
  { enough (~ext_sb e e) by basic_solver.
    intro FALSO; eapply ext_sb_irr; eauto. }
  rewrite (sb_deltaEN ADD').
  arewrite_false (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗extra_a X_t a_t b_t a_t⦘).
  { unfold extra_a; desf; [| basic_solver].
    unfolder. intros x y (EQ1 & SB & EQ2). subst x y.
    apply rsr_Et_restr; desf.
    rewrite <- (rsr_at_bt_tid INV); auto with xmm. }
  now rewrite !union_false_r, rsr_new_e_sb_delta.
Qed.

Lemma rsr_nanb_map_sbdelta :
  mapper ↑ WCore.sb_delta e E_t ≡
    WCore.sb_delta e E_s.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  assert (ANINI : ~is_init a_t) by apply INV.
  assert (BNINI : ~is_init b_t) by apply INV.
  unfold WCore.sb_delta.
  rewrite collect_rel_cross, set_collect_eq, rsr_mappero; auto.
  rewrite set_collect_union.
  rewrite <- fixset_set_fixpoint by auto with xmm.
  arewrite (mapper ↑₁ (E_t ∩₁ same_tid e) ≡₁ E_s ∩₁ same_tid e)
    ; [| reflexivity].
  rewrite (rsr_acts SIMREL), set_inter_union_l.
  rewrite rsr_mapper_sametid; auto.
  arewrite (A_s ∩₁ same_tid e ≡₁ ∅); [| now rewrite set_union_empty_r].
  unfold extra_a, same_tid; desf; [| basic_solver].
  split; auto with hahn.
  unfolder. intros x (XEQ & TID). subst x.
  apply rsr_Et_restr; auto; desf.
Qed.

Lemma rsr_nanb_notin : ~ E_s e.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  intro EIN. apply (rsr_actsE INV SIMREL) in EIN.
  destruct EIN as [EINT | INB].
  { now apply rsr_e_notin. }
  unfold extra_a in INB; desf.
Qed.

Lemma rsr_nanb_notin' : ~ E_s (mapper e).
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  rewrite rsr_mappero; auto.
  apply rsr_nanb_notin.
Qed.

Hint Resolve rsr_nanb_notin rsr_nanb_notin' : xmm.

Lemma rsr_nanb_labeq : eq_dom E_s lab_s' lab_s.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  apply eq_dom_upd_l; [apply rsr_nanb_notin | reflexivity].
Qed.

Lemma rsr_nanb_lab : eq_dom E_t' lab_t' (lab_s' ∘ mapper).
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl.
  rewrite <- rsr_mappero with (a_t := a_t) (b_t := b_t) (x := e).
  all: auto.
  rewrite rsr_step_lab, <- upd_compose; auto with xmm.
  rewrite rsr_step_acts. apply eq_dom_union. split.
  { apply eq_dom_upd; auto with xmm.
    symmetry. apply SIMREL. }
  apply eq_dom_eq. now rewrite !upds.
Qed.

Lemma rsr_nanb_lab' : eq_dom E_t' (lab_s' ∘ mapper) lab_t'.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  symmetry. exact rsr_nanb_lab.
Qed.

Lemma rsr_nanb_mapinj : inj_dom E_t' mapper.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  eapply inj_dom_mori; auto with xmm.
  red; auto with hahn.
Qed.

Hint Resolve rsr_nanb_lab rsr_nanb_lab' rsr_nanb_labeq
            rsr_nanb_mapinj rsr_Gt_wf : xmm.

Lemma rsr_nanb_samesrf_helper :
  srf G_s' ⨾ ⦗E_s⦘ ≡ srf G_s ⨾ ⦗E_s⦘.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  set (NOTIN := rsr_nanb_notin).
  set (NOTIN' := rsr_nanb_notin').
  apply (porf_pref_srf G_s G_s'); auto with xmm.
  { eapply G_s_wf with (X_t := X_t); eauto. }
  { ins. auto with hahn. }
  { rewrite rsr_new_e_sb.
    clear - NOTIN. rewrite seq_union_l. basic_solver. }
  { simpl. clear - NOTIN'. basic_solver. }
  { simpl. clear - NOTIN NOTIN'. basic_solver 7. }
  simpl. destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  rewrite (WCore.add_event_rmw ADD'), (rsr_rmw SIMREL).
  rewrite collect_rel_union.
  clear - NOTIN' NOTIN. basic_solver 7.
Qed.

Lemma rsr_nanb_samesrf :
  srf_s' ⨾ ⦗A_s'⦘ ≡ srf_s ⨾ ⦗A_s⦘.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  rewrite <- rsr_same_exa.
  arewrite (A_s ≡₁ E_s ∩₁ A_s).
  { rewrite set_inter_absorb_l; [reflexivity |].
    rewrite (rsr_acts SIMREL). auto with hahn. }
  rewrite id_inter.
  seq_rewrite rsr_nanb_samesrf_helper.
  now rewrite seqA.
Qed.

Lemma rsr_nanb_codelta :
  eq (mapper e) × (
    A_s' ∩₁ W_s ∩₁
    Loc_s_ (WCore.lab_loc l) ∩₁
    WCore.lab_is_w l
  ) ≡
    add_max
      (eq e ∩₁ WCore.lab_is_w l)
      (A_s' ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l)).
Proof using b_t a_t E_NOT_B E_NOT_A.
  clear - E_NOT_B E_NOT_A.
  rewrite rsr_mappero; auto.
  unfold add_max, WCore.lab_is_w.
  desf.
  all: rewrite ?set_inter_empty_r, ?set_minus_empty_l.
  all: try now rewrite cross_false_l, cross_false_r.
  rewrite !set_inter_full_r.
  rewrite set_minus_disjoint; [reflexivity|].
  unfold extra_a; desf; basic_solver.
Qed.

Lemma rsr_nanb_isr :
  A_s ∩₁ R_s' ≡₁ A_s ∩₁ R_s.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  unfold extra_a; desf; [| basic_solver].
  unfolder. split; intros x (XEQ & ISR); subst x.
  all: split; auto; unfold is_r in *.
  all: rewrite rsr_nanb_labeq in *; auto.
  all: apply (rsr_acts SIMREL); right.
  all: apply extra_a_some; desf.
Qed.

Lemma rsr_nanb_isw :
  A_s ∩₁ W_s' ≡₁ A_s ∩₁ W_s.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  unfold extra_a; desf; [| basic_solver].
  unfolder. split; intros x (XEQ & ISR); subst x.
  all: split; auto; unfold is_w in *.
  all: rewrite rsr_nanb_labeq in *; auto.
  all: apply (rsr_acts SIMREL); right.
  all: apply extra_a_some; desf.
Qed.

Lemma rsr_nanb_exa_pred :
  A_s' ⊆₁ extra_a_pred X_s' a_t b_t.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  unfold extra_a; desf. intros x XEQ. subst x.
  set (APR := rsr_a_preserved).
  set (BPR := rsr_b_preserved).
  assert (INB : E_t b_t) by tauto.
  assert (NINA : ~E_t a_t) by tauto.
  assert (EXAP : extra_a_pred X_s a_t b_t b_t).
  { now apply SIMREL, extra_a_some. }
  constructor.
  { reflexivity. }
  { rewrite <- (extra_a_some X_t' a_t b_t b_t) by desf.
    rewrite !id_inter. seq_rewrite rsr_nanb_samesrf.
    rewrite !seqA, <- id_inter, rsr_nanb_isr.
    rewrite wf_srfE, !seqA, seq_eqvC, extra_a_some; auto.
    sin_rewrite (eba_val EXAP).
    unfolder. intros. desf.
    unfold same_val, loc, val in *.
    now rewrite !rsr_nanb_labeq. }
  all: unfold same_loc, loc, is_rel, is_acq, mod,
              is_r, is_w.
  all: simpl; unfolder; rewrite !updo by auto.
  all: apply SIMREL, extra_a_some; auto.
Qed.

Lemma rsr_nanb_new_add_max :
  add_max
    (extra_co_D E_s' lab_s' (loc_s' b_t))
    (A_s' ∩₁ W_s') ≡
      add_max
        (extra_co_D E_s lab_s (loc_s b_t))
        (A_s ∩₁ W_s) ∪
      add_max (eq e ∩₁ WCore.lab_is_w l)
        (A_s' ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l)).
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  arewrite (loc_s' b_t = loc_s b_t).
  { simpl. unfold loc. rewrite updo; auto. }
  change E_s' with (E_s ∪₁ eq e).
  rewrite extra_co_D_union, add_max_union,
          <- rsr_same_exa, rsr_nanb_isw.
  apply union_more.
  { apply add_max_more; [| reflexivity].
    apply extra_co_D_eq_dom; auto with xmm. }
  unfold add_max.
  rewrite !set_minus_disjoint
      by (unfold extra_co_D, extra_a; desf; basic_solver).
  unfold extra_co_D.
  arewrite (eq e ∩₁ W_s' ≡₁ eq e ∩₁ WCore.lab_is_w l).
  { unfolder. split; ins; desf.
    all: unfold is_w in *; rewrite upds in *.
    all: unfold WCore.lab_is_w in *; desf. }
  assert (EQLOC : WCore.lab_loc l = loc_s' e).
  { simpl. unfold loc. rewrite upds. basic_solver. }
  unfold WCore.lab_is_w.
  destruct l as [lex lmod lloc lval | lxmod lmod lloc lval | lmod].
  all: rewrite ?set_inter_empty_r, ?set_inter_empty_l.
  all: try now rewrite !cross_false_l.
  all: rewrite set_inter_full_r.
  destruct classic
      with (~(~ E_t a_t /\ E_t b_t))
        as [EMP|NEMP].
  { rewrite extra_a_none; auto. basic_solver. }
  rewrite extra_a_some by tauto.
  remember (eq b_t ∩₁ W_s) as A_s_W.
  arewrite (
    eq e ∩₁ Loc_s_' (loc_s b_t) ≡₁
      eq e ∩₁ (fun x => loc_s b_t = loc_s' e)
  ).
  { unfolder. split; ins; splits; desf. }
  arewrite (
    A_s_W ∩₁ Loc_s_ (WCore.lab_loc (Astore lxmod lmod lloc lval)) ≡₁
      A_s_W ∩₁ (fun x => loc_s b_t = loc_s' e)
  ).
  { subst A_s_W. unfolder. split; ins; splits; desf.
    all: unfold loc in *; rewrite upds in *.
    all: desf. }
  basic_solver.
Qed.

Lemma rsr_nanb_sim :
  reord_simrel X_s' X_t' a_t b_t mapper.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  assert (ANINI : ~is_init a_t) by apply INV.
  assert (BNINI : ~is_init b_t) by apply INV.
  assert (WF_t : Wf G_t) by apply INV.
  assert (NEQ : a_t <> b_t) by apply (rsr_at_neq_bt INV).
  assert (TEQ : tid a_t = tid b_t) by apply (rsr_at_bt_tid INV).
  constructor.
  all: auto with xmm.
  { apply rsr_nanb_exa_pred. }
  { rewrite rsr_step_acts. simpl.
    rewrite <- rsr_same_exa.
    rewrite set_collect_union, set_minus_union_l.
    apply set_subset_union; [apply (rsr_codom SIMREL) |].
    rewrite set_collect_eq, rsr_mappero; auto.
    rewrite set_minus_disjoint; [reflexivity |].
    unfold extra_a; desf; basic_solver. }
  { eapply eq_dom_mori; eauto with xmm.
    red. auto with hahn. }
  { rewrite rsr_step_acts, set_collect_union.
    rewrite set_collect_eq, rsr_mappero; auto.
    simpl. rewrite (rsr_acts SIMREL), rsr_same_exa.
    clear. basic_solver 7. }
  { rewrite (WCore.add_event_sb ADD').
    rewrite swap_rel_unionE, seq_union_l, dom_union.
    rewrite minus_disjoint by basic_solver.
    arewrite_false (WCore.sb_delta e E_t ⨾ ⦗eq b_t⦘); [basic_solver |].
    rewrite dom_empty, set_union_empty_r, collect_rel_union.
    rewrite rsr_new_e_sb, rsr_nanb_map_sbdelta.
    rewrite (rsr_sb SIMREL), rsr_same_exa,
            rsr_a_preservedE, rsr_b_preservedE.
    clear. basic_solver 20. }
  { rewrite (WCore.add_event_rf ADD'), <- (rf_delta_RE WF_t ADD'),
            (add_event_to_rf_complete ADD' WF_t (rsr_Gt_rfc INV)).
    rewrite union_false_r, collect_rel_union.
    rewrite id_inter. seq_rewrite rsr_nanb_samesrf.
    rewrite seqA, <- id_inter, rsr_nanb_isr.
    simpl. rewrite (rsr_rf SIMREL). basic_solver 11. }
  { rewrite (WCore.add_event_co ADD'), <- (co_deltaE WF_t ADD'),
            rsr_nanb_new_add_max.
    simpl. rewrite (rsr_co SIMREL), !collect_rel_union.
    basic_solver 11. }
  all: ins.
  all: rewrite ?(WCore.add_event_threads ADD'), ?(WCore.add_event_ctrl ADD'),
               ?(WCore.add_event_threads ADD'), ?(WCore.add_event_addr ADD'),
               ?(WCore.add_event_addr ADD'), ?(WCore.add_event_rmw_dep ADD'),
               ?(WCore.add_event_data ADD'), ?rsr_b_preservedE, ?rsr_a_preservedE.
  all: try now apply SIMREL.
  rewrite rsr_step_acts, !set_minus_union_l.
  apply eq_dom_union. split.
  { intros x XIN. desf. rewrite rsr_mappero.
    all: forward apply XIN; clear; unfold id; basic_solver. }
  clear. unfolder; ins; desf. rewrite rsr_mappero; auto.
Qed.

Lemma rsr_new_Gs_wf :
  Wf G_s'.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  apply (G_s_wf INV' rsr_nanb_sim).
Qed.

Hint Resolve rsr_new_Gs_wf : xmm.

Lemma rsr_nanb_add_event :
  WCore.add_event X_s X_s' (mapper e) l.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  exists (option_map mapper r), (mapper ↑₁ R1),
          (option_map mapper w),
          ((A_s' ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l) ∩₁ WCore.lab_is_w l)
            ∪₁ mapper ↑₁ W1),
          (mapper ↑₁ W2).
  apply add_event_to_wf.
  { apply (rsr_init_acts_s INV SIMREL). }
  all: auto with xmm.
  all: try now (rewrite rsr_mappero; auto with xmm).
  { rewrite <- mapped_rf_delta_R, <- mapped_rf_delta_W,
            (add_event_to_rf_complete ADD').
    all: try now apply INV.
    simpl. rewrite (rf_delta_RE (rsr_Gt_wf INV) ADD').
    basic_solver 11. }
  { rewrite co_delta_union_W1, <- mapped_co_delta,
            rsr_nanb_codelta.
    simpl. rewrite (co_deltaE (rsr_Gt_wf INV) ADD').
    basic_solver 11. }
  { simpl. rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD'),
                   collect_rel_union.
    now rewrite (rsr_rmw SIMREL). }
  { rewrite rsr_new_e_sb, rsr_mappero; auto with xmm hahn. }
  rewrite (rsr_ctrl SIMREL), <- (WCore.add_event_ctrl ADD').
  apply ADD'.
Qed.

Lemma rsr_exec_nanb_step :
  WCore.exec_inst X_s X_s' (mapper e) l.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV' CONS.
  constructor.
  { apply rsr_nanb_add_event. }
  { eapply (G_s_rfc INV' rsr_nanb_sim). }
  eapply rsr_cons with (X_t := X_t').
  all: eauto using rsr_nanb_sim.
Qed.

End ExecNotANotB.