Require Import ReordSimrel ReorderingEq ReorderingMapper.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import PorfPrefix.
Require Import ConsistencyCommon.
Require Import ConsistencyMonotonicity.
Require Import ConsistencyReadExtent.
Require Import ConsistencyWriteExtent.
Require Import ReorderingRpo.

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

Definition rsr_na_nb_Gs_prime := {|
  acts_set := E_s ∪₁ eq e;
  threads_set := threads_set G_s;
  lab := upd lab_s e l;
  rf := rf_s ∪ mapper ↑ (rf_t' ⨾ ⦗eq e⦘);
  co := co_s ∪
        mapper ↑ (⦗eq e⦘ ⨾ co_t') ∪
        mapper ↑ (co_t' ⨾ ⦗eq e⦘) ∪
        add_max (eq e ∩₁ WCore.lab_is_w l)
          (extra_a X_t' a_t b_t b_t ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l));
  rmw := mapper ↑ rmw_t';
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.

Definition rsr_na_nb_Xs_prime := {|
  WCore.G := rsr_na_nb_Gs_prime;
  WCore.sc := WCore.sc X_s;
|}.

Notation "'X_s''" := rsr_na_nb_Xs_prime.
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

Notation "'A_s'" := (extra_a X_t a_t b_t b_t).
Notation "'B_s'" := (extra_a X_t a_t b_t a_t).
Notation "'A_s''" := (extra_a X_t' a_t b_t b_t).

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
  split.
  { unfolder. intros x y (EQ1 & SB & EQ2). subst x y.
    splits; auto. now apply rsr_ext_sb_from_at. }
  unfolder. intros x y ((EQ1 & TID) & EQ2). subst x y.
  exfalso. apply rsr_Et_restr; [| desf].
  rewrite <- (rsr_at_bt_tid INV). apply TID.
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
    rewrite <- (rsr_at_bt_tid INV).
    now apply rsr_ext_sb_to_at. }
  now rewrite !union_false_r, rsr_new_e_sb_delta.
Qed.

Lemma rsr_na_nb_notin : ~ E_s e.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  intro EIN. apply (rsr_actsE INV SIMREL) in EIN.
  destruct EIN as [EINT | INB].
  { now apply rsr_e_notin. }
  unfold extra_a in INB; desf.
Qed.

Lemma rsr_na_nb_notin' : ~ E_s (mapper e).
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  rewrite rsr_mappero; auto.
  apply rsr_na_nb_notin.
Qed.

Lemma rsr_na_nb_labeq : eq_dom E_s lab_s' lab_s.
Proof using.
Admitted.

Lemma rsr_na_nb_samesrf_helper :
  srf G_s' ⨾ ⦗E_s⦘ ≡ srf G_s ⨾ ⦗E_s⦘.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  set (NOTIN := rsr_na_nb_notin).
  set (NOTIN' := rsr_na_nb_notin').
  apply (porf_pref_srf G_s G_s').
  { eapply G_s_wf with (X_t := X_t); eauto. }
  { ins. auto with hahn. }
  { apply rsr_na_nb_labeq. }
  { rewrite rsr_new_e_sb.
    clear - NOTIN. rewrite seq_union_l. basic_solver. }
  { simpl. clear - NOTIN'. basic_solver. }
  { simpl. clear - NOTIN NOTIN'. basic_solver 7. }
  simpl. destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  rewrite (WCore.add_event_rmw ADD'), (rsr_rmw SIMREL).
  rewrite collect_rel_union.
  clear - NOTIN' NOTIN. basic_solver 7.
Qed.

Lemma rsr_na_nb_samesrf :
  srf G_s' ⨾ ⦗A_s'⦘ ≡ srf G_s ⨾ ⦗A_s⦘.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  rewrite <- rsr_same_exa.
  arewrite (A_s ≡₁ E_s ∩₁ A_s).
  { rewrite set_inter_absorb_l; [reflexivity |].
    rewrite (rsr_acts SIMREL). auto with hahn. }
  rewrite id_inter.
  seq_rewrite rsr_na_nb_samesrf_helper.
  now rewrite seqA.
Qed.

Lemma rsr_exec_na_nb_simrel :
  reord_simrel X_s' X_t' a_t b_t mapper.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  assert (WF_t : Wf G_t) by apply INV.
  assert (NEQ : a_t <> b_t) by apply (rsr_at_neq_bt INV).
  assert (TEQ : tid a_t = tid b_t) by apply (rsr_at_bt_tid INV).
  constructor.
  { eapply inj_dom_mori; eauto with xmm.
    red. auto with hahn. }
  { admit. }
  { rewrite rsr_step_acts. simpl.
    rewrite <- rsr_same_exa.
    rewrite set_collect_union, set_minus_union_l.
    apply set_subset_union; [apply (rsr_codom SIMREL) |].
    rewrite set_collect_eq, rsr_mappero; auto.
    rewrite set_minus_disjoint; [reflexivity |].
    unfold extra_a; desf; basic_solver. }
  { apply (rsr_init SIMREL). }
  { eapply eq_dom_mori; eauto with xmm.
    red. auto with hahn. }
  { admit. }
  { rewrite rsr_step_acts, set_collect_union.
    rewrite set_collect_eq, rsr_mappero; auto.
    simpl. rewrite (rsr_acts SIMREL), rsr_same_exa.
    clear. basic_solver 7. }
  { admit. }
  { rewrite (WCore.add_event_rf ADD'), <- (rf_delta_RE WF_t ADD'),
            (add_event_to_rf_complete ADD' WF_t (rsr_Gt_rfc INV)).
    rewrite union_false_r, collect_rel_union.
    rewrite id_inter. seq_rewrite rsr_na_nb_samesrf.
    rewrite seqA, <- id_inter.
    admit. }
  { rewrite (WCore.add_event_co ADD'). unfold WCore.co_delta.
    rewrite <- (co_deltaE1 WF_t ADD'), <- (co_deltaE2 WF_t ADD').
    admit. }
  { ins. }
  { ins. rewrite (WCore.add_event_threads ADD'). apply SIMREL. }
  { ins. rewrite (WCore.add_event_ctrl ADD'). apply SIMREL. }
  { ins. rewrite (WCore.add_event_data ADD'). apply SIMREL. }
  { ins. rewrite (WCore.add_event_addr ADD'). apply SIMREL. }
  { ins. rewrite (WCore.add_event_rmw_dep ADD'). apply SIMREL. }
  { rewrite rsr_step_acts, !set_minus_union_l.
    apply eq_dom_union. split.
    { intros x XIN. desf. rewrite rsr_mappero.
      all: forward apply XIN; clear; unfold id; basic_solver. }
    clear. unfolder; ins; desf. rewrite rsr_mappero; auto. }
  { rewrite rsr_b_preservedE. apply SIMREL. }
  rewrite rsr_a_preservedE. apply SIMREL.
Admitted.

Lemma rsr_new_Gs_wf :
  Wf G_s'.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  apply (G_s_wf INV' rsr_exec_na_nb_simrel).
Qed.

Lemma rsr_exec_nb_nb_cons_exa_helper
    (BIN : E_t' b_t)
    (ANOTIN : ~E_t' a_t)
    (SMEXA : A_s' ≡₁ eq b_t) :
  WCore.is_cons G_s'.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply (rsr_at_neq_bt INV).
  assert (SBFROMA : ⦗eq b_t⦘ ⨾ sb G_s' ⊆ eq b_t × eq a_t).
  { now apply (rsr_sb_froma INV' rsr_exec_na_nb_simrel). }
  assert (AINS : (acts_set G_s') a_t).
  { (* apply (rsr_acts SIMREL'). left.
    exists b_t. split; [apply EMP|].
    apply (rsr_map_bt (proj2 EMP) SIMREL'). *)
    admit. }
  assert (BINS : (acts_set G_s') b_t).
  {(* apply (rsr_acts SIMREL'). right.
    apply extra_a_some; desf. *)
    admit. }
  assert (AINRW : eq a_t ⊆₁ R_s' ∪₁ W_s').
  { (*change G_s' with (WCore.G X_s').
    rewrite <- (simrel_a_lab_wr INV' SIMREL').
    clear - AINS. basic_solver.*) admit. }
  assert (BINRW : eq b_t ⊆₁ R_s' ∪₁ W_s').
  { (*change G_s' with (WCore.G X_s').
    rewrite <- (simrel_b_lab_wr INV' SIMREL').
    clear - BINS. basic_solver.*) admit. }
  assert (AINNREL : eq a_t ⊆₁ set_compl Rel_s').
  { (* transitivity (set_compl (Rel G_s' ∪₁ Acq G_s'))
      ; [| basic_solver].
    change G_s' with (WCore.G X_s').
    rewrite <- (rsr_bs_rlx INV' SIMREL').
    clear - AINS. basic_solver. *) admit. }
  assert (BINACQ : eq b_t ⊆₁ set_compl Acq_s').
  { (* transitivity (set_compl (Rel G_s' ∪₁ Acq G_s'))
      ; [| basic_solver].
    change G_s' with (WCore.G X_s').
    rewrite <- (rsr_as_rlx INV' SIMREL').
    clear - BINS. basic_solver. *) admit. }
  assert (SLOC : ~ same_loc (lab (WCore.G X_s')) b_t a_t).
  { intro FALSO.
    enough (SL : same_loc (lab (WCore.G X_s')) a_t b_t).
    { apply (rsr_as_bs_loc INV' rsr_exec_na_nb_simrel) with a_t b_t.
      clear - AINS BINS SL. basic_solver. }
    clear - FALSO. now unfold same_loc in *. }
  assert (RPOCOD : codom_rel (⦗eq b_t⦘ ⨾ rpo_s') ≡₁ ∅).
  { split; auto with hahn.
    rewrite reord_rpo_emp; eauto.
    clear. basic_solver. }
  assert (RPOMAP : rpo_s' ⨾ ⦗E_s' \₁ eq b_t⦘ ⊆ mapper ↑ rpo_t').
  { apply reord_map_rpo with (a := a_t); auto.
    { apply (G_s_wf INV' rsr_exec_na_nb_simrel). }
    { admit. }
    { admit. }
    { apply rsr_exec_na_nb_simrel. }
    eapply rsr_sb_nexa with (a := a_t).
    { now rewrite (rsr_sb rsr_exec_na_nb_simrel), SMEXA,
                  rsr_mapper_bt. }
    all: auto. }
  assert (SLOCD : codom_rel (⦗eq b_t⦘ ⨾ sb_s' ∩ same_loc_s') ≡₁ ∅).
  { apply reord_ab_loc_codom with (a := a_t).
    all: auto. }
  assert (SBLOCMAP : sb_s' ∩ same_loc_s' ⨾ ⦗E_s' \₁ eq b_t⦘ ⊆ mapper ↑ (sb_t' ∩ same_loc_t')).
  { apply reord_sbloc_to_nb with (a := a_t).
    all: auto.
    { apply (rsr_inj rsr_exec_na_nb_simrel). }
    { admit. }
    { symmetry. apply (rsr_lab rsr_exec_na_nb_simrel). }
    eapply rsr_sb_nexa with (a := a_t).
    { now rewrite (rsr_sb rsr_exec_na_nb_simrel), SMEXA,
                  rsr_mapper_bt. }
    all: auto. }
  destruct (simrel_b_lab_wr INV' rsr_exec_na_nb_simrel)
      with b_t
        as [ISR | ISW].
  { apply set_subset_single_l. rewrite (rsr_acts rsr_exec_na_nb_simrel).
    rewrite SMEXA. basic_solver. }
  { apply XmmCons.read_extent with (G_t := G_t')
        (a := b_t) (m := mapper); eauto.
    { apply rsr_exec_na_nb_simrel. }
    { now rewrite (rsr_acts rsr_exec_na_nb_simrel), SMEXA. }
    { apply rsr_exec_na_nb_simrel. }
    { admit. }
    { admit. }
    { rewrite (rsr_rf rsr_exec_na_nb_simrel), SMEXA.
      arewrite (eq b_t ∩₁ R_s' ≡₁ eq b_t); basic_solver. }
    { rewrite (rsr_co rsr_exec_na_nb_simrel), SMEXA.
      arewrite (eq b_t ∩₁ W_s' ≡₁ ∅).
      { split; auto with hahn.
        clear - ISR. unfold is_r, is_w in *.
        unfolder. ins. desf. }
      now rewrite add_max_empty_r, union_false_r. }
    { admit. }
    apply rsr_new_Gs_wf. }
  apply XmmCons.write_extent with (G_t := G_t')
      (a := b_t) (m := mapper); eauto.
  { apply rsr_exec_na_nb_simrel. }
  { now rewrite (rsr_acts rsr_exec_na_nb_simrel), SMEXA. }
  { apply rsr_exec_na_nb_simrel. }
  { admit. }
  { rewrite (rsr_rf rsr_exec_na_nb_simrel), SMEXA.
    arewrite (eq b_t ∩₁ R_s' ≡₁ ∅).
    { split; auto with hahn.
      clear - ISW. unfold is_r, is_w in *.
      unfolder. ins. desf. }
      now rewrite eqv_empty, seq_false_r, union_false_r. }
  { rewrite (rsr_co rsr_exec_na_nb_simrel), SMEXA.
    arewrite (eq b_t ∩₁ W_s' ≡₁ eq b_t) by basic_solver.
    admit. }
  { apply (rsr_Gt_wf INV'). }
  apply rsr_new_Gs_wf.
Admitted.

Lemma rsr_exec_na_nb_cons :
  WCore.is_cons G_s'.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  destruct (classic (~ E_t' a_t /\ E_t' b_t)) as [EMP|NEMP].
  { apply rsr_exec_nb_nb_cons_exa_helper; desf.
    rewrite extra_a_some; auto. }
  assert (NEXA: A_s' ≡₁ ∅) by admit.
  assert (RPOMAP : rpo_s' ⊆ mapper ↑ (rpo G_t')).
  { apply reord_rpo_map' with (a := a_t) (b := b_t).
    all: rewrite 1?set_unionC with (s := R_t').
    all: try now apply INV'.
    { apply rsr_new_Gs_wf. }
    { admit. }
    { symmetry. apply rsr_exec_na_nb_simrel. }
    { apply rsr_exec_na_nb_simrel. }
    { rewrite (rsr_sb rsr_exec_na_nb_simrel), NEXA,
            cross_false_l, cross_false_r.
      now rewrite !union_false_r. }
    { rewrite (rsr_at_rlx INV'). clear. basic_solver. }
    rewrite (rsr_bt_rlx INV'). clear. basic_solver. }
  assert (SLOCMAP : sb G_s' ∩ same_loc (lab G_s') ⊆ mapper ↑ (sb_t' ∩ same_loc_t')).
  { apply reord_sbloc' with (a := a_t) (b := b_t).
    all: rewrite 1?set_unionC with (s := R_t').
    all: try now apply INV'.
    { now rewrite (rsr_acts rsr_exec_na_nb_simrel), NEXA, set_union_empty_r. }
    { symmetry. apply rsr_exec_na_nb_simrel. }
    rewrite (rsr_sb rsr_exec_na_nb_simrel), NEXA,
            cross_false_l, cross_false_r.
    now rewrite !union_false_r. }
  apply XmmCons.monoton_cons with (G_t := G_t')
              (m := mapper); eauto.
  all: try now apply rsr_exec_na_nb_simrel.
  { now rewrite (rsr_acts rsr_exec_na_nb_simrel), NEXA, set_union_empty_r. }
  { rewrite (rsr_rf rsr_exec_na_nb_simrel), NEXA. basic_solver 8. }
  { rewrite (rsr_co rsr_exec_na_nb_simrel), NEXA.
    now rewrite set_inter_empty_l, add_max_empty_r, union_false_r. }
  { apply (rsr_Gt_wf INV'). }
  apply rsr_new_Gs_wf.
Admitted.

Lemma rsr_na_nb_add_event :
  WCore.add_event X_s X_s' (mapper e) l.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  exists (option_map mapper r), (mapper ↑₁ R1),
          (option_map mapper w),
          ((extra_a X_t' a_t b_t b_t ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l) ∩₁ WCore.lab_is_w l)
          ∪₁ mapper ↑₁ W1),
          (mapper ↑₁ W2).
  apply add_event_to_wf.
  { admit. }
  { rewrite rsr_mappero; auto. admit. }
  { rewrite rsr_mappero; auto. admit. }
  { rewrite rsr_mappero; auto. admit. }
  { rewrite rsr_mappero; auto with hahn. }
  { reflexivity. }
  { rewrite rsr_mappero; auto. }
  { rewrite <- mapped_rf_delta_R,
            <- mapped_rf_delta_W.
    simpl.
    rewrite (rf_delta_RE (rsr_Gt_wf INV) ADD'),
            (add_event_to_rf_complete ADD').
    all: try now apply INV.
    rewrite collect_rel_empty, union_false_r.
    reflexivity. }
  { admit. }
  { simpl.
    rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD'),
            collect_rel_union.
    now rewrite (rsr_rmw SIMREL). }
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { admit. }
  { rewrite (rsr_ctrl SIMREL), <- (WCore.add_event_ctrl ADD').
    apply ADD'. }
  apply (G_s_wf INV' rsr_exec_na_nb_simrel).
Admitted.

Lemma rsr_exec_na_nb_step :
  WCore.exec_inst X_s X_s' (mapper e) l.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  constructor.
  { apply rsr_na_nb_add_event. }
  { eapply (G_s_rfc INV' rsr_exec_na_nb_simrel). }
  apply rsr_exec_na_nb_cons.
Qed.

End ExecNotANotB.