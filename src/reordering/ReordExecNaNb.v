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
Notation "'F_s'" := (F G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (Rlx G_s).
Notation "'Acq_s'" := (Acq G_s).
Notation "'Rel_s'" := (Rel G_s).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'mapper'" := (mapper a_t b_t).

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t b_t.

Lemma simrel_exec_not_a_not_b e l
    (E_NOT_A : e <> a_t)
    (E_NOT_B : e <> b_t)
    (B_NOT_F : ~ is_f lab_t b_t)
    (A_NOT_F : ~ is_f lab_t a_t)
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t b_t mapper >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper e) l >>.
Proof using INV INV'.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  assert (CORR : reord_step_pred X_t a_t b_t); ins.
  assert (CORR' : reord_step_pred X_t' a_t b_t); ins.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
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
  assert (WF : Wf G_t) by apply INV.
  assert (WF' : Wf G_t') by apply INV'.
  assert (LABSUB : eq_dom E_t lab_t' lab_t).
  { rewrite (WCore.add_event_lab ADD). clear - ENOTIN.
    unfold eq_dom. intros x XINE. rewrite updo.
    all: congruence. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> e).
  { intros x XINE FALSO. apply NOTIN, (rsr_codom SIMREL).
    red. exists x; split; [exact XINE | exact FALSO]. }
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
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).
  assert (SAMETID : same_tid e ≡₁ same_tid e).
  { unfold same_tid. reflexivity. }
  assert (AS_TID : extra_a X_t a_t b_t b_t ⊆₁ same_tid b_t).
  { rewrite (rsr_as SIMREL). unfolder. intros x XIN. apply XIN. }
  assert (NOTIN' : ~ E_s (mapper e)).
  { rewrite rsr_mappero; auto. }
  assert (ENEXA : ~ extra_a X_t' a_t b_t b_t e).
  { clear - EXEQ NOTIN EXIN.
    intro FALSO. now apply EXEQ, EXIN in FALSO. }
  assert (ASTID : forall (AS : ~ E_t a_t /\ E_t b_t), same_tid b_t b_t).
  { intros. eapply eba_tid, (rsr_as SIMREL). now apply extra_a_some. }
  assert (SRF' : srf G_s' ⨾ ⦗E_s⦘ ≡ srf G_s ⨾ ⦗E_s⦘).
  { apply (porf_pref_srf G_s G_s'); simpl.
    { eapply G_s_wf with (X_t := X_t); eauto. }
    { clear. auto with hahn. }
    { exact LABEQ. }
    { unfold sb at 1. simpl. rewrite NEWSB.
      clear - NOTIN. rewrite seq_union_l. basic_solver. }
    { clear - NOTIN'. basic_solver. }
    { clear - NOTIN NOTIN'. basic_solver 7. }
    rewrite (WCore.add_event_rmw ADD), (rsr_rmw SIMREL).
    rewrite collect_rel_union.
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
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper).
  { constructor; simpl.
    { eapply inj_dom_mori; eauto with xmm.
      red. auto with hahn. }
    { rewrite <- EXEQ. unfolder.
      intros x XIN. ins. constructor.
      { now apply (rsr_as SIMREL). }
      { change (WCore.G X_s') with G_s'.
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
      (* TODO: finish *)
      all : admit. }
    { rewrite (WCore.add_event_acts ADD).
      rewrite set_collect_union, set_collect_eq, set_minus_union_l.
      rewrite (rsr_codom SIMREL), EXEQ, rsr_mappero; auto.
      clear - ENEXA. basic_solver. }
    { apply (rsr_init SIMREL). }
    { eapply eq_dom_mori; eauto with xmm.
      red. auto with hahn. }
    { rewrite EQACTS, (WCore.add_event_lab ADD).
      apply eq_dom_union; split.
      { unfolder. intros x XIN.
        unfold compose. rupd; try congruence; eauto.
        now rewrite <- (rsr_lab SIMREL) by basic_solver. }
      unfolder. ins. desf. unfold compose.
      rewrite rsr_mappero, !upds; auto. }
    { rewrite EQACTS, set_collect_union.
      rewrite set_collect_eq, rsr_mappero; auto.
      rewrite (rsr_acts SIMREL), EXEQ.
      clear. basic_solver 7. }
    { unfold sb at 1. ins. rewrite NEWSB, <- EXEQ.
      rewrite (rsr_sb SIMREL).
      arewrite (sb_t' ⨾ ⦗eq b_t⦘ ≡ sb_t ⨾ ⦗eq b_t⦘).
      { rewrite (WCore.add_event_sb ADD), seq_union_l.
        clear - E_NOT_B. basic_solver. }
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
      rewrite set_collect_union, <- (fixset_set_fixpoint (rsr_init SIMREL)),
              (rsr_same_tid  _ SIMREL), TIDACTS.
      rewrite rsr_mapper_bt, rsr_mappero; auto.
      clear. basic_solver 20. }
    { arewrite (extra_a X_t' a_t b_t b_t ∩₁ is_r (upd lab_s e l) ≡₁
                extra_a X_t a_t b_t b_t ∩₁ R_s).
      { rewrite <- EXEQ. apply same_lab_u2v_dom_is_r.
        eapply same_lab_u2v_dom_inclusion with (s := E_s); eauto. }
      rewrite SRF'', (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      rewrite (rsr_rf SIMREL), (WCore.add_event_rf ADD),
              !collect_rel_union.
      rewrite (add_event_to_rf_complete ADD); try now apply CORR.
      rewrite collect_rel_empty, union_false_r.
      clear. basic_solver 12. }
    { rewrite (co_deltaE1 (rsr_Gt_wf CORR) ADD),
            (co_deltaE2 (rsr_Gt_wf CORR) ADD).
      rewrite (WCore.add_event_co ADD), !collect_rel_union,
              (rsr_co SIMREL).
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
      assert (INBS : mapper ↑₁ (eq b_t ∩₁ E_t) ⊆₁ E_s).
      { transitivity (mapper ↑₁ E_t); [basic_solver |].
        rewrite (rsr_codom SIMREL). clear. basic_solver. }
      arewrite (rpo G_s' ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⊆
                rpo G_s' ⨾ ⦗E_s⦘ ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘).
      { rewrite <- id_inter, set_inter_absorb_l with (s' := E_s).
        all: ins. }
      arewrite (rpo G_s' ⨾ ⦗E_s⦘ ≡ rpo_s ⨾ ⦗E_s⦘).
      { apply (porf_pref_rpo G_s G_s'); simpl.
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
      { intros x XIN. desf. rewrite rsr_mappero.
        all: forward apply XIN; clear; unfold id; basic_solver. }
      clear. unfolder; ins; desf. rewrite rsr_mappero; auto. }
    { arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t).
      { clear - B_PRESERVED. basic_solver. }
      unfolder; ins; desf; symmetry; eauto with xmm. }
    arewrite (eq a_t ∩₁ E_t' ≡₁ eq a_t ∩₁ E_t).
    { clear - A_PRESERVED. basic_solver. }
    unfolder; ins; desf; symmetry; eauto with xmm. }
  (* Actual proof *)
  exists X_s'.
  split; red; [exact SIMREL' |].
  constructor.
  { exists (option_map mapper r), (mapper ↑₁ R1),
           (option_map mapper w),
           ((extra_a X_t' a_t b_t b_t ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l) ∩₁ WCore.lab_is_w l)
            ∪₁ mapper ↑₁ W1),
           (mapper ↑₁ W2).
    apply add_event_to_wf; simpl.
    { eapply sico_init_acts_s; [| apply CORR].
      eapply rsr_common; eauto. }
    { rewrite rsr_mappero; auto. }
    { rewrite rsr_mappero; auto. }
    { rewrite rsr_mappero; auto. }
    { rewrite rsr_mappero; auto with hahn. }
    { reflexivity. }
    { rewrite rsr_mappero; auto. }
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
      rewrite rsr_mappero, add_max_disjoint; auto.
      all: clear - NEMP ENEXA.
      all: unfold WCore.lab_is_w in *; desf; basic_solver. }
    { rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD),
              collect_rel_union.
      now rewrite (rsr_rmw SIMREL). }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { unfold sb at 1. simpl.
      rewrite NEWSB, rsr_mappero; auto. }
    { rewrite (rsr_ctrl SIMREL), <- (WCore.add_event_ctrl ADD).
      apply ADD. }
    eapply G_s_wf with (X_s := X_s') (X_t := X_t'); eauto. }
  { eapply G_s_rfc; eauto. }
  destruct (classic (~ E_t' a_t /\ E_t' b_t)) as [EMP|NEMP].
  { assert (ANONTIN : ~ E_t a_t).
    { clear - A_PRESERVED EMP. tauto. }
    assert (BIN : E_t b_t).
    { clear - B_PRESERVED EMP. tauto. }
    assert (SBFROMA : ⦗eq b_t⦘ ⨾ sb G_s' ⊆ eq b_t × eq a_t).
    { apply (rsr_sb_froma INV' SIMREL').
      all: clear - EMP; desf. }
    assert (AINS : (acts_set G_s') a_t).
    { apply (rsr_acts SIMREL'). left.
      exists b_t. split; [apply EMP|].
      apply (rsr_map_bt (proj2 EMP) SIMREL'). }
    assert (BINS : (acts_set G_s') b_t).
    { apply (rsr_acts SIMREL'). right.
      apply extra_a_some; desf. }
    assert (AINRW : eq a_t ⊆₁ R G_s' ∪₁ W G_s').
    { change G_s' with (WCore.G X_s').
      rewrite <- (simrel_a_lab_wr INV' SIMREL').
      clear - AINS. basic_solver. }
    assert (BINRW : eq b_t ⊆₁ R G_s' ∪₁ W G_s').
    { change G_s' with (WCore.G X_s').
      rewrite <- (simrel_b_lab_wr INV' SIMREL').
      clear - BINS. basic_solver. }
    assert (AINNREL : eq a_t ⊆₁ set_compl (Rel G_s')).
    { change G_s' with (WCore.G X_s').
      rewrite <- (rsr_bs_nrel INV' SIMREL').
      clear - AINS. basic_solver. }
    assert (BINACQ : eq b_t ⊆₁ set_compl (Acq G_s')).
    { change G_s' with (WCore.G X_s').
      rewrite <- (rsr_as_nacq INV' SIMREL').
      clear - BINS. basic_solver. }
    assert (SLOC : ~ same_loc (lab (WCore.G X_s')) b_t a_t).
    { intro FALSO.
      enough (SL : same_loc (lab (WCore.G X_s')) a_t b_t).
      { apply (rsr_as_bs_loc INV' SIMREL') with a_t b_t.
        clear - AINS BINS SL. basic_solver. }
      clear - FALSO. now unfold same_loc in *. }
    assert (SUB : acts_set (WCore.G X_s') \₁ eq b_t ⊆₁ mapper ↑₁ E_t').
    { rewrite (rsr_acts SIMREL').
      rewrite extra_a_some; desf.
      clear. basic_solver. }
    assert (MAPE : e = mapper e).
    { now rewrite rsr_mappero. }
    destruct (BINRW b_t) as [RR | WW]; vauto.
    { apply XmmCons.read_extent with (G_t := G_t')
        (a := b_t) (m := mapper); eauto.
      { apply SIMREL'. }
      { rewrite (rsr_acts SIMREL').
        rewrite extra_a_some; auto with hahn.
        all: tauto. }
      { apply SIMREL'; vauto. }
      { eapply rsr_as_nacq with (X_t := X_t') (X_s := X_s'); eauto.
        clear - BINS. basic_solver. }
      { apply set_disjointE. split; auto with hahn.
        rewrite (rsr_codom SIMREL'), extra_a_some.
        { basic_solver. }
        all: tauto. }
      { split; auto with hahn.
        rewrite reord_rpo_emp; eauto.
        clear. basic_solver. }
      { apply reord_map_rpo with (a := a_t); auto.
        { apply (G_s_wf CORR' SIMREL'). }
        { symmetry. apply (rsr_lab SIMREL'). }
        { apply (rsr_inj SIMREL'). }
        eapply rsr_sb_nexa with (a := a_t).
        { rewrite (rsr_sb SIMREL'), extra_a_some,
                  rsr_map_bt with (X_s := X_s') (X_t := X_t') (a_t := a_t).
          all: auto; tauto. }
        all: tauto. }
      { apply reord_ab_loc_codom with (a := a_t).
        all: auto. }
      { apply reord_sbloc_to_nb with (a := a_t).
        all: auto.
        { apply (rsr_inj SIMREL'). }
        { symmetry. apply (rsr_lab SIMREL'). }
        eapply rsr_sb_nexa with (a := a_t).
        { rewrite (rsr_sb SIMREL'), extra_a_some,
                  rsr_map_bt with (X_s := X_s') (X_t := X_t') (a_t := a_t).
          all: auto; tauto. }
        all: tauto. }
      { rewrite (rsr_rf SIMREL').
        rewrite extra_a_some by tauto.
        clear - RR. basic_solver 11. }
      { rewrite (rsr_co SIMREL').
        rewrite extra_a_some by tauto.
        arewrite (eq b_t ∩₁ W (WCore.G X_s') ≡₁ ∅).
        { split; auto with hahn.
          clear - RR. unfold is_r, is_w in *.
          unfolder. ins. desf. }
        now rewrite add_max_empty_r, union_false_r. }
      apply G_s_wf with (X_t := X_t') (a_t := a_t)
                (b_t := b_t) (mapper := mapper); vauto. }
    apply XmmCons.write_extent with (G_t := G_t')
      (a := b_t) (m := mapper); eauto.
    { apply SIMREL'. }
    { rewrite (rsr_acts SIMREL').
      rewrite extra_a_some; auto with hahn.
      all: tauto. }
    { apply (rsr_lab SIMREL'). }
    { apply set_disjointE. split; auto with hahn.
      rewrite (rsr_codom SIMREL'), extra_a_some.
      { basic_solver. }
      all: tauto. }
    { split; auto with hahn.
      rewrite reord_rpo_emp; eauto.
      clear. basic_solver. }
    { apply reord_map_rpo with (a := a_t); auto.
      { apply (G_s_wf CORR' SIMREL'). }
      { symmetry. apply (rsr_lab SIMREL'). }
      { apply (rsr_inj SIMREL'). }
      eapply rsr_sb_nexa with (a := a_t).
      { rewrite (rsr_sb SIMREL'), extra_a_some,
                rsr_map_bt with (X_s := X_s') (X_t := X_t') (a_t := a_t).
        all: auto; tauto. }
      all: tauto. }
    { apply reord_ab_loc_codom with (a := a_t).
      all: auto. }
    { apply reord_sbloc_to_nb with (a := a_t).
      all: auto.
      { apply (rsr_inj SIMREL'). }
      { symmetry. apply (rsr_lab SIMREL'). }
      eapply rsr_sb_nexa with (a := a_t).
      { rewrite (rsr_sb SIMREL'), extra_a_some,
                rsr_map_bt with (X_s := X_s') (X_t := X_t') (a_t := a_t).
        all: auto; tauto. }
      all: tauto. }
    { rewrite (rsr_rf SIMREL').
      rewrite extra_a_some by tauto.
      arewrite (eq b_t ∩₁ R (WCore.G X_s') ≡₁ ∅).
      { split; auto with hahn.
        clear - WW. unfold is_r, is_w in *.
        unfolder. ins. desf. }
      now rewrite eqv_empty, seq_false_r, union_false_r. }
    { rewrite (rsr_co SIMREL').
      rewrite extra_a_some by tauto.
      apply union_more; vauto.
      arewrite (eq b_t ∩₁ W (WCore.G X_s') ≡₁ eq b_t).
      { clear - WW; basic_solver. }
      unfold extra_co_D.
      arewrite ((fun x =>
          loc (lab (WCore.G X_s')) x = loc (lab (WCore.G X_s')) b_t
        ) ≡₁ same_loc (lab (WCore.G X_s')) b_t
      ).
      all: clear; basic_solver 11. }
  apply G_s_wf with (X_t := X_t') (a_t := a_t)
            (b_t := b_t) (mapper := mapper); vauto. }
  assert (EXTRA : extra_a X_t' a_t b_t b_t ≡₁ ∅).
  { unfold extra_a. desf. }
  assert (RPOMAP : rpo G_s' ⊆ mapper ↑ (rpo G_t')).
  { apply reord_rpo_map' with (a := a_t) (b := b_t).
    all: rewrite 1?set_unionC with (s := R_t').
    all: try now apply INV'.
    all: try change G_s' with (WCore.G X_s').
    { eapply G_s_wf; eauto. }
    { now rewrite (rsr_acts SIMREL'), EXTRA, set_union_empty_r. }
    { symmetry. apply SIMREL'. }
    { apply SIMREL'. }
    rewrite (rsr_sb SIMREL'), EXTRA,
            cross_false_l, cross_false_r.
    now rewrite !union_false_r. }
  assert (SLOCMAP : sb G_s' ∩ same_loc (lab G_s') ⊆ mapper ↑ (sb_t' ∩ same_loc_t')).
  { apply reord_sbloc' with (a := a_t) (b := b_t).
    all: rewrite 1?set_unionC with (s := R_t').
    all: try now apply INV'.
    all: try change G_s' with (WCore.G X_s').
    { now rewrite (rsr_acts SIMREL'), EXTRA, set_union_empty_r. }
    { symmetry. apply SIMREL'. }
    rewrite (rsr_sb SIMREL'), EXTRA,
            cross_false_l, cross_false_r.
    now rewrite !union_false_r. }
  apply XmmCons.monoton_cons with (G_t := G_t')
              (m := mapper); eauto.
  all: try now apply SIMREL'.
  { now rewrite (rsr_acts SIMREL'), EXTRA, set_union_empty_r. }
  { rewrite (rsr_rf SIMREL'), EXTRA. basic_solver 8. }
  { rewrite (rsr_co SIMREL'), EXTRA.
    now rewrite set_inter_empty_l, add_max_empty_r, union_false_r. }
  eapply G_s_wf with (X_t := X_t'); eauto.
Admitted.

End ExecNotANotB.