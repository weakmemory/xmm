Require Import ReordSimrel.
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

Require Import SubToFullExec.
Require Import xmm_s_hb.
Require Import Thrdle.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Section ExecNotANotB.

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

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t' b_t'.

Lemma simrel_exec_not_a_not_b e l
    (EQA : a_t = a_t')
    (EQB : b_t = b_t')
    (E_NOT_A : e <> a_t)
    (E_NOT_B : e <> b_t)
    (B_NOT_F : ~ is_f lab_t b_t)
    (A_NOT_F : ~ is_f lab_t a_t)
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
  { apply (porf_pref_srf G_s G_s'); simpl.
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
      (* TODO *)
      all : admit. } 
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
  destruct (classic (~ E_t' a_t /\ E_t' b_t)) as [EMP|NEMP].
  { assert (EXTRA : extra_a X_t' a_t b_t b_t ≡₁ eq b_t).
    { unfold extra_a. desf. basic_solver. }
    assert (ANONTIN : ~ E_t a_t).
    { clear - A_PRESERVED EMP. basic_solver 8. }
    assert (BIN : E_t b_t).
    { clear - B_PRESERVED EMP. basic_solver 8. }
    assert (EXTRAOLD : extra_a X_t a_t b_t b_t ≡₁ eq b_t).
    { unfold extra_a. desf. basic_solver. }
    assert (SBFROMA : ⦗eq b_t⦘ ⨾ sb G_s' ⊆ eq b_t × eq a_t).
    { unfold G_s', sb; ins.
      rewrite NEWSB.
      rewrite !seq_union_r.
      assert (SBHELP : ⦗eq b_t⦘ ⨾ sb_s ⊆ eq b_t × eq a_t).
      { transitivity (⦗eq b_t⦘ ⨾ sb_s ⨾ ⦗E_s \₁ eq b_t⦘).
        { unfold set_minus. unfolder. intros x y.
          ins. desf. splits; auto.
          { apply wf_sbE in H0. destruct H0 as
                [x0 [H0 [x1 [H1 [EQ INE]]]]]; vauto. }
          intros FALSE. subst y. apply sb_irr in H0; vauto. }
        rewrite (rsr_sb SIMREL).
        unfold swap_rel.
        arewrite (eq a_t ∩₁ E_t ≡₁ ∅).
        { split; [basic_solver|].
          clear. basic_solver. }
        rels. rewrite EXTRAOLD.
        rewrite !seq_union_l, !seq_union_r.
        apply inclusion_union_l.
        { apply inclusion_union_l.
          { destruct SIMREL. rewrite wf_sbE.
            rewrite collect_rel_seqi.
            rewrite seqA. rewrite collect_rel_eqv.
            rewrite rsr_codom. rewrite EXTRAOLD.
            clear. basic_solver. }
          clear. basic_solver. }
        assert (BMAP : mapper b_t = a_t).
        { apply rsr_map_bt with (X_t := X_t) (X_s := X_s); eauto. }
        rewrite BMAP. basic_solver. }
      arewrite_false (⦗eq b_t⦘ ⨾ WCore.sb_delta e E_s).
      { unfold WCore.sb_delta.
        intros x y PATH. destruct PATH as [x0 [[EQ EQB] CONDS]].
        subst x x0.
        destruct CONDS as [CONDS EQ]. subst y.
        destruct CONDS as [INIT | TIDS].
        { destruct INV; basic_solver 4. }
        destruct TIDS as [INE TIDB].
        unfold same_tid in TIDB.
        apply ETID in TIDB. basic_solver. }
      rewrite SBHELP. basic_solver. }
    assert (AINRW : eq a_t ∩₁ (acts_set G_s') ⊆₁ (R G_s' ∪₁ W G_s')).
    { intros x XIN.
      destruct simrel_a_lab_wr with (X_s := X_s') (X_t := X_t') 
          (a_t := a_t) (b_t := b_t) (mapper := mapper') (x := x); vauto.
      apply EQACTS; basic_solver. }
    assert (AINNREL : eq a_t ∩₁ (acts_set G_s') ⊆₁ set_compl (Rel G_s')).
    { intros x COND.
      apply simrel_a_lab_notrel with (X_s := X_s') (X_t := X_t')
          (a_t := a_t) (b_t := b_t) (mapper := mapper') (x := x); vauto.
      apply EQACTS; basic_solver. }
    assert (RPOIMMEMP : ⦗eq b_t⦘ ⨾ rpo_imm G_s' ⊆ ∅₂).
    { unfold rpo_imm. rewrite !seq_union_r.
      rewrite <- !seqA.
      rewrite !seq_eqvC with (doma := eq b_t).
      rewrite !seqA with (r3 := sb G_s').
      rewrite wf_sbE. rewrite !seqA.
      arewrite !(⦗eq b_t⦘ ⨾ ⦗acts_set G_s'⦘ ≡ ⦗acts_set G_s'⦘ ⨾ ⦗eq b_t⦘).
      { basic_solver 11. }
      rewrite <- !seqA.
      rewrite !seqA with (r3 := ⦗eq b_t⦘).
      rewrite !seqA with (r3 := sb G_s').
      rewrite !SBFROMA.
      rewrite !seqA. rewrite <- !cross_inter_r.
      rewrite <- !cross_inter_l.
      repeat apply inclusion_union_l.
      { destruct INV.
        clear - AINRW rsr_at_neq_bt.
        arewrite_id (⦗R G_s' ∩₁ Rlx G_s'⦘).
        arewrite_id (⦗acts_set G_s'⦘) at 1.
        rels.
        transitivity (eq b_t × eq a_t ⨾ ⦗acts_set G_s'⦘ ⨾ ⦗F G_s'⦘).
        { clear. basic_solver. }
        intros x y PATH.
        destruct PATH as (x0 & (CROSS1 & CROSS2) & COND); subst.
        apply id_inter in COND.
        clear - AINRW COND.
        destruct COND as (EQ & (COND1 & COND2)); subst.
        destruct AINRW with y; [basic_solver 12 | |].
        { unfold is_f, is_r in *. basic_solver 12. }
        unfold is_f, is_w in *. basic_solver 12. }
      { admit. (*TODO : add*)}
      { clear - AINNREL. 
        arewrite_id (⦗acts_set G_s'⦘) at 1. rels.
        intros x y PATH.
        destruct PATH as (x0 & (CROSS1 & CROSS2) & COND); subst.
        apply id_inter in COND.
        clear - AINNREL COND.
        destruct COND as (EQ & (COND1 & COND2)); subst.
        destruct AINNREL with y; basic_solver 12. }
      arewrite_id (⦗W G_s' ∩₁ Rlx G_s'⦘).
      arewrite_id (⦗acts_set G_s'⦘) at 2.
      rels.
      unfold is_f; ins. destruct INV.
      clear - rsr_at_neq_bt E_NOT_B E_NOT_A A_NOT_F SIMREL. unfolder.
      intros x y ((COND1 & EQ) & (COND2 & COND3)).
      subst x y. rewrite updo in COND1; [| basic_solver].
      destruct COND1 as [C1 C2].
      admit. (*TODO : add*) }
      assert (MAPE : e = mapper' e).
      { unfold mapper'. now rewrite upds. }
      assert (RPOEMP : ⦗eq b_t⦘ ⨾ rpo G_s' ⊆ ∅₂).
      { unfold rpo. rewrite ct_begin.
        rewrite <- seqA.
        rewrite RPOIMMEMP. clear. basic_solver. }
      assert (RPOCODOM : codom_rel (⦗eq b_t⦘ ⨾ rpo G_s') ≡₁ ∅).
      { split; [| basic_solver].
        rewrite RPOEMP. clear; basic_solver. }
      assert (RPOIMMCODOM : codom_rel (⦗eq b_t⦘ ⨾ rpo_imm G_s') ≡₁ ∅).
      { split; [| basic_solver]. arewrite (rpo_imm G_s' ⊆ rpo G_s').
        destruct RPOCODOM; vauto. }
      assert (RPOIMMST : ⦗E_s ∪₁ eq e⦘ ⨾ rpo_imm G_s' ≡ rpo_imm G_s').
      { split; [basic_solver |].
        arewrite (rpo_imm G_s' ⊆ ⦗acts_set G_s'⦘ ⨾ rpo_imm G_s').
        { rewrite wf_rpo_immE at 1.
          { basic_solver. }
          admit. (* TODO : add*) }
        unfold G_s' at 1; ins. }
    destruct (lab_s b_t) eqn:BLAB.
    { apply XmmCons.read_extent with (G_t := G_t')
        (sc_t := WCore.sc X_t') (a := b_t) (m := mapper'); eauto.
      { apply SIMREL'. }
      { destruct SIMREL'. rewrite rsr_acts.
        rewrite EXTRA; clear; basic_solver. }
      { destruct SIMREL'; vauto. }
      { unfold G_s', is_r. ins.
        rewrite updo; ins; basic_solver. }
      { admit. (*TODO: add*) }
      { rewrite EQACTS.
        rewrite set_collect_union, MAPER_E, MAPSUB, (rsr_codom SIMREL).
        rewrite EXEQ. rewrite EXTRA; rels. intros FLS.
        destruct FLS as [FLS | FLS].
        { destruct SIMREL.
          destruct FLS; vauto. }
        destruct E_NOT_B; vauto. }
      { arewrite (rpo (WCore.G X_s') ⊆ ⦗acts_set G_s'⦘ ⨾ rpo G_s').
        { rewrite wf_rpoE.
          arewrite (acts_set (WCore.G X_s') ⊆₁ acts_set G_s').
          basic_solver. }
        transitivity (⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ rpo G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘).
        { hahn_frame_r. unfold set_minus. intros x y (x0 & (EQ & INE) & PTH); subst x0.
          red. exists x; splits; vauto. red. split; vauto.
          splits; vauto. intros FALSE. subst x.
          destruct RPOCODOM as [IN OUT]. destruct IN with y.
          clear - PTH. basic_solver 8. }
        unfold rpo. transitivity ((⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ rpo_imm G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘)⁺).
        { induction 1 as (x0 & (P1 & (x1 & (P2 & P3)))).
          destruct P1 as (EQ & COND1); subst x0.
          destruct P3 as (EQ & COND2); subst x1.
          induction P2 as [x y STT | x].
          { apply ct_step. unfold seq. exists x. splits; vauto. }
          apply ct_begin in P2_2. destruct P2_2 as (x0 & P1 & P2).
          apply wf_rpo_immE in P1; vauto.
          { destruct P1 as [x1 [[EQQ INEE] [x2 [P3 [EQ INE]]]]]. subst x2 y.
            unfold G_s' in INE; ins.
            assert (INE' : ((E_s ∪₁ eq e) \₁ eq b_t) x1).
            { unfold set_minus. splits; vauto.
              intros FALSE. subst x1.
              destruct RPOIMMCODOM as [IN OUT]. destruct IN with x0.
              clear - P3. basic_solver 8. }
            apply IHP2_1 in COND1; vauto.
            apply IHP2_2 in INE'; vauto. }
          admit. (*TODO : add*) }
          assert (IND1 : (⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ rpo_imm G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘) ⊆ mapper' ↑ (rpo_imm G_t')⁺).
          { unfold rpo_imm. rewrite !seq_union_l. rewrite !seqA.
            rewrite <- ct_step.
            rewrite !seq_union_r.
            arewrite (sb_t' ≡ ⦗E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t'⦘).
            { rewrite wf_sbE. basic_solver 11. }
            rewrite <- seqA. rewrite seq_eqvC.
            rewrite seqA. rewrite seq_eqvC.
            arewrite (⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗Acq G_s'⦘ ⨾ sb G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ≡
                      ⦗Acq G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ sb G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘).
            { rewrite <- seqA. rewrite seq_eqvC; basic_solver. }
            arewrite (⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ sb G_s' ⨾ ⦗Rel G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ≡
                      ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ sb G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗Rel G_s'⦘).
            { rewrite <- seqA. rewrite seq_eqvC; basic_solver. }
            arewrite (⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ sb G_s' ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ≡
                      ⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ sb G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘).
            { rewrite seq_eqvC. rewrite <- seqA. rewrite seq_eqvC. basic_solver. }
            assert (SBSUB : ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ sb G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⊆
                          ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘).
            { destruct SIMREL'.
              arewrite (G_s' = WCore.G X_s').
              rewrite rsr_sb. rewrite !seq_union_l, !seq_union_r.
              apply inclusion_union_l.
              { apply inclusion_union_l.
                { unfold swap_rel.
                  arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
                  { clear -EMP. basic_solver. }
                  rels. }
                rewrite EXTRA. clear; basic_solver. }
              rewrite EXTRA. clear; basic_solver. }
            arewrite (⦗R G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ sb G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗F G_s' ∩₁ Acq G_s'⦘
                      ⊆ ⦗R G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗F G_s' ∩₁ Acq G_s'⦘).
            { clear - SBSUB. hahn_frame_l. hahn_frame_r; vauto. }
            arewrite (⦗Acq G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ sb G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ 
                      ⊆ ⦗Acq G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘).
            arewrite (⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ sb G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗Rel G_s'⦘
                      ⊆ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗Rel G_s'⦘).
            { clear - SBSUB. hahn_frame_r; vauto. }
            arewrite (⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ sb G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘
                      ⊆ ⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘).
            { clear - SBSUB. hahn_frame_l. hahn_frame_r; vauto. }
            rewrite <- !id_inter. rewrite <- !seqA.
            rewrite <- !id_inter. rewrite !seqA.
            rewrite <- !set_interA.
            destruct SIMREL. rewrite rsr_acts.
            rewrite EXTRAOLD.
            arewrite ((mapper ↑₁ E_t ∪₁ eq b_t ∪₁ eq e) \₁ eq b_t
              ⊆₁ mapper ↑₁ E_t ∪₁ eq e).
            { clear. basic_solver. }
            
            rewrite MAPE.
            arewrite (mapper ↑₁ E_t ∪₁ eq (mapper' e)
              ⊆₁ mapper' ↑₁ E_t').
            { rewrite <- MAPSUB. rewrite EQACTS. clear; basic_solver 8. }
            arewrite (⦗R G_s' ∩₁ Rlx G_s' ∩₁ mapper' ↑₁ E_t'⦘
                        ⊆ mapper' ↑ ⦗R_t' ∩₁ Rlx G_t' ∩₁ E_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as ((COND1 & COND2) & INE).
              destruct INE as [x' [INE MAP]].
              unfold collect_rel.
              exists x', x'. split; vauto.
              split; vauto. split; vauto.
              destruct SIMREL'. split.
              { unfold G_s' in COND1; ins.
                unfold is_r. destruct rsr_lab0 with x'; vauto. }
              unfold G_s' in COND2; ins.
              unfold is_rlx. unfold mod. destruct rsr_lab0 with x'; vauto. }
            arewrite (⦗mapper' ↑₁ E_t' ∩₁ F G_s' ∩₁ Acq G_s'⦘
                        ⊆ mapper' ↑ ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as ((INE & COND2) & COND1).
              destruct INE as [x' [INE MAP]].
              unfold collect_rel.
              exists x', x'. split; vauto.
              split; vauto. destruct SIMREL'. split.
              { split; vauto.
                unfold is_f. destruct rsr_lab0 with x'; vauto. }
              unfold is_acq. unfold mod.
              destruct rsr_lab0 with x'; vauto. }
            arewrite (⦗Acq G_s' ∩₁ mapper' ↑₁ E_t'⦘
                        ⊆ mapper' ↑ ⦗Acq G_t' ∩₁ E_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as (COND1 & INE).
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x', x'. split; vauto.
              split; vauto. destruct SIMREL'.
              split; vauto. 
              unfold G_s' in COND1; ins.
              unfold is_acq. unfold mod.
              destruct rsr_lab0 with x'; vauto. }
            arewrite (mapper' ↑ ⦗Acq G_t' ∩₁ E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗mapper' ↑₁ E_t'⦘
                  ⊆ mapper' ↑ ⦗Acq G_t' ∩₁ E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t'⦘).
            { do 2 hahn_frame_l. rewrite collect_rel_eqv; vauto. }
            arewrite (⦗(mapper' ↑₁ E_t') ∩₁ Rel G_s'⦘
                  ⊆ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as (INE & COND1).
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x', x'. split; vauto.
              split; vauto. destruct SIMREL'.
              split; vauto.
              unfold G_s' in COND1; ins.
              unfold is_rel. unfold mod.
              destruct rsr_lab0 with x'; vauto. }
            
            arewrite (⦗mapper' ↑₁ E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘ 
                  ⊆ mapper' ↑ ⦗E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘).
            { do 2 hahn_frame_r. rewrite collect_rel_eqv; vauto. }
            arewrite (⦗F G_s' ∩₁ Rel G_s' ∩₁ mapper' ↑₁ E_t'⦘ 
                    ⊆ mapper' ↑ ⦗F G_t' ∩₁ Rel G_t' ∩₁ E_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as ((COND1 & COND2) & INE).
              destruct INE as [x' [INE MAP]].
              unfold collect_rel.
              exists x', x'. split; vauto.
              split; vauto. destruct SIMREL'. split; vauto.
              split.
              { unfold is_f. destruct rsr_lab0 with x'; vauto. }
              unfold is_rel. unfold mod.
              destruct rsr_lab0 with x'; vauto. }
            
            arewrite (⦗(mapper' ↑₁ E_t') ∩₁ W G_s' ∩₁ Rlx G_s'⦘
                    ⊆ mapper' ↑ ⦗E_t' ∩₁ W G_t' ∩₁ Rlx G_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as ((INE & COND2) & COND1).
              destruct INE as [x' [INE MAP]].
              unfold collect_rel.
              exists x', x'. split; vauto.
              split; vauto. destruct SIMREL'. split.
              { split; vauto. unfold G_s' in COND1; ins.
                unfold is_w. destruct rsr_lab0 with x'; vauto. }
              unfold G_s' in COND2; ins.
              unfold is_rlx. unfold mod. destruct rsr_lab0 with x'; vauto. }
            rewrite !collect_rel_union.
            apply union_more.
            { apply union_more.
              { apply union_more.
                { rewrite !collect_rel_seq; vauto.
                  { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
                    { rewrite wf_sbE. basic_solver. }
                    assert (IN2 : dom_rel ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘ ⊆₁ E_t').
                    { basic_solver. }
                    rewrite IN1, IN2. destruct SIMREL'.
                    clear - rsr_inj0; basic_solver 8. }
                  assert (IN1 : codom_rel ⦗R_t' ∩₁ Rlx G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
                  { basic_solver. }
                  assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘) ⊆₁ E_t').
                  { rewrite wf_sbE. basic_solver. }
                  rewrite IN1, IN2. destruct SIMREL'.
                  clear - rsr_inj0; basic_solver 8. }
                rewrite !collect_rel_seq; vauto.
                { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
                  { rewrite wf_sbE. basic_solver. }
                  assert (IN2 : dom_rel ⦗E_t'⦘ ⊆₁ E_t').
                  { basic_solver. }
                  rewrite IN1, IN2. destruct SIMREL'.
                  clear - rsr_inj0; basic_solver 8. }
                assert (IN1 : codom_rel ⦗Acq G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
                { basic_solver. }
                assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t'⦘) ⊆₁ E_t').
                { rewrite wf_sbE. basic_solver. }
                rewrite IN1, IN2. destruct SIMREL'.
                clear - rsr_inj0; basic_solver 8. }
              rewrite !collect_rel_seq; vauto.
              { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
                { rewrite wf_sbE. basic_solver. }
                assert (IN2 : dom_rel ⦗E_t' ∩₁ Rel G_t'⦘ ⊆₁ E_t').
                { basic_solver. }
                rewrite IN1, IN2. destruct SIMREL'.
                clear - rsr_inj0; basic_solver 8. }
              assert (IN1 : codom_rel ⦗E_t'⦘ ⊆₁ E_t').
              { basic_solver. }
              assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ Rel G_t'⦘) ⊆₁ E_t').
              { rewrite wf_sbE. basic_solver. }
              rewrite IN1, IN2. destruct SIMREL'.
              clear - rsr_inj0; basic_solver 8. }
            rewrite !collect_rel_seq; vauto.
            { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
              { rewrite wf_sbE. basic_solver. }
              assert (IN2 : dom_rel ⦗E_t' ∩₁ W_t' ∩₁ Rlx G_t'⦘ ⊆₁ E_t').
              { basic_solver. }
              rewrite IN1, IN2. destruct SIMREL'.
              clear - rsr_inj0; basic_solver 8. }
            assert (IN1 : codom_rel ⦗F G_t' ∩₁ Rel G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
            { basic_solver. }
            assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ W_t' ∩₁ Rlx G_t'⦘) ⊆₁ E_t').
            { rewrite wf_sbE. basic_solver. }
            rewrite IN1, IN2. destruct SIMREL'.
            clear - rsr_inj0; basic_solver 8. }
          assert (IND2 : mapper' ↑ (rpo_imm G_t')⁺ ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘ ⨾ (rpo_imm G_s' ⨾ ⦗(E_s ∪₁ eq e) \₁ eq b_t⦘)
            ⊆ mapper' ↑ (rpo_imm G_t')⁺).
          { assert (TRIN : mapper' ↑ (rpo_imm G_t')⁺ ⨾ mapper' ↑ (rpo_imm G_t')⁺
                          ⊆ mapper' ↑ (rpo_imm G_t')⁺).
          { intros x y PATH. destruct PATH as (x0 & P1 & P2).
            unfold collect_rel in P1, P2. unfold collect_rel.
            destruct P1 as (x' & x0' & (P1 & M1 & M2)).
            destruct P2 as (x0'' & y' & (P2 & M3 & M4)).
            exists x', y'. splits; vauto.
            assert (EQ : x0'' = x0').
            { destruct SIMREL'. apply rsr_inj; vauto.
              { apply ct_begin in P2.
                destruct P2 as (x1 & P2 & P3).
                apply wf_rpo_immE in P2; vauto.
                destruct P2 as (x2 & INE & REST).
                destruct INE as (EQ & INEN); subst x2; vauto. }
              apply ct_end in P1.
              destruct P1 as (x1 & P1 & P1').
              apply wf_rpo_immE in P1'; vauto.
              destruct P1' as (x2 & P3 & (x3 & P4 & (EQ & P5))); vauto. }
            subst x0''. apply ct_ct.
            unfold seq. exists x0'. splits; vauto. }
          rewrite <- TRIN at 2. apply seq_mori; vauto. }
        apply inclusion_t_ind_right; vauto. }
      { split; [|basic_solver].
        destruct SIMREL.
        rewrite <- seq_eqv_inter_ll.
        arewrite (WCore.G X_s' = G_s').
        rewrite SBFROMA. unfolder.
        intros x (y & (XEQ & YEQ) & LOC).
        subst x; subst y. destruct INV.
        destruct INV'.
        admit. (*TODO : ask*) }
      { admit. }
      { destruct SIMREL'.
        rewrite rsr_rf. apply union_more; vauto.
        apply seq_more; vauto.
        rewrite EXTRA. unfold is_r.
        arewrite (WCore.G X_s' = G_s').
        unfold G_s'; ins. unfold upd.
        apply eqv_rel_more. unfold set_inter.
        split.
        { red; intros x COND. 
          destruct COND as [COND1 COND2]; vauto. }
        red; intros x COND. split; vauto.
        rewrite BLAB. desf. }
      { destruct SIMREL'.
        rewrite rsr_co. unfold add_max.
        rewrite EXTRA.
        arewrite ((extra_co_D (acts_set (WCore.G X_s')) (lab (WCore.G X_s'))
                  (loc (lab (WCore.G X_s')) b_t) \₁ eq b_t ∩₁ W (WCore.G X_s'))
                    × (eq b_t ∩₁ W (WCore.G X_s')) ≡ ∅₂); [| basic_solver 8].
        arewrite (eq b_t ∩₁ W (WCore.G X_s') ≡₁ ∅); [| basic_solver 8].
        unfold is_w. red. arewrite (WCore.G X_s' = G_s'). split; vauto.
        red. intros x COND.
        destruct COND as [COND1 COND2].
        subst x.
        unfold G_s'; ins. rewrite updo in COND2.
        { desf. }
        basic_solver. }
      admit. (*TODO : add*) }
    all : admit. }
  assert (EXTRA : extra_a X_t' a_t b_t b_t ≡₁ ∅).
  { unfold extra_a. desf. }
  assert (RPOMAP : rpo G_s' ⊆ mapper' ↑ (rpo G_t')).
  { unfold rpo.
    assert (IND1 : (rpo_imm G_s') ⊆ mapper' ↑ (rpo_imm G_t')⁺).
    { unfold rpo_imm.
      assert (SIMRELD : reord_simrel X_s' X_t' a_t b_t mapper') by vauto.
      destruct SIMREL'.
      arewrite (G_s' = WCore.G X_s').
      rewrite wf_sbE.
      rewrite rsr_sb.
      rewrite EXTRA, cross_false_l, cross_false_r, union_false_r.
      rewrite !union_false_r.
      unfold swap_rel. rewrite !collect_rel_union.
      rewrite !seq_union_l. rewrite !seq_union_r.
      arewrite !(sb_t' \ (eq b_t ∩₁ E_t') × (eq a_t ∩₁ E_t') ⊆ sb_t').
      arewrite (WCore.G X_s' = G_s').
      rewrite !seq_union_l. rewrite !seq_union_r.
      destruct INV. rewrite !seqA.
      arewrite_false (⦗R G_s' ∩₁ Rlx G_s'⦘
                        ⨾ ⦗acts_set G_s'⦘
                          ⨾ mapper' ↑ (eq a_t ∩₁ E_t') × (eq b_t ∩₁ E_t')
                            ⨾ ⦗acts_set G_s'⦘ ⨾ ⦗F G_s' ∩₁ Acq G_s'⦘).
      { arewrite (G_s' = WCore.G X_s'). rewrite rsr_acts.
        rewrite EXTRA. rels. arewrite_id (⦗R (WCore.G X_s') ∩₁ Rlx (WCore.G X_s')⦘).
        rels. destruct INV'.
        arewrite (eq b_t ∩₁ E_t' ⊆₁ eq b_t ∩₁ E_t' ∩₁ E_t').
        { clear. basic_solver. }
        rewrite rsr_b_t_is_r_or_w0.
        rewrite rsr_at.
        intros x y PATH.
        destruct PATH as [x0 [MAP [x1 [[C0 C1] [x2 [C2 C3]]]]]].
        destruct C2 as (EQ & MAPA). subst x2.
        destruct C3 as (EQ & (FNC & ACQ)). destruct SIMRELD.
        clear - C1 rsr_lab0 FNC.
        destruct C1 as (x0' & LABS & MAPN).
        apply set_inter_union_l in LABS.
        destruct LABS as [LAB1 | LAB2].
        { destruct LAB1 as (LAB1 & LAB2). unfold is_w, is_f in *.
          unfold eq_dom in rsr_lab0. specialize (rsr_lab0 x0').
          apply rsr_lab0 in LAB2. rewrite <- LAB2 in LAB1.
          unfold compose in LAB1. rewrite MAPN in LAB1.
          basic_solver. }
        destruct LAB2 as (LAB1 & LAB2). unfold is_r, is_f in *.
        unfold eq_dom in rsr_lab0. specialize (rsr_lab0 x0').
        apply rsr_lab0 in LAB2. rewrite <- LAB2 in LAB1.
        unfold compose in LAB1. rewrite MAPN in LAB1.
        basic_solver. }
      arewrite_false (⦗Acq G_s'⦘
                        ⨾ ⦗acts_set G_s'⦘
                          ⨾ mapper' ↑ (eq a_t ∩₁ E_t') × (eq b_t ∩₁ E_t') ⨾ ⦗acts_set G_s'⦘).
      { admit. }
      arewrite_false (⦗acts_set G_s'⦘
                        ⨾ mapper' ↑ (eq a_t ∩₁ E_t') × (eq b_t ∩₁ E_t') ⨾ ⦗acts_set G_s'⦘ ⨾ ⦗Rel G_s'⦘).
      { admit. }
      arewrite_false (⦗F G_s' ∩₁ Rel G_s'⦘
                        ⨾ ⦗acts_set G_s'⦘
                          ⨾ mapper' ↑ (eq a_t ∩₁ E_t') × (eq b_t ∩₁ E_t')
                            ⨾ ⦗acts_set G_s'⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘).
      { admit.  }
      rewrite !union_false_r.
      assert (SBMAP : mapper' ↑ sb_t' ⊆ ⦗mapper' ↑₁ E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗mapper' ↑₁ E_t'⦘).
      { rewrite wf_sbE at 1. clear. basic_solver 8. }
      rewrite SBMAP. rewrite !seqA. arewrite_id (⦗acts_set G_s'⦘). rels.
      seq_rewrite <- !id_inter.
      arewrite (G_s' = WCore.G X_s').
      arewrite (⦗R (WCore.G X_s') ∩₁ Rlx (WCore.G X_s') ∩₁ mapper' ↑₁ E_t'⦘ ⊆
                                  mapper' ↑ ⦗(R_t' ∩₁ Rlx G_t' ∩₁ E_t')⦘).
      { intros x y COND. destruct COND as (EQ & COND); subst y.
        destruct COND as ((COND1 & COND2) & INE).
        destruct INE as [x' [INE MAP]].
        unfold set_collect.
        exists x'. exists x'. splits; vauto.
        split; vauto. split; vauto.
        split.
        { unfold G_s' in COND1; ins.
          unfold is_r. destruct rsr_lab with x'; vauto. }
        unfold G_s' in COND2; ins.
        unfold is_rlx. unfold mod. destruct rsr_lab with x'; vauto. }
      arewrite (⦗mapper' ↑₁ E_t' ∩₁ (F (WCore.G X_s') ∩₁ Acq (WCore.G X_s'))⦘
              ⊆ mapper' ↑ ⦗(E_t' ∩₁ F G_t' ∩₁ Acq G_t')⦘).
      { intros x y COND. destruct COND as (EQ & COND); subst y.
        destruct SIMREL.
        destruct COND as [INE [FACQ FAT]].
        unfold set_collect.
        destruct INE as [x' [INE MAP]].
        exists x'. exists x'. splits; vauto.
        split; vauto. split.
        { split; vauto. unfold G_s' in FACQ; ins.
          unfold is_f. destruct rsr_lab with x'; vauto. }
        unfold G_s' in FAT; ins.
        unfold is_acq. unfold mod. destruct rsr_lab with x'; vauto. }
      arewrite (⦗Acq (WCore.G X_s') ∩₁ mapper' ↑₁ E_t'⦘
              ⊆ mapper' ↑ ⦗(Acq G_t' ∩₁ E_t')⦘).
      { intros x y COND. destruct COND as (EQ & COND); subst y.
        destruct SIMREL.
        destruct COND as [ACQ INE].
        unfold set_collect.
        destruct INE as [x' [INE MAP]].
        exists x'. exists x'. splits; vauto. split; vauto.
        split; vauto.
        unfold G_s' in ACQ; ins.
        unfold is_acq. unfold mod. destruct rsr_lab with x'; vauto. }
      arewrite (mapper' ↑ ⦗(Acq G_t' ∩₁ E_t')⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗mapper' ↑₁ E_t'⦘
              ⊆ mapper' ↑ ⦗(Acq G_t' ∩₁ E_t')⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t'⦘).
      { do 2 hahn_frame_l. rewrite collect_rel_eqv; vauto. }
      arewrite (⦗mapper' ↑₁ E_t'⦘
            ⨾ mapper' ↑ sb_t' ⨾ ⦗mapper' ↑₁ E_t' ∩₁ Rel (WCore.G X_s')⦘
          ⊆ mapper' ↑ ⦗E_t'⦘
            ⨾ mapper' ↑ sb_t' ⨾ ⦗mapper' ↑₁ E_t' ∩₁ Rel (WCore.G X_s')⦘).
      { do 2 hahn_frame_r. rewrite collect_rel_eqv; vauto. }
      arewrite (⦗mapper' ↑₁ E_t' ∩₁ Rel (WCore.G X_s')⦘
            ⊆ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘).
      { intros x y COND. destruct COND as (EQ & COND); subst y.
        destruct SIMREL.
        destruct COND as [INE REL].
        unfold set_collect.
        destruct INE as [x' [INE MAP]].
        exists x'. exists x'. splits; vauto. 
        split; vauto. split; vauto.
        unfold G_s' in REL; ins.
        unfold is_rel. unfold mod. destruct rsr_lab with x'; vauto. }
      arewrite (⦗F (WCore.G X_s') ∩₁ Rel (WCore.G X_s') ∩₁ mapper' ↑₁ E_t'⦘
            ⊆ mapper' ↑ ⦗(F G_t' ∩₁ Rel G_t' ∩₁ E_t')⦘).
      { intros x y COND. destruct COND as (EQ & COND); subst y.
        destruct SIMREL.
        destruct COND as [[FENC REL] INE].
        unfold set_collect.
        destruct INE as [x' [INE MAP]].
        exists x'. exists x'. splits; vauto.
        split; vauto. split; vauto. split.
        { unfold G_s' in FENC; ins.
          unfold is_f. destruct rsr_lab with x'; vauto. }
        unfold G_s' in FENC; ins.
        unfold is_rel. unfold mod. destruct rsr_lab with x'; vauto. }
      arewrite (⦗mapper' ↑₁ E_t' ∩₁ (W (WCore.G X_s') ∩₁ Rlx (WCore.G X_s'))⦘
            ⊆ mapper' ↑ ⦗(E_t' ∩₁ W G_t' ∩₁ Rlx G_t')⦘).
      { intros x y COND. destruct COND as (EQ & COND); subst y.
        destruct SIMREL.
        destruct COND as [INE [WRLX INE']].
        unfold set_collect.
        destruct INE as [x' [INE MAP]].
        exists x'. exists x'. splits; vauto.
        split; vauto. split; vauto.
        { split; vauto.
          unfold G_s' in WRLX; ins.
          unfold is_w. unfold is_rlx. unfold mod.
          destruct rsr_lab with x'; vauto. }
        unfold G_s' in INE'; ins.
        unfold is_rlx. unfold mod. destruct rsr_lab with x'; vauto. }
      rewrite <- ct_step.
      assert (SBT : sb_t' ≡ ⦗E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t'⦘).
      { rewrite wf_sbE. basic_solver. }
      rewrite SBT at 5. rewrite SBT at 6.
      rewrite SBT at 7. rewrite SBT at 8.
      rewrite !collect_rel_union. rewrite !seqA.
      rewrite <- !id_inter.
      rewrite <- !seqA.
      rewrite <- !id_inter.
      rewrite !seqA.
      apply union_more.
      { apply union_more.
        { apply union_more.
          { rewrite !collect_rel_seq; rewrite <- set_interA; vauto.
            { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
              { clear. rewrite wf_sbE. basic_solver. }
              assert (IN2 : dom_rel ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘ ⊆₁ E_t').
              { clear. basic_solver. }
              rewrite IN1, IN2.
              clear - rsr_inj; basic_solver 8. }
            assert (IN1 : codom_rel ⦗R_t' ∩₁ Rlx G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
            { clear. basic_solver. }
            assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘) ⊆₁ E_t').
            { clear. rewrite wf_sbE. basic_solver. }
            rewrite IN1, IN2.
            clear - rsr_inj; basic_solver 8. }
          rewrite !collect_rel_seq; vauto.
          { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
            { clear. rewrite wf_sbE. basic_solver. }
            assert (IN2 : dom_rel ⦗E_t'⦘ ⊆₁ E_t').
            { clear. basic_solver. }
            rewrite IN1, IN2.
            clear - rsr_inj; basic_solver 8. }
          assert (IN1 : codom_rel ⦗Acq G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
          { clear. basic_solver. }
          assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t'⦘) ⊆₁ E_t').
          { clear. rewrite wf_sbE. basic_solver. }
          rewrite IN1, IN2.
          clear - rsr_inj; basic_solver 8. }
        rewrite !collect_rel_seq; vauto.
        { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
          { clear. rewrite wf_sbE. basic_solver. }
          assert (IN2 : dom_rel ⦗E_t' ∩₁ Rel G_t'⦘ ⊆₁ E_t').
          { clear. basic_solver. }
          rewrite IN1, IN2.
          clear - rsr_inj; basic_solver 8. }
        assert (IN1 : codom_rel ⦗E_t'⦘ ⊆₁ E_t').
        { clear. basic_solver. }
        assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ Rel G_t'⦘) ⊆₁ E_t').
        { clear. rewrite wf_sbE. basic_solver. }
        rewrite IN1, IN2.
        clear - rsr_inj; basic_solver 8. }
      rewrite !collect_rel_seq; rewrite <- set_interA; vauto.
      { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
        { clear. rewrite wf_sbE. basic_solver. }
        assert (IN2 : dom_rel ⦗E_t' ∩₁ W_t' ∩₁ Rlx G_t'⦘ ⊆₁ E_t').
        { clear. basic_solver. }
        rewrite IN1, IN2.
        clear - rsr_inj; basic_solver 8. }
      assert (IN1 : codom_rel ⦗F G_t' ∩₁ Rel G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
      { clear. basic_solver. }
      assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ W_t' ∩₁ Rlx G_t'⦘) ⊆₁ E_t').
      { clear. rewrite wf_sbE. basic_solver. }
      rewrite IN1, IN2.
      clear - rsr_inj; basic_solver 8. }
    assert (IND2 : mapper' ↑ (rpo_imm G_t')⁺ ⨾ (rpo_imm G_s')
      ⊆ mapper' ↑ (rpo_imm G_t')⁺).
    { assert (TRIN : mapper' ↑ (rpo_imm G_t')⁺ ⨾ mapper' ↑ (rpo_imm G_t')⁺
              ⊆ mapper' ↑ (rpo_imm G_t')⁺).
      { intros x y PATH. destruct PATH as (x0 & P1 & P2).
        unfold collect_rel in P1, P2. unfold collect_rel.
        destruct P1 as (x' & x0' & (P1 & M1 & M2)).
        destruct P2 as (x0'' & y' & (P2 & M3 & M4)).
        exists x', y'. splits; vauto.
        assert (EQ : x0'' = x0').
        { destruct SIMREL'. apply rsr_inj; vauto.
          { apply ct_begin in P2.
            destruct P2 as (x1 & P2 & P3).
            destruct INV.
            apply wf_rpo_immE in P2; vauto.
            destruct P2 as (x2 & INE & REST).
            apply INE. }
          apply ct_end in P1.
          destruct P1 as (x1 & P1 & P1').
          destruct INV.
          apply wf_rpo_immE in P1'; vauto.
          destruct P1' as (x2 & P3 & (x3 & P4 & (EQ & P5))); vauto. }
        subst. apply ct_ct.
        unfold seq. exists x0'. splits; vauto. }
      rewrite <- TRIN at 2. apply seq_mori; vauto. }
    apply inclusion_t_ind_right; vauto. }
  apply XmmCons.monoton_cons with (G_t := G_t')
              (sc_t := WCore.sc X_t') (m := mapper'); eauto.
  { apply SIMREL'. }
  1-4: destruct SIMREL'.
  { rewrite rsr_acts. rewrite EXTRA. basic_solver. }
  { rewrite rsr_rf. rewrite EXTRA. basic_solver 8. }
  { rewrite rsr_co. rewrite EXTRA. basic_solver 8. }
  { rewrite rsr_rmw; vauto. }
  { assert (IND1 : (sb G_s' ∩ same_loc (lab G_s') ∪ rpo G_s' ∪ sw G_s') 
          ⊆ mapper' ↑ (sb_t' ∩ same_loc_t' ∪ rpo_t' ∪ sw G_t')⁺).
    { rewrite <- ct_step.
      rewrite !collect_rel_union.
      repeat apply union_mori; vauto.
      { apply not_and_or in NEMP. destruct NEMP as [N1 | N2].
        { destruct SIMREL'.
          arewrite (G_s' = WCore.G X_s').
          rewrite rsr_sb. rewrite !EXTRA. rels.
          unfold swap_rel.
          rewrite collect_rel_union. rewrite inter_union_l.
          apply inclusion_union_l.
          { transitivity (mapper' ↑ (sb_t') ∩ same_loc (lab G_s')).
            { basic_solver 21. }
            intros x y ((x0 & y0 & SB & M1 & M2) & PTH2).
            unfold collect_rel. exists x0, y0. splits; vauto.
            split; vauto. unfold same_loc in *.
            unfold loc. unfold loc in PTH2.
            rewrite <- rsr_lab; vauto.
            { rewrite <- rsr_lab; vauto.
              apply wf_sbE in SB. destruct SB as
                  (x1 & INE1 & (y1 & SB & (EQ & INE2))); vauto. }
            apply wf_sbE in SB. destruct SB as
                (x1 & (EQ & INE) & RST); vauto. }
          rewrite collect_rel_cross.
          rewrite rsr_bt, rsr_at. destruct INV'.
          arewrite_false (eq b_t × eq a_t ∩ same_loc (lab (WCore.G X_s'))); vauto.
          intros x y COND. destruct COND as ((Q1 & Q2) & SL).
          subst x y.
          (* unfold same_loc in SL. unfold loc in SL. *)
          destruct rsr_at_bt_loc with a_t b_t.
          apply NNPP in N1.
          assert (EIN : E_t' b_t).
          { clear -  N1 rsr_at_bt_ord. basic_solver 8. }
          exists a_t. split; vauto.
          exists b_t. split; vauto.
          unfold same_loc in SL. unfold loc in SL.
          unfold same_loc, loc.
          rewrite <- rsr_lab; vauto.
          rewrite <- rsr_lab; vauto.
          unfold compose.
          assert (AEQ : mapper' a_t = b_t).
          { rewrite rsr_map_at with (X_s := X_s') (X_t := X_t') (b_t := b_t); vauto. }
          assert (BEQ : mapper' b_t = a_t).
          { rewrite rsr_map_bt with (X_s := X_s') (X_t := X_t') (a_t := a_t); vauto. }
          rewrite AEQ, BEQ. vauto. }
        destruct SIMREL'.
        arewrite (G_s' = WCore.G X_s').
        rewrite rsr_sb. rewrite !EXTRA. rels.
        unfold swap_rel.
        rewrite collect_rel_union. rewrite inter_union_l.
        assert (BEMP : eq b_t ∩₁ E_t' ≡₁ ∅).
        { clear - N2. basic_solver 8. }
        rewrite !BEMP. rels.
        transitivity (mapper' ↑ (sb_t') ∩ same_loc (lab G_s')).
        { basic_solver 21. }
        intros x y ((x0 & y0 & SB & M1 & M2) & PTH2).
        unfold collect_rel. exists x0, y0. splits; vauto.
        split; vauto. unfold same_loc in *.
        unfold loc. unfold loc in PTH2.
        rewrite <- rsr_lab; vauto.
        { rewrite <- rsr_lab; vauto.
          apply wf_sbE in SB. destruct SB as
              (x1 & INE1 & (y1 & SB & (EQ & INE2))); vauto. }
        apply wf_sbE in SB. destruct SB as
            (x1 & (EQ & INE) & RST); vauto. }
      unfold sw. unfold release. unfold rs.
      destruct SIMREL'. arewrite (G_s' = WCore.G X_s').
      rewrite rsr_rf. rewrite EXTRA. rewrite set_inter_empty_l.
      rels. rewrite rsr_rmw.
      arewrite ((mapper' ↑ rf_t' ⨾ mapper' ↑ rmw_t')＊ ⨾ mapper' ↑ rf_t'
            ⊆ ⦗mapper' ↑₁ E_t'⦘ ⨾ (mapper' ↑ rf_t' ⨾ mapper' ↑ rmw_t')＊ ⨾ mapper' ↑ rf_t' ⨾ ⦗mapper' ↑₁ E_t'⦘).
      { rewrite rtE. rewrite !seq_union_l.
        apply inclusion_union_l.
        { rewrite wf_rfE at 1 2; vauto.
          basic_solver 12. }
        rewrite !seq_union_r.
        rewrite ct_begin.
        rewrite wf_rfE at 1 3; vauto.
        apply inclusion_union_r. right.
        rewrite !collect_rel_seqi.
        rewrite !collect_rel_eqv.
        do 2 hahn_frame_r. do 2 hahn_frame_l.
        basic_solver 21. }
      arewrite (⦗Rlx (WCore.G X_s')⦘ ⨾ ⦗W (WCore.G X_s')⦘
                    ⨾ ⦗mapper' ↑₁ E_t'⦘ ⊆ ⦗mapper' ↑₁ E_t'⦘ ⨾ ⦗Rlx (WCore.G X_s')⦘
                            ⨾ ⦗W (WCore.G X_s')⦘ ⨾ ⦗mapper' ↑₁ E_t'⦘) by mode_solver 21.
      arewrite (⦗F (WCore.G X_s')⦘ ⨾ sb (WCore.G X_s')
            ⊆ ⦗F (WCore.G X_s')⦘ ⨾ ⦗mapper' ↑₁ E_t'⦘ ⨾ mapper' ↑ sb_t').
      { rewrite rsr_sb. rewrite !seq_union_r.
        apply inclusion_union_l.
        { apply inclusion_union_l.
          { unfold swap_rel. rewrite collect_rel_union.
            rewrite seq_union_r.
            apply inclusion_union_l.
            { transitivity (⦗F (WCore.G X_s')⦘ ⨾ mapper' ↑ (sb_t')); [basic_solver 21|].
              hahn_frame_l. rewrite wf_sbE. basic_solver. }
            rewrite collect_rel_cross. rewrite rsr_bt.
            arewrite (eq a_t ∩₁ E_t' ≡₁ eq a_t ∩₁ E_t' ∩₁ E_t') by basic_solver.
            rewrite (rsr_a_t_is_r_or_w INV').
            arewrite_false (⦗F (WCore.G X_s')⦘ ⨾ (mapper' ↑₁ ((W_t' ∪₁ R_t') ∩₁ E_t')) × eq a_t); vauto.
            rewrite <- cross_inter_l. clear - rsr_lab.
            intros x y COND. destruct COND as (LT & RT); subst.
            destruct LT as [FNC MAP]. destruct MAP as [x0 [CONDS MAP]].
            rewrite <- MAP in FNC. unfold is_f in FNC.
            unfold compose in rsr_lab. unfold eq_dom in rsr_lab.
            specialize rsr_lab with x0.
            assert (EQ : lab (WCore.G X_s') (mapper' x0) = lab_t' x0).
            { apply rsr_lab. destruct CONDS; vauto. }
            rewrite EQ in FNC. destruct CONDS as [CONDS INE].
            unfold is_w, is_r in CONDS. clear - CONDS FNC.
            destruct CONDS; basic_solver. }
          rewrite EXTRA. basic_solver. }
        rewrite EXTRA. basic_solver. }
      arewrite ((⦗F (WCore.G X_s')⦘ ⨾ ⦗mapper' ↑₁ E_t'⦘ ⨾ mapper' ↑ sb_t')^?
            ⨾ ⦗mapper' ↑₁ E_t'⦘ ⊆ ⦗mapper' ↑₁ E_t'⦘ ⨾ (⦗F (WCore.G X_s')⦘ ⨾ ⦗mapper' ↑₁ E_t'⦘ ⨾ mapper' ↑ sb_t')^?
            ⨾ ⦗mapper' ↑₁ E_t'⦘).
      { rewrite crE at 1. rewrite seq_union_l.
        apply inclusion_union_l; basic_solver 21. }
      rewrite <- seqA. rewrite <- id_inter.
      transitivity (mapper'
          ↑ ((⦗Rel G_t'⦘ ⨾ ⦗E_t'⦘)
            ⨾ ((⦗F G_t'⦘ ⨾ sb_t')^? ⨾ ⦗E_t'⦘)
              ⨾ ⦗Rlx G_t'⦘
                ⨾ ⦗W_t'⦘ ⨾ ⦗E_t'⦘
                  ⨾ (rf_t' ⨾ rmw_t')＊
                    ⨾ rf_t' ⨾ ⦗E_t'⦘
                      ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗E_t'⦘ 
                        ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^? ⨾ ⦗E_t'⦘ 
                          ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘)).
      { arewrite (⦗Rel G_t'⦘ ⨾ ⦗E_t'⦘ ≡ ⦗Rel G_t' ∩₁ E_t'⦘).
        { clear; basic_solver. }
        rewrite collect_rel_seq.
        { apply seq_mori.
          { intros x y COND. destruct COND as (LT & RT); subst.
            destruct RT as [REL [y0 [INE MAP]]].
            red. exists y0, y0. splits; vauto.
            red. split; vauto. split; vauto.
            unfold is_rel in *. unfold mod in *.
            rewrite <- rsr_lab; vauto. }
          rewrite <- seqA.
          transitivity (mapper' ↑ (((⦗F G_t'⦘ ⨾ sb_t')^?
            ⨾ ⦗E_t'⦘) ⨾ ⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗W_t'⦘ ⨾ ⦗E_t'⦘ ⨾ (rf_t' ⨾ rmw_t')＊
              ⨾ rf_t' ⨾ ⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗E_t'⦘
                ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^? ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘)).
          { rewrite collect_rel_seq.
            { apply seq_mori.
              { intros x y COND. unfold collect_rel.
                destruct COND as (z & COND & INE); subst.
                destruct INE as (EQ & MAP); subst.
                destruct MAP as [z0 [INE MAP]]; subst.
                destruct COND as [EQ | NEQ].
                { exists z0, z0. splits; vauto.
                  exists z0. splits; vauto. }
                destruct NEQ as (x0 & (EQ & FNC) & (z1 & (EQ2
                              & (x1 & (MAP2 & INE2))) & MAP)); subst.
                exists x1, z0. splits; vauto.
                exists z0. splits; vauto.
                apply crE. right. exists x1. splits.
                { red. splits; vauto.
                  unfold is_f in *. rewrite <- rsr_lab; vauto. }
                destruct MAP as (x0 & x2 & (SB & M1 & M2)).
                apply rsr_inj in M1.
                { apply rsr_inj in M2. subst; vauto.
                  { apply wf_sbE in SB. clear - SB.
                    destruct SB as (y1 & INE & (y2 & SB & (EQ & INE'))); vauto. }
                  vauto. }
                { apply wf_sbE in SB. clear - SB.
                  destruct SB as (y1 & (EQ & INE') & RST); vauto. }
                vauto. }
              arewrite (⦗mapper' ↑₁ E_t'⦘ ⊆ ⦗mapper' ↑₁ E_t'⦘ ⨾ ⦗mapper' ↑₁ E_t'⦘).
              { clear. basic_solver. }
              do 2 rewrite <- seqA.
              do 2 rewrite seq_eqv.
              transitivity (mapper' ↑ ((⦗E_t'⦘
                ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗W_t'⦘) ⨾ ⦗E_t'⦘ ⨾ (rf_t' ⨾ rmw_t')＊ ⨾ rf_t'
                  ⨾ ⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗E_t'⦘ ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^?
                    ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘)).
              { rewrite collect_rel_seq.
                { apply seq_mori.
                  { intros x y COND. destruct COND as (EQ & COND); subst.
                    destruct COND as ((RLX & ISW) & (y0 & INE & MAP)).
                    unfold collect_rel.
                    exists y0, y0. splits; vauto.
                    exists y0. splits; vauto.
                    exists y0. splits.
                    { red. splits; vauto.
                      unfold is_rlx in *. unfold mod in *.
                      destruct rsr_lab with y0; vauto. }
                    red. split; vauto.
                    unfold is_w in *.
                    destruct rsr_lab with y0; vauto. }
                  rewrite <- collect_rel_seq.
                  { transitivity (mapper' ↑ ((⦗E_t'⦘
                      ⨾ (rf_t' ⨾ rmw_t')＊) ⨾ rf_t'
                        ⨾ ⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗E_t'⦘
                          ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^? ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘)).
                    { rewrite <- seqA.
                      rewrite collect_rel_seq with (rr := (⦗E_t'⦘ ⨾ (rf_t' ⨾ rmw_t')＊)).
                      { apply seq_mori.
                        { intros x y COND. destruct COND as (x0 & (EQ & (x1 & INE & MAP)) & COND).
                          apply rtE in COND. destruct COND as [EQ' | COND].
                          { destruct EQ' as (EQ' & TR).
                            unfold collect_rel. exists x1, x1. splits; vauto.
                            exists x1. splits; vauto. }
                          subst. assert (COND' := COND).
                          apply ct_end in COND. destruct COND as (x2 & COND1 &
                                  (x3 & y3 & PTH & M1 & M2)).
                          unfold collect_rel. exists x1, y3. splits; vauto.
                          exists x1. splits; vauto.
                          apply rtE. right.
                          assert (RESTR : rf_t' ⨾ rmw_t' ≡ restr_rel E_t' (rf_t' ⨾ rmw_t')).
                          { rewrite restr_relE. rewrite wf_rmwE, wf_rfE; vauto. basic_solver 21. }
                          assert (EQQ : mapper' ↑ (restr_rel E_t' (rf_t' ⨾ rmw_t'))⁺ ≡ (mapper' ↑ restr_rel E_t' (rf_t' ⨾ rmw_t'))⁺).
                          { apply collect_rel_ct_inj; vauto. }
                          rewrite <- RESTR in EQQ.
                          apply EQQ in COND'. destruct COND' as (x4 & y4 & PTH' & M3 & M4).
                          apply rsr_inj in M3, M4; vauto.
                          { apply ct_end in PTH'. destruct PTH' as (x5 & PTH' & PTH'').
                            destruct PTH'' as (x6 & P1 & P2).
                            apply wf_rmwE in P2; vauto. clear - P2.
                            destruct P2 as (y5 & P2 & (y6 & P3 & (EQ & P4))); vauto. }
                          { destruct PTH as (x5 & P1 & P2).
                            apply wf_rmwE in P2; vauto. clear - P2.
                            destruct P2 as (y5 & P2 & (y6 & P3 & (EQ & P4))); vauto. }
                          apply ct_begin in PTH'. destruct PTH' as (x5 & P1 & P2).
                          destruct P1 as (x6 & P3 & P4). apply wf_rfE in P3; vauto.
                          destruct P3 as (y5 & (EQ & P3) & P5); vauto. }
                        rewrite collect_rel_seq.
                        { apply seq_mori; vauto.
                          arewrite (⦗mapper' ↑₁ E_t'⦘ ⨾ ⦗mapper' ↑₁ E_t'⦘
                            ⨾ ⦗Rlx (WCore.G X_s')⦘ ⊆ ⦗mapper' ↑₁ E_t'⦘
                            ⨾ ⦗Rlx (WCore.G X_s')⦘ ⨾ ⦗mapper' ↑₁ E_t'⦘) by mode_solver.
                          rewrite <- seqA. rewrite <- id_inter.
                          transitivity (mapper' ↑ ((⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘) ⨾ ⦗E_t'⦘
                               ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^? ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘)).
                          { rewrite collect_rel_seq.
                            { apply seq_mori.
                              { intros x y COND. destruct COND as (EQ & COND); subst.
                                destruct COND as ((y0 & INE & MP) & C2).
                                red. exists y0, y0. splits; vauto.
                                exists y0. splits; vauto.
                                red. split; vauto.
                                unfold is_rlx in *. unfold mod in *.
                                rewrite <- rsr_lab; vauto. }
                              arewrite (⦗mapper' ↑₁ E_t'⦘ ⨾ (sb (WCore.G X_s') ⨾ ⦗F (WCore.G X_s')⦘)^?
                                  ⊆ ⦗mapper' ↑₁ E_t'⦘ ⨾ (sb (WCore.G X_s') ⨾ ⦗F (WCore.G X_s')⦘)^? ⨾ ⦗mapper' ↑₁ E_t'⦘).
                              { rewrite crE at 1.
                                rewrite seq_union_r. apply inclusion_union_l; [basic_solver 8|].
                                hahn_frame_l. rewrite crE. rewrite seq_union_l.
                                apply inclusion_union_r. right. rewrite seqA.
                                arewrite (sb (WCore.G X_s') ⊆ sb (WCore.G X_s') ⨾ ⦗acts_set (WCore.G X_s')⦘).
                                { rewrite wf_sbE. basic_solver. }
                                rewrite rsr_acts. rewrite EXTRA. basic_solver. }
                              arewrite (⦗mapper' ↑₁ E_t'⦘ ⨾ (sb (WCore.G X_s') ⨾ ⦗F (WCore.G X_s')⦘)^?
                                  ⊆ ⦗mapper' ↑₁ E_t'⦘ ⨾ (mapper' ↑ sb_t' ⨾ ⦗mapper' ↑₁ E_t'⦘ ⨾ ⦗F (WCore.G X_s')⦘)^?).
                              { rewrite crE at 1. rewrite seq_union_r.
                                apply inclusion_union_l; [basic_solver 8|].
                                hahn_frame_l.
                                arewrite (sb (WCore.G X_s') ⊆ sb (WCore.G X_s') ⨾ ⦗acts_set (WCore.G X_s')⦘).
                                { rewrite wf_sbE. basic_solver. }
                                rewrite rsr_acts. rewrite EXTRA. rewrite set_union_empty_r.
                                rewrite crE.
                                apply inclusion_union_r. right.
                                rewrite rsr_sb. rewrite !seq_union_l.
                                repeat apply inclusion_union_l.
                                { unfold swap_rel. rewrite collect_rel_union.
                                  rewrite seq_union_l. apply inclusion_union_l.
                                  { basic_solver 21. }
                                  rewrite collect_rel_cross. destruct INV'.
                                  arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t' ∩₁ E_t').
                                  { basic_solver. }
                                  rewrite rsr_b_t_is_r_or_w.
                                  arewrite_false ((mapper' ↑₁ (eq a_t ∩₁ E_t')) × (mapper' ↑₁ ((W_t' ∪₁ R_t') ∩₁ E_t'))
                                      ⨾ ⦗mapper' ↑₁ E_t'⦘ ⨾ ⦗F (WCore.G X_s')⦘); vauto.
                                  rewrite <- seqA. rewrite <- cross_inter_r. rewrite <- cross_inter_r.
                                  clear - rsr_lab.
                                  intros x y COND. destruct COND as (LT & RT); subst.
                                  destruct RT as [[MAP1 MAP2] FNC]. destruct MAP1 as [x0 [CONDS MAP]].
                                  rewrite <- MAP in FNC. unfold is_f in FNC.
                                  unfold compose in rsr_lab. unfold eq_dom in rsr_lab.
                                  specialize rsr_lab with x0.
                                  assert (EQ : lab (WCore.G X_s') (mapper' x0) = lab_t' x0).
                                  { apply rsr_lab. destruct CONDS; vauto. }
                                  rewrite EQ in FNC. destruct CONDS as [CONDS INE].
                                  unfold is_w, is_r in CONDS. clear - CONDS FNC.
                                  destruct CONDS; basic_solver. }
                                { rewrite EXTRA. basic_solver. }
                                rewrite EXTRA. basic_solver. }
                              rewrite <- seqA.
                              transitivity (mapper' ↑ ((⦗E_t'⦘ 
                                  ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^?) ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘)).
                              { rewrite collect_rel_seq.
                                { apply seq_mori.
                                  { intros x y COND. destruct COND as (x0 & (EQ & x1 & (INE & MP)) & PTH).
                                    destruct PTH as [EQQ | NEQ].
                                    { unfold collect_rel. exists x1, x1. splits; vauto.
                                      exists x1. splits; vauto. }
                                    destruct NEQ as (x2 & SB & (x3 & (EQ1 & (x4 & (INE' &MAP))) & (EQ2 & FNC))); subst.
                                    unfold collect_rel. exists x1, x4. splits; vauto.
                                    exists x1. splits; vauto.
                                    apply crE. right. exists x4. splits.
                                    { destruct SB as (x5 & x6 & (SB & M1 & M2)).
                                      apply rsr_inj in M1.
                                      { apply rsr_inj in M2. subst; vauto.
                                        { apply wf_sbE in SB. clear - SB.
                                          destruct SB as (y1 & INE & (y2 & SB & (EQ & INE'))); vauto. }
                                        vauto. }
                                      { apply wf_sbE in SB. clear - SB.
                                        destruct SB as (y1 & (EQ & INE') & RST); vauto. }
                                      vauto. }
                                    red. splits; vauto.
                                    unfold is_f in *. rewrite <- rsr_lab; vauto. }
                                  intros x y COND. destruct COND as (x0 & (EQ & (x1
                                          & INE & EQ1)) & (EQ2 & COND)); subst.
                                  red. exists x1, x1. splits; vauto.
                                  exists x1. splits; vauto.
                                  exists x1. splits; vauto.
                                  red. splits; vauto.
                                  unfold is_acq in *. unfold mod in *.
                                  destruct rsr_lab with x1; vauto. }
                                assert (IN1 : codom_rel (⦗E_t'⦘ ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^?) ⊆₁ E_t').
                                { clear. rewrite wf_sbE. basic_solver. }
                                assert (IN2 : dom_rel (⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘) ⊆₁ E_t').
                                { clear. basic_solver. }
                                rewrite IN1, IN2; basic_solver. }
                              apply collect_rel_mori; vauto.
                              rewrite !seqA; vauto. }
                            assert (IN1 : codom_rel (⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘) ⊆₁ E_t').
                            { clear. basic_solver. }
                            assert (IN2 : dom_rel (⦗E_t'⦘
                              ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^? ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘) ⊆₁ E_t').
                            { clear. basic_solver. }
                            rewrite IN1, IN2; basic_solver. }
                          apply collect_rel_mori; vauto.
                          apply seqA. }
                        assert (IN1 : codom_rel rf_t' ⊆₁ E_t').
                        { rewrite wf_rfE; basic_solver. }
                        assert (IN2 : dom_rel (⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗E_t'⦘
                             ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^? ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘) ⊆₁ E_t').
                        { clear; basic_solver. }
                        rewrite IN1, IN2; basic_solver. }
                      assert (IN1 : codom_rel (⦗E_t'⦘ ⨾ (rf_t' ⨾ rmw_t')＊) ⊆₁ E_t').
                      { rewrite wf_rmwE; vauto. rewrite rtE. rewrite ct_end.
                        basic_solver. }
                      assert (IN2 : dom_rel (rf_t' ⨾ ⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗E_t'⦘
                             ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^? ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘) ⊆₁ E_t').
                      { rewrite wf_rfE; basic_solver. }
                      rewrite IN1, IN2; basic_solver. }
                    apply collect_rel_mori; vauto.
                    apply seqA. }
                  assert (IN1 : codom_rel rf_t' ⊆₁ E_t').
                  { rewrite wf_rfE; basic_solver. }
                  assert (IN2 : dom_rel rmw_t' ⊆₁ E_t').
                  { rewrite wf_rmwE; basic_solver. }
                  rewrite IN1, IN2; basic_solver. }
                assert (IN1 : codom_rel (⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗W_t'⦘) ⊆₁ E_t').
                { clear. basic_solver. }
                assert (IN2 : dom_rel (⦗E_t'⦘ ⨾ (rf_t' ⨾ rmw_t')＊ ⨾ rf_t'
                    ⨾ ⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗E_t'⦘ ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^?
                             ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘) ⊆₁ E_t').
                { clear. basic_solver. }
                rewrite IN1, IN2; basic_solver. }
              apply collect_rel_mori; vauto.
              rewrite !seqA; vauto. }
            assert (IN1 : codom_rel ((⦗F G_t'⦘ ⨾ sb_t')^? ⨾ ⦗E_t'⦘) ⊆₁ E_t').
            { clear. basic_solver. }
            assert (IN2 : dom_rel (⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗W_t'⦘ ⨾ ⦗E_t'⦘
                ⨾ (rf_t' ⨾ rmw_t')＊ ⨾ rf_t' ⨾ ⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘
                  ⨾ ⦗E_t'⦘ ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^? ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘) ⊆₁ E_t').
            { clear. basic_solver. }
            rewrite IN1, IN2; basic_solver. }
          apply collect_rel_mori; vauto.
          rewrite seqA.
          arewrite (⦗E_t'⦘ ⨾ ⦗E_t'⦘ ⊆ ⦗E_t'⦘) by basic_solver. }
        assert (IN1 : codom_rel ⦗Rel G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
        { clear. basic_solver. }
        assert (IN2 : dom_rel ((⦗F G_t'⦘ ⨾ sb_t')^? ⨾ ⦗E_t'⦘
          ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗W_t'⦘ ⨾ ⦗E_t'⦘ ⨾ (rf_t' ⨾ rmw_t')＊ ⨾ rf_t'
            ⨾ ⦗E_t'⦘ ⨾ ⦗Rlx G_t'⦘ ⨾ ⦗E_t'⦘ ⨾ (sb_t' ⨾ ⦗F G_t'⦘)^?
              ⨾ ⦗E_t'⦘ ⨾ ⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘) ⊆₁ E_t').
        { rewrite wf_sbE; vauto. clear. basic_solver. }
        rewrite IN1, IN2; basic_solver. }
      apply collect_rel_mori; vauto.
      clear. arewrite_id (⦗E_t'⦘). rels. }
    assert (IND2 : mapper' ↑ (sb_t' ∩ same_loc_t' ∪ rpo_t' ∪ sw G_t')⁺
          ⨾ (sb G_s' ∩ same_loc (lab G_s') ∪ rpo G_s' ∪ sw G_s')
      ⊆ mapper' ↑ (sb_t' ∩ same_loc_t' ∪ rpo_t' ∪ sw G_t')⁺).
    { assert (TRIN : mapper' ↑ (sb_t' ∩ same_loc_t' ∪ rpo_t' ∪ sw G_t')⁺
        ⨾ mapper' ↑ (sb_t' ∩ same_loc_t' ∪ rpo_t' ∪ sw G_t')⁺
              ⊆ mapper' ↑ (sb_t' ∩ same_loc_t' ∪ rpo_t' ∪ sw G_t')⁺).
      { intros x y PATH. destruct PATH as (x0 & P1 & P2).
        unfold collect_rel in P1, P2. unfold collect_rel.
        destruct P1 as (x' & x0' & (P1 & M1 & M2)).
        destruct P2 as (x0'' & y' & (P2 & M3 & M4)).
        exists x', y'. splits; vauto.
        assert (EQ : x0'' = x0').
        { destruct SIMREL'. apply rsr_inj; vauto.
          { apply ct_begin in P2.
            destruct P2 as (x1 & P2 & P3).
            assert (P2' : rhb (G_t') x0'' x1) by vauto.
            destruct INV.
            apply wf_rhbE in P2'; vauto.
            destruct P2' as (x2 & INE & REST).
            apply INE. }
          apply ct_end in P1.
          destruct P1 as (x1 & P1 & P1').
          assert (P2' : rhb (G_t') x1 x0') by vauto.
          destruct INV.
          apply wf_rhbE in P2'; vauto.
          destruct P2' as (x2 & P3 & (x3 & P4 & (EQ & P5))); vauto. }
        subst. apply ct_ct.
        unfold seq. exists x0'. splits; vauto. }
      rewrite <- TRIN at 2. apply seq_mori; vauto. }
    apply inclusion_t_ind_right; vauto. }
  admit. (*TODO : add*)
Admitted.

End ExecNotANotB.