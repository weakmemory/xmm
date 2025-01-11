Require Import ReordSimrel ReorderingEq.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import PorfPrefix.

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
      change (WCore.G X_s') with G_s'.
      assert (XIN' : extra_a X_t' a_t b_t b_t x).
      { now apply EXEQ. }
      arewrite (⦗eq x ∩₁ R G_s'⦘ ⊆ ⦗extra_a X_t a_t b_t b_t ∩₁ R_s⦘).
      { apply eqv_rel_mori. clear - XIN XIN' ENEXA.
        unfolder. ins. desf. splits; ins.
        unfold is_r in *. now rewrite updo in * by congruence. }
      { rewrite SRF'', SRFE, (rsr_as_val SIMREL).
        clear - NOTIN. unfolder. ins. desf.
        unfold same_val, val in *.
        now rewrite !updo by congruence. }
      { intro FALSO.
        enough (FALSO' : same_loc_s a_t x).
        { eapply eba_loc; eauto.
          apply (rsr_as SIMREL); eauto. }
        apply EXEQ in XIN.
        clear - E_NOT_A ENEXA FALSO XIN. ins.
        unfold same_loc, loc in FALSO.
        rewrite !updo in FALSO; auto.
        congruence. }
      unfold is_acq, mod. ins.
      rewrite updo; [| apply EXEQ in XIN; congruence].
      now eapply eba_nacq, (rsr_as SIMREL). }
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
  admit.
Admitted.

End ExecNotANotB.