Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import xmm_s_hb.
Require Import Lia.
From xmm Require Import Reordering.
From xmm Require Import ThreadTrace.
From xmm Require Import Programs.
From xmm Require Import SequentBase.
From xmm Require Import ConsistencyMonotonicity.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import Setoid Morphisms Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section SimrelStep.

Variable X_t X_t' X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.
Variable mapper_rev : actid -> actid.

Variable e : actid.
Variable l : label.

Variable thrdle : relation thread_id.

Variable ptc_1 ptc_2 : program_trace.

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

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Hypothesis MAPREV : eq_dom E_t (mapper_rev ∘ mapper) id.
Hypothesis PROGSEQ : program_trace_sequented ptc_1 ptc_2 t_1 t_2.
Hypothesis WFT : Wf G_t.

Definition t_12_len := length (ptc_2 t_2).
Definition t_1_len := length (ptc_1 t_1).
Definition t_2_len := length (ptc_1 t_2).

Lemma simrel_step_e_t1
    (T1 : tid e = t_1)
    (IND: index e < t_1_len)
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' X_s',
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper e e).
  set (mapper_rev' := upd mapper_rev e e).
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    clear - ENOTIN XINE. rewrite updo.
    all: congruence. }
  assert (MAPER_E : mapper' ↑₁ eq e ≡₁ eq e).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { clear - MAPEQ. now apply set_collect_eq_dom. }
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq e) by apply ADD.
  assert (MAPREVDOM : E_t ≡₁ mapper_rev ↑₁ E_s).
  { rewrite (seq_acts SIMREL). split.
    { unfolder. intros x XINE.
      exists (mapper x). splits; vauto.
      apply MAPREV; vauto. }
    unfolder. intros x (y & XINE & YEQ).
    destruct XINE as (x0 & (INE & MAPPED)).
    rewrite <- MAPPED in YEQ. rewrite <- YEQ.
    assert (INE' : E_t x0) by vauto.
    apply MAPREV in INE. clear - INE INE'.
    unfold compose in INE. rewrite INE.
    basic_solver. }
  assert (MEPERREV_E : mapper_rev' ↑₁ eq e ≡₁ eq e).
  { subst mapper_rev'. rewrite set_collect_eq. now rupd. }
  assert (NEWE :
  << NINIT : ~is_init e >> /\
  << NOTIN : ~E_s e >> /\
  << TID : tid e = t_1 >>). 
  (* /\
  << NEWSB : ⦗E_s ∪₁ eq e⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq e⦘ ≡
          sb_s ∪ WCore.sb_delta e E_s >>). *)
  { unfold NW; splits; vauto.
    { intro FALSO. unfold is_init in FALSO.
      unfold tid in T1. clear - T1 FALSO NINIT1.
      basic_solver. }
    intro FALSO. destruct ADD.
    assert (CDD : e = mapper' e).
    { unfold mapper'. rewrite upds; vauto. }
    rewrite CDD in FALSO.
    apply (seq_acts SIMREL) in FALSO.
    destruct FALSO as [e' [C1 C2]].
    admit. (* TODO : Discuss *)}
  (*  { unfold sb.
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
    rewrite <- EQACTS. apply ADD. } *)
  unfold NW in NEWE.
  destruct NEWE as (NINIT & NOTIN & TID).

  set (G_s' := {|
  acts_set := mapper' ↑₁ E_t';
    threads_set := threads_set G_s;
    lab := lab_t' ∘ mapper_rev';
    rf := mapper' ↑ rf_t';
    co := mapper' ↑ co_t';
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_t';
    ctrl := ctrl_t';
    data := data_t';
    addr := addr_t';
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists mapper', X_s'.
  assert (SIMRELQ : seq_simrel X_s' X_t' (tid e) t_2 mapper').
  { constructor; vauto; simpl; try basic_solver 6.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { clear - SIMREL MAPEQ.
        unfolder. ins. apply (seq_inj SIMREL); ins.
        now rewrite <- !MAPEQ. }
      { clear. basic_solver. }
      rewrite MAPER_E, MAPSUB, (seq_codom SIMREL).
      clear - NOTIN. basic_solver. }
    { intros ev INE' TIDCOND.
      destruct classic with (ev = e) as [EQ | NEQ].
      { subst ev. unfold mapper'. rewrite upds; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_tid_1 SIMREL); vauto.
      apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto.
      unfold mapper' in TIDCOND. rewrite updo in TIDCOND; vauto. }
    { intros ev INE' TIDCOND.
      destruct classic with (ev = e) as [EQ | NEQ]; vauto.
      rewrite TID. apply (seq_tid_2 SIMREL); vauto.
      { apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto. }
      unfold mapper'. rewrite updo; vauto. }
    { intros x COND. unfold compose.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper', mapper_rev'.
        rewrite !upds; vauto. }
      unfold mapper', mapper_rev'.
      rewrite !updo; vauto.
      { unfold compose in MAPREV. rewrite MAPREV.
        { basic_solver. }
        apply EQACTS in COND.
        destruct COND as [C1 | C2]; vauto. }
        rewrite updo; vauto.
        assert (INE : E_t x).
        { apply EQACTS in COND.
          destruct COND as [C1 | C2]; vauto. }
        intros FALSE.
        assert (PROP : E_s e).
        { rewrite <- FALSE.
          apply (seq_codom SIMREL); vauto. }
        desf. }
    { admit. (*TODO : po-work*) }
    { rewrite (seq_threads SIMREL).
      destruct ADD. rewrite add_event_threads; vauto. }
    unfold mapper'. intros x COND.
    destruct classic with (x = e) as [EQ | NEQ].
    { subst x. rewrite upds; vauto. }
    rewrite updo; vauto.
    apply (seq_init SIMREL); vauto. }
  splits.
  { rewrite <- TID; vauto. }
  constructor.
  { unfold WCore.add_event.
    exists (option_map mapper' r), (mapper' ↑₁ R1),
        (option_map mapper' w),
        (mapper' ↑₁ W1),
        (mapper' ↑₁ W2).
    apply add_event_to_wf; simpl; vauto.
    { apply sico_init_acts_s with
            (X_t := X_t) (mapper := mapper).
      { constructor. all : apply SIMREL. }
      destruct ADD. apply add_event_init. }
    { unfold mapper'. rewrite upds. exact NOTIN. }
    { unfold mapper'. rewrite upds; vauto. }
    { unfold mapper'. rewrite upds.
      rewrite TID. basic_solver. }
    { rewrite EQACTS. rewrite set_collect_union.
      rewrite MAPER_E, MAPSUB. rewrite (seq_acts SIMREL).
      unfold mapper'. rewrite upds. basic_solver. }
    { unfold mapper', mapper_rev'.
      destruct ADD. rewrite add_event_lab.
      rewrite upds. destruct SIMREL.
      apply functional_extensionality.
      intros x.
      destruct (classic (x = e)) as [EQ | NEQ].
      { subst x. rewrite upds.
        unfold compose. rewrite !upds; vauto. }
      rewrite updo; vauto. unfold compose.
      rewrite updo at 1; vauto.
      { rewrite updo; vauto.
        admit. }
      rewrite updo; vauto.
      admit. }
    { destruct ADD. rewrite add_event_rf.
      rewrite !collect_rel_union.
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE); vauto. }
      rewrite (seq_rf SIMREL).
      arewrite (mapper' ↑ WCore.rf_delta_R e w
                    ≡ WCore.rf_delta_R (mapper' e)
                        (option_map mapper' w)).
      { unfold WCore.rf_delta_R.
        rewrite collect_rel_cross.
        apply cross_more.
        { clear. unfold option_map. basic_solver. }
        clear. unfold option_map. basic_solver. }
      arewrite (mapper' ↑ WCore.rf_delta_W e R1
                    ≡ WCore.rf_delta_W (mapper' e) (mapper' ↑₁ R1)).
      { unfold WCore.rf_delta_W.
        rewrite collect_rel_cross.
        apply cross_more.
        { clear. unfold option_map. basic_solver. }
        clear. unfold option_map. basic_solver. }
      vauto. }
    { destruct ADD. rewrite add_event_co.
      rewrite !collect_rel_union.
      arewrite (mapper' ↑ co_t ≡ mapper ↑ co_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_coE); vauto. }
      rewrite (seq_co SIMREL).
      arewrite (mapper' ↑ WCore.co_delta e W1 W2
                    ≡ WCore.co_delta (mapper' e) (mapper' ↑₁ W1)
                    (mapper' ↑₁ W2)).
      { unfold WCore.co_delta. rewrite collect_rel_union.
        apply union_more.
        { rewrite collect_rel_cross.
          apply cross_more; vauto.
          clear. basic_solver. }
        rewrite collect_rel_cross.
        apply cross_more; vauto.
        clear. basic_solver. }
      vauto. }
    { rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD),
      collect_rel_union.
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
      apply (wf_rmwE); vauto. }
      now rewrite (seq_rmw SIMREL). }
    { destruct ADD. rewrite add_event_data.
      rewrite (seq_data SIMREL); vauto. }
    { destruct ADD. rewrite add_event_addr.
      rewrite (seq_addr SIMREL); vauto. }
    { destruct ADD. rewrite add_event_ctrl.
      rewrite (seq_ctrl SIMREL); vauto. }
    { destruct ADD. rewrite add_event_rmw_dep.
      rewrite (seq_rmw_dep SIMREL); vauto. }
    { admit. (* po-work *) }
    { destruct ADD. vauto. }
    admit. (* TODO : add? *) }
  { unfold rf_complete.
    rewrite (seq_acts SIMRELQ), (seq_rf SIMRELQ).
    unfold rf_complete in RFC. rewrite EQACTS.
    rewrite !set_collect_union, MAPER_E, MAPSUB.
    rewrite set_inter_union_l.
    rewrite set_subset_union_l; split.
    { unfold rf_complete in RFC.
      rewrite <- set_collect_codom, <- RFC.
      unfolder. intros x ((x' & INE & XEQ) & ISR).
      exists x'. splits; try basic_solver.
      { apply EQACTS; vauto. }
      subst x. unfold is_r in *.
      assert (CHNG : WCore.G X_s' = G_s') by vauto.
      rewrite CHNG in ISR. unfold G_s' in ISR; ins.
      unfold compose in ISR.
      assert (NEQ : x' <> e).
      { intros FALSE. subst x'. basic_solver 8. }
      assert (NEQ' : mapper x' <> e).
      { intros FALSE. destruct NOTIN.
        rewrite <- FALSE. apply (seq_codom SIMREL); vauto. }
      assert (EQQ : mapper_rev' (mapper x') = x').
      { unfold eq_dom in MAPREV. specialize MAPREV with x'.
        apply MAPREV in INE. unfold compose in INE.
        unfold mapper_rev'. rewrite updo; vauto. }
      rewrite EQQ in ISR; vauto. }
    rewrite <- set_collect_codom. rewrite <- RFC.
    intros x (EQ & RD). subst x.
    unfold set_collect. exists e. splits; vauto.
    { split.
      { apply EQACTS. basic_solver. }
      assert (FEQ : WCore.G X_s' = G_s') by vauto.
      rewrite FEQ in RD. unfold G_s' in RD.
      simpl in RD. clear - RD. unfold compose in RD.
      unfold is_r in RD. unfold mapper_rev' in RD.
      rewrite upds in RD; vauto. }
    unfold mapper'. rewrite upds. vauto. }
  apply XmmCons.monoton_cons with (G_t := G_t')
          (m := mapper'); vauto; try apply SIMRELQ.
  { admit. (* TODO : po-work? *) }
  { admit. (* TODO : po-work? *) }
  all : admit. (* TODO : add? *)
Admitted.

Lemma simrel_step_e_t2
    (T1 : tid e = t_1)
    (IND: index e >= t_1_len)
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' X_s',
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper e (ThreadEvent t_2 (index e - t_1_len))).
  set (mapper_rev' := upd mapper_rev (ThreadEvent t_2 (index e - t_1_len)) e).
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (EMAPNOTIN : ~E_s (ThreadEvent t_2 (index e - t_1_len))).
  { admit. (* TODO : Discuss *) }
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    clear - EMAPNOTIN ENOTIN XINE. rewrite updo; vauto.
    all: congruence. }
  assert (MAPREVEQ : eq_dom E_s mapper_rev' mapper_rev).
  { subst mapper_rev'. unfolder. intros x XINE.
    clear - EMAPNOTIN ENOTIN XINE. rewrite updo; vauto.
    all: congruence. }
  assert (MAPER_E : mapper' ↑₁ eq e ≡₁ eq (ThreadEvent t_2 (index e - t_1_len))).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { clear - MAPEQ. now apply set_collect_eq_dom. }
  assert (MAPREVSUB : mapper_rev' ↑₁ E_s ≡₁ mapper_rev ↑₁ E_s).
  { clear - MAPREVEQ. now apply set_collect_eq_dom. }
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq e) by apply ADD.
  assert (NEWE :
    << NINIT : ~is_init (ThreadEvent t_2 (index e - t_1_len)) >> /\
    << NOTIN : ~E_s (ThreadEvent t_2 (index e - t_1_len)) >> /\
    << TID : tid (ThreadEvent t_2 (index e - t_1_len)) = t_2 >>). 
    { unfold NW; splits; vauto. }
  unfold NW in NEWE. destruct NEWE as (NINIT & NOTIN & TID).

  set (G_s' := {|
    acts_set := E_s ∪₁ eq (ThreadEvent t_2 (index e - t_1_len));
    threads_set := threads_set G_s;
    lab := lab_t' ∘ mapper_rev';
    rf := mapper' ↑ rf_t';
    co := mapper' ↑ co_t';
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_t';
    ctrl := ctrl_t';
    data := data_t';
    addr := addr_t';
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists mapper', X_s'.
  assert (SIMRELQ : seq_simrel X_s' X_t' t_1 t_2 mapper').
  { constructor; vauto; simpl; try basic_solver 6.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { clear - SIMREL MAPEQ.
        unfolder. ins. apply (seq_inj SIMREL); ins.
        now rewrite <- !MAPEQ. }
      { clear. basic_solver. }
      rewrite MAPER_E, MAPSUB, (seq_codom SIMREL).
      unfold set_disjoint. intros x INE' INE.
      assert (CC : E_t (mapper_rev' x)).
      { rewrite <- INE. unfold mapper_rev'.
        rewrite upds; vauto. }
      destruct MAPREVSUB as [IN OUT].
      destruct IN with x.
      { unfold set_collect. exists x; split; vauto. }
      destruct H as [INEE MAPR].
      rewrite <- INE in CC.
      unfold mapper_rev' in CC.
      rewrite updo in CC; vauto. }
    { intros ev INE' TIDCOND.
      destruct classic with (ev = e) as [EQ | NEQ].
      { subst ev. unfold mapper'. rewrite upds; vauto.
        unfold mapper' in TIDCOND. rewrite upds in TIDCOND; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_tid_1 SIMREL); vauto.
      apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto.
      unfold mapper' in TIDCOND. rewrite updo in TIDCOND; vauto. }
    { intros ev INE' TIDCOND. destruct SIMREL.
      destruct classic with (ev = e) as [EQ | NEQ].
      { subst e; vauto. }
      assert (EINN : E_t ev).
      { apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto.
        clear - C2 NEQ. basic_solver. }
      specialize seq_tid_2 with ev.
      apply seq_tid_2 in EINN; vauto.
      unfold mapper' in TIDCOND. rewrite updo in TIDCOND; vauto. }
    { intros x COND. unfold compose.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper', mapper_rev'.
        rewrite !upds; vauto. }
      unfold mapper', mapper_rev'.
      rewrite !updo; vauto.
      { unfold compose in MAPREV. rewrite MAPREV.
        { basic_solver. }
        apply EQACTS in COND.
        destruct COND as [C1 | C2]; vauto. }
      rewrite updo; vauto.
      assert (INE : E_t x).
      { apply EQACTS in COND.
        destruct COND as [C1 | C2]; vauto. }
      intros FALSE.
      assert (PROP : E_s (ThreadEvent t_2 (index e - t_1_len))).
        { rewrite <- FALSE.
          apply (seq_codom SIMREL); vauto. }
        desf. }
    { rewrite EQACTS. rewrite set_collect_union.
      rewrite MAPER_E, MAPSUB, (seq_acts SIMREL); vauto. }
    { admit. (*TODO : po-work*) }
    { rewrite (seq_threads SIMREL).
      destruct ADD. rewrite add_event_threads; vauto. }
    { unfold mapper'. intros x COND.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. clear - T1 COND NINIT1.
        unfold tid in T1. unfold is_init in COND.
        desf. basic_solver 8. }
      rewrite updo; vauto.
      apply (seq_init SIMREL); vauto. }
    rewrite EQACTS. rewrite set_collect_union.
    rewrite MAPER_E, MAPSUB, (seq_acts SIMREL); vauto. }
  splits; vauto.
  constructor.
  { unfold WCore.add_event.
    exists (option_map mapper' r), (mapper' ↑₁ R1),
        (option_map mapper' w),
        (mapper' ↑₁ W1),
        (mapper' ↑₁ W2).
    apply add_event_to_wf; simpl; vauto.
    { apply sico_init_acts_s with
          (X_t := X_t) (mapper := mapper).
      { constructor. all : apply SIMREL. }
      destruct ADD. apply add_event_init. }
    { unfold mapper'. rewrite upds; vauto. }
    { unfold mapper'. rewrite upds; vauto. }
    { unfold mapper'. rewrite upds.
      clear - NINIT2. unfold tid; vauto. }
    { unfold mapper'. rewrite upds. basic_solver. }
    { unfold mapper', mapper_rev'.
      destruct ADD. rewrite add_event_lab.
      rewrite upds. admit. }
    { destruct ADD. rewrite add_event_rf.
      rewrite !collect_rel_union.
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE); vauto. }
      rewrite (seq_rf SIMREL).
      arewrite (mapper' ↑ WCore.rf_delta_R e w
                    ≡ WCore.rf_delta_R (mapper' e)
                        (option_map mapper' w)).
      { unfold WCore.rf_delta_R.
        rewrite collect_rel_cross.
        apply cross_more.
        { clear. unfold option_map. basic_solver. }
        clear. unfold option_map. basic_solver. }
      arewrite (mapper' ↑ WCore.rf_delta_W e R1
                    ≡ WCore.rf_delta_W (mapper' e) (mapper' ↑₁ R1)).
      { unfold WCore.rf_delta_W.
        rewrite collect_rel_cross.
        apply cross_more.
        { clear. unfold option_map. basic_solver. }
        clear. unfold option_map. basic_solver. }
      vauto. }
    { destruct ADD. rewrite add_event_co.
      rewrite !collect_rel_union.
      arewrite (mapper' ↑ co_t ≡ mapper ↑ co_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_coE); vauto. }
      rewrite (seq_co SIMREL).
      arewrite (mapper' ↑ WCore.co_delta e W1 W2
                    ≡ WCore.co_delta (mapper' e) (mapper' ↑₁ W1)
                    (mapper' ↑₁ W2)).
      { unfold WCore.co_delta. rewrite collect_rel_union.
        apply union_more.
        { rewrite collect_rel_cross.
          apply cross_more; vauto.
          clear. basic_solver. }
        rewrite collect_rel_cross.
        apply cross_more; vauto.
        clear. basic_solver. }
      vauto. }
    { rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD),
      collect_rel_union.
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
      apply (wf_rmwE); vauto. }
      now rewrite (seq_rmw SIMREL). }
    { destruct ADD. rewrite add_event_data.
      rewrite (seq_data SIMREL); vauto. }
    { destruct ADD. rewrite add_event_addr.
      rewrite (seq_addr SIMREL); vauto. }
    { destruct ADD. rewrite add_event_ctrl.
      rewrite (seq_ctrl SIMREL); vauto. }
    { destruct ADD. rewrite add_event_rmw_dep.
      rewrite (seq_rmw_dep SIMREL); vauto. }
    { admit. (* po-work *) }
    { destruct ADD. vauto. }
      admit. (* TODO : add? *) }
  { unfold rf_complete.
    rewrite (seq_acts SIMRELQ), (seq_rf SIMRELQ).
    unfold rf_complete in RFC. rewrite EQACTS.
    rewrite !set_collect_union, MAPER_E, MAPSUB.
    rewrite set_inter_union_l.
    rewrite set_subset_union_l; split.
    { unfold rf_complete in RFC.
      rewrite <- set_collect_codom, <- RFC.
      unfolder. intros x ((x' & INE & XEQ) & ISR).
      exists x'. splits; try basic_solver.
      { apply EQACTS; vauto. }
      subst x. unfold is_r in *.
      assert (CHNG : WCore.G X_s' = G_s') by vauto.
      rewrite CHNG in ISR. unfold G_s' in ISR; ins.
      unfold compose in ISR.
      assert (NEQ : x' <> e).
      { intros FALSE. subst x'. basic_solver 8. }
      assert (NEQ' : mapper x' <> (ThreadEvent t_2 (index e - t_1_len))).
      { intros FALSE. destruct NOTIN.
        rewrite <- FALSE. apply (seq_codom SIMREL); vauto. }
      assert (EQQ : mapper_rev' (mapper x') = x').
      { unfold eq_dom in MAPREV. specialize MAPREV with x'.
        apply MAPREV in INE. unfold compose in INE.
        unfold mapper_rev'. rewrite updo; vauto. }
      rewrite EQQ in ISR; vauto. }
    unfolder. intros rd (RD1 & RD2).
    admit. }
  apply XmmCons.monoton_cons with (G_t := G_t')
        (m := mapper'); vauto; try apply SIMRELQ.
  { admit. (* TODO : po-work? *) }
  { admit. (* TODO : po-work? *) }
  all : admit. (* TODO : add? *)
Admitted.

Lemma simrel_step_e_else
    (T1 : tid e <> t_1)
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' X_s',
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper e e).
  set (mapper_rev' := upd mapper_rev e e).
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    clear - ENOTIN XINE. rewrite updo.
    all: congruence. }
  assert (MAPER_E : mapper' ↑₁ eq e ≡₁ eq e).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { clear - MAPEQ. now apply set_collect_eq_dom. }
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq e) by apply ADD.
  assert (NEWE :
  << NINIT : ~is_init e >> /\
  << NOTIN : ~E_s e >> /\
  << TID : tid e <> t_1 >>).
  { unfold NW; splits; vauto.
    { intro FALSO. unfold is_init in FALSO.
      destruct ADD; vauto. }
    intro FALSO. destruct ADD.
    assert (CDD : e = mapper' e).
    { unfold mapper'. rewrite upds; vauto. }
    rewrite CDD in FALSO.
    apply (seq_acts SIMREL) in FALSO.
    destruct FALSO as [e' [C1 C2]].
    admit. (* TODO : Discuss *) }
  unfold NW in NEWE. destruct NEWE as (NINIT & NOTIN & TID).

  set (G_s' := {|
  acts_set := mapper' ↑₁ E_t';
    threads_set := threads_set G_s;
    lab := lab_t' ∘ mapper_rev';
    rf := mapper' ↑ rf_t';
    co := mapper' ↑ co_t';
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_t';
    ctrl := ctrl_t';
    data := data_t';
    addr := addr_t';
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists mapper', X_s'.
  assert (SIMRELQ : seq_simrel X_s' X_t' t_1 t_2 mapper').
  { constructor; vauto; simpl; try basic_solver 6.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { clear - SIMREL MAPEQ.
        unfolder. ins. apply (seq_inj SIMREL); ins.
        now rewrite <- !MAPEQ. }
      { clear. basic_solver. }
      rewrite MAPER_E, MAPSUB, (seq_codom SIMREL).
      clear - NOTIN. basic_solver. }
    { intros ev INE' TIDCOND.
      destruct classic with (ev = e) as [EQ | NEQ].
      { subst ev. unfold mapper'. rewrite upds; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_tid_1 SIMREL); vauto.
      apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto.
      unfold mapper' in TIDCOND. rewrite updo in TIDCOND; vauto. }
    { intros ev INE' TIDCOND.
      destruct classic with (ev = e) as [EQ | NEQ].
      { unfold mapper' in TIDCOND.
        rewrite EQ in TIDCOND.
        rewrite upds in TIDCOND.
        admit. (* TODO : problem *) }
      destruct SIMREL.
      assert (NINE : E_t ev).
      { apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto. }
      specialize seq_tid_2 with ev.
      apply seq_tid_2 in NINE; vauto.
      unfold mapper'. rewrite updo; vauto. }
    { intros x COND. unfold compose.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper', mapper_rev'.
        rewrite !upds; vauto. }
      unfold mapper', mapper_rev'.
      rewrite !updo; vauto.
      { unfold compose in MAPREV. rewrite MAPREV.
        { basic_solver. }
        apply EQACTS in COND.
        destruct COND as [C1 | C2]; vauto. }
        rewrite updo; vauto.
        assert (INE : E_t x).
        { apply EQACTS in COND.
          destruct COND as [C1 | C2]; vauto. }
        intros FALSE.
        assert (PROP : E_s e).
        { rewrite <- FALSE.
          apply (seq_codom SIMREL); vauto. }
        desf. }
    { admit. (*TODO : po-work*) }
    { rewrite (seq_threads SIMREL).
      destruct ADD. rewrite add_event_threads; vauto. }
    unfold mapper'. intros x COND.
    destruct classic with (x = e) as [EQ | NEQ].
    { subst x. rewrite upds; vauto. }
    rewrite updo; vauto.
    apply (seq_init SIMREL); vauto. }
  split; vauto. constructor.
  { unfold WCore.add_event.
    exists (option_map mapper' r), (mapper' ↑₁ R1),
        (option_map mapper' w),
        (mapper' ↑₁ W1),
        (mapper' ↑₁ W2).
    apply add_event_to_wf; simpl; vauto.
    { apply sico_init_acts_s with
          (X_t := X_t) (mapper := mapper).
      { constructor. all : apply SIMREL. }
      destruct ADD. apply add_event_init. }
    { unfold mapper'. rewrite upds. exact NOTIN. }
    { unfold mapper'. rewrite upds; vauto. }
    { unfold mapper'. rewrite upds.
      destruct ADD; vauto. }
    { rewrite EQACTS. rewrite set_collect_union.
      rewrite MAPER_E, MAPSUB. rewrite (seq_acts SIMREL).
      unfold mapper'. rewrite upds. basic_solver. }
    { unfold mapper', mapper_rev'.
      destruct ADD. rewrite add_event_lab.
      rewrite upds. admit. }
    { destruct ADD. rewrite add_event_rf.
      rewrite !collect_rel_union.
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE); vauto. }
      rewrite (seq_rf SIMREL).
      arewrite (mapper' ↑ WCore.rf_delta_R e w
                    ≡ WCore.rf_delta_R (mapper' e)
                        (option_map mapper' w)).
      { unfold WCore.rf_delta_R.
        rewrite collect_rel_cross.
        apply cross_more.
        { clear. unfold option_map. basic_solver. }
        clear. unfold option_map. basic_solver. }
      arewrite (mapper' ↑ WCore.rf_delta_W e R1
                    ≡ WCore.rf_delta_W (mapper' e) (mapper' ↑₁ R1)).
      { unfold WCore.rf_delta_W.
        rewrite collect_rel_cross.
        apply cross_more.
        { clear. unfold option_map. basic_solver. }
        clear. unfold option_map. basic_solver. }
      vauto. }
    { destruct ADD. rewrite add_event_co.
      rewrite !collect_rel_union.
      arewrite (mapper' ↑ co_t ≡ mapper ↑ co_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_coE); vauto. }
      rewrite (seq_co SIMREL).
      arewrite (mapper' ↑ WCore.co_delta e W1 W2
                    ≡ WCore.co_delta (mapper' e) (mapper' ↑₁ W1)
                    (mapper' ↑₁ W2)).
      { unfold WCore.co_delta. rewrite collect_rel_union.
        apply union_more.
        { rewrite collect_rel_cross.
          apply cross_more; vauto.
          clear. basic_solver. }
        rewrite collect_rel_cross.
        apply cross_more; vauto.
        clear. basic_solver. }
      vauto. }
    { rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD),
      collect_rel_union.
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
      apply (wf_rmwE); vauto. }
      now rewrite (seq_rmw SIMREL). }
    { destruct ADD. rewrite add_event_data.
      rewrite (seq_data SIMREL); vauto. }
    { destruct ADD. rewrite add_event_addr.
      rewrite (seq_addr SIMREL); vauto. }
    { destruct ADD. rewrite add_event_ctrl.
      rewrite (seq_ctrl SIMREL); vauto. }
    { destruct ADD. rewrite add_event_rmw_dep.
      rewrite (seq_rmw_dep SIMREL); vauto. }
    { admit. (* po-work *) }
    { destruct ADD. vauto. }
    admit. (* TODO : add? *) }
  { unfold rf_complete.
    rewrite (seq_acts SIMRELQ), (seq_rf SIMRELQ).
    unfold rf_complete in RFC. rewrite EQACTS.
    rewrite !set_collect_union, MAPER_E, MAPSUB.
    rewrite set_inter_union_l.
    rewrite set_subset_union_l; split.
    { unfold rf_complete in RFC.
      rewrite <- set_collect_codom, <- RFC.
      unfolder. intros x ((x' & INE & XEQ) & ISR).
      exists x'. splits; try basic_solver.
      { apply EQACTS; vauto. }
      subst x. unfold is_r in *.
      assert (CHNG : WCore.G X_s' = G_s') by vauto.
      rewrite CHNG in ISR. unfold G_s' in ISR; ins.
      unfold compose in ISR.
      assert (NEQ : x' <> e).
      { intros FALSE. subst x'. basic_solver 8. }
      assert (NEQ' : mapper x' <> e).
      { intros FALSE. destruct NOTIN.
        rewrite <- FALSE. apply (seq_codom SIMREL); vauto. }
      assert (EQQ : mapper_rev' (mapper x') = x').
      { unfold eq_dom in MAPREV. specialize MAPREV with x'.
        apply MAPREV in INE. unfold compose in INE.
        unfold mapper_rev'. rewrite updo; vauto. }
      rewrite EQQ in ISR; vauto. }
    rewrite <- set_collect_codom. rewrite <- RFC.
    intros x (EQ & RD). subst x.
    unfold set_collect. exists e. splits; vauto.
    { split.
      { apply EQACTS. basic_solver. }
      assert (FEQ : WCore.G X_s' = G_s') by vauto.
      rewrite FEQ in RD. unfold G_s' in RD.
      simpl in RD. clear - RD. unfold compose in RD.
      unfold is_r in RD. unfold mapper_rev' in RD.
      rewrite upds in RD; vauto. }
    unfold mapper'. rewrite upds. vauto. }
  apply XmmCons.monoton_cons with (G_t := G_t')
        (m := mapper'); vauto; try apply SIMRELQ.
  { admit. (* TODO : po-work? *) }
  { admit. (* TODO : po-work? *) }
  all : admit. (* TODO : add? *)
Admitted.



End SimrelStep.
