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
Hypothesis MAPREVR : eq_dom E_t (mapper ∘ mapper_rev) id.
Hypothesis PROGSEQ : program_trace_sequented ptc_1 ptc_2 t_1 t_2.
Hypothesis WFT : Wf G_t.

Definition t_12_len := length (ptc_2 t_1).
Definition t_1_len := length (ptc_1 t_1).
Definition t_2_len := length (ptc_1 t_2).

Hypothesis INV : seq_simrel_inv X_t.
Hypothesis INV' : seq_simrel_inv X_t'.

Lemma simrel_step_e_t1
    (T1 : tid e = t_1)
    (IND: index e < t_1_len)
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper mapper_rev ptc_1)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' mapper_rev' X_s',
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' mapper_rev' ptc_1 >> /\
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
    assert (C1' : E_t e') by vauto.
    apply (seq_mapeq SIMREL) in C1; vauto.
    { assert (EQQ : e' = e).
      { rewrite CDD. rewrite <- C2. vauto. }
      subst e'; desf. }
    rewrite C2; rewrite <- CDD.
    clear - T1 THRDNEQ. intros FALSE; desf. }

  unfold NW in NEWE.
  destruct NEWE as (NINIT & NOTIN & TID).

  set (G_s' := {|
  acts_set := mapper' ↑₁ E_t';
    threads_set := threads_set G_s;
    lab := lab_t' ∘ mapper_rev';
    rf := mapper' ↑ rf_t';
    co := mapper' ↑ co_t';
    rmw := mapper' ↑ rmw_t';
    rmw_dep := ∅₂;
    ctrl := ∅₂;
    data := ∅₂;
    addr := ∅₂;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists mapper', mapper_rev', X_s'.
  assert (SIMRELQ : seq_simrel X_s' X_t' (tid e) t_2 mapper' mapper_rev' ptc_1).
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
    { unfold sb. unfold G_s'; ins.
      split; intros x y COND.
      { destruct COND as [CD1 | CD2].
        { destruct CD1 as [x0 [[EQ1 [x' [INE1 M1]]]
                      [x1 [EXT [EQ2 [y' [INE2 M2]]]]]]]; subst.
          unfold collect_rel. exists x', y'; splits; vauto.
          unfold seq. exists x'; splits; vauto.
          exists y'; splits; vauto.
          unfold ext_sb in EXT.
          destruct classic with (x' = e) as [EQ | NEQ].
          { subst. destruct e. 
            { clear - NINIT. desf. }
            destruct classic with (thread = t_2) as [EQ | NEQ].
            { subst. clear - TID THRDNEQ. desf. }
            unfold mapper' in EXT. rewrite upds in EXT.
            destruct y'.
            { destruct SIMREL.
              clear - EXT seq_init.
              unfold upd in EXT. desf.
              rewrite seq_init in Heq; desf. }
            destruct classic with (thread0 = t_2) as [EQ' | NEQ'].
            { subst. destruct ADD.
              exfalso. apply T2NOTIN.
              apply add_event_threads; vauto.
              apply wf_threads with (G := G_t')
                        (e := (ThreadEvent t_2 index0)); vauto.
              apply INV'. }
            desf. unfold upd in Heq. desf.
            assert (MIND : index0 = index1).
            { rewrite (seq_mapeq SIMREL) in Heq; vauto.
              { apply EQACTS in INE2.
                clear - INE2 n.
                destruct INE2 as [C1 | C2]; vauto. }
              intros FALSE.
              rewrite <- (seq_tid_1 SIMREL) in FALSE; vauto.
              { apply EQACTS in INE2.
                clear - INE2 n.
                destruct INE2 as [C1 | C2]; vauto. }
              rewrite Heq in NEQ. desf. }
            assert (MTID : thread0 = thread1).
            { rewrite (seq_mapeq SIMREL) in Heq; vauto.
              { apply EQACTS in INE2.
                clear - INE2 n.
                destruct INE2 as [C1 | C2]; vauto. }
              intros FALSE.
              rewrite <- (seq_tid_1 SIMREL) in FALSE; vauto.
              { apply EQACTS in INE2.
                clear - INE2 n.
                destruct INE2 as [C1 | C2]; vauto. }
              rewrite Heq in NEQ. desf. }
            basic_solver 21. }
          unfold mapper' in EXT. rewrite updo in EXT; vauto.
          destruct x'.
          { destruct SIMREL. 
            clear - seq_init EXT.
            unfold upd in EXT. desf.
            { destruct y'.
              { rewrite seq_init in Heq0; desf. }
              unfold ext_sb; basic_solver. }
            destruct y'.
            { rewrite seq_init in Heq0; desf. }
            unfold ext_sb; basic_solver. }
          destruct classic with (thread = t_2) as [EQ' | NEQ'].
          { subst. destruct ADD.
            exfalso. apply T2NOTIN.
            apply add_event_threads; vauto.
            apply wf_threads with (G := G_t')
                      (e := (ThreadEvent t_2 index)); vauto.
            apply INV'. }
          destruct classic with (y' = e) as [EQY | NEQY].
          { subst. unfold mapper' in EXT. rewrite upds in EXT.
            desf.
            { rewrite (seq_mapeq SIMREL) in Heq; vauto.
              { apply EQACTS in INE1.
                clear - INE1 NEQ.
                destruct INE1 as [C1 | C2]; vauto. }
              intros FALSE.
              rewrite <- (seq_tid_1 SIMREL) in FALSE; vauto.
              { apply EQACTS in INE1.
                clear - INE1 NEQ.
                destruct INE1 as [C1 | C2]; vauto. }
              rewrite Heq in NEQ'.
              unfold tid in NEQ'. destruct SIMREL.
              assert (HLP : mapper_rev (InitEvent l0) = ThreadEvent thread index).
              { rewrite <- Heq. apply MAPREV.
                apply EQACTS in INE1.
                clear - INE1 NEQ.
                destruct INE1 as [C1 | C2]; vauto. }
              rewrite seq_init_rev in HLP; vauto. }
            destruct classic with (thread0 = t_2) as [EQT | NEQT].
            { subst. destruct ADD.
              exfalso. apply T2NOTIN.
              apply add_event_threads; vauto.
              apply wf_threads with (G := G_t')
                        (e := (ThreadEvent t_2 index1)); vauto.
              { apply INV'. }
              destruct EXT; vauto. }
            rewrite (seq_mapeq SIMREL) in Heq; vauto.
            { apply EQACTS in INE1.
              clear - INE1 NEQ.
              destruct INE1 as [C1 | C2]; vauto. }
            rewrite Heq. basic_solver. }
          unfold mapper' in EXT. rewrite updo in EXT; vauto.
          destruct y'.
          { desf.
            { destruct SIMREL.
              clear - seq_init Heq0.
              rewrite seq_init in Heq0; desf. }
            destruct SIMREL.
            clear - seq_init Heq0.
            rewrite seq_init in Heq0; desf. }
          desf.
          { assert (HLP : mapper_rev (InitEvent l0) = ThreadEvent thread index).
            { rewrite <- Heq. apply MAPREV.
              apply EQACTS in INE1.
              clear - INE1 NEQ.
              destruct INE1 as [C1 | C2]; vauto. }
            rewrite seq_init_rev in HLP; vauto. }
          destruct EXT; subst.
          destruct classic with (thread2 = t_2) as [EQT | NEQT].
          { subst.
            assert (MIND1 : thread = t_1).
            { rewrite <- (seq_tid_2 SIMREL)
                with (e := (ThreadEvent thread index)); vauto.
              { apply EQACTS in INE1.
                clear - INE1 NEQ.
                destruct INE1 as [C1 | C2]; vauto. }
              rewrite Heq; vauto. }
            assert (MIND2 : thread0 = t_1).
            { rewrite <- (seq_tid_2 SIMREL)
                with (e := (ThreadEvent thread0 index0)); vauto.
              { apply EQACTS in INE2.
                clear - INE2 NEQY.
                destruct INE2 as [C1 | C2]; vauto. }
              rewrite Heq0; vauto. }
            assert (INDLESS : Events.index (ThreadEvent thread index)
                        < Events.index (ThreadEvent thread0 index0)).
            { rewrite (seq_index SIMREL)
                  with (e := (ThreadEvent thread0 index0)).
              { rewrite (seq_index SIMREL)
                      with (e := (ThreadEvent thread index)).
                { rewrite Heq, Heq0. ins.
                  lia. }
                { apply EQACTS in INE1.
                  clear - INE1 NEQ.
                  destruct INE1 as [C1 | C2]; vauto. }
                rewrite Heq; vauto. }
              { apply EQACTS in INE2.
                clear - INE2 NEQY.
                destruct INE2 as [C1 | C2]; vauto. }
              rewrite Heq0; vauto. }
            clear - MIND1 MIND2 INDLESS.
            unfold ext_sb. basic_solver 21. }
          rewrite (seq_mapeq SIMREL) in Heq; vauto.
          { rewrite (seq_mapeq SIMREL) in Heq0; vauto.
            { apply EQACTS in INE2.
              clear - INE2 NEQY.
              destruct INE2 as [C1 | C2]; vauto. }
            rewrite Heq0; vauto. }
          { apply EQACTS in INE1.
            clear - INE1 NEQ.
            destruct INE1 as [C1 | C2]; vauto. }
          rewrite Heq; vauto. }
        unfold po_seq in CD2.
        change (WCore.G X_s') with G_s' in CD2.
        unfold G_s' in CD2. ins.
        destruct CD2 as [C1 C2].
        destruct C1 as [TR1 [x0 [IN1 MAP1]]].
        destruct C2 as [TR2 [y0 [IN2 MAP2]]].
        unfold collect_rel. exists x0, y0; splits; vauto.
        unfold seq. exists x0; splits; vauto.
        exists y0; splits; vauto.
        assert (TIDD : tid y0 = t_1).
        { admit. }
        admit. }
      admit. }
    { rewrite (seq_threads SIMREL).
      destruct ADD. rewrite add_event_threads; vauto. }
    { unfold mapper'. intros x COND.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. rewrite upds; vauto. }
      rewrite updo; vauto.
      apply (seq_init SIMREL); vauto. }
    { unfold mapper_rev'. intros x COND.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. rewrite upds; vauto. }
      rewrite updo; vauto.
      apply (seq_init_rev SIMREL); vauto. }
    { intros e' INE TID2.
      destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. unfold mapper'. rewrite upds; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_mapeq SIMREL); vauto.
      { apply EQACTS in INE. 
        destruct INE as [C1 | C2]; vauto. }
      unfold mapper' in TID2. rewrite updo in TID2; vauto. }
    { intros e' INE TID2.
      destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. unfold mapper' in TID2.
        rewrite upds in TID2. exfalso.
        clear - TID TID2 THRDNEQ. desf. }
      assert (INE' : E_t e').
      { apply EQACTS in INE.
        destruct INE as [C1 | C2]; vauto. }
      assert (MAPEQQ : mapper' e' = mapper e').
      { unfold mapper'. rewrite updo; vauto. }
      rewrite MAPEQQ. 
      apply (seq_mapto SIMREL) in INE'.
      { rewrite TID; vauto. }
      rewrite <- MAPEQQ; vauto. }
    { intros e' INE TID2.
      destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. unfold mapper' in TID2.
        rewrite upds in TID2. exfalso.
        clear - TID TID2 THRDNEQ. desf. }
      assert (INE' : E_t e').
      { apply EQACTS in INE.
        destruct INE as [C1 | C2]; vauto. }
      assert (MAPEQQ : mapper' e' = mapper e').
      { unfold mapper'. rewrite updo; vauto. }
      rewrite MAPEQQ. 
      apply (seq_index SIMREL) in INE'.
      { rewrite TID; vauto. }
      rewrite <- MAPEQQ; vauto. }
    { intros e' NINE.
      destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. unfold mapper'. rewrite upds; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_rest SIMREL); vauto.
      intros FALSE. apply NINE.
      apply EQACTS. unfold set_union.
      left; vauto. }
    { intros e' NINE.
      destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. unfold mapper_rev'. rewrite upds; vauto. }
      unfold mapper_rev'. rewrite updo; vauto.
      apply (seq_rest_rev SIMREL); vauto.
      intros FALSE. apply NINE.
      apply EQACTS. unfold set_union.
      left; vauto. }
    intros e' NINE.
    destruct classic with (e' = e) as [EQ | NEQ].
    { subst e'. unfold mapper_rev'.
      unfold compose. unfold mapper'.
      rewrite upds; vauto.
      rewrite upds; vauto. }
    unfold mapper_rev'. unfold compose.
    unfold mapper'. rewrite updo; vauto.
    { rewrite updo; vauto.
      rewrite (seq_rest SIMREL); vauto.
      { rewrite (seq_rest_rev SIMREL); vauto.
        intros FALSE. apply NINE.
        apply EQACTS. unfold set_union.
        left; vauto. }
      intros FALSE. apply NINE.
      apply EQACTS. unfold set_union.
      left; vauto. }
    rewrite updo; vauto.
    rewrite (seq_rest SIMREL); vauto.
    intros FALSE. apply NINE.
    apply EQACTS. unfold set_union.
    left; vauto. }
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
      { constructor. all : try apply SIMREL.
        rewrite (seq_lab SIMREL); vauto. }
      destruct ADD. apply add_event_init. }
    { unfold mapper'. rewrite upds. exact NOTIN. }
    { unfold mapper'. rewrite upds; vauto. }
    { unfold mapper'. rewrite upds.
      rewrite TID. basic_solver. }
    { rewrite EQACTS. rewrite set_collect_union.
      rewrite MAPER_E, MAPSUB. rewrite (seq_acts SIMREL).
      unfold mapper'. rewrite upds. basic_solver. }
    { destruct ADD. destruct SIMRELQ.
      unfold mapper', mapper_rev'.
      apply functional_extensionality; ins.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. rewrite !upds. vauto.
        rewrite add_event_lab.
        unfold compose. rewrite upds.
        rewrite upds; vauto. }
      rewrite !updo; vauto.
      { rewrite add_event_lab.
        unfold compose. rewrite updo; vauto.
        { destruct SIMREL.
          destruct classic with (E_t x) as [INN | NINN].
          { rewrite updo; vauto.
            rewrite seq_lab_rev0; vauto. }
          rewrite updo; vauto.
          rewrite seq_rlab0; vauto. }
        rewrite updo; vauto.
        destruct classic with (E_t x) as [INN | NINN].
        { destruct SIMREL.
          intros FALSE.
          assert (STT : mapper (mapper_rev x) = mapper e)
                  by vauto.
          unfold compose in MAPREVR.
          rewrite MAPREVR in STT.
          { unfold id in STT.
            rewrite seq_rest0 in STT; vauto. }
          vauto. }
        destruct SIMREL.
        rewrite seq_rest_rev0; vauto. }
      rewrite upds; vauto. }
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
    { rewrite (seq_data SIMREL); vauto. }
    { rewrite (seq_addr SIMREL); vauto. }
    { rewrite (seq_ctrl SIMREL); vauto. }
    { rewrite (seq_rmw_dep SIMREL); vauto. }
    { admit. (* po-work *) }
    admit. (* wf_s' *) }
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
  { rewrite <- (seq_lab SIMRELQ); vauto. }
  { admit. (* TODO : po-work? *) }
  { apply INV'. }
  constructor. (* wf_s' *)
  all : admit.
Admitted.

Lemma simrel_step_e_t2
    (T1 : tid e = t_1)
    (IND: index e >= t_1_len)
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper mapper_rev ptc_1)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' mapper_rev' X_s',
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' mapper_rev' ptc_1 >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper e (ThreadEvent t_2 (index e - t_1_len))).
  set (mapper_rev' := upd mapper_rev (ThreadEvent t_2 (index e - t_1_len)) e).
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (EMAPNOTIN : ~E_s (ThreadEvent t_2 (index e - t_1_len))).
  { intros FALSE. destruct ADD.
    assert (CDD : (ThreadEvent t_2 (index e - t_1_len)) = mapper' e).
    { unfold mapper'. rewrite upds; vauto. }
    rewrite CDD in FALSE.
    apply (seq_acts SIMREL) in FALSE.
    destruct FALSE as [e' [C1 C2]].
    assert (C1' : E_t e') by vauto.
    apply (seq_mapto SIMREL) in C1; vauto.
    { assert (TID' : tid e' = t_1).
      { apply (seq_tid_2 SIMREL) in C1'; vauto.
        rewrite C1; vauto. }
      rewrite <- CDD in C2. rewrite C1 in C2; vauto.
      assert (INDEX : index e' = index e).
      { unfold t_1_len in H0.
        assert (index e' >= t_1_len).
        { apply (seq_index SIMREL) in C1'.
          { rewrite C1'.
            unfold SequentBase.t_1_len, t_1_len.
            clear. lia. }
          rewrite C1; vauto. }
        unfold SequentBase.t_1_len in H0.
        clear - H0 H IND. unfold t_1_len in *. lia. }
      assert (EQE : e' = e).
      { clear - INDEX TID' T1 NINIT1.
        destruct e', e; basic_solver 8. }
      desf. }
    rewrite C2; rewrite <- CDD.
    vauto. }
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
    rmw_dep := ∅₂;
    ctrl := ∅₂;
    data := ∅₂;
    addr := ∅₂;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists mapper', mapper_rev', X_s'.
  assert (SIMRELQ : seq_simrel X_s' X_t' t_1 t_2 mapper' mapper_rev' ptc_1).
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
    { unfold mapper_rev'. intros x COND.
      destruct classic with (x = (ThreadEvent t_2 (index e - t_1_len))) as [EQ | NEQ].
      { subst x. clear - T1 COND NINIT1.
        unfold tid in T1. unfold is_init in COND.
        desf. }
      rewrite updo; vauto.
      apply (seq_init_rev SIMREL); vauto. }
    { rewrite EQACTS. rewrite set_collect_union.
      rewrite MAPER_E, MAPSUB, (seq_acts SIMREL); vauto. }
    { intros e' INE NTID2.
      apply EQACTS in INE.
      destruct INE as [C1 | C2].
      { destruct classic with (e' = e) as [EQ | NEQ].
        { subst e'. unfold mapper'. rewrite upds; vauto. }
        unfold mapper'. rewrite updo; vauto.
        apply (seq_mapeq SIMREL) in C1; vauto.
        unfold mapper' in NTID2. rewrite updo in NTID2; vauto. }
      subst e'. unfold mapper'. rewrite upds; vauto.
      unfold mapper' in NTID2. rewrite upds in NTID2; vauto. }
    { intros e' INE TID2.
      apply EQACTS in INE.
      destruct INE as [C1 | C2].
      { destruct classic with (e' = e) as [EQ | NEQ].
        { subst e'. unfold mapper'. rewrite upds; vauto. }
        unfold mapper'. rewrite updo; vauto.
        apply (seq_mapto SIMREL) in C1; vauto.
        unfold mapper' in TID2. rewrite updo in TID2; vauto. }
      subst e'. unfold mapper'. rewrite upds; vauto. }
    intros e' INE TID2.
    apply EQACTS in INE.
    destruct INE as [C1 | C2].
    { destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. unfold mapper'. rewrite upds; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_index SIMREL) in C1; vauto.
      unfold mapper' in TID2. rewrite updo in TID2; vauto. }
    subst e'. unfold mapper'. rewrite upds; vauto.
    simpl. unfold SequentBase.t_1_len.
    unfold t_1_len in *. clear - IND. lia. }
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
      { constructor. all : try apply SIMREL.
        rewrite (seq_lab SIMREL); vauto. }
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
    { rewrite (seq_data SIMREL); vauto. }
    { rewrite (seq_addr SIMREL); vauto. }
    { rewrite (seq_ctrl SIMREL); vauto. }
    { rewrite (seq_rmw_dep SIMREL); vauto. }
    { admit. (* po-work *) }
      admit. (* wf_s' *) }
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
  { rewrite <- (seq_lab SIMRELQ); vauto. }
  { admit. (* TODO : po-work? *) }
  { apply INV'. }
  constructor. (* wf_s' *)
  all : admit.
Admitted.

Lemma simrel_step_e_else
    (T1 : tid e <> t_1)
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper mapper_rev ptc_1 )
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' mapper_rev' X_s',
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' mapper_rev' ptc_1 >> /\
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
    assert (C1' : E_t e') by vauto.
    apply (seq_mapeq SIMREL) in C1; vauto.
    { assert (EQQ : e' = e).
      { rewrite CDD. rewrite <- C2. vauto. }
      subst e'; desf. }
    rewrite C2; rewrite <- CDD.
    symmetry in add_event_threads.
    assert (T2NOTIN' : ~ threads_set G_t' t_2).
    { intros FALSE. apply add_event_threads in FALSE; vauto. }
    assert (INEN : E_t' e).
    { apply EQACTS. basic_solver. }
    intros FALSE; desf. }
  unfold NW in NEWE. destruct NEWE as (NINIT & NOTIN & TID).

  set (G_s' := {|
  acts_set := mapper' ↑₁ E_t';
    threads_set := threads_set G_s;
    lab := lab_t' ∘ mapper_rev';
    rf := mapper' ↑ rf_t';
    co := mapper' ↑ co_t';
    rmw := mapper' ↑ rmw_t';
    rmw_dep := ∅₂;
    ctrl := ∅₂;
    data := ∅₂;
    addr := ∅₂;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists mapper', mapper_rev', X_s'.
  assert (SIMRELQ : seq_simrel X_s' X_t' t_1 t_2 mapper' mapper_rev' ptc_1).
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
        subst ev. apply EQACTS in INE'.
        destruct INE' as [C1 | C2].
        { desf. }
        assert (INEN : E_t' e).
        { apply EQACTS. basic_solver. }
        exfalso.
        destruct ADD. symmetry in add_event_threads.
        assert (T2NOTIN' : ~ threads_set G_t' t_2).
        { intros FALSE. apply add_event_threads in FALSE; vauto. }
        desf. }
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
    { unfold mapper'. intros x COND.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. rewrite upds; vauto. }
      rewrite updo; vauto.
      apply (seq_init SIMREL); vauto. }
    { unfold mapper_rev'. intros x COND.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. rewrite upds; vauto. }
      rewrite updo; vauto.
      apply (seq_init_rev SIMREL); vauto. }
    { intros e' INE NTID2.
      apply EQACTS in INE.
      destruct INE as [C1 | C2].
      { destruct classic with (e' = e) as [EQ | NEQ].
        { subst e'. unfold mapper'. rewrite upds; vauto. }
        unfold mapper'. rewrite updo; vauto.
        apply (seq_mapeq SIMREL) in C1; vauto.
        unfold mapper' in NTID2. rewrite updo in NTID2; vauto. }
      subst e'. unfold mapper'. rewrite upds; vauto. }
    { intros e' INE TID2.
      apply EQACTS in INE.
      destruct INE as [C1 | C2].
      { destruct classic with (e' = e) as [EQ | NEQ].
        { subst e'. unfold mapper'. rewrite upds; vauto. }
        unfold mapper'. rewrite updo; vauto.
        apply (seq_mapto SIMREL) in C1; vauto.
        unfold mapper'. rewrite updo; vauto. }
      subst e'. unfold mapper' in TID2.
      rewrite upds in TID2.
      assert (INEN : E_t' e).
      { apply EQACTS. basic_solver. }
      exfalso.
      destruct ADD. symmetry in add_event_threads.
      assert (T2NOTIN' : ~ threads_set G_t' t_2).
      { intros FALSE. apply add_event_threads in FALSE; vauto. }
      desf. }
    intros e' INE TID2.
    apply EQACTS in INE.
    destruct INE as [C1 | C2].
    { destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. unfold mapper'. rewrite upds; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_index SIMREL) in C1; vauto.
      unfold mapper'. rewrite updo; vauto. }
    subst e'. unfold mapper' in TID2.
    rewrite upds in TID2.
    assert (INEN : E_t' e).
    { apply EQACTS. basic_solver. }
    exfalso.
    destruct ADD. symmetry in add_event_threads.
    assert (T2NOTIN' : ~ threads_set G_t' t_2).
    { intros FALSE. apply add_event_threads in FALSE; vauto. }
    desf. }
  split; vauto. constructor.
  { unfold WCore.add_event.
    exists (option_map mapper' r), (mapper' ↑₁ R1),
        (option_map mapper' w),
        (mapper' ↑₁ W1),
        (mapper' ↑₁ W2).
    apply add_event_to_wf; simpl; vauto.
    { apply sico_init_acts_s with
          (X_t := X_t) (mapper := mapper).
      { constructor. all : try apply SIMREL.
        rewrite (seq_lab SIMREL); vauto. }
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
    { rewrite (seq_data SIMREL); vauto. }
    { rewrite (seq_addr SIMREL); vauto. }
    { rewrite (seq_ctrl SIMREL); vauto. }
    { rewrite (seq_rmw_dep SIMREL); vauto. }
    { admit. (* po-work *) }
    admit. (* wf_s' *) }
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
  { rewrite <- (seq_lab SIMRELQ); vauto. }
  { admit. (* TODO : po-work? *) }
  { apply INV'. }
  constructor. (* wf_s' *)
  all : admit.
Admitted.

End SimrelStep.
