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
From xmm Require Import SequentWf.
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
Hypothesis MAPREVR : eq_dom E_s (mapper ∘ mapper_rev) id.
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

  assert (INDLEMMA : forall x y (NNIT : tid x <> tid_init) (EQT : tid x = tid y) (EQI : index x = index y),
          x = y).
  { clear. intros x y NNIT EQT EQI.
    destruct x; destruct y; desf; ins.
    desf. }

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
    { rewrite EQACTS.
      rewrite set_collect_union.
      rewrite set_collect_union.
      apply set_union_more.
      { split.
        { intros x COND.
          destruct classic with (x = e) as [EQ | NEQ].
          { subst x. unfold mapper'.
            desf. }
          unfold set_collect.
          exists (mapper' x). splits; vauto.
          unfold mapper'.
          rewrite updo; vauto.
          unfold mapper_rev'.
          rewrite updo; vauto.
          { apply MAPREV; vauto. }
          intros FALSE.
          assert (INE : E_s e).
          { destruct SIMREL.
            apply seq_acts.
            red; vauto. }
          desf. }
        intros x COND.
        destruct COND as [x0 [[x1 [INE MAP1]] MAP2]].
        apply MAPREVDOM.
        unfold set_collect.
        exists x0; splits; vauto.
        { destruct classic with (x1 = e) as [EQ | NEQ].
          { subst x1. unfold mapper'.
            desf. }
          unfold mapper'.
          rewrite updo; vauto.
          destruct SIMREL.
          apply seq_acts.
          red; vauto. }
        unfold mapper'.
        rewrite updo.
        { unfold mapper_rev'.
          rewrite updo; vauto.
          intros FALSE.
          assert (INES : E_s e).
          { destruct SIMREL.
            apply seq_acts.
            red; vauto. }
          desf. }
        intros FALSE. desf. }
      rewrite MAPER_E.
      rewrite MEPERREV_E; vauto. }
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
        unfold collect_rel. exists x0, y0; splits.
        { unfold seq. exists x0; splits.
          { red; vauto. }
          exists y0; splits.
          { destruct SIMREL.
            assert (NEQ1 : y0 <> e).
            { intros FLS. subst y0.
              unfold mapper' in MAP2.
              rewrite upds in MAP2.
              subst e. rewrite TID in TR2.
              desf. }
            assert (EQQ : mapper' y0 = mapper y0).
            { unfold mapper'. rewrite updo; vauto. }
            rewrite EQQ in MAP2.
            destruct classic with (x0 = e) as [EQ | NEQ].
            { unfold ext_sb.
              rewrite <- MAP2 in TR2.
              apply seq_mapto in TR2.
              { desf.
                { rewrite seq_init in TR2.
                  { clear - TR2 NINIT2.
                    desf. }
                  desf. }
                split.
                { assert (TRH : tid (mapper
                        (ThreadEvent thread0 index0)) = t_2).
                  { rewrite TR2.
                    unfold tid; vauto. }
                  apply seq_thrd in TRH.
                  { unfold tid in *. desf. }
                  apply EQACTS in IN2.
                  destruct IN2 as [C1 | C2]; vauto. }
                assert (LIAH :  t_1_len <= index0).
                { assert (TRH : tid (mapper
                        (ThreadEvent thread0 index0)) = t_2).
                  { rewrite TR2.
                    unfold tid; vauto. }
                  apply seq_index in TRH.
                  { unfold Events.index in *.
                    unfold SequentBase.t_1_len in *.
                    unfold t_1_len in *. rewrite TRH.
                    assert (NINNIT : ~ is_init (mapper
                            (ThreadEvent thread0 index0))).
                    { intros FLS.
                      rewrite TR2 in FLS.
                      unfold is_init in FLS.
                      desf. }
                    lia. }
                  apply EQACTS in IN2.
                  destruct IN2 as [C1 | C2]; vauto. }
                unfold Events.index in *.
                lia. }
              apply EQACTS in IN2.
              destruct IN2 as [C1 | C2]; vauto. }
            unfold ext_sb.
            rewrite <- MAP2 in TR2.
            apply seq_mapto in TR2.
            { desf.
              { rewrite seq_init in TR2.
                { clear - TR2 NINIT2.
                  desf. }
                desf. }
              { rewrite seq_init in TR2.
                { clear - TR2 NINIT2.
                  desf. }
                desf. }
              split.
              { assert (TRH : tid (mapper
                      (ThreadEvent thread0 index0)) = t_2).
                { rewrite TR2.
                  unfold tid; vauto. }
                apply seq_thrd in TRH.
                { unfold tid in *. desf.
                  { exfalso. clear - TR1 NINIT1.
                    apply NINIT1; vauto. }
                  destruct classic with (thread = t_2) as [EQ2 | NEQ2].
                  { apply wf_threads in IN1; [| apply INV'].
                    unfold tid in IN1.
                    rewrite EQ2 in IN1.
                    destruct ADD.
                    apply add_event_threads in IN1.
                    desf. }
                  destruct classic with (thread = t_1) as [EQ3 | NEQ3]; vauto.
                  unfold mapper' in Heq.
                  rewrite updo in Heq; vauto.
                  assert (INEE : E_t (ThreadEvent thread index)).
                  { apply EQACTS in IN1.
                    destruct IN1 as [C1 | C2]; vauto. }
                  assert (TNEQQ : tid (mapper (ThreadEvent thread index)) <> t_2).
                  { rewrite Heq. unfold tid; vauto. }
                  apply seq_out in INEE; vauto.
                  rewrite Heq in INEE.
                  clear - INEE. basic_solver. }
                apply EQACTS in IN2.
                destruct IN2 as [C1 | C2]; vauto. }
              assert (LIAH :  t_1_len <= index0).
              { assert (TRH : tid (mapper
                      (ThreadEvent thread0 index0)) = t_2).
                { rewrite TR2.
                  unfold tid; vauto. }
                apply seq_index in TRH.
                { unfold Events.index in *.
                  unfold SequentBase.t_1_len in *.
                  unfold t_1_len in *. rewrite TRH.
                  assert (NINNIT : ~ is_init (mapper
                          (ThreadEvent thread0 index0))).
                  { intros FLS.
                    rewrite TR2 in FLS.
                    unfold is_init in FLS.
                    desf. }
                  lia. }
                apply EQACTS in IN2.
                destruct IN2 as [C1 | C2]; vauto. }
              assert (INDN : index < t_1_len).
              { assert (INEE : E_t (ThreadEvent thread index)).
                { apply EQACTS in IN1.
                  destruct IN1 as [C1 | C2]; vauto. }
                unfold mapper' in TR1.
                rewrite updo in TR1; vauto.
                assert (TNEQQ : tid (mapper (ThreadEvent thread index)) <> t_2).
                { rewrite TR1. rewrite TID. desf. }
                apply seq_mapeq in INEE; vauto.
                assert (TTDS : thread = t_1).
                { rewrite INEE in TR1.
                  unfold tid in *; vauto. }
                assert (INET : E_t (ThreadEvent thread index)).
                { apply EQACTS in IN1.
                  destruct IN1 as [C1 | C2]; vauto. }
                apply NNPP. intros FLS.
                apply Compare_dec.not_lt in FLS.
                apply seq_out_move in INET; vauto.
                rewrite INEE in INET.
                clear - INET THRDNEQ.
                desf. }
              lia. }
            apply EQACTS in IN2.
            destruct IN2 as [C1 | C2]; vauto. }
          red; vauto. }
        all : vauto. }
      destruct COND as [x0 [y0 [[x1 [[EQ1 INE1]
                  [y1 [COND [EQ2 INE2]]]]] [M1 M2]]]].
      subst.
      assert (INE1' : (acts_set G_s') (mapper' x1)).
      { unfold G_s'; ins.
        unfold set_collect.
        exists x1; vauto. }
      assert (INE2' : (acts_set G_s') (mapper' y0)).
      { unfold G_s'; ins.
        unfold set_collect.
        exists y0; vauto. }
      destruct classic with (tid (mapper' y0) = t_2) as [EQ1 | NEQ1].
      { destruct classic with (tid (mapper' x1) = t_1) as [EQ2 | NEQ2].
        { right. unfold po_seq.
          split.
          { split; vauto.
            rewrite TID; vauto. }
          split; vauto. }
        left.
        assert (TIDD2 : tid y0 = t_1).
        { destruct classic with (y0 = e) as [EQ | NEQ].
          { subst y0; vauto. }
          unfold mapper' in EQ1.
          rewrite updo in EQ1.
          { assert (EQ1' : tid (mapper y0) = t_2) by vauto.
            apply (seq_thrd SIMREL) in EQ1'; vauto.
            apply EQACTS in INE2.
            destruct INE2 as [C1 | C2]; vauto. }
          vauto. }
        destruct x1.
        { unfold seq. exists (mapper' (InitEvent l0)); split.
          { red; vauto. }
          exists (mapper' y0); split.
          { arewrite (mapper' (InitEvent l0) = mapper (InitEvent l0)).
            { unfold mapper'. rewrite updo; vauto.
              intros FLS. apply NINIT; vauto. }
            rewrite (seq_init SIMREL).
            { unfold ext_sb; vauto.
              desf. }
            vauto. }
          red; vauto. }
        assert (TIDD : thread = t_1).
        { unfold ext_sb in COND.
          desf. unfold tid in TIDD2.
          rewrite <- TIDD2; vauto.
          destruct COND; vauto. }
        destruct y0.
        { exfalso. unfold tid in TIDD2; vauto. }
        unfold ext_sb in COND.
        destruct COND as [COND1 COND2].
        unfold seq.
        exists (mapper' (ThreadEvent thread index)); split.
        { red; vauto. }
        exists (mapper' (ThreadEvent thread0 index0)); split.
        { assert (INDD : index >= t_1_len).
          { apply NNPP. intros FLS.
            apply Compare_dec.not_ge in FLS.
            assert (INET : E_t (ThreadEvent thread index)).
            { destruct classic with ((ThreadEvent thread index) = e) as [EQ | NEQ].
              { exfalso. unfold mapper' in NEQ2.
                rewrite EQ in NEQ2.
                rewrite upds in NEQ2; vauto. }
              apply EQACTS in INE1.
              destruct INE1 as [C1 | C2]; vauto. }
            apply (seq_out_snd SIMREL) in INET; vauto.
            destruct classic with ((ThreadEvent t_1 index) = e) as [EQ | NEQ].
            { exfalso. unfold mapper' in NEQ2.
              rewrite EQ in NEQ2.
              rewrite upds in NEQ2; vauto. }
            unfold mapper' in NEQ2.
            rewrite updo in NEQ2; vauto.
            rewrite INET in NEQ2.
            desf. }
          assert (INEE1 : E_t (ThreadEvent thread index)).
          { destruct classic with ((ThreadEvent thread index) = e) as [EQ | NEQ].
            { exfalso. unfold mapper' in NEQ2.
              rewrite EQ in NEQ2.
              rewrite upds in NEQ2; vauto. }
            apply EQACTS in INE1.
            destruct INE1 as [C1 | C2]; vauto. }
          assert (INEE2 : E_t (ThreadEvent thread0 index0)).
          { destruct classic with ((ThreadEvent thread0 index0) = e) as [EQ | NEQ].
            { exfalso. unfold mapper' in EQ1.
              rewrite EQ in EQ1.
              rewrite upds in EQ1; vauto. }
            apply EQACTS in INE2.
            destruct INE2 as [C1 | C2]; vauto. }
          apply (seq_out_move SIMREL) in INEE1, INEE2; vauto.
          { assert (SWP1 : mapper' (ThreadEvent t_1 index)
                  = mapper (ThreadEvent t_1 index)).
            { unfold mapper'.
              destruct classic with (ThreadEvent t_1 index = e) as [EQ | NEQ].
              { exfalso. unfold mapper' in NEQ2.
                rewrite EQ in NEQ2.
                rewrite upds in NEQ2; vauto. }
              rewrite updo; vauto. }
            assert (SWP2 : mapper' (ThreadEvent t_1 index0)
                  = mapper (ThreadEvent t_1 index0)).
            { unfold mapper'.
              destruct classic with (ThreadEvent t_1 index0 = e) as [EQ | NEQ].
              { exfalso. rewrite EQ in THRDNEQ.
                unfold mapper' in THRDNEQ.
                rewrite upds in THRDNEQ; vauto. }
              rewrite updo; vauto. }
            rewrite SWP1, SWP2.
            rewrite INEE1, INEE2.
            unfold ext_sb. split; vauto.
            unfold Events.index.
            clear - COND2 INDD.
            unfold SequentBase.t_1_len in *.
            unfold t_1_len in *.
            lia. }
          unfold Events.index in *.
          unfold SequentBase.t_1_len in *.
          unfold t_1_len in *.
          lia. }
        red; vauto. }
      destruct classic with (y0 = e) as [EQ | NEQ].
      { subst y0. left.
        unfold seq. exists (mapper' x1); split; vauto.
        exists (mapper' e); split; vauto.
        destruct classic with (tid (mapper' x1) = t_2) as [EQ2 | NEQ2].
        { destruct classic with (x1 = e) as [EQ3 | NEQ3].
          { subst x1. unfold mapper'.
            desf. }
          assert (INEE : E_t x1).
          { apply EQACTS in INE1.
            destruct INE1 as [C1 | C2]; vauto. }
          apply (seq_index SIMREL) in INEE; vauto.
          { exfalso. unfold ext_sb in COND.
            desf.
            { rewrite (seq_init SIMREL) in INEE; vauto.
              unfold SequentBase.t_1_len in *.
              unfold t_1_len in *.
              lia. }
            destruct COND as [COND1 COND2].
            unfold Events.index in INEE at 1.
            unfold SequentBase.t_1_len in *.
            unfold t_1_len in *.
            unfold Events.index in IND.
            lia. }
          unfold mapper'. rewrite updo; vauto. }
        assert (INEE : E_t x1).
        { destruct classic with (x1 = e) as [EQ3 | NEQ3].
          { subst x1. unfold ext_sb in COND. desf.
            destruct COND as [COND1 COND2].
            exfalso. clear - COND2. lia. }
          apply EQACTS in INE1.
          destruct INE1 as [C1 | C2]; vauto. }
        apply (seq_mapeq SIMREL) in INEE; vauto.
        { arewrite (mapper' x1 = mapper x1).
          { unfold mapper'. rewrite updo; vauto.
            intros FALSO. subst x1.
            unfold ext_sb in COND. desf.
            destruct COND as [COND1 COND2].
            exfalso. lia. }
          rewrite INEE.
          unfold mapper'.
          rewrite upds; vauto. }
        assert (SWP : mapper' x1 = mapper x1).
        { unfold mapper'. rewrite updo; vauto.
          intros FALSO. subst x1.
          unfold ext_sb in COND. desf. }
        rewrite SWP in NEQ2; vauto. }
      destruct classic with (x1 = e) as [EQ2 | NEQ2].
      { subst x1.
        left.
        assert (SWP : mapper' y0 = mapper y0).
        { unfold mapper'. rewrite updo; vauto. }
        rewrite SWP in NEQ1; vauto.
        assert (INEE : E_t y0).
        { apply EQACTS in INE2.
          destruct INE2 as [C1 | C2]; vauto. }
        apply (seq_mapeq SIMREL) in INEE; vauto.
        unfold seq. exists (mapper' e); split; vauto.
        exists (mapper' y0); split; vauto.
        rewrite SWP, INEE.
        unfold mapper'.
        rewrite upds; vauto. }
      left.
      unfold seq. exists (mapper' x1); split; vauto.
      exists (mapper' y0); split; vauto.
      destruct classic with (tid (mapper' x1) = t_2) as [EQ3 | NEQ3].
      { unfold mapper' in EQ3. rewrite updo in EQ3.
        { assert (INEE : E_t x1).
          { apply EQACTS in INE1.
            destruct INE1 as [C1 | C2]; vauto. }
          assert (INEE' : E_t x1) by vauto.
          apply (seq_index SIMREL) in INEE.
          { apply (seq_thrd SIMREL) in INEE'.
            { destruct classic with (index y0 < t_1_len) as [LS | GT].
              assert (INEY : E_t y0).
              { apply EQACTS in INE2.
                destruct INE2 as [C1 | C2]; vauto. }
              unfold ext_sb in COND.
              desf.
              { unfold mapper' at 1.
                rewrite updo; vauto.
                rewrite (seq_init SIMREL); vauto.
                unfold ext_sb; vauto.
                desf.
                unfold mapper' in Heq.
                rewrite updo in Heq; vauto.
                assert (REVV : mapper_rev (mapper (ThreadEvent thread index))
                      = mapper_rev (InitEvent l1)).
                { rewrite Heq; vauto. }
                unfold compose in MAPREV.
                rewrite MAPREV in REVV; vauto.
                unfold id in REVV.
                rewrite (seq_init_rev SIMREL) in REVV; vauto. }
              { unfold mapper'.
                rewrite !updo; vauto.
                unfold Events.index in *.
                destruct COND as [COND1 COND2].
                exfalso.
                unfold SequentBase.t_1_len in *.
                unfold t_1_len in *.
                lia. }
              exfalso.
              apply Compare_dec.not_lt in GT.
              assert (INEY : E_t y0).
              { apply EQACTS in INE2.
                destruct INE2 as [C1 | C2]; vauto. }
              apply (seq_out_move SIMREL) in INEY; vauto.
              { unfold mapper' in NEQ1.
                rewrite updo in NEQ1; vauto.
                rewrite INEY in NEQ1.
                desf. }
              unfold ext_sb in COND.
              desf.
              { exfalso.
                unfold tid in INEE'.
                apply NINIT1; vauto. }
              unfold tid in INEE'.
              destruct COND as [COND1 COND2].
              unfold tid; vauto. }
            vauto. }
          vauto. }
        vauto. }
      assert (INEE : E_t x1).
      { apply EQACTS in INE1.
        destruct INE1 as [C1 | C2]; vauto. }
      assert (INEE' : E_t y0).
      { apply EQACTS in INE2.
        destruct INE2 as [C1 | C2]; vauto. }
      apply (seq_mapeq SIMREL) in INEE.
      { apply (seq_mapeq SIMREL) in INEE'.
        { unfold mapper'.
          rewrite !updo; vauto.
          rewrite INEE, INEE'; vauto. }
        unfold mapper' in NEQ1.
        rewrite updo in NEQ1; vauto. }
      unfold mapper' in NEQ3.
      rewrite updo in NEQ3; vauto. }
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
    { intros x MAP TIDS.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper_rev'. rewrite upds; vauto. }
      destruct MAP as [x0 [INE MAP]].
      unfold mapper_rev'.
      rewrite updo; vauto.
      unfold mapper'.
      rewrite updo; vauto.
      { unfold mapper' in TIDS.
        rewrite updo in TIDS; vauto.
        { destruct SIMREL.
          apply seq_mapeq_rev in TIDS; vauto.
          apply seq_acts.
          red; exists x0; splits; vauto.
          apply EQACTS in INE.
          destruct INE as [C1 | C2]; vauto.
          apply seq_mapeq in TIDS; vauto.
          { unfold mapper' in NEQ.
            rewrite upds in NEQ.
            desf. }
          unfold mapper' in NEQ.
          rewrite upds in NEQ.
          desf. }
        intros FLS. subst.
        unfold mapper' in NEQ.
        rewrite upds in NEQ. desf. }
      intros FLS. subst.
      unfold mapper' in NEQ.
      rewrite upds in NEQ. desf. }
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
    { intros x INE TID2.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper' in TID2.
        rewrite upds in TID2. exfalso.
        clear - TID TID2 THRDNEQ. desf. }
      unfold mapper' in TID2.
      rewrite updo in TID2.
      { destruct SIMREL.
        apply seq_thrd in TID2.
        { rewrite TID2; vauto. }
        apply EQACTS in INE.
        destruct INE as [C1 | C2]; vauto. }
      vauto. }
    { intros x INE TID2.
      unfold mapper_rev'.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. exfalso.
        clear - TID TID2 THRDNEQ. desf. }
      rewrite updo; vauto.
      rewrite (seq_maprev SIMREL); vauto.
      { apply INDLEMMA; vauto.
        unfold index. rewrite TID; lia. }
      apply (seq_acts SIMREL).
      apply MAPSUB.
      unfold set_collect in INE.
      destruct INE as [x0 [INE MAP]].
      apply EQACTS in INE.
      destruct INE as [C1 | C2].
      { vauto. }
      rewrite <- C2 in MAP.
      assert (MAPNORM : mapper' e = e).
      { rewrite set_collect_eq in MAPER_E.
        apply MAPER_E; vauto. }
      desf. }
    { intros x INE TID2.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper'.
        rewrite upds. exfalso. desf. }
      unfold mapper'.
      rewrite updo; vauto.
      destruct SIMREL.
      rewrite seq_out; vauto.
      { apply EQACTS in INE.
        destruct INE as [C1 | C2]; vauto. }
      rewrite <- TID; vauto. }
    { intros x INE TIDS IDXS.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper'.
        rewrite upds. desf. }
      unfold mapper'.
      rewrite updo; vauto.
      destruct SIMREL.
      rewrite seq_out_snd; vauto.
      { apply EQACTS in INE.
        destruct INE as [C1 | C2]; vauto. }
      { rewrite <- TID; vauto. }
      rewrite <- TID; vauto. }
    { intros x INE TIDS IDXS.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst. clear - IDXS IND TID.
        exfalso. unfold t_1_len in *.
        unfold SequentBase.t_1_len in *.
        rewrite TID in IDXS.
        lia. }
      unfold mapper'.
      rewrite updo; vauto.
      destruct SIMREL.
      rewrite seq_out_move.
      { rewrite <- TID; vauto. }
      { apply EQACTS in INE.
        destruct INE as [C1 | C2]; vauto. }
      { rewrite <- TID; vauto. }
      rewrite <- TID; vauto. }
    { intros e' NINE.
      destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. unfold mapper'. rewrite upds; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_rest SIMREL); vauto.
      intros FALSE. apply NINE.
      apply EQACTS. unfold set_union.
      left; vauto. }
    intros e' NINE.
    destruct classic with (e' = e) as [EQ | NEQ].
    { subst e'. unfold mapper_rev'. rewrite upds; vauto. }
    unfold mapper_rev'. rewrite updo; vauto.
    apply (seq_rest_rev SIMREL); vauto.
    intros FALSE. apply NINE. unfold set_collect.
    exists (mapper_rev e'). split.
    { apply EQACTS. left. apply MAPREVDOM.
      basic_solver. }
    unfold mapper'. rewrite updo; vauto.
    { apply MAPREVR; vauto. }
    intros FLS.
    assert (WRG : E_t e).
    { apply MAPREVDOM. basic_solver 4. }
    desf. }
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
          destruct classic with (E_s x) as [INN | NINN].
          { rewrite updo; vauto.
            rewrite seq_lab_rev0; vauto. }
          rewrite updo; vauto.
          rewrite seq_rlab0; vauto. }
        rewrite updo; vauto.
        destruct classic with (E_s x) as [INN | NINN].
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
    { assert (SBEQ1 : sb_s ≡ mapper ↑ sb_t \ po_seq X_s t_1 t_2).
      { rewrite <- (seq_sb SIMREL).
        rewrite minus_union_l.
        rewrite minusK. split; [| basic_solver].
        intros x y COND.
        left. split; vauto.
        intros FLS.
        unfold po_seq in FLS.
        destruct FLS as [[TID1 INE1] [TID2 INE2]].
        unfold sb in COND. unfold ext_sb in COND.
        clear - COND TID1 TID2 NINIT1 NINIT2 THRDNEQ.
        destruct COND as [x0 [[EQQ1 INEE1] [x1 [COND2 [EQQ2 INEE2]]]]].
        subst. desf. basic_solver 42. }
      assert (SBEQ2 : sb G_s' ≡ mapper' ↑ sb_t' \ po_seq X_s' t_1 t_2).
      { rewrite <- (seq_sb SIMRELQ).
        rewrite minus_union_l. rewrite TID.
        rewrite minusK. split; [| basic_solver].
        intros x y COND.
        left. split; vauto.
        intros FLS.
        unfold po_seq in FLS.
        destruct FLS as [[TID1 INE1] [TID2 INE2]].
        unfold sb in COND. unfold ext_sb in COND.
        clear - COND TID1 TID2 NINIT1 NINIT2 THRDNEQ.
        destruct COND as [x0 [[EQQ1 INEE1] [x1 [COND2 [EQQ2 INEE2]]]]].
        subst. desf. basic_solver 42. }
      rewrite SBEQ1, SBEQ2.
      unfold WCore.sb_delta.
      destruct ADD. rewrite add_event_sb.
      admit. (* po-work *) }
    arewrite (G_s' = WCore.G X_s').
    apply wf_transition with (X_t := X_t')
          (t_1 := t_1) (t_2 := t_2)
          (mapper := mapper') (mapper_rev := mapper_rev')
          (ptc_1 := ptc_1); vauto.
    rewrite <- TID; vauto. }
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
  { unfold rpo. unfold rpo_imm.
    arewrite (WCore.G X_s' = G_s').
    destruct SIMRELQ.
    assert (RESTR : ⦗R_t' ∩₁ Rlx G_t'⦘ ⨾ sb_t' ⨾ ⦗F G_t' ∩₁ Acq G_t'⦘ ∪ ⦗Acq G_t'⦘ ⨾ sb_t' ∪ sb_t' ⨾ ⦗Rel G_t'⦘
              ∪ ⦗F G_t' ∩₁ Rel G_t'⦘ ⨾ sb_t' ⨾ ⦗W_t' ∩₁ Rlx G_t'⦘ ≡ restr_rel E_t' (
                    ⦗R_t' ∩₁ Rlx G_t'⦘ ⨾ sb_t' ⨾ ⦗F G_t' ∩₁ Acq G_t'⦘ ∪ ⦗Acq G_t'⦘ ⨾ sb_t' ∪ sb_t' ⨾ ⦗Rel G_t'⦘
              ∪ ⦗F G_t' ∩₁ Rel G_t'⦘ ⨾ sb_t' ⨾ ⦗W_t' ∩₁ Rlx G_t'⦘)).
    { split.
      { rewrite !restr_union.
        repeat apply union_mori.
        { intros x y COND.
          unfold restr_rel; split; vauto.
          destruct COND as [x0 [[EQ1 CD1] [x1 [COND [EQ2 CD2]]]]]; subst.
          apply wf_sbE in COND. 
          clear - COND. destruct COND as [x2 [[EQ1 CD1] [x3 [COND [EQ2 CD2]]]]]; subst.
          basic_solver. }
        { intros x y COND.
          unfold restr_rel; split; vauto.
          destruct COND as [x0 [[EQ1 CD1] COND]]; subst.
          apply wf_sbE in COND. 
          clear - COND. destruct COND as [x2 [[EQ1 CD1] [x3 [COND [EQ2 CD2]]]]]; subst.
          basic_solver. }
        { intros x y COND.
          unfold restr_rel; split; vauto.
          destruct COND as [x1 [COND [EQ2 CD2]]]; subst.
          apply wf_sbE in COND. 
          clear - COND. destruct COND as [x2 [[EQ1 CD1] [x3 [COND [EQ2 CD2]]]]]; subst.
          basic_solver. }
        intros x y COND.
        unfold restr_rel; split; vauto.
        destruct COND as [x0 [[EQ1 CD1] [x1 [COND [EQ2 CD2]]]]]; subst.
        apply wf_sbE in COND. 
        clear - COND. destruct COND as [x2 [[EQ1 CD1] [x3 [COND [EQ2 CD2]]]]]; subst.
        basic_solver. }
      rewrite inclusion_restr; vauto. }
    rewrite RESTR.
    rewrite collect_rel_ct_inj.
    {  assert (MAPREVCOMP : eq_dom (acts_set G_s') (mapper' ∘ mapper_rev') id).
      { intros x COND.
        unfold G_s' in COND; ins.
        destruct COND as [x0 [COND EQ]]; subst.
        unfold compose.
        destruct classic with (x0 = e) as [EQ1 | NEQ1].
        { subst x0. unfold mapper', mapper_rev'.
          rewrite !upds; vauto. }
        apply EQACTS in COND.
        destruct COND as [C1 | C2].
        { unfold mapper', mapper_rev'.
          unfold id.
          arewrite (upd mapper e e x0 = mapper x0).
          arewrite (upd mapper_rev e e (mapper x0) = mapper_rev (mapper x0)).
          { destruct classic with (mapper x0 = e) as [EQ2 | NEQ2].
            { destruct SIMREL.
              assert (INEE : E_s e).
              { apply seq_acts0.
                red; vauto. }
              desf. }
            rewrite updo; vauto. }
          unfold compose in MAPREV.
          rewrite MAPREV; vauto.
          unfold id. rewrite updo; vauto. }
        desf. }
      assert (SBIN : sb G_s' ⊆ mapper' ↑ sb_t').
      { rewrite <- seq_sb; vauto. }
      apply clos_trans_mori.
      rewrite <- RESTR.
      rewrite !collect_rel_union.
      repeat apply union_mori.
      { rewrite wf_sbE. rewrite !seqA.
        rewrite <- id_inter.
        rewrite <- seqA.
        rewrite <- id_inter.
        rewrite SBIN.
        rewrite wf_sbE at 2.
        rewrite !seqA.
        rewrite <- id_inter.
        arewrite (⦗R_t' ∩₁ Rlx G_t'⦘ ⨾ ⦗E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t' ∩₁ (F G_t' ∩₁ Acq G_t')⦘ ≡
                  ⦗R_t' ∩₁ Rlx G_t' ∩₁ E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t' ∩₁ (F G_t' ∩₁ Acq G_t')⦘).
        { rewrite <- seqA.
          rewrite <- id_inter; vauto. }
        rewrite !collect_rel_seq.
        { repeat apply seq_mori; vauto.
          { intros x y COND.
            destruct COND as [EQ [[ISR ISRLX] INE]]; subst.
            assert (SUB : G_s' = WCore.G X_s') by vauto.
            rewrite SUB in *.
            unfold is_rlx, mod in ISRLX.
            rewrite seq_lab_rev in ISRLX; vauto.
            red. exists (mapper_rev' y), (mapper_rev' y); splits.
            { red; split; vauto.
              repeat split.
              { unfold is_r. unfold compose in ISRLX; vauto. }
              { unfold is_rlx. unfold compose in ISRLX; vauto. }
              apply seq_acts_rev; red; vauto. }
            { unfold compose in MAPREVCOMP.
              rewrite MAPREVCOMP; vauto. }
            unfold compose in MAPREVCOMP.
            rewrite MAPREVCOMP; vauto. }
          intros x y COND.
          destruct COND as [EQ [INE [ISF ISA]]]; subst.
          assert (SUB : G_s' = WCore.G X_s') by vauto.
          rewrite SUB in *.
          unfold is_acq, mod in ISA.
          rewrite seq_lab_rev in ISA; vauto.
          red. exists (mapper_rev' y), (mapper_rev' y); splits.
          { red; split; vauto.
            repeat split.
            { apply seq_acts_rev; red; vauto. }
            { unfold is_r. unfold compose in ISA; vauto. }
            unfold is_rlx. unfold compose in ISA; vauto. }
          { unfold compose in MAPREVCOMP.
            rewrite MAPREVCOMP; vauto. }
          unfold compose in MAPREVCOMP.
          rewrite MAPREVCOMP; vauto. }
        { rewrite wf_sbE.
          rewrite !codom_seq.
          clear - seq_inj.
          basic_solver 8. }
        rewrite wf_sbE.
        clear - seq_inj.
        basic_solver 8. }
      { rewrite wf_sbE.
        rewrite <- seqA.
        rewrite <- id_inter.
        rewrite SBIN.
        rewrite wf_sbE at 2.
        arewrite (⦗Acq G_t'⦘ ⨾ ⦗E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t'⦘ ≡
                  ⦗Acq G_t' ∩₁ E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t'⦘).
        { rewrite <- seqA.
          rewrite <- id_inter; vauto. }
        rewrite !collect_rel_seq.
        { repeat apply seq_mori; vauto.
          { intros x y COND.
            destruct COND as [EQ [ISA INE]]; subst.
            assert (SUB : G_s' = WCore.G X_s') by vauto.
            rewrite SUB in *.
            unfold is_acq, mod in ISA.
            rewrite seq_lab_rev in ISA; vauto.
            red. exists (mapper_rev' y), (mapper_rev' y); splits.
            { red; split; vauto.
              repeat split.
              { unfold is_acq. unfold compose in ISA; vauto. }
              apply seq_acts_rev; red; vauto. }
            { unfold compose in MAPREVCOMP.
              rewrite MAPREVCOMP; vauto. }
            unfold compose in MAPREVCOMP.
            rewrite MAPREVCOMP; vauto. }
          intros x y COND.
          destruct COND as [EQ INE]; subst.
          assert (SUB : G_s' = WCore.G X_s') by vauto.
          rewrite SUB in *.
          red. exists (mapper_rev' y), (mapper_rev' y); splits.
          { red; split; vauto.
            apply seq_acts_rev; red; vauto. }
          { unfold compose in MAPREVCOMP.
            rewrite MAPREVCOMP; vauto. }
          unfold compose in MAPREVCOMP.
          rewrite MAPREVCOMP; vauto. }
        { rewrite wf_sbE.
          rewrite !codom_seq.
          clear - seq_inj.
          basic_solver 8. }
        rewrite wf_sbE.
        clear - seq_inj.
        basic_solver 8. }
      { rewrite wf_sbE. rewrite !seqA.
        rewrite <- id_inter.
        rewrite SBIN.
        rewrite wf_sbE at 2.
        rewrite !seqA.
        rewrite <- id_inter.
        rewrite !collect_rel_seq.
        { repeat apply seq_mori; vauto.
          { intros x y COND.
            destruct COND as [EQ INE]; subst.
            assert (SUB : G_s' = WCore.G X_s') by vauto.
            rewrite SUB in *.
            red. exists (mapper_rev' y), (mapper_rev' y); splits.
            { red; split; vauto.
              apply seq_acts_rev; red; vauto. }
            { unfold compose in MAPREVCOMP.
              rewrite MAPREVCOMP; vauto. }
            unfold compose in MAPREVCOMP.
            rewrite MAPREVCOMP; vauto. }
          intros x y COND.
          destruct COND as [EQ [INE ISR]]; subst.
          assert (SUB : G_s' = WCore.G X_s') by vauto.
          rewrite SUB in *.
          unfold is_rel, mod in ISR.
          rewrite seq_lab_rev in ISR; vauto.
          red. exists (mapper_rev' y), (mapper_rev' y); splits.
          { red; split; vauto.
            repeat split.
            { apply seq_acts_rev; red; vauto. }
            unfold is_rel. unfold compose in ISR; vauto. }
          { unfold compose in MAPREVCOMP.
            rewrite MAPREVCOMP; vauto. }
          unfold compose in MAPREVCOMP.
          rewrite MAPREVCOMP; vauto. }
        { rewrite wf_sbE.
          rewrite !codom_seq.
          clear - seq_inj.
          basic_solver 8. }
        rewrite wf_sbE.
        clear - seq_inj.
        basic_solver 8. }
      rewrite wf_sbE. rewrite !seqA.
      rewrite <- id_inter.
      rewrite <- seqA.
      rewrite <- id_inter.
      rewrite SBIN.
      rewrite wf_sbE at 2.
      rewrite !seqA.
      rewrite <- id_inter.
      arewrite (⦗F G_t' ∩₁ Rel G_t'⦘ ⨾ ⦗E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t' ∩₁ (W_t' ∩₁ Rlx G_t')⦘ ≡
      ⦗F G_t' ∩₁ Rel G_t' ∩₁ E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t' ∩₁ (W_t' ∩₁ Rlx G_t')⦘).
      { rewrite <- seqA.
        rewrite <- id_inter; vauto. }
      rewrite !collect_rel_seq.
      { repeat apply seq_mori; vauto.
        { intros x y COND.
          destruct COND as [EQ [[ISF ISREL] INE]]; subst.
          assert (SUB : G_s' = WCore.G X_s') by vauto.
          rewrite SUB in *.
          unfold is_rel, mod in ISREL.
          rewrite seq_lab_rev in ISREL; vauto.
          red. exists (mapper_rev' y), (mapper_rev' y); splits.
          { red; split; vauto.
            repeat split.
            { unfold is_r. unfold compose in ISREL; vauto. }
            { unfold is_rlx. unfold compose in ISREL; vauto. }
            apply seq_acts_rev; red; vauto. }
          { unfold compose in MAPREVCOMP.
            rewrite MAPREVCOMP; vauto. }
          unfold compose in MAPREVCOMP.
          rewrite MAPREVCOMP; vauto. }
        intros x y COND.
        destruct COND as [EQ [INE [ISF ISA]]]; subst.
        assert (SUB : G_s' = WCore.G X_s') by vauto.
        rewrite SUB in *.
        unfold is_rlx, mod in ISA.
        rewrite seq_lab_rev in ISA; vauto.
        red. exists (mapper_rev' y), (mapper_rev' y); splits.
        { red; split; vauto.
          repeat split.
          { apply seq_acts_rev; red; vauto. }
          { unfold is_r. unfold compose in ISA; vauto. }
          unfold is_rlx. unfold compose in ISA; vauto. }
        { unfold compose in MAPREVCOMP.
          rewrite MAPREVCOMP; vauto. }
        unfold compose in MAPREVCOMP.
        rewrite MAPREVCOMP; vauto. }
      { rewrite wf_sbE.
        rewrite !codom_seq.
        clear - seq_inj.
        basic_solver 8. }
      rewrite wf_sbE.
      clear - seq_inj.
      basic_solver 8. }
    vauto. }
  { rewrite <- (seq_lab SIMRELQ); vauto. }
  { assert (SBEQ : sb G_s' ≡ mapper' ↑ sb_t' \ po_seq X_s' t_1 t_2).
    { rewrite <- (seq_sb SIMRELQ).
      rewrite minus_union_l. rewrite TID.
      rewrite minusK. split; [| basic_solver].
      intros x y COND.
      left. split; vauto.
      intros FLS.
      unfold po_seq in FLS.
      destruct FLS as [[TID1 INE1] [TID2 INE2]].
      unfold sb in COND. unfold ext_sb in COND.
      clear - COND TID1 TID2 NINIT1 NINIT2 THRDNEQ.
      destruct COND as [x0 [[EQQ1 INEE1] [x1 [COND2 [EQQ2 INEE2]]]]].
      subst. desf. basic_solver 42. }
    arewrite (WCore.G X_s' = G_s').
    rewrite SBEQ.
    intros x y COND.
    destruct COND as [[CDMAP POSEQ] COND2].
    destruct CDMAP as [x0 [x1 [CND [M1 M2]]]].
    unfold collect_rel.
    exists x0, x1; split; vauto.
    split; vauto.
    unfold same_loc in *.
    destruct SIMRELQ.
    unfold loc. rewrite !seq_lab.
    { unfold compose; vauto. }
    all : apply wf_sbE in CND.
    all : destruct CND as [x2 [[EQ1 CD1] [x3 [COND [EQ2 CD2]]]]]; vauto. }
  { apply INV'. }
  apply wf_transition with (X_t := X_t')
          (t_1 := t_1) (t_2 := t_2)
          (mapper := mapper') (mapper_rev := mapper_rev')
          (ptc_1 := ptc_1); vauto.
  rewrite <- TID; vauto.
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
    << NINIT' : ~is_init e >> /\
    << NOTIN : ~E_s (ThreadEvent t_2 (index e - t_1_len)) >> /\
    << TID : tid (ThreadEvent t_2 (index e - t_1_len)) = t_2 >>). 
    { unfold NW; splits; vauto.
      intros FLS. unfold is_init in FLS.
      desf. unfold tid in T1.
      apply NINIT1; vauto. }
  unfold NW in NEWE. destruct NEWE as (NINIT & NINIT' & NOTIN & TID).

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
    { rewrite set_collect_union.
      rewrite MAPREVSUB.
      unfold mapper_rev'.
      rewrite set_collect_eq.
      rewrite upds, EQACTS.
      rewrite (seq_acts_rev SIMREL); vauto. }
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
    { intros x MAP TIDS.
      destruct classic with (x = (ThreadEvent t_2 (index e - t_1_len))) as [EQ | NEQ].
      { subst x. unfold mapper_rev'. rewrite upds; vauto. }
      destruct MAP as [INE | MAP].
      { unfold mapper_rev'.
        rewrite updo; vauto.
        apply (seq_mapeq_rev SIMREL) in INE; vauto. }
      unfold mapper_rev'.
      rewrite updo; vauto. }
    { intros e' INE TID2.
      apply EQACTS in INE.
      destruct INE as [C1 | C2].
      { destruct classic with (e' = e) as [EQ | NEQ].
        { subst e'. unfold mapper'. rewrite upds; vauto. }
        unfold mapper'. rewrite updo; vauto.
        apply (seq_mapto SIMREL) in C1; vauto.
        unfold mapper' in TID2. rewrite updo in TID2; vauto. }
      subst e'. unfold mapper'. rewrite upds; vauto. }
    { intros e' INE TID2.
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
    { intros x INE TID2.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x; vauto. }
      unfold mapper' in TID2.
      rewrite updo in TID2.
      { destruct SIMREL.
        apply seq_thrd in TID2.
        { rewrite TID2; vauto. }
        apply EQACTS in INE.
        destruct INE as [C1 | C2]; vauto. }
      vauto. } 
    { intros x INE TID2.
      unfold mapper_rev'.
      destruct classic with (x = (ThreadEvent t_2 (index e - t_1_len))) as [EQ | NEQ].
      { subst x. rewrite upds.
        destruct e.
        { desf. }
        unfold tid in T1. rewrite T1.
        unfold Events.index in *.
        unfold SequentBase.t_1_len in *.
        unfold t_1_len in *.
        assert (INDEQ : index = index - length (ptc_1 t_1) + length (ptc_1 t_1)).
        { lia. }
        rewrite INDEQ at 1; vauto. }
      rewrite updo.
      { apply (seq_maprev SIMREL); vauto.
        destruct INE; vauto.
        exfalso. apply NEQ; vauto. }
      vauto. }
    { intros x INE TID2.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper'.
        rewrite upds. exfalso. desf. }
      unfold mapper'.
      rewrite updo; vauto.
      destruct SIMREL.
      rewrite seq_out; vauto.
      apply EQACTS in INE.
      destruct INE as [C1 | C2]; vauto. }
    { intros x INE TIDS IDXS.
      destruct classic with (x = e) as [EQ | NEQ].
      { unfold SequentBase.t_1_len in *.
        unfold t_1_len in *.
        subst x. exfalso.
        lia. }
      unfold mapper'.
      rewrite updo; vauto.
      apply (seq_out_snd SIMREL); vauto.
      apply EQACTS in INE.
      destruct INE as [C1 | C2]; vauto. }
    { intros x INE TIDS IDXS.
      destruct classic with (x = e) as [EQ | NEQ].
      { unfold mapper'. subst x.
        rewrite upds.
        unfold t_1_len in *.
        unfold SequentBase.t_1_len in *.
        vauto. }
      unfold mapper'.
      rewrite updo; vauto.
      apply (seq_out_move SIMREL); vauto.
      apply EQACTS in INE.
      destruct INE as [C1 | C2]; vauto. }
    { intros e' NINE.
      destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. exfalso. apply NINE.
        apply EQACTS; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_rest SIMREL); vauto.
      intros INN. apply NINE.
      apply EQACTS; vauto. }
    intros e' NINE.
    destruct classic with (e' = (ThreadEvent t_2 (index e - t_1_len))) as [EQ | NEQ].
    { subst e'. exfalso.
      apply NINE; vauto. }
    unfold mapper_rev'. rewrite updo; vauto.
    apply (seq_rest_rev SIMREL); vauto.
    intros FALSE. apply NINE; vauto. }
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
    { destruct ADD. destruct SIMRELQ.
      unfold mapper', mapper_rev'.
      apply functional_extensionality; ins.
      destruct classic with (x = (ThreadEvent t_2 (index e - t_1_len))) as [EQ | NEQ].
      { subst x. rewrite !upds. vauto.
        rewrite add_event_lab.
        unfold compose. rewrite upds.
        rewrite upds; vauto. }
      rewrite !updo; vauto.
      { rewrite add_event_lab.
        unfold compose. rewrite updo; vauto.
        { destruct SIMREL.
          destruct classic with (E_s x) as [INN | NINN].
          { rewrite updo; vauto.
            rewrite seq_lab_rev0; vauto. }
          rewrite updo; vauto.
          rewrite seq_rlab0; vauto. }
        rewrite updo; vauto.
        destruct classic with (E_s x) as [INN | NINN].
        { destruct SIMREL.
          intros FALSE.
          assert (STT : mapper (mapper_rev x) = mapper e)
                  by vauto.
          unfold compose in MAPREVR.
          rewrite MAPREVR in STT.
          { unfold id in STT.
            assert (HLP : E_t (mapper_rev x)).
            { apply seq_acts_rev0.
              red; exists x; vauto. }
            rewrite FALSE in HLP.
            apply seq_mapto0 in HLP.
            { subst x.
              unfold SequentBase.t_1_len, t_1_len in *.
              desf. }
            apply seq_out_move0 in HLP; vauto.
            rewrite HLP. unfold tid; vauto. }
          vauto. }
        admit. (* ??? *) }
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
    arewrite (G_s' = WCore.G X_s').
    apply wf_transition with (X_t := X_t')
          (t_1 := t_1) (t_2 := t_2)
          (mapper := mapper') (mapper_rev := mapper_rev')
          (ptc_1 := ptc_1); vauto. }
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
  apply wf_transition with (X_t := X_t')
        (t_1 := t_1) (t_2 := t_2)
        (mapper := mapper') (mapper_rev := mapper_rev')
        (ptc_1 := ptc_1); vauto.
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
    { rewrite EQACTS.
      rewrite set_collect_union.
      rewrite set_collect_union.
      apply set_union_more.
      { split.
        { intros x COND.
          destruct classic with (x = e) as [EQ | NEQ].
          { subst x. unfold mapper'.
            desf. }
          unfold set_collect.
          exists (mapper' x). splits; vauto.
          unfold mapper'.
          rewrite updo; vauto.
          unfold mapper_rev'.
          rewrite updo; vauto.
          { apply MAPREV; vauto. }
          intros FALSE.
          assert (INE : E_s e).
          { destruct SIMREL.
            apply seq_acts.
            red; vauto. }
          desf. }
        intros x COND.
        destruct COND as [x0 [[x1 [INE MAP1]] MAP2]].
        apply MAPREVDOM.
        unfold set_collect.
        exists x0; splits; vauto.
        { destruct classic with (x1 = e) as [EQ | NEQ].
          { subst x1. unfold mapper'.
            desf. }
          unfold mapper'.
          rewrite updo; vauto.
          destruct SIMREL.
          apply seq_acts.
          red; vauto. }
        unfold mapper'.
        rewrite updo.
        { unfold mapper_rev'.
          rewrite updo; vauto.
          intros FALSE.
          assert (INES : E_s e).
          { destruct SIMREL.
            apply seq_acts.
            red; vauto. }
          desf. }
        intros FALSE. desf. }
      rewrite MAPER_E.
      rewrite MEPERREV_E; vauto. }
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
    { intros x MAP TIDS.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper_rev'. rewrite upds; vauto. }
      destruct MAP as [x0 [INE MAP]].
      unfold mapper_rev'.
      rewrite updo; vauto.
      unfold mapper'.
      rewrite updo; vauto.
      { unfold mapper' in TIDS.
        rewrite updo in TIDS; vauto.
        { destruct SIMREL.
          apply seq_mapeq_rev in TIDS; vauto.
          apply seq_acts.
          red; exists x0; splits; vauto.
          apply EQACTS in INE.
          destruct INE as [C1 | C2]; vauto.
          apply seq_mapeq in TIDS; vauto.
          { unfold mapper' in NEQ.
            rewrite upds in NEQ.
            desf. }
          unfold mapper' in NEQ.
          rewrite upds in NEQ.
          desf. }
        intros FLS. subst.
        unfold mapper' in NEQ.
        rewrite upds in NEQ. desf. }
      intros FLS. subst.
      unfold mapper' in NEQ.
      rewrite upds in NEQ. desf. }
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
    { intros e' INE TID2.
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
    { intros x INE TID2.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper' in TID2.
        rewrite upds in TID2. exfalso.
        apply wf_threads in INE; [ | apply INV'].
        destruct ADD. apply add_event_threads in INE.
        apply T2NOTIN; vauto. }
      unfold mapper' in TID2.
      rewrite updo in TID2.
      { destruct SIMREL.
        apply seq_thrd in TID2.
        { rewrite TID2; vauto. }
        apply EQACTS in INE.
        destruct INE as [C1 | C2]; vauto. }
      vauto. }
    { intros x INE TID2.
      unfold mapper_rev'.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper' in INE.
        destruct INE as [x0 [INE MAP]].
        rewrite upds.
        destruct classic with (x0 = e) as [EQ1 | NEQ1].
        { subst x0. apply wf_threads in INE; [ | apply INV'].
          destruct ADD. apply add_event_threads in INE.
          exfalso. apply T2NOTIN; vauto. }
        apply EQACTS in INE.
        destruct INE as [C1 | C2]; vauto.
        apply wf_threads in C1; [ | apply INV].
        destruct ADD. apply add_event_threads in C1.
        exfalso. apply T2NOTIN; vauto. }
      rewrite updo; vauto.
      rewrite (seq_maprev SIMREL); vauto.
      apply (seq_acts SIMREL).
      apply MAPSUB.
      unfold set_collect in INE.
      destruct INE as [x0 [INE MAP]].
      apply EQACTS in INE.
      destruct INE as [C1 | C2].
      { vauto. }
      rewrite <- C2 in MAP.
      assert (MAPNORM : mapper' e = e).
      { rewrite set_collect_eq in MAPER_E.
        apply MAPER_E; vauto. }
      desf. }
    { intros x INE TID2.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper'.
        rewrite upds; vauto. }
      unfold mapper'.
      rewrite updo; vauto.
      destruct SIMREL.
      rewrite seq_out; vauto.
      apply EQACTS in INE.
      destruct INE as [C1 | C2]; vauto. }
    { intros x INE TIDS IDXS.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper'.
        rewrite upds. desf. }
      unfold mapper'.
      rewrite updo; vauto.
      destruct SIMREL.
      rewrite seq_out_snd; vauto.
      apply EQACTS in INE.
      destruct INE as [C1 | C2]; vauto. }
    { intros x INE TIDS IDXS.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst. clear - IDXS TID.
        exfalso. unfold t_1_len in *.
        unfold SequentBase.t_1_len in *.
        lia. }
      unfold mapper'.
      rewrite updo; vauto.
      destruct SIMREL.
      rewrite seq_out_move; vauto.
      apply EQACTS in INE.
      destruct INE as [C1 | C2]; vauto. }
    { intros e' NINE.
      destruct classic with (e' = e) as [EQ | NEQ].
      { subst e'. unfold mapper'. rewrite upds; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_rest SIMREL); vauto.
      intros FALSE. apply NINE.
      apply EQACTS. unfold set_union.
      left; vauto. }
    intros e' NINE.
    destruct classic with (e' = e) as [EQ | NEQ].
    { subst e'. unfold mapper_rev'. rewrite upds; vauto. }
    unfold mapper_rev'. rewrite updo; vauto.
    apply (seq_rest_rev SIMREL); vauto.
    intros FALSE. apply NINE. unfold set_collect.
    exists (mapper_rev e'). split.
    { apply EQACTS. left. apply MAPREVDOM.
      basic_solver. }
    unfold mapper'. rewrite updo; vauto.
    { apply MAPREVR; vauto. }
    intros FLS.
    assert (WRG : E_t e).
    { apply MAPREVDOM. basic_solver 4. }
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
          destruct classic with (E_s x) as [INN | NINN].
          { rewrite updo; vauto.
            rewrite seq_lab_rev0; vauto. }
          rewrite updo; vauto.
          rewrite seq_rlab0; vauto. }
        rewrite updo; vauto.
        destruct classic with (E_s x) as [INN | NINN].
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
    arewrite (G_s' = WCore.G X_s').
    apply wf_transition with (X_t := X_t')
          (t_1 := t_1) (t_2 := t_2)
          (mapper := mapper') (mapper_rev := mapper_rev')
          (ptc_1 := ptc_1); vauto. }
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
  apply wf_transition with (X_t := X_t')
          (t_1 := t_1) (t_2 := t_2)
          (mapper := mapper') (mapper_rev := mapper_rev')
          (ptc_1 := ptc_1); vauto.
Admitted.

End SimrelStep.
