Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import SubToFullExec.
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
From imm Require Import Events Execution Execution_eco SubExecution.
Require Import Setoid Morphisms Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section SequentWf.

Variable X_t X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.
Variable mapper_rev : actid -> actid.

Variable dtrmt_t cmt_t : actid -> Prop.
Variable thrdle : relation thread_id.
Variable f_t : actid -> actid.

Variable ptc_1 ptc_2 : program_trace.

Notation "'G_t'" := (WCore.G X_t).
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

Definition t_12_len := length (ptc_2 t_2).
Definition t_1_len := length (ptc_1 t_1).
Definition t_2_len := length (ptc_1 t_2).

Hypothesis INV : seq_simrel_inv X_t.

Lemma wf_transition
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper mapper_rev ptc_1) :
  Wf G_s.
Proof using.
  assert (INDLEMMA : forall x y (NNIT : tid x <> tid_init) (EQT : tid x = tid y) (EQI : index x = index y),
          x = y).
  { clear. intros x y NNIT EQT EQI.
    destruct x; destruct y; desf; ins.
    desf. }
  constructor.
  { intros a b COND.
    destruct COND as [INA [INB [NEQ [TIDS NINIT]]]].
    intros FLS.
    specialize INDLEMMA with a b.
    apply NEQ; apply INDLEMMA; vauto.
    unfold is_init in NINIT.
    clear - NINIT. unfold not in NINIT.
    unfold not. intros FLS.
    unfold tid in FLS.
    destruct a.
    { apply NINIT; vauto. }
    admit. (* ??? *) }
  { rewrite (seq_data SIMREL); vauto. }
  { rewrite (seq_data SIMREL); clear; [ basic_solver 4 ]. }
  { rewrite (seq_addr SIMREL); vauto. }
  { rewrite (seq_addr SIMREL); clear; [ basic_solver 4 ]. }
  { rewrite (seq_ctrl SIMREL); vauto. }
  { rewrite (seq_ctrl SIMREL); clear; [ basic_solver 4 ]. }
  { rewrite (seq_ctrl SIMREL); clear; [ basic_solver 4 ]. }
  { split; [| basic_solver 9 ].
    rewrite (seq_rmw SIMREL); vauto.
    intros x y COND. destruct COND as [x0 [y0 [RMW [M1 M2]]]].
    apply wf_rmwE in RMW.
    { destruct RMW as [x1 [[EQ1 INE1] [x2 [PTH [EQ2 INE2]]]]].
      subst. destruct SIMREL.
      apply seq_lab in INE1, INE2.
      apply wf_rmwD in PTH.
      { destruct PTH as [x2 [[EQ1 RD] [x3 [PTH [EQ2 WT]]]]].
        subst. unfold seq. exists (mapper x2); splits.
        { red; splits; vauto.
          unfold compose in INE1.
          unfold is_r in *.
          rewrite <- INE1; vauto. }
        exists (mapper y0); splits; vauto.
        red; splits; vauto. unfold is_w in *.
        unfold compose in INE2.
        rewrite <- INE2; vauto. }
      apply INV. }
    apply INV. }
  { rewrite (seq_rmw SIMREL).
    intros x y COND.
    destruct COND as [x0 [y0 [PTH [M1 M2]]]].
    subst. 
    apply wf_rmwE in PTH; [| apply INV].
    destruct PTH as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]].
    subst.
    apply wf_rmwl in PTH; [| apply INV].
    unfold same_loc in *.
    apply (seq_lab SIMREL) in INE1, INE2.
    unfold compose in *.
    unfold loc in *.
    rewrite <- INE1.
    rewrite <- INE2; vauto. }
  { rewrite (seq_rmw SIMREL).
    intros x y COND.
    destruct COND as [x0 [y0 [PTH [M1 M2]]]].
    subst.
    apply wf_rmwE in PTH; [| apply INV].
    destruct PTH as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]].
    subst. apply wf_rmwi in PTH; [| apply INV].
    admit. (* false *) }
  { split; [| basic_solver 4].
    rewrite (seq_rf SIMREL).
    intros x y COND.
    destruct COND as [x0 [y0 [PTH [M1 M2]]]].
    subst.
    apply wf_rfE in PTH; [| apply INV].
    destruct PTH as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]].
    subst.
    unfold seq.
    exists (mapper x2); split.
    { red; split; vauto.
      destruct SIMREL. apply seq_codom.
      red; exists x2; vauto. }
    exists (mapper y0); split; vauto.
    red; split; vauto.
    destruct SIMREL. apply seq_codom.
    red; exists y0; vauto. }
  { split; [| basic_solver 4].
    rewrite (seq_rf SIMREL).
    intros x y COND.
    destruct COND as [x0 [y0 [PTH [M1 M2]]]].
    subst.
    apply wf_rfE in PTH; [| apply INV].
    destruct PTH as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]].
    subst.
    apply wf_rfD in PTH; [| apply INV].
    destruct PTH as [x3 [[EQ1 WT] [x4 [PTH [EQ2 RD]]]]].
    subst. 
    destruct SIMREL.
    apply seq_lab in INE1, INE2.
    unfold compose in *.
    unfold seq. exists (mapper x3); splits.
    { red; splits; vauto.
      unfold compose in INE1.
      unfold is_w in *.
      rewrite <- INE1; vauto. }
    exists (mapper y0); splits; vauto.
    red; splits; vauto. unfold is_r in *.
    unfold compose in INE2.
    rewrite <- INE2; vauto. }
  { rewrite (seq_rf SIMREL).
    intros x y COND.
    destruct COND as [x0 [y0 [PTH [M1 M2]]]].
    subst. 
    apply wf_rfE in PTH; [| apply INV].
    destruct PTH as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]].
    subst.
    apply wf_rfl in PTH; [| apply INV].
    unfold same_loc in *.
    apply (seq_lab SIMREL) in INE1, INE2.
    unfold compose in *.
    unfold loc in *.
    rewrite <- INE1.
    rewrite <- INE2; vauto. }
  { rewrite (seq_rf SIMREL).
    unfold funeq. intros a b MAP.
    destruct MAP as [x0 [y0 [PTH [M1 M2]]]].
    subst.
    apply wf_rfE in PTH; [| apply INV].
    destruct PTH as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]].
    subst.
    apply wf_rfv in PTH; [| apply INV].
    apply (seq_lab SIMREL) in INE1.
    apply (seq_lab SIMREL) in INE2.
    unfold compose in *.
    unfold val in *.
    rewrite <- INE1.
    rewrite <- INE2; vauto. }
  { rewrite (seq_rf SIMREL).
    unfold functional.
    intros x y z M M'.
    destruct M as [x0 [y0 [PTH1 [M1 M2]]]]; subst.
    destruct M' as [x1 [y1 [PTH2 [M3 M4]]]]; subst.
    destruct SIMREL.
    assert (EQQ : y1 = y0).
    { apply seq_inj; vauto.
      { apply wf_rfE in PTH2; [| apply INV].
        destruct PTH2 as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]]; vauto. }
      apply wf_rfE in PTH1; [| apply INV].
      destruct PTH1 as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]]; vauto. }
    subst.
    assert (EQQ' : x0 = x1).
    { destruct wf_rff with (G := G_t) (x := y0)
                (y := x0) (z := x1); vauto.
      apply INV. }
    basic_solver. }
  { split; [| basic_solver].
    rewrite (seq_co SIMREL).
    intros x y COND.
    destruct COND as [x0 [y0 [PTH [M1 M2]]]].
    subst.
    apply wf_coE in PTH; [| apply INV].
    destruct PTH as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]].
    subst.
    unfold seq.
    exists (mapper x2); split.
    { red; split; vauto.
      destruct SIMREL. apply seq_codom.
      red; exists x2; vauto. }
    exists (mapper y0); split; vauto.
    red; split; vauto.
    destruct SIMREL. apply seq_codom.
    red; exists y0; vauto. }
  { split; [| basic_solver 4].
    rewrite (seq_co SIMREL).
    intros x y COND.
    destruct COND as [x0 [y0 [PTH [M1 M2]]]].
    subst.
    apply wf_coE in PTH; [| apply INV].
    destruct PTH as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]].
    subst.
    apply wf_coD in PTH; [| apply INV].
    destruct PTH as [x3 [[EQ1 WT] [x4 [PTH [EQ2 RD]]]]].
    subst. 
    destruct SIMREL.
    apply seq_lab in INE1, INE2.
    unfold compose in *.
    unfold seq. exists (mapper x3); splits.
    { red; splits; vauto.
      unfold compose in INE1.
      unfold is_w in *.
      rewrite <- INE1; vauto. }
    exists (mapper y0); splits; vauto.
    red; splits; vauto. unfold is_w in *.
    unfold compose in INE2.
    rewrite <- INE2; vauto. }
  { rewrite (seq_co SIMREL).
    intros x y COND.
    destruct COND as [x0 [y0 [PTH [M1 M2]]]].
    subst. 
    apply wf_coE in PTH; [| apply INV].
    destruct PTH as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]].
    subst.
    apply wf_col in PTH; [| apply INV].
    unfold same_loc in *.
    apply (seq_lab SIMREL) in INE1, INE2.
    unfold compose in *.
    unfold loc in *.
    rewrite <- INE1.
    rewrite <- INE2; vauto. }
  { rewrite (seq_co SIMREL).
    unfold transitive.
    intros x y z M M'.
    destruct M as [x0 [y0 [PTH1 [M1 M2]]]]; subst.
    destruct M' as [x1 [y1 [PTH2 [M3 M4]]]]; subst.
    destruct SIMREL.
    red; exists x0, y1; splits; vauto.
    assert (EQQ : x1 = y0).
    { apply seq_inj; vauto.
      { apply wf_coE in PTH2; [| apply INV].
        destruct PTH2 as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]]; vauto. }
      apply wf_coE in PTH1; [| apply INV].
      destruct PTH1 as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]]; vauto. }
    subst.
    apply co_trans with (x := x0) (y := y0) (z := y1); vauto.
    apply INV. }
  { intros ol.
    rewrite (seq_co SIMREL).
    unfold is_total.
    intros a COND1 b COND2 NEQ.
    unfold collect_rel.
    destruct COND1 as [[INE1 ISW1] LOC1].
    destruct COND2 as [[INE2 ISW2] LOC2].
    destruct SIMREL.
    apply seq_acts in INE1, INE2.
    destruct INE1 as [a0 [INE1 MAP1]].
    destruct INE2 as [b0 [INE2 MAP2]].
    destruct wf_co_total with (G := G_t) (ol := ol)
                    (a := a0) (b := b0).
    { apply INV. }
    { split.
      { split; vauto.
        apply seq_lab in INE1.
        unfold compose in *.
        unfold is_w in *.
        rewrite INE1; vauto. }
      unfold loc in *.
      apply seq_lab in INE1.
      unfold compose in *.
      rewrite INE1; vauto. }
    { split.
      { split; vauto.
        apply seq_lab in INE2.
        unfold compose in *.
        unfold is_w in *.
        rewrite INE2; vauto. }
      unfold loc in *.
      apply seq_lab in INE2.
      unfold compose in *.
      rewrite INE2; vauto. }
    { intros FALSE.
      apply NEQ. subst; vauto. }
    { left. exists a0, b0; splits; vauto. }
    right. exists b0, a0; splits; vauto. }
  { rewrite (seq_co SIMREL).
    unfold irreflexive.
    intros x COND.
    destruct COND as [x0 [y0 [PTH1 [M1 M2]]]]; subst.
    destruct co_irr with (G := G_t) (x := x0); [apply INV|].
    assert (EQQ : y0 = x0).
    { apply (seq_inj SIMREL); vauto.
      { apply wf_coE in PTH1; [| apply INV].
        destruct PTH1 as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]]; vauto. }
      apply wf_coE in PTH1; [| apply INV].
      destruct PTH1 as [x2 [[EQ1 INE1] [x3 [PTH [EQ2 INE2]]]]]; vauto. }
    subst; vauto. }
  { intros l COND.
    destruct COND.
    destruct H as [INE LOC].
    apply (seq_acts SIMREL) in INE.
    destruct INE as [x0 [INE MAP]].
    apply (seq_acts SIMREL).
    unfold set_collect. exists (InitEvent l); split; vauto.
    { apply wf_init; [apply INV |].
      exists x0; split; vauto.
      unfold loc in *. apply (seq_lab SIMREL) in INE.
      unfold compose in *.
      rewrite INE; vauto. }
    rewrite (seq_init SIMREL); vauto. }
  { intros l.
    assert (INE1 : E_s (InitEvent l)).
    { apply (seq_acts SIMREL).
      exists (InitEvent l).
      split; [now apply (rsr_init_acts INV) |].
      destruct SIMREL.
      rewrite seq_init; vauto. }
    destruct SIMREL.
    apply seq_lab_rev in INE1.
    rewrite INE1.
    unfold compose.
    rewrite seq_init_rev; vauto.
    apply wf_init_lab; apply INV. }
  { rewrite (seq_rmw_dep SIMREL); vauto. }
  { rewrite (seq_rmw_dep SIMREL); basic_solver 4. }
  intros e INE.
  assert (INE' : E_s e) by vauto.
  destruct SIMREL.
  apply seq_acts in INE.
  destruct INE as [e0 [INE MAP]].
  assert (INE2 : E_t e0) by vauto.
  apply wf_threads in INE; [| apply INV].
  rewrite <- MAP.
  apply seq_threads.
  destruct classic with (tid (mapper e0) = t_2).
  { right; vauto. }
  left. apply seq_mapeq in H.
  { rewrite H; vauto. }
  vauto.
Admitted.

End SequentWf.