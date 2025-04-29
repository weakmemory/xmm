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

Section SequentReexec.

Variable X_t X_t' X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.
Variable mapper_rev : actid -> actid.

Variable dtrmt_t cmt_t : actid -> Prop.
Variable thrdle : relation thread_id.
Variable f_t : actid -> actid.

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
Hypothesis STEP : WCore.reexec_gen X_t X_t' f_t dtrmt_t cmt_t thrdle.

Definition t_12_len := length (ptc_2 t_2).
Definition t_1_len := length (ptc_1 t_1).
Definition t_2_len := length (ptc_1 t_2).

(* Definition cmt' := mapper ↑₁ cmt_t.
Definition dtrmt' := mapper ↑₁ dtrmt_t. *)

Definition relation_lowering (A : Type) (r : relation A) (P : A -> Prop) : relation A :=
  fun x y => r x y /\ P x /\ P y.

Lemma codom_ct_union (A : Type) (r r' : relation A) :
  codom_rel ((r ∪ r')⁺) ≡₁ codom_rel r ∪₁ codom_rel r'.
Proof using.
  rewrite codom_ct.
  unfold codom_rel; basic_solver.
Qed.

Lemma rel_low (A : Type) (r : relation A) (P : A -> Prop) :
  relation_lowering r P ≡ r ∩ (P × P).
Proof using.
  unfold relation_lowering. basic_solver.
Qed.

Lemma codom_crossed (A : Type) (P P' : A -> Prop) :
  codom_rel (P × P') ⊆₁ P'.
Proof using.
  unfold codom_rel. basic_solver.
Qed.

Lemma codom_rel_low (A : Type) (r : relation A) (P : A -> Prop) :
  codom_rel (relation_lowering r P) ⊆₁ codom_rel r ∩₁ P.
Proof using.
  rewrite rel_low. basic_solver.
Qed.

Definition thrdle' := thrdle ∪ eq t_2 × eq t_1 ∪ (dom_rel (thrdle ⨾ ⦗eq t_1⦘) \₁ eq t_2) × eq t_2
                      ∪ eq t_2 × (codom_rel (⦗eq t_1⦘ ⨾ thrdle) \₁ eq t_2)
                      ∪ eq tid_init × codom_rel (thrdle).

Hypothesis INV : seq_simrel_inv X_t.
Hypothesis INV' : seq_simrel_inv X_t'.

Lemma simrel_step_reex
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper mapper_rev ptc_1) :
  exists (X_s' : WCore.t) (mapper' : actid -> actid) (mapper_rev' : actid -> actid)
    (dtrmt' : actid -> Prop) (cmt' : actid -> Prop),
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' mapper_rev' ptc_1 >> /\
    << REX : WCore.reexec X_s X_s' id dtrmt' cmt' >>.
Proof using.

  set (mapper' := fun x => ifP (~ E_t' x) then x else
                           (ifP ((tid x) <> t_1) then x
                           else (ifP index x < t_1_len then x
                           else ThreadEvent t_2 (index x - t_1_len)))).

  set (G_s' := {|
    acts_set := mapper' ↑₁ E_t';
    threads_set := threads_set G_s;
    lab := lab_t' ∘ (fun x => ifP (~ (mapper' ↑₁ E_t') x) then x else
                              ( ifP ((tid x) <> t_2) then x
                              else ThreadEvent t_1 (t_1_len + index x)));
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

  set (mapper_rev' := fun x => ifP (~ (acts_set G_s') x) then x else
                            ( ifP ((tid x) <> t_2) then x
                            else ThreadEvent t_1 (t_1_len + index x))).

  set (dtrmt' := mapper' ↑₁ dtrmt_t).
  set (cmt' := mapper' ↑₁ cmt_t).

  exists X_s', mapper', mapper_rev', dtrmt', cmt'.
  assert (threads_set G_t ≡₁ threads_set G_t') as TSET.
  { symmetry. apply reex_thrd_preserve with (f := f_t)
      (dtrmt := dtrmt_t) (cmt := cmt_t)
      (thrdle := thrdle); vauto. }
  assert (MAPCOMP : eq_dom E_t' (mapper_rev' ∘ mapper') id).
  { unfold mapper', mapper_rev'.
    unfold eq_dom. intros x INE.
    unfold compose. desf; vauto.
    { exfalso.
      apply n. unfold set_collect.
      exists x; split; vauto.
      unfold mapper'. desf; vauto. }
    { unfold not in n0. apply NNPP in n0.
      unfold tid in *.
      apply wf_threads in INE; vauto.
      { apply TSET in INE.
        exfalso. desf. }
      apply INV'. }
    { unfold not in n0. apply NNPP in n0.
      clear - n0 INE TSET T2NOTIN INV'.
      apply wf_threads in INE; vauto.
      { exfalso. apply TSET in INE.
        desf. }
      apply INV'. }
    unfold not in n0, n2. apply NNPP in n0, n2.
    clear - n0 n2 n3 THRDNEQ NINIT1.
    destruct x.
    { clear - n2 NINIT1.
      exfalso; desf. }
    unfold Events.index in *.
    unfold tid in n0. subst.
    unfold id.
    assert (HLP : (t_1_len + (index - t_1_len)) = index).
    { lia. }
    basic_solver. }
  assert (SIMRELQ : seq_simrel X_s' X_t' t_1 t_2
                          mapper' mapper_rev' ptc_1).
  { constructor; vauto.
    { unfold inj_dom. intros x y INX INY MAP.
      unfold mapper' in MAP. desf; vauto.
      { apply wf_threads in INX.
        { unfold tid in INX.
          apply TSET in INX.
          exfalso. desf. }
        apply INV'. }
      { apply wf_threads in INX.
        { unfold tid in INX.
          apply TSET in INX.
          exfalso. desf. }
        apply INV'. }
      { apply wf_threads in INY.
        { unfold tid in INY.
          apply TSET in INY.
          exfalso. desf. }
        apply INV'. }
      { apply wf_threads in INY.
        { unfold tid in INY.
          apply TSET in INY.
          exfalso. desf. }
        apply INV'. }
      destruct x, y.
      { clear - n0 n3 NINIT1.
        unfold not in n0, n3. apply NNPP in n0, n3.
        desf. }
      { clear - n0 n3 NINIT1.
        unfold not in n0, n3. apply NNPP in n0, n3.
        desf. }
      { clear - n0 n3 NINIT1.
        unfold not in n0, n3. apply NNPP in n0, n3.
        destruct n3. desf. }
      clear - n0 n3 n1 n4 H0.
      unfold not in n0, n3.
      apply NNPP in n0, n3.
      unfold tid in n0, n3.
      assert (INDEQ : index = index0).
      { unfold Events.index in *. lia. }
      basic_solver. }
    { intros e INE TIDE.
      unfold mapper' in TIDE.
      desf.
      { unfold mapper'. desf. }
      unfold mapper'. desf; vauto. }
    { intros e INE TIDE.
      unfold mapper' in TIDE.
      desf.
      { assert (FLSTID : threads_set G_t' (tid e)).
        { apply wf_threads in INE; vauto.
          apply INV'. }
        clear - FLSTID TSET T2NOTIN.
        exfalso. apply TSET in FLSTID.
        basic_solver. }
      { assert (FLSTID : threads_set G_t' (tid e)).
        { apply wf_threads in INE; vauto.
          apply INV'. }
        unfold not in n0.
        apply NNPP in n0.
        rewrite n0 in FLSTID.
        apply TSET in FLSTID.
        clear - FLSTID T2NOTIN n0.
        exfalso. desf. }
      clear - n0.
      unfold not in n0.
      apply NNPP in n0.
      desf. }
    { unfold X_s'; ins.
      arewrite ((fun x : actid =>
        ifP ~ (mapper' ↑₁ E_t') x then x
        else (ifP tid x <> t_2 then x
              else
              ThreadEvent t_1
                (t_1_len + index x))) = mapper_rev').
      clear - MAPCOMP.
      unfold eq_dom in *.
      intros x INE. unfold compose.
      apply MAPCOMP in INE.
      unfold compose in INE.
      rewrite INE. basic_solver. }
    { unfold X_s'; ins.
      clear - MAPCOMP.
      unfold eq_dom in *.
      split.
      { intros x INE. unfold set_collect.
        exists (mapper' x); split; vauto.
        apply MAPCOMP in INE.
        basic_solver 8. }
      intros x INE. unfold set_collect in INE.
      destruct INE as [x0 [EQ MAP1]].
      destruct EQ as [x1 [EQ MAP2]].
      subst.
      assert (EQ' : E_t' x1) by vauto.
      apply MAPCOMP in EQ.
      unfold compose in EQ.
      rewrite EQ. basic_solver. }
    { unfold po_seq.
      arewrite (WCore.G X_s' = G_s').
      unfold G_s' at 2. simpls.
      split.
      { apply inclusion_union_l.
        { unfold sb. unfold G_s'; ins.
          rewrite <- collect_rel_eqv.
          intros x y PTH.
          destruct PTH as [x0 [E1 [xm [PTH E2]]]].
          destruct E1 as [x2 [x3 [[EQ1 INE1] [M1 M2]]]]; subst.
          destruct E2 as [x4 [x5 [[EQ2 INE2] [M3 M4]]]]; subst.
          unfold collect_rel.
          exists x3, x5; split; vauto.
          unfold seq. exists x3; split; vauto.
          exists x5; split; vauto.
          unfold mapper' in PTH. desf; vauto.
          { unfold not in n2.
            apply NNPP in n2.
            unfold ext_sb in PTH. desf.
            { basic_solver. }
            unfold ext_sb. desf.
            { clear - n2 NINIT1.
              desf. }
            split.
            { apply wf_threads in INE1.
              { unfold tid in INE1.
                apply TSET in INE1.
                exfalso. desf. }
              apply INV'. }
            unfold Events.index in *.
            lia. }
          { unfold not in n2, n0.
            apply NNPP in n2, n0.
            unfold ext_sb. desf.
            { clear - n2 NINIT1.
              desf. }
            split.
            { unfold tid in n2, n0; vauto. }
            unfold Events.index in *.
            lia. }
          { unfold not in n0.
            apply NNPP in n0.
            unfold ext_sb. desf.
            unfold ext_sb in PTH. desf.
            exfalso. unfold Events.index in *.
            apply wf_threads in INE2.
            { unfold tid in INE2.
              apply TSET in INE2.
              exfalso. desf. }
            apply INV'. }
          { unfold not in n0, n3.
            apply NNPP in n0, n3.
            unfold ext_sb. desf.
            unfold tid in *.
            unfold Events.index in *.
            split; vauto.
            unfold ext_sb in PTH.
            destruct PTH as [EQ IND].
            desf. }
          unfold not in n0, n3.
          apply NNPP in n0, n3.
          unfold ext_sb. desf.
          { unfold tid in *.
            clear - n0 NINIT1. desf. }
          { unfold tid in *.
            clear - n3 NINIT1. desf. }
          unfold tid in *.
          unfold Events.index in *.
          split; vauto.
          unfold ext_sb in PTH.
          destruct PTH as [EQ IND].
          lia. }
        intros x y PTH.
        destruct PTH as [[T1 [x0 [EQ1 M1]]]
                        [T2 [x1 [EQ2 M2]]]].
        unfold collect_rel.
        exists x0, x1; split; vauto.
        unfold sb. unfold seq.
        exists x0; split; vauto.
        exists x1; split; vauto.
        unfold ext_sb. desf.
        { unfold mapper' in M2. desf.
          unfold not in n0.
          apply NNPP in n0.
          unfold tid in *.
          clear - n0 NINIT1. desf. }
        { unfold mapper' in M2. desf.
          unfold not in n0.
          apply NNPP in n0.
          unfold tid in *.
          clear - n0 NINIT1. desf. }
        unfold mapper' in M2. desf.
        { unfold mapper' in T1. desf.
          unfold not in n2.
          apply NNPP in n2.
          unfold tid in *.
          apply wf_threads in EQ2; vauto.
          { apply TSET in EQ2.
            unfold tid in EQ2.
            desf. }
          apply INV'. }
        { unfold mapper' in T1. desf.
          { unfold not in n0, n2.
            apply NNPP in n0, n2.
            unfold tid in *. desf. }
          unfold not in n0, n2.
          apply NNPP in n0, n2.
          unfold tid in *. desf. }
        unfold mapper' in T1. desf.
        { unfold not in n0, n2.
          apply NNPP in n0, n2.
          unfold tid in *. desf.
          split; vauto. unfold Events.index in *.
          lia. }
        unfold not in n0, n2.
        apply NNPP in n0, n2.
        unfold tid in *. desf. }
      intros x y PTH.
      destruct PTH as [x0 [x1 [SB [M1 M2]]]].
      unfold sb in SB.
      destruct SB as [x2 [[EQ1 INE1]
                  [x3 [PTH [EQ2 INE2]]]]]; subst.
      destruct x2.
      { unfold mapper' at 3.
        desf. all : left.
        { unfold sb, G_s'; simpl.
          unfold seq; exists (InitEvent l); split; vauto.
          { red; split; vauto.
            unfold set_collect.
            exists (InitEvent l); split; vauto.
            unfold mapper'. desf; vauto. }
          exists (mapper' x1); split; vauto.
          unfold ext_sb. desf.
          unfold mapper' in Heq. desf. }
        { unfold sb, G_s'; simpl.
          unfold seq; exists (InitEvent l); split; vauto.
          { red; split; vauto.
            unfold set_collect.
            exists (InitEvent l); split; vauto.
            unfold mapper'. desf; vauto. }
          exists (mapper' x1); split; vauto.
          unfold ext_sb. desf.
          unfold mapper' in Heq. desf. }
        unfold not in n0.
        apply NNPP in n0.
        unfold tid in *.
        clear - n0 NINIT1.
        symmetry in n0. desf. }
      destruct x1.
      { unfold ext_sb in PTH; vauto. }
      unfold ext_sb in PTH.
      destruct PTH as [THRD IND]; subst.
      destruct classic with (thread0 = t_1) as [THRD1 | THRD1].
      { destruct classic with (index < t_1_len) as [IND1 | IND1].
        { destruct classic with (index0 < t_1_len) as [IND2 | IND2].
          { unfold mapper'. subst; ins.
            left. desf.
            unfold sb.
            unfold G_s'; ins.
            unfold seq. exists (ThreadEvent t_1 index); split; vauto.
            { red. split; vauto.
              unfold set_collect.
              exists (ThreadEvent t_1 index); split; vauto.
              unfold mapper'. desf; vauto. }
            exists (ThreadEvent t_1 index0); split; vauto.
            red. split; vauto.
            unfold set_collect.
            exists (ThreadEvent t_1 index0); split; vauto.
            unfold mapper'. desf; vauto. }
          subst. right. unfold mapper' at 3 4.
          unfold tid, Events.index.
          unfold tid in *.
          desf. split; split; vauto.
          { unfold set_collect.
            exists (ThreadEvent t_1 index); split; vauto.
            unfold mapper'. desf; vauto. }
          unfold set_collect.
          exists (ThreadEvent t_1 index0); split; vauto.
          unfold mapper'. desf; vauto. }
        destruct classic with (index0 < t_1_len) as [IND2 | IND2].
        { exfalso. clear - IND IND1 IND2.
          apply IND1. lia. }
        left. desf.
        unfold sb. unfold G_s'; ins.
        unfold seq. exists (ThreadEvent t_2 (index - t_1_len)); split.
        { apply collect_rel_eqv.
          unfold collect_rel.
          exists (ThreadEvent t_1 index),
                (ThreadEvent t_1 index); splits; vauto.
          unfold mapper'. desf. }
        exists (ThreadEvent t_2 (index0 - t_1_len)); split.
        { clear - IND IND1 IND2.
          unfold ext_sb; splits; vauto.
          lia. }
        apply collect_rel_eqv.
        unfold collect_rel.
        exists (ThreadEvent t_1 index0),
              (ThreadEvent t_1 index0); splits; vauto.
        unfold mapper'. unfold tid.
        desf. }
      left.
      unfold sb. unfold G_s'; ins.
      unfold seq. exists (ThreadEvent thread0 index); splits; vauto.
      { apply collect_rel_eqv.
        unfold collect_rel.
        exists (ThreadEvent thread0 index),
              (ThreadEvent thread0 index); splits; vauto.
        unfold mapper'.
        desf. }
      exists (ThreadEvent thread0 index0); splits; vauto.
      apply collect_rel_eqv.
      unfold collect_rel.
      exists (ThreadEvent thread0 index0),
            (ThreadEvent thread0 index0); splits; vauto.
      unfold mapper'.
      desf. }
    { arewrite (WCore.G X_s' = G_s').
      unfold G_s'; ins. rewrite <- TSET.
      apply SIMREL. }
    { unfold fixset. intros e INIT.
      unfold mapper'.
      desf.
      unfold not in n0.
      apply NNPP in n0.
      clear - n0 NINIT1 INIT.
      unfold is_init in INIT.
      exfalso. desf. }
    { unfold fixset. intros e INIT.
      unfold mapper_rev'.
      desf.
      unfold not in n0.
      apply NNPP in n0.
      clear - n0 NINIT2 INIT.
      unfold is_init in INIT.
      exfalso. desf. }
    { intros e INE TID2.
      unfold mapper'. 
      desf; vauto.
      unfold mapper' in TID2.
      unfold not in n0.
      apply NNPP in n0.
      desf. }
    { arewrite (WCore.G X_s' = G_s').
      intros e INE TID2.
      unfold mapper_rev'. 
      desf; vauto.  }
    { intros e INE TID2.
      unfold mapper'. desf.
      { unfold mapper' in TID2.
        desf.
        apply wf_threads in INE.
        { clear - INE T2NOTIN TSET.
          apply TSET in INE.
          exfalso. desf. }
        apply INV'. }
      unfold mapper' in TID2.
      desf.
      unfold not in n0, n2.
      apply NNPP in n0, n2.
      apply wf_threads in INE.
      { clear - INE T2NOTIN TSET.
        apply TSET in INE.
        exfalso. desf. }
      apply INV'. }
    { intros e INE TID2.
      unfold mapper'. desf.
      { unfold mapper' in TID2.
        desf.
        apply wf_threads in INE.
        { clear - INE T2NOTIN TSET.
          apply TSET in INE.
          exfalso. desf. }
        apply INV'. }
      { unfold mapper' in TID2.
        desf.
        unfold not in n0, n2.
        apply NNPP in n0, n2.
        apply wf_threads in INE.
        { clear - INE T2NOTIN TSET.
          apply TSET in INE.
          exfalso. desf. }
        apply INV'. }
      unfold mapper' in TID2.
      desf.
      unfold not in n0, n3.
      apply NNPP in n0, n3.
      unfold index in *.
      unfold t_1_len in *. unfold SequentBase.t_1_len.
      desf. unfold tid in *.
      lia. }
    { intros e INE COND.
      unfold mapper' in COND. desf.
      { apply wf_threads in INE.
        { exfalso. apply TSET in INE. desf. }
        apply INV'. }
      { unfold not in n0.
        apply NNPP in n0; vauto. }
      unfold not in n0.
      apply NNPP in n0; vauto. }
    { intros e NINE.
      unfold mapper'; desf. }
    intros e NINE.
    unfold mapper_rev'; desf. }
  split; red.
  { apply SIMRELQ. }

  assert (INDLEMMA : forall x y (NNIT : tid x <> tid_init) (EQT : tid x = tid y) (EQI : index x = index y),
          x = y).
  { clear. intros x y NNIT EQT EQI.
    destruct x; destruct y; desf; ins.
    desf. }
  
  assert (MAPS : forall x y, E_t' x -> E_t y ->
          mapper' x = mapper y -> x = y).
  { unfold mapper'. ins; desf.
    { destruct classic with (tid (mapper y) = t_2) as [TID2 | TID2].
      2: { apply (seq_mapeq SIMREL) in TID2; vauto. }
      apply wf_threads in H.
      { rewrite TID2 in H.
        apply TSET in H.
        exfalso. desf. }
      apply INV'. }
    { apply (seq_mapeq SIMREL); vauto.
      clear - n0 THRDNEQ.
      intros FLS. unfold not in n0.
      apply n0. desf. intros FLS'.
      desf. }
    destruct classic with (tid (mapper y) = t_2) as [TID2 | TID2].
    2: { rewrite <- H1 in TID2. desf. }
    apply NNPP in n0.
    apply INDLEMMA.
    { rewrite n0; vauto. }
    { apply (seq_thrd SIMREL) in TID2; vauto.
      rewrite TID2; vauto. }
    apply (seq_index SIMREL) in TID2; vauto.
    rewrite <- H1 in TID2.
    simpl in *. unfold t_1_len in *.
    unfold SequentBase.t_1_len in *.
    lia. }

  unfold WCore.reexec.
  exists thrdle'.
  constructor; vauto.
  { unfold dtrmt'. destruct SIMRELQ.
    arewrite ((fun a : actid => is_init a) ⊆₁
              mapper' ↑₁ (fun a : actid => is_init a)).
    { clear- seq_init.
      unfold fixset in seq_init.
      basic_solver. }
    destruct STEP.
    rewrite dtrmt_init; vauto. }
  { unfold dtrmt', cmt'.
    rewrite (WCore.dtrmt_cmt STEP); vauto. }
  { destruct STEP. unfold cmt'.
    arewrite (WCore.G X_s' = G_s').
    unfold G_s'. simpls.
    basic_solver 8. }
  { constructor.
    { destruct STEP. destruct reexec_sur.
      unfold least_elt. intros trn INIT.
      unfold thrdle'.
      right.
      split; vauto.
      unfold least_elt in surg_init_least.
      specialize (surg_init_least trn INIT).
      clear - surg_init_least.
      basic_solver. }
    { unfold min_elt. intros trn INIT.
      assert (FLS : codom_rel thrdle' tid_init).
      { clear - INIT. basic_solver. }
      unfold thrdle' in INIT.
      apply codom_union in FLS.
      destruct FLS as [FLS | FLS1].
      { apply codom_union in FLS.
        destruct FLS as [FLS | FLS2].
        { apply codom_union in FLS.
          destruct FLS as [FLS | FLS3].
          { apply codom_union in FLS.
            destruct FLS as [FLS | FLS4].
            { destruct STEP. destruct reexec_sur.
              unfold min_elt in surg_init_min.
              destruct FLS as [x FLS].
              specialize (surg_init_min x).
              apply surg_init_min.
              vauto. }
            clear - NINIT1 FLS4.
            apply codom_crossed in FLS4.
            desf. }
          clear - NINIT2 FLS3.
          apply codom_crossed in FLS3.
          desf. }
        apply codom_crossed in FLS2.
        unfold set_minus in FLS2.
        destruct FLS2 as [FLS2 _].
        destruct STEP. destruct reexec_sur.
        clear - FLS2 surg_init_min.
        unfold min_elt in surg_init_min.
        destruct FLS2 as [x FLS2].
        specialize (surg_init_min x).
        apply surg_init_min.
        destruct FLS2 as [x0 [EQ FLS2]].
        destruct EQ. desf. }
      apply codom_crossed in FLS1.
      destruct STEP. destruct reexec_sur.
      clear - FLS1 surg_init_min.
      unfold min_elt in surg_init_min.
      destruct FLS1 as [x FLS1].
      specialize (surg_init_min x).
      desf. }
    { constructor.
      { unfold thrdle'.
        apply irreflexive_union; split.
        { apply irreflexive_union; split.
          { apply irreflexive_union; split.
            { apply irreflexive_union; split.
              { destruct STEP. destruct reexec_sur.
                unfold strict_partial_order in surg_order.
                destruct surg_order as [IRR _]; vauto. }
              clear - THRDNEQ. basic_solver. }
            clear. basic_solver. }
          clear. basic_solver. }
        destruct STEP. destruct reexec_sur.
        unfold min_elt in surg_init_min.
        clear - surg_init_min.
        intros x [EQ [y FLS]].
        specialize (surg_init_min y).
        basic_solver 4. }
      unfold thrdle'. unfold transitive.
      intros x y z XY YZ.
      (* TODO : discuss *)
      admit. }
    admit. }
  { unfold sb. rewrite !seqA.
    rewrite <- !id_inter.
    rewrite <- seqA with (r1 := ⦗dtrmt'⦘).
    rewrite <- id_inter.
    unfold dtrmt'. destruct SIMREL.
    rewrite seq_acts.
    intros x y PTH.
    destruct PTH as [x0 [[EQ1 IN1]
                      [x1 [PTH [EQ2 [IN2 IN3]]]]]].
    destruct IN1 as [x2 [IN1 M1]].
    destruct IN2 as [x3 [IN2 M2]].
    subst.
    unfold seq. exists (mapper x2); split.
    { red; split; vauto.
      split; [| basic_solver].
      destruct STEP.
      destruct reexec_dtrmt_sb_closed with
          (x := x2) (y := x3).
      { unfold seq. exists x3; split.
        { destruct x2.
          { unfold sb.
            unfold seq; exists (InitEvent l); split; vauto.
            exists x3; split; vauto.
            unfold ext_sb. desf.
            rewrite !seq_init in PTH; vauto. }
          destruct classic with (tid (mapper 
                (ThreadEvent thread index)) = t_2) as [TID2 | TID2].
          { rewrite seq_mapto in PTH.
            { destruct x3.
              { rewrite !seq_init in PTH; vauto. }
              destruct classic with (tid (mapper 
                    (ThreadEvent thread0 index0)) = t_2) as [TID2' | TID2'].
              { rewrite seq_mapto in PTH.
                { assert (TD1 : thread = t_1).
                  { apply seq_thrd in TID2; vauto. }
                  assert (TD2 : thread0 = t_1).
                  { apply seq_thrd in TID2'; vauto. }
                  clear - PTH IN1 IN2 TID2 TID2' TD1 TD2.
                  unfold sb. unfold seq.
                  exists (ThreadEvent thread index); split; vauto.
                  exists (ThreadEvent t_1 index0); split; vauto.
                  unfold ext_sb. desf; split; vauto.
                  unfold ext_sb in PTH. desf.
                  unfold Events.index in *. lia. }
                all : vauto. }
              clear - TID2 TID2' PTH IN1 IN2.
              unfold sb. unfold seq.
              exists (ThreadEvent thread index); split; vauto.
              exists (ThreadEvent thread0 index0); split; vauto.
              unfold ext_sb in *.
              unfold tid in *.
              desf; desf. }
            all : vauto. }
          destruct x3.
          { exfalso.
            assert (HLP : mapper (InitEvent l)
                = InitEvent l).
            { rewrite seq_init; vauto. }
            rewrite HLP in PTH.
            clear - PTH.
            unfold ext_sb in PTH.
            desf. }
          destruct classic with (tid (mapper 
                (ThreadEvent thread0 index0)) = t_2) as [TID2' | TID2'].
          { clear - TID2 TID2' PTH IN1 IN2 seq_init seq_init_rev MAPREV.
            unfold sb. unfold seq.
            exists (ThreadEvent thread index); split; vauto.
            exists (ThreadEvent thread0 index0); split; vauto.
            exfalso. unfold ext_sb in *.
            unfolder. desf.
            { assert (Heqq : mapper_rev (mapper (ThreadEvent thread index)) =
                mapper_rev (InitEvent l)).
              { rewrite Heq; vauto. }
              unfold compose in MAPREV.
              rewrite MAPREV in Heqq; vauto.
              unfold id in Heqq.
              rewrite seq_init_rev in Heqq; vauto. }
            unfold tid in *. desf. }
          assert (EQQ1 : mapper (ThreadEvent thread index) =
              ThreadEvent thread index).
          { rewrite seq_mapeq; vauto. }
          assert (EQQ2 : mapper (ThreadEvent thread0 index0) =
              ThreadEvent thread0 index0).
          { rewrite seq_mapeq; vauto. }
          rewrite EQQ1, EQQ2 in PTH.
          unfold sb. unfold seq.
          exists (ThreadEvent thread index); split; vauto. }
        red; split; vauto.
        unfold set_collect in IN3.
        destruct IN3 as [x4 [IN3 EQ]].
        assert (IN4 : E_t' x4).
        { apply dtrmt_cmt, reexec_embd_dom in IN3; vauto. }
        unfold mapper' in EQ.
        apply MAPS in EQ; vauto. }
      unfold set_collect.
      exists x2; split.
      { destruct H as [DT _].
        red in DT. basic_solver 4. }
      destruct x2.
      { rewrite seq_init; vauto.
        destruct SIMRELQ.
        rewrite seq_init0; vauto. }
      admit. }
    exists (mapper x3); split; vauto.
    red; split; vauto. }
  { admit. }
  { admit. }
  { destruct STEP.
    destruct reexec_embd_corr.
    constructor; vauto.
    { intros e CMT.
      arewrite (WCore.G X_s' = G_s').
      unfold G_s'. simpls.
      unfold compose.
      admit. (* ??? *) }
    all : admit. }
  { destruct STEP. unfold rf_complete.
    arewrite (WCore.G X_s' = G_s').
    unfold G_s'. simpls.
    arewrite ((fun x : actid =>
    ifP ~ (mapper' ↑₁ E_t') x then x
    else (if
           negb
             (BinPos.Pos.eqb (tid x) t_2)
          then x
          else
           ThreadEvent t_1
             (t_1_len + index x))) = mapper_rev').
    rewrite collect_rel_id, set_collect_id,
        Combinators.compose_id_right.
    apply rexec_rfc. }
  { constructor; ins.
    { apply sub_WF with (G := G_s) (sc := ∅₂) (sc' := ∅₂).
      { ins.
        assert (INITDER : (fun a : actid => is_init a) ⊆₁ dtrmt_t).
        { destruct STEP; vauto. }
        rewrite INITDER; vauto. }
      { admit. (* TODO : Wf G_s *) }
      apply restrict_sub; [basic_solver |].
      admit. }
    { ins. rewrite set_interA, set_inter_absorb_r.
      { constructor; ins.
        all : admit. }
      admit. }
    all : admit. }
  { assert (SBEQ : sb G_s' ≡ sb_t').
    { unfold sb. unfold G_s'; ins.
      clear; basic_solver 8. }
    apply XmmCons.monoton_cons with (G_t := G_t')
                    (m := id); vauto.
    all : try arewrite (WCore.G X_s' = G_s').
    { unfold rpo. unfold rpo_imm.
      arewrite (R G_s' ≡₁ R_t').
      arewrite (F G_s' ≡₁ F G_t').
      arewrite (W G_s' ≡₁ W G_t').
      arewrite (Acq G_s' ≡₁ Acq G_t').
      arewrite (Rlx G_s' ≡₁ Rlx G_t').
      arewrite (Rel G_s' ≡₁ Rel G_t').
      rewrite collect_rel_id.
      apply inclusion_t_t.
      rewrite SBEQ; vauto. }
    { rewrite SBEQ. rewrite collect_rel_id.
      unfold same_loc. unfold G_s'; ins. }
    { apply INV'. }
    { admit. (* wf_s' *) }
    destruct STEP; vauto. }
  { admit. }
  apply sub_to_full_exec_listless
    with (thrdle := thrdle'); vauto.
  all : admit.
Admitted.

End SequentReexec.