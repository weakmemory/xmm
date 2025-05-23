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
From xmm Require Import SequentWf.
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

Hypothesis THRLEE : thrdle ≡ ⦗threads_set G_t⦘ ⨾ thrdle ⨾ ⦗threads_set G_t⦘.

Definition thrdle' := thrdle ∪ eq t_2 × eq t_1 ∪ dom_rel (thrdle ⨾ ⦗eq t_1⦘) × eq t_2
                      ∪ eq t_2 × codom_rel (⦗eq t_1⦘ ⨾ thrdle)
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
    << REX : WCore.reexec X_s X_s' (mapper ∘ f_t ∘ mapper_rev') dtrmt' cmt' >>.
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
  
  assert (INDLEMMA : forall x y (NNIT : tid x <> tid_init) (EQT : tid x = tid y) (EQI : index x = index y),
          x = y).
  { clear. intros x y NNIT EQT EQI.
    destruct x; destruct y; desf; ins.
    desf. }

  assert (DTRSAME : forall x, dtrmt_t x -> 
                      mapper x = mapper' x).
  { intros x COND.
    destruct classic with (tid (mapper
                      x) = t_2) as [TID2 | TID2].
    { assert (TID2' : tid (mapper x) = t_2) by vauto.
      assert (TID2S : tid (mapper x) = t_2) by vauto.
      destruct SIMREL.
      apply seq_index in TID2.
      apply seq_thrd in TID2'.
      { apply INDLEMMA.
        { unfold mapper'. desf. }
        { unfold mapper'.
          rewrite TID2S. clear TID2S.
          desf.
          { destruct STEP.
            apply dtrmt_cmt in COND.
            apply reexec_embd_dom in COND; vauto. }
          symmetry in TID2.
          rewrite <- TID2 in l.
          exfalso. unfold Events.index in *.
          unfold SequentBase.t_1_len in *.
          unfold t_1_len in *.
          lia. }
        unfold mapper'.
        rewrite TID2. clear TID2.
        desf.
        { destruct STEP.
          apply dtrmt_cmt in COND.
          apply reexec_embd_dom in COND; vauto. }
        { exfalso. unfold Events.index in *.
          unfold SequentBase.t_1_len in *.
          unfold t_1_len in *.
          lia. }
        unfold Events.index in *.
        unfold t_1_len in *.
        unfold SequentBase.t_1_len in *.
        lia. }
      { destruct STEP. apply rexec_acts; vauto. }
      destruct STEP. apply rexec_acts; vauto. }
    assert (TID2' : tid (mapper x) <> t_2) by vauto.
    assert (TID2S : tid (mapper x) <> t_2) by vauto.
    apply (seq_mapeq SIMREL) in TID2.
    { rewrite TID2. clear TID2.
      unfold mapper'. desf.
      apply INDLEMMA.
      { unfold not in n0.
        apply NNPP in n0.
        rewrite n0; vauto. }
      { unfold tid.
        unfold not in n0.
        apply NNPP in n0.
        apply (seq_out_move SIMREL) in n0; vauto.
        { apply (seq_mapeq SIMREL) in TID2S; vauto.
          rewrite TID2S in n0.
          desf.
          destruct STEP. apply rexec_acts; vauto. }
        { destruct STEP. apply rexec_acts; vauto. }
        unfold Events.index in *.
        unfold t_1_len in *.
        unfold SequentBase.t_1_len in *.
        lia. }
      unfold Events.index in *.
      unfold not in n0.
      apply NNPP in n0.
      apply (seq_out_move SIMREL) in n0; vauto.
      { apply (seq_mapeq SIMREL) in TID2S; vauto.
        { rewrite TID2S in n0.
          desf. }
        destruct STEP. apply rexec_acts; vauto. }
      { destruct STEP. apply rexec_acts; vauto. }
      unfold Events.index in *.
      unfold t_1_len in *.
      unfold SequentBase.t_1_len in *.
      lia. }
    destruct STEP. apply rexec_acts; vauto. }

  assert (EXTSBL : forall x y, E_t' x -> E_t' y ->
                  ext_sb (mapper' x) (mapper' y) ->
                  ext_sb x y).
  { intros x y INE1 INE2 PTH.
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
  assert (MAPREVCOMP : eq_dom (acts_set G_s') (mapper' ∘ mapper_rev') id).
  { intros x COND.
    unfold G_s' in COND; ins.
    destruct COND as [x0 [INE MAP]].
    rewrite <- MAP. unfold compose in *.
    rewrite MAPCOMP; vauto. }

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
          apply EXTSBL; vauto. }
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
    { intros e INE COND.
      unfold mapper_rev'. desf.
      unfold t_1_len, SequentBase.t_1_len.
      apply INDLEMMA; vauto.
      unfold index. desf.
      lia. }
    { intros e NINE.
      unfold mapper'; desf. }
    { intros e INE TID.
      unfold mapper'.
      desf; vauto. }
    { intros e INE TID IND.
      unfold mapper'.
      desf; vauto.
      unfold SequentBase.t_1_len in *.
      unfold t_1_len in *. lia. }
    { intros e NINE.
      unfold mapper'; desf. }
    intros e NINE.
    unfold mapper_rev'; desf. }
  split; red.
  { apply SIMRELQ. }
  
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

  assert (RPOIN : rpo G_s' ⊆ mapper' ↑ rpo_t').
  { unfold rpo. unfold rpo_imm.
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
    { assert (SBIN : sb G_s' ⊆ mapper' ↑ sb_t').
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

  assert (SBSEQ : sb (WCore.G X_s') ≡ mapper' ↑ sb_t' \ po_seq X_s' t_1 t_2).
  { destruct SIMRELQ.
    assert (HLP : (sb (WCore.G X_s') ∪ po_seq X_s' t_1 t_2)
              \ po_seq X_s' t_1 t_2 ≡ mapper' ↑ sb_t' \ po_seq X_s' t_1 t_2).
    { apply minus_rel_more; vauto. }
    rewrite <- HLP.
    rewrite minus_union_l.
    rewrite minusK.
    rewrite minus_disjoint; [basic_solver |].
    split; vauto.
    intros x y COND.
    destruct COND as [COND1 COND2].
    unfold po_seq in COND2.
    destruct COND2 as [[TID1 IN1] [TID2 IN2]].
    unfold sb in COND1.
    destruct COND1 as [x0 [[EQ1 INE1] [x1 [COND [EQ2 INE2]]]]].
    subst x0 x1.
    unfold ext_sb in COND.
    desf.
    { unfold tid in TID1. apply NINIT1; vauto. }
    unfold tid in *. desf. }

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
  { unfold dtrmt'.
    unfold fixset.
    intros x DTT.
    destruct DTT as [x0 [INX DTT]].
    subst. unfold compose.
    assert (HLP : mapper_rev' (mapper' x0) = x0).
    { unfold compose in MAPCOMP.
      apply MAPCOMP. destruct STEP.
      apply dtrmt_cmt, reexec_embd_dom in INX; vauto. }
    rewrite HLP.
    arewrite (f_t x0 = x0).
    { destruct STEP.
      apply dtrmt_fixed; vauto. }
    apply DTRSAME; vauto. }
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
        repeat (apply irreflexive_union; split).
        { destruct STEP. destruct reexec_sur.
          unfold strict_partial_order in surg_order.
          destruct surg_order as [IRR _]; vauto. }
        { clear - THRDNEQ. basic_solver. }
        { intros x COND.
          destruct COND as [CD1 CD2]; subst x.
          destruct CD1 as [x1 [x2 [CD1 CD2]]].
          apply THRLEE in CD1.
          destruct CD1 as [x3 [[EQ INE] CD3]].
          subst x3. desf. }
        { intros x COND.
          destruct COND as [CD1 CD2]; subst x.
          destruct CD2 as [x1 [x2 [CD1 CD2]]].
          apply THRLEE in CD2.
          destruct CD2 as [x3 [CD2 [x4 [CD3 [EQ INE]]]]].
          subst x4. desf. }
        destruct STEP. destruct reexec_sur.
        unfold min_elt in surg_init_min.
        clear - surg_init_min.
        intros x [EQ [y FLS]].
        specialize (surg_init_min y).
        basic_solver 4. }
      unfold thrdle'. unfold transitive.
      intros x y z XY YZ.
      destruct XY as [[[[C1 | C1] | C1] | C1] | C1].
      all : destruct YZ as [[[[C2 | C2] | C2] | C2] | C2].
      all : destruct STEP.
      all : destruct reexec_sur.
      all : destruct surg_order as [IR TR].
      { do 4 left. clear - C1 C2 TR. basic_solver 4. }
      { destruct C2 as [EQ1 EQ2].
        subst y. apply THRLEE in C1.
        destruct C1 as [x3 [CD2 [x4 [CD3 [EQ INE]]]]].
        desf. }
      { do 2 left; right.
        clear - C1 C2 TR.
        destruct C2 as [C2 EQ]; subst z.
        split; vauto.
        destruct C2 as [x0 [x1 [CD2 [EQ1 EQ2]]]]; subst.
        basic_solver 8. }
      { destruct C2 as [EQ1 EQ2].
        subst y. apply THRLEE in C1.
        destruct C1 as [x3 [CD2 [x4 [CD3 [EQ INE]]]]].
        desf. }
      { clear - C1 C2 surg_init_min.
        exfalso. unfold min_elt in surg_init_min.
        destruct C2 as [C2 C3].
        basic_solver 4. }
      { left; right.
        clear - C1 C2 TR.
        destruct C1 as [C1 EQ]; subst x y.
        split; vauto. }
      { clear - C1 C2 THRDNEQ.
        destruct C1 as [C1 EQ]; subst x y.
        destruct C2 as [C2 EQ1]; subst z.
        exfalso. desf. }
      { clear - C1 C2 IR.
        exfalso.
        destruct C1 as [C1 EQ]; subst x y.
        destruct C2 as [C2 EQ1]; subst z.
        destruct IR with t_1.
        destruct C2 as [x0 [x1 [CD [EQ1 EQ2]]]]; subst.
        vauto. }
      { clear - C1 C2 THRDNEQ.
        destruct C1 as [C1 EQ]; subst x y.
        destruct C2 as [C2 EQ1].
        exfalso. desf. }
      { clear - C1 C2 NINIT1.
        destruct C1 as [C1 EQ]; subst x y.
        destruct C2 as [C2 EQ1].
        exfalso. desf. }
      { destruct C1 as [EQ1 EQ2].
        subst y. apply THRLEE in C2.
        destruct C2 as [x3 [[EQ TD] [x4 [CD3 CD4]]]].
        desf. }
      { do 4 left. clear - C1 C2 TR.
        destruct C2 as [C2 EQ]; subst y z.
        destruct C1 as [C1 EQ1].
        destruct C1 as [x0 [x1 [CD1 [EQ2 EQ3]]]]; subst.
        vauto. }
      { destruct C1 as [EQ1 EQ2].
        subst y.
        destruct C2 as [C2 EQ]; subst z.
        destruct C2 as [x0 [x1 [CD2 [EQ3 EQ4]]]]; subst.
        apply THRLEE in CD2.
        destruct CD2 as [x3 [[EQ TD] [x4 [CD3 CD4]]]].
        desf. }
      { do 4 left. clear - C1 C2 TR.
        destruct C2 as [C2 EQ]; subst.
        destruct C1 as [C1 EQ1]; subst.
        destruct C1 as [x0 [x1 [CD1 [EQ2 EQ3]]]]; subst.
        destruct EQ as [x1 [x2 [[EQ INE] CDD]]]; subst.
        basic_solver 8. }
      { clear - C1 C2 NINIT2.
        destruct C1 as [C1 EQ]; subst.
        destruct C2 as [C2 EQ1]; subst.
        exfalso. desf. }
      { left; right.
        clear - C1 C2 TR.
        destruct C1 as [EQ1 EQ2].
        subst x. split; vauto.
        unfold codom_rel.
        destruct EQ2 as [x0 [x1 [[EQ1 EQ2] CD]]].
        basic_solver 8. }
      { clear - C1 C2 THRLEE T2NOTIN.
        destruct C2 as [C2 EQ]; subst.
        destruct C1 as [C1 EQ1]; subst.
        destruct EQ1 as [x0 [x1 [[EQ1 EQ2] CD]]].
        apply THRLEE in CD.
        destruct CD as [x3 [[EQ TD] [x4 [CD3 [EQ3 TD2]]]]].
        desf. }
      { clear - C1 C2 IR TR.
        exfalso.
        destruct C1 as [C1 EQ]; subst.
        destruct C2 as [C2 EQ1]; subst.
        destruct EQ as [x0 [x1 [[EQ1 EQ2] CD]]]; subst.
        destruct C2 as [x2 [x3 [CD2 [INE1 INE2]]]]; subst.
        basic_solver 8. }
      { destruct C1 as [EQ1 EQ2].
        subst x.
        destruct C2 as [C2 EQ]; subst.
        destruct EQ2 as [x0 [x1 [CD2 CD3]]]; subst.
        apply THRLEE in CD3.
        destruct CD3 as [x3 [[EQ2 TD] [x4 [CD3 [EQ3 EQ4]]]]].
        desf. }
      { clear - C1 C2 surg_init_min TR.
        exfalso.
        destruct C1 as [C1 EQ]; subst.
        destruct C2 as [C2 EQ1]; subst.
        destruct EQ as [x0 [x1 [[EQ3 EQ2] CD]]]; subst.
        destruct surg_init_min with x1; vauto. }
      { do 4 left. clear - C1 C2 TR surg_init_least surg_init_min.
        destruct C1.
        destruct H0 as [x0 CND]; subst.
        unfold least_elt in surg_init_least.
        apply surg_init_least.
        intros FLS. basic_solver 12. }
      { clear - C1 C2 THRLEE T2NOTIN.
        exfalso.
        destruct C1 as [C1 EQ]; subst.
        destruct C2 as [C2 EQ1]; subst.
        destruct EQ as [x0 CND]; subst.
        apply THRLEE in CND.
        destruct CND as [x3 [[EQ2 TD] [x4 [CD3 [EQ3 EQ4]]]]].
        desf. }
      { do 2 left; right.
        clear - C1 C2 TR NINIT1 surg_init_least.
        destruct C1 as [C1 EQ]; subst.
        destruct C2 as [C2 EQ1]; subst.
        split; vauto.
        unfold dom_rel.
        exists t_1; vauto.
        unfold seq; exists t_1; split; vauto.
        unfold least_elt in surg_init_least.
        specialize (surg_init_least t_1).
        apply surg_init_least.
        basic_solver. }
      { clear - C1 C2 THRLEE T2NOTIN.
        exfalso.
        destruct C1 as [C1 EQ]; subst.
        destruct C2 as [C2 EQ1]; subst.
        destruct EQ as [x0 CND]; subst.
        apply THRLEE in CND.
        destruct CND as [x3 [[EQ2 TD] [x4 [CD3 [EQ3 EQ4]]]]].
        desf. }
      clear - C1 C2 surg_init_min.
      destruct C1 as [C1 EQ]; subst.
      destruct C2 as [C2 EQ1]; subst.
      exfalso.
      unfold min_elt in surg_init_min.
      destruct EQ as [x0 CND].
      specialize (surg_init_min x0).
      vauto. }
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
      destruct H as [DT SB].
      destruct classic with (tid (mapper
                (ThreadEvent thread index)) = t_2) as [TID2 | TID2].
      { assert (TID2' : tid (mapper (ThreadEvent thread index)) = t_2) by vauto.
        assert (TID2S : tid (mapper (ThreadEvent thread index)) = t_2) by vauto.
        apply seq_index in TID2.
        apply seq_thrd in TID2'.
        { apply INDLEMMA.
          { unfold mapper'. desf.
            { rewrite TID2'; vauto. }
          unfold not in n0.
          apply NNPP in n0.
          rewrite n0; vauto. }
          { unfold mapper'.
            rewrite TID2S. clear TID2S.
            desf.
            { red in DT. destruct DT as [EQ DT].
              apply dtrmt_cmt in DT.
              apply reexec_embd_dom in DT; vauto. }
            symmetry in TID2.
            rewrite <- TID2 in l.
            exfalso. unfold Events.index in *.
            unfold SequentBase.t_1_len in *.
            unfold t_1_len in *.
            lia. }
          unfold mapper'.
          rewrite TID2. clear TID2.
          desf.
          { red in DT. destruct DT as [EQ DT].
            apply dtrmt_cmt in DT.
            apply reexec_embd_dom in DT; vauto. }
          { exfalso. unfold Events.index in *.
            unfold SequentBase.t_1_len in *.
            unfold t_1_len in *.
            lia. }
          unfold Events.index in *.
          unfold t_1_len in *.
          unfold SequentBase.t_1_len in *.
          lia. }
        { red in DT. destruct DT as [EQ DT].
          apply dtrmt_cmt in DT.
          apply reexec_embd_dom in DT; vauto. }
        red in DT. destruct DT as [EQ DT].
        apply dtrmt_cmt in DT.
        apply reexec_embd_dom in DT; vauto. }
      assert (TID2' : tid (mapper (ThreadEvent thread index)) <> t_2) by vauto.
      assert (TID2S : tid (mapper (ThreadEvent thread index)) <> t_2) by vauto.
      apply seq_mapeq in TID2.
      { rewrite TID2. clear TID2.
        unfold mapper'. desf.
        apply INDLEMMA.
        { unfold tid; vauto. }
        { unfold tid.
          unfold not in n0.
          apply NNPP in n0.
          apply seq_out_move in n0; vauto.
          { apply seq_mapeq in TID2S; vauto.
            rewrite TID2S in n0.
            desf. }
          unfold Events.index in *.
          unfold t_1_len in *.
          unfold SequentBase.t_1_len in *.
          lia. }
        unfold Events.index in *.
        unfold not in n0.
        apply NNPP in n0.
        apply seq_out_move in n0; vauto.
        { apply seq_mapeq in TID2S; vauto.
          rewrite TID2S in n0.
          desf. }
        unfold Events.index in *.
        unfold t_1_len in *.
        unfold SequentBase.t_1_len in *.
        lia. }
      red in DT. destruct DT as [EQ DT].
      apply dtrmt_cmt in DT.
      apply reexec_embd_dom in DT; vauto. }
    exists (mapper x3); split; vauto.
    red; split; vauto. }
  { unfold nin_sb.
    rewrite SBSEQ.
    rewrite <- seq_eqv_minus_ll.
    admit. (* something for immediate of exclusion is needed *)}
  { arewrite (WCore.G X_s' = G_s').
    unfold G_s' at 1; ins.
    intros x COND.
    destruct COND as (INE & NDT).
    unfold set_compl. intros FLS.
    destruct INE as [x0 [INE M1]]; subst.
    unfold dtrmt' in NDT.
    assert (DTRM : ~ dtrmt_t x0).
    { intros FLSS.
      apply NDT. unfold set_collect.
      exists x0; split; vauto. }
    destruct FLS as [FL1 | FL2].
    { assert (FLS : (Rel G_t') x0).
      { assert (SUBST : (fun x : actid =>
                  ifP ~ (mapper' ↑₁ E_t') x then x
                  else (ifP tid x <> t_2 then x
                        else ThreadEvent t_1
                              (t_1_len + index x))) = mapper_rev') by vauto.
        rewrite SUBST in FL1.
        unfold compose in FL1.
        unfold is_rel, mod in *.
        assert (HLP : mapper_rev' (mapper' x0) = x0).
        { unfold compose in MAPCOMP.
          apply MAPCOMP in INE.
          unfold id in INE; vauto. }
        rewrite HLP in FL1; vauto. }
      destruct STEP.
      clear - reexec_dtrmt_rpo FLS DTRM INE.
      unfold set_compl in reexec_dtrmt_rpo.
      destruct reexec_dtrmt_rpo with x0; vauto. }
    assert (FLS : (Acq G_t') x0).
    { assert (SUBST : (fun x : actid =>
                ifP ~ (mapper' ↑₁ E_t') x then x
                else (ifP tid x <> t_2 then x
                      else ThreadEvent t_1
                            (t_1_len + index x))) = mapper_rev') by vauto.
      rewrite SUBST in FL2.
      unfold compose in FL2.
      unfold is_acq, mod in *.
      assert (HLP : mapper_rev' (mapper' x0) = x0).
      { unfold compose in MAPCOMP.
        apply MAPCOMP in INE.
        unfold id in INE; vauto. }
      rewrite HLP in FL2; vauto. }
    destruct STEP.
    clear - reexec_dtrmt_rpo FLS DTRM INE.
    unfold set_compl in reexec_dtrmt_rpo.
    destruct reexec_dtrmt_rpo with x0; vauto. }
  { destruct STEP.
    destruct reexec_embd_corr.
    constructor; vauto.
    { unfold cmt'.
      unfold inj_dom.
      intros x y CD1 CD2 EQQ.
      destruct CD1 as [x0 [CD1 M1]].
      destruct CD2 as [x1 [CD2 M2]].
      subst.
      unfold compose in EQQ.
      unfold compose in MAPCOMP.
      assert (HLP1 : mapper_rev' (mapper' x0) = x0).
      { unfold compose in MAPCOMP.
        apply MAPCOMP.
        apply reexec_embd_dom in CD1; vauto. }
      assert (HLP2 : mapper_rev' (mapper' x1) = x1).
      { unfold compose in MAPCOMP.
        apply MAPCOMP.
        apply reexec_embd_dom in CD2; vauto. }
      rewrite HLP1, HLP2 in EQQ.
      destruct SIMREL.
      apply seq_inj in EQQ.
      { apply reexec_embd_inj in EQQ; vauto. }
      { apply reexec_embd_acts; red.
        exists x0; vauto. }
      apply reexec_embd_acts; red.
      exists x1; vauto. }
    { intros e CMT.
      unfold cmt' in CMT.
      unfold set_collect in CMT.
      destruct CMT as [x [CMT EQ]].
      specialize (reexec_embd_lab x).
      assert (INE : E_t' x).
      { apply reexec_embd_dom in CMT; vauto. }
      assert (CMT' : cmt_t x) by vauto.
      apply reexec_embd_lab in CMT.
      destruct SIMRELQ.
      apply seq_lab in INE.
      unfold compose in INE.
      rewrite EQ in INE.
      rewrite <- INE.
      destruct SIMREL.
      rewrite CMT.
      subst.
      unfold compose.
      unfold compose in MAPCOMP.
      rewrite MAPCOMP.
      { unfold id.
        apply seq_lab0.
        apply reexec_embd_acts; red; vauto. }
      apply reexec_embd_dom; vauto. }
    { admit. (* needs a better analysis of sb structure *) }
    { unfold cmt'.
      rewrite (seq_rf SIMRELQ).
      rewrite (seq_rf SIMREL).
      destruct STEP.
      destruct reexec_embd_corr.
      rewrite <- reexec_embd_rf0.
      rewrite collect_rel_restr.
      { intros x y COND.
        unfold compose in COND.
        unfold collect_rel in COND.
        destruct COND as [x0 [x1 [COND [EQ1 EQ2]]]].
        destruct COND as [x2 [x3 [COND [EQ3 EQ4]]]].
        unfold collect_rel.
        exists (f_t (mapper_rev' x0)), (f_t (mapper_rev' x1)); splits.
        { exists x2, x3; splits; vauto.
          { unfold compose in MAPCOMP.
            rewrite MAPCOMP; vauto.
            destruct COND as [RF CDS].
            apply wf_rfE in RF; [|apply INV'].
            destruct RF as [x0 [[INE EQQ] RF2]]; vauto. }
          unfold compose in MAPCOMP.
          rewrite MAPCOMP; vauto.
          destruct COND as [RF CDS].
          apply wf_rfE in RF; [|apply INV'].
          destruct RF as [x0 [RF1 [RF2 [RF3 [INE EQQ]]]]]; vauto. }
        all : vauto. }
      rewrite reexec_embd_dom0.
      rewrite wf_rfE; [| apply INV'].
      rewrite dom_eqv1.
      rewrite <- seqA.
      rewrite codom_seq_eqv_r.
      arewrite (E_t' ∩₁ dom_rel (rf_t' ⨾ ⦗E_t'⦘) ⊆₁ E_t').
      { basic_solver. }
      destruct SIMRELQ.
      clear - seq_inj.
      basic_solver 8. }
    { unfold cmt'.
      rewrite (seq_co SIMRELQ).
      rewrite (seq_co SIMREL).
      destruct STEP.
      destruct reexec_embd_corr.
      rewrite <- reexec_embd_co0.
      rewrite collect_rel_restr.
      { intros x y COND.
        unfold compose in COND.
        unfold collect_rel in COND.
        destruct COND as [x0 [x1 [COND [EQ1 EQ2]]]].
        destruct COND as [x2 [x3 [COND [EQ3 EQ4]]]].
        unfold collect_rel.
        exists (f_t (mapper_rev' x0)), (f_t (mapper_rev' x1)); splits.
        { exists x2, x3; splits; vauto.
          { unfold compose in MAPCOMP.
            rewrite MAPCOMP; vauto.
            destruct COND as [CO CDS].
            apply wf_coE in CO; [|apply INV'].
            destruct CO as [x0 [[INE EQQ] CO2]]; vauto. }
          unfold compose in MAPCOMP.
          rewrite MAPCOMP; vauto.
          destruct COND as [CO CDS].
          apply wf_coE in CO; [|apply INV'].
          destruct CO as [x0 [CO1 [CO2 [CO3 [INE EQQ]]]]]; vauto. }
        all : vauto. }
      rewrite reexec_embd_dom0.
      rewrite wf_coE; [| apply INV'].
      rewrite dom_eqv1.
      rewrite <- seqA.
      rewrite codom_seq_eqv_r.
      arewrite (E_t' ∩₁ dom_rel (co_t' ⨾ ⦗E_t'⦘) ⊆₁ E_t').
      { basic_solver. }
      destruct SIMRELQ.
      clear - seq_inj.
      basic_solver 8. }
    { unfold cmt'.
      rewrite (seq_rmw SIMRELQ).
      rewrite (seq_rmw SIMREL).
      destruct STEP.
      destruct reexec_embd_corr.
      rewrite <- reexec_embd_rmw0.
      rewrite collect_rel_restr.
      { intros x y COND.
        unfold compose in COND.
        unfold collect_rel in COND.
        destruct COND as [x0 [x1 [COND [EQ1 EQ2]]]].
        destruct COND as [x2 [x3 [COND [EQ3 EQ4]]]].
        unfold collect_rel.
        exists (f_t (mapper_rev' x0)), (f_t (mapper_rev' x1)); splits.
        { exists x2, x3; splits; vauto.
          { unfold compose in MAPCOMP.
            rewrite MAPCOMP; vauto.
            destruct COND as [RM CDS].
            apply wf_rmwE in RM; [|apply INV'].
            destruct RM as [x0 [[INE EQQ] RM2]]; vauto. }
          unfold compose in MAPCOMP.
          rewrite MAPCOMP; vauto.
          destruct COND as [RM CDS].
          apply wf_rmwE in RM; [|apply INV'].
          destruct RM as [x0 [RM1 [RM2 [RM3 [INE EQQ]]]]]; vauto. }
        all : vauto. }
      rewrite reexec_embd_dom0.
      rewrite wf_rmwE; [| apply INV'].
      rewrite dom_eqv1.
      rewrite <- seqA.
      rewrite codom_seq_eqv_r.
      arewrite (E_t' ∩₁ dom_rel (rmw_t' ⨾ ⦗E_t'⦘) ⊆₁ E_t').
      { basic_solver. }
      destruct SIMRELQ.
      clear - seq_inj.
      basic_solver 8. }
    unfold cmt'.
    intros x COND.
    unfold set_collect in COND.
    destruct COND as [x0 [COND EQ]].
    destruct COND as [x1 [COND EQ1]].
    rewrite <- EQ1 in EQ.
    unfold compose in EQ.
    unfold compose in MAPCOMP.
    rewrite MAPCOMP in EQ.
    { unfold id in EQ.
      rewrite <- EQ.
      destruct SIMREL.
      apply seq_acts.
      unfold set_collect.
      exists (f_t x1); split; vauto.
      apply reexec_embd_acts.
      clear - COND.
      basic_solver. }
    apply reexec_embd_dom; vauto. }
  { destruct STEP. unfold rf_complete.
    arewrite (WCore.G X_s' = G_s').
    unfold G_s'. simpls.
    arewrite ((fun x : actid =>
       ifP ~ (mapper' ↑₁ E_t') x then x
       else (ifP tid x <> t_2 then x
             else ThreadEvent t_1
                    (t_1_len + index x))) = mapper_rev').
    unfold is_r. unfold compose.
    intros x COND.
    destruct COND as [MAP RD].
    destruct MAP as [x0 [MAP M1]]; subst.
    unfold rf_complete in rexec_rfc.
    destruct rexec_rfc with x0; vauto.
    { split; vauto.
      unfold compose in MAPCOMP.
      apply MAPCOMP in MAP.
      unfold id in MAP.
      rewrite MAP in RD.
      unfold is_r; vauto. }
    unfold codom_rel.
    exists (mapper' x).
    unfold collect_rel.
    exists x, x0; split; vauto. }
  { constructor; ins.
    { apply sub_WF with (G := G_s) (sc := ∅₂) (sc' := ∅₂).
      { ins.
        assert (INITDER : (fun a : actid => is_init a) ⊆₁ dtrmt_t).
        { destruct STEP; vauto. }
        arewrite ((fun a : actid => is_init a) ⊆₁ mapper' ↑₁
                  (fun a : actid => is_init a)).
        { destruct SIMRELQ. clear- seq_init.
          unfold fixset in seq_init.
          basic_solver. }
        rewrite INITDER.
        unfold dtrmt'; vauto. }
      { apply wf_transition with (X_t := X_t)
          (t_1 := t_1) (t_2 := t_2)
          (mapper := mapper) (mapper_rev := mapper_rev)
          (ptc_1 := ptc_1); vauto. }
      apply restrict_sub; [basic_solver |].
      unfold dtrmt'.
      destruct SIMREL.
      rewrite seq_acts.
      intros x COND.
      unfold set_collect in COND.
      destruct COND as [x0 [COND EQ]].
      unfold set_collect.
      exists x0; split; vauto.
      { destruct STEP.
        apply rexec_acts; vauto. }
      destruct classic with (tid (mapper
                x0) = t_2) as [TID2 | TID2].
      { assert (TID2' : tid (mapper x0) = t_2) by vauto.
        assert (TID2S : tid (mapper x0) = t_2) by vauto.
        apply seq_index in TID2.
        apply seq_thrd in TID2'.
        { apply INDLEMMA.
          { unfold mapper'. desf. }
          { unfold mapper'.
            rewrite TID2S. clear TID2S.
            desf.
            { destruct STEP.
              apply dtrmt_cmt in COND.
              apply reexec_embd_dom in COND; vauto. }
            symmetry in TID2.
            rewrite <- TID2 in l.
            exfalso. unfold Events.index in *.
            unfold SequentBase.t_1_len in *.
            unfold t_1_len in *.
            lia. }
          unfold mapper'.
          rewrite TID2. clear TID2.
          desf.
          { destruct STEP.
            apply dtrmt_cmt in COND.
            apply reexec_embd_dom in COND; vauto. }
          { exfalso. unfold Events.index in *.
            unfold SequentBase.t_1_len in *.
            unfold t_1_len in *.
            lia. }
          unfold Events.index in *.
          unfold t_1_len in *.
          unfold SequentBase.t_1_len in *.
          lia. }
        { destruct STEP. apply rexec_acts; vauto. }
        destruct STEP. apply rexec_acts; vauto. }
      assert (TID2' : tid (mapper x0) <> t_2) by vauto.
      assert (TID2S : tid (mapper x0) <> t_2) by vauto.
      apply seq_mapeq in TID2.
      { rewrite TID2. clear TID2.
        unfold mapper'. desf.
        apply INDLEMMA.
        { unfold not in n0.
          apply NNPP in n0.
          rewrite n0; vauto. }
        { unfold tid.
          unfold not in n0.
          apply NNPP in n0.
          apply seq_out_move in n0; vauto.
          { apply seq_mapeq in TID2S; vauto.
            rewrite TID2S in n0.
            desf.
            destruct STEP. apply rexec_acts; vauto. }
          { destruct STEP. apply rexec_acts; vauto. }
          unfold Events.index in *.
          unfold t_1_len in *.
          unfold SequentBase.t_1_len in *.
          lia. }
        unfold Events.index in *.
        unfold not in n0.
        apply NNPP in n0.
        apply seq_out_move in n0; vauto.
        { apply seq_mapeq in TID2S; vauto.
          { rewrite TID2S in n0.
            desf. }
          destruct STEP. apply rexec_acts; vauto. }
        { destruct STEP. apply rexec_acts; vauto. }
        unfold Events.index in *.
        unfold t_1_len in *.
        unfold SequentBase.t_1_len in *.
        lia. }
      destruct STEP. apply rexec_acts; vauto. }
    { constructor.
      { unfold WCore.X_start; ins.
        destruct SIMRELQ.
        unfold dtrmt'.
        unfold cmt'.
        rewrite <- !set_interA.
        split.
        { arewrite (mapper' ↑₁ dtrmt_t ⊆₁ mapper' ↑₁ E_t').
          apply set_subset_collect.
          { destruct STEP.
            rewrite dtrmt_cmt.
            rewrite reexec_embd_dom; vauto. }
          clear. basic_solver 8. }
        clear. basic_solver 8. }
      { unfold WCore.X_start; ins. }
      { unfold WCore.X_start; ins.
        arewrite ((fun x : actid =>
        ifP ~ (mapper' ↑₁ E_t') x then x
        else (ifP tid x <> t_2 then x
              else ThreadEvent t_1
                     (t_1_len + index x))) = mapper_rev').
        unfold eq_dom. intros x COND.
        destruct SIMREL.
        rewrite seq_lab_rev.
        { destruct STEP.
          destruct reexec_start_wf.
          destruct wf_ereq.
          unfold compose.
          rewrite <- ereq_lab.
          { unfold WCore.X_start; ins.
            assert (EQQ: mapper_rev x = mapper_rev' x).
            { unfold mapper_rev'. desf.
              { apply seq_rest_rev.
                clear - n COND reexec_embd_dom.
                destruct n.
                unfold cmt' in COND.
                destruct COND as [CND [x0 [IN1 IN2]]].
                unfold set_collect.
                exists x0; split; vauto.
                apply reexec_embd_dom; vauto. }
              { apply NNPP in n.
                apply seq_mapeq_rev; vauto.
                clear - COND.
                destruct COND as [[DTT ES] RST]; vauto. }
              unfold not in n0.
              apply NNPP in n0.
              rewrite seq_maprev; vauto.
              { apply INDLEMMA; vauto.
                unfold index.
                unfold SequentBase.t_1_len, t_1_len.
                lia. }
              destruct COND as [[DTT ES] RST]; vauto. }
            rewrite EQQ; vauto. }
          unfold WCore.X_start; ins.
          destruct COND as [[DTT ES] RST].
          apply seq_acts in ES.
          unfold dtrmt', cmt' in *.
          split.
          { split.
            { destruct DTT as [x0 [DTT M1]].
              rewrite <- M1.
              unfold compose in MAPCOMP.
              rewrite MAPCOMP; vauto.
              apply dtrmt_cmt in DTT.
              apply reexec_embd_dom in DTT; vauto. }
            destruct DTT as [x1 [DTT M1]].
            rewrite <- M1.
            unfold compose in MAPCOMP.
            rewrite MAPCOMP.
            { apply rexec_acts; vauto. }
            apply dtrmt_cmt in DTT.
            apply reexec_embd_dom in DTT; vauto. }
          destruct RST as [x1 [RST M1]].
          rewrite <- M1.
          unfold compose in MAPCOMP.
          rewrite MAPCOMP.
          { unfold id; vauto. }
          apply reexec_embd_dom in RST; vauto. }
        destruct COND as [[DTT ES] RST]; vauto. }
      { unfold WCore.X_start; ins.
        destruct STEP.
        destruct reexec_start_wf.
        destruct wf_ereq.
        split.
        { intros x y COND.
          unfold restr_rel in *.
          destruct COND as [CD1 [CD2 CD3]].
          split; vauto.
          destruct CD1 as [x0 [[EQ1 DT1]
                    [x1 [RF [EQ2 DT2]]]]]; subst.
          destruct ereq_rf as [IN OUT].
          destruct DT1 as [x2 [DT1 M1]].
          destruct DT2 as [x3 [DT2 M2]].
          destruct IN with x2 x3.
          { unfold WCore.X_start; ins.
            apply (seq_rf SIMREL) in RF.
            unfold collect_rel in RF.
            destruct RF as [x5 [x6 [RF [EQ3 EQ4]]]].
            splits.
            { unfold seq.
              exists x2; split; vauto.
              exists x3; split; vauto.
              assert (EQQ1 : x5 = x2).
              { assert (MEQ : mapper' x2 = mapper x2).
                { apply DTRSAME in DT1; vauto. }
                rewrite MEQ in EQ3.
                apply (seq_inj SIMREL) in EQ3; vauto.
                { apply wf_rfE in RF; [|apply INV].
                  destruct RF as [x4 [[INE EQQ] RF2]]; vauto. }
                apply rexec_acts; vauto. }
              assert (EQQ2 : x6 = x3).
              { assert (MEQ : mapper' x3 = mapper x3).
                { apply DTRSAME in DT2; vauto. }
                rewrite MEQ in M2.
                apply (seq_inj SIMREL) in M2; vauto.
                { apply rexec_acts; vauto. }
                apply wf_rfE in RF; [|apply INV].
                destruct RF as [x4 [[INE EQQ]
                        [x7 [RF [EQR INER]]]]]; vauto. }
              subst; vauto. }
            { split.
              { split; vauto.
                apply rexec_acts; vauto. }
              apply dtrmt_cmt in DT1; vauto. }
            split.
            { split; vauto.
              apply rexec_acts; vauto. }
            apply dtrmt_cmt in DT2; vauto. }
          unfold collect_rel.
          exists x2, x3; splits; vauto. }
        intros x y COND.
        unfold restr_rel in *.
        destruct COND as [CD1 [CD2 CD3]].
        destruct CD1 as [x0 [x1 [CDD [M1 M2]]]].
        splits.
        { unfold seq. exists x; split.
          { red; split; vauto.
            destruct CD2 as [[CD1 CD2] CD4]; vauto. }
          exists y; split.
          { apply (seq_rf SIMREL).
            destruct ereq_rf as [IN OUT].
            unfold collect_rel.
            exists x0, x1; splits; vauto.
            { destruct OUT with x0 x1.
              { split; vauto.
                unfold WCore.X_start; ins. split.
                { split.
                  { split.
                    { destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                                  [x3 [CMT1 MP2]]].
                      apply (seq_inj SIMRELQ) in MP1.
                      { subst; vauto. }
                      { apply dtrmt_cmt in DTT1.
                        apply reexec_embd_dom in DTT1; vauto. }
                      apply wf_rfE in CDD; [|apply INV'].
                      destruct CDD as [x4 [[INE EQQ] RF2]]; vauto. }
                    destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                            [x3 [CMT1 MP2]]].
                    apply (seq_inj SIMRELQ) in MP1.
                    { apply rexec_acts.
                      subst; vauto. }
                    { apply dtrmt_cmt in DTT1.
                      apply reexec_embd_dom in DTT1; vauto. }
                    apply wf_rfE in CDD; [|apply INV'].
                    destruct CDD as [x4 [[INE EQQ] RF2]]; vauto. }
                  destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                        [x3 [CMT1 MP2]]].
                  apply (seq_inj SIMRELQ) in MP1.
                  { subst; vauto.
                    apply dtrmt_cmt in DTT1; vauto. }
                  { apply dtrmt_cmt in DTT1.
                    apply reexec_embd_dom in DTT1; vauto. }
                  apply wf_rfE in CDD; [|apply INV'].
                  destruct CDD as [x4 [[INE EQQ] RF2]]; vauto. }
                split.
                { split.
                  { destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                          [x3 [CMT1 MP2]]].
                    apply (seq_inj SIMRELQ) in MP1.
                    { subst; vauto. }
                    { apply dtrmt_cmt in DTT1.
                      apply reexec_embd_dom in DTT1; vauto. }
                    apply wf_rfE in CDD; [|apply INV'].
                    destruct CDD as [x4 [[INE EQQ]
                            [x5 [RF [INE2 EQ2]]]]]; vauto. }
                  destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                          [x3 [CMT1 MP2]]].
                  apply (seq_inj SIMRELQ) in MP1.
                  { apply rexec_acts.
                    subst; vauto. }
                  { apply dtrmt_cmt in DTT1.
                    apply reexec_embd_dom in DTT1; vauto. }
                  apply wf_rfE in CDD; [|apply INV'].
                  destruct CDD as [x4 [[INE EQQ]
                            [x5 [RF [INE2 EQ2]]]]]; vauto. }
                destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                            [x3 [CMT1 MP2]]].
                apply (seq_inj SIMRELQ) in MP1.
                { subst; vauto.
                  apply dtrmt_cmt in DTT1; vauto. }
                { apply dtrmt_cmt in DTT1.
                  apply reexec_embd_dom in DTT1; vauto. }
                apply wf_rfE in CDD; [|apply INV'].
                destruct CDD as [x4 [[INE EQQ]
                        [x5 [RF [INE2 EQ2]]]]]; vauto. }
              unfold WCore.X_start in H; ins.
              destruct H as [x2 [[EQ1 DT1] [x3 [RF [EQ2 DT2]]]]].
              subst; vauto. }
            { destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                    [x3 [CMT1 MP2]]].
              apply (seq_inj SIMRELQ) in MP1.
              { subst.
                apply DTRSAME; vauto. }
              { apply dtrmt_cmt in DTT1.
                apply reexec_embd_dom in DTT1; vauto. }
              apply wf_rfE in CDD; [|apply INV'].
              destruct CDD as [x4 [[INE EQQ]
                      [x5 [RF [INE2 EQ2]]]]]; vauto. }
            destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                      [x3 [CMT1 MP2]]].
            apply (seq_inj SIMRELQ) in MP1.
            { subst.
              apply DTRSAME; vauto. }
            { apply dtrmt_cmt in DTT1.
              apply reexec_embd_dom in DTT1; vauto. }
            apply wf_rfE in CDD; [|apply INV'].
            destruct CDD as [x4 [[INE EQQ]
                    [x5 [RF [INE2 EQ2]]]]]; vauto. }
          red; split; vauto.
          destruct CD3 as [[CD1 CD3] CD4]; vauto. }
        all : vauto. }
      { unfold WCore.X_start; ins.
        destruct STEP.
        destruct reexec_start_wf.
        destruct wf_ereq.
        split.
        { intros x y COND.
          unfold restr_rel in *.
          destruct COND as [CD1 [CD2 CD3]].
          split; vauto.
          destruct CD1 as [x0 [[EQ1 DT1]
                    [x1 [RF [EQ2 DT2]]]]]; subst.
          destruct ereq_co as [IN OUT].
          destruct DT1 as [x2 [DT1 M1]].
          destruct DT2 as [x3 [DT2 M2]].
          destruct IN with x2 x3.
          { unfold WCore.X_start; ins.
            apply (seq_co SIMREL) in RF.
            unfold collect_rel in RF.
            destruct RF as [x5 [x6 [RF [EQ3 EQ4]]]].
            splits.
            { unfold seq.
              exists x2; split; vauto.
              exists x3; split; vauto.
              assert (EQQ1 : x5 = x2).
              { assert (MEQ : mapper' x2 = mapper x2).
                { apply DTRSAME in DT1; vauto. }
                rewrite MEQ in EQ3.
                apply (seq_inj SIMREL) in EQ3; vauto.
                { apply wf_coE in RF; [|apply INV].
                  destruct RF as [x4 [[INE EQQ] RF2]]; vauto. }
                apply rexec_acts; vauto. }
              assert (EQQ2 : x6 = x3).
              { assert (MEQ : mapper' x3 = mapper x3).
                { apply DTRSAME in DT2; vauto. }
                rewrite MEQ in M2.
                apply (seq_inj SIMREL) in M2; vauto.
                { apply rexec_acts; vauto. }
                apply wf_coE in RF; [|apply INV].
                destruct RF as [x4 [[INE EQQ]
                        [x7 [RF [EQR INER]]]]]; vauto. }
              subst; vauto. }
            { split.
              { split; vauto.
                apply rexec_acts; vauto. }
              apply dtrmt_cmt in DT1; vauto. }
            split.
            { split; vauto.
              apply rexec_acts; vauto. }
            apply dtrmt_cmt in DT2; vauto. }
          unfold collect_rel.
          exists x2, x3; splits; vauto. }
        intros x y COND.
        unfold restr_rel in *.
        destruct COND as [CD1 [CD2 CD3]].
        destruct CD1 as [x0 [x1 [CDD [M1 M2]]]].
        splits.
        { unfold seq. exists x; split.
          { red; split; vauto.
            destruct CD2 as [[CD1 CD2] CD4]; vauto. }
          exists y; split.
          { apply (seq_co SIMREL).
            destruct ereq_co as [IN OUT].
            unfold collect_rel.
            exists x0, x1; splits; vauto.
            { destruct OUT with x0 x1.
              { split; vauto.
                unfold WCore.X_start; ins. split.
                { split.
                  { split.
                    { destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                                  [x3 [CMT1 MP2]]].
                      apply (seq_inj SIMRELQ) in MP1.
                      { subst; vauto. }
                      { apply dtrmt_cmt in DTT1.
                        apply reexec_embd_dom in DTT1; vauto. }
                      apply wf_coE in CDD; [|apply INV'].
                      destruct CDD as [x4 [[INE EQQ] RF2]]; vauto. }
                    destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                            [x3 [CMT1 MP2]]].
                    apply (seq_inj SIMRELQ) in MP1.
                    { apply rexec_acts.
                      subst; vauto. }
                    { apply dtrmt_cmt in DTT1.
                      apply reexec_embd_dom in DTT1; vauto. }
                    apply wf_coE in CDD; [|apply INV'].
                    destruct CDD as [x4 [[INE EQQ] RF2]]; vauto. }
                  destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                        [x3 [CMT1 MP2]]].
                  apply (seq_inj SIMRELQ) in MP1.
                  { subst; vauto.
                    apply dtrmt_cmt in DTT1; vauto. }
                  { apply dtrmt_cmt in DTT1.
                    apply reexec_embd_dom in DTT1; vauto. }
                  apply wf_coE in CDD; [|apply INV'].
                  destruct CDD as [x4 [[INE EQQ] RF2]]; vauto. }
                split.
                { split.
                  { destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                          [x3 [CMT1 MP2]]].
                    apply (seq_inj SIMRELQ) in MP1.
                    { subst; vauto. }
                    { apply dtrmt_cmt in DTT1.
                      apply reexec_embd_dom in DTT1; vauto. }
                    apply wf_coE in CDD; [|apply INV'].
                    destruct CDD as [x4 [[INE EQQ]
                            [x5 [RF [INE2 EQ2]]]]]; vauto. }
                  destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                          [x3 [CMT1 MP2]]].
                  apply (seq_inj SIMRELQ) in MP1.
                  { apply rexec_acts.
                    subst; vauto. }
                  { apply dtrmt_cmt in DTT1.
                    apply reexec_embd_dom in DTT1; vauto. }
                  apply wf_coE in CDD; [|apply INV'].
                  destruct CDD as [x4 [[INE EQQ]
                            [x5 [RF [INE2 EQ2]]]]]; vauto. }
                destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                            [x3 [CMT1 MP2]]].
                apply (seq_inj SIMRELQ) in MP1.
                { subst; vauto.
                  apply dtrmt_cmt in DTT1; vauto. }
                { apply dtrmt_cmt in DTT1.
                  apply reexec_embd_dom in DTT1; vauto. }
                apply wf_coE in CDD; [|apply INV'].
                destruct CDD as [x4 [[INE EQQ]
                        [x5 [RF [INE2 EQ2]]]]]; vauto. }
              unfold WCore.X_start in H; ins.
              destruct H as [x2 [[EQ1 DT1] [x3 [RF [EQ2 DT2]]]]].
              subst; vauto. }
            { destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                    [x3 [CMT1 MP2]]].
              apply (seq_inj SIMRELQ) in MP1.
              { subst.
                apply DTRSAME; vauto. }
              { apply dtrmt_cmt in DTT1.
                apply reexec_embd_dom in DTT1; vauto. }
              apply wf_coE in CDD; [|apply INV'].
              destruct CDD as [x4 [[INE EQQ]
                      [x5 [RF [INE2 EQ2]]]]]; vauto. }
            destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                      [x3 [CMT1 MP2]]].
            apply (seq_inj SIMRELQ) in MP1.
            { subst.
              apply DTRSAME; vauto. }
            { apply dtrmt_cmt in DTT1.
              apply reexec_embd_dom in DTT1; vauto. }
            apply wf_coE in CDD; [|apply INV'].
            destruct CDD as [x4 [[INE EQQ]
                    [x5 [RF [INE2 EQ2]]]]]; vauto. }
          red; split; vauto.
          destruct CD3 as [[CD1 CD3] CD4]; vauto. }
        all : vauto. }
      { unfold WCore.X_start; ins.
        destruct STEP.
        destruct reexec_start_wf.
        destruct wf_ereq.
        split.
        { intros x y COND.
          unfold restr_rel in *.
          destruct COND as [CD1 [CD2 CD3]].
          split; vauto.
          destruct CD1 as [x0 [[EQ1 DT1]
                    [x1 [RF [EQ2 DT2]]]]]; subst.
          destruct ereq_rmw as [IN OUT].
          destruct DT1 as [x2 [DT1 M1]].
          destruct DT2 as [x3 [DT2 M2]].
          destruct IN with x2 x3.
          { unfold WCore.X_start; ins.
            apply (seq_rmw SIMREL) in RF.
            unfold collect_rel in RF.
            destruct RF as [x5 [x6 [RF [EQ3 EQ4]]]].
            splits.
            { unfold seq.
              exists x2; split; vauto.
              exists x3; split; vauto.
              assert (EQQ1 : x5 = x2).
              { assert (MEQ : mapper' x2 = mapper x2).
                { apply DTRSAME in DT1; vauto. }
                rewrite MEQ in EQ3.
                apply (seq_inj SIMREL) in EQ3; vauto.
                { apply wf_rmwE in RF; [|apply INV].
                  destruct RF as [x4 [[INE EQQ] RF2]]; vauto. }
                apply rexec_acts; vauto. }
              assert (EQQ2 : x6 = x3).
              { assert (MEQ : mapper' x3 = mapper x3).
                { apply DTRSAME in DT2; vauto. }
                rewrite MEQ in M2.
                apply (seq_inj SIMREL) in M2; vauto.
                { apply rexec_acts; vauto. }
                apply wf_rmwE in RF; [|apply INV].
                destruct RF as [x4 [[INE EQQ]
                        [x7 [RF [EQR INER]]]]]; vauto. }
              subst; vauto. }
            { split.
              { split; vauto.
                apply rexec_acts; vauto. }
              apply dtrmt_cmt in DT1; vauto. }
            split.
            { split; vauto.
              apply rexec_acts; vauto. }
            apply dtrmt_cmt in DT2; vauto. }
          unfold collect_rel.
          exists x2, x3; splits; vauto. }
        intros x y COND.
        unfold restr_rel in *.
        destruct COND as [CD1 [CD2 CD3]].
        destruct CD1 as [x0 [x1 [CDD [M1 M2]]]].
        splits.
        { unfold seq. exists x; split.
          { red; split; vauto.
            destruct CD2 as [[CD1 CD2] CD4]; vauto. }
          exists y; split.
          { apply (seq_rmw SIMREL).
            destruct ereq_rmw as [IN OUT].
            unfold collect_rel.
            exists x0, x1; splits; vauto.
            { destruct OUT with x0 x1.
              { split; vauto.
                unfold WCore.X_start; ins. split.
                { split.
                  { split.
                    { destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                                  [x3 [CMT1 MP2]]].
                      apply (seq_inj SIMRELQ) in MP1.
                      { subst; vauto. }
                      { apply dtrmt_cmt in DTT1.
                        apply reexec_embd_dom in DTT1; vauto. }
                      apply wf_rmwE in CDD; [|apply INV'].
                      destruct CDD as [x4 [[INE EQQ] RF2]]; vauto. }
                    destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                            [x3 [CMT1 MP2]]].
                    apply (seq_inj SIMRELQ) in MP1.
                    { apply rexec_acts.
                      subst; vauto. }
                    { apply dtrmt_cmt in DTT1.
                      apply reexec_embd_dom in DTT1; vauto. }
                    apply wf_rmwE in CDD; [|apply INV'].
                    destruct CDD as [x4 [[INE EQQ] RF2]]; vauto. }
                  destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                        [x3 [CMT1 MP2]]].
                  apply (seq_inj SIMRELQ) in MP1.
                  { subst; vauto.
                    apply dtrmt_cmt in DTT1; vauto. }
                  { apply dtrmt_cmt in DTT1.
                    apply reexec_embd_dom in DTT1; vauto. }
                  apply wf_rmwE in CDD; [|apply INV'].
                  destruct CDD as [x4 [[INE EQQ] RF2]]; vauto. }
                split.
                { split.
                  { destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                          [x3 [CMT1 MP2]]].
                    apply (seq_inj SIMRELQ) in MP1.
                    { subst; vauto. }
                    { apply dtrmt_cmt in DTT1.
                      apply reexec_embd_dom in DTT1; vauto. }
                    apply wf_rmwE in CDD; [|apply INV'].
                    destruct CDD as [x4 [[INE EQQ]
                            [x5 [RF [INE2 EQ2]]]]]; vauto. }
                  destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                          [x3 [CMT1 MP2]]].
                  apply (seq_inj SIMRELQ) in MP1.
                  { apply rexec_acts.
                    subst; vauto. }
                  { apply dtrmt_cmt in DTT1.
                    apply reexec_embd_dom in DTT1; vauto. }
                  apply wf_rmwE in CDD; [|apply INV'].
                  destruct CDD as [x4 [[INE EQQ]
                            [x5 [RF [INE2 EQ2]]]]]; vauto. }
                destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                            [x3 [CMT1 MP2]]].
                apply (seq_inj SIMRELQ) in MP1.
                { subst; vauto.
                  apply dtrmt_cmt in DTT1; vauto. }
                { apply dtrmt_cmt in DTT1.
                  apply reexec_embd_dom in DTT1; vauto. }
                apply wf_rmwE in CDD; [|apply INV'].
                destruct CDD as [x4 [[INE EQQ]
                        [x5 [RF [INE2 EQ2]]]]]; vauto. }
              unfold WCore.X_start in H; ins.
              destruct H as [x2 [[EQ1 DT1] [x3 [RF [EQ2 DT2]]]]].
              subst; vauto. }
            { destruct CD2 as [[[x2 [DTT1 MP1]] ES]
                    [x3 [CMT1 MP2]]].
              apply (seq_inj SIMRELQ) in MP1.
              { subst.
                apply DTRSAME; vauto. }
              { apply dtrmt_cmt in DTT1.
                apply reexec_embd_dom in DTT1; vauto. }
              apply wf_rmwE in CDD; [|apply INV'].
              destruct CDD as [x4 [[INE EQQ]
                      [x5 [RF [INE2 EQ2]]]]]; vauto. }
            destruct CD3 as [[[x2 [DTT1 MP1]] ES]
                      [x3 [CMT1 MP2]]].
            apply (seq_inj SIMRELQ) in MP1.
            { subst.
              apply DTRSAME; vauto. }
            { apply dtrmt_cmt in DTT1.
              apply reexec_embd_dom in DTT1; vauto. }
            apply wf_rmwE in CDD; [|apply INV'].
            destruct CDD as [x4 [[INE EQQ]
                    [x5 [RF [INE2 EQ2]]]]]; vauto. }
          red; split; vauto.
          destruct CD3 as [[CD1 CD3] CD4]; vauto. }
        all : vauto. }
      { unfold WCore.X_start; ins.
        rewrite (seq_data SIMREL).
        clear; basic_solver 8. }
      { unfold WCore.X_start; ins.
        rewrite (seq_ctrl SIMREL).
        clear; basic_solver 8. }
      unfold WCore.X_start; ins.
      rewrite (seq_rmw_dep SIMREL).
      clear; basic_solver 8. }
    { unfold rf_complete.
      unfold restrict; ins.
      arewrite ((fun x : actid =>
            ifP ~ (mapper' ↑₁ E_t') x
            then x
            else (ifP tid x <> t_2 then x
                  else ThreadEvent t_1
                   (t_1_len +
                    index x))) = mapper_rev').
      destruct STEP.
      intros x COND.
      destruct COND as [[CD2 CD3] CD1].
      destruct CD2 as [x0 [CM MP]].
      destruct reexec_start_wf.
      destruct wf_rfc with x0.
      { split.
        { unfold restrict; ins.
          split; vauto.
          apply reexec_embd_dom in CM; vauto. }
        unfold restrict; ins.
        unfold compose in CD1.
        unfold is_r in *.
        rewrite <- MP in CD1.
        unfold compose in MAPCOMP.
        rewrite MAPCOMP in CD1.
        { unfold id in CD1; vauto. }
        apply reexec_embd_dom in CM; vauto. }
      unfold restrict in H; ins.
      unfold codom_rel.
      exists (mapper' x1).
      unfold seq. exists (mapper' x1); split.
      { red. split; vauto.
        destruct H as [x2 [[EQQ CMM] MP]]; subst.
        unfold cmt'.
        unfold set_collect.
        exists x2; split; vauto. }
      exists x; split; vauto.
      unfold collect_rel.
      exists x1, x0; splits; vauto.
      destruct H as [x2 [[EQQ CMM]
              [x3 [RF [CM3 EQ]]]]]; subst; vauto. }
    intros x COND.
    destruct COND as [[DTT ESS] RD].
    destruct DTT as [x0 [DTT MP1]].
    destruct STEP.
    destruct reexec_start_wf.
    destruct wf_sub_rfD with x0.
    { unfold WCore.X_start; ins.
      split.
      { split; vauto.
        apply rexec_acts; vauto. }
      rewrite <- MP1 in RD.
      unfold is_r in *.
      destruct SIMREL.
      rewrite seq_lab.
      { unfold compose.
        assert (COND : mapper' x0 = mapper x0).
        { apply DTRSAME in DTT; vauto. }
        rewrite <- COND; vauto. }
      apply rexec_acts; vauto. }
    { left. unfold WCore.X_start; ins.
      destruct SIMREL.
      destruct H as [x1 PTH].
      unfold codom_rel. exists (mapper' x1).
      unfold seq. exists (mapper' x1); split.
      { red. split; vauto.
        unfold dtrmt'. unfold set_collect.
        exists x1; split; vauto.
        destruct PTH as [x2 [[EQQ CMM] MP]]; subst; vauto. }
      exists x; split; vauto.
      apply seq_rf.
      unfold collect_rel.
      exists x1, x0; splits; vauto.
      { destruct PTH as [x2 [[EQQ CMM]
              [x3 [RF [CM3 EQ]]]]]; subst; vauto. }
      { apply DTRSAME.
        destruct PTH as [x2 [[EQQ CMM] MP]]; vauto. }
      apply DTRSAME.
      destruct PTH as [x2 [[EQQ CMM] MP]]; vauto. }
    right.
    unfold cmt'.
    unfold set_collect.
    exists x0; split; vauto. }
  { apply XmmCons.monoton_cons with (G_t := G_t')
                    (m := mapper'); vauto.
    all : try arewrite (WCore.G X_s' = G_s').
    { apply SIMRELQ. }
    { unfold G_s'; ins.
      arewrite ((fun x : actid =>
          ifP ~ (mapper' ↑₁ E_t') x then x
          else (ifP tid x <> t_2 then x
                else ThreadEvent t_1
                      (t_1_len + index x))) = mapper_rev').
      unfold compose. unfold eq_dom.
      intros x COND.
      unfold compose in MAPCOMP.
      apply MAPCOMP in COND.
      rewrite COND.
      unfold id; vauto. }
    { intros x y PTH.
      destruct PTH as [SBP SL].
      unfold sb in SBP.
      unfold G_s' in SBP; ins.
      destruct SBP as [x0 [[EQ1 INE1]
                      [x1 [PTH [EQ2 INE2]]]]]; subst.
      unfold collect_rel.
      destruct INE1 as [x2 [INE1 M1]].
      destruct INE2 as [x3 [INE2 M2]].
      exists x2, x3; splits; vauto.
      split.
      { unfold sb.
        unfold seq. exists x2; split; vauto.
        exists x3; split; vauto.
        apply EXTSBL; vauto. }
      assert (MAPP : (fun x : actid =>
          ifP ~ (mapper' ↑₁ E_t') x then x
          else (ifP tid x <> t_2 then x
                else ThreadEvent t_1
                      (t_1_len + index x))) = mapper_rev') by vauto.
      rewrite MAPP in SL.
      unfold same_loc in SL.
      unfold loc in SL.
      unfold compose in SL.
      unfold compose in MAPCOMP.
      apply MAPCOMP in INE1.
      unfold id in INE1.
      apply MAPCOMP in INE2.
      unfold id in INE2.
      rewrite INE1, INE2 in SL.
      unfold same_loc, loc; vauto. }
    { apply INV'. }
    { arewrite (G_s' = (WCore.G X_s')).
      apply wf_transition with (X_t := X_t')
          (t_1 := t_1) (t_2 := t_2)
          (mapper := mapper') (mapper_rev := mapper_rev')
          (ptc_1 := ptc_1); vauto. }
    destruct STEP; vauto. }
  { destruct SIMREL.
    unfold dtrmt'. unfold WCore.reexec_thread.
    arewrite ((WCore.G X_s') = G_s').
    unfold G_s'; ins.
    rewrite <- set_collect_minus.
    { rewrite seq_acts.
      destruct STEP.
      rewrite rexec_acts at 1.
      rewrite set_collect_union.
      apply set_union_more.
      { split.
        { intros x COND.
          destruct COND as [x0 [COND EQ]].
          unfold set_collect.
          exists x0; split; vauto.
          symmetry.
          apply DTRSAME; vauto. }
        intros x COND.
        destruct COND as [x0 [COND EQ]].
        unfold set_collect.
        exists x0; split; vauto.
        apply DTRSAME; vauto. }
      unfold WCore.reexec_thread.
      split.
      { intros x COND.
        destruct COND as [x0 [COND EQ]].
        split.
        { unfold set_collect.
          exists x0; split; vauto.
          apply COND; vauto. }
        destruct COND as [CD1 CD2].
        unfold set_collect in CD2.
        unfold set_collect.
        unfold set_map in CD2.
        unfold set_map.
        destruct CD2 as [x1 [INE TIDS]].
        exists (mapper' x1); split; vauto.
        admit. (* ?????? *) }
      admit. }
    destruct STEP. rewrite dtrmt_cmt.
    rewrite reexec_embd_dom.
    destruct SIMRELQ.
    clear - seq_inj0.
    basic_solver. }
  apply sub_to_full_exec_listless
    with (thrdle := thrdle'); vauto.
  { admit. (* we have it *) }
  { admit. (* we have it *) }
  { admit. (* we have it *) }
  { admit. }
  { constructor.
    { unfold WCore.X_start; ins.
      destruct STEP; vauto.
      unfold dtrmt'. rewrite <- dtrmt_init.
      destruct SIMREL. rewrite seq_acts.
      split.
      { destruct SIMRELQ.
        unfold set_collect. exists x; split; vauto.
        apply seq_init0 in H; vauto. }
      unfold set_collect.
      exists x; split.
      { apply INV; vauto. }
      destruct SIMRELQ.
      apply seq_init in H; vauto. }
    { unfold WCore.X_start; ins.
      rewrite (seq_acts SIMREL).
      unfold dtrmt'. destruct STEP.
      rewrite dtrmt_cmt, reexec_embd_dom.
      admit. }
    all : admit. }
  { apply wf_transition with (X_t := X_t')
        (t_1 := t_1) (t_2 := t_2)
        (mapper := mapper') (mapper_rev := mapper_rev')
        (ptc_1 := ptc_1); vauto. }
  { unfold WCore.X_start; ins.
    destruct STEP.
    intros x COND.
    destruct COND as [MP NOT].
    intros FLS.
    assert (INITT: is_init x).
    { admit. (* is this a joke? *) }
    assert (INITT2: is_init x) by vauto.
    apply dtrmt_init in INITT.
    assert (DTRF : dtrmt' x).
    { unfold dtrmt'.
      unfold set_collect.
      exists x; split; vauto.
      destruct SIMRELQ.
      apply seq_init; vauto. }
    destruct NOT.
    split; vauto.
    destruct SIMREL.
    apply seq_acts.
    unfold set_collect.
    exists x; split; vauto.
    { apply rexec_acts; vauto. }
    destruct MP as [x0 [INE MPP]].
    apply seq_init; vauto. }
  admit. (* we have it *)
Admitted.

End SequentReexec.