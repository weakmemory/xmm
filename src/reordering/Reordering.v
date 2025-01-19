Require Import AuxDef Core Lia.
Require Import ReordSimrel ReorderingMapper.
Require Import ReorderingExecA ReorderingExecB.
Require Import ReordExecNaNb ReorderingReexec.
Require Import ThreadTrace TraceSwap.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Definition event_mem (a : actid) (t : trace label) : Prop :=
  match t, a with
  | _, InitEvent _ => False
  | trace_inf _, _ => True
  | trace_fin l, ThreadEvent _ n => n < length l
  end.

Lemma event_memE G e
    (NINIT : tid e <> tid_init)
    (CONT : contigious_actids G) :
  event_mem e (thread_trace G (tid e)) <->
    acts_set G e.
Proof using.
  destruct e as [el | et en]; ins.
  red in CONT. destruct (CONT _ NINIT) as [N EQ].
  split; intros HSET.
  { enough (IN' :
      (acts_set G ∩₁ (fun e => et = tid e))
        (ThreadEvent et en)
    ).
    { apply IN'. }
    apply EQ, thread_set_iff.
    unfold thread_trace, thread_actid_trace in HSET.
    ins. rewrite EQ, thread_seq_set_size in HSET.
    ins. now autorewrite with calc_length in HSET. }
  unfold thread_trace, thread_actid_trace.
  ins. rewrite EQ, thread_seq_set_size.
  ins. autorewrite with calc_length.
  eapply thread_set_iff, EQ. basic_solver.
Qed.

Section ReorderingSteps.

Variable X_t X_t' X_s : WCore.t.
Variable rtid : thread_id.
Variable i_b : nat.
Variable traces_t traces_s : trace_storage.

Definition i_a := i_b + 1.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'W_t'" := (fun e => is_true (is_w lab_t e)).
Notation "'R_t'" := (fun e => is_true (is_r lab_t e)).
Notation "'F_t'" := (fun e => is_true (is_f lab_t e)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).
Notation "'Val_t_' l" := (fun e => val_t e = l) (at level 1).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'same_val_t'" := (same_val lab_t).
Notation "'Acq_t'" := (fun e => is_true (is_acq lab_t e)).
Notation "'Rel_t'" := (fun e => is_true (is_rel lab_t e)).
Notation "'Rlx_t'" := (fun e => is_true (is_rlx lab_t e)).
Notation "'Sc_t'" := (fun e => is_true (is_sc lab_t e)).

Notation "'b_t'" := (ThreadEvent rtid i_b).
Notation "'a_t'" := (ThreadEvent rtid i_a).
Notation "'mapper'" := (mapper a_t b_t).

Definition prefix_closed
    (t : thread_id) :
  Prop :=
    forall tr tr' (IN : traces_t t tr) (PREF : trace_prefix tr' tr),
      traces_t t tr'.

Definition full_coverage : Prop :=
  forall tr (TRIN : traces_t (tid b_t) tr) (IN : event_mem b_t tr),
    exists tr',
      << PREF : trace_prefix tr tr' >> /\
      << AIN : event_mem a_t tr' >>.

Definition correct_loc : Prop :=
  forall (tr : trace label) (TRIN : traces_t (tid b_t) tr)
    (BIN : event_mem b_t tr) (AIN : event_mem a_t tr),
      WCore.lab_loc (trace_nth (index b_t) tr (Afence Opln)) <>
      WCore.lab_loc (trace_nth (index a_t) tr (Afence Opln)).

Definition correct_op_bt : Prop :=
  forall (tr : trace label)
    (TRIN : traces_t (tid b_t) tr) (BIN : event_mem b_t tr),
      (
        WCore.lab_is_r (trace_nth (index b_t) tr (Afence Opln)) ∪₁
        WCore.lab_is_w (trace_nth (index b_t) tr (Afence Opln))
      ) b_t.

Definition correct_op_at : Prop :=
  forall (tr : trace label)
    (TRIN : traces_t (tid a_t) tr) (BIN : event_mem a_t tr),
    (
      WCore.lab_is_r (trace_nth (index a_t) tr (Afence Opln)) ∪₁
      WCore.lab_is_w (trace_nth (index a_t) tr (Afence Opln))
    ) a_t.

Definition correct_mod_bt : Prop :=
  forall (tr : trace label)
    (TRIN : traces_t (tid b_t) tr) (BIN : event_mem b_t tr),
    ~mode_le Orel (WCore.lab_mode (
      trace_nth (index b_t) tr (Afence Opln)
    )).

Definition correct_mod_at : Prop :=
  forall (tr : trace label)
    (TRIN : traces_t (tid a_t) tr) (BIN : event_mem a_t tr),
    ~mode_le Oacq (WCore.lab_mode (
      trace_nth (index a_t) tr (Afence Opln)
    )).

Record correct_traces_t : Prop := {
  prf_at_tid : rtid <> tid_init;
  prf_closed : forall t (NINIT : t <> tid_init), prefix_closed t;
  prf_cov : full_coverage;
  prf_loc : correct_loc;
  prf_op_bt : correct_op_bt;
  prf_op_at : correct_op_at;
  prf_mod_bt : correct_mod_bt;
  prf_mod_at : correct_mod_at;
}.

Lemma simrel_xmm_step
    (INV : reord_step_pred X_t a_t b_t)
    (INV' : reord_step_pred X_t' a_t b_t)
    (STEP : xmm_step X_t X_t')
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper) :
  exists X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t b_t mapper >> /\
    << STEP : xmm_step⁺ X_s X_s' >>.
Proof using.
  admit.
Admitted.

Lemma corr_coh_inv
    (WF : Wf G_t)
    (RFC : rf_complete G_t)
    (INIT : is_init ⊆₁ E_t)
    (DEP : rmw_dep_t ≡ ∅₂)
    (DATA : data_t ≡ ∅₂)
    (CTRL : ctrl_t ≡ ∅₂)
    (ADDR : addr_t ≡ ∅₂)
    (CONT : contigious_actids G_t)
    (CORR : correct_traces_t)
    (FIN : set_finite (E_t \₁ is_init))
    (COH : trace_coherent traces_t G_t)
    (INITTID : E_t ∩₁ (fun e => tid e = tid_init) ⊆₁ is_init)
    (RMWD : rmw G_t ⊆ Sc_t × Sc_t) :
  reord_step_pred X_t a_t b_t.
Proof using.
  set (tr := thread_trace G_t rtid).
  assert (NINIT : rtid <> tid_init) by apply CORR.
  assert (EXTSB : ext_sb b_t a_t).
  { unfold ext_sb, i_a. split; auto; lia. }
  assert (NACQ : eq a_t ∩₁ E_t ⊆₁ set_compl Acq_t).
  { unfolder. intros x (EQ & XIN). subst x.
    intro FALSO. apply (prf_mod_at CORR) with tr; auto.
    { apply event_memE; auto. }
    unfold WCore.lab_mode, is_acq in *.
    subst tr. rewrite thread_trace_nth'; auto. }
  assert (NREL : eq b_t ∩₁ E_t ⊆₁ set_compl Rel_t).
  { unfolder. intros x (EQ & XIN). subst x.
    intro FALSO. apply (prf_mod_bt CORR) with tr; auto.
    { apply event_memE; auto. }
    unfold WCore.lab_mode, is_rel in *.
    subst tr. rewrite thread_trace_nth'; auto. }
  constructor; ins.
  { unfolder. intros x (EQ & XIN). subst x.
    destruct (prf_op_at CORR tr) as [ISR|ISW].
    { apply COH, CORR. }
    { apply event_memE; auto. }
    { right. unfold WCore.lab_is_r, is_r in *.
      subst tr.
      rewrite thread_trace_nth' in ISR; auto.
      desf. }
    left. unfold WCore.lab_is_w, is_w in *.
    subst tr.
    rewrite thread_trace_nth' in ISW; auto.
    desf. }
  { unfolder. intros x (EQ & XIN). subst x.
    destruct (prf_op_bt CORR tr) as [ISR|ISW].
    { apply COH, CORR. }
    { apply event_memE; auto. }
    { right. unfold WCore.lab_is_r, is_r in *.
      subst tr.
      rewrite thread_trace_nth' in ISR; auto.
      desf. }
    left. unfold WCore.lab_is_w, is_w in *.
    subst tr.
    rewrite thread_trace_nth' in ISW; auto.
    desf. }
  { unfolder. intros x y ((XEQ & XIN) & SLOC & (YEQ & YIN)).
    subst x y. apply (prf_loc CORR) with tr; auto.
    { apply event_memE; auto. }
    { apply event_memE; auto. }
    unfold same_loc, loc, WCore.lab_loc in *.
    subst tr. rewrite !thread_trace_nth'; auto. }
  { red in CONT. destruct (CONT _ NINIT) as [N EQ].
    assert (INA' : (E_t ∩₁ (fun e => rtid = tid e)) a_t).
    { basic_solver. }
    enough (INB' : (E_t ∩₁ (fun e => rtid = tid e)) b_t).
    { apply INB'. }
    apply EQ, thread_set_iff. apply EQ, thread_set_iff in INA'.
    unfold i_a in INA'. lia. }
  { unfold sb. unfolder. intros x y (((XEQ & XIN) & _) & SB & YIN).
    apply NINA. subst x. destruct y as [yl | yt yn]; ins.
    destruct classic with (yn = i_b + 1) as [EQ|NEQ].
    { desf. }
    apply ext_sb_dense with (e2 := (ThreadEvent yt yn)); auto.
    red. desf; split; ins. unfold i_a. lia. }
  { intros x y RMW. unfolder.
    apply (wf_rmwE WF) in RMW.
    unfolder in RMW. destruct RMW as (XIN & RMW & YIN).
    apply RMWD in RMW. destruct RMW as [XSC YSC].
    splits; auto.
    all: intro FALSO.
    { subst x. apply NACQ with a_t; [basic_solver|].
      unfold is_sc, is_acq in *. desf. }
    { subst x. apply NREL with b_t; [basic_solver|].
      unfold is_sc, is_rel in *. desf. }
    { subst y. apply NACQ with a_t; [basic_solver|].
      unfold is_sc, is_acq in *. desf. }
    subst y. apply NREL with b_t; [basic_solver|].
    unfold is_sc, is_rel in *. desf. }
  { unfold i_a. intro FALSO. desf. lia. }
  { unfold sb. unfolder.
    intros x y ((XEQ & XIN) & YEQ & YIN). subst x y.
    splits; auto. intros c (_ & BC & CIN) (_ & CA & _).
    unfold i_a in *. ins. desf. ins. desf. lia. }
  unfolder. intros x y (XEQ & SB & YIN). subst x.
  apply NINA, ext_sb_dense with (e2 := y); auto.
Qed.

End ReorderingSteps.