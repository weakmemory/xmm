Require Import Core.
Require Import ReordSimrel ReorderingMapper.
Require Import ReorderingExecA ReorderingExecB.
Require Import ReordExecNaNb ReorderingReexec.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Section ReorderingSteps.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t : actid.
Variable traces_t traces_s : thread_id -> trace label -> Prop.

Notation "'mapper'" := (mapper a_t b_t).

Definition event_mem (a : actid) (t : trace label) : Prop :=
  match t, a with
  | _, InitEvent _ => False
  | trace_inf _, _ => True
  | trace_fin l, ThreadEvent _ n => n < length l
  end.

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
    ) b_t.

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
  prf_tid : tid b_t = tid a_t;
  prf_at_bt_neq : a_t <> b_t;
  prf_bt_at_imm : immediate ext_sb b_t a_t;
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

End ReorderingSteps.