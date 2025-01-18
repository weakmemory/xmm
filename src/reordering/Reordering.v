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

Notation "'mapper'" := (mapper a_t b_t).

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