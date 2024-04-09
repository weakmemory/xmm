Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.
Require Import ReorderingCommon.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.
From imm Require Import CombRelations.

Section SimRel.

(* G -- source, G' -- target *)
Variable G G' : execution.
Variable a b : actid.

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'rpo''" := (rpo G').
Notation "'srf''" := (srf G').

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'rpo'" := (rpo G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).

Notation "'mapper'" := (ReordCommon.mapper a b).

Definition rsrw_a_subst a' : Prop :=
  << LABEQU2V : same_label_u2v (lab a') (lab a) >> /\
  << IMMSB : immediate sb a' (mapper b) >>
.

Record reord_simrel_rw : Prop :=
{ rsrw_ninit1 : ~is_init a;
  rsrw_ninit2 : ~is_init b;

  rsrw_lab : lab' = upd (upd lab a (lab b)) b (lab a);
  rsrw_actids1 : forall (SAME : E' a <-> E' b), E ≡₁ mapper ↓₁ E';
  rsrw_actids2 : forall (INB : E' b) (NOTINA : ~ E' a),
                E ≡₁ mapper ↓₁ E' ∪₁ rsrw_a_subst;
  rsrw_no_rpo1 : ~rpo a b;
  rsrw_no_rpo2 : ~rpo' a b;
  rsrw_rpo : rpo ≡ mapper ↓ rpo;
  rsrw_rf1 : forall (SAME : E' a <-> E' b), rf' ≡ mapper ↓ rf;
  rsrw_rf2 : forall (INB : E' b) (NOTINA : ~ E' a),
                rf ≡ mapper ↓ rf' ∪ mapper ↓ srf' ⨾ ⦗rsrw_a_subst⦘;
  rsrw_co : co ≡ mapper ↓ co';
}.

End SimRel.

Module ReordRwSimRelProps.

Lemma sim_rel_init G G' a b :
  reord_simrel_rw (WCore.init_exec G) (WCore.init_exec G') a b.
Proof using.
  admit.
Admitted.

Section ExecutionSteps.

Variable Gt Gt' Gs : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Notation "'mapper'" := (ReordCommon.mapper a b).

(* Hypothesis SWAPPED_TRACES : traces_swapped traces traces'. *)
Hypothesis SWAPPED_TRACES : True.

Lemma simrel_exec_not_a_not_b e l
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons Gt)
    (CONS' : WCore.is_cons Gs)
    (SIM : reord_simrel_rw Gs Gt a b)
    (STEP : WCore.exec_inst Gt Gt' traces e l) :
  exists Gs',
    << STEP' : WCore.exec_inst Gs Gs' traces' e l >> /\
    << SIM' : reord_simrel_rw Gs' Gt' a b >>.
Proof using SWAPPED_TRACES.
  admit.
Admitted.

Lemma simrel_exec_b
    (CONS : WCore.is_cons Gt)
    (CONS' : WCore.is_cons Gs)
    (SIM : reord_simrel_rw Gs Gt a b)
    (STEP : WCore.exec_inst Gt Gt' traces b (lab Gt b)) :
  exists Gs'_int Gs' a',
    << STEP1 : WCore.exec_inst Gs Gs'_int traces' a' (lab Gt' a') >> /\
    << STEP2 : WCore.exec_inst Gs'_int Gs' traces' (mapper b) (lab Gt' (mapper b)) >> /\
    << SIM' : reord_simrel_rw Gs' Gt' a b >>.
Proof using SWAPPED_TRACES.
  admit.
Admitted.

Lemma simrel_exec_a w
    (CONS : WCore.is_cons Gt)
    (CONS' : WCore.is_cons Gs)
    (RF : Gt.(rf) w a)
    (SIM : reord_simrel_rw Gs Gt a b)
    (STEP : WCore.exec_inst Gt Gt' traces a (lab Gt a)) :
  exists Gs' rfre,
    << STEP : WCore.reexec Gs Gs' rfre traces' >> /\
    << SIM' : reord_simrel_rw Gs' Gt' a b >>.
Proof using SWAPPED_TRACES.
  admit.
Admitted.

Lemma simrel_reexec rfre
    (CONS : WCore.is_cons Gt)
    (CONS' : WCore.is_cons Gs)
    (SIM : reord_simrel_rw Gs Gt a b)
    (STEP : WCore.reexec Gt Gt' rfre traces) :
  exists Gs' rfre,
    << STEP : WCore.reexec Gs Gs' (mapper ↓ rfre) traces' >> /\
    << SIM' : reord_simrel_rw Gs' Gt' a b >>.
Proof using SWAPPED_TRACES.
  admit.
Admitted.

End ExecutionSteps.

Section SimrelPreservations.

Variable Gs Gt : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Lemma simrel_implies_cons
    (CONS : WCore.is_cons Gt)
    (SIM : reord_simrel_rw Gs Gt a b) :
  WCore.is_cons Gs.
Proof using.
  admit.
Admitted.

Lemma simrel_term
    (CONS : WCore.is_cons Gt)
    (SIM : reord_simrel_rw Gt Gs a b)
    (TERM : machine_terminated Gt traces) :
  << TERM' : machine_terminated Gs traces' >> /\
  << SIM' : ReordCommon.reord Gs Gt traces traces' a b >>.
Proof using.
  admit.
Admitted.

End SimrelPreservations.

(* Lemma sim_rel_step : about any step *)

End ReordRwSimRelProps.