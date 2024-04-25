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

Variable G_s G_t : execution.
Variable a b : actid.

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
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
Notation "'srf_t'" := (srf G_t).

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
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
Notation "'W_s'" := (is_w lab_s).
Notation "'R_s'" := (is_r lab_s).

Notation "'mapper'" := (ReordCommon.mapper a b).

(* TODO: ban ~E' b /\ E' a *)
(* We should require srf *)
(* srf is functional *)
(* psc -> sc *)
Record reord_simrel_rw : Prop :=
{ rsrw_ninit1 : ~is_init a;
  rsrw_ninit2 : ~is_init b;

  rsrw_lab_u2v : same_lab_u2v lab_s (lab_t ∘ mapper);
  rsrw_lab_v : forall e (NOTA : e <> a), val_s e = (val_t ∘ mapper) e;
  rsrw_actids_t_ord : forall (INA : E_t b) (NOTINB : ~E_t a), False;

  rsrw_sb1 : forall (SAME : E_t a <-> E_t b), immediate sb_s ≡ immediate sb_t;
  rsrw_sb2 : forall (INB : E_t a) (NOTINA : ~E_t b),
                immediate sb_s ≡ immediate sb_t ∪ singl_rel a b;
  rsrw_actids1 : forall (SAME : E_t a <-> E_t b), E_s ≡₁ E_t;
  rsrw_actids2 : forall (INB : E_t a) (NOTINA : ~E_t b),
                 E_s ≡₁ E_t ∪₁ eq b;
  rsrw_rf1 : forall (SAME : E_t a <-> E_t b), rf_s ≡ mapper ↑ rf_t;
  rsrw_rf2 : forall (INB : E_t a) (NOTINA : ~ E_t b),
                    rf_s ≡ mapper ↑ rf_t ∪ srf_t ⨾ ⦗eq b⦘;
  rsrw_co : co_s ≡ mapper ↑ co_t;
}.

End SimRel.

Module ReordRwSimRelProps.

(* TODO: move to Common *)
Lemma mapper_init G a b
    (ANIT : ~is_init a)
    (BNIT : ~is_init b) :
  ReordCommon.mapper a b ↑₁ (acts_set G ∩₁ is_init) ≡₁ acts_set G ∩₁ is_init.
Proof using.
  unfold ReordCommon.mapper.
  unfolder; split; desf; intros x.
  { intros (y & IN & EQ); generalize EQ; clear EQ.
    destruct (classic (y = a)) as [HA|HA],
             (classic (y = b)) as [HB|HB].
    all: subst; rupd; ins; desf; exfalso; eauto. }
  destruct (classic (x = a)) as [HA|HA],
           (classic (x = b)) as [HB|HB].
  all: subst; ins; desf.
  exists x; rupd.
Qed.

Lemma mapper_simrel_iff G' a b
    (ANIT : ~is_init a)
    (BNIT : ~is_init b)
    (SAME : acts_set G' a <-> acts_set G' b)
    (NEQ : a <> b) :
  reord_simrel_rw (ReordCommon.mapped_G_t G' a b) G' a b.
Proof using.
  constructor; ins.
  { unfold same_lab_u2v, same_lab_u2v_dom, same_label_u2v.
    ins. desf. }
  { now apply NOTINB, SAME. }
  all: exfalso; now apply NOTINA, SAME.
Qed.

(* TODO: constraint on a and b *)
Lemma mapper_simrel_niff G' a b
    (ANIT : ~is_init a)
    (BNIT : ~is_init b)
    (INA : acts_set G' a)
    (NOTINB : ~acts_set G' b)
    (NEQ : a <> b) :
  reord_simrel_rw (ReordCommon.mapped_G_t_with_b G' a b) G' a b.
Proof using.
  constructor; ins.
  { unfold same_lab_u2v, same_lab_u2v_dom, same_label_u2v.
    ins. desf. }
  all: try now (exfalso; apply NOTINB, SAME, INA).
  { apply ReordCommon.mapped_G_t_imm_sb; ins.
    all: admit. } (* TODO constraints *)
  admit. (* TODO: Why do we have an srf edge *)
Admitted.

Lemma sim_rel_init G G' a b
    (INIT_WF : Wf (WCore.init_exec G))
    (INIT_WF' : Wf (WCore.init_exec G'))
    (ANIT : ~is_init a)
    (BNIT : ~is_init b)
    (INIT : acts_set G ∩₁ is_init ≡₁ acts_set G' ∩₁ is_init)
    (LAB : lab G' = upd (upd (lab G) a (lab G b)) b (lab G a)) :
  reord_simrel_rw (WCore.init_exec G) (WCore.init_exec G') a b.
Proof using.
  admit.
  (* constructor; ins.
  all: try rewrite mapper_init; ins.
  all: try rewrite collect_rel_empty; ins.
  { now rewrite RSRW_EMPTY, set_union_empty_r. }
  rewrite RSRW_EMPTY; basic_solver. *)
Admitted.

Section ExecutionSteps.

Variable Gt Gt' Gs : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Notation "'mapper'" := (ReordCommon.mapper a b).

Hypothesis SWAPPED_TRACES : ReordCommon.traces_swapped traces traces' a b.

Lemma simrel_exec_not_a_not_b e
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons Gt)
    (CONS' : WCore.is_cons Gs)
    (SIM : reord_simrel_rw Gs Gt a b)
    (STEP : WCore.exec_inst Gt Gt' traces e) :
  exists Gs',
    << STEP' : WCore.exec_inst Gs Gs' traces' e >> /\
    << SIM' : reord_simrel_rw Gs' Gt' a b >>.
Proof using SWAPPED_TRACES.
  admit.
Admitted.

Lemma simrel_exec_b
    (CONS : WCore.is_cons Gt)
    (CONS' : WCore.is_cons Gs)
    (SIM : reord_simrel_rw Gs Gt a b)
    (STEP : WCore.exec_inst Gt Gt' traces b) :
  exists Gs'_int Gs' a',
    << STEP1 : WCore.exec_inst Gs Gs'_int traces' a' >> /\
    << STEP2 : WCore.exec_inst Gs'_int Gs' traces' (mapper b) >> /\
    << SIM' : reord_simrel_rw Gs' Gt' a b >>.
Proof using SWAPPED_TRACES.
  admit.
Admitted.

Lemma simrel_exec_a w
    (CONS : WCore.is_cons Gt)
    (CONS' : WCore.is_cons Gs)
    (RF : Gt.(rf) w a)
    (SIM : reord_simrel_rw Gs Gt a b)
    (STEP : WCore.exec_inst Gt Gt' traces a) :
  exists Gs' rfre,
    << STEP : WCore.reexec Gs Gs' traces' rfre >> /\
    << SIM' : reord_simrel_rw Gs' Gt' a b >>.
Proof using SWAPPED_TRACES.
  admit.
Admitted.

Lemma simrel_reexec rfre
    (CONS : WCore.is_cons Gt)
    (CONS' : WCore.is_cons Gs)
    (SIM : reord_simrel_rw Gs Gt a b)
    (STEP : WCore.reexec Gt Gt' traces rfre) :
  exists Gs' rfre,
    << STEP : WCore.reexec Gs Gs' traces' (mapper ↓ rfre) >> /\
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

(*
 forall traces P_src, P_trgt. If target is a reordereing of src, then
 <..> (clarify cuz the theorem statement looks weird)
*)
(* Theorem reordering_rw : TODO.
Proof using.
  admit.
Admitted. *)


End ReordRwSimRelProps.