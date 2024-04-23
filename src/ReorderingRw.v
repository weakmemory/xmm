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

(* TODO: ban ~E' b /\ E' a *)
Record reord_simrel_rw : Prop :=
{ rsrw_ninit1 : ~is_init a;
  rsrw_ninit2 : ~is_init b;

  rsrw_lab : lab' = upd (upd lab a (lab b)) b (lab a);
  rsrw_actids1 : forall (SAME : E' a <-> E' b), mapper ↑₁ E ≡₁ E';
  rsrw_actids2 : forall (INB : E' b) (NOTINA : ~ E' a),
                mapper ↑₁ E ≡₁ E' ∪₁ rsrw_a_subst;
  (* rpo stuff is disabled for now. *)
  (* rsrw_no_rpo1 : ~rpo a b;
  rsrw_no_rpo2 : ~rpo' a b;
  rsrw_rpo : rpo ≡ mapper ↑ rpo'; *)
  rsrw_rf1 : forall (SAME : E' a <-> E' b), mapper ↑ rf' ≡ rf;
  rsrw_rf2 : forall (INB : E' b) (NOTINA : ~ E' a),
                    rf ≡ mapper ↑ rf' ∪ srf' ⨾ ⦗rsrw_a_subst⦘;
  rsrw_co : co ≡ mapper ↑ co';
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

Lemma mapper_rsrw_a_subst G' a b
    (SAME : acts_set G' a <-> acts_set G' b)
    (NOTINA : ~acts_set G' a) :
  rsrw_a_subst (ReordCommon.mapped_G G' a b) a b ≡₁ ∅.
Proof using.
  unfold rsrw_a_subst; split; [| basic_solver].
  unfolder; ins; desf. apply NOTINA.
  rewrite ReordCommon.mapper_eq_b in IMMSB.
  unfold sb in IMMSB; unfolder in IMMSB; desf.
  now apply ReordCommon.mapper_set_iff in IMMSB2.
Qed.

Lemma mapper_simrel G' a b
    (ANIT : ~is_init a)
    (BNIT : ~is_init b)
    (SAME : acts_set G' a <-> acts_set G' b)
    (RPO : ~ rpo G' a b)
    (RPO' : ~ rpo (ReordCommon.mapped_G G' a b) a b)
    (NEQ : a <> b) :
  reord_simrel_rw (ReordCommon.mapped_G G' a b) G' a b.
Proof using.
  assert (SAME_ACTS : ReordCommon.mapper a b ↑₁
    (ReordCommon.mapper a b ↑₁ acts_set G') ≡₁ acts_set G').
  { rewrite !ReordCommon.mapper_set_iff; ins.
    rewrite <- 2!set_subset_single_l with (A := actid).
    rewrite !ReordCommon.mapper_set_iff; ins.
    now rewrite !set_subset_single_l with (A := actid). }

  constructor; ins.
  { unfold compose. apply functional_extensionality. intro x.
    rewrite ReordCommon.mapper_eq_a, ReordCommon.mapper_eq_b.
    destruct (classic (x = a)) as [EQA|EQA],
             (classic (x = b)) as [EQB|EQB].
    all: try subst x; subst; rupd; auto.
    now rewrite ReordCommon.mapper_neq. }
  { rewrite mapper_rsrw_a_subst, set_union_empty_r; ins. }
  (* { unfold ReordCommon.mapped_G, rpo; ins.
    rewrite !collect_rel_union, !collect_rel_seq, !collect_rel_eqv.
    all: eauto using ReordCommon.mapper_inj_dom.
    repeat apply union_more.
    all: admit. } *)
  rewrite mapper_rsrw_a_subst; auto.
  now rewrite eqv_empty, seq_false_r, union_false_r.
Qed.


Lemma sim_rel_init G G' a b
    (INIT_WF : Wf (WCore.init_exec G))
    (INIT_WF' : Wf (WCore.init_exec G'))
    (ANIT : ~is_init a)
    (BNIT : ~is_init b)
    (INIT : acts_set G ∩₁ is_init ≡₁ acts_set G' ∩₁ is_init)
    (LAB : lab G' = upd (upd (lab G) a (lab G b)) b (lab G a)) :
  reord_simrel_rw (WCore.init_exec G) (WCore.init_exec G') a b.
Proof using.
  assert (RSRW_EMPTY : rsrw_a_subst (WCore.init_exec G) a b ≡₁ ∅).
  { unfold rsrw_a_subst; split; [| basic_solver].
    intros a' [_ IMM]; unfolder.
    apply immediate_in in IMM. unfold sb in IMM.
    unfolder in IMM; desf; ins; desf.
    rewrite ReordCommon.mapper_eq_b in IMM2; eauto. }

  constructor; ins.
  all: try rewrite mapper_init; ins.
  all: try rewrite collect_rel_empty; ins.
  { now rewrite RSRW_EMPTY, set_union_empty_r. }
  (* { intro F; apply wf_rpoE in F; auto.
    unfolder in F; desf; ins; desf; eauto. }
  { intro F; apply wf_rpoE in F; auto.
    unfolder in F; desf; ins; desf; eauto. }
  { admit. } *)
  rewrite RSRW_EMPTY; basic_solver.
Qed.

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
  exists (ReordCommon.mapped_G Gt' a b); split.
  { admit. }
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

(*
 forall traces P_src, P_trgt. If target is a reordereing of src, then
 <..> (clarify cuz the theorem statement looks weird)
*)
(* Theorem reordering_rw : TODO.
Proof using.
  admit.
Admitted. *)


End ReordRwSimRelProps.