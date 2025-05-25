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
From xmm Require Import SequentExec.
From xmm Require Import SequentExec2.
From xmm Require Import SequentExec3.
From xmm Require Import SequentReexec.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import Setoid Morphisms Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section SimrelGen.

Variable X_t X_t' X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.
Variable mapper_rev : actid -> actid.

Variable ptc_1 ptc_2 : program_trace.

Variable dtrmt_t cmt_t : actid -> Prop.
Variable thrdle : relation thread_id.

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

Lemma seq_step_gen
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRDNEQ : t_1 <> t_2)
    (STEP : xmm_step X_t X_t')
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper mapper_rev ptc_1) :
  exists X_s' mapper' mapper_rev',
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' mapper_rev' ptc_1 >> /\
    << STEP : xmm_step⁺ X_s X_s' >>.
Proof using.
  admit.
Admitted.

End SimrelGen.

Section BehaviorGraph.

Variable G_1 G_2 : execution.

Notation "'E_1'" := (acts_set G_1).

Notation "'lab'" := (lab G_1).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).

Definition graph_locations (G : execution) : Set :=
  { l : location | exists e, acts_set G e /\ loc e = Some l }.

Definition same_behaviors (G_1 G_2 : execution) : Prop :=
  behavior_spec G_1 = behavior_spec G_2.

End BehaviorGraph.

Section SimrelMain.

Variable X_t_init X_s_init X_t : WCore.t.
Variable t_1 t_2 : thread_id.
Variable ptc_1 ptc_2 : program_trace.

Notation "'G_t_init'" := (WCore.G X_t_init).
Notation "'G_s_init'" := (WCore.G X_s_init).
Notation "'G_t'" := (WCore.G X_t).

Notation "'R' G" := (fun e => is_true (is_r (lab G) e)) (at level 1).
Notation "'F' G" := (fun e => is_true (is_f (lab G) e)) (at level 1).
Notation "'W' G" := (fun e => is_true (is_w (lab G) e)) (at level 1).
Notation "'Acq' G" := (fun e => is_true (is_acq (lab G) e)) (at level 1).
Notation "'Rlx' G" := (fun e => is_true (is_rlx (lab G) e)) (at level 1).
Notation "'Rel' G" := (fun e => is_true (is_rel (lab G) e)) (at level 1).

Notation "'lab_t_init'" := (lab G_t_init).
Notation "'val_t_init'" := (val lab_t_init).
Notation "'loc_t_init'" := (loc lab_t_init).
Notation "'same_loc_t_init'" := (same_loc lab_t_init).
Notation "'E_t_init'" := (acts_set G_t_init).
Notation "'sb_t_init'" := (sb G_t_init).
Notation "'rf_t_init'" := (rf G_t_init).
Notation "'co_t_init'" := (co G_t_init).
Notation "'rmw_t_init'" := (rmw G_t_init).
Notation "'rpo_t_init'" := (rpo G_t_init).
Notation "'rmw_dep_t_init'" := (rmw_dep G_t_init).
Notation "'data_t_init'" := (data G_t_init).
Notation "'ctrl_t_init'" := (ctrl G_t_init).
Notation "'addr_t_init'" := (addr G_t_init).
Notation "'W_t_init'" := (fun x => is_true (is_w lab_t_init x)).
Notation "'R_t_init'" := (fun x => is_true (is_r lab_t_init x)).
Notation "'Loc_t_init_' l" := (fun e => loc_t_init e = l) (at level 1).

Notation "'lab_s_init'" := (lab G_s_init).
Notation "'val_s_init'" := (val lab_s_init).
Notation "'loc_s_init'" := (loc lab_s_init).
Notation "'same_loc_s_init'" := (same_loc lab_s_init).
Notation "'E_s_init'" := (acts_set G_s_init).
Notation "'loc_s_init'" := (loc lab_s_init).
Notation "'sb_s_init'" := (sb G_s_init).
Notation "'rf_s_init'" := (rf G_s_init).
Notation "'co_s_init'" := (co G_s_init).
Notation "'rmw_s_init'" := (rmw G_s_init).
Notation "'rpo_s_init'" := (rpo G_s_init).
Notation "'rmw_dep_s_init'" := (rmw_dep G_s_init).
Notation "'data_s_init'" := (data G_s_init).
Notation "'ctrl_s_init'" := (ctrl G_s_init).
Notation "'addr_s_init'" := (addr G_s_init).
Notation "'W_s_init'" := (fun x => is_true (is_w lab_s_init x)).
Notation "'R_s_init'" := (fun x => is_true (is_r lab_s_init x)).
Notation "'Loc_s_init_' l" := (fun e => loc_s_init e = l) (at level 1).

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

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Lemma simrel_main
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRDNEQ : t_1 <> t_2)
    (TARGETPTH : xmm_step＊ X_t_init X_t) :
  exists X_s mapper mapper_rev,
    << SIMREL : seq_simrel X_s X_t t_1 t_2 mapper mapper_rev ptc_1>> /\
    << STEP : xmm_step＊ X_s_init X_s >> /\
    << BEHRS : same_behaviors (WCore.G X_s) G_t >>.
Proof using.
  admit.
Admitted.

End SimrelMain.

Section ProgMain.

Variable X_t : WCore.t.
Variable t_1 t_2 : thread_id.
Variable threads : thread_id -> Prop.
Variable ptc_1 ptc_2 : program_trace.

Variable p1 p2 : program.

Definition X_t_init : WCore.t := WCore.Build_t (WCore.init_exec threads) ∅₂.
Definition X_s_init : WCore.t := WCore.Build_t (WCore.init_exec (threads ∪₁ eq t_2)) ∅₂.

Hypothesis PROGSEQ : program_sequented p1 p2 t_1 t_2.

Lemma prog_supp : 
  exists X_s mapper mapper_rev,
    << SIMREL : seq_simrel X_s X_t t_1 t_2 mapper mapper_rev ptc_1>> /\
    << STEP   : xmm_step＊ X_s_init X_s >> /\
    << BEHRS  : same_behaviors (WCore.G X_s) (WCore.G X_t) >>.
Proof using.
  admit.
Admitted.

Lemma prog_helper X_s mapper mapper_rev :
  seq_simrel X_s X_t t_1 t_2 mapper mapper_rev ptc_1 ->
  exec_sequent X_s X_t p1 p2 t_1 t_2.
Proof using.
  intros SIMREL.
  constructor; vauto.
  intros tr_1 tr2 TR1 TR2 CR1 CR2.
  constructor. all : admit.
Admitted.

Lemma prog_main :
  exists X_s,
    << SEQUED : exec_sequent X_s X_t p1 p2 t_1 t_2 >> /\
    << STEP   : xmm_step＊ X_s_init X_s >> /\
    << BEHRS  : same_behaviors (WCore.G X_s) (WCore.G X_t) >>.
Proof using.
  destruct prog_supp as (X_s & mapper & mapper_rev & SIMREL & STEP & BEHRS).
  exists X_s; splits; auto.
  apply prog_helper with (mapper := mapper)
  (mapper_rev := mapper_rev).
  vauto.
Admitted.

End ProgMain.
