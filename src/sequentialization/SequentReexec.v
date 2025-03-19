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
From xmm Require Import ConsistencyMonotonicity.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
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

Definition cmt' := id ↑₁ cmt_t.
Definition dtrmt' := id ↑₁ dtrmt_t.

Definition thrdle' := eq t_2 × eq t_1 ∪ dom_rel (thrdle ⨾ ⦗eq t_1⦘) × eq t_2
                      ∪ eq t_1 × codom_rel (⦗eq t_2⦘ ⨾ thrdle).

Lemma simrel_step_reex
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper) :
  exists (X_s' : WCore.t),
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 id >> /\
    << REX : WCore.reexec X_s X_s' id dtrmt' cmt' >>.
Proof using.
  set (G_s' := {|
    acts_set := id ↑₁ E_t';
    threads_set := threads_set G_s;
    lab := lab_t' ∘ id;
    rf := id ↑ rf_t';
    co := id ↑ co_t';
    rmw := id ↑ rmw_t';
    rmw_dep := rmw_dep_t';
    ctrl := ctrl_t';
    data := data_t';
    addr := addr_t';
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists X_s'. split; red.
  { constructor; vauto.
    { intros e INE TIDE.
      (* TODO : preserves threads? *)
      admit. }
    { admit. (* po-work *) }
    arewrite (WCore.G X_s' = G_s').
    unfold G_s'. simpls.
    rewrite (seq_threads SIMREL).
    apply set_union_more; vauto.
    (* TODO : preserves threads? *)
    admit. }
  unfold WCore.reexec.
  exists thrdle'.
  arewrite (cmt' = cmt_t).
  { unfold cmt'.
    rewrite set_collect_id; vauto. }
  arewrite (dtrmt' = dtrmt_t).
  { unfold dtrmt'.
    rewrite set_collect_id; vauto. }
  constructor; vauto.
  { unfold dtrmt'. destruct STEP.
    rewrite dtrmt_init; vauto. }
  { exact (WCore.dtrmt_cmt STEP). }
  { destruct STEP.
    arewrite (WCore.G X_s' = G_s').
    unfold G_s'. simpls. unfold cmt'.
    basic_solver 8. }
  { constructor.
    { destruct STEP. destruct reexec_sur.
      unfold least_elt. intros trn INIT.
      unfold thrdle'. (* transitive closure? *)
      admit. }
    all : admit. }
  { admit. }
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
    rewrite collect_rel_id, set_collect_id,
        Combinators.compose_id_right.
    apply rexec_rfc. }
  { admit. }
  { apply XmmCons.monoton_cons with (G_t := G_t')
                    (m := id); vauto.
    all : try arewrite (WCore.G X_s' = G_s').
    { admit. (* po-work? *) }
    { admit. (* po-work? *) }
    { admit. (* add *) }
    { admit. (* add? *) }
    destruct STEP; vauto. }
  all : admit.
Admitted.

End SequentReexec.