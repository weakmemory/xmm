Require Import ReordSimrel.
Require Import ReordSimrel.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import SubToFullExec.
Require Import ReorderingFakeSrf.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import Setoid Morphisms Program.Basics.
Require Import xmm_s_hb.

Module ReorderingReexecInternal.

Section ReorderingReexecInternal.

Variable X_t X_t' X_s X_s' : WCore.t.
Variable a_t b_t a_t' b_t' : actid.
Variable mapper : actid -> actid.
Variable f : actid -> actid.
Variable dtrmt cmt : actid -> Prop.

Notation "'R' G" := (fun e => is_true (is_r (lab G) e)) (at level 1).
Notation "'F' G" := (fun e => is_true (is_f (lab G) e)) (at level 1).
Notation "'W' G" := (fun e => is_true (is_w (lab G) e)) (at level 1).
Notation "'Acq' G" := (fun e => is_true (is_acq (lab G) e)) (at level 1).
Notation "'Rlx' G" := (fun e => is_true (is_rlx (lab G) e)) (at level 1).
Notation "'Rel' G" := (fun e => is_true (is_rel (lab G) e)) (at level 1).

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_t''" := (WCore.G X_t').
Notation "'G_s'" := (WCore.G X_s).
Notation "'G_s''" := (WCore.G X_s').

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
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (Rlx G_s).
Notation "'Acq_s'" := (Acq G_s).
Notation "'Rel_s'" := (Rel G_s).

Notation "'lab_s''" := (lab G_s').
Notation "'val_s''" := (val lab_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'same_loc_s''" := (same_loc lab_s').
Notation "'same_val_s''" := (same_val lab_s').
Notation "'E_s''" := (acts_set G_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'sb_s''" := (sb G_s').
Notation "'rf_s''" := (rf G_s').
Notation "'co_s''" := (co G_s').
Notation "'rmw_s''" := (rmw G_s').
Notation "'rpo_s''" := (rpo G_s').
Notation "'rmw_dep_s''" := (rmw_dep G_s').
Notation "'data_s''" := (data G_s').
Notation "'ctrl_s''" := (ctrl G_s').
Notation "'addr_s''" := (addr G_s').
Notation "'W_s''" := (fun x => is_true (is_w lab_s' x)).
Notation "'R_s''" := (fun x => is_true (is_r lab_s' x)).
Notation "'F_s''" := (F G_s').
Notation "'vf_s''" := (vf G_s').
Notation "'srf_s''" := (srf G_s').
Notation "'Loc_s_'' l" := (fun e => loc_s' e = l) (at level 1).
Notation "'Val_s_'' l" := (fun e => val_s' e = l) (at level 1).
Notation "'Rlx_s''" := (Rlx G_s').
Notation "'Acq_s''" := (Acq G_s').
Notation "'Rel_s''" := (Rel G_s').

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

(* Id aliases for better readability *)
Definition a_s := b_t.
Definition b_s := a_t.
Definition a_s' := b_t'.
Definition b_s' := a_t'.
Definition A_s' := extra_a X_t' a_t' b_t' a_s'.

Definition mapper' := upd (upd id a_t' a_s') b_t' b_s'.
Definition G_s'' : execution := {|
  acts_set := mapper' ↑₁ E_t';
  threads_set := threads_set G_t';
  lab := lab_t' ∘ mapper';
  rf := mapper' ↑ rf_t';
  co := mapper' ↑ co_t';
  rmw := mapper' ↑ rmw_t';
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.

Record reexec_conds : Prop := {
  rc_a_dtrmt : dtrmt a_t <-> dtrmt a_t';
  rc_b_dtrmt : dtrmt b_t <-> dtrmt b_t';
  rc_a_eq : dtrmt a_t -> a_t = a_t';
  rc_b_eq : dtrmt b_t -> b_t = b_t';
  rc_pres : b_t = b_t' -> a_t = a_t';
  rc_simrel : reord_simrel X_s X_t a_t b_t mapper;
  rc_step : WCore.reexec X_t X_t' f dtrmt cmt;
  rc_inv_start : reord_step_pred X_t a_t b_t;
  rc_inv_end : reord_step_pred X_t' a_t' b_t';
  rc_l_a_nacq : Rlx_s' a_s';
  rc_vf : forall (IMB : E_t' b_t') (NINA : ~ E_t' a_t'),
            vf_s' ⨾ sb_s' ⨾ ⦗eq a_s'⦘ ≡ vf G_s'' ⨾ sb_s' ⨾ ⦗eq a_s'⦘;
  (**)
  rc_extra_lab : fake_srf G_s'' a_s' (lab_s' a_s') ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s')⦘ ⊆ same_val_s';
  rc_lab : eq_dom E_t' (lab_s' ∘ mapper') lab_t';
  rc_acts : E_s' ≡₁ mapper' ↑₁ E_t' ∪₁ extra_a X_t' a_t' b_t' a_s';
  rc_rf : rf_s' ≡ mapper' ↑ rf_t' ∪ fake_srf G_s'' a_s' (lab_s' a_s') ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s')⦘;
  rc_co : co_s' ≡ mapper' ↑ co_t' ∪
          add_max
            (extra_co_D (mapper' ↑₁ E_t') lab_s (WCore.lab_loc (lab_s' a_s')))
            (A_s' ∩₁ WCore.lab_is_w (lab_s' a_s'));
  rc_rmw : rmw_s ≡ mapper ↑ rmw_t;
  rc_threads : threads_set G_s ≡₁ threads_set G_t;
  rc_ctrl : ctrl_s' ≡ ctrl_s;
  rc_data : data_s' ≡ data_s;
  rc_addr : addr_s' ≡ addr_s;
  rc_rmw_dep : rmw_dep_s' ≡ rmw_dep_s;
}.

Lemma mapinj : inj_dom E_t' mapper'.
Proof using.
  admit.
Admitted.

Lemma intermediate_graph_wf
    (INB : E_t' b_t')
    (NINA : ~ E_t' a_t')
    (CTX : reexec_conds) :
  Wf G_s''.
Proof using.
  admit. (* This graph is very conveniently mapped by m *)
Admitted.

Lemma reexec_simrel
    (CTX : reexec_conds) :
  reord_simrel X_s' X_t' a_t' b_t' mapper'.
Proof using.
  assert (EXAR : eq b_t' ∩₁ R_s' ≡₁ eq b_t' ∩₁ WCore.lab_is_r (lab_s' a_s')).
  { unfold a_s', is_r, WCore.lab_is_r.
    unfolder; split; ins; desf. }
  assert (SRF :
    fake_srf G_s'' a_s' (lab_s' a_s') ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s')⦘ ≡
    srf_s' ⨾ ⦗extra_a X_t' a_t' b_t' b_t' ∩₁ R_s'⦘
  ).
  { unfold A_s', extra_a; desf; [desf | basic_solver 11].
    rewrite EXAR, <- fake_srf_is_srf with (G_s := G_s'').
    all: ins.
    { apply intermediate_graph_wf; auto. }
    { unfold fake_sb, G_s'', sb. ins.
      rewrite (rc_acts CTX), extra_a_some; auto. }
    { unfold G_s'', mapper'. ins. intro FALSO.
      admit. (* Invert the mapper *) }
    { unfold G_s''. ins.
      admit. (* TODO *) }
    { apply CTX; auto. }
    rewrite (rc_co CTX), seq_union_l.
    unfold A_s'. rewrite extra_a_some; auto.
    admit. (* TODO: add_max_eq_r *) }
  constructor; ins.
  { apply mapinj. }
  { unfolder. unfold extra_a; ins; desf.
    constructor; [red; auto | desf].
    rewrite extra_a_some in SRF; auto.
    rewrite <- SRF. apply CTX. }
  { rewrite (rc_acts CTX), set_minus_union_l.
    unfold a_s'. rewrite set_minusK, set_union_empty_r.
    unfold extra_a; desf; [| clear; basic_solver].
    rewrite set_minus_disjoint; auto with hahn.
    admit. (* a_t' is not in *) }
  { admit. (* TODO *) }
  { admit. (* TODO *) }
  { apply CTX. }
  { apply CTX. }
  { admit. }
  { rewrite <- SRF, (rc_rf CTX). auto. }
  { rewrite (rc_co CTX). admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. (* rpo *) }
  { admit. }
  { admit. }
  admit.
Admitted.

End ReorderingReexecInternal.

End ReorderingReexecInternal.

Section ReorderingReexec.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t a_t' b_t' : actid.
Variable mapper : actid -> actid.
Variable f : actid -> actid.
Variable dtrmt cmt : actid -> Prop.
Variable l_a' : label. (* The 'desired' label for phantom a_s *)

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
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (Rlx G_s).
Notation "'Acq_s'" := (Acq G_s).
Notation "'Rel_s'" := (Rel G_s).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

(* Conditions for the re-execution lemma *)
Record reexec_conds : Prop := {
  rc_a_dtrmt : dtrmt a_t <-> dtrmt a_t';
  rc_b_dtrmt : dtrmt b_t <-> dtrmt b_t';
  rc_a_eq : dtrmt a_t -> a_t = a_t';
  rc_b_eq : dtrmt b_t -> b_t = b_t';
  rc_pres : b_t = b_t' -> a_t = a_t';
  rc_simrel : reord_simrel X_s X_t a_t b_t mapper;
  rc_step : WCore.reexec X_t X_t' f dtrmt cmt;
  rc_inv_start : reord_step_pred X_t a_t b_t;
  rc_inv_end : reord_step_pred X_t' a_t' b_t';
  rc_l_a_nacq : mode_le (WCore.lab_mode l_a') Orlx;
}.

Hypothesis CTX : reexec_conds.

(* Id aliases for better readability *)
Definition a_s := b_t.
Definition b_s := a_t.
Definition a_s' := b_t'.
Definition b_s' := a_t'.

Definition extra_b :=
  ifP ~E_t' a_t' /\ E_t' b_t' then ∅
  else eq b_t' ∩₁ E_t'.

Definition mapper' := upd (upd id a_t' a_s') b_t' b_s'.

Lemma mapeq : eq_dom dtrmt mapper mapper'.
Proof using CTX.
  admit.
Admitted.

Definition cmt' := mapper' ↑₁ (cmt ∪₁ extra_b).
Definition dtrmt' := mapper' ↑₁ (dtrmt \₁ extra_b).
Definition f' := mapper' ∘ f ∘ mapper'.
(* Intermediate graph for locating the srf edge for for a_s *)

Definition A_s' := extra_a X_t' a_t' b_t' a_s'.
Definition E_s' := mapper' ↑₁ E_t' ∪₁ A_s'.

Lemma simrel_reexec :
  exists mapper' X_s' f' dtrmt' cmt',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP : WCore.reexec X_s X_s' f' dtrmt' cmt' >>.
Proof using CTX.
Admitted.

End ReorderingReexec.

(* DRAFTS FOR FINAL THEOREM *)

(* Lemma simrel_term
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel G_t G_s a_t b_t mapper)
    (TERM : machine_terminated G_t traces) :
  << TERM' : machine_terminated G_s traces' >> /\
  << SIM' : ReordCommon.reord G_s G_t traces traces' a b >>.
Proof using.
  admit.
Admitted.

Lemma simrel_implies_cons
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel X_s X_t a_t b_t mapper) :
  WCore.is_cons G_s (WCore.sc X_s).
Proof using.
  admit.
Admitted.

*)

(* Lemma sim_rel_step : about any step *)

(*
 forall traces P_src, P_trgt. If target is a reordereing of src, then
 <..> (clarify cuz the theorem statement looks weird)
*)
(* Theorem reordering_rw : TODO.
Proof using.
  admit.
Admitted. *)