Require Import ReordSimrel.
Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
(* Require Import ThreadTrace. *)
Require Import Core.
(* Require Import TraceSwap. *)
Require Import SubToFullExec.
Require Import AuxRel.
Require Import AuxRel2.
Require Import StepOps.
Require Import Srf Rhb SrfProps.
Require Import AuxInj.
(* Require Import Instructions. *)
Require Import Setoid Morphisms.
Require Import SimrelCommon.
Require Import AddEvent.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
(* From imm Require Import SubExecution. *)
From imm Require Import CombRelations.

Section Reexec.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t a_t' b_t' : actid.
Variable mapper : actid -> actid.

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

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t' b_t'.

Definition extra_b :=
  ifP ~E_t' a_t' /\ E_t' b_t' then ∅
  else eq b_t' ∩₁ E_t'.

Lemma simrel_reexec f dtrmt cmt
    (ADTRMT : dtrmt a_t <-> dtrmt a_t')
    (BDTRMT : dtrmt b_t <-> dtrmt b_t')
    (ACMT : dtrmt a_t -> a_t = a_t')
    (BCMT : dtrmt b_t -> b_t = b_t')
    (PRESERVATION : b_t = b_t' -> a_t = a_t')
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.reexec X_t X_t' f dtrmt cmt) :
  exists mapper' X_s' f' dtrmt' cmt',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP : WCore.reexec X_s X_s' f' dtrmt' cmt' >>.
Proof using INV INV'.
  destruct STEP as (thrdle & STEP).
  set (mapper' :=  upd (upd id a_t' b_t') b_t' a_t').
  set (cmt' := mapper' ↑₁ (cmt ∪₁ extra_b)).
  set (dtrmt' := mapper' ↑₁ (dtrmt \₁ extra_b)).
  set (f' := mapper' ∘ f ∘ mapper').
  set (G_s' := {|
    acts_set := mapper' ↑₁ E_t' ∪₁ extra_a X_t' a_t' b_t' b_t';
    threads_set := threads_set G_t';
    lab := lab_t' ∘ mapper';
    rf := mapper' ↑ rf_t' ∪
          srf_s ⨾ ⦗extra_a X_t' a_t' b_t' b_t' ∩₁ R_s⦘;
    co := mapper' ↑ co_t' ∪
          add_max
            (extra_co_D (mapper' ↑₁ E_t') lab_s (loc_s b_t))
            (extra_a X_t' a_t' b_t' b_t' ∩₁ W_s);
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_s;
    ctrl := ctrl_s;
    data := data_s;
    addr := addr_s;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).
  assert (MAPEQ : eq_dom dtrmt mapper mapper').
  { assert (DTRMT : dtrmt ⊆₁ E_t).
    { rewrite (WCore.dtrmt_cmt STEP), WCore.reexec_embd_acts.
      all: eauto using WCore.reexec_embd_corr. }
    unfold mapper'.
    destruct classic with (dtrmt a_t) as [DA|NDA],
             classic with (dtrmt b_t) as [DB|NDB].
    all: unfolder; intros x XIN.
    all: try rewrite <- ACMT by auto.
    all: try rewrite <- BCMT by auto.
    all: rewrite (rsr_mapper SIMREL)
         by (apply DTRMT in XIN; exact XIN).
    { reflexivity. }
    { exfalso. apply NDB. apply (WCore.reexec_dtrmt_sb_closed STEP).
      unfolder. exists a_t, a_t; splits; auto.
      apply DTRMT in DA.
      unfold sb. unfolder. splits; auto; try now apply INV.
      now apply (rsr_at_bt_ord INV). }
    { destruct classic with (x = b_t) as [EQB|NQB].
      { subst x. rewrite !upds. auto. }
      rewrite !updo with (a := b_t) by exact NQB.
      rewrite !updo; try congruence.
      intro FALSO. subst x. now apply NDA, ADTRMT. }
    rewrite !updo; try congruence.
    { intro FALSO. subst x. now apply NDA, ADTRMT. }
    intro FALSO. subst x. now apply NDB, BDTRMT. }
  assert (MAPINJ : inj_dom E_t' mapper').
  { unfold inj_dom, mapper'. intros x y XIN YIN FEQ.
      destruct classic with (x = a_t') as [XEQA|XNQA],
               classic with (x = b_t') as [XEQB|XNQB],
               classic with (y = a_t') as [YEQA|YNQA],
               classic with (y = b_t') as [YEQB|YNQB].
      all: try subst x; try subst y.
      all: try congruence.
      all: try now (exfalso; apply (rsr_at_neq_bt INV'); congruence).
      all: rewrite ?upds in FEQ.
      all: rewrite 1?updo in FEQ; try congruence.
      all: rewrite ?upds in FEQ; try congruence.
      all: unfold id in FEQ.
      all: rewrite 2?updo in FEQ; try congruence.
      all: rewrite ?upds in FEQ; try congruence.
      rewrite updo in FEQ; try congruence. }
  assert (SIMREL' : reord_simrel X_s' X_t' a_t' b_t' mapper').
  { constructor; ins.
    { unfold extra_a; desf. intros x XEQ. subst x.
      constructor; ins.
      admit. }
    { rewrite set_minus_union_l, set_minusK, set_union_empty_r.
      rewrite set_minus_disjoint; [reflexivity |].
      apply set_disjointE. split; [| basic_solver].
      unfold extra_a; desf; [| clear; basic_solver].
      unfold mapper', id. unfolder.
      intros x ((y & YINE & MAP) & XEQ). subst x.
      destruct classic with (y = b_t') as [YEQB | YNQB].
      { subst y. rewrite upds in XEQ. apply (rsr_at_neq_bt INV').
        congruence. }
      rewrite updo in XEQ; [| congruence].
      destruct classic with (y = a_t') as [YEQA | YNQA].
      { subst y. desf. }
      rewrite updo in XEQ; congruence. }
    { unfolder. unfold mapper', id. intros x INIT.
      rewrite !updo; auto.
      all: intro FALSO; subst x.
      { now apply (rsr_at_ninit INV'). }
      now apply (rsr_bt_ninit INV'). }
    { unfold mapper', id, compose. unfolder.
      intros x XIN.
      destruct classic with (x = a_t') as [XEQA|XNQA],
               classic with (x = b_t') as [XEQB|XNQB].
      all: try subst x.
      all: rupd; try now apply INV'.
      all: symmetry; apply INV'. }
    { unfold mapper', id, compose. unfolder.
      intros x _.
      destruct classic with (x = a_t') as [XEQA|XNQA],
               classic with (x = b_t') as [XEQB|XNQB].
      all: try subst x.
      all: try now (exfalso; try now apply (rsr_at_neq_bt INV')).
      { rewrite updo with (c := a_t'); [| apply INV'].
        now rewrite !upds. }
      { rewrite upds, updo with (c := a_t'); [| apply INV'].
        now rewrite upds. }
      rewrite !updo with (c := x); auto. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { unfold mapper', id. clear. unfolder.
      ins. desf. rewrite !updo; congruence. }
    { unfold mapper', id. clear. unfolder.
      ins. desf. now rewrite upds. }
    unfold mapper', id. clear - INV'. unfolder.
    ins. desf. rewrite updo, upds; auto.
    apply INV'. }
  exists mapper', X_s', f', dtrmt', cmt'.
  unfold NW; split; auto.
  red.
  exists thrdle.
  constructor; ins; unfold dtrmt', cmt'.
  { admit. }
  { rewrite (WCore.reexec_embd_dom STEP).
    unfold extra_b, extra_a; desf.
    all: rewrite ?set_union_empty_r.
    { auto with hahn. }
    destruct classic
        with (E_t' b_t')
          as [INB|NINB].
    { rewrite set_union_absorb_r; auto with hahn.
      clear. basic_solver. }
    arewrite (eq b_t' ∩₁ E_t' ≡₁ ∅).
    { clear - NINB. basic_solver. }
    clear. basic_solver. }
  { admit. }
  admit.
Admitted.

Lemma simrel_implies_cons
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel X_s X_t a_t b_t mapper) :
  WCore.is_cons G_s (WCore.sc X_s).
Proof using.
  admit.
Admitted.

End Reexec.

(* DRAFTS FOR FINAL THEOREM *)

(* Lemma simrel_term
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel G_t G_s a_t b_t mapper)
    (TERM : machine_terminated G_t traces) :
  << TERM' : machine_terminated G_s traces' >> /\
  << SIM' : ReordCommon.reord G_s G_t traces traces' a b >>.
Proof using.
  admit.
Admitted. *)

(* Lemma sim_rel_step : about any step *)

(*
 forall traces P_src, P_trgt. If target is a reordereing of src, then
 <..> (clarify cuz the theorem statement looks weird)
*)
(* Theorem reordering_rw : TODO.
Proof using.
  admit.
Admitted. *)