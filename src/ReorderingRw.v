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

Record reord_simrel_rw : Prop :=
{ rsrw_ninit1 : ~is_init a;
  rsrw_ninit2 : ~is_init b;

  rsrw_sb : ext_sb a b;
  rsrw_a_max : forall (INA : E_t a) (NOTINB : ~E_t b), max_elt (sb G_t) a;

  rsrw_lab_u2v : same_lab_u2v lab_s (lab_t ∘ mapper);
  rsrw_lab_v : forall e (NOTA : e <> a), val_s e = (val_t ∘ mapper) e;
  rsrw_actids_t_ord : forall (INB : E_t b) (NOTINA : ~E_t a), False;

  rsrw_sb1 : forall (SAME : E_t a <-> E_t b), immediate sb_s ≡ immediate sb_t;
  rsrw_sb2 : forall (INA : E_t a) (NOTINB : ~E_t b),
                immediate sb_s ≡ immediate sb_t ∪ singl_rel a b;
  rsrw_actids1 : forall (SAME : E_t a <-> E_t b), E_s ≡₁ E_t;
  rsrw_actids2 : forall (INA : E_t a) (NOTINB : ~E_t b),
                 E_s ≡₁ E_t ∪₁ eq b;
  rsrw_rf1 : forall (SAME : E_t a <-> E_t b), rf_s ≡ mapper ↑ rf_t;
  rsrw_rf2 : forall (INA : E_t a) (NOTINB : ~ E_t b),
                    rf_s ≡ mapper ↑ rf_t ∪ mapper ↑ (srf_t ⨾ ⦗eq b⦘);
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
    (SB : ext_sb a b)
    (NEQ : a <> b) :
  reord_simrel_rw (ReordCommon.mapped_G_t G' a b) G' a b.
Proof using.
  constructor; ins.
  all: try now (exfalso; now apply NOTINB, SAME).
  { unfold same_lab_u2v, same_lab_u2v_dom, same_label_u2v.
    ins. desf. }
  apply NOTINA, SAME, INB.
Qed.

(* TODO: constraint on a and b *)
Lemma mapper_simrel_niff G' a b
    (WF : Wf G')
    (IS_R : is_r (lab G') b)
    (ANIT : ~is_init a)
    (BNIT : ~is_init b)
    (INA : acts_set G' a)
    (NOTINB : ~acts_set G' b)
    (NEQ : a <> b)
    (MAX : max_elt (sb G') a)
    (SB : ext_sb a b) :
  reord_simrel_rw (ReordCommon.mapped_G_t_with_b G' a b) G' a b.
Proof using.
  constructor; ins.
  all: try now (exfalso; apply NOTINB, SAME, INA).
  { unfold same_lab_u2v, same_lab_u2v_dom, same_label_u2v.
    ins. desf. }
  apply ReordCommon.mapped_G_t_imm_sb; ins.
Qed.

Section Basic.

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

Lemma sim_rel_init
    (ANIT : ~is_init a)
    (BNIT : ~is_init b)
    (INIT : acts_set G_s ∩₁ is_init ≡₁ acts_set G_t ∩₁ is_init)
    (LABU2V : same_lab_u2v lab_s (lab_t ∘ mapper))
    (LABV : forall e (NOTA : e <> a), val_s e = (val_t ∘ mapper) e)
    (SB : ext_sb a b) :
  reord_simrel_rw (WCore.init_exec G_s) (WCore.init_exec G_t) a b.
Proof using.
  constructor; ins.
  all: try now (exfalso; apply ANIT, INA).
  all: try rewrite collect_rel_empty; ins.
  { apply BNIT, INB. }
  apply immediate_more. unfold sb; ins.
  now rewrite INIT.
Qed.

End Basic.

Section ExecutionSteps.

Variable G_t G_t' G_s : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
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
Notation "'R_t'" := (is_r lab_t).

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

Record reord_context : Prop := {
  rctx_aninit : ~is_init a;
  rctx_bninit : ~is_init b;
  rctx_diff : a <> b;
  rctx_sb : ext_sb a b;
  rctx_is_r : R_t b;
  rctx_amax : forall (INA : E_t a) (NOTINB : ~E_t b), max_elt (sb G_t) a;
}.

Hypothesis SWAPPED_TRACES : ReordCommon.traces_swapped traces traces' a b.
Hypothesis CTX : reord_context.

Lemma simrel_exec_not_a_not_b_same_helper e
    (SAME : E_t a <-> E_t b)
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' traces e) :
  exists G_s',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP' : WCore.exec_inst G_s G_s' traces' e >>.
Proof using SWAPPED_TRACES CTX.
  assert (IFF : acts_set G_t' a <-> acts_set G_t' b).
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins.
    split; intro HIN; apply e_new in HIN; apply e_new; left.
    all: unfolder in HIN; desf; eauto. }
  exists (ReordCommon.mapped_G_t G_t' a b).
  split.
  { apply mapper_simrel_iff; ins; apply CTX. }
  admit.
Admitted.

Lemma simrel_exec_not_a_not_b e
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' traces e) :
  exists G_s',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP' : WCore.exec_inst G_s G_s' traces' e >>.
Proof using SWAPPED_TRACES CTX.
  tertium_non_datur (E_t a) as [INA|INA].
  all: tertium_non_datur (E_t b) as [INB|INB].
  all: try now (exfalso; eapply rsrw_actids_t_ord; eauto).
  all: try now (apply simrel_exec_not_a_not_b_same_helper; ins).
  exists (ReordCommon.mapped_G_t_with_b G_t' a b).
  split.
  { apply mapper_simrel_niff; ins; try apply CTX.
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. apply wf_new_conf. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct start_wf, pfx. ins.
      rewrite <- pfx_sub.(sub_lab). apply CTX. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. apply e_new. now left. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. intro F; apply INB.
      apply e_new in F; unfolder in F; desf. }
    admit. (* Helper: sb is max *) }
  admit.
Admitted.

Lemma simrel_exec_b
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' traces a) :
  exists G_s',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    exists G_s'_int,
      << STEP1 : WCore.exec_inst G_s G_s'_int traces' a >> /\
      << STEP2 : WCore.exec_inst G_s'_int G_s' traces' b >>.
Proof using SWAPPED_TRACES CTX.
  exists (ReordCommon.mapped_G_t_with_b G_t' a b); split.
  { apply mapper_simrel_niff; ins; try apply CTX.
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. apply wf_new_conf. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct start_wf, pfx. ins.
      rewrite <- pfx_sub.(sub_lab). apply CTX. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins. apply e_new. now right. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. intro F; apply e_new in F.
      unfolder in F; desf; [| now apply CTX.(rctx_diff)].
      now apply SIM.(rsrw_actids_t_ord G_s G_t a b). }
    change G_t' with (WCore.G (WCore.Build_t G_t' G_t' ∅)).
    eapply WCore.new_event_max_sb; eapply STEP. }
  admit. (* TODO: research *)
Admitted.

Lemma simrel_exec_a w
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (RF : G_t.(rf) w a)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' traces b) :
  exists G_s' rfre,
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.reexec G_s G_s' traces' rfre >>.
Proof using SWAPPED_TRACES.
  (* TODO: check article *)
  admit.
Admitted.

Lemma simrel_reexec rfre
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.reexec G_t G_t' traces rfre) :
  exists G_s' rfre,
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.reexec G_s G_s' traces' (mapper ↓ rfre) >>.
Proof using SWAPPED_TRACES.
  tertium_non_datur (E_t a) as [INA|INA].
  all: tertium_non_datur (E_t b) as [INB|INB].
  all: try now (exfalso; eapply rsrw_actids_t_ord; eauto).
  (* TODO adapt. *)
  (* all: try now (apply simrel_exec_not_a_not_b_same_helper; ins).
  exists (ReordCommon.mapped_G_t_with_b G_t' a b).
  split; [| apply mapper_simrel_niff; ins].
  all: try apply CTX.
  { admit. } (* TODO *)
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins. apply wf_new_conf. }
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    admit. } (* TODO ensure <G_t, G_t', cmt> is wf *)
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins. apply e_new. now left. }
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins. intro F; apply INB.
    apply e_new in F; unfolder in F; desf. } *)
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