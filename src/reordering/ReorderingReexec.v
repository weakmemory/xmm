Require Import ReordSimrel ReorderingEq ReorderingMapper.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2 AuxRel3.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import SubToFullExec.
Require Import ReorderingFakeSrf.
Require Import Thrdle.
Require Import StepOps.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import Setoid Morphisms Program.Basics.
Require Import xmm_s_hb.

Set Implicit Arguments.

(*
NOTE: we assume that a and b do NOT change their
indices between re-executions. This simplfication
makes the formalisation somewhat more conservative.
*)

Module ReorderingReexecInternal.

Section ReorderingReexecInternal.

Variable X_t X_t' X_s X_s' : WCore.t.
Variable a_t b_t : actid.
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
Notation "'hb_t'" := (hb G_t).
Notation "'rhb_t'" := (rhb G_t).
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
Notation "'hb_t''" := (hb G_t').
Notation "'rhb_t''" := (rhb G_t').
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
Notation "'hb_s'" := (hb G_s).
Notation "'rhb_s'" := (rhb G_s).
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
Notation "'hb_s''" := (hb G_s').
Notation "'rhb_s''" := (rhb G_s').
Notation "'eco_s''" := (eco G_s').
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

Notation "'mapper'" := (mapper a_t b_t).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'A_s'" := (extra_a X_t a_t b_t b_t).
Notation "'A_s''" := (extra_a X_t' a_t b_t b_t).

(* Id aliases for better readability *)
Definition a_s := b_t.
Definition b_s := a_t.

Definition mapper_inv := mapper.

Definition G_s'' : execution := {|
  acts_set := mapper ↑₁ E_t';
  threads_set := threads_set G_t';
  lab := lab_t' ∘ mapper;
  rf := mapper ↑ rf_t';
  co := mapper ↑ co_t';
  rmw := mapper ↑ rmw_t';
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.

Record reexec_conds : Prop := {
  rc_simrel : reord_simrel X_s X_t a_t b_t mapper;
  rc_step : WCore.reexec X_t X_t' f dtrmt cmt;
  rc_inv_start : reord_step_pred X_t a_t b_t;
  rc_inv_end : reord_step_pred X_t' a_t b_t;
  rc_l_a_nacq : Rlx_s' a_s;
  rc_end_cons : WCore.is_cons G_t' ∅₂;
  rc_new_cons : WCore.is_cons G_s' ∅₂;
  rc_vf : forall (IMB : E_t' b_t) (NINA : ~ E_t' a_t),
            vf_s' ⨾ sb_s' ⨾ ⦗eq a_s⦘ ≡ vf G_s'' ⨾ sb_s' ⨾ ⦗eq a_s⦘;
  (**)
  rc_extra_lab : fake_srf G_s'' a_s (lab_s' a_s) ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s)⦘ ⊆ same_val_s';
  rc_lab : eq_dom E_t' (lab_s' ∘ mapper) lab_t';
  rc_acts : E_s' ≡₁ mapper ↑₁ E_t' ∪₁ extra_a X_t' a_t b_t a_s;
  rc_rf : rf_s' ≡ mapper ↑ rf_t' ∪ fake_srf G_s'' a_s (lab_s' a_s) ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s)⦘;
  rc_co : co_s' ≡ mapper ↑ co_t' ∪
          add_max
            (extra_co_D (mapper ↑₁ E_t') lab_s' (WCore.lab_loc (lab_s' a_s)))
            (A_s' ∩₁ WCore.lab_is_w (lab_s' a_s));
  rc_rmw : rmw_s' ≡ mapper ↑ rmw_t';
  rc_threads : threads_set G_s' ≡₁ threads_set G_t';
  rc_ctrl : ctrl_s' ≡ ctrl_t';
  rc_data : data_s' ≡ data_t';
  rc_addr : addr_s' ≡ addr_t';
  rc_rmw_dep : rmw_dep_s' ≡ rmw_dep_t';
  rc_f_b_t : forall (ACMT : cmt b_t), f b_t = b_t;
  rc_f_a_t : forall (ACMT : cmt a_t), f a_t = a_t;
}.

Lemma mapinj
    (NEQ : a_t <> b_t) :
  inj_dom E_t' mapper.
Proof using.
  eapply inj_dom_mori; eauto with xmm.
  red; auto with hahn.
Qed.

Lemma mapinj_inv'
    (NEQ : a_t <> b_t) :
  inj_dom ⊤₁ mapper_inv.
Proof using.
  unfold mapper_inv. auto with xmm.
Qed.

Lemma mapinj_inv
    (NEQ : a_t <> b_t) :
  inj_dom E_t' mapper_inv.
Proof using.
  eapply inj_dom_mori; eauto using mapinj_inv'.
  red. auto with hahn.
Qed.

Lemma mapper_inv_l_inv
    (NEQ : a_t <> b_t) :
  mapper ∘ mapper_inv = id.
Proof using.
  unfold mapper_inv. now apply rsr_mapper_compose.
Qed.

Lemma mapper_inv_r_inv
    (NEQ : a_t <> b_t) :
  mapper_inv ∘ mapper = id.
Proof using.
  unfold mapper_inv. now apply rsr_mapper_compose.
Qed.

Lemma intermediate_graph_wf
    (INB : E_t' b_t)
    (NINA : ~ E_t' a_t)
    (CTX : reexec_conds) :
  Wf G_s''.
Proof using.
  admit. (* This graph is very conveniently mapped by m *)
Admitted.

Lemma reexec_simrel
    (CTX : reexec_conds) :
  reord_simrel X_s' X_t' a_t b_t mapper.
Proof using.
  assert (EQ : a_t <> b_t) by apply CTX.
  assert (TEQ : tid a_t = tid b_t) by apply CTX.
  assert (EXAR : eq b_t ∩₁ R_s' ≡₁ eq b_t ∩₁ WCore.lab_is_r (lab_s' a_s)).
  { unfold a_s, is_r, WCore.lab_is_r.
    unfolder; split; ins; desf. }
  assert (SRF :
    fake_srf G_s'' a_s (lab_s' a_s) ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s)⦘ ≡
    srf_s' ⨾ ⦗extra_a X_t' a_t b_t b_t ∩₁ R_s'⦘
  ).
  { unfold extra_a; desf; [desf | basic_solver 11].
    rewrite EXAR, <- fake_srf_is_srf with (G_s := G_s'').
    all: ins.
    { apply intermediate_graph_wf; auto. }
    { unfold fake_sb, G_s'', sb. ins.
      rewrite (rc_acts CTX), extra_a_some; auto. }
    { unfold G_s''.
      intros (x & XIN & XEQ). enough (x = a_t); desf.
      eapply rsr_mapper_inv_bt; eauto. }
    { unfold G_s''. ins.
      admit. (* TODO: weaken cond*) }
    { apply CTX; auto. }
    rewrite (rc_co CTX), seq_union_l.
    rewrite extra_a_some; auto.
    rewrite add_max_seq_r, set_interC, set_interA.
    arewrite (eq a_s ∩₁ mapper ↑₁ E_t' ≡₁ ∅).
    { split; [| basic_solver]. unfold a_s.
      intros x (XEQ & y & YIN & YEQ). enough (y = a_t); desf.
      eapply rsr_mapper_inv_bt; eauto. }
    rewrite set_inter_empty_r, add_max_empty_r.
    now rewrite union_false_r. }
  constructor; ins.
  all: try now apply CTX.
  { apply mapinj. apply CTX. }
  { unfolder. unfold extra_a; ins; desf.
    constructor; [red; auto | desf | |].
    { rewrite extra_a_some in SRF; auto.
      rewrite <- SRF, <- (rc_extra_lab CTX).
      rewrite extra_a_some; auto with hahn. }
    { admit. (* TODO: add loc property to CTX *) }
    admit. (* TODO: update the nacq prop in CTX *) }
  { rewrite (rc_acts CTX), set_minus_union_l.
    unfold a_s. rewrite set_minusK, set_union_empty_r.
    unfold extra_a; desf; [| clear; basic_solver].
    rewrite set_minus_disjoint; auto with hahn.
    unfolder. intros x (y & YIN & YEQ) XEQ. desf.
    enough (y = a_t); desf. eapply rsr_mapper_inv_bt; eauto. }
  { eapply eq_dom_mori; eauto with xmm.
    red. auto with hahn. }
  { admit. }
  { rewrite <- SRF, (rc_rf CTX). auto. }
  { rewrite (rc_co CTX), (rc_acts CTX).
    apply union_more; auto.
    arewrite (WCore.lab_loc (lab_s' a_s) = loc_s' b_t).
    arewrite (A_s' ∩₁ W_s' ≡₁
              A_s' ∩₁ WCore.lab_is_w (lab_s' a_s)).
    { unfold extra_a, a_s. desf; [| basic_solver].
      clear. unfold is_w, WCore.lab_is_w.
      unfolder. split; ins; desf. }
    destruct classic
        with (WCore.lab_is_w (lab_s' a_s) ≡₁ ∅)
          as [EMP | NEMP].
    { rewrite EMP, set_inter_empty_r.
      now rewrite !add_max_empty_r. }
    arewrite (WCore.lab_is_w (lab_s' a_s) ≡₁ ⊤₁).
    { unfold WCore.lab_is_w in *. desf. }
    rewrite set_inter_full_r,
            add_max_a with (A := extra_co_D (mapper ↑₁ E_t') lab_s' (loc_s' b_t)),
            add_max_a with (A := extra_co_D (mapper ↑₁ E_t' ∪₁ A_s') lab_s' (loc_s' b_t)).
    rewrite !extra_co_D_minus, set_minus_union_l.
    now rewrite set_minusK, set_union_empty_r. }
  { admit. (* rpo *) }
  { clear. unfold mapper. unfolder.
    ins. desf. now rewrite !updo by auto. }
  { clear. unfold mapper. unfolder.
    ins. desf. now rewrite upds. }
  clear - CTX. unfold mapper. unfolder.
  ins. desf. rewrite updo, upds; [done |].
  apply CTX.
Admitted.

Definition extra_b :=
  ifP E_t' a_t /\ ~dtrmt a_t /\ dtrmt b_t then eq b_t
  else ∅.
Definition extra_d :=
  ifP
    ~cmt b_t /\
    cmt a_t /\
    ~dtrmt a_t /\
    dom_rel (immediate sb_t' ⨾ ⦗eq b_t⦘) ⊆₁ dtrmt
  then eq a_s
  else ∅.
Definition cmt' := mapper ↑₁ cmt.
Definition dtrmt' := mapper ↑₁ (dtrmt \₁ extra_b) ∪₁ extra_d.
Definition f' := (mapper ∘ f) ∘ mapper_inv.

Lemma extra_d_in_E_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  extra_d ⊆₁ E_s.
Proof using.
  unfold extra_d. desf.
  transitivity (mapper ↑₁ E_t);
    [| rewrite (rsr_acts (rc_simrel CTX)); basic_solver].
  rewrite <- (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
  arewrite (
    eq a_s ≡₁ mapper ↑₁ (f ↑₁ eq a_t)
  ).
  { admit. }
  do 2 (apply set_collect_mori; auto).
  basic_solver.
Admitted.

Lemma dtrmt_in_E_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  dtrmt' ⊆₁ E_s.
Proof using.
  unfold dtrmt'.
  arewrite (dtrmt \₁ extra_b ⊆₁ dtrmt).
  { basic_solver. }
  rewrite extra_d_in_E_s, (rexec_dtrmt_in_start GREEXEC); eauto.
  apply set_subset_union_l; split; [| reflexivity].
  rewrite (rsr_acts (rc_simrel CTX)); auto with hahn.
Qed.

Lemma reexec_threads_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  WCore.reexec_thread X_s' dtrmt' ≡₁
    WCore.reexec_thread X_t' dtrmt ∪₁ tid ↑₁ A_s'.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  assert (TEQ : tid a_t = tid b_t) by apply CTX.
  unfold WCore.reexec_thread, dtrmt'.
  rewrite (rsr_acts (reexec_simrel CTX)).
  rewrite set_minus_union_l, set_collect_union.
  arewrite (
    A_s' \₁ (mapper ↑₁ (dtrmt \₁ extra_b) ∪₁ extra_d) ≡₁ A_s'
  ).
  { unfold extra_a; desf; [| basic_solver].
    split; [clear; basic_solver |].
    unfolder. intros x XEQ. subst. split; auto.
    unfold extra_b, extra_d; intro FALSO; do 2 desf.
    all: enough (E_t' a_t) by eauto.
    all: try now apply (WCore.reexec_embd_dom GREEXEC).
    eapply rexec_dtrmt_in_fin; eauto.
    erewrite <- rsr_mapper_inv_bt; eauto. }
  apply set_union_more; [| reflexivity].
  unfold extra_d; desf.
  { assert (INA : E_t' a_t).
    { apply (WCore.reexec_embd_dom GREEXEC). desf. }
    assert (INB : E_t' b_t).
    { now apply (rsr_at_bt_ord (rc_inv_end CTX)). }
    rewrite rsr_setE_iff; eauto.
    assert (ND : ~dtrmt b_t).
    { intro FALSO. enough (cmt b_t) by desf.
      now apply (WCore.dtrmt_cmt GREEXEC). }
    unfold extra_b; desf; [exfalso; tauto |].
    arewrite (dtrmt \₁ ∅ ≡₁ dtrmt) by basic_solver.
    rewrite rsr_setE_iff; eauto.
    unfold a_s. apply tid_map_replace.
    { clear. basic_solver 11. }
    rewrite set_minus_union_r.
    unfolder. intros x (XIN & NDX).
    exists (ifP x = b_t then a_t else x).
    desf; auto. }
  rewrite set_union_empty_r.
  unfold extra_b; desf.
  { assert (INB : E_t' b_t).
    { now apply (rsr_at_bt_ord (rc_inv_end CTX)). }
    rewrite rsr_setE_iff; desf; eauto.
    rewrite rsr_setE_iff; eauto;
      [| desf; unfolder; tauto].
    rewrite set_minus_minus_r, set_collect_union.
    split; [| auto with hahn].
    apply set_subset_union_l; split; auto.
    transitivity (eq (tid a_t)); basic_solver. }
  arewrite (dtrmt \₁ ∅ ≡₁ dtrmt) by basic_solver.
  rewrite <- set_collect_minus;
    [| eapply inj_dom_mori; eauto with xmm; red; auto with hahn].
  rewrite <- set_collect_compose.
  rewrite set_collect_eq_dom with (g := tid); [reflexivity |].
  eapply eq_dom_mori; eauto with xmm.
  red; auto with hahn.
Qed.

Lemma reexec_thread_mapper thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  mapper ↑₁ (tid ↓₁ WCore.reexec_thread X_t' dtrmt) ≡₁
    tid ↓₁ WCore.reexec_thread X_t' dtrmt.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  assert (TID : tid a_t = tid b_t) by apply CTX.
  eapply rsr_setE_iff; eauto.
  destruct classic
      with ((tid ↓₁ WCore.reexec_thread X_t' dtrmt) a_t)
        as [INA|NINA].
  all: unfolder; rewrite <- TID; auto.
Qed.

Lemma reexec_acts_s_helper thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  A_s ⊆₁ tid ↓₁ WCore.reexec_thread X_t' dtrmt ∪₁
            tid ↓₁ (tid ↑₁ A_s').
Proof using.
  assert (TEQ : tid a_t = tid b_t) by apply CTX.
  unfold extra_a at 1; desf.
  assert (NDA : ~ dtrmt a_t).
  { intro FALSO. enough (E_t a_t) by desf.
    eapply rexec_dtrmt_in_start; eauto. }
  destruct classic with (dtrmt b_t) as [DB|NDB].
  { unfold extra_a; desf; [basic_solver |].
    assert (INB : E_t' b_t).
    { eapply rexec_dtrmt_in_fin; eauto. }
    assert (INA : E_t' a_t) by tauto.
    apply set_subset_union_r. left.
    unfold WCore.reexec_thread. basic_solver. }
  assert (INB : E_t b_t) by desf.
  apply (WCore.rexec_acts GREEXEC) in INB.
  destruct INB as [DB | [_ OK]]; basic_solver.
Qed.

Lemma reexec_acts_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  E_s ≡₁ dtrmt' ∪₁ E_s ∩₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt'.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  assert (TID : tid a_t = tid b_t) by apply CTX.
  enough (SUB : E_s \₁ dtrmt' ⊆₁ tid ↓₁ WCore.reexec_thread X_s' dtrmt').
  { split; [|
      rewrite (dtrmt_in_E_s GREEXEC CTX) at 1;
        basic_solver].
    rewrite set_union_minus
       with (s := E_s) (s' := dtrmt')
         at 1
         by eauto using dtrmt_in_E_s.
    rewrite <- SUB. basic_solver. }
  arewrite (E_s \₁ dtrmt' ⊆₁ E_s \₁ mapper ↑₁ (dtrmt \₁ extra_b)).
  { unfold dtrmt'. basic_solver. }
  rewrite reexec_threads_s; eauto.
  rewrite (rsr_acts (rc_simrel CTX)), set_minus_union_l.
  rewrite set_map_union.
  arewrite (
    A_s \₁ (mapper ↑₁ (dtrmt \₁ extra_b)) ≡₁ A_s
  ).
  { unfold extra_a; desf; [| basic_solver].
    split; [clear; basic_solver |].
    unfolder. intros x XEQ. subst. split; auto.
    unfold extra_b; intro FALSO; do 2 desf.
    all: enough (E_t a_t) by eauto.
    all: eapply rexec_dtrmt_in_start; eauto.
    { erewrite <- (rsr_mapper_inv_bt y NEQ); eauto. }
    erewrite <- rsr_mapper_inv_bt; eauto. }
  apply set_subset_union_l.
  split; eauto using reexec_acts_s_helper.
  apply set_subset_union_r; left.
  rewrite <- set_collect_minus;
    [| eapply inj_dom_mori; eauto with xmm; red; auto with hahn].
  rewrite <- reexec_thread_mapper; eauto.
  apply set_collect_mori; auto.
  rewrite set_minus_minus_r.
  apply set_subset_union_l. split.
  { rewrite (WCore.rexec_acts GREEXEC). basic_solver. }
  unfold extra_b. desf; [| basic_solver].
  unfolder. ins. desf.
  rewrite <- TID. unfold WCore.reexec_thread.
  basic_solver.
Qed.

Lemma reexec_extra_a_ncmt thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  extra_a X_t' a_t b_t b_t ⊆₁ set_compl cmt'.
Proof using.
  assert (NEQ : a_t <> b_t) by apply CTX.
  unfold extra_a, cmt'. desf.
  unfolder. ins. desf.
  intros (y & CMT & MAP).
  assert (YIN : E_t' y).
  { now apply (WCore.reexec_embd_dom GREEXEC). }
  enough (E_t' a_t) by desf.
  erewrite <- (rsr_mapper_inv_bt _ NEQ); eauto.
Qed.

Lemma dtrmt_in_cmt thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  dtrmt' ⊆₁ cmt'.
Proof using.
  unfold dtrmt', cmt'.
  (* unfold extra_b, extra_cmt. desf.
  { exfalso.
    enough (E_t' a_t') by desf.
    apply (WCore.reexec_embd_dom GREEXEC).
    desf. }
  { rewrite set_union_empty_r.
    apply set_collect_mori; auto.
    rewrite <- (WCore.dtrmt_cmt GREEXEC).
    clear. basic_solver. }
  { rewrite set_minus_disjoint; [| clear; basic_solver].
    assert (IN : E_t' a_t' \/ ~E_t' b_t') by tauto.
    assert (BND : ~dtrmt b_t').
    { intro FALSO. enough (cmt b_t') by desf.
      now apply (WCore.dtrmt_cmt GREEXEC). }
    rewrite (rsr_setE_iff (rc_inv_end CTX) (reexec_simrel CTX));
            [| eapply rexec_dtrmt_in_fin; eauto | right; desf].
    rewrite (rsr_setE_ex (rc_inv_end CTX) (reexec_simrel CTX));
            [| apply (WCore.reexec_embd_dom GREEXEC) | desf].
    rewrite <- (WCore.dtrmt_cmt GREEXEC), set_minus_disjoint.
    all: basic_solver. }
  rewrite set_minus_disjoint, set_union_empty_r
    ; [| clear; basic_solver].
  apply set_collect_mori; auto.
  exact (WCore.dtrmt_cmt GREEXEC). *)
Admitted.

Lemma imm_sb_d_s thrdle
    (GREEXEC : WCore.reexec_gen X_t X_t' f dtrmt cmt thrdle)
    (CTX : reexec_conds) :
  ⦗dtrmt'⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗cmt'⦘ ⊆
    ⦗dtrmt'⦘ ⨾ immediate (nin_sb G_s') ⨾ ⦗dtrmt'⦘.
Proof using.
  rewrite rsr_sbE_imm
     with (X_s := X_s') (X_t := X_t') (a_t := a_t) (b_t := b_t).
  all: eauto using rc_inv_end, reexec_simrel.
  rewrite !seq_union_l, !seq_union_r.
  rewrite extra_sbE; eauto using rc_inv_end, reexec_simrel.
  seq_rewrite <- cross_inter_l.
  arewrite (dtrmt' ∩₁ extra_a X_t' a_t b_t b_t ≡₁ ∅).
  { split; [| auto with hahn].
    rewrite reexec_extra_a_ncmt, dtrmt_in_cmt; eauto.
    clear. basic_solver. }
  apply union_mori; [| basic_solver].
Admitted.

Lemma reexec_step
    (CTX : reexec_conds) :
  WCore.reexec X_s X_s' f' dtrmt' cmt'.
Proof using.
  assert (NEQ : a_t <> b_t).
  { apply CTX. }
  assert (GREEXEC :
    WCore.reexec X_t X_t' f dtrmt cmt
  ).
  { apply (rc_step CTX). }
  red in GREEXEC. destruct GREEXEC as (thrdle & GREEXEC).
  assert (MEQA : mapper a_t = b_t).
  { unfold mapper.
    rewrite updo, upds; [done |].
    apply CTX. }
  assert (INJHELPER : inj_dom (codom_rel (⦗E_t' \₁ dtrmt⦘ ⨾ rf_t') ∪₁ dom_rel rhb_t'^?) mapper).
  { eapply inj_dom_mori; eauto with xmm.
    red. auto with hahn. }
  assert (EXNCMT : extra_a X_t' a_t b_t b_t ∩₁ cmt' ≡₁ ∅).
  { split; vauto.
    rewrite (reexec_extra_a_ncmt GREEXEC CTX).
    clear. basic_solver. }
  assert (SURG :
    WCore.stable_uncmt_reads_gen X_s' cmt' thrdle
  ).
  { constructor; try now apply GREEXEC.
    admit. }
  assert (WF_START :
    WCore.wf (WCore.X_start X_s dtrmt') X_s' cmt'
  ).
  { admit. (* TODO *) }
  (**)
  red. exists thrdle.
  constructor.
  { eapply dtrmt_in_cmt; eauto. }
  { admit. }
  (* { unfold f', dtrmt'.
    assert (EQDOM : eq_dom (dtrmt \₁ extra_b) mapper mapper).
    { arewrite (dtrmt \₁ extra_b ⊆₁ dtrmt) by basic_solver.
      unfolder. ins. symmetry. now apply mapd. }
    rewrite set_collect_eq_dom with (g := mapper); auto.
    rewrite Combinators.compose_assoc.
    apply fixset_swap.
    apply fixset_eq_dom
      with (g := f ∘ mapper_inv ∘ mapper).
    { admit. }
    eapply fixset_mori; try now apply GREEXEC.
    { red. clear. basic_solver. }
    now rewrite Combinators.compose_assoc,
                mapper_inv_r_inv,
                Combinators.compose_id_right. } *)
  { unfold cmt'.
    rewrite (rc_acts CTX), (WCore.reexec_embd_dom GREEXEC).
    auto with hahn. }
  { exact SURG. }
  { admit. (* sb-clos *) }
  { eapply imm_sb_d_s; eauto. }
  { admit. (* rpo edges *) }
  { constructor.
    { intros x' y'; unfold cmt', f'.
      intros [x [Hx]] [y [Hy]]; subst x' y'.
      unfold compose.
      change (mapper_inv (mapper x)) with ((mapper_inv ∘ mapper) x).
      change (mapper_inv (mapper y)) with ((mapper_inv ∘ mapper) y).
      rewrite !mapper_inv_r_inv; auto; unfold id; intro EQf.
      enough (EQxy: x = y); [by rewrite EQxy|].
      apply (WCore.reexec_embd_inj (WCore.reexec_embd_corr GREEXEC)); auto.
      apply (rsr_inj (rc_simrel CTX)).
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      done. }
    { intros e CMT.
      change (tid (f' e)) with ((tid ∘ f') e).
      unfold f'.
      rewrite <- !Combinators.compose_assoc.
      change ((tid ∘ mapper ∘ f ∘ mapper_inv) e)
        with ((tid ∘ mapper) ((f ∘ mapper_inv) e)).
      unfold cmt' in CMT. unfolder in CMT.
      destruct CMT as (e' & CMT & EQ); subst e.
      assert (INE : E_t ((f ∘ mapper_inv) (mapper e'))).
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
        unfolder. exists e'. split; auto.
        change ((f ∘ mapper_inv) (mapper e'))
          with (f ((mapper_inv ∘ mapper) e')).
        rewrite mapper_inv_r_inv; [now unfold id | apply CTX]. }
      rewrite (rsr_tid (rc_simrel CTX)); auto.
      unfold compose.
      rewrite (WCore.reexec_embd_tid (WCore.reexec_embd_corr GREEXEC));
        [| change (mapper_inv (mapper e')) with ((mapper_inv ∘ mapper) e');
           rewrite mapper_inv_r_inv; [now unfold id | apply CTX]].
      change (mapper_inv (mapper e'))
        with ((mapper_inv ∘ mapper) e').
      rewrite mapper_inv_r_inv by apply CTX.
      unfold id.
      apply rsr_tid' with (X_s := X_s') (X_t := X_t')
                          (a_t := a_t) (b_t := b_t).
      { now apply reexec_simrel. }
      now apply (WCore.reexec_embd_dom GREEXEC). }
    { intros e CMT.
      change (lab_s (f' e)) with ((lab_s ∘ f') e).
      unfold f'.
      rewrite <- !Combinators.compose_assoc.
      unfold cmt' in CMT. unfolder in CMT.
      destruct CMT as (e' & CMT & EQ); subst e.
      change ((lab_s ∘ mapper ∘ f ∘ mapper_inv) (mapper e'))
        with ((lab_s ∘ mapper) ((f ∘ (mapper_inv ∘ mapper)) e')).
      change (lab_s' (mapper e')) with ((lab_s' ∘ mapper) e').
      rewrite mapper_inv_r_inv by apply CTX.
      arewrite (f ∘ id = f) by done.
      rewrite (rsr_lab (rc_simrel CTX));
        [| apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver].
      rewrite (rsr_lab (reexec_simrel CTX));
        [| apply (WCore.reexec_embd_dom GREEXEC); auto].
      now apply GREEXEC. }
    { admit. }
    { rewrite (rsr_rf (reexec_simrel CTX)),
              restr_union, collect_rel_union.
      arewrite_false (restr_rel cmt'
        (srf_s' ⨾ ⦗extra_a X_t' a_t b_t b_t ∩₁ R_s'⦘)).
      { rewrite restr_relE, !seqA, <- id_inter.
        rewrite (reexec_extra_a_ncmt GREEXEC CTX).
        clear. basic_solver. }
      rewrite collect_rel_empty, union_false_r.
      unfold cmt', f'.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto with xmm;
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f ∘ id = f) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_rf (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_rf (rc_simrel CTX)); auto with hahn. }
    { rewrite (rsr_co (reexec_simrel CTX)),
              restr_union, collect_rel_union.
      arewrite_false (restr_rel cmt'
        (add_max (extra_co_D E_s' lab_s' (loc_s' b_t))
          (extra_a X_t' a_t b_t b_t ∩₁ W_s'))).
      { rewrite restr_add_max. unfold add_max.
        rewrite (reexec_extra_a_ncmt GREEXEC CTX) at 2.
        clear. basic_solver. }
      rewrite collect_rel_empty, union_false_r.
      unfold cmt', f'.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto with xmm;
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f ∘ id = f) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_co (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_co (rc_simrel CTX)); auto with hahn. }
    { rewrite (rsr_rmw (reexec_simrel CTX)).
      unfold cmt', f'.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto with xmm;
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f ∘ id = f) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_rmw (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_rmw (rc_simrel CTX)); auto with hahn. }
    unfold cmt', f'.
    rewrite <- !set_collect_compose.
    rewrite Combinators.compose_assoc.
    rewrite mapper_inv_r_inv; auto.
    rewrite Combinators.compose_assoc.
    arewrite (f ∘ id = f) by done.
    rewrite set_collect_compose.
    rewrite (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
    rewrite (rsr_acts (rc_simrel CTX)); auto with hahn. }
  { exact WF_START. (* wf start *) }
  { admit. (* Consistency *) }
  { eapply reexec_acts_s; eauto. }
  apply sub_to_full_exec_listless
   with (thrdle := thrdle).
  { exact WF_START. }
  { eapply G_s_rfc with (X_t := X_t').
    { apply CTX. }
    now apply reexec_simrel. }
  { apply CTX. }
  { admit. (* difference between acts and dtrmt is fin *) }
  { admit. (* Prefix. Trivial? *) }
  { eapply G_s_wf with (X_t := X_t').
    { apply CTX. }
    now apply reexec_simrel. }
  { admit. (* init acts *) }
  { admit. (* Unprovable SC *) }
  { now rewrite (rc_data CTX), (rsr_ndata (rc_inv_end CTX)). }
  { now rewrite (rc_addr CTX), (rsr_naddr (rc_inv_end CTX)). }
  { now rewrite (rc_ctrl CTX), (rsr_nctrl (rc_inv_end CTX)). }
  { now rewrite (rc_rmw_dep CTX), (rsr_nrmw_dep (rc_inv_end CTX)). }
  ins.
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

(* Intermediate graph for locating the srf edge for for a_s *)

Definition A_s'' := extra_a X_t' a_t' b_t' a_s'.
Definition E_s' := mapper ↑₁ E_t' ∪₁ A_s''.

Lemma simrel_reexec :
  exists mapper X_s' f' dtrmt' cmt',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper >> /\
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