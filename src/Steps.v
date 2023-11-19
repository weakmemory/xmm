Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import Core.  
Import WCore.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

From RecordUpdate Require Import RecordSet. 

Import ListNotations.

Lemma add_step_same_committed (X X' : t) (STEP : add_step X X') : committed X' ≡₁ committed X.
Proof using.
  do 2 (red in STEP; desf).
  unfold committed. now rewrite COMMITENTR.
Qed.

Lemma add_step_wf (X X' : t) (WF : wf X) (STEP : add_step X X') : wf X'.
Proof using.
  unfold add_step, add_step_, add_step_exec in *.
  desf; constructor; auto; intros.
  all: rewrite ?CONT', ?COMMITENTR, ?NCOMMITIDS; auto; try apply WF.
  all: try now apply NCOMMITIDS.
  all: try now apply NCOMMITIDS; rewrite COMMITENTR in CIN;
               apply WF.
  all: try now rewrite updo by congruence;
               apply WF; apply THREADS.

  all: apply set_subset_eq with (P := set_compl _) (a := e) in NRMW.
  all: rewrite RMW', dom_union, set_compl_union in NRMW.
  all: apply EVENTS in IN; unfolder in IN; desf; ins.
  all: try now rewrite upds.
  2: { exfalso. eapply NRMW; eauto.
       clear. basic_solver. }
  all: rewrite updo.
  all: try now apply WF; auto; apply NRMW.
  all: injection as Heq; subst.
  all: eapply EVENT; eauto.
  all: clear; basic_solver.
Qed. 

Lemma commit_step_wf (X X' : t) (WF: wf X)
                (cid : Commit.id) (e : actid)
                (STEP: commit_step cid e X X'): wf X'.
Proof using.
  desf; constructor; intros.
  all: rewrite ?(cmt_K STEP).
  all: try (apply WF; erewrite <- ?cmt_G by eassumption; auto).

  { rewrite (cmt_G STEP).
    now apply WF. }
  { rewrite (cmt_noncid STEP).
    apply set_size_inf_minus_singl.
    apply WF. }
  { apply (cmt_noncid STEP) in NCI.
    rewrite (cmt_centries STEP), updo; [apply WF | symmetry].
    all: apply NCI. }
  assert (AA : cid0 <> cid).
  { intro F. now rewrite F, (cmt_centries STEP), upds in CIN. }
  rewrite (cmt_centries STEP), updo in CIN by auto.
  apply WF in CIN. apply (cmt_noncid STEP). basic_solver.
Qed. 

Lemma rf_change_step_disjoint (G : execution) (r : actid) (WF : Wf G) :
  set_disjoint ((fun a => is_init a) ∩₁ acts_set G) (codom_rel (⦗eq r⦘⨾ (sb G ∪ rf G)⁺)).
Proof using.
  unfolder. intros e (INIT & _) (e' & EQ & REL). subst e'.
  induction REL as [r e REL |]; auto.
  destruct REL as [REL|REL].
  all: apply no_sb_to_init in REL || apply no_rf_to_init in REL.
  all: now unfolder in REL.
Qed.

Lemma rfc_imG_wf (G'' : execution) sc'' (w r : actid) (X X' : t)
  (STEP : rf_change_step_ G'' sc'' w r X X') (WF : Wf (G X)) : Wf G''.
Proof using.
  eapply sub_WF; eauto using rfc_sub.
  rewrite (rfc_acts STEP).
  erewrite <- (set_minus_disjoint (_ ∩₁ _)).
  { apply set_subset_minus; basic_solver. }
  eapply set_disjoint_more.
  all: try apply rf_change_step_disjoint; eauto.
  unfold rfc_remove_events; basic_solver.
Qed.

Lemma rfc_imG_no_broken_rmw (G'' : execution) sc'' (w r e e' : actid) (X X' : t)
  (STEP : rf_change_step_ G'' sc'' w r X X')
  (WF : Wf (G X))
  (RMW : rmw (G X) e e')
  (E_SAVED : acts_set G'' e):
  rmw G'' e e'.
Proof using.
  apply (sub_rmw (rfc_sub STEP)).
  apply wf_rmwE in RMW; eauto using rfc_imG_wf.
  unfolder in RMW.
  destruct RMW as (DOML & RMW & DOMR).
  unfolder. splits; auto.
  apply (rfc_acts STEP).
  unfolder. splits; auto.
  unfold rfc_remove_events. unfolder.
  intros (x & z & [EQ1 EQ2] & REL). subst x z.
  apply (rfc_acts STEP) in E_SAVED.
  destruct E_SAVED as [_ NOT_REMOVED].
  unfold rfc_remove_events in NOT_REMOVED. unfolder in NOT_REMOVED.
  apply NOT_REMOVED. do 2 exists r. splits; auto. clear NOT_REMOVED.
 (* immediate set of a union *)
 (* r <> e? *)
 (* We seem to be stuck due to the same po-rf problem *)
  admit.
Admitted.

Lemma rfc_endG_preserve_r (r w : actid) (G : execution) (e : actid)
  : is_r (lab (rfc_endG r w G)) e = is_r (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, is_r in *; ins.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_endG_preserve_w (r w : actid) (G : execution) (e : actid)
  : is_w (lab (rfc_endG r w G)) e = is_w (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, is_w in *; ins.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_endG_preserve_f (r w : actid) (G : execution) (e : actid)
  : is_f (lab (rfc_endG r w G)) e = is_f (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, is_f in *; ins.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_endG_r_eq (r w : actid) (G : execution)
  : is_r (lab (rfc_endG r w G)) ≡₁ is_r (lab G).
Proof using.
  unfolder; splits; intros.
  all: now rewrite ?rfc_endG_preserve_r in *.
Qed.

Lemma rfc_endG_w_eq (r w : actid) (G : execution)
  : is_w (lab (rfc_endG r w G)) ≡₁ is_w (lab G).
Proof using.
  unfolder; splits; intros.
  all: now rewrite ?rfc_endG_preserve_w in *.
Qed.

Lemma rfc_endG_f_eq (r w : actid) (G : execution)
  : is_f (lab (rfc_endG r w G)) ≡₁ is_f (lab G).
Proof using.
  unfolder; splits; intros.
  all: now rewrite ?rfc_endG_preserve_f in *.
Qed.

Lemma rfc_endG_preserve_loc (e : actid) (r w : actid) (G : execution)
  : loc (lab (rfc_endG r w G)) e = loc (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, loc. simpl.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_endG_same_loc_eq (r w : actid) (G : execution)
  : same_loc (lab (rfc_endG r w G)) ≡ same_loc (lab G).
Proof using.
  unfold same_loc; unfolder; splits; intros.
  all: now rewrite ?rfc_endG_preserve_loc in *.
Qed.

Lemma rfc_endG_eqE (r w : actid) (G : execution)
  : acts_set (rfc_endG r w G) ≡₁ acts_set G.
Proof using.
  unfold acts_set; unfold rfc_endG; simpl.
  easy.
Qed.

Lemma rfc_endG_eqRex_bool (e : actid) (r w : actid) (G : execution)
  : R_ex (lab (rfc_endG r w G)) e = R_ex (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, R_ex. simpl.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_endG_eqRex (r w : actid) (G : execution)
  : R_ex (lab (rfc_endG r w G)) ≡₁ R_ex (lab G).
Proof using.
  unfolder; splits; intros.
  all: now rewrite ?rfc_endG_eqRex_bool in *.
Qed.

Lemma update_rf_ineq_l (r x y : actid) (G : execution)
  (WF : Wf G) (RF : (rf G \ edges_to r) x y) (IS_READ : is_r (lab G) r) :
  x <> r.
Proof using.
  destruct RF as [RF INEQ]. intro F; subst.
  apply (wf_rfD WF) in RF.
  unfolder in RF; desc.
  unfold is_w, is_r in *; destruct (lab G r); auto.
Qed.

Lemma update_rf_ineq_r (r x y : actid) (G : execution)
  (WF : Wf G) (RF : (rf G \ edges_to r) x y) (IS_READ : is_r (lab G) r) :
  y <> r.
Proof using.
  destruct RF as [RF INEQ]. intro; subst.
  apply INEQ; basic_solver.
Qed.

Lemma rfc_endG_wf (r w : actid) (G : execution) (WF : Wf G)
  (R_MEM : acts_set G w)
  (W_MEM : acts_set G r)
  (R_READ : is_r (lab G) r)
  (W_WRITE : is_w (lab G) w)
  (W_R_SAME_LOC : same_loc (lab G) w r):
  Wf (rfc_endG r w G).
Proof using.
  assert (SUB : rf G \ edges_to r ⊆ rf G) by basic_solver.
  constructor; try now apply WF.
  all: rewrite ?rfc_endG_r_eq, ?rfc_endG_w_eq, ?rfc_endG_f_eq, ?rfc_endG_eqRex.
  all: rewrite ?rfc_endG_same_loc_eq, ?rfc_endG_eqE.
  all: try solve [unfold rfc_endG; simpl; now apply WF].

  { unfold rfc_endG; simpl.
    rewrite seq_union_l, seq_union_r.
    rewrite <- single_rel_compress by assumption.
    now erewrite <- rel_compress_sub by (apply WF || eauto). }
  { unfold rfc_endG; simpl.
    rewrite seq_union_l, seq_union_r.
    rewrite <- single_rel_compress by assumption.
    now erewrite <- rel_compress_sub by (apply WF || eauto). }
  { unfold rfc_endG; simpl.
    set (HH := wf_rfl WF).
    apply inclusion_union_l; basic_solver. }
  { unfold rfc_endG; simpl. apply funeq_union.
    { intros x y RF.
      unfold val; simpl.
      rewrite updo by (eapply update_rf_ineq_l; eauto).
      rewrite updo by (eapply update_rf_ineq_r; eauto).
      apply wf_rfv; basic_solver. }
    intros x y [EQ EQ']. subst.
    unfold val; simpl.
    rewrite upds. unfold is_r, is_w in *.
    destruct (lab G r) eqn:HEQ1; destruct (lab G w) eqn:HEQ2.
    all: try easy; simpl.
    rewrite updo by (intro F; subst; congruence).
    now rewrite HEQ2. }
  { unfold rfc_endG; simpl.
    rewrite transp_union. apply functional_union.
    { eapply functional_mori; unfold flip; eauto using wf_rff, transp_mori. }
    { basic_solver. }
    unfolder; intros e [y [RF F]] [y' [EQ1 EQ2]]; subst.
    apply F; eauto. }
  { intro ol.
    rewrite rfc_endG_w_eq, rfc_endG_eqE.
    enough (HEQ :
      (fun x : actid => loc _ x = ol) ≡₁
      (fun x : actid => loc _ x = ol)
    ) by (rewrite HEQ; unfold rfc_endG; simpl; apply WF).
    unfold same_loc; unfolder; splits; intros.
    all: now rewrite ?rfc_endG_preserve_loc in *. }
  { intros l [e [INACT LOC]].
    apply rfc_endG_eqE in INACT.
    rewrite rfc_endG_preserve_loc in LOC.
    apply WF; eauto. }
  unfold rfc_endG; simpl. intros l.
  enough (HNEQ: InitEvent l <> r) by (rewrite updo; apply WF || auto).
  intro F; subst. eapply read_or_fence_is_not_init; eauto.
Qed.

Lemma rf_change_step_wf w r (X X' : t)
  (WF : wf X) (STEP : rf_change_step w r X X')
  : wf X'.
Proof using.
  unfold rf_change_step in STEP. destruct STEP as (G'' & sc & CONDS).
  desc. constructor.
  { erewrite rfc_G by eassumption.
    apply rfc_endG_wf.
    all: try now (erewrite sub_lab; apply RFC).
    { eapply rfc_imG_wf; eauto.
      apply WF. }
    { eapply rfc_acts; eauto. unfolder; splits.
      { eapply rfc_act_w; eauto. }
      intros (r' & r'' & ((EQ & EQ') & PORF)); subst r''; subst r'.
      admit. }
    eapply rfc_acts; eauto. unfolder; splits.
    { eapply rfc_act_r; eauto. }
    admit. }
  { rewrite (rfc_G RFC), CONTINUATION.
    intros e INIT ACT NRMW.
    apply rfc_endG_eqE in ACT.
    unfold rfc_endG in NRMW; simpl in NRMW.
    unfold rfc_new_cont.
    edestruct (excluded_middle_informative _).
    { exfalso.
      apply (rfc_acts RFC) in ACT.
      now apply ACT. }
    apply set_subset_eq with (P := set_compl _) (a := e) in NRMW.
    rewrite (sub_rmw (rfc_sub RFC)) in NRMW.
    rewrite dom_eqv1, set_compl_inter in NRMW.
    destruct (NRMW e) as [MEM | DOM]; try (auto || basic_solver).
    (* NOW prove that the right half of RMW didn't get cut *)
    admit. }
  { intros tid HTHREAD.
    rewrite CONTINUATION. unfold rfc_new_cont.
    apply WF.
    enough (HEQ : threads_set (G X') ≡₁ threads_set (G X)) by now apply HEQ.
    rewrite (rfc_G RFC).
    unfold rfc_endG; simpl.
    (* TODO G'' and (G X) have same thread sets *)
    admit. }
  { rewrite NCOMMITIDS.
    apply set_size_inf_union.
    apply WF. }
  { intros cid NON_CMT.
    apply NCOMMITIDS in NON_CMT.
    rewrite COMMIT_ENTRIES; unfold rfc_new_commit_entries.
    edestruct (excluded_middle_informative _); auto.
    apply WF; unfolder in NON_CMT; basic_solver. }
  intros cid ENTRY.
  rewrite COMMIT_ENTRIES in ENTRY. unfold rfc_new_commit_entries in ENTRY.
  apply NCOMMITIDS.
  edestruct (excluded_middle_informative _); try basic_solver.
  left. now apply WF.
Admitted.

Lemma reexec_step_wf w r (X X' : t)
  (WF : wf X) (STEP : reexec_step w r X X') : wf X'.
Proof using.
  cdes STEP.
  assert (WF'' : wf X'').
  { eapply rf_change_step_wf; eauto. }
  clear - RESTORE WF''. induction RESTORE; eauto.
  eapply add_step_wf; eauto.
Qed.