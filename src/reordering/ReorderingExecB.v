Require Import ReordSimrel ReorderingEq.
Require Import AuxDef MapDoms.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import PorfPrefix.
Require Import AddEventWf.
Require Import ReorderingFakeSrf.
Require Import ReorderingCons ReorderingMapper.
Require Import ConsistencyMonotonicity.
Require Import xmm_s_hb.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics Lia.

Section ExecB.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t : actid.
Variable l_a l_b : label.

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
Notation "'rpo_imm_s'" := (rpo_imm G_s).
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

Notation "'is_init'" := (fun e => is_true (is_init e)).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'mapper'" := (mapper a_t b_t).

Notation "'A_s'" := (extra_a X_t a_t b_t b_t).
Notation "'B_s'" := (extra_a X_t a_t b_t a_t).
Notation "'A_s''" := (extra_a X_t' a_t b_t b_t).

Definition rsr_b_immg := {|
  acts_set := E_s ∪₁ eq b_t;
  threads_set := threads_set G_s;
  lab := upd lab_s b_t l_a;
  rf := rf_s ∪
        fake_srf G_s b_t l_a ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘;
  co := co_s ∪
        (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
          (eq b_t ∩₁ WCore.lab_is_w l_a);
  rmw := mapper ↑ rmw_t;
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.
Definition rsr_b_immx := {|
  WCore.sc := WCore.sc X_s;
  WCore.G := rsr_b_immg;
|}.

Notation "'X_s'''" := rsr_b_immx.
Notation "'G_s'''" := (WCore.G X_s'').
Notation "'lab_s'''" := (lab G_s'').
Notation "'val_s'''" := (val lab_s'').
Notation "'loc_s'''" := (loc lab_s'').
Notation "'same_loc_s'''" := (same_loc lab_s'').
Notation "'E_s'''" := (acts_set G_s'').
Notation "'loc_s'''" := (loc lab_s'').
Notation "'sb_s'''" := (sb G_s'').
Notation "'rf_s'''" := (rf G_s'').
Notation "'co_s'''" := (co G_s'').
Notation "'rmw_s'''" := (rmw G_s'').
Notation "'rpo_imm_s'''" := (rpo_imm G_s'').
Notation "'rpo_s'''" := (rpo G_s'').
Notation "'sw_s'''" := (sw G_s'').
Notation "'rmw_dep_s'''" := (rmw_dep G_s'').
Notation "'data_s'''" := (data G_s'').
Notation "'ctrl_s'''" := (ctrl G_s'').
Notation "'addr_s'''" := (addr G_s'').
Notation "'W_s'''" := (fun x => is_true (is_w lab_s'' x)).
Notation "'R_s'''" := (fun x => is_true (is_r lab_s'' x)).
Notation "'F_s'''" := (fun x => is_true (is_f lab_s'' x)).
Notation "'vf_s'''" := (vf G_s'').
Notation "'srf_s'''" := (srf G_s'').
Notation "'Loc_s_''' l" := (fun e => loc_s'' e = l) (at level 1).
Notation "'Val_s_''' l" := (fun e => val_s'' e = l) (at level 1).
Notation "'Rlx_s'''" := (fun e => is_true (is_rlx lab_s'' e)).
Notation "'Acq_s'''" := (fun e => is_true (is_acq lab_s'' e)).
Notation "'Rel_s'''" := (fun e => is_true (is_rel lab_s'' e)).

Definition rsr_b_Gs_prime := {|
  acts_set := E_s ∪₁ eq b_t ∪₁ eq a_t;
  threads_set := threads_set G_s;
  lab := upd (upd lab_s b_t l_a) a_t l_b;
  rf := rf_s ∪
        mapper ↑ (rf_t' ⨾ ⦗eq b_t⦘) ∪
        srf_s'' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘;
  co := co_s ∪
        mapper ↑ (⦗eq b_t⦘ ⨾ co_t' ∪ co_t' ⨾ ⦗eq b_t⦘) ∪
        (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
          (eq b_t ∩₁ WCore.lab_is_w l_a);
  rmw := mapper ↑ rmw_t';
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.
Definition rsr_b_Xs_prime := {|
  WCore.sc := WCore.sc X_s;
  WCore.G := rsr_b_Gs_prime;
|}.

Notation "'X_s''" := rsr_b_Xs_prime.
Notation "'G_s''" := (WCore.G X_s').
Notation "'lab_s''" := (lab G_s').
Notation "'val_s''" := (val lab_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'same_loc_s''" := (same_loc lab_s').
Notation "'E_s''" := (acts_set G_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'sb_s''" := (sb G_s').
Notation "'rf_s''" := (rf G_s').
Notation "'co_s''" := (co G_s').
Notation "'rmw_s''" := (rmw G_s').
Notation "'rpo_imm_s''" := (rpo_imm G_s').
Notation "'rpo_s''" := (rpo G_s').
Notation "'sw_s''" := (sw G_s').
Notation "'rmw_dep_s''" := (rmw_dep G_s').
Notation "'data_s''" := (data G_s').
Notation "'ctrl_s''" := (ctrl G_s').
Notation "'addr_s''" := (addr G_s').
Notation "'W_s''" := (fun x => is_true (is_w lab_s' x)).
Notation "'R_s''" := (fun x => is_true (is_r lab_s' x)).
Notation "'F_s''" := (fun x => is_true (is_f lab_s' x)).
Notation "'vf_s''" := (vf G_s').
Notation "'srf_s''" := (srf G_s').
Notation "'Loc_s_'' l" := (fun e => loc_s' e = l) (at level 1).
Notation "'Val_s_'' l" := (fun e => val_s' e = l) (at level 1).
Notation "'Rlx_s''" := (fun e => is_true (is_rlx lab_s' e)).
Notation "'Acq_s''" := (fun e => is_true (is_acq lab_s' e)).
Notation "'Rel_s''" := (fun e => is_true (is_rel lab_s' e)).

Hypothesis ADD : WCore.add_event X_t X_t' b_t l_b.

Lemma rsr_step_acts : E_t' ≡₁ E_t ∪₁ eq b_t.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_b_tid : tid b_t <> tid_init.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_b_ninit : ~is_init b_t.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_b_notin : ~E_t b_t.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Lemma rsr_b_in' : E_t' b_t.
Proof using ADD.
  apply rsr_step_acts. now right.
Qed.

Lemma rsr_step_lab : lab_t' = upd lab_t b_t l_b.
Proof using ADD.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply ADD'.
Qed.

Hint Resolve rsr_b_tid rsr_b_notin rsr_b_ninit
             rsr_b_in' : xmm.

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t b_t.
Hypothesis CONS : WCore.is_cons G_t'.

Lemma rsr_b_a_nin' : ~ E_t' a_t.
Proof using ADD INV'.
Admitted.

Lemma rsr_b_a_nin : ~ E_t a_t.
Proof using ADD INV'.
Admitted.

Lemma rsr_b_old_exa : A_s ≡₁ ∅.
Proof using ADD INV'.
Admitted.

Lemma rsr_b_new_exa : A_s' ≡₁ eq b_t.
Proof using ADD INV'.
Admitted.

Hint Resolve rsr_b_a_nin' rsr_b_a_nin : xmm.

Hypothesis SIMREL : reord_simrel X_s X_t a_t b_t mapper.

Lemma rsr_new_a_sb_delta :
  ⦗E_s⦘ ⨾ ext_sb ⨾ ⦗eq b_t⦘ ≡ WCore.sb_delta b_t E_s.
Proof using b_t a_t ADD SIMREL INV INV'.
  (* destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  rewrite (rsr_actsE INV SIMREL).
  arewrite (WCore.sb_delta e (E_t ∪₁ B_s) ≡
    WCore.sb_delta e E_t ∪ (B_s ∩₁ same_tid e) × eq e
  ).
  { unfold WCore.sb_delta.
    rewrite set_inter_union_l, !cross_union_l.
    now rewrite <- unionA. }
  rewrite id_union, !seq_union_l.
  apply union_more; [apply (sb_deltaEE ADD') |].
  unfold extra_a. desf; [| basic_solver].
  unfold same_tid. split.
  { unfolder. intros x y (EQ1 & SB & EQ2).
    subst x y. auto with xmm. }
  unfolder. intros x y ((EQ1 & TID) & EQ2). subst x y.
  exfalso. apply rsr_Et_restr; [| desf].
  now rewrite <- (rsr_at_bt_tid INV). *)
Admitted.

Lemma rsr_new_a_sb :
  sb_s'' ≡ sb_s ∪ WCore.sb_delta b_t E_s.
Proof using b_t a_t ADD SIMREL INV INV'.
  (* unfold sb at 1. simpl.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  rewrite !id_union, !seq_union_l, !seq_union_r.
  change (⦗E_s⦘ ⨾ ext_sb ⨾ ⦗E_s⦘) with sb_s.
  rewrite (rsr_actsE INV SIMREL) at 2.
  rewrite !id_union, !seq_union_r.
  arewrite_false (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗eq e⦘).
  { enough (~ext_sb e e) by basic_solver.
    intro FALSO; eapply ext_sb_irr; eauto. }
  rewrite (sb_deltaEN ADD').
  arewrite_false (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗extra_a X_t a_t b_t a_t⦘).
  { unfold extra_a; desf; [| basic_solver].
    unfolder. intros x y (EQ1 & SB & EQ2). subst x y.
    apply rsr_Et_restr; desf.
    rewrite <- (rsr_at_bt_tid INV); auto with xmm. }
  now rewrite !union_false_r, rsr_new_e_sb_delta. *)
Admitted.

(* Lemma rsr_nanb_map_sbdelta :
  mapper ↑ WCore.sb_delta b_t E_t ≡
    WCore.sb_delta b_t E_s.
Proof using b_t a_t ADD E_NOT_B E_NOT_A SIMREL INV INV'.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  assert (ANINI : ~is_init a_t) by apply INV.
  assert (BNINI : ~is_init b_t) by apply INV.
  unfold WCore.sb_delta.
  rewrite collect_rel_cross, set_collect_eq, rsr_mappero; auto.
  rewrite set_collect_union.
  rewrite <- fixset_set_fixpoint by auto with xmm.
  arewrite (mapper ↑₁ (E_t ∩₁ same_tid e) ≡₁ E_s ∩₁ same_tid e)
    ; [| reflexivity].
  rewrite (rsr_acts SIMREL), set_inter_union_l.
  rewrite rsr_mapper_sametid; auto.
  arewrite (A_s ∩₁ same_tid e ≡₁ ∅); [| now rewrite set_union_empty_r].
  unfold extra_a, same_tid; desf; [| basic_solver].
  split; auto with hahn.
  unfolder. intros x (XEQ & TID). subst x.
  apply rsr_Et_restr; auto; desf.
Qed. *)

Lemma rsr_b_notin_s : ~ E_s b_t.
Proof using b_t a_t ADD SIMREL INV INV'.
Admitted.

Lemma rsr_b_notin_s' : ~ E_s (mapper a_t).
Proof using b_t a_t ADD SIMREL INV INV'.
Admitted.

Lemma rsr_b_a_notin_s : ~ E_s a_t.
Proof using b_t a_t ADD SIMREL INV INV'.
Admitted.

Lemma rsr_b_a_notin_s' : ~ E_s'' a_t.
Proof using b_t a_t ADD SIMREL INV INV'.
Admitted.

Hint Resolve rsr_b_notin_s rsr_b_notin_s'
             rsr_b_a_notin_s rsr_b_a_notin_s' : xmm.

Lemma rsr_b_lab : eq_dom E_t' lab_t' (lab_s' ∘ mapper).
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl.
  rewrite <- rsr_mapper_at with (a_t := a_t) (b_t := b_t) at 1.
  all: auto.
Admitted.

Lemma rsr_b_labi : eq_dom E_s'' lab_s'' lab_s'.
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. apply eq_dom_upd_r; [| reflexivity].
  unfolder. intros [XIN | EQ].
  all: auto with xmm.
Qed.

Lemma rsr_b_labi' : eq_dom E_s'' lab_s' lab_s''.
Proof using ADD SIMREL INV INV'.
  symmetry. exact rsr_b_labi.
Qed.

Lemma rsr_b_lab' : eq_dom E_t' (lab_s' ∘ mapper) lab_t'.
Proof using ADD SIMREL INV INV'.
  symmetry. exact rsr_b_lab.
Qed.

Lemma rsr_b_mapinj : inj_dom E_t' mapper.
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  eapply inj_dom_mori; auto with xmm.
  red; auto with hahn.
Qed.

Lemma rsr_b_in1 : E_s'' ⊆₁ E_s'.
Proof using.
  clear. simpl. basic_solver.
Qed.

Hint Resolve rsr_b_lab rsr_b_lab'
             rsr_b_labi rsr_b_labi'
            rsr_b_mapinj rsr_Gt_wf : xmm.

Lemma rsr_b_sim :
  reord_simrel X_s' X_t' a_t b_t mapper.
Proof using.
Admitted.

Lemma rsr_new_Gs_wf :
  Wf G_s'.
Proof using b_t a_t ADD SIMREL INV INV'.
  apply (G_s_wf INV' rsr_b_sim).
Qed.

Lemma rsr_new_Gs_cons :
  WCore.is_cons G_s'.
Proof using.
Admitted.

Lemma rsr_b_imm_rpoimm_in :
  rpo_imm_s'' ⊆ rpo_imm_s'.
Proof using ADD SIMREL INV INV'.
  unfold rpo_imm, sb.
  rewrite !seqA.
  seq_rewrite (seq_eqvC E_s'' (F_s'' ∩₁ Acq_s'')).
  seq_rewrite (seq_eqvC E_s'' Rel_s'').
  seq_rewrite (seq_eqvC E_s'' (W_s'' ∩₁ Rlx_s'')).
  seq_rewrite (seq_eqvC E_s' (F_s' ∩₁ Acq_s')).
  seq_rewrite (seq_eqvC E_s' Rel_s').
  seq_rewrite (seq_eqvC E_s' (W_s' ∩₁ Rlx_s')).
  seq_rewrite <- !id_inter.
  rewrite !set_interA.
  rewrite !set_inter_rlx with (G := G_s').
  all: auto with xmm.
  rewrite !set_inter_acq with (G := G_s').
  all: auto with xmm.
  rewrite !set_inter_rel with (G := G_s').
  all: auto with xmm.
  rewrite !set_inter_is_f with (G := G_s') (s' := E_s'') (G' := G_s''),
          set_inter_is_r with (G := G_s') (s' := E_s''),
          set_inter_is_w with (G := G_s') (s' := E_s'').
  all: auto with xmm.
  { rewrite rsr_b_in1. reflexivity. }
  all: basic_solver.
Qed.

Lemma rsr_b_imm_rpo_in :
  rpo_s'' ⊆ rpo_s'.
Proof using ADD SIMREL INV INV'.
  unfold rpo. now rewrite rsr_b_imm_rpoimm_in.
Qed.

Lemma rsr_imm_Gs_cons :
  WCore.is_cons G_s''.
Proof using.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  apply XmmCons.monoton_cons
   with (G_t := G_s') (m := id).
  all: rewrite ?set_collect_id, ?collect_rel_id.
  { basic_solver. }
  { simpl. basic_solver. }
  { apply rsr_b_imm_rpo_in. }
  { admit. }
  { simpl. rewrite unionA.
    apply union_mori; [reflexivity |].
    apply inclusion_union_r. now right. }
  { simpl. rewrite (WCore.add_event_rmw ADD').
    rewrite collect_rel_union.
    apply inclusion_union_r. now left. }
  { admit. }
  { admit. }
  { apply (G_s_wf INV' rsr_b_sim). }
  { admit. }
  apply rsr_new_Gs_cons.
Admitted.

Hint Resolve rsr_new_Gs_wf rsr_new_Gs_cons : xmm.

Lemma rsr_b_step1 :
  WCore.add_event X_s X_s'' (mapper a_t) l_a.
Proof using.
Admitted.

Lemma rsr_b_step2 :
  WCore.add_event X_s'' X_s' (mapper b_t) l_b.
Proof using.
Admitted.

Lemma simrel_exec_b_step_1 :
    WCore.exec_inst X_s  X_s'' b_t l_a.
Proof using INV INV'.
Admitted.

Lemma simrel_exec_b_step_2 :
    WCore.exec_inst X_s'' X_s' a_t l_b.
Proof using INV INV'.
Admitted.

End ExecB.