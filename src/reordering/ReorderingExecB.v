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

Lemma rsr_new_a_sb' :
  sb_s' ≡ sb_s'' ∪ WCore.sb_delta a_t E_s''.
Proof using b_t a_t ADD SIMREL INV INV'.
Admitted.

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

Lemma rsr_b_Gs_wf : Wf G_s.
Proof using INV SIMREL.
  apply (G_s_wf INV SIMREL).
Qed.

Lemma rsr_b_initE : is_init ⊆₁ E_s.
Proof using ADD SIMREL INV INV'.
  apply (rsr_init_acts_s INV SIMREL).
Qed.

Lemma rsr_b_initE' : is_init ⊆₁ E_s''.
Proof using ADD SIMREL INV INV'.
  transitivity E_s; [| simpl; basic_solver].
  apply (rsr_init_acts_s INV SIMREL).
Qed.

Hint Resolve rsr_b_notin_s rsr_b_notin_s'
             rsr_b_a_notin_s rsr_b_a_notin_s'
             rsr_b_Gs_wf
             rsr_b_initE rsr_b_initE' : xmm.

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

Lemma rsr_b_labs : eq_dom E_s lab_s lab_s''.
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. apply eq_dom_upd_r; [| reflexivity].
  all: auto with xmm.
Qed.

Lemma rsr_b_labb : eq_dom E_s lab_s lab_s'.
Proof using ADD SIMREL INV INV'.
  simpl. apply eq_dom_upd_r; [| apply rsr_b_labs].
  auto with xmm.
Qed.

Lemma rsr_b_labs' : eq_dom E_s lab_s'' lab_s.
Proof using ADD SIMREL INV INV'.
  symmetry. exact rsr_b_labs.
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

Lemma rsr_b_mapb : mapper ↑₁ (eq b_t ∩₁ E_t') ⊆₁ eq a_t.
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  rewrite set_inter_absorb_r.
  { rewrite set_collect_eq, rsr_mapper_bt.
    all: auto with hahn. }
  red. intros x XEQ. subst x. auto with xmm.
Qed.

Lemma rsr_b_mapa : mapper ↑₁ (eq a_t ∩₁ E_t') ⊆₁ eq b_t.
Proof using ADD SIMREL INV INV'.
  arewrite (eq a_t ∩₁ E_t' ⊆₁ ∅).
  { unfolder. intros x (XEQ & XIN). subst x.
    auto with xmm. }
  rewrite set_collect_empty. auto with hahn.
Qed.

Lemma rsr_imm_Gs_wf :
  Wf G_s''.
Proof using b_t a_t ADD SIMREL INV INV'.
Admitted.

Hint Resolve rsr_b_lab rsr_b_lab'
             rsr_b_labi rsr_b_labi'
             rsr_b_mapinj rsr_Gt_wf
             rsr_b_labs rsr_b_labs'
             rsr_b_mapb rsr_b_mapa
             rsr_b_labb rsr_imm_Gs_wf : xmm.

Lemma rsr_b_in1 : E_s'' ⊆₁ E_s'.
Proof using.
  clear. simpl. basic_solver.
Qed.

Lemma rsr_b_imm_sb_to_a :
  sb_s'' ⨾ ⦗eq b_t⦘ ≡ WCore.sb_delta b_t E_s.
Proof using SIMREL INV' INV ADD.
  assert (NINS : ~E_s b_t) by auto with xmm.
  rewrite rsr_new_a_sb, seq_union_l.
  arewrite_false (sb_s ⨾ ⦗eq b_t⦘).
  { unfold sb. basic_solver. }
  rewrite union_false_l. unfold WCore.sb_delta.
  now rewrite <- cross_inter_r, set_interK.
Qed.

Lemma rsr_b_vfsb_eq :
  vf_s'' ⨾ sb_s'' ⨾ ⦗eq b_t⦘ ≡
    vf_s ⨾ sb_s'' ⨾ ⦗eq b_t⦘.
Proof using SIMREL INV' INV ADD.
  assert (NINS : ~E_s b_t) by auto with xmm.
  rewrite rsr_b_imm_sb_to_a.
  arewrite (
    WCore.sb_delta b_t E_s ≡
      ⦗E_s⦘ ⨾ WCore.sb_delta b_t E_s
  ).
  { unfold WCore.sb_delta. rewrite <- cross_inter_l.
    rewrite set_inter_absorb_l
       with (s' := E_s) (s := is_init ∪₁ E_s ∩₁ same_tid b_t)
        ; [reflexivity |].
    apply set_subset_union_l.
    split; auto with xmm. basic_solver. }
  rewrite <- !seqA. apply seq_more; [| reflexivity].
  apply porf_pref_vf.
  all: auto with xmm.
  { ins. basic_solver. }
  { rewrite rsr_new_a_sb, seq_union_l.
    arewrite_false (WCore.sb_delta b_t E_s ⨾ ⦗E_s⦘);
      [| basic_solver].
    unfold WCore.sb_delta. basic_solver. }
  { simpl. rewrite seq_union_l.
    basic_solver. }
  simpl. now rewrite (rsr_rmw SIMREL).
Qed.

Lemma rsr_b_fakesrf :
  srf_s'' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ ≡
    fake_srf G_s b_t l_a ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘.
Proof using SIMREL INV' INV ADD.
  assert (NINS : ~E_s b_t) by auto with xmm.
  symmetry. apply fake_srf_is_srf.
  all: auto with xmm.
  { apply rsr_b_vfsb_eq. }
  simpl. rewrite seq_union_l.
  basic_solver.
Qed.

Lemma rsr_b_isr_helper :
  eq b_t ∩₁ R_s' ≡₁ eq b_t ∩₁ WCore.lab_is_r l_a.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. unfold is_r, WCore.lab_is_r.
  unfolder. split.
  all: intros x (XEQ & ISR); subst x.
  all: rewrite updo, upds in *; desf.
  all: congruence.
Qed.

Lemma rsr_b_samesrf :
  srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ ≡
    srf_s'' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘.
Proof using SIMREL INV' INV ADD.
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (NIN : ~E_s a_t) by auto with xmm.
  assert (IDE : eq a_t ∩₁ (E_s ∪₁ eq b_t) ⊆₁ ∅).
  { basic_solver. }
  arewrite (
    ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ ≡
      ⦗E_s''⦘ ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘
  ).
  { rewrite <- id_inter, set_inter_absorb_l with (s' := E_s'').
    all: auto with hahn.
    simpl. basic_solver. }
  rewrite <- !seqA. apply seq_more; [| reflexivity].
  apply porf_pref_srf; auto with xmm.
  { simpl. basic_solver. }
  { rewrite rsr_new_a_sb', seq_union_l.
    arewrite_false (WCore.sb_delta a_t E_s'' ⨾ ⦗E_s''⦘);
      [| now rewrite union_false_r].
    unfold WCore.sb_delta. rewrite <- cross_inter_r.
    arewrite (eq a_t ∩₁ E_s'' ⊆₁ ∅).
    now rewrite cross_false_r. }
  { simpl. rewrite <- rsr_b_fakesrf.
    rewrite !seq_union_l.
    arewrite_false (mapper ↑ (rf_t' ⨾ ⦗eq b_t⦘) ⨾ ⦗E_s ∪₁ eq b_t⦘)
      ; [| basic_solver 11].
    rewrite collect_rel_seqi, collect_rel_eqv,
            set_collect_eq, rsr_mapper_bt; auto.
    rewrite seqA, <- id_inter, IDE.
    now rewrite eqv_empty, seq_false_r. }
  { simpl. rewrite !seq_union_l, !seq_union_r.
    arewrite_false (
      ⦗E_s ∪₁ eq b_t⦘ ⨾
        mapper ↑ (⦗eq b_t⦘ ⨾ co_t' ∪ co_t' ⨾ ⦗eq b_t⦘) ⨾
          ⦗E_s ∪₁ eq b_t⦘
    ); [| basic_solver 11].
    rewrite collect_rel_union, seq_union_l,
            seq_union_r, !collect_rel_seqi.
    rewrite collect_rel_eqv, set_collect_eq,
              rsr_mapper_bt, !seqA; auto.
    seq_rewrite (seq_eqvC (E_s ∪₁ eq b_t) (eq a_t)).
    rewrite <- id_inter, IDE, eqv_empty.
    now rewrite !seq_false_r, !seq_false_l, union_false_r. }
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  simpl. rewrite (WCore.add_event_rmw ADD'), collect_rel_union.
  rewrite seq_union_l, mapped_rmw_delta, rsr_mapper_bt; auto.
  unfold WCore.rmw_delta.
  split; [| apply inclusion_union_r; now left].
  rewrite <- cross_inter_r, IDE.
  now rewrite cross_false_r, union_false_r.
Qed.

Lemma rsr_b_exco_helper :
  eq a_t ∩₁ W_s' ∩₁ Loc_s_' (loc_s' b_t) ≡₁ ∅.
Proof using.
Admitted.

Lemma rsr_b_isw_helper :
  eq b_t ∩₁ W_s' ≡₁ eq b_t ∩₁ WCore.lab_is_w l_a.
Proof using INV.
  assert (NEQ : a_t <> b_t) by apply INV.
  simpl. unfold is_w, WCore.lab_is_w.
  unfolder. split.
  all: intros x (XEQ & ISR); subst x.
  all: rewrite updo, upds in *; desf.
  all: congruence.
Qed.

Lemma rsr_b_exco :
  add_max
    (extra_co_D E_s' lab_s' (loc_s' b_t))
    (A_s' ∩₁ W_s') ≡
      (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
        (eq b_t ∩₁ WCore.lab_is_w l_a).
Proof using SIMREL INV' INV ADD.
  assert (NEQ : a_t <> b_t) by apply INV.
  unfold add_max, extra_co_D.
  rewrite rsr_b_new_exa.
  arewrite (
    (E_s' ∩₁ W_s' ∩₁ Loc_s_' (loc_s' b_t) \₁ eq b_t ∩₁ W_s') ×
      (eq b_t ∩₁ W_s') ≡
        (E_s' ∩₁ W_s' ∩₁ Loc_s_' (loc_s' b_t) \₁ eq b_t) ×
          (eq b_t ∩₁ W_s')
  ).
  { destruct classic with (W_s' b_t) as [ISW|NIS].
    { rewrite set_inter_absorb_r with (s := eq b_t).
      all: basic_solver. }
    arewrite (eq b_t ∩₁ W_s' ≡₁ ∅) by basic_solver.
    now rewrite !cross_false_r. }
  arewrite (
    E_s' ∩₁ W_s' ∩₁ Loc_s_' (loc_s' b_t) \₁ eq b_t ≡₁
      (E_s' \₁ eq b_t) ∩₁ W_s' ∩₁ Loc_s_' (loc_s' b_t)
  ) by basic_solver 11.
  arewrite (E_s' \₁ eq b_t ≡₁ E_s ∪₁ eq a_t).
  { simpl. rewrite !set_minus_union_l, set_minusK.
    rewrite set_union_empty_r, set_minus_disjoint.
    { basic_solver. }
    unfolder. intros x XIN XEQ. subst x.
    auto with xmm. }
  rewrite !set_inter_union_l, rsr_b_isw_helper.
  rewrite rsr_b_exco_helper, set_union_empty_r.
  arewrite (loc_s' b_t = WCore.lab_loc l_a).
  { simpl. unfold loc. rewrite updo, upds by congruence.
    unfold WCore.lab_loc. desf. }
  apply cross_more; [| reflexivity].
  transitivity (
    W_s' ∩₁ Loc_s_' (WCore.lab_loc l_a) ∩₁ E_s
  ); [basic_solver |].
  transitivity (
    W_s ∩₁ Loc_s_ (WCore.lab_loc l_a) ∩₁ E_s
  ); [| basic_solver].
  rewrite !set_interA. split.
  all: rewrite set_inter_loc, set_inter_is_w.
  all: try reflexivity.
  all: try now (
    eapply eq_dom_mori; eauto with xmm;
      red; basic_solver
  ).
  all: symmetry.
  all: try now (
    eapply eq_dom_mori; eauto with xmm;
      red; basic_solver
  ).
Qed.

Lemma rsr_b_sim :
  reord_simrel X_s' X_t' a_t b_t mapper.
Proof using SIMREL INV' INV ADD.
  assert (WF_t : Wf G_t) by apply (rsr_Gt_wf INV).
  assert (NEQ : a_t <> b_t) by apply INV.
  assert (TEQ : tid a_t = tid b_t) by apply INV.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  constructor.
  all: auto with xmm.
  { admit. }
  { rewrite rsr_b_new_exa, rsr_step_acts.
    ins. rewrite set_collect_union, !set_minus_union_l.
    rewrite set_minusK, set_union_empty_r.
    rewrite (rsr_acts SIMREL), rsr_b_old_exa, set_union_empty_r.
    rewrite set_collect_eq, rsr_mapper_bt; auto.
    rewrite set_minus_disjoint; [basic_solver |].
    unfolder. intros x (y & YIN & XEQ) XEQ'. subst x.
    enough (y = a_t) by (desf; auto with xmm).
    apply rsr_mapper_inv_bt with (a_t := a_t) (b_t := b_t).
    all: auto. }
  { eapply eq_dom_mori; auto with xmm.
    red. auto with hahn. }
  { simpl. rewrite rsr_b_new_exa, rsr_step_acts.
    rewrite set_collect_union, set_collect_eq,
            rsr_mapper_bt, (rsr_acts SIMREL),
            rsr_b_old_exa, set_union_empty_r.
    all: basic_solver 7. }
  { admit. }
  { rewrite (WCore.add_event_rf ADD').
    rewrite (add_event_to_rf_complete ADD' WF_t (rsr_Gt_rfc INV)).
    rewrite union_false_r, collect_rel_union.
    rewrite rsr_b_new_exa, rsr_b_isr_helper.
    rewrite rsr_b_samesrf. simpl.
    rewrite (rsr_rf SIMREL), (rf_delta_RE WF_t ADD').
    now rewrite rsr_b_old_exa, set_inter_empty_l, eqv_empty,
                seq_false_r, union_false_r. }
  { rewrite (WCore.add_event_co ADD').
    rewrite rsr_b_exco. simpl.
    rewrite (rsr_co SIMREL), (co_deltaE WF_t ADD').
    rewrite collect_rel_union.
    now rewrite rsr_b_old_exa, set_inter_empty_l,
                add_max_empty_r, union_false_r. }
  { simpl. rewrite (WCore.add_event_threads ADD').
    apply (rsr_threads SIMREL). }
  all: ins.
  all: rewrite ?(WCore.add_event_threads ADD'), ?(WCore.add_event_ctrl ADD'),
               ?(WCore.add_event_threads ADD'), ?(WCore.add_event_addr ADD'),
               ?(WCore.add_event_addr ADD'), ?(WCore.add_event_rmw_dep ADD'),
               ?(WCore.add_event_data ADD'), ?rsr_b_preservedE, ?rsr_a_preservedE.
  all: try now apply SIMREL.
  rewrite rsr_step_acts, !set_minus_union_l.
  apply eq_dom_union. split.
  { intros x XIN. desf. rewrite rsr_mappero.
    all: forward apply XIN; clear; unfold id; basic_solver. }
  arewrite ((eq b_t \₁ eq a_t) \₁ eq b_t ⊆₁ ∅).
  all: basic_solver.
Admitted.

Lemma rsr_new_Gs_wf :
  Wf G_s'.
Proof using b_t a_t ADD SIMREL INV INV'.
  apply (G_s_wf INV' rsr_b_sim).
Qed.

Lemma rsr_new_Gs_cons :
  WCore.is_cons G_s'.
Proof using b_t a_t CONS ADD SIMREL INV INV'.
  apply (rsr_cons INV' CONS rsr_b_sim).
Qed.

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

Lemma rsr_b_srf_exists :
  exists w,
    fake_srf G_s b_t l_a ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ ≡
      eq_opt w × eq b_t.
Proof using ADD SIMREL INV INV'.
  destruct fake_srf_exists
      with (G_s := G_s) (e := b_t) (l_e := l_a)
        as [w SRF].
  all: auto with xmm.
  exists w. rewrite SRF.
  clear. basic_solver 11.
Qed.

Lemma rsr_b_imm_fin : set_finite (E_s'' \₁ is_init).
Proof using ADD SIMREL INV INV'.
  simpl. rewrite set_minus_union_l, set_unionC.
  apply set_finite_union. split.
  { eapply set_finite_mori; auto with hahn.
    red. basic_solver. }
  apply (rsr_fin_s INV SIMREL).
Qed.

Lemma rsr_b_srf_exists_helper w
    (ISR : R_s'' b_t)
    (SRF : srf_s'' w b_t) :
  fake_srf G_s b_t l_a ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ ≡
    eq w × eq b_t.
Proof using ADD SIMREL INV INV'.
  rewrite <- rsr_b_fakesrf.
  arewrite (eq b_t ∩₁ WCore.lab_is_r l_a ≡₁ eq b_t).
  { rewrite set_inter_absorb_r; [reflexivity |].
    intros x XEQ. subst x. unfold WCore.lab_is_r, is_r in *.
    simpl in ISR. rewrite upds in ISR. desf. }
  split; [| basic_solver].
  intros w' y (y' & SRF' & (EQ1 & EQ2)).
  subst y y'. red. split; auto.
  apply (wf_srff rsr_imm_Gs_wf) with b_t.
  all: red; auto.
Qed.

Lemma rsr_b_srf_exists'
    (ISR : R_s'' b_t) :
  exists w,
    fake_srf G_s b_t l_a ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ ≡
      eq w × eq b_t.
Proof using ADD SIMREL INV INV'.
  assert (EQ : exists ll, WCore.lab_loc l_a = Some ll).
  { unfold is_r in ISR. simpl in ISR. rewrite upds in ISR.
    unfold WCore.lab_loc. desf. eauto. }
  destruct EQ as [ll EQ].
  destruct srf_exists
      with (G := G_s'') (r := b_t) (l := ll)
        as [w SRF].
  all: auto with xmm.
  all: try now apply rsr_imm_Gs_wf.
  { simpl. basic_solver. }
  { simpl. unfold loc. rewrite upds.
    unfold WCore.lab_loc in EQ. desf. }
  { apply rsr_b_imm_fin. }
  exists w.
  now apply rsr_b_srf_exists_helper.
Qed.

Lemma rsr_b_co_delta :
  WCore.co_delta b_t ∅
    (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a) ∩₁ WCore.lab_is_w l_a) ≡
      (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
        (eq b_t ∩₁ WCore.lab_is_w l_a).
Proof using.
  unfold WCore.co_delta.
  rewrite cross_false_r, union_false_l.
  unfold WCore.lab_is_w.
  destruct l_a.
  all: rewrite ?set_inter_empty_r.
  all: try now rewrite cross_false_r, cross_false_l.
  now rewrite !set_inter_full_r.
Qed.

Lemma rsr_b_step1 :
  WCore.add_event X_s X_s'' b_t l_a.
Proof using ADD SIMREL INV INV'.
  assert (NEQ : a_t <> b_t) by apply INV.
  destruct rsr_b_srf_exists as [w SRF].
  exists None, ∅, w, ∅,
    (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a) ∩₁ WCore.lab_is_w l_a).
  apply add_event_to_wf.
  all: auto with xmm.
  { simpl. rewrite SRF. basic_solver. }
  { simpl. now rewrite rsr_b_co_delta. }
  { simpl. rewrite (rsr_rmw SIMREL).
    unfold WCore.rmw_delta. basic_solver 7. }
  { apply rsr_new_a_sb. }
  simpl.
  now rewrite (rsr_ctrl SIMREL), (rsr_nctrl INV).
Qed.

Lemma rsr_b_step2 :
  WCore.add_event X_s'' X_s' a_t l_b.
Proof using ADD SIMREL INV INV'.
  assert (WF_t : Wf G_t) by apply (rsr_Gt_wf INV).
  assert (NEQ : a_t <> b_t) by apply INV.
  destruct ADD as (r & R1 & w & W1 & W2 & ADD').
  exists (option_map mapper r), ∅,
        (option_map mapper w), (mapper ↑₁ W1), (mapper ↑₁ W2).
  apply add_event_to_wf.
  all: auto with xmm.
  { apply (rsr_at_tid INV). }
  { simpl. rewrite <- rsr_b_fakesrf.
    rewrite (rf_delta_RE WF_t ADD').
    rewrite mapped_rf_delta_R, rsr_mapper_bt; auto.
    basic_solver 7. }
  { simpl. rewrite <- rsr_b_co_delta.
    rewrite (co_deltaE WF_t ADD').
    rewrite mapped_co_delta, rsr_mapper_bt; auto.
    basic_solver 11. }
  { simpl. rewrite (WCore.add_event_rmw ADD'), collect_rel_union.
    rewrite mapped_rmw_delta, rsr_mapper_bt; auto. }
  { apply rsr_new_a_sb'. }
  now rewrite (rsr_ctrl SIMREL), (rsr_nctrl INV).
Qed.

Lemma rsr_b_imm_rfc : rf_complete G_s''.
Proof using ADD SIMREL INV INV'.
  assert (RFC : rf_complete G_s).
  { apply (G_s_rfc INV SIMREL). }
  unfold rf_complete. simpl.
  rewrite set_inter_union_l, codom_union.
  arewrite (eq b_t ∩₁ R_s'' ≡₁ eq b_t ∩₁ WCore.lab_is_r l_a).
  { clear. simpl. unfolder. split; intros x (XEQ & ISR).
    all: subst x; split; auto.
    all: unfold is_r, WCore.lab_is_r in *; rewrite upds in *.
    all: desf. }
  apply set_subset_union.
  { red in RFC. rewrite <- RFC, set_interC.
    rewrite set_inter_is_r
       with (G := G_s) (G' := G_s'') (s' := E_s).
    all: auto with hahn xmm.
    basic_solver. }
  intros x (XEQ & ISR'). subst x.
  assert (ISR : R_s'' b_t).
  { unfold is_r, WCore.lab_is_r in *. simpl.
    rewrite upds. desf. }
  destruct (rsr_b_srf_exists' ISR)
        as [w SRF].
  exists w. apply SRF. basic_solver.
Qed.

Lemma simrel_exec_b_step_1 :
    WCore.exec_inst X_s  X_s'' b_t l_a.
Proof using ADD SIMREL INV INV' CONS.
  constructor.
  { apply rsr_b_step1. }
  { apply rsr_b_imm_rfc. }
  apply rsr_imm_Gs_cons.
Qed.

Lemma simrel_exec_b_step_2 :
    WCore.exec_inst X_s'' X_s' a_t l_b.
Proof using ADD SIMREL INV INV' CONS.
  constructor.
  { apply rsr_b_step2. }
  { apply (G_s_rfc INV' rsr_b_sim). }
  apply rsr_new_Gs_cons.
Qed.

End ExecB.