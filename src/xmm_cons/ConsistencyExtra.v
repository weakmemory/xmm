Require Import Setoid Program.Basics.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel3 AuxInj.
Require Import Srf Rhb.
Require Import ConsistencyCommon ConsistencyMonotonicity.
Require Import MapDoms.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco SubExecution.
Require Import xmm_s_hb.

Open Scope program_scope.

Set Implicit Arguments.

Module XmmCons.

Section ConsistencyExtra.

Variable G_s G_t : execution.
Variable sc_s sc_t : relation actid.
Variable m : actid -> actid.

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'W_s'" := (fun a => is_true (is_w lab_s a)).
Notation "'R_s'" := (fun a => is_true (is_r lab_s a)).
Notation "'F_s'" := (fun a => is_true (is_f lab_s a)).
Notation "'R_ex_s'" := (fun a => is_true (R_ex lab_s a)).
Notation "'Rel_s'" := (fun a => is_true (is_rel lab_s a)).
Notation "'Acq_s'" := (fun a => is_true (is_acq lab_s a)).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).
Notation "'release_s'" := (release G_s).
Notation "'rs_s'" := (rs G_s).
Notation "'hb_s'" := (hb G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'eco_s'" := (eco G_s).
Notation "'psc_s'" := (imm.psc G_s).
Notation "'fr_s'" := (fr G_s).
Notation "'sw_s'" := (sw G_s).
Notation "'data_s'" := (data G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'W_t'" := (fun a => is_true (is_w lab_t a)).
Notation "'R_t'" := (fun a => is_true (is_r lab_t a)).
Notation "'F_t'" := (fun a => is_true (is_f lab_t a)).
Notation "'R_ex_t'" := (fun a => is_true (R_ex lab_t a)).
Notation "'Rel_t'" := (fun a => is_true (is_rel lab_t a)).
Notation "'Acq_t'" := (fun a => is_true (is_acq lab_t a)).
Notation "'Rlx_t'" := (fun e => is_true (is_rlx lab_t e)).
Notation "'release_t'" := (release G_t).
Notation "'rs_t'" := (rs G_t).
Notation "'hb_t'" := (hb G_t).
Notation "'rhb_t'" := (rhb G_t).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'vf_t'" := (vf G_t).
Notation "'srf_t'" := (srf G_t).
Notation "'eco_t'" := (eco G_t).
Notation "'psc_t'" := (imm.psc G_t).
Notation "'fr_t'" := (fr G_t).
Notation "'sw_t'" := (sw G_t).
Notation "'data_t'" := (data G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).

Hypothesis (EQE : E_s ≡₁ E_t).
Hypothesis (RF : rf_s ≡ rf_t).
Hypothesis (CO : co_s ≡ co_t).
Hypothesis (RMW : rmw_s ≡ rmw_t).
Hypothesis (THRS : threads_set G_s ≡₁ threads_set G_t).
Hypothesis (LAB : eq_dom E_t lab_s lab_t).
Hypothesis (DATA : data_s ≡ data_t).
Hypothesis (ADDR : addr_s ≡ addr_t).
Hypothesis (CTRL : ctrl_s ≡ ctrl_t).
Hypothesis (RMWD : rmw_dep_s ≡ rmw_dep_t).
Hypothesis (INI : is_init ⊆₁ E_t).
Hypothesis (WF_t : Wf G_t).

Lemma consistency_wf_help_sb : sb_s ≡ sb_t.
Proof using EQE.
  unfold sb. now rewrite EQE.
Qed.

Lemma consistency_wf_help : Wf G_s.
Proof using THRS EQE RF CO RMW LAB DATA ADDR CTRL RMWD WF_t INI.
  constructor.
  { intros a b (AIN & BIN & NEQ & TEQ & NIN).
    apply (wf_index WF_t); splits; auto.
    all: now apply EQE. }
  all: rewrite 1?consistency_wf_help_sb, 1?DATA,
               1?EQE, 1?RF, 1?CO, 1?RMW, 1?ADDR,
               1?CTRL, 1?RMWD.
  all: try now apply WF_t.
  { split; [| basic_solver].
    rewrite (wf_dataE WF_t) at 2.
    rewrite !seqA. seq_rewrite (seq_eqvC E_t W_s).
    seq_rewrite <- !id_inter.
    rewrite <- set_inter_is_r with (G' := G_t),
            <- set_inter_is_w with (G' := G_t).
    all: auto.
    rewrite (wf_dataD WF_t), (wf_dataE WF_t) at 1.
    basic_solver. }
  { split; [| basic_solver].
    rewrite (wf_addrE WF_t) at 2.
    rewrite !seqA. seq_rewrite (seq_eqvC E_t (R_s ∪₁ W_s)).
    seq_rewrite <- !id_inter. rewrite set_inter_union_l.
    rewrite <- set_inter_is_r with (G' := G_t),
            <- set_inter_is_w with (G' := G_t).
    all: auto.
    rewrite (wf_addrD WF_t), (wf_addrE WF_t) at 1.
    basic_solver. }
  { split; [| basic_solver].
    rewrite (wf_ctrlE WF_t) at 2.
    seq_rewrite <- !id_inter.
    rewrite <- set_inter_is_r with (G' := G_t).
    all: auto.
    rewrite (wf_ctrlD WF_t), (wf_ctrlE WF_t) at 1.
    basic_solver. }
  { split; [| basic_solver].
    rewrite (wf_rmwE WF_t) at 2.
    rewrite !seqA. seq_rewrite (seq_eqvC E_t W_s).
    seq_rewrite <- !id_inter.
    rewrite <- set_inter_is_r with (G' := G_t),
            <- set_inter_is_w with (G' := G_t).
    all: auto.
    rewrite (wf_rmwD WF_t), (wf_rmwE WF_t) at 1.
    basic_solver. }
  { apply inclusion_sameloc with (G' := G_t) (s := E_t) (s' := E_s).
    all: rewrite 1?EQE; auto with hahn.
    { apply WF_t. }
    apply dom_helper_3, (wf_rmwE WF_t). }
  { split; [| basic_solver].
    rewrite (wf_rfE WF_t) at 2.
    rewrite !seqA. seq_rewrite (seq_eqvC E_t R_s).
    seq_rewrite <- !id_inter.
    rewrite <- set_inter_is_r with (G' := G_t),
            <- set_inter_is_w with (G' := G_t).
    all: auto.
    rewrite (wf_rfD WF_t), (wf_rfE WF_t) at 1.
    basic_solver. }
  { apply inclusion_sameloc with (G' := G_t) (s := E_t) (s' := E_s).
    all: rewrite 1?EQE; auto with hahn.
    { apply WF_t. }
    apply dom_helper_3, (wf_rfE WF_t). }
  { apply inclusion_sameval with (G' := G_t) (s := E_t) (s' := E_s).
    all: rewrite 1?EQE; auto with hahn.
    { apply WF_t. }
    apply dom_helper_3, (wf_rfE WF_t). }
  { split; [| basic_solver].
    rewrite (wf_coE WF_t) at 2.
    rewrite !seqA. seq_rewrite (seq_eqvC E_t W_s).
    seq_rewrite <- !id_inter.
    rewrite <- set_inter_is_w with (G' := G_t).
    all: auto.
    rewrite (wf_coD WF_t), (wf_coE WF_t) at 1.
    basic_solver. }
  { apply inclusion_sameloc with (G' := G_t) (s := E_t) (s' := E_s).
    all: rewrite 1?EQE; auto with hahn.
    { apply WF_t. }
    apply dom_helper_3, (wf_coE WF_t). }
  { intro ol.
    rewrite set_interA.
    rewrite set_interC with (s := E_s).
    rewrite set_interA.
    rewrite set_inter_loc with (G := G_t),
            set_inter_is_w with (G := G_t) (s' := E_s).
    { rewrite CO, <- set_interA, EQE,
              set_interC with (s' := E_t),
              <- set_interA.
      apply WF_t. }
    all: auto.
    { basic_solver. }
    all: symmetry; rewrite EQE; apply LAB. }
  { intros l (b & BIN & LOC).
    apply EQE, (wf_init WF_t).
    apply EQE in BIN. exists b. splits; auto.
    unfold loc in *. rewrite <- LAB; auto. }
  { intro l. rewrite LAB; [apply WF_t |].
    now apply INI. }
  { split; [| basic_solver].
    rewrite (wf_rmw_depE WF_t) at 2.
    rewrite !seqA. seq_rewrite (seq_eqvC E_t R_ex_s).
    seq_rewrite <- !id_inter.
    rewrite <- set_inter_is_r with (G' := G_t),
            <- set_inter_Rex with (G' := G_t).
    all: auto.
    rewrite (wf_rmw_depD WF_t), (wf_rmw_depE WF_t) at 1.
    basic_solver. }
  intros e EIN. apply EQE in EIN.
  now apply THRS, WF_t.
Qed.

Lemma consistency_swap_lab_rpo :
  rpo_s ⊆ rpo_t.
Proof using THRS EQE RF CO RMW LAB DATA ADDR CTRL RMWD WF_t INI.
  unfold rpo. apply clos_trans_mori.
  unfold rpo_imm. rewrite wf_sbE, !seqA.
  seq_rewrite (seq_eqvC E_s (F_s ∩₁ Acq_s)).
  seq_rewrite (seq_eqvC E_s Rel_s).
  seq_rewrite (seq_eqvC E_s (W_s ∩₁ Rlx_s)).
  seq_rewrite <- !id_inter. rewrite !set_interA.
  rewrite EQE, consistency_wf_help_sb.
  rewrite set_inter_acq with (G := G_t),
          set_inter_rel with (G := G_t),
          set_inter_rlx with (G := G_t).
  all: auto; try now symmetry.
  rewrite set_inter_is_r with (G := G_t),
          set_inter_is_w with (G := G_t),
          !set_inter_is_f with (G := G_t) (G' := G_s).
  { repeat apply union_mori; basic_solver. }
  all: auto.
  all: symmetry; eapply eq_dom_mori; eauto.
  all: red; basic_solver.
Qed.

Lemma consistency_swap_lab
    (CONS : WCore.is_cons G_t) :
  WCore.is_cons G_s.
Proof using THRS EQE RF CO RMW LAB DATA ADDR CTRL RMWD WF_t INI.
  apply XmmCons.monoton_cons with (m := id) (G_t := G_t).
  { basic_solver. }
  all: rewrite 1?set_collect_id, 1?collect_rel_id.
  all: auto with hahn.
  { apply EQE. }
  { apply consistency_swap_lab_rpo. }
  { apply RF. }
  { apply CO. }
  { apply RMW. }
  { rewrite consistency_wf_help_sb.
    rewrite <- interK with (r := sb_t) at 1.
    rewrite interA.
    enough (SBSL : sb_t ∩ same_loc_s ⊆ same_loc_t).
    { now rewrite SBSL. }
    apply inclusion_sameloc with (G' := G_s) (s := E_t) (s' := E_s).
    all: rewrite 1?EQE; auto with hahn.
    { now symmetry. }
    rewrite wf_sbE. basic_solver. }
  apply consistency_wf_help.
Qed.

Lemma consistency_subexec
    (CONS : WCore.is_cons G_t)
    (SUB : sub_execution G_t G_s sc_t sc_s) :
  WCore.is_cons G_s.
Proof using.
  constructor.
  { rewrite (sub_hb_in SUB), (sub_eco_in SUB).
    apply CONS. }
  split; [| basic_solver].
  rewrite (sub_rmw_in SUB), (sub_fr_in SUB),
          (sub_co_in SUB).
  apply CONS.
Qed.

End ConsistencyExtra.

End XmmCons.