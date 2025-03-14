Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2 AuxInj.
Require Import SimrelCommon ReordSimrel ReorderingEq.
Require Import Rhb.
Require Import MapDoms.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Set Implicit Arguments.

Section ReordRpo.

Variable G G' : execution.
Variable a b : actid.
Variable mapper : actid -> actid.

Notation "'lab''" := (lab G').
Notation "'loc''" := (loc lab').
Notation "'val''" := (val lab').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'data''" := (data G').
Notation "'ctrl''" := (ctrl G').
Notation "'addr''" := (addr G').
Notation "'W''" := (fun e => is_true (is_w lab' e)).
Notation "'R''" := (fun e => is_true (is_r lab' e)).
Notation "'F''" := (fun e => is_true (is_f lab' e)).
Notation "'Loc_'' l" := (fun e => loc' e = l) (at level 1).
Notation "'Val_'' l" := (fun e => val' e = l) (at level 1).
Notation "'same_loc''" := (same_loc lab').
Notation "'same_val''" := (same_val lab').
Notation "'Acq''" := (fun e => is_true (is_acq lab' e)).
Notation "'Rel''" := (fun e => is_true (is_rel lab' e)).
Notation "'Rlx''" := (fun e => is_true (is_rlx lab' e)).
Notation "'rpo_imm''" := (rpo_imm G').
Notation "'rpo''" := (rpo G').

Notation "'lab'" := (lab G).
Notation "'val'" := (val lab).
Notation "'loc'" := (loc lab).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'data'" := (data G).
Notation "'ctrl'" := (ctrl G).
Notation "'addr'" := (addr G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'R'" := (fun e => is_true (is_r lab e)).
Notation "'F'" := (fun e => is_true (is_f lab e)).
Notation "'Loc_' l" := (fun e => loc e = l) (at level 1).
Notation "'Val_' l" := (fun e => val e = l) (at level 1).
Notation "'same_loc'" := (same_loc lab).
Notation "'same_val'" := (same_val lab).
Notation "'Acq'" := (fun e => is_true (is_acq lab e)).
Notation "'Rel'" := (fun e => is_true (is_rel lab e)).
Notation "'Rlx'" := (fun e => is_true (is_rlx lab e)).
Notation "'rpo_imm'" := (rpo_imm G).
Notation "'rpo'" := (rpo G).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Lemma reord_rpo_imm_emp
    (BNAQ : eq b ⊆₁ set_compl Acq')
    (ANREL : eq a ⊆₁ set_compl Rel')
    (ARW : eq a ⊆₁ R' ∪₁ W')
    (BRW : eq b ⊆₁ R' ∪₁ W')
    (SBFROMB : ⦗eq b⦘ ⨾ sb' ⊆ eq b × eq a) :
  ⦗eq b⦘ ⨾ rpo_imm' ⊆ ∅₂.
Proof using.
  unfold rpo_imm. rewrite !seq_union_r.
  seq_rewrite !(seq_eqvC (eq b)). rewrite !seqA.
  sin_rewrite !SBFROMB.
  rewrite <- !cross_inter_r, <- !cross_inter_l.
  repeat apply inclusion_union_l.
  { rewrite ARW. clear.
    unfold is_r, is_w, is_f.
    basic_solver. }
  { rewrite BNAQ. clear. basic_solver. }
  { rewrite ANREL. clear. basic_solver. }
  rewrite BRW. clear.
  unfold is_r, is_w, is_f.
  basic_solver.
Qed.

Lemma reord_rpo_emp
    (BNAQ : eq b ⊆₁ set_compl Acq')
    (ANREL : eq a ⊆₁ set_compl Rel')
    (ARW : eq a ⊆₁ R' ∪₁ W')
    (BRW : eq b ⊆₁ R' ∪₁ W')
    (SBFROMB : ⦗eq b⦘ ⨾ sb' ⊆ eq b × eq a) :
  ⦗eq b⦘ ⨾ rpo' ⊆ ∅₂.
Proof using.
  unfold rpo. rewrite ct_begin.
  sin_rewrite reord_rpo_imm_emp; auto.
  now rewrite seq_false_l.
Qed.

Lemma reord_rpo_imm_start
    (WF : Wf G')
    (BIN : E' b)
    (BNAQ : eq b ⊆₁ set_compl Acq')
    (ANREL : eq a ⊆₁ set_compl Rel')
    (ARW : eq a ⊆₁ R' ∪₁ W')
    (BRW : eq b ⊆₁ R' ∪₁ W')
    (SBFROMB : ⦗eq b⦘ ⨾ sb' ⊆ eq b × eq a) :
  rpo_imm' ⨾ ⦗E' \₁ eq b⦘ ⊆
    ⦗E' \₁ eq b⦘ ⨾ rpo_imm' ⨾ ⦗E' \₁ eq b⦘.
Proof using.
  transitivity (
    ⦗E'⦘ ⨾ rpo_imm' ⨾ ⦗E' \₁ eq b⦘
  ).
  { rewrite (wf_rpo_immE WF) at 1. basic_solver. }
  rewrite set_union_minus
     with (s := E') (s' := eq b)
       at 1; [| basic_solver].
  rewrite id_union, !seq_union_l.
  apply inclusion_union_l; [reflexivity |].
  sin_rewrite reord_rpo_imm_emp; auto.
  now rewrite seq_false_l.
Qed.

Lemma reord_map_rpo_helper
    (INJ : inj_dom E mapper)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  ⦗R' ∩₁ Rlx'⦘ ⨾ mapper ↑ sb ⨾ ⦗F' ∩₁ Acq'⦘ ∪
    ⦗Acq'⦘ ⨾ mapper ↑ sb ∪
      mapper ↑ sb ⨾ ⦗Rel'⦘ ∪
        ⦗F' ∩₁ Rel'⦘ ⨾ mapper ↑ sb ⨾ ⦗W' ∩₁ Rlx'⦘ ⊆
  mapper ↑ rpo.
Proof using.
  rewrite wf_sbE, !collect_rel_seqi, !seqA.
  rewrite collect_rel_eqv.
  seq_rewrite (seq_eqvC (mapper ↑₁ E) (W' ∩₁ Rlx')).
  seq_rewrite (seq_eqvC (mapper ↑₁ E) (F' ∩₁ Acq')).
  seq_rewrite (seq_eqvC (mapper ↑₁ E) Rel').
  seq_rewrite <- !id_inter. rewrite !set_interA.
  rewrite set_collect_rlx, set_collect_acq,
          set_collect_rel; eauto.
  rewrite set_collect_is_r, set_collect_is_w,
          2!set_collect_is_f; eauto.
  all: try basic_solver 2.
  unfold rpo, rpo_imm. rewrite <- ct_step.
  rewrite !collect_rel_union.
  repeat apply union_mori.
  all: rewrite <- !collect_rel_eqv.
  all: rewrite <- !collect_rel_seq.
  all: try (rewrite 1?wf_sbE; eapply inj_dom_mori;
        eauto; red; basic_solver).
  all: apply collect_rel_mori; auto.
  all: basic_solver.
Qed.

Lemma reord_map_rpo
    (WF' : Wf G')
    (BIN : E' b)
    (MAPIN : E' \₁ eq b ⊆₁ mapper ↑₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper))
    (INJ : inj_dom E mapper)
    (BNAQ : eq b ⊆₁ set_compl Acq')
    (ANREL : eq a ⊆₁ set_compl Rel')
    (ARW : eq a ⊆₁ R' ∪₁ W')
    (BRW : eq b ⊆₁ R' ∪₁ W')
    (SBFROMB : ⦗eq b⦘ ⨾ sb' ⊆ eq b × eq a)
    (SBSUB : ⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘ ⊆
                ⦗E' \₁ eq b⦘ ⨾ mapper ↑ sb ⨾ ⦗E' \₁ eq b⦘) :
  rpo' ⨾ ⦗E' \₁ eq b⦘ ⊆ mapper ↑ rpo.
Proof using.
  arewrite (rpo' ⊆ ⦗E'⦘ ⨾ rpo').
  { rewrite wf_rpoE. basic_solver. }
  transitivity (⦗E' \₁ eq b⦘ ⨾ rpo' ⨾ ⦗E' \₁ eq b⦘).
  { rewrite set_union_minus
       with (s := E') (s' := eq b)
         at 1; [| basic_solver].
    rewrite id_union, !seq_union_l.
    apply inclusion_union_l; [reflexivity |].
    sin_rewrite reord_rpo_emp; auto.
    now rewrite seq_false_l. }
  unfold rpo at 1.
  transitivity ((⦗E' \₁ eq b⦘ ⨾ rpo_imm' ⨾ ⦗E' \₁ eq b⦘)⁺).
  { rewrite ct_l_upward_closed.
    { rewrite reord_rpo_imm_start at 1; auto.
      basic_solver. }
    unfold upward_closed. intros x y RPOIMM YIN.
    split.
    { apply (wf_rpo_immE WF') in RPOIMM.
      unfolder in RPOIMM; desf. }
    intro FALSO; subst x.
    eapply reord_rpo_imm_emp; auto.
    basic_solver. }
  assert (IND1 : (⦗E' \₁ eq b⦘ ⨾ rpo_imm' ⨾ ⦗E' \₁ eq b⦘) ⊆ mapper ↑ rpo).
  { rewrite <- reord_map_rpo_helper; auto.
    unfold rpo_imm.
    rewrite !seq_union_l, !seq_union_r, !seqA.
    seq_rewrite (seq_eqvC (E' \₁ eq b) (R' ∩₁ Rlx')).
    seq_rewrite (seq_eqvC (F' ∩₁ Acq') (E' \₁ eq b)).
    seq_rewrite (seq_eqvC (E' \₁ eq b) Acq').
    seq_rewrite (seq_eqvC Rel' (E' \₁ eq b)).
    seq_rewrite (seq_eqvC (W' ∩₁ Rlx') (E' \₁ eq b)).
    seq_rewrite (seq_eqvC (E' \₁ eq b) (F' ∩₁ Rel')).
    rewrite !seqA. sin_rewrite !SBSUB. rewrite !seqA.
    repeat apply union_mori; clear; basic_solver 11. }
  apply inclusion_t_ind_right; vauto.
  rewrite IND1. unfold rpo.
  rewrite <- collect_rel_seq, ct_ct; [reflexivity |].
  eapply inj_dom_mori; eauto.
  red. change rpo_imm⁺ with rpo.
  rewrite wf_rpoE. basic_solver.
Qed.

Lemma reord_ab_loc
    (NLOC : ~same_loc' b a)
    (SBFROMB : ⦗eq b⦘ ⨾ sb' ⊆ eq b × eq a) :
  ⦗eq b⦘ ⨾ sb' ∩ same_loc' ⊆ ∅₂.
Proof using.
  rewrite <- seq_eqv_inter_ll, SBFROMB.
  basic_solver.
Qed.

Lemma reord_ab_loc_codom
    (NLOC : ~same_loc' b a)
    (SBFROMB : ⦗eq b⦘ ⨾ sb' ⊆ eq b × eq a) :
  codom_rel (⦗eq b⦘ ⨾ sb' ∩ same_loc') ≡₁ ∅.
Proof using.
  split; [| auto with hahn].
  rewrite reord_ab_loc; auto; basic_solver.
Qed.

Lemma reord_sbloc_to_nb
    (BIN : E' b)
    (NLOC : ~same_loc' b a)
    (INJ : inj_dom E mapper)
    (MAPIN : E' \₁ eq b ⊆₁ mapper ↑₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper))
    (SBFROMB : ⦗eq b⦘ ⨾ sb' ⊆ eq b × eq a)
    (SBSUB : ⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘ ⊆
                ⦗E' \₁ eq b⦘ ⨾ mapper ↑ sb ⨾ ⦗E' \₁ eq b⦘) :
  sb' ∩ same_loc' ⨾ ⦗E' \₁ eq b⦘ ⊆
    mapper ↑ (sb ∩ same_loc).
Proof using.
  rewrite <- seq_eqv_inter_lr.
  arewrite (sb' ⨾ ⦗E' \₁ eq b⦘ ⊆ ⦗E'⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘).
  { rewrite wf_sbE at 1. basic_solver. }
  rewrite set_union_minus
      with (s := E') (s' := eq b)
        at 1; [| basic_solver].
  rewrite id_union, !seq_union_l, inter_union_l.
  arewrite_false ((⦗eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘) ∩ same_loc').
  { rewrite <- seqA, seq_eqv_inter_lr.
    rewrite seq_eqv_inter_ll, reord_ab_loc.
    all: auto.
    now rewrite seq_false_l. }
  rewrite union_false_r, SBSUB, MAPIN.
  rewrite seq_eqv_inter_ll, seq_eqv_inter_lr.
  rewrite <- seq_eqv_inter_rr, <- seq_eqv_inter_rl.
  arewrite (
    ⦗mapper ↑₁ E⦘ ⨾ same_loc' ⨾ ⦗mapper ↑₁ E⦘ ⊆
      mapper ↑ (⦗E⦘ ⨾ same_loc ⨾ ⦗E⦘)
  ).
  { unfolder. intros x' y' ((x & XIN & XEQ) & LOC & (y & YIN & YEQ)).
    subst x' y'. exists x, y. splits; auto.
    unfold same_loc, loc in *.
    rewrite !LABEQ; auto. }
  rewrite <- collect_rel_interE.
  { apply collect_rel_mori; auto. basic_solver. }
  eapply inj_dom_mori; eauto.
  rewrite wf_sbE. red. basic_solver.
Qed.

Lemma rsr_sb_nexa
    (SB : sb' ≡
      mapper ↑ swap_rel sb (eq b ∩₁ E) (eq a ∩₁ E) ∪
      (mapper ↑₁ dom_rel (sb ⨾ ⦗eq b⦘)) × eq b ∪
      eq b × eq a)
    (NINA : ~E a)
    (INB : E b) :
  ⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘ ⊆
    ⦗E' \₁ eq b⦘ ⨾ mapper ↑ sb ⨾ ⦗E' \₁ eq b⦘.
Proof using.
  rewrite SB, !seq_union_l, !seq_union_r.
  arewrite (eq a ∩₁ E ≡₁ ∅) by basic_solver.
  rewrite swap_rel_empty_r.
  rewrite <- !cross_inter_r, <- !cross_inter_l.
  arewrite (eq b ∩₁ (E' \₁ eq b) ≡₁ ∅) by basic_solver.
  arewrite ((E' \₁ eq b) ∩₁ eq b ≡₁ ∅) by basic_solver.
  rewrite cross_false_r, cross_false_l.
  now rewrite !union_false_r.
Qed.

Lemma reord_rpo_map'
    (WF' : Wf G')
    (MAPIN : E' ⊆₁ mapper ↑₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper))
    (INJ : inj_dom E mapper)
    (SB : sb' ≡ mapper ↑ swap_rel sb (eq b ∩₁ E) (eq a ∩₁ E))
    (ANAQ : eq a ∩₁ E ⊆₁ set_compl Acq)
    (BNREL : eq b ∩₁ E ⊆₁ set_compl Rel)
    (ARW : eq a ∩₁ E ⊆₁ R ∪₁ W)
    (BRW : eq b ∩₁ E ⊆₁ R ∪₁ W) :
  rpo' ⊆ mapper ↑ rpo.
Proof using.
  assert (IND1 : rpo_imm' ⊆ mapper ↑ rpo).
  { unfold rpo_imm.
    rewrite SB. unfold swap_rel.
    arewrite !(sb \ (eq b ∩₁ E) × (eq a ∩₁ E) ⊆ sb).
    rewrite !collect_rel_union, !seq_union_l, !seq_union_r.
    arewrite_false (mapper ↑ (eq a ∩₁ E) × (eq b ∩₁ E) ⨾ ⦗F' ∩₁ Acq'⦘).
    { rewrite collect_rel_cross. seq_rewrite <- cross_inter_r.
      arewrite (mapper ↑₁ (eq b ∩₁ E) ∩₁ (F' ∩₁ Acq') ⊆₁ ∅);
        [| basic_solver].
      rewrite set_interC with (s := F'), set_interC.
      rewrite set_interA, set_collect_is_f, BRW; try basic_solver.
      clear. unfold is_r, is_w, is_f. basic_solver. }
    arewrite_false (⦗Acq'⦘ ⨾ mapper ↑ (eq a ∩₁ E) × (eq b ∩₁ E)).
    { rewrite collect_rel_cross. seq_rewrite <- cross_inter_l.
      arewrite (Acq' ∩₁ mapper ↑₁ (eq a ∩₁ E) ⊆₁ ∅);
        [| basic_solver].
      rewrite set_collect_acq, ANAQ; basic_solver. }
    arewrite_false (mapper ↑ (eq a ∩₁ E) × (eq b ∩₁ E) ⨾ ⦗Rel'⦘).
    { rewrite collect_rel_cross. seq_rewrite <- cross_inter_r.
      arewrite (mapper ↑₁ (eq b ∩₁ E) ∩₁ Rel' ⊆₁ ∅);
        [| basic_solver].
      rewrite set_interC with (s' := Rel').
      rewrite set_collect_rel, BNREL; basic_solver. }
    arewrite_false (⦗F' ∩₁ Rel'⦘ ⨾ mapper ↑ (eq a ∩₁ E) × (eq b ∩₁ E)).
    { rewrite collect_rel_cross. seq_rewrite <- cross_inter_l.
      arewrite ((F' ∩₁ Rel') ∩₁ mapper ↑₁ (eq a ∩₁ E) ⊆₁ ∅);
        [| basic_solver].
      rewrite set_interC with (s := F').
      rewrite set_interA, set_collect_is_f, ARW; try basic_solver.
      clear. unfold is_r, is_w, is_f. basic_solver. }
    rewrite seq_false_r, seq_false_l, !union_false_r.
    rewrite <- reord_map_rpo_helper; auto.
    repeat apply union_mori; clear; basic_solver 11. }
  apply inclusion_t_ind_right; vauto.
  rewrite IND1. unfold rpo.
  rewrite <- collect_rel_seq, ct_ct; [reflexivity |].
  eapply inj_dom_mori; eauto.
  red. change rpo_imm⁺ with rpo.
  rewrite wf_rpoE. basic_solver.
Qed.

Lemma reord_map_sloc r
    (SUB : r ⊆ E × E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  same_loc' ∩ mapper ↑ r ⊆ mapper ↑ (same_loc ∩ r).
Proof using.
  unfolder. intros x' y' (LOC & (x & y & REL & XEQ & YEQ)).
  subst x' y'. exists x, y; splits; auto.
  unfold same_loc, loc in *. rewrite !LABEQ; auto.
  all: apply SUB in REL; red in REL; desf.
Qed.

Lemma reord_sbloc'
    (NLOC : ⦗eq a ∩₁ E⦘ ⨾ same_loc ⨾ ⦗eq b ∩₁ E⦘ ⊆ ∅₂)
    (MAPIN : E' ⊆₁ mapper ↑₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper))
    (SB : sb' ≡ mapper ↑ swap_rel sb (eq b ∩₁ E) (eq a ∩₁ E)) :
  sb' ∩ same_loc' ⊆ mapper ↑ (sb ∩ same_loc).
Proof using.
  rewrite interC with (r2 := same_loc), interC with (r2 := same_loc').
  rewrite SB, reord_map_sloc; auto; [| rewrite wf_sbE; basic_solver].
  unfold swap_rel. rewrite inter_union_r, collect_rel_union.
  arewrite (same_loc ∩ (sb \ (eq b ∩₁ E) × (eq a ∩₁ E)) ⊆ same_loc ∩ sb).
  apply inclusion_union_l; [reflexivity | ].
  arewrite (same_loc ∩ (eq a ∩₁ E) × (eq b ∩₁ E) ⊆
    ⦗eq a ∩₁ E⦘ ⨾ same_loc ⨾ ⦗eq b ∩₁ E⦘) by basic_solver.
  rewrite NLOC, collect_rel_empty. basic_solver.
Qed.

End ReordRpo.

Section NRpo.

Variable X_s X_t : WCore.t.
Variable a_t b_t : actid.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rhb_t'" := (rhb G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rpo_imm_t'" := (rpo_imm G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'W_t'" := (fun e => is_true (is_w lab_t e)).
Notation "'R_t'" := (fun e => is_true (is_r lab_t e)).
Notation "'F_t'" := (fun e => is_true (is_f lab_t e)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).
Notation "'Val_t_' l" := (fun e => val_t e = l) (at level 1).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'same_val_t'" := (same_val lab_t).
Notation "'Acq_t'" := (fun e => is_true (is_acq lab_t e)).
Notation "'Rel_t'" := (fun e => is_true (is_rel lab_t e)).
Notation "'Rlx_t'" := (fun e => is_true (is_rlx lab_t e)).

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rpo_imm_s'" := (rpo_imm G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun e => is_true (is_w lab_s e)).
Notation "'R_s'" := (fun e => is_true (is_r lab_s e)).
Notation "'F_s'" := (fun e => is_true (is_f lab_s e)).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'same_val_s'" := (same_val lab_s).
Notation "'Acq_s'" := (fun e => is_true (is_acq lab_s e)).
Notation "'Rel_s'" := (fun e => is_true (is_rel lab_s e)).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).

Lemma rsr_nrpo
    (INV : reord_step_pred X_t a_t b_t)
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper) :
  ⦗mapper ↑₁ (eq a_t ∩₁ E_t)⦘ ⨾ rpo_s ⨾ ⦗mapper ↑₁ (eq b_t ∩₁ E_t)⦘ ⊆ ∅₂.
Proof using.
  destruct classic with (E_t a_t) as [INA|NINA]
    ; [| basic_solver].
  destruct classic with (E_t b_t) as [INB|NINB]
    ; [| basic_solver].
  rewrite (rsr_bt SIMREL), (rsr_at SIMREL).
  unfold rpo.
  rewrite ct_begin, <- cr_of_ct, crE.
  rewrite seq_union_r, seq_id_r.
  rewrite seq_union_l, seq_union_r.
  assert (INAS : E_s b_t).
  { apply (rsr_acts SIMREL). left.
    exists a_t. split; auto.
    now apply (rsr_map_at INA SIMREL). }
  assert (INBS : E_s a_t).
  { apply (rsr_acts SIMREL). left.
    exists b_t. split; auto.
    now apply (rsr_map_bt INB SIMREL). }
  arewrite_false (
    ⦗eq b_t⦘ ⨾ (rpo_imm_s ⨾ rpo_imm_s⁺) ⨾ ⦗eq a_t⦘
  ).
  { rewrite rpo_imm_in_sb, ct_of_trans; auto using sb_trans.
    enough (RR : ~ (sb_s ⨾ sb_s) b_t a_t).
    { forward apply RR. basic_solver. }
    apply immediateE, (rsr_as_bs_imm INV SIMREL).
    basic_solver. }
  rewrite union_false_r.
  arewrite (eq b_t ≡₁ eq b_t ∩₁ E_s) by basic_solver.
  arewrite (eq a_t ≡₁ eq a_t ∩₁ E_s) by basic_solver.
  rewrite (rsr_as_rlx INV SIMREL), (rsr_bs_rlx INV SIMREL).
  unfold rpo_imm. rewrite !seq_union_l, !seq_union_r.
  repeat apply inclusion_union_l.
  all: basic_solver.
Qed.

End NRpo.