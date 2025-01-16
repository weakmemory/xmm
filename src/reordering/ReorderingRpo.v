Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2 AuxInj.
Require Import SimrelCommon ReordSimrel.
Require Import Rhb.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Set Implicit Arguments.

Section ReordRpo.

Variable X X' : WCore.t.
Variable a b : actid.
Variable mapper : actid -> actid.

Notation "'G''" := (WCore.G X').
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

Notation "'G'" := (WCore.G X).
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

Lemma reord_map_rlx s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  Rlx' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (Rlx ∩₁ s).
Proof using.
  unfolder. intros x' (RLX & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_rlx, mod in *. rewrite LABEQ; auto.
Qed.

Lemma reord_map_rel s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  Rel' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (Rel ∩₁ s).
Proof using.
  unfolder. intros x' (REL & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_rel, mod in *. rewrite LABEQ; auto.
Qed.

Lemma reord_map_acq s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  Acq' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (Acq ∩₁ s).
Proof using.
  unfolder. intros x' (ACQ & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_acq, mod in *. rewrite LABEQ; auto.
Qed.

Lemma reord_map_r s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  R' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (R ∩₁ s).
Proof using.
  unfolder. intros x' (ISR & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_r in *. rewrite LABEQ; auto.
Qed.

Lemma reord_map_w s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  W' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (W ∩₁ s).
Proof using.
  unfolder. intros x' (ISW & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_w in *. rewrite LABEQ; auto.
Qed.

Lemma reord_map_f s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  F' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (F ∩₁ s).
Proof using.
  unfolder. intros x' (ISF & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_f in *. rewrite LABEQ; auto.
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
  unfold rpo.
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
  assert (IND1 : (⦗E' \₁ eq b⦘ ⨾ rpo_imm' ⨾ ⦗E' \₁ eq b⦘) ⊆ mapper ↑ rpo_imm⁺).
  { unfold rpo_imm.
    rewrite !seq_union_l, !seq_union_r, !seqA.
    seq_rewrite (seq_eqvC (E' \₁ eq b) (R' ∩₁ Rlx')).
    seq_rewrite (seq_eqvC (F' ∩₁ Acq') (E' \₁ eq b)).
    seq_rewrite (seq_eqvC (E' \₁ eq b) Acq').
    seq_rewrite (seq_eqvC Rel' (E' \₁ eq b)).
    seq_rewrite (seq_eqvC (W' ∩₁ Rlx') (E' \₁ eq b)).
    seq_rewrite (seq_eqvC (E' \₁ eq b) (F' ∩₁ Rel')).
    rewrite !seqA. sin_rewrite !SBSUB. rewrite !seqA.
    rewrite <- ct_step. seq_rewrite <- !id_inter.
    rewrite !set_interC with (s := E' \₁ eq b).
    rewrite MAPIN, !set_interA.
    arewrite (Rlx' ∩₁ mapper ↑₁ E ⊆₁ mapper ↑₁ (Rlx ∩₁ E)).
    { apply reord_map_rlx; auto with hahn. }
    arewrite (Acq' ∩₁ mapper ↑₁ E ⊆₁ mapper ↑₁ (Acq ∩₁ E)).
    { apply reord_map_acq; auto with hahn. }
    arewrite (Rel' ∩₁ mapper ↑₁ E ⊆₁ mapper ↑₁ (Rel ∩₁ E)).
    { apply reord_map_rel; auto with hahn. }
    arewrite (R' ∩₁ mapper ↑₁ (Rlx ∩₁ E) ⊆₁ mapper ↑₁ (R ∩₁ Rlx ∩₁ E)).
    { rewrite reord_map_r; auto; [apply set_collect_mori |].
      all: clear; basic_solver. }
    arewrite (W' ∩₁ mapper ↑₁ (Rlx ∩₁ E) ⊆₁ mapper ↑₁ (W ∩₁ Rlx ∩₁ E)).
    { rewrite reord_map_w; auto; [apply set_collect_mori |].
      all: clear; basic_solver. }
    arewrite (F' ∩₁ mapper ↑₁ (Acq ∩₁ E) ⊆₁ mapper ↑₁ (F ∩₁ Acq ∩₁ E)).
    { rewrite reord_map_f; auto; [apply set_collect_mori |].
      all: clear; basic_solver. }
    arewrite (F' ∩₁ mapper ↑₁ (Rel ∩₁ E) ⊆₁ mapper ↑₁ (F ∩₁ Rel ∩₁ E)).
    { rewrite reord_map_f; auto; [apply set_collect_mori |].
      all: clear; basic_solver. }
    rewrite !collect_rel_union.
    repeat apply union_mori.
    all: rewrite <- !collect_rel_eqv.
    all: rewrite <- !collect_rel_seq.
    all: try (rewrite 1?wf_sbE; eapply inj_dom_mori;
          eauto; red; basic_solver).
    all: apply collect_rel_mori; auto.
    all: basic_solver. }
  apply inclusion_t_ind_right; vauto.
  rewrite IND1.
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

End ReordRpo.