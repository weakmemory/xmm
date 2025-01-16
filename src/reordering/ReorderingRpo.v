Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import SimrelCommon ReordSimrel ReorderingMapper.
Require Import Rhb.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Set Implicit Arguments.

Section ReordRpo.

Variable X X' : WCore.t.
Variable a b : actid.

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

Notation "'mapper'" := (mapper a b).

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

Lemma reord_map_rpo
    (WF : Wf G')
    (BIN : E' b)
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
    { apply (wf_rpo_immE WF) in RPOIMM.
      unfolder in RPOIMM; desf. }
    intro FALSO; subst x.
    eapply reord_rpo_imm_emp; auto.
    basic_solver. }
  assert (IND1 : (⦗E' \₁ eq b⦘ ⨾ rpo_imm' ⨾ ⦗E' \₁ eq b⦘) ⊆ mapper ↑ rpo_imm⁺).
  { unfold rpo_imm.
    rewrite !seq_union_l, !seq_union_r, !seqA.
    rewrite <- ct_step.
    arewrite (sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘).
    { rewrite wf_sbE. basic_solver 11. }
    rewrite <- seqA. rewrite seq_eqvC.
    rewrite seqA. rewrite seq_eqvC.
    arewrite (⦗E' \₁ eq b⦘ ⨾ ⦗Acq'⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘ ≡
              ⦗Acq'⦘ ⨾ ⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘).
    { rewrite <- seqA. rewrite seq_eqvC; basic_solver. }
    arewrite (⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗Rel'⦘ ⨾ ⦗E' \₁ eq b⦘ ≡
              ⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘ ⨾ ⦗Rel'⦘).
    { rewrite seq_eqvC; basic_solver. }
    arewrite (⦗E' \₁ eq b⦘ ⨾ ⦗F' ∩₁ Rel'⦘ ⨾ sb' ⨾ ⦗W' ∩₁ Rlx'⦘ ⨾ ⦗E' \₁ eq b⦘ ≡
              ⦗F' ∩₁ Rel'⦘ ⨾ ⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘ ⨾ ⦗W' ∩₁ Rlx'⦘).
    { rewrite seq_eqvC. rewrite <- seqA. rewrite seq_eqvC. basic_solver. }
    arewrite (⦗R' ∩₁ Rlx'⦘ ⨾ ⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘ ⨾ ⦗F' ∩₁ Acq'⦘
              ⊆ ⦗R' ∩₁ Rlx'⦘ ⨾ ⦗E' \₁ eq b⦘ ⨾ mapper ↑ sb ⨾ ⦗E' \₁ eq b⦘ ⨾ ⦗F' ∩₁ Acq'⦘).
    { clear - SBSUB. hahn_frame_l. hahn_frame_r; vauto. }
    arewrite (⦗Acq'⦘ ⨾ ⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘
              ⊆ ⦗Acq'⦘ ⨾ ⦗E' \₁ eq b⦘ ⨾ mapper ↑ sb ⨾ ⦗E' \₁ eq b⦘).
    arewrite (⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘ ⨾ ⦗Rel'⦘
              ⊆ ⦗E' \₁ eq b⦘ ⨾ mapper ↑ sb ⨾ ⦗E' \₁ eq b⦘ ⨾ ⦗Rel'⦘).
    { clear - SBSUB. hahn_frame_r; vauto. }
    arewrite (⦗F' ∩₁ Rel'⦘ ⨾ ⦗E' \₁ eq b⦘ ⨾ sb' ⨾ ⦗E' \₁ eq b⦘ ⨾ ⦗W' ∩₁ Rlx'⦘
              ⊆ ⦗F' ∩₁ Rel'⦘ ⨾ ⦗E' \₁ eq b⦘ ⨾ mapper ↑ sb ⨾ ⦗E' \₁ eq b⦘ ⨾ ⦗W' ∩₁ Rlx'⦘).
    { clear - SBSUB. hahn_frame_l. hahn_frame_r; vauto. }
    rewrite <- !id_inter. rewrite <- !seqA.
    rewrite <- !id_inter. rewrite !seqA.
    rewrite <- !set_interA.
    arewrite (E' \₁ eq b ⊆₁ mapper ↑₁ E).
    { admit. }
    arewrite (⦗R' ∩₁ Rlx' ∩₁ mapper ↑₁ E⦘
                ⊆ mapper ↑ ⦗R ∩₁ Rlx ∩₁ E⦘).
    { admit. }
    arewrite (⦗mapper ↑₁ E ∩₁ F' ∩₁ Acq'⦘
                ⊆ mapper ↑ ⦗E ∩₁ F ∩₁ Acq⦘).
    { admit. }
    arewrite (⦗Acq' ∩₁ mapper ↑₁ E⦘
                ⊆ mapper ↑ ⦗Acq ∩₁ E⦘).
    { admit. }
    arewrite (mapper ↑ ⦗Acq ∩₁ E⦘ ⨾ mapper ↑ sb ⨾ ⦗mapper ↑₁ E⦘
          ⊆ mapper ↑ ⦗Acq ∩₁ E⦘ ⨾ mapper ↑ sb ⨾ mapper ↑ ⦗E⦘).
    { do 2 hahn_frame_l. rewrite collect_rel_eqv; vauto. }
    arewrite (⦗(mapper ↑₁ E) ∩₁ Rel'⦘
          ⊆ mapper ↑ ⦗E ∩₁ Rel⦘).
    { admit. }
    arewrite (⦗mapper ↑₁ E⦘ ⨾ mapper ↑ sb ⨾ mapper ↑ ⦗E ∩₁ Rel⦘
          ⊆ mapper ↑ ⦗E⦘ ⨾ mapper ↑ sb ⨾ mapper ↑ ⦗E ∩₁ Rel⦘).
    { do 2 hahn_frame_r. rewrite collect_rel_eqv; vauto. }
    arewrite (⦗F' ∩₁ Rel' ∩₁ mapper ↑₁ E⦘
            ⊆ mapper ↑ ⦗F ∩₁ Rel ∩₁ E⦘).
    { admit. }
    arewrite (⦗(mapper ↑₁ E) ∩₁ W' ∩₁ Rlx'⦘
            ⊆ mapper ↑ ⦗E ∩₁ W ∩₁ Rlx⦘).
    { admit. }
    rewrite !collect_rel_union.
    admit. }
  assert (IND2 : mapper ↑ rpo_imm⁺ ⨾ ⦗E' \₁ eq b⦘ ⨾ (rpo_imm' ⨾ ⦗E' \₁ eq b⦘)
    ⊆ mapper ↑ rpo_imm⁺).
  { assert (TRIN : mapper ↑ rpo_imm⁺ ⨾ mapper ↑ rpo_imm⁺
                  ⊆ mapper ↑ rpo_imm⁺).
    { intros x y PATH. destruct PATH as (x0 & P1 & P2).
      unfold collect_rel in P1, P2. unfold collect_rel.
      destruct P1 as (x' & x0' & (P1 & M1 & M2)).
      destruct P2 as (x0'' & y' & (P2 & M3 & M4)).
      exists x', y'. splits; vauto.
      assert (EQ : x0'' = x0').
      { admit. }
      subst x0''. apply ct_ct.
      unfold seq. exists x0'. splits; vauto. }
    rewrite <- TRIN at 2. apply seq_mori; vauto. }
  apply inclusion_t_ind_right; vauto.
Admitted.

End ReordRpo.