From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import AuxDef.

Set Implicit Arguments.

Lemma empty_codom_irr (A : Type) (r r' : relation A)
        (EMP : codom_rel r ≡₁ ∅) :
    irreflexive (r ⨾ r').
Proof using.
    apply empty_irr. split; try basic_solver.
    intros x y H. destruct H. destruct H. assert (Q : ∅ x0).
    { apply EMP. basic_solver. }
    destruct Q.
Qed.

Lemma empty_seq_codom (A : Type) (r r' : relation A)
        (EMP : codom_rel r ≡₁ ∅) :
    codom_rel (r ⨾ r') ≡₁ ∅.
Proof using.
    split; try basic_solver. intros x H. induction H.
    destruct H. destruct H. destruct EMP.
    assert (IN : codom_rel r x1).
    { exists x0; eauto. }
    assert (F : ∅ x1).
    { apply H1 in IN; eauto. }
    basic_solver.
Qed.

Lemma set_disjoint_union_minus (A : Type) (s1 s2 s' : A -> Prop)
    (E_MAP : s' ≡₁ s1 ∪₁ s2)
    (NIN : set_disjoint s1 s2) :
  s' \₁ s2 ≡₁ s1.
Proof using.
    rewrite E_MAP. rewrite set_minus_union_l.
    rewrite set_minusK. rewrite set_union_empty_r.
    apply set_minus_disjoint; eauto.
Qed.

Lemma tid_map_replace (s s' : actid -> Prop)
    (SUB1 : s ⊆₁ tid ↓₁ (tid ↑₁ s'))
    (SUB2 : s' ⊆₁ tid ↓₁ (tid ↑₁ s)) :
  tid ↑₁ s ≡₁ tid ↑₁ s'.
Proof using.
  split.
  { now rewrite SUB1, collect_map_in_set. }
  now rewrite SUB2, collect_map_in_set.
Qed.

Lemma sb_downward_total G
    (WF : Wf G) :
  downward_total (nin_sb G).
Proof using.
  unfold downward_total, nin_sb.
  unfolder.
  intros y z x
    (y' & (EQY & YNIN) & SB1)
    (z' & (EQZ & ZNIN) & SB2).
  subst y' z'.
  destruct classic with (y = z) as [EQ|NEQ].
  { basic_solver. }
  destruct sb_semi_total_r
      with (x := x) (y := y) (z := z) (G := G)
        as [YZ|ZY].
  all: eauto 7.
Qed.

Lemma nin_sb_functional_l G
    (WF : Wf G) :
  functional ((immediate (nin_sb G))⁻¹).
Proof using.
  now apply dwt_imm_f, sb_downward_total.
Qed.