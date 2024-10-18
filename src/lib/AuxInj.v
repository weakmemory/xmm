From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Program.Basics.

Set Implicit Arguments.

Open Scope program_scope.

Section AuxInj.

Variable A B : Type.
Variable f : A -> B.

Lemma set_collect_minus s s'
    (INJ : inj_dom (s ∪₁ s') f) :
  f ↑₁ (s \₁ s') ≡₁ f ↑₁ s \₁ f ↑₁ s'.
Proof using.
  unfold inj_dom, set_union in INJ.
  unfold set_collect, set_minus.
  split; intros x HSET.
  all: desf; splits.
  all: try (eexists; splits; eauto).
  intros (y' & IN & FALSO). apply INJ in FALSO.
  all: eauto.
  congruence.
Qed.

Lemma set_collect_interE s s'
    (INJ : inj_dom (s ∪₁ s') f) :
  f ↑₁ (s ∩₁ s') ≡₁ f ↑₁ s ∩₁ f ↑₁ s'.
Proof using.
  split; [apply set_collect_inter |].
  unfold inj_dom, set_union in INJ.
  unfold set_collect, set_inter.
  intros x SET; desf.
  eexists; splits; eauto.
  erewrite INJ; eauto.
Qed.

Lemma collect_rel_restr s r
    (FINJ : inj_dom (dom_rel r ∪₁ codom_rel r ∪₁ s) f) :
  restr_rel (f ↑₁ s) (f ↑ r) ≡ f ↑ (restr_rel s r).
Proof using.
  rewrite 2!restr_relE, 2!collect_rel_seq, collect_rel_eqv.
  { reflexivity. }
  all: eapply inj_dom_mori; eauto.
  all: unfold flip.
  { rewrite dom_eqv. unfold set_union, set_subset.
    intros. tauto. }
  rewrite codom_eqv, inclusion_seq_eqv_r.
  unfold set_union, set_subset. intros. tauto.
Qed.

Lemma map_rel_eqvE d
    (INJ : inj_dom (f ↓₁ d) f) :
  ⦗f ↓₁ d⦘ ≡ f ↓ ⦗d⦘.
Proof using.
  split; [apply map_rel_eqv |].
  unfold inj_dom, set_map in INJ.
  unfold map_rel, eqv_rel, set_map.
  intros x y (EQ & IN). split; [| exact IN].
  apply INJ; [exact IN | | exact EQ].
  rewrite <- EQ. exact IN.
Qed.

Lemma collect_rel_interE r r'
    (INJ : inj_dom (dom_rel r ∪₁ codom_rel r ∪₁ dom_rel r' ∪₁ codom_rel r') f) :
  f ↑ (r ∩ r') ≡ f ↑ r ∩ f ↑ r'.
Proof using.
  split; [apply collect_rel_inter |].
  unfold inj_dom, set_union, dom_rel, codom_rel in INJ.
  unfold collect_rel, inter_rel.
  intros x y.
  intros ((x'1 & y'1 & REL1 & XEQ1 & YEQ1) &
          (x'2 & y'2 & REL2 & XEQ2 & YEQ2)).
  exists x'2, y'2. splits; auto. subst.
  rewrite (INJ x'2 x'1), (INJ y'2 y'1).
  all: eauto.
Qed.

Lemma collect_set_disjoint s1 s2
    (FINJ : inj_dom (s1 ∪₁ s2) f)
    (DISJ : set_disjoint s1 s2) :
  set_disjoint (f ↑₁ s1) (f ↑₁ s2).
Proof using.
  apply set_disjointE. apply set_disjointE in DISJ.
  rewrite <- set_collect_interE, DISJ, set_collect_empty.
  all: auto.
Qed.

Lemma collect_rel_minusE r1 r2
    (INJ : inj_dom (dom_rel r1 ∪₁ codom_rel r1 ∪₁ dom_rel r2 ∪₁ codom_rel r2) f) :
  f ↑ (r1 \ r2) ≡ f ↑ r1 \ f ↑ r2.
Proof using.
  split; [| apply collect_rel_minus].
  unfold inj_dom, set_union, dom_rel, codom_rel in INJ.
  unfold collect_rel, minus_rel.
  intros x y (x' & y' & (REL & NREL) & XEQ & YEQ).
  split.
  { exists x', y'. auto. }
  intros (x'' & y'' & REL' & XEQ' & YEQ').
  subst. apply NREL. rewrite (INJ x' x''), (INJ y' y'').
  all: eauto.
Qed.

Lemma collect_rel_immediate r
    (FINJ : inj_dom (dom_rel r ∪₁ codom_rel r) f) :
  immediate (f ↑ r) ≡ f ↑ immediate r.
Proof using.
  rewrite !immediateE.
  rewrite collect_rel_minusE, collect_rel_seq.
  { reflexivity. }
  { now rewrite set_unionC. }
  eapply inj_dom_mori; eauto. unfold flip.
  rewrite dom_seq, codom_seq.
  clear. basic_solver.
Qed.

Lemma upd_compose {C} a b
    (g : C -> A)
    (INJ : inj_dom ⊤₁ g) :
  upd (f ∘ g) a b = (upd f (g a) b) ∘ g.
Proof using.
  unfold compose. apply functional_extensionality. intro x.
  destruct classic with (x = a) as [HEQA|NEQA]; subst.
  { now rewrite !upds. }
  rewrite !updo; auto.
  intro F. apply INJ in F.
  all: ins.
Qed.

End AuxInj.