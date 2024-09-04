From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Program.Basics.

Set Implicit Arguments.

Section AuxInj.

Variable A B : Type.
Variable f : A -> B.

Lemma set_collect_minus s s'
    (INJ : inj_dom (s ∪₁ s') f) :
  f ↑₁ (s \₁ s') ≡₁ f ↑₁ s \₁ f ↑₁ s'.
Proof using.
  unfolder in *. split; intros x HSET.
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
  unfolder in *; intros x SET; desf.
  eexists; splits; eauto.
  erewrite INJ; eauto.
Qed.

Lemma collect_rel_restr s r
    (FINJ : inj_dom (dom_rel r ∪₁ codom_rel r ∪₁ s) f) :
  restr_rel (f ↑₁ s) (f ↑ r) ≡ f ↑ (restr_rel s r).
Proof using.
  rewrite !restr_relE, !collect_rel_seq, collect_rel_eqv; ins.
  all: eapply inj_dom_mori; eauto.
  all: red; clear; basic_solver.
Qed.

Lemma map_rel_eqvE d
    (INJ : inj_dom (f ↓₁ d) f) :
  ⦗f ↓₁ d⦘ ≡ f ↓ ⦗d⦘.
Proof using.
  split; [apply map_rel_eqv |].
  unfolder; intros x y; desf.
  splits; desf. apply INJ; ins.
  unfolder. congruence.
Qed.

Lemma collect_rel_interE r r'
    (INJ : inj_dom (dom_rel r ∪₁ codom_rel r ∪₁ dom_rel r' ∪₁ codom_rel r') f) :
  f ↑ (r ∩ r') ≡ f ↑ r ∩ f ↑ r'.
Proof using.
  split; [apply collect_rel_inter |].
  unfolder; intros x y (REL & REL'); desf.
  do 2 eexists; splits; eauto.
  rewrite <- 2!INJ; eauto.
  all: clear - REL REL'.
  all: basic_solver 7.
Qed.

Lemma collect_set_disjoint s1 s2
    (FINJ : inj_dom (s1 ∪₁ s2) f)
    (DISJ : set_disjoint s1 s2) :
  set_disjoint (f ↑₁ s1) (f ↑₁ s2).
Proof using.
  apply set_disjointE. apply set_disjointE in DISJ.
  rewrite <- set_collect_interE, DISJ, set_collect_empty; ins.
Qed.

Lemma collect_rel_minusE r1 r2
    (FINJ : inj_dom (dom_rel r1 ∪₁ codom_rel r1 ∪₁ dom_rel r2 ∪₁ codom_rel r2) f) :
  f ↑ (r1 \ r2) ≡ f ↑ r1 \ f ↑ r2.
Proof using.
  split; [| apply collect_rel_minus].
  unfolder. ins. desf; splits; eauto.
  intros (x'0 & y'0 & F & XEQ & YEQ).
  erewrite (FINJ x'0), (FINJ y'0) in F; eauto.
  all: basic_solver 7.
Qed.

Lemma collect_rel_immediate r
    (FINJ : inj_dom (dom_rel r ∪₁ codom_rel r) f) :
  immediate (f ↑ r) ≡ f ↑ immediate r.
Proof using.
  rewrite !immediateE.
  rewrite collect_rel_minusE, collect_rel_seq; ins.
  { now rewrite set_unionC. }
  rewrite dom_seq, codom_seq.
  eapply inj_dom_mori; eauto. unfold flip.
  clear. basic_solver.
Qed.

End AuxInj.