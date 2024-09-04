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
  unfolder. split; intros x HSET.
  { destruct HSET as (y & (HSET & HMINUS) & XEQ).
    split; eauto.
    intros (y' & INS & XEQ'). apply HMINUS.
    rewrite INJ with (x := y) (y := y'); eauto.
    all: try congruence.
    all: basic_solver. }
  destruct HSET as ((y & HSET & XEQ) & NOTIN).
  exists y; splits; eauto.
Qed.

Lemma set_collect_interE s s'
    (INJ : inj_dom (s ∪₁ s') f) :
  f ↑₁ (s ∩₁ s') ≡₁ f ↑₁ s ∩₁ f ↑₁ s'.
Proof using.
  split; [apply set_collect_inter |].
  unfolder; intros x SET; desf.
  apply INJ in SET1; ins; desf.
  { exists y0; splits; ins. }
  all: basic_solver.
Qed.

Lemma collect_rel_restr s r
    (FINJ : inj_dom (dom_rel r ∪₁ codom_rel r ∪₁ s) f) :
  restr_rel (f ↑₁ s) (f ↑ r) ≡ f ↑ (restr_rel s r).
Proof using.
  rewrite !restr_relE, !collect_rel_seq, collect_rel_eqv; ins.
  all: eapply inj_dom_mori; eauto.
  all: unfold flip; basic_solver.
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
  unfolder; intros x y REL; desf.
  apply INJ in REL1, REL2; ins; desf.
  { exists x'0, y'0; splits; ins. }
  all: basic_solver 11.
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
  unfolder. intros x y (x' & y' & (R1 & R2) & XEQ & YEQ).
  split; eauto. intros (x'' & y'' & R2' & XEQ' & YEQ').
  apply R2.
  rewrite FINJ with x' x'', FINJ with y' y''.
  all: try congruence.
  all: basic_solver 11.
Qed.

Lemma collect_rel_immediate r
    (FINJ : inj_dom (dom_rel r ∪₁ codom_rel r) f) :
  immediate (f ↑ r) ≡ f ↑ immediate r.
Proof using.
  rewrite !immediateE.
  rewrite collect_rel_minusE, collect_rel_seq; ins.
  { now rewrite set_unionC. }
  rewrite dom_seq, codom_seq.
  eapply inj_dom_mori; eauto. unfold flip. basic_solver.
Qed.

End AuxInj.