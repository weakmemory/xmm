From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From PromisingLib Require Import Basic.

Require Import Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section PartialId.

Variable A : Type.
Variable f : A -> option A.

Definition partial_id (g : A -> option A) :=
  forall x y (SOME : g x = Some y), y = x.

Definition partial_id_dom (g : A -> option A) : A -> Prop :=
  is_some ∘ g.

Hypothesis PARTIAL : partial_id f.

Lemma partial_id_iff x : partial_id_dom f x <-> f x = Some x.
Proof using PARTIAL.
  unfold partial_id_dom, compose, is_some.
  split; ins; desf.
  f_equal. now apply PARTIAL.
Qed.

Lemma partial_id_rel r : Some ↓ (f ↑ r) ≡ restr_rel (partial_id_dom f) r.
Proof using PARTIAL.
  symmetry. unfolder; splits; ins; desf.
  { do 2 eexists. rewrite <- !partial_id_iff; auto. }
  rewrite PARTIAL with (x := x') (y := x),
          PARTIAL with (x := y') (y := y).
  all: splits; auto.
  all: unfold partial_id_dom, is_some, compose; desf.
Qed.

Lemma partial_id_set s : Some ↓₁ (f ↑₁ s) ≡₁ s ∩₁ (partial_id_dom f).
Proof using PARTIAL.
  symmetry.
  unfolder. splits; ins; desf.
  { eexists. rewrite <- !partial_id_iff; auto. }
  rewrite PARTIAL with (x := y) (y := x); auto.
  all: unfold partial_id_dom, is_some, compose; desf.
Qed.

Lemma partial_id_inj s :
  inj_dom (s ∩₁ partial_id_dom f) f.
Proof using PARTIAL.
  unfolder; ins; desf.
  apply PARTIAL. rewrite <- EQ.
  now apply partial_id_iff.
Qed.

Lemma upd_partial_id x :
  partial_id (upd f x (Some x)).
Proof using PARTIAL.
  unfold partial_id. intros x' y.
  destruct (classic (x' = x)); subst; rupd.
  { congruence. }
  apply PARTIAL.
Qed.

Lemma partial_id_sub_eq :
  (fun x y => f x = Some y) ⊆ (fun x => eq x).
Proof using PARTIAL.
  unfolder; ins; desf.
  symmetry; now apply PARTIAL.
Qed.

Lemma partial_id_collect_eq a :
  f ↓₁ (eq (Some a)) ≡₁ if f a then eq a else ∅.
Proof using PARTIAL.
  destruct (f a) eqn:HEQ; ins; eauto.
  all: unfolder; split; ins; desf.
  { apply PARTIAL; congruence. }
  { symmetry; apply partial_id_iff.
    unfold partial_id_dom, is_some, compose.
    now rewrite HEQ. }
  match goal with
  | A : Some a = f x |- _ => rename x into a', A into HEQ'
  end.
  symmetry in HEQ'.
  assert (HIN : partial_id_dom f a').
  { unfold partial_id_dom, is_some, compose.
    now rewrite HEQ'. }
  rewrite (PARTIAL HEQ') in HEQ.
  congruence.
Qed.

Lemma partial_id_upd_dom a :
    partial_id_dom (upd f a (Some a)) ≡₁ partial_id_dom f ∪₁ eq a.
Proof using.
  unfold partial_id_dom, is_some, compose.
  unfolder. split; intro x.
  all: destruct (classic (a = x)); subst; rupd; eauto.
  ins. desf.
Qed.

End PartialId.
