From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Setoid Morphisms.

Set Implicit Arguments.

Lemma restr_rel_ct {A : Type} (r : relation A) s
    (NEST : upward_closed r s) :
  restr_rel s r⁺ ⊆ (restr_rel s r)⁺.
Proof using.
  intros x y (REL & DOM & CODOM).
  apply clos_trans_tn1 in REL. apply clos_tn1_trans.
  induction REL as [y REL | y z REL1 REL2 IHREL].
  { apply tn1_step. basic_solver. }
  apply Relation_Operators.tn1_trans with y.
  { basic_solver. }
  eapply IHREL, NEST; eauto.
Qed.

Lemma minus_inter_l {A : Type} (r1 r2 r3 : relation A) :
  (r1 ∩ r2) \ r3 ≡ (r1 \ r3) ∩ r2.
Proof using.
  basic_solver.
Qed.

Lemma cross_minus_l {T : Type} (A1 A2 B : T -> Prop) :
  (A1 \₁ A2) × B ≡ A1 × B \ A2 × B.
Proof using.
  unfolder. split; ins; desf; tauto.
Qed.

Lemma set_minus_inter {A : Type} (s1 s2 s3 : A -> Prop) :
  (s1 \₁ s2 ∩₁ s3) ∩₁ s3 ≡₁ (s1 \₁ s2) ∩₁ s3.
Proof using.
  unfolder. split; ins; desf; tauto.
Qed.

Definition swap_rel {T : Type} (r : relation T) A B :=
  r \ A × B ∪ B × A.

Definition add_max {T : Type} (A B : T -> Prop) := (A \₁ B) × B.

Lemma add_max_union T (A1 A2 B : T -> Prop) :
  add_max (A1 ∪₁ A2) B ≡ add_max A1 B ∪ add_max A2 B.
Proof using.
  unfold add_max. basic_solver 11.
Qed.

Lemma add_max_empty_r T (A : T -> Prop) :
  add_max A ∅ ≡ ∅₂.
Proof using.
  unfold add_max. now rewrite cross_false_r.
Qed.

Lemma add_max_empty_l T (B : T -> Prop) :
  add_max ∅ B ≡ ∅₂.
Proof using.
  unfold add_max. basic_solver.
Qed.

Lemma add_max_sub T (A B : T -> Prop)
    (SUB : A ⊆₁ B) :
  add_max A B ≡ ∅₂.
Proof using.
  unfold add_max. basic_solver.
Qed.

Lemma add_max_disjoint T (A B : T -> Prop)
    (DISJ : set_disjoint A B) :
  add_max A B ≡ A × B.
Proof using.
  unfold add_max. now rewrite set_minus_disjoint.
Qed.

Lemma restr_add_max T (A B C : T -> Prop) :
  restr_rel C (add_max A B) ≡ add_max (A ∩₁ C) (B ∩₁ C).
Proof using.
  unfold add_max.
  rewrite restr_relE, <- cross_inter_r, <- cross_inter_l.
  arewrite (C ∩₁ (A \₁ B) ≡₁ A ∩₁ C \₁ B ∩₁ C); ins.
  unfolder. split; ins; desf; splits; tauto.
Qed.

Lemma swap_rel_union {T : Type} (r1 r2 : relation T) A B :
  swap_rel (r1 ∪ r2) A B ≡
    swap_rel r1 A B ∪ swap_rel r2 A B.
Proof using.
  unfold swap_rel. basic_solver 11.
Qed.

Lemma swap_rel_unionE {T : Type} (r1 r2 : relation T) A B :
  swap_rel (r1 ∪ r2) A B ≡ swap_rel r1 A B ∪ r2 \ A × B.
Proof using.
  rewrite swap_rel_union. unfold swap_rel. basic_solver 11.
Qed.

Lemma swap_rel_empty_l {T : Type} (r : relation T) B :
  swap_rel r ∅ B ≡ r.
Proof using.
  unfold swap_rel. rewrite cross_false_l, cross_false_r.
  basic_solver.
Qed.

Lemma swap_rel_empty_r {T : Type} (r : relation T) A :
  swap_rel r A ∅ ≡ r.
Proof using.
  unfold swap_rel. rewrite cross_false_l, cross_false_r.
  basic_solver.
Qed.

Lemma swap_rel_imm {T : Type} (r : relation T) A B x y
    (XNA : ~A x)
    (XNB : ~B x)
    (YNA : ~A y)
    (YNB : ~B y)
    (IN : singl_rel x y ⊆ immediate r) :
  singl_rel x y ⊆ immediate (swap_rel r A B).
Proof using.
  unfold swap_rel. rewrite immediateE in *.
  intros x' y' EQ. unfolder in EQ. desf.
  split.
  { assert (IN' : r x y) by now apply IN.
    unfolder. left; split; eauto using or_not_and. }
  assert (IN' : ~ (r ⨾ r) x y) by now apply IN.
  unfolder. intros FALSO. desf.
  apply IN'. basic_solver.
Qed.

Lemma immediate_union_ignore {T : Type} (r1 r2 r3 : relation T)
    (NOX : set_disjoint (dom_rel r1) (dom_rel r3))
    (NOY : set_disjoint (codom_rel r1) (codom_rel r3))
    (IN : r1 ⊆ immediate r2) :
  r1 ⊆ immediate (r2 ∪ r3).
Proof using.
  rewrite immediateE in *.
  intros x y REL. split.
  { left. now apply IN. }
  unfolder. intros FALSE. desf.
  { assert (IN' : ~ (r2 ⨾ r2) x y) by now apply IN.
    apply IN'. basic_solver. }
  { apply NOX with x; basic_solver. }
  { apply NOY with y; basic_solver. }
  apply NOY with y; basic_solver.
Qed.

Lemma immediate_union_ignore_alt {T : Type} (r1 r2 r3 : relation T)
    (NOX : set_disjoint (dom_rel r1) (codom_rel r3))
    (NOY : set_disjoint (codom_rel r1) (codom_rel r3))
    (EDGE : set_disjoint (codom_rel r3) (dom_rel r2))
    (IN : r1 ⊆ immediate r2) :
  r1 ⊆ immediate (r2 ∪ r3).
Proof using.
  rewrite immediateE in *.
  intros x y REL. split.
  { left. now apply IN. }
  unfolder. intros FALSE. desf.
  { assert (IN' : ~ (r2 ⨾ r2) x y) by now apply IN.
    apply IN'. basic_solver. }
  { apply EDGE with z; basic_solver. }
  { apply NOY with y; basic_solver. }
  apply NOY with y; basic_solver.
Qed.

Add Parametric Morphism T : (@swap_rel T) with signature
  same_relation ==> set_equiv ==> set_equiv
    ==> same_relation as swap_rel_more.
Proof using.
  intros r1 r2 REQ A1 A2 AEQ B1 B2 BEQ.
  unfold swap_rel. now rewrite REQ, AEQ, BEQ.
Qed.

Add Parametric Morphism T : (@add_max T) with signature
  set_equiv ==> set_equiv ==> same_relation as add_max_more.
Proof using.
  intros A1 A2 AEQ B1 B2 BEQ. unfold add_max.
  now rewrite AEQ, BEQ.
Qed.

#[export]
Instance swap_rel_Propere T : Proper (_ ==> _ ==> _ ==> _) _ := swap_rel_more (T:=T).
#[export]
Instance add_max_Propere T : Proper (_ ==> _ ==> _) _ := add_max_more (T:=T).

#[export]
Hint Unfold swap_rel add_max : unfolderDb.