From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Setoid Morphisms.
From imm Require Import Events Execution.

Require Import AuxDef.

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

Lemma add_max_a T (A B : T -> Prop) :
  add_max A B ≡ add_max (A \₁ B) B.
Proof using.
  unfold add_max.
  basic_solver 11.
Qed.

Lemma restr_add_max T (A B C : T -> Prop) :
  restr_rel C (add_max A B) ≡ add_max (A ∩₁ C) (B ∩₁ C).
Proof using.
  unfold add_max.
  rewrite restr_relE, <- cross_inter_r, <- cross_inter_l.
  arewrite (C ∩₁ (A \₁ B) ≡₁ A ∩₁ C \₁ B ∩₁ C); ins.
  unfolder. split; ins; desf; splits; tauto.
Qed.

Lemma add_max_seq_r T (A B C : T -> Prop) :
  add_max A B ⨾ ⦗C⦘ ≡ add_max (A \₁ (B \₁ C)) (B ∩₁ C).
Proof using.
  unfold add_max.
  rewrite <- cross_inter_r.
  apply cross_more; auto.
  rewrite set_minus_minus_l.
  apply set_minus_more; auto.
  split; [| basic_solver].
  unfolder. ins. desf. splits; tauto.
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

Lemma swap_rel_imm {T : Type} (r1 r2 : relation T) A B
    (NIN : r1 ⊆ (set_compl B × set_compl (A ∪₁ B)))
    (IN : r1 ⊆ immediate r2) :
  r1 ⊆ immediate (swap_rel r2 A B).
Proof using.
  rewrite set_compl_union in NIN.
  unfold swap_rel. rewrite immediateE in *.
  intros x y REL. split; unfolder in *.
  { unfolder in *. left; split; [now apply IN|].
    apply or_not_and. right. apply (NIN x y REL). }
  intro F. desf.
  { apply (IN x y); eauto. }
  { enough (~ B x); [eauto | apply (NIN x y REL)]. }
  { enough (~ A y); [eauto | apply (NIN x y REL)]. }
  enough (~ A y); [eauto | apply (NIN x y REL)].
Qed.

Lemma collect_rel_swap {S T : Type} (f : S -> T) A B r :
  swap_rel (f ↑ r) (f ↑₁ A) (f ↑₁ B) ⊆ f ↑ (swap_rel r A B).
Proof using.
  unfold swap_rel.
  now rewrite collect_rel_union, <- collect_rel_minus,
          !collect_rel_cross.
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

(*
  General lemma for dragging relation restriction in
  and out of the immediate relation.
*)
Lemma immediate_restrE {T : Type} (s1 s2 : T -> Prop) r
    (LRCLOS :
      ⦗s1⦘ ⨾ r ⨾ r ⨾ ⦗s2⦘ ⊆
        ⦗s1⦘ ⨾ r ⨾ ⦗s2⦘ ⨾ ⦗s1⦘ ⨾ r ⨾ ⦗s2⦘
    ) :
  ⦗s1⦘ ⨾ immediate r ⨾ ⦗s2⦘ ≡
    immediate (⦗s1⦘ ⨾ r ⨾ ⦗s2⦘).
Proof using.
  rewrite !immediateE.
  arewrite (
    ⦗s1⦘ ⨾ (r \ r ⨾ r) ⨾ ⦗s2⦘ ≡
      ⦗s1⦘ ⨾ r ⨾ ⦗s2⦘ \ ⦗s1⦘ ⨾ r ⨾ r ⨾ ⦗s2⦘
  ).
  { split.
    all: unfolder; ins; desf.
    all: splits; eauto.
    all: intro FALSO; desf; eauto 7. }
  split.
  { apply minus_rel_mori; [reflexivity |].
    unfold Basics.flip. basic_solver. }
  apply minus_rel_mori; [reflexivity |].
  now unfold Basics.flip.
Qed.

(*
  Specialised version of the lemma for left- and right-
  continious sets
*)
Lemma immediate_restrE' {T : Type} (s1 s2 : T -> Prop) r
    (LCONT : ⦗s1⦘ ⨾ r ⊆ ⦗s1⦘ ⨾ r ⨾ ⦗s1⦘)
    (RCONT : r ⨾ ⦗s2⦘ ⊆ ⦗s2⦘ ⨾ r ⨾ ⦗s2⦘) :
  ⦗s1⦘ ⨾ immediate r ⨾ ⦗s2⦘ ≡
    immediate (⦗s1⦘ ⨾ r ⨾ ⦗s2⦘).
Proof using.
  apply immediate_restrE.
  seq_rewrite seq_eqvC.
  sin_rewrite LCONT.
  sin_rewrite RCONT.
  rewrite !seqA.
  reflexivity.
Qed.

Lemma left_dom_right_cont {T : Type} (r : relation T) a
    (TRANS : transitive r) :
  r ⨾ ⦗left_dom r a⦘ ≡ ⦗left_dom r a⦘ ⨾ r ⨾ ⦗left_dom r a⦘.
Proof using.
  basic_solver 7.
Qed.

Lemma right_dom_left_cont {T : Type} (r : relation T) a
    (TRANS : transitive r) :
  ⦗right_dom r a⦘ ⨾ r ≡ ⦗right_dom r a⦘ ⨾ r ⨾ ⦗right_dom r a⦘.
Proof using.
  basic_solver 7.
Qed.

Lemma left_domE {T : Type} (r : relation T) a :
  left_dom r a ≡₁ dom_rel (r ⨾ ⦗eq a⦘) ∪₁ eq a.
Proof using.
  unfolder. split; ins; desf.
  all: eauto.
Qed.

Lemma right_domE {T : Type} (r : relation T) a :
  right_dom r a ≡₁ codom_rel (⦗eq a⦘ ⨾ r) ∪₁ eq a.
Proof using.
  unfolder. split; ins; desf.
  all: eauto.
Qed.

Lemma tid_left_cont G t
    (NINIT : t <> tid_init) :
  ⦗fun e => tid e = t⦘ ⨾ sb G ≡
    ⦗fun e => tid e = t⦘ ⨾ sb G ⨾ ⦗fun e => tid e = t⦘.
Proof using.
  split; [| basic_solver].
  unfold sb, ext_sb.
  unfolder. ins. desf.
  all: ins; desf.
Qed.