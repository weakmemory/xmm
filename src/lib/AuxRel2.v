From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Setoid Morphisms.

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

Lemma imm_exclude {T : Type} (a : T) r
    (SEMITOTL : semi_total_l r)
    (SEMITOTR : semi_total_r r)
    (TRANS : transitive r) :
  immediate r ≡
    immediate (⦗fun e => ~r e a⦘ ⨾ r ⨾ ⦗fun e => ~r a e⦘) ∪
      immediate (r \ (⦗fun e => ~r e a⦘ ⨾ r ⨾ ⦗fun e => ~r a e⦘)).
Proof using.
  split.
  { arewrite (
      r ≡ ⦗fun e => ~r e a⦘ ⨾ r ⨾ ⦗fun e => ~r a e⦘ ∪
        (r \ ⦗fun e => ~r e a⦘ ⨾ r ⨾ ⦗fun e => ~r a e⦘)
    ) at 1.
    { split; [| basic_solver].
      unfolder. ins. desf. tauto. }
    now rewrite !imm_union. }
  unfolder.
  intros x y [
    ((NXA & XY & NAY) & IMM) |
    ((XY & YEA) & IMM)
  ]; split; auto; intros z XZ ZY.
  { apply IMM with z; splits; auto.
    all: intro FALSO.
    { apply NAY. eapply TRANS; eauto. }
    apply NXA. eapply TRANS; eauto. }
  assert (YEA' : r x a \/ r a y) by tauto.
  apply IMM with z; split; auto.
  all: desf; try tauto.
  { destruct classic with (z = a) as [EQ|NEQ].
    { subst z. tauto. }
    destruct SEMITOTR
        with a z y
          as [AZ | ZA].
    all: auto; try tauto.
    enough (r x a) by tauto.
    eapply TRANS; eauto. }
  destruct classic with (z = a) as [EQ|NEQ].
  { subst z. tauto. }
  destruct SEMITOTL
      with x z a
        as [ZA | AZ].
  all: auto; try tauto.
  enough (r a y) by tauto.
  eapply TRANS; eauto.
Qed.

Lemma imm_split {T : Type} (a : T) r
    (IRR : irreflexive r)
    (SEMITOTL : semi_total_l r)
    (SEMITOTR : semi_total_r r)
    (TRANS : transitive r) :
  immediate r ≡
    immediate (⦗fun e => ~r e a⦘ ⨾ r ⨾ ⦗fun e => ~r a e⦘) ∪
      immediate (⦗fun e => r a e \/ e = a⦘ ⨾ r) ∪
        immediate (r ⨾ ⦗fun e => r e a \/ e = a⦘).
Proof using.
  rewrite imm_exclude with (a := a) at 1.
  all: auto.
  rewrite unionA.
  apply union_more; [reflexivity |].
  rewrite minus_inter_compl.
  arewrite (
    ⦗fun e : T => ~ r e a⦘ ⨾ r ⨾ ⦗fun e : T => ~ r a e⦘ ≡
      (fun x y => ~ r x a /\ r x y /\ ~ r a y)
  ) by basic_solver.
  arewrite (
    compl_rel (fun x y => ~ r x a /\ r x y /\ ~ r a y) ≡
      (fun x y => r x a \/ ~r x y \/ r a y)
  ) by unfolder; splits; ins; desf; tauto.
  arewrite (
    r ∩ (fun x y : T => r x a \/ ~ r x y \/ r a y) ≡
      r ∩ (fun x y : T => r x a \/ r a y)
  ) by basic_solver.
  arewrite (
    r ∩ (fun x y : T => r x a \/ r a y) ≡
      r ∩ (fun x y : T => r x a) ∪
        r ∩ (fun x y : T => r a y)
  ) by basic_solver.
  arewrite (
    r ∩ (fun x y => r x a) ≡
      ⦗fun e =>
        codom_rel (⦗eq e⦘ ⨾ immediate r) ⊆₁
          eq a ∪₁ (fun y => r y a)
      ⦘ ⨾ r
  ).
  { split; unfolder; [intros x y | intros x y IMM].
    all: ins; desf.
    all: split; auto.
    { intros x1 R. desf.
      destruct classic with (a = x1); auto.
      destruct SEMITOTL with z x1 a; auto.
      exfalso. eauto. }
    assert (IMME : exists y', immediate r x y'); desf.
    { admit. }
    destruct IMM with y' as [EQ | YA].
    { exists x, x. splits; auto.
      all: apply IMME. }
    { subst y'. apply IMME. }
    apply TRANS with y'; auto.
    apply IMME. }
  arewrite (
    r ∩ (fun x y => r a y) ≡
      r ⨾ ⦗fun e =>
        dom_rel (immediate r ⨾ ⦗eq e⦘) ⊆₁
          eq a ∪₁ (fun x => r a x)
      ⦘
  ).
  { admit. }
  arewrite (
    immediate (
      ⦗fun e =>
        codom_rel (⦗eq e⦘ ⨾ immediate r) ⊆₁
          eq a ∪₁ (fun y : T => r y a)
      ⦘ ⨾ r ∪
      r ⨾ ⦗fun e : T =>
        dom_rel (immediate r ⨾ ⦗eq e⦘) ⊆₁
          eq a ∪₁ (fun x : T => r a x)
      ⦘)
    ≡
    immediate (
      ⦗fun e =>
        codom_rel (⦗eq e⦘ ⨾ immediate r) ⊆₁
          eq a ∪₁ (fun y : T => r y a)
      ⦘ ⨾ r
    ) ∪
    immediate (
      r ⨾ ⦗fun e : T =>
        dom_rel (immediate r ⨾ ⦗eq e⦘) ⊆₁
          eq a ∪₁ (fun x : T => r a x)
      ⦘
    )
  ).
  { split; [apply imm_union |].
    set (LA := ⦗fun e : T =>
      codom_rel (⦗eq e⦘ ⨾ immediate r) ⊆₁ eq a ∪₁ (fun
        y : T
      => r y a)⦘).
    set (RA := ⦗fun e : T =>
        dom_rel (immediate r ⨾ ⦗eq e⦘) ⊆₁ eq a ∪₁ (fun
          x : T
        => r a x)⦘).
    rewrite !immediateE, !seqA.
    rewrite minus_union_l. apply union_mori.
    { rewrite !seq_union_l, !seq_union_r, !seqA.
      rewrite !minus_union_r.
      admit. }
    admit. }
Admitted.