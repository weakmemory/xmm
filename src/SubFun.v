From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From PromisingLib Require Import Basic.

Require Import Program.Basics.

Require Import PartialId.

Set Implicit Arguments.

Section SubFunction.

Definition sub_fun {A B} (f g : A -> option B) :=
  forall x y (SOME : f x = Some y), g x = Some y.

Lemma sub_id_refl {A B} : reflexive (@sub_fun A B).
Proof using.
  now unfolder.
Qed.

Lemma sub_id_trans {A B} : transitive (@sub_fun A B).
Proof using.
  unfolder. unfold sub_fun.
  intros f g h SUB1 SUB2 x y EQ.
  now apply SUB1, SUB2 in EQ.
Qed.

Add Parametric Relation A B : (A -> option B) (@sub_fun A B)
  reflexivity proved by (sub_id_refl (A:=A) (B:=B))
  transitivity proved by (sub_id_trans (A:=A) (B:=B))
  as sub_fun_rel.

Add Parametric Morphism A : (@partial_id A) with signature
  sub_fun --> Basics.impl as partial_id_mori.
Proof using.
  unfolder; unfold sub_fun, partial_id.
  ins; auto.
Qed.

Add Parametric Morphism A : (@partial_id_dom A) with signature
  sub_fun --> flip set_subset as partial_id_dom_mori.
Proof using.
  unfolder; unfold sub_fun, partial_id, partial_id_dom,
                    is_some, compose.
  intros f g EQ x MATCH; desf.
  now erewrite EQ in Heq; eauto.
Qed.

Lemma partial_id_upd_sub {A} {f} (a : A)
    (PARTIAL : partial_id f) :
  sub_fun f (upd f a (Some a)).
Proof using.
  unfold sub_fun. intros x y HEQ.
  destruct (classic (x = a)); subst; rupd.
  f_equal. symmetry. now apply PARTIAL.
Qed.

Lemma sub_fun_upd {A B} {f f' : A -> option B} x0
    (SUB : sub_fun f f') :
  sub_fun (upd f x0 (f' x0)) f'.
Proof using.
  unfold sub_fun. intros x y.
  destruct (classic (x = x0)); subst; rupd; ins.
  now apply SUB.
Qed.

Lemma sub_fun_upd_ext {A B} {f f' : A -> option B} x0
    (SUB : sub_fun f f') :
  sub_fun f (upd f x0 (f' x0)).
Proof using.
  unfold sub_fun. intros x y.
  destruct (classic (x = x0)); subst; rupd; ins.
  now apply SUB.
Qed.


End SubFunction.