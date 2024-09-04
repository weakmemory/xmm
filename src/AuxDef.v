From imm Require Import Events Execution.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

Set Implicit Arguments.

Definition surj_dom {A B} (s : B -> Prop) (f : A -> B) :=
  forall y, exists x, y = f x.

Definition edges_to {A} (e : A) := (fun _ _ => True) ⨾ ⦗eq e⦘.
Hint Unfold edges_to : unfolderDb.

Definition rmw_delta e e' : relation actid :=
  eq e × eq_opt e'.

Definition least_elt {A} (r : relation A) (x : A) :=
  forall (y : A) (NOTX : x <> y), r x y.

#[global]
Hint Unfold least_elt rmw_delta : unfolderDb.