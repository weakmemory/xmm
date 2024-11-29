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

Definition semi_total_l {A} (r : relation A) : Prop :=
  forall x y z (XZ : r x y) (YZ : r x z) (NEQ : y <> z),
    r y z \/ r z y.

Definition semi_total_r {A} (r : relation A) : Prop :=
  forall x y z (XZ : r x z) (YZ : r y z) (NEQ : x <> y),
    r x y \/ r y x.

Definition left_dom {A} (r : relation A) (a : A) : A -> Prop :=
  fun x => r x a.

Definition right_dom {A} (r : relation A) (a : A) : A -> Prop :=
  fun x => r a x.

#[global]
Hint Unfold least_elt rmw_delta left_dom right_dom : unfolderDb.