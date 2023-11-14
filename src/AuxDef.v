From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

Lemma rel_compress_sub (A : Type) (S1 S2 : A -> Prop) (R1 R2 : relation A)
  (SUB : R1 ⊆ R2) (EQ : R2 ≡ ⦗S1⦘⨾ R2⨾ ⦗ S2⦘):
  R1 ≡ ⦗S1⦘⨾ R1⨾ ⦗S2⦘.
Proof using.
  unfolder; split; try solve[ins; desf; eauto].
  intros x y REL.
  set (REL' := REL).
  apply SUB, EQ in REL'.
  unfolder in REL'; easy.
Qed.

Lemma single_rel_compress (A : Type) (S1 S2 : A -> Prop) (x y : A)
  (MEM_X : S1 x) (MEM_Y : S2 y):
  singl_rel x y ≡ ⦗S1⦘⨾ singl_rel x y⨾ ⦗S2⦘.
Proof using.
  unfolder; split; ins; desf; eauto.
Qed.

(* TODO: move to HahnExt/SetSize.v *)
Lemma set_size_inf_minus_finite {A} (s s' : A -> Prop)
    (INF : set_size s = NOinfinity)
    (FIN : set_finite s') :
  set_size (s \₁ s') = NOinfinity.
Proof using.
  unfold set_size in *. desf.
  exfalso.
  destruct s0 as [l HH].
  destruct FIN as [l' AA].
  apply n. exists (l ++ l'). ins.
  destruct (classic (s' x)) as [IN'|NIN].
  { apply in_app_r. now apply AA. }
  apply in_app_l. apply HH.
  red. auto.
Qed.

(* TODO: move to HahnExt/SetSize.v *)
Lemma set_finite_singl {A} (a : A) : set_finite (eq a).
Proof using. exists [a]. ins. auto. Qed.

(* TODO: move to HahnExt/SetSize.v *)
Lemma set_size_inf_minus_singl {A} (s : A -> Prop) (a : A)
    (INF : set_size s = NOinfinity) :
  set_size (s \₁ eq a) = NOinfinity.
Proof using.
  apply set_size_inf_minus_finite; auto.
  apply set_finite_singl.
Qed.