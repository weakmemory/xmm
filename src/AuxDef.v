From imm Require Import Events Execution imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

Section HbAlt.

Variable (G : execution).
Notation "'lab'" := (lab G).
Notation "'same_loc'" := (same_loc lab).
Notation "'bob'" := (bob G).
Notation "'rf'" := (rf G).
Notation "'sb'" := (sb G).

Definition ppo_alt := (sb ∩ same_loc ∪ bob)⁺.
Definition hb_alt := (ppo_alt ∪ rf)⁺.

End HbAlt.

Definition edges_to {A} (e : A) := (fun _ _ => True) ⨾ ⦗eq e⦘.
Hint Unfold edges_to : unfolderDb.

Definition rmw_delta e e' : relation actid :=
  eq e × eq_opt e'.
#[global]
Hint Unfold rmw_delta : unfolderDb.

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

Lemma set_size_inf_union {A} (s s' : A -> Prop)
  (INF : set_size s = NOinfinity) :
  set_size (s ∪₁ s') = NOinfinity.
Proof using.
  unfold set_size in *. desf.
  exfalso.
  destruct s0 as [l HH].
  apply n. exists (List.filter (fun x => ifP s x then true else false) l). ins.
  apply in_filter_iff.
  splits; try apply HH; basic_solver.
Qed.

Lemma immediate_total {A} (x y z : A) (s : A -> Prop) (r : relation A)
  (X : s x)
  (Y : s y)
  (Z : s z)
  (TOTAL : is_total s r)
  (FIRST : r x z)
  (IMM : immediate r y z)
  (NEQ : x <> y) :
  r x y.
Proof using.
  unfolder in IMM. desc.
  destruct (TOTAL x X y Y NEQ).
  all: auto || exfalso; eauto.
Qed.

Lemma rmw_irr G
    (WF : Wf G) :
  irreflexive (rmw G).
Proof using.
  rewrite wf_rmwD; auto.
  unfold is_r, is_w.
  unfolder; ins; desf.
Qed.

Lemma rmw_dep_irr G
    (WF : Wf G) :
  irreflexive (rmw_dep G).
Proof using.
  eapply irreflexive_inclusion, sb_irr.
  apply WF.
Qed.

Definition one_dir {A} s (r : relation A) : Prop :=
  dom_rel (r ⨾ ⦗s⦘) ∩₁ codom_rel (⦗s⦘ ⨾ r) ≡₁ ∅.

Lemma one_dir_assym_helper_1 {A} {a : A} {s r}
    (NODOM : ~dom_rel (r ⨾ ⦗s⦘) a) :
  ⦗eq a⦘ ⨾ r ⨾ ⦗s⦘ ≡ ∅₂.
Proof using.
  split; [| basic_solver].
  unfolder. ins. desf.
  apply NODOM. unfolder.
  eauto.
Qed.

Lemma one_dir_assym_helper_2 {A} {a : A} {s r}
    (NODOM : ~codom_rel (⦗s⦘ ⨾ r) a) :
    ⦗s⦘ ⨾ r ⨾ ⦗eq a⦘ ≡ ∅₂.
Proof using.
  split; [| basic_solver].
  unfolder. ins. desf.
  apply NODOM. unfolder.
  eauto.
Qed.

Lemma one_dir_assym_1 {A} {a : A} {s r}
    (ONE_DIR : one_dir s r)
    (IN : dom_rel (r ⨾ ⦗s⦘) a) :
  ⦗s⦘ ⨾ r ⨾ ⦗eq a⦘ ≡ ∅₂.
Proof using.
  apply one_dir_assym_helper_2. intro F.
  change False with (∅ a).
  apply ONE_DIR; now split.
Qed.

Lemma one_dir_assym_2 {A} {a : A} {s r}
    (ONE_DIR : one_dir s r)
    (IN : codom_rel (⦗s⦘ ⨾ r) a) :
  ⦗eq a⦘ ⨾ r ⨾ ⦗s⦘ ≡ ∅₂.
Proof using.
  apply one_dir_assym_helper_1. intro F.
  change False with (∅ a).
  apply ONE_DIR; now split.
Qed.

Lemma one_dir_irrefl {A} {a r} (s : A -> Prop)
    (IN : s a)
    (ONE_DIR : one_dir s r) :
  ⦗eq a⦘ ⨾ r ⨾ ⦗eq a⦘ ≡ ∅₂.
Proof using.
  split; [| basic_solver].
  unfolder; intros x y R. desf.
  assert (LEFT : dom_rel (r ⨾ ⦗s⦘) y).
  { unfolder. ins. eauto. }
  assert (RIGHT : codom_rel (⦗s⦘ ⨾ r ) y).
  { unfolder. ins. eauto. }
  change False with (∅ y). apply ONE_DIR.
  split; eauto.
Qed.

Lemma one_dir_dom {A} {s'} {r : relation A} s
    (ONE_DIR : one_dir s r)
    (SUB : s' ⊆₁ s) :
  one_dir s' r.
Proof using.
  unfold one_dir in *.
  split; [| basic_solver].
  rewrite SUB. apply ONE_DIR.
Qed.

Lemma one_dir_sub {A} {s} (r r' : relation A)
    (ONE_DIR : one_dir s r)
    (SUB : r' ⊆ r) :
  one_dir s r'.
Proof using.
  unfold one_dir.
  split; [| basic_solver].
  rewrite SUB. apply ONE_DIR.
Qed.

Lemma rmw_one_dir G
    (WF : Wf G) :
  one_dir (acts_set G) (rmw G).
Proof using.
  unfold one_dir.
  rewrite wf_rmwD; auto.
  unfold is_w, is_r.
  unfolder; split; ins; desf.
Qed.

Lemma rf_one_dir G
    (WF : Wf G) :
  one_dir (acts_set G) (rf G).
Proof using.
  unfold one_dir.
  rewrite wf_rfD; auto.
  unfold is_w, is_r.
  unfolder; split; ins; desf.
Qed.

Lemma rmw_dense G x y
    (WF : Wf G)
    (IN : (acts_set G) y)
    (RMW : (rmw G) x y) :
  (acts_set G) x.
Proof using.
  apply wf_rmwi, immediate_in in RMW; eauto.
  unfold sb in RMW. unfolder in RMW.
  desf.
Qed.