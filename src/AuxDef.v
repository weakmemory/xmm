From imm Require Import Events Execution imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

Require Import Program.Basics.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From PromisingLib Require Import Language Basic.

Open Scope program_scope.

Set Implicit Arguments.

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

Lemma new_event_plus e G G'
    (NEW : ~ acts_set G e)
    (ADD : acts_set G' ≡₁ acts_set G ∪₁ eq e) :
  set_size (acts_set G' ∩₁ same_tid e) =
  NOmega.add
    (set_size (acts_set G ∩₁ same_tid e))
    (NOnum 1).
Proof using.
  rewrite ADD, set_inter_union_l.
  arewrite (eq e ∩₁ same_tid e ≡₁ eq e).
  { basic_solver. }
  unfold NOmega.add. desf.
  { now apply set_size_inf_union. }
  apply set_size_union_disjoint; auto using set_size_single.
  unfolder; ins; desf.
Qed.

Lemma new_event_plus_other_tid e t G G'
    (DIFF : t <> tid e)
    (NEW : ~ acts_set G e)
    (ADD : acts_set G' ≡₁ acts_set G ∪₁ eq e) :
  set_size (acts_set G' ∩₁ (fun e => t = tid e)) =
  set_size (acts_set G  ∩₁ (fun e => t = tid e)).
Proof using.
  apply set_size_equiv.
  rewrite ADD, set_inter_union_l.
  arewrite (eq e ∩₁ (fun e => t = tid e) ≡₁ ∅).
  { basic_solver. }
  now rewrite set_union_empty_r.
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

Lemma list_min_elt {A} {h : A} {t}
    (NODUP : NoDup (h :: t)) :
  min_elt (total_order_from_list (h :: t)) h.
Proof using.
  unfolder. unfold total_order_from_list.
  intros e F. desf.
  enough (IN : In h t) by inv NODUP.
  destruct l1 as [ | h' t']; inv F.
  { apply in_app_iff. right. desf. }
  apply in_app_iff; right.
  ins. right.
  apply in_app_iff. right.
  now left.
Qed.

Lemma equiv_seq_eq {A} (s : A -> Prop)
  (r : relation A) :
  ⦗s⦘ ⨾ (⦗s⦘ ⨾ r ⨾ ⦗s⦘) ⨾ ⦗s⦘ ≡ ⦗s⦘ ⨾ r ⨾ ⦗s⦘.
Proof using.
  basic_solver.
Qed.

Lemma in_restr_acts G e :
  acts_set G e <-> (acts_set G ∩₁ same_tid e) e.
Proof using.
  unfolder; split; ins; desf.
Qed.

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

End SubFunction.

Section ExecEqv.

Variable (G G' : execution).
Notation "'D'" := (acts_set G' \₁ acts_set G).

Record exec_equiv : Prop := {
  exeeqv_acts : acts_set G ≡₁ acts_set G';
  exeeqv_threads : threads_set G ≡₁ threads_set G';
  exeeqv_lab : lab G = lab G';
  exeeqv_rmw : rmw G ≡ rmw G';
  exeeqv_data : data G ≡ data G';
  exeeqv_addr : addr G ≡ addr G';
  exeeqv_ctrl : ctrl G ≡ ctrl G';
  exeeqv_rmw_dep : rmw_dep G ≡ rmw_dep G';
  exeeqv_rf : rf G ≡ rf G';
  exeeqv_co : co G ≡ co G';
}.

Lemma exec_equiv_eq (EQV : exec_equiv) : G = G'.
Proof using.
  destruct EQV, G, G'; f_equal.
  all: try apply set_extensionality.
  all: try apply rel_extensionality.
  all: assumption.
Qed.

Lemma sub_sub_equiv sc sc'
    (WF : Wf G')
    (SUB : sub_execution G G' sc sc')
    (SUB' : sub_execution G' G sc' sc) :
  exec_equiv.
Proof using.
  assert (HEQ : acts_set G ≡₁ acts_set G').
  { split; eauto using sub_E. }
  constructor; eauto using sub_lab, sub_threads.
  all: rewrite 1?sub_rmw,
    1?sub_data,
    1?sub_addr,
    1?sub_ctrl,
    1?sub_frmw,
    1?sub_rf,
    1?sub_co at 1; eauto.
  all: try rewrite HEQ.
  all: now rewrite <- 1?wf_rmwE,
    <- 1?wf_dataE,
    <- 1?wf_addrE,
    <- 1?wf_ctrlE,
    <- 1?wf_rmw_depE,
    <- 1?wf_rfE,
    <- 1?wf_coE; auto.
Qed.

Lemma sub_sym
    (WF_G : Wf G')
    (PREFIX : sub_execution G' G ∅₂ ∅₂)
    (ENUM_D : D ≡₁ ∅) :
  sub_execution G G' ∅₂ ∅₂.
Proof using.
    assert (E_EQ : acts_set G = acts_set G').
    { apply set_extensionality.
      split; eauto using sub_E.
      now apply set_subsetE. }
    constructor.
    all: try now symmetry; apply PREFIX.
    all: try now rewrite seq_false_l, seq_false_r.
    { now rewrite E_EQ. }
    all: rewrite 1?wf_rmwE,
                 1?wf_dataE,
                 1?wf_addrE,
                 1?wf_ctrlE,
                 1?wf_rmw_depE,
                 1?wf_rfE,
                 1?wf_coE; auto.
    all: symmetry.
    all: rewrite 1?sub_rmw,
                 1?sub_data,
                 1?sub_addr,
                 1?sub_ctrl,
                 1?sub_frmw,
                 1?sub_rf,
                 1?sub_co; eauto.
    all: rewrite E_EQ.
    all: apply equiv_seq_eq.
Qed.

Lemma sub_eq
    (WF_G : Wf G')
    (PREFIX : sub_execution G' G ∅₂ ∅₂)
    (ENUM_D : D ≡₁ ∅)
     : G = G'.
Proof using.
  eapply exec_equiv_eq, sub_sub_equiv; eauto.
  now apply sub_sym.
Qed.

End ExecEqv.