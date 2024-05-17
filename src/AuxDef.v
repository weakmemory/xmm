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

Definition edges_to {A} (e : A) := (fun _ _ => True) ⨾ ⦗eq e⦘.
Hint Unfold edges_to : unfolderDb.

Definition rmw_delta e e' : relation actid :=
  eq e × eq_opt e'.
#[global]
Hint Unfold rmw_delta : unfolderDb.

Lemma total_order_from_list_l {A} (l1 l2 : list A) :
  total_order_from_list l1 ⊆
    total_order_from_list (l1 ++ l2).
Proof using.
  unfold total_order_from_list. unfolder.
  intros x y HREL. destruct HREL as (l'0 & l'1 & l'2 & HREL).
  subst l1. exists l'0, l'1, (l'2 ++ l2).
  do 2 (rewrite <- app_assoc; ins).
Qed.

Lemma total_order_from_list_r {A} (l1 l2 : list A) :
  total_order_from_list l2 ⊆
    total_order_from_list (l1 ++ l2).
Proof using.
  unfold total_order_from_list. unfolder.
  intros x y HREL. destruct HREL as (l'0 & l'1 & l'2 & HREL).
  subst l2. exists (l1 ++ l'0), l'1, l'2.
  do 2 (rewrite <- app_assoc; ins).
Qed.

Lemma in_iff {A} (x : A) l
    (IN : In x l) :
  exists l1 l2, l = l1 ++ x :: l2.
Proof using.
  induction l as [ | h t IHL]; ins.
  desf.
  { exists [], t; ins. }
  destruct (IHL IN) as (l1 & l2 & HEQ).
  subst t. exists (h :: l1), l2. ins.
Qed.

Lemma total_order_from_list_bridge {A} (x y : A) l1 l2
    (XIN : In x l1)
    (YIN : In y l2) :
  total_order_from_list (l1 ++ l2) x y.
Proof using.
  unfold total_order_from_list.
  destruct (in_iff x _ XIN) as (l1x & l2x & XEQ).
  destruct (in_iff y _ YIN) as (l1y & l2y & YEQ).
  subst. exists l1x, (l2x ++ l1y), l2y.
  rewrite <- !app_assoc. ins.
Qed.

Lemma same_lab_u2v_compose {A} lab1 lab2 (f : A -> actid)
    (U2V : same_lab_u2v lab1 lab2) :
  same_lab_u2v (lab1 ∘ f) (lab2 ∘ f).
Proof using.
  unfold same_lab_u2v, same_lab_u2v_dom in *.
  ins. now apply U2V.
Qed.

Lemma seq_absorb_l {A} s s' (r : relation A)
    (SUB : s ⊆₁ s') :
  ⦗s⦘ ⨾ ⦗s'⦘ ⨾ r ≡ ⦗s⦘ ⨾ r.
Proof using.
  now rewrite <- seqA, <- id_inter, set_inter_absorb_r.
Qed.

Lemma seq_absorb_r {A} s s' (r : relation A)
    (SUB : s ⊆₁ s') :
  (r ⨾ ⦗s'⦘) ⨾ ⦗s⦘ ≡  r ⨾ ⦗s⦘.
Proof using.
  now rewrite seqA, <- id_inter, set_inter_absorb_l.
Qed.

Lemma seq_absorb {A} s1 s1' s2 s2' (r : relation A)
    (SUB1 : s1 ⊆₁ s1')
    (SUB2 : s2 ⊆₁ s2') :
  ⦗s1⦘ ⨾ (⦗s1'⦘ ⨾ r ⨾ ⦗s2'⦘) ⨾ ⦗s2⦘ ≡ ⦗s1⦘ ⨾ r ⨾ ⦗s2⦘.
Proof using.
  rewrite seqA, seq_absorb_l, seq_absorb_r; ins.
Qed.

Lemma seq_restr_eq_prod {A} s s' (r : relation A) :
  ⦗s⦘ ⨾ r ⨾ ⦗s'⦘ ≡ r ∩ s × s'.
Proof using.
  basic_solver.
Qed.

Lemma seq_restr_helper {A} s1 s1' s2 s2' (r : relation A)
    (SUB1 : s1 ⊆₁ s1')
    (SUB2 : s2 ⊆₁ s2') :
  ⦗s1⦘ ⨾ r ⨾ ⦗s2⦘ ⊆ ⦗s1'⦘ ⨾ r ⨾ ⦗s2'⦘.
Proof using.
  red in SUB1, SUB2. rewrite !seq_restr_eq_prod.
  intros x y (REL & L & R). repeat (red; split; ins).
  all: eauto.
Qed.

Lemma upd_compose (A B C : Type) a b
    (f : B -> C)
    (g : A -> B)
    (INJ : inj_dom ⊤₁ g) :
  upd (f ∘ g) a b = (upd f (g a) b) ∘ g.
Proof using.
  unfold compose. apply functional_extensionality. intro x.
  tertium_non_datur (x = a) as [HEQA|NEQA]; subst.
  { now rewrite !upds. }
  rewrite !updo; ins.
  intro F. apply INJ in F; ins.
Qed.

Lemma set_collect_interE (A B : Type) (f : A -> B) s s'
    (INJ : inj_dom ⊤₁ f) :
  f ↑₁ (s ∩₁ s') ≡₁ f ↑₁ s ∩₁ f ↑₁ s'.
Proof using.
  split; [apply set_collect_inter |].
  unfolder; intros x SET; desf.
  apply INJ in SET1; ins; desf.
  exists y0; splits; ins.
Qed.

Lemma collect_rel_restr {A B} (f : A -> B) s r
    (FINJ : inj_dom ⊤₁ f) :
  restr_rel (f ↑₁ s) (f ↑ r) ≡ f ↑ (restr_rel s r).
Proof using.
  rewrite !restr_relE, !collect_rel_seq, collect_rel_eqv; ins.
  all: eapply inj_dom_mori; eauto; ins.
Qed.

Lemma conjugate_sub {A} r (f : A -> option A)
    (m m' : A -> A)
    (MINJ : inj_dom ⊤₁ m)
    (MSURJ : forall y, exists x, y = m x)
    (INV : m' ∘ m = id) :
  Some ↓ ((option_map m ∘ f ∘ m') ↑ (m ↑ r)) ⊆
    m ↑ (Some ↓ (f ↑ r)).
Proof using.
  rewrite <- !collect_rel_compose, Combinators.compose_assoc.
  rewrite INV, Combinators.compose_id_right.
  unfold compose. unfolder; ins; desf.
  destruct MSURJ with x as [x'0 XEQ].
  destruct MSURJ with y as [y'0 YEQ].
  subst; exists x'0, y'0; splits; ins.
  exists x', y'. splits; ins.
  { destruct (f x') eqn:HEQ; ins.
    f_equal. apply MINJ; ins. congruence. }
  destruct (f y') eqn:HEQ; ins.
  f_equal. apply MINJ; ins. congruence.
Qed.

Lemma map_rel_eqvE (A B : Type) (f : A -> B) d
    (INJ : inj_dom ⊤₁ f) :
  ⦗f ↓₁ d⦘ ≡ f ↓ ⦗d⦘.
Proof using.
  split; [apply map_rel_eqv |].
  unfolder; intros x y; desf.
  splits; desf.
  now apply INJ.
Qed.

Lemma collect_rel_interE (A B : Type) (f : A -> B) r r'
    (INJ : inj_dom ⊤₁ f) :
  f ↑ (r ∩ r') ≡ f ↑ r ∩ f ↑ r'.
Proof using.
  split; [apply collect_rel_inter |].
  unfolder; intros x y REL; desf.
  apply INJ in REL1, REL2; ins; desf.
  exists x'0, y'0; splits; ins.
Qed.

Lemma restr_irr A (x : A) s r
    (IRR : irreflexive r) :
  restr_rel (s ∩₁ eq x) r ≡ ∅₂.
Proof using.
  destruct (classic (s x)) as [HIN|HIN]; [| basic_solver].
  arewrite (s ∩₁ eq x ≡₁ eq x) by basic_solver.
  now apply restr_irrefl_eq.
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

Lemma nodup_not_in A (e h : A) t
    (NODUP : NoDup (h :: t))
    (IN : In e t) :
  h <> e.
Proof using.
  inv NODUP.
  now destruct (classic (h = e)); subst.
Qed.

Lemma equiv_seq_eq {A} (s : A -> Prop)
  (r : relation A) :
  ⦗s⦘ ⨾ (⦗s⦘ ⨾ r ⨾ ⦗s⦘) ⨾ ⦗s⦘ ≡ ⦗s⦘ ⨾ r ⨾ ⦗s⦘.
Proof using.
  basic_solver.
Qed.

Lemma seq_eq_prod {A} (a : A) r :
  ⦗eq a⦘ ⨾ r ≡ eq a × codom_rel (⦗eq a⦘ ⨾ r).
Proof using.
  basic_solver.
Qed.

Lemma in_restr_acts G e :
  acts_set G e <-> (acts_set G ∩₁ same_tid e) e.
Proof using.
  unfolder; split; ins; desf.
Qed.

Lemma wf_rmwff G
    (WF : Wf G) :
  functional ((rmw G)⁻¹).
Proof using.
  unfolder; intros x y z RMW1 RMW2.
  assert (ZINIT : ~is_init z).
  { apply read_or_fence_is_not_init with (G := G); ins.
    left. apply WF.(wf_rmwD) in RMW2. unfolder in RMW2; desf. }
  tertium_non_datur (y = z) as [EQ|NEQ]; ins.
  apply WF.(wf_rmwi) in RMW1, RMW2. unfolder in *. desf.
  destruct sb_semi_total_r with (G := G) (x := x)
                                (y := y) (z := z) as [SB|SB].
  all: ins.
  all: exfalso; eauto.
Qed.

Lemma set_minus_union_r A (s1 s2 s3 : A -> Prop) :
  s1 \₁ (s2 ∪₁ s3) ≡₁ s1 \₁ s2 \₁ s3.
Proof using.
  split; unfolder; ins; desf.
  { splits; auto. }
  splits; auto.
  apply and_not_or; auto.
Qed.

Lemma seq_seq_inter A (a b c d : A -> Prop) r :
  ⦗a⦘ ⨾ (⦗b⦘ ⨾ r ⨾ ⦗c⦘) ⨾ ⦗d⦘ ≡ ⦗a ∩₁ b⦘ ⨾ r ⨾ ⦗c ∩₁ d⦘.
Proof using.
  basic_solver.
Qed.