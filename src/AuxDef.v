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

Lemma wf_rmwf G
    (WF : Wf G) :
  functional (rmw G).
Proof using.
  unfolder; intros x y z RMW1 RMW2.
  assert (XR : is_r (lab G) x).
  { apply wf_rmwD in RMW1; auto. unfolder in RMW1; desf. }
  assert (XE : acts_set G x).
  { apply wf_rmwE in RMW1; auto. unfolder in RMW1; desf. }
  assert (NINIT : ~is_init x).
  { intro F. destruct x as [l | ]; ins.
    unfold is_r in XR. rewrite wf_init_lab in XR; desf. }
  destruct (classic (y = z)) as [EQ|EQ]; ins.
  apply wf_rmwi, immediateE in RMW1, RMW2; auto.
  unfolder in RMW1; unfolder in RMW2; desf.
  destruct sb_total with (G := G) (t := tid x)
                         (a := y) (b := z); ins.
  all: try now exfalso; eauto.
  all: unfolder; splits.
  all: try by (symmetry; eapply ninit_sb_same_tid; unfolder; split; eauto).
  { unfold sb in RMW1; unfolder in RMW1; desf. }
  { apply no_sb_to_init in RMW1; unfolder in RMW1; desf. }
  { unfold sb in RMW2; unfolder in RMW2; desf. }
  apply no_sb_to_init in RMW2; unfolder in RMW2; desf.
Qed.

Lemma wf_rmwff G
    (WF : Wf G) :
  functional ((rmw G) ⁻¹).
Proof using.
  unfolder; intros x y z RMW1 RMW2.
  assert (YR : is_r (lab G) y).
  { apply wf_rmwD in RMW1; auto. unfolder in RMW1; desf. }
  assert (ZR : is_r (lab G) z).
  { apply wf_rmwD in RMW2; auto. unfolder in RMW2; desf. }
  assert (YE : acts_set G y).
  { apply wf_rmwE in RMW1; auto. unfolder in RMW1; desf. }
  assert (ZE : acts_set G z).
  { apply wf_rmwE in RMW2; auto. unfolder in RMW2; desf. }
  assert (YNINIT : ~is_init y).
  { intro F. destruct y as [l | ]; ins.
    unfold is_r in YR. rewrite wf_init_lab in YR; desf. }
  assert (ZNINIT : ~is_init z).
  { intro F. destruct z as [l | ]; ins.
    unfold is_r in ZR. rewrite wf_init_lab in ZR; desf. }
  destruct (classic (y = z)) as [EQ|EQ]; ins.
  apply wf_rmwi, immediateE in RMW1, RMW2; auto.
  unfolder in RMW1; unfolder in RMW2; desf.
  destruct sb_total with (G := G) (t := tid x)
                         (a := y) (b := z); ins.
  all: try now exfalso; eauto.
  all: unfolder; splits; eauto.
  all: try by (eapply ninit_sb_same_tid; unfolder; split; eauto).
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