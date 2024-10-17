From imm Require Import Events Execution imm_s_hb.

Require Import Program.Basics.
Require Import AuxDef.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

Set Implicit Arguments.

Open Scope program_scope.

Section Thrdle.

Variable G : execution.
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).

(* Definition ppo_alt := (sb ∩ same_loc ∪ bob)⁺.
Definition hb_alt := (ppo_alt ∪ rf)⁺. *)

Lemma thrdle_sb_closed thrdle
    (INIT_MIN : min_elt thrdle tid_init)
    (INIT_LEAST : least_elt thrdle tid_init) :
  sb^? ⨾ tid ↓ thrdle ⨾ sb^? ⊆ tid ↓ thrdle.
Proof.
  rewrite crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r, !unionA.
  apply inclusion_union_l; try done.
  arewrite (tid ↓ thrdle ⨾ sb ⊆ tid ↓ thrdle).
  { unfolder. intros x y (z & TID & SB).
    unfold sb in SB; unfolder in SB.
    destruct SB as (_ & SB & _).
    destruct z as [zl | zt zn], y as [yl | yt yn]; ins.
    { exfalso. now apply INIT_MIN with (tid x). }
    desf. }
  arewrite (sb ⨾ tid ↓ thrdle ⊆ tid ↓ thrdle).
  { unfolder. intros x y (z & SB & TID).
    unfold sb in SB; unfolder in SB.
    destruct SB as (_ & SB & _).
    destruct z as [zl | zt zn], x as [xl | xt xn]; ins.
    { apply INIT_LEAST. intro F.
      apply INIT_MIN with zt. congruence. }
    desf. }
  clear. basic_solver.
Qed.

End Thrdle.

Lemma ct_l_upward_closed {A : Type} (r : relation A) s
    (UPC : upward_closed r s) :
  r⁺ ⨾ ⦗s⦘ ≡ (r ⨾ ⦗s⦘)⁺.
Proof using.
  split; [|apply inclusion_ct_seq_eqv_r].
  arewrite (r⁺ ≡ clos_trans_n1 A r).
  { unfolder; split; ins.
    all: now apply clos_trans_tn1_iff. }
  arewrite ((r ⨾ ⦗s⦘)⁺ ≡ clos_trans_n1 A (r ⨾ ⦗s⦘)).
  { unfolder; split; ins.
    all: now apply clos_trans_tn1_iff. }
  unfolder. intros x y (REL & YINE).
  generalize YINE; clear YINE.
  induction REL as [y REL | y z REL IHREL].
  all: intros HIN.
  { apply tn1_step. eauto. }
  apply Relation_Operators.tn1_trans with y; eauto.
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
  unfold irreflexive. intros x RMW.
  now apply (wf_rmwi WF), immediate_in, sb_irr in RMW.
Qed.

Lemma nodup_not_in A (e h : A) t
    (NODUP : NoDup (h :: t))
    (IN : In e t) :
  h <> e.
Proof using.
  inv NODUP.
  now destruct (classic (h = e)); subst.
Qed.

Lemma in_restr_acts G e :
  acts_set G e <-> (acts_set G ∩₁ same_tid e) e.
Proof using.
  unfold same_tid, set_inter.
  split; intro HIN; auto || easy.
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
  red. unfold set_minus, set_union, set_subset.
  split; intros; tauto.
Qed.

Lemma eq_dom_is_r lab lab' (s : actid -> Prop)
    (SUB : s ⊆₁ is_r lab)
    (LABEQ : eq_dom s lab' lab) :
  s ⊆₁ is_r lab'.
Proof using.
  unfolder. unfold is_r. intros x XIN.
  rewrite LABEQ; ins. now apply SUB.
Qed.

Lemma eq_dom_is_w lab lab' (s : actid -> Prop)
    (SUB : s ⊆₁ is_w lab)
    (LABEQ : eq_dom s lab' lab) :
  s ⊆₁ is_w lab'.
Proof using.
  unfolder. unfold is_w. intros x XIN.
  rewrite LABEQ; ins. now apply SUB.
Qed.

Lemma eq_dom_loc lab lab' (s : actid -> Prop) l
    (SUB : s ⊆₁ (fun e => loc lab e = l))
    (LABEQ : eq_dom s lab' lab) :
  s ⊆₁ (fun e => loc lab' e = l).
Proof using.
  unfolder. unfold loc. intros x XIN.
  rewrite LABEQ; ins. now apply SUB.
Qed.

Lemma eq_dom_val lab lab' (s : actid -> Prop) v
    (SUB : s ⊆₁ (fun e => val lab e = v))
    (LABEQ : eq_dom s lab' lab) :
  s ⊆₁ (fun e => val lab' e = v).
Proof using.
  unfolder. unfold val. intros x XIN.
  rewrite LABEQ; ins. now apply SUB.
Qed.

Lemma wf_rfv' G
    (WF : Wf G) :
  rf G ⊆ same_val (lab G).
Proof using.
  intros x y RF. unfold same_val.
  now apply (wf_rfv WF).
Qed.

Lemma collect_rel_eq_dom {A B : Type} (f g : A -> B) r
    (EQ : eq_dom (dom_rel r ∪₁ codom_rel r) f g) :
  f ↑ r ≡ g ↑ r.
Proof using.
  split; intros x' y' (x & y & R & XEQ & YEQ).
  all: subst x'; subst y'.
  all: exists x, y; splits; ins.
  all: rewrite EQ; ins.
  all: clear - R; basic_solver.
Qed.

Lemma collect_rel_eq_dom' {A B : Type} (f g : A -> B) r s
    (EQ : eq_dom s f g)
    (RESTR : r ≡ ⦗s⦘ ⨾ r ⨾ ⦗s⦘) :
  f ↑ r ≡ g ↑ r.
Proof using.
  apply collect_rel_eq_dom.
  eapply eq_dom_mori with (x := s); eauto.
  unfold flip. rewrite RESTR.
  clear. basic_solver.
Qed.

Lemma same_lab_u2v_dom_eq_loc {A : Type} l
    (s : A -> Prop)
    lab1
    lab2
    (DOM : same_lab_u2v_dom s lab1 lab2) :
  s ∩₁ (fun e => loc lab1 e = l) ≡₁ s ∩₁ (fun e => loc lab2 e = l).
Proof using.
  unfold set_inter.
  split; intros x (XIN & LOC); splits; auto.
  all: rewrite same_lab_u2v_dom_loc with (s := s) (lab2 := lab2) in *.
  all: assumption.
Qed.

Lemma expand_transitive {A : Type} (r : relation A) s s'
    (TRANS : transitive r)
    (SCLOSED : upward_closed r s)
    (NOTIN : s' ⊆₁ set_compl (dom_rel r)) :
  transitive (r ∪ s × s').
Proof using.
  unfold union, cross_rel.
  intros x y z.
  intros [R1 | [INS1 EQE1]] [R2 | [INS2 EQE2]].
  all: eauto.
  exfalso. apply NOTIN with y; [exact EQE1|].
  exists z. exact R2.
Qed.

Lemma collect_rel_id {A : Type} (r : relation A) :
  id ↑ r ≡ r.
Proof using.
  red.
  unfold id, collect_rel, inclusion.
  split; intros x y HREL.
  { destruct HREL as (x' & y' & REL & XEQ & YEQ).
    subst. exact REL. }
  exists x, y. splits; auto.
Qed.

Lemma seq_eqv_minus_r {A : Type} r1 r2 (s : A -> Prop) :
  (r1 \ r2) ⨾ ⦗s⦘ ≡ (r1 ⨾ ⦗s⦘) \ (r2 ⨾ ⦗s⦘).
Proof using.
  unfold minus_rel, seq, eqv_rel.
  split; intros x y HREL.
  { destruct HREL as (y' & (R1 & NR2) & EQ & YIN). subst y'.
    split; eauto. intros (y' & (R2 & EQ & _)). congruence. }
  destruct HREL as ((y' & R1 & EQ & YIN) & NEG). subst y'.
  exists y. splits; auto.
  intro FALSO. apply NEG. eauto.
Qed.