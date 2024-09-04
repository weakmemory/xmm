From imm Require Import Events Execution imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

Require Import Program.Basics.
Require Import AuxDef.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.
From imm Require Import CombRelations.

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
  basic_solver.
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

(* Lemma conjugate_sub {A} r (f : A -> option A)
    (m m' : A -> A)
    (MINJ : inj_dom ⊤₁ m)
    (MSURJ : surj_dom ⊤₁ m)
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
Qed. *)

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

Lemma nsame_loc_nrmw G x y
    (WF : Wf G)
    (NLOC : ~same_loc (lab G) x y) :
  ~rmw G x y.
Proof using.
  intro F. now apply (wf_rmwl WF) in F.
Qed.

Lemma rsrw_a_b_nrmw_dep G x y
    (IS_W : is_w (lab G) x)
    (WF : Wf G) :
  ~rmw_dep G x y.
Proof using.
  intro F. apply (wf_rmw_depD WF) in F.
  unfolder in F. destruct F as (IS_R & _ & _ ).
  unfold is_r, is_w in *. desf.
Qed.

Lemma w_nrmwdep G y
    (IS_W : is_w (lab G) y)
    (WF : Wf G) :
  ~codom_rel (rmw_dep G) y.
Proof using.
  intros [x F]. apply (wf_rmw_depD WF) in F.
  unfolder in F. destruct F as (_ & _ & IS_R).
  unfold R_ex, is_w in *. desf.
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
  unfolder. intros x y RF. unfold same_val.
  now apply (wf_rfv WF).
Qed.

Lemma collect_rel_eq_dom {A B : Type} (f g : A -> B) r
    (EQ : eq_dom (dom_rel r ∪₁ codom_rel r) f g) :
  f ↑ r ≡ g ↑ r.
Proof using.
  unfolder. split; intros x' y' (x & y & R & XEQ & YEQ).
  all: subst x'; subst y'.
  all: exists x, y; splits; ins.
  all: rewrite EQ; ins.
  all: basic_solver.
Qed.

Lemma collect_rel_eq_dom' {A B : Type} (f g : A -> B) r s
    (EQ : eq_dom s f g)
    (RESTR : r ≡ ⦗s⦘ ⨾ r ⨾ ⦗s⦘) :
  f ↑ r ≡ g ↑ r.
Proof using.
  apply collect_rel_eq_dom.
  eapply eq_dom_mori with (x := s); eauto.
  unfold flip. rewrite RESTR. basic_solver.
Qed.

Lemma same_lab_u2v_dom_eq_loc {A : Type} l
    (s : A -> Prop)
    lab1
    lab2
    (DOM : same_lab_u2v_dom s lab1 lab2) :
  s ∩₁ (fun e => loc lab1 e = l) ≡₁ s ∩₁ (fun e => loc lab2 e = l).
Proof using.
  unfolder. split; intros x (XIN & LOC); splits; ins.
  all: rewrite same_lab_u2v_dom_loc with (s := s) (lab2 := lab2) in *.
  all: ins.
Qed.

Lemma expand_transitive {A : Type} (r : relation A) s s'
    (TRANS : transitive r)
    (SCLOSED : upward_closed r s)
    (NOTIN : s' ⊆₁ set_compl (dom_rel r)) :
  transitive (r ∪ s × s').
Proof using.
  unfolder. intros x y z.
  intros [R1 | [INS1 EQE1]] [R2 | [INS2 EQE2]].
  all: eauto.
  exfalso. eapply NOTIN.
  all: unfolder; eauto.
Qed.

Lemma collect_rel_id {A : Type} (r : relation A) :
  id ↑ r ≡ r.
Proof using.
  unfold id. unfolder. split; intros x y HREL; ins.
  all: desf; eauto.
Qed.
