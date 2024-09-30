From imm Require Import Events Execution.
Require Import xmm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_bob.
From imm Require Import SubExecution.
From imm Require Import Events Execution Execution_eco.
Require Import xmm_comb_rel.

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

Definition ppo_alt := (sb ∩ same_loc ∪ bob)⁺.
Definition hb_alt := (ppo_alt ∪ rf)⁺.
Definition rpo_imm :=
  ⦗R ∩₁ is_rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ is_acq⦘ ∪
  ⦗is_acq⦘ ⨾ sb ∪
  sb ⨾ ⦗is_rel⦘ ∪
  ⦗F ∩₁ is_rel⦘ ⨾ sb ⨾ ⦗W ∩₁ is_rlx⦘.
Definition rpo := rpo_imm⁺.
Definition rhb := (sb ∩ same_loc ∪ rpo ∪ sw)⁺.
Definition vf := ⦗E⦘ ⨾ ⦗W⦘ ⨾ rf^? ⨾ hb^?.
Definition srf := (vf ∩ same_loc) ⨾ ⦗R⦘ \ (co ⨾ vf).

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
Qed . 

Lemma rpo_imm_in_sb : rpo_imm ⊆ sb.
Proof using.
  unfold rpo_imm.
  basic_solver.
Qed.

Lemma rpo_in_sb : rpo ⊆ sb.
Proof using.
  unfold rpo. rewrite rpo_imm_in_sb.
  apply ct_of_trans. apply sb_trans.
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

Lemma wf_rpoE
    (WF : Wf G) :
  rpo ≡ ⦗E⦘ ⨾ rpo ⨾ ⦗E⦘.
Proof using.
  split; [| basic_solver].
  unfolder. intros x y REL.
  splits; ins.
  all: apply rpo_in_sb in REL.
  all: unfold sb in REL; unfolder in REL; desf.
Qed.

Lemma wf_vfE
    (WF : Wf G) :
  vf ≡ ⦗E⦘ ⨾ vf ⨾ ⦗E⦘.
Proof using.
  split; [| basic_solver].
  unfold vf.
  rewrite (wf_hbE WF), (wf_rfE WF).
  basic_solver 12.
Qed.

Lemma vf_dom : dom_rel vf ⊆₁ W.
Proof using.
  unfold vf. basic_solver.
Qed.

Lemma wf_srfE
    (WF : Wf G) :
  srf ≡ ⦗E⦘ ⨾ srf ⨾ ⦗E⦘.
Proof using.
  split; [| basic_solver]. unfold srf.
  rewrite wf_vfE at 1 by auto.
  unfolder. ins. desf. splits; eauto.
Qed.

Lemma wf_srfD : srf ≡ ⦗W⦘ ⨾ srf ⨾ ⦗R⦘.
Proof using.
  split; [| basic_solver]. unfold srf.
  intros x y SRF. unfolder in SRF. desf.
  unfolder; ins; desf; splits; ins.
  { apply vf_dom. now exists y. }
  exists y; ins.
Qed.

Lemma wf_srf_loc : srf ⊆ same_loc.
Proof using.
  unfold srf. intros x y SRF.
  unfolder in SRF; desf.
Qed.

Lemma wf_rhbE
    (WF : Wf G) :
  rhb ≡ ⦗E⦘ ⨾ rhb ⨾ ⦗E⦘.
Proof using.
  unfold rhb. rewrite wf_swE, wf_rpoE, wf_sbE; auto.
  assert (SB_SAMELOC : (⦗E⦘ ⨾ sb ⨾ ⦗E⦘) ∩ same_loc ≡ ⦗E⦘ ⨾ sb ∩ same_loc ⨾ ⦗E⦘).
  { basic_solver 10. }
  rewrite SB_SAMELOC.
  rewrite <- !seq_union_r, <- !seq_union_l.
  seq_rewrite <- ct_seq_eqv_l. rewrite <- seqA.
  now seq_rewrite <- ct_seq_eqv_r.
Qed.

Lemma rf_sub_vf (WF : Wf G) : rf ⊆ vf.
Proof using.
  rewrite WF.(wf_rfD), WF.(wf_rfE).
  unfold vf; unfolder; ins; desf.
  splits; eauto.
Qed.

Lemma wf_srff'
    (CO_TOT : forall ol,
      is_total (E ∩₁ W ∩₁ (fun x => loc x = ol)) co
    ) :
  functional srf⁻¹.
Proof using.
  unfolder; unfold srf. intros x y z (VF1 & CO1) (VF2 & CO2).
  tertium_non_datur (y = z) as [EQ|NEQ]; ins; exfalso.
  destruct CO_TOT with (a := y) (b := z)
                       (ol := loc x) as [CO|CO].
  all: ins; unfolder in *; desf; splits; eauto.
  all: try now (apply vf_dom; eexists; eauto).
  { unfold vf in VF1. unfolder in VF1; desf. }
  unfold vf in VF2. unfolder in VF2; desf.
Qed.

Lemma wf_srff (WF : Wf G) : functional srf⁻¹.
Proof using.
  apply wf_srff', WF.
Qed.

Lemma srf_exists b
    (HIN : E b)
    (FIN_ACTS : set_finite (E \₁ is_init))
    (WF : Wf G)
    (IS_R : R b) :
  exists a, srf a b.
Proof using.
  assert (HLOC : exists l, loc b = Some l); desf.
  { unfold is_r in IS_R. unfold loc. desf. eauto. }
  assert (HINIT : E (InitEvent l)).
  { apply WF; eauto. }
  assert (INILAB : lab (InitEvent l) = Astore Xpln Opln l 0).
  { apply WF. }
  assert (INILOC : loc (InitEvent l) = Some l).
  { unfold loc. now rewrite (wf_init_lab WF). }
  assert (INIW : W (InitEvent l)).
  { unfold is_w, loc. desf. }
  assert (INISB : sb (InitEvent l) b).
  { eapply init_ninit_sb, read_or_fence_is_not_init; eauto. }
  assert (INIVF : vf (InitEvent l) b).
  { unfold vf. exists (InitEvent l).
    splits; ins.
    hahn_rewrite <- sb_in_hb.
    basic_solver 21. }
  assert (ACT_LIST : exists El, E ∩₁ Loc_ l ≡₁ (fun x => In x El)); desf.
  { apply set_finiteE in FIN_ACTS. desf.
    exists (InitEvent l :: filterP (Loc_ l) findom). split; intros x HSET.
    { destruct HSET as [EX LX].
      ins. destruct x as [xl | xt xn]; ins; eauto.
      { unfold loc in LX. rewrite (wf_init_lab WF) in LX.
        desf. eauto. }
      right.
      apply in_filterP_iff; split; try now apply LX.
      apply FIN_ACTS0. split; ins. }
    ins. desf. apply in_filterP_iff in HSET.
    destruct HSET as [INX LX]. split; ins.
    now apply FIN_ACTS0. }
  forward (eapply last_exists with (s:= co ⨾ ⦗fun x => vf x b⦘)
                                   (dom := filterP W El)
                                   (a := InitEvent l)).
  { eapply acyclic_mon.
    apply trans_irr_acyclic; [apply co_irr | apply co_trans]; eauto.
    basic_solver. }
  { ins.
    assert (A: (co ⨾ ⦗fun x : actid => vf x b⦘)^? (InitEvent l) c).
    { apply rt_of_trans; try done.
      apply transitiveI.
      arewrite_id ⦗fun x : actid => vf x b⦘ at 1.
      rewrite seq_id_l.
      arewrite (co ⨾ co ⊆ co); [|done].
      apply transitiveI.
      eapply co_trans; eauto. }
    unfolder in A; desf.
    { apply in_filterP_iff; split; auto.
      by apply ACT_LIST. }
    apply in_filterP_iff.
    hahn_rewrite WF.(wf_coE) in A.
    hahn_rewrite WF.(wf_coD) in A.
    hahn_rewrite WF.(wf_col) in A.
    unfold same_loc in *; unfolder in *; desf; splits; eauto.
    apply ACT_LIST. split; ins.
    rewrite <- A3. unfold loc.
    now rewrite (wf_init_lab WF). }
  ins; desc.
  assert (A: (co ⨾ ⦗fun x : actid => vf x b⦘)^? (InitEvent l) b0).
  { apply rt_of_trans; [|by subst].
    apply transitiveI.
    arewrite_id ⦗fun x : actid => vf x b⦘ at 1.
    rewrite seq_id_l.
    arewrite (co ⨾ co ⊆ co); [|done].
    apply transitiveI.
    eapply co_trans; eauto. }
  assert (loc b0 = Some l).
  { unfolder in A; desf.
    hahn_rewrite WF.(wf_col) in A.
    unfold same_loc in *; desf; unfolder in *; congruence. }
  exists b0; red; split.
  { unfold urr, same_loc.
    unfolder in A; desf; unfolder; ins; desf; splits; try basic_solver 21; congruence. }
  unfold max_elt in *.
  unfolder in *; ins; desf; intro; desf; basic_solver 11.
Qed.

Lemma srf_in_sb_rf :
  srf ⊆ (sb ∪ rf)⁺.
Proof using.
  admit.
Admitted.

Lemma ct_unit_left A (r : relation A) :
    r ⨾ r⁺ ⊆ r⁺.
Proof.
  arewrite (r ⊆ r⁺) at 1. apply ct_ct.
Qed.

Lemma trans_helper_swapped A (r r' : relation A)
        (TRANS : transitive r) :
    r ⨾ (r' ∪ r)⁺ ⊆ r ∪ (r ⨾ r'⁺)⁺ ⨾ r^?.
Proof using.
  rewrite path_union2. rewrite !seq_union_r.
  arewrite (r ⨾ r＊ ⊆ r⁺).
  arewrite (r ⨾ r⁺ ⊆ r⁺) by apply ct_unit_left.
  arewrite (r⁺ ⊆ r).
  arewrite (r'⁺ ⊆ r'＊).
  rels.
  rewrite rtE at 1. rewrite seq_union_r, seq_id_r.
  unionL; eauto with hahn.
  all: unionR right.
  { rewrite <- ct_step with (r := r ;; r'⁺).
    basic_solver 10. }
  rewrite ct_rotl, <- !seqA.
  rewrite <- ct_begin.
  rewrite !seqA.
  rewrite rtE, !seq_union_r, seq_id_r.
  arewrite ((r ⨾ r'⁺)⁺ ⨾ r ⨾ r'⁺ ⊆ (r ⨾ r'⁺)⁺).
  { now rewrite ct_unit. }
  rewrite crE, seq_union_r, seq_id_r.
  eauto with hahn.
Qed.

End AuxRel.
