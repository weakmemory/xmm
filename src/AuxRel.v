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

Section AuxRel.

Variable G : execution.
Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'is_acq'" := (is_acq lab).
Notation "'is_rel'" := (is_rel lab).
Notation "'is_rlx'" := (is_rlx lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'ppo'" := (ppo G).
Notation "'hb'" := (hb G).
Notation "'psc'" := (imm.psc G).
Notation "'sw'" := (sw G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'F'" := (is_f lab).
Notation "'bob'" := (bob G).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Definition ppo_alt := (sb ∩ same_loc ∪ bob)⁺.
Definition hb_alt := (ppo_alt ∪ rf)⁺.
Definition rpo :=
  sb ∩ same_loc ∪
  ⦗is_acq⦘ ⨾ sb ⨾ ⦗is_rel⦘ ∪
  ⦗R ∩₁ is_rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ is_acq⦘ ∪
  ⦗is_acq⦘ ⨾ sb ∪
  sb ⨾ ⦗is_rel⦘ ∪
  ⦗F ∩₁ is_rel⦘ ⨾ sb ⨾ ⦗W ∩₁ is_rlx⦘.
Definition rhb := (rpo ∪ sw)⁺.
Definition vf := ⦗E⦘ ⨾ ⦗W⦘ ⨾ rf^? ⨾ hb^?.
Definition srf := ((vf ⨾ sb) ∩ same_loc) ⨾ ⦗R⦘ \ (co ⨾ vf ⨾ sb).

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

Lemma rpo_in_sb : rpo ⊆ sb.
Proof using.
  unfold rpo. unfolder. ins. desf.
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

Lemma wf_vfE_left : vf ≡ ⦗E⦘ ⨾ vf.
Proof using.
  split; [| basic_solver].
  unfold vf. basic_solver 11.
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

Lemma vf_d_left : vf ≡ ⦗W⦘ ⨾ vf.
Proof using.
  unfold vf. basic_solver 11.
Qed.

Lemma vf_sb_in_vf :
  vf ⨾ sb ⊆ vf.
Proof using.
  unfold vf. rewrite sb_in_hb.
  hahn_frame. rewrite rewrite_trans_seq_cr_l.
  all: eauto using hb_trans.
  basic_solver.
Qed.

Lemma wf_srfE : srf ≡ ⦗E⦘ ⨾ srf ⨾ ⦗E⦘.
Proof using.
  split; [| basic_solver]. apply dom_helper_3.
  unfold srf, sb. rewrite wf_vfE_left.
  basic_solver.
Qed.

Lemma wf_srfD : srf ≡ ⦗W⦘ ⨾ srf ⨾ ⦗R⦘.
Proof using.
  split; [| basic_solver]. apply dom_helper_3.
  unfold srf. rewrite vf_d_left. hahn_frame.
  basic_solver.
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
  unfold rhb. rewrite wf_swE, wf_rpoE; auto.
  rewrite <- seq_union_r, <- seq_union_l.
  seq_rewrite <- ct_seq_eqv_l.
  rewrite <- seqA.
  now seq_rewrite <- ct_seq_eqv_r.
Qed.

Lemma rf_sub_vf (WF : Wf G) : rf ⊆ vf.
Proof using.
  rewrite WF.(wf_rfD), WF.(wf_rfE).
  unfold vf; unfolder; ins; desf.
  splits; eauto.
Qed.

Lemma srf_in_vf : srf ⊆ vf.
Proof using.
  unfold srf. rewrite vf_sb_in_vf at 1.
  basic_solver 11.
Qed.

Lemma srf_in_vf_sb : srf ⊆ vf ⨾ sb.
Proof using.
  unfold srf. basic_solver.
Qed.

Lemma wf_srff'
    (CO_TOT : forall ol,
      is_total (E ∩₁ W ∩₁ (fun x => loc x = ol)) co
    ) :
  functional srf⁻¹.
Proof using.
  unfolder. intros x y z SRF1 SRF2.
  destruct (classic (y = z)) as [EQ|NEQ]; ins.
  destruct CO_TOT with (a := y) (b := z)
                       (ol := loc x) as [CO|CO].
  all: ins; repeat split.
  all: try now apply wf_srf_loc.
  all: try now (apply wf_srfE in SRF1; unfolder in SRF1; desf).
  all: try now (apply wf_srfE in SRF2; unfolder in SRF2; desf).
  all: try now (apply wf_srfD in SRF1; unfolder in SRF1; desf).
  all: try now (apply wf_srfD in SRF2; unfolder in SRF2; desf).
  { exfalso. apply SRF1.
    apply srf_in_vf_sb in SRF2.
    basic_solver. }
  exfalso. apply SRF2.
  apply srf_in_vf_sb in SRF1.
  basic_solver.
Qed.

Lemma wf_srff (WF : Wf G) : functional srf⁻¹.
Proof using.
  apply wf_srff', WF.
Qed.

Lemma srf_exists r l
    (HIN : E r)
    (NINIT : ~is_init r)
    (LOC : loc r = Some l)
    (INIT : E (InitEvent l))
    (INILAB : forall l', lab (InitEvent l') = Astore Xpln Opln l' 0)
    (FIN_ACTS : set_finite (E \₁ is_init))
    (COL : co ⊆ same_loc)
    (COT : transitive co)
    (COD : co ≡ eqv_rel W ;; co ;; eqv_rel W)
    (COE : co ≡ eqv_rel E ;; co ;; eqv_rel E)
    (COIRR : irreflexive co)
    (IS_R : R r) :
  exists w, srf w r.
Proof using.
  (* PREAMBLE *)
  assert (INILAB' : lab (InitEvent l) = Astore Xpln Opln l 0); eauto.
  assert (INISB : sb (InitEvent l) r).
  { unfold sb, ext_sb. basic_solver. }
  assert (SBVFSB : eqv_rel W ;; sb ⊆ vf ;; sb).
  { unfold vf, sb. basic_solver 11. }
  assert (INIVF : (vf ;; sb) (InitEvent l) r).
  { hahn_rewrite <- SBVFSB. esplit; split; eauto.
    unfolder. split; ins. unfold is_w; eauto. now rewrite INILAB. }
  assert (FINLOC : set_finite (E ∩₁ Loc_ l ∩₁ W)).
  { apply set_finite_mori with (E ∩₁ Loc_ l); [unfold flip; basic_solver| ].
    arewrite (E ⊆₁ E ∩₁ is_init ∪₁ E \₁ is_init).
    { rewrite set_minusE, <- set_inter_union_r, set_compl_union_id.
      basic_solver. }
    rewrite set_inter_union_l.
    arewrite ((E \₁ is_init) ∩₁ Loc_ l ⊆₁ E \₁ is_init) by basic_solver.
    apply set_finite_union. split; ins.
    unfolder. exists [InitEvent l]. intros e ((INE & ENIT) & ELOC).
    destruct e as [el | et en]; ins. unfold loc in *. left.
    rewrite INILAB in ELOC. congruence. }
  assert (COTLIN : codom_rel (eqv_rel (eq (InitEvent l)) ;; co＊) ⊆₁ Loc_ l).
  { rewrite <- cr_of_ct, crE, seq_union_r, codom_union,
            (ct_of_trans COT), COL.
    unfold same_loc, loc. apply set_subset_union_l. split.
    all: basic_solver. }
  assert (COTEIN : codom_rel (eqv_rel (eq (InitEvent l)) ;; co＊) ⊆₁ E).
  { rewrite <- cr_of_ct, crE, seq_union_r, codom_union,
            (ct_of_trans COT), COE.
    apply set_subset_union_l.
    split; [| rewrite inclusion_seq_eqv_l]; basic_solver. }
  assert (COTDIN : codom_rel (eqv_rel (eq (InitEvent l)) ;; co＊) ⊆₁ W).
  { rewrite <- cr_of_ct, crE, seq_union_r, codom_union,
            (ct_of_trans COT), COD.
    apply set_subset_union_l.
    split; [unfold is_w | rewrite inclusion_seq_eqv_l].
    all: basic_solver. }
  (* EXTRACT W *)
  apply set_finiteE in FINLOC. destruct FINLOC as (El & _ & FINLOC).
  destruct last_exists
     with (s   := co ⨾ ⦗fun x => (vf ;; sb) x r⦘)
          (dom := El)
          (a   := InitEvent l)
       as (w & LESS & MAX).
  { eapply acyclic_mon with (r := co); [| basic_solver].
    now apply trans_irr_acyclic. }
  { intros w LESS. apply FINLOC.
    hahn_rewrite inclusion_seq_eqv_r in LESS.
    enough (codom_rel (eqv_rel (eq (InitEvent l)) ;; co＊) w).
    { basic_solver. }
    exists (InitEvent l); unfolder; ins. }
  (* THE PROOF *)
  assert (WVF : (vf ⨾ sb) w r).
  { hahn_rewrite <- cr_of_ct in LESS.
    hahn_rewrite crE in LESS.
    destruct LESS as [EQ|CO]; [unfolder in EQ; desf|].
    hahn_rewrite ct_seq_eqv_r in CO.
    unfolder in CO. unfolder. desf. eauto. }
  exists w. red. split.
  all: try (apply seq_eqv_inter_lr; split).
  { unfolder. split; ins. }
  { unfold same_loc. rewrite COTLIN, LOC; ins.
    hahn_rewrite inclusion_seq_eqv_r in LESS.
    exists (InitEvent l); unfolder; ins. }
  unfolder. intros (w' & CO & FALSO). apply MAX with w'.
  basic_solver.
Qed.

Lemma srf_in_sb_rf :
  srf ⊆ (sb ∪ rf)⁺.
Proof using.
  admit.
Admitted.

Lemma sw_to_nacq a
    (NACHQ : mode_le (mod lab a) Orlx) :
  sw ⨾ ⦗eq a⦘ ⊆ ∅₂.
Proof using.
  unfold sw. hahn_frame.
  rewrite <- id_inter.
  arewrite (is_acq ∩₁ eq a ⊆₁ ∅); [| basic_solver].
  unfold is_acq, mode_le, mod in *. unfolder.
  ins. desf.
Qed.

Lemma hb_to_nacq a
    (NACHQ : mode_le (mod lab a) Orlx) :
  hb ⨾ ⦗eq a⦘ ⊆ hb^? ⨾ sb ⨾ ⦗eq a⦘.
Proof using.
  unfold hb at 1.
  rewrite ct_end at 1.
  rewrite seq_union_r, seq_union_l.
  arewrite ((sb ∪ sw)＊ ⨾ sb ≡ hb^? ⨾ sb).
  { unfold hb. basic_solver 11. }
  seq_rewrite sw_to_nacq; ins.
  basic_solver 11.
Qed.

Lemma vf_to_nacq a
    (IS_R : R a)
    (NACHQ : mode_le (mod lab a) Orlx) :
  vf ⨾ ⦗eq a⦘ ⊆ vf ⨾ sb ⨾ ⦗eq a⦘ ∪ ⦗E ∩₁ W⦘ ⨾ rf ⨾ ⦗eq a⦘.
Proof using.
  unfold vf. rewrite !seqA.
  arewrite (hb^? ⨾ ⦗eq a⦘ ≡ (hb ∪ eq) ⨾ ⦗eq a⦘).
  { basic_solver. }
  rewrite seq_union_l, hb_to_nacq by ins.
  arewrite (eq ⨾ ⦗eq a⦘ ≡ ⦗eq a⦘) by basic_solver.
  rewrite !seq_union_r. apply union_mori; ins.
  seq_rewrite <- id_inter.
  arewrite (rf^? ≡ rf ∪ eq) by basic_solver.
  rewrite seq_union_l, seq_union_r.
  arewrite (eq ⨾ ⦗eq a⦘ ≡ ⦗eq a⦘) by basic_solver.
  rewrite <- id_inter.
  arewrite (E ∩₁ W ∩₁ eq a ⊆₁ ∅); [| basic_solver].
  unfold is_r, is_w in *. unfolder. ins. desf.
Qed.

Lemma vf_to_nacq_nrf a
    (IS_R : R a)
    (NACHQ : mode_le (mod lab a) Orlx)
    (NRF : rf ⨾ ⦗eq a⦘ ⊆ ∅₂) :
  vf ⨾ ⦗eq a⦘ ⊆ vf ⨾ sb ⨾ ⦗eq a⦘.
Proof using.
  rewrite vf_to_nacq, NRF by ins.
  basic_solver.
Qed.

(* Lemma srf_to_nacq_nrf a
    (IS_R : R a)
    (NACHQ : mode_le (mod lab a) Orlx)
    (NRF : rf ⨾ ⦗eq a⦘ ⊆ ∅₂) : *)

Lemma vf_to_nacq_with_srf a
    (IS_R : R a)
    (NACHQ : mode_le (mod lab a) Orlx)
    (RFEQ : rf ⨾ ⦗eq a⦘ ≡ srf ⨾ ⦗eq a⦘) :
  srf ⨾ ⦗eq a⦘ ⊆ vf ⨾ sb ⨾ ⦗eq a⦘.
Proof using.
  unfold srf. basic_solver 11.
Qed.

End AuxRel.