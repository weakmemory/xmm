From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution SubExecution.
Require Import Program.Basics.

Require Import xmm_s_hb.
Require Import Rhb.

Set Implicit Arguments.

Section Srf.
Variable G : execution.

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'Acq'" := (fun e => is_true (is_acq lab e)).
Notation "'Rel'" := (fun e => is_true (is_rel lab e)).
Notation "'Rlx'" := (fun e => is_true (is_rlx lab e)).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'hb'" := (hb G).
Notation "'rhb'" := (rhb G).
Notation "'sw'" := (sw G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'R'" := (fun e => is_true (is_r lab e)).
Notation "'F'" := (fun e => is_true (is_f lab e)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Definition vf := ⦗E⦘ ⨾ ⦗W⦘ ⨾ rf^? ⨾ hb^?.
Definition srf := ((vf ⨾ sb) ∩ same_loc) ⨾ ⦗R⦘ \ (co ⨾ vf ⨾ sb).

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

Lemma vf_hb :
    vf ⨾ hb ⨾ hb^? ⊆ vf.
Proof using.
    unfold vf.
    generalize (@hb_trans G); basic_solver 21.
Qed.

Lemma rf_rhb_sub_vf
        (WF  : Wf G):
    ⦗W⦘ ⨾ rf^? ⨾ rhb ⊆ vf.
Proof using.
    unfold vf. rewrite rhb_in_hb; eauto.
    assert (EQ1 : rf ≡ ⦗E⦘ ⨾ ⦗W⦘ ⨾ rf).
    { rewrite wf_rfD; eauto. rewrite wf_rfE; eauto. basic_solver. }
    case_refl _.
    { rewrite <- inclusion_id_cr with (r := rf).
      rewrite <- inclusion_step_cr with (r := hb) (r' := hb). 2 : basic_solver.
      rels. assert (EQ2 : hb ≡ ⦗E⦘ ⨾ hb ⨾ ⦗E⦘).
      { rewrite wf_hbE; eauto. basic_solver. }
      rewrite EQ2. basic_solver. }
    rewrite <- inclusion_step_cr with (r := hb) (r' := hb). 2 : basic_solver.
    rewrite <- inclusion_step_cr with (r := rf) (r' := rf). 2 : basic_solver.
    rewrite EQ1. basic_solver.
Qed.

Lemma sbvf_as_rhb :
  vf ⨾ sb ≡ ⦗E⦘ ⨾ ⦗W⦘ ⨾ rf^? ⨾ rhb^? ⨾ sb.
Proof using.
  unfold vf. rewrite !seqA.
  split; [| now rewrite rhb_in_hb].
  rewrite hb_helper, cr_union_r,
          seq_union_l.
  rewrite rewrite_trans by apply sb_trans.
  basic_solver 11.
Qed.

Lemma srf_as_rhb :
  srf ≡
    ((⦗E⦘ ⨾ ⦗W⦘ ⨾ rf^? ⨾ rhb^? ⨾ sb) ∩ same_loc) ⨾ ⦗R⦘ \
      (co ⨾ ⦗E⦘ ⨾ ⦗W⦘ ⨾ rf^? ⨾ rhb^? ⨾ sb).
Proof using.
  unfold srf.
  now rewrite sbvf_as_rhb.
Qed.

End Srf.

Section SubSrf.

Variable G G' : execution.
Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'loc''" := (loc lab').
Notation "'same_loc''" := (same_loc lab').
Notation "'Acq''" := (fun e => is_true (is_acq lab' e)).
Notation "'Rel''" := (fun e => is_true (is_rel lab' e)).
Notation "'Rlx''" := (fun e => is_true (is_rlx lab' e)).
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'hb''" := (hb G').
Notation "'sw''" := (sw G').
Notation "'W''" := (fun e => is_true (is_w lab' e)).
Notation "'R''" := (fun e => is_true (is_r lab' e)).
Notation "'F''" := (fun e => is_true (is_f lab' e)).
Notation "'Loc_'' l" := (fun x => loc' x = Some l) (at level 1).
Notation "'vf''" := (vf G').
Notation "'srf''" := (srf G').

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'Acq'" := (fun e => is_true (is_acq lab e)).
Notation "'Rel'" := (fun e => is_true (is_rel lab e)).
Notation "'Rlx'" := (fun e => is_true (is_rlx lab e)).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'hb'" := (hb G).
Notation "'sw'" := (sw G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'R'" := (fun e => is_true (is_r lab e)).
Notation "'F'" := (fun e => is_true (is_f lab e)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'vf'" := (vf G).
Notation "'srf'" := (srf G).

Lemma sub_vf_in sc sc'
    (SUB : sub_execution G G' sc sc') :
  vf' ⊆ vf.
Proof using.
  unfold vf.
  rewrite (sub_lab SUB),
          (sub_rf_in SUB),
          (sub_hb_in SUB),
          (sub_E SUB).
  reflexivity.
Qed.

End SubSrf.