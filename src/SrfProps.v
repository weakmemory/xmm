From imm Require Import Events Execution imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

Require Import Program.Basics.
Require Import AuxRel AuxDef Core StepOps.

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

Section SrfDelta.

Variable X X' : WCore.t.
Variable e : actid.
Variable l : label.

Notation "'G''" := (WCore.G X').
Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'loc''" := (loc lab').
Notation "'same_loc''" := (same_loc lab').
Notation "'co''" := (co G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'hb''" := (hb G').
Notation "'sw''" := (sw G').
Notation "'W''" := (is_w lab').
Notation "'R''" := (is_r lab').
Notation "'F''" := (is_f lab').
Notation "'vf''" := (vf G').
Notation "'srf''" := (srf G').
Notation "'Loc_'' l" := (fun x => loc' x = Some l) (at level 1).

Notation "'G'" := (WCore.G X).
Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'co'" := (co G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'hb'" := (hb G).
Notation "'sw'" := (sw G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'F'" := (is_f lab).
Notation "'vf'" := (vf G).
Notation "'srf'" := (srf G).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Lemma seq_eqv_minus_r {A : Type} r1 r2 (s : A -> Prop) :
  (r1 \ r2) ⨾ ⦗s⦘ ≡ (r1 ⨾ ⦗s⦘) \ (r2 ⨾ ⦗s⦘).
Proof using.
  unfolder. split; intros x y HREL.
  { desf; splits; eauto. apply or_not_and; eauto. }
  desf; splits; eauto.
Qed.

Lemma seq_eqv_minus_l {A : Type} r1 r2 (s : A -> Prop) :
  ⦗s⦘ ⨾ (r1 \ r2) ≡ (⦗s⦘ ⨾ r1) \ (⦗s⦘ ⨾ r2).
Proof using.
  unfolder. split; intros x y HREL.
  { desf; splits; eauto. apply or_not_and; eauto. }
  desf; splits; eauto.
Qed.

(*
Other version:

show that po-rf to E is the same
*)

Lemma hb_add_event
    (WF : Wf G)
    (RFC : rf_complete G)
    (ADD_EVENT : WCore.add_event X X' e l) :
  hb' ⨾ ⦗E⦘ ≡ hb ⨾ ⦗E⦘.
Proof using.
  red in ADD_EVENT. desf.
  assert (NIN : ~E e) by apply ADD_EVENT.
  unfold hb at 1.
  assert (SW_DELTA : exists dsw, sw' ≡ sw ∪ dsw ⨾ ⦗eq e⦘); desf.
  { admit. }
  rewrite (WCore.add_event_sb ADD_EVENT), SW_DELTA.
  rewrite <- !unionA.
  arewrite (sb ∪ WCore.sb_delta X e ∪ sw ∪ dsw ⨾ ⦗eq e⦘ ≡
            (WCore.sb_delta X e ∪ dsw ⨾ ⦗eq e⦘) ∪ (sb ∪ sw)).
  { basic_solver 11. }
  rewrite ct_unionE, <- cr_of_ct.
  change ((sb ∪ sw)⁺) with hb.
  rewrite ct_end, seq_union_l, !seqA.
  arewrite_false ((WCore.sb_delta X e ∪ dsw ⨾ ⦗eq e⦘) ⨾ hb^? ⨾ ⦗E⦘).
  { rewrite (wf_hbE WF), crE, !seq_union_l,
            !seq_id_l, !seq_union_r.
    basic_solver 11. }
  now rewrite !seq_false_r, union_false_r.
Admitted.

Lemma hb_add_event_start
    (WF : Wf G)
    (RFC : rf_complete G)
    (ADD_EVENT : WCore.add_event X X' e l) :
  ⦗eq e⦘ ⨾ hb' ≡ ∅₂.
Proof using.
  admit.
Admitted.

Lemma vf_add_event
    (WF : Wf G)
    (RFC : rf_complete G)
    (ADD_EVENT : WCore.add_event X X' e l) :
  vf' ⨾ ⦗E⦘ ≡ vf ⨾ ⦗E⦘.
Proof using.
  red in ADD_EVENT. desf.
  assert (NINE : ~E e) by apply ADD_EVENT.
  unfold vf. rewrite !seqA.
  rewrite (WCore.add_event_acts ADD_EVENT).
  (* Shrug off the `∪₁ eq e` *)
  rewrite id_union, seq_union_l.
  rewrite crE at 2.
  rewrite !seq_union_l, !seq_union_r.
  arewrite (⦗eq e⦘ ⨾ ⦗W'⦘ ⨾ rf' ≡ ∅₂).
  { seq_rewrite (seq_eqvC (eq e)). rewrite seqA.
    rewrite (rf_delta_WE WF ADD_EVENT),
            (add_event_to_rf_complete ADD_EVENT WF RFC).
    basic_solver. }
  rewrite !seq_false_l, union_false_r.
  rewrite crE with (r := hb') at 2.
  rewrite !seq_union_l, !seq_union_r.
  seq_rewrite !seq_id_r.
  arewrite (⦗eq e⦘ ⨾ ⦗W'⦘ ⨾ ⦗E⦘ ≡ ∅₂).
  { basic_solver 11. }
  rewrite union_false_l.
  arewrite (⦗eq e⦘ ⨾ ⦗W'⦘ ⨾ hb' ≡ ∅₂).
  { seq_rewrite (seq_eqvC (eq e)). rewrite seqA.
    rewrite (hb_add_event_start WF RFC); [basic_solver |].
    unfold WCore.add_event. eauto 11. }
  rewrite !seq_false_l, union_false_r.
  (* Shrug off the rfW delta *)
  arewrite (⦗E⦘ ⨾ ⦗W'⦘ ≡ ⦗E⦘ ⨾ ⦗W⦘).
  { unfold is_w. rewrite (WCore.add_event_lab ADD_EVENT).
    unfolder. split; intros x y (EQ & XINE & LAB).
    all: rewrite updo in * by congruence.
    all: eauto. }
  rewrite crE with (r := rf'), crE with (r := rf).
  rewrite !seq_union_l, !seq_union_r.
  seq_rewrite !seq_id_r.
  rewrite (WCore.add_event_rf ADD_EVENT).
  rewrite (add_event_to_rf_complete ADD_EVENT); ins.
  rewrite union_false_r.
  rewrite !seq_union_l, !seq_union_r.
  arewrite (WCore.rf_delta_R e l w ⨾ hb'^? ⨾ ⦗E⦘ ≡ ∅₂).
  { rewrite crE, seq_union_l, seq_union_r, seq_id_l.
    rewrite (hb_add_event WF RFC), (wf_hbE WF); [basic_solver 11|].
    unfold WCore.add_event. eauto 11. }
  rewrite !seq_false_r, union_false_r.
  seq_rewrite !(seq_eqvC E).
  rewrite (wf_rfE WF), !seqA.
  arewrite (⦗E⦘ ⨾ hb'^? ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ hb^? ⨾ ⦗E⦘); ins.
  rewrite !crE, !seq_union_l, !seq_union_r.
  apply union_more; ins.
  rewrite hb_add_event; ins.
  unfold WCore.add_event; eauto 11.
Qed.

Lemma srf_add_event r
    (WF : Wf G)
    (RFC : rf_complete G)
    (OTHER : tid r <> tid e)
    (ADD_EVENT : WCore.add_event X X' e l) :
  srf ⨾ ⦗eq r⦘ ≡ srf' ⨾ ⦗eq r⦘.
Proof using.
  red in ADD_EVENT. desf.
  assert (NOTINE : ~E e) by apply ADD_EVENT.
  unfold srf.
  rewrite !seq_eqv_minus_r.
  arewrite ((co ⨾ vf ⨾ sb) ⨾ ⦗eq r⦘ ≡ co ⨾ (vf ⨾ sb ⨾ ⦗eq r⦘)).
  { basic_solver 11. }
  arewrite ((vf ⨾ sb) ∩ same_loc ⨾ ⦗R⦘ ⨾ ⦗eq r⦘ ≡ (vf ⨾ sb ⨾ ⦗eq r⦘) ∩ same_loc ⨾ ⦗R⦘).
  { basic_solver 11. }
  arewrite ((vf' ⨾ sb') ∩ same_loc' ⨾ ⦗R'⦘ ⨾ ⦗eq r⦘ ≡ (vf' ⨾ sb' ⨾ ⦗eq r⦘) ∩ same_loc' ⨾ ⦗R'⦘).
  { basic_solver 11. }
  rewrite (WCore.add_event_sb ADD_EVENT), seq_union_l,
            seq_union_r.
  arewrite (WCore.sb_delta X e ⨾ ⦗eq r⦘ ≡ ∅₂).
  { basic_solver 11. }
  rewrite seq_false_r, union_false_r.
  arewrite (vf' ⨾ sb ≡ vf ⨾ sb).
  { unfold sb. rewrite <- !seqA, vf_add_event; ins.
    unfold WCore.add_event; eauto 11. }
  arewrite ((vf ⨾ sb ⨾ ⦗eq r⦘) ∩ same_loc' ⨾ ⦗R'⦘ ≡
            (vf ⨾ sb ⨾ ⦗eq r⦘) ∩ same_loc ⨾ ⦗R⦘).
  { rewrite <- seqA with (r3 := ⦗eq r⦘).
    rewrite !seq_eqv_inter_lr, !seqA, <- !id_inter.
    rewrite <- !seq_eqv_inter_rr.
    unfolder. split.
    all: intros x y ((z & SB & VF) & LOC & EQ & ISR).
    all: apply wf_vfE_left in SB.
    all: unfolder in SB; desf.
    all: unfold same_loc, is_r, loc in *.
    all: rewrite (WCore.add_event_lab ADD_EVENT) in *.
    all: rewrite !updo in *; splits; eauto.
    all: congruence. }
  arewrite (vf ⨾ sb ⨾ ⦗eq r⦘ ≡ ⦗E⦘ ⨾ vf ⨾ sb ⨾ ⦗eq r⦘).
  { rewrite wf_vfE_left. basic_solver 11. }
  arewrite ((⦗E⦘ ⨾ vf ⨾ sb ⨾ ⦗eq r⦘) ∩ same_loc ⨾ ⦗R⦘ ≡
            ⦗E⦘ ⨾ (vf ⨾ sb ⨾ ⦗eq r⦘) ∩ same_loc ⨾ ⦗R⦘).
  { basic_solver 11. }
  rewrite !seq_eqv_minus_ll, !seq_eqv_minus_l.
  seq_rewrite <- !restr_relE.
  arewrite (restr_rel E co' ≡ restr_rel E co); ins.
  rewrite (WCore.add_event_co ADD_EVENT). unfold WCore.co_delta.
  rewrite !restr_union. basic_solver 11.
Qed.

End SrfDelta.