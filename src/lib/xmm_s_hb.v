(******************************************************************************)
(** * Definition of happens-before in the s_IMM memory model (similar to C11) *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

From imm Require Import Events.
From imm Require Import Execution.
From imm Require Import Execution_eco.
From imm Require Import SubExecution.

Set Implicit Arguments.

Section IMM_hb.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).

Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'detour'" := (detour G).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'W_ex'" := (W_ex G).

Implicit Type WF : Wf G.
Implicit Type SC_PER_LOC : sc_per_loc G.

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* release sequence *)
Definition rs := ⦗W⦘ ⨾ (rf ⨾ rmw)＊.

Definition release := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗Rlx⦘ ⨾ rs.

(* synchronizes with *)
Definition sw := release ⨾ rf ⨾ ⦗Rlx⦘ ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.

(* happens-before *)
Definition hb := (sb ∪ sw)⁺.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma hb_trans : transitive hb.
Proof using. vauto. Qed.

Lemma sb_in_hb : sb ⊆ hb.
Proof using. vauto. Qed.

Lemma sw_in_hb : sw ⊆ hb.
Proof using. vauto. Qed.

Lemma cr_hb_hb : hb^? ⨾ hb ≡ hb.
Proof using. generalize hb_trans; basic_solver. Qed.

Lemma cr_hb_cr_hb : hb^? ⨾ hb^? ≡ hb^?.
Proof using. generalize hb_trans; basic_solver 20. Qed.

Lemma hb_sb_sw : hb ≡ hb^? ⨾ (sb ∪ sw).
Proof using.
unfold hb; rewrite ct_end at 1; rels.
Qed.

(******************************************************************************)
(** ** Same Location relations  *)
(******************************************************************************)

Lemma loceq_rs WF : funeq loc rs.
Proof using. destruct WF; unfold rs; desf; eauto 10 with hahn. Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_rsE WF : rs ≡ ⦗W⦘ ∪ ⦗E⦘ ⨾ rs ⨾ ⦗E⦘.
Proof using.
unfold rs.
split; [|basic_solver 15].
rewrite rtE; relsf; unionL; [basic_solver 12|].
unionR right -> right.
rewrite (dom_r (wf_rmwE WF)) at 1.
rewrite <- !seqA.
sin_rewrite inclusion_ct_seq_eqv_r.
rewrite !seqA.
arewrite (⦗E⦘ ⨾ ⦗W⦘ ≡ ⦗W⦘ ⨾ ⦗E⦘) by basic_solver.
hahn_frame.
rewrite ct_begin.
rewrite (dom_l (wf_rfE WF)) at 1.
basic_solver 21.
Qed.

Lemma wf_releaseE WF : release ≡ ⦗W ∩₁ Rel⦘ ∪ ⦗E⦘ ⨾ release ⨾ ⦗E⦘.
Proof using.
arewrite (W ∩₁ Rel ≡₁ W ∩₁ Rel ∩₁ Rlx).
{ rewrite set_interA. apply set_equiv_inter; [reflexivity |].
  split; [| basic_solver]. unfolder.
  unfold is_rel, is_rlx, mod, mode_le.
  ins. desf. }
unfold release.
rewrite (wf_rsE WF).
rewrite (@wf_sbE G) at 1.
split; unfolder; ins; desf; eauto 42.
Qed.

Lemma wf_swE_right WF : sw ≡ sw ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold sw.
rewrite wf_sbE at 1 2.
rewrite (wf_rfE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_swE WF : sw ≡ ⦗E⦘ ⨾ sw ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
rewrite (wf_swE_right WF) at 1.
hahn_frame.
unfold sw.
rewrite (wf_releaseE WF).
rewrite (dom_l (wf_rfE WF)).
rewrite (dom_l (@wf_sbE G)).
basic_solver 40.
Qed.

Lemma wf_hbE WF : hb ≡ ⦗E⦘ ⨾ hb ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold hb.
rewrite <- inclusion_ct_seq_eqv_r, <- inclusion_ct_seq_eqv_l.
apply inclusion_t_t.
rewrite wf_sbE at 1.
rewrite (wf_swE WF) at 1.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_rsD WF : rs ≡ ⦗W⦘ ⨾ rs ⨾ ⦗W⦘.
Proof using.
split; [|basic_solver].
unfold rs.
rewrite rtE; relsf; unionL; [basic_solver 12|].
rewrite (dom_r (wf_rmwD WF)) at 1.
rewrite <- !seqA.
rewrite inclusion_ct_seq_eqv_r.
basic_solver 42.
Qed.

Lemma wf_releaseD WF : release ≡ ⦗FW ∩₁ Rel⦘ ⨾ release ⨾ ⦗W⦘.
Proof using.
split; [|basic_solver].
unfold release.
rewrite (wf_rsD WF) at 1.
basic_solver 42.
Qed.

Lemma wf_swD WF : sw ≡ ⦗FW∩₁Rel⦘ ⨾ sw ⨾ ⦗FR∩₁Acq⦘.
Proof using.
split; [|basic_solver].
unfold sw.
rewrite (wf_releaseD WF) at 1.
rewrite (wf_rfD WF) at 1.
basic_solver 42.
Qed.


(******************************************************************************)
(** ** init *)
(******************************************************************************)

Lemma no_release_from_init WF: release ≡ ⦗set_compl is_init⦘ ⨾ release.
Proof using.
  split; [| basic_solver]. apply doma_helper.
  unfold release. rewrite init_pln; eauto. mode_solver.
Qed.

Lemma no_sw_to_init WF : sw ≡ sw ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
split; [|basic_solver].
rewrite (wf_swD WF) at 1.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

Lemma no_hb_to_init WF : hb ≡ hb ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
split; [|basic_solver].
unfold hb.
rewrite ct_end.
rewrite (no_sw_to_init WF) at 2.
rewrite no_sb_to_init at 2.
basic_solver 42.
Qed.

(******************************************************************************)
(** more properties **   *)
(******************************************************************************)

Lemma release_rf_in_sw WF: release ⨾ rf ⨾ ⦗Acq⦘ ⊆ sw.
Proof using.
unfold sw. hahn_frame_l.
unfolder. ins. desf. eexists. splits; eauto.
mode_solver.
Qed.

Lemma sw_in_release_rf WF:
  sw ⨾ ⦗R⦘ ⊆ release ⨾ rf ⨾ ⦗Acq⦘.
Proof using.
unfold sw; rewrite !seqA.
arewrite (⦗Rlx⦘ ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗R⦘ ⊆ ⦗Acq⦘) by type_solver 42.
Qed.


Lemma rs_in_co WF SC_PER_LOC : rs ⊆ ⦗W⦘ ⨾ co^?.
Proof using.
unfold rs.
rewrite rtE; relsf; unionL; [basic_solver|].
sin_rewrite !(rf_rmw_in_co WF SC_PER_LOC).
sin_rewrite (dom_r (wf_coD WF)).
hahn_frame.
arewrite_id ⦗W⦘.
generalize (co_trans WF); ins; relsf.
Qed.

Lemma release_in_hb_co WF SC_PER_LOC : release ⊆ (hb^? ⨾ co^?).
Proof using.
unfold release; rewrite rs_in_co; try done.
rewrite sb_in_hb; basic_solver 10.
Qed.

Lemma hb_W WF : hb ⨾ ⦗ W ⦘ ⊆ (hb ⨾ ⦗FR∩₁Acq⦘)^? ⨾ sb.
Proof using.
unfold hb; rewrite path_ut_last at 1.
generalize (@sb_trans G); ins; relsf; unionL.
basic_solver.
rewrite !seqA; rewrite (dom_r (wf_swD WF)) at 2.
rewrite !seqA.
arewrite (sw ⊆ (sb ∪ sw)＊) at 2.
rewrite crE; relsf; unionL.
type_solver.
basic_solver 12.
Qed.

Lemma hb_first_Rel WF : hb ⊆ sb ∪ sb^? ⨾ ⦗FW ∩₁ Rel⦘ ⨾ hb.
Proof using.
unfold hb.
rewrite path_ut_first at 1.
generalize (@sb_trans G); ins; relsf; unionL.
basic_solver.
rewrite (dom_l (wf_swE WF)) at 1.
rewrite (dom_l (wf_swD WF)) at 1.
arewrite (sw ⊆ (sb ∪ sw)⁺) at 1; relsf.
basic_solver 21.
Qed.

Lemma release_int : release ⊆ release ⨾ ⦗W_ex⦘ ∪ ⦗F ∩₁ Rel⦘ ⨾ sb ⨾ ⦗W⦘ ∪
  ⦗W ∩₁ Rel⦘ ⨾  (sb ∩ same_loc)^? ⨾ ⦗W⦘.
Proof using.
unfold release, rs.
rewrite rtE; relsf; unionL.
generalize (@sb_trans G); basic_solver 21.
rewrite rmw_W_ex at 1.
rewrite <- !seqA, inclusion_ct_seq_eqv_r, !seqA.
basic_solver 21.
Qed.

Lemma release_rf_rmw_step : release ⨾ rf ⨾ rmw ⊆ release.
Proof using.
  unfold release at 1. unfold rs.
  rewrite !seqA.
  arewrite (rf ⨾ rmw ⊆ (rf ⨾ rmw)＊) at 2.
    by rewrite rt_rt.
Qed.

Lemma release_rf_rmw_steps : release ⨾ (rf ⨾ rmw)＊ ⊆ release.
Proof using.
  unfold release at 1. unfold rs.
  rewrite !seqA.
    by rewrite rt_rt.
Qed.

(******************************************************************************)
(** ... **   *)
(******************************************************************************)

Definition coherence := irreflexive (hb ⨾ eco^?).

Implicit Type COH : coherence.

Lemma coherence_sc_per_loc COH : sc_per_loc G.
Proof using.
red; rewrite sb_in_hb.
red in COH; unfolder in *; basic_solver 12.
Qed.

Lemma hb_irr WF COH : irreflexive hb.
Proof using.
red in COH.
unfolder in *; eauto 20.
Qed.

Proposition coherence_alt :
  irreflexive (hb ∪ hb ⨾ rfe ∪ hb ⨾ co ∪ hb ⨾ co ⨾ rfe ∪ hb ⨾ fr ∪ hb ⨾ fr ⨾ rfe) -> coherence.
Proof using.
  unfold coherence; unfold Execution_eco.eco; relsf.
rewrite rfi_union_rfe; relsf.
arewrite (rfi ⊆ sb); rewrite sb_in_hb; rewrite !crE; relsf.
ins; unionL.
all: try rotate 1.
all: generalize hb_trans; ins; relsf.
all: try (unfolder in *; basic_solver 12).
Qed.

End IMM_hb.

Section XMM_hb_sub.

Variable G G' : execution.
Variable sc sc' : relation actid.

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
Notation "'rs''" := (rs G').
Notation "'release''" := (release G').
Notation "'sw''" := (sw G').
Notation "'W''" := (fun e => is_true (is_w lab' e)).
Notation "'R''" := (fun e => is_true (is_r lab' e)).
Notation "'F''" := (fun e => is_true (is_f lab' e)).
Notation "'Loc_'' l" := (fun x => loc' x = Some l) (at level 1).

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
Notation "'rs'" := (rs G).
Notation "'release'" := (release G).
Notation "'sw'" := (sw G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'R'" := (fun e => is_true (is_r lab e)).
Notation "'F'" := (fun e => is_true (is_f lab e)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Hypothesis SUB : sub_execution G G' sc sc'.

Lemma sub_rs_in : rs' ⊆ rs.
Proof using SUB.
  unfold rs.
  now rewrite
    (sub_lab SUB),
    (sub_rf_in SUB),
    (sub_rmw_in SUB).
Qed.

Lemma sub_release_in : release' ⊆ release.
Proof using SUB.
  unfold release.
  now rewrite
    (sub_lab SUB),
    (sub_sb_in SUB),
    sub_rs_in.
Qed.

Lemma sub_sw_in : sw' ⊆ sw.
Proof using SUB.
  unfold sw.
  now rewrite
    (sub_lab SUB),
    (sub_rf_in SUB),
    (sub_sb_in SUB),
    sub_release_in.
Qed.

Lemma sub_hb_in : hb' ⊆ hb.
Proof using SUB.
  unfold hb.
  now rewrite
    (sub_sb_in SUB),
    sub_sw_in.
Qed.

End XMM_hb_sub.