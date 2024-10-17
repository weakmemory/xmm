From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution imm_s_hb.

Set Implicit Arguments.

Section Rhb.
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
Notation "'sw'" := (sw G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'R'" := (fun e => is_true (is_r lab e)).
Notation "'F'" := (fun e => is_true (is_f lab e)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Definition rpo_imm :=
  ⦗R ∩₁ Rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ∪
  ⦗Acq⦘ ⨾ sb ∪
  sb ⨾ ⦗Rel⦘ ∪
  ⦗F ∩₁ Rel⦘ ⨾ sb ⨾ ⦗W ∩₁ Rlx⦘.
Definition rpo := rpo_imm⁺.
Definition rhb := (rpo ∪ sw)⁺.

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

Lemma rpo_imm_upward_closed s
    (SBUP : upward_closed sb s) :
  upward_closed rpo_imm s.
Proof using.
  unfold upward_closed, rpo_imm.
  unfolder. intros x y HREL IN; desf.
  all: eapply SBUP; eauto.
Qed.

Lemma rpo_upward_closed s
    (SBUP : upward_closed sb s) :
  upward_closed rpo s.
Proof using.
  unfold upward_closed, rpo.
  intros x y REL.
  apply clos_trans_tn1 in REL.
  induction REL as [y REL | y z HEAD TAIL IHREL].
  { intro HIN. eapply rpo_imm_upward_closed; eauto. }
  intro HIN. apply IHREL.
  eapply rpo_imm_upward_closed; eauto.
Qed.

Lemma rpo_to_rpo_imm a b
    (SBIMM : immediate sb a b)
    (RPO : rpo a b) :
  rpo_imm a b.
Proof using.
  unfold rpo in RPO.
  apply clos_trans_tn1 in RPO.
  destruct RPO as [y RPO | y z HEAD TAIL]; ins.
  apply clos_tn1_trans in TAIL.
  apply rpo_in_sb in TAIL.
  apply rpo_imm_in_sb in HEAD.
  exfalso. now apply SBIMM with y.
Qed.

End Rhb.