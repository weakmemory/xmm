Require Import Setoid Program.Basics.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel.
Require Import Srf.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import xmm_s_hb.

Open Scope program_scope.

Set Implicit Arguments.

Module XmmCons.

Section ConsistencyCommon.

Variable G : execution.
Variable sc : relation actid.

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'R'" := (fun e => is_true (is_r lab e)).
Notation "'F'" := (fun e => is_true (is_f lab e)).
Notation "'hb'" := (hb G).
Notation "'same_loc'" := (same_loc lab).
Notation "'eco'" := (eco G).
Notation "'fr'" := (fr G).
Notation "'sw'" := (sw G).
Notation "'Acq'" := (fun e => is_true (is_acq lab e)).
Notation "'Rlx'" := (fun e => is_true (is_rlx lab e)).
Notation "'Rel'" := (fun e => is_true (is_rel lab e)).
Notation "'vf'" := (vf G).
Notation "'srf'" := (srf G).

Lemma hb_eco_irr
    (WF  : Wf G)
    (CONS : WCore.is_cons G) :
  irreflexive (hb ⨾ eco).
Proof using.
  destruct CONS.
  apply irreflexive_inclusion
   with (r' := hb ⨾ eco^?); eauto.
  apply inclusion_seq_mon; basic_solver.
Qed.

Lemma vf_hb_irr
    (WF  : Wf G)
    (CONS : WCore.is_cons G) :
  irreflexive (vf ⨾ hb).
Proof using.
  unfold vf. arewrite_id ⦗W⦘; arewrite_id ⦗E⦘.
  rels. arewrite (rf^? ⊆ eco^?).
  generalize (eco_trans WF); ins; relsf.
  generalize (@hb_trans G); ins; relsf.
  relsf; repeat (splits; try apply irreflexive_union).
  by rotate 1; apply CONS.
Qed.

Lemma srf_hb_irr
    (WF  : Wf G)
    (CONS : WCore.is_cons G) :
  irreflexive (srf ⨾ hb).
Proof using.
  rewrite srf_in_vf; try apply vf_hb_irr; eauto.
Qed.

Lemma coll_rel_inter (A B : Type) (f : A -> B) r r'
    (INJ : inj_dom (dom_rel r ∪₁ codom_rel r ∪₁ dom_rel r' ∪₁ codom_rel r') f) :
  f ↑ (r ∩ r') ≡ f ↑ r ∩ f ↑ r'.
Proof using.
  split; [apply collect_rel_inter |].
  unfolder; intros x y REL; desf.
  apply INJ in REL1, REL2; ins; desf.
  { exists x'0, y'0; splits; ins. }
  all: basic_solver 11.
Qed.

End ConsistencyCommon.

End XmmCons.