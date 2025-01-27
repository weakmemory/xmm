From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Set Implicit Arguments.
Open Scope program_scope.

Section MapDoms.

Variable G G' : execution.
Variable mapper : actid -> actid.

Notation "'lab''" := (lab G').
Notation "'loc''" := (loc lab').
Notation "'val''" := (val lab').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'data''" := (data G').
Notation "'ctrl''" := (ctrl G').
Notation "'addr''" := (addr G').
Notation "'W''" := (fun e => is_true (is_w lab' e)).
Notation "'R''" := (fun e => is_true (is_r lab' e)).
Notation "'F''" := (fun e => is_true (is_f lab' e)).
Notation "'Loc_'' l" := (fun e => loc' e = l) (at level 1).
Notation "'Val_'' l" := (fun e => val' e = l) (at level 1).
Notation "'same_loc''" := (same_loc lab').
Notation "'same_val''" := (same_val lab').
Notation "'Acq''" := (fun e => is_true (is_acq lab' e)).
Notation "'Rel''" := (fun e => is_true (is_rel lab' e)).
Notation "'Rlx''" := (fun e => is_true (is_rlx lab' e)).

Notation "'lab'" := (lab G).
Notation "'val'" := (val lab).
Notation "'loc'" := (loc lab).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'data'" := (data G).
Notation "'ctrl'" := (ctrl G).
Notation "'addr'" := (addr G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'R'" := (fun e => is_true (is_r lab e)).
Notation "'F'" := (fun e => is_true (is_f lab e)).
Notation "'Loc_' l" := (fun e => loc e = l) (at level 1).
Notation "'Val_' l" := (fun e => val e = l) (at level 1).
Notation "'same_loc'" := (same_loc lab).
Notation "'same_val'" := (same_val lab).
Notation "'Acq'" := (fun e => is_true (is_acq lab e)).
Notation "'Rel'" := (fun e => is_true (is_rel lab e)).
Notation "'Rlx'" := (fun e => is_true (is_rlx lab e)).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Lemma set_collect_rlx s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  Rlx' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (Rlx ∩₁ s).
Proof using.
  unfolder. intros x' (RLX & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_rlx, mod in *. rewrite LABEQ; auto.
Qed.

Lemma set_collect_rel s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  Rel' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (Rel ∩₁ s).
Proof using.
  unfolder. intros x' (REL & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_rel, mod in *. rewrite LABEQ; auto.
Qed.

Lemma set_collect_acq s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  Acq' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (Acq ∩₁ s).
Proof using.
  unfolder. intros x' (ACQ & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_acq, mod in *. rewrite LABEQ; auto.
Qed.

Lemma set_collect_is_r s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  R' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (R ∩₁ s).
Proof using.
  unfolder. intros x' (ISR & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_r in *. rewrite LABEQ; auto.
Qed.

Lemma set_collect_is_w s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  W' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (W ∩₁ s).
Proof using.
  unfolder. intros x' (ISW & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_w in *. rewrite LABEQ; auto.
Qed.

Lemma set_collect_is_f s
    (SUB : s ⊆₁ E)
    (LABEQ : eq_dom E lab (lab' ∘ mapper)) :
  F' ∩₁ mapper ↑₁ s ⊆₁ mapper ↑₁ (F ∩₁ s).
Proof using.
  unfolder. intros x' (ISF & (x & XIN & XEQ)).
  subst x'. exists x; splits; auto.
  unfold is_f in *. rewrite LABEQ; auto.
Qed.

Lemma mapdom_rewrite_l s1 s2 :
  mapper ↑ ⦗s1⦘ ⨾ ⦗s2⦘ ≡ ⦗s2 ∩₁ mapper ↑₁ s1⦘.
Proof using.
  rewrite collect_rel_eqv, id_inter.
  apply seq_eqvC.
Qed.

Lemma mapdom_rewrite_l' s1 s2 :
  ⦗mapper ↑₁ s1⦘ ⨾ ⦗s2⦘ ≡ ⦗s2 ∩₁ mapper ↑₁ s1⦘.
Proof using.
  rewrite id_inter. apply seq_eqvC.
Qed.

Lemma mapdom_rewrite_r s1 s2 :
  ⦗s2⦘ ⨾ mapper ↑ ⦗s1⦘ ≡ ⦗s2 ∩₁ mapper ↑₁ s1⦘.
Proof using.
  rewrite collect_rel_eqv, id_inter.
  now rewrite seq_eqvC.
Qed.

Lemma mapdom_rewrite_rel r
    (WF : r ≡ ⦗E⦘ ⨾ r ⨾ ⦗E⦘) :
  mapper ↑ r ≡
    ⦗mapper ↑₁ E⦘ ⨾ mapper ↑ r ⨾ ⦗mapper ↑₁ E⦘.
Proof using.
  split; [| basic_solver 11].
  rewrite WF at 1.
  now rewrite !collect_rel_seqi, !collect_rel_eqv.
Qed.

Lemma set_inter_rlx s s'
    (SUB : s ⊆₁ s')
    (LABEQ : eq_dom s' lab lab') :
  Rlx' ∩₁ s ⊆₁ Rlx ∩₁ s.
Proof using.
  unfolder. intros x (RLX & XIN).
  splits; auto.
  unfold is_rlx, mod in *. rewrite LABEQ; auto.
Qed.

Lemma set_inter_rel s s'
    (SUB : s ⊆₁ s')
    (LABEQ : eq_dom s' lab lab') :
  Rel' ∩₁ s ⊆₁ Rel ∩₁ s.
Proof using.
  unfolder. intros x (RLX & XIN).
  splits; auto.
  unfold is_rel, mod in *. rewrite LABEQ; auto.
Qed.

Lemma set_inter_acq s s'
    (SUB : s ⊆₁ s')
    (LABEQ : eq_dom s' lab lab') :
  Acq' ∩₁ s ⊆₁ Acq ∩₁ s.
Proof using.
  unfolder. intros x (RLX & XIN).
  splits; auto.
  unfold is_acq, mod in *. rewrite LABEQ; auto.
Qed.

Lemma set_inter_is_r s s'
    (SUB : s ⊆₁ s')
    (LABEQ : eq_dom s' lab lab') :
  R' ∩₁ s ⊆₁ R ∩₁ s.
Proof using.
  unfolder. intros x (RLX & XIN).
  splits; auto.
  unfold is_r in *. rewrite LABEQ; auto.
Qed.

Lemma set_inter_is_w s s'
    (SUB : s ⊆₁ s')
    (LABEQ : eq_dom s' lab lab') :
  W' ∩₁ s ⊆₁ W ∩₁ s.
Proof using.
  unfolder. intros x (RLX & XIN).
  splits; auto.
  unfold is_w in *. rewrite LABEQ; auto.
Qed.

Lemma set_inter_is_f s s'
    (SUB : s ⊆₁ s')
    (LABEQ : eq_dom s' lab lab') :
  F' ∩₁ s ⊆₁ F ∩₁ s.
Proof using.
  unfolder. intros x (RLX & XIN).
  splits; auto.
  unfold is_f in *. rewrite LABEQ; auto.
Qed.

Lemma set_inter_loc s s' l
    (SUB : s ⊆₁ s')
    (LABEQ : eq_dom s' lab lab') :
  Loc_' l ∩₁ s ⊆₁ Loc_ l ∩₁ s.
Proof using.
  unfolder. intros x (LOC & XIN).
  splits; auto.
  unfold loc in *. rewrite LABEQ; auto.
Qed.

End MapDoms.