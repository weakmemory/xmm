Require Import Lia Setoid Program.Basics.
Require Import AuxDef AuxRel.
Require Import ThreadTrace.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.

Section ExecRestrEq.

Variable G G' : execution.
Variable d : actid -> Prop.

Notation "'E''" := (acts_set G').
Notation "'threads_set''" := (threads_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').

Notation "'E'" := (acts_set G).
Notation "'threads_set'" := (threads_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).

Record exec_restr_eq : Prop := {
  ereq_acts : E ∩₁ d ≡₁ E' ∩₁ d;
  ereq_threads : threads_set ≡₁ threads_set';
  ereq_lab : eq_dom d lab lab';
  ereq_rf : restr_rel d rf ≡ restr_rel d rf';
  ereq_co : restr_rel d co ≡ restr_rel d co';
  ereq_rmw : restr_rel d rmw ≡ restr_rel d rmw';
  ereq_data : restr_rel d data ≡ restr_rel d data';
  ereq_ctrl : restr_rel d ctrl ≡ restr_rel d ctrl';
  ereq_rmw_dep : restr_rel d rmw_dep ≡ restr_rel d rmw_dep';
}.

Hypothesis EREQ : exec_restr_eq.

Lemma ereq_sb : restr_rel d sb ≡ restr_rel d sb'.
Proof using EREQ.
  unfold sb. rewrite <- !restr_relE, !restr_restr.
  now rewrite (ereq_acts EREQ).
Qed.

End ExecRestrEq.