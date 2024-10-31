Require Import Lia Setoid Program.Basics.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms.

Require Import xmm_s xmm_s_hb.
Require Import Core AuxDef Rhb.

Open Scope program_scope.

Set Implicit Arguments.

Section Thrdle.

Variable X : WCore.t.
Variable dtrmt : actid -> Prop.
Variable thrdle : relation thread_id.

Notation "'G'" := (WCore.G X).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'hb'" := (hb G).
Notation "'rhb'" := (rhb G).

Lemma thrdle_sb_closed
  (INIT_MIN : min_elt thrdle tid_init)
  (INIT_LEAST : least_elt thrdle tid_init) :
    sb^? ⨾ tid ↓ thrdle ⨾ sb^? ⊆ tid ↓ thrdle.
Proof using.
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

Lemma thrdle_with_rhb
    (INIT_MIN : min_elt thrdle tid_init)
    (INIT_LEAST : least_elt thrdle tid_init) :
  ⦗E \₁ dtrmt⦘ ⨾ rf ⨾ hb^? ⊆ sb ∪ tid ↓ thrdle <->
    ⦗E \₁ dtrmt⦘ ⨾ rf ⨾ rhb^? ⊆ sb ∪ tid ↓ thrdle.
Proof using.
  split; intros SUB.
  { now rewrite rhb_in_hb. }
  rewrite hb_helper.
  rewrite cr_union_r, !seq_union_r.
  apply inclusion_union_l; auto.
  assert (SUB' : ⦗E \₁ dtrmt⦘ ⨾ rf ⊆ sb ∪ tid ↓ thrdle).
  { rewrite <- SUB. basic_solver. }
  rewrite <- seqA, SUB', seq_union_l.
  apply inclusion_union_l.
  { rewrite rewrite_trans.
    all: auto using sb_trans with hahn. }
  rewrite <- thrdle_sb_closed at 2; auto.
  basic_solver 11.
Qed.

End Thrdle.