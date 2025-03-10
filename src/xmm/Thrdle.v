Require Import Lia Setoid Program.Basics.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms.

Require Import xmm_s xmm_s_hb.
Require Import Core AuxDef Rhb Srf.

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
Notation "'vf'" := (vf G).
Notation "'vf_rhb'" := (vf_rhb G).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

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

Lemma thrdle_frame_sb_r r
    (INIT_MIN : min_elt thrdle tid_init)
    (INIT_LEAST : least_elt thrdle tid_init)
    (HIN : r ⊆ sb ∪ tid ↓ thrdle) :
  r ⨾ sb ⊆ sb ∪ tid ↓ thrdle.
Proof using.
  rewrite HIN, seq_union_l.
  rewrite rewrite_trans by apply sb_trans.
  apply union_mori; auto with hahn.
  rewrite <- thrdle_sb_closed at 2.
  all: auto.
  basic_solver 11.
Qed.

Lemma thrdle_with_rhb cmt
    (INIT_MIN : min_elt thrdle tid_init)
    (INIT_LEAST : least_elt thrdle tid_init)
    (WF : Wf G)
    (TID : E ∩₁ Tid_ tid_init ⊆₁ is_init) :
  vf ⨾ same_tid ⨾ ⦗E \₁ cmt⦘ ⊆ tid ↓ thrdle ∪ same_tid <->
    vf_rhb ⨾ same_tid ⨾ ⦗E \₁ cmt⦘ ⊆ tid ↓ thrdle ∪ same_tid.
Proof using.
  split; intros SUB.
  { now rewrite vfrhb_in_vf. }
  seq_rewrite (vf_tid_as_rhb WF).
  rewrite seq_union_l, !seqA, SUB.
  apply inclusion_union_l; [reflexivity |].
  apply inclusion_union_r. left.
  unfolder. intros x y (XINIT & (z & SB & TEQ & CMT)).
  destruct x as [xl | xt xn]; ins.
  apply INIT_LEAST. intro TEQ'.
  assert (ZNINI : ~is_init z).
  { apply no_sb_to_init in SB.
    forward apply SB. basic_solver. }
  assert (YNINI : ~is_init y).
  { intro FALSO. apply ZNINI, TID.
    split; [forward apply SB; unfold sb; basic_solver |].
    now rewrite TEQ. }
  apply YNINI, TID. basic_solver.
Qed.

End Thrdle.