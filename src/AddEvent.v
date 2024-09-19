From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.

Require Import Core.
Require Import Lia.

Section AddEvent.

Variable X : WCore.t.

Notation "'G'" := (WCore.G X).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Lemma add_sb_max_event t
    (INIT : is_init ⊆₁ E)
    (NTID : t <> tid_init)
    (FIN : set_finite (E \₁ is_init)) :
  exists e,
    << NINIT : ~is_init e >> /\
    << NOTIN : ~E e >> /\
    << TID : tid e = t >> /\
    << SB : ⦗E ∪₁ eq e⦘ ⨾ ext_sb ⨾ ⦗E ∪₁ eq e⦘ ≡
            sb ∪ WCore.sb_delta e E >>.
Proof using.
  unfold NW.
  destruct classic with (E ∩₁ Tid_ t ≡₁ ∅) as [EMP | NEMP].
  { assert (NIN : ~ E (ThreadEvent t 0)).
    { intro FALSO. apply EMP with (ThreadEvent t 0).
      split; auto. }
    exists (ThreadEvent t 0). splits; auto.
    rewrite id_union.
    rewrite !seq_union_l, !seq_union_r.
    change (⦗E⦘ ⨾ ext_sb ⨾ ⦗E⦘) with sb.
    arewrite_false (⦗eq (ThreadEvent t 0)⦘ ⨾ ext_sb ⨾ ⦗eq (ThreadEvent t 0)⦘).
    { unfolder. intros. desf. eapply ext_sb_irr. eassumption. }
    arewrite_false (⦗eq (ThreadEvent t 0)⦘ ⨾ ext_sb ⨾ ⦗E⦘).
    { unfolder. unfold ext_sb. intros. desf.
      eapply EMP. split; eauto. desf. }
    rewrite !union_false_r. apply union_more; [reflexivity |].
    unfold WCore.sb_delta.
    arewrite (same_tid (ThreadEvent t 0) ≡₁ Tid_ t).
    { unfold same_tid. unfolder. split; ins. }
    rewrite EMP, set_union_empty_r. unfold ext_sb.
    unfolder. split; ins; desf; splits; auto.
    exfalso. desf. eapply EMP. split; eauto. }
  apply set_nonemptyE in NEMP.
  destruct NEMP as (e' & IN).
  assert (NINI : ~is_init e').
  { unfold is_init. desf.
    unfolder in IN. desf. }
  apply set_finiteE in FIN.
  destruct FIN as (l & NODUP & ELE).
  destruct last_exists
      with (dom := l)
           (s := sb)
           (a := e')
        as (e0 & SB & MAX).
  { apply sb_acyclic. }
  { intros c SB.
    apply rt_of_trans in SB; auto using sb_trans.
    apply crE in SB.
    destruct SB as [EQ|SB].
    { apply ELE. red in EQ. desf.
      split; [apply IN | apply NINI]. }
    apply ELE. split.
    { apply wf_sbE in SB. unfolder in SB. desf. }
    unfold sb, ext_sb in SB. unfolder in SB. desf. }
  assert (NINI0 : ~is_init e0).
  { apply rt_of_trans in SB; auto using sb_trans.
    apply crE in SB.
    destruct SB as [EQ|SB].
    { red in EQ. desf. }
    unfold sb, ext_sb in SB. unfolder in SB. desf. }
  assert (TID0 : tid e0 = t).
  { destruct IN as (INE & TID).
    apply rt_of_trans in SB; auto using sb_trans.
    apply crE in SB.
    destruct SB as [EQ|SB].
    { red in EQ. desf. }
    unfold sb, ext_sb in SB. unfolder in SB. do 2 desf. }
  assert (IN0 : E e0).
  { destruct IN as (INE & TID).
    apply rt_of_trans in SB; auto using sb_trans.
    apply crE in SB.
    destruct SB as [EQ|SB].
    { red in EQ. desf. }
    apply wf_sbE in SB. unfolder in SB. desf. }
  destruct e0 as [e0l | e0t e0n].
  all: ins; desf.
  exists (ThreadEvent t (1 + e0n)). splits; auto.
  { intro FALSO. apply MAX with (ThreadEvent t (1 + e0n)).
    unfold sb, ext_sb. unfolder. splits; ins. }
  rewrite id_union.
  rewrite !seq_union_l, !seq_union_r.
  change (⦗E⦘ ⨾ ext_sb ⨾ ⦗E⦘) with sb.
  arewrite_false (⦗eq (ThreadEvent t (1 + e0n))⦘ ⨾ ext_sb ⨾ ⦗eq (ThreadEvent t (1 + e0n))⦘).
  { unfolder. intros. desf. eapply ext_sb_irr. eassumption. }
  arewrite_false (⦗eq (ThreadEvent t (1 + e0n))⦘ ⨾ ext_sb ⨾ ⦗E⦘).
  { unfolder. unfold ext_sb. intros. desf.
    eapply MAX. unfold sb. unfolder. splits; eauto.
    unfold ext_sb. split; desf. lia. }
  rewrite !union_false_r. apply union_more; [reflexivity |].
  unfold WCore.sb_delta.
  arewrite (same_tid (ThreadEvent t (1 + e0n)) ≡₁ Tid_ t).
  { unfold same_tid. unfolder. split; ins. }
  unfolder. split.
  { intros x y (INE & SB' & EQ). subst y. split; auto.
    unfold ext_sb in SB'. desf; ins; [now left|].
    right. desf. }
  intros x y ([XINI | INX] & EQ); subst y.
  { unfold ext_sb; splits; auto. desf. }
  desf. unfold ext_sb; splits; auto.
  destruct x as [xl | xt xn]; ins.
  split; [auto |].
  destruct PeanoNat.Nat.lt_ge_cases
      with (n := xn) (m := S e0n)
        as [LT | GE]; auto.
  assert (LT : e0n < xn) by lia.
  exfalso. apply MAX with (ThreadEvent xt xn).
  unfold sb, ext_sb. unfolder. splits; ins.
Qed.

End AddEvent.

Lemma add_sb_max_event_to_set t E
    (INIT : is_init ⊆₁ E)
    (NTID : t <> tid_init)
    (FIN : set_finite (E \₁ is_init)) :
  exists e,
    << NINIT : ~is_init e >> /\
    << NOTIN : ~E e >> /\
    << TID : tid e = t >> /\
    << SB : ⦗E ∪₁ eq e⦘ ⨾ ext_sb ⨾ ⦗E ∪₁ eq e⦘ ≡
            ⦗E⦘ ⨾ ext_sb ⨾ ⦗E⦘ ∪ WCore.sb_delta e E >>.
Proof using.
  admit.
Admitted.