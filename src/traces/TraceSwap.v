Require Import Lia Setoid Program.Basics.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
Import ListNotations.

Open Scope list_scope.

Module ListSwap.

Record lsc A (a b l1 l2 : list A) x y : Prop :=
{   L1_EQ : a = l1 ++ [x] ++ l2 ++ [y];
    L2_EQ : b = l1 ++ [y] ++ l2 ++ [x];
}.

Definition ls A a b m n :=
    exists l1 l2 x y,
        ⟪ STRUCT : lsc A a b l1 l2 x y ⟫ /\
        ⟪ L1_LEN : length l1 = m ⟫ /\
        ⟪ L2_LEN : length l1 + 1 + length l2 = n ⟫.

Global Hint Unfold ls : unfolderDb.

Section ListsSwappedConstr.

Variable A : Type.
Variable a b l1 l2 : list A.
Variable x y : A.
Hypothesis SWAPPED : lsc A a b l1 l2 x y.

Lemma lsc_sym : lsc A b a l1 l2 y x.
Proof using SWAPPED.
    destruct SWAPPED; subst a b.
    constructor; ins.
Qed.

Lemma lsc_len_eq : length b = length a.
Proof using SWAPPED.
    destruct SWAPPED; subst a b.
    now autorewrite with calc_length.
Qed.

Lemma lsc_len : length a = length l1 + 1 + length l2 + 1.
Proof using SWAPPED.
    destruct SWAPPED; subst a b.
    autorewrite with calc_length; lia.
Qed.

Hint Rewrite lsc_len_eq lsc_len : lsc.

Lemma lsc_len_1 :
    length l1 < length b.
Proof using SWAPPED.
    autorewrite with calc_length lsc; lia.
Qed.

Lemma lsc_len_2 :
    length l1 + 1 + length l2 < length b.
Proof using SWAPPED.
    autorewrite with calc_length lsc; lia.
Qed.

Lemma lsc_nth_1 n d
    (LT : n < length l1) :
    nth n b d = nth n a d.
Proof using SWAPPED.
    destruct SWAPPED; subst a b.
    now rewrite !app_nth1 by auto.
Qed.

Lemma lsc_nth_2 n d
    (LT : length l1 < n)
    (LT' : n < length l1 + 1 + length l2) :
    nth n b d = nth n a d.
Proof using SWAPPED.
    destruct SWAPPED; subst a b.
    rewrite !app_assoc with (l := l1).
    rewrite !app_nth2 with (l := l1 ++ [_]).
    all: autorewrite with calc_length; try lia.
    now rewrite !app_nth1 by lia.
Qed.

Lemma lsc_nth_y d :
    nth (length l1) b d = y.
Proof using SWAPPED.
    destruct SWAPPED; subst a b.
    rewrite app_nth2 by lia.
    now rewrite PeanoNat.Nat.sub_diag.
Qed.

Lemma lsc_nth_x d :
    nth (length l1 + 1 + length l2) b d = x.
Proof using SWAPPED.
    destruct SWAPPED; subst a b.
    rewrite !app_assoc.
    rewrite <- app_assoc with (l := l1) (n := l2).
    rewrite app_nth2.
    all: autorewrite with calc_length; try lia.
    now rewrite PeanoNat.Nat.add_assoc, PeanoNat.Nat.sub_diag.
Qed.

Lemma lsc_nth n d
    (NEQ1 : n <> length l1)
    (NEQ2 : n <> length l1 + 1 + length l2) :
    nth n b d = nth n a d.
Proof using SWAPPED.
    destruct (PeanoNat.Nat.lt_total n (length l1)).
    all: destruct (PeanoNat.Nat.lt_total n (length l1 + 1 + length l2)).
    all: desf; try lia.
    all: eauto using lsc_nth_1, lsc_nth_2.
    rewrite !nth_overflow; auto.
    all: autorewrite with lsc; lia.
Qed.

Lemma lsc_in : (fun x => In x a) ≡₁ (fun x => In x b).
Proof using SWAPPED.
    destruct SWAPPED; subst a b.
    unfolder. splits.
    all: intros; rewrite !in_app_iff in *.
    all: desf; eauto.
Qed.

Lemma lsc_impl_ls : ls A a b (length l1) (length l1 + 1 + length l2).
Proof using SWAPPED.
    destruct SWAPPED; subst a b.
    unfolder. repeat econstructor.
Qed.

End ListsSwappedConstr.

Global Hint Resolve lsc_sym lsc_len_eq lsc_len lsc_nth_1 lsc_nth_2 lsc_nth
    lsc_impl_ls lsc_in : listswap.

Section ListsSwapped.

Variable A : Type.
Variable a b : list A.
Variable m n : nat.
Hypothesis SWAPPED : ls A a b m n.

Lemma ls_sym : ls A b a m n.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    repeat econstructor; apply STRUCT.
Qed.

Lemma ls_len_eq : length b = length a.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    eauto with listswap.
Qed.

Lemma ls_len : length a = n + 1.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    eauto with listswap.
Qed.

Lemma ls_lt_m : m < n.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    lia.
Qed.

Lemma ls_lt_n : n < length a.
Proof using SWAPPED.
    rewrite ls_len; lia.
Qed.

Lemma ls_nth_1 N d
    (LT : N < m) :
    nth N b d = nth N a d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    eauto with listswap.
Qed.

Lemma ls_nth_2 N d
    (LT : m < N)
    (LT' : N < n) :
    nth N b d = nth N a d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    eauto with listswap.
Qed.

Lemma ls_nth_y d :
    nth n b d = nth m a d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    now erewrite lsc_nth_x, lsc_nth_y by eauto with listswap.
Qed.

Lemma ls_nth_x d :
    nth m b d = nth n a d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    now erewrite lsc_nth_x, lsc_nth_y by eauto with listswap.
Qed.

Lemma ls_nth N d
    (NEQ1 : N <> m)
    (NEQ2 : N <> n) :
    nth N b d = nth N a d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    eauto with listswap.
Qed.

Lemma ls_in : (fun x => In x a) ≡₁ (fun x => In x b).
Proof using SWAPPED.
    destruct SWAPPED; desc.
    eauto with listswap.
Qed.

End ListsSwapped.

Global Hint Resolve ls_sym ls_len ls_len_eq ls_nth_1 ls_nth_2 ls_nth
    ls_nth_x ls_nth_y ls_lt_m ls_lt_n ls_in : listswap.

End ListSwap.

Definition trace_swapped A t t' m n : Prop :=
    exists l l' rest,
        ⟪ SWAP : ListSwap.ls A l l' m n ⟫ /\
        ⟪ STRUCT1 : t = trace_app (trace_fin l) rest ⟫ /\
        ⟪ STRUCT2 : t' = trace_app (trace_fin l') rest ⟫.

Global Hint Unfold trace_swapped : unfolderDb.

Section TracesSwapped.

Variable A : Type.
Variable t t' : trace A.
Variable m n : nat.
Variable SWAPPED : trace_swapped A t t' m n.

Lemma trace_swapped_sym : trace_swapped A t' t m n.
Proof using SWAPPED.
    destruct SWAPPED as (l & l' & SWAPPED'); desf.
    exists l', l, rest.
    splits; eauto with listswap.
Qed.

Lemma trace_swapped_len : trace_length t' = trace_length t.
Proof using SWAPPED.
    destruct SWAPPED; desf.
    destruct rest; ins.
    autorewrite with calc_length.
    do 2 f_equal.
    eauto with listswap.
Qed.

Lemma trace_swapped_lt_m : m < n.
Proof using SWAPPED.
    destruct SWAPPED; desf.
    eauto with listswap.
Qed.

Lemma trace_swapped_lt_n : NOmega.lt_nat_l n (trace_length t).
Proof using SWAPPED.
    destruct SWAPPED; desf.
    rewrite trace_length_app.
    destruct (trace_length rest); ins.
    eauto using PeanoNat.Nat.lt_lt_add_r with listswap.
Qed.

(* TODO: useful for hahn? *)
Lemma trace_nth_app1 (a b : trace A) p d
    (LT : NOmega.lt_nat_l p (trace_length a)) :
    trace_nth p (trace_app a b) d = trace_nth p a d.
Proof using.
    rewrite trace_nth_app. desf.
Qed.

Lemma trace_nth_app2 (a : list A) (b : trace A) p d
    (LT : length a <= p) :
    trace_nth p (trace_app (trace_fin a) b) d = trace_nth (p - length a) b d.
Proof using.
    rewrite trace_nth_app. desf. ins.
    lia.
Qed.

Lemma trace_swapped_nth_i_lt_m i d
    (LT : i < m) :
    trace_nth i t' d = trace_nth i t d.
Proof using SWAPPED.
    assert (LT' : m < n) by apply trace_swapped_lt_m.
    destruct SWAPPED; desf.
    rewrite !trace_nth_app1; ins; eauto with listswap.
    all: erewrite ListSwap.ls_len; eauto with listswap; lia.
Qed.

Lemma trace_swapped_nth_m_lt_i_lt_n i d
    (LT : m < i)
    (LT' : i < n) :
    trace_nth i t' d = trace_nth i t d.
Proof using SWAPPED.
    destruct SWAPPED; desf.
    rewrite !trace_nth_app1; ins; eauto with listswap.
    all: erewrite ListSwap.ls_len; eauto with listswap; lia.
Qed.

Lemma trace_swapped_nth_n_lt_i i d
    (LT : n < i) :
    trace_nth i t' d = trace_nth i t d.
Proof using SWAPPED.
    destruct SWAPPED; desf.
    rewrite !trace_nth_app2; ins.
    all: erewrite !ListSwap.ls_len; eauto with listswap; lia.
Qed.

Lemma trace_swapped_nth_y d :
    trace_nth n t' d = trace_nth m t d.
Proof using SWAPPED.
    assert (LT' : m < n) by apply trace_swapped_lt_m.
    destruct SWAPPED; desf.
    rewrite !trace_nth_app1; simpl; eauto with listswap.
    erewrite ListSwap.ls_len; eauto with listswap; lia.
Qed.

Lemma trace_swapped_nth_x d :
    trace_nth m t' d = trace_nth n t d.
Proof using SWAPPED.
    assert (LT' : m < n) by apply trace_swapped_lt_m.
    destruct SWAPPED; desf.
    rewrite !trace_nth_app1; simpl; eauto with listswap.
    erewrite ListSwap.ls_len; eauto with listswap; lia.
Qed.

Lemma trace_swapped_nth N d
    (NEQ1 : N <> m)
    (NEQ2 : N <> n) :
    trace_nth N t d = trace_nth N t' d.
Proof using SWAPPED.
    destruct SWAPPED; desf.
    destruct (PeanoNat.Nat.lt_ge_cases N (n + 1)).
    { rewrite !trace_nth_app1; simpl; eauto with listswap.
      all: erewrite ListSwap.ls_len; eauto with listswap; lia. }
    rewrite !trace_nth_app2.
    all: erewrite !ListSwap.ls_len; eauto with listswap.
Qed.

Lemma trace_swapped_elems : trace_elems t ≡₁ trace_elems t'.
Proof using SWAPPED.
    destruct SWAPPED; desf.
    rewrite !trace_elems_app. simpl.
    rewrite ListSwap.ls_in by eauto.
    unfold trace_finite; desf; exfalso; eauto.
Qed.

End TracesSwapped.

Global Hint Resolve trace_swapped_sym trace_swapped_len trace_swapped_lt_m
    trace_swapped_lt_n
    trace_swapped_nth_i_lt_m
    trace_swapped_nth_m_lt_i_lt_n
    trace_swapped_nth_n_lt_i
    trace_swapped_nth_x
    trace_swapped_nth_y
    trace_swapped_nth
    trace_swapped_elems
     : trace_swap.