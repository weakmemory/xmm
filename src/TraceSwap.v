Require Import Lia Setoid Program.Basics.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
Import ListNotations.

Open Scope list_scope.

Record lsc A (a b l1 l2 : list A) x y : Prop :=
{   L1_EQ : a = l1 ++ [x] ++ l2 ++ [y];
    L2_EQ : b = l1 ++ [y] ++ l2 ++ [x];
}.

Definition ls A a b m n :=
    exists l1 l2 x y,
        ⟪ STRUCT : lsc A a b l1 l2 x y ⟫ /\
        ⟪ L1_LEN : length l1 = m ⟫ /\
        ⟪ L2_LEN : length l1 + 1 + length l2 = n ⟫.

Definition trace_swapped A t t' m n : Prop :=
    exists l l' rest,
        ⟪ SWAP : ls A l l' m n ⟫ /\
        ⟪ STRUCT1 : t = trace_app (trace_fin l) rest ⟫ /\
        ⟪ STRUCT2 : t' = trace_app (trace_fin l') rest ⟫.

Global Hint Unfold ls trace_swapped : unfolderDb.

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
    destruct (NPeano.Nat.lt_total n (length l1)).
    all: destruct (NPeano.Nat.lt_total n (length l1 + 1 + length l2)).
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
    lsc_impl_ls lsc_in : lsc.

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
    eauto with lsc.
Qed.

Lemma ls_len : length a = n + 1.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    eauto with lsc.
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
    eauto with lsc.
Qed.

Lemma ls_nth_2 N d
    (LT : m < N)
    (LT' : N < n) :
    nth N b d = nth N a d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    eauto with lsc.
Qed.

Lemma ls_nth_y d :
    nth n b d = nth m a d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    now erewrite lsc_nth_x, lsc_nth_y by eauto with lsc.
Qed.

Lemma ls_nth_x d :
    nth m b d = nth n a d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    now erewrite lsc_nth_x, lsc_nth_y by eauto with lsc.
Qed.

Lemma ls_nth N d
    (NEQ1 : N <> m)
    (NEQ2 : N <> n) :
    nth N b d = nth N a d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst n m.
    eauto with lsc.
Qed.

Lemma ls_in : (fun x => In x a) ≡₁ (fun x => In x b).
Proof using SWAPPED.
    destruct SWAPPED; desc.
    eauto with lsc.
Qed.

End ListsSwapped.

Global Hint Resolve ls_sym ls_len ls_len_eq ls_nth_1 ls_nth_2 ls_nth
    ls_nth_x ls_nth_y ls_lt_m ls_lt_n ls_in : ls.

Section TracesSwapped.

Variable A : Type.
Variable t t' : trace A.
Variable m n : nat.
Variable SWAPPED : trace_swapped A t t' m n.

Lemma trace_swapped_sym : trace_swapped A t' t m n.
Proof using SWAPPED.
    destruct SWAPPED as (l & l' & SWAPPED'); desc; subst t t'.
    exists l'; exists l; exists rest.
    splits; eauto with ls.
Qed.

Lemma trace_swapped_len : trace_length t' = trace_length t.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst t t'.
    destruct rest; simpl; try easy.
    autorewrite with calc_length; do 2 f_equal.
    eauto with ls.
Qed.

Lemma trace_swapped_lt_m : m < n.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst t t'.
    eauto with ls.
Qed.

Lemma trace_swapped_lt_n : NOmega.lt_nat_l n (trace_length t).
Proof using SWAPPED.
    destruct SWAPPED; desc; subst t t'.
    rewrite trace_length_app.
    destruct (trace_length rest); simpl; try easy.
    eauto using PeanoNat.Nat.lt_lt_add_r with ls.
Qed.

(* TODO: useful for hahn? *)
Lemma trace_nth_app1 (a b : trace A) N d
    (LT : NOmega.lt_nat_l N (trace_length a)) :
    trace_nth N (trace_app a b) d = trace_nth N a d.
Proof using.
    rewrite trace_nth_app.
    destruct excluded_middle_informative; auto.
    now exfalso.
Qed.

Lemma trace_nth_app2 (a : list A) (b : trace A) N d
    (LT : length a <= N) :
    trace_nth N (trace_app (trace_fin a) b) d = trace_nth (N - length a) b d.
Proof using.
    rewrite trace_nth_app.
    destruct excluded_middle_informative; simpl in *; auto.
    lia.
Qed.

Lemma trace_swapped_nth_1 N d
    (LT : N < m) :
    trace_nth N t' d = trace_nth N t d.
Proof using SWAPPED.
    assert (LT' : m < n) by apply trace_swapped_lt_m.
    destruct SWAPPED; desc; subst t t'.
    rewrite !trace_nth_app1; simpl; eauto with ls.
    all: erewrite ls_len; eauto with ls; lia.
Qed.

Lemma trace_swapped_nth_2 N d
    (LT : m < N)
    (LT' : N < n) :
    trace_nth N t' d = trace_nth N t d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst t t'.
    rewrite !trace_nth_app1; simpl; eauto with ls.
    all: erewrite ls_len; eauto with ls; lia.
Qed.

Lemma trace_swapped_nth_3 N d
    (LT : n < N) :
    trace_nth N t' d = trace_nth N t d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst t t'.
    rewrite !trace_nth_app2; simpl.
    all: erewrite !ls_len; eauto with ls; lia.
Qed.

Lemma trace_swapped_nth_y d :
    trace_nth n t' d = trace_nth m t d.
Proof using SWAPPED.
    assert (LT' : m < n) by apply trace_swapped_lt_m.
    destruct SWAPPED; desc; subst t t'.
    rewrite !trace_nth_app1; simpl; eauto with ls.
    erewrite ls_len; eauto with ls; lia.
Qed.

Lemma trace_swapped_nth_x d :
    trace_nth m t' d = trace_nth n t d.
Proof using SWAPPED.
    assert (LT' : m < n) by apply trace_swapped_lt_m.
    destruct SWAPPED; desc; subst t t'.
    rewrite !trace_nth_app1; simpl; eauto with ls.
    erewrite ls_len; eauto with ls; lia.
Qed.

Lemma trace_swapped_nth N d
    (NEQ1 : N <> m)
    (NEQ2 : N <> n) :
    trace_nth N t d = trace_nth N t' d.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst t t'.
    destruct (PeanoNat.Nat.lt_ge_cases N (n + 1)).
    { rewrite !trace_nth_app1; simpl; eauto with ls.
      all: erewrite ls_len; eauto with ls; lia. }
    rewrite !trace_nth_app2.
    all: erewrite !ls_len; eauto with ls.
Qed.

Lemma trace_swapped_elems : trace_elems t ≡₁ trace_elems t'.
Proof using SWAPPED.
    destruct SWAPPED; desc; subst t t'.
    rewrite !trace_elems_app. simpl.
    rewrite ls_in by eauto.
    assert (FIN : forall (l : list A), trace_finite (trace_fin l)) by (intros; red; eauto).
    do 2 destruct excluded_middle_informative; try solve [exfalso; eauto].
    done.
Qed.

End TracesSwapped.

Global Hint Resolve trace_swapped_sym trace_swapped_len trace_swapped_lt_m
    trace_swapped_lt_n trace_swapped_nth_1 trace_swapped_nth_2 trace_swapped_nth_3
    trace_swapped_nth_x trace_swapped_nth_y trace_swapped_nth trace_swapped_elems
     : trace_swap.