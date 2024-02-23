Require Import Lia Setoid Program.Basics.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
Import ListNotations.

Open Scope list_scope.

Section TraceSwapConstructive.

Variable A : Type.

Record t_constructive_gen l1 l2 rest x y (t t' : trace A) : Prop :=
{   L_FORM : t = trace_app (trace_fin (l1 ++ [x] ++ l2 ++ [y])) rest;
    R_FORM : t' = trace_app (trace_fin (l1 ++ [y] ++ l2 ++ [x])) rest;
}.

Lemma swapped_sym l1 l2 rest x y t t'
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t') :
    t_constructive_gen l1 l2 rest y x t' t.
Proof using.
    destruct SWAPPED; subst t t'.
    constructor; ins.
Qed.

Lemma swapped_len l1 l2 rest x y t t'
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t') :
    trace_length t' = trace_length t.
Proof using.
    destruct SWAPPED; subst t t'.
    rewrite !trace_length_app. simpl.
    change (y :: l2 ++ [x]) with ([y] ++ l2 ++ [x]).
    change (x :: l2 ++ [y]) with ([x] ++ l2 ++ [y]).
    now do 6 rewrite length_app.
Qed.

Lemma swapped_l2_len l1 l2 rest x y t t'
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t') :
    NOmega.lt_nat_l (length l1 + 1 + length l2) (trace_length t').
Proof using.
    destruct SWAPPED; subst t'.
    rewrite trace_length_app; simpl.
    change (y :: l2 ++ [x]) with ([y] ++ l2 ++ [x]).
    do 3 rewrite length_app.
    destruct trace_length; try easy.
    simpl. lia.
Qed.

Lemma swapped_l1_len l1 l2 rest x y t t'
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t') :
    NOmega.lt_nat_l (length l1) (trace_length t').
Proof using.
    eapply NOmega.lt_lt_nat.
    2: eapply swapped_l2_len; exact SWAPPED.
    lia.
Qed.

Lemma swapped_nth_1 l1 l2 rest x y t t' n d
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t')
    (LT : n < length l1) :
    trace_nth n t' d = trace_nth n t d.
Proof using.
    destruct SWAPPED; subst t t'.
    rewrite !trace_nth_app. simpl.
    rewrite !length_app.
    do 2 destruct (excluded_middle_informative _); try lia.
    rewrite !nth_app.
    destruct (Compare_dec.le_lt_dec _ _); auto.
    exfalso; lia.
Qed.

Lemma swapped_nth_2 l1 l2 rest x y t t' n d
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t')
    (LT : length l1 < n)
    (LT' : n < length l1 + 1 + length l2):
    trace_nth n t' d = trace_nth n t d.
Proof using.
    destruct SWAPPED; subst t t'.
    rewrite !trace_nth_app. simpl.
    do 2 (rewrite !length_app; simpl).
    destruct (excluded_middle_informative _); try lia.
    rewrite !nth_app.
    destruct (Compare_dec.le_lt_dec _ _); auto.
    change (y :: l2 ++ [x]) with ([y] ++ l2 ++ [x]).
    change (x :: l2 ++ [y]) with ([x] ++ l2 ++ [y]).
    rewrite !nth_app.
    destruct (Compare_dec.le_lt_dec _ _); try solve [simpl in *; lia].
    destruct (Compare_dec.le_lt_dec _ _); try solve [simpl in *; lia].
    done.
Qed.

Lemma swapped_nth_3 l1 l2 rest x y t t' n d
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t')
    (LT : length l1 + 1 + length l2 < n):
    trace_nth n t' d = trace_nth n t d.
Proof using.
    destruct SWAPPED; subst t t'.
    rewrite !trace_nth_app. simpl.
    do 2 (rewrite !length_app; simpl).
    now destruct (excluded_middle_informative _); try lia.
Qed.

Lemma swapped_nth_x l1 l2 rest x y t t' d
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t') :
    trace_nth (length l1) t' d = y.
Proof using.
    destruct SWAPPED; subst t t'.
    rewrite !trace_nth_app. simpl.
    do 2 (rewrite !length_app; simpl).
    destruct (excluded_middle_informative _); try lia.
    rewrite nth_app.
    destruct (Compare_dec.le_lt_dec _ _); try lia.
    now rewrite PeanoNat.Nat.sub_diag.
Qed.

Lemma swapped_nth_y l1 l2 rest x y t t' d
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t') :
    trace_nth (length l1 + 1 + length l2) t' d = x.
Proof using.
    destruct SWAPPED; subst t t'.
    rewrite !trace_nth_app. simpl.
    do 2 (rewrite !length_app; simpl).
    destruct (excluded_middle_informative _); try lia.
    rewrite nth_app.
    destruct (Compare_dec.le_lt_dec _ _); try lia.
    change (y :: l2 ++ [x]) with ([y] ++ l2 ++ [x]).
    rewrite nth_app.
    destruct (Compare_dec.le_lt_dec _ _); try solve [simpl in *; lia].
    rewrite nth_app.
    destruct (Compare_dec.le_lt_dec _ _); try solve [simpl in *; lia].
    simpl.
    arewrite (length l1 + 1 + length l2 - length l1 - 1 - length l2 = 0) by lia.
Qed.

Lemma swapped_nth l1 l2 rest x y t t' n d
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t')
    (NEQ1 : n <> length l1)
    (NEQ2 : n <> length l1 + 1 + length l2) :
    trace_nth n t' d = trace_nth n t d.
Proof using.
    destruct (NPeano.Nat.lt_total n (length l1)) as [LT | [EQ | GT]].
    all: destruct (NPeano.Nat.lt_total n (length l1 + 1 + length l2)) as [LT' | [EQ' | GT']].
    all: try lia.
    all: eauto using swapped_nth_1, swapped_nth_2, swapped_nth_3.
Qed.

Lemma all_finite (l : list A) :
    trace_finite (trace_fin l).
Proof using.
    unfold trace_finite. eauto.
Qed.

Lemma swapped_same_elems_sub l1 l2 rest x y t t'
    (SWAPPED : t_constructive_gen l1 l2 rest x y t t') :
    trace_elems t ≡₁ trace_elems t'.
Proof using.
    destruct SWAPPED; subst t t'.
    rewrite !trace_elems_app.
    do 2 destruct excluded_middle_informative.
    all: try solve [exfalso; eauto using all_finite].
    simpl. unfolder. splits; intros e HIN.
    all: do 2 (rewrite in_app_iff in *; simpl in *).
    all: desf; tauto.
Qed.

Definition trace_swapped t t' n m : Prop :=
    exists l1 l2 rest x y,
        ⟪ L1_LEN : length l1 = n ⟫ /\
        ⟪ L2_LEN : length l2 = m ⟫ /\
        ⟪ STRUCT : t_constructive_gen l1 l2 rest x y t t' ⟫.


