From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Lia.

Lemma total_order_from_list_l {A} (l1 l2 : list A) :
  total_order_from_list l1 ⊆
    total_order_from_list (l1 ++ l2).
Proof using.
  intros x y HREL. apply total_order_from_list_app.
  eauto.
Qed.

Lemma total_order_from_list_r {A} (l1 l2 : list A) :
  total_order_from_list l2 ⊆
    total_order_from_list (l1 ++ l2).
Proof using.
  intros x y HREL. apply total_order_from_list_app.
  eauto.
Qed.

Lemma in_iff {A} (x : A) l
    (IN : In x l) :
  exists l1 l2, l = l1 ++ x :: l2.
Proof using.
  induction l as [ | h t IHL]; ins.
  desf.
  { exists [], t; ins. }
  destruct (IHL IN) as (l1 & l2 & HEQ).
  subst t. exists (h :: l1), l2. ins.
Qed.

Lemma total_order_from_list_bridge {A} (x y : A) l1 l2
    (XIN : In x l1)
    (YIN : In y l2) :
  total_order_from_list (l1 ++ l2) x y.
Proof using.
  apply total_order_from_list_app. eauto.
Qed.

Lemma list_neq_helper {A} (a : A) l1 x l2 y l3 :
  [a] <> l1 ++ x :: l2 ++ y :: l3.
Proof using.
  intro HREL. apply f_equal with (f := @length A) in HREL.
  autorewrite with calc_length in HREL. lia.
Qed.

Lemma total_order_from_filterP {A} s (l : list A) :
  total_order_from_list (filterP s l) ≡ restr_rel s (total_order_from_list l).
Proof using.
  split; intros x y HREL.
  all: induction l as [ | h t IHL]; ins.
  all: try change (h :: t) with ([h] ++ t) in *.
  all: try change (h :: filterP s t)
             with ([h] ++ filterP s t) in *.
  { red in HREL. desf.
    exfalso. eapply app_cons_not_nil. eauto. }
  { unfolder in IHL. desf.
    all: unfolder; splits.
    all: try apply total_order_from_list_app.
    all: try apply total_order_from_list_app in HREL.
    all: rewrite ?in_filterP_iff in *.
    all: ins; splits; desf; eauto.
    all: try now apply IHL.
    all: try now (red in HREL; desf; exfalso;
                  eapply list_neq_helper, HREL).
    all: do 2 right; now apply IHL. }
  { red in HREL. desf. }
  unfolder in HREL. unfolder in IHL.
  desf; try apply total_order_from_list_app.
  all: try apply total_order_from_list_app in HREL.
  all: ins; desf; eauto 11.
  { left; split; eauto.
    now apply in_filterP_iff; split. }
  red in HREL. desf.
  exfalso. eapply list_neq_helper. eauto.
Qed.

Lemma total_order_from_sorted {A} (l : list A) ord
    (ORD : strict_total_order (fun x => In x l) ord)
    (SORT : StronglySorted ord l) :
  total_order_from_list l ≡
    restr_rel (fun x => In x l) ord.
Proof using.
  induction l as [ | h t IHL]; ins.
  { unfold total_order_from_list. unfolder.
    split; intros x y HREL; desf.
    exfalso. eapply app_cons_not_nil; eauto. }
  change (h :: t) with ([h] ++ t).
  split; intros x y HREL.
  { apply total_order_from_list_app in HREL.
    unfolder. ins. desf; splits; ins; eauto.
    all: apply StronglySorted_inv in SORT; desf.
    all: try now (exfalso; red in HREL; desf;
                  eapply list_neq_helper; eauto).
    { eapply ForallE; eauto. }
    { apply IHL in HREL; ins.
      { apply HREL. }
      unfolder in ORD; unfolder; desf.
      splits; ins; eauto. }
    all: eauto using total_order_from_list_in1,
                     total_order_from_list_in2. }
  unfolder in ORD. desf.
  apply total_order_from_list_app. ins.
  apply StronglySorted_inv in SORT; desf.
  unfolder in HREL. desf.
  all: eauto.
  { exfalso. eauto. }
  { exfalso. apply ORD with x. apply ORD1 with y; ins.
    eapply ForallE; eauto. }
  do 2 right. apply IHL; ins.
  unfolder; splits; ins; eauto.
Qed.

Lemma total_order_from_isort {A} (l : list A) ord
    (NODUP : NoDup l)
    (ORD : strict_total_order ⊤₁ ord) :
  total_order_from_list (isort ord l) ≡
    restr_rel (fun x => In x l) ord.
Proof using.
  rewrite total_order_from_sorted with (ord := ord)
                                      (l := isort ord l).
  { unfolder. split; intros x y HREL; desf.
    all: splits; ins.
    all: eapply in_isort_iff; eauto. }
  { unfolder. unfolder in ORD. desf.
    splits; ins; eauto. }
  apply StronglySorted_isort; ins.
Qed.

Lemma StronglySorted_sub {A} (l : list A) r ext_r
    (SUB : r ⊆ ext_r)
    (TOT : strict_total_order (fun x => In x l) r)
    (EXT_TOT : strict_total_order ⊤₁ ext_r)
    (SORT : StronglySorted ext_r l) :
  StronglySorted r l.
Proof using.
  induction l; ins.
  unfolder in EXT_TOT. desf.
  unfolder in TOT. desf.
  apply StronglySorted_inv in SORT. desf.
  constructor; ins.
  { apply IHl; eauto.
    unfolder; splits; eauto. }
  apply ForallE. intros x HIN.
  destruct TOT0 with a x as [HORD|HORD]; eauto.
  { intro F; subst. apply EXT_TOT with x.
    eapply ForallE; eauto. }
  apply SUB in HORD.
  enough (HORD' : ext_r a x).
  { exfalso. eauto. }
  eapply ForallE; eauto.
Qed.

Lemma list_min_elt {A} {h : A} {t}
    (NODUP : NoDup (h :: t)) :
  min_elt (total_order_from_list (h :: t)) h.
Proof using.
  unfolder. unfold total_order_from_list.
  intros e F. desf.
  enough (IN : In h t) by inv NODUP.
  destruct l1 as [ | h' t']; inv F.
  { apply in_app_iff. right. desf. }
  apply in_app_iff; right.
  ins. right.
  apply in_app_iff. right.
  now left.
Qed.