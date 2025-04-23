Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import xmm_s_hb.
Require Import Lia.
From xmm Require Import Reordering.
From xmm Require Import ThreadTrace.
From xmm Require Import Programs.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import Setoid Morphisms Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section SimRelSeq.

Variable X_s X_t : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.
Variable mappre_rev : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rhb_t'" := (rhb G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rpo_imm_t'" := (rpo_imm G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rpo_imm_s'" := (rpo_imm G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Definition po_seq := (Tid_ t_1 ∩₁ E_s) × (Tid_ t_2 ∩₁ E_s).

Variable ptc_1 ptc_2 : program_trace.

Definition t_12_len := length (ptc_2 t_1).
Definition t_1_len := length (ptc_1 t_1).
Definition t_2_len := length (ptc_1 t_2).

Record seq_simrel : Prop := {
    seq_inj : inj_dom E_t mapper;

    seq_tid_1 : forall e : actid, E_t e -> tid (mapper e) <> t_2 -> tid e = tid (mapper e);
    seq_tid_2 : forall e : actid, E_t e -> tid (mapper e) = t_2 -> tid e = t_1;

    seq_lab : eq_dom E_t lab_t (lab_s ∘ mapper);
    seq_lab_rev : eq_dom E_s lab_s (lab_t ∘ mappre_rev);
    seq_acts : E_s ≡₁ mapper ↑₁ E_t;
    seq_acts_rev : E_t ≡₁ mappre_rev ↑₁ E_s;
    seq_sb : sb_s ∪ po_seq ≡ mapper ↑ sb_t;
    seq_rf : rf_s ≡ mapper ↑ rf_t;
    seq_co : co_s ≡ mapper ↑ co_t;
    seq_rmw : rmw_s ≡ mapper ↑ rmw_t;
    seq_threads : threads_set G_s ≡₁ threads_set G_t ∪₁ eq t_2;

    seq_ctrl : ctrl_s ≡ ∅₂;
    seq_data : data_s ≡ ∅₂;
    seq_addr : addr_s ≡ ∅₂;
    seq_rmw_dep : rmw_dep_s ≡ ∅₂;

    seq_init : fixset is_init mapper;
    seq_init_rev : fixset is_init mappre_rev;
    seq_codom : mapper ↑₁ E_t ⊆₁ E_s;

    seq_mapeq : forall e : actid, E_t e -> tid (mapper e) <> t_2 -> mapper e = e;
    seq_mapeq_rev : forall e : actid, E_s e -> tid e <> t_2 -> mappre_rev e = e;
    seq_mapto : forall e : actid, E_t e -> tid (mapper e) = t_2 -> mapper e = ThreadEvent t_2 (index e - t_1_len);
    seq_index : forall e : actid, E_t e -> tid (mapper e) = t_2 -> index e = t_1_len + index (mapper e);
    seq_thrd : forall e : actid, E_t e -> tid (mapper e) = t_2 -> tid e = t_1;

    seq_rest : forall e : actid, ~ E_t e -> mapper e = e;
    seq_rest_rev : forall e : actid, ~ E_s e -> mappre_rev e = e;
    seq_rlab : forall e : actid, ~ E_s e -> lab_s e = lab_t (mappre_rev e);
}.

Record seq_simrel_inv : Prop := {
    rsr_Gt_wf : Wf G_t;
    rsr_nctrl : ctrl_t ≡ ∅₂;
    rsr_ndata : data_t ≡ ∅₂;
    rsr_naddr : addr_t ≡ ∅₂;
    rsr_nrmw_dep : rmw_dep_t ≡ ∅₂;
}.

End SimRelSeq.

Section SeqSimrelInit.

Variable X_t X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.
Variable mappre_rev : actid -> actid.

Variable ptc_1 ptc_2 : program_trace.

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_s'" := (WCore.G X_s).

Hypothesis INV : seq_simrel_inv X_t.

Lemma seq_simrel_init threads
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRD1 : threads t_1)
    (THRDNEQ : t_1 <> t_2)
    (INIT : threads tid_init) :
  << SIMREL : seq_simrel
    (WCore.Build_t (WCore.init_exec (threads ∪₁ eq t_2)) ∅₂)
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    t_1 t_2
    id id ptc_1 >>.
Proof using.
    assert (IWF : Wf (WCore.init_exec threads)).
    { now apply WCore.wf_init_exec. }
    split; vauto; ins.
    { assert (FALSE : t_2 = tid_init).
      { rewrite <- H0. unfold tid. desf.
        unfold is_init in H. desf. }
      desf. }
    { clear; basic_solver. }
    { clear; basic_solver. }
    { rewrite collect_rel_id; split; vauto.
      unfold po_seq; ins.
      assert (EMP1 : (fun e : actid => tid e = t_1)
                    ∩₁ (fun a : actid => is_init a) ≡₁ ∅).
      { split; [|basic_solver].
        intros x COND. destruct COND as [TID ISINIT].
        unfold is_init in ISINIT. desf. }
      assert (EMP2 : (fun e : actid => tid e = t_2)
                    ∩₁ (fun a : actid => is_init a) ≡₁ ∅).
      { split; [|basic_solver].
        intros x COND. destruct COND as [TID ISINIT].
        unfold is_init in ISINIT. desf. }
      rewrite EMP1, EMP2. clear; basic_solver 8. }
    all : try basic_solver.
    all : unfold is_init in H; desf.
Qed.

End SeqSimrelInit.
