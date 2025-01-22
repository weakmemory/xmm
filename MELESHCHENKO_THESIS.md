This documents details the parts of the artifact, that have been developed as part of Meleshcenko Innokentii's bachelor thesis.

## Overiew

The part produces during the writing of the thesis were:
1. The formal model itself -- mostly contained in `src/xmm` and `src/xmm_cons`
2. The reordering transformation -- mostly contained in `src/reordering`
3. Various auxiliary facts -- contained in `src/lib` and `src/traces`

## Detail

### The Formal Model Itself

* `src/xmm/Core.v` formalises the two steps XMM can take. The execute step is defined as `exec_inst`, the re-execute step is defined as `reexec`. The guide-add-step rule is formalised as `guided_step`, while the add-event rule is formalised as `add_event`. The "deltas" (delta-rf, delta-mo, etc.) are defined there too.
* `src/xmm/AddEventWf.v` provides a "sanity check" lemma `add_event_wf`, that ensures that add-event rule preserves graph well-formedness.
* `src/xmm/StepOps.v` is a library of acts about model steps. It provides the following facts:
    - Lemmas about applying the functions to the "deltas" (e.g. `mapped_co_delta`)
    - Lemmas about extracting deltas from the result-graph relations (e.g. `rf_delta_WE`)
    - A short-cut lemma when the resulting graph is known it advance to be well-formed -- `add_event_to_wf`
    - The fact that consistency implies that internal rf edges respect the po order -- `rfi_in_sb`
    - Preservation of various useful properties of graphs with each step (e.g. rf-completeness, well-formedness, finiteness, init event properties) -- `xmm_exec_correct`, `xmm_rexec_correct`
* `src/xmm/SubToFullExec.v` is the file solely dedicated to "lemma 1" or multistep lemma (the lemma about being able to take many guided steps, given some finite sequence of events). The main results are the `sub_to_full_exec` and `sub_to_full_exec_listless` lemmas.
* `src/xmm/SimrelCommon.v` and `src/xmm/Thrdle.v` just provide some useful small shortcuts.
* `src/xmm_cons/ConsistencyMonotonicity.v` provides the proof of the monotonicity property together with a useful rhb relation mapping lemma.
* `src/xmm_cons/ConsistencyReadExtent.v` provides the proof for the read extensibility
* `src/xmm_cons/ConsistencyWriteExtent.v` privdes the proof for write extensibility

### The Reordering Transformation

- The simulation relation (Def E.32) is located in `src/reordering/ReordSimrel.v` along with a "Step Invariant" predicate, which is expected to be preserved by the target graph after each step.
- The proof of simulation relation for init graphs (Lm E.25) is located in `src/reordering/ReordSimrelInit.v` along with the proof that init graphs satisfy the "Step Invariant".
- The "not a, not b" step (Lm E.27) is proven in `src/reordering/ReordExecNaNb.v`.
- The "b" step (Lm E.28) is proven in `src/reordering/ReordExecB.v`.
- The "a" step (Lm E.29) is proven in `src/reordering/ReordExecA.v`.
- The "rexec" step (Lm E.30) is provne in `src/reordering/ReordReexec.v`.