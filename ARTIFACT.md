This artifact provides the supplementary Coq development for the *Relaxed Memory Concurrency Re-executed* paper.

## List of paper claims and definitions supported by the artifact

The overall structure of Coq development in `src` folder is as follows:

* `lib` contains various auxillary definitions and lemmas for the project
* `reordering` contains the proof that reordering transformation is consistent in XMM
* `traces` contains various properties and definitions for connecting graphs to traces
* `xmm` contains the basic deifinitions and properties of the model
* `xmm_cons` contains proofs for the consistency properties

### Formal model

* Definitions of labels (Def 3.1), events (Def 3.2), execution graphs (Def 3.3) and their well-formedness predicate (Def 3.3 too) are provided by the `imm` package.
* We define the execution graph constructions rules, along with concepts such as "rf-completeness" (Def 3.5) and "well formed configuration" (Def 3.6) in `src/xmm/Core.v`.
    - This includes the step deltas (See figure 3.4)
* A sanity-check proof that a well-formed graph is well-formed after `add_event` can be found in `src/xmm/AddEventWf.v`.
* The proof for multistep lemma (Lm 3.1) can be found in `src/xmm/SubToFullExec.v` under the name `sub_to_full_exec`.
* Definitions of graphs embdedding (Def 3.7) and the `StableUncommittedReads` predicate (Def 3.8) are located in `src/xmm/Core.v` too.
* The proof for listless multistep lemma (Lm 3.2) can be found in `src/xmm/SubToFullExec.v` under the name `sub_to_full_exec_listless`.
* The definition of `RC20` consistency can be found in `src/xmm/Core.v` as the `WCore.is_cons` predicate.
    - The `hb` and `sw` relations are acquired from `imm`.
    - The `rpo` and `rhb` relation definitions can be found in `src/xmm/Rhb.v`.
* The definition of the `srf` relation (Def 3.11) along some of its properties can be found in `src/xmm/Srf.v`.

### Soundness of program transformations

* The proofs of all consistency predicate properties is located in the `xmm_cons` direcotry
    - The monotonicity (Lm B.7) is proven in `src/xmm_cons/ConsistencyMonotonicity.v`
    - The maximal read extensibility (Lm B.8) is proven in `src/xmm_cons/ConsistencyReadExtensibility.v`
    - The maximal write extensibility (Lm B.9) is proven in `srx/xmm_cons/ConsistencyWriteExtensibility.v`
    - Some common consistency lemmas are proven in `src/xmm_cons/ConsistencyCommon.v`
* The proof for consistency of the reordering transformation with XMM is located inside the `reordering` directory
    - The simulation relation (Def E.32) is located in `src/reordering/ReordSimrel.v` along with a "Step Invariant" predicate, which is expected to be preserved by the target graph after each step.
    - The proof of simulation relation for init graphs (Lm E.25) is located in `src/reordering/ReordSimrelInit.v` along with the proof that init graphs satisfy the "Step Invariant".
    - The "not a, not b" step (Lm E.27) is proven in `src/reordering/ReordExecNaNb.v`.
    - The "b" step (Lm E.28) is proven in `src/reordering/ReordExecB.v`.
    - The "a" step (Lm E.29) is proven in `src/reordering/ReordExecA.v`.
    - The "rexec" step (Lm E.30) is provne in `src/reordering/ReordReexec.v`.

### Miscellaneous

* Additional files in the xmm directory include:
    - Some common simulation relation properties in `src/xmm/SimrelCommon.v`
    - Some useful properties of the step deltas in `src/xmm/StepOps.v`
    - A shortcut lemma for proving less goals when we know in advance that the graph acquired after adding an event is well-formed
* List of files in `lib`
    - `src/lib/AuxDef.v` provides extra definitions like function surjectivity (without any related proofs).
    - `src/lib/AuxInj.v` provides extra lemmas about mapping relations and sets with injective functions.
    - `src/lib/AuxRel.v` and `src/lib/AuxRel2.v` provide various handy rewrite lemmas without any particular subject.
    - `src/lib/ExecEquiv.v` provides the definition of execution equivalence, which is equivalent to definitional execution equality under the assumptions of classic logic.
    - `src/lib/HahnTotalListEx.v` provides extra lemmas for working with the total order induced by a list.
    - `src/lib/HbPrefix.v` provides a handy (for avoiding recursive definitions) lemma for computing the view-front relation (`vf`) in smaller graphs by removing some "happens-after events".
    - `src/lib/Instructions.v` provides a weak universal abstraction of program instructions.
    - `src/lib/PorfPrefix.v` provides simpler but more constraining lemmas for computing the `view-front relation in smaller graphs by removing the po-rf suffix.

## List of paper claims planned, but not yet supported by the artifact

The following statements are planned to be supported (in order of priority)
1. The following statements from the reordering transformation
    - Reordering reexecution step lemma (Lm E.2.30 )
    - Reordering simulation relation implying consistency (Lm E.2.31)
    - The lemma about simulating any sequence of steps from target graph in source graph (Lm E.2.26)
    - The reordering theorem (Th E.2.5)
2. Full support for the sequentilisation transformation
3. Other consistency properties
    - same-read extensibility (Lm B.11)
    - overwrite extensibility (Lm B.10)