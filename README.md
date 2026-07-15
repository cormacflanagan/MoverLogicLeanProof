# Mover Logic in Lean 4

A self-contained Lean 4 formalization of the program logic from
**"Mover Logic: A Concurrent Program Logic for Reduction and Rely-Guarantee
Reasoning"** (Flanagan & Freund, ECOOP 2024) — the paper in this repository
(`final/main.tex`).

Nothing in the existing repository is modified; this all lives under `lean/`.

## Build

```bash
cd lean
~/.elan/bin/lake build          # ~5s, no Mathlib dependency
```

Toolchain: `leanprover/lean4:v4.32.0` (pinned in `lean-toolchain`, installed via
`elan`). The development is deliberately **Mathlib-free** — it depends only on
core Lean, so it builds in seconds and is easy to audit.

## The modules

Built in five pieces (Effects → Language → Specs → Logic → Soundness), plus a
sixth (`Instrumented.lean`) mechanizing the paper's full soundness chain.

| File | Paper section | Contents |
|------|---------------|----------|
| `MoverLogic/Effects.lean`   | §"Effects"           | The 6-point effect lattice `Y,B,R,L,N,E`; order `⊑`, join `⊔`, sequential composition `;;`, closure `*`; the **reduction / DFA theorem** |
| `MoverLogic/Language.lean`  | §"Mover Logic Language" | Stores, actions, statements, evaluation contexts, per-thread + whole-state operational semantics, "goes wrong" |
| `MoverLogic/Specs.lean`     | §"Mover Specifications" | Mover specs `M`, the lifted `M(A,P)` as a genuine least-upper-bound, the four **Validity** conditions |
| `MoverLogic/Logic.lean`     | Figs. "proof rules"  | Predicate operators; the judgment `R,G ⊢ s : P ⇒ Q ! e` with every rule; function + state judgments |
| `MoverLogic/Canonical.lean` | Lemmas Consequence / Evaluation Context | Canonical (non-`M-conseq`) form, `M-seq` inversion, and the Evaluation Context lemma — the structural core of Preservation |
| `MoverLogic/Reduction.lean` | Lemmas Right / Left Commutativity, Diamond | All state-level action/action commutation lemmas of Reduction — Right, Left, the parallel Diamond, and the store-preserving cases — derived from `Valid M` |
| `MoverLogic/ReductionThm.lean` | §sec:red-thm (Reduction proof) | The **trace-composable** local-commutation layer: thread-indexed steps `→_i`, the state classes `ℝ_i`/`𝕃_i`/`ℕ_i`/`𝔼_i`, the step classifier, *absorbing wrong*, and `right_commutes` / `left_commutes` / `diamond_commutes` / `indep_*` covering **every** step kind (structural + store-touching, `I-action` + `I-if`) with all class side-conditions discharged |
| `MoverLogic/PostCommit.lean` | Lemma lem:post-commit-term | The statement size metric `bodySize`, the model well-formedness the paper assumes (`NeverYields`, `CondTotal`, `GoodSizing` = atomic functions non-recursive), the `progress` engine, and **`post_commit_term`** — a post-commit thread of a verified state runs to a settled state under `↦` |
| `MoverLogic/Assembly.lean` | §sec:red-thm (global argument) | Infrastructure for the trace-block assembly: tagged runs `IStepsT`, **class invariance** under other-thread steps, the phase-generalized `right_commutes'`, and `NonJRun` (the "main trace" shape). The remaining combinatorial bubble/induction is documented here |
| `MoverLogic/Soundness.lean` | Thm "Soundness"      | Not-Wrong for standard states; Soundness-modulo-Preservation |
| `MoverLogic/Instrumented.lean` | §"Overview of Correctness Proof" | The **full soundness chain**: instrumented semantics, non-preemptive scheduler, `⊢ Π`, Simulation, Reduction, Preservation, and the assembled `soundness` |

## What is proved

The whole development contains **no `sorry` and no `native_decide`**. Every
result named in this section is machine-checked using **only Lean's standard
axioms** (`propext` / `Classical.choice` / `Quot.sound`; verify with
`#print axioms`). The single place where custom axioms enter is the two
faithful metatheorems of the full soundness chain — `reduction` and
`preservation` — documented in the last section; `#print axioms soundness`
lists exactly those two and nothing else.

**Piece 1 — the mathematical core (fully proved).**
- `Effect.seq_assoc`, `seq_B_left/right` — `(Effect, ;;, B)` is a monoid.
- `join_comm/assoc/idem`, `le_*` — `⊑` is the lattice order; `join` is the LUB.
- `Effect.stateOf_seq` — the homomorphism linking the algebra to the automaton.
- `Effect.runDFA_eq_stateOf` — running the reduction DFA equals the abstract
  state of the `;`-fold.
- **`Effect.reducible_iff_seqFold_ne_E`** — *the paper's key claim, verbatim:*
  an effect sequence composes under `;` to something other than the error `E`
  **iff** it is accepted by the reduction DFA (i.e. it is reducible sequences
  `R*[N]L*` separated by yields).
- `Effect.yielding_accepts` — an explicit inductive `R*[N]L*`-with-yields
  grammar is sound for the DFA.

**Piece 3 (fully proved).** `le_sSup` / `sSup_le`: `M(A,P)` really is the least
upper bound over `P`'s pre-stores.

**Piece 5 (fully proved).**
- **`verified_not_wrong`** — a verified state is not *currently* wrong (the
  paper's "Verified States Are Not Wrong", proved by context inversion on rule
  M-wrong). This is the base case of soundness, proved unconditionally.
- **`soundness_of_preservation`** — *if* verification is preserved by each step
  (the paper's Preservation theorem), *then* a verified state never goes wrong.
  The induction assembling Preservation with the base case is fully mechanized.
- **`thread_effect_reducible`** — bridges to Piece 1: each verified thread's
  effect is non-error, hence any realizing effect sequence is DFA-accepted.

## The full soundness chain (`Instrumented.lean`)

`MoverLogic/Instrumented.lean` mechanizes the paper's entire proof structure
(§"Overview of Correctness Proof") and assembles the top-level theorem

```lean
theorem soundness (h : StateValid M D st) : ¬ GoesWrong D.bodies st
```

exactly as in the paper: embed `Σ` into a verified, all-yielding instrumented
`Π`; run Simulation to a wrong preemptive `Π'`; apply Reduction to reach a wrong
non-preemptive `Π''`; apply Preservation to get `⊢ Π''`; contradict Not-Wrong.

**Proved with no `sorry`, only standard axioms:**
- the instrumented semantics (rules I-*), preemptive `→` and non-preemptive `↦`;
- `IStateValid.not_wrong` — Not-Wrong for instrumented states (Thm not-wrong);
- `simulation` and `simulation_star` — the Simulation theorem and its closure;
- `embed` — a verified standard state embeds into a verified instrumented one;
- `preservation_star` — Preservation lifted along `↦*`;
- `right_commute` / `left_commute` — the store-level mover commutativity (paper
  Lemmas Right/Left Commutativity) derived directly from `Valid M`; this is the
  mathematical core on which the state-level Reduction argument rests;
- `soundness` — the final assembly.

**Taken as two named axioms** (`#print axioms soundness` shows exactly these,
plus Lean's standard `propext`/`Classical.choice`/`Quot.sound`):
- `reduction`    — Theorem thm:red (proof: the `Pre`/`Post`/`Finish` trace-block
  algebra with Diamond / Iterative Diamond / Post-Commit Termination);
- `preservation` — Theorem thm:pres (proof: the Evaluation-Context / Consequence
  / Preservation-for-Redexes / Yield-Stabilization / Prefix / Context-Switch
  inversion stack).

Both are stated faithfully over the instrumented non-preemptive semantics (where
they are *true* — unlike step-wise preservation over the raw preemptive
semantics, which is false and is exactly what reduction repairs). Their
paper-length proofs are the remaining mechanization work.

`Soundness.lean` additionally provides `soundness_of_preservation`, a variant
that takes Preservation as an explicit **hypothesis** (no axioms at all), for a
fully axiom-free conditional statement.

## Progress toward eliminating the two axioms

`Canonical.lean` mechanizes the **structural core of the Preservation proof**
(all verified, no `sorry`, standard axioms only):

- `Judg.consequence` — the paper's **Consequence** lemma: every derivation is a
  canonical (non-`M-conseq`) derivation `JudgNC` up to weakening of `R,G,P,Q,e`;
- `Judg.inv_seq` — inversion for `M-seq` via the canonical form;
- `Judg.eval_ctxt` — the **Evaluation Context** lemma: decompose a derivation of
  `E[s]` into a canonical derivation of the redex `s` plus a context effect
  `e_E`, with a rebuild principle for any replacement redex `s'`.

These are exactly the inversion lemmas on which Preservation-for-Redexes,
Yield-Stabilization and the Preservation theorem are built.

**Why the two axioms are not yet removed.** Two genuine obstacles remain — these
are not mechanical transcription:

1. *Preservation* additionally needs the **Prefix** lemma
   (`⊢∅,∅ s : P⇒Q ! e  ⟹  ⊢R,G s : (P';P)⇒(P';Q) ! e`). Prefixing a precondition
   can only *shrink* a lifted mover effect `M(A,·)`, so an action's effect can
   drop below the left-mover threshold `⊑ L`, at which point rule `M-action`'s
   totality side-condition ("if the effect is a left-mover then the action is
   total") must be re-discharged. The paper originally carried a validity
   condition making left-movers total, then commented it out (see the
   struck-through condition (4) in the Validity definition) and folded totality
   into `M-action`. Discharging this rigorously needs either that condition
   reinstated or a more careful argument — a real proof obligation, not a
   transcription gap.

2. *Reduction* is a global **trace-block commutation** argument
   (`Pre`/`Post`/`Finish` decomposition, Diamond / Iterative Diamond /
   Post-Commit Termination). Its entire **mover-theoretic layer** is now
   mechanized — first at the state level in `Reduction.lean`, and then, in
   `ReductionThm.lean`, lifted to the **thread-indexed, trace-composable form**
   the global argument actually consumes: `right_commutes` (validity (1)),
   `left_commutes` (validity (2)), `diamond_commutes` (validity (4)) and the
   structural cases `indep_i_first`/`indep_i_second`. Unlike the state-level
   versions these are indexed by the acting thread, cover *every* step kind
   (structural and store-touching, `I-action` and `I-if`), and discharge the
   `ℝ_i`/`𝕃_i`/`ℕ_i`/`𝔼_i` class side-conditions, so the swaps chain directly.
   `ReductionThm.lean` also proves that **reaching wrong is absorbing**
   (`iwrong_step`), which lets the block argument keep the fatal step *inside*
   its own thread's transaction — so only the OK/structural commutations above
   are ever needed (no wrong step is commuted across threads).

   **Post-Commit Termination is now proved** (`PostCommit.lean`,
   `post_commit_term`): a post-commit thread of a verified state runs to a
   settled state under `↦`, by the paper's size-metric argument. It needs a
   well-founded size metric, which is well-founded *only if atomic functions are
   non-recursive* — the paper's side-condition, which the Lean model's `FnValid`
   had dropped. Rather than mutate the core `Judg`, this is reinstated as an
   explicit `GoodSizing D fs` witness (a size assignment strictly dominating each
   atomic body; it exists iff the atomic call graph is well-founded), passed to
   the lemma alongside `NeverYields` and `CondTotal`. `post_commit_term` depends
   only on `preservation` plus the standard axioms.

   **Iterative Diamond is now proved** (`Assembly.lean`, `iter_diamond`, built on
   the single-step `push_j`): a whole left-mover run of a thread pushes through a
   non-`a` run, so a post-commit termination run can be merged into the main
   trace. Depends only on `propext`.

   With this, **every named lemma of the paper's Reduction proof is mechanized**
   (Right/Left Commutativity, Diamond, Iterative Diamond, Post-Commit
   Termination), plus the phase-generalized commutation, class invariance, and
   tagged-run infrastructure the top-level argument needs.

   What remains is the **top-level trace-block induction** (`(form:b)`/`(form:c)`):
   the transaction bubble that extracts a thread's steps to the front of a run
   (via the two adjacent swaps `right_commutes'` / `left_commutes`),
   first-committer identification, the fatal-step diamond for the single
   wrong-reaching step, and the outer induction that assembles these with
   Post-Commit Termination and Iterative Diamond — a large but now
   fully-equipped combinatorial development.

So the honest status is: the **entire chain is assembled, every logic-level
structural lemma is mechanized, and the mover-theoretic engines of both hard
theorems are proved** (`right_commute_state` for Reduction; Consequence /
inversion / Evaluation Context for Preservation). The two axioms isolate exactly
the two remaining combinatorial developments above, and `#print axioms
soundness` still lists precisely `reduction` and `preservation`.
