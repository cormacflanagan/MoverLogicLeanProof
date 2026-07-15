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

Built in five pieces (Effects → Language → Specs → Logic → Soundness), plus the
soundness chain (`Instrumented.lean`) and the fully-mechanized **Reduction
theorem** (`Reduction` → `ReductionThm` → `PostCommit` → `Assembly`).

| File | Paper section | Contents |
|------|---------------|----------|
| `MoverLogic/Effects.lean`   | §"Effects"           | The 6-point effect lattice `Y,B,R,L,N,E`; order `⊑`, join `⊔`, sequential composition `;;`, closure `*`; the **reduction / DFA theorem** |
| `MoverLogic/Language.lean`  | §"Mover Logic Language" | Stores, actions, statements, evaluation contexts, per-thread + whole-state operational semantics, "goes wrong" |
| `MoverLogic/Specs.lean`     | §"Mover Specifications" | Mover specs `M`, the lifted `M(A,P)` as a genuine least-upper-bound, the four **Validity** conditions |
| `MoverLogic/Logic.lean`     | Figs. "proof rules"  | Predicate operators; the judgment `R,G ⊢ s : P ⇒ Q ! e` with every rule; function + state judgments |
| `MoverLogic/Canonical.lean` | Lemmas Consequence / Evaluation Context | Canonical (non-`M-conseq`) form, `M-seq` inversion, and the Evaluation Context lemma — the structural core of Preservation |
| `MoverLogic/Reduction.lean` | Lemmas Right / Left Commutativity, Diamond | All state-level action/action commutation lemmas of Reduction — Right, Left, the parallel Diamond, and the store-preserving cases — derived from `Valid M` |
| `MoverLogic/ReductionThm.lean` | §sec:red-thm (Reduction proof) | The **trace-composable** local-commutation layer: thread-indexed steps `→_i`, the state classes `ℝ_i`/`𝕃_i`/`ℕ_i`/`𝔼_i`, the step classifier, *absorbing wrong*, and `right_commutes` / `left_commutes` / `diamond_commutes` / `indep_*` covering **every** step kind (structural + store-touching, `I-action` + `I-if`) with all class side-conditions discharged |
| `MoverLogic/PostCommit.lean` | Lemma lem:post-commit-term | The statement size metric `bodySize`, the model well-formedness the paper assumes (`NeverYields`, `CondTotal`, `GoodSizing` = atomic functions non-recursive), the `progress` engine, and **`post_commit_term`** / **`post_commit_lm`** — a post-commit thread of a verified state runs to a settled state under `↦` |
| `MoverLogic/Assembly.lean` | §sec:red-thm (global argument) | The **complete Reduction proof**: length-indexed merge (`merge_wrongN`), mover-invariance (`mover_invariant`, `active_*_le_L`), the dischargeable wrong-commutation (`left_commutes_w'` + `interfered_branches_ne_E`), transaction extraction (`extract_committer`, `left_decompose`), the outer induction `reorder_core`, and finally **`reduction_proved`** and **`soundness'`** |
| `MoverLogic/Soundness.lean` | Thm "Soundness"      | Not-Wrong for standard states; Soundness-modulo-Preservation |
| `MoverLogic/Instrumented.lean` | §"Overview of Correctness Proof" | The **soundness chain**: instrumented semantics, non-preemptive scheduler, `⊢ Π`, Simulation, `embed`, and the `preservation` axiom (Reduction and the assembled Soundness are proved in `Assembly.lean`) |

## What is proved

The whole development contains **no `sorry` and no `native_decide`**. Every
result named in this section is machine-checked using **only Lean's standard
axioms** (`propext` / `Classical.choice` / `Quot.sound`; verify with
`#print axioms`). **The Reduction theorem is now fully mechanized** (it was
previously taken as an axiom), so the *only* custom axiom left in the soundness
chain is `preservation`; `#print axioms soundness'` lists exactly `preservation`
plus the standard axioms and nothing else.

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

## The full soundness chain

The paper's entire proof structure (§"Overview of Correctness Proof") is
mechanized across `Instrumented.lean` (the semantics + Simulation + embedding)
and `Assembly.lean` (the Reduction theorem + the final assembly). The top-level
theorem is

```lean
theorem soundness' (hwf : WF M D) (h : StateValid M D st) : ¬ GoesWrong D.bodies st
```

assembled exactly as in the paper: embed `Σ` into a verified, all-yielding
instrumented `Π`; run Simulation to a wrong preemptive `Π'`; apply **Reduction**
(`reduction_proved`) to reach a wrong non-preemptive `Π''`; apply Preservation to
get `⊢ Π''`; contradict Not-Wrong. The `WF M D` hypothesis bundles the model
well-formedness the paper assumes (`NeverYields`, `CondTotal`, `NeverError`, and
non-recursive atomic functions via `GoodSizing`).

**Proved with no `sorry`, only standard axioms (+ `preservation`):**
- the instrumented semantics (rules I-*), preemptive `→` and non-preemptive `↦`;
- `IStateValid.not_wrong` — Not-Wrong for instrumented states (Thm not-wrong);
- `simulation` and `simulation_star` — the Simulation theorem and its closure;
- `embed` — a verified standard state embeds into a verified instrumented one;
- `preservation_star` — Preservation lifted along `↦*`;
- **`reduction_proved`** — Theorem thm:red, the Reduction theorem itself (see the
  next section);
- `soundness'` — the final assembly.

**The one remaining axiom** (`#print axioms soundness'` shows exactly this, plus
Lean's standard `propext`/`Classical.choice`/`Quot.sound`):
- `preservation` — Theorem thm:pres (proof: the Evaluation-Context / Consequence
  / Preservation-for-Redexes / Yield-Stabilization / Prefix / Context-Switch
  inversion stack), stated faithfully over the instrumented non-preemptive
  semantics (where it is *true* — unlike step-wise preservation over the raw
  preemptive semantics, which is false and is exactly what Reduction repairs).

`Soundness.lean` additionally provides `soundness_of_preservation`, a variant
that takes Preservation as an explicit **hypothesis** (no axioms at all), for a
fully axiom-free conditional statement.

## The Reduction theorem, mechanized

Reduction (Theorem thm:red) — *a verified all-yielding state that goes wrong
preemptively also goes wrong non-preemptively* — is now **fully proved** as
`reduction_proved`, discharging what was previously an axiom. The proof follows
the paper (§sec:red-thm) and is built bottom-up:

- **Mover-theoretic layer** (`Reduction.lean`, `ReductionThm.lean`). The
  state-level action/action commutations, lifted to the thread-indexed,
  trace-composable form the global argument consumes: `right_commutes`
  (validity 1), `left_commutes` (validity 2), `diamond_commutes` (validity 4),
  the structural cases, and their wrong-case variants — covering *every* step
  kind (structural and store-touching, `I-action` and `I-if`) with the
  `ℝ_i`/`𝕃_i`/`ℕ_i`/`𝔼_i` class side-conditions discharged. Plus *reaching wrong
  is absorbing*.

- **Post-Commit Termination** (`PostCommit.lean`, `post_commit_term` /
  `post_commit_lm`). A post-commit thread of a verified state runs to a settled
  state under `↦`, by the paper's size-metric argument. Well-foundedness needs
  atomic functions non-recursive — the paper's side-condition, reinstated as an
  explicit `GoodSizing D fs` witness (rather than mutating the core `Judg`),
  alongside `NeverYields` and `CondTotal` (bundled as `WF M D`).

- **Iterative Diamond & length-indexed merge** (`Assembly.lean`, `iter_diamond`
  / `iter_diamondN` / `merge_wrongN`). A whole left-mover run pushes through a
  non-`a` run; the length-indexed variant makes the merged residual's length
  bounded, so the outer induction is well-founded.

- **Mover invariance & the committer-is-fatal case** (`Assembly.lean`). By
  validity (3), a non-`a` step cannot change `a`'s action effects
  (`mover_invariant`); a committed thread's redex is a left-mover
  (`active_action_le_L` / `active_branches_le_L`, via `Judg.eval_ctxt`); and a
  verified state's active thread cannot step to wrong (`valid_no_wrong_step`,
  from `preservation`). Together these discharge the wrong-case left-commutation
  side condition (`left_commutes_w'` + `interfered_branches_ne_E`) and rule out a
  committer being the fatal thread (`committed_run_cannot_wrong`) — following the
  paper's *commute-don't-refute* handling of the fatal step.

- **Transaction extraction & the outer induction** (`Assembly.lean`,
  `extract_committer` / `left_decompose` / `reorder_core`). The outer induction
  uses the measure `2·n + w` (run length `n`, with `w ∈ {0,1}` distinguishing an
  all-yielding start from a single post-commit-active thread) — capturing the
  paper's unfinished-block count without an explicit `Post*/Pre*` block datatype.
  `w = 0` pulls the first committer's transaction to the front non-preemptively;
  `w = 1` pulls a post-commit thread's left-mover transaction, then either
  settles it (recurse from an all-yielding state) or finishes and merges it
  (`post_commit_lm` + `merge_wrongN`).

`reduction_proved` feeds a preemptive-wrong run into `reorder_core` (`ISteps.toN`
supplies the length), and `soundness'` re-assembles Soundness on top. Every one
of these lemmas is machine-checked with only the standard axioms, or
`preservation` for the post-commit steps.

### What is left: the Preservation axiom

The single remaining axiom is `preservation`. Its **structural core is
mechanized** in `Canonical.lean` (all verified, no `sorry`, standard axioms):

- `Judg.consequence` — the **Consequence** lemma (every derivation is a canonical
  `JudgNC` up to weakening);
- `Judg.inv_seq` — inversion for `M-seq` via the canonical form;
- `Judg.eval_ctxt` — the **Evaluation Context** lemma (decompose a derivation of
  `E[s]` into the redex `s` plus a context effect, with a rebuild principle).

What remains for Preservation is the **Prefix** lemma
(`⊢∅,∅ s : P⇒Q ! e ⟹ ⊢R,G s : (P';P)⇒(P';Q) ! e`): prefixing a precondition can
only *shrink* a lifted mover effect, so an action's effect can drop below the
left-mover threshold, at which point rule `M-action`'s totality side-condition
must be re-discharged — a real proof obligation (the paper originally carried a
validity condition making left-movers total, then folded totality into
`M-action`). Discharging it rigorously is the remaining mechanization work.

So the honest status: **the Reduction theorem is fully proved**, the entire
soundness chain is assembled, and `#print axioms soundness'` lists precisely
`preservation` (plus Lean's standard `propext`/`Classical.choice`/`Quot.sound`).
