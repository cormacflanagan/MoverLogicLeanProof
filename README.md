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
