# Mover Logic in Lean 4

A self-contained Lean 4 formalization of the program logic from
**"Mover Logic: A Concurrent Program Logic for Reduction and Rely-Guarantee
Reasoning"** (Cormac Flanagan and Stephen N. Freund, ECOOP 2024).

The mechanization surfaced two bugs in the paper's proofs — the Prefix lemma
didn't hold for one case, and the Yield Stabilization argument
applied a rule at the wrong rely/guarantee pair — both documented and corrected
below. A revised version of the paper incorporates the matching fixes.

## Build

```bash
lake build          # ~5s, no Mathlib dependency
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
| `MoverLogic/Prefix.lean` | Lemma Prefix | `compP2` (the paper's `P';P`) and the **Prefix** lemma `Judg.prefix`, proved in its original unrestricted form (see "The Prefix lemma and the upper-bound rule forms" below) |
| `MoverLogic/Reduction.lean` | Lemmas Right / Left Commutativity, Diamond | All state-level action/action commutation lemmas of Reduction — Right, Left, the parallel Diamond, and the store-preserving cases — derived from `Valid M` |
| `MoverLogic/ReductionThm.lean` | §sec:red-thm (Reduction proof) | The **trace-composable** local-commutation layer: thread-indexed steps `→_i`, the state classes `ℝ_i`/`𝕃_i`/`ℕ_i`/`𝔼_i`, the step classifier, *absorbing wrong*, and `right_commutes` / `left_commutes` / `diamond_commutes` / `indep_*` covering **every** step kind (structural + store-touching, `I-action` + `I-if`) with all class side-conditions discharged |
| `MoverLogic/PostCommit.lean` | Lemma lem:post-commit-term | The statement size metric `bodySize`, the model well-formedness the paper assumes (`NeverYields`, `CondTotal`, `GoodSizing` = atomic functions non-recursive), the `progress` engine, and **`post_commit_term`** / **`post_commit_lm`** — a post-commit thread of a verified state runs to a settled state under `↦` |
| `MoverLogic/Assembly.lean` | §sec:red-thm (global argument) | The **complete Reduction proof**: length-indexed merge (`merge_wrongN`), mover-invariance (`mover_invariant`, `active_*_le_L`), the dischargeable wrong-commutation (`left_commutes_w'` + `interfered_branches_ne_E`), transaction extraction (`extract_committer`, `left_decompose`), the outer induction `reorder_core`, and finally **`reduction_proved`** and **`soundness'`** |
| `MoverLogic/Soundness.lean` | Thm "Soundness"      | Not-Wrong for standard states; Soundness-modulo-Preservation |
| `MoverLogic/Instrumented.lean` | §"Overview of Correctness Proof" | The **soundness chain**: instrumented semantics, non-preemptive scheduler, `⊢ Π`, Simulation, `embed` (Reduction and the assembled Soundness are proved in `Assembly.lean`) |
| `MoverLogic/Preservation.lean` | Thm thm:pres + Lemmas lem:yield-stable / lem:ctxt-switch / lem:pres-redex | The **complete Preservation proof**: Yield Stabilization, Context Switch, Preservation for Redexes (fused with the Evaluation Context rebuild), and **`preservation`** / `preservation_star` |
| `MoverLogic/Examples.lean` | Figs. 3, 5, 7 (the examples) | **Worked `Judg` derivations for the paper's examples** against a concrete mover spec and concrete actions (spin lock, the `add()`/`client()` counter, the initial state); see "Worked example derivations" below |

## What is proved

The whole development contains **no `sorry` and no `native_decide`**. Every
result named in this section is machine-checked using **only Lean's standard
axioms** (`propext` / `Classical.choice` / `Quot.sound`; verify with
`#print axioms`). **Both hard theorems — Reduction and Preservation — are now
fully mechanized** (each was previously taken as an axiom), so the development
is **axiom-free**: `#print axioms soundness'` lists exactly the standard
axioms and nothing else.

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

**Proved with no `sorry`, only standard axioms:**
- the instrumented semantics (rules I-*), preemptive `→` and non-preemptive `↦`;
- `IStateValid.not_wrong` — Not-Wrong for instrumented states (Thm not-wrong);
- `simulation` and `simulation_star` — the Simulation theorem and its closure;
- `embed` — a verified standard state embeds into a verified instrumented one;
- **`preservation`** — Theorem thm:pres (the Evaluation-Context / Consequence /
  Preservation-for-Redexes / Yield-Stabilization / Prefix / Context-Switch
  inversion stack; see "The Preservation theorem, mechanized" below), stated
  over the instrumented non-preemptive semantics (where it is *true* — unlike
  step-wise preservation over the raw preemptive semantics, which is false and
  is exactly what Reduction repairs), and `preservation_star`, its `↦*`-closure;
- **`reduction_proved`** — Theorem thm:red, the Reduction theorem itself (see the
  next section);
- `soundness'` — the final assembly.

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
of these lemmas is machine-checked with only the standard axioms (the
post-commit steps invoke the proved `preservation` theorem).

### The Prefix lemma and the upper-bound rule forms

Mechanizing Preservation surfaced a genuine bug in the paper. The **Prefix**
lemma (paper `lem:prefix`) claims

```
∅,∅ ⊢ s : P ⇒ Q ! e     ⟹     R,G ⊢ s : (P';P) ⇒ (P';Q) ! e   for ALL P', R, G.
```

Under the paper's *original* rules — whose effect antecedents were equalities,
e.g. `e = (M(A₁,P);e₁)*;M(A₂,P)` in `M-while` — **this is false**. During
development we machine-checked a counterexample against the original rule
forms (the file predates this repository's rule change and is not retained;
its argument is spelled out below, and a regression `example` in `Prefix.lean`
pins its judgment as derivable under the corrected rules):

- Take `M := λ_ _ _. R` (everything a right-mover), `s := while [I·I] skip` (a
  loop whose test never fails), `P := (a = σ₀)`, and a prefix `P' := (b = σ₁)`
  with `σ₀ ≠ σ₁`.
- The hypothesis holds: `∅,∅ ⊢ while [I·I] skip : P ⇒ P ! R` (loop effect
  `(R;B)*;R = R`, side condition `¬(R ⊑ L)` ✓).
- But `P';P` is **empty** (post-stores of `P'` are `{σ₁}`, pre-stores of `P` are
  `{σ₀}`), so the claimed conclusion is `R,G ⊢ while [I·I] skip : ∅ ⇒ ∅ ! R`.
  Inverting to canonical form forces the loop invariant empty, which collapses
  both lifted movers to the lattice bottom `Y`; the recomputed loop effect is
  then `⊑ L`, contradicting `M-while`'s `¬(e ⊑ L)` guard. No derivation
  exists. ∎

**Root cause.** `post(P';P) ⊆ post P`, so a lifted mover `M(A, P';P)` can only
*shrink* relative to `M(A, P)` — down to `Y` when `P';P` is empty. An
*equality* effect antecedent can therefore never be re-established under a
prefixed precondition, and `M-while`'s recomputed effect can cross below the
`¬(e ⊑ L)` guard. The paper's `M-while` case wrote "Thus …" and never
re-checked either.

**The fix: upper-bound antecedents.** Generalize the effect antecedents of
`M-if` and `M-while` from equalities to upper bounds — the same generalization
`M-action` already carries (`M(A,P) ⊑ e`):

```
M-if:     (M(A₁,P);e₁) ⊔ (M(A₂,P);e₂) ⊑ e
M-while:  M(A₁,P);e₁ ⊑ R                     ← new antecedent
          (M(A₁,P);e₁)* ; M(A₂,P) ⊑ e        ← was =
          ¬(e ⊑ L)                            ← unchanged, on the ASCRIBED e
```

Soundness bookkeeping is preserved because both `M-while` side conditions are
now stated on quantities stable under prefixing:

- `¬(e ⊑ L)` on the *ascribed* effect governs placement — `p;e ≠ E` with
  `p = N` forces `e ⊑ L`, so a loop can never sit post-commit — and the
  ascribed effect is held fixed by Prefix.
- The new `M(A₁,P);e₁ ⊑ R` — *each iteration is a right-mover* — prevents an
  iteration from committing and looping again (the post-commit-divergence
  pattern of the paper's `while(true)` footnote). It is implied by the old
  rule (whose `¬(computed ⊑ L)` forced per-iteration effects into `{Y,B,R}`)
  and it is monotone, hence Prefix-stable. It even *admits* sound programs the
  old rule rejected, such as loops whose iterations commit and then yield
  (`(L Y)*` blocks).

Because `M-conseq` already allowed arbitrary effect weakening `e₁ ⊑ e`, the
`⊑`-form rules derive essentially the same judgments — the change relocates
weakening into the syntax-directed rules, which is exactly what canonical-form
inversion (and hence Prefix) needs.

With these rule forms, the Prefix lemma holds **in its original unrestricted
form** — no hypothesis on `P'` — by pure monotonicity of `;`, `⊔`, `*`, and
`M(A,·)`:

```lean
theorem Judg.prefix (P' R G : Pred2)
    (hD : ∀ f spec body, D f = some (spec, body) → FnValid M D spec body)
    (h : Judg M D botP botP s P Q e) :
    Judg M D R G s (compP2 P' P) (compP2 P' Q) e
```

is **fully proved, no `sorry`, standard axioms only** (`#print axioms
Judg.prefix`). `hD` (valid declaration table) discharges the `M-call-non-atomic`
case, whose non-empty guarantee cannot sit under the empty root guarantee. A
regression `example` in `Prefix.lean` pins the counterexample's judgment as now
derivable, and `Effects.iter_seq_le` / `Effects.exit_le` machine-check the two
finite lattice facts that the paper's loop-unfolding Preservation case needs
under the `⊑`-form rules. The revised paper carries the matching rule
changes, the corrected `M-while` case of the Prefix lemma, and the updated
loop-unfolding case of Preservation for Redexes.

## The Preservation theorem, mechanized

Preservation (Theorem thm:pres) — *verification is preserved by every
non-preemptive instrumented step* — is fully proved as
`MoverLogic.preservation` in `Preservation.lean`, discharging the last axiom.
The proof is the paper's inversion stack:

- **Proof-theoretic core** (`Canonical.lean`, `Prefix.lean`):
  `Judg.consequence` (the **Consequence** lemma), `Judg.inv_seq` (`M-seq`
  inversion), `Judg.eval_ctxt` (the **Evaluation Context** lemma: canonical
  redex + rebuild principle), and `Judg.prefix` (the **Prefix** lemma in its
  original unrestricted form, above).
- **Yield Stabilization** (`yield_stable`) — a parked (yielding) thread's
  judgment is re-typed with the stabilized precondition `yield P R`, keeping
  its effect. Mechanization surfaced a subtlety in the paper's `E[yield]`
  case: the fresh `M-yield` instance must be applied at the *outer* `R,G`
  (where `I ⟹ G` covers the diagonal stabilized precondition), not at the
  redex's conseq-weakened rely/guarantee, whose guarantee need not be
  reflexive — so the proof rebuilds the `M-seq` spine at `R,G` by an inner
  induction on the context. The paper's proof is corrected accordingly.
- **Context Switch** (`ctxt_switch`) — an all-yielding valid state re-anchors
  at the current store with any thread active; the outgoing active thread's
  yielding precondition is published to `G` and flows through compatibility
  into every other thread's rely.
- **Preservation for Redexes** — one case per instrumented step rule, fused
  with the Evaluation Context rebuild inside `preservation_active`. The
  atomic-call case is where `Judg.prefix` fires; the loop-unfolding case is
  where the upper-bound `M-while` (via `iter_seq_le` / `exit_le`) fires; the
  `wrong`-step rules are refuted from the `p;e ≠ E` bookkeeping.

One formalization repair was needed: `IStateValid` quantifies the active
thread index over all of `ℕ`, and with an out-of-range index nothing tied the
sequence-initial store `σ₀` to the current store, making Preservation
unprovable (the paper's rule I-state indexes an actual thread, so this is a
Lean-model artifact, not a paper bug). `IStateValid` now carries the *anchor*
conjunct `Pi.threads[a]? = none → σ₀ = Pi.store` — vacuous for genuine
states and trivially supplied by `embed`.

## Worked example derivations

Where the modules above formalize the *logic* and its *soundness*, `Examples.lean`
puts the logic to work: it exhibits, as concrete `Judg` terms, mover-logic
**derivations for the paper's examples**, showing they satisfy the proof system.
Everything is checked against a *single concrete mover specification* `Mspec` and
*concrete actions*, so the derivations are self-contained — the mover claims of
the paper's variable declarations (a lock acquire is a right-mover `R`, a release
is a left-mover `L`, lock-protected/local accesses are both-movers `B`) are
**derived from `Mspec`, not assumed**. The lock is modelled in one variable with
a `free = -1` / `held = tid` encoding, which makes the classification total.

| Result | Paper | What it shows |
|--------|-------|---------------|
| `spin_lock_loop` | Fig. 5, §8.1 | The paper's *own* worked derivation, verbatim: `while (!cas(l,0,tid)) skip` verifies with effect `(B;B)*;R = R`, side condition `¬(R ⊑ L)` ✓ |
| `spin_lock_def` / `spin_unlock_def` | Fig. 5 | `spin_lock` / `spin_unlock` verify as atomic right- and left-movers (rule `M-def-atomic`) |
| `add_body_atomic` | Fig. 7 | `add()`'s body is a single reducible sequence `R;B;B;B;B;L;B = N` (an `R*[N]L*`), so the function is **atomic** |
| `add_meets_ensures` | Fig. 7 | `add()` meets the paper's exact spec `ensures x == \old(x)+arg ∧ result == x` (rule `M-def-atomic`) |
| `client_body_verifies` / `client_def` | Fig. 7 | the **non-atomic** `client()`: effect `B;N;Y;B;N;B;B;Y = R`, two reducible sequences separated by yields, two `add()` calls via `M-call-atomic`, and `assert even(u)` whose `wrong` branch has an *empty precondition* (rejected by `M-wrong`), all under the disentangled invariant `even(x)` |
| `init_state_valid` | Fig. 7 | `⊢ Σ` for the two-thread initial state `(yield; client()) ‖ (yield; client())` (rule `M-state`), given the paper's standing assumption that `M` is valid |

Each result is machine-checked with only the three standard axioms (verify with
`#print axioms client_body_verifies`, etc.). The `init_state_valid` theorem takes
`Valid Mspec` as an explicit hypothesis: validity is the semantic side-condition
the paper *assumes* about a mover specification (Definition "Validity"), checked
separately for the concrete program actions — the simplified `Mspec` here
classifies *arbitrary* actions by their lock behaviour, so it is not valid in that
full generality, and the assumption is stated rather than proved, exactly as the
paper assumes it.

## Status

**Both hard theorems are fully proved**: Reduction (`reduction_proved`) and
Preservation (`preservation`). The entire soundness chain is assembled, and
`#print axioms soundness'` lists precisely Lean's standard
`propext`/`Classical.choice`/`Quot.sound` — no custom axioms, no `sorry`.

The paper's **examples** (spin lock, the `add()`/`client()` counter, the initial
state) are given explicit machine-checked derivations in `Examples.lean` — see
"Worked example derivations" above.
