/-
  Mover Logic — a Lean 4 formalization of
  "Mover Logic: A Concurrent Program Logic for Reduction and Rely-Guarantee
  Reasoning" (Flanagan & Freund, ECOOP 2024).

  Modules:
    * `MoverLogic.Effects`  — Piece 1: effect algebra + DFA reduction theorem
    * `MoverLogic.Language` — Piece 2: MML syntax and operational semantics
    * `MoverLogic.Specs`    — Piece 3: mover specifications and validity
    * `MoverLogic.Logic`    — Piece 4: the mover-logic proof system
    * `MoverLogic.Soundness`— Piece 5: soundness statement and proofs
    * `MoverLogic.Reduction`, `MoverLogic.ReductionThm`
                            — the Reduction theorem's commutation layer:
                              state-level, then thread-indexed / trace-composable
    * `MoverLogic.PostCommit`— Post-Commit Termination (size metric + progress)
    * `MoverLogic.Examples` — worked `Judg` derivations for the paper's examples
                              (spin lock, the `add()`/`client()` counter, the
                              initial state), against a concrete mover spec
    * `MoverLogic.ValidSpec` — a sync-disciplined mover spec proved *valid*
                              outright (`MspecV_valid : Valid MspecV`, no
                              assumption), plus two unconditional whole-state
                              judgments against it: a lock round-trip and a
                              faithful `x++`-under-lock critical section
                              (`acqRel_state_valid`, `client_state_valid`)
    * `MoverLogic.ValidSpecExamples`
                            — the paper's examples (spin lock, the `add()`/
                              `client()` counter with thread-local `r`/`arg`/
                              `result`, the initial state) re-verified against the
                              *proved-valid* `MspecV`, with **no validity
                              assumption** (`client_state_valid`)
-/
import MoverLogic.Effects
import MoverLogic.Language
import MoverLogic.Specs
import MoverLogic.Logic
import MoverLogic.Canonical
import MoverLogic.Prefix
import MoverLogic.Soundness
import MoverLogic.Instrumented
import MoverLogic.Preservation
import MoverLogic.Reduction
import MoverLogic.ReductionThm
import MoverLogic.PostCommit
import MoverLogic.Assembly
import MoverLogic.Examples
import MoverLogic.ValidSpec
import MoverLogic.ValidSpecExamples
