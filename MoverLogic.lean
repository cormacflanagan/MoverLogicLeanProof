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
-/
import MoverLogic.Effects
import MoverLogic.Language
import MoverLogic.Specs
import MoverLogic.Logic
import MoverLogic.Soundness
import MoverLogic.Instrumented
