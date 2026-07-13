/-
  Piece 5 — the Soundness theorem.

  The paper's central result (Theorem "Soundness"):

        if  ⊢ Σ  then  Σ  does not go wrong.

  A *complete* mechanization of this theorem requires the paper's entire
  metatheory: an instrumented semantics, a non-preemptive scheduler, the
  Simulation theorem, the Reduction theorem, and a Preservation argument (with
  the Right/Left-Commutativity, Diamond, Iterative-Diamond, Yield-Stabilization,
  Prefix and Context-Switch lemmas).  That is a large development; here we give
  the parts that stand on their own and factor the rest through an explicit,
  clearly-labelled Preservation hypothesis, so that `#print axioms` never hides
  anything.

  What is proved *unconditionally* here:
    * `verified_not_wrong` — a verified state is not *currently* wrong.  This is
      the base case of soundness and the paper's "Verified States Are Not Wrong"
      property, proved from rule M-wrong via context inversion.

  What is proved *modulo Preservation*:
    * `soundness_of_preservation` — given that verification is preserved along
      reduced executions (the paper's Preservation theorem, whose proof rests on
      the Reduction theorem mechanized in `Effects.lean`), a verified state does
      not go wrong.  The induction that combines Preservation with the base case
      is fully mechanized.
-/
import MoverLogic.Effects
import MoverLogic.Language
import MoverLogic.Specs
import MoverLogic.Logic

namespace MoverLogic

variable {M : MoverSpec} {D : Decls}

/-! ### Verified states are not currently wrong -/

/-- **Verified states are not (immediately) wrong.**  If `⊢ Σ` then no thread of
    `Σ` is about to execute `wrong`.  Fully mechanized. -/
theorem verified_not_wrong {st : State} (h : StateValid M D st) : ¬ StateWrong st := by
  rintro ⟨s, hmem, E, rfl⟩
  obtain ⟨R, G, _hfns, _hvalid, _hrefl, hthreads, _hcompat⟩ := h
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have hidx : st.threads[i]? = some (E.plug .wrong) := by
    rw [List.getElem?_eq_getElem hi, hget]
  obtain ⟨P, Q, e, hJ, _hne, _hQG, _hy, hP⟩ := hthreads i _ hidx
  exact hJ.wrong_empty E rfl i st.store st.store hP

/-! ### Soundness modulo Preservation

`StateSteps` preserves verification provided each single step does — the
induction is mechanized; the single-step premise is the paper's Preservation
theorem. -/

/-- Verification is preserved along any run of the state relation, given that it
    is preserved by a single step (`hpres`).  The semantics uses the body
    environment `D.bodies` underlying the declaration table `D`. -/
theorem StateValid.preserved_along
    (hpres : ∀ a b, StateValid M D a → StateStep D.bodies a b → StateValid M D b)
    {a b : State} (hab : StateSteps D.bodies a b) : StateValid M D a → StateValid M D b := by
  induction hab with
  | refl => exact fun h => h
  | step hst _ ih => exact fun h => ih (hpres _ _ h hst)

/-- **Soundness (modulo Preservation).**  If verification is preserved by each
    step of the operational semantics (the paper's Preservation theorem, itself
    a consequence of the Reduction theorem mechanized in `Effects.lean`), then a
    verified state never goes wrong.  The reduction of Soundness to Preservation
    plus the base case is fully mechanized here. -/
theorem soundness_of_preservation
    (hpres : ∀ a b, StateValid M D a → StateStep D.bodies a b → StateValid M D b)
    {st : State} (h : StateValid M D st) : ¬ GoesWrong D.bodies st := by
  rintro ⟨st', hsteps, hwrong⟩
  exact verified_not_wrong (StateValid.preserved_along hpres hsteps h) hwrong

/-! ### Link to the Reduction theorem (Piece 1)

Every verified thread carries a *non-error* composite effect `e ≠ E`.  By the
mechanized reduction theorem `reducible_iff_seqFold_ne_E`, any sequence of
per-action effects that composes to such an `e` is accepted by the reduction
DFA — i.e. it genuinely decomposes into reducible blocks `R*[N]L*` separated by
yields.  This is the formal bridge between the logic's effect discipline and the
reduction argument underpinning soundness. -/

/-- In a verified state, each thread's effect is non-error, and therefore any
    underlying effect sequence realizing it is DFA-accepted (reducible). -/
theorem thread_effect_reducible {st : State}
    (h : StateValid M D st) {i : Tid} {s : Stmt}
    (hidx : st.threads[i]? = some s) :
    ∃ R G P Q e, Judg M D R G s P Q e ∧ e ≠ Effect.E ∧
      (∀ es : List Effect, Effect.seqFold es = e → Effect.accepts es) := by
  obtain ⟨R, G, _hfns, _hvalid, _hrefl, hthreads, _hcompat⟩ := h
  obtain ⟨P, Q, e, hJ, hne, _hQG, _hy, _hP⟩ := hthreads i s hidx
  exact ⟨R, G, P, Q, e, hJ, hne, fun es hes =>
    (Effect.reducible_iff_seqFold_ne_E es).2 (by rw [hes]; exact hne)⟩

end MoverLogic
