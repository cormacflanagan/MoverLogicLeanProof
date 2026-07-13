/-
  Toward the Reduction theorem: the state-level commutativity engine.

  The Reduction theorem (`Π` goes wrong preemptively ⟹ `Π` goes wrong
  non-preemptively) rests on a Lipton-style trace-block commutation argument.
  Its mover-theoretic core is **Right/Left Commutativity** (paper §sec:red-thm):
  a right-mover step of one thread commutes past a step of another thread.

  This file mechanizes that core for the representative and central case — two
  `I-action` steps — deriving the whole state-level diamond (context/phase/list
  bookkeeping and all) from the store-level `right_commute` (validity (1)) and
  the effect-invariance condition (validity (3)).  Fully proved, no `sorry`.

  What remains for the *full* Reduction theorem is documented at the end.
-/
import MoverLogic.Instrumented

namespace MoverLogic

open Effect

/-! ### Effect facts: "not error" is exactly "⊑ N" -/

/-- Every effect except `E` is `⊑ N`. -/
theorem le_N_of_ne_E {e : Effect} (h : e ≠ Effect.E) : e ⊑ Effect.N := by
  cases e <;> first | rfl | exact absurd rfl h

/-- If a sequential composition is non-error, so is its second argument. -/
theorem seq_arg_ne_E {a b : Effect} (h : a ;; b ≠ Effect.E) : b ≠ Effect.E := by
  intro hb; exact h (by rw [hb, seq_E_right])

/-! ### List bookkeeping for independent thread indices -/

/-- Reading a different index after a `set` is unaffected. -/
theorem getElem?_set_ne {α} (l : List α) {i j : Nat} (x : α) (h : i ≠ j) :
    (l.set i x)[j]? = l[j]? := by
  rw [List.getElem?_set]
  simp [h]

/-- Independent `set`s commute. -/
theorem set_comm {α} (l : List α) {i j : Nat} (x y : α) (h : i ≠ j) :
    (l.set i x).set j y = (l.set j y).set i x := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_set, List.length_set]
  by_cases hik : i = k <;> by_cases hjk : j = k <;> simp_all

/-! ### Right Commutativity (state level), action/action case

The paper's Lemma "Right Commutativity" restricted to two `I-action` steps.
A right-mover action step of thread `i` (`M(A_i,i,σ) ⊑ R`) followed by any
non-erroring action step of thread `j ≠ i` can be performed in the opposite
order, reaching the *same* instrumented state.  Everything — the store swap,
the phase updates, and the thread-list bookkeeping — is discharged from
`Valid M` (conditions (1) and (3)).  Fully proved. -/

theorem right_commute_state {M : MoverSpec} {D : BodyEnv} (hV : Valid M)
    {ths : List (Stmt × Phase)} {σ σ' σ'' : Store} {i j : Tid}
    {Ei Ej : Ctx} {Ai Aj : Action} {pi pj : Phase}
    (hij : i ≠ j)
    (hi : ths[i]? = some (Ei.plug (.act Ai), pi))
    (hj : ths[j]? = some (Ej.plug (.act Aj), pj))
    (hmi : M Ai i σ ⊑ Effect.R)
    (hAi : Ai i σ σ') (hnei : pi ;; M Ai i σ ≠ Effect.E)
    (hAj : Aj j σ' σ'') (hnej : pj ;; M Aj j σ' ≠ Effect.E) :
    ∃ σ''' : Store,
      -- left path: i then j
      IStep M D ⟨ths, σ⟩ ⟨ths.set i (Ei.plug .skip, pi ;; M Ai i σ), σ'⟩ ∧
      IStep M D ⟨ths.set i (Ei.plug .skip, pi ;; M Ai i σ), σ'⟩
              ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
                  (Ej.plug .skip, pj ;; M Aj j σ'), σ''⟩ ∧
      -- right path: j then i, reaching the SAME final state
      IStep M D ⟨ths, σ⟩ ⟨ths.set j (Ej.plug .skip, pj ;; M Aj j σ), σ'''⟩ ∧
      IStep M D ⟨ths.set j (Ej.plug .skip, pj ;; M Aj j σ), σ'''⟩
              ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
                  (Ej.plug .skip, pj ;; M Aj j σ'), σ''⟩ := by
  -- effect bounds
  have hmiN : M Ai i σ ⊑ Effect.N := le_trans hmi (by decide)
  have hmjN' : M Aj j σ' ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnej)
  -- store swap from validity (1)
  obtain ⟨σ''', hAjσ, hAiσ'''⟩ :=
    hV.right i j Ai Aj σ σ' σ'' hij hmi hAi hmjN' hAj
  -- effect invariances from validity (3)
  have heffj : M Aj j σ' = M Aj j σ :=
    hV.effect i j Ai Aj σ σ' (M Aj j σ) hij hmiN hAi rfl
  have hmjNσ : M Aj j σ ⊑ Effect.N := heffj ▸ hmjN'
  have heffi : M Ai i σ''' = M Ai i σ :=
    hV.effect j i Aj Ai σ σ''' (M Ai i σ) (Ne.symm hij) hmjNσ hAjσ rfl
  -- non-error transfer for the swapped steps
  have hnejσ : pj ;; M Aj j σ ≠ Effect.E := by rw [← heffj]; exact hnej
  have hneiσ''' : pi ;; M Ai i σ''' ≠ Effect.E := by rw [heffi]; exact hnei
  refine ⟨σ''', ?_, ?_, ?_, ?_⟩
  · -- L1
    exact IStep.mk ths i _ _ σ σ' pi _ hi (IThreadStep.iaction_ok Ei Ai σ σ' pi hAi hnei)
  · -- L2
    have hgetj : (ths.set i (Ei.plug .skip, pi ;; M Ai i σ))[j]? =
        some (Ej.plug (.act Aj), pj) := by rw [getElem?_set_ne _ _ hij]; exact hj
    exact IStep.mk _ j _ _ σ' σ'' pj _ hgetj (IThreadStep.iaction_ok Ej Aj σ' σ'' pj hAj hnej)
  · -- R1
    exact IStep.mk ths j _ _ σ σ''' pj _ hj (IThreadStep.iaction_ok Ej Aj σ σ''' pj hAjσ hnejσ)
  · -- R2, reaching the same final list
    have hgeti : (ths.set j (Ej.plug .skip, pj ;; M Aj j σ))[i]? =
        some (Ei.plug (.act Ai), pi) := by
      rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hi
    have step : IStep M D ⟨ths.set j (Ej.plug .skip, pj ;; M Aj j σ), σ'''⟩
        ⟨(ths.set j (Ej.plug .skip, pj ;; M Aj j σ)).set i
            (Ei.plug .skip, pi ;; M Ai i σ'''), σ''⟩ :=
      IStep.mk (ths.set j (Ej.plug .skip, pj ;; M Aj j σ)) i _ _ σ''' σ'' pi _
        hgeti (IThreadStep.iaction_ok Ei Ai σ''' σ'' pi hAiσ''' hneiσ''')
    have hfin :
        (ths.set j (Ej.plug .skip, pj ;; M Aj j σ)).set i (Ei.plug .skip, pi ;; M Ai i σ''')
        = (ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j (Ej.plug .skip, pj ;; M Aj j σ') := by
      rw [heffi, heffj]
      exact (set_comm ths _ _ hij).symm
    -- coerce `step`'s target list to the shared final list
    have : (⟨(ths.set j (Ej.plug .skip, pj ;; M Aj j σ)).set i
              (Ei.plug .skip, pi ;; M Ai i σ'''), σ''⟩ : IState)
        = ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
              (Ej.plug .skip, pj ;; M Aj j σ'), σ''⟩ := by rw [hfin]
    exact this ▸ step

/-! ### What remains for the full Reduction theorem

`right_commute_state` (with its mirror, Left Commutativity — a symmetric
argument from validity conditions (2) and (4)) is the mover-theoretic engine of
the Reduction theorem.  The full theorem additionally requires:

  * the remaining commutativity cases (`I-if` steps, and steps that do not
    touch the store — which commute unconditionally);
  * the **Diamond** and **Iterative Diamond** lemmas assembling local swaps;
  * **Post-Commit Termination**, which itself invokes the (still axiomatized)
    Preservation theorem;
  * the global **trace-block induction** (`Pre`/`Post`/`Finish` decomposition of
    `→*`, then induction on the number of unfinished post-commit blocks).

That trace-level combinatorial argument is a large separate development; the
top-level `reduction` axiom in `Instrumented.lean` remains, now backed by a
mechanized proof of its central commutativity lemma. -/

end MoverLogic
