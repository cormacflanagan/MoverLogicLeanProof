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

/-! ### The commutativity diamond (state level), action/action case

The shared core.  Given two `I-action` steps of threads `i ≠ j` (`i` from `σ`
to `σ'`, then `j` from `σ'` to `σ''`), *any* store swap `σ'''` witnessing that
the two store transitions commute (`Aⱼ j σ σ'''` and `Aᵢ i σ''' σ''`) plus the
bound `M(Aᵢ,i,σ) ⊑ N` yields the full instrumented-state diamond: the phase
updates and thread-list bookkeeping all reconcile, via `Valid M` condition (3).
Right and Left Commutativity below just supply the store swap from validity
condition (1) resp. (2). -/

theorem diamond_core {M : MoverSpec} {D : BodyEnv} (hV : Valid M)
    {ths : List (Stmt × Phase)} {σ σ' σ'' σ''' : Store} {i j : Tid}
    {Ei Ej : Ctx} {Ai Aj : Action} {pi pj : Phase}
    (hij : i ≠ j)
    (hi : ths[i]? = some (Ei.plug (.act Ai), pi))
    (hj : ths[j]? = some (Ej.plug (.act Aj), pj))
    (hmiN : M Ai i σ ⊑ Effect.N)
    (hAi : Ai i σ σ') (hnei : pi ;; M Ai i σ ≠ Effect.E)
    (hAj : Aj j σ' σ'') (hnej : pj ;; M Aj j σ' ≠ Effect.E)
    (hAjσ : Aj j σ σ''') (hAiσ''' : Ai i σ''' σ'') :
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
  have hmjN' : M Aj j σ' ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnej)
  -- effect invariances from validity (3)
  have heffj : M Aj j σ' = M Aj j σ :=
    hV.effect i j Ai Aj σ σ' (M Aj j σ) hij hmiN hAi rfl
  have hmjNσ : M Aj j σ ⊑ Effect.N := heffj ▸ hmjN'
  have heffi : M Ai i σ''' = M Ai i σ :=
    hV.effect j i Aj Ai σ σ''' (M Ai i σ) (Ne.symm hij) hmjNσ hAjσ rfl
  -- non-error transfer for the swapped steps
  have hnejσ : pj ;; M Aj j σ ≠ Effect.E := by rw [← heffj]; exact hnej
  have hneiσ''' : pi ;; M Ai i σ''' ≠ Effect.E := by rw [heffi]; exact hnei
  refine ⟨?_, ?_, ?_, ?_⟩
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
    have : (⟨(ths.set j (Ej.plug .skip, pj ;; M Aj j σ)).set i
              (Ei.plug .skip, pi ;; M Ai i σ'''), σ''⟩ : IState)
        = ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
              (Ej.plug .skip, pj ;; M Aj j σ'), σ''⟩ := by rw [hfin]
    exact this ▸ step

/-- **Right Commutativity** (state level, action/action).  A right-mover action
    step of thread `i` (`M(A_i,i,σ) ⊑ R`) commutes past any non-erroring action
    step of thread `j ≠ i`.  Store swap from validity condition (1). -/
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
      IStep M D ⟨ths, σ⟩ ⟨ths.set i (Ei.plug .skip, pi ;; M Ai i σ), σ'⟩ ∧
      IStep M D ⟨ths.set i (Ei.plug .skip, pi ;; M Ai i σ), σ'⟩
              ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
                  (Ej.plug .skip, pj ;; M Aj j σ'), σ''⟩ ∧
      IStep M D ⟨ths, σ⟩ ⟨ths.set j (Ej.plug .skip, pj ;; M Aj j σ), σ'''⟩ ∧
      IStep M D ⟨ths.set j (Ej.plug .skip, pj ;; M Aj j σ), σ'''⟩
              ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
                  (Ej.plug .skip, pj ;; M Aj j σ'), σ''⟩ := by
  have hmiN : M Ai i σ ⊑ Effect.N := le_trans hmi (by decide)
  have hmjN' : M Aj j σ' ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnej)
  obtain ⟨σ''', hAjσ, hAiσ'''⟩ := hV.right i j Ai Aj σ σ' σ'' hij hmi hAi hmjN' hAj
  exact ⟨σ''', diamond_core hV hij hi hj hmiN hAi hnei hAj hnej hAjσ hAiσ'''⟩

/-- **Left Commutativity** (state level, action/action).  A left-mover action
    step of thread `j` (`M(A_j,j,σ') ⊑ L`), taken *after* a non-erroring action
    step of thread `i ≠ j`, commutes to *before* it.  Store swap from validity
    condition (2).  Same diamond as Right Commutativity, different witness. -/
theorem left_commute_state {M : MoverSpec} {D : BodyEnv} (hV : Valid M)
    {ths : List (Stmt × Phase)} {σ σ' σ'' : Store} {i j : Tid}
    {Ei Ej : Ctx} {Ai Aj : Action} {pi pj : Phase}
    (hij : i ≠ j)
    (hi : ths[i]? = some (Ei.plug (.act Ai), pi))
    (hj : ths[j]? = some (Ej.plug (.act Aj), pj))
    (hmj : M Aj j σ' ⊑ Effect.L)
    (hAi : Ai i σ σ') (hnei : pi ;; M Ai i σ ≠ Effect.E)
    (hAj : Aj j σ' σ'') (hnej : pj ;; M Aj j σ' ≠ Effect.E) :
    ∃ σ''' : Store,
      IStep M D ⟨ths, σ⟩ ⟨ths.set i (Ei.plug .skip, pi ;; M Ai i σ), σ'⟩ ∧
      IStep M D ⟨ths.set i (Ei.plug .skip, pi ;; M Ai i σ), σ'⟩
              ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
                  (Ej.plug .skip, pj ;; M Aj j σ'), σ''⟩ ∧
      IStep M D ⟨ths, σ⟩ ⟨ths.set j (Ej.plug .skip, pj ;; M Aj j σ), σ'''⟩ ∧
      IStep M D ⟨ths.set j (Ej.plug .skip, pj ;; M Aj j σ), σ'''⟩
              ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
                  (Ej.plug .skip, pj ;; M Aj j σ'), σ''⟩ := by
  have hmiN : M Ai i σ ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnei)
  obtain ⟨σ''', hAjσ, hAiσ'''⟩ := hV.left i j Ai Aj σ σ' σ'' hij hmiN hAi hmj hAj
  exact ⟨σ''', diamond_core hV hij hi hj hmiN hAi hnei hAj hnej hAjσ hAiσ'''⟩

/-! ### Independent (store-preserving) step commutation

The commutativity cases the paper dismisses as "similar": when thread `i`'s step
does not modify the store (`I-seq`, `I-yield`, `I-while`, `I-call`), it commutes
with *any* step of thread `j ≠ i` with no mover conditions at all.  We take the
"replay `i` from the other store" fact as a hypothesis — it holds trivially for
those four rules, whose premises never mention the store. -/

theorem indep_commute {M : MoverSpec} {D : BodyEnv} {i j : Tid}
    (hij : i ≠ j) {ths : List (Stmt × Phase)} {σ σj : Store}
    {si si' sj sj' : Stmt} {pi pi' pj pj' : Phase}
    (hi : ths[i]? = some (si, pi)) (hj : ths[j]? = some (sj, pj))
    (istep_i : IThreadStep M D i si σ pi si' σ pi')       -- i from σ, store-preserving
    (replay_i : IThreadStep M D i si σj pi si' σj pi')    -- i replayed from σj
    (jstep : IThreadStep M D j sj σ pj sj' σj pj') :      -- j from σ to σj
    IStep M D ⟨ths, σ⟩ ⟨ths.set i (si', pi'), σ⟩ ∧
    IStep M D ⟨ths.set i (si', pi'), σ⟩
            ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩ ∧
    IStep M D ⟨ths, σ⟩ ⟨ths.set j (sj', pj'), σj⟩ ∧
    IStep M D ⟨ths.set j (sj', pj'), σj⟩
            ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IStep.mk ths i _ _ σ σ pi _ hi istep_i
  · have hgetj : (ths.set i (si', pi'))[j]? = some (sj, pj) := by
      rw [getElem?_set_ne _ _ hij]; exact hj
    exact IStep.mk _ j _ _ σ σj pj _ hgetj jstep
  · exact IStep.mk ths j _ _ σ σj pj _ hj jstep
  · have hgeti : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
      rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hi
    have step : IStep M D ⟨ths.set j (sj', pj'), σj⟩
        ⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ :=
      IStep.mk (ths.set j (sj', pj')) i _ _ σj σj pi _ hgeti replay_i
    have hcomm : (⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ : IState)
        = ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩ := by
      rw [set_comm ths _ _ (Ne.symm hij)]
    exact hcomm ▸ step

/-- Composing a phase-`N` post-commit thread with a left-mover keeps it `≠ E`. -/
theorem N_seq_ne_E_of_le_L {e : Effect} (h : e ⊑ Effect.L) : Effect.N ;; e ≠ Effect.E := by
  cases e <;> revert h <;> decide

/-! ### The Diamond lemma (state level), action/action case

The paper's Lemma "Diamond": when thread `j` is in its post-commit phase `N`
(`Π ∈ CL_j`) and takes a left-mover step, two steps out of the *same* state `Π`
— one by `i`, one by `j ≠ i` — reconverge.  This is the confluence property used
to merge the post-commit termination trace into the main trace in the Reduction
theorem.  Store swap from validity condition (4). -/

theorem diamond_parallel {M : MoverSpec} {D : BodyEnv} (hV : Valid M)
    {ths : List (Stmt × Phase)} {σ σ' σ'' : Store} {i j : Tid}
    {Ei Ej : Ctx} {Ai Aj : Action} {pi : Phase}
    (hij : i ≠ j)
    (hi : ths[i]? = some (Ei.plug (.act Ai), pi))
    (hj : ths[j]? = some (Ej.plug (.act Aj), Effect.N))
    (hmiN : M Ai i σ ⊑ Effect.N)
    (hAi : Ai i σ σ') (hnei : pi ;; M Ai i σ ≠ Effect.E)
    (hmjL : M Aj j σ ⊑ Effect.L)
    (hAj : Aj j σ σ'') :
    ∃ σ''' : Store,
      -- i then j
      IStep M D ⟨ths, σ⟩ ⟨ths.set i (Ei.plug .skip, pi ;; M Ai i σ), σ'⟩ ∧
      IStep M D ⟨ths.set i (Ei.plug .skip, pi ;; M Ai i σ), σ'⟩
              ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
                  (Ej.plug .skip, Effect.N ;; M Aj j σ), σ'''⟩ ∧
      -- j then i, reconverging
      IStep M D ⟨ths, σ⟩ ⟨ths.set j (Ej.plug .skip, Effect.N ;; M Aj j σ), σ''⟩ ∧
      IStep M D ⟨ths.set j (Ej.plug .skip, Effect.N ;; M Aj j σ), σ''⟩
              ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
                  (Ej.plug .skip, Effect.N ;; M Aj j σ), σ'''⟩ := by
  have hmjN : M Aj j σ ⊑ Effect.N := le_trans hmjL (by decide)
  have hnej : Effect.N ;; M Aj j σ ≠ Effect.E := N_seq_ne_E_of_le_L hmjL
  -- store swap from validity (4)
  obtain ⟨σ''', hAjσ', hAiσ''⟩ := hV.nonblock i j Ai Aj σ σ' σ'' hij hmiN hAi hmjL hAj
  -- effect invariances from validity (3)
  have heffj : M Aj j σ' = M Aj j σ :=
    hV.effect i j Ai Aj σ σ' (M Aj j σ) hij hmiN hAi rfl
  have heffi : M Ai i σ'' = M Ai i σ :=
    hV.effect j i Aj Ai σ σ'' (M Ai i σ) (Ne.symm hij) hmjN hAj rfl
  refine ⟨σ''', ?_, ?_, ?_, ?_⟩
  · -- i step
    exact IStep.mk ths i _ _ σ σ' pi _ hi (IThreadStep.iaction_ok Ei Ai σ σ' pi hAi hnei)
  · -- i-then-j
    have hgetj : (ths.set i (Ei.plug .skip, pi ;; M Ai i σ))[j]? =
        some (Ej.plug (.act Aj), Effect.N) := by rw [getElem?_set_ne _ _ hij]; exact hj
    have hnej' : Effect.N ;; M Aj j σ' ≠ Effect.E := by rw [heffj]; exact hnej
    have step : IStep M D ⟨ths.set i (Ei.plug .skip, pi ;; M Ai i σ), σ'⟩
        ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
            (Ej.plug .skip, Effect.N ;; M Aj j σ'), σ'''⟩ :=
      IStep.mk _ j _ _ σ' σ''' Effect.N _ hgetj
        (IThreadStep.iaction_ok Ej Aj σ' σ''' Effect.N hAjσ' hnej')
    have : (⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
              (Ej.plug .skip, Effect.N ;; M Aj j σ'), σ'''⟩ : IState)
        = ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
              (Ej.plug .skip, Effect.N ;; M Aj j σ), σ'''⟩ := by rw [heffj]
    exact this ▸ step
  · -- j step
    exact IStep.mk ths j _ _ σ σ'' Effect.N _ hj (IThreadStep.iaction_ok Ej Aj σ σ'' Effect.N hAj hnej)
  · -- j-then-i, reconverging
    have hgeti : (ths.set j (Ej.plug .skip, Effect.N ;; M Aj j σ))[i]? =
        some (Ei.plug (.act Ai), pi) := by
      rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hi
    have hnei'' : pi ;; M Ai i σ'' ≠ Effect.E := by rw [heffi]; exact hnei
    have step : IStep M D ⟨ths.set j (Ej.plug .skip, Effect.N ;; M Aj j σ), σ''⟩
        ⟨(ths.set j (Ej.plug .skip, Effect.N ;; M Aj j σ)).set i
            (Ei.plug .skip, pi ;; M Ai i σ''), σ'''⟩ :=
      IStep.mk _ i _ _ σ'' σ''' pi _ hgeti
        (IThreadStep.iaction_ok Ei Ai σ'' σ''' pi hAiσ'' hnei'')
    have hfin :
        (ths.set j (Ej.plug .skip, Effect.N ;; M Aj j σ)).set i (Ei.plug .skip, pi ;; M Ai i σ'')
        = (ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j (Ej.plug .skip, Effect.N ;; M Aj j σ) := by
      rw [heffi]; exact (set_comm ths _ _ hij).symm
    have : (⟨(ths.set j (Ej.plug .skip, Effect.N ;; M Aj j σ)).set i
              (Ei.plug .skip, pi ;; M Ai i σ''), σ'''⟩ : IState)
        = ⟨(ths.set i (Ei.plug .skip, pi ;; M Ai i σ)).set j
              (Ej.plug .skip, Effect.N ;; M Aj j σ), σ'''⟩ := by rw [hfin]
    exact this ▸ step

/-! ### What remains for the full Reduction theorem

The complete local-commutation toolkit of the Reduction proof is now mechanized
for the action/action cases (the store-touching ones), all from `Valid M`:

  * `right_commute_state` — Right Commutativity (validity (1));
  * `left_commute_state`  — Left Commutativity  (validity (2));
  * `diamond_parallel`    — the Diamond lemma    (validity (4));
  * `indep_commute`       — the store-preserving cases (no validity needed).

What remains for the full theorem is the surrounding structure, which is
combinatorial rather than mover-theoretic:

  * the `I-if` variants of the commutation cases (identical in spirit to the
    `I-action` cases, since a conditional action is just a store update);
  * **Iterative Diamond** (iterating `diamond_parallel` along a left-mover run);
  * **Post-Commit Termination**, which invokes the (still axiomatized)
    Preservation theorem;
  * the global **trace-block induction**: decompose any `→*` run as
    `Post*; Pre*`, then induct on the number of unfinished post-commit blocks.

That trace-level argument is a large separate development; the top-level
`reduction` axiom in `Instrumented.lean` remains, now backed by mechanized
proofs of all of its local commutativity lemmas. -/

end MoverLogic
