/-
  The Reduction Theorem (Theorem thm:red): the trace-composable
  local-commutation layer.

  Following the paper's proof structure (§sec:red-thm), this file provides:

    * indexed preemptive steps `→_i` and the state classes `ℝ_i`, `𝕃_i`,
      `ℕ_i`, `𝔼_i`;
    * the eight structural properties of evaluation;
    * clean thread-indexed commutation lemmas (Right, Left, Diamond,
      Independent), lifting the state-level engines of `Reduction.lean` and
      covering the "other thread goes wrong" cases.

  The theorem is completed downstream: Post-Commit Termination in
  `PostCommit.lean` (which genuinely invokes the `preservation` theorem of
  `Preservation.lean`, exactly as in the paper) and the global trace-block
  argument in `Assembly.lean`, culminating in `reduction_proved` and the
  re-assembled `soundness'`.
-/
import MoverLogic.Reduction

namespace MoverLogic

open Effect

/-! ### Thread-indexed preemptive steps `→_i`

`IStepI M D i Π Π'` is a preemptive whole-state step whose active thread is
exactly `i`.  It is `IStep` with the acting thread exposed. -/

inductive IStepI (M : MoverSpec) (D : BodyEnv) (i : Tid) : IState → IState → Prop where
  | mk (ths : List (Stmt × Phase)) (s s' : Stmt) (σ σ' : Store) (p p' : Phase)
      (hget : ths[i]? = some (s, p))
      (hstep : IThreadStep M D i s σ p s' σ' p') :
      IStepI M D i ⟨ths, σ⟩ ⟨ths.set i (s', p'), σ'⟩

/-- A preemptive step is an indexed step for some thread. -/
theorem IStep.exists_tid {M D} {a b : IState} (h : IStep M D a b) :
    ∃ i, IStepI M D i a b := by
  cases h with
  | mk ths t s s' σ σ' p p' hget hstep => exact ⟨t, .mk ths s s' σ σ' p p' hget hstep⟩

/-- An indexed step is a preemptive step. -/
theorem IStepI.toIStep {M D i} {a b : IState} (h : IStepI M D i a b) : IStep M D a b := by
  cases h with
  | mk ths s s' σ σ' p p' hget hstep => exact .mk ths i s s' σ σ' p p' hget hstep

/-! ### Classification of a per-thread step

Every `IThreadStep` is exactly one of:
  * **structural** — store-independent and store-preserving (`I-seq`, `I-yield`,
    `I-while`, `I-call`): the same step fires from any store;
  * **store-touching (ok)** — `I-action`/`I-if` firing an action `A`, updating
    the store and composing the phase with `M(A,t,σ)` (`≠ E`);
  * **wrong** — `I-action`/`I-if` composing to the error effect `E`, leaving the
    store fixed and rewriting the redex to `wrong`. -/

theorem ithreadstep_classify {M D t} {s : Stmt} {σ : Store} {p : Phase}
    {s' : Stmt} {σ' : Store} {p' : Phase}
    (h : IThreadStep M D t s σ p s' σ' p') :
    (σ' = σ ∧ ∀ σx, IThreadStep M D t s σx p s' σx p') ∨
    (∃ A : Action, ActionLike M D t s s' A p ∧ A t σ σ' ∧
        p' = p ;; M A t σ ∧ p ;; M A t σ ≠ Effect.E) ∨
    (IsWrong s' ∧ σ' = σ ∧ p' = p ∧
      -- the erroring action `A`, its error effect, and a rule to *re-fire* the
      -- wrong step from any store `τ` where the effect is still `E` (following
      -- the paper's I-if error case: the branch witness transports via validity)
      ((∃ A : Action, p ;; M A t σ = Effect.E ∧
          ∀ τ, p ;; M A t τ = Effect.E → IThreadStep M D t s τ p s' τ p) ∨
       (∃ (A : Action) (σ0 : Store), A t σ σ0 ∧ p ;; M A t σ = Effect.E ∧
          ∀ τ τ', A t τ τ' → p ;; M A t τ = Effect.E → IThreadStep M D t s τ p s' τ p))) := by
  cases h with
  | iseq E s0 σ p => exact Or.inl ⟨rfl, fun σx => .iseq E s0 σx p⟩
  | iyield E σ p => exact Or.inl ⟨rfl, fun σx => .iyield E σx p⟩
  | iwhile E C s0 σ p => exact Or.inl ⟨rfl, fun σx => .iwhile E C s0 σx p⟩
  | icall E f s0 σ p hbody => exact Or.inl ⟨rfl, fun σx => .icall E f s0 σx p hbody⟩
  | iaction_ok E A σ σ' p hA hne =>
      exact Or.inr (Or.inl ⟨A, actionLike_action, hA, rfl, hne⟩)
  | iif_ok_T E C s1 s2 σ σ' p hA hne =>
      exact Or.inr (Or.inl ⟨C.tru, actionLike_ite_tru, hA, rfl, hne⟩)
  | iif_ok_F E C s1 s2 σ σ' p hA hne =>
      exact Or.inr (Or.inl ⟨C.fls, actionLike_ite_fls, hA, rfl, hne⟩)
  | iaction_wrong E A σ p hp =>
      exact Or.inr (Or.inr ⟨⟨E, rfl⟩, rfl, rfl,
        Or.inl ⟨A, hp, fun τ hτ => IThreadStep.iaction_wrong E A τ p hτ⟩⟩)
  | iif_wrong_T E C s1 s2 σ σ' p hA hp =>
      exact Or.inr (Or.inr ⟨⟨E, rfl⟩, rfl, rfl,
        Or.inr ⟨C.tru, σ', hA, hp, fun τ τ' hA' hτ => IThreadStep.iif_wrong_T E C s1 s2 τ τ' p hA' hτ⟩⟩)
  | iif_wrong_F E C s1 s2 σ σ' p hA hp =>
      exact Or.inr (Or.inr ⟨⟨E, rfl⟩, rfl, rfl,
        Or.inr ⟨C.fls, σ', hA, hp, fun τ τ' hA' hτ => IThreadStep.iif_wrong_F E C s1 s2 τ τ' p hA' hτ⟩⟩)

/-! ### The state classes `ℝ_i`, `𝕃_i`, `ℕ_i`, `𝔼_i`

A thread is *settled* (`ℕ_i`) when it is yielding or has gone wrong; otherwise it
is running, in the right-mover pre-commit phase (`ℝ_i`, phase `R`) or the
left-mover post-commit phase (`𝕃_i`, phase `N`). -/

/-- `𝔼_i` — thread `i` has gone wrong (`E[wrong]`). -/
def clE (Pi : IState) (i : Tid) : Prop :=
  ∃ s p, Pi.threads[i]? = some (s, p) ∧ IsWrong s

/-- `ℕ_i` — thread `i` is settled: yielding or wrong (includes `𝔼_i`). -/
def clN (Pi : IState) (i : Tid) : Prop :=
  ∃ s p, Pi.threads[i]? = some (s, p) ∧ (yielding s ∨ IsWrong s)

/-- `ℝ_i` — thread `i` is running in the right-mover pre-commit phase `R`. -/
def clR (Pi : IState) (i : Tid) : Prop :=
  ∃ s p, Pi.threads[i]? = some (s, p) ∧ p = Effect.R ∧ ¬ (yielding s ∨ IsWrong s)

/-- `𝕃_i` — thread `i` is running in the left-mover post-commit phase `N`. -/
def clL (Pi : IState) (i : Tid) : Prop :=
  ∃ s p, Pi.threads[i]? = some (s, p) ∧ p = Effect.N ∧ ¬ (yielding s ∨ IsWrong s)

/-- `𝔼_i ⊆ ℕ_i`. -/
theorem clN_of_clE {Pi i} (h : clE Pi i) : clN Pi i := by
  obtain ⟨s, p, hget, hw⟩ := h; exact ⟨s, p, hget, Or.inr hw⟩

/-! ### Wrong is absorbing

A wrong thread cannot step and is untouched by other threads' steps, so once a
state is wrong it stays wrong along any run. -/

/-- Structural "is the leftmost redex `wrong`" test. -/
def isStuck : Stmt → Bool
  | .wrong => true
  | .seq a _ => isStuck a
  | _ => false

theorem isStuck_plug (E : Ctx) (r : Stmt) : isStuck (E.plug r) = isStuck r := by
  induction E with
  | hole => rfl
  | seqL E' s2 ih => simp [Ctx.plug, isStuck, ih]

theorem isStuck_of_isWrong {s : Stmt} (hw : IsWrong s) : isStuck s = true := by
  obtain ⟨E, rfl⟩ := hw; rw [isStuck_plug]; rfl

/-- A wrong statement `E[wrong]` does not step. -/
theorem isWrong_not_step {M D t} {s : Stmt} {σ : Store} {p : Phase}
    {s' σ' p'} (hw : IsWrong s) (h : IThreadStep M D t s σ p s' σ' p') : False := by
  have hfalse : isStuck s = false := by
    cases h <;> rw [isStuck_plug] <;> rfl
  rw [isStuck_of_isWrong hw] at hfalse; exact Bool.noConfusion hfalse

/-- `IWrong` in index form: some thread `i` is in `𝔼_i`. -/
theorem iwrong_iff_clE {Pi : IState} : IWrong Pi ↔ ∃ i, clE Pi i := by
  constructor
  · rintro ⟨sp, hmem, hw⟩
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    exact ⟨i, sp.1, sp.2, by rw [List.getElem?_eq_getElem hi, hget], hw⟩
  · rintro ⟨i, s, p, hget, hw⟩
    exact ⟨(s, p), List.mem_of_getElem? hget, hw⟩

/-- A step out of a state where thread `i` is wrong keeps thread `i` wrong:
    a wrong thread cannot be the one that steps, and other threads leave it
    untouched. -/
theorem clE_step {M D k} {a b : IState} (h : IStepI M D k a b) {i : Tid}
    (hi : clE a i) : clE b i := by
  obtain ⟨s, p, hget, hw⟩ := hi
  cases h with
  | mk ths s0 s0' σ σ' p0 p0' hget0 hstep =>
    by_cases hik : i = k
    · subst hik
      rw [hget0] at hget
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hget
      exact absurd (isWrong_not_step hw hstep) id
    · refine ⟨s, p, ?_, hw⟩
      rw [getElem?_set_ne _ _ (Ne.symm hik)]; exact hget

/-- Reaching wrong is preserved by a preemptive step. -/
theorem iwrong_step {M D} {a b : IState} (h : IStep M D a b) (hw : IWrong a) :
    IWrong b := by
  obtain ⟨k, hk⟩ := h.exists_tid
  obtain ⟨i, hi⟩ := iwrong_iff_clE.1 hw
  exact iwrong_iff_clE.2 ⟨i, clE_step hk hi⟩

/-! ### Thread-indexed commutation diamond (store-touching core)

The `IStepI`-tagged analogue of `Reduction.diamond_core`: from action-like steps
of `i` then `j` and a store swap witnessing that the two store transitions
commute, the full square of four indexed steps reconciles.  Same proof as
`diamond_core`, tagged with thread indices so it composes in the trace algebra. -/

theorem diamond_core_I {M : MoverSpec} {D : BodyEnv} (hV : Valid M)
    {ths : List (Stmt × Phase)} {σ σ' σ'' σ''' : Store} {i j : Tid}
    {ri ri' rj rj' : Stmt} {Ai Aj : Action} {pi pj : Phase}
    (hij : i ≠ j)
    (hi : ths[i]? = some (ri, pi)) (hj : ths[j]? = some (rj, pj))
    (ali : ActionLike M D i ri ri' Ai pi) (alj : ActionLike M D j rj rj' Aj pj)
    (hmiN : M Ai i σ ⊑ Effect.N)
    (hAi : Ai i σ σ') (hnei : pi ;; M Ai i σ ≠ Effect.E)
    (hAj : Aj j σ' σ'') (hnej : pj ;; M Aj j σ' ≠ Effect.E)
    (hAjσ : Aj j σ σ''') (hAiσ''' : Ai i σ''' σ'') :
    IStepI M D i ⟨ths, σ⟩ ⟨ths.set i (ri', pi ;; M Ai i σ), σ'⟩ ∧
    IStepI M D j ⟨ths.set i (ri', pi ;; M Ai i σ), σ'⟩
            ⟨(ths.set i (ri', pi ;; M Ai i σ)).set j (rj', pj ;; M Aj j σ'), σ''⟩ ∧
    IStepI M D j ⟨ths, σ⟩ ⟨ths.set j (rj', pj ;; M Aj j σ), σ'''⟩ ∧
    IStepI M D i ⟨ths.set j (rj', pj ;; M Aj j σ), σ'''⟩
            ⟨(ths.set i (ri', pi ;; M Ai i σ)).set j (rj', pj ;; M Aj j σ'), σ''⟩ := by
  have hmjN' : M Aj j σ' ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnej)
  have heffj : M Aj j σ' = M Aj j σ :=
    hV.effect i j Ai Aj σ σ' (M Aj j σ) hij hmiN hAi rfl
  have hmjNσ : M Aj j σ ⊑ Effect.N := heffj ▸ hmjN'
  have heffi : M Ai i σ''' = M Ai i σ :=
    hV.effect j i Aj Ai σ σ''' (M Ai i σ) (Ne.symm hij) hmjNσ hAjσ rfl
  have hnejσ : pj ;; M Aj j σ ≠ Effect.E := by rw [← heffj]; exact hnej
  have hneiσ''' : pi ;; M Ai i σ''' ≠ Effect.E := by rw [heffi]; exact hnei
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IStepI.mk ths _ _ σ σ' pi _ hi (ali σ σ' hAi hnei)
  · have hgetj : (ths.set i (ri', pi ;; M Ai i σ))[j]? = some (rj, pj) := by
      rw [getElem?_set_ne _ _ hij]; exact hj
    exact IStepI.mk _ _ _ σ' σ'' pj _ hgetj (alj σ' σ'' hAj hnej)
  · exact IStepI.mk ths _ _ σ σ''' pj _ hj (alj σ σ''' hAjσ hnejσ)
  · have hgeti : (ths.set j (rj', pj ;; M Aj j σ))[i]? = some (ri, pi) := by
      rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hi
    have step : IStepI M D i ⟨ths.set j (rj', pj ;; M Aj j σ), σ'''⟩
        ⟨(ths.set j (rj', pj ;; M Aj j σ)).set i (ri', pi ;; M Ai i σ'''), σ''⟩ :=
      IStepI.mk (ths.set j (rj', pj ;; M Aj j σ)) _ _ σ''' σ'' pi _
        hgeti (ali σ''' σ'' hAiσ''' hneiσ''')
    have hfin :
        (ths.set j (rj', pj ;; M Aj j σ)).set i (ri', pi ;; M Ai i σ''')
        = (ths.set i (ri', pi ;; M Ai i σ)).set j (rj', pj ;; M Aj j σ') := by
      rw [heffi, heffj]; exact (set_comm ths _ _ hij).symm
    have : (⟨(ths.set j (rj', pj ;; M Aj j σ)).set i (ri', pi ;; M Ai i σ'''), σ''⟩ : IState)
        = ⟨(ths.set i (ri', pi ;; M Ai i σ)).set j (rj', pj ;; M Aj j σ'), σ''⟩ := by rw [hfin]
    exact this ▸ step

/-! ### Effect bookkeeping for phase transitions -/

/-- If a phase step composes to `R`, the composed effect is `⊑ R`. -/
theorem seq_eq_R_imp_le_R {a b : Effect} (h : a ;; b = Effect.R) : b ⊑ Effect.R := by
  cases a <;> cases b <;> simp_all [Effect.seq] <;> decide

/-! ### Independent commutation: a structural step commutes with any step

A structural (store-independent, store-preserving) step of thread `i` commutes
with *any* step of thread `j ≠ i`, with no mover conditions — this is the
paper's "the remaining cases are similar" for `I-seq`, `I-yield`, `I-while`,
`I-call`.  We phrase both orientations (structural step first, or second). -/

/-- Structural `i`-step first, then any `j`-step: swap to `j` first, then `i`. -/
theorem indep_i_first {M : MoverSpec} {D : BodyEnv} {i j : Tid} (hij : i ≠ j)
    {ths : List (Stmt × Phase)} {σ σj : Store}
    {si si' sj sj' : Stmt} {pi pi' pj pj' : Phase}
    (hi : ths[i]? = some (si, pi)) (hj : ths[j]? = some (sj, pj))
    (replay_i : ∀ σx, IThreadStep M D i si σx pi si' σx pi')
    (jstep : IThreadStep M D j sj σ pj sj' σj pj') :
    IStepI M D j ⟨ths, σ⟩ ⟨ths.set j (sj', pj'), σj⟩ ∧
    IStepI M D i ⟨ths.set j (sj', pj'), σj⟩
            ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩ := by
  refine ⟨IStepI.mk ths _ _ σ σj pj _ hj jstep, ?_⟩
  have hgeti : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
    rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hi
  have step : IStepI M D i ⟨ths.set j (sj', pj'), σj⟩
      ⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ :=
    IStepI.mk (ths.set j (sj', pj')) _ _ σj σj pi _ hgeti (replay_i σj)
  have hcomm : (⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ : IState)
      = ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩ := by
    rw [set_comm ths _ _ (Ne.symm hij)]
  exact hcomm ▸ step

/-- Any `j`-step first, then a structural `i`-step: swap to `i` first, then `j`. -/
theorem indep_i_second {M : MoverSpec} {D : BodyEnv} {i j : Tid} (hij : i ≠ j)
    {ths : List (Stmt × Phase)} {σ σj : Store}
    {si si' sj sj' : Stmt} {pi pi' pj pj' : Phase}
    (hi : ths[i]? = some (si, pi)) (hj : ths[j]? = some (sj, pj))
    (replay_i : ∀ σx, IThreadStep M D i si σx pi si' σx pi')
    (jstep : IThreadStep M D j sj σ pj sj' σj pj') :
    IStepI M D i ⟨ths, σ⟩ ⟨ths.set i (si', pi'), σ⟩ ∧
    IStepI M D j ⟨ths.set i (si', pi'), σ⟩
            ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩ := by
  refine ⟨IStepI.mk ths _ _ σ σ pi _ hi (replay_i σ), ?_⟩
  have hgetj : (ths.set i (si', pi'))[j]? = some (sj, pj) := by
    rw [getElem?_set_ne _ _ hij]; exact hj
  exact IStepI.mk _ _ _ σ σj pj _ hgetj jstep

/-- Index-`i` `getElem?` after setting index `i`. -/
theorem getElem?_set_self_of {α} (l : List α) {i : Nat} (x : α)
    (h : i < l.length) : (l.set i x)[i]? = some x := by
  rw [List.getElem?_set_self]; simp [h]

theorem lt_of_getElem? {α} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    i < l.length := (List.getElem?_eq_some_iff.1 h).1

/-! ### Right Commutativity (thread-indexed)

Paper Lemma Right Commutativity: `(→_i ∖ ℝ_i)` commutes with `→_j`.  A right-mover
step of thread `i` (ending in `ℝ_i`, so `M(A_i,i,σ) ⊑ R`) commutes past any
*non-wrong* step of thread `j ≠ i`.  Store-touching cases use validity (1) via
`diamond_core_I`; structural cases are independent. -/

theorem right_commutes {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {i j : Tid}
    (hij : i ≠ j) {Pa Pb Pc : IState}
    (hi : IStepI M D i Pa Pb) (hclR : clR Pb i)
    (hj : IStepI M D j Pb Pc) (hjok : ¬ clE Pc j) :
    ∃ Pd, IStepI M D j Pa Pd ∧ IStepI M D i Pd Pc := by
  cases hi with
  | mk ths si si' σ σ' pi pi' hgeti histep_i =>
    have hilt : i < ths.length := lt_of_getElem? hgeti
    rcases ithreadstep_classify histep_i with
      ⟨hσ, replay_i⟩ | ⟨Ai, ali, hAi, hpi', hnei⟩ | ⟨hw, _, _⟩
    · -- i structural
      subst σ'
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        -- ths2 = ths.set i (si',pi'), σa = σ
        have hgetjb : ths[j]? = some (sj, pj) := by
          rw [← getElem?_set_ne ths (si', pi') hij]; exact hgetj
        refine ⟨⟨ths.set j (sj', pj'), σj⟩, IStepI.mk ths _ _ σ σj pj _ hgetjb histep_j, ?_⟩
        have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
          rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
        have step : IStepI M D i ⟨ths.set j (sj', pj'), σj⟩
            ⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ :=
          IStepI.mk (ths.set j (sj', pj')) _ _ σj σj pi _ hgeti2 (replay_i σj)
        have hcomm : (⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ : IState)
            = ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩ := by
          rw [set_comm ths _ _ (Ne.symm hij)]
        exact hcomm ▸ step
    · -- i store-touching (right-mover)
      -- extract M A_i i σ ⊑ R from clR Π' i
      obtain ⟨s0, p0, hget0, hpR, _⟩ := hclR
      rw [getElem?_set_self_of ths (si', pi') hilt] at hget0
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hget0
      have hmi : M Ai i σ ⊑ Effect.R := seq_eq_R_imp_le_R (hpi' ▸ hpR)
      have hmiN : M Ai i σ ⊑ Effect.N := le_trans hmi (by decide)
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        -- ths2 = ths.set i (si',pi'), σa = σ'
        have hgetjb : ths[j]? = some (sj, pj) := by
          rw [← getElem?_set_ne ths (si', pi') hij]; exact hgetj
        rcases ithreadstep_classify histep_j with
          ⟨hσj, replay_j⟩ | ⟨Aj, alj, hAj, hpj', hnej⟩ | ⟨hwj, _, _⟩
        · -- j structural: j first (store σ), then i store-touching
          subst σj
          refine ⟨⟨ths.set j (sj', pj'), σ⟩,
            IStepI.mk ths _ _ σ σ pj _ hgetjb (replay_j σ), ?_⟩
          have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
            rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
          have step : IStepI M D i ⟨ths.set j (sj', pj'), σ⟩
              ⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ :=
            IStepI.mk (ths.set j (sj', pj')) _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
          have hcomm : (⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ : IState)
              = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'⟩ := by
            rw [set_comm ths _ _ (Ne.symm hij)]
          exact hcomm ▸ step
        · -- j store-touching: validity (1) + diamond_core_I
          have hmjN' : M Aj j σ' ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnej)
          obtain ⟨σ''', hAjσ, hAiσ'''⟩ := hV.right i j Ai Aj σ σ' σj hij hmi hAi hmjN' hAj
          obtain ⟨_, _, D3, D4⟩ :=
            diamond_core_I hV hij hgeti hgetjb ali alj hmiN hAi (hpi' ▸ hnei) hAj hnej hAjσ hAiσ'''
          refine ⟨_, D3, ?_⟩
          -- reconcile final state and phases: pi' = pi;;M Ai i σ, pj' = pj;;M Aj j σ'
          rw [hpi', hpj']; exact D4
        · exact absurd ⟨sj', pj', getElem?_set_self_of _ _ (lt_of_getElem? hgetj), hwj⟩ hjok
    · -- i store-touching-wrong contradicts clR (i not wrong at Π')
      obtain ⟨s0, p0, hget0, _, hnotwrong⟩ := hclR
      rw [getElem?_set_self_of ths (si', pi') hilt] at hget0
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hget0
      exact absurd (Or.inr hw) hnotwrong

/-- If `N ; b` is non-error then `b ⊑ L` (a post-commit step is a left-mover). -/
theorem seq_N_ne_E_imp_le_L {b : Effect} (h : Effect.N ;; b ≠ Effect.E) : b ⊑ Effect.L := by
  cases b <;> simp_all [Effect.seq] <;> decide

/-! ### Left Commutativity (thread-indexed)

Paper Lemma Left Commutativity: `→_i` commutes with `(𝕃_j ∖ →_j)`.  A left-mover
step of thread `j` (from `𝕃_j`, so `M(A_j,j,σ') ⊑ L`), taken *after* a non-wrong
step of thread `i ≠ j`, commutes to *before* it.  Store-touching cases use
validity (2); structural cases are independent. -/

theorem left_commutes {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {i j : Tid}
    (hij : i ≠ j) {Pa Pb Pc : IState}
    (hi : IStepI M D i Pa Pb) (hiok : ¬ clE Pb i)
    (hclL : clL Pb j) (hj : IStepI M D j Pb Pc) (hjok : ¬ clE Pc j) :
    ∃ Pd, IStepI M D j Pa Pd ∧ IStepI M D i Pd Pc := by
  cases hi with
  | mk ths si si' σ σ' pi pi' hgeti histep_i =>
    have hilt : i < ths.length := lt_of_getElem? hgeti
    rcases ithreadstep_classify histep_i with
      ⟨hσ, replay_i⟩ | ⟨Ai, ali, hAi, hpi', hnei⟩ | ⟨hw, _, _⟩
    · -- i structural
      subst σ'
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        have hgetjb : ths[j]? = some (sj, pj) := by
          rw [← getElem?_set_ne ths (si', pi') hij]; exact hgetj
        refine ⟨⟨ths.set j (sj', pj'), σj⟩, IStepI.mk ths _ _ σ σj pj _ hgetjb histep_j, ?_⟩
        have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
          rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
        have step : IStepI M D i ⟨ths.set j (sj', pj'), σj⟩
            ⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ :=
          IStepI.mk (ths.set j (sj', pj')) _ _ σj σj pi _ hgeti2 (replay_i σj)
        have hcomm : (⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ : IState)
            = ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩ := by
          rw [set_comm ths _ _ (Ne.symm hij)]
        exact hcomm ▸ step
    · -- i store-touching (non-wrong)
      have hmiN : M Ai i σ ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnei)
      -- j's phase at Pb is N (from clL)
      obtain ⟨s0, p0, hget0, hpjN, _⟩ := hclL
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        have hgetjb : ths[j]? = some (sj, pj) := by
          rw [← getElem?_set_ne ths (si', pi') hij]; exact hgetj
        have hpjN' : pj = Effect.N := by
          have h : (s0, p0) = (sj, pj) := Option.some.inj (hget0.symm.trans hgetj)
          have hp : p0 = pj := congrArg Prod.snd h
          rw [← hp]; exact hpjN
        rcases ithreadstep_classify histep_j with
          ⟨hσj, replay_j⟩ | ⟨Aj, alj, hAj, hpj', hnej⟩ | ⟨hwj, _, _⟩
        · -- j structural: j first (store σ), then i store-touching
          subst σj
          refine ⟨⟨ths.set j (sj', pj'), σ⟩,
            IStepI.mk ths _ _ σ σ pj _ hgetjb (replay_j σ), ?_⟩
          have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
            rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
          have step : IStepI M D i ⟨ths.set j (sj', pj'), σ⟩
              ⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ :=
            IStepI.mk (ths.set j (sj', pj')) _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
          have hcomm : (⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ : IState)
              = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'⟩ := by
            rw [set_comm ths _ _ (Ne.symm hij)]
          exact hcomm ▸ step
        · -- j store-touching left-mover: validity (2) + diamond_core_I
          have hmjL : M Aj j σ' ⊑ Effect.L := seq_N_ne_E_imp_le_L (hpjN' ▸ hnej)
          obtain ⟨σ''', hAjσ, hAiσ'''⟩ := hV.left i j Ai Aj σ σ' σj hij hmiN hAi hmjL hAj
          obtain ⟨_, _, D3, D4⟩ :=
            diamond_core_I hV hij hgeti hgetjb ali alj hmiN hAi (hpi' ▸ hnei) hAj hnej hAjσ hAiσ'''
          refine ⟨_, D3, ?_⟩
          rw [hpi', hpj']; exact D4
        · exact absurd ⟨sj', pj', getElem?_set_self_of _ _ (lt_of_getElem? hgetj), hwj⟩ hjok
    · -- i wrong contradicts hiok
      exact absurd ⟨si', pi', getElem?_set_self_of ths (si', pi') hilt, hw⟩ hiok

/-! ### The Diamond lemma (thread-indexed)

Paper Lemma Diamond: when thread `j` is post-commit (`Pa ∈ 𝕃_j`), two steps out
of the *same* state `Pa` — one by `i`, one by `j ≠ i` — reconverge.  Store swap
from validity (4) via `diamond_parallel`; structural cases are independent.  This
is the confluence used to merge post-commit termination traces. -/

theorem diamond_commutes {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {i j : Tid}
    (hij : i ≠ j) {Pa Pb Pc : IState}
    (hi : IStepI M D i Pa Pb) (hiok : ¬ clE Pb i)
    (hclL : clL Pa j) (hj : IStepI M D j Pa Pc) (hjok : ¬ clE Pc j) :
    ∃ Pd, IStepI M D j Pb Pd ∧ IStepI M D i Pc Pd := by
  cases hi with
  | mk ths si si' σ σ' pi pi' hgeti histep_i =>
    have hilt : i < ths.length := lt_of_getElem? hgeti
    obtain ⟨sj0, pj0, hgetj0, hpjN, _⟩ := hclL
    rcases ithreadstep_classify histep_i with
      ⟨hσ, replay_i⟩ | ⟨Ai, ali, hAi, hpi', hnei⟩ | ⟨hw, _, _⟩
    · -- i structural
      subst σ'
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        refine ⟨⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩, ?_, ?_⟩
        · have hgetj2 : (ths.set i (si', pi'))[j]? = some (sj, pj) := by
            rw [getElem?_set_ne _ _ hij]; exact hgetj
          exact IStepI.mk _ _ _ σ σj pj _ hgetj2 histep_j
        · have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
            rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
          have step : IStepI M D i ⟨ths.set j (sj', pj'), σj⟩
              ⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ :=
            IStepI.mk _ _ _ σj σj pi _ hgeti2 (replay_i σj)
          have : (⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ : IState)
              = ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩ := by
            rw [set_comm ths _ _ (Ne.symm hij)]
          exact this ▸ step
    · -- i store-touching (non-wrong)
      have hmiN : M Ai i σ ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnei)
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        have hpjN' : pj = Effect.N := by
          have h : (sj0, pj0) = (sj, pj) := Option.some.inj (hgetj0.symm.trans hgetj)
          have hp : pj0 = pj := congrArg Prod.snd h
          rw [← hp]; exact hpjN
        rcases ithreadstep_classify histep_j with
          ⟨hσj, replay_j⟩ | ⟨Aj, alj, hAj, hpj', hnej⟩ | ⟨hwj, _, _⟩
        · -- j structural
          subst σj
          refine ⟨⟨(ths.set i (si', pi')).set j (sj', pj'), σ'⟩, ?_, ?_⟩
          · have hgetj2 : (ths.set i (si', pi'))[j]? = some (sj, pj) := by
              rw [getElem?_set_ne _ _ hij]; exact hgetj
            exact IStepI.mk _ _ _ σ' σ' pj _ hgetj2 (replay_j σ')
          · have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
              rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
            have step : IStepI M D i ⟨ths.set j (sj', pj'), σ⟩
                ⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ :=
              IStepI.mk _ _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
            have : (⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ : IState)
                = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'⟩ := by
              rw [set_comm ths _ _ (Ne.symm hij)]
            exact this ▸ step
        · -- both store-touching: validity (4)
          have hmjL : M Aj j σ ⊑ Effect.L := seq_N_ne_E_imp_le_L (hpjN' ▸ hnej)
          obtain ⟨σ''', hAjσ', hAiσ''⟩ := hV.nonblock i j Ai Aj σ σ' σj hij hmiN hAi hmjL hAj
          -- effect invariances (validity 3)
          have heffj : M Aj j σ' = M Aj j σ :=
            hV.effect i j Ai Aj σ σ' (M Aj j σ) hij hmiN hAi rfl
          have heffi : M Ai i σj = M Ai i σ :=
            hV.effect j i Aj Ai σ σj (M Ai i σ) (Ne.symm hij) (le_trans hmjL (by decide)) hAj rfl
          refine ⟨⟨(ths.set i (si', pi')).set j (sj', pj'), σ'''⟩, ?_, ?_⟩
          · -- j from Pb = ⟨ths.set i (si',pi'), σ'⟩
            have hgetj2 : (ths.set i (si', pi'))[j]? = some (sj, pj) := by
              rw [getElem?_set_ne _ _ hij]; exact hgetj
            have hnej' : pj ;; M Aj j σ' ≠ Effect.E := by rw [heffj]; exact hpj' ▸ hnej
            have step : IStepI M D j ⟨ths.set i (si', pi'), σ'⟩
                ⟨(ths.set i (si', pi')).set j (sj', pj ;; M Aj j σ'), σ'''⟩ :=
              IStepI.mk _ _ _ σ' σ''' pj _ hgetj2 (alj σ' σ''' hAjσ' hnej')
            have : (⟨(ths.set i (si', pi')).set j (sj', pj ;; M Aj j σ'), σ'''⟩ : IState)
                = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'''⟩ := by rw [hpj', heffj]
            exact this ▸ step
          · -- i from Pc = ⟨ths.set j (sj',pj'), σj⟩
            have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
              rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
            have hnei' : pi ;; M Ai i σj ≠ Effect.E := by rw [heffi]; exact hpi' ▸ hnei
            have step : IStepI M D i ⟨ths.set j (sj', pj'), σj⟩
                ⟨(ths.set j (sj', pj')).set i (si', pi ;; M Ai i σj), σ'''⟩ :=
              IStepI.mk _ _ _ σj σ''' pi _ hgeti2 (ali σj σ''' hAiσ'' hnei')
            have hfin : (⟨(ths.set j (sj', pj')).set i (si', pi ;; M Ai i σj), σ'''⟩ : IState)
                = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'''⟩ := by
              have : (ths.set j (sj', pj')).set i (si', pi ;; M Ai i σj)
                  = (ths.set i (si', pi')).set j (sj', pj') := by
                rw [heffi, hpi']; exact (set_comm ths _ _ hij).symm
              rw [this]
            exact hfin ▸ step
        · exact absurd ⟨sj', pj', getElem?_set_self_of _ _ (lt_of_getElem? hgetj), hwj⟩ hjok
    · exact absurd ⟨si', pi', getElem?_set_self_of ths (si', pi') hilt, hw⟩ hiok

/-! ### Status: the local-commutation layer, complete

This file mechanizes the **entire local-commutation layer of the Reduction
theorem in trace-composable, thread-indexed form** — the interface the global
trace-block argument consumes — all `sorry`-free from `Valid M`:

  * `right_commutes` — Right Commutativity: a right-mover step of `i` (ending in
    `ℝ_i`) commutes past any non-wrong step of `j ≠ i`  (validity (1));
  * `left_commutes`  — Left Commutativity: a left-mover step of `j` (from `𝕃_j`),
    after a non-wrong step of `i ≠ j`, commutes before it  (validity (2));
  * `diamond_commutes` — the Diamond: two steps out of a state with `j` post-commit
    reconverge  (validity (4));
  * `indep_i_first` / `indep_i_second` — the structural (store-preserving) cases,
    with no mover conditions.

Each is stated over `IStepI` (thread-indexed preemptive steps) and the state
classes `ℝ_i`/`𝕃_i`/`ℕ_i`/`𝔼_i`, so the swaps chain directly in the trace
algebra.  Compared with `Reduction.lean` (state-level, single-diamond, action/
action only), these additionally cover *every* step kind (structural and
store-touching, `I-action` and `I-if`) and discharge the class-membership
side-conditions.  The supporting facts — the step classifier
`ithreadstep_classify`, and that *reaching wrong is absorbing* (`iwrong_step`,
`clE_step`) — are proved here too; the latter is what lets the global argument
keep the fatal step *inside* its thread's transaction, so no wrong step is ever
commuted across threads (only the OK/structural cases above are needed).

The remaining ingredients of the Reduction theorem are proved downstream:

  1. **Post-Commit Termination** (paper Lemma) — `post_commit_term` in
     `PostCommit.lean`, together with its `progress` engine, using the model
     well-formedness the paper assumes (`NeverYields`, `CondTotal`, and a
     `GoodSizing` witness = atomic functions are non-recursive), invoking the
     proved `preservation` theorem along the run.

  2. **Iterative Diamond** — `iter_diamond` / `iter_diamondN` in `Assembly.lean`:
     iterate `diamond_commutes` along a left-mover run to merge a post-commit
     termination trace into the main trace.

  3. The **global block-decomposition induction** — `reorder_core` in
     `Assembly.lean`: extract each thread's transaction (commit-ordered) to the
     front via the commutation lemmas above, using (1)+(2) to close off
     unfinished post-commit blocks — the `Post*; Pre*` / `Finish*` argument of
     the paper's Reduction proof, culminating in `reduction_proved` and the
     re-assembled `soundness'`. -/

end MoverLogic
