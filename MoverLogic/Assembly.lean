/-
  Assembly of the Reduction Theorem (Theorem thm:red).

  Using the trace-composable commutation lemmas (`ReductionThm.lean`) and
  Post-Commit Termination (`PostCommit.lean`), this file carries out the global
  trace-block argument (§sec:red-thm) and discharges the `reduction` axiom,
  re-deriving `soundness` with no `reduction` axiom.

  Structure:
    * tagged runs `IStepsT` (preemptive runs recording the acting thread);
    * class invariance (a step of one thread leaves the others' classes fixed);
    * a phase-generalized right commutation and the adjacent-`swap` primitive;
    * `bubble` — move one thread's step to the front of a run;
    * transaction extraction + the outer induction on commit count.
-/
import MoverLogic.PostCommit

namespace MoverLogic

open Effect

/-! ### Tagged preemptive runs -/

/-- A preemptive run recording each step's acting thread. -/
inductive IStepsT (M : MoverSpec) (D : BodyEnv) : IState → IState → Prop where
  | nil (P : IState) : IStepsT M D P P
  | cons {P Pm Pe : IState} (t : Tid) (h : IStepI M D t P Pm) (rest : IStepsT M D Pm Pe) :
      IStepsT M D P Pe

/-- Forget the tags. -/
theorem IStepsT.toISteps {M D} {a b : IState} (h : IStepsT M D a b) : ISteps M D a b := by
  induction h with
  | nil => exact .refl _
  | cons t h _ ih => exact .step h.toIStep ih

/-- Recover a tagged run from an untagged one. -/
theorem ISteps.toTagged {M D} {a b : IState} (h : ISteps M D a b) : IStepsT M D a b := by
  induction h with
  | refl => exact .nil _
  | step hstep _ ih => obtain ⟨t, ht⟩ := hstep.exists_tid; exact .cons t ht ih

/-- Append tagged runs. -/
theorem IStepsT.trans {M D} {a b c : IState} (h1 : IStepsT M D a b) (h2 : IStepsT M D b c) :
    IStepsT M D a c := by
  induction h1 with
  | nil => exact h2
  | cons t h _ ih => exact .cons t h (ih h2)

/-- A single tagged step is a run. -/
theorem IStepI.toStepsT {M D t} {a b : IState} (h : IStepI M D t a b) : IStepsT M D a b :=
  .cons t h (.nil b)

/-! ### Class invariance under a step of another thread

A step by thread `k ≠ j` leaves thread `j`'s statement and phase — hence its
class — unchanged. -/

theorem threads_get_invariant {M D k} {Pa Pb : IState} (h : IStepI M D k Pa Pb) {j : Tid}
    (hjk : j ≠ k) : Pb.threads[j]? = Pa.threads[j]? := by
  cases h with
  | mk ths s s' σ σ' p p' hget hstep => exact getElem?_set_ne ths (s', p') (Ne.symm hjk)

theorem clL_invariant {M D k} {Pa Pb : IState} (h : IStepI M D k Pa Pb) {j : Tid}
    (hjk : j ≠ k) (hL : clL Pa j) : clL Pb j := by
  obtain ⟨s, p, hget, hpN, hns⟩ := hL
  exact ⟨s, p, (threads_get_invariant h hjk).trans hget, hpN, hns⟩

theorem clE_invariant {M D k} {Pa Pb : IState} (h : IStepI M D k Pa Pb) {j : Tid}
    (hjk : j ≠ k) (hE : clE Pa j) : clE Pb j := by
  obtain ⟨s, p, hget, hw⟩ := hE
  exact ⟨s, p, (threads_get_invariant h hjk).trans hget, hw⟩

/-- No single action is assigned the error effect `E` (analogous to `NeverYields`;
    `E` is reserved for non-reducible *compositions*).  This is what lets a wrong
    step's branch witness transport across a mover, exactly as the paper's I-if
    error case uses "`M` validity". -/
def NeverError (M : MoverSpec) : Prop := ∀ A t σ, M A t σ ≠ Effect.E

theorem le_N_of_neverError {M : MoverSpec} (hNE : NeverError M) (A : Action) (t : Tid)
    (σ : Store) : M A t σ ⊑ Effect.N := le_N_of_ne_E (hNE A t σ)

/-! ### Phase-generalized Right Commutativity

`right_commutes` required the first step to end in `ℝ_i` (running).  For the
trace algebra we also need to commute a right-mover step that *settles* to
`skip` (still phase `R`, but yielding).  This variant asks only that `i`'s step
ends with phase `R` and is not wrong — covering both. -/

theorem right_commutes' {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {i j : Tid}
    (hij : i ≠ j) {Pa Pb Pc : IState}
    (hi : IStepI M D i Pa Pb) (hphaseR : ∃ s, Pb.threads[i]? = some (s, Effect.R))
    (hiok : ¬ clE Pb i) (hj : IStepI M D j Pb Pc) (hjok : ¬ clE Pc j) :
    ∃ Pd, IStepI M D j Pa Pd ∧ IStepI M D i Pd Pc := by
  cases hi with
  | mk ths si si' σ σ' pi pi' hgeti histep_i =>
    have hilt : i < ths.length := lt_of_getElem? hgeti
    rcases ithreadstep_classify histep_i with
      ⟨hσ, replay_i⟩ | ⟨Ai, ali, hAi, hpi', hnei⟩ | ⟨hw, _, _⟩
    · subst σ'
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
    · obtain ⟨s0, hget0⟩ := hphaseR
      rw [getElem?_set_self_of ths (si', pi') hilt] at hget0
      have hpR : pi' = Effect.R := (Prod.mk.injEq .. ▸ Option.some.inj hget0).2
      have hmi : M Ai i σ ⊑ Effect.R := seq_eq_R_imp_le_R (hpi' ▸ hpR)
      have hmiN : M Ai i σ ⊑ Effect.N := le_trans hmi (by decide)
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        have hgetjb : ths[j]? = some (sj, pj) := by
          rw [← getElem?_set_ne ths (si', pi') hij]; exact hgetj
        rcases ithreadstep_classify histep_j with
          ⟨hσj, replay_j⟩ | ⟨Aj, alj, hAj, hpj', hnej⟩ | ⟨hwj, _, _⟩
        · subst σj
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
        · have hmjN' : M Aj j σ' ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnej)
          obtain ⟨σ''', hAjσ, hAiσ'''⟩ := hV.right i j Ai Aj σ σ' σj hij hmi hAi hmjN' hAj
          obtain ⟨_, _, D3, D4⟩ :=
            diamond_core_I hV hij hgeti hgetjb ali alj hmiN hAi (hpi' ▸ hnei) hAj hnej hAjσ hAiσ'''
          refine ⟨_, D3, ?_⟩
          rw [hpi', hpj']; exact D4
        · exact absurd ⟨sj', pj', getElem?_set_self_of _ _ (lt_of_getElem? hgetj), hwj⟩ hjok
    · exact absurd ⟨si', pi', getElem?_set_self_of ths (si', pi') hilt, hw⟩ hiok

/-! ### Wrong-case Right Commutativity

`right_commutes_w` drops the `¬ clE Pc j` hypothesis of `right_commutes'`: the
second step of thread `j` may reach `wrong`.  An assertion (`I-if` landing on a
`wrong` statement) is an *ok* store-touching step, already handled; an
*instrumented* wrong step (`I-action`/`I-if` error) is reconstructed from the
swapped store via its re-fire capability — the error effect transports by
validity (3) and the branch witness by validity (1), needing only `NeverError`.
This is the paper's I-if error case (commented out in the paper source). -/

theorem right_commutes_w {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M)
    {i j : Tid} (hij : i ≠ j) {Pa Pb Pc : IState}
    (hi : IStepI M D i Pa Pb) (hphaseR : ∃ s, Pb.threads[i]? = some (s, Effect.R))
    (hiok : ¬ clE Pb i) (hj : IStepI M D j Pb Pc) :
    ∃ Pd, IStepI M D j Pa Pd ∧ IStepI M D i Pd Pc := by
  cases hi with
  | mk ths si si' σ σ' pi pi' hgeti histep_i =>
    have hilt : i < ths.length := lt_of_getElem? hgeti
    rcases ithreadstep_classify histep_i with
      ⟨hσ, replay_i⟩ | ⟨Ai, ali, hAi, hpi', hnei⟩ | ⟨hw, _, _⟩
    · subst σ'
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
        exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
          (⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ : IState)
            = ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩) ▸ step
    · obtain ⟨s0, hget0⟩ := hphaseR
      rw [getElem?_set_self_of ths (si', pi') hilt] at hget0
      have hpR : pi' = Effect.R := (Prod.mk.injEq .. ▸ Option.some.inj hget0).2
      have hmi : M Ai i σ ⊑ Effect.R := seq_eq_R_imp_le_R (hpi' ▸ hpR)
      have hmiN : M Ai i σ ⊑ Effect.N := le_trans hmi (by decide)
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        have hgetjb : ths[j]? = some (sj, pj) := by
          rw [← getElem?_set_ne ths (si', pi') hij]; exact hgetj
        rcases ithreadstep_classify histep_j with
          ⟨hσj, replay_j⟩ | ⟨Aj, alj, hAj, hpj', hnej⟩ | ⟨hwj, hσj, hpj, hrefire⟩
        · subst σj
          refine ⟨⟨ths.set j (sj', pj'), σ⟩,
            IStepI.mk ths _ _ σ σ pj _ hgetjb (replay_j σ), ?_⟩
          have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
            rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
          have step : IStepI M D i ⟨ths.set j (sj', pj'), σ⟩
              ⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ :=
            IStepI.mk (ths.set j (sj', pj')) _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
          exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
            (⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ : IState)
              = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'⟩) ▸ step
        · have hmjN' : M Aj j σ' ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnej)
          obtain ⟨σ''', hAjσ, hAiσ'''⟩ := hV.right i j Ai Aj σ σ' σj hij hmi hAi hmjN' hAj
          obtain ⟨_, _, D3, D4⟩ :=
            diamond_core_I hV hij hgeti hgetjb ali alj hmiN hAi (hpi' ▸ hnei) hAj hnej hAjσ hAiσ'''
          refine ⟨_, D3, ?_⟩
          rw [hpi', hpj']; exact D4
        · -- j instrumented-wrong: reconstruct from the swapped store σ
          subst σj; subst pj'
          refine ⟨⟨ths.set j (sj', pj), σ⟩, ?_, ?_⟩
          · have hjstep : IThreadStep M D j sj σ pj sj' σ pj := by
              rcases hrefire with ⟨A, hEσ', refire⟩ | ⟨A, σ0, hwit, hEσ', refire⟩
              · have heff : M A j σ = M A j σ' :=
                  hV.effect i j Ai A σ σ' (M A j σ) hij hmiN hAi rfl |>.symm
                exact refire σ (by rw [heff]; exact hEσ')
              · have heff : M A j σ = M A j σ' :=
                  hV.effect i j Ai A σ σ' (M A j σ) hij hmiN hAi rfl |>.symm
                obtain ⟨σt, hAjt, _⟩ :=
                  hV.right i j Ai A σ σ' σ0 hij hmi hAi (le_N_of_neverError hNE A j σ') hwit
                exact refire σ σt hAjt (by rw [heff]; exact hEσ')
            exact IStepI.mk ths _ _ σ σ pj _ hgetjb hjstep
          · have hgeti2 : (ths.set j (sj', pj))[i]? = some (si, pi) := by
              rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
            have step : IStepI M D i ⟨ths.set j (sj', pj), σ⟩
                ⟨(ths.set j (sj', pj)).set i (si', pi'), σ'⟩ :=
              IStepI.mk (ths.set j (sj', pj)) _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
            exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
              (⟨(ths.set j (sj', pj)).set i (si', pi'), σ'⟩ : IState)
                = ⟨(ths.set i (si', pi')).set j (sj', pj), σ'⟩) ▸ step
    · exact absurd ⟨si', pi', getElem?_set_self_of ths (si', pi') hilt, hw⟩ hiok

/-! ### Wrong-case Diamond

`diamond_commutes_w` drops the `¬ clE Pb i` hypothesis of `diamond_commutes`:
the first thread `i` may reach wrong (the merge's "fatal step").  It is
reconstructed on the left-mover `j`'s post-store — the error effect by validity
(3), the branch witness by validity (4) (forward transport past a left-mover). -/

theorem diamond_commutes_w {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M)
    {i j : Tid} (hij : i ≠ j) {Pa Pb Pc : IState}
    (hi : IStepI M D i Pa Pb)
    (hclL : clL Pa j) (hj : IStepI M D j Pa Pc) (hjok : ¬ clE Pc j) :
    ∃ Pd, IStepI M D j Pb Pd ∧ IStepI M D i Pc Pd := by
  cases hi with
  | mk ths si si' σ σ' pi pi' hgeti histep_i =>
    have hilt : i < ths.length := lt_of_getElem? hgeti
    obtain ⟨sj0, pj0, hgetj0, hpjN, _⟩ := hclL
    rcases ithreadstep_classify histep_i with
      ⟨hσ, replay_i⟩ | ⟨Ai, ali, hAi, hpi', hnei⟩ | ⟨hw, hσ, hp, hrefire⟩
    · -- i structural (identical to diamond_commutes)
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
          exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
            (⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ : IState)
              = ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩) ▸ step
    · -- i store-touching (non-wrong) — identical to diamond_commutes
      have hmiN : M Ai i σ ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnei)
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        have hpjN' : pj = Effect.N := by
          have h : (sj0, pj0) = (sj, pj) := Option.some.inj (hgetj0.symm.trans hgetj)
          have hp2 : pj0 = pj := congrArg Prod.snd h
          rw [← hp2]; exact hpjN
        rcases ithreadstep_classify histep_j with
          ⟨hσj, replay_j⟩ | ⟨Aj, alj, hAj, hpj', hnej⟩ | ⟨hwj, _, _⟩
        · subst σj
          refine ⟨⟨(ths.set i (si', pi')).set j (sj', pj'), σ'⟩, ?_, ?_⟩
          · have hgetj2 : (ths.set i (si', pi'))[j]? = some (sj, pj) := by
              rw [getElem?_set_ne _ _ hij]; exact hgetj
            exact IStepI.mk _ _ _ σ' σ' pj _ hgetj2 (replay_j σ')
          · have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
              rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
            have step : IStepI M D i ⟨ths.set j (sj', pj'), σ⟩
                ⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ :=
              IStepI.mk _ _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
            exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
              (⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ : IState)
                = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'⟩) ▸ step
        · have hmjL : M Aj j σ ⊑ Effect.L := seq_N_ne_E_imp_le_L (hpjN' ▸ hnej)
          obtain ⟨σ''', hAjσ', hAiσ''⟩ := hV.nonblock i j Ai Aj σ σ' σj hij hmiN hAi hmjL hAj
          have heffj : M Aj j σ' = M Aj j σ :=
            hV.effect i j Ai Aj σ σ' (M Aj j σ) hij hmiN hAi rfl
          have heffi : M Ai i σj = M Ai i σ :=
            hV.effect j i Aj Ai σ σj (M Ai i σ) (Ne.symm hij) (le_trans hmjL (by decide)) hAj rfl
          refine ⟨⟨(ths.set i (si', pi')).set j (sj', pj'), σ'''⟩, ?_, ?_⟩
          · have hgetj2 : (ths.set i (si', pi'))[j]? = some (sj, pj) := by
              rw [getElem?_set_ne _ _ hij]; exact hgetj
            have hnej' : pj ;; M Aj j σ' ≠ Effect.E := by rw [heffj]; exact hpj' ▸ hnej
            have step : IStepI M D j ⟨ths.set i (si', pi'), σ'⟩
                ⟨(ths.set i (si', pi')).set j (sj', pj ;; M Aj j σ'), σ'''⟩ :=
              IStepI.mk _ _ _ σ' σ''' pj _ hgetj2 (alj σ' σ''' hAjσ' hnej')
            exact (by rw [hpj', heffj] :
              (⟨(ths.set i (si', pi')).set j (sj', pj ;; M Aj j σ'), σ'''⟩ : IState)
                = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'''⟩) ▸ step
          · have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
              rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
            have hnei' : pi ;; M Ai i σj ≠ Effect.E := by rw [heffi]; exact hpi' ▸ hnei
            have step : IStepI M D i ⟨ths.set j (sj', pj'), σj⟩
                ⟨(ths.set j (sj', pj')).set i (si', pi ;; M Ai i σj), σ'''⟩ :=
              IStepI.mk _ _ _ σj σ''' pi _ hgeti2 (ali σj σ''' hAiσ'' hnei')
            refine (?_ : (⟨(ths.set j (sj', pj')).set i (si', pi ;; M Ai i σj), σ'''⟩ : IState)
                = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'''⟩) ▸ step
            have : (ths.set j (sj', pj')).set i (si', pi ;; M Ai i σj)
                = (ths.set i (si', pi')).set j (sj', pj') := by
              rw [heffi, hpi']; exact (set_comm ths _ _ hij).symm
            rw [this]
        · exact absurd ⟨sj', pj', getElem?_set_self_of _ _ (lt_of_getElem? hgetj), hwj⟩ hjok
    · -- i instrumented-wrong: reconstruct i wronging from j's post-store
      subst σ'; subst pi'
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        have hpjN' : pj = Effect.N := by
          have h : (sj0, pj0) = (sj, pj) := Option.some.inj (hgetj0.symm.trans hgetj)
          have hp2 : pj0 = pj := congrArg Prod.snd h
          rw [← hp2]; exact hpjN
        rcases ithreadstep_classify histep_j with
          ⟨hσj, replay_j⟩ | ⟨Aj, alj, hAj, hpj', hnej⟩ | ⟨hwj, _, _⟩
        · -- j structural: i re-fires from the same store σ
          subst σj
          refine ⟨⟨(ths.set i (si', pi)).set j (sj', pj'), σ⟩, ?_, ?_⟩
          · have hgetj2 : (ths.set i (si', pi))[j]? = some (sj, pj) := by
              rw [getElem?_set_ne _ _ hij]; exact hgetj
            exact IStepI.mk _ _ _ σ σ pj _ hgetj2 (replay_j σ)
          · have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
              rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
            have hire : IThreadStep M D i si σ pi si' σ pi := by
              rcases hrefire with ⟨A, hEσ, refire⟩ | ⟨A, σ0, hwit, hEσ, refire⟩
              · exact refire σ hEσ
              · exact refire σ σ0 hwit hEσ
            have step : IStepI M D i ⟨ths.set j (sj', pj'), σ⟩
                ⟨(ths.set j (sj', pj')).set i (si', pi), σ⟩ :=
              IStepI.mk _ _ _ σ σ pi _ hgeti2 hire
            exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
              (⟨(ths.set j (sj', pj')).set i (si', pi), σ⟩ : IState)
                = ⟨(ths.set i (si', pi)).set j (sj', pj'), σ⟩) ▸ step
        · -- j store-touching left-mover: i re-fires from σj (validity 3 + 4)
          have hmjL : M Aj j σ ⊑ Effect.L := seq_N_ne_E_imp_le_L (hpjN' ▸ hnej)
          have hmjN : M Aj j σ ⊑ Effect.N := le_trans hmjL (by decide)
          refine ⟨⟨(ths.set i (si', pi)).set j (sj', pj'), σj⟩, ?_, ?_⟩
          · have hgetj2 : (ths.set i (si', pi))[j]? = some (sj, pj) := by
              rw [getElem?_set_ne _ _ hij]; exact hgetj
            have step : IStepI M D j ⟨ths.set i (si', pi), σ⟩
                ⟨(ths.set i (si', pi)).set j (sj', pj ;; M Aj j σ), σj⟩ :=
              IStepI.mk _ _ _ σ σj pj _ hgetj2 (alj σ σj hAj hnej)
            exact (by rw [hpj'] :
              (⟨(ths.set i (si', pi)).set j (sj', pj ;; M Aj j σ), σj⟩ : IState)
                = ⟨(ths.set i (si', pi)).set j (sj', pj'), σj⟩) ▸ step
          · have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
              rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
            have hire : IThreadStep M D i si σj pi si' σj pi := by
              rcases hrefire with ⟨A, hEσ, refire⟩ | ⟨A, σ0, hwit, hEσ, refire⟩
              · have heff : M A i σj = M A i σ :=
                  hV.effect j i Aj A σ σj (M A i σ) (Ne.symm hij) hmjN hAj rfl
                exact refire σj (by rw [heff]; exact hEσ)
              · have heff : M A i σj = M A i σ :=
                  hV.effect j i Aj A σ σj (M A i σ) (Ne.symm hij) hmjN hAj rfl
                obtain ⟨σt, _, hAiσj⟩ :=
                  hV.nonblock i j A Aj σ σ0 σj hij (le_N_of_neverError hNE A i σ) hwit hmjL hAj
                exact refire σj σt hAiσj (by rw [heff]; exact hEσ)
            have step : IStepI M D i ⟨ths.set j (sj', pj'), σj⟩
                ⟨(ths.set j (sj', pj')).set i (si', pi), σj⟩ :=
              IStepI.mk _ _ _ σj σj pi _ hgeti2 hire
            exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
              (⟨(ths.set j (sj', pj')).set i (si', pi), σj⟩ : IState)
                = ⟨(ths.set i (si', pi)).set j (sj', pj'), σj⟩) ▸ step
        · exact absurd ⟨sj', pj', getElem?_set_self_of _ _ (lt_of_getElem? hgetj), hwj⟩ hjok

/-! ### Non-`j` runs

A run whose every step avoids thread `j` and never makes any thread wrong.  This
is the shape of the "main trace" that a post-commit termination run of thread
`j` is merged into (Iterative Diamond). -/

/-- A run in which every step is by a thread `≠ j` and no intermediate or final
    state is wrong. -/
inductive NonJRun (M : MoverSpec) (D : BodyEnv) (j : Tid) : IState → IState → Prop where
  | nil (P : IState) (hP : ¬ IWrong P) : NonJRun M D j P P
  | cons {P Pm Pe : IState} (t : Tid) (ht : t ≠ j) (h : IStepI M D t P Pm) (hP : ¬ IWrong P)
      (rest : NonJRun M D j Pm Pe) : NonJRun M D j P Pe

theorem NonJRun.toISteps {M D j} {a b : IState} (h : NonJRun M D j a b) : ISteps M D a b := by
  induction h with
  | nil => exact .refl _
  | cons t ht h _ _ ih => exact .step h.toIStep ih

/-- `¬ IWrong` of the source of a non-`j` run. -/
theorem NonJRun.src_not_wrong {M D j} {a b : IState} (h : NonJRun M D j a b) : ¬ IWrong a := by
  cases h with
  | nil _ hP => exact hP
  | cons _ _ _ hP _ => exact hP

/-- A non-`j` run preserves `j`'s post-commit class (class invariance at each step). -/
theorem NonJRun.clL_end {M D j} {a b : IState} (h : NonJRun M D j a b) (hL : clL a j) :
    clL b j := by
  induction h with
  | nil => exact hL
  | cons t ht hstep _ _ ih => exact ih (clL_invariant hstep (Ne.symm ht) hL)

/-- `clE Pa j` is impossible when `¬ IWrong Pa`. -/
theorem not_clE_of_not_wrong {Pa : IState} (h : ¬ IWrong Pa) (j : Tid) : ¬ clE Pa j :=
  fun hE => h (iwrong_iff_clE.2 ⟨j, hE⟩)

/-- A `j`-step out of a non-wrong state whose result keeps `j` non-wrong lands in
    a non-wrong state (other threads are untouched; `j` is non-wrong by `hjok`). -/
theorem jstep_not_wrong {M D j} {Pa Pj : IState} (h : IStepI M D j Pa Pj)
    (hP : ¬ IWrong Pa) (hjok : ¬ clE Pj j) : ¬ IWrong Pj := by
  intro hw
  obtain ⟨k, hkE⟩ := iwrong_iff_clE.1 hw
  by_cases hkj : k = j
  · exact hjok (hkj ▸ hkE)
  · refine hP (iwrong_iff_clE.2 ⟨k, ?_⟩)
    obtain ⟨s, p, hget, hw'⟩ := hkE
    exact ⟨s, p, (threads_get_invariant h hkj).symm.trans hget, hw'⟩

/-! ### Iterative Diamond

Push a single left-mover `j`-step through a whole `NonJRun`: it re-emerges as a
`j`-step off the *end* of the run, and the run replays from just after the
`j`-step.  By induction on the run, applying `diamond_commutes` at each cell;
class invariance keeps `j` post-commit throughout, and the commuted `j`-step
stays non-wrong because the reconverged state differs from the old `j`-result
only in the *other* thread's slot. -/

theorem push_j {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {j : Tid} :
    ∀ {Pa Pe : IState}, NonJRun M D j Pa Pe → ∀ {Pj : IState},
      clL Pa j → IStepI M D j Pa Pj → ¬ clE Pj j →
      ∃ Pe', IStepI M D j Pe Pe' ∧ NonJRun M D j Pj Pe' ∧ ¬ clE Pe' j := by
  intro Pa Pe hrun
  induction hrun with
  | nil P hP =>
      intro Pj hclL hjstep hjok
      exact ⟨Pj, hjstep, .nil Pj (jstep_not_wrong hjstep hP hjok), hjok⟩
  | @cons P Pm Pe t ht hstep hP hrest ih =>
      intro Pj hclL hjstep hjok
      have hiok : ¬ clE Pm t := not_clE_of_not_wrong hrest.src_not_wrong t
      obtain ⟨Pd, hjPm, htPj⟩ := diamond_commutes hV ht hstep hiok hclL hjstep hjok
      have hclLm : clL Pm j := clL_invariant hstep (Ne.symm ht) hclL
      have hjokd : ¬ clE Pd j := by
        intro hE
        obtain ⟨s, p, hget, hw⟩ := hE
        exact hjok ⟨s, p, (threads_get_invariant htPj (Ne.symm ht)).symm.trans hget, hw⟩
      obtain ⟨Pe', hje, hrest', hpe'⟩ := ih hclLm hjPm hjokd
      exact ⟨Pe', hje, .cons t ht htPj (jstep_not_wrong hjstep hP hjok) hrest', hpe'⟩

/-- A left-mover run of thread `a`: each step is `a`'s, from a post-commit state,
    landing non-wrong.  This is the shape of a post-commit termination run. -/
inductive LMRun (M : MoverSpec) (D : BodyEnv) (a : Tid) : IState → IState → Prop where
  | nil (P : IState) : LMRun M D a P P
  | cons {P Pm Pe : IState} (hL : clL P a) (h : IStepI M D a P Pm) (hok : ¬ clE Pm a)
      (rest : LMRun M D a Pm Pe) : LMRun M D a P Pe

/-- **Iterative Diamond.**  Push an entire left-mover run of `a` through a non-`a`
    run: the non-`a` run replays from the end of the `a`-run, and the `a`-run
    replays from the end of the non-`a` run.  By iterating `push_j`. -/
theorem iter_diamond {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {a : Tid} :
    ∀ {Pa Pfin : IState}, LMRun M D a Pa Pfin → ∀ {Pe : IState}, NonJRun M D a Pa Pe →
      ∃ Pe', NonJRun M D a Pfin Pe' ∧ LMRun M D a Pe Pe' := by
  intro Pa Pfin hlm
  induction hlm with
  | nil P => intro Pe hrun; exact ⟨Pe, hrun, .nil Pe⟩
  | @cons P Pm Pfin hL hstep hok hrest ih =>
      intro Pe hrun
      obtain ⟨Pe1, haStep, hrun1, hok1⟩ := push_j hV hrun hL hstep hok
      obtain ⟨Pe', hrun', hlm'⟩ := ih hrun1
      exact ⟨Pe', hrun', .cons (hrun.clL_end hL) haStep hok1 hlm'⟩

/-- Push a *wrong-reaching* step of thread `c` through a left-mover run of `a`:
    `c` still reaches wrong off the end of the run (each cell via the wrong-case
    Diamond `diamond_commutes_w`).  This is how the fatal step survives the merge
    of a post-commit termination run into the main trace. -/
theorem push_c_wrong {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M)
    {c a : Tid} (hca : c ≠ a) :
    ∀ {X Xfin : IState}, LMRun M D a X Xfin → ∀ {Y : IState},
      IStepI M D c X Y → clE Y c → ∃ Yfin, ISteps M D Xfin Yfin ∧ IWrong Yfin := by
  intro X Xfin hlm
  induction hlm with
  | nil P =>
      intro Y hc hYc
      exact ⟨Y, .step1 hc.toIStep, iwrong_iff_clE.2 ⟨c, hYc⟩⟩
  | @cons P Pm Xfin hL hastep hok hrest ih =>
      intro Y hc hYc
      obtain ⟨Pd, haY, hcPm⟩ := diamond_commutes_w hV hNE hca hc hL hastep hok
      exact ih hcPm (clE_step haY hYc)

theorem ISteps.trans {M D} {a b c : IState} (h1 : ISteps M D a b) (h2 : ISteps M D b c) :
    ISteps M D a c := by
  induction h1 with
  | refl => exact h2
  | step hstep _ ih => exact .step hstep (ih h2)

/-- **The merge.**  A post-commit termination run of `a` (`LMRun`) is merged into
    a non-`a` main trace that ends in the fatal step of another thread `c`: from
    the *end* of the `a`-run, the main trace replays and `c` still reaches wrong.
    This is `iter_diamond` (for the non-wrong prefix) followed by `push_c_wrong`
    (for the fatal step). -/
theorem merge_wrong {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M)
    {a c : Tid} (hca : c ≠ a) {P_a P_fin Pe_prev Pe : IState}
    (hlm : LMRun M D a P_a P_fin) (hrun : NonJRun M D a P_a Pe_prev)
    (hc : IStepI M D c Pe_prev Pe) (hPec : clE Pe c) :
    ∃ Pw, ISteps M D P_fin Pw ∧ IWrong Pw := by
  obtain ⟨Pe', hnonj, hlm'⟩ := iter_diamond hV hlm hrun
  obtain ⟨Yfin, hsteps, hwrong⟩ := push_c_wrong hV hNE hca hlm' hc hPec
  exact ⟨Yfin, ISteps.trans hnonj.toISteps hsteps, hwrong⟩

/-- Yielding and wrong are mutually exclusive statement shapes. -/
theorem yielding_not_wrong {s : Stmt} (h : yielding s) : ¬ IsWrong s := by
  intro hw
  have h1 : isStuck s = true := isStuck_of_isWrong hw
  have h2 : isStuck s = false := by
    rcases h with ⟨E, rfl⟩ | rfl
    · rw [isStuck_plug]; rfl
    · rfl
  rw [h1] at h2; exact Bool.noConfusion h2

/-- **Post-Commit Termination, as an `LMRun`.**  A post-commit thread of a
    verified state either runs (as a left-mover run) to a *yielding* state, or
    reaches *wrong* non-preemptively.  Same proof as `post_commit_term`, but
    exposing the per-step `LMRun` structure the merge needs. -/
theorem post_commit_lm {M : MoverSpec} {D : Decls}
    (hNY : NeverYields M) (hCT : CondTotal) {fs : FnName → Nat} (hfs : GoodSizing D fs) :
    ∀ (n : Nat) (Pi : IState) (i : Tid),
      IStateValid M D Pi → clL Pi i →
      (∀ s p, Pi.threads[i]? = some (s, p) → bodySize fs s ≤ n) →
      (∃ Pi', LMRun M D.bodies i Pi Pi' ∧ ∃ s p, Pi'.threads[i]? = some (s, p) ∧ yielding s) ∨
      (∃ Pw, INonSteps M D.bodies Pi Pw ∧ IWrong Pw) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro Pi i hval hL hsz
    obtain ⟨ths, σst⟩ := Pi
    obtain ⟨s_i, p_i, hget_i, hpN, hnot⟩ := hL
    subst hpN
    obtain ⟨R, G, a, σ0, hfns, hVal, hrefl, hanchor, hthreads, hcompat⟩ := hval
    obtain ⟨P, Q, e, hJ, hne, hQG, hpre⟩ := hthreads i s_i Effect.N hget_i
    by_cases hia : i = a
    · rw [if_pos hia] at hpre
      have heL : e ⊑ Effect.L := seq_N_ne_E_imp_le_L hne
      obtain ⟨s_i', σ', hstep, hsz'⟩ := progress hNY hCT hfs s_i R G P Q e σst hJ heL hpre hnot
      have hy : ∀ u su pu, u ≠ i → ths[u]? = some (su, pu) → yielding su := by
        intro u su pu hui hgetu
        obtain ⟨Pu, Qu, eu, hJu, hneu, hQGu, hpreu⟩ := hthreads u su pu hgetu
        rw [if_neg (hia ▸ hui)] at hpreu
        exact hpreu.1
      have hnonstep : INonStep M D.bodies ⟨ths, σst⟩ ⟨ths.set i (s_i', Effect.N), σ'⟩ :=
        INonStep.mk ths i s_i s_i' σst σ' Effect.N Effect.N hget_i hstep hy
      have histepI : IStepI M D.bodies i ⟨ths, σst⟩ ⟨ths.set i (s_i', Effect.N), σ'⟩ :=
        IStepI.mk ths s_i s_i' σst σ' Effect.N Effect.N hget_i hstep
      have hset_i : (ths.set i (s_i', Effect.N))[i]? = some (s_i', Effect.N) :=
        getElem?_set_self_of ths (s_i', Effect.N) (lt_of_getElem? hget_i)
      have hLsrc : clL (⟨ths, σst⟩ : IState) i := ⟨s_i, Effect.N, hget_i, rfl, hnot⟩
      by_cases hset : yielding s_i' ∨ IsWrong s_i'
      · rcases hset with hyield | hwrong
        · left
          have hok : ¬ clE (⟨ths.set i (s_i', Effect.N), σ'⟩ : IState) i := by
            rintro ⟨s, p, hg, hw⟩
            rw [hset_i] at hg
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hg
            exact yielding_not_wrong hyield hw
          exact ⟨⟨ths.set i (s_i', Effect.N), σ'⟩,
            LMRun.cons hLsrc histepI hok (.nil _), s_i', Effect.N, hset_i, hyield⟩
        · right
          exact ⟨⟨ths.set i (s_i', Effect.N), σ'⟩, INonSteps.step hnonstep (INonSteps.refl _),
            iwrong_iff_clE.2 ⟨i, s_i', Effect.N, hset_i, hwrong⟩⟩
      · have hval' : IStateValid M D ⟨ths.set i (s_i', Effect.N), σ'⟩ :=
          preservation ⟨R, G, a, σ0, hfns, hVal, hrefl, hanchor, hthreads, hcompat⟩ hnonstep
        have hlt : bodySize fs s_i' < n := Nat.lt_of_lt_of_le hsz' (hsz s_i Effect.N hget_i)
        have hok : ¬ clE (⟨ths.set i (s_i', Effect.N), σ'⟩ : IState) i := by
          rintro ⟨s, p, hg, hw⟩
          rw [hset_i] at hg
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hg
          exact hset (Or.inr hw)
        rcases ih (bodySize fs s_i') hlt ⟨ths.set i (s_i', Effect.N), σ'⟩ i hval'
            ⟨s_i', Effect.N, hset_i, rfl, hset⟩
            (by intro s p hgp
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hset_i.symm.trans hgp)
                exact Nat.le_refl _) with
          ⟨Pi'', hlm'', hy''⟩ | ⟨Pw, hsteps'', hwrong''⟩
        · exact Or.inl ⟨Pi'', LMRun.cons hLsrc histepI hok hlm'', hy''⟩
        · exact Or.inr ⟨Pw, INonSteps.step hnonstep hsteps'', hwrong''⟩
    · rw [if_neg hia] at hpre
      exact absurd (Or.inl hpre.1) hnot

/-! ### The post-commit bubble

Move a left-mover `a`-step that sits *after* a non-`a` prefix to the *front* of
that prefix, via `left_commutes` at each cell (a left-mover commutes before any
preceding non-wrong step; class invariance keeps `a` post-commit). -/

theorem bubble_left {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {a : Tid} :
    ∀ {P Pmid : IState}, NonJRun M D a P Pmid → clL P a →
      ∀ {Pnext : IState}, IStepI M D a Pmid Pnext → ¬ clE Pnext a →
      ∃ P', IStepI M D a P P' ∧ NonJRun M D a P' Pnext := by
  intro P Pmid hrun
  induction hrun with
  | nil Q hQ =>
      intro hclL Pnext ha haok
      exact ⟨Pnext, ha, .nil Pnext (jstep_not_wrong ha hQ haok)⟩
  | @cons Q Qm Pmid c hc hstep hQ hrest ih =>
      intro hclL Pnext ha haok
      have hclLm : clL Qm a := clL_invariant hstep (Ne.symm hc) hclL
      obtain ⟨Qm', haQm, hrestbub⟩ := ih hclLm ha haok
      have hcok : ¬ clE Qm c := not_clE_of_not_wrong hrest.src_not_wrong c
      have haok' : ¬ clE Qm' a := not_clE_of_not_wrong hrestbub.src_not_wrong a
      obtain ⟨Q', haQ, hcQ'⟩ := left_commutes hV hc hstep hcok hclLm haQm haok'
      have haokQ' : ¬ clE Q' a := by
        intro hE
        obtain ⟨s, p, hget, hw⟩ := hE
        exact haok' ⟨s, p, (threads_get_invariant hcQ' (Ne.symm hc)).trans hget, hw⟩
      exact ⟨Q', haQ, .cons c hc hcQ' (jstep_not_wrong haQ hQ haokQ') hrestbub⟩

/-! ### The pre-commit bubble

A "green" run: every step is by a thread `≠ a` that ends in phase `R` and
non-wrong (a right-mover/structural pre-commit step).  `bubble_green` moves an
`a`-step — *including a fatal one* — to the front of a green prefix, via
`right_commutes_w` at each cell.  Greenness is stable under the passing `a`-step
(class invariance), so the replayed run stays green. -/

inductive GreenRun (M : MoverSpec) (D : BodyEnv) (a : Tid) : IState → IState → Prop where
  | nil (P : IState) : GreenRun M D a P P
  | cons {P Pm Pe : IState} (t : Tid) (ht : t ≠ a) (h : IStepI M D t P Pm)
      (hg : ∃ s, Pm.threads[t]? = some (s, Effect.R) ∧ ¬ IsWrong s)
      (rest : GreenRun M D a Pm Pe) : GreenRun M D a P Pe

theorem GreenRun.toISteps {M D a} {x y : IState} (h : GreenRun M D a x y) : ISteps M D x y := by
  induction h with
  | nil => exact .refl _
  | cons t ht h hg rest ih => exact .step h.toIStep ih

theorem bubble_green {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M) {a : Tid} :
    ∀ {P Pmid : IState}, GreenRun M D a P Pmid →
      ∀ {Pnext : IState}, IStepI M D a Pmid Pnext →
      ∃ P', IStepI M D a P P' ∧ GreenRun M D a P' Pnext := by
  intro P Pmid hrun
  induction hrun with
  | nil Q => intro Pnext ha; exact ⟨Pnext, ha, .nil Pnext⟩
  | @cons Q Qm Pmid c hc hcstep hg hrest ih =>
      intro Pnext ha
      obtain ⟨Qm', haQm, hrestbub⟩ := ih ha
      obtain ⟨s0, hgs0, hns0⟩ := hg
      have hcok : ¬ clE Qm c := by
        rintro ⟨s, p, hgg, hw⟩
        rw [hgs0] at hgg
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hgg
        exact hns0 hw
      obtain ⟨Q', haQ, hcQ'⟩ := right_commutes_w hV hNE hc hcstep ⟨s0, hgs0⟩ hcok haQm
      refine ⟨Q', haQ, .cons c hc hcQ' ⟨s0, ?_, hns0⟩ hrestbub⟩
      exact (threads_get_invariant haQm hc).trans hgs0

/-! ### Transaction extraction

`ARun` is a run of `a`-steps only.  `push_green_back` moves a single green step
past a whole `a`-run (each cell via the wrong-case Right Commutativity), and
`partition_green` uses it to split a run of `a`-steps interleaved with green
non-`a` steps into `(a-run ; green-run)` — i.e. it pulls thread `a`'s entire
(pre-commit through fatal) transaction to the front. -/

inductive ARun (M : MoverSpec) (D : BodyEnv) (a : Tid) : IState → IState → Prop where
  | nil (P : IState) : ARun M D a P P
  | cons {P Pm Pe : IState} (h : IStepI M D a P Pm) (rest : ARun M D a Pm Pe) : ARun M D a P Pe

theorem ARun.toINonSteps_or {M D a} {x y : IState} (h : ARun M D a x y) : ISteps M D x y := by
  induction h with
  | nil => exact .refl _
  | cons h _ ih => exact .step h.toIStep ih

theorem ARun.trans {M D a} {x y z : IState} (h1 : ARun M D a x y) (h2 : ARun M D a y z) :
    ARun M D a x z := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h (ih h2)

/-- Move a green non-`a` step to *after* an `a`-run (bubble it back). -/
theorem push_green_back {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M)
    {a t : Tid} (ht : t ≠ a) :
    ∀ {Pm Pmid : IState}, ARun M D a Pm Pmid → ∀ {P : IState}, IStepI M D t P Pm →
      (∃ s, Pm.threads[t]? = some (s, Effect.R) ∧ ¬ IsWrong s) →
      ∃ P', ARun M D a P P' ∧ IStepI M D t P' Pmid ∧
        (∃ s, Pmid.threads[t]? = some (s, Effect.R) ∧ ¬ IsWrong s) := by
  intro Pm Pmid harun
  induction harun with
  | nil Q => intro P hg hgreen; exact ⟨P, .nil P, hg, hgreen⟩
  | @cons Q Qa Pmid hastep hrest ih =>
      intro P hg hgreen
      obtain ⟨s0, hgs0, hns0⟩ := hgreen
      have hcok : ¬ clE Q t := by
        rintro ⟨s, p, hgg, hw⟩
        rw [hgs0] at hgg
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hgg
        exact hns0 hw
      obtain ⟨P1, haP1, htQa⟩ := right_commutes_w hV hNE ht hg ⟨s0, hgs0⟩ hcok hastep
      have hgreenQa : ∃ s, Qa.threads[t]? = some (s, Effect.R) ∧ ¬ IsWrong s :=
        ⟨s0, (threads_get_invariant hastep ht).trans hgs0, hns0⟩
      obtain ⟨P', harP', htPmid, hgreenPmid⟩ := ih htQa hgreenQa
      exact ⟨P', .cons haP1 harP', htPmid, hgreenPmid⟩

/-- A run of `a`-steps interleaved with green non-`a` steps. -/
inductive GAMix (M : MoverSpec) (D : BodyEnv) (a : Tid) : IState → IState → Prop where
  | nil (P : IState) : GAMix M D a P P
  | consA {P Pm Pe : IState} (h : IStepI M D a P Pm) (rest : GAMix M D a Pm Pe) : GAMix M D a P Pe
  | consG {P Pm Pe : IState} (t : Tid) (ht : t ≠ a) (h : IStepI M D t P Pm)
      (hg : ∃ s, Pm.threads[t]? = some (s, Effect.R) ∧ ¬ IsWrong s)
      (rest : GAMix M D a Pm Pe) : GAMix M D a P Pe

/-- Split a green-interleaved run into `a`'s transaction followed by a green run. -/
theorem partition_green {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M) {a : Tid} :
    ∀ {P Pe : IState}, GAMix M D a P Pe →
      ∃ Pmid, ARun M D a P Pmid ∧ GreenRun M D a Pmid Pe := by
  intro P Pe h
  induction h with
  | nil P => exact ⟨P, .nil P, .nil P⟩
  | @consA P Pm Pe hstep rest ih =>
      obtain ⟨Pmid, harun, hgreen⟩ := ih
      exact ⟨Pmid, .cons hstep harun, hgreen⟩
  | @consG P Pm Pe t ht hstep hg rest ih =>
      obtain ⟨Pmid, harun, hgreen⟩ := ih
      obtain ⟨P', harun', htP', hgreenPmid⟩ := push_green_back hV hNE ht harun hstep hg
      exact ⟨P', harun', .cons t ht htP' hgreenPmid hgreen⟩

/-! ### Post-commit transaction extraction

The left-mover analogue of `partition_green`: `push_left_back` moves a non-`a`
step past an `a` left-mover run (via `left_commutes`), and `partition_left`
splits a run of `a` left-mover steps interleaved with non-`a` steps into
`(LMRun ; non-a run)` — extracting a post-commit thread's remaining transaction. -/

theorem push_left_back {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {a t : Tid} (ht : t ≠ a) :
    ∀ {Pm Pmid : IState}, LMRun M D a Pm Pmid → ∀ {P : IState},
      IStepI M D t P Pm → ¬ clE Pm t →
      ∃ P', LMRun M D a P P' ∧ IStepI M D t P' Pmid ∧ ¬ clE Pmid t := by
  intro Pm Pmid hlm
  induction hlm with
  | nil Q => intro P htstep hcok; exact ⟨P, .nil P, htstep, hcok⟩
  | @cons Q Qa Pmid hL hastep hok hrest ih =>
      intro P htstep hcok
      obtain ⟨P1, haP1, htQa⟩ := left_commutes hV ht htstep hcok hL hastep hok
      have hLP : clL P a := by
        obtain ⟨s, p, hg, hpN, hns⟩ := hL
        exact ⟨s, p, (threads_get_invariant htstep (Ne.symm ht)).symm.trans hg, hpN, hns⟩
      have hokP1 : ¬ clE P1 a := by
        rintro ⟨s, p, hg, hw⟩
        exact hok ⟨s, p, (threads_get_invariant htQa (Ne.symm ht)).trans hg, hw⟩
      have hcokQa : ¬ clE Qa t := by
        rintro ⟨s, p, hg, hw⟩
        exact hcok ⟨s, p, (threads_get_invariant hastep ht).symm.trans hg, hw⟩
      obtain ⟨P', hlmP', htP', hcokPmid⟩ := ih htQa hcokQa
      exact ⟨P', .cons hLP haP1 hokP1 hlmP', htP', hcokPmid⟩

/-- A run of `a` left-mover steps interleaved with non-`a` steps (all non-wrong). -/
inductive LAMix (M : MoverSpec) (D : BodyEnv) (a : Tid) : IState → IState → Prop where
  | nil (P : IState) : LAMix M D a P P
  | consA {P Pm Pe : IState} (hL : clL P a) (h : IStepI M D a P Pm) (hok : ¬ clE Pm a)
      (rest : LAMix M D a Pm Pe) : LAMix M D a P Pe
  | consN {P Pm Pe : IState} (t : Tid) (ht : t ≠ a) (h : IStepI M D t P Pm) (hok : ¬ clE Pm t)
      (rest : LAMix M D a Pm Pe) : LAMix M D a P Pe

/-- Split a left-mover-interleaved run into `a`'s post-commit run then a non-`a`
    run.  The non-`a` run's steps are all `¬ clE`, but we return it as an
    `IStepsT` tagged run (wrong-freeness of whole states is threaded separately). -/
theorem partition_left {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {a : Tid} :
    ∀ {P Pe : IState}, LAMix M D a P Pe →
      ∃ Pmid, LMRun M D a P Pmid ∧ IStepsT M D Pmid Pe := by
  intro P Pe h
  induction h with
  | nil P => exact ⟨P, .nil P, .nil P⟩
  | @consA P Pm Pe hL hstep hok rest ih =>
      obtain ⟨Pmid, hlm, hnon⟩ := ih
      exact ⟨Pmid, .cons hL hstep hok hlm, hnon⟩
  | @consN P Pm Pe t ht hstep hok rest ih =>
      obtain ⟨Pmid, hlm, hnon⟩ := ih
      obtain ⟨P', hlm', htP', _⟩ := push_left_back hV ht hlm hstep hok
      exact ⟨P', hlm', .cons t htP' hnon⟩

/-! ### The phase invariant

Every thread's phase stays in `{R, N}` along the semantics (from all-yielding
states, whose phases are `R`).  This is what lets the block decomposition read a
non-green step as either wrong or a *commit* (phase `N`).  `PhaseRN` is defined in
`Instrumented`. -/

theorem seq_RN_of {p M : Effect} (hp : p = Effect.R ∨ p = Effect.N) (hne : p ;; M ≠ Effect.E) :
    p ;; M = Effect.R ∨ p ;; M = Effect.N := by
  rcases hp with rfl | rfl <;> cases M <;> simp_all [Effect.seq]

theorem PhaseRN.step {M D t} {P Pm : IState} (h : IStepI M D t P Pm) (hP : PhaseRN P) :
    PhaseRN Pm := by
  cases h with
  | mk ths s s' σ σ' p p' hget hstep =>
    intro u su pu hgetu
    by_cases hut : u = t
    · rw [hut, getElem?_set_self_of ths (s', p') (lt_of_getElem? hget)] at hgetu
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hgetu
      have hpRN : p = Effect.R ∨ p = Effect.N := hP t s p hget
      cases hstep with
      | iseq _ _ _ _ => exact hpRN
      | iyield _ _ _ => exact Or.inl rfl
      | iwhile _ _ _ _ _ => exact hpRN
      | icall _ _ _ _ _ _ => exact hpRN
      | iaction_ok _ A σ σ' p hA hne => exact seq_RN_of hpRN hne
      | iaction_wrong _ _ _ _ _ => exact hpRN
      | iif_ok_T _ C s1 s2 σ σ' p hA hne => exact seq_RN_of hpRN hne
      | iif_ok_F _ C s1 s2 σ σ' p hA hne => exact seq_RN_of hpRN hne
      | iif_wrong_T _ _ _ _ _ _ _ _ => exact hpRN
      | iif_wrong_F _ _ _ _ _ _ _ _ => exact hpRN
    · rw [getElem?_set_ne _ _ (Ne.symm hut)] at hgetu; exact hP u su pu hgetu

/-- A step sets its own thread's slot. -/
theorem istep_result {M D t} {P Pm : IState} (h : IStepI M D t P Pm) :
    ∃ s' p', Pm.threads[t]? = some (s', p') := by
  cases h with
  | mk ths s s' σ σ' p p' hget hstep =>
    exact ⟨s', p', getElem?_set_self_of ths (s', p') (lt_of_getElem? hget)⟩

/-- **Green decomposition** (the `(form:b)` prefix).  Any run from a non-wrong,
    phase-`{R,N}` state to a wrong state factors as `GAMix a` (thread `a`'s
    pre-commit transaction — `a`-steps interleaved with green non-`a` steps) up
    to `a`'s first non-green step, followed by the rest; and at that point `a`
    is either wrong or committed (phase `N`). -/
theorem green_decompose {M D} :
    ∀ {Pi Pe : IState}, IStepsT M D Pi Pe → ¬ IWrong Pi → IWrong Pe → PhaseRN Pi →
      ∃ (a : Tid) (Q : IState), GAMix M D a Pi Q ∧ IStepsT M D Q Pe ∧
        (clE Q a ∨ ∃ s, Q.threads[a]? = some (s, Effect.N)) ∧ PhaseRN Q := by
  intro Pi Pe hrun
  induction hrun with
  | nil P => intro hnw hw _; exact absurd hw hnw
  | @cons P Pm Pe t hstep hrest ih =>
      intro hnw hw hphase
      by_cases hgreen : ∃ s, Pm.threads[t]? = some (s, Effect.R) ∧ ¬ IsWrong s
      · obtain ⟨s0, hg0, hns0⟩ := hgreen
        have hcokm : ¬ clE Pm t := by
          rintro ⟨s, p, hgg, hw'⟩
          rw [hg0] at hgg
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hgg
          exact hns0 hw'
        have hnwm : ¬ IWrong Pm := jstep_not_wrong hstep hnw hcokm
        have hphasem : PhaseRN Pm := PhaseRN.step hstep hphase
        obtain ⟨a, Q, hgamix, hrest', hend, hphaseQ⟩ := ih hnwm hw hphasem
        by_cases hta : t = a
        · subst hta; exact ⟨t, Q, .consA hstep hgamix, hrest', hend, hphaseQ⟩
        · exact ⟨a, Q, .consG t hta hstep ⟨s0, hg0, hns0⟩ hgamix, hrest', hend, hphaseQ⟩
      · obtain ⟨s', p', hres⟩ := istep_result hstep
        have hphasem : PhaseRN Pm := PhaseRN.step hstep hphase
        have hp'RN : p' = Effect.R ∨ p' = Effect.N := hphasem t s' p' hres
        refine ⟨t, Pm, .consA hstep (.nil Pm), hrest, ?_, hphasem⟩
        by_cases hws' : IsWrong s'
        · exact Or.inl ⟨s', p', hres, hws'⟩
        · have hp'N : p' = Effect.N := by
            rcases hp'RN with hR | hN
            · exact absurd ⟨s', hR ▸ hres, hws'⟩ hgreen
            · exact hN
          exact Or.inr ⟨s', hp'N ▸ hres⟩

/-! ### Wrong-case Left Commutativity

`left_commutes_w` drops the `¬ clE Pc j` hypothesis of `left_commutes`.  An
assertion (`I-if` landing on a `wrong` statement) is an *ok* store-touching step,
already handled by that branch; an instrumented-wrong *action* step
(`iaction_wrong`) is reconstructed on the swapped store, its error effect carried
by validity (3) (no branch witness needed).  For a verified post-commit thread an
instrumented-wrong *conditional* step cannot arise (both branches are `⊑ L`), so
`hjno_iif` — that `j`'s step is not `iif_wrong`-shaped — is a vacuous side
condition supplied by the caller. -/

theorem left_commutes_w {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {i j : Tid}
    (hij : i ≠ j) {Pa Pb Pc : IState}
    (hi : IStepI M D i Pa Pb) (hiok : ¬ clE Pb i)
    (hclL : clL Pb j) (hj : IStepI M D j Pb Pc)
    (hjno_iif : ∀ (A : Action) (sj0 pj0 : _), Pb.threads[j]? = some (sj0, pj0) →
      ∀ σ0, A j Pb.store σ0 → pj0 ;; M A j Pb.store ≠ Effect.E) :
    ∃ Pd, IStepI M D j Pa Pd ∧ IStepI M D i Pd Pc := by
  cases hi with
  | mk ths si si' σ σ' pi pi' hgeti histep_i =>
    have hilt : i < ths.length := lt_of_getElem? hgeti
    rcases ithreadstep_classify histep_i with
      ⟨hσ, replay_i⟩ | ⟨Ai, ali, hAi, hpi', hnei⟩ | ⟨hw, _, _⟩
    · subst σ'
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
        exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
          (⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ : IState)
            = ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩) ▸ step
    · have hmiN : M Ai i σ ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnei)
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
          ⟨hσj, replay_j⟩ | ⟨Aj, alj, hAj, hpj', hnej⟩ | ⟨hwj, hσj, hpj, hrefire⟩
        · subst σj
          refine ⟨⟨ths.set j (sj', pj'), σ⟩,
            IStepI.mk ths _ _ σ σ pj _ hgetjb (replay_j σ), ?_⟩
          have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
            rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
          have step : IStepI M D i ⟨ths.set j (sj', pj'), σ⟩
              ⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ :=
            IStepI.mk (ths.set j (sj', pj')) _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
          exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
            (⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ : IState)
              = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'⟩) ▸ step
        · have hmjL : M Aj j σ' ⊑ Effect.L := seq_N_ne_E_imp_le_L (hpjN' ▸ hnej)
          obtain ⟨σ''', hAjσ, hAiσ'''⟩ := hV.left i j Ai Aj σ σ' σj hij hmiN hAi hmjL hAj
          obtain ⟨_, _, D3, D4⟩ :=
            diamond_core_I hV hij hgeti hgetjb ali alj hmiN hAi (hpi' ▸ hnei) hAj hnej hAjσ hAiσ'''
          refine ⟨_, D3, ?_⟩
          rw [hpi', hpj']; exact D4
        · -- j instrumented-wrong: only `iaction_wrong` (effect carried by validity 3)
          subst σj; subst pj'
          have hgetPbj : (ths.set i (si', pi'))[j]? = some (sj, pj) := by
            rw [getElem?_set_ne _ _ hij]; exact hgetjb
          refine ⟨⟨ths.set j (sj', pj), σ⟩, ?_, ?_⟩
          · have hjstep : IThreadStep M D j sj σ pj sj' σ pj := by
              rcases hrefire with ⟨A, hEσ', refire⟩ | ⟨A, σ0, hwit, hEσ', refire⟩
              · have heff : M A j σ = M A j σ' :=
                  (hV.effect i j Ai A σ σ' (M A j σ) hij hmiN hAi rfl).symm
                exact refire σ (by rw [heff]; exact hEσ')
              · exact absurd hEσ' (hjno_iif A sj pj hgetPbj σ0 hwit)
            exact IStepI.mk ths _ _ σ σ pj _ hgetjb hjstep
          · have hgeti2 : (ths.set j (sj', pj))[i]? = some (si, pi) := by
              rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
            have step : IStepI M D i ⟨ths.set j (sj', pj), σ⟩
                ⟨(ths.set j (sj', pj)).set i (si', pi'), σ'⟩ :=
              IStepI.mk (ths.set j (sj', pj)) _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
            exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
              (⟨(ths.set j (sj', pj)).set i (si', pi'), σ'⟩ : IState)
                = ⟨(ths.set i (si', pi')).set j (sj', pj), σ'⟩) ▸ step
    · exact absurd ⟨si', pi', getElem?_set_self_of ths (si', pi') hilt, hw⟩ hiok

/-- Like `ithreadstep_classify`, but the instrumented-wrong bucket exposes whether
    the wrong step is an *action* (`iaction_wrong`, with a re-fire rule) or a
    *conditional* (`iif_wrong`, exposing the branch whose composition is `E`).
    This lets `left_commutes_w'` discharge the conditional case with a dischargeable
    `hjno_iif`.  Proved standalone (no shared store), so `cases` is unproblematic. -/
theorem ithreadstep_classify2 {M D t} {s : Stmt} {σ : Store} {p : Phase}
    {s' : Stmt} {σ' : Store} {p' : Phase}
    (h : IThreadStep M D t s σ p s' σ' p') :
    (σ' = σ ∧ ∀ σx, IThreadStep M D t s σx p s' σx p') ∨
    (∃ A : Action, ActionLike M D t s s' A p ∧ A t σ σ' ∧
        p' = p ;; M A t σ ∧ p ;; M A t σ ≠ Effect.E) ∨
    (IsWrong s' ∧ σ' = σ ∧ p' = p ∧
      ((∃ (E : Ctx) (A : Action), s = E.plug (.act A) ∧ p ;; M A t σ = Effect.E ∧
          ∀ τ, p ;; M A t τ = Effect.E → IThreadStep M D t s τ p s' τ p) ∨
       (∃ (E : Ctx) (C : CondAction) (s1 s2 : Stmt), s = E.plug (.ite C s1 s2) ∧
          (p ;; M C.tru t σ = Effect.E ∨ p ;; M C.fls t σ = Effect.E)))) := by
  cases h with
  | iseq E s0 σ0 p0 => exact Or.inl ⟨rfl, fun σx => .iseq E s0 σx p⟩
  | iyield E σ0 p0 => exact Or.inl ⟨rfl, fun σx => .iyield E σx p⟩
  | iwhile E C s0 σ0 p0 => exact Or.inl ⟨rfl, fun σx => .iwhile E C s0 σx p⟩
  | icall E f s0 σ0 p0 hbody => exact Or.inl ⟨rfl, fun σx => .icall E f s0 σx p hbody⟩
  | iaction_ok E A σ0 σ0' p0 hA hne =>
      exact Or.inr (Or.inl ⟨A, actionLike_action, hA, rfl, hne⟩)
  | iif_ok_T E C s1 s2 σ0 σ0' p0 hA hne =>
      exact Or.inr (Or.inl ⟨C.tru, actionLike_ite_tru, hA, rfl, hne⟩)
  | iif_ok_F E C s1 s2 σ0 σ0' p0 hA hne =>
      exact Or.inr (Or.inl ⟨C.fls, actionLike_ite_fls, hA, rfl, hne⟩)
  | iaction_wrong E A σ0 p0 hp =>
      exact Or.inr (Or.inr ⟨⟨E, rfl⟩, rfl, rfl,
        Or.inl ⟨E, A, rfl, hp, fun τ hτ => IThreadStep.iaction_wrong E A τ p hτ⟩⟩)
  | iif_wrong_T E C s1 s2 σ0 σ0' p0 hA hp =>
      exact Or.inr (Or.inr ⟨⟨E, rfl⟩, rfl, rfl, Or.inr ⟨E, C, s1, s2, rfl, Or.inl hp⟩⟩)
  | iif_wrong_F E C s1 s2 σ0 σ0' p0 hA hp =>
      exact Or.inr (Or.inr ⟨⟨E, rfl⟩, rfl, rfl, Or.inr ⟨E, C, s1, s2, rfl, Or.inr hp⟩⟩)

/-- **Wrong-case Left Commutativity, dischargeable form.**  Same as
    `left_commutes_w` but with a `hjno_iif` a caller can discharge (via
    `interfered_branches_ne_E`): rather than the over-general `∀ A`, it asks only
    that `j`'s *conditional* redex (if any) has both branch movers compose `≠ E`.
    Uses `ithreadstep_classify2` so the `iif`-wrong case exposes the conditional. -/
theorem left_commutes_w' {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {i j : Tid}
    (hij : i ≠ j) {Pa Pb Pc : IState}
    (hi : IStepI M D i Pa Pb) (hiok : ¬ clE Pb i)
    (hclL : clL Pb j) (hj : IStepI M D j Pb Pc)
    (hjno_iif : ∀ (C : CondAction) (s1 s2 : Stmt) (E' : Ctx),
      Pb.threads[j]? = some (E'.plug (.ite C s1 s2), Effect.N) →
      Effect.N ;; M C.tru j Pb.store ≠ Effect.E ∧ Effect.N ;; M C.fls j Pb.store ≠ Effect.E) :
    ∃ Pd, IStepI M D j Pa Pd ∧ IStepI M D i Pd Pc := by
  cases hi with
  | mk ths si si' σ σ' pi pi' hgeti histep_i =>
    have hilt : i < ths.length := lt_of_getElem? hgeti
    rcases ithreadstep_classify histep_i with
      ⟨hσ, replay_i⟩ | ⟨Ai, ali, hAi, hpi', hnei⟩ | ⟨hw, _, _⟩
    · subst σ'
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
        exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
          (⟨(ths.set j (sj', pj')).set i (si', pi'), σj⟩ : IState)
            = ⟨(ths.set i (si', pi')).set j (sj', pj'), σj⟩) ▸ step
    · have hmiN : M Ai i σ ⊑ Effect.N := le_N_of_ne_E (seq_arg_ne_E hnei)
      obtain ⟨s0, p0, hget0, hpjN, _⟩ := hclL
      cases hj with
      | mk ths2 sj sj' σa σj pj pj' hgetj histep_j =>
        have hgetjb : ths[j]? = some (sj, pj) := by
          rw [← getElem?_set_ne ths (si', pi') hij]; exact hgetj
        have hpjN' : pj = Effect.N := by
          have h : (s0, p0) = (sj, pj) := Option.some.inj (hget0.symm.trans hgetj)
          have hp : p0 = pj := congrArg Prod.snd h
          rw [← hp]; exact hpjN
        rcases ithreadstep_classify2 histep_j with
          ⟨hσj, replay_j⟩ | ⟨Aj, alj, hAj, hpj', hnej⟩ | ⟨hwj, hσj, hpj, hrefire⟩
        · subst σj
          refine ⟨⟨ths.set j (sj', pj'), σ⟩,
            IStepI.mk ths _ _ σ σ pj _ hgetjb (replay_j σ), ?_⟩
          have hgeti2 : (ths.set j (sj', pj'))[i]? = some (si, pi) := by
            rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
          have step : IStepI M D i ⟨ths.set j (sj', pj'), σ⟩
              ⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ :=
            IStepI.mk (ths.set j (sj', pj')) _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
          exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
            (⟨(ths.set j (sj', pj')).set i (si', pi'), σ'⟩ : IState)
              = ⟨(ths.set i (si', pi')).set j (sj', pj'), σ'⟩) ▸ step
        · have hmjL : M Aj j σ' ⊑ Effect.L := seq_N_ne_E_imp_le_L (hpjN' ▸ hnej)
          obtain ⟨σ''', hAjσ, hAiσ'''⟩ := hV.left i j Ai Aj σ σ' σj hij hmiN hAi hmjL hAj
          obtain ⟨_, _, D3, D4⟩ :=
            diamond_core_I hV hij hgeti hgetjb ali alj hmiN hAi (hpi' ▸ hnei) hAj hnej hAjσ hAiσ'''
          refine ⟨_, D3, ?_⟩
          rw [hpi', hpj']; exact D4
        · subst σj; subst pj'
          refine ⟨⟨ths.set j (sj', pj), σ⟩, ?_, ?_⟩
          · have hjstep : IThreadStep M D j sj σ pj sj' σ pj := by
              rcases hrefire with ⟨E0, A, hsj, hEσ', refire⟩ | ⟨E0, C0, s1, s2, hsj, hbr⟩
              · have heff : M A j σ = M A j σ' :=
                  (hV.effect i j Ai A σ σ' (M A j σ) hij hmiN hAi rfl).symm
                exact refire σ (by rw [heff]; exact hEσ')
              · have hget_Pb : (ths.set i (si', pi'))[j]? =
                    some (E0.plug (.ite C0 s1 s2), Effect.N) := by
                  rw [getElem?_set_ne _ _ hij, ← hsj, ← hpjN']; exact hgetjb
                rcases hbr with hbr | hbr
                · exact absurd (hpjN' ▸ hbr) (hjno_iif C0 s1 s2 E0 hget_Pb).1
                · exact absurd (hpjN' ▸ hbr) (hjno_iif C0 s1 s2 E0 hget_Pb).2
            exact IStepI.mk ths _ _ σ σ pj _ hgetjb hjstep
          · have hgeti2 : (ths.set j (sj', pj))[i]? = some (si, pi) := by
              rw [getElem?_set_ne _ _ (Ne.symm hij)]; exact hgeti
            have step : IStepI M D i ⟨ths.set j (sj', pj), σ⟩
                ⟨(ths.set j (sj', pj)).set i (si', pi'), σ'⟩ :=
              IStepI.mk (ths.set j (sj', pj)) _ _ σ σ' pi _ hgeti2 (hpi' ▸ ali σ σ' hAi (hpi' ▸ hnei))
            exact (by rw [set_comm ths _ _ (Ne.symm hij)] :
              (⟨(ths.set j (sj', pj)).set i (si', pi'), σ'⟩ : IState)
                = ⟨(ths.set i (si', pi')).set j (sj', pj), σ'⟩) ▸ step
    · exact absurd ⟨si', pi', getElem?_set_self_of ths (si', pi') hilt, hw⟩ hiok

/-! ### From an extracted `a`-run to a non-preemptive run

While a single thread `a` is active and all others yield, an `a`-run is a
non-preemptive run.  `OthersYield` is that invariant; it is preserved by `a`'s
steps. -/

/-- The model well-formedness the paper assumes (`NeverYields`, `CondTotal`,
    non-recursive atomic functions via a `GoodSizing` witness, and `NeverError`). -/
structure WF (M : MoverSpec) (D : Decls) : Prop where
  neverYields : NeverYields M
  condTotal : CondTotal
  neverError : NeverError M
  sizing : ∃ fs : FnName → Nat, GoodSizing D fs

def OthersYield (Q : IState) (a : Tid) : Prop :=
  ∀ (u : Tid) (su : Stmt) (pu : Phase), u ≠ a → Q.threads[u]? = some (su, pu) → yielding su

theorem OthersYield.step {M Db a} {P Pm : IState} (h : IStepI M Db a P Pm)
    (hO : OthersYield P a) : OthersYield Pm a := by
  intro u su pu hua hgetu
  cases h with
  | mk ths s s' σ σ' p p' hget hstep =>
    rw [getElem?_set_ne _ _ (Ne.symm hua)] at hgetu
    exact hO u su pu hua hgetu

theorem istep_to_inonstep {M Db a} {P Pm : IState} (h : IStepI M Db a P Pm)
    (hO : OthersYield P a) : INonStep M Db P Pm := by
  cases h with
  | mk ths s s' σ σ' p p' hget hstepT =>
    exact INonStep.mk ths a s s' σ σ' p p' hget hstepT
      (fun u su pu hua hgetu => hO u su pu hua hgetu)

theorem ARun.toINonSteps {M Db a} {P Pe : IState} (h : ARun M Db a P Pe)
    (hO : OthersYield P a) : INonSteps M Db P Pe := by
  induction h with
  | nil => exact .refl _
  | @cons P Pm Pe hstep rest ih =>
      exact .step (istep_to_inonstep hstep hO) (ih (OthersYield.step hstep hO))

theorem INonSteps.trans {M Db} {a b c : IState} (h1 : INonSteps M Db a b)
    (h2 : INonSteps M Db b c) : INonSteps M Db a c := by
  induction h1 with
  | refl => exact h2
  | step hstep _ ih => exact .step hstep (ih h2)

/-! ### Length-indexed runs (for the outer induction's measure)

`ISteps` is a `Prop`, so no `Nat` length can be extracted from it.  `IStepsTn n`
is a run of exactly `n` steps; `ISteps` yields *some* `n`, and the extraction
shortens `n`, giving a well-founded measure. -/

inductive IStepsTn (M : MoverSpec) (Db : BodyEnv) : Nat → IState → IState → Prop where
  | nil (P : IState) : IStepsTn M Db 0 P P
  | cons {n P Pm Pe} (t : Tid) (h : IStepI M Db t P Pm) (rest : IStepsTn M Db n Pm Pe) :
      IStepsTn M Db (n + 1) P Pe

theorem ISteps.toN {M Db} {a b : IState} (h : ISteps M Db a b) : ∃ n, IStepsTn M Db n a b := by
  induction h with
  | refl => exact ⟨0, .nil _⟩
  | step hstep _ ih => obtain ⟨t, ht⟩ := hstep.exists_tid; obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .cons t ht hn⟩

theorem IStepsTn.toISteps {M Db n} {a b : IState} (h : IStepsTn M Db n a b) : ISteps M Db a b := by
  induction h with
  | nil => exact .refl _
  | cons t hstep _ ih => exact .step hstep.toIStep ih

theorem IStepsTn.src_not_wrong_of {M Db n} {a b : IState} : IStepsTn M Db n a b → True := fun _ => trivial

/-- A run preserves `OthersYield` of thread `a` across an `a`-run. -/
theorem ARun.othersYield_end {M Db a} {P Pe : IState} (h : ARun M Db a P Pe)
    (hO : OthersYield P a) : OthersYield Pe a := by
  induction h with
  | nil => exact hO
  | cons hstep _ ih => exact ih (OthersYield.step hstep hO)

/-- An `a`-run preserves `PhaseRN`. -/
theorem ARun.phaseRN {M D a} {P Pe : IState} (h : ARun M D a P Pe) (hP : PhaseRN P) :
    PhaseRN Pe := by
  induction h with
  | nil => exact hP
  | cons hstep _ ih => exact ih (PhaseRN.step hstep hP)

/-- **Length-indexed transaction extraction** (`green_decompose` + `partition_green`
    fused, tracking run length).  From a length-`n` run to a wrong state, extract
    the first committing thread `a`'s entire pre-commit-through-commit transaction
    as an `ARun` to `Pc`, leaving a *strictly shorter* (`m < n`) run `Pc ⟶* Pe`;
    at `Pc` thread `a` is wrong or committed (phase `N`).  The length shrinks
    because the extracted transaction has at least one step and the recursion's
    residual is strictly shorter. -/
theorem extract_committer {M D} (hV : Valid M) (hNE : NeverError M) :
    ∀ {n} {Pi Pe : IState}, IStepsTn M D n Pi Pe → ¬ IWrong Pi → IWrong Pe → PhaseRN Pi →
      ∃ (a : Tid) (Pc : IState) (m : Nat),
        ARun M D a Pi Pc ∧ IStepsTn M D m Pc Pe ∧ m < n ∧
        (clE Pc a ∨ ∃ s, Pc.threads[a]? = some (s, Effect.N)) ∧ PhaseRN Pc := by
  intro n Pi Pe hrun
  induction hrun with
  | nil P => intro hnw hw _; exact absurd hw hnw
  | @cons n' P Pm Pe t hstep hrest ih =>
      intro hnw hw hphase
      by_cases hgreen : ∃ s, Pm.threads[t]? = some (s, Effect.R) ∧ ¬ IsWrong s
      · obtain ⟨s0, hg0, hns0⟩ := hgreen
        have hcokm : ¬ clE Pm t := by
          rintro ⟨s, p, hgg, hw'⟩
          rw [hg0] at hgg
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hgg
          exact hns0 hw'
        have hnwm : ¬ IWrong Pm := jstep_not_wrong hstep hnw hcokm
        have hphasem : PhaseRN Pm := PhaseRN.step hstep hphase
        obtain ⟨a, Pc, m, harun, hrestm, hmn, hend, hphasec⟩ := ih hnwm hw hphasem
        by_cases hta : t = a
        · subst hta
          exact ⟨t, Pc, m, .cons hstep harun, hrestm, Nat.lt_succ_of_lt hmn, hend, hphasec⟩
        · obtain ⟨P', harun', htP', _⟩ := push_green_back hV hNE hta harun hstep ⟨s0, hg0, hns0⟩
          have hinv : Pc.threads[a]? = P'.threads[a]? := threads_get_invariant htP' (Ne.symm hta)
          refine ⟨a, P', m + 1, harun', .cons t htP' hrestm, Nat.succ_lt_succ hmn, ?_,
            harun'.phaseRN hphase⟩
          rcases hend with hE | ⟨s, hsN⟩
          · obtain ⟨s, p, hg, hww⟩ := hE; exact Or.inl ⟨s, p, hinv ▸ hg, hww⟩
          · exact Or.inr ⟨s, hinv ▸ hsN⟩
      · obtain ⟨s', p', hres⟩ := istep_result hstep
        have hphasem : PhaseRN Pm := PhaseRN.step hstep hphase
        have hp'RN : p' = Effect.R ∨ p' = Effect.N := hphasem t s' p' hres
        refine ⟨t, Pm, n', .cons hstep (.nil Pm), hrest, Nat.lt_succ_self n', ?_, hphasem⟩
        by_cases hws' : IsWrong s'
        · exact Or.inl ⟨s', p', hres, hws'⟩
        · have hp'N : p' = Effect.N := by
            rcases hp'RN with hR | hN
            · exact absurd ⟨s', hR ▸ hres, hws'⟩ hgreen
            · exact hN
          exact Or.inr ⟨s', hp'N ▸ hres⟩

/-! ### Length-indexed merge (obligation 1 for the outer induction's measure)

The merge (`merge_wrong`) produces an `ISteps` with no length bound, so it cannot
drive a well-founded recursion.  These are its length-indexed counterparts:
`NonJRunN` records the non-`a` run's length, `push_jN`/`iter_diamondN` preserve
it, and `merge_wrongN` delivers an `IStepsTn (q + 1)` off the end of the `a`-run —
a run of *exactly* `q + 1` steps (`q` = the non-`a` run's length, `+1` the fatal
step).  Each mirrors its unindexed sibling, threading the `Nat` index. -/

/-- A length-indexed non-`j` run. -/
inductive NonJRunN (M : MoverSpec) (D : BodyEnv) (j : Tid) : Nat → IState → IState → Prop where
  | nil (P : IState) (hP : ¬ IWrong P) : NonJRunN M D j 0 P P
  | cons {n : Nat} {P Pm Pe : IState} (t : Tid) (ht : t ≠ j) (h : IStepI M D t P Pm)
      (hP : ¬ IWrong P) (rest : NonJRunN M D j n Pm Pe) : NonJRunN M D j (n + 1) P Pe

theorem NonJRunN.src_not_wrong {M D j n} {a b : IState} (h : NonJRunN M D j n a b) : ¬ IWrong a := by
  cases h with
  | nil _ hP => exact hP
  | cons _ _ _ hP _ => exact hP

theorem NonJRunN.clL_end {M D j n} {a b : IState} :
    NonJRunN M D j n a b → clL a j → clL b j
  | .nil _ _, hL => hL
  | .cons _ ht hstep _ rest, hL => rest.clL_end (clL_invariant hstep (Ne.symm ht) hL)

theorem NonJRunN.toIStepsTn {M D j n} {a b : IState} :
    NonJRunN M D j n a b → IStepsTn M D n a b
  | .nil P _ => .nil P
  | .cons t _ hstep _ rest => .cons t hstep rest.toIStepsTn

/-- `IStepsTn` is transitive, summing lengths. -/
theorem IStepsTn.trans {M D} {m n} {a b c : IState} (h1 : IStepsTn M D m a b)
    (h2 : IStepsTn M D n b c) : IStepsTn M D (m + n) a c := by
  induction h1 with
  | nil P => exact (Nat.zero_add n).symm ▸ h2
  | @cons k P Pm Pe t hstep _ ih =>
      have hcons : IStepsTn M D ((k + n) + 1) P c := IStepsTn.cons t hstep (ih h2)
      have heq : (k + 1) + n = (k + n) + 1 := by omega
      rw [heq]; exact hcons

/-- Length-preserving `push_j`. -/
theorem push_jN {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {j : Tid} :
    ∀ {n} {Pa Pe : IState}, NonJRunN M D j n Pa Pe → ∀ {Pj : IState},
      clL Pa j → IStepI M D j Pa Pj → ¬ clE Pj j →
      ∃ Pe', IStepI M D j Pe Pe' ∧ NonJRunN M D j n Pj Pe' ∧ ¬ clE Pe' j := by
  intro n Pa Pe hrun
  induction hrun with
  | nil P hP =>
      intro Pj hclL hjstep hjok
      exact ⟨Pj, hjstep, .nil Pj (jstep_not_wrong hjstep hP hjok), hjok⟩
  | @cons n P Pm Pe t ht hstep hP hrest ih =>
      intro Pj hclL hjstep hjok
      have hiok : ¬ clE Pm t := not_clE_of_not_wrong hrest.src_not_wrong t
      obtain ⟨Pd, hjPm, htPj⟩ := diamond_commutes hV ht hstep hiok hclL hjstep hjok
      have hclLm : clL Pm j := clL_invariant hstep (Ne.symm ht) hclL
      have hjokd : ¬ clE Pd j := by
        intro hE
        obtain ⟨s, p, hget, hw⟩ := hE
        exact hjok ⟨s, p, (threads_get_invariant htPj (Ne.symm ht)).symm.trans hget, hw⟩
      obtain ⟨Pe', hje, hrest', hpe'⟩ := ih hclLm hjPm hjokd
      exact ⟨Pe', hje, .cons t ht htPj (jstep_not_wrong hjstep hP hjok) hrest', hpe'⟩

/-- Length-preserving `iter_diamond`. -/
theorem iter_diamondN {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {a : Tid} :
    ∀ {Pa Pfin : IState}, LMRun M D a Pa Pfin → ∀ {n} {Pe : IState}, NonJRunN M D a n Pa Pe →
      ∃ Pe', NonJRunN M D a n Pfin Pe' ∧ LMRun M D a Pe Pe' := by
  intro Pa Pfin hlm
  induction hlm with
  | nil P => intro n Pe hrun; exact ⟨Pe, hrun, .nil Pe⟩
  | @cons P Pm Pfin hL hstep hok hrest ih =>
      intro n Pe hrun
      obtain ⟨Pe1, haStep, hrun1, hok1⟩ := push_jN hV hrun hL hstep hok
      obtain ⟨Pe', hrun', hlm'⟩ := ih hrun1
      exact ⟨Pe', hrun', .cons (hrun.clL_end hL) haStep hok1 hlm'⟩

/-- The fatal step reaches wrong in *exactly one* step off the end of the `a`-run. -/
theorem push_c_wrongN {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M)
    {c a : Tid} (hca : c ≠ a) :
    ∀ {X Xfin : IState}, LMRun M D a X Xfin → ∀ {Y : IState},
      IStepI M D c X Y → clE Y c → ∃ Yfin, IStepsTn M D 1 Xfin Yfin ∧ IWrong Yfin := by
  intro X Xfin hlm
  induction hlm with
  | nil P =>
      intro Y hc hYc
      exact ⟨Y, .cons c hc (.nil Y), iwrong_iff_clE.2 ⟨c, hYc⟩⟩
  | @cons P Pm Xfin hL hastep hok hrest ih =>
      intro Y hc hYc
      obtain ⟨Pd, haY, hcPm⟩ := diamond_commutes_w hV hNE hca hc hL hastep hok
      exact ih hcPm (clE_step haY hYc)

/-- **Length-indexed merge.**  From the end of the `a`-run, the non-`a` run (of
    length `q`) replays and the fatal `c`-step still reaches wrong — a run of
    exactly `q + 1` steps. -/
theorem merge_wrongN {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M)
    {a c : Tid} (hca : c ≠ a) {q} {P_a P_fin Pe_prev Pe : IState}
    (hlm : LMRun M D a P_a P_fin) (hrun : NonJRunN M D a q P_a Pe_prev)
    (hc : IStepI M D c Pe_prev Pe) (hPec : clE Pe c) :
    ∃ Pw, IStepsTn M D (q + 1) P_fin Pw ∧ IWrong Pw := by
  obtain ⟨Pe', hnonj, hlm'⟩ := iter_diamondN hV hlm hrun
  obtain ⟨Yfin, hsteps, hwrong⟩ := push_c_wrongN hV hNE hca hlm' hc hPec
  exact ⟨Yfin, IStepsTn.trans hnonj.toIStepsTn hsteps, hwrong⟩

/-! ### Mover invariance (obligation 2's core: a committed thread cannot go wrong)

A step by another thread `c ≠ a` cannot change the mover effect of any action of
`a` (validity (3), plus: structural and instrumented-wrong steps leave the store
fixed).  Folded over a non-`a` run, `a`'s action effects are *invariant* under the
interference — the fact that lets us refute a post-commit thread going wrong. -/

theorem istep_mover_invariant {M D} (hV : Valid M) (hNE : NeverError M) {c a : Tid}
    (hca : c ≠ a) {X Y : IState} (h : IStepI M D c X Y) (A : Action) :
    M A a X.store = M A a Y.store := by
  cases h with
  | mk ths s s' σ σ' p p' hget hstep =>
    cases hstep with
    | iseq _ _ _ _ => rfl
    | iyield _ _ _ => rfl
    | iwhile _ _ _ _ _ => rfl
    | icall _ _ _ _ _ _ => rfl
    | iaction_ok _ A1 σ σ' _ hA1 _ =>
        exact (hV.effect c a A1 A σ σ' (M A a σ) hca (le_N_of_neverError hNE A1 c σ) hA1 rfl).symm
    | iaction_wrong _ _ _ _ _ => rfl
    | iif_ok_T _ C _ _ σ σ' _ hA _ =>
        exact (hV.effect c a C.tru A σ σ' (M A a σ) hca (le_N_of_neverError hNE C.tru c σ) hA rfl).symm
    | iif_ok_F _ C _ _ σ σ' _ hA _ =>
        exact (hV.effect c a C.fls A σ σ' (M A a σ) hca (le_N_of_neverError hNE C.fls c σ) hA rfl).symm
    | iif_wrong_T _ _ _ _ _ _ _ _ => rfl
    | iif_wrong_F _ _ _ _ _ _ _ _ => rfl

theorem nonjrun_mover_invariant {M D} (hV : Valid M) (hNE : NeverError M) {a : Tid} :
    ∀ {X Y : IState}, NonJRun M D a X Y → ∀ (A : Action), M A a X.store = M A a Y.store := by
  intro X Y h
  induction h with
  | nil P hP => intro A; rfl
  | cons t ht hstep hP hrest ih =>
      intro A; exact (istep_mover_invariant hV hNE ht hstep A).trans (ih A)

/-- **A valid state's active thread cannot step to wrong.**  If `a` steps from a
    verified state (others yielding, so the step is non-preemptive) into a state
    where `a` is wrong, `preservation` would make that wrong state verified,
    contradicting Not-Wrong.  This is what refutes a *committed* thread going
    wrong — the `c = a` case of the post-commit decomposition. -/
theorem valid_no_wrong_step {M : MoverSpec} {D : Decls} {a : Tid} {Pmid Y : IState}
    (hval : IStateValid M D Pmid) (hO : OthersYield Pmid a)
    (h : IStepI M D.bodies a Pmid Y) (hclE : clE Y a) : False :=
  (preservation hval (istep_to_inonstep h hO)).not_wrong (iwrong_iff_clE.2 ⟨a, hclE⟩)

/-! ### The committer's redex is a left-mover (`hjno_iif`'s discharge)

At a verified state, the *active* thread's redex effect is `⊑ L`: the whole
statement's judgment effect is `⊑ L` (from `p ;; e ≠ E` with `p = N`), and the
Evaluation-Context lemma peels the redex derivation off with a `⊑ L` effect,
whose canonical form bounds the redex's mover.  For an action redex this bounds
`M A`; for a conditional it bounds *both* branch movers.  This is exactly what
makes a committer's conditional step never `iif`-wrong (`left_commutes_w`'s
`hjno_iif`), and — via `mover_invariant` — keeps that so under interference. -/

/-- The active thread's redex, peeled off with a `⊑ L` canonical derivation. -/
theorem active_redex_judg {M : MoverSpec} {D : Decls} {a : Tid} {Pmid : IState}
    (E : Ctx) {redex : Stmt}
    (hval : IStateValid M D Pmid)
    (hget : Pmid.threads[a]? = some (E.plug redex, Effect.N))
    (hns : ¬ (yielding (E.plug redex) ∨ IsWrong (E.plug redex))) :
    ∃ (R1 G1 P1 Q1 : Pred2) (e1 : Effect) (σ0 : Store),
      JudgNC M D R1 G1 redex P1 Q1 e1 ∧ e1 ⊑ Effect.L ∧ P1 a σ0 Pmid.store := by
  obtain ⟨R, G, av, σ0, hfns, hVal, hrefl, _hanchor, hthreads, hcompat⟩ := hval
  obtain ⟨P, Q, e, hJ, hne, hQG, hpre⟩ := hthreads a (E.plug redex) Effect.N hget
  have hpre_a : P a σ0 Pmid.store := by
    by_cases hia : a = av
    · rw [if_pos hia] at hpre; exact hpre
    · rw [if_neg hia] at hpre; exact absurd (Or.inl hpre.1) hns
  have heL : e ⊑ Effect.L := seq_N_ne_E_imp_le_L hne
  obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, hle, hnc, _hrebuild⟩ := hJ.eval_ctxt E
  exact ⟨R1, G1, P1, Q1, e1, σ0, hnc, seq_le_L_imp_le_L (le_trans hle heL),
    hP a σ0 Pmid.store hpre_a⟩

/-- A committer's action redex is a left-mover. -/
theorem active_action_le_L {M : MoverSpec} {D : Decls} {a : Tid} {Pmid : IState}
    {E : Ctx} {A : Action}
    (hval : IStateValid M D Pmid)
    (hget : Pmid.threads[a]? = some (E.plug (.act A), Effect.N))
    (hns : ¬ (yielding (E.plug (.act A)) ∨ IsWrong (E.plug (.act A)))) :
    M A a Pmid.store ⊑ Effect.L := by
  obtain ⟨R1, G1, P1, Q1, e1, σ0, hnc, he1L, hP1⟩ := active_redex_judg E hval hget hns
  cases hnc with
  | action he htot => exact le_trans (le_trans (M.le_lift A P1 hP1) he) he1L

/-- Both branch movers of a committer's conditional redex are left-movers. -/
theorem active_branches_le_L {M : MoverSpec} {D : Decls} {a : Tid} {Pmid : IState}
    {E : Ctx} {C : CondAction} {s1 s2 : Stmt}
    (hval : IStateValid M D Pmid)
    (hget : Pmid.threads[a]? = some (E.plug (.ite C s1 s2), Effect.N))
    (hns : ¬ (yielding (E.plug (.ite C s1 s2)) ∨ IsWrong (E.plug (.ite C s1 s2)))) :
    M C.tru a Pmid.store ⊑ Effect.L ∧ M C.fls a Pmid.store ⊑ Effect.L := by
  obtain ⟨R1, G1, P1, Q1, e1, σ0, hnc, he1L, hP1⟩ := active_redex_judg E hval hget hns
  cases hnc with
  | ite h1 h2 he =>
      have he1L' := le_trans he he1L
      exact ⟨le_trans (M.le_lift C.tru P1 hP1) (seq_le_L_imp_le_L (le_trans (le_join_left _ _) he1L')),
             le_trans (M.le_lift C.fls P1 hP1) (seq_le_L_imp_le_L (le_trans (le_join_right _ _) he1L'))⟩

/-- Composing phase `N` with a left-mover never errors (`N ;; {Y,B,L} ∈ {R,N}`). -/
theorem N_seq_le_L_ne_E {b : Effect} (hb : b ⊑ Effect.L) : Effect.N ;; b ≠ Effect.E := by
  revert hb; cases b <;> decide

/-- **`hjno_iif`'s discharge.**  At any state `Pb` reached from a verified state
    `Pmid` by a non-`a` run, the committer `a`'s conditional-redex branches still
    compose `≠ E`: their movers are `⊑ L` at `Pmid` (`active_branches_le_L`) and
    invariant along the run (`mover_invariant`), and `N ;; (⊑ L) ≠ E`.  So a
    committer's conditional step is never `iif`-wrong under interference. -/
theorem interfered_branches_ne_E {M : MoverSpec} {D : Decls} (hV : Valid M)
    (hNE : NeverError M) {a : Tid} {Pmid Pb : IState} {E : Ctx} {C : CondAction} {s1 s2 : Stmt}
    (hval : IStateValid M D Pmid)
    (hget_m : Pmid.threads[a]? = some (E.plug (.ite C s1 s2), Effect.N))
    (hns : ¬ (yielding (E.plug (.ite C s1 s2)) ∨ IsWrong (E.plug (.ite C s1 s2))))
    (hnonj : NonJRun M D.bodies a Pmid Pb) :
    Effect.N ;; M C.tru a Pb.store ≠ Effect.E ∧ Effect.N ;; M C.fls a Pb.store ≠ Effect.E := by
  obtain ⟨htL, hfL⟩ := active_branches_le_L hval hget_m hns
  refine ⟨?_, ?_⟩
  · rw [← nonjrun_mover_invariant hV hNE hnonj C.tru]; exact N_seq_le_L_ne_E htL
  · rw [← nonjrun_mover_invariant hV hNE hnonj C.fls]; exact N_seq_le_L_ne_E hfL

/-! ### All-yielding states and left-mover run glue -/

/-- Every thread of `Pi` is yielding. -/
def AllYielding (Pi : IState) : Prop := ∀ sp ∈ Pi.threads, yielding sp.1

theorem AllYielding.othersYield {Pi a} (h : AllYielding Pi) : OthersYield Pi a :=
  fun _u su pu _ hgetu => h (su, pu) (List.mem_of_getElem? hgetu)

/-- Rebuild `AllYielding` from `OthersYield` plus the active thread yielding. -/
theorem allYielding_of {Pi : IState} {a : Tid} (hO : OthersYield Pi a)
    (ha : ∀ s p, Pi.threads[a]? = some (s, p) → yielding s) : AllYielding Pi := by
  intro sp hmem
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have hidx : Pi.threads[i]? = some sp := by rw [List.getElem?_eq_getElem hi, hget]
  obtain ⟨s, p⟩ := sp
  by_cases hia : i = a
  · subst hia; exact ha s p hidx
  · exact hO i s p hia hidx

theorem LMRun.toINonSteps {M Db a} {P Pe : IState} (h : LMRun M Db a P Pe)
    (hO : OthersYield P a) : INonSteps M Db P Pe := by
  induction h with
  | nil => exact .refl _
  | cons hL hstep hok rest ih =>
      exact .step (istep_to_inonstep hstep hO) (ih (OthersYield.step hstep hO))

theorem LMRun.phaseRN {M D a} {P Pe : IState} (h : LMRun M D a P Pe) (hP : PhaseRN P) :
    PhaseRN Pe := by
  induction h with
  | nil => exact hP
  | cons hL hstep hok rest ih => exact ih (PhaseRN.step hstep hP)

theorem LMRun.othersYield_end {M D a} {P Pe : IState} (h : LMRun M D a P Pe)
    (hO : OthersYield P a) : OthersYield Pe a := by
  induction h with
  | nil => exact hO
  | cons hL hstep hok rest ih => exact ih (OthersYield.step hstep hO)

/-! ### Length-indexed left-mover partition (feeds `merge_wrongN`)

`LAMixN` is a length-indexed left-mover-interleaved run (a's post-commit
left-movers interleaved with non-`a` steps).  `partition_left_n` splits it into
`a`'s left-mover run (bubbled to the front) followed by a non-`a` `NonJRunN` of
bounded length — exactly the `LMRun` + `NonJRunN` pair `merge_wrongN` consumes. -/

/-- A left-mover run keeps the whole state non-wrong. -/
theorem LMRun.dest_not_wrong {M D a} {P Pe : IState} :
    LMRun M D a P Pe → ¬ IWrong P → ¬ IWrong Pe := by
  intro h
  induction h with
  | nil => exact id
  | cons hL hstep hok rest ih => exact fun hP => ih (jstep_not_wrong hstep hP hok)

/-- A length-indexed left-mover-interleaved run. -/
inductive LAMixN (M : MoverSpec) (D : BodyEnv) (a : Tid) : Nat → IState → IState → Prop where
  | nil (P : IState) : LAMixN M D a 0 P P
  | consA {n : Nat} {P Pm Pe : IState} (hL : clL P a) (h : IStepI M D a P Pm) (hok : ¬ clE Pm a)
      (rest : LAMixN M D a n Pm Pe) : LAMixN M D a (n + 1) P Pe
  | consN {n : Nat} {P Pm Pe : IState} (t : Tid) (ht : t ≠ a) (h : IStepI M D t P Pm)
      (hok : ¬ clE Pm t) (rest : LAMixN M D a n Pm Pe) : LAMixN M D a (n + 1) P Pe

/-- Split a length-indexed left-mover-interleaved run into `a`'s left-mover run
    followed by a non-`a` run of length `≤ l`. -/
theorem partition_left_n {M : MoverSpec} {D : BodyEnv} (hV : Valid M) {a : Tid} :
    ∀ {l} {P Pe : IState}, LAMixN M D a l P Pe → ¬ IWrong P →
      ∃ (Pmid : IState) (q : Nat), LMRun M D a P Pmid ∧ NonJRunN M D a q Pmid Pe ∧ q ≤ l := by
  intro l P Pe h
  induction h with
  | nil P => intro hP; exact ⟨P, 0, .nil P, .nil P hP, Nat.le_refl 0⟩
  | @consA n P Pm Pe hL hstep hok rest ih =>
      intro hP
      obtain ⟨Pmid, q, hlm, hnon, hq⟩ := ih (jstep_not_wrong hstep hP hok)
      exact ⟨Pmid, q, .cons hL hstep hok hlm, hnon, Nat.le_succ_of_le hq⟩
  | @consN n P Pm Pe t ht hstep hok rest ih =>
      intro hP
      obtain ⟨Pmid, q, hlm, hnon, hq⟩ := ih (jstep_not_wrong hstep hP hok)
      obtain ⟨P', hlm', htP', _⟩ := push_left_back hV ht hlm hstep hok
      exact ⟨P', q + 1, hlm', .cons t ht htP' (hlm'.dest_not_wrong hP) hnon, Nat.succ_le_succ hq⟩

/-! ### The committer-is-fatal case (`c = a`), by commutation

Following the paper, a committer's fatal step is *commuted* into its block, not
refuted directly.  `bubble_a_wrong` moves `a`'s wrong step back through the non-`a`
run (via `left_commutes_w'`, its `hjno_iif` discharged by `interfered_branches_ne_E`
transported along the run) to `a`'s last verified state; `committed_run_cannot_wrong`
then contradicts it with `valid_no_wrong_step`.  So a committed thread never turns
out to be the fatal one — the fatal thread is always some `c ≠ a`. -/

/-- Bubble `a`'s wrong step back through a non-`a` run to its front, given that
    `a`'s conditional-redex branches compose `≠ E` throughout (threaded as `hbr`). -/
theorem bubble_a_wrong {M : MoverSpec} {D : BodyEnv} (hV : Valid M) (hNE : NeverError M) {a : Tid} :
    ∀ {q} {Q Pe_prev Pw : IState}, NonJRunN M D a q Q Pe_prev →
      IStepI M D a Pe_prev Pw → clE Pw a → clL Q a →
      (∀ (C : CondAction) (s1 s2 : Stmt) (E' : Ctx),
        Q.threads[a]? = some (E'.plug (.ite C s1 s2), Effect.N) →
        Effect.N ;; M C.tru a Q.store ≠ Effect.E ∧ Effect.N ;; M C.fls a Q.store ≠ Effect.E) →
      ∃ Pw', IStepI M D a Q Pw' ∧ clE Pw' a := by
  intro q Q Pe_prev Pw hrun
  induction hrun with
  | nil P hP => intro hstep hclE _ _; exact ⟨Pw, hstep, hclE⟩
  | @cons n Q Pm Pe_prev t ht hstep_c hP hrest ih =>
      intro hstep_a hclE hclL hbr
      have hclLm : clL Pm a := clL_invariant hstep_c (Ne.symm ht) hclL
      have hbrm : ∀ (C : CondAction) (s1 s2 : Stmt) (E' : Ctx),
          Pm.threads[a]? = some (E'.plug (.ite C s1 s2), Effect.N) →
          Effect.N ;; M C.tru a Pm.store ≠ Effect.E ∧ Effect.N ;; M C.fls a Pm.store ≠ Effect.E := by
        intro C s1 s2 E' hPm
        have hQa : Q.threads[a]? = some (E'.plug (.ite C s1 s2), Effect.N) := by
          rw [← threads_get_invariant hstep_c (Ne.symm ht)]; exact hPm
        obtain ⟨htru, hfls⟩ := hbr C s1 s2 E' hQa
        refine ⟨?_, ?_⟩
        · rw [← istep_mover_invariant hV hNE ht hstep_c C.tru]; exact htru
        · rw [← istep_mover_invariant hV hNE ht hstep_c C.fls]; exact hfls
      obtain ⟨Pw'', hstepPm, hclEPm⟩ := ih hstep_a hclE hclLm hbrm
      have hiok : ¬ clE Pm t := not_clE_of_not_wrong hrest.src_not_wrong t
      obtain ⟨Pd, haStep, htStep⟩ := left_commutes_w' hV ht hstep_c hiok hclLm hstepPm hbrm
      obtain ⟨s, p, hget, hw⟩ := hclEPm
      exact ⟨Pd, haStep, s, p, (threads_get_invariant htStep (Ne.symm ht)).symm.trans hget, hw⟩

/-- **A committed thread never turns out to be the fatal one.**  If `a` is
    post-commit at a verified state and, after some non-`a` run, takes a step to
    wrong, that is a contradiction. -/
theorem committed_run_cannot_wrong {M : MoverSpec} {D : Decls} (hV : Valid M) (hNE : NeverError M)
    {a : Tid} {q} {Pmid Pe_prev Pw : IState} (hrun : NonJRunN M D.bodies a q Pmid Pe_prev)
    (hval : IStateValid M D Pmid) (hclL : clL Pmid a) (hOY : OthersYield Pmid a)
    (hstep : IStepI M D.bodies a Pe_prev Pw) (hclE : clE Pw a) : False := by
  have hbr : ∀ (C : CondAction) (s1 s2 : Stmt) (E' : Ctx),
      Pmid.threads[a]? = some (E'.plug (.ite C s1 s2), Effect.N) →
      Effect.N ;; M C.tru a Pmid.store ≠ Effect.E ∧ Effect.N ;; M C.fls a Pmid.store ≠ Effect.E := by
    intro C s1 s2 E' hget
    obtain ⟨s, p, hgetL, hpN, hns⟩ := hclL
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hgetL.symm.trans hget)
    obtain ⟨htL, hfL⟩ := active_branches_le_L hval hget hns
    exact ⟨N_seq_le_L_ne_E htL, N_seq_le_L_ne_E hfL⟩
  obtain ⟨Pw', hstep', hclE'⟩ := bubble_a_wrong hV hNE hrun hstep hclE hclL hbr
  exact valid_no_wrong_step hval hOY hstep' hclE'

/-- A post-commit thread's non-wrong, non-settling step stays in phase `N`: the
    only phase-changing steps are `iyield` (needs a yielding redex, excluded by
    `clL`) and an action/branch with a `Y` mover (excluded by `NeverYields`). -/
theorem post_commit_step_phase_N {M : MoverSpec} {D : BodyEnv} {a : Tid} {P Pm : IState}
    (hNY : NeverYields M) (hclL : clL P a) (h : IStepI M D a P Pm) (hok : ¬ clE Pm a)
    {s' p' : _} (hres : Pm.threads[a]? = some (s', p')) : p' = Effect.N := by
  obtain ⟨sa, pa, hgeta, hpaN, hns⟩ := hclL
  subst hpaN
  cases h with
  | mk ths s0 s0' σ σ' p0 p0' hget0 hstep =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hgeta.symm.trans hget0)
    have hp' : p' = p0' := by
      have hset : (ths.set a (s0', p0'))[a]? = some (s0', p0') :=
        getElem?_set_self_of ths (s0', p0') (lt_of_getElem? hget0)
      exact (Prod.mk.injEq .. ▸ Option.some.inj (hres.symm.trans hset)).2
    subst hp'
    cases hstep with
    | iseq _ _ _ _ => rfl
    | iyield E _ _ =>
        exact absurd (Or.inl (Or.inl ⟨E, rfl⟩ : yielding (E.plug .yield))) hns
    | iwhile _ _ _ _ _ => rfl
    | icall _ _ _ _ _ _ => rfl
    | iaction_ok _ A _ _ _ hA hne =>
        exact N_seq_eq_N_of_le_L (seq_N_ne_E_imp_le_L hne) (hNY A a σ)
    | iaction_wrong E A _ _ hp =>
        exact absurd (⟨E.plug .wrong, Effect.N,
          getElem?_set_self_of ths (E.plug .wrong, Effect.N) (lt_of_getElem? hget0), E, rfl⟩ : clE _ a) hok
    | iif_ok_T _ C _ _ _ _ _ hA hne =>
        exact N_seq_eq_N_of_le_L (seq_N_ne_E_imp_le_L hne) (hNY C.tru a σ)
    | iif_ok_F _ C _ _ _ _ _ hA hne =>
        exact N_seq_eq_N_of_le_L (seq_N_ne_E_imp_le_L hne) (hNY C.fls a σ)
    | iif_wrong_T E C _ _ _ _ _ hA hp =>
        exact absurd (⟨E.plug .wrong, Effect.N,
          getElem?_set_self_of ths (E.plug .wrong, Effect.N) (lt_of_getElem? hget0), E, rfl⟩ : clE _ a) hok
    | iif_wrong_F E C _ _ _ _ _ hA hp =>
        exact absurd (⟨E.plug .wrong, Effect.N,
          getElem?_set_self_of ths (E.plug .wrong, Effect.N) (lt_of_getElem? hget0), E, rfl⟩ : clE _ a) hok

/-- **Post-commit decomposition.**  A run to wrong from a post-commit state
    factors as `a`'s left-mover transaction pulled to the front, then either `a`
    settles (its stmt becomes yielding, leaving a strictly shorter residual) or a
    fatal step is reached with `a` frozen post-commit and a bounded non-`a` run
    before it.  Mirror of `extract_committer` for the left-mover side. -/
theorem left_decompose {M : MoverSpec} {D : BodyEnv} (hV : Valid M)
    (hNY : NeverYields M) {a : Tid} :
    ∀ {n} {Pc Pe : IState}, IStepsTn M D n Pc Pe → ¬ IWrong Pc → IWrong Pe → clL Pc a →
      (∃ (Pmid : IState) (m : Nat), LMRun M D a Pc Pmid ∧
         (∃ s p, Pmid.threads[a]? = some (s, p) ∧ yielding s) ∧ IStepsTn M D m Pmid Pe ∧ m < n)
      ∨ (∃ (Pmid Pe_prev Pw : IState) (q : Nat) (c : Tid), LMRun M D a Pc Pmid ∧ clL Pmid a ∧
           NonJRunN M D a q Pmid Pe_prev ∧ IStepI M D c Pe_prev Pw ∧ clE Pw c ∧ q + 1 ≤ n) := by
  intro n Pc Pe hrun
  induction hrun with
  | nil P => intro hnw hw _; exact absurd hw hnw
  | @cons n' P Pm Pe t hstep hrest ih =>
      intro hnw hw hclL
      by_cases hclEm : clE Pm t
      · exact Or.inr ⟨P, P, Pm, 0, t, .nil P, hclL, .nil P hnw, hstep, hclEm,
          Nat.succ_le_succ (Nat.zero_le n')⟩
      · have hnwm : ¬ IWrong Pm := jstep_not_wrong hstep hnw hclEm
        by_cases hta : t = a
        · subst t
          obtain ⟨s', p', hres⟩ := istep_result hstep
          by_cases hyield : yielding s'
          · exact Or.inl ⟨Pm, n', .cons hclL hstep hclEm (.nil Pm), ⟨s', p', hres, hyield⟩,
              hrest, Nat.lt_succ_self n'⟩
          · have hp'N : p' = Effect.N := post_commit_step_phase_N hNY hclL hstep hclEm hres
            have hclLm : clL Pm a :=
              ⟨s', p', hres, hp'N, fun h => h.elim hyield (fun hw' => hclEm ⟨s', p', hres, hw'⟩)⟩
            rcases ih hnwm hw hclLm with settle | fatal
            · obtain ⟨Pmid, m, hlm, hy, hrun2, hm⟩ := settle
              exact Or.inl ⟨Pmid, m, .cons hclL hstep hclEm hlm, hy, hrun2, Nat.lt_succ_of_lt hm⟩
            · obtain ⟨Pmid, Pe_prev, Pw, q, c, hlm, hclLmid, hnon, hc, hcE, hq⟩ := fatal
              exact Or.inr ⟨Pmid, Pe_prev, Pw, q, c, .cons hclL hstep hclEm hlm, hclLmid, hnon,
                hc, hcE, Nat.le_succ_of_le hq⟩
        · have hclLm : clL Pm a := clL_invariant hstep (Ne.symm hta) hclL
          rcases ih hnwm hw hclLm with settle | fatal
          · obtain ⟨Pmid, m, hlm, hy, hrun2, hm⟩ := settle
            obtain ⟨P', hlm', htP', _⟩ := push_left_back hV hta hlm hstep hclEm
            obtain ⟨sy, py, hgy, hyld⟩ := hy
            have hgy' : P'.threads[a]? = some (sy, py) :=
              (threads_get_invariant htP' (Ne.symm hta)).symm.trans hgy
            exact Or.inl ⟨P', m + 1, hlm', ⟨sy, py, hgy', hyld⟩, .cons t htP' hrun2,
              Nat.succ_lt_succ hm⟩
          · obtain ⟨Pmid, Pe_prev, Pw, q, c, hlm, hclLmid, hnon, hc, hcE, hq⟩ := fatal
            obtain ⟨P', hlm', htP', _⟩ := push_left_back hV hta hlm hstep hclEm
            obtain ⟨sy, py, hgy, hpyN, hns⟩ := hclLmid
            have hgy' : P'.threads[a]? = some (sy, py) :=
              (threads_get_invariant htP' (Ne.symm hta)).symm.trans hgy
            exact Or.inr ⟨P', Pe_prev, Pw, q + 1, c, hlm', ⟨sy, py, hgy', hpyN, hns⟩,
              .cons t hta htP' (hlm'.dest_not_wrong hnw) hnon, hc, hcE, Nat.succ_le_succ hq⟩

/-- **The `(form:c)` reordering.**  From an all-yielding (`w = 0`) or single
    post-commit-active (`w = 1`) verified state that goes wrong under the
    preemptive semantics, it goes wrong under the non-preemptive semantics.  By
    strong induction on `2 * n + w` (run length, with the post-commit refinement
    breaking ties): `extract_committer` pulls the first committer's transaction
    non-preemptively (`w = 0`); `left_decompose` + `post_commit_lm` + `merge_wrongN`
    finish and merge a post-commit thread (`w = 1`); `committed_run_cannot_wrong`
    rules out a committer being the fatal thread. -/
theorem reorder_core {M : MoverSpec} {D : Decls} (hV : Valid M) (hNE : NeverError M)
    (hNY : NeverYields M) (hCT : CondTotal) {fs : FnName → Nat} (hfs : GoodSizing D fs) :
    ∀ (μ n : Nat) (Pc Pe : IState) (a : Tid) (w : Nat), 2 * n + w = μ → w ≤ 1 →
      IStateValid M D Pc → PhaseRN Pc → IStepsTn M D.bodies n Pc Pe → IWrong Pe →
      (w = 0 → AllYielding Pc) → (w = 1 → clL Pc a ∧ OthersYield Pc a) →
      ∃ Pw, INonSteps M D.bodies Pc Pw ∧ IWrong Pw := by
  intro μ
  induction μ using Nat.strongRecOn with
  | ind μ ih =>
    intro n Pc Pe a w hμ hw1 hval hphase hrun hwrong hAY hPC
    have hnwc : ¬ IWrong Pc := hval.not_wrong
    obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
    · -- w = 0: all-yielding
      have hallY := hAY rfl
      obtain ⟨a', Pc', m, harun, hrestm, hmn, hend, hphasec⟩ :=
        extract_committer hV hNE hrun hnwc hwrong hphase
      have hOYc : OthersYield Pc a' := hallY.othersYield
      have hnonPc : INonSteps M D.bodies Pc Pc' := harun.toINonSteps hOYc
      have hvalPc' : IStateValid M D Pc' := preservation_star hnonPc hval
      have hOYPc' : OthersYield Pc' a' := harun.othersYield_end hOYc
      rcases hend with hclE | ⟨s, hget⟩
      · exact ⟨Pc', hnonPc, iwrong_iff_clE.2 ⟨a', hclE⟩⟩
      · by_cases hws : IsWrong s
        · exact ⟨Pc', hnonPc, iwrong_iff_clE.2 ⟨a', s, Effect.N, hget, hws⟩⟩
        · by_cases hys : yielding s
          · have hallY' : AllYielding Pc' := allYielding_of hOYPc'
              (fun s2 p2 hg2 => by
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hget.symm.trans hg2)
                exact hys)
            obtain ⟨Pw, hnonPw, hwPw⟩ := ih (2 * m + 0) (by omega) m Pc' Pe a' 0 rfl (by omega)
              hvalPc' hphasec hrestm hwrong (fun _ => hallY') (by simp)
            exact ⟨Pw, hnonPc.trans hnonPw, hwPw⟩
          · have hclL' : clL Pc' a' := ⟨s, Effect.N, hget, rfl, fun h => h.elim hys hws⟩
            obtain ⟨Pw, hnonPw, hwPw⟩ := ih (2 * m + 1) (by omega) m Pc' Pe a' 1 rfl (by omega)
              hvalPc' hphasec hrestm hwrong (by simp) (fun _ => ⟨hclL', hOYPc'⟩)
            exact ⟨Pw, hnonPc.trans hnonPw, hwPw⟩
    · -- w = 1: single post-commit-active thread `a`
      obtain ⟨hclLc, hOYc⟩ := hPC rfl
      rcases left_decompose hV hNY hrun hnwc hwrong hclLc with settle | fatal
      · obtain ⟨Pmid, m, hlm, ⟨s, p, hget, hyield⟩, hrun2, hm⟩ := settle
        have hnonPc : INonSteps M D.bodies Pc Pmid := hlm.toINonSteps hOYc
        have hvalPmid : IStateValid M D Pmid := preservation_star hnonPc hval
        have hOYPmid : OthersYield Pmid a := hlm.othersYield_end hOYc
        have hphasePmid : PhaseRN Pmid := hlm.phaseRN hphase
        have hallY : AllYielding Pmid := allYielding_of hOYPmid
          (fun s2 p2 hg2 => by
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hget.symm.trans hg2)
            exact hyield)
        obtain ⟨Pw, hnonPw, hwPw⟩ := ih (2 * m + 0) (by omega) m Pmid Pe a 0 rfl (by omega)
          hvalPmid hphasePmid hrun2 hwrong (fun _ => hallY) (by simp)
        exact ⟨Pw, hnonPc.trans hnonPw, hwPw⟩
      · obtain ⟨Pmid, Pe_prev, Pw0, q, c, hlm, hclLmid, hnon, hc, hcE, hq⟩ := fatal
        have hnonPc : INonSteps M D.bodies Pc Pmid := hlm.toINonSteps hOYc
        have hvalPmid : IStateValid M D Pmid := preservation_star hnonPc hval
        have hOYPmid : OthersYield Pmid a := hlm.othersYield_end hOYc
        by_cases hca : c = a
        · subst hca
          exact absurd (committed_run_cannot_wrong hV hNE hnon hvalPmid hclLmid hOYPmid hc hcE) id
        · obtain ⟨s_a, p_a, hget_a, hpaN, hns_a⟩ := hclLmid
          rcases post_commit_lm hNY hCT hfs (bodySize fs s_a) Pmid a hvalPmid
            ⟨s_a, p_a, hget_a, hpaN, hns_a⟩
            (fun s2 p2 hg2 => by
              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hget_a.symm.trans hg2)
              exact Nat.le_refl _) with
          ⟨Pf, hlmf, sf, pf, hgetf, hyf⟩ | ⟨Pw1, hnon1, hw1'⟩
          · obtain ⟨Pw2, hmergeSteps, hmergeW⟩ := merge_wrongN hV hNE hca hlmf hnon hc hcE
            have hnonPf : INonSteps M D.bodies Pc Pf := hnonPc.trans (hlmf.toINonSteps hOYPmid)
            have hvalPf : IStateValid M D Pf := preservation_star hnonPf hval
            have hOYPf : OthersYield Pf a := (hlmf.othersYield_end hOYPmid)
            have hphasePf : PhaseRN Pf := hlmf.phaseRN (hlm.phaseRN hphase)
            have hallYf : AllYielding Pf := allYielding_of hOYPf
              (fun s2 p2 hg2 => by
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hgetf.symm.trans hg2)
                exact hyf)
            obtain ⟨Pw3, hnonPw3, hwPw3⟩ := ih (2 * (q + 1) + 0) (by omega) (q + 1) Pf Pw2 a 0 rfl
              (by omega) hvalPf hphasePf hmergeSteps hmergeW (fun _ => hallYf) (by simp)
            exact ⟨Pw3, hnonPf.trans hnonPw3, hwPw3⟩
          · exact ⟨Pw1, hnonPc.trans hnon1, hw1'⟩

/-! ### The Reduction Theorem, proved (discharging the `reduction` axiom)

`reduction_proved` is the paper's Theorem (Reduction), now mechanized from
`reorder_core` (no `reduction` axiom): a verified all-yielding state that goes
wrong preemptively goes wrong non-preemptively.  `soundness'` re-assembles
Soundness on top of it, so `#print axioms soundness'` shows no `reduction`. -/

theorem reduction_proved {M : MoverSpec} {D : Decls} (hwf : WF M D) {Pi : IState}
    (hval : IStateValid M D Pi) (hphase : PhaseRN Pi) (hAY : AllYielding Pi)
    (hgo : ∃ Pi', ISteps M D.bodies Pi Pi' ∧ IWrong Pi') :
    ∃ Pi'', INonSteps M D.bodies Pi Pi'' ∧ IWrong Pi'' := by
  obtain ⟨Pi', hsteps, hwrong⟩ := hgo
  obtain ⟨n, hn⟩ := hsteps.toN
  obtain ⟨fs, hfs⟩ := hwf.sizing
  obtain ⟨_, _, _, _, _, hV, _, _, _⟩ := id hval
  exact reorder_core hV hwf.neverError hwf.neverYields hwf.condTotal hfs
    (2 * n + 0) n Pi Pi' 0 0 rfl (by omega) hval hphase hn hwrong (fun _ => hAY)
    (fun h => absurd h (by decide))

/-- **Soundness**, assembled with the *proved* Reduction (no `reduction` axiom;
    the model well-formedness `WF M D` is threaded as a hypothesis). -/
theorem soundness' {M : MoverSpec} {D : Decls} (hwf : WF M D) {st : State}
    (h : StateValid M D st) : ¬ GoesWrong D.bodies st := by
  rintro ⟨st', hsteps, hwrong⟩
  obtain ⟨Pi, hPival, hsim, hyield, hphase⟩ := embed h
  obtain ⟨Pi', histeps, hiwrong⟩ := simulation_star hsteps hwrong Pi hsim
  obtain ⟨Pi'', hnon, hiwrong''⟩ :=
    reduction_proved hwf hPival hphase hyield ⟨Pi', histeps, hiwrong⟩
  exact (preservation_star hnon hPival).not_wrong hiwrong''

/-! ### Status: the Reduction proof, complete

Every **named lemma** of the paper's Reduction proof (§sec:red-thm) is
mechanized, `sorry`-free.  This file adds, on top of the commutation layer of
`ReductionThm.lean` and Post-Commit Termination of `PostCommit.lean`:

  * `IStepsT` — tagged preemptive runs, with conversions to/from `ISteps`;
  * `clL_invariant` / `clE_invariant` / `threads_get_invariant` — **class
    invariance** (a step by thread `k` leaves the other threads untouched);
  * `right_commutes'` — a **phase-generalized Right Commutativity** (the first
    step need only end in phase `R`, so it covers a right-mover that settles to
    `skip`).  With `left_commutes` these are the two adjacent-swap primitives;
  * `NonJRun` / `LMRun` — the "main trace" and "left-mover run" shapes;
  * **`push_j`** and **`iter_diamond`** — the **Iterative Diamond** (Lemma
    lem:iter-diamond): push a whole left-mover run of `a` through a non-`a` run;
  * **`bubble_left`** / **`bubble_green`** — the **post-commit** and **pre-commit
    bubbles**: move an `a`-step (left-mover; or any step — including the fatal
    one — past a green prefix) to the front of a run (the primitive that
    extracts a post-commit thread's steps to the head of a run);
  * **`right_commutes_w`** / **`left_commutes_w`** / **`diamond_commutes_w`** — the
    **wrong-case** Right/Left Commutativity and Diamond, following the paper's
    commented-out I-if error case: an instrumented-wrong step commutes like any
    other, its error effect and branch witness reconstructed on the swapped store
    by validity (3) and validity (1)/(4), assuming only `NeverError`.  Assertions
    (`I-if` to a `wrong` statement) are ordinary store-touching steps handled by
    the ok branch; a post-commit *conditional* reducibility violation is vacuous
    for a verified state and carried as the side condition `hjno_iif`;
  * **`push_c_wrong`** / **`merge_wrong`** — the **merge**: a post-commit
    termination run of `a` is merged into a non-`a` main trace ending in the
    *fatal step* of another thread `c`, which still reaches wrong from the end of
    the `a`-run;
  * **`post_commit_lm`** — Post-Commit Termination delivering an `LMRun` to a
    yielding state (or `INonSteps` to wrong) — the exact shape `merge_wrong`
    consumes;
  * **`ARun`** / **`push_green_back`** / **`partition_green`** and **`LAMix`** /
    **`push_left_back`** / **`partition_left`** — the **transaction extraction**
    in both directions: pull a thread's pre-commit (green) resp. post-commit
    (left-mover) transaction to the front of a run;
  * **`PhaseRN`** / **`PhaseRN.step`** — the **phase invariant** (phases stay in
    `{R,N}`); and **`green_decompose`** — the `(form:b)` decomposition: any run
    to wrong factors as the first committer's pre-commit transaction (a `GAMix`)
    plus the rest, with the committer then wrong or in phase `N`.

  * **`IStepsTn`** / **`extract_committer`** — the **length-indexed transaction
    extraction** that drives the outer induction's measure: since the `reduction`
    hypothesis is a `Prop`-valued `ISteps`, no `Nat` length can be read off it, so
    `IStepsTn n` records a run of exactly `n` steps (`ISteps.toN` supplies some
    `n`).  `extract_committer` fuses `green_decompose` + `partition_green` and
    tracks length: from a length-`n` run to wrong it pulls the first committer's
    entire pre-commit-through-commit transaction to the front as an `ARun`,
    leaving a **strictly shorter** (`m < n`) residual run, with the committer then
    wrong or in phase `N`.

  * **Obligation (1) — the length-indexed merge**: `NonJRunN` (a non-`a` run of
    exactly `n` steps), `push_jN` / `iter_diamondN` (the **Iterative Diamond**,
    length-preserving), `push_c_wrongN` (the fatal step reaches wrong in exactly
    one step off the end), and **`merge_wrongN`** — the merge delivering an
    `IStepsTn (q + 1)` from the end of the `a`-run, so the merged residual is
    provably bounded and the `(form:c)` recursion is well-founded.  Plus
    `IStepsTn.trans` (summing lengths) and `NonJRunN.toIStepsTn`.  And
    **`LAMixN`** / **`partition_left_n`** (with `LMRun.dest_not_wrong`) — the
    length-indexed left-mover partition that produces the `LMRun` + `NonJRunN`
    pair `merge_wrongN` consumes.

  * **Obligation (2) core — a committed thread cannot go wrong**: three facts.
      - `mover_invariant` (`istep_mover_invariant` + `nonjrun_mover_invariant`) —
        by validity (3) a non-`a` step cannot change any of `a`'s action effects,
        so along a non-`a` run `a`'s movers are *invariant*.
      - **`active_redex_judg`** and its corollaries **`active_action_le_L`** /
        **`active_branches_le_L`** — at a verified state the *active* thread's
        redex is a left-mover: the statement's judgment effect is `⊑ L` (from
        `N ;; e ≠ E`), the Evaluation-Context lemma (`Judg.eval_ctxt`) peels off
        the redex derivation with a `⊑ L` effect, and its canonical form bounds
        the redex's mover — `M A ⊑ L` for an action, *both* branch movers `⊑ L`
        for a conditional.  This is the precise content of `left_commutes_w`'s
        `hjno_iif`: a committer's conditional step cannot be `iif`-wrong.
      - **`valid_no_wrong_step`** — a verified state's active thread cannot step to
        wrong (else `preservation` would make the wrong state verified,
        contradicting Not-Wrong).
      - **`N_seq_le_L_ne_E`** / **`interfered_branches_ne_E`** — package the above
        into the exact `hjno_iif` side condition: a committer's conditional-redex
        branches compose `≠ E` at *any* state reached from its last verified state
        by a non-`a` run (`⊑ L` at the valid state, invariant along the run).
    Together: a committer that appears to wrong post-commit under interference has
    (`mover_invariant`) the same mover effect as at its last verified state, where
    (`active_*_le_L`) it is `⊑ L` and so cannot compose to `E`.  Plus the
    all-yielding / left-mover-run glue (`AllYielding`, `allYielding_of`,
    `LMRun.toINonSteps` / `.phaseRN` / `.othersYield_end`).

  * **Obligation (2) wiring — the usable wrong-case commutation**:
    **`ithreadstep_classify2`** (a `classify` variant whose instrumented-wrong
    bucket exposes whether the step is `iaction_wrong` or `iif_wrong`, and for the
    latter the offending branch) and **`left_commutes_w'`** — the wrong-case Left
    Commutativity restated with a *dischargeable* `hjno_iif` (the conditional-only
    form `interfered_branches_ne_E` supplies), replacing `left_commutes_w`'s
    over-general `∀ A` side condition.  This is what lets `(form:b)` absorb a
    committer's fatal wrong step into its block.

**The top-level assembly.**  Instead of the paper's explicit
`Post*; Pre*` block algebra, the outer induction `reorder_core` uses the measure
`2 * n + w` (run length `n`, with `w ∈ {0,1}` distinguishing an all-yielding start
from a single post-commit-active thread) — which captures the paper's
unfinished-block count without a separate block datatype:

  * `w = 0` (all-yielding): `extract_committer` pulls the first committer's
    pre-commit-through-commit transaction to the front *non-preemptively*
    (`ARun.toINonSteps`), leaving a strictly shorter residual; the committer is
    then wrong (done) or committed (recurse at `w = 1`).

  * `w = 1` (post-commit thread `a`, others yielding): `left_decompose` pulls `a`'s
    left-mover transaction to the front and either (settle) `a`'s stmt becomes
    yielding, giving an all-yielding state with a shorter residual, or (fatal) a
    step reaches wrong with `a` frozen post-commit before it.  A fatal `c = a` is
    ruled out by `committed_run_cannot_wrong` (bubble `a`'s wrong step back via
    `left_commutes_w'`, contradict with `valid_no_wrong_step`); a fatal `c ≠ a` is
    handled by `post_commit_lm` (finish `a` to a yield) + `merge_wrongN` (Iterative
    Diamond), reaching wrong from an all-yielding state with a bounded residual.

`reduction_proved` feeds a preemptive-wrong run (via `ISteps.toN`) into
`reorder_core`, and `soundness'` re-assembles Soundness on top of it.
`#print axioms soundness'` = `[propext, Classical.choice, Quot.sound]` — both
the `reduction` and `preservation` axioms are discharged; the development is
axiom-free.  No `sorry`/`admit`/`native_decide`. -/

end MoverLogic
