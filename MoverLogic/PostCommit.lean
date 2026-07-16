/-
  Post-Commit Termination (paper Lemma lem:post-commit-term).

  A thread in its post-commit phase (`𝕃_i`) of a verified state runs to a
  settled state (`ℕ_i`) under the non-preemptive scheduler: it never blocks and
  never diverges.  The proof is the paper's size-metric argument, discharged
  here with the model well-formedness the paper assumes (and the Lean model had
  omitted):

    * `NeverYields M`     — a mover spec never assigns the yield effect to an
                            action (paper: only `yield` has effect `Y`);
    * `CondTotal`         — conditional actions are exhaustive / non-blocking
                            (paper: "all conditional actions are non-blocking");
    * `GoodSizing D fs`   — a size assignment on function names that strictly
                            dominates each atomic body — this exists exactly when
                            atomic functions are non-recursive (paper: "`f()` is
                            not (directly or indirectly) recursive").

  Post-Commit Termination additionally invokes the `preservation` theorem
  (proved in `Preservation.lean`) to carry `⊢ Pi` forward along the run (as in
  the paper).
-/
import MoverLogic.ReductionThm
import MoverLogic.Canonical
import MoverLogic.Preservation

namespace MoverLogic

open Effect

/-! ### The statement size metric

`bodySize fs s` is the paper's `|s|`, with per-function sizes supplied by `fs`
(so the definition is structural on `s`).  `GoodSizing` is the well-foundedness
witness: every atomic body is strictly smaller than its function's size — which
holds iff atomic functions are non-recursive. -/

def bodySize (fs : FnName → Nat) : Stmt → Nat
  | .skip => 0
  | .wrong => 0
  | .act _ => 1
  | .yield => 1
  | .call f => fs f
  | .seq s1 s2 => 1 + bodySize fs s1 + bodySize fs s2
  | .while _ _ => 1
  | .ite _ s1 s2 => 1 + bodySize fs s1 + bodySize fs s2

/-- The non-recursion witness: `fs` strictly dominates each atomic body.  Such an
    `fs` exists precisely when the atomic call graph is well-founded. -/
def GoodSizing (D : Decls) (fs : FnName → Nat) : Prop :=
  ∀ f e S Q b, D f = some (.atomic e S Q, b) → bodySize fs b < fs f

/-- Conditional actions are exhaustive: from every store some branch fires. -/
def CondTotal : Prop :=
  ∀ (C : CondAction) (t : Tid) (σ : Store),
    (∃ σ', C.tru t σ σ') ∨ (∃ σ', C.fls t σ σ')

/-! ### Effect facts used by the metric argument -/

/-- If `a ; b ⊑ L` then `a ⊑ L` (a left-mover sequence starts with a left-mover). -/
theorem seq_le_L_imp_le_L {a b : Effect} (h : a ;; b ⊑ Effect.L) : a ⊑ Effect.L := by
  revert h; cases a <;> cases b <;> decide

/-- `R ⋢ L`. -/
theorem R_not_le_L : ¬ (Effect.R ⊑ Effect.L) := by decide

/-- Composing phase `N` with a non-yield left-mover stays `N` (hence `≠ E`). -/
theorem N_seq_eq_N_of_le_L {b : Effect} (hL : b ⊑ Effect.L) (hY : b ≠ Effect.Y) :
    Effect.N ;; b = Effect.N := by
  revert hL hY; cases b <;> decide

/-! ### Thread steps are closed under a `seq` context

Reapplying each step rule with an extended context lifts a step of `s₁` to a
step of `s₁ ; s₂`. -/

theorem IThreadStep.seqR {M D t} {s1 : Stmt} {σ : Store} {p : Phase}
    {s1' : Stmt} {σ' : Store} {p' : Phase} (s2 : Stmt)
    (h : IThreadStep M D t s1 σ p s1' σ' p') :
    IThreadStep M D t (.seq s1 s2) σ p (.seq s1' s2) σ' p' := by
  cases h with
  | iseq E s σ p => exact IThreadStep.iseq (.seqL E s2) s σ p
  | iyield E σ p => exact IThreadStep.iyield (.seqL E s2) σ p
  | iwhile E C s σ p => exact IThreadStep.iwhile (.seqL E s2) C s σ p
  | icall E f s σ p hb => exact IThreadStep.icall (.seqL E s2) f s σ p hb
  | iaction_ok E A σ σ' p hA hne => exact IThreadStep.iaction_ok (.seqL E s2) A σ σ' p hA hne
  | iaction_wrong E A σ p hp => exact IThreadStep.iaction_wrong (.seqL E s2) A σ p hp
  | iif_ok_T E C s1 s2' σ σ' p hA hne => exact IThreadStep.iif_ok_T (.seqL E s2) C s1 s2' σ σ' p hA hne
  | iif_ok_F E C s1 s2' σ σ' p hA hne => exact IThreadStep.iif_ok_F (.seqL E s2) C s1 s2' σ σ' p hA hne
  | iif_wrong_T E C s1 s2' σ σ' p hA hp => exact IThreadStep.iif_wrong_T (.seqL E s2) C s1 s2' σ σ' p hA hp
  | iif_wrong_F E C s1 s2' σ σ' p hA hp => exact IThreadStep.iif_wrong_F (.seqL E s2) C s1 s2' σ σ' p hA hp

/-- The body environment of an atomic function. -/
theorem bodies_of_atomic {D : Decls} {f : FnName} {e : Effect} {S : Pred1} {Q : Pred2}
    {b : Stmt} (hd : D f = some (.atomic e S Q, b)) : D.bodies f = some b := by
  unfold Decls.bodies; rw [hd]; rfl

/-! ### Progress in the post-commit phase

A verified statement with a left-mover effect (`e ⊑ L`), that is running (not
skip/wrong/yielding), always takes a phase-`N`-preserving thread step to a
strictly smaller statement.  This is the paper's redex case analysis: actions
are total (`M-action`'s side-condition), atomic calls shrink by non-recursion,
conditionals are exhaustive, and `while` / non-atomic-call redexes are ruled out
because their effect is `⋢ L`. -/

theorem progress {M : MoverSpec} {D : Decls} (hNY : NeverYields M) (hCT : CondTotal)
    {fs : FnName → Nat} (hfs : GoodSizing D fs) {i : Tid} {σ0 : Store} :
    ∀ (s : Stmt) (R G P Q : Pred2) (e : Effect) (σ : Store),
      Judg M D R G s P Q e → e ⊑ Effect.L → P i σ0 σ → ¬ (yielding s ∨ IsWrong s) →
      ∃ s' σ', IThreadStep M D.bodies i s σ Effect.N s' σ' Effect.N ∧
               bodySize fs s' < bodySize fs s := by
  intro s
  induction s with
  | skip => intro R G P Q e σ hJ heL hP hns; exact absurd (Or.inl (Or.inr rfl)) hns
  | wrong => intro R G P Q e σ hJ heL hP hns; exact absurd (Or.inr ⟨.hole, rfl⟩) hns
  | yield => intro R G P Q e σ hJ heL hP hns; exact absurd (Or.inl (Or.inl ⟨.hole, rfl⟩)) hns
  | act A =>
      intro R G P Q e σ hJ heL hP hns
      obtain ⟨R1, G1, P1, Q1, e1, hR, hG, hPP, hQ, he1, hnc⟩ := hJ.consequence
      cases hnc with
      | action he htot =>
          have he1L : e1 ⊑ Effect.L := le_trans he1 heL
          obtain ⟨σ', hA⟩ := htot he1L i σ
          have hmL : M A i σ ⊑ Effect.L :=
            le_trans (le_trans (M.le_lift A P1 (hPP i σ0 σ hP)) he) he1L
          have hNN : Effect.N ;; M A i σ = Effect.N := N_seq_eq_N_of_le_L hmL (hNY A i σ)
          have hne : Effect.N ;; M A i σ ≠ Effect.E := by rw [hNN]; decide
          have step := IThreadStep.iaction_ok (M := M) (D := D.bodies) (t := i) .hole A σ σ' _ hA hne
          rw [hNN] at step
          exact ⟨.skip, σ', step, by simp only [bodySize]; omega⟩
  | seq s1 s2 ih1 _ih2 =>
      intro R G P Q e σ hJ heL hP hns
      by_cases hs1 : s1 = .skip
      · subst hs1
        exact ⟨s2, σ, IThreadStep.iseq (M := M) (D := D.bodies) (t := i) .hole s2 σ _,
          by simp only [bodySize]; omega⟩
      · obtain ⟨R1, G1, P1, Qm, Q1, e1, e2, hR, hG, hPP, hQ, he, hJ1, hJ2⟩ := hJ.inv_seq
        have he1L : e1 ⊑ Effect.L := seq_le_L_imp_le_L (le_trans he heL)
        have hns1 : ¬ (yielding s1 ∨ IsWrong s1) := by
          rintro (hy | hw)
          · rcases hy with ⟨E', hE'⟩ | hsk
            · exact hns (Or.inl (Or.inl ⟨.seqL E' s2, by rw [Ctx.plug, ← hE']⟩))
            · exact hs1 hsk
          · obtain ⟨E', hE'⟩ := hw
            exact hns (Or.inr ⟨.seqL E' s2, by rw [Ctx.plug, ← hE']⟩)
        obtain ⟨s1', σ', hstep, hsz⟩ := ih1 R1 G1 P1 Qm e1 σ hJ1 he1L (hPP i σ0 σ hP) hns1
        exact ⟨.seq s1' s2, σ', IThreadStep.seqR s2 hstep, by simp only [bodySize]; omega⟩
  | «while» C s' _ih =>
      intro R G P Q e σ hJ heL hP hns
      obtain ⟨R1, G1, P1, Q1, e1, hR, hG, hPP, hQ, he1, hnc⟩ := hJ.consequence
      cases hnc with
      | wloop h1 hiter he hnl => exact absurd (le_trans he1 heL) hnl
  | ite C s1 s2 _ih1 _ih2 =>
      intro R G P Q e σ hJ heL hP hns
      obtain ⟨R1, G1, P1, Q1, e1, hR, hG, hPP, hQ, he1, hnc⟩ := hJ.consequence
      cases hnc with
      | ite h1 h2 he =>
          have hP1 : P1 i σ0 σ := hPP i σ0 σ hP
          have hjoinL := le_trans he (le_trans he1 heL : e1 ⊑ Effect.L)
          have hjtL := le_trans (le_join_left _ _) hjoinL
          have hjfL := le_trans (le_join_right _ _) hjoinL
          rcases hCT C i σ with ⟨σ', hAtru⟩ | ⟨σ', hAfls⟩
          · have hmL : M C.tru i σ ⊑ Effect.L :=
              le_trans (M.le_lift C.tru P1 hP1) (seq_le_L_imp_le_L hjtL)
            have hNN : Effect.N ;; M C.tru i σ = Effect.N := N_seq_eq_N_of_le_L hmL (hNY _ _ _)
            have hne : Effect.N ;; M C.tru i σ ≠ Effect.E := by rw [hNN]; decide
            have step := IThreadStep.iif_ok_T (M := M) (D := D.bodies) (t := i)
              .hole C s1 s2 σ σ' _ hAtru hne
            rw [hNN] at step
            exact ⟨s1, σ', step, by simp only [bodySize]; omega⟩
          · have hmL : M C.fls i σ ⊑ Effect.L :=
              le_trans (M.le_lift C.fls P1 hP1) (seq_le_L_imp_le_L hjfL)
            have hNN : Effect.N ;; M C.fls i σ = Effect.N := N_seq_eq_N_of_le_L hmL (hNY _ _ _)
            have hne : Effect.N ;; M C.fls i σ ≠ Effect.E := by rw [hNN]; decide
            have step := IThreadStep.iif_ok_F (M := M) (D := D.bodies) (t := i)
              .hole C s1 s2 σ σ' _ hAfls hne
            rw [hNN] at step
            exact ⟨s2, σ', step, by simp only [bodySize]; omega⟩
  | call f =>
      intro R G P Q e σ hJ heL hP hns
      obtain ⟨R1, G1, P1, Q1, e1, hR, hG, hPP, hQ, he1, hnc⟩ := hJ.consequence
      cases hnc with
      | callAtomic hd hpre =>
          exact ⟨_, σ, IThreadStep.icall (M := M) (D := D.bodies) (t := i) .hole f _ σ _
            (bodies_of_atomic hd), hfs f _ _ _ _ hd⟩
      | callNonAtomic hd => exact absurd (le_trans he1 heL) R_not_le_L

/-! ### Post-Commit Termination (Lemma lem:post-commit-term)

A verified state's post-commit thread `i` (in `𝕃_i`) runs to a settled state
(`ℕ_i`) under the non-preemptive scheduler.  By strong induction on the size
metric: `progress` supplies a phase-`N` step that shrinks `|s_i|`, that step is
non-preemptive because `i` is the (unique) active thread, and `preservation`
carries `⊢ Pi` forward to the next state. -/

theorem post_commit_term {M : MoverSpec} {D : Decls}
    (hNY : NeverYields M) (hCT : CondTotal) {fs : FnName → Nat} (hfs : GoodSizing D fs) :
    ∀ (n : Nat) (Pi : IState) (i : Tid),
      IStateValid M D Pi → clL Pi i →
      (∀ s p, Pi.threads[i]? = some (s, p) → bodySize fs s ≤ n) →
      ∃ Pi', INonSteps M D.bodies Pi Pi' ∧ clN Pi' i := by
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
      have hset_i : (ths.set i (s_i', Effect.N))[i]? = some (s_i', Effect.N) :=
        getElem?_set_self_of ths (s_i', Effect.N) (lt_of_getElem? hget_i)
      by_cases hset : yielding s_i' ∨ IsWrong s_i'
      · exact ⟨⟨ths.set i (s_i', Effect.N), σ'⟩, INonSteps.step hnonstep (INonSteps.refl _),
          ⟨s_i', Effect.N, hset_i, hset⟩⟩
      · have hval' : IStateValid M D ⟨ths.set i (s_i', Effect.N), σ'⟩ :=
          preservation ⟨R, G, a, σ0, hfns, hVal, hrefl, hanchor, hthreads, hcompat⟩ hnonstep
        have hlt : bodySize fs s_i' < n := Nat.lt_of_lt_of_le hsz' (hsz s_i Effect.N hget_i)
        obtain ⟨Pi'', hsteps'', hclN''⟩ :=
          ih (bodySize fs s_i') hlt ⟨ths.set i (s_i', Effect.N), σ'⟩ i hval'
            ⟨s_i', Effect.N, hset_i, rfl, hset⟩
            (by intro s p hgp
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hset_i.symm.trans hgp)
                exact Nat.le_refl _)
        exact ⟨Pi'', INonSteps.step hnonstep hsteps'', hclN''⟩
    · rw [if_neg hia] at hpre
      exact absurd (Or.inl hpre.1) hnot

end MoverLogic
