/-
  The full soundness chain — instrumented semantics and the assembly of
  Soundness from the paper's intermediate theorems (§"Overview of Correctness
  Proof", Fig. "Instrumented semantics").

  The paper proves Soundness (⊢ Σ ⟹ Σ does not go wrong) via:
    (1) an instrumented semantics enforcing the mover spec `M` and reducibility;
    (2) a non-preemptive scheduler (context switches only at yields);
    (3) Simulation  — preemptive instrumented ≈ standard, but goes wrong more;
    (4) Reduction   — preemptive and non-preemptive instrumented agree;
    (5) Preservation + Not-Wrong for the non-preemptive instrumented semantics.

  This file mechanizes the chain.  Proved here, with no `sorry`:
    * `IStateValid.not_wrong`      — Not-Wrong for instrumented states;
    * `simulation` / `simulation_star` — the Simulation theorem and its closure;
    * `embed`                      — a verified standard state embeds into a
                                     verified instrumented state (all yielding);
    * `right_commute` / `left_commute` — the store-level commutativity at the
                                     heart of Reduction, derived from `Valid M`.

  Both hard theorems are **proved** downstream, so the development is
  axiom-free: Reduction (Theorem thm:red) as `MoverLogic.reduction_proved`
  (its trace-block algebra is mechanized across `ReductionThm`/`PostCommit`/
  `Assembly`, and Soundness is assembled there as `MoverLogic.soundness'`),
  and Preservation (Theorem thm:pres) as `MoverLogic.preservation` in
  `Preservation.lean` (the inversion stack: Evaluation Context, Consequence,
  Preservation for Redexes, Yield Stabilization, Prefix, Context Switch).
  `#print axioms soundness'` shows only Lean's standard axioms.
-/
import MoverLogic.Logic

namespace MoverLogic

open Effect

/-- Body environment used by the operational semantics. -/
abbrev BodyEnv := FnName → Option Stmt

/-- A thread phase `p ∈ {R, N}` (invariant maintained by the semantics). -/
abbrev Phase := Effect

/-- An instrumented state `Pi = ⟨p₁…pₙ⟩ · ⟨s₁…sₙ, σ⟩`: each thread carries its
    statement paired with its phase, over a shared store. -/
structure IState where
  threads : List (Stmt × Phase)
  store : Store

/-- The underlying statements of an instrumented state. -/
def IState.stmts (Pi : IState) : List Stmt := Pi.threads.map Prod.fst

/-- Every thread's phase is `R` or `N` (the invariant maintained by the
    semantics; established here for the all-`R` embedded state). -/
def PhaseRN (Q : IState) : Prop :=
  ∀ (u : Tid) (su : Stmt) (pu : Phase), Q.threads[u]? = some (su, pu) →
    pu = Effect.R ∨ pu = Effect.N

/-- A statement is *yielding* if it is `E[yield]` or has terminated (`skip`). -/
def yielding (s : Stmt) : Prop := (∃ E : Ctx, s = E.plug .yield) ∨ s = .skip

/-! ### Instrumented per-thread semantics (rules I-*) -/

/-- Instrumented per-thread step `⟨s,σ,p⟩ →ₜ ⟨s',σ',p'⟩`.  Extends the standard
    step to compose the phase with each action's mover effect and to go `wrong`
    when that composition is the error effect `E`. -/
inductive IThreadStep (M : MoverSpec) (D : BodyEnv) (t : Tid) :
    Stmt → Store → Phase → Stmt → Store → Phase → Prop where
  | iseq (E : Ctx) (s : Stmt) (σ : Store) (p : Phase) :
      IThreadStep M D t (E.plug (.seq .skip s)) σ p (E.plug s) σ p
  | iyield (E : Ctx) (σ : Store) (p : Phase) :
      IThreadStep M D t (E.plug .yield) σ p (E.plug .skip) σ Effect.R
  | iwhile (E : Ctx) (C : CondAction) (s : Stmt) (σ : Store) (p : Phase) :
      IThreadStep M D t (E.plug (.while C s)) σ p
        (E.plug (.ite C (.seq s (.while C s)) .skip)) σ p
  | icall (E : Ctx) (f : FnName) (s : Stmt) (σ : Store) (p : Phase) (h : D f = some s) :
      IThreadStep M D t (E.plug (.call f)) σ p (E.plug s) σ p
  | iaction_ok (E : Ctx) (A : Action) (σ σ' : Store) (p : Phase)
      (hA : A t σ σ') (hne : p ;; M A t σ ≠ Effect.E) :
      IThreadStep M D t (E.plug (.act A)) σ p (E.plug .skip) σ' (p ;; M A t σ)
  | iaction_wrong (E : Ctx) (A : Action) (σ : Store) (p : Phase)
      (hp : p ;; M A t σ = Effect.E) :
      IThreadStep M D t (E.plug (.act A)) σ p (E.plug .wrong) σ p
  | iif_ok_T (E : Ctx) (C : CondAction) (s1 s2 : Stmt) (σ σ' : Store) (p : Phase)
      (hA : C.tru t σ σ') (hne : p ;; M C.tru t σ ≠ Effect.E) :
      IThreadStep M D t (E.plug (.ite C s1 s2)) σ p (E.plug s1) σ' (p ;; M C.tru t σ)
  | iif_ok_F (E : Ctx) (C : CondAction) (s1 s2 : Stmt) (σ σ' : Store) (p : Phase)
      (hA : C.fls t σ σ') (hne : p ;; M C.fls t σ ≠ Effect.E) :
      IThreadStep M D t (E.plug (.ite C s1 s2)) σ p (E.plug s2) σ' (p ;; M C.fls t σ)
  | iif_wrong_T (E : Ctx) (C : CondAction) (s1 s2 : Stmt) (σ σ' : Store) (p : Phase)
      (hA : C.tru t σ σ') (hp : p ;; M C.tru t σ = Effect.E) :
      IThreadStep M D t (E.plug (.ite C s1 s2)) σ p (E.plug .wrong) σ p
  | iif_wrong_F (E : Ctx) (C : CondAction) (s1 s2 : Stmt) (σ σ' : Store) (p : Phase)
      (hA : C.fls t σ σ') (hp : p ;; M C.fls t σ = Effect.E) :
      IThreadStep M D t (E.plug (.ite C s1 s2)) σ p (E.plug .wrong) σ p

/-! ### Preemptive and non-preemptive whole-state steps -/

/-- Preemptive instrumented step `Pi → Pi'` (rule I-preemptive). -/
inductive IStep (M : MoverSpec) (D : BodyEnv) : IState → IState → Prop where
  | mk (ths : List (Stmt × Phase)) (t : Tid) (s s' : Stmt) (σ σ' : Store) (p p' : Phase)
      (hget : ths[t]? = some (s, p))
      (hstep : IThreadStep M D t s σ p s' σ' p') :
      IStep M D ⟨ths, σ⟩ ⟨ths.set t (s', p'), σ'⟩

/-- Non-preemptive instrumented step `Pi ↦ Pi'` (rule I-non-preemptive): the
    active thread `t` steps while every other thread is yielding. -/
inductive INonStep (M : MoverSpec) (D : BodyEnv) : IState → IState → Prop where
  | mk (ths : List (Stmt × Phase)) (t : Tid) (s s' : Stmt) (σ σ' : Store) (p p' : Phase)
      (hget : ths[t]? = some (s, p))
      (hstep : IThreadStep M D t s σ p s' σ' p')
      (hy : ∀ u su pu, u ≠ t → ths[u]? = some (su, pu) → yielding su) :
      INonStep M D ⟨ths, σ⟩ ⟨ths.set t (s', p'), σ'⟩

/-- Reflexive–transitive closure of the preemptive instrumented step. -/
inductive ISteps (M : MoverSpec) (D : BodyEnv) : IState → IState → Prop where
  | refl (Pi : IState) : ISteps M D Pi Pi
  | step {a b c : IState} : IStep M D a b → ISteps M D b c → ISteps M D a c

/-- Reflexive–transitive closure of the non-preemptive instrumented step. -/
inductive INonSteps (M : MoverSpec) (D : BodyEnv) : IState → IState → Prop where
  | refl (Pi : IState) : INonSteps M D Pi Pi
  | step {a b c : IState} : INonStep M D a b → INonSteps M D b c → INonSteps M D a c

theorem ISteps.step1 {M D} {a b : IState} (h : IStep M D a b) : ISteps M D a b :=
  .step h (.refl b)

/-- An instrumented state is *wrong* if some thread is about to execute `wrong`. -/
def IWrong (Pi : IState) : Prop := ∃ sp ∈ Pi.threads, IsWrong sp.1

/-! ### Verification of instrumented states `⊢ Pi` (rule I-state) -/

/-- `⊢ Pi` — an instrumented state verifies.  Bundles the premises of I-state:
    a global rely/guarantee, an active thread `a` and its sequence-initial store
    `σ₀`, all function definitions valid, `M` valid, `G` reflexive, and for each
    thread a derivation whose phase-composed effect `pₜ ;; eₜ` avoids `E`, with
    the active thread relating `σ₀` to the current store and every other thread
    yielding with a precondition over `σ₀`.  The *anchor* conjunct pins `σ₀` to
    the current store when the active index is out of range (e.g. the empty
    state) — for genuine states it is vacuous, and without it `σ₀` would be
    unmoored from the store, making Preservation unprovable. -/
def IStateValid (M : MoverSpec) (D : Decls) (Pi : IState) : Prop :=
  ∃ (R G : Pred2) (a : Tid) (σ0 : Store),
    (∀ f spec body, D f = some (spec, body) → FnValid M D spec body) ∧
    Valid M ∧
    (∀ t σ, G t σ σ) ∧
    (Pi.threads[a]? = none → σ0 = Pi.store) ∧
    (∀ t s p, Pi.threads[t]? = some (s, p) →
       ∃ P Q e, Judg M D R G s P Q e ∧ (p ;; e ≠ Effect.E) ∧ (Q ⟹ G) ∧
         (if t = a then P t σ0 Pi.store
          else yielding s ∧ ∃ σx, P t σx σ0)) ∧
    (∀ t u σ σ', t ≠ u → G t σ σ' → R u σ σ')

/-! ### Not-Wrong for instrumented states (Theorem thm:not-wrong) -/

/-- **Verified instrumented states are not wrong.**  Fully mechanized, by the
    same context-inversion on rule M-wrong used in `verified_not_wrong`. -/
theorem IStateValid.not_wrong {M : MoverSpec} {D : Decls} {Pi : IState}
    (h : IStateValid M D Pi) : ¬ IWrong Pi := by
  rintro ⟨⟨s, p⟩, hmem, E, rfl⟩
  obtain ⟨R, G, a, σ0, _hfns, _hvalid, _hrefl, _hanchor, hthreads, _hcompat⟩ := h
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have hidx : Pi.threads[i]? = some (E.plug .wrong, p) := by
    rw [List.getElem?_eq_getElem hi, hget]
  obtain ⟨P, Q, e, hJ, _hne, _hQG, hpre⟩ := hthreads i _ p hidx
  -- In either branch, `P` is inhabited, contradicting `wrong_empty`.
  split at hpre
  · exact hJ.wrong_empty E rfl i σ0 Pi.store hpre
  · obtain ⟨_, σx, hPx⟩ := hpre
    exact hJ.wrong_empty E rfl i σx σ0 hPx

/-! ### The simulation relation `Σ ~ Π` -/

/-- `Sim st Pi` — the standard state `st` matches the instrumented state `Pi`:
    same store, and `Pi`'s statements are exactly `st`'s threads. -/
def Sim (st : State) (Pi : IState) : Prop :=
  st.store = Pi.store ∧ st.threads = Pi.threads.map Prod.fst

/-- `List.map` commutes with `List.set` on the first projection. -/
private theorem map_fst_set {α β} (l : List (α × β)) (i : Nat) (x : α × β) :
    (l.set i x).map Prod.fst = (l.map Prod.fst).set i x.1 := by
  induction l generalizing i with
  | nil => rfl
  | cons hd tl ih => cases i with
    | zero => rfl
    | succ n => simp [List.set_cons_succ, List.map_cons, ih]

/-- Pairing with a constant then projecting back is the identity on a list. -/
private theorem map_pair_fst {α β} (c : β) (l : List α) :
    (l.map (fun x => (x, c))).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih]

/-- A wrong standard state maps to a wrong instrumented state. -/
theorem iwrong_of_stateWrong {st : State} {Pi : IState}
    (hsim : Sim st Pi) (hw : StateWrong st) : IWrong Pi := by
  obtain ⟨s, hmem, hW⟩ := hw
  rw [hsim.2] at hmem
  obtain ⟨sp, hsp_mem, hsp_eq⟩ := List.mem_map.1 hmem
  exact ⟨sp, hsp_mem, by rw [hsp_eq]; exact hW⟩

/-! ### Simulation (Theorem thm:sim) -/

/-- **Per-thread simulation.** Every standard thread step is matched by an
    instrumented thread step from any phase, landing either on the same
    statement/store or on a `wrong` statement (the "goes wrong more often"). -/
theorem ithreadstep_of_threadstep {M : MoverSpec} {D : BodyEnv} {t : Tid}
    {s : Stmt} {σ : Store} {s' : Stmt} {σ' : Store}
    (h : ThreadStep D t s σ s' σ') (p : Phase) :
    ∃ s'' σ'' p'', IThreadStep M D t s σ p s'' σ'' p'' ∧
      ((s'' = s' ∧ σ'' = σ') ∨ IsWrong s'') := by
  cases h with
  | eseq E s σ => exact ⟨_, _, p, .iseq E s σ p, Or.inl ⟨rfl, rfl⟩⟩
  | eyield E σ => exact ⟨_, _, Effect.R, .iyield E σ p, Or.inl ⟨rfl, rfl⟩⟩
  | eaction E A σ σ' hA =>
      by_cases hE : p ;; M A t σ = Effect.E
      · exact ⟨_, σ, p, .iaction_wrong E A σ p hE, Or.inr ⟨E, rfl⟩⟩
      · exact ⟨_, σ', _, .iaction_ok E A σ σ' p hA hE, Or.inl ⟨rfl, rfl⟩⟩
  | eifT E C s1 s2 σ σ' hA =>
      by_cases hE : p ;; M C.tru t σ = Effect.E
      · exact ⟨_, σ, p, .iif_wrong_T E C s1 s2 σ σ' p hA hE, Or.inr ⟨E, rfl⟩⟩
      · exact ⟨_, σ', _, .iif_ok_T E C s1 s2 σ σ' p hA hE, Or.inl ⟨rfl, rfl⟩⟩
  | eifF E C s1 s2 σ σ' hA =>
      by_cases hE : p ;; M C.fls t σ = Effect.E
      · exact ⟨_, σ, p, .iif_wrong_F E C s1 s2 σ σ' p hA hE, Or.inr ⟨E, rfl⟩⟩
      · exact ⟨_, σ', _, .iif_ok_F E C s1 s2 σ σ' p hA hE, Or.inl ⟨rfl, rfl⟩⟩
  | ewhile E C s σ => exact ⟨_, _, p, .iwhile E C s σ p, Or.inl ⟨rfl, rfl⟩⟩
  | ecall E f s σ hbody => exact ⟨_, _, p, .icall E f s σ p hbody, Or.inl ⟨rfl, rfl⟩⟩

/-- **Simulation.** If `Σ ~ Π` and `Σ → Σ'` then there is `Π'` with `Π → Π'` and
    either `Σ' ~ Π'` or `Π'` is wrong.  Fully mechanized. -/
theorem simulation {M : MoverSpec} {D : BodyEnv} {st : State} {Pi : IState} {st' : State}
    (hsim : Sim st Pi) (hstep : StateStep D st st') :
    ∃ Pi', IStep M D Pi Pi' ∧ (Sim st' Pi' ∨ IWrong Pi') := by
  cases hstep with
  | estate ts t s s' σ σ' hget hts =>
    obtain ⟨pths, pσ⟩ := Pi
    obtain ⟨hσ, hstmts⟩ := hsim
    -- hσ : σ = pσ  ;  hstmts : ts = pths.map Prod.fst
    subst hσ
    have hmap : (pths[t]?).map Prod.fst = some s := by
      have h1 : (pths.map Prod.fst)[t]? = some s := by rw [← hstmts]; exact hget
      rwa [List.getElem?_map] at h1
    cases hpt : pths[t]? with
    | none => rw [hpt] at hmap; simp at hmap
    | some sp =>
      obtain ⟨s0, p⟩ := sp
      rw [hpt] at hmap
      simp only [Option.map_some] at hmap
      have hs0 : s0 = s := Option.some.inj hmap
      rw [hs0] at hpt
      obtain ⟨s'', σ'', p'', histep, hdisj⟩ := ithreadstep_of_threadstep (M := M) hts p
      refine ⟨⟨pths.set t (s'', p''), σ''⟩,
        IStep.mk pths t s s'' σ σ'' p p'' hpt histep, ?_⟩
      cases hdisj with
      | inl heq =>
        obtain ⟨hs, hσ⟩ := heq
        subst s''; subst σ''
        refine Or.inl ⟨rfl, ?_⟩
        rw [map_fst_set, ← hstmts]
      | inr hwr =>
        refine Or.inr ⟨(s'', p''), ?_, hwr⟩
        have hlt : t < pths.length := (List.getElem?_eq_some_iff.1 hpt).1
        have hset : (pths.set t (s'', p''))[t]? = some (s'', p'') := by
          rw [List.getElem?_set_self]; simp [hlt]
        exact List.mem_of_getElem? hset

/-- **Simulation, closed under `→*`.** If `Σ ~ Π`, `Σ →* Σ'`, and `Σ'` is wrong,
    then `Π →* Π'` for some wrong `Π'`.  (The instrumented run may go wrong at or
    before the corresponding point.)  Fully mechanized. -/
theorem simulation_star {M : MoverSpec} {D : BodyEnv} {st st' : State}
    (hsteps : StateSteps D st st') :
    StateWrong st' → ∀ Pi, Sim st Pi → ∃ Pi', ISteps M D Pi Pi' ∧ IWrong Pi' := by
  induction hsteps with
  | refl => intro hw Pi hsim; exact ⟨Pi, .refl Pi, iwrong_of_stateWrong hsim hw⟩
  | step hstep _ ih =>
      intro hw Pi hsim
      obtain ⟨Pimid, histep, hdisj⟩ := simulation (M := M) hsim hstep
      cases hdisj with
      | inl hsimmid =>
          obtain ⟨Pi', h1, h2⟩ := ih hw Pimid hsimmid
          exact ⟨Pi', .step histep h1, h2⟩
      | inr hwrong => exact ⟨Pimid, ISteps.step1 histep, hwrong⟩

/-! ### Embedding a verified standard state into a verified instrumented state -/

/-- `R ;; e ≠ E` whenever `e ≠ E` (starting a reducible sequence in phase `R`
    keeps it non-error unless the future is already an error). -/
theorem R_seq_ne_E {e : Effect} (h : e ≠ Effect.E) : Effect.R ;; e ≠ Effect.E := by
  cases e <;> simp_all [Effect.seq]

/-- **Embedding.** A verified standard state gives a verified instrumented state
    with all phases `R`, matching statements/store, and all threads yielding.
    (This is the `⊢ Σ ⟹ ⊢ Π ∧ Σ ~ Π` step opening the Soundness proof.) -/
theorem phaseRN_map_R {ss : List Stmt} {σ : Store} :
    PhaseRN ⟨ss.map (fun s => (s, Effect.R)), σ⟩ := by
  intro u su pu hget
  have hmap : (ss[u]?).map (fun s => (s, Effect.R)) = some (su, pu) := by
    rw [← List.getElem?_map]; exact hget
  rcases hh : ss[u]? with _ | s0
  · rw [hh] at hmap; simp at hmap
  · rw [hh] at hmap
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
    exact Or.inl hmap.2.symm

theorem embed {M : MoverSpec} {D : Decls} {st : State} (h : StateValid M D st) :
    ∃ Pi, IStateValid M D Pi ∧ Sim st Pi ∧ (∀ sp ∈ Pi.threads, yielding sp.1) ∧ PhaseRN Pi := by
  obtain ⟨R, G, hfns, hvalid, hrefl, hthreads, hcompat⟩ := h
  refine ⟨⟨st.threads.map (fun s => (s, Effect.R)), st.store⟩, ?_, ?_, ?_, phaseRN_map_R⟩
  · refine ⟨R, G, 0, st.store, hfns, hvalid, hrefl, fun _ => rfl, ?_, hcompat⟩
    intro t s p hidx
    -- decode the mapped thread list: recover `st.threads[t]? = some s` and `p = R`
    have hmap : (st.threads[t]?).map (fun x => (x, Effect.R)) = some (s, p) := by
      rw [← List.getElem?_map]; exact hidx
    have key : st.threads[t]? = some s ∧ p = Effect.R := by
      rcases hh : st.threads[t]? with _ | s0
      · rw [hh] at hmap; simp at hmap
      · rw [hh] at hmap
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
        exact ⟨congrArg some hmap.1, hmap.2.symm⟩
    obtain ⟨hst, rfl⟩ := key
    obtain ⟨P, Q, e, hJ, hne, hQG, hy, hPtt⟩ := hthreads t s hst
    refine ⟨P, Q, e, hJ, R_seq_ne_E hne, hQG, ?_⟩
    split
    · exact hPtt
    · exact ⟨Or.inl hy, st.store, hPtt⟩
  · exact ⟨rfl, (map_pair_fst Effect.R st.threads).symm⟩
  · intro sp hmem
    obtain ⟨s0, hs0mem, hsp⟩ := List.mem_map.1 hmem
    obtain ⟨i, hi, hgeti⟩ := List.getElem_of_mem hs0mem
    have hidx : st.threads[i]? = some s0 := by rw [List.getElem?_eq_getElem hi, hgeti]
    obtain ⟨_, _, _, _, _, _, hy, _⟩ := hthreads i s0 hidx
    rw [← hsp]; exact Or.inl hy

/-! ### The two hard theorems

`reduction` (Theorem thm:red) and `preservation` (Theorem thm:pres) are the
paper's two deepest results.  Both are now **mechanized**:

* **Reduction** is proved as `MoverLogic.reduction_proved` in `Assembly.lean`
  (from the trace-block algebra built across `ReductionThm`/`PostCommit`/
  `Assembly`), and `soundness'` there re-assembles Soundness on top.
* **Preservation** is proved as `MoverLogic.preservation` in
  `Preservation.lean` (from the inversion stack: Evaluation Context,
  Consequence, Preservation for Redexes, Yield Stabilization, Prefix,
  Context Switch), together with its `↦*`-closure `preservation_star`.

No axioms remain: `#print axioms soundness'` shows only Lean's standard
axioms. -/

/-! ### Store-level commutativity — the crux of Reduction, from `Valid`

These are the mover-commutativity facts (paper Lemmas Right/Left Commutativity)
at the level of stores, obtained directly from mover-spec validity.  They are
the mathematical core on which the state-level Reduction proof rests. -/

/-- Right-movers commute *after* a following non-mover (Validity (1)). -/
theorem right_commute {M : MoverSpec} (hV : Valid M) {t u : Tid} {A1 A2 : Action}
    {σ σ' σ'' : Store} (htu : t ≠ u)
    (h1 : M A1 t σ ⊑ Effect.R) (hA1 : A1 t σ σ')
    (h2 : M A2 u σ' ⊑ Effect.N) (hA2 : A2 u σ' σ'') :
    ∃ σ''', A2 u σ σ''' ∧ A1 t σ''' σ'' :=
  hV.right t u A1 A2 σ σ' σ'' htu h1 hA1 h2 hA2

/-- Left-movers commute *before* a preceding non-mover (Validity (2)). -/
theorem left_commute {M : MoverSpec} (hV : Valid M) {t u : Tid} {A1 A2 : Action}
    {σ σ' σ'' : Store} (htu : t ≠ u)
    (h1 : M A1 t σ ⊑ Effect.N) (hA1 : A1 t σ σ')
    (h2 : M A2 u σ' ⊑ Effect.L) (hA2 : A2 u σ' σ'') :
    ∃ σ''', A2 u σ σ''' ∧ A1 t σ''' σ'' :=
  hV.left t u A1 A2 σ σ' σ'' htu h1 hA1 h2 hA2

/-! ### Soundness (Theorem thm:sound)

Soundness is assembled in `Assembly.lean` as `MoverLogic.soundness'`, on top of
the *proved* Reduction (`reduction_proved`) — embed `Σ` into a verified,
all-yielding instrumented `Π`; run Simulation to a wrong preemptive `Π'`; apply
Reduction to reach a wrong non-preemptive `Π''`; apply Preservation; contradict
with Not-Wrong.  It lives there (not here) because Reduction is proved downstream
of this module, so `#print axioms soundness'` shows no `reduction`. -/

end MoverLogic
