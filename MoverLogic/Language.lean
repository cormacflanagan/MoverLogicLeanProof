/-
  Piece 2 — the Mover Logic Language (MML): syntax and operational semantics.

  Formalizes the figure "Mover Logic Language" from the paper: stores, actions,
  statements, evaluation contexts, the per-thread step relation `⟨s,σ⟩ →_t ⟨s',σ'⟩`,
  the whole-state step `Σ → Σ'`, and what it means for a state to *go wrong*.
-/

namespace MoverLogic

/-- Values.  The paper leaves `Value` abstract; integers suffice for the model. -/
abbrev Value := Int

/-- Program variables (`x, y, r, m, …`).  Thread-local `rₜ` are ordinary
    globals reserved for thread `t`, exactly as in the paper. -/
abbrev Var := String

/-- A store maps variables to values (`σ ∈ Var → Value`). -/
abbrev Store := Var → Value

/-- Thread identifiers `Tid = {1, 2, …}` (we use all of `ℕ`; `0` is a convenient
    "unheld lock" sentinel as in the paper's lock encoding). -/
abbrev Tid := Nat

/-- Function names. -/
abbrev FnName := String

/-- An **action** `A ⊆ Tid × Store × Store` — a relation that may depend on the
    acting thread's identifier. -/
abbrev Action := Tid → Store → Store → Prop

/-- A **conditional action** `[A₁ ⋅ A₂]`: `A₁` for the true/success case, `A₂`
    for the false/failure case. -/
structure CondAction where
  tru : Action
  fls : Action

/-- Negation of a conditional action swaps the two branches (paper: `!⟨A₁·A₂⟩ = ⟨A₂·A₁⟩`). -/
def CondAction.neg (c : CondAction) : CondAction := ⟨c.fls, c.tru⟩

/-- MML statements (paper: `s ::= skip | wrong | A | s;s | if C s s | while C s | f() | yield`). -/
inductive Stmt where
  | skip : Stmt
  | wrong : Stmt
  | act : Action → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : CondAction → Stmt → Stmt → Stmt
  | while : CondAction → Stmt → Stmt
  | call : FnName → Stmt
  | yield : Stmt

/-- Evaluation contexts `E ::= • | E ; s` — a hole nested to the left of `;`. -/
inductive Ctx where
  | hole : Ctx
  | seqL : Ctx → Stmt → Ctx

/-- Plug a statement into a context: `E[s]`. -/
def Ctx.plug : Ctx → Stmt → Stmt
  | .hole, s => s
  | .seqL E s2, s => .seq (E.plug s) s2

/-- The identity action `I = {(t,σ,σ)}`. -/
def idAction : Action := fun _ σ σ' => σ = σ'

/-- Point update of a store: `σ[x := v]`. -/
def upd (σ : Store) (x : Var) (v : Value) : Store :=
  fun y => if y = x then v else σ y

/-! ### Per-thread operational semantics `⟨s, σ⟩ →ₜ ⟨s', σ'⟩`

A declaration environment `D : FnName → Option Stmt` gives function bodies
(the paper keeps `D` implicit). -/

/-- Per-thread small-step relation, indexed by the acting thread `t` and the
    function-body environment `D`.  One constructor per evaluation rule in the
    paper's figure. -/
inductive ThreadStep (D : FnName → Option Stmt) (t : Tid) :
    Stmt → Store → Stmt → Store → Prop where
  /-- E-seq: `E[skip; s] → E[s]`. -/
  | eseq (E : Ctx) (s : Stmt) (σ : Store) :
      ThreadStep D t (E.plug (.seq .skip s)) σ (E.plug s) σ
  /-- E-yield: `E[yield] → E[skip]` (yields have no runtime effect). -/
  | eyield (E : Ctx) (σ : Store) :
      ThreadStep D t (E.plug .yield) σ (E.plug .skip) σ
  /-- E-action: `E[A] → E[skip]` updating `σ` to any `σ'` with `(t,σ,σ') ∈ A`. -/
  | eaction (E : Ctx) (A : Action) (σ σ' : Store) (h : A t σ σ') :
      ThreadStep D t (E.plug (.act A)) σ (E.plug .skip) σ'
  /-- E-if (true branch): `(t,σ,σ') ∈ A₁`. -/
  | eifT (E : Ctx) (C : CondAction) (s1 s2 : Stmt) (σ σ' : Store) (h : C.tru t σ σ') :
      ThreadStep D t (E.plug (.ite C s1 s2)) σ (E.plug s1) σ'
  /-- E-if (false branch): `(t,σ,σ') ∈ A₂`. -/
  | eifF (E : Ctx) (C : CondAction) (s1 s2 : Stmt) (σ σ' : Store) (h : C.fls t σ σ') :
      ThreadStep D t (E.plug (.ite C s1 s2)) σ (E.plug s2) σ'
  /-- E-while: unfold one iteration into an `if`. -/
  | ewhile (E : Ctx) (C : CondAction) (s : Stmt) (σ : Store) :
      ThreadStep D t (E.plug (.while C s)) σ
        (E.plug (.ite C (.seq s (.while C s)) .skip)) σ
  /-- E-call: inline the body of `f` from `D`. -/
  | ecall (E : Ctx) (f : FnName) (s : Stmt) (σ : Store) (h : D f = some s) :
      ThreadStep D t (E.plug (.call f)) σ (E.plug s) σ

/-- An execution state `Σ = ⟨s₁ … sₙ, σ⟩`: a thread pool and a shared store. -/
structure State where
  threads : List Stmt
  store : Store

/-- Whole-state step (rule E-State): some thread `t` takes a per-thread step. -/
inductive StateStep (D : FnName → Option Stmt) : State → State → Prop where
  | estate (ts : List Stmt) (t : Tid) (s s' : Stmt) (σ σ' : Store)
      (hget : ts[t]? = some s)
      (hstep : ThreadStep D t s σ s' σ') :
      StateStep D ⟨ts, σ⟩ ⟨ts.set t s', σ'⟩

/-- Reflexive–transitive closure of the state step relation (`Σ →* Σ'`). -/
inductive StateSteps (D : FnName → Option Stmt) : State → State → Prop where
  | refl (st : State) : StateSteps D st st
  | step {st₁ st₂ st₃ : State} :
      StateStep D st₁ st₂ → StateSteps D st₂ st₃ → StateSteps D st₁ st₃

/-! ### Going wrong -/

/-- A statement is *about to go wrong* if it is `E[wrong]` for some context. -/
def IsWrong (s : Stmt) : Prop := ∃ E : Ctx, s = E.plug .wrong

/-- A state is *wrong* if some thread is about to execute `wrong`. -/
def StateWrong (st : State) : Prop := ∃ s ∈ st.threads, IsWrong s

/-- A state *goes wrong* if it can reach a wrong state. -/
def GoesWrong (D : FnName → Option Stmt) (st : State) : Prop :=
  ∃ st', StateSteps D st st' ∧ StateWrong st'

/-! ### Basic sanity lemmas -/

/-- `wrong` itself is wrong (via the empty context). -/
theorem isWrong_wrong : IsWrong .wrong := ⟨.hole, rfl⟩

/-- Plugging into a nested sequence composes contexts. -/
theorem plug_seqL (E : Ctx) (s s2 : Stmt) :
    (Ctx.seqL E s2).plug s = .seq (E.plug s) s2 := rfl

/-- `StateSteps` is transitive (used pervasively in the soundness proof). -/
theorem StateSteps.trans {D} {a b c : State}
    (h1 : StateSteps D a b) (h2 : StateSteps D b c) : StateSteps D a c := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact .step s (ih h2)

/-- A single step lifts to the closure. -/
theorem StateStep.toSteps {D} {a b : State} (h : StateStep D a b) : StateSteps D a b :=
  .step h (.refl b)

/-- Worked example: the two-thread program `⟨assert(x ≥ 0) ‖ (x := 1)⟩` from a
    store with `x ≥ 0`.  We exhibit one concrete reduction step of thread 1
    (the write), showing the semantics actually fires.  `assert B` desugars to
    `if B skip wrong`. -/
example :
    let D : FnName → Option Stmt := fun _ => none
    let write1 : Action := fun _ σ σ' => σ' = upd σ "x" 1
    StateStep D ⟨[.skip, .act write1], fun _ => 0⟩
                ⟨[.skip, .skip], upd (fun _ => 0) "x" 1⟩ := by
  intro D write1
  have h : StateStep D ⟨[.skip, .act write1], fun _ => (0:Int)⟩
      ⟨([.skip, .act write1]).set 1 .skip, upd (fun _ => 0) "x" 1⟩ := by
    refine StateStep.estate _ 1 (.act write1) .skip _ _ rfl ?_
    exact ThreadStep.eaction .hole write1 _ _ rfl
  simpa using h

end MoverLogic
