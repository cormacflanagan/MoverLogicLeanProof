/-
  Piece 3 — mover specifications and validity.

  Formalizes Section "Mover Specifications" and the `Validity` definition:
  a mover specification `M : Action × Tid × Store → Effect`, its lift to a
  precondition `M(A,P)` as the least upper bound over the pre-stores of `P`,
  and the four validity conditions that make `M`'s mover claims sound.
-/
import MoverLogic.Effects
import MoverLogic.Language

namespace MoverLogic

open Effect

/-- One-store predicate `S, T ⊆ Tid × Store`. -/
abbrev Pred1 := Tid → Store → Prop
/-- Two-store predicate `R, G, P, Q ⊆ Tid × Store × Store`. -/
abbrev Pred2 := Tid → Store → Store → Prop

/-- A mover specification `M(A, t, σ) ∈ Effect` describing how action `A`,
    taken by thread `t` from store `σ`, commutes with other threads.
    (The paper additionally assumes `M` never returns `Y`; see `NeverYields`.) -/
abbrev MoverSpec := Action → Tid → Store → Effect

/-- A mover specification never assigns the yield effect to an action. -/
def NeverYields (M : MoverSpec) : Prop := ∀ A t σ, M A t σ ≠ Effect.Y

/-! ### Finite supremum over effects

`M(A,P)` is `⨆_{(t,_,σ) ∈ P} M(A,t,σ)`.  Because `Effect` is a finite lattice,
every set of effects has a least upper bound; we define it by folding `⊔` over
the six effects (classically deciding membership) and prove it is the LUB. -/

open Classical in
/-- Least upper bound of an arbitrary set of effects. -/
noncomputable def sSup (S : Effect → Prop) : Effect :=
  Effect.all.foldl (fun acc e => if S e then acc ⊔ e else acc) Effect.Y

open Classical in
private theorem foldl_mono (S : Effect → Prop) (l : List Effect) :
    ∀ acc, acc ⊑ l.foldl (fun acc e => if S e then acc ⊔ e else acc) acc := by
  induction l with
  | nil => intro acc; exact le_refl acc
  | cons x xs ih =>
    intro acc
    have hstep : acc ⊑ (if S x then acc ⊔ x else acc) := by
      by_cases hx : S x <;> simp [hx]
      · exact le_join_left acc x
      · exact le_refl acc
    exact le_trans hstep (ih _)

open Classical in
private theorem foldl_le (S : Effect → Prop) {b : Effect} (hb : ∀ e, S e → e ⊑ b)
    (l : List Effect) :
    ∀ acc, acc ⊑ b → l.foldl (fun acc e => if S e then acc ⊔ e else acc) acc ⊑ b := by
  induction l with
  | nil => intro acc hacc; exact hacc
  | cons x xs ih =>
    intro acc hacc
    apply ih
    by_cases hx : S x <;> simp [hx]
    · exact join_le hacc (hb x hx)
    · exact hacc

open Classical in
private theorem foldl_mem_le (S : Effect → Prop) {e : Effect} (he : S e) (l : List Effect)
    (hmem : e ∈ l) :
    ∀ acc, e ⊑ l.foldl (fun acc e => if S e then acc ⊔ e else acc) acc := by
  induction l with
  | nil => intro _; exact absurd hmem (by simp)
  | cons x xs ih =>
    intro acc
    rcases List.mem_cons.1 hmem with h | h
    · subst h
      have h1 : e ⊑ acc ⊔ e := le_join_right acc e
      have h2 : acc ⊔ e ⊑ xs.foldl (fun acc e => if S e then acc ⊔ e else acc) (acc ⊔ e) :=
        foldl_mono S xs (acc ⊔ e)
      have : e ⊑ xs.foldl (fun acc e => if S e then acc ⊔ e else acc) (acc ⊔ e) :=
        le_trans h1 h2
      simpa [he] using this
    · exact ih h _

/-- `sSup S` is an upper bound: every member of `S` is `⊑ sSup S`. -/
theorem le_sSup {S : Effect → Prop} {e : Effect} (he : S e) : e ⊑ sSup S :=
  foldl_mem_le S he Effect.all (mem_all e) Effect.Y

/-- `sSup S` is the *least* upper bound. -/
theorem sSup_le {S : Effect → Prop} {b : Effect} (hb : ∀ e, S e → e ⊑ b) : sSup S ⊑ b :=
  foldl_le S hb Effect.all Effect.Y (Y_le b)

/-- `M(A, P) = ⨆_{(t,_,σ) ∈ P} M(A,t,σ)` — the effect of action `A` under
    precondition `P`, overloading `M` exactly as the paper does. -/
noncomputable def MoverSpec.lift (M : MoverSpec) (A : Action) (P : Pred2) : Effect :=
  sSup (fun e => ∃ t σ σ0, P t σ0 σ ∧ M A t σ = e)

/-- The lifted effect dominates each pointwise effect allowed by `P`. -/
theorem MoverSpec.le_lift (M : MoverSpec) (A : Action) (P : Pred2)
    {t σ σ0 : _} (h : P t σ0 σ) : M A t σ ⊑ M.lift A P :=
  le_sSup ⟨t, σ, σ0, h, rfl⟩

/-! ### Validity

`M` is *valid* when its mover claims commute correctly.  These are conditions
(1)–(4) of the paper's Definition (Validity), verbatim. -/

/-- The four validity conditions for a mover specification. -/
structure Valid (M : MoverSpec) : Prop where
  /-- (1) A right-mover can be commuted *after* a following non-mover. -/
  right : ∀ (t u : Tid) (A1 A2 : Action) (σ σ' σ'' : Store),
    t ≠ u → M A1 t σ ⊑ Effect.R → A1 t σ σ' →
    M A2 u σ' ⊑ Effect.N → A2 u σ' σ'' →
    ∃ σ''', A2 u σ σ''' ∧ A1 t σ''' σ''
  /-- (2) A left-mover can be commuted *before* a preceding non-mover. -/
  left : ∀ (t u : Tid) (A1 A2 : Action) (σ σ' σ'' : Store),
    t ≠ u → M A1 t σ ⊑ Effect.N → A1 t σ σ' →
    M A2 u σ' ⊑ Effect.L → A2 u σ' σ'' →
    ∃ σ''', A2 u σ σ''' ∧ A1 t σ''' σ''
  /-- (3) An action of one thread cannot change the effect of another's action. -/
  effect : ∀ (t u : Tid) (A1 A2 : Action) (σ σ' : Store) (e : Effect),
    t ≠ u → M A1 t σ ⊑ Effect.N → A1 t σ σ' →
    M A2 u σ = e → M A2 u σ' = e
  /-- (4) An action of one thread cannot cause another's left-mover to block. -/
  nonblock : ∀ (t u : Tid) (A1 A2 : Action) (σ σ' σ'' : Store),
    t ≠ u → M A1 t σ ⊑ Effect.N → A1 t σ σ' →
    M A2 u σ ⊑ Effect.L → A2 u σ σ'' →
    ∃ σ''', A2 u σ' σ''' ∧ A1 t σ'' σ'''

end MoverLogic
