/-
  The Prefix lemma (paper `lem:prefix`), in its original unrestricted form:

      ∅,∅ ⊢ s : P ⇒ Q ! e    ⟹    R,G ⊢ s : (P';P) ⇒ (P';Q) ! e    for all P', R, G.

  This holds because the rules `M-action`, `M-if`, and `M-while` state their
  effect antecedents as *upper bounds* (`M(A,P) ⊑ e`, etc.) rather than
  equalities.  Prefixing shrinks every lifted mover (`M(A, P';X) ⊑ M(A, X)`,
  since `post (P';X) ⊆ post X`), so by monotonicity of `;;`, `⊔`, and `*` all
  the `⊑`-antecedents transfer, while the declared effect `e` — and with it
  `M-while`'s `¬(e ⊑ L)` side condition and `M-action`'s totality side
  condition — is untouched.

  With the equality-form antecedents (`e = (M(A₁,P);e₁)*;M(A₂,P)` in `M-while`)
  the lemma is FALSE: composing with `P'` can shrink a lifted mover strictly
  (down to the bottom `Y` when `P';P` is empty), making the recomputed loop
  effect `⊑ L` and the required `M-while` instance underivable.  A
  machine-checked counterexample against the equality-form rules is preserved
  in the git history (`PrefixCounterexample.lean`); the regression `example`
  at the bottom of this file pins the judgment it exhibited as now derivable.
-/
import MoverLogic.Canonical

namespace MoverLogic

/-- Relational composition of two two-store predicates: the paper's `P' ; P`. -/
def compP2 (P' P : Pred2) : Pred2 := fun t a c => ∃ b, P' t a b ∧ P t b c

/-! ### Algebraic facts about `compP2` -/

/-- Composition is monotone in its second argument. -/
theorem compP2_mono {P' X Y : Pred2} (h : X ⟹ Y) : compP2 P' X ⟹ compP2 P' Y :=
  fun t _ c ⟨b, hb, hX⟩ => ⟨b, hb, h t b c hX⟩

/-- Associativity linking `compP2` with the action-composition `compPA`:
    `(P';P);A = P';(P;A)`. -/
theorem compPA_compP2 (P' P : Pred2) (A : Action) :
    compPA (compP2 P' P) A = compP2 P' (compPA P A) := by
  funext t a c
  apply propext
  constructor
  · rintro ⟨σ', ⟨m, hm, hPm⟩, hA⟩; exact ⟨m, hm, σ', hPm, hA⟩
  · rintro ⟨m, hm, σ', hPm, hA⟩; exact ⟨σ', ⟨m, hm, hPm⟩, hA⟩

/-- Prefixing the empty predicate stays empty. -/
theorem compP2_botP (P' : Pred2) : compP2 P' botP = botP := by
  funext t a c
  apply propext
  constructor
  · rintro ⟨_, _, hf⟩; exact hf
  · intro hf; exact hf.elim

/-- Prefixing a pointwise-empty predicate is empty. -/
theorem compP2_empty {P' P : Pred2} (h : P ⟹ botP) : compP2 P' P = botP := by
  funext t a c
  apply propext
  constructor
  · rintro ⟨b, _, hP⟩; exact h t b c hP
  · intro hf; exact hf.elim

/-- The yield postcondition of a pointwise-empty precondition is empty. -/
theorem yieldP_empty {P R : Pred2} (h : P ⟹ botP) : yieldP P R = botP := by
  funext t a b
  apply propext
  constructor
  · rintro ⟨_, σ0, σ, hP, _⟩; exact h t σ0 σ hP
  · intro hf; exact hf.elim

/-- `M.lift A P₁ = Y` whenever `P₁` is empty: the supremum is over the empty set
    of pointwise effects, so it collapses to the lattice bottom `Y`. -/
theorem lift_empty {M : MoverSpec} {A : Action} {P1 : Pred2}
    (h : ∀ t a b, ¬ P1 t a b) : M.lift A P1 = Effect.Y := by
  unfold MoverSpec.lift
  apply Effect.le_antisymm
  · apply sSup_le
    rintro e ⟨t, σ, σ0, hP, _⟩
    exact absurd hP (h t σ0 σ)
  · exact Effect.Y_le _

/-- **Prefixing shrinks lifted movers**: `post (P';X) ⊆ post X`, so the
    supremum defining `M(A, P';X)` ranges over a subset of that for `M(A,X)`. -/
theorem MoverSpec.lift_comp_le (M : MoverSpec) (A : Action) (P' X : Pred2) :
    M.lift A (compP2 P' X) ⊑ M.lift A X := by
  apply sSup_le
  rintro e ⟨t, σ, σ0, ⟨b, _, hX⟩, hM⟩
  exact hM ▸ M.le_lift A X hX

/-! ### The Prefix lemma -/

open Effect in
/-- Auxiliary induction for Prefix.  The guarantee is empty (`G0 ⟹ botP`),
    which holds for the `∅,∅` root and propagates through every rule; it kills
    the `M-yield` and `M-call-non-atomic` cases exactly as in the paper. -/
theorem Judg.prefix_aux {M : MoverSpec} {D : Decls} (P' R G : Pred2)
    (hD : ∀ f spec body, D f = some (spec, body) → FnValid M D spec body)
    {R0 G0 : Pred2} {s : Stmt} {P Q : Pred2} {e : Effect}
    (h : Judg M D R0 G0 s P Q e) (hG0 : G0 ⟹ botP) :
    Judg M D R G s (compP2 P' P) (compP2 P' Q) e := by
  revert hG0
  induction h with
  | @action R0 G0 A P e he htot =>
      intro _
      rw [← compPA_compP2]
      exact Judg.action (le_trans (M.lift_comp_le A P' P) he) htot
  | @seq R0 G0 P Q1 Q2 s1 s2 e1 e2 h1 h2 ih1 ih2 =>
      intro hG0
      exact Judg.seq (ih1 hG0) (ih2 hG0)
  | @ite R0 G0 P Q C s1 s2 e e1 e2 h1 h2 he ih1 ih2 =>
      intro hG0
      refine Judg.ite (e1 := e1) (e2 := e2) ?_ ?_ ?_
      · rw [compPA_compP2]; exact ih1 hG0
      · rw [compPA_compP2]; exact ih2 hG0
      · exact le_trans
          (join_le
            (le_trans (seq_mono (M.lift_comp_le C.tru P' P) (le_refl e1)) (le_join_left _ _))
            (le_trans (seq_mono (M.lift_comp_le C.fls P' P) (le_refl e2)) (le_join_right _ _)))
          he
  | @wloop R0 G0 P C s e e1 h1 hiter he hnl ih1 =>
      intro hG0
      rw [← compPA_compP2]
      refine Judg.wloop (e1 := e1) ?_ ?_ ?_ hnl
      · rw [compPA_compP2]; exact ih1 hG0
      · exact le_trans (seq_mono (M.lift_comp_le C.tru P' P) (le_refl e1)) hiter
      · exact le_trans
          (seq_mono (star_mono (seq_mono (M.lift_comp_le C.tru P' P) (le_refl e1)))
                    (M.lift_comp_le C.fls P' P))
          he
  | @skip R0 G0 P => intro _; exact Judg.skip
  | @wrong R0 G0 => intro _; rw [compP2_botP]; exact Judg.wrong
  | @conseq R0 G0 R1 G1 P P1 Q1 Q s e1 e hP hQ hR hG he h ih =>
      intro hG0
      exact Judg.conseq (compP2_mono hP) (compP2_mono hQ) (Implies2.refl _)
        (Implies2.refl _) he (ih (Implies2.trans hG hG0))
  | @yield R0 G0 P Q hGy hQy =>
      intro hG0
      have hPe : P ⟹ botP := Implies2.trans hGy hG0
      rw [hQy, compP2_empty hPe, yieldP_empty hPe, compP2_botP]
      exact Judg.yield (fun _ _ _ hh => hh.elim) (yieldP_empty (Implies2.refl botP)).symm
  | @callAtomic R0 G0 P f e S Qspec body hd hpre =>
      intro _
      rw [← compPA_compP2]
      exact Judg.callAtomic hd
        (fun t σ hh => hpre t σ (by obtain ⟨_, m, _, hpm⟩ := hh; exact ⟨m, hpm⟩))
  | @callNonAtomic R0 G0 f S T body hd =>
      intro hG0
      exact absurd (hD _ _ _ hd).2 (fun ⟨t, σ, σ', hg⟩ => hG0 t σ σ' hg)

/-- **Prefix** (paper `lem:prefix`).  If `∅,∅ ⊢ s : P ⇒ Q ! e` then
    `R,G ⊢ s : (P';P) ⇒ (P';Q) ! e` for all `P', R, G` — with no hypothesis on
    `P'`.  The valid declaration table `hD` discharges the `M-call-non-atomic`
    case (whose non-empty guarantee cannot sit under the empty root guarantee). -/
theorem Judg.prefix {M : MoverSpec} {D : Decls} (P' R G : Pred2)
    (hD : ∀ f spec body, D f = some (spec, body) → FnValid M D spec body)
    {s : Stmt} {P Q : Pred2} {e : Effect}
    (h : Judg M D botP botP s P Q e) :
    Judg M D R G s (compP2 P' P) (compP2 P' Q) e :=
  Judg.prefix_aux P' R G hD h (Implies2.refl botP)

/-! ### Regression: the judgment that broke the equality-form rules

Under the equality-form `M-while` this judgment was *underivable* (an empty
invariant collapses both lifted movers to `Y`, so the recomputed loop effect is
`⊑ L`, violating `¬(e ⊑ L)`) — which made the unrestricted Prefix lemma false.
Under the upper-bound form it is derivable, as Prefix requires. -/
open Effect in
example (M : MoverSpec) (D : Decls) :
    Judg M D botP botP
      (.while ⟨idAction, idAction⟩ .skip) botP (compPA botP idAction) Effect.R := by
  have hlift : ∀ A : Action, M.lift A botP = Effect.Y :=
    fun A => lift_empty (fun _ _ _ h => h)
  refine Judg.wloop (e1 := Effect.B) ?_ ?_ ?_ (by decide)
  · exact Judg.conseq (fun t a b ⟨_, hf, _⟩ => hf.elim) (Implies2.refl _)
      (Implies2.refl _) (Implies2.refl _) (le_refl _) Judg.skip
  · rw [show (⟨idAction, idAction⟩ : CondAction).tru = idAction from rfl, hlift]; decide
  · rw [show (⟨idAction, idAction⟩ : CondAction).tru = idAction from rfl,
        show (⟨idAction, idAction⟩ : CondAction).fls = idAction from rfl, hlift]
    decide

end MoverLogic
