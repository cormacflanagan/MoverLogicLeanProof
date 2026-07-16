/-
  Piece 4 — the Mover Logic proof system.

  Formalizes Figures "Mover Logic proof rules" and "proof rules for function
  definitions, calls, and run-time states": the one- and two-store predicate
  operators, the main judgment `R,G |- s : P => Q ! e` (`Judg`), the function
  specification judgments (`FnValid`), and the state judgment `⊢ Σ`
  (`StateValid`).
-/
import MoverLogic.Effects
import MoverLogic.Language
import MoverLogic.Specs

namespace MoverLogic

-- NOTE: we deliberately do *not* `open Effect`, because the judgment's
-- rely/guarantee metavariables `R`, `G` and effect names would otherwise clash
-- with the effect constructors `Effect.R`, `Effect.L`, `Effect.N`, ….

/-! ### Predicate operators (paper: "One-Store and Two-Store Predicates") -/

/-- `⌈S⌉` — lift a one-store predicate to the diagonal two-store predicate
    `{(t,σ,σ) | (t,σ) ∈ S}`. -/
def two (S : Pred1) : Pred2 := fun t σ σ' => σ' = σ ∧ S t σ

/-- `post P` — project a two-store predicate onto its post-stores. -/
def post (P : Pred2) : Pred1 := fun t σ' => ∃ σ, P t σ σ'

/-- The identity two-store predicate `I = {(t,σ,σ)}`. -/
def Ipred : Pred2 := fun _ σ σ' => σ' = σ

/-- `P ; A` — sequential composition of a two-store predicate with an action. -/
def compPA (P : Pred2) (A : Action) : Pred2 :=
  fun t σ σ'' => ∃ σ', P t σ σ' ∧ A t σ' σ''

/-- `∅` — the empty (unsatisfiable) two-store predicate. -/
def botP : Pred2 := fun _ _ _ => False

/-- Reflexive–transitive closure of a two-store predicate, per thread (`R*`). -/
inductive Rtc (R : Pred2) : Tid → Store → Store → Prop where
  | refl (t σ) : Rtc R t σ σ
  | step {t σ σ' σ''} : R t σ σ' → Rtc R t σ' σ'' → Rtc R t σ σ''

/-- `yield P R` — the postcondition entering a new reducible sequence after a
    yield: interference `R*` is applied and each `\old x` is reset to `x`.
    Paper: `{(t,σ',σ') | (t,_,σ) ∈ P ∧ (t,σ,σ') ∈ R*}`. -/
def yieldP (P R : Pred2) : Pred2 :=
  fun t a b => a = b ∧ ∃ σ0 σ, P t σ0 σ ∧ Rtc R t σ a

/-- Implication (containment) of two-store predicates. -/
def Implies2 (P Q : Pred2) : Prop := ∀ t σ σ', P t σ σ' → Q t σ σ'
/-- Implication (containment) of one-store predicates. -/
def Implies1 (S T : Pred1) : Prop := ∀ t σ, S t σ → T t σ

infix:50 " ⟹ " => Implies2
infix:50 " ⟹₁ " => Implies1

/-- An action is *total* (never blocks): from every pre-store some step exists. -/
def Total (A : Action) : Prop := ∀ t σ, ∃ σ', A t σ σ'

/-! ### Function specifications and declaration tables -/

/-- Function specification (paper `fn_spec`): atomic (reducible body) or
    non-atomic (may contain yields, so carries rely/guarantee). -/
inductive FnSpec where
  /-- `atomic e requires S ensures Q` -/
  | atomic (e : Effect) (S : Pred1) (Q : Pred2)
  /-- `relies R guarantees G requires S ensures T` -/
  | nonatomic (R G : Pred2) (S T : Pred1)

/-- A declaration table maps a function name to its specification and body. -/
abbrev Decls := FnName → Option (FnSpec × Stmt)

/-- The body environment underlying a declaration table — the view the
    operational semantics (`ThreadStep`/`StateStep`) uses. -/
def Decls.bodies (D : Decls) : FnName → Option Stmt := fun f => (D f).map Prod.snd

/-! ### The main judgment `R,G ⊢ s : P ⇒ Q ! e`

Fixed parameters: the mover specification `M` and declaration table `D`. -/

/-- Mover-logic derivability, one constructor per proof rule in the paper. -/
inductive Judg (M : MoverSpec) (D : Decls) :
    Pred2 → Pred2 → Stmt → Pred2 → Pred2 → Effect → Prop where
  /-- **M-action**: `M(A,P) ⊑ e`, and if `e ⊑ L` then `A` is total. -/
  | action {R G : Pred2} {A : Action} {P : Pred2} {e : Effect}
      (he : M.lift A P ⊑ e) (htot : e ⊑ Effect.L → Total A) :
      Judg M D R G (.act A) P (compPA P A) e
  /-- **M-seq**. -/
  | seq {R G P Q1 Q2 : Pred2} {s1 s2 : Stmt} {e1 e2 : Effect}
      (h1 : Judg M D R G s1 P Q1 e1) (h2 : Judg M D R G s2 Q1 Q2 e2) :
      Judg M D R G (.seq s1 s2) P Q2 (e1 ;; e2)
  /-- **M-if**: the ascribed effect bounds both branches' effects. -/
  | ite {R G P Q : Pred2} {C : CondAction} {s1 s2 : Stmt} {e e1 e2 : Effect}
      (h1 : Judg M D R G s1 (compPA P C.tru) Q e1)
      (h2 : Judg M D R G s2 (compPA P C.fls) Q e2)
      (he : (M.lift C.tru P ;; e1) ⊔ (M.lift C.fls P ;; e2) ⊑ e) :
      Judg M D R G (.ite C s1 s2) P Q e
  /-- **M-while**: loop invariant `P`; each iteration is a right-mover
      (`M(A₁,P);e₁ ⊑ R`, so an iteration cannot commit and keep looping); the
      ascribed effect bounds the loop's effect and must not be `⊑ L` (so the
      loop cannot be placed post-commit). -/
  | wloop {R G P : Pred2} {C : CondAction} {s : Stmt} {e e1 : Effect}
      (h1 : Judg M D R G s (compPA P C.tru) P e1)
      (hiter : M.lift C.tru P ;; e1 ⊑ Effect.R)
      (he : ((M.lift C.tru P ;; e1)^* ;; M.lift C.fls P) ⊑ e)
      (hnl : ¬ (e ⊑ Effect.L)) :
      Judg M D R G (.while C s) P (compPA P C.fls) e
  /-- **M-skip**. -/
  | skip {R G P : Pred2} : Judg M D R G .skip P P Effect.B
  /-- **M-wrong**: unsatisfiable pre/postcondition rejects reachable `wrong`. -/
  | wrong {R G : Pred2} : Judg M D R G .wrong botP botP Effect.B
  /-- **M-conseq**. -/
  | conseq {R G R1 G1 P P1 Q1 Q : Pred2} {s : Stmt} {e1 e : Effect}
      (hP : P ⟹ P1) (hQ : Q1 ⟹ Q) (hR : R ⟹ R1) (hG : G1 ⟹ G)
      (he : e1 ⊑ e) (h : Judg M D R1 G1 s P1 Q1 e1) :
      Judg M D R G s P Q e
  /-- **M-yield**: publish `P` to `G`; new sequence starts at `yield P R`. -/
  | yield {R G P Q : Pred2}
      (hG : P ⟹ G) (hQ : Q = yieldP P R) :
      Judg M D R G .yield P Q Effect.Y
  /-- **M-call-atomic**. -/
  | callAtomic {R G P : Pred2} {f : FnName} {e : Effect} {S : Pred1} {Q : Pred2} {body : Stmt}
      (hd : D f = some (.atomic e S Q, body)) (hpre : post P ⟹₁ S) :
      Judg M D R G (.call f) P (compPA P (fun t σ σ' => Q t σ σ')) e
  /-- **M-call-non-atomic**. -/
  | callNonAtomic {R G : Pred2} {f : FnName} {S T : Pred1} {body : Stmt}
      (hd : D f = some (.nonatomic R G S T, body)) :
      Judg M D R G (.call f) (two S) (two T) Effect.R

/-! ### Function-definition judgment `⊢ fn` -/

/-- `⊢ fn` for a spec/body pair (rules M-def-atomic and M-def-non-atomic).
    The atomic rule's non-recursion side-condition is passed as `hnonrec`. -/
def FnValid (M : MoverSpec) (D : Decls) : FnSpec → Stmt → Prop
  | .atomic e S Q, body =>
      -- M-def-atomic: verified with empty rely/guarantee (forces yield-freedom)
      Judg M D botP botP body (two S) Q e
  | .nonatomic R G S T, body =>
      -- M-def-non-atomic: effect at most R, and a non-empty guarantee
      Judg M D R G body (two S) (two T) Effect.R ∧ (∃ t σ σ', G t σ σ')

/-! ### State judgment `⊢ Σ` (rule M-state) -/

/-- `IsYielding s` — `s = E[yield]` for some evaluation context (the paper
    requires every thread to start at a yield). -/
def IsYielding (s : Stmt) : Prop := ∃ E : Ctx, s = E.plug .yield

/-- `⊢ Σ` — a run-time state verifies.  Bundles all premises of rule M-state:
    a global rely `R` and guarantee `G` such that every function definition is
    valid, `M` is valid, `G` is reflexive, every thread verifies with a
    non-error effect from a `yielding` statement whose precondition holds at the
    current store and whose postcondition is published to `G`, and each thread's
    guarantee is contained in every other thread's rely. -/
def StateValid (M : MoverSpec) (D : Decls) (st : State) : Prop :=
  ∃ R G : Pred2,
    (∀ f spec body, D f = some (spec, body) → FnValid M D spec body) ∧
    Valid M ∧
    (∀ t σ, G t σ σ) ∧
    (∀ t s, st.threads[t]? = some s →
       ∃ P Q e, Judg M D R G s P Q e ∧ e ≠ Effect.E ∧ (Q ⟹ G) ∧
                IsYielding s ∧ P t st.store st.store) ∧
    (∀ t u σ σ', t ≠ u → G t σ σ' → R u σ σ')

/-! ### Context inversion for `wrong`

The semantic content of rule M-wrong: any statement derivable by `Judg` that has
the shape `E[wrong]` must have an *unsatisfiable* precondition.  Used by both the
standard and instrumented Not-Wrong theorems. -/

/-- If `Judg M D R G s P Q e` and `s = E[wrong]`, then `P` is unsatisfiable. -/
theorem Judg.wrong_empty {M : MoverSpec} {D : Decls}
    {R G P Q : Pred2} {s : Stmt} {e : Effect} (h : Judg M D R G s P Q e) :
    ∀ (E : Ctx), s = E.plug .wrong → ∀ t σ σ', ¬ P t σ σ' := by
  induction h with
  | @action R G A P e he htot =>
      intro E hE; exact absurd hE (by cases E <;> simp [Ctx.plug])
  | @seq R G P Q1 Q2 s1 s2 e1 e2 h1 h2 ih1 ih2 =>
      intro E hE t σ σ' hP
      cases E with
      | hole => simp [Ctx.plug] at hE
      | seqL E' s2' =>
          simp only [Ctx.plug] at hE
          have hs1 : s1 = E'.plug .wrong := (Stmt.seq.inj hE).1
          exact ih1 E' hs1 t σ σ' hP
  | @ite R G P Q C s1 s2 e e1 e2 h1 h2 he ih1 ih2 =>
      intro E hE; exact absurd hE (by cases E <;> simp [Ctx.plug])
  | @wloop R G P C s e e1 h1 hiter he hnl ih1 =>
      intro E hE; exact absurd hE (by cases E <;> simp [Ctx.plug])
  | @skip R G P =>
      intro E hE; exact absurd hE (by cases E <;> simp [Ctx.plug])
  | @wrong R G =>
      intro E hE t σ σ' hbot; exact hbot
  | @conseq R G R1 G1 P P1 Q1 Q s e1 e hP hQ hR hG he h ih =>
      intro E hE t σ σ' hPt
      exact ih E hE t σ σ' (hP t σ σ' hPt)
  | @yield R G P Q hG hQ =>
      intro E hE; exact absurd hE (by cases E <;> simp [Ctx.plug])
  | @callAtomic R G P f e S Q body hd hpre =>
      intro E hE; exact absurd hE (by cases E <;> simp [Ctx.plug])
  | @callNonAtomic R G f S T body hd =>
      intro E hE; exact absurd hE (by cases E <;> simp [Ctx.plug])

/-! ### Sanity checks: small derivations in the system -/

variable (M : MoverSpec) (D : Decls) (R G P : Pred2)

/-- `skip` verifies with the both-mover effect (rule M-skip). -/
example : Judg M D R G .skip P P Effect.B := .skip

/-- `skip; skip` verifies; its effect `B;;B` computes to `B` (definitionally). -/
example : Judg M D R G (.seq .skip .skip) P P Effect.B := .seq .skip .skip

/-- `wrong` is derivable only from the empty precondition, so it can never be
    reached from a satisfiable state — the essence of rule M-wrong. -/
example : Judg M D R G .wrong botP botP Effect.B := .wrong

/-- Consequence can raise the effect (here `B ⊑ N`) and weaken pre/post. -/
example : Judg M D R G .skip P P Effect.N :=
  .conseq (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
    (by decide) .skip

end MoverLogic
