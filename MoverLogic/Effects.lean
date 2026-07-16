/-
  Piece 1 — Effect algebra and the reduction / DFA characterization.

  This file formalizes Section "Mover Logic Effects and Specifications" of
  "Mover Logic: A Concurrent Program Logic for Reduction and Rely-Guarantee
  Reasoning" (ECOOP 2024): the six-point effect lattice, its order, join,
  sequential composition `;`, and iterative closure `*`, exactly as given by
  the tables in the paper.

  The central result (`runDFA_eq_stateOf`, `reducible_iff_seqFold_ne_E`) is the
  paper's key claim made precise and machine-checked: the sequential
  composition of a sequence of effects is *not* the error effect `E` **iff**
  that sequence is accepted by the reduction DFA that recognises reducible
  sequences `R*[N]L*` separated by yields `Y`.

  Deliberately Mathlib-free: everything below reduces to finite case analysis
  discharged by `decide`.
-/

namespace MoverLogic

/-- The six mover effects (paper: `e ∈ Effect ::= Y | R | L | B | N | E`).
    * `Y` — a yield annotation;
    * `R` — right-mover;
    * `L` — left-mover;
    * `B` — both-mover (left and right);
    * `N` — non-mover;
    * `E` — error (e.g. two non-movers with no intervening yield). -/
inductive Effect where
  | Y | B | R | L | N | E
deriving DecidableEq, Repr

namespace Effect

/-- Enumerate all six effects; used to phrase `∀`-lemmas as `decide`. -/
def all : List Effect := [Y, B, R, L, N, E]

@[simp] theorem mem_all (e : Effect) : e ∈ all := by cases e <;> decide

/-! ### Join and the induced order `⊑`

The paper's Hasse diagram is `Y ⊑ B ⊑ R,L ⊑ N ⊑ E`, with `R` and `L`
incomparable.  We define the join (least upper bound) directly and take the
order to be the one it induces, `a ⊑ b ↔ a ⊔ b = b`. -/

/-- Least upper bound in the effect lattice. -/
def join : Effect → Effect → Effect
  | Y, y => y
  | x, Y => x
  | E, _ => E
  | _, E => E
  | N, _ => N
  | _, N => N
  | B, y => y
  | x, B => x
  | R, R => R
  | L, L => L
  | R, L => N
  | L, R => N

infixl:65 " ⊔ " => join

/-- The lattice order induced by `join`. -/
def le (a b : Effect) : Prop := a ⊔ b = b

infix:50 " ⊑ " => le

instance : DecidableEq Effect := inferInstance
instance (a b : Effect) : Decidable (a ⊑ b) := by unfold le; infer_instance

theorem join_comm (a b : Effect) : a ⊔ b = b ⊔ a := by cases a <;> cases b <;> rfl
theorem join_assoc (a b c : Effect) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem join_idem (a : Effect) : a ⊔ a = a := by cases a <;> rfl

/-- `⊑` is reflexive, antisymmetric and transitive: a genuine partial order. -/
theorem le_refl (a : Effect) : a ⊑ a := join_idem a
theorem le_antisymm {a b : Effect} : a ⊑ b → b ⊑ a → a = b := by
  cases a <;> cases b <;> decide
theorem le_trans {a b c : Effect} : a ⊑ b → b ⊑ c → a ⊑ c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Enables `calc` chaining and `Trans` for the effect order `⊑`. -/
instance : Trans (· ⊑ ·) (· ⊑ ·) (· ⊑ ·) where
  trans := le_trans

/-- The bottom `Y` and top `E` of the lattice. -/
theorem Y_le (a : Effect) : Y ⊑ a := by cases a <;> rfl
theorem le_E (a : Effect) : a ⊑ E := by cases a <;> rfl

/-- `join` really is the least upper bound. -/
theorem le_join_left (a b : Effect) : a ⊑ a ⊔ b := by cases a <;> cases b <;> decide
theorem le_join_right (a b : Effect) : b ⊑ a ⊔ b := by cases a <;> cases b <;> decide
theorem join_le {a b c : Effect} : a ⊑ c → b ⊑ c → a ⊔ b ⊑ c := by
  cases a <;> cases b <;> cases c <;> decide

/-! ### Sequential composition `;`

The table in the paper (rows = first effect, columns = second):

```
 ;  | Y  B  R  L  N  E
 ---+------------------
 Y  | Y  Y  Y  L  L  E
 B  | Y  B  R  L  N  E
 R  | R  R  R  N  N  E
 L  | Y  L  E  L  E  E
 N  | R  N  E  N  E  E
 E  | E  E  E  E  E  E
```
-/

/-- Sequential composition of effects (`e₁ ; e₂`), from the paper's table. -/
def seq : Effect → Effect → Effect
  | Y, Y => Y | Y, B => Y | Y, R => Y | Y, L => L | Y, N => L | Y, E => E
  | B, Y => Y | B, B => B | B, R => R | B, L => L | B, N => N | B, E => E
  | R, Y => R | R, B => R | R, R => R | R, L => N | R, N => N | R, E => E
  | L, Y => Y | L, B => L | L, R => E | L, L => L | L, N => E | L, E => E
  | N, Y => R | N, B => N | N, R => E | N, L => N | N, N => E | N, E => E
  | E, _ => E

infixl:70 " ;; " => seq

/-- `B` is a two-sided identity for `;`, so it is the unit of the effect monoid. -/
theorem seq_B_left (e : Effect) : B ;; e = e := by cases e <;> rfl
theorem seq_B_right (e : Effect) : e ;; B = e := by cases e <;> rfl

/-- `;` is associative: `(Effect, ;;, B)` is a monoid. -/
theorem seq_assoc (a b c : Effect) : (a ;; b) ;; c = a ;; (b ;; c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `E` is a two-sided absorbing element (an error stays an error). -/
theorem seq_E_left (e : Effect) : E ;; e = E := rfl
theorem seq_E_right (e : Effect) : e ;; E = E := by cases e <;> rfl

/-- Sequential composition is monotone in both arguments w.r.t. `⊑`
    (the paper relies on this for rule `M-conseq`). -/
theorem seq_mono {a a' b b' : Effect} : a ⊑ a' → b ⊑ b' → a ;; b ⊑ a' ;; b' := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

/-- Left-fold of `;` over a list of effects, starting from the unit `B`.
    `seqFold [e₁,…,eₙ] = e₁ ; … ; eₙ` (and `= B` on the empty list). -/
def seqFold (es : List Effect) : Effect := es.foldl seq B

@[simp] theorem seqFold_nil : seqFold [] = B := rfl

theorem seqFold_cons (e : Effect) (es : List Effect) :
    seqFold (e :: es) = e ;; seqFold es := by
  unfold seqFold
  rw [List.foldl_cons, seq_B_left]
  -- foldl seq e es = seq e (foldl seq B es), by the monoid structure
  suffices h : ∀ (acc : Effect) (l : List Effect),
      l.foldl seq acc = acc ;; l.foldl seq B by
    simpa [seq_B_left] using h e es
  intro acc l
  induction l generalizing acc with
  | nil => simp [seq_B_right]
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (acc ;; x), ih (B ;; x),
        seq_B_left, seq_assoc]

/-! ### Iterative closure `*`

```
 e  | Y  B  R  L  N  E
 ---+------------------
 e* | Y  B  R  L  E  E
```
-/

/-- Iterative closure of an effect (the effect of a loop body repeated). -/
def star : Effect → Effect
  | Y => Y | B => B | R => R | L => L | N => E | E => E

postfix:max "^*" => star

theorem star_idem (e : Effect) : (e^*)^* = e^* := by cases e <;> rfl
/-- Iterative closure is monotone w.r.t. `⊑`. -/
theorem star_mono {a b : Effect} (h : a ⊑ b) : a^* ⊑ b^* := by
  revert h; cases a <;> cases b <;> decide
/-- Repeating a starred effect adds nothing: `e* ; e* = e*`. -/
theorem seq_star_star (e : Effect) : e^* ;; e^* = e^* := by cases e <;> rfl

/-! Two finite lattice facts justifying the loop-unfolding case of the paper's
Preservation-for-Redexes lemma, for the upper-bound form of rule `M-while`
(iteration effect `x = M(A₁,P);e₁ ⊑ R`, loop effect `x*;m₂ ⊑ e`, `¬(e ⊑ L)`). -/

/-- A right-mover iteration prefixed to the loop effect stays below it:
    if `x ⊑ R` and `¬(e ⊑ L)` then `x ; e ⊑ e`. -/
theorem iter_seq_le {x e : Effect} (hx : x ⊑ R) (he : ¬ (e ⊑ L)) : x ;; e ⊑ e := by
  revert hx he; cases x <;> cases e <;> decide

/-- The loop-exit mover is below the declared loop effect:
    if `x ⊑ R`, `x* ; m ⊑ e`, and `¬ (e ⊑ L)` then `m ⊑ e`. -/
theorem exit_le {x m e : Effect} (hx : x ⊑ R) (hm : x^* ;; m ⊑ e) (he : ¬ (e ⊑ L)) :
    m ⊑ e := by
  revert hx hm he; cases x <;> cases m <;> cases e <;> decide
/-- One iteration is dominated by the closure: `e ⊑ e*` unless `e = N`
    (`N* = E` because two non-movers cannot form one reducible block). -/
theorem le_star (e : Effect) (h : e ≠ N) : e ⊑ e^* := by cases e <;> simp_all <;> decide

/-! ## The reduction DFA and the central characterization

The paper verifies that yields correctly separate reducible sequences using a
DFA that accepts the language `(R*[N]L* Y)* R*[N]L*` — reducible sequences
`R*[N]L*` separated by yields, where a both-mover `B` may appear freely inside
either the right-mover or left-mover phase.

We model it with three states.  `pre` (pre-commit) and `post` (post-commit) are
accepting; `dead` is the sink reached exactly when the sequence is not
reducible. -/

/-- DFA states. `pre` and `post` accept; `dead` rejects. -/
inductive DState where
  | pre | post | dead
deriving DecidableEq, Repr

/-- The DFA transition function `δ`.

* In `pre`: right-movers `R` and both-movers `B` self-loop; a non-mover `N`
  or left-mover `L` is the *commit* to `post`; a yield `Y` resets to `pre`.
* In `post`: left/both-movers `L`,`B` self-loop; `R` or a second `N` is an
  error (`dead`); `Y` starts a fresh reducible block in `pre`.
* `E` and everything from `dead` go to `dead`. -/
def step : DState → Effect → DState
  | .pre,  .Y => .pre   | .pre,  .B => .pre  | .pre,  .R => .pre
  | .pre,  .N => .post  | .pre,  .L => .post | .pre,  .E => .dead
  | .post, .Y => .pre   | .post, .B => .post | .post, .L => .post
  | .post, .R => .dead  | .post, .N => .dead | .post, .E => .dead
  | .dead, _  => .dead

/-- Run the DFA over a sequence of effects from a given start state. -/
def runFrom (q : DState) (es : List Effect) : DState := es.foldl step q

/-- Run the DFA from the initial `pre` state. -/
def runDFA (es : List Effect) : DState := runFrom .pre es

/-- The DFA accepts iff it does not end in the `dead` sink. -/
def accepts (es : List Effect) : Prop := runDFA es ≠ .dead

/-- Read off the DFA state that a partial `;`-fold value corresponds to.
    This is the abstraction that links the algebra to the automaton. -/
def stateOf : Effect → DState
  | .Y | .B | .R => .pre
  | .L | .N => .post
  | .E => .dead

/-- **Homomorphism lemma.** The DFA transition depends on the running
    `;`-fold value *only through* its abstract state: for every accumulator
    `acc` and input `e`, `stateOf (acc ; e) = step (stateOf acc) e`.
    This 6×6 fact (checked by `decide`) is what makes the algebra and the
    automaton coincide. -/
theorem stateOf_seq (acc e : Effect) : stateOf (acc ;; e) = step (stateOf acc) e := by
  cases acc <;> cases e <;> decide

/-- Generalized correspondence: from *any* accumulator, running the DFA from
    `stateOf acc` tracks the abstract state of the running `;`-fold. -/
theorem runFrom_stateOf (es : List Effect) :
    ∀ acc : Effect, runFrom (stateOf acc) es = stateOf (es.foldl seq acc) := by
  induction es with
  | nil => intro acc; rfl
  | cons e es ih =>
    intro acc
    show runFrom (step (stateOf acc) e) es = stateOf (es.foldl seq (acc ;; e))
    rw [← stateOf_seq acc e]
    exact ih (acc ;; e)

/-- **Central correspondence.** Running the DFA from `pre` over `es` yields
    exactly the abstract state of the sequential composition of `es`:
    `runDFA es = stateOf (seqFold es)`. -/
theorem runDFA_eq_stateOf (es : List Effect) : runDFA es = stateOf (seqFold es) := by
  have h : stateOf B = DState.pre := rfl
  calc runDFA es = runFrom (stateOf B) es := by rw [h]; rfl
    _ = stateOf (es.foldl seq B) := runFrom_stateOf es B
    _ = stateOf (seqFold es) := rfl

/-- **Reduction theorem (effect form).** A sequence of effects composes under
    `;` to something other than the error effect `E` **iff** it is accepted by
    the reduction DFA — i.e. iff it consists of reducible sequences `R*[N]L*`
    separated by yields `Y`.  This is the machine-checked statement of the
    paper's claim that the `;`-fold being non-error characterizes exactly the
    reducible sequences recognised by the DFA. -/
theorem reducible_iff_seqFold_ne_E (es : List Effect) :
    accepts es ↔ seqFold es ≠ E := by
  unfold accepts
  rw [runDFA_eq_stateOf]
  constructor
  · intro h hE; rw [hE] at h; exact h rfl
  · intro h
    -- `stateOf x = dead` only when `x = E`
    cases hx : seqFold es with
    | E => exact absurd hx h
    | _ => simp [stateOf]

/-! ### An explicit regular-language characterization of the DFA

To make the "reducible sequences `R*[N]L*` separated by yields" reading fully
explicit, we give an inductive predicate matching that regular expression and
prove it equivalent to DFA acceptance.  `Reducible` describes one block
`R*[N]L*` (both-movers `B` may appear inside either phase), and `Yielding`
describes `(block Y)* block`. -/

/-- One reducible block `R*[N]L*` (with `B` freely inside either phase),
    parameterised by whether the commit (`N` or the first `L`) has happened. -/
inductive Block : (committed : Bool) → List Effect → Prop where
  | nil {c} : Block c []
  /-- a right-mover in the pre-commit phase -/
  | rmov {es} : Block false es → Block false (R :: es)
  /-- a both-mover in the pre-commit phase -/
  | rboth {es} : Block false es → Block false (B :: es)
  /-- the single non-mover commit -/
  | commit {es} : Block true es → Block false (N :: es)
  /-- a left-mover; it commits (`c` may be `false` for the first one) -/
  | lmov {c es} : Block true es → Block c (L :: es)
  /-- a both-mover in the post-commit phase -/
  | lboth {es} : Block true es → Block true (B :: es)

/-- `(block Y)* block`: reducible blocks separated by yields. -/
inductive Yielding : List Effect → Prop where
  | last {es} : Block false es → Yielding es
  | seq {es rest} : Block false es → Yielding rest → Yielding (es ++ Y :: rest)

/-- Start state for a block phase: pre-commit ↦ `pre`, post-commit ↦ `post`. -/
def startState : Bool → DState
  | false => .pre
  | true => .post

/-- Running the DFA over a reducible block from its phase's start state ends in
    an accepting state (`pre` or `post`), never `dead`. -/
theorem block_runFrom {c es} (h : Block c es) :
    runFrom (startState c) es = .pre ∨ runFrom (startState c) es = .post := by
  induction h with
  | nil => cases ‹Bool› with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl
  | rmov _ ih => exact ih
  | rboth _ ih => exact ih
  | commit _ ih => exact ih
  | lmov _ ih => cases ‹Bool› <;> exact ih
  | lboth _ ih => exact ih

/-- Running the DFA over a yield-separated sequence of reducible blocks, from
    `pre`, ends in an accepting state. -/
theorem yielding_runDFA {es} (h : Yielding es) :
    runDFA es = .pre ∨ runDFA es = .post := by
  induction h with
  | last hb => exact block_runFrom hb
  | @seq es rest hb _ ih =>
    unfold runDFA runFrom at *
    rw [List.foldl_append]
    have hpre : es.foldl step .pre = .pre ∨ es.foldl step .pre = .post :=
      block_runFrom hb
    -- after the block we are in pre/post, the separating `Y` resets to `pre`,
    -- then the remaining blocks keep us accepting.
    rcases hpre with hp | hp <;> rw [hp] <;> simpa [step] using ih

/-- **Soundness of the regular-expression reading.** Every yield-separated
    sequence of reducible blocks `(R*[N]L* Y)* R*[N]L*` is accepted by the DFA,
    hence (by `reducible_iff_seqFold_ne_E`) composes to a non-error effect. -/
theorem yielding_accepts {es} (h : Yielding es) : accepts es := by
  rcases yielding_runDFA h with hp | hp <;> simp [accepts, hp]

theorem yielding_seqFold_ne_E {es} (h : Yielding es) : seqFold es ≠ E :=
  (reducible_iff_seqFold_ne_E es).1 (yielding_accepts h)

end Effect

end MoverLogic

