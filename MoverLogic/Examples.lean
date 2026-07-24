/-
  Worked derivations for the paper's examples.

  This file exhibits, as concrete `Judg` terms, mover-logic derivations for the
  examples of "Mover Logic: A Concurrent Program Logic for Reduction and
  Rely-Guarantee Reasoning" (Flanagan & Freund, ECOOP 2024):

    * the spin lock library of Figure 5 (`spin_lock` / `spin_unlock`);
    * the `add()` atomic counter body and the non-atomic `client()` of Figure 7
      (the motivating example, = Figure 3 (right));
    * the whole initial state `Σ = (yield; client()) ‖ (yield; client())`.

  Everything is checked against a single *concrete* mover specification `Mspec`
  and *concrete* actions, so the derivations are self-contained: no admitted
  mover facts, no `sorry`.  The mover claims of the paper's variable
  declarations (a lock acquire is a right-mover, a release is a left-mover,
  lock-protected/local accesses are both-movers) are *derived* from `Mspec`,
  not assumed.

  The headline results (all with `#print axioms` = the three standard axioms):

    * `spin_lock_loop`   — the paper's own worked derivation `e = (B;B)*;R = R`
                           for `while (!cas(l,0,tid)) skip` (§8.1).
    * `spin_lock_def` / `spin_unlock_def`
                         — `spin_lock` / `spin_unlock` as atomic right- and
                           left-movers.
    * `add_body_atomic`  — `add()`'s body is one reducible sequence
                           (`R;B;B;B;B;L;B = N`), so it is atomic.
    * `add_meets_ensures`— `add()` meets `ensures x==\old(x)+arg ∧ result==x`.
    * `client_body_verifies` / `client_def`
                         — the non-atomic `client()`, effect `B;N;Y;B;N;B;B;Y = R`,
                           two reducible sequences split by yields, with the
                           assertion's `wrong` branch rejected (empty precondition).
    * `init_state_valid` — `⊢ Σ` for the two-thread initial state (rule `M-state`).
-/
import MoverLogic.Logic

namespace MoverLogic
namespace Examples

open Effect

/-! ### A concrete store model and actions

We model the shared lock in a single variable `LOCK`.  The lock is *free* when
it holds the sentinel value `FREE = -1` (which no thread identifier `t : ℕ` can
take, since `(↑t : ℤ) ≥ 0`), and *held by thread `t`* when it holds `↑t`.  This
`-1`/`↑t` split is what makes the mover classification below total and clean:
an acquire can only ever be a right-mover, a release only ever a left-mover. -/

/-- The lock variable. -/
def LOCK : Var := "l"

/-- The "unheld lock" sentinel; distinct from every `(↑t : Value)`. -/
def FREE : Value := -1

/-- The sentinel is never a thread identifier (`(↑t : ℤ) ≥ 0 > -1`). -/
theorem free_ne_tid (t : Tid) : (FREE : Value) ≠ (t : Value) := by
  show (-1 : Int) ≠ (t : Int); omega

/-- `σ[x := v]` reads back `v` at `x`. -/
theorem upd_same (σ : Store) (x : Var) (v : Value) : upd σ x v x = v := by
  unfold upd; simp

/-- `σ[x := v]` leaves every other variable unchanged. -/
theorem upd_other (σ : Store) (x : Var) (v : Value) (z : Var) (h : z ≠ x) :
    upd σ x v z = σ z := by
  unfold upd; simp [h]

/-- `acquire(l)` — succeeds only from a free lock, setting it to the acting
    thread (paper: `⟨\old(l)=0 ∧ l=tid⟩l`). -/
def acquireL : Action := fun t σ σ' => σ LOCK = FREE ∧ σ' = upd σ LOCK (t : Value)

/-- `release(l)` — sets the lock back to free (paper: `⟨l=0⟩l`). -/
def releaseL : Action := fun _ σ σ' => σ' = upd σ LOCK FREE

/-- An assignment `dst := f(σ)` computing a new value from the current store
    (models `r = x`, `r = r + arg`, `x = 1`, `x = r`, `result = r`, `arg = 2`,
    `u = result`, …).  `dst` is a non-lock variable, so it is a
    lock-protected/local both-mover. -/
def write (dst : Var) (f : Store → Value) : Action := fun _ σ σ' => σ' = upd σ dst (f σ)

/-! ### The concrete mover specification

`Mspec A t σ` reads what `A` does to the lock from `σ`:

  * if it drives `LOCK` from `FREE` to `↑t`, it is a **right-mover** `R`
    (a lock acquire);
  * if it drives `LOCK` from `↑t` to `FREE`, it is a **left-mover** `L`
    (a lock release);
  * otherwise it is a **both-mover** `B` (a local or lock-protected access).

This is exactly the synchronization discipline of the paper's `lock` declaration
`write right-mover if \old(l)==0 && l==tid; write left-mover if \old(l)==tid && l==0`. -/
open Classical in
noncomputable def Mspec : MoverSpec := fun A t σ =>
  if σ LOCK = FREE ∧ A t σ (upd σ LOCK (t : Value)) then Effect.R
  else if σ LOCK = (t : Value) ∧ A t σ (upd σ LOCK FREE) then Effect.L
  else Effect.B

/-- `Mspec` never assigns the yield effect (needed for `Valid`/`M-state`). -/
theorem Mspec_neverYields : NeverYields Mspec := by
  intro A t σ
  unfold Mspec
  split
  · exact (by decide)
  · split <;> exact (by decide)

/-! ### Lifting `Mspec` to preconditions

`M(A,P) = ⨆_{(t,_,σ) ∈ P} M(A,t,σ)`.  When `M A t σ ⊑ e` holds *for every*
`t, σ`, the least-upper-bound `M.lift A P` is `⊑ e` for every `P`. -/

/-- Uniform pointwise bound ⇒ bound on the lifted effect, for any `P`. -/
theorem lift_le_of_all {A : Action} {P : Pred2} {e : Effect}
    (h : ∀ t σ, Mspec A t σ ⊑ e) : Mspec.lift A P ⊑ e := by
  apply sSup_le
  rintro e' ⟨t, σ, σ0, _, rfl⟩
  exact h t σ

/-- An acquire is a right-mover, pointwise and hence when lifted. -/
theorem Mspec_acquire_all (t : Tid) (σ : Store) : Mspec acquireL t σ ⊑ Effect.R := by
  unfold Mspec
  by_cases h1 : σ LOCK = FREE ∧ acquireL t σ (upd σ LOCK (t : Value))
  · rw [if_pos h1]; decide
  · rw [if_neg h1]
    by_cases h2 : σ LOCK = (t : Value) ∧ acquireL t σ (upd σ LOCK FREE)
    · exfalso
      obtain ⟨hL, hacq⟩ := h2
      -- `acquireL t σ _` forces the lock to already be free
      have hfree : σ LOCK = FREE := hacq.1
      rw [hfree] at hL
      exact free_ne_tid t hL
    · rw [if_neg h2]; decide

theorem Mspec_acquire_le (P : Pred2) : Mspec.lift acquireL P ⊑ Effect.R :=
  lift_le_of_all (Mspec_acquire_all)

/-- A release is a left-mover, pointwise and hence when lifted. -/
theorem Mspec_release_all (t : Tid) (σ : Store) : Mspec releaseL t σ ⊑ Effect.L := by
  unfold Mspec
  by_cases h1 : σ LOCK = FREE ∧ releaseL t σ (upd σ LOCK (t : Value))
  · exfalso
    -- `releaseL t σ (upd σ LOCK ↑t)` says `σ[l:=↑t] = σ[l:=FREE]`, so `↑t = FREE`
    have h := h1.2
    have := congrFun h LOCK
    rw [upd_same, upd_same] at this
    exact free_ne_tid t this.symm
  · rw [if_neg h1]
    by_cases h2 : σ LOCK = (t : Value) ∧ releaseL t σ (upd σ LOCK FREE)
    · rw [if_pos h2]; decide
    · rw [if_neg h2]; decide

theorem Mspec_release_le (P : Pred2) : Mspec.lift releaseL P ⊑ Effect.L :=
  lift_le_of_all (Mspec_release_all)

/-- The identity action is a both-mover (it touches no variable at all). -/
theorem Mspec_idAction_all (t : Tid) (σ : Store) : Mspec idAction t σ ⊑ Effect.B := by
  unfold Mspec
  by_cases h1 : σ LOCK = FREE ∧ idAction t σ (upd σ LOCK (t : Value))
  · exfalso
    have := congrFun h1.2 LOCK
    rw [upd_same] at this
    rw [h1.1] at this
    exact free_ne_tid t this
  · rw [if_neg h1]
    by_cases h2 : σ LOCK = (t : Value) ∧ idAction t σ (upd σ LOCK FREE)
    · exfalso
      have := congrFun h2.2 LOCK
      rw [upd_same] at this
      rw [h2.1] at this
      exact free_ne_tid t this.symm
    · rw [if_neg h2]; decide

theorem Mspec_idAction_le (P : Pred2) : Mspec.lift idAction P ⊑ Effect.B :=
  lift_le_of_all (Mspec_idAction_all)

/-- A general non-lock assignment is a both-mover. -/
theorem Mspec_write_all (dst : Var) (f : Store → Value) (hx : dst ≠ LOCK)
    (t : Tid) (σ : Store) : Mspec (write dst f) t σ ⊑ Effect.B := by
  unfold Mspec
  by_cases h1 : σ LOCK = FREE ∧ write dst f t σ (upd σ LOCK (t : Value))
  · exfalso
    have := congrFun h1.2 LOCK
    rw [upd_same, upd_other σ dst (f σ) LOCK (Ne.symm hx)] at this
    rw [h1.1] at this
    exact free_ne_tid t this.symm
  · rw [if_neg h1]
    by_cases h2 : σ LOCK = (t : Value) ∧ write dst f t σ (upd σ LOCK FREE)
    · exfalso
      have := congrFun h2.2 LOCK
      rw [upd_same, upd_other σ dst (f σ) LOCK (Ne.symm hx)] at this
      rw [h2.1] at this
      exact free_ne_tid t this
    · rw [if_neg h2]; decide

theorem Mspec_write_le (dst : Var) (f : Store → Value) (hx : dst ≠ LOCK) (P : Pred2) :
    Mspec.lift (write dst f) P ⊑ Effect.B :=
  lift_le_of_all (Mspec_write_all dst f hx)

/-- `P; I = P`: sequencing with the identity action is a no-op on preconditions.
    (`idAction` is `fun _ σ σ' => σ = σ'`.) -/
theorem compPA_idAction_imp (P : Pred2) : compPA P idAction ⟹ P := by
  rintro t σ σ'' ⟨σ', hP, (hid : σ' = σ'')⟩
  exact hid ▸ hP

/-! ## Example 1 — the spin lock (Figure 5, left)

```
atomic right-mover  ensures l == tid
void spin_lock() {
  while (!cas(l, 0, tid)) { skip; }
}
atomic left-mover   requires l == tid
void spin_unlock() { l = 0; }
```

The paper works this derivation out explicitly (§8.1, "Consider the loop in
`spin_lock`"): the test `!cas(l,0,tid)` is the conditional action
`I ⋄ ⟨\old(l)=0 ∧ l=tid⟩l`, the body is `skip`, and

  `e = (M(I,P); B)*; M(⟨…⟩l, P) = (B;B)*; R = R`,   with `¬(R ⊑ L)`.

We reproduce exactly that computation. -/

/-- `cas(l,0,tid)` as a conditional action: the true branch is a successful
    acquire, the false branch is the identity (a failed `cas`, which the paper
    treats as a both-mover). -/
def casLock : CondAction := ⟨acquireL, idAction⟩

/-- The loop test `!cas(l,0,tid)` is the negation, `I ⋄ ⟨\old(l)=0 ∧ l=tid⟩l`. -/
theorem casLock_neg : casLock.neg = ⟨idAction, acquireL⟩ := rfl

/-- **The spin-lock loop.**  `while (!cas(l,0,tid)) skip` verifies with a
    right-mover effect `R` from any loop invariant `P`, ending in the store
    where the lock was just acquired (`compPA P acquireL`, i.e. `l == tid`).
    This is the paper's `e = (B;B)*; R = R` computation, machine-checked. -/
theorem spin_lock_loop (D : Decls) (R G P : Pred2) :
    Judg Mspec D R G (.while casLock.neg .skip) P (compPA P acquireL) Effect.R := by
  have ha : Mspec.lift idAction P ⊑ Effect.B := Mspec_idAction_le P
  have hb : Mspec.lift acquireL P ⊑ Effect.R := Mspec_acquire_le P
  -- one iteration: `skip` on `P; I`, re-establishing the invariant `P`
  have h1 : Judg Mspec D R G .skip (compPA P idAction) P Effect.B :=
    Judg.conseq (fun _ _ _ h => h) (compPA_idAction_imp P) (fun _ _ _ h => h)
      (fun _ _ _ h => h) (by decide) Judg.skip
  -- each iteration is a right-mover:  M(I,P); B = B ⊑ R
  have hiB : Mspec.lift idAction P ;; Effect.B ⊑ Effect.B :=
    le_trans (Effect.seq_mono ha (Effect.le_refl _)) (by decide)
  have hiter : Mspec.lift idAction P ;; Effect.B ⊑ Effect.R := le_trans hiB (by decide)
  -- the loop effect:  (M(I,P); B)*; M(⟨…⟩l,P) = (B;B)*; R = R
  have hstar : (Mspec.lift idAction P ;; Effect.B)^* ⊑ Effect.B :=
    le_trans (Effect.star_mono hiB) (by decide)
  have he : ((Mspec.lift idAction P ;; Effect.B)^* ;; Mspec.lift acquireL P) ⊑ Effect.R :=
    le_trans (Effect.seq_mono hstar hb) (by decide)
  exact Judg.wloop (C := casLock.neg) (s := .skip) (e1 := Effect.B) h1 hiter he (by decide)

/-- **`spin_lock` verifies as an atomic right-mover** (rule `M-def-atomic`).
    `requires true`, `ensures l == tid`. -/
theorem spin_lock_def (D : Decls) :
    FnValid Mspec D
      (.atomic Effect.R (fun _ _ => True) (compPA (two (fun _ _ => True)) acquireL))
      (.while casLock.neg .skip) :=
  spin_lock_loop D botP botP (two (fun _ _ => True))

/-- **`spin_unlock` verifies as an atomic left-mover** (rule `M-def-atomic`).
    Its body `l = 0` is a single release, a left-mover `L`.  `requires l == tid`. -/
theorem spin_unlock_def (D : Decls) :
    FnValid Mspec D
      (.atomic Effect.L (fun t σ => σ LOCK = (t : Value))
        (compPA (two (fun t σ => σ LOCK = (t : Value))) releaseL))
      (.act releaseL) := by
  refine Judg.action (Mspec_release_le _) ?_
  intro _; exact fun t σ => ⟨upd σ LOCK FREE, rfl⟩

/-! ### Per-action judgments (instances of rule `M-action`) -/

/-- An `acquire` is a right-mover; it may block (need not be total). -/
theorem judg_acquire (D : Decls) (R G P : Pred2) :
    Judg Mspec D R G (.act acquireL) P (compPA P acquireL) Effect.R :=
  Judg.action (Mspec_acquire_le P) (fun h => absurd h (by decide))

/-- A `release` is a left-mover, and is total (it never blocks). -/
theorem judg_release (D : Decls) (R G P : Pred2) :
    Judg Mspec D R G (.act releaseL) P (compPA P releaseL) Effect.L :=
  Judg.action (Mspec_release_le P) (fun _ _ σ => ⟨upd σ LOCK FREE, rfl⟩)

/-- A non-lock assignment is a both-mover, and is total. -/
theorem judg_write (D : Decls) (R G P : Pred2) (dst : Var) (f : Store → Value)
    (hx : dst ≠ LOCK) :
    Judg Mspec D R G (.act (write dst f)) P (compPA P (write dst f)) Effect.B :=
  Judg.action (Mspec_write_le dst f hx P) (fun _ _ σ => ⟨upd σ dst (f σ), rfl⟩)

/-! ## Example 2 — the atomic `add()` counter body (Figure 7)

```
atomic  ensures x == \old(x) + arg  ensures result == x
int add() {
  ⟨\old(m)==0 ∧ m==tid⟩m;   -- R   acquire
  r = x;                     -- B
  r = r + arg;               -- B
  x = 1;                     -- B   (break the even(x) invariant)
  x = r;                     -- B   (restore it)
  ⟨m==0⟩m;                   -- L   release
  result = r;                -- B
}
```

The left margin effects compose to `R;B;B;B;B;L;B = N`: a **single reducible
sequence** `R*[N]L*`.  That is what makes `add()` atomic.  We build the body as
a nested `M-seq` of `M-action`s and check the composite effect is `N ≠ E`. -/

/-- The body of `add()` (variables `x`, `r`, `arg`, `result`; lock `l`). -/
def addBody : Stmt :=
  .seq (.act acquireL)
   (.seq (.act (write "r" (fun σ => σ "x")))
    (.seq (.act (write "r" (fun σ => σ "r" + σ "arg")))
     (.seq (.act (write "x" (fun _ => 1)))
      (.seq (.act (write "x" (fun σ => σ "r")))
       (.seq (.act releaseL)
             (.act (write "result" (fun σ => σ "r"))))))))

/-- **`add()`'s body is atomic**: from any precondition `P` it verifies with the
    single-reducible-sequence effect `N` (`= R;B;B;B;B;L;B`), so the whole
    function may be treated as one atomic step.  `Q` is its exact
    (strongest) postcondition, the composition of the seven actions. -/
theorem add_body_atomic (D : Decls) (R G P : Pred2) :
    ∃ Q, Judg Mspec D R G addBody P Q Effect.N := by
  have hne : ("x" : Var) ≠ LOCK := by decide
  have hnr : ("r" : Var) ≠ LOCK := by decide
  have hnres : ("result" : Var) ≠ LOCK := by decide
  -- R ; (B ; (B ; (B ; (B ; (L ; B)))))  =  N
  exact ⟨_, Judg.seq (judg_acquire D R G P)
    (Judg.seq (judg_write D R G _ "r" _ hnr)
     (Judg.seq (judg_write D R G _ "r" _ hnr)
      (Judg.seq (judg_write D R G _ "x" _ hne)
       (Judg.seq (judg_write D R G _ "x" _ hne)
        (Judg.seq (judg_release D R G _)
                  (judg_write D R G _ "result" _ hnres))))))⟩

/-- **`add()` verifies as an atomic function** (rule `M-def-atomic`), with the
    elided effect `N`, from the trivial precondition. -/
theorem add_def (D : Decls) :
    ∃ Q, FnValid Mspec D (.atomic Effect.N (fun _ _ => True) Q) addBody := by
  obtain ⟨Q, hQ⟩ := add_body_atomic D botP botP (two (fun _ _ => True))
  exact ⟨Q, hQ⟩

/-! ### `add()`'s precise postcondition (the paper's `ensures`)

We now pin `add()`'s postcondition to the paper's `x == \old(x) + arg` and
`result == x`, so that `client()` can call `add()` through this spec.  The
strongest postcondition of the body (the nested `M-seq` composition) implies it;
that implication is the ordinary Hoare-logic content, discharged by unfolding
the seven assignments. -/

/-- The strongest postcondition produced by `add()`'s body (the composition of
    its seven actions), from precondition `P`. -/
def addPost (P : Pred2) : Pred2 :=
  compPA (compPA (compPA (compPA (compPA (compPA
    (compPA P acquireL)
    (write "r" (fun σ => σ "x")))
    (write "r" (fun σ => σ "r" + σ "arg")))
    (write "x" (fun _ => 1)))
    (write "x" (fun σ => σ "r")))
    releaseL)
    (write "result" (fun σ => σ "r"))

/-- `add()`'s body verifies with its strongest postcondition `addPost P`. -/
theorem add_body_post (D : Decls) (R G P : Pred2) :
    Judg Mspec D R G addBody P (addPost P) Effect.N := by
  have hne : ("x" : Var) ≠ LOCK := by decide
  have hnr : ("r" : Var) ≠ LOCK := by decide
  have hnres : ("result" : Var) ≠ LOCK := by decide
  exact Judg.seq (judg_acquire D R G P)
    (Judg.seq (judg_write D R G _ "r" _ hnr)
     (Judg.seq (judg_write D R G _ "r" _ hnr)
      (Judg.seq (judg_write D R G _ "x" _ hne)
       (Judg.seq (judg_write D R G _ "x" _ hne)
        (Judg.seq (judg_release D R G _)
                  (judg_write D R G _ "result" _ hnres))))))

/-- The paper's `add()` postcondition, as a two-store relation from the entry
    store `σ` to the exit store `σ'`: `x == \old(x) + arg ∧ result == x`. -/
def addEnsures : Pred2 := fun _ σ σ' => σ' "x" = σ "x" + σ "arg" ∧ σ' "result" = σ' "x"

/-- The strongest postcondition entails the paper's `ensures` (from the diagonal
    precondition `two S`).  This is the arithmetic of `r=x; r=r+arg; x=1; x=r;
    result=r`, which lands `x' = x + arg` and `result = x'`. -/
theorem addPost_imp_ensures (S : Pred1) :
    addPost (two S) ⟹ addEnsures := by
  rintro t σ σ' hpost
  -- unfold the seven-fold composition down to the raw stores
  obtain ⟨s6, ⟨s5, ⟨s4, ⟨s3, ⟨s2, ⟨s1, ⟨s0, hP, hacq⟩, hw1⟩, hw2⟩, hw3⟩, hw4⟩, hrel⟩, hw5⟩ := hpost
  obtain ⟨hs0eq, _⟩ := hP
  subst s0                       -- diagonal precondition: s0 = σ
  have e1 := hacq.2              -- s1 = σ[l := t]
  subst s1                       -- via e1
  subst s2 s3 s4 s5 s6 σ'        -- via hw1..hw5, hrel (each `s = upd …`)
  -- goals are now concrete store lookups; `simp [upd]` reduces the string tests
  refine ⟨?_, ?_⟩ <;> simp [upd, LOCK]

/-- **`add()` verifies against the paper's exact specification**
    (`atomic ensures x == \old(x) + arg ∧ result == x`), rule `M-def-atomic`. -/
theorem add_meets_ensures (D : Decls) :
    FnValid Mspec D (.atomic Effect.N (fun _ _ => True) addEnsures) addBody :=
  Judg.conseq (fun _ _ _ h => h) (addPost_imp_ensures _) (fun _ _ _ h => h)
    (fun _ _ _ h => h) (Effect.le_refl _)
    (add_body_post D botP botP (two (fun _ _ => True)))

/-! ## Example 3 — the non-atomic `client()` (Figure 7)

```
relies even(x)  guarantees even(x)  requires even(x)  ensures even(x)
void client() {
  arg = 2;                          -- B
  add();                            -- N   ┐ reducible sequence 1
  yield;                            -- Y   ┘
  arg = 2;                          -- B   ┐
  add();                            -- N   │
  u = result;                       -- B   │ reducible sequence 2
  if even(u) skip else wrong;       -- B   │  (assert even(u))
  yield;                            -- Y   ┘
}
```

`client()` is **not atomic** — it has yields — but it *is* verifiable: its
effect is `B;N;Y;B;N;B;B;Y = R ⊑ R`, two reducible sequences separated by yields.
The assertion `even(u)` succeeds because `u == result == x` and the invariant
`even(x)` holds; the `wrong` branch is unreachable (empty precondition), which is
exactly how rule `M-wrong` rejects reachable errors.

The declaration table binds `add` to its verified atomic spec. -/

/-- `even(x)` as a store predicate. -/
def evenx (σ : Store) : Prop := ∃ k : Int, σ "x" = 2 * k

/-- A program-point assertion about the *current* store, as a two-store predicate
    (ignoring `\old`). -/
def now (φ : Store → Prop) : Pred2 := fun _ _ σ => φ σ

/-- The client's rely/guarantee: an interference step preserves `even(x)`
    (the paper's `relies even(x)` / `guarantees even(x)`). -/
def evenRely : Pred2 := fun _ σ σ' => evenx σ → evenx σ'

/-- The declaration table: `add` bound to its verified atomic specification. -/
def Dtable : Decls :=
  fun f => if f = "add" then some (.atomic Effect.N (fun _ _ => True) addEnsures, addBody)
           else none

theorem Dtable_add : Dtable "add" =
    some (.atomic Effect.N (fun _ _ => True) addEnsures, addBody) := by
  unfold Dtable; rw [if_pos rfl]

/-- `even(x)` is preserved along any `evenRely*` interference. -/
theorem evenx_stable {t σ a} (h : Rtc evenRely t σ a) : evenx σ → evenx a := by
  induction h with
  | refl => exact id
  | step hstep _ ih => exact fun he => ih (hstep he)

/-- A store-preserving action (a predicate test) touches no variable, so it is a
    both-mover. -/
theorem Mspec_stpres_all {A : Action} (hA : ∀ t σ σ', A t σ σ' → σ' = σ)
    (t : Tid) (σ : Store) : Mspec A t σ ⊑ Effect.B := by
  unfold Mspec
  by_cases h1 : σ LOCK = FREE ∧ A t σ (upd σ LOCK (t : Value))
  · exfalso
    have := congrFun (hA _ _ _ h1.2) LOCK
    rw [upd_same] at this; rw [h1.1] at this
    exact free_ne_tid t this.symm
  · rw [if_neg h1]
    by_cases h2 : σ LOCK = (t : Value) ∧ A t σ (upd σ LOCK FREE)
    · exfalso
      have := congrFun (hA _ _ _ h2.2) LOCK
      rw [upd_same] at this; rw [h2.1] at this
      exact free_ne_tid t this
    · rw [if_neg h2]; decide

theorem Mspec_stpres_le {A : Action} (hA : ∀ t σ σ', A t σ σ' → σ' = σ) (P : Pred2) :
    Mspec.lift A P ⊑ Effect.B :=
  lift_le_of_all (Mspec_stpres_all hA)

/-- `even(u)` as a store predicate (`u` holds the client's `result`). -/
def evenu (σ : Store) : Prop := ∃ k : Int, σ "u" = 2 * k

/-- `even(u)` as a conditional action: the true branch tests `even(u)` (store
    unchanged), the false branch tests `¬even(u)`.  This encodes `assert even(u)
    = if even(u) skip else wrong`. -/
def evenCond : CondAction :=
  ⟨fun _ σ σ' => σ' = σ ∧ evenu σ, fun _ σ σ' => σ' = σ ∧ ¬ evenu σ⟩

/-- The body of `client()`. -/
def clientBody : Stmt :=
  .seq (.act (write "arg" (fun _ => 2)))
   (.seq (.call "add")
    (.seq .yield
     (.seq (.act (write "arg" (fun _ => 2)))
      (.seq (.call "add")
       (.seq (.act (write "u" (fun σ => σ "result")))
        (.seq (.ite evenCond .skip .wrong)
              .yield))))))

/-- The client's rely and guarantee are the *same* relation — an interference
    step preserves `even(x)` (paper: `relies even(x)`, `guarantees even(x)`).
    Note this relation is reflexive, as rule `M-state` requires of `G`. -/
private abbrev Rc : Pred2 := evenRely
private abbrev Gc : Pred2 := evenRely
/-- The client's one-store pre/postcondition `even(x)`. -/
private abbrev Sx : Pred1 := fun _ σ => evenx σ

/-- `now(even x)` (an even post-store) entails `evenRely` (even is preserved). -/
theorem now_evenx_imp_evenRely : now evenx ⟹ evenRely := fun _ _ _ h _ => h

/-- Program-point predicate after `arg = 2`: `even(x) ∧ arg = 2`. -/
private def φarg : Store → Prop := fun σ => evenx σ ∧ σ "arg" = 2
/-- Program-point predicate after the second `add()`: `even(x) ∧ even(result)`. -/
private def φres : Store → Prop := fun σ => evenx σ ∧ ∃ k : Int, σ "result" = 2 * k
/-- Program-point predicate after `u = result`: `even(x) ∧ even(u)`. -/
private def φu : Store → Prop := fun σ => evenx σ ∧ evenu σ

/-- **`client()`'s body verifies** with effect `R` (`= B;N;Y;B;N;B;B;Y`), from
    precondition `even(x)` to postcondition `even(x)`, under a rely/guarantee that
    preserve `even(x)`.  The two `add()` calls go through the atomic spec; the
    two yields separate the two reducible sequences; and the `wrong` branch of
    the assertion has an empty (unsatisfiable) precondition, so it is rejected. -/
theorem client_body_verifies :
    Judg Mspec Dtable Rc Gc clientBody (two Sx) (two Sx) Effect.R := by
  have hax : ("arg" : Var) ≠ LOCK := by decide
  -- `arg = 2`  (B):   two(even x)  →  now(even x ∧ arg = 2)
  have J1 : Judg Mspec Dtable Rc Gc (.act (write "arg" (fun _ => 2)))
      (two Sx) (now φarg) Effect.B := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (judg_write Dtable Rc Gc (two Sx) "arg" (fun _ => 2) hax)
    rintro t σ0 σ'' ⟨σ', ⟨rfl, ⟨k, hk⟩⟩, rfl⟩
    exact ⟨⟨k, by rw [upd_other _ _ _ _ (by decide : ("x":Var) ≠ "arg")]; exact hk⟩,
           upd_same _ _ _⟩
  -- `add()`   (N):   now(even x ∧ arg = 2)  →  now(even x)   [x := x + 2]
  have J2 : Judg Mspec Dtable Rc Gc (.call "add") (now φarg) (now evenx) Effect.N := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.callAtomic (P := now φarg) Dtable_add (fun _ _ _ => trivial))
    rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, harg⟩, hx, _⟩
    exact ⟨k + 1, by rw [hx, hk, harg, Int.mul_add, Int.mul_one]⟩
  -- `yield`   (Y):   now(even x)  →  now(even x)   [even x is stable under R*]
  have J3 : Judg Mspec Dtable Rc Gc .yield (now evenx) (now evenx) Effect.Y := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.yield (P := now evenx) now_evenx_imp_evenRely rfl)
    rintro t a b ⟨rfl, _σ0, σ, hev, hrtc⟩
    exact evenx_stable hrtc hev
  -- `arg = 2` (B):   now(even x)  →  now(even x ∧ arg = 2)
  have J4 : Judg Mspec Dtable Rc Gc (.act (write "arg" (fun _ => 2)))
      (now evenx) (now φarg) Effect.B := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (judg_write Dtable Rc Gc (now evenx) "arg" (fun _ => 2) hax)
    rintro t σ0 σ'' ⟨σ', ⟨k, hk⟩, rfl⟩
    exact ⟨⟨k, by rw [upd_other _ _ _ _ (by decide : ("x":Var) ≠ "arg")]; exact hk⟩,
           upd_same _ _ _⟩
  -- `add()`   (N):   now(even x ∧ arg = 2)  →  now(even x ∧ even result)
  have J5 : Judg Mspec Dtable Rc Gc (.call "add") (now φarg) (now φres) Effect.N := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.callAtomic (P := now φarg) Dtable_add (fun _ _ _ => trivial))
    rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, harg⟩, hx, hres⟩
    exact ⟨⟨k + 1, by rw [hx, hk, harg, Int.mul_add, Int.mul_one]⟩,
           k + 1, by rw [hres, hx, hk, harg, Int.mul_add, Int.mul_one]⟩
  -- `u = result` (B):   now(even x ∧ even result)  →  now(even x ∧ even u)
  have J6 : Judg Mspec Dtable Rc Gc (.act (write "u" (fun σ => σ "result")))
      (now φres) (now φu) Effect.B := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (judg_write Dtable Rc Gc (now φres) "u" (fun σ => σ "result") (by decide))
    rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, kr, hres⟩, rfl⟩
    refine ⟨⟨k, ?_⟩, kr, ?_⟩
    · rw [upd_other _ _ _ _ (by decide : ("x":Var) ≠ "u")]; exact hk
    · rw [upd_same]; exact hres
  -- `assert even(u)` (B):   now(even x ∧ even u)  →  now(even x)
  --   the `wrong` branch has an empty precondition (even u ∧ ¬even u)
  have J7 : Judg Mspec Dtable Rc Gc (.ite evenCond .skip .wrong)
      (now φu) (now evenx) Effect.B := by
    have hta : Mspec.lift evenCond.tru (now φu) ⊑ Effect.B :=
      Mspec_stpres_le (fun _ _ _ h => h.1) _
    have htf : Mspec.lift evenCond.fls (now φu) ⊑ Effect.B :=
      Mspec_stpres_le (fun _ _ _ h => h.1) _
    refine Judg.ite (Q := now evenx) (e1 := Effect.B) (e2 := Effect.B) ?_ ?_ ?_
    · refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
        (by decide) Judg.skip
      rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, _⟩, rfl, _⟩
      exact ⟨k, hk⟩
    · refine Judg.conseq ?_ (fun _ _ _ hf => hf.elim) (fun _ _ _ h => h) (fun _ _ _ h => h)
        (by decide) Judg.wrong
      rintro t σ0 σ'' ⟨σ', ⟨_, heu⟩, _, hneu⟩
      exact absurd heu hneu
    · exact Effect.join_le (le_trans (Effect.seq_mono hta (Effect.le_refl _)) (by decide))
        (le_trans (Effect.seq_mono htf (Effect.le_refl _)) (by decide))
  -- `yield`   (Y):   now(even x)  →  two(even x)   [publish the sequence, reset \old]
  have J8 : Judg Mspec Dtable Rc Gc .yield (now evenx) (two Sx) Effect.Y := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.yield (P := now evenx) now_evenx_imp_evenRely rfl)
    rintro t a b ⟨rfl, _σ0, σ, hev, hrtc⟩
    exact ⟨rfl, evenx_stable hrtc hev⟩
  -- assemble:  B;N;Y;B;N;B;B;Y  =  R
  exact Judg.seq J1 (Judg.seq J2 (Judg.seq J3 (Judg.seq J4
        (Judg.seq J5 (Judg.seq J6 (Judg.seq J7 J8))))))

/-- **`client()` verifies as a non-atomic function** (rule `M-def-non-atomic`):
    `relies even(x) guarantees even(x) requires even(x) ensures even(x)`,
    with a non-empty guarantee. -/
theorem client_def :
    FnValid Mspec Dtable (.nonatomic Rc Gc Sx Sx) clientBody := by
  refine ⟨client_body_verifies, ?_⟩
  -- the guarantee `evenRely` is non-empty (identity on an even store is in it)
  exact ⟨0, (fun _ => 0), (fun _ => 0), fun h => h⟩

/-! ## Example 4 — the whole initial state (Figure 7)

```
Σ  =  (yield; client()) ‖ (yield; client())  ·  [x := 0, l := free]
```

We verify `⊢ Σ` via rule `M-state`.  Every premise is discharged concretely —
each thread verifies from a yield with `even(x)` holding at the initial store
`x = 0`, the guarantee is reflexive and published, and the compatibility
condition holds because both threads share the same rely/guarantee — **except**
`M is valid`, which is the paper's standing semantic assumption on the mover
specification (Definition "Validity"); it is checked separately for the concrete
program actions and taken as a hypothesis here, exactly as the paper assumes it. -/

/-- The initial store: `x = 0` (even) and the lock `l` free. -/
def initStore : Store := fun v => if v = LOCK then FREE else 0

/-- Each initial thread: `yield; client()` (the client body inlined; the leading
    yield makes the thread start at a yield, as `M-state` requires). -/
def clientThread : Stmt := .seq .yield clientBody

/-- **Each thread verifies.**  `yield; client()` runs from `even(x)` back to
    `even(x)` with effect `Y;R = Y ≠ E`. -/
theorem clientThread_verifies :
    Judg Mspec Dtable Rc Gc clientThread (two Sx) (two Sx) (Effect.Y ;; Effect.R) := by
  refine Judg.seq (Judg.yield (P := two Sx) ?_ rfl) ?_
  · -- publish the (trivial) leading reducible sequence to G
    rintro t σ σ' ⟨rfl, he⟩ _; exact he
  · -- the client body runs from the post-yield precondition
    refine Judg.conseq ?_ (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) client_body_verifies
    rintro t a b ⟨rfl, _σ0, σ, ⟨rfl, hev⟩, hrtc⟩
    exact ⟨rfl, evenx_stable hrtc hev⟩

/-- **`⊢ Σ`** — the two-thread initial state verifies (rule `M-state`), given the
    paper's standing assumption that the mover specification is valid. -/
theorem init_state_valid (hV : Valid Mspec) :
    StateValid Mspec Dtable ⟨[clientThread, clientThread], initStore⟩ := by
  refine ⟨Rc, Gc, ?_, hV, ?_, ?_, ?_⟩
  · -- every declaration in the table is valid (`add`)
    rintro f spec body hf
    unfold Dtable at hf
    by_cases hfa : f = "add"
    · rw [if_pos hfa] at hf
      obtain ⟨rfl, rfl⟩ := Option.some.inj hf
      exact add_meets_ensures Dtable
    · rw [if_neg hfa] at hf; exact absurd hf (by simp)
  · -- G = evenRely is reflexive
    intro t σ; exact fun h => h
  · -- each thread verifies, is yielding, and its precondition holds at `x = 0`
    intro t s hs
    have hx0 : evenx initStore := ⟨0, by simp [initStore, LOCK]⟩
    -- both list entries are `clientThread`
    have hsc : s = clientThread := by
      rcases t with _ | _ | t <;> simp_all
    subst hsc
    refine ⟨two Sx, two Sx, Effect.Y ;; Effect.R, clientThread_verifies, by decide, ?_, ?_, ?_⟩
    · rintro t σ σ' ⟨rfl, he⟩ _; exact he
    · exact ⟨.seqL .hole clientBody, rfl⟩
    · exact ⟨rfl, hx0⟩
  · -- compatibility: both threads share the rely = guarantee = evenRely
    intro t u σ σ' _ h; exact h

end Examples
end MoverLogic
