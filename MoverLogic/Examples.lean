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

  Thread-local variables are modelled faithfully: `r`, `arg`, `result`, `u` are
  the paper's `r_tid`, resolved to `loc "r" t` for the acting thread `t`, so one
  shared `add`/`client` body serves every thread and different threads touch
  disjoint locals.  Only the counter `x` and the lock `l` are shared.

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

/-! ### Thread-local variable names

A thread-local variable `r_tid` (paper: "each thread accesses a separate variable
`r_tid`") is modelled as the name `r` tagged with the acting thread.  The tag is a
`(t+1)`-character unary marker, so the encoding is injective in a way we can prove
without wrestling `Nat.repr`: names differ from the one-character globals `x`, `l`
by *length*, and two locals with different base names differ after cancelling the
shared tag.  These are the only string facts the derivations need. -/

/-- A `(t+1)`-character tag, distinguishing thread `t`'s locals. -/
def tag : Nat → String
  | 0 => "a"
  | n + 1 => "a" ++ tag n

theorem tag_length (t : Nat) : (tag t).length = t + 1 := by
  induction t with
  | zero => decide
  | succ n ih => rw [tag, String.length_append, ih]; have : "a".length = 1 := rfl; omega

/-- `loc name t` — thread `t`'s copy of the local variable `name`. -/
def loc (name : Var) (t : Tid) : Var := name ++ tag t

/-- A thread-local variable is never a one-character global (length ≥ 2 > 1). -/
theorem loc_ne_global {name : Var} (hn : 1 ≤ name.length) {g : Var}
    (hg : g.length = 1) (t : Tid) : loc name t ≠ g := by
  intro h; have hl := congrArg String.length h
  rw [loc, String.length_append, tag_length, hg] at hl; omega

/-- Different base names give different thread-local variables (same thread). -/
theorem loc_ne_loc {a b : Var} (h : a ≠ b) (t : Tid) : loc a t ≠ loc b t := by
  intro he; apply h
  have hd := congrArg String.toList he
  rw [loc, loc, String.toList_append, String.toList_append] at hd
  exact String.toList_inj.mp (List.append_cancel_right hd)

/-- `acquire(l)` — succeeds only from a free lock, setting it to the acting
    thread (paper: `⟨\old(l)=0 ∧ l=tid⟩l`). -/
def acquireL : Action := fun t σ σ' => σ LOCK = FREE ∧ σ' = upd σ LOCK (t : Value)

/-- `release(l)` — sets the lock back to free (paper: `⟨l=0⟩l`). -/
def releaseL : Action := fun _ σ σ' => σ' = upd σ LOCK FREE

/-- A thread-aware assignment `d(t) := f(t, σ)` — writes the variable `d t`
    (a global like `x`, or a thread-local like `loc "r" t`) with a value that may
    read the acting thread's own variables.  Models `r_t = x`, `r_t = r_t + arg_t`,
    `x = 1`, `x = r_t`, `result_t = r_t`, `arg_t = 2`, `u_t = result_t`, ….  As
    long as `d t` is not the lock, it is a lock-protected/local both-mover. -/
def gen (d : Tid → Var) (f : Tid → Store → Value) : Action :=
  fun t σ σ' => σ' = upd σ (d t) (f t σ)

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

/-- A thread-aware non-lock assignment is a both-mover. -/
theorem Mspec_gen_all {d : Tid → Var} {f : Tid → Store → Value} (hd : ∀ t, d t ≠ LOCK)
    (t : Tid) (σ : Store) : Mspec (gen d f) t σ ⊑ Effect.B := by
  unfold Mspec
  by_cases h1 : σ LOCK = FREE ∧ gen d f t σ (upd σ LOCK (t : Value))
  · exfalso
    have := congrFun h1.2 LOCK
    rw [upd_same, upd_other σ (d t) (f t σ) LOCK (Ne.symm (hd t))] at this
    rw [h1.1] at this
    exact free_ne_tid t this.symm
  · rw [if_neg h1]
    by_cases h2 : σ LOCK = (t : Value) ∧ gen d f t σ (upd σ LOCK FREE)
    · exfalso
      have := congrFun h2.2 LOCK
      rw [upd_same, upd_other σ (d t) (f t σ) LOCK (Ne.symm (hd t))] at this
      rw [h2.1] at this
      exact free_ne_tid t this
    · rw [if_neg h2]; decide

theorem Mspec_gen_le {d : Tid → Var} {f : Tid → Store → Value} (hd : ∀ t, d t ≠ LOCK)
    (P : Pred2) : Mspec.lift (gen d f) P ⊑ Effect.B :=
  lift_le_of_all (Mspec_gen_all hd)

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

/-- A thread-aware non-lock assignment is a both-mover, and is total. -/
theorem judg_gen (D : Decls) (R G P : Pred2) (d : Tid → Var) (f : Tid → Store → Value)
    (hd : ∀ t, d t ≠ LOCK) :
    Judg Mspec D R G (.act (gen d f)) P (compPA P (gen d f)) Effect.B :=
  Judg.action (Mspec_gen_le hd P) (fun _ t σ => ⟨upd σ (d t) (f t σ), rfl⟩)

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

/-! `r`, `arg`, `result` are **thread-local** (`loc "r" t` = the paper's `r_tid`),
so one shared `add` body works for every thread; `x` is the shared counter. -/

/-- `d t ≠ l` for `d ∈ {loc "r", loc "arg", loc "result", const "x"}` — the
    variables `add`/`client` write are never the lock. -/
theorem locR_ne_lock : ∀ t, loc "r" t ≠ LOCK := fun t => loc_ne_global (by decide) (by decide) t
theorem locArg_ne_lock : ∀ t, loc "arg" t ≠ LOCK := fun t => loc_ne_global (by decide) (by decide) t
theorem locRes_ne_lock : ∀ t, loc "result" t ≠ LOCK := fun t => loc_ne_global (by decide) (by decide) t
theorem locU_ne_lock : ∀ t, loc "u" t ≠ LOCK := fun t => loc_ne_global (by decide) (by decide) t
theorem x_ne_L : ("x" : Var) ≠ LOCK := by decide
theorem x_ne_lock : ∀ t : Tid, (fun _ : Tid => ("x" : Var)) t ≠ LOCK := fun _ => x_ne_L

/-- Thread-locals are distinct from the shared counter `x`. -/
theorem locArg_ne_x (t : Tid) : loc "arg" t ≠ "x" := loc_ne_global (by decide) (by decide) t
theorem locRes_ne_x (t : Tid) : loc "result" t ≠ "x" := loc_ne_global (by decide) (by decide) t
theorem locU_ne_x (t : Tid) : loc "u" t ≠ "x" := loc_ne_global (by decide) (by decide) t

/-- The body of `add()`, with thread-local `r`, `arg`, `result` and shared `x`. -/
def addBody : Stmt :=
  .seq (.act acquireL)
   (.seq (.act (gen (loc "r") (fun _ σ => σ "x")))
    (.seq (.act (gen (loc "r") (fun t σ => σ (loc "r" t) + σ (loc "arg" t))))
     (.seq (.act (gen (fun _ => "x") (fun _ _ => 1)))
      (.seq (.act (gen (fun _ => "x") (fun t σ => σ (loc "r" t))))
       (.seq (.act releaseL)
             (.act (gen (loc "result") (fun t σ => σ (loc "r" t)))))))))

/-- **`add()`'s body is atomic**: from any precondition `P` it verifies with the
    single-reducible-sequence effect `N` (`= R;B;B;B;B;L;B`), so the whole
    function may be treated as one atomic step. -/
theorem add_body_atomic (D : Decls) (R G P : Pred2) :
    ∃ Q, Judg Mspec D R G addBody P Q Effect.N :=
  ⟨_, Judg.seq (judg_acquire D R G P)
    (Judg.seq (judg_gen D R G _ (loc "r") _ locR_ne_lock)
     (Judg.seq (judg_gen D R G _ (loc "r") _ locR_ne_lock)
      (Judg.seq (judg_gen D R G _ (fun _ => "x") _ x_ne_lock)
       (Judg.seq (judg_gen D R G _ (fun _ => "x") _ x_ne_lock)
        (Judg.seq (judg_release D R G _)
                  (judg_gen D R G _ (loc "result") _ locRes_ne_lock))))))⟩

/-- **`add()` verifies as an atomic function** (rule `M-def-atomic`). -/
theorem add_def (D : Decls) :
    ∃ Q, FnValid Mspec D (.atomic Effect.N (fun _ _ => True) Q) addBody :=
  add_body_atomic D botP botP (two (fun _ _ => True))

/-! ### `add()`'s precise postcondition (the paper's `ensures`) -/

/-- The strongest postcondition produced by `add()`'s body, from precondition `P`. -/
def addPost (P : Pred2) : Pred2 :=
  compPA (compPA (compPA (compPA (compPA (compPA
    (compPA P acquireL)
    (gen (loc "r") (fun _ σ => σ "x")))
    (gen (loc "r") (fun t σ => σ (loc "r" t) + σ (loc "arg" t))))
    (gen (fun _ => "x") (fun _ _ => 1)))
    (gen (fun _ => "x") (fun t σ => σ (loc "r" t))))
    releaseL)
    (gen (loc "result") (fun t σ => σ (loc "r" t)))

/-- `add()`'s body verifies with its strongest postcondition `addPost P`. -/
theorem add_body_post (D : Decls) (R G P : Pred2) :
    Judg Mspec D R G addBody P (addPost P) Effect.N :=
  Judg.seq (judg_acquire D R G P)
    (Judg.seq (judg_gen D R G _ (loc "r") _ locR_ne_lock)
     (Judg.seq (judg_gen D R G _ (loc "r") _ locR_ne_lock)
      (Judg.seq (judg_gen D R G _ (fun _ => "x") _ x_ne_lock)
       (Judg.seq (judg_gen D R G _ (fun _ => "x") _ x_ne_lock)
        (Judg.seq (judg_release D R G _)
                  (judg_gen D R G _ (loc "result") _ locRes_ne_lock))))))

/-- The paper's `add()` postcondition, thread-local: from entry `σ` to exit `σ'`,
    `x == \old(x) + arg_tid ∧ result_tid == x`. -/
def addEnsures : Pred2 :=
  fun t σ σ' => σ' "x" = σ "x" + σ (loc "arg" t) ∧ σ' (loc "result" t) = σ' "x"

set_option linter.unusedSimpArgs false in
/-- The strongest postcondition entails the paper's `ensures` (from the diagonal
    precondition `two S`).  This is the arithmetic of `r=x; r=r+arg; x=1; x=r;
    result=r` on thread `t`'s own `r`, `arg`, `result`.  (The final `simp` is
    given the full pairwise-distinctness set so it can peel every `upd`; not all
    of it fires on both conjuncts, hence the linter is silenced.) -/
theorem addPost_imp_ensures (S : Pred1) :
    addPost (two S) ⟹ addEnsures := by
  rintro t σ σ' hpost
  obtain ⟨s6, ⟨s5, ⟨s4, ⟨s3, ⟨s2, ⟨s1, ⟨s0, hP, hacq⟩, hw1⟩, hw2⟩, hw3⟩, hw4⟩, hrel⟩, hw5⟩ := hpost
  obtain ⟨hs0eq, _⟩ := hP
  subst s0
  have e1 := hacq.2
  subst s1
  subst s2 s3 s4 s5 s6 σ'
  -- distinctness of the variables touched (thread `t`'s locals vs `x` vs the lock)
  have a2 : loc "r" t ≠ "x" := loc_ne_global (by decide) (by decide) t
  have a3 : loc "arg" t ≠ loc "r" t := loc_ne_loc (by decide) t
  have a4 : loc "arg" t ≠ "x" := loc_ne_global (by decide) (by decide) t
  have a6 : loc "result" t ≠ "x" := loc_ne_global (by decide) (by decide) t
  have a8 : loc "result" t ≠ loc "r" t := loc_ne_loc (by decide) t
  refine ⟨?_, ?_⟩ <;>
    simp [gen, upd, x_ne_L, x_ne_L.symm,
      locR_ne_lock t, (locR_ne_lock t).symm, locArg_ne_lock t, (locArg_ne_lock t).symm,
      locRes_ne_lock t, (locRes_ne_lock t).symm,
      a2, a2.symm, a3, a3.symm, a4, a4.symm, a6, a6.symm, a8, a8.symm]

/-- **`add()` verifies against the paper's exact specification**
    (`atomic ensures x == \old(x) + arg_tid ∧ result_tid == x`), rule `M-def-atomic`. -/
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

/-- `even(x)` as a store predicate (`x` is the shared counter). -/
def evenx (σ : Store) : Prop := ∃ k : Int, σ "x" = 2 * k

/-- A program-point assertion about the *current* store and acting thread, as a
    two-store predicate (ignoring `\old`).  Thread-indexed so it can mention the
    acting thread's own locals (`loc "u" t`, …). -/
def now (φ : Tid → Store → Prop) : Pred2 := fun t _ σ => φ t σ

/-- The `even(x)` invariant as a thread-indexed point predicate. -/
def ex : Tid → Store → Prop := fun _ σ => evenx σ

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

/-- `even(u_tid)` as a thread-indexed store predicate (`u` is thread-local). -/
def evenu (t : Tid) (σ : Store) : Prop := ∃ k : Int, σ (loc "u" t) = 2 * k

/-- `even(u)` as a conditional action: the true branch tests `even(u_tid)` (store
    unchanged), the false branch tests `¬even(u_tid)`.  Encodes `assert even(u)
    = if even(u) skip else wrong`. -/
def evenCond : CondAction :=
  ⟨fun t σ σ' => σ' = σ ∧ evenu t σ, fun t σ σ' => σ' = σ ∧ ¬ evenu t σ⟩

/-- The body of `client()`, with thread-local `arg`, `u`, `result` and shared `x`. -/
def clientBody : Stmt :=
  .seq (.act (gen (loc "arg") (fun _ _ => 2)))
   (.seq (.call "add")
    (.seq .yield
     (.seq (.act (gen (loc "arg") (fun _ _ => 2)))
      (.seq (.call "add")
       (.seq (.act (gen (loc "u") (fun t σ => σ (loc "result" t))))
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
theorem now_ex_imp_evenRely : now ex ⟹ evenRely := fun _ _ _ h _ => h

/-- Program-point predicate after `arg = 2`: `even(x) ∧ arg_tid = 2`. -/
private def φarg : Tid → Store → Prop := fun t σ => evenx σ ∧ σ (loc "arg" t) = 2
/-- Predicate after the second `add()`: `even(x) ∧ even(result_tid)`. -/
private def φres : Tid → Store → Prop := fun t σ => evenx σ ∧ ∃ k : Int, σ (loc "result" t) = 2 * k
/-- Predicate after `u = result`: `even(x) ∧ even(u_tid)`. -/
private def φu : Tid → Store → Prop := fun t σ => evenx σ ∧ evenu t σ

/-- **`client()`'s body verifies** with effect `R` (`= B;N;Y;B;N;B;B;Y`), from
    precondition `even(x)` to postcondition `even(x)`, under a rely/guarantee that
    preserve `even(x)`.  Each thread uses its own `arg_tid`, `u_tid`, `result_tid`;
    the two `add()` calls go through the atomic spec; the two yields separate the
    two reducible sequences; and the `wrong` branch of the assertion has an empty
    (unsatisfiable) precondition, so it is rejected. -/
theorem client_body_verifies :
    Judg Mspec Dtable Rc Gc clientBody (two Sx) (two Sx) Effect.R := by
  -- `arg = 2`  (B):   two(even x)  →  now(even x ∧ arg = 2)
  have J1 : Judg Mspec Dtable Rc Gc (.act (gen (loc "arg") (fun _ _ => 2)))
      (two Sx) (now φarg) Effect.B := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (judg_gen Dtable Rc Gc (two Sx) (loc "arg") (fun _ _ => 2) locArg_ne_lock)
    rintro t σ0 σ'' ⟨σ', ⟨rfl, ⟨k, hk⟩⟩, rfl⟩
    exact ⟨⟨k, by simp [upd, (locArg_ne_x t).symm]; exact hk⟩, by simp [upd]⟩
  -- `add()`   (N):   now(even x ∧ arg = 2)  →  now(even x)   [x := x + arg]
  have J2 : Judg Mspec Dtable Rc Gc (.call "add") (now φarg) (now ex) Effect.N := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.callAtomic (P := now φarg) Dtable_add (fun _ _ _ => trivial))
    rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, harg⟩, hx, _⟩
    exact ⟨k + 1, by rw [hx, hk, harg, Int.mul_add, Int.mul_one]⟩
  -- `yield`   (Y):   now(even x)  →  now(even x)   [even x is stable under R*]
  have J3 : Judg Mspec Dtable Rc Gc .yield (now ex) (now ex) Effect.Y := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.yield (P := now ex) now_ex_imp_evenRely rfl)
    rintro t a b ⟨rfl, _σ0, σ, hev, hrtc⟩
    exact evenx_stable hrtc hev
  -- `arg = 2` (B):   now(even x)  →  now(even x ∧ arg = 2)
  have J4 : Judg Mspec Dtable Rc Gc (.act (gen (loc "arg") (fun _ _ => 2)))
      (now ex) (now φarg) Effect.B := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (judg_gen Dtable Rc Gc (now ex) (loc "arg") (fun _ _ => 2) locArg_ne_lock)
    rintro t σ0 σ'' ⟨σ', ⟨k, hk⟩, rfl⟩
    exact ⟨⟨k, by simp [upd, (locArg_ne_x t).symm]; exact hk⟩, by simp [upd]⟩
  -- `add()`   (N):   now(even x ∧ arg = 2)  →  now(even x ∧ even result)
  have J5 : Judg Mspec Dtable Rc Gc (.call "add") (now φarg) (now φres) Effect.N := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.callAtomic (P := now φarg) Dtable_add (fun _ _ _ => trivial))
    rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, harg⟩, hx, hres⟩
    exact ⟨⟨k + 1, by rw [hx, hk, harg, Int.mul_add, Int.mul_one]⟩,
           k + 1, by rw [hres, hx, hk, harg, Int.mul_add, Int.mul_one]⟩
  -- `u = result` (B):   now(even x ∧ even result)  →  now(even x ∧ even u)
  have J6 : Judg Mspec Dtable Rc Gc (.act (gen (loc "u") (fun t σ => σ (loc "result" t))))
      (now φres) (now φu) Effect.B := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (judg_gen Dtable Rc Gc (now φres) (loc "u") (fun t σ => σ (loc "result" t))
        locU_ne_lock)
    rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, kr, hres⟩, rfl⟩
    refine ⟨⟨k, ?_⟩, kr, ?_⟩
    · simp [upd, (locU_ne_x t).symm]; exact hk
    · simp only [upd_same]; exact hres
  -- `assert even(u)` (B):   now(even x ∧ even u)  →  now(even x)
  --   the `wrong` branch has an empty precondition (even u ∧ ¬even u)
  have J7 : Judg Mspec Dtable Rc Gc (.ite evenCond .skip .wrong)
      (now φu) (now ex) Effect.B := by
    have hta : Mspec.lift evenCond.tru (now φu) ⊑ Effect.B :=
      Mspec_stpres_le (fun _ _ _ h => h.1) _
    have htf : Mspec.lift evenCond.fls (now φu) ⊑ Effect.B :=
      Mspec_stpres_le (fun _ _ _ h => h.1) _
    refine Judg.ite (Q := now ex) (e1 := Effect.B) (e2 := Effect.B) ?_ ?_ ?_
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
  have J8 : Judg Mspec Dtable Rc Gc .yield (now ex) (two Sx) Effect.Y := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.yield (P := now ex) now_ex_imp_evenRely rfl)
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

Both threads run the same `yield; client()` code, each resolving its locals to
`loc … tid`.  We verify `⊢ Σ` via rule `M-state`.  Every premise is discharged
concretely — each thread verifies from a yield with `even(x)` holding at the
initial store `x = 0`, the guarantee is reflexive and published, and the
compatibility condition holds because both threads share the same rely/guarantee
— **except** `M is valid`, the paper's standing semantic assumption on the mover
specification (Definition "Validity"), taken as a hypothesis here exactly as the
paper assumes it. -/

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
    paper's standing assumption that the mover specification is valid.  Each thread
    runs the *same* `yield; client()` code, resolving `r`/`arg`/`result`/`u` to its
    own `loc … tid`.  Every other `M-state` premise is discharged concretely; the
    `Valid Mspec` hypothesis is genuinely needed and, for this simplified model,
    still *false* — now because of the shared counter `x` (see `Mspec_not_valid`). -/
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

/-! ### Is `Mspec` valid?  Not quite — the residual gap is the shared counter `x`.

With `r`, `arg`, `result`, `u` now genuinely thread-local, the thread-locality
race is gone.  But `Valid Mspec` (Definition "Validity", quantified over *all*
actions) is still not provable, and the reason is now the one genuinely shared
mutable variable: the counter `x`.  In the program every write to `x` is
performed while holding the lock, so two threads never write `x` concurrently —
but `Mspec` classifies a write to `x` as a both-mover *unconditionally*, without
encoding the "only while `m == tid`" side condition of the paper's
`int x both-mover if m == tid`.  Two *unsynchronized* writes to `x` are therefore
falsely called both-movers, and validity condition (1) fails.

This still illustrates why the per-thread `Judg` derivations verify: the judgment
is parametric in `Mspec` and only trusts its mover claims; the one place that
demands those claims be *true* is `Valid Mspec`.  Fully closing the gap would
mean making `Mspec` lock-conditional for `x` (a both-mover only when the lock is
held) and re-proving the reduction commutativity that `Reduction.lean` already
assumes via `Valid` — a separate axis of faithfulness (the synchronization
discipline) from the thread-locality fixed here. -/

/-- **`Mspec` is not valid.**  Witness: two threads write the shared counter `x`
    (with no lock held) to different values.  `Mspec` calls both writes
    both-movers (`⊑ R` and `⊑ N`), yet they do not commute — validity condition
    (1) fails.  The residual gap is the shared `x`, whose writes `Mspec` treats as
    unconditional both-movers rather than lock-conditional ones; hence
    `init_state_valid` still *assumes* `Valid Mspec`. -/
theorem Mspec_not_valid : ¬ Valid Mspec := by
  intro hV
  -- thread 1 writes x := 1, then thread 2 writes x := 2, from the store `0`
  have h := hV.right 1 2 (gen (fun _ => "x") (fun _ _ => 1)) (gen (fun _ => "x") (fun _ _ => 2))
    (fun _ => 0) (upd (fun _ => 0) "x" 1) (upd (upd (fun _ => 0) "x" 1) "x" 2)
    (by decide)
    (le_trans (Mspec_gen_all x_ne_lock 1 _) (by decide))
    rfl
    (le_trans (Mspec_gen_all x_ne_lock 2 _) (by decide))
    rfl
  obtain ⟨σ''', _hA2, hA1⟩ := h
  -- the "commuted" trace ends with x = 1, but the real trace ends with x = 2
  have e1 : (upd (upd (fun _ => (0 : Value)) "x" 1) "x" 2) "x" = 1 := by
    rw [hA1]; exact upd_same σ''' "x" 1
  have e2 : (upd (upd (fun _ => (0 : Value)) "x" 1) "x" 2) "x" = 2 := upd_same _ "x" 2
  rw [e1] at e2
  exact absurd e2 (by decide)

end Examples
end MoverLogic
