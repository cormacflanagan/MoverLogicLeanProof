/-
  The paper's examples, verified against the *proved-valid* mover spec `MspecV`.

  `Examples.lean` gives faithful `Judg` derivations of the paper's examples (the
  spin lock, the `add()`/`client()` counter, the initial state) — but against
  `Mspec`, whose validity is *assumed* (and which is in fact not valid, because it
  treats every `x`-write as an unconditional both-mover).  `ValidSpec.lean` proves
  a concrete spec `MspecV` valid outright, but only exercised it on streamlined
  states.

  This file closes the gap: it re-runs the faithful derivations against `MspecV`,
  so the paper's central example is verified with **no validity assumption**.  The
  synchronization discipline is now real — an `x`-access is a both-mover *only
  while the lock is held* — so the derivations must thread "the lock is held"
  through each critical section.  The headline result is

    * `client_state_valid` — `⊢ Σ` for `(yield; client()) ‖ (yield; client())`
      via rule `M-state`, discharging `Valid MspecV` with the *proof* `MspecV_valid`
      (`#print axioms` = the three standard axioms), the `add()` body doing a real
      read-modify-write of the shared counter `x` through thread-local `r`, `arg`,
      `result` under the lock.

  Thread-local variables are owned under `MspecV`'s leading-`'A'` ownership: thread
  `t`'s copy of `name` is `A^(t+1) ++ name`, which `owns t` recognizes.
-/
import MoverLogic.ValidSpec

namespace MoverLogic
namespace ValidSpecExamples

open Effect MoverLogic.ValidSpec

/-! ### Thread-local variable names, owned under `MspecV`'s `owns`

`owns t v` holds iff `v` begins with exactly `t+1` `'A'`s.  So thread `t`'s copy of
a local `name` (with `name` not starting with `'A'`) is `A^(t+1) ++ name`. -/

/-- The prefix of `n` copies of `'A'`. -/
def Apre : Nat → String
  | 0 => ""
  | n + 1 => "A" ++ Apre n

theorem Apre_toList : ∀ n, (Apre n).toList = List.replicate n 'A'
  | 0 => rfl
  | n + 1 => by rw [Apre, String.toList_append, Apre_toList n]; rfl

theorem takeWhile_replicate_A : ∀ (n : Nat) (l : List Char),
    l.takeWhile (· = 'A') = [] →
    (List.replicate n 'A' ++ l).takeWhile (· = 'A') = List.replicate n 'A'
  | 0, l, hl => by simpa using hl
  | n + 1, l, hl => by
      show ('A' :: (List.replicate n 'A' ++ l)).takeWhile (· = 'A') = 'A' :: List.replicate n 'A'
      rw [List.takeWhile_cons, takeWhile_replicate_A n l hl]; simp

/-- `loc name t` — thread `t`'s copy of the local variable `name`. -/
def loc (name : String) (t : Tid) : Var := Apre (t + 1) ++ name

/-- A `loc name t` (with `name` not `'A'`-led) is owned by `t`. -/
theorem owns_loc (name : String) (hname : name.toList.takeWhile (· = 'A') = []) (t : Tid) :
    owns t (loc name t) := by
  unfold owns leadA loc
  rw [String.toList_append, Apre_toList, takeWhile_replicate_A (t + 1) _ hname]
  simp

/-- Different base names give different thread-locals (same thread). -/
theorem loc_ne_loc {a b : String} (h : a ≠ b) (t : Tid) : loc a t ≠ loc b t := by
  intro he; apply h
  have hd := congrArg String.toList he
  rw [loc, loc, String.toList_append, String.toList_append] at hd
  exact String.toList_inj.mp (List.append_cancel_left hd)

/-- The base names the counter example uses are owned by the acting thread. -/
theorem owns_r (t : Tid) : owns t (loc "r" t) := owns_loc "r" (by decide) t
theorem owns_arg (t : Tid) : owns t (loc "arg" t) := owns_loc "arg" (by decide) t
theorem owns_result (t : Tid) : owns t (loc "result" t) := owns_loc "result" (by decide) t
theorem owns_u (t : Tid) : owns t (loc "u" t) := owns_loc "u" (by decide) t

/-- Thread-locals are never the lock. -/
theorem loc_ne_lock (name) (hname : name.toList.takeWhile (· = 'A') = []) (t : Tid) :
    loc name t ≠ LOCK := fun he => not_owns_l t (he ▸ owns_loc name hname t)
/-- Thread-locals are never the shared counter `x`. -/
theorem loc_ne_x (name) (hname : name.toList.takeWhile (· = 'A') = []) (t : Tid) :
    loc name t ≠ XVAR := fun he => not_owns_x t (he ▸ owns_loc name hname t)

/-! ### The generic thread-aware assignment and its `MspecV` classification -/

/-- A thread-aware assignment `d(t) := f(t, σ)` — writes `d t` (owned by `t`, or the
    shared `x`) with a value reading `t`'s own state (and `x`).  Total. -/
def gen (d : Tid → Var) (f : Tid → Store → Value) : Action :=
  fun t σ σ' => σ' = upd σ (d t) (f t σ)

theorem gen_total (d f) : Total (gen d f) := fun t σ => ⟨upd σ (d t) (f t σ), rfl⟩

/-- A `gen` writing an owned variable, reading only owned state, is a **local**
    both-mover (store-independent `B`). -/
theorem gen_isLocal {d f} {t : Tid} (hd : owns t (d t))
    (hf : ∀ σ1 σ2, (∀ v, owns t v → σ1 v = σ2 v) → f t σ1 = f t σ2) :
    IsLocal (gen d f) t := by
  refine ⟨fun σ => upd σ (d t) (f t σ), ⟨?_, ?_⟩, fun _ _ => Iff.rfl⟩
  · intro σ v hv; exact upd_other σ (d t) (f t σ) v (fun he => hv (he ▸ hd))
  · intro σ1 σ2 hag v hv
    by_cases he : v = d t
    · subst he; rw [upd_same, upd_same, hf σ1 σ2 hag]
    · rw [upd_other _ _ _ _ he, upd_other _ _ _ _ he, hag v hv]

/-- A `gen` writing `x` or an owned variable, reading only owned state and `x`, is a
    lock-protected **x-access** (both-mover `B` *while the lock is held*). -/
theorem gen_isXacc {d f} {t : Tid} (hdx : d t = XVAR ∨ owns t (d t))
    (hf : ∀ σ1 σ2, (∀ v, (owns t v ∨ v = XVAR) → σ1 v = σ2 v) → f t σ1 = f t σ2) :
    IsXacc (gen d f) t := by
  have hdR : owns t (d t) ∨ d t = XVAR := hdx.symm
  have hdl : d t ≠ LOCK := by
    rcases hdx with h | h
    · exact h ▸ (by decide)
    · exact fun he => not_owns_l t (he ▸ h)
  refine ⟨fun σ => upd σ (d t) (f t σ), ⟨?_, ?_⟩,
    fun σ => upd_other σ (d t) (f t σ) LOCK (Ne.symm hdl), fun _ _ => Iff.rfl⟩
  · intro σ v hv; exact upd_other σ (d t) (f t σ) v (fun he => hv (he ▸ hdR))
  · intro σ1 σ2 hag v hv
    by_cases he : v = d t
    · subst he; rw [upd_same, upd_same, hf σ1 σ2 hag]
    · rw [upd_other _ _ _ _ he, upd_other _ _ _ _ he, hag v hv]

/-! ### `MspecV` classification lemmas (local ⇒ `B`; idAction ⇒ `B`; test ⇒ `B`) -/

theorem isLocal_not_isAcq {A t} (h : IsLocal A t) : ¬ IsAcq A t := by
  obtain ⟨g, _, hch⟩ := h
  intro hacq
  have hfire : A t (fun _ => (0 : Value)) (g (fun _ => (0 : Value))) := (hch _ _).mpr rfl
  exact absurd ((hacq _ _).mp hfire).1 (by decide)

theorem isLocal_not_isRel {A t} (h : IsLocal A t) : ¬ IsRel A t := by
  obtain ⟨g, hc, hch⟩ := h
  intro hrel
  have h0 : g (fun _ => (0 : Value)) LOCK = FREE := by
    rw [(hrel _ _).mp ((hch _ _).mpr rfl), upd_same]
  rw [lock_pres hc (not_owns_l t) _] at h0
  exact absurd h0 (by decide)

theorem MspecV_local_B {A t σ} (h : IsLocal A t) : MspecV A t σ = Effect.B := by
  unfold MspecV
  rw [if_neg (isLocal_not_isAcq h), if_neg (isLocal_not_isRel h), if_pos h]

theorem idAction_isLocal (t : Tid) : IsLocal idAction t :=
  ⟨fun σ => σ, confined_id _, fun _ _ => eq_comm⟩

theorem isTest_not_isAcq {A t} (h : IsTest A t) : ¬ IsAcq A t := by
  obtain ⟨P, _, hch⟩ := h
  intro hacq
  have hfire : A t (fun _ => FREE) (upd (fun _ => FREE) LOCK (t : Value)) :=
    (hacq _ _).mpr ⟨rfl, rfl⟩
  have hthis := congrFun ((hch _ _).mp hfire).1 LOCK
  rw [upd_same] at hthis
  exact absurd hthis (t_ne_free t)

theorem isTest_not_isRel {A t} (h : IsTest A t) : ¬ IsRel A t := by
  obtain ⟨P, _, hch⟩ := h
  intro hrel
  have hfire : A t (fun _ => (0 : Value)) (upd (fun _ => (0 : Value)) LOCK FREE) :=
    (hrel _ _).mpr rfl
  have hthis := congrFun ((hch _ _).mp hfire).1 LOCK
  rw [upd_same] at hthis
  exact absurd hthis (by decide)

/-- A total x-access that is also a test must be the identity — hence local. -/
theorem isXacc_isTest_isLocal {A t} (hx : IsXacc A t) (ht : IsTest A t) : IsLocal A t := by
  obtain ⟨g, _, _, hchx⟩ := hx
  obtain ⟨P, _, hcht⟩ := ht
  have hgid : ∀ σ, g σ = σ := fun σ => ((hcht σ (g σ)).mp ((hchx σ (g σ)).mpr rfl)).1
  refine ⟨fun σ => σ, confined_id _, fun σ σ' => ?_⟩
  rw [hchx σ σ', hgid σ]

theorem MspecV_test_B {A t σ} (h : IsTest A t) : MspecV A t σ = Effect.B := by
  unfold MspecV
  rw [if_neg (isTest_not_isAcq h), if_neg (isTest_not_isRel h)]
  by_cases hl : IsLocal A t
  · rw [if_pos hl]
  · rw [if_neg hl, if_neg (fun hx => hl (isXacc_isTest_isLocal hx h)), if_pos h]

/-! ### Lifted `MspecV` bounds for the program actions -/

/-- Uniform pointwise bound ⇒ lifted bound. -/
theorem lift_le_of_all {A : Action} {P : Pred2} {e : Effect}
    (h : ∀ t σ, MspecV A t σ ⊑ e) : MspecV.lift A P ⊑ e := by
  apply sSup_le; rintro e' ⟨t, σ, σ0, _, rfl⟩; exact h t σ

theorem MspecV_idAction_le (P : Pred2) : MspecV.lift idAction P ⊑ Effect.B :=
  lift_le_of_all (fun t σ => by rw [MspecV_local_B (idAction_isLocal t)]; exact Effect.le_refl _)

theorem MspecV_gen_local_le {d f} (P : Pred2) (hd : ∀ t, owns t (d t))
    (hf : ∀ (t : Tid) σ1 σ2, (∀ v, owns t v → σ1 v = σ2 v) → f t σ1 = f t σ2) :
    MspecV.lift (gen d f) P ⊑ Effect.B :=
  lift_le_of_all (fun t σ => by
    rw [MspecV_local_B (gen_isLocal (hd t) (hf t))]; exact Effect.le_refl _)

/-- "The precondition guarantees the lock is held by the acting thread." -/
def HeldPre (P : Pred2) : Prop := ∀ t σ σ0, P t σ0 σ → σ LOCK = (t : Value)

theorem MspecV_gen_xacc_le {d f} (P : Pred2) (hdx : ∀ t, d t = XVAR ∨ owns t (d t))
    (hf : ∀ (t : Tid) σ1 σ2, (∀ v, (owns t v ∨ v = XVAR) → σ1 v = σ2 v) → f t σ1 = f t σ2)
    (hHeld : HeldPre P) : MspecV.lift (gen d f) P ⊑ Effect.B := by
  apply sSup_le
  rintro e' ⟨t, σ, σ0, hP, rfl⟩
  rw [MspecV_xacc_held (gen_isXacc (hdx t) (hf t)) (hHeld t σ σ0 hP)]; exact Effect.le_refl _

/-- After an acquire, the lock is held. -/
theorem HeldPre_acq (P : Pred2) : HeldPre (compPA P acquireL) := by
  rintro t σ σ0 ⟨σ', _, hacq⟩; rw [hacq.2]; exact upd_same _ _ _

/-- A lock-preserving `gen` keeps the lock held. -/
theorem HeldPre_gen {d f} (P : Pred2) (h : HeldPre P) (hd : ∀ t, d t ≠ LOCK) :
    HeldPre (compPA P (gen d f)) := by
  rintro t σ σ0 ⟨σ', hP, hg⟩
  rw [hg, upd_other σ' (d t) (f t σ') LOCK (Ne.symm (hd t))]; exact h t σ' σ0 hP

/-! ## Example 1 — the spin lock (Figure 5), against `MspecV`

```
void spin_lock()   { while (!cas(l, 0, tid)) { skip; } }   -- right-mover
void spin_unlock() { l = 0; }                              -- left-mover  (l == tid)
```
The paper's own derivation `e = (M(I,P);B)*; M(⟨…⟩l,P) = (B;B)*; R = R`. -/

/-- `cas(l,0,tid)`: success acquires, failure is the identity. -/
def casLock : CondAction := ⟨acquireL, idAction⟩

theorem compPA_idAction_imp (P : Pred2) : compPA P idAction ⟹ P := by
  rintro t σ σ'' ⟨σ', hP, (hid : σ' = σ'')⟩; exact hid ▸ hP

/-- **The spin-lock loop verifies as a right-mover** `R` against `MspecV`. -/
theorem spin_lock_loop (D : Decls) (R G P : Pred2) :
    Judg MspecV D R G (.while casLock.neg .skip) P (compPA P acquireL) Effect.R := by
  have ha : MspecV.lift idAction P ⊑ Effect.B := MspecV_idAction_le P
  have hb : MspecV.lift acquireL P ⊑ Effect.R := MspecV_acquire_le P
  have h1 : Judg MspecV D R G .skip (compPA P idAction) P Effect.B :=
    Judg.conseq (fun _ _ _ h => h) (compPA_idAction_imp P) (fun _ _ _ h => h)
      (fun _ _ _ h => h) (by decide) Judg.skip
  have hiB : MspecV.lift idAction P ;; Effect.B ⊑ Effect.B :=
    le_trans (Effect.seq_mono ha (Effect.le_refl _)) (by decide)
  have hiter : MspecV.lift idAction P ;; Effect.B ⊑ Effect.R := le_trans hiB (by decide)
  have hstar : (MspecV.lift idAction P ;; Effect.B)^* ⊑ Effect.B :=
    le_trans (Effect.star_mono hiB) (by decide)
  have he : ((MspecV.lift idAction P ;; Effect.B)^* ;; MspecV.lift acquireL P) ⊑ Effect.R :=
    le_trans (Effect.seq_mono hstar hb) (by decide)
  exact Judg.wloop (C := casLock.neg) (s := .skip) (e1 := Effect.B) h1 hiter he (by decide)

/-- **`spin_lock` verifies as an atomic right-mover** (rule `M-def-atomic`). -/
theorem spin_lock_def (D : Decls) :
    FnValid MspecV D
      (.atomic Effect.R (fun _ _ => True) (compPA (two (fun _ _ => True)) acquireL))
      (.while casLock.neg .skip) :=
  spin_lock_loop D botP botP (two (fun _ _ => True))

/-- **`spin_unlock` verifies as an atomic left-mover** — `requires l == tid`, so the
    total release is used at `L` (the sync discipline threaded through the spec). -/
theorem spin_unlock_def (D : Decls) :
    FnValid MspecV D
      (.atomic Effect.L (fun t σ => σ LOCK = (t : Value))
        (compPA (two (fun t σ => σ LOCK = (t : Value))) releaseL))
      (.act releaseL) := by
  refine Judg.action (MspecV_release_le _ ?_) (fun _ t σ => ⟨upd σ LOCK FREE, rfl⟩)
  rintro t σ σ0 ⟨rfl, hheld⟩; exact hheld

/-! ## Example 2 — the atomic `add()` counter body (Figure 7), against `MspecV`

```
int add() {
  acquire(l);       -- R
  r = x;            -- B   (x-access: lock held)
  r = r + arg;      -- B   (local)
  x = 1;            -- B   (x-access: lock held)
  x = r;            -- B   (x-access: lock held)
  release(l);       -- L   (lock held)
  result = r;       -- B   (local)
}
```
Effects `R;B;B;B;B;L;B = N`, one reducible sequence — `add()` is atomic.  The three
`x`-accesses are both-movers *because the lock is held*; the `add()` acquires the
lock itself, and it stays held (each step preserves it) until the release. -/

/-- The five straight-line assignments of `add()`'s body. -/
def a_rx : Action := gen (loc "r") (fun _ σ => σ XVAR)
def a_rra : Action := gen (loc "r") (fun t σ => σ (loc "r" t) + σ (loc "arg" t))
def a_x1 : Action := gen (fun _ => XVAR) (fun _ _ => 1)
def a_xr : Action := gen (fun _ => XVAR) (fun t σ => σ (loc "r" t))
def a_resr : Action := gen (loc "result") (fun t σ => σ (loc "r" t))

/-- The body of `add()`. -/
def addBody : Stmt :=
  .seq (.act acquireL)
   (.seq (.act a_rx)
    (.seq (.act a_rra)
     (.seq (.act a_x1)
      (.seq (.act a_xr)
       (.seq (.act releaseL)
             (.act a_resr))))))

/-- The strongest postcondition of `add()`'s body from precondition `P`. -/
def addPost (P : Pred2) : Pred2 :=
  compPA (compPA (compPA (compPA (compPA (compPA
    (compPA P acquireL) a_rx) a_rra) a_x1) a_xr) releaseL) a_resr

/-- **`add()`'s body verifies with effect `N`**, its strongest postcondition, against
    the *valid* `MspecV` — no validity assumption.  The lock, acquired first, is held
    through every `x`-access. -/
theorem add_body_post (D : Decls) (R G P : Pred2) :
    Judg MspecV D R G addBody P (addPost P) Effect.N := by
  -- lock held after the acquire, and preserved by each subsequent assignment
  have hH1 : HeldPre (compPA P acquireL) := HeldPre_acq P
  have hH2 : HeldPre (compPA (compPA P acquireL) a_rx) :=
    HeldPre_gen _ hH1 (fun t => loc_ne_lock "r" (by decide) t)
  have hH3 : HeldPre (compPA (compPA (compPA P acquireL) a_rx) a_rra) :=
    HeldPre_gen _ hH2 (fun t => loc_ne_lock "r" (by decide) t)
  have hH4 : HeldPre (compPA (compPA (compPA (compPA P acquireL) a_rx) a_rra) a_x1) :=
    HeldPre_gen _ hH3 (fun _ => by decide)
  have hH5 : HeldPre (compPA (compPA (compPA (compPA (compPA P acquireL) a_rx) a_rra) a_x1) a_xr) :=
    HeldPre_gen _ hH4 (fun _ => by decide)
  refine Judg.seq (Judg.action (MspecV_acquire_le P) (fun h => absurd h (by decide)))
    (Judg.seq (Judg.action (MspecV_gen_xacc_le _ (fun t => Or.inr (owns_r t))
        (fun _ σ1 σ2 hag => hag XVAR (Or.inr rfl)) hH1) (fun _ => gen_total _ _))
     (Judg.seq (Judg.action (MspecV_gen_local_le _ (fun t => owns_r t)
        (fun t σ1 σ2 hag => by rw [hag (loc "r" t) (owns_r t), hag (loc "arg" t) (owns_arg t)]))
        (fun _ => gen_total _ _))
      (Judg.seq (Judg.action (MspecV_gen_xacc_le _ (fun _ => Or.inl rfl)
          (fun _ _ _ _ => rfl) hH3) (fun _ => gen_total _ _))
       (Judg.seq (Judg.action (MspecV_gen_xacc_le _ (fun _ => Or.inl rfl)
           (fun t σ1 σ2 hag => hag (loc "r" t) (Or.inl (owns_r t))) hH4) (fun _ => gen_total _ _))
        (Judg.seq (Judg.action (MspecV_release_le _ hH5) (fun _ t σ => ⟨upd σ LOCK FREE, rfl⟩))
                  (Judg.action (MspecV_gen_local_le _ (fun t => owns_result t)
                    (fun t σ1 σ2 hag => hag (loc "r" t) (owns_r t))) (fun _ => gen_total _ _)))))))

/-- **`add()`'s body is atomic** (effect `N`, one reducible sequence). -/
theorem add_body_atomic (D : Decls) (R G P : Pred2) :
    ∃ Q, Judg MspecV D R G addBody P Q Effect.N :=
  ⟨_, add_body_post D R G P⟩

/-- The paper's `add()` postcondition: `x == \old(x) + arg_tid ∧ result_tid == x`. -/
def addEnsures : Pred2 :=
  fun t σ σ' => σ' XVAR = σ XVAR + σ (loc "arg" t) ∧ σ' (loc "result" t) = σ' XVAR

set_option linter.unusedSimpArgs false in
/-- `add()`'s strongest postcondition entails the paper's `ensures`. -/
theorem addPost_imp_ensures (S : Pred1) : addPost (two S) ⟹ addEnsures := by
  rintro t σ σ' hpost
  obtain ⟨s6, ⟨s5, ⟨s4, ⟨s3, ⟨s2, ⟨s1, ⟨s0, hP, hacq⟩, hw1⟩, hw2⟩, hw3⟩, hw4⟩, hrel⟩, hw5⟩ := hpost
  obtain ⟨hs0eq, _⟩ := hP
  subst s0
  have e1 := hacq.2
  subst s1
  subst s2 s3 s4 s5 s6 σ'
  have a2 : loc "r" t ≠ XVAR := loc_ne_x "r" (by decide) t
  have a3 : loc "arg" t ≠ loc "r" t := loc_ne_loc (by decide) t
  have a4 : loc "arg" t ≠ XVAR := loc_ne_x "arg" (by decide) t
  have a6 : loc "result" t ≠ XVAR := loc_ne_x "result" (by decide) t
  have a8 : loc "result" t ≠ loc "r" t := loc_ne_loc (by decide) t
  have hxl : (XVAR : Var) ≠ LOCK := by decide
  refine ⟨?_, ?_⟩ <;>
    simp [a_rx, a_rra, a_x1, a_xr, a_resr, gen, upd, hxl, hxl.symm,
      loc_ne_lock "r" (by decide) t, (loc_ne_lock "r" (by decide) t).symm,
      loc_ne_lock "arg" (by decide) t, (loc_ne_lock "arg" (by decide) t).symm,
      loc_ne_lock "result" (by decide) t, (loc_ne_lock "result" (by decide) t).symm,
      a2, a2.symm, a3, a3.symm, a4, a4.symm, a6, a6.symm, a8, a8.symm]

/-- **`add()` verifies against the paper's exact specification** (rule `M-def-atomic`),
    against the *valid* `MspecV`. -/
theorem add_meets_ensures (D : Decls) :
    FnValid MspecV D (.atomic Effect.N (fun _ _ => True) addEnsures) addBody :=
  Judg.conseq (fun _ _ _ h => h) (addPost_imp_ensures _) (fun _ _ _ h => h)
    (fun _ _ _ h => h) (Effect.le_refl _)
    (add_body_post D botP botP (two (fun _ _ => True)))

/-! ## Example 3 — the non-atomic `client()` (Figure 7), against `MspecV`

```
void client() {
  arg = 2;  add();  yield;              -- reducible sequence 1
  arg = 2;  add();  u = result;
  if even(u) skip else wrong;  yield;   -- reducible sequence 2
}
```
Effect `B;N;Y;B;N;B;B;Y = R`: two reducible sequences split by yields, the
assertion's `wrong` branch rejected by an empty precondition. -/

/-- `even(x)` on the shared counter. -/
def evenx (σ : Store) : Prop := ∃ k : Int, σ XVAR = 2 * k
/-- A program-point predicate on the current store and acting thread. -/
def now (φ : Tid → Store → Prop) : Pred2 := fun t _ σ => φ t σ
/-- The `even(x)` invariant as a point predicate. -/
def ex : Tid → Store → Prop := fun _ σ => evenx σ
/-- `relies even(x)` / `guarantees even(x)`: an interference step preserves `even(x)`. -/
def evenRely : Pred2 := fun _ σ σ' => evenx σ → evenx σ'
/-- `even(u_tid)` on thread `t`'s local `u`. -/
def evenu (t : Tid) (σ : Store) : Prop := ∃ k : Int, σ (loc "u" t) = 2 * k
/-- `assert even(u) = if even(u) skip else wrong`. -/
def evenCond : CondAction :=
  ⟨fun t σ σ' => σ' = σ ∧ evenu t σ, fun t σ σ' => σ' = σ ∧ ¬ evenu t σ⟩

/-- The declaration table: `add` bound to its `MspecV`-verified atomic spec. -/
def Dtable : Decls :=
  fun f => if f = "add" then some (.atomic Effect.N (fun _ _ => True) addEnsures, addBody)
           else none

theorem Dtable_add : Dtable "add" =
    some (.atomic Effect.N (fun _ _ => True) addEnsures, addBody) := by
  unfold Dtable; rw [if_pos rfl]

theorem evenx_stable {t σ a} (h : Rtc evenRely t σ a) : evenx σ → evenx a := by
  induction h with
  | refl => exact id
  | step hstep _ ih => exact fun he => ih (hstep he)

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

private abbrev Rc : Pred2 := evenRely
private abbrev Gc : Pred2 := evenRely
private abbrev Sx : Pred1 := fun _ σ => evenx σ

theorem now_ex_imp_evenRely : now ex ⟹ evenRely := fun _ _ _ h _ => h

private def φarg : Tid → Store → Prop := fun t σ => evenx σ ∧ σ (loc "arg" t) = 2
private def φres : Tid → Store → Prop := fun t σ => evenx σ ∧ ∃ k : Int, σ (loc "result" t) = 2 * k
private def φu : Tid → Store → Prop := fun t σ => evenx σ ∧ evenu t σ

/-- A test (a store-preserving conditional whose guard reads owned state) is a `B`. -/
theorem MspecV_test_le {A : Action} (P : Pred2) (h : ∀ t, IsTest A t) :
    MspecV.lift A P ⊑ Effect.B :=
  lift_le_of_all (fun t σ => by rw [MspecV_test_B (h t)]; exact Effect.le_refl _)

theorem evenCond_tru_isTest (t : Tid) : IsTest evenCond.tru t :=
  ⟨evenu t, fun σ1 σ2 hag => by unfold evenu; rw [hag (loc "u" t) (owns_u t)], fun _ _ => Iff.rfl⟩
theorem evenCond_fls_isTest (t : Tid) : IsTest evenCond.fls t :=
  ⟨fun σ => ¬ evenu t σ, fun σ1 σ2 hag => by
    simp only [evenu]; rw [hag (loc "u" t) (owns_u t)], fun _ _ => Iff.rfl⟩

/-- A local `gen` judgment (both-mover `B`, total). -/
theorem judg_local (D : Decls) (R G P : Pred2) (d f) (hd : ∀ t, owns t (d t))
    (hf : ∀ (t : Tid) σ1 σ2, (∀ v, owns t v → σ1 v = σ2 v) → f t σ1 = f t σ2) :
    Judg MspecV D R G (.act (gen d f)) P (compPA P (gen d f)) Effect.B :=
  Judg.action (MspecV_gen_local_le P hd hf) (fun _ => gen_total _ _)

/-- **`client()`'s body verifies** with effect `R` (`= B;N;Y;B;N;B;B;Y`), against the
    *valid* `MspecV`, from `even(x)` to `even(x)`. -/
theorem client_body_verifies :
    Judg MspecV Dtable Rc Gc clientBody (two Sx) (two Sx) Effect.R := by
  have J1 : Judg MspecV Dtable Rc Gc (.act (gen (loc "arg") (fun _ _ => 2)))
      (two Sx) (now φarg) Effect.B := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (judg_local Dtable Rc Gc (two Sx) (loc "arg") (fun _ _ => 2)
        (fun t => owns_arg t) (fun _ _ _ _ => rfl))
    rintro t σ0 σ'' ⟨σ', ⟨rfl, ⟨k, hk⟩⟩, rfl⟩
    exact ⟨⟨k, by simp [upd]; exact hk⟩, by simp [upd]⟩
  have J2 : Judg MspecV Dtable Rc Gc (.call "add") (now φarg) (now ex) Effect.N := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.callAtomic (P := now φarg) Dtable_add (fun _ _ _ => trivial))
    rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, harg⟩, hx, _⟩
    exact ⟨k + 1, by rw [hx, hk, harg, Int.mul_add, Int.mul_one]⟩
  have J3 : Judg MspecV Dtable Rc Gc .yield (now ex) (now ex) Effect.Y := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.yield (P := now ex) now_ex_imp_evenRely rfl)
    rintro t a b ⟨rfl, _σ0, σ, hev, hrtc⟩
    exact evenx_stable hrtc hev
  have J4 : Judg MspecV Dtable Rc Gc (.act (gen (loc "arg") (fun _ _ => 2)))
      (now ex) (now φarg) Effect.B := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (judg_local Dtable Rc Gc (now ex) (loc "arg") (fun _ _ => 2)
        (fun t => owns_arg t) (fun _ _ _ _ => rfl))
    rintro t σ0 σ'' ⟨σ', ⟨k, hk⟩, rfl⟩
    exact ⟨⟨k, by simp [upd]; exact hk⟩, by simp [upd]⟩
  have J5 : Judg MspecV Dtable Rc Gc (.call "add") (now φarg) (now φres) Effect.N := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.callAtomic (P := now φarg) Dtable_add (fun _ _ _ => trivial))
    rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, harg⟩, hx, hres⟩
    exact ⟨⟨k + 1, by rw [hx, hk, harg, Int.mul_add, Int.mul_one]⟩,
           k + 1, by rw [hres, hx, hk, harg, Int.mul_add, Int.mul_one]⟩
  have J6 : Judg MspecV Dtable Rc Gc (.act (gen (loc "u") (fun t σ => σ (loc "result" t))))
      (now φres) (now φu) Effect.B := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (judg_local Dtable Rc Gc (now φres) (loc "u") (fun t σ => σ (loc "result" t))
        (fun t => owns_u t) (fun t σ1 σ2 hag => hag (loc "result" t) (owns_result t)))
    rintro t σ0 σ'' ⟨σ', ⟨⟨k, hk⟩, kr, hres⟩, rfl⟩
    refine ⟨⟨k, ?_⟩, kr, ?_⟩
    · simp [upd]; exact hk
    · show upd σ' (loc "u" t) (σ' (loc "result" t)) (loc "u" t) = _
      rw [upd_same]; exact hres
  have J7 : Judg MspecV Dtable Rc Gc (.ite evenCond .skip .wrong)
      (now φu) (now ex) Effect.B := by
    have hta : MspecV.lift evenCond.tru (now φu) ⊑ Effect.B :=
      MspecV_test_le _ evenCond_tru_isTest
    have htf : MspecV.lift evenCond.fls (now φu) ⊑ Effect.B :=
      MspecV_test_le _ evenCond_fls_isTest
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
  have J8 : Judg MspecV Dtable Rc Gc .yield (now ex) (two Sx) Effect.Y := by
    refine Judg.conseq (fun _ _ _ h => h) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) (Judg.yield (P := now ex) now_ex_imp_evenRely rfl)
    rintro t a b ⟨rfl, _σ0, σ, hev, hrtc⟩
    exact ⟨rfl, evenx_stable hrtc hev⟩
  exact Judg.seq J1 (Judg.seq J2 (Judg.seq J3 (Judg.seq J4
        (Judg.seq J5 (Judg.seq J6 (Judg.seq J7 J8))))))

/-- **`client()` verifies as a non-atomic function** (rule `M-def-non-atomic`). -/
theorem client_def :
    FnValid MspecV Dtable (.nonatomic Rc Gc Sx Sx) clientBody :=
  ⟨client_body_verifies, ⟨0, (fun _ => 0), (fun _ => 0), fun h => h⟩⟩

/-! ## Example 4 — the whole initial state (Figure 7), against `MspecV`

```
Σ  =  (yield; client()) ‖ (yield; client())  ·  [x := 0, l := free]
```
Verified via rule `M-state` with **no validity assumption** — `Valid MspecV` is
discharged by the proof `MspecV_valid`. -/

/-- The initial store: `x = 0` (even), lock free. -/
def initStore : Store := fun v => if v = LOCK then FREE else 0

/-- Each initial thread: `yield; client()`. -/
def clientThread : Stmt := .seq .yield clientBody

theorem clientThread_verifies :
    Judg MspecV Dtable Rc Gc clientThread (two Sx) (two Sx) (Effect.Y ;; Effect.R) := by
  refine Judg.seq (Judg.yield (P := two Sx) ?_ rfl) ?_
  · rintro t σ σ' ⟨rfl, he⟩ _; exact he
  · refine Judg.conseq ?_ (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (by decide) client_body_verifies
    rintro t a b ⟨rfl, _σ0, σ, ⟨rfl, hev⟩, hrtc⟩
    exact ⟨rfl, evenx_stable hrtc hev⟩

/-- **`⊢ Σ` with no validity assumption.**  The two-thread counter state — each
    thread `yield; client()`, doing a real lock-protected read-modify-write of the
    shared `x` — verifies via `M-state`, discharging `Valid MspecV` with the proof
    `MspecV_valid`.  This is the paper's motivating example, machine-checked against
    a mover spec that is itself proved valid. -/
theorem client_state_valid :
    StateValid MspecV Dtable ⟨[clientThread, clientThread], initStore⟩ := by
  refine ⟨Rc, Gc, ?_, MspecV_valid, ?_, ?_, ?_⟩
  · rintro f spec body hf
    unfold Dtable at hf
    by_cases hfa : f = "add"
    · rw [if_pos hfa] at hf
      obtain ⟨rfl, rfl⟩ := Option.some.inj hf
      exact add_meets_ensures Dtable
    · rw [if_neg hfa] at hf; exact absurd hf (by simp)
  · intro t σ; exact fun h => h
  · intro t s hs
    have hx0 : evenx initStore := ⟨0, by simp [initStore, LOCK, XVAR]⟩
    have hsc : s = clientThread := by rcases t with _ | _ | t <;> simp_all
    subst hsc
    refine ⟨two Sx, two Sx, Effect.Y ;; Effect.R, clientThread_verifies, by decide, ?_, ?_, ?_⟩
    · rintro t σ σ' ⟨rfl, he⟩ _; exact he
    · exact ⟨.seqL .hole clientBody, rfl⟩
    · exact ⟨rfl, hx0⟩
  · intro t u σ σ' _ h; exact h

end ValidSpecExamples
end MoverLogic
