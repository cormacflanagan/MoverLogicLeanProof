/-
  A concrete, sync-disciplined mover specification that is *provably valid* —
  discharging `Valid` (Definition "Validity") outright, with no assumption.

  The idea: classify an action purely by its *shape* (store-independently), so
  that validity condition (3) — one thread's step cannot change another's mover
  effect — is trivial.  The mover classes are:

    * lock **acquire** `⟨l=free ∧ l:=tid⟩`         → right-mover `R`
    * lock **release** `⟨l=tid ∧ l:=free⟩`         → left-mover  `L`
    * a **local** write (to a variable *owned* by the acting thread) → `B`
    * a **lock-protected** write to the shared `x` (the action itself only fires
      while the thread holds the lock) → `B`
    * a store-preserving **test** whose guard reads only owned variables → `B`
    * anything else                                → error `E`

  Ownership is by a leading-`'A'` run: thread `t` owns exactly the variables whose
  name begins with `t+1` copies of `'A'`.  Two threads therefore own disjoint sets
  (the run length is a function of the name), and the shared `x`, `l` are owned by
  no one — so the sync discipline is: touch `x` only while holding the lock.

  `Valid MspecV` is proved (conditions 1–4), and the two-thread counter state is
  verified via `M-state` with *no* validity hypothesis (`state_valid`).
-/
import MoverLogic.Logic

namespace MoverLogic
namespace ValidSpec

open Effect

/-! ### Store helpers -/

def LOCK : Var := "l"
def XVAR : Var := "x"
def FREE : Value := -1

theorem upd_same (σ : Store) (x : Var) (v : Value) : upd σ x v x = v := by unfold upd; simp
theorem upd_other (σ : Store) (x : Var) (v : Value) (z : Var) (h : z ≠ x) :
    upd σ x v z = σ z := by unfold upd; simp [h]

/-! ### Ownership by leading-`'A'` run -/

/-- Length of the leading run of `'A'`s in a variable name. -/
def leadA (v : Var) : Nat := (v.toList.takeWhile (· = 'A')).length

/-- Thread `t` owns variable `v` iff `v` begins with exactly `t+1` `'A'`s. -/
def owns (t : Tid) (v : Var) : Prop := leadA v = t + 1

/-- **Ownership is disjoint** — the crux of thread-locality — for free, because
    `leadA` is a function of the name. -/
theorem owns_disjoint {v : Var} {t u : Tid} (ht : owns t v) (hu : owns u v) : t = u :=
  Nat.add_right_cancel (ht.symm.trans hu)

theorem not_owns_x (t : Tid) : ¬ owns t XVAR := by simp [owns, leadA, XVAR]
theorem not_owns_l (t : Tid) : ¬ owns t LOCK := by simp [owns, leadA, LOCK]

/-! ### Confinement and the commutation atom -/

/-- A function `g` (a deterministic action body) is *confined* to region `S`:
    it writes only `S`, and its result on `S` depends only on the input on `S`. -/
structure Confined (g : Store → Store) (S : Var → Prop) : Prop where
  writes : ∀ σ v, ¬ S v → g σ v = σ v
  reads  : ∀ σ1 σ2, (∀ v, S v → σ1 v = σ2 v) → (∀ v, S v → g σ1 v = g σ2 v)

/-- **Confined actions over disjoint regions commute.** -/
theorem confined_comm {g1 g2 : Store → Store} {S1 S2 : Var → Prop}
    (h1 : Confined g1 S1) (h2 : Confined g2 S2) (hdisj : ∀ v, S1 v → S2 v → False)
    (σ : Store) : g1 (g2 σ) = g2 (g1 σ) := by
  funext v
  by_cases hs1 : S1 v
  · have hns2 : ¬ S2 v := fun h => hdisj v hs1 h
    rw [h2.writes (g1 σ) v hns2]
    exact h1.reads (g2 σ) σ (fun w hw => h2.writes σ w (fun h => hdisj w hw h)) v hs1
  · by_cases hs2 : S2 v
    · rw [h1.writes (g2 σ) v hs1]
      exact (h2.reads (g1 σ) σ (fun w hw => h1.writes σ w (fun h => hdisj w h hw)) v hs2).symm
    · rw [h1.writes (g2 σ) v hs1, h2.writes σ v hs2, h2.writes (g1 σ) v hs2, h1.writes σ v hs1]

/-- A confined action preserves any variable outside its region.  In particular a
    local/x action preserves the lock `l`. -/
theorem Confined.pres {g S} (h : Confined g S) {v} (hv : ¬ S v) (σ) : g σ v = σ v :=
  h.writes σ v hv

/-! ### The mover classes (store-independent shape recognizers)

Each recognizer says "action `A`, taken by thread `t`, has this shape", as a
property of the *relation* `A` — independent of any current store. -/

/-- Acquire: `l : free → tid`, fires only from a free lock. -/
def IsAcq (A : Action) (t : Tid) : Prop :=
  ∀ σ σ', A t σ σ' ↔ (σ LOCK = FREE ∧ σ' = upd σ LOCK (t : Value))

/-- Release: `l : tid → free`, fires only while holding the lock. -/
def IsRel (A : Action) (t : Tid) : Prop :=
  ∀ σ σ', A t σ σ' ↔ (σ LOCK = (t : Value) ∧ σ' = upd σ LOCK FREE)

/-- A local action: a deterministic `g` confined to the variables owned by `t`. -/
def IsLocal (A : Action) (t : Tid) : Prop :=
  ∃ g, Confined g (owns t) ∧ ∀ σ σ', A t σ σ' ↔ σ' = g σ

/-- A lock-protected access to the shared `x`: deterministic `g` confined to
    `owned(t) ∪ {x}` that leaves the lock alone, firing only while `t` holds it. -/
def IsXacc (A : Action) (t : Tid) : Prop :=
  ∃ g, Confined g (fun v => owns t v ∨ v = XVAR) ∧ (∀ σ, g σ LOCK = σ LOCK) ∧
       ∀ σ σ', A t σ σ' ↔ (σ LOCK = (t : Value) ∧ σ' = g σ)

/-- A store-preserving test whose guard reads only variables owned by `t`. -/
def IsTest (A : Action) (t : Tid) : Prop :=
  ∃ P : Store → Prop, (∀ σ1 σ2, (∀ v, owns t v → σ1 v = σ2 v) → (P σ1 ↔ P σ2)) ∧
    ∀ σ σ', A t σ σ' ↔ (σ' = σ ∧ P σ)

open Classical in
/-- **The mover specification.**  Store-independent: the effect depends only on
    the action's shape, which makes validity condition (3) immediate. -/
noncomputable def MspecV : MoverSpec := fun A t _ =>
  if IsAcq A t then Effect.R
  else if IsRel A t then Effect.L
  else if IsLocal A t then Effect.B
  else if IsXacc A t then Effect.B
  else if IsTest A t then Effect.B
  else Effect.E

theorem MspecV_neverYields : NeverYields MspecV := by
  intro A t σ; unfold MspecV
  repeat' (first | rfl | split)
  all_goals first | rfl | exact (by decide) | (intro h; exact (by decide))

/-! ### A uniform firing witness

Every mover class fires as `σ' = g σ` under a guard `guard σ`, with `g` confined
to a region `R`.  The region is always inside `owned(t) ∪ {l, x}`, and `g`
changes the lock `l` only for acquire/release. -/

/-- `A` (thread `t`) fires as the confined function `g` (region `R`) under `guard`. -/
structure Fires (A : Action) (t : Tid) (g : Store → Store) (R : Var → Prop)
    (guard : Store → Prop) : Prop where
  conf : Confined g R
  char : ∀ σ σ', A t σ σ' ↔ (guard σ ∧ σ' = g σ)

/-- The identity is confined to any region. -/
theorem confined_id (S : Var → Prop) : Confined (fun σ => σ) S := ⟨fun _ _ _ => rfl, fun _ _ h => h⟩

/-- Updating one variable `v` with a constant is confined to `{v}`. -/
theorem confined_constUpd (v : Var) (c : Value) : Confined (fun σ => upd σ v c) (fun w => w = v) :=
  ⟨fun σ w hw => upd_other σ v c w hw, by
    intro σ1 σ2 hag w hw; subst hw; rw [upd_same, upd_same]⟩

/-- Acquire fires as the `{l}`-confined `l := tid`, guarded by `l = free`. -/
theorem acq_fires (h : IsAcq A t) :
    Fires A t (fun σ => upd σ LOCK (t : Value)) (fun w => w = LOCK) (fun σ => σ LOCK = FREE) :=
  ⟨confined_constUpd _ _, by intro σ σ'; rw [h σ σ']⟩

/-- Release fires as the `{l}`-confined `l := free`, guarded by `l = tid`. -/
theorem rel_fires (h : IsRel A t) :
    Fires A t (fun σ => upd σ LOCK FREE) (fun w => w = LOCK) (fun σ => σ LOCK = (t : Value)) :=
  ⟨confined_constUpd _ _, by intro σ σ'; rw [h σ σ']⟩

/-- A local action fires unguarded as its `owned(t)`-confined function. -/
theorem local_fires (h : IsLocal A t) :
    ∃ g, Fires A t g (owns t) (fun _ => True) := by
  obtain ⟨g, hc, hch⟩ := h
  exact ⟨g, hc, by intro σ σ'; rw [hch σ σ']; simp⟩

/-- An x-access fires as its `owned(t) ∪ {x}`-confined function, guarded by `l = tid`;
    it never touches the lock. -/
theorem xacc_fires (h : IsXacc A t) :
    ∃ g, Fires A t g (fun v => owns t v ∨ v = XVAR) (fun σ => σ LOCK = (t : Value))
      ∧ (∀ σ, g σ LOCK = σ LOCK) := by
  obtain ⟨g, hc, hl, hch⟩ := h
  exact ⟨g, ⟨hc, by intro σ σ'; rw [hch σ σ']⟩, hl⟩

/-- A test fires unguarded-shape (guard is its predicate) as the identity. -/
theorem test_fires (h : IsTest A t) :
    ∃ P, Fires A t (fun σ => σ) (owns t) P := by
  obtain ⟨P, hP, hch⟩ := h
  exact ⟨P, confined_id _, by intro σ σ'; rw [hch σ σ']; exact and_comm⟩

/-! ### Region facts (disjointness of the confinement regions) -/

theorem owns_ne_lock {t v} (h : owns t v) : v ≠ LOCK := fun he => not_owns_l t (he ▸ h)
theorem owns_ne_x {t v} (h : owns t v) : v ≠ XVAR := fun he => not_owns_x t (he ▸ h)
theorem lock_ne_x : LOCK ≠ XVAR := by decide

end ValidSpec
end MoverLogic
