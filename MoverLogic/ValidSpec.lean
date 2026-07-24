/-
  A concrete, sync-disciplined mover specification that is *provably valid* —
  discharging `Valid` (Definition "Validity") outright, with no assumption.

  Classification is by an action's *shape*, and reads the store only through one
  cell (the lock, and only for a release).  The mover classes are:

    * lock **acquire** `⟨l=free ∧ l:=tid⟩`  → right-mover `R` (may block; total not
      required, since `R` movers need no "terminates" side condition)
    * lock **release** `l:=free`, **total and unconditional** → left-mover `L`
      *exactly when the releaser holds the lock* (`σ(l)=tid`), else error `E`.
      Making release total (no guard) is what lets it be used in `M-action` at
      effect `L`; the "left-mover only while held" is store-dependent, and stays
      valid because a thread's acquire/release never flips another thread's lock
      ownership (condition (3), `MspecV_stable`).
    * a **local** write (to a variable *owned* by the acting thread) → `B`
    * a **lock-protected** write to the shared `x` → `B`
    * a store-preserving **test** whose guard reads only owned variables → `B`
    * anything else                                → error `E`

  Ownership is by a leading-`'A'` run: thread `t` owns exactly the variables whose
  name begins with `t+1` copies of `'A'`.  Two threads therefore own disjoint sets
  (the run length is a function of the name), and the shared `x`, `l` are owned by
  no one — so the sync discipline is: touch `x` only while holding the lock.

  **`MspecV_valid : Valid MspecV`** is proved outright — all four validity
  conditions of Definition "Validity", with *no* hypothesis — using only the
  three standard axioms.  On top of it, **`acqRel_state_valid`** verifies a
  two-thread lock **acquire/release** state via `M-state` with *no* validity
  hypothesis (the `Valid MspecV` premise discharged by `MspecV_valid`, not
  assumed).  The disciplined actions classify as the paper's movers:
  `MspecV_acquire_le` (`R`), `MspecV_release_le` (`L`, given the lock is held),
  `xWrite_isXacc` (a lock-protected `x`-access is a both-mover).
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

/-- Release: `l := free`, **unconditional and total** (no guard).  Its mover
    effect is store-*dependent* (below): a left-mover exactly when the releaser
    holds the lock. -/
def IsRel (A : Action) (t : Tid) : Prop :=
  ∀ σ σ', A t σ σ' ↔ σ' = upd σ LOCK FREE

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
/-- **The mover specification.**  Almost store-independent: only a release reads
    the store, and only its lock cell — a release is a left-mover exactly when the
    releaser holds the lock (`σ l = tid`), else an error (releasing a lock you do
    not hold is not a mover).  This is the synchronization discipline on the lock,
    and it keeps the total release usable in `M-action` while staying valid. -/
noncomputable def MspecV : MoverSpec := fun A t σ =>
  if IsAcq A t then Effect.R
  else if IsRel A t then (if σ LOCK = (t : Value) then Effect.L else Effect.E)
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

/-- Release fires as the `{l}`-confined `l := free`, **total** (guard `True`). -/
theorem rel_fires (h : IsRel A t) :
    Fires A t (fun σ => upd σ LOCK FREE) (fun w => w = LOCK) (fun _ => True) :=
  ⟨confined_constUpd _ _, by intro σ σ'; rw [h σ σ']; simp⟩

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

/-- `owned(t)` is disjoint from any confinement region `R2` of another thread `u`
    (`u`'s owned vars, or the lock, or `u`'s owned ∪ {x}). -/
theorem ownsT_disj_ownsU {t u} (hne : t ≠ u) : ∀ v, owns t v → owns u v → False :=
  fun _ h1 h2 => hne (owns_disjoint h1 h2)

/-! ### Inverting the effect bound back to a class -/

theorem le_R_cases {A t σ} (h : MspecV A t σ ⊑ Effect.R) :
    IsAcq A t ∨ IsLocal A t ∨ IsXacc A t ∨ IsTest A t := by
  unfold MspecV at h
  by_cases h1 : IsAcq A t
  · exact .inl h1
  · rw [if_neg h1] at h
    by_cases h2 : IsRel A t
    · rw [if_pos h2] at h
      by_cases hlk : σ LOCK = (t : Value)
      · rw [if_pos hlk] at h; exact absurd h (by decide)
      · rw [if_neg hlk] at h; exact absurd h (by decide)
    · rw [if_neg h2] at h
      by_cases h3 : IsLocal A t
      · exact .inr (.inl h3)
      · rw [if_neg h3] at h
        by_cases h4 : IsXacc A t
        · exact .inr (.inr (.inl h4))
        · rw [if_neg h4] at h
          by_cases h5 : IsTest A t
          · exact .inr (.inr (.inr h5))
          · rw [if_neg h5] at h; exact absurd h (by decide)

theorem le_N_cases {A t σ} (h : MspecV A t σ ⊑ Effect.N) :
    IsAcq A t ∨ IsRel A t ∨ IsLocal A t ∨ IsXacc A t ∨ IsTest A t := by
  unfold MspecV at h
  by_cases h1 : IsAcq A t
  · exact .inl h1
  · rw [if_neg h1] at h
    by_cases h2 : IsRel A t
    · by_cases hlk : σ LOCK = (t : Value)
      · exact .inr (.inl h2)
      · rw [if_pos h2, if_neg hlk] at h; exact absurd h (by decide)
    · rw [if_neg h2] at h
      by_cases h3 : IsLocal A t
      · exact .inr (.inr (.inl h3))
      · rw [if_neg h3] at h
        by_cases h4 : IsXacc A t
        · exact .inr (.inr (.inr (.inl h4)))
        · rw [if_neg h4] at h
          by_cases h5 : IsTest A t
          · exact .inr (.inr (.inr (.inr h5)))
          · rw [if_neg h5] at h; exact absurd h (by decide)

theorem le_L_cases {A t σ} (h : MspecV A t σ ⊑ Effect.L) :
    IsRel A t ∨ IsLocal A t ∨ IsXacc A t ∨ IsTest A t := by
  unfold MspecV at h
  by_cases h1 : IsAcq A t
  · rw [if_pos h1] at h; exact absurd h (by decide)
  · rw [if_neg h1] at h
    by_cases h2 : IsRel A t
    · by_cases hlk : σ LOCK = (t : Value)
      · exact .inl h2
      · rw [if_pos h2, if_neg hlk] at h; exact absurd h (by decide)
    · rw [if_neg h2] at h
      by_cases h3 : IsLocal A t
      · exact .inr (.inl h3)
      · rw [if_neg h3] at h
        by_cases h4 : IsXacc A t
        · exact .inr (.inr (.inl h4))
        · rw [if_neg h4] at h
          by_cases h5 : IsTest A t
          · exact .inr (.inr (.inr h5))
          · rw [if_neg h5] at h; exact absurd h (by decide)

/-- A total release is never an acquire. -/
theorem isRel_not_isAcq {A t} (h : IsRel A t) : ¬ IsAcq A t := by
  intro hacq
  have h1 : A t (fun _ => (0 : Value)) (upd (fun _ => (0 : Value)) LOCK FREE) := (h _ _).mpr rfl
  exact absurd ((hacq _ _).mp h1).1 (by decide)

/-- **A release is a mover only while its thread holds the lock.**  If a release's
    effect is non-error at `σ`, then `σ(l) = tid` — the sync discipline made
    usable in the validity conditions. -/
theorem rel_classified {A u σ} (hrel : IsRel A u) (h : MspecV A u σ ⊑ Effect.N) :
    σ LOCK = (u : Value) := by
  unfold MspecV at h
  rw [if_neg (isRel_not_isAcq hrel), if_pos hrel] at h
  by_cases hlk : σ LOCK = (u : Value)
  · exact hlk
  · rw [if_neg hlk] at h; exact absurd h (by decide)

/-! ### Guard/value preservation across a disjoint confined action -/

/-- A confined `g` disjoint from `owned(u)` preserves a `u`-test's guard. -/
theorem test_guard_pres {g R} {u} (hc : Confined g R) (hdisj : ∀ v, R v → owns u v → False)
    {P : Store → Prop} (hP : ∀ σ1 σ2, (∀ v, owns u v → σ1 v = σ2 v) → (P σ1 ↔ P σ2)) (σ) :
    P (g σ) ↔ P σ :=
  hP (g σ) σ (fun v hv => hc.writes σ v (fun h => hdisj v h hv))

/-- A confined `g` that never touches the lock preserves any lock predicate. -/
theorem lock_pres {g R} (hc : Confined g R) (hL : ¬ R LOCK) (σ) : g σ LOCK = σ LOCK :=
  hc.writes σ LOCK hL

/-! ### The two commutation shapes -/

/-- Sequential commutation (conditions 1 and 2): `A1` from `σ`, `A2` from `σ'`;
    if `A2` may also fire from `σ` and `A1` from `g2 σ`, and regions are disjoint,
    then `A2` can go first. -/
theorem commute_seq {A1 A2 t u σ σ' σ'' g1 g2 R1 R2 guard1 guard2}
    (F1 : Fires A1 t g1 R1 guard1) (F2 : Fires A2 u g2 R2 guard2)
    (hdisj : ∀ v, R1 v → R2 v → False)
    (hg2σ : guard2 σ) (hg1 : guard1 (g2 σ))
    (h2 : A2 u σ' σ'') (h1 : A1 t σ σ') :
    ∃ σ''', A2 u σ σ''' ∧ A1 t σ''' σ'' := by
  obtain ⟨_, e1⟩ := (F1.char σ σ').mp h1
  obtain ⟨_, e2⟩ := (F2.char σ' σ'').mp h2
  refine ⟨g2 σ, (F2.char σ (g2 σ)).mpr ⟨hg2σ, rfl⟩, (F1.char (g2 σ) σ'').mpr ⟨hg1, ?_⟩⟩
  rw [e2, e1, confined_comm F1.conf F2.conf hdisj σ]

/-- Diamond commutation (condition 4): `A1` and `A2` both from `σ`; if each may
    fire after the other and regions are disjoint, they reach a common state. -/
theorem commute_diamond {A1 A2 t u σ σ' σ'' g1 g2 R1 R2 guard1 guard2}
    (F1 : Fires A1 t g1 R1 guard1) (F2 : Fires A2 u g2 R2 guard2)
    (hdisj : ∀ v, R1 v → R2 v → False)
    (hg2 : guard2 σ') (hg1 : guard1 σ'')
    (h1 : A1 t σ σ') (h2 : A2 u σ σ'') :
    ∃ σ''', A2 u σ' σ''' ∧ A1 t σ'' σ''' := by
  obtain ⟨_, e1⟩ := (F1.char σ σ').mp h1
  obtain ⟨_, e2⟩ := (F2.char σ σ'').mp h2
  refine ⟨g1 σ'', (F2.char σ' (g1 σ'')).mpr ⟨hg2, ?_⟩, (F1.char σ'' (g1 σ'')).mpr ⟨hg1, rfl⟩⟩
  rw [e2, e1, ← confined_comm F1.conf F2.conf hdisj σ]

/-! ### Value/tid arithmetic helpers -/

theorem t_ne_free (t : Tid) : (t : Value) ≠ FREE := by
  show (↑t : Int) ≠ -1; omega
theorem free_ne_tid (u : Tid) : FREE ≠ (u : Value) := (t_ne_free u).symm
theorem tid_cast_inj {t u : Tid} (h : (t : Value) = (u : Value)) : t = u := by
  exact_mod_cast h

/-- After an acquire or x-access by `t`, the lock reads `tid`. -/
theorem post_lock_t_acq {A t σ σ'} (h : IsAcq A t) (h1 : A t σ σ') : σ' LOCK = (t : Value) := by
  obtain ⟨_, e⟩ := (h σ σ').mp h1; rw [e, upd_same]
theorem post_lock_t_xacc {A : Action} {t : Tid} {σ σ' : Store} {g : Store → Store}
    (hg : ∀ σ, g σ LOCK = σ LOCK)
    (hch : ∀ σ σ', A t σ σ' ↔ (σ LOCK = (t : Value) ∧ σ' = g σ)) (h1 : A t σ σ') :
    σ' LOCK = (t : Value) := by
  obtain ⟨hguard, e⟩ := (hch σ σ').mp h1; rw [e, hg]; exact hguard

/-- **The classification of `A2` (by `u`) is unchanged by a mover step of `t ≠ u`.**
    Only a release reads the store (its lock cell), and a `t`-mover keeps
    `σ(l) = u ↔ σ'(l) = u` — so validity condition (3) still holds. -/
theorem MspecV_stable {A1 A2 : Action} {t u : Tid} {σ σ' : Store}
    (hne : t ≠ u) (hN : MspecV A1 t σ ⊑ Effect.N) (h1 : A1 t σ σ') :
    MspecV A2 u σ = MspecV A2 u σ' := by
  have hlock : σ LOCK = (u : Value) ↔ σ' LOCK = (u : Value) := by
    rcases le_N_cases hN with h | h | h | h | h
    · have e1 := post_lock_t_acq h h1
      have e0 := ((h σ σ').mp h1).1
      constructor <;> intro hh
      · rw [e0] at hh; exact absurd hh.symm (t_ne_free u)
      · rw [e1] at hh; exact absurd (tid_cast_inj hh) hne
    · have hσl := rel_classified h hN
      have hσ' : σ' LOCK = FREE := by rw [(h σ σ').mp h1, upd_same]
      constructor <;> intro hh
      · rw [hσl] at hh; exact absurd (tid_cast_inj hh) hne
      · rw [hσ'] at hh; exact absurd hh.symm (t_ne_free u)
    · obtain ⟨g1, hc1, hch1⟩ := h
      rw [show σ' LOCK = σ LOCK by rw [(hch1 σ σ').mp h1]; exact lock_pres hc1 (not_owns_l t) σ]
    · obtain ⟨g1, hc1, hlk1, hch1⟩ := h
      rw [show σ' LOCK = σ LOCK by rw [((hch1 σ σ').mp h1).2]; exact hlk1 σ]
    · obtain ⟨P, _, hch1⟩ := h
      rw [show σ' = σ from ((hch1 σ σ').mp h1).1]
  unfold MspecV
  by_cases hacq : IsAcq A2 u
  · rw [if_pos hacq, if_pos hacq]
  · rw [if_neg hacq, if_neg hacq]
    by_cases hrel : IsRel A2 u
    · rw [if_pos hrel, if_pos hrel]
      by_cases hh : σ LOCK = (u : Value)
      · rw [if_pos hh, if_pos (hlock.mp hh)]
      · rw [if_neg hh, if_neg (mt hlock.mpr hh)]
    · rw [if_neg hrel, if_neg hrel]

/-- **Extraction bundle for the "other" action** `A2` (thread `u ≠ t`) from its
    non-error effect: a firing witness whose region is disjoint from `owned(t)`,
    and whose guard is preserved by any action confined to `owned(t)`. -/
theorem extract_other {A2 : Action} {u t : Tid} {σ0 : Store} (hne : t ≠ u)
    (h : MspecV A2 u σ0 ⊑ Effect.N) :
    ∃ g2 R2 guard2, Fires A2 u g2 R2 guard2 ∧ (∀ v, R2 v → owns t v → False) ∧
      (∀ {g}, Confined g (owns t) → ∀ s, guard2 (g s) ↔ guard2 s) := by
  have hlock : ∀ {g : Store → Store}, Confined g (owns t) → ∀ (s : Store), g s LOCK = s LOCK :=
    fun hc s => lock_pres hc (not_owns_l t) s
  rcases le_N_cases h with h | h | h | h | h
  · refine ⟨_, _, _, acq_fires h, fun v hv ho => not_owns_l t (hv ▸ ho), ?_⟩
    intro g hc s; change (g s LOCK = FREE) ↔ (s LOCK = FREE); rw [hlock hc s]
  · exact ⟨_, _, _, rel_fires h, fun v hv ho => not_owns_l t (hv ▸ ho), fun _ _ => Iff.rfl⟩
  · obtain ⟨g2, F2⟩ := local_fires h
    exact ⟨g2, owns u, (fun _ => True), F2, fun v hv ho => hne (owns_disjoint ho hv),
      fun _ _ => Iff.rfl⟩
  · obtain ⟨g2, F2, _⟩ := xacc_fires h
    refine ⟨g2, _, _, F2, ?_, ?_⟩
    · rintro v (hv | hv) ho
      · exact hne (owns_disjoint ho hv)
      · exact not_owns_x t (hv ▸ ho)
    · intro g hc s; change (g s LOCK = (u : Value)) ↔ (s LOCK = (u : Value)); rw [hlock hc s]
  · obtain ⟨P, hPframe, hch⟩ := h
    refine ⟨_, owns u, P, ⟨confined_id (owns u), ?_⟩, fun v hv ho => hne (owns_disjoint ho hv),
      fun hc s => test_guard_pres hc (fun v hv ho => hne (owns_disjoint hv ho)) hPframe s⟩
    intro σ σ'; rw [hch σ σ']; exact and_comm

/-- Extraction for a **local or test** action: region `owned(u)`, guard preserved
    by any action confined to a region disjoint from `owned(u)`. -/
theorem extract_lt {A2 : Action} {u : Tid} (h : IsLocal A2 u ∨ IsTest A2 u) :
    ∃ g2 guard2, Fires A2 u g2 (owns u) guard2 ∧
      (∀ {g : Store → Store} {R : Var → Prop}, Confined g R → (∀ v, R v → owns u v → False) →
        ∀ s, guard2 (g s) ↔ guard2 s) := by
  rcases h with h | h
  · obtain ⟨g2, F2⟩ := local_fires h
    exact ⟨g2, _, F2, fun _ _ _ => Iff.rfl⟩
  · obtain ⟨P, hPframe, hch⟩ := h
    refine ⟨_, P, ⟨confined_id (owns u), ?_⟩, fun hc hdisj s => test_guard_pres hc hdisj hPframe s⟩
    intro σ σ'; rw [hch σ σ']; exact and_comm

/-! ### Condition (3): a mover of `t` cannot change `u`'s effect (via `MspecV_stable`). -/
theorem cond3 : ∀ (t u : Tid) (A1 A2 : Action) (σ σ' : Store) (e : Effect),
    t ≠ u → MspecV A1 t σ ⊑ Effect.N → A1 t σ σ' → MspecV A2 u σ = e → MspecV A2 u σ' = e :=
  fun _ _ _ _ _ _ _ hne hN h1 he => (MspecV_stable hne hN h1).symm.trans he

/-- Commute a lock-op / x-access `A1` (region `R1`, disjoint from `owned(u)`,
    guard on the lock) past a following local/test `A2`. -/
theorem commute_shared_lt {A1 A2 : Action} {t u : Tid} {σ σ' σ'' : Store}
    {g1 : Store → Store} {R1 : Var → Prop} {guard1 : Store → Prop}
    (F1 : Fires A1 t g1 R1 guard1) (hR1disj : ∀ v, R1 v → owns u v → False)
    (hg1refire : ∀ (g2 : Store → Store), (∀ s, g2 s LOCK = s LOCK) → guard1 σ → guard1 (g2 σ))
    (hg1σ : guard1 σ) (hlt : IsLocal A2 u ∨ IsTest A2 u)
    (h1 : A1 t σ σ') (h2 : A2 u σ' σ'') :
    ∃ σ''', A2 u σ σ''' ∧ A1 t σ''' σ'' := by
  obtain ⟨g2, guard2, F2, hgpres⟩ := extract_lt hlt
  obtain ⟨hg2σ', _⟩ := (F2.char σ' σ'').mp h2
  obtain ⟨_, e1⟩ := (F1.char σ σ').mp h1
  have hg2l : ∀ s, g2 s LOCK = s LOCK := fun s => lock_pres F2.conf (not_owns_l u) s
  refine commute_seq F1 F2 (fun v hR1 ho => hR1disj v hR1 ho) ?_ (hg1refire g2 hg2l hg1σ) h2 h1
  rw [e1] at hg2σ'
  exact (hgpres F1.conf hR1disj σ).mp hg2σ'

/-! ### Condition (1): a right-mover commutes after a following non-mover. -/
theorem cond1 {t u : Tid} {A1 A2 : Action} {σ σ' σ'' : Store}
    (hne : t ≠ u) (hR : MspecV A1 t σ ⊑ Effect.R) (h1 : A1 t σ σ')
    (hN : MspecV A2 u σ' ⊑ Effect.N) (h2 : A2 u σ' σ'') :
    ∃ σ''', A2 u σ σ''' ∧ A1 t σ''' σ'' := by
  -- lock-contending A2 could not have fired once the lock reads `t`
  have vac : σ' LOCK = (t : Value) →
      (IsAcq A2 u ∨ IsRel A2 u ∨ IsXacc A2 u) → False := by
    intro hlt hc
    rcases hc with h | h | h
    · exact t_ne_free t (hlt ▸ ((h σ' σ'').mp h2).1)
    · exact hne (tid_cast_inj (hlt.symm.trans (rel_classified h hN)))
    · obtain ⟨g, _, _, hch⟩ := h
      exact hne (tid_cast_inj (hlt ▸ ((hch σ' σ'').mp h2).1))
  rcases le_R_cases hR with hA1 | hA1 | hA1 | hA1
  · -- A1 = acquire
    have hlt : σ' LOCK = (t : Value) := post_lock_t_acq hA1 h1
    have hg1σ : σ LOCK = FREE := ((hA1 σ σ').mp h1).1
    rcases le_N_cases hN with h | h | h | h | h
    · exact (vac hlt (.inl h)).elim
    · exact (vac hlt (.inr (.inl h))).elim
    · exact commute_shared_lt (acq_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun g2 hg2 hg => by change g2 σ LOCK = FREE; rw [hg2]; exact hg) hg1σ (.inl h) h1 h2
    · exact (vac hlt (.inr (.inr h))).elim
    · exact commute_shared_lt (acq_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun g2 hg2 hg => by change g2 σ LOCK = FREE; rw [hg2]; exact hg) hg1σ (.inr h) h1 h2
  · -- A1 = local: commutes with every A2
    obtain ⟨g1, F1⟩ := local_fires hA1
    obtain ⟨g2, R2, guard2, F2, hRdisj, hgpres⟩ := extract_other hne hN
    obtain ⟨_, e1⟩ := (F1.char σ σ').mp h1
    obtain ⟨hg2σ', _⟩ := (F2.char σ' σ'').mp h2
    refine commute_seq F1 F2 (fun v hR1 hR2 => hRdisj v hR2 hR1) ?_ trivial h2 h1
    rw [e1] at hg2σ'; exact (hgpres F1.conf σ).mp hg2σ'
  · -- A1 = x-access
    obtain ⟨g1, hc1, hlk1, hch1⟩ := hA1
    have hlt : σ' LOCK = (t : Value) := post_lock_t_xacc hlk1 hch1 h1
    have hg1σ : σ LOCK = (t : Value) := ((hch1 σ σ').mp h1).1
    have F1 : Fires A1 t g1 (fun v => owns t v ∨ v = XVAR) (fun σ => σ LOCK = (t : Value)) :=
      ⟨hc1, hch1⟩
    have hdisj : ∀ v, (owns t v ∨ v = XVAR) → owns u v → False := by
      rintro v (hv | hv) ho
      · exact hne (owns_disjoint hv ho)
      · exact not_owns_x u (hv ▸ ho)
    rcases le_N_cases hN with h | h | h | h | h
    · exact (vac hlt (.inl h)).elim
    · exact (vac hlt (.inr (.inl h))).elim
    · exact commute_shared_lt F1 hdisj
        (fun g2 hg2 hg => by change g2 σ LOCK = (t : Value); rw [hg2]; exact hg) hg1σ (.inl h) h1 h2
    · exact (vac hlt (.inr (.inr h))).elim
    · exact commute_shared_lt F1 hdisj
        (fun g2 hg2 hg => by change g2 σ LOCK = (t : Value); rw [hg2]; exact hg) hg1σ (.inr h) h1 h2
  · -- A1 = test: commutes with every A2
    obtain ⟨P, hPframe, hch⟩ := hA1
    have F1 : Fires A1 t (fun σ => σ) (owns t) P :=
      ⟨confined_id _, by intro a b; rw [hch a b]; exact and_comm⟩
    obtain ⟨g2, R2, guard2, F2, hRdisj, _⟩ := extract_other hne hN
    obtain ⟨hPσ, e1⟩ := (F1.char σ σ').mp h1
    obtain ⟨hg2σ', _⟩ := (F2.char σ' σ'').mp h2
    refine commute_seq F1 F2 (fun v hR1 hR2 => hRdisj v hR2 hR1) ?_ ?_ h2 h1
    · rw [show σ' = σ from e1] at hg2σ'; exact hg2σ'
    · exact (test_guard_pres F2.conf (fun v hR2 ho => hRdisj v hR2 ho) hPframe σ).mpr hPσ

/-- Commute an `A1` confined to `owned(t)` (local/test) with the following `A2`
    (any non-error): the symmetric partner of `commute_shared_lt`, used when the
    *left*-mover `A2` is the shared one. -/
theorem commute_lt_any {A1 A2 : Action} {t u : Tid} {σ σ' σ'' : Store}
    {g1 : Store → Store} {guard1 : Store → Prop}
    (hne : t ≠ u) (F1 : Fires A1 t g1 (owns t) guard1)
    (hg1refire : ∀ {g2 : Store → Store} {R2 : Var → Prop}, Confined g2 R2 →
      (∀ v, R2 v → owns t v → False) → guard1 σ → guard1 (g2 σ))
    (hN2 : MspecV A2 u σ' ⊑ Effect.N) (h1 : A1 t σ σ') (h2 : A2 u σ' σ'') :
    ∃ σ''', A2 u σ σ''' ∧ A1 t σ''' σ'' := by
  obtain ⟨g2, R2, guard2, F2, hRdisj, hgpres⟩ := extract_other hne hN2
  obtain ⟨hg1σ, e1⟩ := (F1.char σ σ').mp h1
  obtain ⟨hg2σ', _⟩ := (F2.char σ' σ'').mp h2
  refine commute_seq F1 F2 (fun v hR1 hR2 => hRdisj v hR2 hR1) ?_ (hg1refire F2.conf hRdisj hg1σ) h2 h1
  rw [e1] at hg2σ'; exact (hgpres F1.conf σ).mp hg2σ'

/-! ### Condition (2): a left-mover commutes before a preceding non-mover.

We case on `A1` (the non-mover): if it is confined to `owned(t)` it commutes with
the left-mover `A2` for free; if it is a lock op / x-access, then `A2` local/test
commutes and `A2` lock-contending is impossible (the lock already reads `t`/free). -/
theorem cond2 {t u : Tid} {A1 A2 : Action} {σ σ' σ'' : Store}
    (hne : t ≠ u) (hN : MspecV A1 t σ ⊑ Effect.N) (h1 : A1 t σ σ')
    (hL : MspecV A2 u σ' ⊑ Effect.L) (h2 : A2 u σ' σ'') :
    ∃ σ''', A2 u σ σ''' ∧ A1 t σ''' σ'' := by
  -- A2 lock-contending (rel/xacc) reads `σ' l = u`.
  have hA2u : (IsRel A2 u ∨ IsXacc A2 u) → σ' LOCK = (u : Value) := by
    rintro (h | h)
    · exact rel_classified h (le_trans hL (by decide))
    · obtain ⟨g, _, _, hch⟩ := h; exact ((hch σ' σ'').mp h2).1
  rcases le_N_cases hN with hA1 | hA1 | hA1 | hA1 | hA1
  · -- A1 = acquire: σ' l = t
    have hlt : σ' LOCK = (t : Value) := post_lock_t_acq hA1 h1
    rcases le_L_cases hL with h | h | h | h
    · exact absurd ((hlt ▸ hA2u (.inl h)) : (t:Value) = (u:Value)) (fun e => hne (tid_cast_inj e))
    · exact commute_shared_lt (acq_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun g2 hg2 hg => by change g2 σ LOCK = FREE; rw [hg2]; exact hg) ((hA1 σ σ').mp h1).1 (.inl h) h1 h2
    · exact absurd ((hlt ▸ hA2u (.inr h)) : (t:Value) = (u:Value)) (fun e => hne (tid_cast_inj e))
    · exact commute_shared_lt (acq_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun g2 hg2 hg => by change g2 σ LOCK = FREE; rw [hg2]; exact hg) ((hA1 σ σ').mp h1).1 (.inr h) h1 h2
  · -- A1 = release: total, σ' l = free
    have hlf : σ' LOCK = FREE := by rw [(hA1 σ σ').mp h1, upd_same]
    rcases le_L_cases hL with h | h | h | h
    · exact absurd ((hlf ▸ hA2u (.inl h)) : (FREE:Value) = (u:Value)) (free_ne_tid u)
    · exact commute_shared_lt (rel_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun _ _ h => h) trivial (.inl h) h1 h2
    · exact absurd ((hlf ▸ hA2u (.inr h)) : (FREE:Value) = (u:Value)) (free_ne_tid u)
    · exact commute_shared_lt (rel_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun _ _ h => h) trivial (.inr h) h1 h2
  · -- A1 = local: commutes with any A2 (⊑ L ⟹ ⊑ N)
    obtain ⟨g1, F1⟩ := local_fires hA1
    exact commute_lt_any hne F1 (fun _ _ h => h) (le_trans hL (by decide)) h1 h2
  · -- A1 = x-access: σ' l = t
    obtain ⟨g1, hc1, hlk1, hch1⟩ := hA1
    have F1 : Fires A1 t g1 (fun v => owns t v ∨ v = XVAR) (fun σ => σ LOCK = (t : Value)) := ⟨hc1, hch1⟩
    have hlt : σ' LOCK = (t : Value) := post_lock_t_xacc hlk1 hch1 h1
    have hg1σ : σ LOCK = (t : Value) := ((hch1 σ σ').mp h1).1
    have hdisj : ∀ v, (owns t v ∨ v = XVAR) → owns u v → False := by
      rintro v (hv | hv) ho
      · exact hne (owns_disjoint hv ho)
      · exact not_owns_x u (hv ▸ ho)
    rcases le_L_cases hL with h | h | h | h
    · exact absurd ((hlt ▸ hA2u (.inl h)) : (t:Value) = (u:Value)) (fun e => hne (tid_cast_inj e))
    · exact commute_shared_lt F1 hdisj
        (fun g2 hg2 hg => by change g2 σ LOCK = (t:Value); rw [hg2]; exact hg) hg1σ (.inl h) h1 h2
    · exact absurd ((hlt ▸ hA2u (.inr h)) : (t:Value) = (u:Value)) (fun e => hne (tid_cast_inj e))
    · exact commute_shared_lt F1 hdisj
        (fun g2 hg2 hg => by change g2 σ LOCK = (t:Value); rw [hg2]; exact hg) hg1σ (.inr h) h1 h2
  · -- A1 = test: commutes with any A2
    obtain ⟨P, hPframe, hch⟩ := hA1
    have F1 : Fires A1 t (fun σ => σ) (owns t) P :=
      ⟨confined_id _, by intro a b; rw [hch a b]; exact and_comm⟩
    refine commute_lt_any hne F1 ?_ (le_trans hL (by decide)) h1 h2
    intro g2 R2 hc2 hd2 hPσ
    exact (test_guard_pres hc2 hd2 hPframe σ).mpr hPσ

/-! ### Condition (4): a non-mover cannot make a left-mover in another thread
block — the diamond. -/

theorem commute_diam_lt_any {A1 A2 : Action} {t u : Tid} {σ σ' σ'' : Store}
    {g1 : Store → Store} {guard1 : Store → Prop} (hne : t ≠ u)
    (F1 : Fires A1 t g1 (owns t) guard1)
    (hg1refire : ∀ {g2 : Store → Store} {R2 : Var → Prop}, Confined g2 R2 →
      (∀ v, R2 v → owns t v → False) → guard1 σ → guard1 (g2 σ))
    (hN2 : MspecV A2 u σ ⊑ Effect.N) (h1 : A1 t σ σ') (h2 : A2 u σ σ'') :
    ∃ σ''', A2 u σ' σ''' ∧ A1 t σ'' σ''' := by
  obtain ⟨g2, R2, guard2, F2, hRdisj, hgpres⟩ := extract_other hne hN2
  obtain ⟨hg1σ, e1⟩ := (F1.char σ σ').mp h1
  obtain ⟨hg2σ, e2⟩ := (F2.char σ σ'').mp h2
  refine commute_diamond F1 F2 (fun v hR1 hR2 => hRdisj v hR2 hR1) ?_ ?_ h1 h2
  · rw [e1]; exact (hgpres F1.conf σ).mpr hg2σ
  · rw [e2]; exact hg1refire F2.conf hRdisj hg1σ

theorem commute_diam_shared_lt {A1 A2 : Action} {t u : Tid} {σ σ' σ'' : Store}
    {g1 : Store → Store} {R1 : Var → Prop} {guard1 : Store → Prop}
    (F1 : Fires A1 t g1 R1 guard1) (hR1disj : ∀ v, R1 v → owns u v → False)
    (hg1refire : ∀ (g2 : Store → Store), (∀ s, g2 s LOCK = s LOCK) → guard1 σ → guard1 (g2 σ))
    (hg1σ : guard1 σ) (hlt : IsLocal A2 u ∨ IsTest A2 u)
    (h1 : A1 t σ σ') (h2 : A2 u σ σ'') :
    ∃ σ''', A2 u σ' σ''' ∧ A1 t σ'' σ''' := by
  obtain ⟨g2, guard2, F2, hgpres⟩ := extract_lt hlt
  obtain ⟨_, e1⟩ := (F1.char σ σ').mp h1
  obtain ⟨hg2σ, e2⟩ := (F2.char σ σ'').mp h2
  have hg2l : ∀ s, g2 s LOCK = s LOCK := fun s => lock_pres F2.conf (not_owns_l u) s
  refine commute_diamond F1 F2 (fun v hR1 ho => hR1disj v hR1 ho) ?_ ?_ h1 h2
  · rw [e1]; exact (hgpres F1.conf hR1disj σ).mpr hg2σ
  · rw [e2]; exact hg1refire g2 hg2l hg1σ

theorem cond4 {t u : Tid} {A1 A2 : Action} {σ σ' σ'' : Store}
    (hne : t ≠ u) (hN : MspecV A1 t σ ⊑ Effect.N) (h1 : A1 t σ σ')
    (hL : MspecV A2 u σ ⊑ Effect.L) (h2 : A2 u σ σ'') :
    ∃ σ''', A2 u σ' σ''' ∧ A1 t σ'' σ''' := by
  have hA2u : (IsRel A2 u ∨ IsXacc A2 u) → σ LOCK = (u : Value) := by
    rintro (h | h)
    · exact rel_classified h (le_trans hL (by decide))
    · obtain ⟨g, _, _, hch⟩ := h; exact ((hch σ σ'').mp h2).1
  rcases le_N_cases hN with hA1 | hA1 | hA1 | hA1 | hA1
  · -- A1 = acquire: σ l = free
    have hf : σ LOCK = FREE := ((hA1 σ σ').mp h1).1
    rcases le_L_cases hL with h | h | h | h
    · exact absurd (hf ▸ hA2u (.inl h)) (free_ne_tid u)
    · exact commute_diam_shared_lt (acq_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun g2 hg2 hg => by change g2 σ LOCK = FREE; rw [hg2]; exact hg) hf (.inl h) h1 h2
    · exact absurd (hf ▸ hA2u (.inr h)) (free_ne_tid u)
    · exact commute_diam_shared_lt (acq_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun g2 hg2 hg => by change g2 σ LOCK = FREE; rw [hg2]; exact hg) hf (.inr h) h1 h2
  · -- A1 = release: total, mover ⟹ σ l = t
    have ht : σ LOCK = (t : Value) := rel_classified hA1 hN
    rcases le_L_cases hL with h | h | h | h
    · exact absurd ((ht ▸ hA2u (.inl h)) : (t:Value) = (u:Value)) (fun e => hne (tid_cast_inj e))
    · exact commute_diam_shared_lt (rel_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun _ _ h => h) trivial (.inl h) h1 h2
    · exact absurd ((ht ▸ hA2u (.inr h)) : (t:Value) = (u:Value)) (fun e => hne (tid_cast_inj e))
    · exact commute_diam_shared_lt (rel_fires hA1) (fun v hv ho => not_owns_l u (hv ▸ ho))
        (fun _ _ h => h) trivial (.inr h) h1 h2
  · -- A1 = local
    obtain ⟨g1, F1⟩ := local_fires hA1
    exact commute_diam_lt_any hne F1 (fun _ _ h => h) (le_trans hL (by decide)) h1 h2
  · -- A1 = x-access: σ l = t
    obtain ⟨g1, hc1, hlk1, hch1⟩ := hA1
    have F1 : Fires A1 t g1 (fun v => owns t v ∨ v = XVAR) (fun σ => σ LOCK = (t : Value)) := ⟨hc1, hch1⟩
    have ht : σ LOCK = (t : Value) := ((hch1 σ σ').mp h1).1
    have hdisj : ∀ v, (owns t v ∨ v = XVAR) → owns u v → False := by
      rintro v (hv | hv) ho
      · exact hne (owns_disjoint hv ho)
      · exact not_owns_x u (hv ▸ ho)
    rcases le_L_cases hL with h | h | h | h
    · exact absurd ((ht ▸ hA2u (.inl h)) : (t:Value) = (u:Value)) (fun e => hne (tid_cast_inj e))
    · exact commute_diam_shared_lt F1 hdisj
        (fun g2 hg2 hg => by change g2 σ LOCK = (t:Value); rw [hg2]; exact hg) ht (.inl h) h1 h2
    · exact absurd ((ht ▸ hA2u (.inr h)) : (t:Value) = (u:Value)) (fun e => hne (tid_cast_inj e))
    · exact commute_diam_shared_lt F1 hdisj
        (fun g2 hg2 hg => by change g2 σ LOCK = (t:Value); rw [hg2]; exact hg) ht (.inr h) h1 h2
  · -- A1 = test
    obtain ⟨P, hPframe, hch⟩ := hA1
    have F1 : Fires A1 t (fun σ => σ) (owns t) P :=
      ⟨confined_id _, by intro a b; rw [hch a b]; exact and_comm⟩
    refine commute_diam_lt_any hne F1 ?_ (le_trans hL (by decide)) h1 h2
    intro g2 R2 hc2 hd2 hPσ
    exact (test_guard_pres hc2 hd2 hPframe σ).mpr hPσ

/-- **`MspecV` is valid** — all four conditions, with no assumption. -/
theorem MspecV_valid : Valid MspecV where
  right := fun _ _ _ _ _ _ _ hne hR h1 hN h2 => cond1 hne hR h1 hN h2
  left := fun _ _ _ _ _ _ _ hne hN h1 hL h2 => cond2 hne hN h1 hL h2
  effect := cond3
  nonblock := fun _ _ _ _ _ _ _ hne hN h1 hL h2 => cond4 hne hN h1 hL h2

/-! ### The disciplined program actions classify as the paper's movers

Concrete evidence that `MspecV` gives the paper's mover annotations against a
*valid* spec: the lock ops are right/left movers, and a lock-protected `x`-access
whose value reads only owned/`x` state is a both-mover — the sync discipline
made precise (`x` is a both-mover *because the action holds the lock*). -/

/-- The store-independence of `MspecV` lifts a uniform pointwise bound. -/
theorem MspecV_lift_le {A : Action} {P : Pred2} {e : Effect} (h : ∀ t σ, MspecV A t σ ⊑ e) :
    MspecV.lift A P ⊑ e := by
  apply sSup_le; rintro e' ⟨t, σ, σ0, _, rfl⟩; exact h t σ

/-- `acquire` on the lock (guarded — an acquire may block; it is a right-mover, so
    `M-action` needs no totality). -/
def acquireL : Action := fun t σ σ' => σ LOCK = FREE ∧ σ' = upd σ LOCK (t : Value)
/-- `release` on the lock — **total and unconditional** (`l := free`), per the fix.
    Its effect is store-dependent: a left-mover exactly while the lock is held. -/
def releaseL : Action := fun _ σ σ' => σ' = upd σ LOCK FREE

theorem MspecV_acquire (t : Tid) (σ : Store) : MspecV acquireL t σ = Effect.R := by
  have hacq : IsAcq acquireL t := fun _ _ => Iff.rfl
  unfold MspecV; rw [if_pos hacq]

theorem isRel_releaseL (t : Tid) : IsRel releaseL t := fun _ _ => Iff.rfl

/-- Release is a left-mover **exactly when the releaser holds the lock**. -/
theorem MspecV_release_held (t : Tid) (σ : Store) (h : σ LOCK = (t : Value)) :
    MspecV releaseL t σ = Effect.L := by
  unfold MspecV
  rw [if_neg (isRel_not_isAcq (isRel_releaseL t)), if_pos (isRel_releaseL t), if_pos h]

theorem MspecV_acquire_le (P : Pred2) : MspecV.lift acquireL P ⊑ Effect.R :=
  MspecV_lift_le (fun t σ => by rw [MspecV_acquire t σ]; exact Effect.le_refl _)

/-- Lift bound for release: `L` provided the precondition guarantees the lock is
    held (`σ(l) = tid`) — the sync discipline threaded through the derivation. -/
theorem MspecV_release_le (P : Pred2)
    (hP : ∀ t σ σ0, P t σ0 σ → σ LOCK = (t : Value)) : MspecV.lift releaseL P ⊑ Effect.L := by
  apply sSup_le
  rintro e' ⟨t, σ, σ0, hPσ, rfl⟩
  rw [MspecV_release_held t σ (hP t σ σ0 hPσ)]; exact Effect.le_refl _

/-- A lock-protected `x`-access whose value reads only owned/`x` state is a
    lock-protected access (`IsXacc`), hence a **both-mover**.  This is the
    synchronization discipline on `x`, verified against the *valid* spec. -/
def xWrite (f : Store → Value) : Action :=
  fun t σ σ' => σ LOCK = (t : Value) ∧ σ' = upd σ XVAR (f σ)

theorem xWrite_isXacc {f : Store → Value} {t : Tid}
    (hf : ∀ σ1 σ2, (∀ v, (owns t v ∨ v = XVAR) → σ1 v = σ2 v) → f σ1 = f σ2) :
    IsXacc (xWrite f) t := by
  refine ⟨fun σ => upd σ XVAR (f σ), ⟨?_, ?_⟩, fun σ => upd_other σ XVAR (f σ) LOCK lock_ne_x,
    fun _ _ => Iff.rfl⟩
  · intro σ v hv; exact upd_other σ XVAR (f σ) v (fun he => hv (Or.inr he))
  · intro σ1 σ2 hag v hv
    rcases hv with hv | hv
    · rw [upd_other _ _ _ _ (owns_ne_x hv), upd_other _ _ _ _ (owns_ne_x hv), hag v (Or.inl hv)]
    · subst hv; rw [upd_same, upd_same, hf σ1 σ2 hag]

/-! ### An unconditional whole-state verification against the valid spec

`M-action` requires a both/left-mover to be *total* (the "left-mover terminates"
condition).  Acquire is a right-mover, so it needs no totality — a lock *acquire*
may block.  We verify a two-thread state that acquires the lock, showing
**`StateValid MspecV D Σ` outright — plugging in `MspecV_valid`, with no validity
hypothesis** (a faithful `release`/`x`-write version needs the store-dependent
variant of `MspecV` discussed in the README). -/

/-- The always-true predicate, used as a trivial rely/guarantee here. -/
def topP : Pred2 := fun _ _ _ => True
/-- The empty declaration table. -/
def emptyD : Decls := fun _ => none

/-- Each thread: `yield; acquire; release; yield` — a full lock round-trip.  The
    total release is a left-mover here because the precondition after the acquire
    guarantees the lock is held (`σ(l) = tid`), discharging `MspecV_release_le`. -/
def acqRelThread : Stmt := .seq .yield (.seq (.act acquireL) (.seq (.act releaseL) .yield))

theorem acqRelThread_verifies :
    ∃ Q, Judg MspecV emptyD topP topP acqRelThread topP Q
      (Effect.Y ;; (Effect.R ;; (Effect.L ;; Effect.Y))) := by
  -- after `acquire`, the lock is held — the sync discipline the release relies on
  have hP2 : ∀ t σ σ0, compPA (yieldP topP topP) acquireL t σ0 σ → σ LOCK = (t : Value) := by
    rintro t σ σ0 ⟨σ', _, hacq⟩; rw [hacq.2]; exact upd_same _ _ _
  exact ⟨_, Judg.seq (Judg.yield (fun _ _ _ _ => trivial) rfl)
    (Judg.seq (Judg.action (MspecV_acquire_le _) (fun h => absurd h (by decide)))
      (Judg.seq (Judg.action (MspecV_release_le _ hP2) (fun _ t σ => ⟨upd σ LOCK FREE, rfl⟩))
        (Judg.yield (fun _ _ _ _ => trivial) rfl)))⟩

/-- **`⊢ Σ` with no validity assumption.**  A two-thread lock **acquire/release**
    state verifies via `M-state`; the `Valid MspecV` premise is discharged by the
    proved `MspecV_valid`, not assumed.  The total release is used at effect `L` —
    exactly the fix. -/
theorem acqRel_state_valid :
    StateValid MspecV emptyD ⟨[acqRelThread, acqRelThread], fun _ => FREE⟩ := by
  obtain ⟨Q, hJ⟩ := acqRelThread_verifies
  refine ⟨topP, topP, ?_, MspecV_valid, ?_, ?_, ?_⟩
  · intro f spec body hf; simp [emptyD] at hf
  · intro _ _; trivial
  · intro t s hs
    have hsc : s = acqRelThread := by rcases t with _ | _ | t <;> simp_all
    subst hsc
    exact ⟨topP, Q, _, hJ, by decide, fun _ _ _ _ => trivial, ⟨.seqL .hole _, rfl⟩, trivial⟩
  · intro _ _ _ _ _ _; trivial

end ValidSpec
end MoverLogic
