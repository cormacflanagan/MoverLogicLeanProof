/-
  The Preservation theorem (paper Theorem thm:pres), fully mechanized —
  discharging the last remaining axiom of the soundness chain.

  The proof follows the paper's inversion stack:
    * **Yield Stabilization** (`yield_stable`) — a parked (yielding) thread's
      judgment is re-typed with the stabilized precondition `yield P R`,
      keeping its effect.  The `E[yield]` case rebuilds the `M-seq` spine at
      the *outer* rely/guarantee `R,G` (where `G` is reflexive), so the fresh
      `M-yield` instance's premise `P' ⟹ G` holds for the diagonal `P'`.
    * **Context Switch** (`ctxt_switch`) — an all-yielding valid state
      re-anchors at the current store with any thread as the active one;
      the outgoing active thread's yielding precondition is published to `G`
      and flows to every other thread's rely.
    * **Preservation for Redexes** — inlined in `preservation_active`, one
      case per instrumented step rule, each using the Evaluation Context
      lemma's canonical redex + rebuild.  The atomic-call case is where the
      **Prefix** lemma fires; the loop-unfolding case is where the
      upper-bound form of `M-while` (with `iter_seq_le` / `exit_le`) fires.
    * **Preservation** (`preservation`) — the assembly: if the stepping
      thread is not the active one, Context Switch activates it first.
-/
import MoverLogic.Instrumented
import MoverLogic.Prefix

namespace MoverLogic

open Effect

/-! ### Effect-lattice helpers -/

theorem eq_E_of_E_le {e : Effect} (h : Effect.E ⊑ e) : e = Effect.E := by
  revert h; cases e <;> decide

theorem ne_E_of_le {a b : Effect} (hab : a ⊑ b) (hb : b ≠ Effect.E) : a ≠ Effect.E :=
  fun ha => hb (eq_E_of_E_le (ha ▸ hab))

theorem ne_E_of_seq_left {a b : Effect} (h : a ;; b ≠ Effect.E) : a ≠ Effect.E :=
  fun ha => h (by rw [ha, seq_E_left])

theorem ne_E_of_seq_right {a b : Effect} (h : a ;; b ≠ Effect.E) : b ≠ Effect.E :=
  fun hb => h (by rw [hb, seq_E_right])

/-! ### `Rtc` and `yieldP` toolkit -/

theorem Rtc.single {R : Pred2} {t : Tid} {σ σ' : Store} (h : R t σ σ') : Rtc R t σ σ' :=
  .step h (.refl t σ')

theorem Rtc.trans' {R : Pred2} {t : Tid} {a b c : Store}
    (h1 : Rtc R t a b) (h2 : Rtc R t b c) : Rtc R t a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem Rtc.mono {R R' : Pred2} (hR : R ⟹ R') {t : Tid} {a b : Store}
    (h : Rtc R t a b) : Rtc R' t a b := by
  induction h with
  | refl => exact .refl _ _
  | step hs _ ih => exact .step (hR _ _ _ hs) ih

/-- `yield P R` holds diagonally at any store `R*`-reachable from a post-store of `P`. -/
theorem yieldP_intro {P R : Pred2} {t : Tid} {x y a : Store}
    (hp : P t x y) (hr : Rtc R t y a) : yieldP P R t a a :=
  ⟨rfl, x, y, hp, hr⟩

theorem yieldP_mono {P P' R R' : Pred2} (hP : P ⟹ P') (hR : R ⟹ R') :
    yieldP P R ⟹ yieldP P' R' := by
  rintro t a b ⟨rfl, x, y, hp, hr⟩
  exact ⟨rfl, x, y, hP _ _ _ hp, hr.mono hR⟩

/-- Stabilizing twice adds nothing: `yield (yield P R) R ⟹ yield P R`. -/
theorem yieldP_collapse {P R : Pred2} : yieldP (yieldP P R) R ⟹ yieldP P R := by
  rintro t a b ⟨rfl, x, y, ⟨heq, u, v, hp, hr1⟩, hr2⟩
  subst heq
  exact ⟨rfl, u, v, hp, hr1.trans' hr2⟩

/-- A stabilized (diagonal) precondition sits inside any reflexive guarantee. -/
theorem yieldP_imp_G {P R G : Pred2} (hrefl : ∀ t σ, G t σ σ) : yieldP P R ⟹ G := by
  rintro t a b ⟨rfl, _⟩
  exact hrefl t a

/-! ### Small inversion helpers -/

/-- A `skip` judgment's precondition implies its postcondition, and its effect
    dominates `B`. -/
theorem Judg.skip_inv {M : MoverSpec} {D : Decls} {R G P Q : Pred2} {e : Effect}
    (h : Judg M D R G .skip P Q e) : (P ⟹ Q) ∧ Effect.B ⊑ e := by
  obtain ⟨R1, G1, P1, Q1, e1, _, _, hP, hQ, he, hnc⟩ := h.consequence
  cases hnc with
  | skip => exact ⟨Implies2.trans hP hQ, he⟩

/-! ### Yield Stabilization (paper Lemma lem:yield-stable)

The `E[yield]` case rebuilds the sequential spine at the outer `R,G` — where
`G` is reflexive, so a fresh `M-yield` on the diagonal stabilized precondition
applies — rather than re-typing the redex at the inner (conseq-weakened)
rely/guarantee, whose guarantee need not be reflexive. -/

theorem yield_stable_ctx {M : MoverSpec} {D : Decls} :
    ∀ (E : Ctx) {R G P Q : Pred2} {e : Effect},
      Judg M D R G (E.plug .yield) P Q e →
      (∀ t σ, G t σ σ) →
      (P ⟹ G) ∧ ∃ Q', Judg M D R G (E.plug .yield) (yieldP P R) Q' e ∧ (Q' ⟹ Q) := by
  intro E
  induction E with
  | hole =>
      intro R G P Q e h hrefl
      obtain ⟨R1, G1, P1, Q1, e1, hR, hG, hP, hQ, he, hnc⟩ := h.consequence
      cases hnc with
      | yield hPG hQ1 =>
          refine ⟨fun t a b hp => hG t a b (hPG t a b (hP t a b hp)),
                  yieldP (yieldP P R) R, ?_, ?_⟩
          · exact Judg.conseq (Implies2.refl _) (Implies2.refl _) (Implies2.refl _)
              (Implies2.refl _) (Y_le e) (Judg.yield (yieldP_imp_G hrefl) rfl)
          · intro t a b hyy
            apply hQ
            rw [hQ1]
            exact yieldP_mono hP hR t a b (yieldP_collapse t a b hyy)
  | seqL E' s2 ih =>
      intro R G P Q e h hrefl
      obtain ⟨R1, G1, P1, Qm, Q1, e1, e2, hR, hG, hP, hQ, he, hbody, htail⟩ := h.inv_seq
      have hbody' : Judg M D R G (E'.plug .yield) P1 Qm e1 :=
        .conseq (Implies2.refl _) (Implies2.refl _) hR hG (le_refl _) hbody
      have htail' : Judg M D R G s2 Qm Q1 e2 :=
        .conseq (Implies2.refl _) (Implies2.refl _) hR hG (le_refl _) htail
      obtain ⟨hPG, Qm', hJ', hQm'⟩ := ih hbody' hrefl
      refine ⟨Implies2.trans hP hPG, Q1, ?_, hQ⟩
      have hJ'' : Judg M D R G (E'.plug .yield) (yieldP P R) Qm' e1 :=
        .conseq (yieldP_mono hP (Implies2.refl R)) (Implies2.refl _) (Implies2.refl _)
          (Implies2.refl _) (le_refl _) hJ'
      have htail'' : Judg M D R G s2 Qm' Q1 e2 :=
        .conseq hQm' (Implies2.refl _) (Implies2.refl _) (Implies2.refl _) (le_refl _) htail'
      exact .conseq (Implies2.refl _) (Implies2.refl _) (Implies2.refl _) (Implies2.refl _)
        he (.seq hJ'' htail'')

/-- **Yield Stabilization.**  A yielding statement's judgment is re-typed with
    the stabilized precondition `yield P R`, keeping the effect; the new
    postcondition still publishes to `G`, and `P` itself publishes to `G`. -/
theorem yield_stable {M : MoverSpec} {D : Decls} {R G : Pred2} {s : Stmt}
    {P Q : Pred2} {e : Effect}
    (hJ : Judg M D R G s P Q e) (hy : yielding s)
    (hrefl : ∀ t σ, G t σ σ) (hQG : Q ⟹ G) :
    (P ⟹ G) ∧ ∃ Q', Judg M D R G s (yieldP P R) Q' e ∧ (Q' ⟹ G) := by
  cases hy with
  | inl hEy =>
      obtain ⟨E, rfl⟩ := hEy
      obtain ⟨hPG, Q', hJ', hQ'⟩ := yield_stable_ctx E hJ hrefl
      exact ⟨hPG, Q', hJ', Implies2.trans hQ' hQG⟩
  | inr hskip =>
      subst hskip
      obtain ⟨hPQ, hBe⟩ := hJ.skip_inv
      refine ⟨Implies2.trans hPQ hQG, yieldP P R, ?_, yieldP_imp_G hrefl⟩
      exact .conseq (Implies2.refl _) (Implies2.refl _) (Implies2.refl _) (Implies2.refl _)
        hBe .skip

/-! ### Context Switch (paper Lemma lem:ctxt-switch)

An all-yielding thread pool re-anchors at the current store `σ` with any
thread `t` as the active one.  The old active thread `a`'s (yielding)
precondition is published to `G` and hence to every other thread's rely,
carrying each parked precondition from `σ₀` to `σ`; if `a` is out of range
the anchor gives `σ₀ = σ` directly. -/

theorem ctxt_switch {M : MoverSpec} {D : Decls} {R G : Pred2} {a : Tid} {σ0 : Store}
    {ths : List (Stmt × Phase)} {σ : Store} (t : Tid)
    (hrefl : ∀ u σ1, G u σ1 σ1)
    (hanchor : ths[a]? = none → σ0 = σ)
    (hthreads : ∀ u su pu, ths[u]? = some (su, pu) →
       ∃ P Q e, Judg M D R G su P Q e ∧ (pu ;; e ≠ Effect.E) ∧ (Q ⟹ G) ∧
         (if u = a then P u σ0 σ else yielding su ∧ ∃ σx, P u σx σ0))
    (hcompat : ∀ u v σ1 σ2, u ≠ v → G u σ1 σ2 → R v σ1 σ2)
    (hay : ∀ su pu, ths[a]? = some (su, pu) → yielding su) :
    ∀ u su pu, ths[u]? = some (su, pu) →
       ∃ P Q e, Judg M D R G su P Q e ∧ (pu ;; e ≠ Effect.E) ∧ (Q ⟹ G) ∧
         (if u = t then P u σ σ else yielding su ∧ ∃ σx, P u σx σ) := by
  -- the store moved from `σ0` to `σ` within every non-`a` thread's rely
  have hRtc : ∀ u, u ≠ a → Rtc R u σ0 σ := by
    intro u hua
    cases hpa : ths[a]? with
    | none => rw [hanchor hpa]; exact .refl _ _
    | some sp =>
        obtain ⟨sa, pa⟩ := sp
        obtain ⟨Pa, Qa, ea, hJa, _, hQGa, hbr⟩ := hthreads a sa pa hpa
        rw [if_pos rfl] at hbr
        have hPaG : Pa ⟹ G := (yield_stable hJa (hay sa pa hpa) hrefl hQGa).1
        exact Rtc.single (hcompat a u σ0 σ (Ne.symm hua) (hPaG a σ0 σ hbr))
  intro u su pu hget
  obtain ⟨P, Q, e, hJ, hne, hQG, hbr⟩ := hthreads u su pu hget
  have hyu : yielding su := by
    by_cases hua : u = a
    · exact hay su pu (hua ▸ hget)
    · rw [if_neg hua] at hbr; exact hbr.1
  obtain ⟨_, Q', hJ', hQ'G⟩ := yield_stable hJ hyu hrefl hQG
  have hdiag : yieldP P R u σ σ := by
    by_cases hua : u = a
    · subst hua; rw [if_pos rfl] at hbr; exact yieldP_intro hbr (.refl _ _)
    · rw [if_neg hua] at hbr
      obtain ⟨_, σx, hPx⟩ := hbr
      exact yieldP_intro hPx (hRtc u hua)
  refine ⟨yieldP P R, Q', e, hJ', hne, hQ'G, ?_⟩
  by_cases hut : u = t
  · rw [if_pos hut]; exact hdiag
  · rw [if_neg hut]; exact ⟨hyu, σ, hdiag⟩

/-! ### List-lookup bookkeeping for `List.set` -/

private theorem set_get_self {α} {l : List α} {i : Nat} {x : α} (h : i < l.length) :
    (l.set i x)[i]? = some x := by
  rw [List.getElem?_set_self]; simp [h]

private theorem set_get_ne {α} {l : List α} {i j : Nat} {x : α} (h : j ≠ i) :
    (l.set i x)[j]? = l[j]? := by
  rw [List.getElem?_set_ne (Ne.symm h)]

/-! ### Reassembling a valid state after the active thread steps -/

private theorem reassemble {M : MoverSpec} {D : Decls} {R G : Pred2} {t : Tid}
    {σ0' : Store} {ths : List (Stmt × Phase)} {σ' : Store} {s' : Stmt} {p' : Phase}
    (hfns : ∀ f spec body, D f = some (spec, body) → FnValid M D spec body)
    (hVal : Valid M)
    (hrefl : ∀ u σ1, G u σ1 σ1)
    (hcompat : ∀ u v σ1 σ2, u ≠ v → G u σ1 σ2 → R v σ1 σ2)
    (hlt : t < ths.length)
    (hold : ∀ u su pu, u ≠ t → ths[u]? = some (su, pu) →
       ∃ P Q e, Judg M D R G su P Q e ∧ (pu ;; e ≠ Effect.E) ∧ (Q ⟹ G) ∧
         yielding su ∧ ∃ σx, P u σx σ0')
    (hnew : ∃ P Q e, Judg M D R G s' P Q e ∧ (p' ;; e ≠ Effect.E) ∧ (Q ⟹ G) ∧ P t σ0' σ') :
    IStateValid M D ⟨ths.set t (s', p'), σ'⟩ := by
  obtain ⟨Pn, Qn, en, hJn, hnen, hQGn, hPn⟩ := hnew
  refine ⟨R, G, t, σ0', hfns, hVal, hrefl, ?_, ?_, hcompat⟩
  · intro h
    rw [show (⟨ths.set t (s', p'), σ'⟩ : IState).threads = ths.set t (s', p') from rfl,
        set_get_self hlt] at h
    exact absurd h (Option.some_ne_none _)
  · intro u su pu hget'
    by_cases hut : u = t
    · subst hut
      rw [show (⟨ths.set u (s', p'), σ'⟩ : IState).threads = ths.set u (s', p') from rfl,
          set_get_self hlt] at hget'
      obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj hget'
      subst h1; subst h2
      exact ⟨Pn, Qn, en, hJn, hnen, hQGn, by rw [if_pos rfl]; exact hPn⟩
    · rw [show (⟨ths.set t (s', p'), σ'⟩ : IState).threads = ths.set t (s', p') from rfl,
          set_get_ne hut] at hget'
      obtain ⟨P, Q, e, hJ, hne, hQG, hy, σx, hPx⟩ := hold u su pu hut hget'
      exact ⟨P, Q, e, hJ, hne, hQG, by rw [if_neg hut]; exact ⟨hy, σx, hPx⟩⟩

/-! ### Preservation for the active thread's step

One case per instrumented step rule — the paper's Preservation-for-Redexes,
fused with the Evaluation Context rebuild. -/

theorem preservation_active {M : MoverSpec} {D : Decls} {R G : Pred2} {t : Tid}
    {σ0 : Store} {ths : List (Stmt × Phase)} {σ : Store} {s s' : Stmt}
    {p p' : Phase} {σ' : Store}
    (hfns : ∀ f spec body, D f = some (spec, body) → FnValid M D spec body)
    (hVal : Valid M)
    (hrefl : ∀ u σ1, G u σ1 σ1)
    (hthreads : ∀ u su pu, ths[u]? = some (su, pu) →
       ∃ P Q e, Judg M D R G su P Q e ∧ (pu ;; e ≠ Effect.E) ∧ (Q ⟹ G) ∧
         (if u = t then P u σ0 σ else yielding su ∧ ∃ σx, P u σx σ0))
    (hcompat : ∀ u v σ1 σ2, u ≠ v → G u σ1 σ2 → R v σ1 σ2)
    (hget : ths[t]? = some (s, p))
    (hstep : IThreadStep M D.bodies t s σ p s' σ' p') :
    IStateValid M D ⟨ths.set t (s', p'), σ'⟩ := by
  obtain ⟨P, Q, e, hJ, hne, hQG, hbr⟩ := hthreads t s p hget
  rw [if_pos rfl] at hbr
  have hlt : t < ths.length := (List.getElem?_eq_some_iff.1 hget).1
  -- the untouched threads, for every case that keeps `σ0`
  have hold : ∀ u su pu, u ≠ t → ths[u]? = some (su, pu) →
      ∃ P Q e, Judg M D R G su P Q e ∧ (pu ;; e ≠ Effect.E) ∧ (Q ⟹ G) ∧
        yielding su ∧ ∃ σx, P u σx σ0 := by
    intro u su pu hut hg
    obtain ⟨P', Q', e', hJ', hne', hQG', hbr'⟩ := hthreads u su pu hg
    rw [if_neg hut] at hbr'
    exact ⟨P', Q', e', hJ', hne', hQG', hbr'.1, hbr'.2⟩
  cases hstep with
  | iseq E s2 σx px =>
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, hrebuild⟩ := hJ.eval_ctxt E
      cases hnc with
      | seq h1 h2 =>
          rename_i Qm es et
          obtain ⟨hP1Qm, hBes⟩ := h1.skip_inv
          refine reassemble hfns hVal hrefl hcompat hlt hold
            ⟨Qm, Q, et ;; eE, hrebuild s2 Qm et h2, ?_, hQG,
             hP1Qm _ _ _ (hP _ _ _ hbr)⟩
          have hle : et ;; eE ⊑ e := by
            calc et ;; eE = (Effect.B ;; et) ;; eE := by rw [seq_B_left]
              _ ⊑ (es ;; et) ;; eE := seq_mono (seq_mono hBes (le_refl _)) (le_refl _)
              _ ⊑ e := heE
          exact ne_E_of_le (seq_mono (le_refl p) hle) hne
  | iyield E σx px =>
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, hrebuild⟩ := hJ.eval_ctxt E
      cases hnc with
      | yield hPG hQ1 =>
          -- publication: the transaction σ0 → σ enters G, hence others' relies
          have hGpub : G t σ0 σ := hG _ _ _ (hPG _ _ _ (hP _ _ _ hbr))
          have heEne : eE ≠ Effect.E :=
            ne_E_of_seq_right (ne_E_of_le heE (ne_E_of_seq_right hne))
          refine reassemble (σ0' := σ) hfns hVal hrefl hcompat hlt ?_
            ⟨Q1, Q, Effect.B ;; eE, hrebuild .skip Q1 Effect.B .skip, ?_, hQG, ?_⟩
          · -- other threads: stabilize at the new sequence-initial store σ
            intro u su pu hut hg
            obtain ⟨P', Q', e', hJ', hne', hQG', hbr'⟩ := hthreads u su pu hg
            rw [if_neg hut] at hbr'
            obtain ⟨hyu, σx, hPx⟩ := hbr'
            obtain ⟨_, Q'', hJ'', hQ''G⟩ := yield_stable hJ' hyu hrefl hQG'
            exact ⟨yieldP P' R, Q'', e', hJ'', hne', hQ''G, hyu, σ,
              yieldP_intro hPx (Rtc.single (hcompat t u σ0 σ (Ne.symm hut) hGpub))⟩
          · rw [seq_B_left]; exact R_seq_ne_E heEne
          · rw [hQ1]; exact yieldP_intro (hP _ _ _ hbr) (.refl _ _)
  | iwhile E C sb σx px =>
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, hrebuild⟩ := hJ.eval_ctxt E
      cases hnc with
      | wloop h1 hiter he hnl =>
          rename_i eb
          -- rebuild the unfolded conditional at the canonical level
          have hwhile : Judg M D R1 G1 (.while C sb) P1 (compPA P1 C.fls) e1 :=
            .wloop h1 hiter he hnl
          have hite : Judg M D R1 G1 (.ite C (.seq sb (.while C sb)) .skip) P1
              (compPA P1 C.fls) e1 := by
            refine .ite (.seq h1 hwhile) .skip ?_
            apply join_le
            · rw [← seq_assoc]; exact iter_seq_le hiter hnl
            · rw [seq_B_right]; exact exit_le hiter he hnl
          refine reassemble hfns hVal hrefl hcompat hlt hold
            ⟨P1, Q, e1 ;; eE, hrebuild _ P1 e1 hite, ?_, hQG, hP _ _ _ hbr⟩
          exact ne_E_of_le (seq_mono (le_refl p) heE) hne
  | icall E f sb σx px hDf =>
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, hrebuild⟩ := hJ.eval_ctxt E
      cases hnc with
      | callAtomic hd hpre =>
          rename_i S Qs body
          -- the stepped body is the declared body
          have hsb : sb = body := by
            have h2 : D.bodies f = some body := by
              unfold Decls.bodies; rw [hd]; rfl
            exact Option.some.inj (hDf.symm.trans h2)
          subst hsb
          -- inline the body via Prefix
          have hbodyJ : Judg M D botP botP sb (two S) Qs e1 := hfns f _ sb hd
          have hpref : Judg M D R1 G1 sb (compP2 P1 (two S)) (compP2 P1 Qs) e1 :=
            Judg.prefix P1 R1 G1 hfns hbodyJ
          refine reassemble hfns hVal hrefl hcompat hlt hold
            ⟨compP2 P1 (two S), Q, e1 ;; eE, hrebuild sb (compP2 P1 (two S)) e1 hpref,
             ?_, hQG, ⟨σ, hP _ _ _ hbr, rfl, hpre t σ ⟨σ0, hP _ _ _ hbr⟩⟩⟩
          exact ne_E_of_le (seq_mono (le_refl p) heE) hne
      | callNonAtomic hd =>
          rename_i S T body
          have hsb : sb = body := by
            have h2 : D.bodies f = some body := by
              unfold Decls.bodies; rw [hd]; rfl
            exact Option.some.inj (hDf.symm.trans h2)
          subst hsb
          obtain ⟨hbodyJ, _⟩ := hfns f _ sb hd
          refine reassemble hfns hVal hrefl hcompat hlt hold
            ⟨two S, Q, Effect.R ;; eE, hrebuild sb (two S) Effect.R hbodyJ,
             ?_, hQG, hP _ _ _ hbr⟩
          exact ne_E_of_le (seq_mono (le_refl p) heE) hne
  | iaction_ok E A σx σ2 px hA hneM =>
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, hrebuild⟩ := hJ.eval_ctxt E
      cases hnc with
      | action he htot =>
          have hM : M A t σ ⊑ e1 := le_trans (M.le_lift A P1 (hP _ _ _ hbr)) he
          refine reassemble hfns hVal hrefl hcompat hlt hold
            ⟨compPA P1 A, Q, Effect.B ;; eE, hrebuild .skip (compPA P1 A) Effect.B .skip,
             ?_, hQG, ⟨σ, hP _ _ _ hbr, hA⟩⟩
          rw [seq_B_left]
          have hle : (p ;; M A t σ) ;; eE ⊑ p ;; e := by
            calc (p ;; M A t σ) ;; eE ⊑ (p ;; e1) ;; eE :=
                  seq_mono (seq_mono (le_refl p) hM) (le_refl _)
              _ = p ;; (e1 ;; eE) := seq_assoc _ _ _
              _ ⊑ p ;; e := seq_mono (le_refl p) heE
          exact ne_E_of_le hle hne
  | iaction_wrong E A σx px hpE =>
      exfalso
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, _⟩ := hJ.eval_ctxt E
      cases hnc with
      | action he htot =>
          have hM : M A t σ ⊑ e1 := le_trans (M.le_lift A P1 (hP _ _ _ hbr)) he
          have hle : (p ;; M A t σ) ;; eE ⊑ p ;; e := by
            calc (p ;; M A t σ) ;; eE ⊑ (p ;; e1) ;; eE :=
                  seq_mono (seq_mono (le_refl p) hM) (le_refl _)
              _ = p ;; (e1 ;; eE) := seq_assoc _ _ _
              _ ⊑ p ;; e := seq_mono (le_refl p) heE
          rw [hpE, seq_E_left] at hle
          exact hne (eq_E_of_E_le hle)
  | iif_ok_T E C s1 s2 σx σ2 px hA hneM =>
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, hrebuild⟩ := hJ.eval_ctxt E
      cases hnc with
      | ite h1 h2 he =>
          rename_i ea eb
          have hM : M C.tru t σ ;; ea ⊑ e1 :=
            le_trans (seq_mono (M.le_lift C.tru P1 (hP _ _ _ hbr)) (le_refl _))
              (le_trans (le_join_left _ _) he)
          refine reassemble hfns hVal hrefl hcompat hlt hold
            ⟨compPA P1 C.tru, Q, ea ;; eE, hrebuild s1 (compPA P1 C.tru) ea h1,
             ?_, hQG, ⟨σ, hP _ _ _ hbr, hA⟩⟩
          have hle : (p ;; M C.tru t σ) ;; (ea ;; eE) ⊑ p ;; e := by
            calc (p ;; M C.tru t σ) ;; (ea ;; eE)
                = p ;; ((M C.tru t σ ;; ea) ;; eE) := by
                  rw [seq_assoc, seq_assoc]
              _ ⊑ p ;; (e1 ;; eE) := seq_mono (le_refl p) (seq_mono hM (le_refl _))
              _ ⊑ p ;; e := seq_mono (le_refl p) heE
          exact ne_E_of_le hle hne
  | iif_ok_F E C s1 s2 σx σ2 px hA hneM =>
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, hrebuild⟩ := hJ.eval_ctxt E
      cases hnc with
      | ite h1 h2 he =>
          rename_i ea eb
          have hM : M C.fls t σ ;; eb ⊑ e1 :=
            le_trans (seq_mono (M.le_lift C.fls P1 (hP _ _ _ hbr)) (le_refl _))
              (le_trans (le_join_right _ _) he)
          refine reassemble hfns hVal hrefl hcompat hlt hold
            ⟨compPA P1 C.fls, Q, eb ;; eE, hrebuild s2 (compPA P1 C.fls) eb h2,
             ?_, hQG, ⟨σ, hP _ _ _ hbr, hA⟩⟩
          have hle : (p ;; M C.fls t σ) ;; (eb ;; eE) ⊑ p ;; e := by
            calc (p ;; M C.fls t σ) ;; (eb ;; eE)
                = p ;; ((M C.fls t σ ;; eb) ;; eE) := by
                  rw [seq_assoc, seq_assoc]
              _ ⊑ p ;; (e1 ;; eE) := seq_mono (le_refl p) (seq_mono hM (le_refl _))
              _ ⊑ p ;; e := seq_mono (le_refl p) heE
          exact ne_E_of_le hle hne
  | iif_wrong_T E C s1 s2 σx σ2 px hA hpE =>
      exfalso
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, _⟩ := hJ.eval_ctxt E
      cases hnc with
      | ite h1 h2 he =>
          rename_i ea eb
          have hM : M C.tru t σ ;; ea ⊑ e1 :=
            le_trans (seq_mono (M.le_lift C.tru P1 (hP _ _ _ hbr)) (le_refl _))
              (le_trans (le_join_left _ _) he)
          have hle : ((p ;; M C.tru t σ) ;; ea) ;; eE ⊑ p ;; e := by
            calc ((p ;; M C.tru t σ) ;; ea) ;; eE
                = p ;; ((M C.tru t σ ;; ea) ;; eE) := by
                  simp only [Effect.seq_assoc]
              _ ⊑ p ;; (e1 ;; eE) := seq_mono (le_refl p) (seq_mono hM (le_refl _))
              _ ⊑ p ;; e := seq_mono (le_refl p) heE
          rw [hpE, seq_E_left, seq_E_left] at hle
          exact hne (eq_E_of_E_le hle)
  | iif_wrong_F E C s1 s2 σx σ2 px hA hpE =>
      exfalso
      obtain ⟨R1, G1, P1, Q1, e1, eE, hR, hG, hP, heE, hnc, _⟩ := hJ.eval_ctxt E
      cases hnc with
      | ite h1 h2 he =>
          rename_i ea eb
          have hM : M C.fls t σ ;; eb ⊑ e1 :=
            le_trans (seq_mono (M.le_lift C.fls P1 (hP _ _ _ hbr)) (le_refl _))
              (le_trans (le_join_right _ _) he)
          have hle : ((p ;; M C.fls t σ) ;; eb) ;; eE ⊑ p ;; e := by
            calc ((p ;; M C.fls t σ) ;; eb) ;; eE
                = p ;; ((M C.fls t σ ;; eb) ;; eE) := by
                  simp only [Effect.seq_assoc]
              _ ⊑ p ;; (e1 ;; eE) := seq_mono (le_refl p) (seq_mono hM (le_refl _))
              _ ⊑ p ;; e := seq_mono (le_refl p) heE
          rw [hpE, seq_E_left, seq_E_left] at hle
          exact hne (eq_E_of_E_le hle)

/-! ### Preservation (Theorem thm:pres) -/

/-- **Preservation.**  Verification is preserved by a single non-preemptive
    instrumented step.  Previously an axiom; now fully proved. -/
theorem preservation {M : MoverSpec} {D : Decls} {Pi Pi' : IState}
    (hval : IStateValid M D Pi) (hstep : INonStep M D.bodies Pi Pi') :
    IStateValid M D Pi' := by
  obtain ⟨ths, t, s, s', σ, σ', p, p', hget, htstep, hy⟩ := hstep
  obtain ⟨R, G, a, σ0, hfns, hVal, hrefl, hanchor, hthreads, hcompat⟩ := hval
  by_cases hta : t = a
  · subst hta
    exact preservation_active hfns hVal hrefl hthreads hcompat hget htstep
  · -- the stepping thread is not the active one: all threads are yielding
    -- (the active one by the scheduler's premise, the rest by validity), so
    -- Context Switch re-anchors the state with `t` active at the current store
    have hay : ∀ su pu, ths[a]? = some (su, pu) → yielding su :=
      fun su pu hg => hy a su pu (fun h => hta h.symm) hg
    have hthreads' := ctxt_switch t hrefl hanchor hthreads hcompat hay
    exact preservation_active hfns hVal hrefl hthreads' hcompat hget htstep

/-- Preservation lifted along `↦*`. -/
theorem preservation_star {M : MoverSpec} {D : Decls} {Pi Pi' : IState}
    (hs : INonSteps M D.bodies Pi Pi') : IStateValid M D Pi → IStateValid M D Pi' := by
  induction hs with
  | refl => exact fun h => h
  | step hstep _ ih => exact fun h => ih (preservation h hstep)

end MoverLogic
