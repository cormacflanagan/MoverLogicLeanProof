/-
  Canonical form and inversion for the mover-logic judgment.

  Toward mechanizing the Preservation theorem, this file provides:
    * `JudgNC` — derivations whose *last* rule is not `M-conseq`;
    * `Judg.consequence` — the paper's Consequence lemma: every derivation is a
      `JudgNC` derivation up to weakening of `R, G, P, Q, e`;
    * per-rule inversion lemmas obtained by `cases` on the canonical form;
    * the `Prefix` and `Evaluation Context` lemmas.
  Depends only on `Logic` (pure proof-theory; no operational semantics).
-/
import MoverLogic.Logic

namespace MoverLogic

open Effect

/-- `Implies2` is reflexive and transitive (a preorder on two-store predicates). -/
theorem Implies2.refl (P : Pred2) : P ⟹ P := fun _ _ _ h => h
theorem Implies2.trans {P Q S : Pred2} (h1 : P ⟹ Q) (h2 : Q ⟹ S) : P ⟹ S :=
  fun t σ σ' h => h2 t σ σ' (h1 t σ σ' h)

/-! ### Canonical (non-`M-conseq`) derivations

`JudgNC R G s P Q e` holds exactly when `Judg R G s P Q e` is derivable by a rule
other than `M-conseq` at the root (its sub-derivations may still use `M-conseq`,
so premises refer to the full `Judg`). -/

inductive JudgNC (M : MoverSpec) (D : Decls) :
    Pred2 → Pred2 → Stmt → Pred2 → Pred2 → Effect → Prop where
  | action {R G : Pred2} {A : Action} {P : Pred2} {e : Effect}
      (he : M.lift A P ⊑ e) (htot : e ⊑ Effect.L → Total A) :
      JudgNC M D R G (.act A) P (compPA P A) e
  | seq {R G P Q1 Q2 : Pred2} {s1 s2 : Stmt} {e1 e2 : Effect}
      (h1 : Judg M D R G s1 P Q1 e1) (h2 : Judg M D R G s2 Q1 Q2 e2) :
      JudgNC M D R G (.seq s1 s2) P Q2 (e1 ;; e2)
  | ite {R G P Q : Pred2} {C : CondAction} {s1 s2 : Stmt} {e e1 e2 : Effect}
      (h1 : Judg M D R G s1 (compPA P C.tru) Q e1)
      (h2 : Judg M D R G s2 (compPA P C.fls) Q e2)
      (he : (M.lift C.tru P ;; e1) ⊔ (M.lift C.fls P ;; e2) ⊑ e) :
      JudgNC M D R G (.ite C s1 s2) P Q e
  | wloop {R G P : Pred2} {C : CondAction} {s : Stmt} {e e1 : Effect}
      (h1 : Judg M D R G s (compPA P C.tru) P e1)
      (hiter : M.lift C.tru P ;; e1 ⊑ Effect.R)
      (he : ((M.lift C.tru P ;; e1)^* ;; M.lift C.fls P) ⊑ e)
      (hnl : ¬ (e ⊑ Effect.L)) :
      JudgNC M D R G (.while C s) P (compPA P C.fls) e
  | skip {R G P : Pred2} : JudgNC M D R G .skip P P Effect.B
  | wrong {R G : Pred2} : JudgNC M D R G .wrong botP botP Effect.B
  | yield {R G P Q : Pred2}
      (hG : P ⟹ G) (hQ : Q = yieldP P R) :
      JudgNC M D R G .yield P Q Effect.Y
  | callAtomic {R G P : Pred2} {f : FnName} {e : Effect} {S : Pred1} {Q : Pred2} {body : Stmt}
      (hd : D f = some (.atomic e S Q, body)) (hpre : post P ⟹₁ S) :
      JudgNC M D R G (.call f) P (compPA P (fun t σ σ' => Q t σ σ')) e
  | callNonAtomic {R G : Pred2} {f : FnName} {S T : Pred1} {body : Stmt}
      (hd : D f = some (.nonatomic R G S T, body)) :
      JudgNC M D R G (.call f) (two S) (two T) Effect.R

/-- A canonical derivation is in particular a derivation. -/
theorem JudgNC.toJudg {M D R G s P Q e} (h : JudgNC M D R G s P Q e) :
    Judg M D R G s P Q e := by
  cases h with
  | action he htot => exact .action he htot
  | seq h1 h2 => exact .seq h1 h2
  | ite h1 h2 he => exact .ite h1 h2 he
  | wloop h1 hiter he hnl => exact .wloop h1 hiter he hnl
  | skip => exact .skip
  | wrong => exact .wrong
  | yield hG hQ => exact .yield hG hQ
  | callAtomic hd hpre => exact .callAtomic hd hpre
  | callNonAtomic hd => exact .callNonAtomic hd

/-- **Consequence lemma.** Every derivation equals a canonical (non-`M-conseq`)
    derivation up to weakening `P ⟹ P₁`, `R ⟹ R₁`, `G₁ ⟹ G`, `Q₁ ⟹ Q`,
    `e₁ ⊑ e`. -/
theorem Judg.consequence {M D R G s P Q e} (h : Judg M D R G s P Q e) :
    ∃ R1 G1 P1 Q1 e1, (R ⟹ R1) ∧ (G1 ⟹ G) ∧ (P ⟹ P1) ∧ (Q1 ⟹ Q) ∧ (e1 ⊑ e) ∧
      JudgNC M D R1 G1 s P1 Q1 e1 := by
  induction h with
  | @action R G A P e he htot =>
      exact ⟨R, G, P, compPA P A, e, Implies2.refl _, Implies2.refl _, Implies2.refl _,
        Implies2.refl _, le_refl _, .action he htot⟩
  | @seq R G P Q1 Q2 s1 s2 e1 e2 h1 h2 _ _ =>
      exact ⟨R, G, P, Q2, e1 ;; e2, Implies2.refl _, Implies2.refl _, Implies2.refl _,
        Implies2.refl _, le_refl _, .seq h1 h2⟩
  | @ite R G P Q C s1 s2 e e1 e2 h1 h2 he _ _ =>
      exact ⟨R, G, P, Q, e, Implies2.refl _, Implies2.refl _, Implies2.refl _,
        Implies2.refl _, le_refl _, .ite h1 h2 he⟩
  | @wloop R G P C s e e1 h1 hiter he hnl _ =>
      exact ⟨R, G, P, compPA P C.fls, e, Implies2.refl _, Implies2.refl _, Implies2.refl _,
        Implies2.refl _, le_refl _, .wloop h1 hiter he hnl⟩
  | @skip R G P =>
      exact ⟨R, G, P, P, Effect.B, Implies2.refl _, Implies2.refl _, Implies2.refl _,
        Implies2.refl _, le_refl _, .skip⟩
  | @wrong R G =>
      exact ⟨R, G, botP, botP, Effect.B, Implies2.refl _, Implies2.refl _, Implies2.refl _,
        Implies2.refl _, le_refl _, .wrong⟩
  | @yield R G P Q hG hQ =>
      exact ⟨R, G, P, Q, Effect.Y, Implies2.refl _, Implies2.refl _, Implies2.refl _,
        Implies2.refl _, le_refl _, .yield hG hQ⟩
  | @callAtomic R G P f e S Q body hd hpre =>
      exact ⟨R, G, P, _, e, Implies2.refl _, Implies2.refl _, Implies2.refl _,
        Implies2.refl _, le_refl _, .callAtomic hd hpre⟩
  | @callNonAtomic R G f S T body hd =>
      exact ⟨R, G, two S, two T, Effect.R, Implies2.refl _, Implies2.refl _, Implies2.refl _,
        Implies2.refl _, le_refl _, .callNonAtomic hd⟩
  | @conseq R G R1 G1 P P1 Q1 Q s e1 e hP hQ hR hG he _ ih =>
      obtain ⟨R2, G2, P2, Q2, e2, hR2, hG2, hP2, hQ2, he2, hnc⟩ := ih
      exact ⟨R2, G2, P2, Q2, e2,
        Implies2.trans hR hR2, Implies2.trans hG2 hG, Implies2.trans hP hP2,
        Implies2.trans hQ2 hQ, le_trans he2 he, hnc⟩

/-! ### Inversion for sequential composition (from canonical form) -/

/-- **M-seq inversion.** A derivation of `s₁; s₂` decomposes (up to weakening)
    into derivations of `s₁` and `s₂` sharing an intermediate assertion. -/
theorem Judg.inv_seq {M D R G s1 s2 P Q e} (h : Judg M D R G (.seq s1 s2) P Q e) :
    ∃ R1 G1 P1 Qm Q1 e1 e2,
      (R ⟹ R1) ∧ (G1 ⟹ G) ∧ (P ⟹ P1) ∧ (Q1 ⟹ Q) ∧ (e1 ;; e2 ⊑ e) ∧
      Judg M D R1 G1 s1 P1 Qm e1 ∧ Judg M D R1 G1 s2 Qm Q1 e2 := by
  obtain ⟨R1, G1, P1, Q1, e1, hR, hG, hP, hQ, he, hnc⟩ := h.consequence
  cases hnc with
  | seq h1 h2 => exact ⟨R1, G1, P1, _, Q1, _, _, hR, hG, hP, hQ, he, h1, h2⟩

/-! ### The Evaluation Context lemma

Decompose a derivation of `E[s]` into a canonical derivation of the redex `s`
plus a "context effect" `e_E`, together with a way to rebuild the context
around any replacement redex `s'`. -/

theorem Judg.eval_ctxt {M D R G} (E : Ctx) {s P Q e}
    (h : Judg M D R G (E.plug s) P Q e) :
    ∃ R1 G1 P1 Q1 e1 eE,
      (R ⟹ R1) ∧ (G1 ⟹ G) ∧ (P ⟹ P1) ∧ (e1 ;; eE ⊑ e) ∧
      JudgNC M D R1 G1 s P1 Q1 e1 ∧
      (∀ s' P' e1', Judg M D R1 G1 s' P' Q1 e1' →
        Judg M D R G (E.plug s') P' Q (e1' ;; eE)) := by
  induction E generalizing R G P Q e with
  | hole =>
      obtain ⟨R1, G1, P1, Q1, e1, hR, hG, hP, hQ, he, hnc⟩ := h.consequence
      refine ⟨R1, G1, P1, Q1, e1, Effect.B, hR, hG, hP, ?_, hnc, ?_⟩
      · rw [seq_B_right]; exact he
      · intro s' P' e1' h'
        rw [seq_B_right]
        exact .conseq (Implies2.refl P') hQ hR hG (le_refl e1') h'
  | seqL E' s2 ih =>
      -- E.plug s = (E'.plug s) ; s2
      obtain ⟨R1, G1, P1, Qm, Q1, e1, e2, hR, hG, hP, hQ, he, hbody, htail⟩ := h.inv_seq
      obtain ⟨R2, G2, P2, Qm2, e2', eE', hR2, hG2, hP2, he', hnc, hfar⟩ := ih hbody
      refine ⟨R2, G2, P2, Qm2, e2', eE' ;; e2,
        Implies2.trans hR hR2, Implies2.trans hG2 hG, Implies2.trans hP hP2, ?_, hnc, ?_⟩
      · -- e2' ;; (eE' ;; e2) ⊑ e
        have h1 : e2' ;; (eE' ;; e2) = (e2' ;; eE') ;; e2 := (seq_assoc _ _ _).symm
        rw [h1]
        exact le_trans (seq_mono he' (le_refl e2)) he
      · intro s' P' e1' h'
        -- rebuild:  (E'.plug s') ; s2
        have hstep : Judg M D R1 G1 (E'.plug s') P' Qm (e1' ;; eE') := hfar s' P' e1' h'
        have hseq : Judg M D R1 G1 (.seq (E'.plug s') s2) P' Q1 ((e1' ;; eE') ;; e2) :=
          .seq hstep htail
        have hfull : Judg M D R G (.seq (E'.plug s') s2) P' Q ((e1' ;; eE') ;; e2) :=
          .conseq (Implies2.refl P') hQ hR hG (le_refl _) hseq
        -- reassociate the effect and re-fold the context
        rw [Ctx.plug]
        rw [show e1' ;; (eE' ;; e2) = (e1' ;; eE') ;; e2 from (seq_assoc _ _ _).symm]
        exact hfull

end MoverLogic
