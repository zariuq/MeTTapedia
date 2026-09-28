import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingPointed

/-!
# Typing of the pointed compiler in the selected judgment

An equality-proof algebra is *lawful* for a reading when each operation, on
typed premises, returns a term of the selected typed judgment of the reading's
package at the decoding of the expected equation code (`EqualityRaw.Lawful`,
`PointedRaw.Lawful`). The premises are typed judgments, and reflexivity at a
point takes typed equality of its endpoints, `Equal ρ.rules Γ l r (carrier τ)`:
this is the premise that sees β and η, which untyped conversion of the
formation-sensitive judgment does not.

* `TypedOperations ρ` is the typed analogue of the legacy `Operations`: an
  algebra with its laws. `PointedOperations ρ` adds reflexivity at a point.
  The forgetful map `PointedOperations.forget` and the embedding
  `TypedOperations.pointedByConstant` compose to the identity
  (`pointedByConstant_forget`), and a proof without reflexivity nodes compiles
  the same way under an algebra and under the embedding of its forgetful image
  (`PointedOperations.compileP_forget`).
* **Typing** (`Laws.compileP_typedO`): under a lawful algebra, a compiled proof
  is typed in the selected judgment at the decoding of the code of its
  conclusion, in every typed environment whose hypotheses are typed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization
open Mettapedia.Logic

universe u v

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-! ## The laws -/

/-- Each operation of the algebra is certified in the selected judgment of the
reading's package: on typed premises it returns a term of the decoding of the
expected code. -/
structure EqualityRaw.Lawful (ρ : HOLReading Head Base Const) (raw : EqualityRaw Head Base) :
    Prop where
  reflexivity : ∀ {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {l r out : Tm Head n},
    raw.reflexivity = some out →
    Typed ρ.rules Γ l (ρ.carrierAt n τ) → Typed ρ.rules Γ r (ρ.carrierAt n τ) →
    Equal ρ.rules Γ l r (ρ.carrierAt n τ) →
    Typed ρ.rules Γ out (ρ.holdsOf (ρ.eqOf τ l r))
  symmetry : ∀ {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {l r e out : Tm Head n},
    raw.symmetry τ l r e = some out →
    Typed ρ.rules Γ l (ρ.carrierAt n τ) → Typed ρ.rules Γ r (ρ.carrierAt n τ) →
    Typed ρ.rules Γ e (ρ.holdsOf (ρ.eqOf τ l r)) →
    Typed ρ.rules Γ out (ρ.holdsOf (ρ.eqOf τ r l))
  transitivity : ∀ {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {l m r e₁ e₂ out : Tm Head n},
    raw.transitivity τ l m r e₁ e₂ = some out →
    Typed ρ.rules Γ l (ρ.carrierAt n τ) → Typed ρ.rules Γ m (ρ.carrierAt n τ) →
    Typed ρ.rules Γ r (ρ.carrierAt n τ) →
    Typed ρ.rules Γ e₁ (ρ.holdsOf (ρ.eqOf τ l m)) → Typed ρ.rules Γ e₂ (ρ.holdsOf (ρ.eqOf τ m r)) →
    Typed ρ.rules Γ out (ρ.holdsOf (ρ.eqOf τ l r))
  propositionExtensionality : ∀ {n : Nat} {Γ : Ctx Head n} {p q f b out : Tm Head n},
    raw.propositionExtensionality p q f b = some out →
    Typed ρ.rules Γ p ρ.codes.propT → Typed ρ.rules Γ q ρ.codes.propT →
    Typed ρ.rules Γ f (ρ.holdsOf (ρ.impOf p q)) → Typed ρ.rules Γ b (ρ.holdsOf (ρ.impOf q p)) →
    Typed ρ.rules Γ out (ρ.holdsOf (ρ.eqOf .prop p q))
  propositionForward : ∀ {n : Nat} {Γ : Ctx Head n} {p q e out : Tm Head n},
    raw.propositionForward p q e = some out →
    Typed ρ.rules Γ p ρ.codes.propT → Typed ρ.rules Γ q ρ.codes.propT →
    Typed ρ.rules Γ e (ρ.holdsOf (ρ.eqOf .prop p q)) →
    Typed ρ.rules Γ out (ρ.holdsOf (ρ.impOf p q))
  functionCongruence : ∀ {n : Nat} {Γ : Ctx Head n} {σ τ : HOL.Ty Base} {f g a e out : Tm Head n},
    raw.functionCongruence σ τ f g a e = some out →
    Typed ρ.rules Γ f (ρ.carrierAt n (.arr σ τ)) → Typed ρ.rules Γ g (ρ.carrierAt n (.arr σ τ)) →
    Typed ρ.rules Γ a (ρ.carrierAt n σ) →
    Typed ρ.rules Γ e (ρ.holdsOf (ρ.eqOf (.arr σ τ) f g)) →
    Typed ρ.rules Γ out (ρ.holdsOf (ρ.eqOf τ (.app f a) (.app g a)))
  argumentCongruence : ∀ {n : Nat} {Γ : Ctx Head n} {σ τ : HOL.Ty Base} {f l r e out : Tm Head n},
    raw.argumentCongruence σ τ f l r e = some out →
    Typed ρ.rules Γ f (ρ.carrierAt n (.arr σ τ)) →
    Typed ρ.rules Γ l (ρ.carrierAt n σ) → Typed ρ.rules Γ r (ρ.carrierAt n σ) →
    Typed ρ.rules Γ e (ρ.holdsOf (ρ.eqOf σ l r)) →
    Typed ρ.rules Γ out (ρ.holdsOf (ρ.eqOf τ (.app f l) (.app f r)))
  functionExtensionality : ∀ {n : Nat} {Γ : Ctx Head n} {σ τ : HOL.Ty Base}
      {f g pw out : Tm Head n},
    raw.functionExtensionality σ τ f g pw = some out →
    Typed ρ.rules Γ f (ρ.carrierAt n (.arr σ τ)) → Typed ρ.rules Γ g (ρ.carrierAt n (.arr σ τ)) →
    Typed ρ.rules Γ pw (ρ.holdsOf (ρ.allOf σ (.lam (ρ.eqOf τ
      (.app (Presentation.rename wk f) (.var 0)) (.app (Presentation.rename wk g) (.var 0)))))) →
    Typed ρ.rules Γ out (ρ.holdsOf (ρ.eqOf (.arr σ τ) f g))

/-- The laws of an algebra with reflexivity at a point: reflexivity at `l`
proves `l = r` for every `r` typed-equal to `l`. -/
structure PointedRaw.Lawful (ρ : HOLReading Head Base Const) (ops : PointedRaw Head Base) : Prop
    extends ops.forget.Lawful ρ where
  pointed : ∀ {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {l r out : Tm Head n},
    ops.pointed τ l = some out →
    Typed ρ.rules Γ l (ρ.carrierAt n τ) → Typed ρ.rules Γ r (ρ.carrierAt n τ) →
    Equal ρ.rules Γ l r (ρ.carrierAt n τ) →
    Typed ρ.rules Γ out (ρ.holdsOf (ρ.eqOf τ l r))

variable {ρ : HOLReading Head Base Const}

/-- The embedding keeps the laws: reflexivity at a point is the point-free
reflexivity, whose law already takes typed-equal endpoints. -/
theorem EqualityRaw.Lawful.pointedByConstant {raw : EqualityRaw Head Base}
    (lawful : raw.Lawful ρ) : raw.pointedByConstant.Lawful ρ where
  toLawful := lawful
  pointed := lawful.reflexivity

theorem EqualityRaw.logicalOnly_lawful : (EqualityRaw.logicalOnly : EqualityRaw Head Base).Lawful ρ where
  reflexivity := fun h => nomatch h
  symmetry := fun h => nomatch h
  transitivity := fun h => nomatch h
  propositionExtensionality := fun h => nomatch h
  propositionForward := fun h => nomatch h
  functionCongruence := fun h => nomatch h
  argumentCongruence := fun h => nomatch h
  functionExtensionality := fun h => nomatch h

/-! ## The algebras with their laws -/

/-- The typed analogue of the legacy `Operations`: an equality-proof algebra
whose operations are certified in the selected judgment of the reading's
package. -/
structure TypedOperations (ρ : HOLReading Head Base Const) where
  raw : EqualityRaw Head Base
  lawful : raw.Lawful ρ

/-- An equality-proof algebra with reflexivity at a point, certified in the
selected judgment of the reading's package. -/
structure PointedOperations (ρ : HOLReading Head Base Const) where
  raw : PointedRaw Head Base
  lawful : raw.Lawful ρ

/-- The forgetful map. -/
def PointedOperations.forget (ops : PointedOperations ρ) : TypedOperations ρ :=
  ⟨ops.raw.forget, ops.lawful.toLawful⟩

/-- The embedding: reflexivity at every point is the point-free reflexivity. -/
def TypedOperations.pointedByConstant (ops : TypedOperations ρ) : PointedOperations ρ :=
  ⟨ops.raw.pointedByConstant, ops.lawful.pointedByConstant⟩

@[simp] theorem TypedOperations.pointedByConstant_forget (ops : TypedOperations ρ) :
    ops.pointedByConstant.forget = ops :=
  rfl

/-- The algebra with no equality operation. -/
def TypedOperations.logicalOnly (ρ : HOLReading Head Base Const) : TypedOperations ρ :=
  ⟨EqualityRaw.logicalOnly, EqualityRaw.logicalOnly_lawful⟩

/-- **Forgetful map.** A proof with no reflexivity node compiles the same way
under an algebra and under the embedding of its forgetful image. -/
theorem PointedOperations.compileP_forget (ops : PointedOperations ρ) {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ)
    (noPointed : ∀ τ, Request.pointed τ ∉ requests d) {n : Nat}
    (objects : Sub Head Γ.length n) (hyps : Fin Δ.length → Tm Head n) :
    ρ.compileP ops.raw d objects hyps = ρ.compileP ops.forget.pointedByConstant.raw d objects hyps :=
  HOLReading.compileP_forget ops.raw d noPointed objects hyps

/-! ## Typing -/

namespace HOLReading

/-! ## Reading of composite terms -/

theorem term_eq_of {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {l r : HOL.Term Const Γ τ}
    {l' r' : Tm Head Γ.length} (hl : ρ.term l = some l') (hr : ρ.term r = some r') :
    ρ.term (.eq l r) = some (ρ.eqOf τ l' r') := by
  simp only [term, hl, hr]
  rfl

theorem term_imp_of {Γ : HOL.Ctx Base} {p q : HOL.Formula Const Γ} {p' q' : Tm Head Γ.length}
    (hp : ρ.term p = some p') (hq : ρ.term q = some q') :
    ρ.term (.imp p q) = some (ρ.impOf p' q') := by
  simp only [term, hp, hq]
  rfl

theorem term_app_of {Γ : HOL.Ctx Base} {σ τ : HOL.Ty Base} {f : HOL.Term Const Γ (.arr σ τ)}
    {a : HOL.Term Const Γ σ} {f' a' : Tm Head Γ.length} (hf : ρ.term f = some f')
    (ha : ρ.term a = some a') : ρ.term (.app f a) = some (.app f' a') := by
  simp only [term, hf, ha]
  rfl

theorem term_lam_of {Γ : HOL.Ctx Base} {σ τ : HOL.Ty Base} {b : HOL.Term Const (σ :: Γ) τ}
    {b' : Tm Head (Γ.length + 1)} (hb : ρ.term b = some b') :
    ρ.term (.lam b) = some (.lam b') := by
  simp only [term, hb, Option.map_some]

end HOLReading

namespace HOLReading.Laws

variable (L : ρ.Laws)
include L

/-- A read term, moved along a typed substitution, has its carrier as a type. -/
theorem term_typed_subst {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {t : HOL.Term Const Γ τ}
    {code : Tm Head Γ.length} (h : ρ.term t = some code) {n : Nat} {target : Ctx Head n}
    {objects : Sub Head Γ.length n} (objectsTyped : SubstMor ρ.rules (ρ.objCtx Γ) target objects) :
    Typed ρ.rules target (Presentation.subst objects code) (ρ.carrierAt n τ) := by
  simpa only [HOLReading.subst_carrierAt] using (L.term_typed h).substitute objectsTyped

/-- The β-step that opens a weakened abstraction at the variable it binds:
`(λ b)⁺ x ≡ b`. -/
theorem equal_app_wk_lam {n : Nat} {Γ : Ctx Head n} {σ τ : HOL.Ty Base} {b : Tm Head (n + 1)}
    (hb : Typed ρ.rules (.snoc Γ (ρ.carrierAt n σ)) b (ρ.carrierAt (n + 1) τ)) :
    Equal ρ.rules (.snoc Γ (ρ.carrierAt n σ))
      (.app (Presentation.rename wk (.lam b)) (.var 0)) b (ρ.carrierAt (n + 1) τ) := by
  have lifted : Typed ρ.rules (.snoc (.snoc Γ (ρ.carrierAt n σ)) (ρ.carrierAt (n + 1) σ))
      (Presentation.rename (liftRen wk) b) (ρ.carrierAt (n + 2) τ) := by
    have h := hb.rename (CtxRen.snoc (Gamma := Γ) (Delta := .snoc Γ (ρ.carrierAt n σ))
      (rho := wk) (fun _ => rfl) (ρ.carrierAt n σ))
    simpa only [HOLReading.rename_carrierAt] using h
  have beta := Derivable.betaPi (L.carrierAt_typed (.arr σ τ)) L.proofs_universe lifted
    (ρ.var_carrier σ)
  rw [inst0_var_rename_liftRen_wk, HOLReading.inst0_carrierAt] at beta
  exact beta

/-- **Typing of compiled proofs.** Under a lawful algebra, if the objects are
typed at their carriers and each hypothesis is read and has a proof of the
decoding of its code, a compiled proof is typed, in the selected judgment of the
reading's package, at the decoding of the code of its conclusion. -/
theorem compileP_typedO {ops : PointedRaw Head Base} (lawful : ops.Lawful ρ)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntax Const Δ φ) :
    ∀ {n : Nat} {target : Ctx Head n} {objects : Sub Head Γ.length n}
      {hyps : Fin Δ.length → Tm Head n},
      SubstMor ρ.rules (ρ.objCtx Γ) target objects →
      (∀ i, ∃ c, ρ.term (Δ.get i) = some c ∧
        Typed ρ.rules target (hyps i) (ρ.holdsOf (Presentation.subst objects c))) →
      ∀ {out : Tm Head n}, ρ.compileP ops d objects hyps = some out →
        ∃ code, ρ.term φ = some code ∧
          Typed ρ.rules target out (ρ.holdsOf (Presentation.subst objects code)) := by
  induction d with
  | hyp i =>
      intro n target objects hyps _ hypsTyped out success
      simp only [HOLReading.compileP, Option.some.injEq] at success
      subst success
      exact hypsTyped i
  | @impI Γ Δ p q body ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at success
      obtain ⟨pc, hp, b, hb, rfl⟩ := success
      have objectsTyped' : SubstMor ρ.rules (ρ.objCtx Γ)
          (.snoc target (ρ.holdsOf (Presentation.subst objects pc)))
          (fun i => Presentation.rename wk (objects i)) := fun i => by
        simpa only [rename_subst] using (objectsTyped i).weaken
          (extension := ρ.holdsOf (Presentation.subst objects pc))
      have hypsTyped' : ∀ i : Fin (p :: Δ).length, ∃ c,
          ρ.term ((p :: Δ).get i) = some c ∧
          Typed ρ.rules (.snoc target (ρ.holdsOf (Presentation.subst objects pc)))
            (Fin.cases (.var 0) (fun i => Presentation.rename wk (hyps i)) i)
            (ρ.holdsOf (Presentation.subst
              (fun i => Presentation.rename wk (objects i)) c)) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · refine ⟨pc, hp, ?_⟩
          simpa only [Fin.cases_zero, Ctx.lookup_snoc_zero, rename_subst,
            Presentation.rename] using
            (Derivable.var (R := ρ.rules)
              (Γ := .snoc target (ρ.holdsOf (Presentation.subst objects pc))) 0)
        · obtain ⟨c, hc, typed⟩ := hypsTyped j
          refine ⟨c, hc, ?_⟩
          simpa only [Fin.cases_succ, rename_subst, Presentation.rename] using
            typed.weaken (extension := ρ.holdsOf (Presentation.subst objects pc))
      obtain ⟨qc, hq, bodyTyped⟩ := ih objectsTyped' hypsTyped' hb
      refine ⟨ρ.impOf pc qc, by simp only [HOLReading.term, hp, hq]; rfl, ?_⟩
      exact L.impIntro ((L.term_typed hp).substitute objectsTyped)
        ((L.term_typed hq).substitute objectsTyped)
        (by simpa only [rename_subst] using bodyTyped)
  | impE function argument ihFunction ihArgument =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at success
      obtain ⟨f, hf, a, ha, rfl⟩ := success
      obtain ⟨fc, hfc, functionTyped⟩ := ihFunction objectsTyped hypsTyped hf
      obtain ⟨pc, hpc, argumentTyped⟩ := ihArgument objectsTyped hypsTyped ha
      obtain ⟨p', q', hp', hq', rfl⟩ := HOLReading.term_imp hfc
      rw [hpc] at hp'
      cases hp'
      exact ⟨q', hq', L.impElim ((L.term_typed hpc).substitute objectsTyped)
        ((L.term_typed hq').substitute objectsTyped) functionTyped argumentTyped⟩
  | @allI Γ Δ σ φ body ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at success
      obtain ⟨b, hb, rfl⟩ := success
      have objectsTyped' : SubstMor ρ.rules (ρ.objCtx (σ :: Γ))
          (.snoc target (ρ.carrierAt n σ)) (liftSub objects) := by
        have lifted := SubstMor.lift objectsTyped (ρ.carrierAt Γ.length σ)
        rw [HOLReading.subst_carrierAt] at lifted
        exact lifted
      have hypsTyped' : ∀ i : Fin (HOL.weakenHyps (σ := σ) Δ).length, ∃ c,
          ρ.term ((HOL.weakenHyps (σ := σ) Δ).get i) = some c ∧
            Typed ρ.rules (.snoc target (ρ.carrierAt n σ))
              (Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))
              (ρ.holdsOf (Presentation.subst (liftSub objects) c)) := by
        intro i
        obtain ⟨c, hc, typed⟩ := hypsTyped (i.cast (by simp [HOL.weakenHyps]))
        refine ⟨Presentation.rename wk c, ?_, ?_⟩
        · have entry : (HOL.weakenHyps (σ := σ) Δ).get i =
              HOL.weaken (Δ.get (i.cast (by simp [HOL.weakenHyps]))) := by
            have indexValid : i.val < Δ.length := by simpa [HOL.weakenHyps] using i.isLt
            change (Δ.map (HOL.weaken (σ := σ)))[i.val] = HOL.weaken Δ[i.val]
            simp only [List.getElem_map]
          rw [entry, ρ.term_weaken, hc]
          rfl
        · simpa only [subst_liftSub_wk, Presentation.rename] using
            typed.weaken (extension := ρ.carrierAt n σ)
      obtain ⟨bc, hbc, bodyTyped⟩ := ih objectsTyped' hypsTyped' hb
      refine ⟨ρ.allOf σ (.lam bc), by simp only [HOLReading.term, hbc]; rfl, ?_⟩
      exact L.allIntro ((L.term_typed hbc).substitute objectsTyped') bodyTyped
  | @allE Γ Δ σ φ t function ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at success
      obtain ⟨tc, ht, f, hf, rfl⟩ := success
      obtain ⟨fc, hfc, functionTyped⟩ := ih objectsTyped hypsTyped hf
      obtain ⟨φc, hφc, rfl⟩ := HOLReading.term_all hfc
      refine ⟨inst0 tc φc, by rw [ρ.term_instantiate ht, hφc]; rfl, ?_⟩
      have objectsTyped' : SubstMor ρ.rules (ρ.objCtx (σ :: Γ))
          (.snoc target (ρ.carrierAt n σ)) (liftSub objects) := by
        have lifted := SubstMor.lift objectsTyped (ρ.carrierAt Γ.length σ)
        rw [HOLReading.subst_carrierAt] at lifted
        exact lifted
      have eliminated := L.allElim ((L.term_typed hφc).substitute objectsTyped')
        functionTyped (L.term_typed_subst ht objectsTyped)
      simpa only [subst_inst0] using eliminated
  | @eqRefl Γ Δ τ t =>
      intro n target objects hyps objectsTyped _ out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨t', ht, hp⟩ := success
      refine ⟨ρ.eqOf τ t' t', by simp only [HOLReading.term, ht]; rfl, ?_⟩
      have hl := L.term_typed_subst ht objectsTyped
      exact lawful.pointed hp hl hl (.refl hl)
  | @eqSymm Γ Δ τ t u proof ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨t', ht, u', hu, e, he, hs⟩ := success
      obtain ⟨c, hc, typed⟩ := ih objectsTyped hypsTyped he
      obtain ⟨t'', u'', ht', hu', rfl⟩ := HOLReading.term_eq hc
      rw [ht] at ht'
      cases ht'
      rw [hu] at hu'
      cases hu'
      refine ⟨ρ.eqOf τ u' t', by simp only [HOLReading.term, ht, hu]; rfl, ?_⟩
      exact lawful.symmetry hs (L.term_typed_subst ht objectsTyped)
        (L.term_typed_subst hu objectsTyped) typed
  | @eqTrans Γ Δ τ t u w first second ihFirst ihSecond =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨t', ht, u', hu, w', hw, e₁, he₁, e₂, he₂, hs⟩ := success
      obtain ⟨c₁, hc₁, typed₁⟩ := ihFirst objectsTyped hypsTyped he₁
      obtain ⟨c₂, hc₂, typed₂⟩ := ihSecond objectsTyped hypsTyped he₂
      obtain ⟨a, b, ha, hb, rfl⟩ := HOLReading.term_eq hc₁
      rw [ht] at ha
      cases ha
      rw [hu] at hb
      cases hb
      obtain ⟨a, b, ha, hb, rfl⟩ := HOLReading.term_eq hc₂
      rw [hu] at ha
      cases ha
      rw [hw] at hb
      cases hb
      refine ⟨ρ.eqOf τ t' w', by simp only [HOLReading.term, ht, hw]; rfl, ?_⟩
      exact lawful.transitivity hs (L.term_typed_subst ht objectsTyped)
        (L.term_typed_subst hu objectsTyped) (L.term_typed_subst hw objectsTyped) typed₁ typed₂
  | @eqPropI Γ Δ p q forward backward ihForward ihBackward =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨p', hp, q', hq, f, hf, b, hb, hs⟩ := success
      obtain ⟨c₁, hc₁, typedForward⟩ := ihForward objectsTyped hypsTyped hf
      obtain ⟨c₂, hc₂, typedBackward⟩ := ihBackward objectsTyped hypsTyped hb
      obtain ⟨a, a', ha, ha', rfl⟩ := HOLReading.term_imp hc₁
      rw [hp] at ha
      cases ha
      rw [hq] at ha'
      cases ha'
      obtain ⟨a, a', ha, ha', rfl⟩ := HOLReading.term_imp hc₂
      rw [hq] at ha
      cases ha
      rw [hp] at ha'
      cases ha'
      refine ⟨ρ.eqOf .prop p' q', by simp only [HOLReading.term, hp, hq]; rfl, ?_⟩
      exact lawful.propositionExtensionality hs (L.term_typed_subst hp objectsTyped)
        (L.term_typed_subst hq objectsTyped) typedForward typedBackward
  | @eqPropEL Γ Δ p q proof ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨p', hp, q', hq, e, he, hs⟩ := success
      obtain ⟨c, hc, typed⟩ := ih objectsTyped hypsTyped he
      obtain ⟨a, a', ha, ha', rfl⟩ := HOLReading.term_eq hc
      rw [hp] at ha
      cases ha
      rw [hq] at ha'
      cases ha'
      refine ⟨ρ.impOf p' q', by simp only [HOLReading.term, hp, hq]; rfl, ?_⟩
      exact lawful.propositionForward hs (L.term_typed_subst hp objectsTyped)
        (L.term_typed_subst hq objectsTyped) typed
  | @eqPropER Γ Δ p q proof ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨p', hp, q', hq, e, he, reversed, hr, hs⟩ := success
      obtain ⟨c, hc, typed⟩ := ih objectsTyped hypsTyped he
      obtain ⟨a, a', ha, ha', rfl⟩ := HOLReading.term_eq hc
      rw [hp] at ha
      cases ha
      rw [hq] at ha'
      cases ha'
      refine ⟨ρ.impOf q' p', by simp only [HOLReading.term, hp, hq]; rfl, ?_⟩
      have typedP := L.term_typed_subst hp objectsTyped
      have typedQ := L.term_typed_subst hq objectsTyped
      exact lawful.propositionForward hs typedQ typedP
        (lawful.symmetry (τ := .prop) hr typedP typedQ typed)
  | @eqApp Γ Δ σ τ f g t proof ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨f', hf, g', hg, a', ha, e, he, hs⟩ := success
      obtain ⟨c, hc, typed⟩ := ih objectsTyped hypsTyped he
      obtain ⟨b, b', hb, hb', rfl⟩ := HOLReading.term_eq hc
      rw [hf] at hb
      cases hb
      rw [hg] at hb'
      cases hb'
      refine ⟨ρ.eqOf τ (.app f' a') (.app g' a'),
        by simp only [HOLReading.term, hf, hg, ha]; rfl, ?_⟩
      exact lawful.functionCongruence hs (L.term_typed_subst hf objectsTyped)
        (L.term_typed_subst hg objectsTyped) (L.term_typed_subst ha objectsTyped) typed
  | @eqAppArg Γ Δ σ τ f t u proof ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨f', hf, t', ht, u', hu, e, he, hs⟩ := success
      obtain ⟨c, hc, typed⟩ := ih objectsTyped hypsTyped he
      obtain ⟨b, b', hb, hb', rfl⟩ := HOLReading.term_eq hc
      rw [ht] at hb
      cases hb
      rw [hu] at hb'
      cases hb'
      refine ⟨ρ.eqOf τ (.app f' t') (.app f' u'),
        by simp only [HOLReading.term, hf, ht, hu]; rfl, ?_⟩
      exact lawful.argumentCongruence hs (L.term_typed_subst hf objectsTyped)
        (L.term_typed_subst ht objectsTyped) (L.term_typed_subst hu objectsTyped) typed
  | @eqLam Γ Δ σ τ t u proof ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨l, hl, r, hr, e, he, hs⟩ := success
      have objectsTyped' : SubstMor ρ.rules (ρ.objCtx (σ :: Γ))
          (.snoc target (ρ.carrierAt n σ)) (liftSub objects) := by
        have lifted := SubstMor.lift objectsTyped (ρ.carrierAt Γ.length σ)
        rw [HOLReading.subst_carrierAt] at lifted
        exact lifted
      have hypsTyped' : ∀ i : Fin (HOL.weakenHyps (σ := σ) Δ).length, ∃ c,
          ρ.term ((HOL.weakenHyps (σ := σ) Δ).get i) = some c ∧
            Typed ρ.rules (.snoc target (ρ.carrierAt n σ))
              (Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))
              (ρ.holdsOf (Presentation.subst (liftSub objects) c)) := by
        intro i
        obtain ⟨c, hc, typed⟩ := hypsTyped (i.cast (by simp [HOL.weakenHyps]))
        refine ⟨Presentation.rename wk c, ?_, ?_⟩
        · have entry : (HOL.weakenHyps (σ := σ) Δ).get i =
              HOL.weaken (Δ.get (i.cast (by simp [HOL.weakenHyps]))) := by
            have indexValid : i.val < Δ.length := by simpa [HOL.weakenHyps] using i.isLt
            change (Δ.map (HOL.weaken (σ := σ)))[i.val] = HOL.weaken Δ[i.val]
            simp only [List.getElem_map]
          rw [entry, ρ.term_weaken, hc]
          rfl
        · simpa only [subst_liftSub_wk, Presentation.rename] using
            typed.weaken (extension := ρ.carrierAt n σ)
      obtain ⟨c, hc, typed⟩ := ih objectsTyped' hypsTyped' he
      obtain ⟨a, a', ha, ha', rfl⟩ := HOLReading.term_eq hc
      rw [hl] at ha
      cases ha
      rw [hr] at ha'
      cases ha'
      refine ⟨ρ.eqOf (.arr σ τ) (.lam l) (.lam r),
        by simp only [HOLReading.term, hl, hr]; rfl, ?_⟩
      have typedF : Typed ρ.rules target (.lam (Presentation.subst (liftSub objects) l))
          (ρ.carrierAt n (.arr σ τ)) := L.term_typed_subst (HOLReading.term_lam_of hl) objectsTyped
      have typedG : Typed ρ.rules target (.lam (Presentation.subst (liftSub objects) r))
          (ρ.carrierAt n (.arr σ τ)) := L.term_typed_subst (HOLReading.term_lam_of hr) objectsTyped
      have bodyLeft := L.term_typed_subst hl objectsTyped'
      have bodyRight := L.term_typed_subst hr objectsTyped'
      have betaLeft := L.equal_app_wk_lam bodyLeft
      have betaRight := L.equal_app_wk_lam bodyRight
      have openedLeft : Typed ρ.rules (.snoc target (ρ.carrierAt n σ))
          (.app (Presentation.rename wk (.lam (Presentation.subst (liftSub objects) l))) (.var 0))
          (ρ.carrierAt (n + 1) τ) :=
        HOLReading.app_carrier (σ := σ)
          (by simpa only [HOLReading.rename_carrierAt] using
            typedF.weaken (extension := ρ.carrierAt n σ))
          (ρ.var_carrier σ)
      have openedRight : Typed ρ.rules (.snoc target (ρ.carrierAt n σ))
          (.app (Presentation.rename wk (.lam (Presentation.subst (liftSub objects) r))) (.var 0))
          (ρ.carrierAt (n + 1) τ) :=
        HOLReading.app_carrier (σ := σ)
          (by simpa only [HOLReading.rename_carrierAt] using
            typedG.weaken (extension := ρ.carrierAt n σ))
          (ρ.var_carrier σ)
      have codes := L.equal_eqOf betaLeft betaRight
      have pointwise := L.allIntro (L.eqOf_typed openedLeft openedRight)
        (.conv typed (L.equal_holdsOf (.symm codes)) L.proofs_universe)
      exact lawful.functionExtensionality hs typedF typedG pointwise
  | @funExt Γ Δ σ τ f g proof ih =>
      intro n target objects hyps objectsTyped hypsTyped out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨f', hf, g', hg, e, he, hs⟩ := success
      obtain ⟨c, hc, typed⟩ := ih objectsTyped hypsTyped he
      have read : ρ.term (.all (.eq (.app (HOL.weaken (σ := σ) f) (.var .vz))
          (.app (HOL.weaken (σ := σ) g) (.var .vz)))) =
          some (ρ.allOf σ (.lam (ρ.eqOf τ (.app (Presentation.rename wk f') (.var 0))
            (.app (Presentation.rename wk g') (.var 0))))) := by
        simp only [HOLReading.term, ρ.term_weaken, hf, hg, Option.map_some]
        rfl
      rw [read] at hc
      cases hc
      refine ⟨ρ.eqOf (.arr σ τ) f' g', by simp only [HOLReading.term, hf, hg]; rfl, ?_⟩
      have moved : Presentation.subst objects (ρ.allOf σ (.lam (ρ.eqOf τ
          (.app (Presentation.rename wk f') (.var 0)) (.app (Presentation.rename wk g') (.var 0))))) =
          ρ.allOf σ (.lam (ρ.eqOf τ
            (.app (Presentation.rename wk (Presentation.subst objects f')) (.var 0))
            (.app (Presentation.rename wk (Presentation.subst objects g')) (.var 0)))) := by
        simp only [HOLReading.allOf, HOLReading.eqOf, Presentation.subst, subst_liftSub_wk]
        rfl
      rw [moved] at typed
      exact lawful.functionExtensionality hs (L.term_typed_subst hf objectsTyped)
        (L.term_typed_subst hg objectsTyped) typed
  | @beta Γ Δ σ τ t body =>
      intro n target objects hyps objectsTyped _ out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨a, ha, b, hb, hs⟩ := success
      have redex : ρ.term (.app (.lam body) t) = some (.app (.lam b) a) :=
        HOLReading.term_app_of (HOLReading.term_lam_of hb) ha
      have reduct : ρ.term (HOL.instantiate t body) = some (inst0 a b) := by
        rw [ρ.term_instantiate ha, hb]
        rfl
      refine ⟨ρ.eqOf τ (.app (.lam b) a) (inst0 a b), HOLReading.term_eq_of redex reduct, ?_⟩
      have objectsTyped' : SubstMor ρ.rules (ρ.objCtx (σ :: Γ))
          (.snoc target (ρ.carrierAt n σ)) (liftSub objects) := by
        have lifted := SubstMor.lift objectsTyped (ρ.carrierAt Γ.length σ)
        rw [HOLReading.subst_carrierAt] at lifted
        exact lifted
      have typedLeft := L.term_typed_subst redex objectsTyped
      have typedRight := L.term_typed_subst reduct objectsTyped
      have beta := Derivable.betaPi (L.carrierAt_typed (.arr σ τ)) L.proofs_universe
        (L.term_typed_subst hb objectsTyped') (L.term_typed_subst ha objectsTyped)
      rw [HOLReading.inst0_carrierAt, ← subst_inst0] at beta
      exact lawful.pointed hs typedLeft typedRight beta
  | @eta Γ Δ σ τ f =>
      intro n target objects hyps objectsTyped _ out success
      simp only [HOLReading.compileP, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨f', hf, hs⟩ := success
      refine ⟨ρ.eqOf (.arr σ τ) (.lam (.app (Presentation.rename wk f') (.var 0))) f',
        by simp only [HOLReading.term, ρ.term_weaken, hf, Option.map_some]; rfl, ?_⟩
      have moved : Presentation.subst objects
          (ρ.eqOf (.arr σ τ) (.lam (.app (Presentation.rename wk f') (.var 0))) f') =
          ρ.eqOf (.arr σ τ)
            (.lam (.app (Presentation.rename wk (Presentation.subst objects f')) (.var 0)))
            (Presentation.subst objects f') := by
        simp only [HOLReading.eqOf, Presentation.subst, subst_liftSub_wk]
        rfl
      rw [moved]
      have typedRight := L.term_typed_subst hf objectsTyped
      have opened : Typed ρ.rules (.snoc target (ρ.carrierAt n σ))
          (.app (Presentation.rename wk (Presentation.subst objects f')) (.var 0))
          (ρ.carrierAt (n + 1) τ) :=
        HOLReading.app_carrier (σ := σ)
          (by simpa only [HOLReading.rename_carrierAt] using
            typedRight.weaken (extension := ρ.carrierAt n σ))
          (ρ.var_carrier σ)
      have typedLeft := L.lam_carrier opened
      have pointwise := L.equal_app_wk_lam opened
      exact lawful.pointed hs typedLeft typedRight (.etaPi typedLeft typedRight pointwise)
  | _ =>
      intro n target objects hyps _ _ out success
      simp [HOLReading.compileP] at success

end HOLReading.Laws

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
