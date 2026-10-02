import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchLifting

/-!
# Controls: lifting the object package's derivations to its annotation

* **Positive: the domain of an abstraction is reconstructed.** The raw identity function of
  the numbers, `λ x. x : Π (x : num). num`, lifts over the empty context (`idNum_lifts`), and
  every lift of it is `λ (x : D). x` at `Π (x : num). num` with `D` equal to the numbers
  (`idNum_lift_domain`, `idNum_domain_reconstructed`).
* **Positive: an abstraction in function position.** The raw redex `(λ x. x) 0 : num` lifts
  to `(λ (x : D). x) 0`, which computes to `0` at the numbers (`idApp_lift_computes`).
* **Positive: an equation of types with an abstraction** lifts in the form the transfer of
  the facts about weak-head forms consumes: `(λ X. X) num ≡ num : U₀` is the erasure of
  `(λ (X : D). X) num ≡ num` for some domain `D` (`betaType_lift`).
* **Positive: η for functions lifts.** In the context `f : Π (x : num). num`, the raw
  η-equation `f ≡ λ x. f x`, derived by the η-rule from a β-step (`etaNum_raw`), lifts to
  `f ≡ λ (x : D). f x` with `D` equal to the numbers (`etaNum_lift`).
* **Negative: a judgment over an ill-formed context does not lift.** In the context
  `x : λ y. y`, whose entry is no type, `x : λ y. y` and the type `U₀` are derivable
  (`illFormed_var_typed`, `illFormed_isType`), but no formed annotated context erases to that
  context (`illFormed_no_lift`), since no abstraction is a type (`lam_not_type`). So neither
  judgment lifts (`illFormed_var_not_lifted`, `illFormed_type_not_lifted`): the hypothesis of
  the lifting on the context cannot be dropped. Through the lifting, the context is not
  formed (`illFormed_not_formed`).
* **Negative: erasure is not injective, so the lift's choice is visible.**
  - `λ (x : num). x` and `λ (x : set). x` have one erasure and differ (`idNum_idSet_erase`).
    The first is a lift of the raw identity at `Π (x : num). num` (`idNum_annot_typed`); the
    second is typed at no such type (`idSet_not_typed`): at a dependent function type, the
    domain is forced up to equality.
  - In function position it is not: `(λ (X : U₀). X) num` and `(λ (X : U₁). X) num` have one
    erasure (`redexes_erase`) and are both typed at `U₁` (`redex0_typed`, `redex1_typed`),
    although `U₀` and `U₁` are not equal types (`universes_not_equal`). Coherence equates
    the two redexes (`redexes_equal`), which is what makes the lifting independent of the
    choice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Package (numT U0)

namespace CodeModel
namespace LiftingControls

/-! ## Positive: the domain of an abstraction is reconstructed -/

/-- The raw identity function of the numbers. -/
theorem idNum_raw : Typed objectRules (.nil : Tower.Ctx 0) (.lam (.var 0)) (.pi numT numT) :=
  .lamIntro (piO num_typedO num_typedO) (.sort _) (.var 0)

/-- **The raw identity function of the numbers lifts** over the empty context. -/
theorem idNum_lifts : ∃ (t' A' : CTm Tower.Head 0), t'.erase = .lam (.var 0) ∧
    A'.erase = .pi numT numT ∧ CTyped objectChurch .nil t' A' :=
  objectRules_lifts idNum_raw CCtxFormed.nil rfl

/-- **Every lift of the identity function of the numbers is an abstraction whose domain is
equal to the numbers**, at `Π (x : num). num`. -/
theorem idNum_lift_domain {t' A' : CTm Tower.Head 0} (et : t'.erase = .lam (.var 0))
    (eA : A'.erase = .pi numT numT) (typing : CTyped objectChurch .nil t' A') :
    ∃ D, t' = .lam D (.var 0) ∧ A' = .pi cnum cnum ∧ CTypeEq objectChurch .nil D cnum := by
  obtain ⟨D, b, rfl, eb⟩ := CTm.erase_eq_lam et
  obtain rfl := CTm.erase_eq_var eb
  obtain rfl : A' = .pi cnum cnum := CTm.eq_of_erase_eq_of_lamFree eA rfl
  exact ⟨D, rfl, rfl, (CTyped.lam_inv objectFormerFacts ConvRules.objectLevels typing .nil).1⟩

/-- **The lifting reconstructs the domain of the identity function**: an annotated
abstraction typed at `Π (x : num). num` whose domain is equal to the numbers. -/
theorem idNum_domain_reconstructed : ∃ D, CTyped objectChurch .nil (.lam D (.var 0)) (.pi cnum cnum) ∧
    CTypeEq objectChurch .nil D cnum := by
  obtain ⟨t', A', et, eA, typing⟩ := idNum_lifts
  obtain ⟨D, rfl, rfl, eD⟩ := idNum_lift_domain et eA typing
  exact ⟨D, typing, eD⟩

/-! ## Positive: an abstraction in function position -/

/-- The raw application of the identity function to zero. -/
theorem idApp_raw :
    Typed objectRules (.nil : Tower.Ctx 0) (.app (.lam (.var 0)) (.const zeroN)) numT := by
  have h := Derivable.appElim idNum_raw zero_typedO
  exact h

/-- **The lifted redex computes**: the raw `(λ x. x) 0 : num` lifts to `(λ (x : D). x) 0` at
the numbers, which is equal to `0` there. -/
theorem idApp_lift_computes : ∃ D, CTyped objectChurch .nil (.app (.lam D (.var 0)) czero) cnum ∧
    CEqual objectChurch .nil (.app (.lam D (.var 0)) czero) czero cnum := by
  obtain ⟨t', A', et, eA, typing⟩ := objectRules_lifts idApp_raw CCtxFormed.nil rfl
  obtain ⟨f, a, rfl, ef, ea⟩ := CTm.erase_eq_app et
  obtain ⟨D, b, rfl, eb⟩ := CTm.erase_eq_lam ef
  obtain rfl := CTm.erase_eq_var eb
  obtain rfl := CTm.erase_eq_const ea
  obtain rfl := CTm.erase_eq_const eA
  exact ⟨D, typing, CTyped.beta_equal objectFormerFacts ConvRules.objectLevels .nil typing⟩

/-! ## Positive: an equation of types with an abstraction -/

/-- The raw equation of types `(λ X. X) num ≡ num : U₀`. -/
theorem betaType_raw :
    TypeEq objectRules (.nil : Tower.Ctx 0) (.app (.lam (.var 0)) numT) numT := by
  have h := Derivable.betaPi (R := objectRules) (Γ := .nil) (body := .var 0) (a := numT)
    (piO U0_typedO U0_typedO) (.sort _) (.var 0) num_typedO
  exact ⟨_, .sort Tower.zero, h⟩

/-- **The equation of types lifts**, in the form the transfer consumes: it is the erasure of
the annotated equation `(λ (X : D). X) num ≡ num` for a reconstructed domain `D`. -/
theorem betaType_lift : ∃ D, CTypeEq objectChurch .nil (.app (.lam D (.var 0)) cnum) cnum := by
  obtain ⟨Γ', A', B', _, _, eA, eB, equal⟩ := objectRules_liftTypeEq CtxFormed.nil betaType_raw
  cases Γ'
  obtain ⟨f, a, rfl, ef, ea⟩ := CTm.erase_eq_app eA
  obtain ⟨D, b, rfl, eb⟩ := CTm.erase_eq_lam ef
  obtain rfl := CTm.erase_eq_var eb
  obtain rfl := CTm.erase_eq_const ea
  obtain rfl := CTm.erase_eq_const eB
  exact ⟨D, equal⟩

/-! ## Positive: η for functions lifts -/

/-- The context `f : Π (x : num). num`. -/
abbrev ctxF : Tower.Ctx 1 := .snoc .nil (.pi numT numT)

/-- The annotated context `f : Π (x : num). num`. -/
abbrev cctxF : CCtx Tower.Head 1 := .snoc .nil (.pi cnum cnum)

/-- The raw η-equation `f ≡ λ x. f x`, by the η-rule from a β-step. -/
theorem etaNum_raw :
    Equal objectRules ctxF (.var 0) (.lam (.app (.var 1) (.var 0))) (.pi numT numT) := by
  have tf : Typed objectRules ctxF (.var 0) (.pi numT numT) := .var 0
  have tBody : Typed objectRules (.snoc ctxF numT) (.app (.var 1) (.var 0)) numT := by
    have h := Derivable.appElim (R := objectRules) (Γ := .snoc ctxF numT) (g := .var 1)
      (a := .var 0) (A := numT) (B := numT) (.var 1) (.var 0)
    exact h
  have tg : Typed objectRules ctxF (.lam (.app (.var 1) (.var 0))) (.pi numT numT) :=
    .lamIntro (piO num_typedO num_typedO) (.sort _) tBody
  have tBody' : Typed objectRules (.snoc (.snoc ctxF numT) numT) (.app (.var 2) (.var 0)) numT := by
    have h := Derivable.appElim (R := objectRules) (Γ := .snoc (.snoc ctxF numT) numT)
      (g := .var 2) (a := .var 0) (A := numT) (B := numT) (.var 2) (.var 0)
    exact h
  have beta := Derivable.betaPi (R := objectRules) (Γ := .snoc ctxF numT) (A := numT) (B := numT)
    (body := .app (.var 2) (.var 0)) (a := .var 0) (piO num_typedO num_typedO) (.sort _) tBody'
    (.var 0)
  exact .etaPi tf tg (.symm beta)

/-- **η for functions lifts**: the raw `f ≡ λ x. f x` is the erasure of `f ≡ λ (x : D). f x`
at `Π (x : num). num`, with `D` equal to the numbers. -/
theorem etaNum_lift : ∃ D, CEqual objectChurch cctxF (.var 0) (.lam D (.app (.var 1) (.var 0)))
    (.pi cnum cnum) ∧ CTypeEq objectChurch cctxF D cnum := by
  have formed : CCtxFormed objectChurch cctxF := .snoc .nil ⟨_, .sort _, cpiT cnum_typed cnum_typed⟩
  obtain ⟨a, b, A, ea, eb, eA, e⟩ := objectRules_lifts etaNum_raw formed rfl
  obtain rfl := CTm.erase_eq_var ea
  obtain ⟨D, c, rfl, ec⟩ := CTm.erase_eq_lam eb
  obtain ⟨f, x, rfl, ef, ex⟩ := CTm.erase_eq_app ec
  obtain rfl := CTm.erase_eq_var ef
  obtain rfl := CTm.erase_eq_var ex
  obtain rfl : A = .pi cnum cnum := CTm.eq_of_erase_eq_of_lamFree eA rfl
  exact ⟨D, e, (CTyped.lam_inv objectFormerFacts ConvRules.objectLevels
    (CEqual.typed ConvRules.objectLevels e formed).2 formed).1⟩

/-! ## Negative: a judgment over an ill-formed context does not lift -/

/-- The context `x : λ y. y`, whose entry is no type. -/
abbrev ctxBad : Tower.Ctx 1 := .snoc .nil (.lam (.var 0))

/-- The variable of the ill-formed context is typed at its entry. -/
theorem illFormed_var_typed : Typed objectRules ctxBad (.var 0) (.lam (.var 0)) := by
  have h := Derivable.var (R := objectRules) (Γ := ctxBad) 0
  exact h

/-- `U₀` is a type of the ill-formed context. -/
theorem illFormed_isType : IsType objectRules ctxBad U0 :=
  ⟨_, .sort _, U0_typedO⟩

/-- **No abstraction is an annotated type.** -/
theorem lam_not_type {n : Nat} {Γ : CCtx Tower.Head n} (formed : CCtxFormed objectChurch Γ)
    {D : CTm Tower.Head n} {b : CTm Tower.Head (n + 1)} :
    ¬ CIsType objectChurch Γ (.lam D b) := by
  rintro ⟨u, hu, typing⟩
  obtain ⟨B, u', w, _, _, tPi, hu', _, le⟩ := typing.generation
  have below := CTypeLe.toBelow le (CIsType.head_of_universe ConvRules.objectLevels hu)
  obtain ⟨A', B', eT, -, -⟩ := CBelow.pi_source objectFormerFacts ConvRules.objectLevels below
    formed (CIsType.refl ⟨u', hu', tPi⟩)
  exact CTypeEq.pi_ne_head objectFormerFacts formed eT.symm

/-- **No formed annotated context erases to the ill-formed context.** -/
theorem illFormed_no_lift :
    ¬ ∃ Γ' : CCtx Tower.Head 1, CCtxFormed objectChurch Γ' ∧ Γ'.erase = ctxBad := by
  rintro ⟨Γ', formed, e⟩
  cases formed with
  | snoc formed₀ type =>
      obtain ⟨-, eA⟩ := Ctx.snoc.inj e
      obtain ⟨D, b, rfl, -⟩ := CTm.erase_eq_lam eA
      exact lam_not_type formed₀ type

/-- **The variable's typing over the ill-formed context does not lift.** -/
theorem illFormed_var_not_lifted :
    ¬ ∃ (Γ' : CCtx Tower.Head 1) (t' A' : CTm Tower.Head 1), CCtxFormed objectChurch Γ' ∧
      Γ'.erase = ctxBad ∧ t'.erase = .var 0 ∧ A'.erase = .lam (.var 0) ∧
        CTyped objectChurch Γ' t' A' :=
  fun ⟨Γ', _, _, formed, e, _⟩ => illFormed_no_lift ⟨Γ', formed, e⟩

/-- **The type `U₀` over the ill-formed context does not lift**, although it is a type
there: the conclusion of `objectRules_liftType` fails without its hypothesis on the
context. -/
theorem illFormed_type_not_lifted :
    ¬ ∃ (Γ' : CCtx Tower.Head 1) (A' : CTm Tower.Head 1), CCtxFormed objectChurch Γ' ∧
      Γ'.erase = ctxBad ∧ A'.erase = U0 ∧ CIsType objectChurch Γ' A' :=
  fun ⟨Γ', _, formed, e, _⟩ => illFormed_no_lift ⟨Γ', formed, e⟩

/-- **The ill-formed context is not formed**, through the lifting of formed contexts. -/
theorem illFormed_not_formed : ¬ CtxFormed objectRules ctxBad :=
  fun formed => illFormed_no_lift (objectRules_liftCtx formed)

/-! ## Negative: erasure is not injective, so the lift's choice is visible -/

/-- **The identity at the numbers and at the sets**: one erasure, two annotated terms. -/
theorem idNum_idSet_erase :
    (CTm.lam cnum (.var 0) : CTm Tower.Head 0) ≠ CTm.lam cset (.var 0) ∧
      (CTm.lam cnum (.var 0) : CTm Tower.Head 0).erase = (CTm.lam cset (.var 0)).erase :=
  CTm.erase_not_injective (by decide)

/-- The identity at the numbers is a lift of the raw identity at `Π (x : num). num`. -/
theorem idNum_annot_typed : CTyped objectChurch .nil (.lam cnum (.var 0)) (.pi cnum cnum) :=
  .lamIntro cnum_typed (.sort _) (cpiT cnum_typed cnum_typed) (.sort _) (.var 0)

/-- **The identity at the sets is typed at no dependent function type on the numbers**: its
domain would be equal to the numbers. -/
theorem idSet_not_typed : ¬ CTyped objectChurch .nil (.lam cset (.var 0)) (.pi cnum cnum) :=
  fun typing => CTypeEq.neutral_ne_inductive (A := cset) objectFormFacts .nil
    (Neutral.rigid [] objectRoles_setRigid) objectRoles_num
    (CTyped.lam_inv objectFormerFacts ConvRules.objectLevels typing .nil).1

/-- The identity of a universe applied to the numbers. -/
abbrev redexAt (D : CTm Tower.Head 0) : CTm Tower.Head 0 := .app (.lam D (.var 0)) cnum

/-- `(λ (X : U₀). X) num` is typed at `U₁`. -/
theorem redex0_typed : CTyped objectChurch .nil (redexAt cU0) cU1 := by
  have h : CTyped objectChurch .nil (redexAt cU0) (CTm.inst0 cnum cU0) :=
    .appElim (.lamIntro cU0_typed (.sort _) (cpiT cU0_typed cU0_typed) (.sort _) (.var 0))
      cnum_typed
  exact craise h

/-- `(λ (X : U₁). X) num` is typed at `U₁`. -/
theorem redex1_typed : CTyped objectChurch .nil (redexAt cU1) cU1 := by
  have h : CTyped objectChurch .nil (redexAt cU1) (CTm.inst0 cnum cU1) :=
    .appElim (.lamIntro (CU_typed _) (.sort _) (cpiT (CU_typed _) (CU_typed _)) (.sort _) (.var 0))
      (craise cnum_typed)
  exact h

/-- The two redexes have one erasure. -/
theorem redexes_erase : (redexAt cU0).erase = (redexAt cU1).erase :=
  rfl

/-- **`U₀` and `U₁` are not equal types**: their levels differ. -/
theorem universes_not_equal : ¬ CTypeEq objectChurch (.nil : CCtx Tower.Head 0) cU0 cU1 :=
  fun equal => absurd
    (HeadSame.level ConvRules.objectLevels (CTypeEq.head_injective objectFormerFacts equal .nil)).2
    (by decide)

/-- **Coherence equates the two redexes**, although their domains are not equal. -/
theorem redexes_equal : CEqual objectChurch .nil (redexAt cU0) (redexAt cU1) cU1 :=
  objectCoherence .nil redex0_typed redex1_typed redexes_erase

end LiftingControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
