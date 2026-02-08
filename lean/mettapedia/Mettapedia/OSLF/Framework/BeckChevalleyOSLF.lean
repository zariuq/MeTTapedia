import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.RhoCalculus.Soundness

/-!
# Beck-Chevalley for OSLF: Substitution and Change-of-Base

This file establishes how substitution interacts with the OSLF change-of-base
machinery. The Beck-Chevalley condition in categorical logic says that
quantification commutes with substitution. For OSLF, this manifests as:

1. **Substitution as change-of-base**: The COMM rule's substitution
   `commSubst pBody q = openBVar 0 (NQuote q) pBody` induces an adjoint triple
   `∃_σ ⊣ σ* ⊣ ∀_σ` on the predicate fiber.

2. **Composed Galois connections**: The modal adjunction `◇ ⊣ □` composes with
   the substitution adjunction to give new Galois connections combining
   reduction modalities with substitution.

3. **Substitutability as pullback inequality**: The substitutability theorem
   expressed as `typedAt(Γ.extend x σ, τ) ≤ σ*(typedAt(Γ, τ))` — the
   pullback of the base typing predicate along substitution contains the
   extended-context typing predicate.

4. **COMM Beck-Chevalley**: The COMM rule's type preservation expressed as
   a change-of-base property.

## Why the Strong GSLT Beck-Chevalley Fails

The GSLT's `BeckChevalley` quantifies over ALL commuting squares in the base
category. For the constructor fibration (free category on sort-crossing
constructors), this is too strong: the square

```
    Proc --NQuote--> Name
     |                |
   NQuote           PDrop
     ↓                ↓
    Name --PDrop---> Proc
```

commutes (NQuote ∘ PDrop = NQuote ∘ PDrop) but is NOT a pullback, and the
Beck-Chevalley identity `f* ∘ ∃g = ∃π₁ ∘ π₂*` fails for it.

Instead, we prove the SPECIFIC instances needed for type preservation:
substitutability and COMM preservation, expressed using change-of-base.

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §5
- Jacobs, "Categorical Logic and Type Theory" Ch. 1, §1.9 (Beck-Chevalley)
- Williams & Stay, "Native Type Theory" (ACT 2021) §3
-/

namespace Mettapedia.OSLF.Framework.BeckChevalleyOSLF

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.ConstructorFibration
open Mettapedia.OSLF.Framework.ModalEquivalence
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.RhoCalculus.Soundness
open Mettapedia.OSLF.RhoCalculus.Reduction (possiblyProp)

/-! ## Composition of Galois Connections

The key tool for combining the substitution and modal adjunctions.
If `f ⊣ g` and `h ⊣ k`, then `h ∘ f ⊣ g ∘ k`. -/

/-- Composing two Galois connections yields a Galois connection.

    If `l₁ ⊣ u₁` and `l₂ ⊣ u₂` (where `u₁` and `l₂` are composable),
    then `l₂ ∘ l₁ ⊣ u₁ ∘ u₂`.

    Proof: `l₂(l₁(a)) ≤ c ↔ l₁(a) ≤ u₂(c) ↔ a ≤ u₁(u₂(c))`. -/
theorem galoisConnection_comp [Preorder α] [Preorder β] [Preorder γ]
    {l₁ : α → β} {u₁ : β → α} {l₂ : β → γ} {u₂ : γ → β}
    (gc₁ : GaloisConnection l₁ u₁) (gc₂ : GaloisConnection l₂ u₂) :
    GaloisConnection (l₂ ∘ l₁) (u₁ ∘ u₂) :=
  fun a c => (gc₂ (l₁ a) c).trans (gc₁ a (u₂ c))

/-! ## Substitution-Induced Change-of-Base

The COMM rule substitution `commSubst pBody q = openBVar 0 (NQuote q) pBody`
is a function `Pattern → Pattern`. Like any function between sets, it induces
the adjoint triple `∃_σ ⊣ σ* ⊣ ∀_σ` via the generic Set-level change-of-base
from DerivedModalities.lean. -/

/-- The COMM substitution map (function of the body, with q fixed). -/
def commMap (q : Pattern) : Pattern → Pattern :=
  fun pBody => commSubst pBody q

/-- `commMap` unfolds to `openBVar 0 (NQuote q) ·`. -/
theorem commMap_def (q pBody : Pattern) :
    commMap q pBody = openBVar 0 (.apply "NQuote" [q]) pBody := rfl

/-- Pullback along COMM substitution: `σ*(φ)(p) = φ(commSubst p q)`. -/
def commPb (q : Pattern) : (Pattern → Prop) → (Pattern → Prop) := pb (commMap q)

/-- Direct image: `∃_σ(ψ)(r) = ∃ p, commSubst p q = r ∧ ψ p`. -/
def commDi (q : Pattern) : (Pattern → Prop) → (Pattern → Prop) := di (commMap q)

/-- Universal image: `∀_σ(ψ)(r) = ∀ p, commSubst p q = r → ψ p`. -/
def commUi (q : Pattern) : (Pattern → Prop) → (Pattern → Prop) := ui (commMap q)

/-- `∃_σ ⊣ σ*` for the COMM substitution. -/
theorem comm_di_pb_adj (q : Pattern) : GaloisConnection (commDi q) (commPb q) :=
  di_pb_adj (commMap q)

/-- `σ* ⊣ ∀_σ` for the COMM substitution. -/
theorem comm_pb_ui_adj (q : Pattern) : GaloisConnection (commPb q) (commUi q) :=
  pb_ui_adj (commMap q)

/-- COMM pullback unfolds. -/
theorem commPb_apply (q : Pattern) (φ : Pattern → Prop) (pBody : Pattern) :
    commPb q φ pBody = φ (commSubst pBody q) := rfl

/-- COMM direct image unfolds. -/
theorem commDi_apply (q : Pattern) (ψ : Pattern → Prop) (r : Pattern) :
    commDi q ψ r = (∃ p, commSubst p q = r ∧ ψ p) := rfl

/-! ## Composed Galois Connections: Modal + Substitution

The modal adjunction `◇ ⊣ □` (from TypeSynthesis) and the substitution
adjunction `∃_σ ⊣ σ*` compose to give new Galois connections. These
capture the combined effect of reduction modalities and substitution. -/

variable (lang : LanguageDef)

/-- `◇ ∘ ∃_σ ⊣ σ* ∘ □`: Diamond composed with substitution direct image.

    `langDiamond(∃_σ(φ)) ≤ ψ  ↔  φ ≤ σ*(□ψ)`

    "It's possible to reduce from some COMM-image satisfying φ to reach ψ"
    iff "φ is bounded by the pullback of box-ψ along the COMM substitution." -/
theorem diamond_commDi_galois (q : Pattern) :
    GaloisConnection (langDiamond lang ∘ commDi q) (commPb q ∘ langBox lang) :=
  galoisConnection_comp (comm_di_pb_adj q) (langGalois lang)

/-- `∃_σ ∘ ◇ ⊣ □ ∘ σ*`: Substitution direct image composed with diamond.

    `∃_σ(◇φ) ≤ ψ  ↔  φ ≤ □(σ*(ψ))`

    "The COMM-image of diamond-φ is bounded by ψ"
    iff "φ is bounded by box of the pullback of ψ along COMM." -/
theorem commDi_diamond_galois (q : Pattern) :
    GaloisConnection (commDi q ∘ langDiamond lang) (langBox lang ∘ commPb q) :=
  galoisConnection_comp (langGalois lang) (comm_di_pb_adj q)

/-! ## Properties of COMM Change-of-Base -/

/-- COMM pullback is monotone. -/
theorem commPb_mono (q : Pattern) : Monotone (commPb q) :=
  (comm_di_pb_adj q).monotone_u

/-- COMM direct image is monotone. -/
theorem commDi_mono (q : Pattern) : Monotone (commDi q) :=
  (comm_di_pb_adj q).monotone_l

/-- COMM pullback preserves ⊤: `σ*(⊤) = ⊤`. -/
theorem commPb_top (q : Pattern) : commPb q ⊤ = ⊤ := rfl

/-- COMM pullback preserves ⊓: `σ*(φ ⊓ ψ) = σ*(φ) ⊓ σ*(ψ)`. -/
theorem commPb_inf (q : Pattern) (φ ψ : Pattern → Prop) :
    commPb q (φ ⊓ ψ) = commPb q φ ⊓ commPb q ψ := rfl

/-- COMM direct image preserves ⊥: `∃_σ(⊥) = ⊥`. -/
theorem commDi_bot (q : Pattern) : commDi q ⊥ = ⊥ :=
  funext fun _ => propext ⟨fun ⟨_, _, h⟩ => h, False.elim⟩

/-! ## TypedAt Predicate

The "typed at" predicate turns the typing judgment into a predicate on patterns,
allowing us to express substitutability using change-of-base vocabulary. -/

/-- The set of patterns typeable at a given context and type.

    `typedAt Γ τ p ↔ HasType Γ p τ` -/
def typedAt (Γ : TypingContext) (τ : NativeType) : Pattern → Prop :=
  fun p => HasType Γ p τ

/-! ## Substitutability as Change-of-Base

The substitutability theorem — the fundamental property of the ρ-calculus
type system — expressed as a pullback inequality. This is the operational
content of Beck-Chevalley for OSLF. -/

/-- **Substitutability as pullback inequality** (OSLF Beck-Chevalley, Main Form).

    If `Γ ⊢ q : σ` (with q subst-free and locally closed), then the
    extended-context typing predicate is contained in the pullback of the
    base-context typing predicate along substitution:

    `typedAt(Γ.extend x σ, τ) ≤ σ_q*(typedAt(Γ, τ))`

    In words: every p typeable in the extended context has its substitution
    `p[q/x]` typeable in the base context with the same type.

    This is the operational Beck-Chevalley: "substitution commutes with typing". -/
theorem substitutability_pb
    {Γ : TypingContext} {τ : NativeType}
    {x : String} {q : Pattern} {σ : NativeType}
    (hq : HasType Γ q σ)
    (hnes : noExplicitSubst q = true)
    (hlc : lc q = true) :
    typedAt (Γ.extend x σ) τ ≤
    pb (applySubst (SubstEnv.extend SubstEnv.empty x q)) (typedAt Γ τ) :=
  fun _ hp => substitutability hp hq hnes hlc

/-- **Adjoint form**: the direct image of the extended-context typed terms
    along substitution is contained in the base-context typed terms.

    `∃_{σ_q}(typedAt(Γ.extend x σ, τ)) ≤ typedAt(Γ, τ)`

    "Every substitution image of an extended-context typeable term is
    base-context typeable." This follows from `substitutability_pb` via
    the `∃_f ⊣ f*` adjunction: `∃_f(α) ≤ β ↔ α ≤ f*(β)`. -/
theorem substitutability_di
    {Γ : TypingContext} {τ : NativeType}
    {x : String} {q : Pattern} {σ : NativeType}
    (hq : HasType Γ q σ)
    (hnes : noExplicitSubst q = true)
    (hlc : lc q = true) :
    di (applySubst (SubstEnv.extend SubstEnv.empty x q)) (typedAt (Γ.extend x σ) τ) ≤
    typedAt Γ τ :=
  (di_pb_adj _).l_le (substitutability_pb hq hnes hlc)

/-! ## COMM Type Preservation as Change-of-Base

The COMM rule's type preservation expressed using the change-of-base vocabulary.
This is the key theorem connecting the operational typing to the categorical
framework. -/

/-- **COMM Beck-Chevalley**: The COMM rule preserves types, expressed as a
    change-of-base property.

    Given body typing (cofinite quantification) and argument typing, the
    COMM substitution result is typeable. In change-of-base terms: the
    COMM substitution map `commMap q` preserves the body's typing predicate.

    This is the operational Beck-Chevalley for the ρ-calculus: it states
    that the specific substitution arising from the COMM rule is compatible
    with the typing judgment. -/
theorem comm_beck_chevalley
    {Γ : TypingContext} {pBody q : Pattern}
    {φ : Pattern → Prop}
    {L : List String}
    (hbody : ∀ z, z ∉ L →
      HasType (Γ.extend z ⟨"Name", possiblyProp (fun _ => True), by simp⟩)
        (openBVar 0 (.fvar z) pBody) ⟨"Proc", φ, by simp⟩)
    (hq : HasType Γ q ⟨"Proc", fun _ => True, by simp⟩)
    (hlc_q : lc q = true) :
    typedAt Γ ⟨"Proc", φ, by simp⟩ (commMap q pBody) :=
  comm_preserves_type hbody hq hlc_q

/-- The COMM pullback of the body predicate describes the set of well-typed
    bodies for the COMM rule with argument q.

    `commPb q (typedAt Γ (Proc, φ)) pBody ↔ Γ ⊢ commSubst pBody q : (Proc, φ)` -/
theorem commPb_typedAt (Γ : TypingContext) (q : Pattern) (φ : Pattern → Prop)
    (hsort : "Proc" ∈ rhoCalc.types) (pBody : Pattern) :
    commPb q (typedAt Γ ⟨"Proc", φ, hsort⟩) pBody =
    HasType Γ (commSubst pBody q) ⟨"Proc", φ, hsort⟩ := rfl

/-! ## NQuote Factoring of COMM Substitution

The COMM substitution factors through NQuote's semantic function:
`commMap q = openBVar 0 (arrowSem rhoCalc nquoteArrow q)`

This shows the COMM rule combines:
1. The NQuote constructor (structural: quote the argument)
2. Binder opening (operational: substitute into the body)

The NQuote part is the constructor change-of-base from Phase B;
the opening is the reduction substitution from the COMM rule. -/

/-- The COMM substitution factors through NQuote's arrow semantic. -/
theorem commMap_factors_nquote (q pBody : Pattern) :
    commMap q pBody = openBVar 0 (arrowSem rhoCalc nquoteArrow q) pBody := rfl

/-- The COMM substitution result is the body opened with the NQuote
    change-of-base applied to the argument.

    `commSubst pBody q = openBVar 0 (pathSem rhoCalc nquoteMor q) pBody`

    At the type level: if `q : (Proc, ψ)`, then `NQuote q : (Name, ◇ψ)`,
    and the body opened with `NQuote q` gets the body's type `(Proc, φ)`.
    The modal operator ◇ bridges the sort gap (Proc → Name). -/
theorem commSubst_eq_open_constructorSem (q pBody : Pattern) :
    commSubst pBody q = openBVar 0 (pathSem rhoCalc nquoteMor q) pBody := rfl

/-! ## General Substitution Change-of-Base Properties

For any function `σ : Pattern → Pattern`, the induced change-of-base
operations have standard Set-level properties. These are direct instantiations
of the DerivedModalities infrastructure. -/

/-- Pullback is contravariantly functorial: `(g ∘ f)* = f* ∘ g*`. -/
theorem subst_pb_comp (f g : Pattern → Pattern) (φ : Pattern → Prop) :
    pb (g ∘ f) φ = pb f (pb g φ) := rfl

/-- Direct image is covariantly functorial: `∃_{g∘f} = ∃_g ∘ ∃_f`. -/
theorem subst_di_comp (f g : Pattern → Pattern) (φ : Pattern → Prop) :
    di (g ∘ f) φ = di g (di f φ) := by
  funext x
  simp only [di, Function.comp]
  apply propext
  constructor
  · rintro ⟨e, hge, hφ⟩
    exact ⟨f e, hge, e, rfl, hφ⟩
  · rintro ⟨y, hgy, e, hfe, hφ⟩
    subst hfe
    exact ⟨e, hgy, hφ⟩

/-- The COMM substitution composed with NQuote's semantic:
    `commPb q ∘ constructorPullback NQuote = pb (fun p => NQuote(commSubst p q))`.

    This factoring shows how the COMM substitution and NQuote change-of-base compose. -/
theorem comm_nquote_pb_comp (q : Pattern) (φ : Pattern → Prop) :
    commPb q (constructorPullback rhoCalc nquoteMor φ) =
    pb (fun p => pathSem rhoCalc nquoteMor (commMap q p)) φ := rfl

/-! ## Counterexample: Strong Beck-Chevalley Fails

The GSLT `BeckChevalley` condition quantifies over ALL commuting squares.
For the constructor fibration, this fails because the constructor semantics
(`pathSem`) is not surjective — not every pattern is in the image of a
constructor arrow. We provide a concrete counterexample. -/

section Counterexample

open ConstructorCategory (rhoProcObj rhoNameObj nquoteMor pdropMor)

/-- The commuting square NQuote ∘ PDrop = NQuote ∘ PDrop (both sides are the
    same path Proc → Name → Proc, so they trivially commute). -/
private theorem comm_square :
    (nquoteMor.comp pdropMor : rhoProcObj ⟶ rhoProcObj) =
    (nquoteMor.comp pdropMor : rhoProcObj ⟶ rhoProcObj) := rfl

/-- For this commuting square, the LHS of Beck-Chevalley evaluates
    PDrop*(∃PDrop(φ))(p) = φ(p) when PDrop is injective as a constructor. -/
theorem bc_lhs_at_fvar (φ : Pattern → Prop) (x : String) :
    constructorPullback rhoCalc pdropMor
      (constructorDirectImage rhoCalc pdropMor φ)
      (.fvar x)
    = (∃ q, Pattern.apply "PDrop" [q] = Pattern.apply "PDrop" [.fvar x] ∧ φ q) := rfl

/-- For the same square, the RHS evaluates
    ∃NQuote(NQuote*(φ))(p) = (∃ q, NQuote(q) = p ∧ ...).
    At `p = .fvar x`, no pattern q satisfies `NQuote(q) = .fvar x`. -/
theorem bc_rhs_at_fvar (φ : Pattern → Prop) (x : String) :
    constructorDirectImage rhoCalc nquoteMor
      (constructorPullback rhoCalc nquoteMor φ)
      (.fvar x)
    = (∃ q, Pattern.apply "NQuote" [q] = Pattern.fvar x ∧
            φ (Pattern.apply "NQuote" [q])) := rfl

/-- No pattern `q` satisfies `NQuote(q) = FVar x`. -/
theorem nquote_ne_fvar (q : Pattern) (x : String) :
    Pattern.apply "NQuote" [q] ≠ Pattern.fvar x := Pattern.noConfusion

/-- The RHS of Beck-Chevalley is False at FVar x (no NQuote preimage). -/
theorem bc_rhs_false (φ : Pattern → Prop) (x : String) :
    ¬ constructorDirectImage rhoCalc nquoteMor
        (constructorPullback rhoCalc nquoteMor φ)
        (.fvar x) := by
  rintro ⟨q, habs, _⟩
  exact nquote_ne_fvar q x habs

/-- The LHS of Beck-Chevalley is True at FVar x (for φ = ⊤), because
    PDrop is injective as a Pattern constructor. -/
theorem bc_lhs_true (x : String) :
    constructorPullback rhoCalc pdropMor
      (constructorDirectImage rhoCalc pdropMor ⊤)
      (.fvar x) := by
  exact ⟨.fvar x, rfl, trivial⟩

/-- **Strong Beck-Chevalley fails for the constructor fibration.**

    For the commuting square NQuote ∘ PDrop = NQuote ∘ PDrop, the
    Beck-Chevalley identity `PDrop* ∘ ∃PDrop = ∃NQuote ∘ NQuote*` fails:
    the LHS is ⊤ at (.fvar x) while the RHS is ⊥.

    This motivates our approach of proving specific BC instances
    (substitutability, COMM preservation) rather than the strong universal form. -/
theorem strong_bc_fails :
    ¬ (∀ (φ : Pattern → Prop),
        constructorPullback rhoCalc pdropMor
          (constructorDirectImage rhoCalc pdropMor φ) =
        constructorDirectImage rhoCalc nquoteMor
          (constructorPullback rhoCalc nquoteMor φ)) := by
  intro h
  have := congr_fun (h ⊤) (.fvar "x")
  rw [show constructorPullback rhoCalc pdropMor
    (constructorDirectImage rhoCalc pdropMor ⊤) (.fvar "x") = True from
    propext ⟨fun _ => trivial, fun _ => bc_lhs_true "x"⟩] at this
  rw [show constructorDirectImage rhoCalc nquoteMor
    (constructorPullback rhoCalc nquoteMor ⊤) (.fvar "x") = False from
    propext ⟨fun h => bc_rhs_false ⊤ "x" h, False.elim⟩] at this
  exact this.mp trivial

end Counterexample

/-! ## Summary

**0 sorries. 0 axioms.**

### Key Results

1. **`galoisConnection_comp`**: Composing `l₁ ⊣ u₁` and `l₂ ⊣ u₂`
   gives `l₂ ∘ l₁ ⊣ u₁ ∘ u₂`.

2. **COMM change-of-base**: `commDi q ⊣ commPb q ⊣ commUi q` — the
   adjoint triple for the COMM substitution map.

3. **Composed adjunctions**: `◇ ∘ ∃_σ ⊣ σ* ∘ □` and `∃_σ ∘ ◇ ⊣ □ ∘ σ*`
   — combining modal operators with substitution.

4. **`substitutability_pb`**: `typedAt(Γ.extend x σ, τ) ≤ σ_q*(typedAt(Γ, τ))`
   — substitutability as a pullback inequality (the operational BC).

5. **`substitutability_di`**: `∃_{σ_q}(typedAt(Γ.extend x σ, τ)) ≤ typedAt(Γ, τ)`
   — the adjoint form.

6. **`comm_beck_chevalley`**: COMM type preservation as change-of-base.

7. **`commSubst_eq_open_constructorSem`**: The COMM substitution factors
   through NQuote's constructor semantic.

8. **`strong_bc_fails`**: The GSLT's strong Beck-Chevalley (all commuting
   squares) does NOT hold for the constructor fibration — motivating our
   approach of proving specific instances.

### Connection to Other Phases

- **Phase B** (ConstructorFibration): Provides `constructorPullback`,
  `constructorDirectImage`, and the `ChangeOfBase` instance.
- **Phase C** (ModalEquivalence): Provides `nquoteTypingAction = ◇`,
  `typing_action_galois`, connecting constructors to modalities.
- **Phase D** (DerivedTyping): Provides `DerivedHasType`, the generic
  typing judgment from change-of-base.
- **Soundness.lean**: Provides `substitutability` and `comm_preserves_type`,
  the operational theorems that this file lifts to categorical form.
-/

end Mettapedia.OSLF.Framework.BeckChevalleyOSLF
