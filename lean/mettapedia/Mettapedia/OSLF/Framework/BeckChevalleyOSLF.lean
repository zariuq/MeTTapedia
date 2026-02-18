import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.GSLT.Topos.PredicateFibration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness

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
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction (possiblyProp)

/-! ## Presheaf Beck–Chevalley Transport into OSLF Layer

This theorem makes the presheaf-topos Beck–Chevalley result available directly
from the OSLF framework layer, so substitution/rewrite theorems in this module
can cite the same base-change law without dropping back to `GSLT/Topos`.
-/

/-- OSLF-layer transport of the generic presheaf Beck–Chevalley theorem.

Reference:
- `GSLT.Topos.PredicateFibration.beckChevalleyCondition_presheafChangeOfBase`. -/
theorem presheafPrimary_beckChevalley_transport
    (C : Type _) [CategoryTheory.Category C] :
    Mettapedia.GSLT.Topos.BeckChevalleyCondition
      (Mettapedia.GSLT.Topos.presheafPredicateFib (C := C))
      (Mettapedia.GSLT.Topos.presheafChangeOfBase (C := C)) := by
  exact
    (Mettapedia.GSLT.Topos.beckChevalleyCondition_presheafChangeOfBase (C := C))

/-- Direct OSLF-layer Beck–Chevalley square corollary over presheaf subobjects.

This uses the concrete presheaf pullback/map square theorem directly (not
through `BeckChevalleyCondition` transport wrappers). -/
theorem presheaf_beckChevalley_square_direct
    (C : Type _) [CategoryTheory.Category C]
    {P A B D : CategoryTheory.Functor (Opposite C) (Type _)}
    (pi1 : P ⟶ A) (pi2 : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (φ : CategoryTheory.Subobject A) :
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj φ)
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj φ) := by
  letI : CategoryTheory.Mono f := hf
  letI : CategoryTheory.Mono pi2 := hpi2
  simpa using
    (Mettapedia.GSLT.Topos.beckChevalleyPresheaf
      (C := C) pi1 pi2 f g hpb φ)

/-- Representable-object Beck–Chevalley corollary for predicates obtained from
`Pattern → Prop` via `languageSortFiber_ofPatternPred`.

This is the first bridge from executable-style predicates (`Pattern → Prop`) to
the representable-fiber (`Sub(y(s))`) BC path in the language-presheaf lift. -/
theorem representable_patternPred_beckChevalley
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed φ)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2) :
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed φ hNat))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed φ hNat)) := by
  exact presheaf_beckChevalley_square_direct
    (C := ConstructorObj lang)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (φ := Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
      lang s seed φ hNat)

/-- OSLF-layer bridge: `◇` can be read over the internal presheaf reduction
graph (`E`,`source`,`target`) built in `ToposReduction`.

This keeps the substitution/rewrite path on the graph object rather than only
the binary relation presentation. -/
theorem langDiamondUsing_graph_transport
    (C : Type _) [CategoryTheory.Category C]
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (lang : LanguageDef) {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langDiamondUsing relEnv lang φ p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).source.app X e).down = p ∧
        φ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).target.app X e).down) := by
  simpa using
    (Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphStep
      (C := C) (relEnv := relEnv) (lang := lang) (X := X) (φ := φ) (p := p))

/-- OSLF-layer bridge: `□` can be read over incoming edges in the internal
presheaf reduction graph (`E`,`source`,`target`) built in `ToposReduction`. -/
theorem langBoxUsing_graph_transport
    (C : Type _) [CategoryTheory.Category C]
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (lang : LanguageDef) {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langBoxUsing relEnv lang φ p ↔
      ∀ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).target.app X e).down = p →
        φ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).source.app X e).down) := by
  simpa using
    (Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphIncoming
      (C := C) (relEnv := relEnv) (lang := lang) (X := X) (φ := φ) (p := p))

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

/-- Representable-fiber Beck-Chevalley instance specialized to the
COMM substitution direct image predicate `commDi q φ`.

This is a substitution/rewrite BC theorem directly over language-presheaf
representables, instantiated from `representable_patternPred_beckChevalley`. -/
theorem representable_commDi_patternPred_beckChevalley
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hNatComm :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed (commDi q φ))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2) :
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ) hNatComm))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ) hNatComm)) := by
  exact representable_patternPred_beckChevalley
    (lang := lang) (s := s) (seed := seed) (φ := commDi q φ)
    (hNat := hNatComm) (pi1 := pi1) (pi2 := pi2)
    (f := f) (g := g) (hpb := hpb) (hf := hf) (hpi2 := hpi2)

/-- Derived COMM representable Beck–Chevalley corollary from the named
structural lifting condition.

This avoids passing a bespoke naturality proof manually: naturality of
`commDi q φ` is synthesized via
`CategoryBridge.languageSortPredNaturality_commDi`. -/
theorem representable_commDi_patternPred_beckChevalley_of_lifting
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLift :
      Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting
        lang s seed q φ)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2) :
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q φ hLift)))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q φ hLift))) := by
  exact representable_commDi_patternPred_beckChevalley
    (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
    (hNatComm :=
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
        lang s seed q φ hLift)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)

/-- `representable_commDi_patternPred_beckChevalley` with naturality derived via
the path-based lifting constructor (`commDiWitnessLifting_of_pathSemLift`). -/
theorem representable_commDi_patternPred_beckChevalley_of_pathSemLift
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLiftEq :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s)
        {u : Pattern},
          commSubst u q = pathSem lang h seed →
          commSubst (pathSem lang g u) q = pathSem lang (g.comp h) seed)
    (hClosed :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) {u : Pattern},
          φ u → φ (pathSem lang g u))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2) :
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q φ
              (Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLift
                lang s seed q φ hLiftEq hClosed))))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q φ
              (Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLift
                lang s seed q φ hLiftEq hClosed)))) := by
  exact representable_commDi_patternPred_beckChevalley_of_lifting
    (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
    (hLift :=
      Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLift
        lang s seed q φ hLiftEq hClosed)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)

/-- `representable_commDi_patternPred_beckChevalley` with naturality derived via
canonical path-semantics closure (`PathSemClosedPred`).

This consumes only the witness-transport equation (`hLiftEq`); closure is
discharged by `commDiWitnessLifting_of_pathSemClosed`. -/
theorem representable_commDi_patternPred_beckChevalley_of_pathSemClosed
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLiftEq :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s)
        {u : Pattern},
          commSubst u q = pathSem lang h seed →
          commSubst (pathSem lang g u) q = pathSem lang (g.comp h) seed)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2) :
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ))
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ)
              (Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemClosed
                lang s seed q φ hLiftEq))))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ))
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ)
              (Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemClosed
                lang s seed q φ hLiftEq)))) := by
  exact representable_commDi_patternPred_beckChevalley_of_lifting
    (lang := lang) (s := s) (seed := seed) (q := q)
    (φ := Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ)
    (hLift :=
      Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemClosed
        lang s seed q φ hLiftEq)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)

/-- Package form of `representable_commDi_patternPred_beckChevalley_of_pathSemClosed`. -/
theorem representable_commDi_patternPred_beckChevalley_of_pathSemLiftPkg
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hPkg :
      Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
        lang s seed q)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2) :
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ))
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ hPkg)))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ))
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ hPkg))) := by
  exact representable_commDi_patternPred_beckChevalley_of_pathSemClosed
    (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
    (hLiftEq := hPkg.liftEq)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)

/-- Graph-edge form of substitution/rewrite compatibility for COMM direct image.

This is an explicit graph-level formulation:
`◇ (∃_{comm} φ)` holds at `p` iff there is an internal reduction edge from `p`
to some target that is a COMM-substitution image of a `φ`-state. -/
theorem commDi_diamond_graph_step_iff
    (C : Type _) [CategoryTheory.Category C]
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (lang : LanguageDef) {X : Opposite C}
    (q p : Pattern) (φ : Pattern → Prop) :
    langDiamondUsing relEnv lang (commDi q φ) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).source.app X e).down = p ∧
        ∃ u : Pattern,
          commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := C) relEnv lang).target.app X e).down ∧
          φ u := by
  rw [langDiamondUsing_graph_transport (C := C) (relEnv := relEnv) (lang := lang)
    (X := X) (φ := commDi q φ) (p := p)]
  constructor
  · rintro ⟨e, hs, hcomm⟩
    rcases (by simpa [commDi_apply] using hcomm) with ⟨u, hu, hφ⟩
    exact ⟨e, hs, u, hu, hφ⟩
  · rintro ⟨e, hs, u, hu, hφ⟩
    refine ⟨e, hs, ?_⟩
    exact (by simpa [commDi_apply] using (show ∃ u : Pattern,
      commSubst u q =
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).target.app X e).down ∧ φ u from ⟨u, hu, hφ⟩))

/-- One-step composition theorem: representable COMM-BC plus graph-`◇` form.

This packages the representable Beck–Chevalley specialization for COMM
direct-image predicates together with the graph-edge characterization of
`langDiamondUsing (commDi q φ)` in one theorem. -/
theorem representable_commDi_bc_and_graphDiamond
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hNatComm :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed (commDi q φ))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    {X : Opposite (ConstructorObj lang)} (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ) hNatComm))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ) hNatComm)))
    ∧
    (langDiamondUsing relEnv lang (commDi q φ) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app X e).down = p ∧
        ∃ u : Pattern,
          commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app X e).down ∧
          φ u) := by
  refine ⟨?_, ?_⟩
  · exact representable_commDi_patternPred_beckChevalley
      (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
      (hNatComm := hNatComm) (pi1 := pi1) (pi2 := pi2)
      (f := f) (g := g) (hpb := hpb) (hf := hf) (hpi2 := hpi2)
  · simpa using
      (commDi_diamond_graph_step_iff
        (C := ConstructorObj lang) (relEnv := relEnv) (lang := lang)
        (X := X) (q := q) (p := p) (φ := φ))

/-- `representable_commDi_bc_and_graphDiamond` with naturality synthesized from
`commDiWitnessLifting`. -/
theorem representable_commDi_bc_and_graphDiamond_of_lifting
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLift :
      Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting
        lang s seed q φ)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    {X : Opposite (ConstructorObj lang)} (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q φ hLift)))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q φ hLift))))
    ∧
    (langDiamondUsing relEnv lang (commDi q φ) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app X e).down = p ∧
        ∃ u : Pattern,
          commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app X e).down ∧
          φ u) := by
  exact representable_commDi_bc_and_graphDiamond
    (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
    (hNatComm :=
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
        lang s seed q φ hLift)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (relEnv := relEnv) (X := X) (p := p)

/-- `representable_commDi_bc_and_graphDiamond` with naturality derived via the
path-based lifting constructor (`commDiWitnessLifting_of_pathSemLift`). -/
theorem representable_commDi_bc_and_graphDiamond_of_pathSemLift
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLiftEq :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s)
        {u : Pattern},
          commSubst u q = pathSem lang h seed →
          commSubst (pathSem lang g u) q = pathSem lang (g.comp h) seed)
    (hClosed :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) {u : Pattern},
          φ u → φ (pathSem lang g u))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    {X : Opposite (ConstructorObj lang)} (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q φ
              (Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLift
                lang s seed q φ hLiftEq hClosed))))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q φ
              (Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLift
                lang s seed q φ hLiftEq hClosed)))))
    ∧
    (langDiamondUsing relEnv lang (commDi q φ) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app X e).down = p ∧
        ∃ u : Pattern,
          commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app X e).down ∧
          φ u) := by
  exact representable_commDi_bc_and_graphDiamond_of_lifting
    (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
    (hLift :=
      Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLift
        lang s seed q φ hLiftEq hClosed)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (relEnv := relEnv) (X := X) (p := p)

/-- `representable_commDi_bc_and_graphDiamond` with naturality derived via
canonical path-semantics closure (`PathSemClosedPred`).

This consumes only the witness-transport equation (`hLiftEq`) and packages both:
1. the representable-fiber BC square for `commDi`,
2. the graph-edge `◇` compatibility shape.
-/
theorem representable_commDi_bc_and_graphDiamond_of_pathSemClosed
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLiftEq :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s)
        {u : Pattern},
          commSubst u q = pathSem lang h seed →
          commSubst (pathSem lang g u) q = pathSem lang (g.comp h) seed)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    {X : Opposite (ConstructorObj lang)} (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed
              (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ))
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ)
              (Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemClosed
                lang s seed q φ hLiftEq))))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed
              (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ))
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              lang s seed q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ)
              (Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemClosed
                lang s seed q φ hLiftEq)))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ)) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app X e).down = p ∧
        ∃ u : Pattern,
          commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app X e).down ∧
          Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ u) := by
  exact representable_commDi_bc_and_graphDiamond_of_lifting
    (lang := lang) (s := s) (seed := seed) (q := q)
    (φ := Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ)
    (hLift :=
      Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemClosed
        lang s seed q φ hLiftEq)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (relEnv := relEnv) (X := X) (p := p)

/-- Package form of `representable_commDi_bc_and_graphDiamond_of_pathSemClosed`. -/
theorem representable_commDi_bc_and_graphDiamond_of_pathSemLiftPkg
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hPkg :
      Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
        lang s seed q)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    {X : Opposite (ConstructorObj lang)} (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed
              (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ))
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ hPkg)))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            lang s seed
              (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ))
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ hPkg))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi q (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ)) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app X e).down = p ∧
        ∃ u : Pattern,
          commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app X e).down ∧
          Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred lang φ u) := by
  exact representable_commDi_bc_and_graphDiamond_of_pathSemClosed
    (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
    (hLiftEq := hPkg.liftEq)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (relEnv := relEnv) (X := X) (p := p)

/-- Specialized rho-Proc version of the path-lift BC+graph theorem, consuming
the concrete package `rho_proc_pathSemLift_pkg`. -/
theorem rhoProc_commDi_bc_and_graphDiamond_of_pathSemLift_pkg
    (seed q : Pattern)
    (φ : Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred)
    (hPkg : Mettapedia.OSLF.Framework.CategoryBridge.rho_proc_pathSemLift_pkg seed q φ)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj rhoCalc)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        rhoCalc rhoProc))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        rhoCalc rhoProc) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    {X : Opposite (ConstructorObj rhoCalc)} (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            rhoCalc rhoProc seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              rhoCalc rhoProc seed q φ
              (Mettapedia.OSLF.Framework.CategoryBridge.rho_proc_commDiWitnessLifting_of_pkg
                seed q φ hPkg))))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
            rhoCalc rhoProc seed (commDi q φ)
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
              rhoCalc rhoProc seed q φ
              (Mettapedia.OSLF.Framework.CategoryBridge.rho_proc_commDiWitnessLifting_of_pkg
                seed q φ hPkg)))))
    ∧
    (langDiamondUsing relEnv rhoCalc (commDi q φ) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj rhoCalc) relEnv rhoCalc).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj rhoCalc) relEnv rhoCalc).source.app X e).down = p ∧
        ∃ u : Pattern,
          commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj rhoCalc) relEnv rhoCalc).target.app X e).down ∧
          φ u) := by
  exact representable_commDi_bc_and_graphDiamond_of_pathSemLift
    (lang := rhoCalc) (s := rhoProc) (seed := seed) (q := q) (φ := φ)
    (hLiftEq := hPkg.1) (hClosed := hPkg.2)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (relEnv := relEnv) (X := X) (p := p)

/-- Substitution/rewrite square theorem stated directly over a packaged
`ReductionGraphObj`.

This is the graph-object form of COMM direct-image compatibility, independent
of the specific construction of edges/source/target. -/
theorem commDi_diamond_graphObj_square
    (C : Type _) [CategoryTheory.Category C]
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (lang : LanguageDef)
    (G : Mettapedia.OSLF.Framework.ToposReduction.ReductionGraphObj C relEnv lang)
    {X : Opposite C} (q p : Pattern) (φ : Pattern → Prop) :
    langDiamondUsing relEnv lang (commDi q φ) p ↔
      ∃ e : G.Edge.obj X,
        (G.source.app X e).down = p ∧
        ∃ u : Pattern, commSubst u q = (G.target.app X e).down ∧ φ u := by
  constructor
  · intro h
    rcases (langDiamondUsing_spec relEnv lang (commDi q φ) p).1 h with ⟨r, hred, hcomm⟩
    rcases (G.edge_endpoints_iff (X := X) (p := p) (q := r)).2 hred with ⟨e, hs, ht⟩
    rcases (by simpa [commDi_apply] using hcomm) with ⟨u, hu, hφ⟩
    refine ⟨e, hs, u, ?_, hφ⟩
    simpa [ht] using hu
  · rintro ⟨e, hs, u, hu, hφ⟩
    let r : Pattern := (G.target.app X e).down
    have hred : langReducesUsing relEnv lang p r :=
      (G.edge_endpoints_iff (X := X) (p := p) (q := r)).1 ⟨e, hs, rfl⟩
    refine (langDiamondUsing_spec relEnv lang (commDi q φ) p).2 ?_
    refine ⟨r, hred, ?_⟩
    have hcomm : ∃ t : Pattern, commSubst t q = r ∧ φ t := by
      refine ⟨u, ?_, hφ⟩
      simpa [r] using hu
    simpa [commDi_apply] using hcomm

/-- Graph-object substitution/rewrite square, proved through the graph-form
`◇` characterization over `ReductionGraphObj`.

This keeps the corollary in the OSLF graph layer rather than routing through
relation-transport wrappers. -/
theorem commDi_diamond_graphObj_square_direct
    (C : Type _) [CategoryTheory.Category C]
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (lang : LanguageDef)
    (G : Mettapedia.OSLF.Framework.ToposReduction.ReductionGraphObj C relEnv lang)
    {X : Opposite C} (q p : Pattern) (φ : Pattern → Prop) :
    langDiamondUsing relEnv lang (commDi q φ) p ↔
      ∃ e : G.Edge.obj X,
        (G.source.app X e).down = p ∧
        ∃ u : Pattern, commSubst u q = (G.target.app X e).down ∧ φ u := by
  rw [Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphObjStep
    (C := C) (relEnv := relEnv) (lang := lang) (G := G) (X := X)
    (φ := commDi q φ) (p := p)]
  constructor
  · rintro ⟨e, hs, hcomm⟩
    rcases (by simpa [commDi_apply] using hcomm) with ⟨u, hu, hφ⟩
    exact ⟨e, hs, u, hu, hφ⟩
  · rintro ⟨e, hs, u, hu, hφ⟩
    refine ⟨e, hs, ?_⟩
    exact (by
      simpa [commDi_apply] using
        (show ∃ t : Pattern, commSubst t q = (G.target.app X e).down ∧ φ t from
          ⟨u, hu, hφ⟩))

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
