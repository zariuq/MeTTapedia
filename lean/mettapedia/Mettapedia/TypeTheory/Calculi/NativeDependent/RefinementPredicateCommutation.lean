import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPredicateInterpretation
import Mettapedia.TypeTheory.PresheafNativePropositionSubstitution
import Mettapedia.TypeTheory.PresheafNativeRefinementTermSubstitution
import Mettapedia.TypeTheory.PresheafNativePredicateQuantifierSubstitution

/-!
# Actual proposition and refinement values under substitution

The equalities retain complete native annotations and supplied sections.
Propositions substitute by inverse image; refinement introduction substitutes
its original inhabitant and earns the new predicate membership. The chosen
native operations supply these laws independently of the syntax evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open ContextualModelTelescopes NativeLocalTypeFormers DisplayedPresheafComprehension
open PresheafNativePropositionReadout PresheafNativePropositionSubstitution
open PresheafNativeRefinementTermSubstitution PresheafNativeStableRefinement
open External (bindResult)

universe u v
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

namespace ModelData

attribute [local irreducible] PresheafNativeStableRefinement.chosen

set_option backward.isDefEq.respectTransparency false in
theorem proposition_value_substitute (σ : Q ⟶ P) (value : (nativeOmega P).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨nativeOmega P, value⟩ : NativeValue P) σ =
      ⟨nativeOmega Q, substituteNative σ value⟩ :=
  Sigma.ext (nativeOmega_reindex σ)
    (cast_heq (congrArg (fun type : NativeType Q => ↥type.decoded.sections)
      (nativeOmega_reindex σ))
      (ContextualLocalUniverses.substituteTerm (C := DisplayedPresheafCwf.presheafCwf C)
        (type := nativeOmega P) value σ)).symm

set_option backward.isDefEq.respectTransparency false in
theorem quote_value_substitute (σ : Q ⟶ P) (predicate : Subfunctor P) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨nativeOmega P, nativeQuote predicate⟩ : NativeValue P) σ =
      ⟨nativeOmega Q, nativeQuote (predicate.preimage σ)⟩ :=
  Sigma.ext (nativeOmega_reindex σ) (nativeQuote_substituteTerm σ predicate)

set_option backward.isDefEq.respectTransparency false in
theorem refinement_value_substitute (σ : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (value : (chosen A predicate).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨chosen A predicate, value⟩ : NativeValue P) σ =
      ⟨chosen (A.reindex σ) (predicate.preimage (totalReindexMap σ A.decoded)),
        substituteChosen σ A predicate value⟩ :=
  Sigma.ext (chosen_reindex σ A predicate)
    (cast_heq (congrArg (fun type : NativeType Q => ↥type.decoded.sections)
      (chosen_reindex σ A predicate))
      (ContextualLocalUniverses.substituteTerm (C := DisplayedPresheafCwf.presheafCwf C)
        (type := chosen A predicate) value σ)).symm

set_option backward.isDefEq.respectTransparency false in
theorem refine?_supplied (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (value : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world) :
    refine? A predicate (some ⟨A, value⟩) = some ⟨chosen A predicate, intro A predicate value satisfies⟩ := by
  rw [refine?, check?_supplied]
  simp only [bindResult, dif_pos satisfies]

set_option backward.isDefEq.respectTransparency false in
theorem refine?_rejected (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (value : A.decoded.sections)
    (fails : ¬ ∀ world (base : P.obj world),
      (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world) :
    refine? A predicate (some ⟨A, value⟩) = none := by
  rw [refine?, check?_supplied]
  simp only [bindResult, dif_neg fails]

theorem refine?_eq_some_iff (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (result : Option (NativeValue P)) (output : NativeValue P) :
    refine? A predicate result = some output ↔
      ∃ (value : A.decoded.sections), ∃ (satisfies : ∀ world (base : P.obj world),
        (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world),
        result = some ⟨A, value⟩ ∧ ⟨chosen A predicate, intro A predicate value satisfies⟩ = output := by
  classical
  constructor
  · intro read
    rw [refine?] at read
    rcases (External.bindResult_eq_some_iff _ _ _).mp read with ⟨value, checked, rest⟩
    have resultRead := (check?_eq_some_iff _ _ _).mp checked
    split_ifs at rest with satisfies
    · exact ⟨value, satisfies, resultRead, Option.some.inj rest⟩
  · rintro ⟨value, satisfies, resultRead, outputRead⟩
    rw [resultRead, refine?_supplied A predicate value satisfies, outputRead]

set_option backward.isDefEq.respectTransparency false in
theorem forget?_supplied (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (value : (chosen A predicate).decoded.sections) :
    forget? A predicate (some ⟨chosen A predicate, value⟩) =
      some ⟨A, forget A predicate value⟩ := by
  rw [forget?, check?_supplied]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem refine?_substitution (σ : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (value : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world) :
    (refine? A predicate (some ⟨A, value⟩)).map
      (fun value => Value.substitute (K := (NativeModel C).toCwf) value σ) =
      refine? (A.reindex σ) (predicate.preimage (totalReindexMap σ A.decoded))
        (some (Value.substitute (K := (NativeModel C).toCwf) (⟨A, value⟩ : NativeValue P) σ)) := by
  rw [refine?_supplied A predicate value satisfies, Option.map_some,
    refinement_value_substitute]
  change some ⟨_, substituteChosen σ A predicate (intro A predicate value satisfies)⟩ =
    refine? (A.reindex σ) _
      (some ⟨A.reindex σ, ContextualLocalUniverses.substituteTerm
        (C := DisplayedPresheafCwf.presheafCwf C) (type := A) value σ⟩)
  rw [refine?_supplied (A.reindex σ) _ _ (substitutedSatisfaction σ A predicate value satisfies)]
  exact congrArg (fun term => some (⟨_, term⟩ : NativeValue Q))
    (introduction_substitution σ A predicate value satisfies)

set_option backward.isDefEq.respectTransparency false in
theorem forget?_substitution (σ : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (value : (chosen A predicate).decoded.sections) :
    (forget? A predicate (some ⟨chosen A predicate, value⟩)).map
      (fun value => Value.substitute (K := (NativeModel C).toCwf) value σ) =
      forget? (A.reindex σ) (predicate.preimage (totalReindexMap σ A.decoded))
        (some ⟨_, substituteChosen σ A predicate value⟩) := by
  rw [forget?_supplied, forget?_supplied, Option.map_some]
  apply congrArg some
  exact Sigma.ext rfl (forget_substitution σ A predicate value)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
