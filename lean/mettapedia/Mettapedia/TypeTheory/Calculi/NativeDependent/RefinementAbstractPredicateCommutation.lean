import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPredicateInterpretation
import Mettapedia.TypeTheory.ContextualPredicateValueSubstitution

/-!
# Checked refinement and proposition readouts under substitution

The supplied guard retains its logical scope. Reindexing uses the actual
model self-extension square, ordinary proposition substitution and the local
refinement operations. Complete values retain their annotations and witnesses;
no commutation law for the whole syntax is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualModelTelescopes
open ContextualTypeOperations ContextualProductComparison
open External (bindResult)

universe a c s t m p
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
variable {localModel : LocalModel.{c, s, t, m, p} C}
variable {source target : C.toCwf.Ctx}

namespace ModelData

abbrev substituteProposition
    (operations : ContextualPredicateCapabilities.PropositionOperations localModel.doctrine)
    (σ : C.toCwf.Sub source target) (value : C.toCwf.Tm target (operations.omega target)) :=
  ContextualPredicateValueSubstitution.PropositionOperations.substitute operations σ value

abbrev substituteRefinement
    (operations : ContextualPredicateCapabilities.RefinementOperations localModel.doctrine)
    (σ : C.toCwf.Sub source target) (A : C.toCwf.Ty target)
    (predicate : localModel.doctrine.Predicate (C.toCwf.ext target A))
    (value : C.toCwf.Tm target (operations.refined A predicate)) :=
  ContextualPredicateValueSubstitution.RefinementOperations.substitute operations σ A predicate value

theorem proposition_value_substitute (σ : C.toCwf.Sub source target)
    (value : C.toCwf.Tm target (localModel.propositions.omega target)) :
    Value.substitute (⟨localModel.propositions.omega target, value⟩ : Value C.toCwf target) σ =
      ⟨localModel.propositions.omega source, substituteProposition localModel.propositions σ value⟩ :=
  ContextualPredicateValueSubstitution.PropositionOperations.value_substitute _ _ _

theorem quote_value_substitute (σ : C.toCwf.Sub source target)
    (predicate : localModel.doctrine.Predicate target) :
    Value.substitute (⟨localModel.propositions.omega target, localModel.propositions.quote predicate⟩ :
      Value C.toCwf target) σ =
      ⟨localModel.propositions.omega source,
        localModel.propositions.quote (localModel.doctrine.reindex σ predicate)⟩ :=
  ContextualPredicateValueSubstitution.PropositionOperations.quote_value_substitute _ _ _

theorem refinement_value_substitute (σ : C.toCwf.Sub source target)
    (A : C.toCwf.Ty target) (predicate : localModel.doctrine.Predicate (C.toCwf.ext target A))
    (value : C.toCwf.Tm target (localModel.refinements.refined A predicate)) :
    Value.substitute (⟨localModel.refinements.refined A predicate, value⟩ : Value C.toCwf target) σ =
      ⟨localModel.refinements.refined (C.toCwf.tySub A σ)
          (localModel.doctrine.reindex (TypeOver.extensionSubstitution σ A) predicate),
        substituteRefinement localModel.refinements σ A predicate value⟩ :=
  ContextualPredicateValueSubstitution.RefinementOperations.value_substitute _ _ _ _ _

theorem refine?_supplied (A : C.toCwf.Ty target)
    (predicate : localModel.doctrine.Predicate (C.toCwf.ext target A)) (value : C.toCwf.Tm target A)
    (guard : localModel.doctrine.reindex (selfExtend C.toCwf value) predicate = ⊤) :
    refine? localModel A predicate (some ⟨A, value⟩) =
      some ⟨localModel.refinements.refined A predicate, localModel.refinements.intro A predicate value guard⟩ := by
  rw [refine?, check?_supplied]
  simp only [bindResult, dif_pos guard]

theorem refine?_rejected (A : C.toCwf.Ty target)
    (predicate : localModel.doctrine.Predicate (C.toCwf.ext target A)) (value : C.toCwf.Tm target A)
    (rejected : localModel.doctrine.reindex (selfExtend C.toCwf value) predicate ≠ ⊤) :
    refine? localModel A predicate (some ⟨A, value⟩) = none := by
  rw [refine?, check?_supplied]
  simp only [bindResult, dif_neg rejected]

theorem refine?_eq_some_iff (localModel : LocalModel.{c, s, t, m, p} C)
    (A : C.toCwf.Ty target) (predicate : localModel.doctrine.Predicate (C.toCwf.ext target A))
    (result : Option (Value C.toCwf target)) (output : Value C.toCwf target) :
    refine? localModel A predicate result = some output ↔
      ∃ (value : C.toCwf.Tm target A),
        ∃ (guard : localModel.doctrine.reindex (selfExtend C.toCwf value) predicate = ⊤),
          result = some ⟨A, value⟩ ∧
            ⟨localModel.refinements.refined A predicate, localModel.refinements.intro A predicate value guard⟩ =
              output := by
  classical
  constructor
  · intro read
    rw [refine?] at read
    rcases (External.bindResult_eq_some_iff _ _ _).mp read with ⟨value, checked, rest⟩
    have resultRead := (check?_eq_some_iff _ _ _).mp checked
    split_ifs at rest with guard
    · exact ⟨value, guard, resultRead, Option.some.inj rest⟩
  · rintro ⟨value, guard, resultRead, outputRead⟩
    rw [resultRead, refine?_supplied A predicate value guard, outputRead]

theorem forget?_supplied (A : C.toCwf.Ty target)
    (predicate : localModel.doctrine.Predicate (C.toCwf.ext target A))
    (value : C.toCwf.Tm target (localModel.refinements.refined A predicate)) :
    forget? localModel A predicate (some ⟨localModel.refinements.refined A predicate, value⟩) =
      some ⟨A, localModel.refinements.forget A predicate value⟩ := by
  rw [forget?, check?_supplied]
  rfl

theorem refine?_substitution (σ : C.toCwf.Sub source target) (A : C.toCwf.Ty target)
    (predicate : localModel.doctrine.Predicate (C.toCwf.ext target A)) (value : C.toCwf.Tm target A)
    (guard : localModel.doctrine.reindex (selfExtend C.toCwf value) predicate = ⊤) :
    (refine? localModel A predicate (some ⟨A, value⟩)).map (fun value => Value.substitute value σ) =
      refine? localModel (C.toCwf.tySub A σ)
        (localModel.doctrine.reindex (TypeOver.extensionSubstitution σ A) predicate)
          (some (Value.substitute (⟨A, value⟩ : Value C.toCwf target) σ)) := by
  rw [refine?_supplied A predicate value guard, Option.map_some]
  change some _ = refine? localModel (C.toCwf.tySub A σ) _
    (some ⟨C.toCwf.tySub A σ, C.toCwf.tmSub value σ⟩)
  rw [refine?_supplied _ _ _
    (ContextualPredicateValueSubstitution.RefinementOperations.substituted_guard σ A predicate value guard)]
  exact congrArg some
    (ContextualPredicateValueSubstitution.RefinementOperations.introduction_value_substitute _ _ _ _ _ _)

theorem forget?_substitution (σ : C.toCwf.Sub source target) (A : C.toCwf.Ty target)
    (predicate : localModel.doctrine.Predicate (C.toCwf.ext target A))
    (value : C.toCwf.Tm target (localModel.refinements.refined A predicate)) :
    (forget? localModel A predicate (some ⟨localModel.refinements.refined A predicate, value⟩)).map
      (fun value => Value.substitute value σ) =
      forget? localModel (C.toCwf.tySub A σ)
        (localModel.doctrine.reindex (TypeOver.extensionSubstitution σ A) predicate)
          (some ⟨_, substituteRefinement localModel.refinements σ A predicate value⟩) := by
  rw [forget?_supplied, forget?_supplied, Option.map_some]
  exact congrArg some
    (ContextualPredicateValueSubstitution.RefinementOperations.forgetting_value_substitute _ _ _ _ _)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
