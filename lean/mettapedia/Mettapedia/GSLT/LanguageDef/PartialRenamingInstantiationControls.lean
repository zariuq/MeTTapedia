import Mettapedia.GSLT.LanguageDef.PartialRenamingInstantiation
import Mettapedia.GSLT.LanguageDef.PartialRenamingControls

/-!
# Recovered bodies through actual contextual instantiation

The controls retain the existing LanguageDef-derived signature and assignments.
They exercise subset/permuted arguments, nested bodies, and instantiation into
an extension whose body still contains an unresolved metavariable.
-/

namespace Mettapedia.GSLT.LanguageDef.PartialRenamingInstantiationControls

open Mettapedia.OSLF.Binding Mettapedia.OSLF.MeTTaIL.Syntax
open MetaDependencyControls ScopedMatcherDependencyBoundary PartialRenamingControls
open WellSorted.OccurrenceControls (a)

set_option autoImplicit false

theorem subset_recovery_instantiates :
    instantiate usesArgument (rename oldArgument (metaVar dependentIndex)) =
      (.var (.succ .zero) : Term signature [a, a] a) :=
  (strengthenT_instantiate_metaVar_iff usesArgument dependentIndex oldArgument selectOld _).mp
    subset_variable_recovered

theorem permutation_recovery_instantiates :
    instantiate firstBody (rename swapArguments (metaVar binaryIndex)) =
      (.var (.succ .zero) : Term signature [a, a] a) :=
  (strengthenT_instantiate_metaVar_iff firstBody binaryIndex swapArguments inverseSwap _).mp
    permutation_variable_recovered

abbrev nestedDeclarations : List (MetaArity signature) := [([a], .arrow a a)]
abbrev nestedIndex : Fin nestedDeclarations.length := ⟨0, by decide⟩

def nestedAssignment : (i : Fin nestedDeclarations.length) →
    Term signature (nestedDeclarations.get i).1 (nestedDeclarations.get i).2 :=
  fun i => Fin.cases nestedBody (fun impossible => Fin.elim0 impossible) i

theorem nested_recovery_instantiates :
    instantiate nestedAssignment (rename oldArgument (metaVar nestedIndex)) = nestedSelected :=
  (strengthenT_instantiate_metaVar_iff nestedAssignment nestedIndex oldArgument selectOld _).mp
    subset_nested_recovered

/-- The returned body is consumed by the actual instantiated argument spine. -/
theorem nested_recovery_through_argsToSub :
    bind (argsToSub (instantiateArgs nestedAssignment
      (renameArgs oldArgument (idArgs (S := signature) (M := nestedDeclarations) [a]))))
      nestedBody = nestedSelected :=
  recovered_body_instantiates nestedAssignment oldArgument selectOld
    nestedSelected nestedBody subset_nested_recovered

theorem unsupported_target_has_no_instantiating_assignment :
    ¬ ∃ assignment : (i : Fin nestedDeclarations.length) →
        Term signature (nestedDeclarations.get i).1 (nestedDeclarations.get i).2,
      instantiate assignment (rename oldArgument (metaVar nestedIndex)) = nestedUnsupported := by
  rintro ⟨assignment, equality⟩
  have found :=
    (strengthenT_instantiate_metaVar_iff assignment nestedIndex oldArgument selectOld _).mpr equality
  rw [unsupported_nested_reference_declined] at found
  cases found

/-- A contextual body may itself retain a metavariable from another extension. -/
def residualBody : Term (withMetas signature declarations) [a] (.arrow a a) :=
  .op (.inl (.lambda a a))
    (.cons (rename oldArgument (metaVar dependentIndex)) .nil)

def residualAssignment : (i : Fin nestedDeclarations.length) →
    Term (withMetas signature declarations)
      (nestedDeclarations.get i).1 (nestedDeclarations.get i).2 :=
  fun i => Fin.cases residualBody (fun impossible => Fin.elim0 impossible) i

def residualTarget : Term (withMetas signature declarations) [a, a] (.arrow a a) :=
  .op (.inl (.lambda a a))
    (.cons (rename (fun _ v => .succ v)
      (rename oldArgument (metaVar dependentIndex))) .nil)

def residualInverse : Strengthener (S := withMetas signature declarations) oldArgument where
  un := selectOld.un
  un_rho := selectOld.un_rho
  rho_un := selectOld.rho_un

theorem residual_body_recovered :
    strengthenT residualInverse residualTarget =
      some residualBody := rfl

theorem residual_body_instantiates_into_extension :
    instInto residualAssignment (rename oldArgument (metaVar nestedIndex)) = residualTarget :=
  (strengthenT_instInto_metaVar_iff residualAssignment nestedIndex oldArgument residualInverse _).mp
    residual_body_recovered

end Mettapedia.GSLT.LanguageDef.PartialRenamingInstantiationControls
