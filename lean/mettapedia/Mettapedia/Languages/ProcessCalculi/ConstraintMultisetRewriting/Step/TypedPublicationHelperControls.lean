import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationCodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentParameterExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentProgramBoundaryControls

/-!
# Publication under actual helper exchange and binder substitution

The existing typed exchange applies to two declarations formed over the
same base. Code and its environment travel along that real substitution.
Exchanging twice recovers all source data. A lambda carrying an outer value
provides a concrete capture-sensitive control.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.HelperControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open ContextualDependentParameterExchange

variable {Head : Type} {rules : Rules Head} {base observer : Context rules}

theorem independent_exchange_twice (first second : TypeOver base) (code : Code (context first second)) :
    (code.reindex (swap second first)).reindex (swap first second) = code := by
  rw [Code.reindex_comp, swap_twice, Code.reindex_id]

theorem exchanged_readout (first second : TypeOver base) (code : Code (context first second))
    (substitution : observer ⟶ context second first)
    (licensed : (code.reindex (swap second first)).At substitution) :
    (code.reindex (swap second first)).readout substitution licensed =
      code.readout (substitution ≫ swap second first)
        ((code.at_reindex_iff (swap second first) substitution).mp licensed) :=
  code.readout_reindex (swap second first) substitution licensed

/-- The actual exchange fixes every old variable; reindexing an output is
therefore not permission to capture a name from the surrounding context. -/
theorem exchange_keeps_outer_variable (first second : TypeOver base) (index : Fin base.arity) :
    (swap first second).substitution index.succ.succ = .var index.succ.succ :=
  swap_older first second index

open DependentProgram.Controls

noncomputable def binderCode (context : Context Tower.rules) : Code (outputContext context) :=
  .value (Output.unchanged (DependentProgram.BoundaryControls.capturedFunction context))

theorem binder_license {context : Context Tower.rules} (baseMap : DependentFull.Controls.point ⟶ context) :
    (binderCode context).At (model baseMap) :=
  NativeTypesOnTheStep.below_refl_of_isType
    ((DependentProgram.BoundaryControls.capturedFunction context).1.reindex (model baseMap)).isType

theorem substituted_lambda_retains_outer_argument {context : Context Tower.rules}
    (baseMap : DependentFull.Controls.point ⟶ context) :
    ((binderCode context).readout (model baseMap) (binder_license baseMap)).2.code = .lam (.var 1) :=
  DependentProgram.BoundaryControls.instantiated_lambda_keeps_outer_variable baseMap

theorem substituted_lambda_is_not_captured {context : Context Tower.rules}
    (baseMap : DependentFull.Controls.point ⟶ context) :
    ((binderCode context).readout (model baseMap) (binder_license baseMap)).2.code ≠ .lam (.var 0) :=
  DependentProgram.BoundaryControls.instantiated_lambda_is_not_captured baseMap

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.HelperControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.HelperControls.independent_exchange_twice
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.HelperControls.substituted_lambda_is_not_captured
