import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineDiscovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineApplication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSupportControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalCheckingTower

/-!
# Three dependent binders, neutral eta, and future type instantiation

The telescope T:U0, x:T, p:Id T x x ends in Id T x x. Opening and
abstracting its actual proof argument preserve all dependencies. A supplied
identity witness is not identified with reflexivity. Reindexing T to Ground
changes the dependent types while keeping x and p rigid and open. Checked
discovery constructs the same three-argument shape from the declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiSpine.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiShape ContextualDependentScope

abbrev setting := ContextualDependentNormalSupport.Controls.setting
abbrev rigid := ContextualDependentNormalSupport.Controls.rigid_constants
abbrev normal := @ContextualDependentNormalSupport.Controls.stopped_normal
abbrev closed := empty Tower.rules
abbrev universeType := ContextualDependentInversion.Controls.universeType
abbrev types := ContextualDependentInversion.Controls.typeContext
abbrev element := ContextualDependentInversion.Controls.parameterType
abbrev values := ContextualDependentInversion.Controls.small

def identityType : TypeOver values :=
  ⟨.id (.var 1) (.var 0) (.var 0), .sort Tower.zero, .sort _, .idForm (.var 1) (.sort _) (.var 0) (.var 0)⟩
abbrev proofs := extend values identityType
def resultType := identityType.reindex (projectionHom values identityType)

def innerWhole : TypeOver values :=
  ⟨.pi identityType.code resultType.code, .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm identityType.formed identityType.universeWitness resultType.formed resultType.universeWitness (.sorts _ _)⟩
def inner : Shape values := ⟨identityType, resultType, innerWhole, rfl⟩

def middleWhole : TypeOver types :=
  ⟨.pi element.code innerWhole.code, .sort (.max Tower.zero (.max Tower.zero Tower.zero)), .sort _,
    .piForm element.formed element.universeWitness innerWhole.formed innerWhole.universeWitness (.sorts _ _)⟩
def middle : Shape types := ⟨element, innerWhole, middleWhole, rfl⟩

def outerWhole : TypeOver closed :=
  ⟨.pi universeType.code middleWhole.code, .sort (.max (.succ Tower.zero) (.max Tower.zero (.max Tower.zero Tower.zero))), .sort _,
    .piForm universeType.formed universeType.universeWitness middleWhole.formed middleWhole.universeWitness (.sorts _ _)⟩
def outer : Shape closed := ⟨universeType, middleWhole, outerWhole, rfl⟩

def tail : Spine middleWhole := .bind middle (.bind inner (.stop resultType))
def full : Spine outerWhole := .bind outer tail

def suppliedProof : Term full.target full.result := ⟨(.var 0 : Tower.Tm 3), .var (0 : Fin 3)⟩
def reflexivity : Term full.target full.result := ⟨(.refl (.var 1) : Tower.Tm 3), .reflIntro (.var (1 : Fin 3))⟩
def function := full.abstractBody suppliedProof
def reflexiveFunction := full.abstractBody reflexivity

theorem three_actual_dependent_binders : full.length = 3 ∧ full.target = proofs := by exact ⟨rfl, rfl⟩
theorem actual_abstraction : function.code = .lam (.lam (.lam (.var 0))) := rfl
theorem actual_dependent_result : full.result.code = (.id (.var 2) (.var 1) (.var 1) : Tower.Tm 3) := rfl

theorem typed_beta_returns_the_supplied_witness :
    Equal Tower.rules full.target.raw (full.openFunction function).code suppliedProof.code full.result.code :=
  full.beta suppliedProof

theorem actual_beta_execution :
    (ExecutableReduction.normalize Tower.rules (fun _ => none) 8 (full.openFunction function).code).map Subtype.val =
      some (.var 0 : Tower.Tm 3) := by rfl'

theorem supplied_witness_is_not_reflexivity :
    ¬ Equal Tower.rules closed.raw function.code reflexiveFunction.code outerWhole.code := by
  intro same
  have bodies := (full.abstractBody_equal_iff suppliedProof reflexivity).mp same
  have support := ContextualDependentNormalSupport.equal_support (S := setting) rigid TowerModel.complete full.target.formed bodies
    (normal _ (by rfl')) (normal _ (by rfl'))
  change ({0} : Finset (Fin 3)) = {1} at support
  exact (by decide +kernel : ({0} : Finset (Fin 3)) ≠ {1}) support

theorem scoped_and_closed_solutions_agree :
    (∃ solution : closed ⟶ closed, (frames setting.levels).Models solution
      [((⟨outerWhole, function⟩ : TotalTerm closed), (⟨outerWhole, reflexiveFunction⟩ : TotalTerm closed))]) ↔
      ∃ solution : closed ⟶ closed, (full.openedConstraint function reflexiveFunction).Holds solution :=
  full.fixed_point_solutions_iff setting.levels function reflexiveFunction closed

namespace Eta

abbrev context := extend closed outerWhole
def lifted := full.reindex (projectionHom closed outerWhole)
def neutral := newest closed outerWhole
def expansion := lifted.abstractBody (lifted.openFunction neutral)

theorem eta_at_all_three_arguments : Equal Tower.rules context.raw expansion.code neutral.code
    (outerWhole.reindex (projectionHom closed outerWhole)).code := lifted.eta neutral

theorem actual_eta_code : expansion.code = .lam (.lam (.lam (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)))) := by rfl'
theorem eta_has_distinct_raw_syntax : expansion.code ≠ neutral.code := by decide +kernel

end Eta

namespace Reindex

def ground : Term closed universeType := ⟨.head .legacyGround, .headType .legacyGround⟩
def solution := Elimination.instantiate closed ground
def specialized := tail.reindex solution

theorem actual_context_changes : specialized.target.raw =
    .snoc (.snoc .nil (.head .legacyGround)) (.id (.head .legacyGround) (.var 0) (.var 0)) := by rfl'

theorem rigid_arguments_are_retained :
    List.ofFn (tail.map solution).substitution = ([.var 0, .var 1, .head .legacyGround] : List (Tower.Tm 2)) := by rfl'

theorem actual_result_type_changes : specialized.result.code = (.id (.head .legacyGround) (.var 1) (.var 1) : Tower.Tm 2) := by rfl'

theorem abstraction_commutes_with_type_assignment :
    (tail.abstractBody suppliedProof).reindex solution =
      specialized.abstractBody ((suppliedProof.reindex (tail.map solution)).cast (tail.result_reindex solution)) :=
  tail.abstractBody_reindex solution suppliedProof

end Reindex

namespace Discovery

def run (fuel count : Nat) := ContextualDependentPiSpineDiscovery.discover (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
  ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
  ContextualDependentInversion.Controls.reducer fuel count outerWhole

def discovered := (run 64 3).get (by decide +kernel)

theorem actual_discovery_has_three_binders : discovered.length = 3 := by rfl'
theorem actual_discovery_context : discovered.target = proofs := by rfl'

def resultShape {n : Nat} : Tower.Tm n → Option (Nat × Nat × Nat)
  | .id (.var carrier) (.var first) (.var second) => some (carrier.val, first.val, second.val)
  | _ => none

def variableIndex {n : Nat} : Tower.Tm n → Option Nat
  | .var index => some index.val
  | _ => none

theorem discovered_dependent_result : resultShape discovered.result.code = some (2, 1, 1) := by rfl'

theorem discovered_opening_computes :
    (ExecutableReduction.normalize Tower.rules (fun _ => none) 8 (discovered.openFunction function).code).map
      (fun value => variableIndex value.val) = some (some 0) := by rfl'

theorem too_many_arguments_stay_unfinished : run 64 4 = none := by rfl'
theorem zero_formation_budget_stays_unfinished : run 0 3 = none := by rfl'

end Discovery

namespace Solver

def body : Term Eta.lifted.target Eta.lifted.result :=
  (suppliedProof.reindex (full.map (projectionHom closed outerWhole))).cast (full.result_reindex (projectionHom closed outerWhole))
def reflBody : Term Eta.lifted.target Eta.lifted.result :=
  (reflexivity.reindex (full.map (projectionHom closed outerWhole))).cast (full.result_reindex (projectionHom closed outerWhole))
def opened := Eta.lifted.openFunction Eta.neutral

def run (fuel : Nat) (right : Term Eta.lifted.target Eta.lifted.result) :=
  ContextualDependentPiSpineSolver.solveBody (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer fuel outerWhole Eta.lifted opened right

def result := run 64 body
def reflResult := run 64 reflBody

theorem actual_solver_finishes : result.update.remaining = [] := by rfl'
theorem computed_three_argument_function : result.update.answer.substitution 0 = .lam (.lam (.lam (.var 0))) := by rfl'
theorem computed_reflexive_alternative : reflResult.update.answer.substitution 0 = .lam (.lam (.lam (.refl (.var 1)))) := by rfl'
theorem reflexive_alternative_finishes : reflResult.update.remaining = [] := by rfl'

theorem original_scoped_problem_has_principal_answer :
    ContextualDependentScopedDispatch.Holds [Eta.lifted.toScoped ⟨Eta.lifted.result, opened, body⟩] result.update.answer ∧
      ∀ (Δ : Context Tower.rules) (solution : Δ ⟶ Eta.context),
        ContextualDependentScopedDispatch.Holds [Eta.lifted.toScoped ⟨Eta.lifted.result, opened, body⟩] solution →
          ∃ residual : Δ ⟶ result.update.target, ∀ term : TotalTerm Eta.context,
            (frames setting.levels).E (term.reindex solution) (term.reindex (residual ≫ result.update.answer)) :=
  result.completed actual_solver_finishes

theorem zero_solver_budget_is_pending : (run 0 body).update.remaining.length = 1 := by rfl'

def ambientFunction : Term Eta.lifted.target (outerWhole.reindex (toEmpty Eta.lifted.target)) :=
  ⟨(.var 3 : Tower.Tm 4), .var (3 : Fin 4)⟩
def typeArgument : Term Eta.lifted.target (universeType.reindex (toEmpty Eta.lifted.target)) :=
  ⟨(.var 2 : Tower.Tm 4), .var (2 : Fin 4)⟩
def typeMap := pair (toEmpty Eta.lifted.target) typeArgument
def valueArgument : Term Eta.lifted.target (element.reindex typeMap) := ⟨(.var 1 : Tower.Tm 4), .var (1 : Fin 4)⟩
def valueMap := pair typeMap valueArgument
def repeatedArgument : Term Eta.lifted.target (identityType.reindex valueMap) := opened.cast (by apply TypeOver.ext <;> rfl)
def firstApplication := outer.apply (toEmpty Eta.lifted.target) ambientFunction typeArgument
def secondApplication := middle.apply typeMap firstApplication valueArgument
def recursiveBody : Term Eta.lifted.target Eta.lifted.result :=
  (inner.apply valueMap secondApplication repeatedArgument).cast (by apply TypeOver.ext <;> rfl)
def recursiveResult := run 64 recursiveBody

def ambientAt (arguments : Eta.lifted.target ⟶ full.target) :
    Term Eta.lifted.target (outerWhole.reindex (arguments ≫ full.projection)) :=
  ambientFunction.cast (congrArg (fun map => outerWhole.reindex map)
    (toEmpty_unique Eta.lifted.target (arguments ≫ full.projection)).symm)

def naturalArguments := full.map (projectionHom closed outerWhole)
def repeatedArguments := pair valueMap repeatedArgument

theorem arbitrary_ambient_function_applies_to_fresh_arguments :
    (full.apply naturalArguments (ambientAt naturalArguments)).code = opened.code := by rfl'

theorem arbitrary_ambient_function_applies_to_nonpattern_arguments :
    (full.apply repeatedArguments (ambientAt repeatedArguments)).code = recursiveBody.code := by rfl'

theorem general_application_beta : Equal Tower.rules Eta.lifted.target.raw
    (full.apply repeatedArguments (function.reindex (repeatedArguments ≫ full.projection))).code
    (suppliedProof.reindex repeatedArguments).code (full.result.reindex repeatedArguments).code :=
  full.apply_beta suppliedProof repeatedArguments

theorem nonpattern_stays_residual : recursiveResult.update.remaining.length = 1 := by rfl'

def identityAssignment := Elimination.instantiate closed function

theorem nonpattern_has_an_independent_solution :
    (Eta.lifted.toScoped ⟨Eta.lifted.result, opened, recursiveBody⟩).Holds identityAssignment := by
  apply (Eta.lifted.closeBody_holds_iff identityAssignment opened recursiveBody).mp
  let equation := Eta.lifted.closeBody opened recursiveBody
  have compared := ((Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer 128
    (TotalTerm.reindex (⟨equation.type, equation.left⟩ : TotalTerm Eta.context) identityAssignment)
    (TotalTerm.reindex (⟨equation.type, equation.right⟩ : TotalTerm Eta.context) identityAssignment)).get (by decide +kernel)).down
  exact compared.2

end Solver
end ContextualDependentPiSpine.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
