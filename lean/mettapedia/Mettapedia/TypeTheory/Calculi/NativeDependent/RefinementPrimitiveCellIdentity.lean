import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMap
import Mettapedia.TypeTheory.ContextualPredicateCellIdentity

/-!
# Local display readings and primitive instances

Only the complete display of each primitive family and the one closed
ordinary proposition display are fixed. Independently checked mixed
arguments supply the actual instance arrow. Cartesian naturality then
forces every such primitive instance at an already fixed caller context.
No condition at all authored families or all predicate assumptions is a
field of declaration identity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract.ModelCellIdentity

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.TypeTheory.ContextualCartesianCellIdentity
open External (bindResult_eq_some_iff)

universe a c s t m p
variable {S : Symbols.{a}} {C E : CwfWithTerminal.{c,s,t,m}}
  {localModel : LocalModel.{c,s,t,m,p} C}
variable (source : ModelData S C localModel) (mapping : StrictCwfMorphism C E)
  (cell : mapping.toFamilyMorphism.base ⟶ mapping.toFamilyMorphism.base)

/-- One local reading per declared family and the distinguished ordinary
proposition sort. These are complete display contexts, not scalar tests. -/
structure PrimitiveIdentity : Prop where
  family : ∀ symbol : S.TypeSymbol,
    cell.app ⟨C.toCwf.ext (source.typeParameters symbol).1 (source.typeFamily symbol)⟩ =
      𝟙 (mapping.toFamilyMorphism.base.obj
        ⟨C.toCwf.ext (source.typeParameters symbol).1 (source.typeFamily symbol)⟩)
  propositions : cell.app ⟨C.toCwf.ext C.empty (localModel.propositions.omega C.empty)⟩ =
    𝟙 (mapping.toFamilyMorphism.base.obj
      ⟨C.toCwf.ext C.empty (localModel.propositions.omega C.empty)⟩)

/-- Actual complete family instances retain their supplied mixed header
substitution. The local declared display forces their component. -/
theorem family_instance_fixed (primitive : PrimitiveIdentity source mapping cell)
    {Γ : C.toCwf.Ctx} (symbol : S.TypeSymbol)
    (arguments : C.toCwf.Sub Γ (source.typeParameters symbol).1)
    (baseFixed : cell.app ⟨Γ⟩ = 𝟙 (mapping.toFamilyMorphism.base.obj ⟨Γ⟩)) :
    cell.app ⟨C.toCwf.ext Γ (source.familyAt symbol arguments)⟩ =
      𝟙 (mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ (source.familyAt symbol arguments)⟩) :=
  reindexed_fixed mapping cell arguments (source.typeFamily symbol) baseFixed (primitive.family symbol)

/-- Evaluator success earns the instance substitution with every actual
assumption guard. No compatibility of whole expressions is assumed. -/
theorem family_success_fixed (primitive : PrimitiveIdentity source mapping cell)
    {n : Nat} (Γ : ModelScope C localModel n) (symbol : S.TypeSymbol)
    (arguments : Fin (S.typeArity symbol) → TermExpr S n) (A : C.toCwf.Ty Γ.1)
    (evaluated : source.evaluateType Γ (.family symbol arguments) = some A)
    (baseFixed : cell.app ⟨Γ.1⟩ = 𝟙 (mapping.toFamilyMorphism.base.obj ⟨Γ.1⟩)) :
    cell.app ⟨C.toCwf.ext Γ.1 A⟩ =
      𝟙 (mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ.1 A⟩) := by
  change External.bindResult ((source.typeParameters symbol).2.assemble?
    (fun index => source.evaluateTerm Γ (arguments index)))
      (fun substitution => some (source.familyAt symbol substitution)) = some A at evaluated
  rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, _assembled, last⟩
  have actualType : source.familyAt symbol actual = A := Option.some.inj last
  rw [← actualType]
  exact family_instance_fixed source mapping cell primitive symbol actual baseFixed

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract.ModelCellIdentity
