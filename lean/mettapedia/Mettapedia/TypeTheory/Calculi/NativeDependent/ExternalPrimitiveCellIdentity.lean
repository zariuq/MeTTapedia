import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMap
import Mettapedia.TypeTheory.ContextualCartesianCellIdentity

/-!
# Declaration-local identity forces every primitive-family instance

Only each primitive's complete declared display context is fixed. Successful
independent argument checking supplies an actual contextual substitution.
Cartesian naturality then fixes the primitive family at any already fixed
caller context; no identity condition on all generated families is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelCellIdentity

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCartesianCellIdentity

universe a c s t m
variable {S : Symbols.{a}} {C E : CwfWithTerminal.{c,s,t,m}}
variable (source : ModelData S C) (F : StrictCwfMorphism C E)
  (cell : F.toFamilyMorphism.base ⟶ F.toFamilyMorphism.base)

/-- Identity is required only at the actual complete display context of
an individual declared family. -/
def PrimitiveIdentity : Prop :=
  ∀ symbol : S.TypeSymbol,
    cell.app ⟨C.toCwf.ext (source.typeParameters symbol).1 (source.typeFamily symbol)⟩ =
      𝟙 (F.toFamilyMorphism.base.obj
        ⟨C.toCwf.ext (source.typeParameters symbol).1 (source.typeFamily symbol)⟩)

/-- Every supplied instantiation is forced by the complete primitive
reading and the already fixed caller base. -/
theorem family_instance_fixed (primitive : PrimitiveIdentity source F cell)
    {Γ : C.toCwf.Ctx} (symbol : S.TypeSymbol)
    (arguments : C.toCwf.Sub Γ (source.typeParameters symbol).1)
    (baseFixed : cell.app ⟨Γ⟩ = 𝟙 (F.toFamilyMorphism.base.obj ⟨Γ⟩)) :
    cell.app ⟨C.toCwf.ext Γ (source.familyAt symbol arguments)⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ (source.familyAt symbol arguments)⟩) :=
  reindexed_fixed F cell arguments (source.typeFamily symbol) baseFixed (primitive symbol)

/-- Independent evaluator success earns the actual instantiated family
and its displayed identity. The premise concerns one declared symbol. -/
theorem family_success_fixed (primitive : PrimitiveIdentity source F cell)
    {n : Nat} (Γ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C n)
    (symbol : S.TypeSymbol) (arguments : Fin (S.typeArity symbol) → TermExpr S n)
    (A : C.toCwf.Ty Γ.1) (evaluated : source.evaluateType Γ (.family symbol arguments) = some A)
    (baseFixed : cell.app ⟨Γ.1⟩ = 𝟙 (F.toFamilyMorphism.base.obj ⟨Γ.1⟩)) :
    cell.app ⟨C.toCwf.ext Γ.1 A⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ.1 A⟩) := by
  have lifted := (source.evaluateType_eq_some_iff _ _ _).mp evaluated
  rw [ModelData.evaluateTypeLifted] at lifted
  rcases (bindResult_eq_some_iff _ _ _).mp lifted with ⟨actual, _assembled, last⟩
  have actualType : source.familyAt symbol actual = A :=
    congrArg ULift.down (Option.some.inj last)
  rw [← actualType]
  exact family_instance_fixed source F cell primitive symbol actual baseFixed

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelCellIdentity
