import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Chains of laws through terms of one sort

A chain of a language's static laws may pass through terms of no sort: a one-member bag wrapped around a name where
a name is expected is an instance of the bag's laws, read backwards. `SortedEquiv` keeps the chains whose every
step relates two terms of one sort, in one context of free and bound variables. It is part of the static theory
(`SortedEquiv.toEquationEquiv`), a context of the right sort carries it (`SortedEquiv.fill`), and its two ends have
the sort together (`SortedEquiv.typed_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationContextStep EquationEquiv EquationInstance
  DerivedInstance equationContextStep_fill)

/-- **One law between two terms of one sort**, in a context. -/
structure SortedStep (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr) (sort : TypeExpr)
    (first second : Pattern) : Prop where
  step : EquationContextStep (engineBasePremises RelationEnv.empty) language first second
  firstTyped : HasType language free bound first sort
  secondTyped : HasType language free bound second sort

/-! ## Contexts of base sorts -/

/-- **A context of base sorts**: every free and every bound variable has a base sort. -/
structure BaseContext (free : FreeTypeContext) (bound : List TypeExpr) : Prop where
  free : ∀ name type, free name = some type → ∃ sort, type = .base sort
  bound : ∀ type ∈ bound, ∃ sort, type = .base sort

theorem BaseContext.cons {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    (sort : String) : BaseContext free (.base sort :: bound) :=
  ⟨context.free, by
    intro type member
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨sort, rfl⟩
    · exact context.bound type inside⟩

theorem BaseContext.replicate {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    (count : Nat) (sort : String) : BaseContext free (List.replicate count (.base sort) ++ bound) :=
  ⟨context.free, by
    intro type member
    rcases List.mem_append.mp member with member | member
    · exact ⟨sort, (List.eq_of_mem_replicate member)⟩
    · exact context.bound type member⟩

/-- **A chain of laws through terms of one sort.** -/
def SortedEquiv (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr) (sort : TypeExpr) :
    Pattern → Pattern → Prop :=
  Relation.EqvGen (SortedStep language free bound sort)

namespace SortedEquiv

variable {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr} {sort : TypeExpr}

/-- A sorted chain is part of the static theory. -/
theorem toEquationEquiv {first second : Pattern} (equivalent : SortedEquiv language free bound sort first second) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language first second :=
  Relation.EqvGen.mono (fun _ _ step => step.step) _ _ equivalent

/-- **Both ends have the sort, or neither.** -/
theorem typed_iff {first second : Pattern} (equivalent : SortedEquiv language free bound sort first second) :
    HasType language free bound first sort ↔ HasType language free bound second sort := by
  induction equivalent with
  | rel _ _ step => exact iff_of_true step.firstTyped step.secondTyped
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ left right => exact left.trans right

/-- **A context of the right sort carries a sorted chain.** -/
theorem fill {holeBound : List TypeExpr} {holeSort : TypeExpr} (context : OneHoleContext)
    (rebuild : ∀ filling, HasType language free holeBound filling holeSort →
      HasType language free bound (context.fill filling) sort)
    {first second : Pattern} (equivalent : SortedEquiv language free holeBound holeSort first second) :
    SortedEquiv language free bound sort (context.fill first) (context.fill second) := by
  induction equivalent with
  | rel _ _ step =>
      exact .rel _ _ ⟨equationContextStep_fill context step.step, rebuild _ step.firstTyped,
        rebuild _ step.secondTyped⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ recurse => exact Relation.EqvGen.symm _ _ recurse
  | trans _ _ _ _ _ left right => exact Relation.EqvGen.trans _ _ _ left right

/-- An authored instance between two terms of the sort. -/
theorem ofInstance {first second : Pattern}
    (witness : EquationInstance (engineBasePremises RelationEnv.empty) language first second)
    (firstTyped : HasType language free bound first sort) (secondTyped : HasType language free bound second sort) :
    SortedEquiv language free bound sort first second :=
  .rel _ _ ⟨.inContext .hole (.inl witness), firstTyped, secondTyped⟩

/-- A derived instance between two terms of the sort. -/
theorem ofDerived {first second : Pattern} (witness : DerivedInstance language first second)
    (firstTyped : HasType language free bound first sort) (secondTyped : HasType language free bound second sort) :
    SortedEquiv language free bound sort first second :=
  .rel _ _ ⟨.inContext .hole (.inr witness), firstTyped, secondTyped⟩

end SortedEquiv

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
