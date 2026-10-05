import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.Lists
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDeclarationLists
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ParameterizedDatatypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Erasure

/-!
# Lists as a parameterized datatype

`MegalodonHOTG.Lists` declares `List`, `nil`, `cons` and `append` by a hand-written
table. The same `List`, `nil` and `cons` are a parameterized datatype: one
parameter, the type of all sets, with `nil` having no fields and `cons` having
the parameter and one uniform field. The declared types agree.

The family declares `append` and not a recursor. The datatype declares a
recursor and not `append`. The value of the type of `List` is a function from
the universe of sets to itself. The parameterization is admissible over the bare
tower (`listDatatype_parameterAdmissible`): the parameter is the universe of
sets. `smallList_no_setModel` is untouched: it is the same family with `List`
landing in the least universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG
namespace Lists

open Presentation Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (tracePiSet)

universe u

variable {L : Type} [LevelOrder L]

/-- The recursor of the list datatype. The hand-written family has `append` in
its place. -/
def listRecN : DeclName := .str .anonymous "listRec"

/-- One parameter, the type of all sets. -/
def listParameters : Parameterization (Head L) where
  telescope := ⟨1, .snoc .nil (.head (.sort (.const (.above 0))))⟩
  constructors := [
    (nilN, []),
    (consN, [.plain (.var 0), .uniform])
  ]

/-- Lists as a parameterized datatype. The simple constructor list is empty:
the constructors are open fields. -/
def listDatatype : Datatype (Head L) where
  type := listN
  typeUniverse := .sort (.const (.above 0))
  ctors := []
  recursor := listRecN
  motiveUniverse := .sort (.const (.above 1))
  parameters := listParameters

omit [LevelOrder L] in
theorem list_type_agrees :
    typeConstant (listDatatype (L := L)) = (listType : CTm (Head L) 0).erase := rfl

omit [LevelOrder L] in
theorem nil_type_agrees :
    parameterDecls (listDatatype (L := L)) nilN = some (nilType : CTm (Head L) 0).erase := rfl

omit [LevelOrder L] in
theorem cons_type_agrees :
    parameterDecls (listDatatype (L := L)) consN = some (consType : CTm (Head L) 0).erase := rfl

omit [LevelOrder L] in
/-- `append` is a constant of the hand-written family, not a constructor of the
datatype. -/
theorem append_not_a_constructor :
    parameterDecls (listDatatype (L := L)) appendN = (none : Option (Tm (Head L) 0)) := rfl

omit [LevelOrder L] in
/-- The type of `List` reads as a function from the universe of sets to itself. -/
theorem listType_ev (heads : Head L → ZFSet.{u}) (consts : DeclName → ZFSet.{u}) :
    ev heads consts (listType : CTm (Head L) 0) Fin.elim0 =
      tracePiSet (heads (.sort (.const (.above 0))))
        (fun _ => heads (.sort (.const (.above 0)))) := rfl

/-- The list parameterization is admissible over the bare tower. The parameter
is the universe of sets, `nil` has no fields, and `cons` has the parameter and
one uniform field. -/
theorem listDatatype_parameterAdmissible :
    ParameterAdmissible (bare L) (listDatatype (L := L)) := by
  have levels : Presentation.TypedEquality.Normalization.LevelModel (rules L) (Above L) :=
    Presentation.TypedEquality.Normalization.TowerModel.levels
      fun _ => (LevelOrder.bot : Above L)
  refine ⟨⟨trivial, ?_⟩, ?_, Or.inr rfl⟩
  · exact CIsType.head_of_universe (P := bare L) (Γ := .nil) levels
      (LevelTower.IsUniverse.sort _)
  · intro k fs member f fm
    simp only [listDatatype, listParameters] at member
    cases member with
    | head => cases fm
    | tail _ member =>
      cases member with
      | head =>
        cases fm with
        | head => rfl
        | tail _ fm =>
          cases fm with
          | head => exact uniform_plainAdmissible _ _
          | tail _ fm => cases fm
      | tail _ member => cases member

omit [LevelOrder L] in
/-- The hand-written family declares `append` and not a recursor. The declaring
package declares the recursor and not `append`. `listFamily_setModel` is a model
of the family, which has `append` and no recursor. -/
theorem listFamily_not_the_declaring_package :
    (∃ ty : Tm (Head L) 0, parameterDecls (listDatatype (L := L)) listRecN = some ty) ∧
      parameterDecls (listDatatype (L := L)) appendN = (none : Option (Tm (Head L) 0)) :=
  ⟨⟨_, rfl⟩, append_not_a_constructor⟩

end Lists
end MegalodonHOTG

section InstancePackage

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization (LevelModel)
open UniverseLevel (LevelOrder)
open Mettapedia.Logic.HOL.Embedding

universe u

variable {Head : Type} {R : Rules Head} {L : Type} [LevelOrder L]

/-- **Each closed instance has a set model.** This is `declarations_setModel` at the
one declaration `d.instantiate σ`. The package it models is the simple package of
that instance, `withDeclarations B [.datatype (d.instantiate σ)]`. -/
theorem instance_setModel
    (heads : Head → ZFSet.{u}) (base : DeclName → ZFSet.{u})
    (levels : LevelModel R L) (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    {d : Datatype Head} {σ : Sub Head d.parameters.telescope.count 0}
    (stage : (d.instantiate σ).Admissible B)
    (closed : ZFSetUniverseClosure.Closed (heads (d.instantiate σ).typeUniverse))
    (omega : ZFSet.omega ∈ heads (d.instantiate σ).typeUniverse)
    (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c,
      (withDeclarations B [.datatype (d.instantiate σ)]).constantType c ≠ none →
        consts c = declarationsConsts heads base [.datatype (d.instantiate σ)] c) :
    SetModel heads consts (withDeclarations B [.datatype (d.instantiate σ)]) :=
  declarations_setModel (heads := heads) (base := base) levels B baseModel
    [.datatype (d.instantiate σ)] ⟨trivial, stage⟩
    (fun _ member => by
      simp only [List.mem_singleton] at member
      cases member
      exact ⟨closed, omega⟩)
    consts agrees

end InstancePackage

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
