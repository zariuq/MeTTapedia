import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalClassifyingCellUniqueness
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalCanonicalModelMap

/-!
# The declaration-admitted classifying model property

Objects are actual logical and primitive-preserving contextual model maps.
Their arrows are actual corrected cells satisfying the independently stated
primitive display square. That local admission is closed under identity and
composition. Constructor propagation earns uniqueness of every admitted cell.

The generated model has an actual interpretation into every qualified model,
including models with independently sized contextual carriers. Every other
interpretation has a unique admitted coherent isomorphism with it. Authored
raw contexts remain objects, and the morphisms retain full display coherence.
This is the strict chosen-representative model-map class; no internal universe
or identity capability, nor an arbitrary pseudo logical map, is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ClassifyingCells

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open LiftedModelMapComparison

universe u z
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}
variable (headers : HeaderFormation D) (target : Interpretation.QualifiedModel D C)

/-- Complete corrected cells with only the independently supplied local
primitive display admission. -/
abbrev AdmittedCell
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) :=
  {candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo //
    PrimitiveAdmission headers target first second candidate}

instance admittedCell_subsingleton
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) :
    Subsingleton (AdmittedCell headers target first second) where
  allEq firstCell secondCell := Subtype.ext
    ((cell_unique headers target first second firstCell.val firstCell.property).trans
      (cell_unique headers target first second secondCell.val secondCell.property).symm)

/-- Identity retains each independently fixed target declaration. -/
theorem identity_admitted
    (mapping : ModelMap (sourceModel.{u,z} headers).data target.data) :
    PrimitiveAdmission headers target mapping mapping
      (CorrectedTransformationData.identity mapping.morphism.toPseudo) := by
  intro symbol
  exact Category.id_comp _

/-- Two local declaration squares compose to the square for their actual
corrected composite, including every displayed component. -/
theorem vertical_admitted
    {first second third : ModelMap (sourceModel.{u,z} headers).data target.data}
    (left : AdmittedCell headers target first second)
    (right : AdmittedCell headers target second third) :
    PrimitiveAdmission headers target first third
      (CorrectedTransformationData.vertical left.val right.val) := by
  intro symbol
  change (left.val.base.app _ ≫ right.val.base.app _) ≫
    eqToHom (primitiveImage headers target third symbol) =
      eqToHom (primitiveImage headers target first symbol)
  rw [Category.assoc]
  erw [right.property symbol]
  exact left.property symbol

/-- The hom category uses genuine corrected composition and local
declaration preservation; its laws follow from earned complete-cell uniqueness. -/
noncomputable instance modelMapCategory :
    Category (ModelMap (sourceModel.{u,z} headers).data target.data) where
  Hom := AdmittedCell headers target
  id mapping := ⟨CorrectedTransformationData.identity mapping.morphism.toPseudo,
    identity_admitted headers target mapping⟩
  comp left right := ⟨CorrectedTransformationData.vertical left.val right.val,
    vertical_admitted headers target left right⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

instance modelHom_subsingleton
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) :
    Subsingleton (first ⟶ second) := admittedCell_subsingleton headers target first second

/-- The supplied canonical comparison has actual full display coherence
and earns the independent primitive square. -/
noncomputable def comparisonCell
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) : first ⟶ second :=
  ⟨(correctedIso headers first second).hom, canonical_admitted headers target first second⟩

/-- Every pair of actual interpretations has a coherent admitted inverse.
The inverse equations are equality of the complete corrected cells. -/
noncomputable def comparisonIso
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) : first ≅ second where
  hom := comparisonCell headers target first second
  inv := comparisonCell headers target second first
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

@[instance_reducible] noncomputable def admittedCellUnique
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) :
    Unique (first ⟶ second) where
  default := comparisonCell headers target first second
  uniq _ := Subsingleton.elim _ _

/-- Uniqueness includes the complete displayed comparison and both inverse
equations; it is not merely uniqueness of a syntax-tree fold. -/
@[instance_reducible] noncomputable def admittedIsoUnique
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) :
    Unique (first ≅ second) where
  default := comparisonIso headers target first second
  uniq candidate := Iso.ext (Subsingleton.elim candidate.hom _)

@[simp] theorem comparison_unit
    (mapping : ModelMap (sourceModel.{u,z} headers).data target.data) :
    comparisonCell headers target mapping mapping = 𝟙 mapping := Subsingleton.elim _ _

/-- Unit and composition coherence hold for the actual complete cells. -/
@[simp] theorem comparison_composition
    (first second third : ModelMap (sourceModel.{u,z} headers).data target.data) :
    comparisonCell headers target first second ≫ comparisonCell headers target second third =
      comparisonCell headers target first third := Subsingleton.elim _ _

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ClassifyingCells

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Classifying

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ClassifyingCells

universe u c s t m
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}
variable (headers : HeaderFormation D) (model : Interpretation.QualifiedModel D C)

/-- Actual local primitives and logical constructors earn interpretation
existence at a common external carrier level, without changing the syntax. -/
noncomputable def interpretation : ModelMap
    (sourceModel.{u,max c s t m} headers).data
    (model.commonUniverseLift.{u,c,s,t,m,u}).data :=
  Interpretation.canonicalModelMap model headers

/-- The generated contextual model classifies qualified interpretations:
every other local logical/primitive-preserving map has exactly one coherent
declaration-admitted comparison isomorphism with the earned interpretation. -/
@[instance_reducible] noncomputable def comparisonUnique
    (other : ModelMap (sourceModel.{u,max c s t m} headers).data
      (model.commonUniverseLift.{u,c,s,t,m,u}).data) :
    Unique (interpretation headers model ≅ other) :=
  admittedIsoUnique headers (model.commonUniverseLift.{u,c,s,t,m,u})
    (interpretation headers model) other

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Classifying
