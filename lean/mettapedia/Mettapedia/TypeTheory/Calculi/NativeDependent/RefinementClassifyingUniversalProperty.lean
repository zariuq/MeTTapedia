import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementClassifyingPredicateCoherence

/-!
# Coherent classifying property of the generated predicate model

Objects are actual constructor-, predicate- and primitive-preserving model
maps. Arrows are complete corrected contextual cells satisfying independently
stated local declaration squares. Identity and vertical composition preserve
these squares; earned constructor propagation proves complete-cell uniqueness.

Every independently sized qualified target receives the actual canonical
interpretation and a unique admitted coherent isomorphism from it to every
other interpretation. Authored raw contexts remain objects. The model-map
class has strict chosen dependent operations and local comparison laws;
arbitrary pseudo logical maps and identification of definable predicates with
all target subobjects are not asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ClassifyingCells

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Refinement.Abstract ModelMapComparison

universe u z p
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}
variable (headers : HeaderFormation D)
  (target : Interpretation.QualifiedModel.{u,max u z,max u z,max u z,max u z,p} D C)

abbrev AdmittedCell (first second : ModelMap (sourceModel.{u,z} headers).data target.data) :=
  {candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo //
    PrimitiveAdmission headers target first second candidate}

instance admittedCell_subsingleton
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) :
    Subsingleton (AdmittedCell headers target first second) where
  allEq left right := Subtype.ext
    ((cell_unique headers target first second left.val left.property).trans
      (cell_unique headers target first second right.val right.property).symm)

theorem identity_admitted (mapping : ModelMap (sourceModel.{u,z} headers).data target.data) :
    PrimitiveAdmission headers target mapping mapping
      (CorrectedTransformationData.identity mapping.morphism.toPseudo) where
  families _ := Category.id_comp _
  propositions := Category.id_comp _
  predicates _ := Category.id_comp _

theorem vertical_admitted
    {first second third : ModelMap (sourceModel.{u,z} headers).data target.data}
    (left : AdmittedCell headers target first second)
    (right : AdmittedCell headers target second third) :
    PrimitiveAdmission headers target first third
      (CorrectedTransformationData.vertical left.val right.val) where
  families symbol := by
    change (left.val.base.app _ ≫ right.val.base.app _) ≫
      eqToHom (primitiveFamilyImage headers target third symbol) =
        eqToHom (primitiveFamilyImage headers target first symbol)
    rw [Category.assoc]
    erw [right.property.families symbol]
    exact left.property.families symbol
  propositions := by
    change (left.val.base.app _ ≫ right.val.base.app _) ≫
      eqToHom (omegaImage headers target third) = eqToHom (omegaImage headers target first)
    rw [Category.assoc]
    erw [right.property.propositions]
    exact left.property.propositions
  predicates symbol := by
    change (left.val.base.app _ ≫ right.val.base.app _) ≫
      eqToHom (primitivePredicateImage headers target third symbol) =
        eqToHom (primitivePredicateImage headers target first symbol)
    rw [Category.assoc]
    erw [right.property.predicates symbol]
    exact left.property.predicates symbol

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

noncomputable def comparisonCell
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) : first ⟶ second :=
  ⟨(correctedIso headers first second).hom, canonical_admitted headers target first second⟩

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

@[instance_reducible] noncomputable def admittedIsoUnique
    (first second : ModelMap (sourceModel.{u,z} headers).data target.data) :
    Unique (first ≅ second) where
  default := comparisonIso headers target first second
  uniq candidate := Iso.ext (Subsingleton.elim candidate.hom _)

@[simp] theorem comparison_unit
    (mapping : ModelMap (sourceModel.{u,z} headers).data target.data) :
    comparisonCell headers target mapping mapping = 𝟙 mapping := Subsingleton.elim _ _

@[simp] theorem comparison_composition
    (first second third : ModelMap (sourceModel.{u,z} headers).data target.data) :
    comparisonCell headers target first second ≫ comparisonCell headers target second third =
      comparisonCell headers target first third := Subsingleton.elim _ _

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ClassifyingCells

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Classifying

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Refinement.Abstract ClassifyingCells

universe u c s t m p
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}
variable (headers : HeaderFormation D) (model : Interpretation.QualifiedModel.{u,c,s,t,m,p} D C)

/-- Existence retains the original mixed syntax and all five independently
sized model carriers at the earned external presentation. -/
noncomputable def interpretation : ModelMap (sourceModel.{u,max c s t m} headers).data
    (model.commonCarrierLift.{u,c,s,t,m,p,u,0}).data :=
  Interpretation.canonicalModelMap model headers

/-- Coherent classification is a universal property of actual contextual
maps and complete corrected cells, rather than a proof-tree fold alone. -/
@[instance_reducible] noncomputable def comparisonUnique
    (other : ModelMap (sourceModel.{u,max c s t m} headers).data
      (model.commonCarrierLift.{u,c,s,t,m,p,u,0}).data) :
    Unique (interpretation headers model ≅ other) :=
  admittedIsoUnique headers (model.commonCarrierLift.{u,c,s,t,m,p,u,0})
    (interpretation headers model) other

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Classifying
