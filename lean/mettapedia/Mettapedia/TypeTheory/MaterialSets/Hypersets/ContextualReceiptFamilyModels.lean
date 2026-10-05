import Mettapedia.TypeTheory.ContextualSmallFamilyIdentity
import Mettapedia.TypeTheory.ContextualSmallFamilyWTypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWTypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualMaterialization

/-!
# Material dictionaries for small families over wider parameters

The parameter functor may inhabit an arbitrary larger universe. Its actual
value remains external. Every complete future argument can nevertheless be
labelled at the original receipt bound by its target world, actual arrow,
and decoded argument graph. No graph or decoder for the parameter carrier
is used. Sigma, full future Pi, discrete identity, hereditary W, and stable
separation construct their dictionaries from the input dictionaries.

The W dictionary uses the actual small future-cone signature of the native
contextual W construction. All its worlds, shapes and branches retain their
complete future arrows. The native parameter is not replaced by its present
support, nor reconstructed from an authored label.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReceiptFamilyModels

open CategoryTheory
open Mettapedia.TypeTheory
open ContextualSmallFamilyTypeFormers
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}

abbrev Model (domain : base.Elements ⥤ Type u) := (point : base.Elements) → PresentedType (domain.obj point)

variable (domain : base.Elements ⥤ Type u) (models : Model domain)
variable (body : domain.Elements ⥤ Type u) (bodyModels : (point : domain.Elements) → PresentedType (body.obj point))
variable (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))

def termCoding (point : base.Elements) : ArgumentCoding (domain.obj point) where
  graph := (models point).termGraph
  injective first second same := (models point).value_injective
    ((PresentedType.mk_termGraph _ first).symm.trans (same.trans (PresentedType.mk_termGraph _ second)))

/-- The original parameter determines its transported future value. Only
the actual small world and arrow need faithful graph labels. -/
def futureWorldCoding (point : base.Elements) : ArgumentCoding (Future.Objects point.1) where
  graph future := (worlds.sigma (arrows point.1)).graph ⟨future.1, future.2⟩
  injective _first _second same :=
    congrArg (fun future : (target : D) × (point.1 ⟶ target) =>
      (⟨future.1, future.2⟩ : Future.Objects point.1))
      ((worlds.sigma (arrows point.1)).injective same)

def futureCoding (point : base.Elements) : ArgumentCoding (futureDomain domain point).Elements :=
  (futureWorldCoding worlds arrows point).sigma fun future =>
    termCoding domain models ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future)

def futureArrowCoding (point : base.Elements) (first second : Future.Objects point.1) :
    ArgumentCoding (first ⟶ second) :=
  (arrows first.1 second.1).subtype (fun arrow => first.2 ≫ arrow = second.2)

def outputModels (point : base.Elements) (argument : (futureDomain domain point).Elements) :
    PresentedType ((futureBody domain body point).obj argument) :=
  bodyModels ((futureArguments domain point).obj argument)

def sigmaModel (point : base.Elements) : PresentedType ((sigma domain body).obj point) :=
  PresentedType.sum (models point) (fun argument => bodyModels ⟨point, argument⟩)

def piModel (point : base.Elements) : PresentedType ((pi domain body).obj point) :=
  LabelledDependentProducts.compatibleProduct (futureCoding domain models worlds arrows point)
    (outputModels domain body bodyModels point)
    (fun values => values ∈ (futureBody domain body point).sections)

/-- The original-bound native W is already a hereditary-natural tree on
the small future cone. Its complete material graph and decoder are built
at the same bound from these constructed cone dictionaries. -/
def wModel (point : base.Elements) : PresentedType ((ContextualSmallFamilyWTypes.w domain body).obj point) :=
  MaterialContextualWTypes.naturalModel (futureDomain domain point) (futureBody domain body point)
    (futureWorldCoding worlds arrows point) (futureArrowCoding arrows point)
    (fun future => models ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future))
    (outputModels domain body bodyModels point) (ContextualSmallFamilyUniverse.root point.1)

theorem sigma_first (point : base.Elements) (pair : (sigma domain body).obj point) :
    HSet.fst ((sigmaModel domain models body bodyModels point).value pair) = (models point).value pair.1 :=
  (congrArg HSet.fst (PresentedType.sum_value (models point)
    (fun argument => bodyModels ⟨point, argument⟩) pair)).trans (HSet.fst_kpair _ _)

theorem sigma_second (point : base.Elements) (pair : (sigma domain body).obj point) :
    HSet.snd ((sigmaModel domain models body bodyModels point).value pair) =
      (bodyModels ⟨point, pair.1⟩).value pair.2 :=
  (congrArg HSet.snd (PresentedType.sum_value (models point)
    (fun argument => bodyModels ⟨point, argument⟩) pair)).trans (HSet.snd_kpair _ _)

theorem pi_entry (point : base.Elements) (function : (pi domain body).obj point)
    (argument : (futureDomain domain point).Elements) :
    HSet.kpair ((futureCoding domain models worlds arrows point).reading argument)
      ((outputModels domain body bodyModels point argument).value (function.val argument)) ∈
        (piModel domain models body bodyModels worlds arrows point).value function :=
  LabelledDependentProducts.product_entry (futureCoding domain models worlds arrows point)
    (outputModels domain body bodyModels point) function.val argument

theorem pi_evaluation (point : base.Elements) (function : (pi domain body).obj point)
    (argument : (futureDomain domain point).Elements) :
    LabelledDependentProducts.evalValue (futureCoding domain models worlds arrows point)
      (outputModels domain body bodyModels point)
      ((piModel domain models body bodyModels worlds arrows point).value function) argument =
        (outputModels domain body bodyModels point argument).value (function.val argument) :=
  LabelledDependentProducts.evalValue_functionGraph (futureCoding domain models worlds arrows point)
    (outputModels domain body bodyModels point) function.val argument

theorem w_value (point : base.Elements) (tree : (ContextualSmallFamilyWTypes.w domain body).obj point) :
    (wModel domain models body bodyModels worlds arrows point).value tree =
      MaterialContextualWTypes.encode (futureDomain domain point) (futureBody domain body point)
        (futureWorldCoding worlds arrows point) (futureArrowCoding arrows point)
        (fun future => models ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future))
        (outputModels domain body bodyModels point) tree.val :=
  MaterialContextualWTypes.naturalModel_value _ _ _ _ _ _ tree

def identityModel (left right : domain.sections) (point : base.Elements) :
    PresentedType ((ContextualSmallFamilyIdentity.identityFamily domain left right).obj point) :=
  PowerClassContextualMaterialization.powerClassModel (PresheafIdentityWitness.graph (left.val point) (right.val point))

theorem identity_inhabited (left right : domain.sections) (point : base.Elements) :
    Nonempty ((ContextualSmallFamilyIdentity.identityFamily domain left right).obj point) ↔
      (models point).value (left.val point) = (models point).value (right.val point) := by
  constructor
  · rintro ⟨witness⟩
    exact congrArg (models point).value (PresheafIdentityWitness.decode witness)
  · intro same
    exact ⟨PresheafIdentityWitness.encode ((models point).value_injective same)⟩

theorem model_value_heq {E : Type v} {family : E → Type u}
    (dictionaries : (point : E) → PresentedType (family point))
    {first second : E} (same : first = second)
    (left : family first) (right : family second) (values : HEq left right) :
    (dictionaries first).value left = (dictionaries second).value right := by
  cases same
  cases eq_of_heq values
  rfl

/-- Complete product restriction preserves the material output at every
actual prefixed future argument, including its transported parameter. -/
theorem pi_restriction_evaluation {first second : base.Elements} (step : first ⟶ second)
    (function : (pi domain body).obj first) (argument : (futureDomain domain second).Elements) :
    LabelledDependentProducts.evalValue (futureCoding domain models worlds arrows second)
        (outputModels domain body bodyModels second)
        ((piModel domain models body bodyModels worlds arrows second).value
          ((pi domain body).map step function)) argument =
      LabelledDependentProducts.evalValue (futureCoding domain models worlds arrows first)
        (outputModels domain body bodyModels first)
        ((piModel domain models body bodyModels worlds arrows first).value function)
        ((prefixArguments domain step).obj argument) := by
  rw [pi_evaluation, pi_evaluation]
  exact model_value_heq bodyModels (prefixArguments_embedding domain step argument).symm
    _ _ (productMap_value domain body step function argument)

/-! ## Actual material-member families and natural section decoders -/

def memberMap {first second : base.Elements} (step : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ (models first).carrier}) :
    {value : HSet.{u} // value ∈ (models second).carrier} :=
  (models second).decode.symm (domain.map step ((models first).decode member))

theorem memberMap_decode {first second : base.Elements} (step : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ (models first).carrier}) :
    (models second).decode (memberMap domain models step member) =
      domain.map step ((models first).decode member) :=
  (models second).decode.apply_symm_apply _

theorem memberMap_value {first second : base.Elements} (step : first ⟶ second)
    (term : domain.obj first) :
    (memberMap domain models step ((models first).decode.symm term)).val =
      (models second).value (domain.map step term) := by
  unfold memberMap
  rw [Equiv.apply_symm_apply]
  rfl

def members : base.Elements ⥤ Type (u + 1) where
  obj point := {value : HSet.{u} // value ∈ (models point).carrier}
  map step := TypeCat.ofHom (memberMap domain models step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro member
    apply (models point).decode.injective
    exact (memberMap_decode domain models (𝟙 point) member).trans
      (congrArg (fun operation => operation ((models point).decode member)) (domain.map_id point))
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro member
    apply (models _).decode.injective
    change (models _).decode (memberMap domain models (earlier ≫ later) member) =
      (models _).decode (memberMap domain models later (memberMap domain models earlier member))
    rw [memberMap_decode, memberMap_decode, memberMap_decode]
    exact congrArg (fun operation => operation ((models _).decode member)) (domain.map_comp earlier later)

def materialSection (term : domain.sections) : (members domain models).sections :=
  ⟨fun point => (models point).decode.symm (term.val point), by
    intro first second step
    change memberMap domain models step _ = _
    unfold memberMap
    rw [Equiv.apply_symm_apply, term.property step]⟩

def nativeSection (term : (members domain models).sections) : domain.sections :=
  ⟨fun point => (models point).decode (term.val point), by
    intro first second step
    exact (memberMap_decode domain models step (term.val first)).symm.trans
      (congrArg (models second).decode (term.property step))⟩

def sectionEquiv : domain.sections ≃ (members domain models).sections where
  toFun := materialSection domain models
  invFun := nativeSection domain models
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (models point).decode.apply_symm_apply _
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (models point).decode.symm_apply_apply _

theorem sectionEquiv_value (term : domain.sections) (point : base.Elements) :
    ((sectionEquiv domain models term).val point).val = (models point).value (term.val point) := rfl

theorem sectionEquiv_decode (term : (members domain models).sections) (point : base.Elements) :
    ((sectionEquiv domain models).symm term).val point = (models point).decode (term.val point) := rfl

/-! ## Stable separation at the original graph bound -/

structure StablePredicate where
  holds : (point : base.Elements) → domain.obj point → Prop
  map : ∀ {first second : base.Elements} (step : first ⟶ second) (term : domain.obj first),
    holds first term → holds second (domain.map step term)

def separate (predicate : StablePredicate domain) : base.Elements ⥤ Type u where
  obj point := {term : domain.obj point // predicate.holds point term}
  map step := TypeCat.ofHom fun term => ⟨domain.map step term.val, predicate.map step term.val term.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro term
    exact Subtype.ext (congrArg (fun operation => operation term.val) (domain.map_id point))
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro term
    exact Subtype.ext (congrArg (fun operation => operation term.val) (domain.map_comp earlier later))

def separateModels (predicate : StablePredicate domain) : Model (separate domain predicate) :=
  fun point => PresentedType.restrict (models point) (predicate.holds point)

theorem separate_value (predicate : StablePredicate domain) (point : base.Elements)
    (term : (separate domain predicate).obj point) :
    (separateModels domain models predicate point).value term = (models point).value term.val :=
  PresentedType.restrict_value _ _ term

def separationSectionEquiv (predicate : StablePredicate domain) :
    (separate domain predicate).sections ≃
      {term : domain.sections // ∀ point, predicate.holds point (term.val point)} where
  toFun term := ⟨⟨fun point => (term.val point).val,
    fun {_ _} step => congrArg Subtype.val (term.property step)⟩, fun point => (term.val point).property⟩
  invFun term := ⟨fun point => ⟨term.val.val point, term.property point⟩,
    fun {_ _} step => Subtype.ext (term.val.property step)⟩
  left_inv term := by apply Subtype.ext; funext point; rfl
  right_inv term := by apply Subtype.ext; apply Subtype.ext; funext point; rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReceiptFamilyModels
