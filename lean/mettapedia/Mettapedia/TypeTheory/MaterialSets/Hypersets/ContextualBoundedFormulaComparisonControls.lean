import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedFormulaComparison
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogicControls

/-!
# Infinite controls for bounded logical comparison

Infinitely many natural values acquire their self-member after the initial
stage. An embedding adds a genuinely new empty value while covering every
member of each embedded parent. Bounded formulas still agree through all
futures, whereas the unbounded assertion that every value is inhabited fails
after embedding. These are logical comparison controls, not models of the
material set axioms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedFormulaComparisonControls

open _root_.CategoryTheory ContextualMaterialLogic ContextualBoundedFormulaComparison
open Mettapedia.TypeTheory.ContextualWitnessCover
open ContextualMaterialLogicControls

def upperValues : ℕ ⥤ Type where
  obj _ := Option ℕ
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def upperModel : Model upperValues where
  member point child parent := ∃ value : ℕ, child = some value ∧ parent = some value ∧ 0 < point
  member_transport := by
    rintro point later arrow child parent ⟨value, childSame, parentSame, positive⟩
    exact ⟨value, childSame, parentSame, Nat.lt_of_lt_of_le positive (leOfHom arrow)⟩

def valueMap : NaturalHom values upperValues where
  app _ := some
  naturality _ _ := rfl

def embedding : MembershipEmbedding model upperModel where
  valueMap := valueMap
  injective _ := by
    intro first second same
    exact Option.some.inj same
  member_iff point child parent := by
    constructor
    · rintro ⟨value, childSame, parentSame, positive⟩
      exact ⟨positive, (Option.some.inj childSame).trans (Option.some.inj parentSame).symm⟩
    · rintro ⟨positive, same⟩
      exact ⟨parent, congrArg some same, rfl, positive⟩
  member_onto _ _ child belongs := by
    obtain ⟨value, same, _, _⟩ := belongs
    exact ⟨value, same.symm⟩

def inhabitedParent : Formula 1 := .exist (.both (.member 0 1) (.equal 0 1))

theorem inhabitedParent_bounded : Bounded inhabitedParent := .existIn 0 (.equal 0 1)

theorem bounded_agreement (point value : ℕ) :
    force values model inhabitedParent point (fun _ => value) ↔
      force upperValues upperModel inhabitedParent point (fun _ => some value) :=
  force_iff model upperModel embedding inhabitedParent_bounded point (fun _ => value)

theorem present_parent_empty (value : ℕ) :
    ¬ force values model inhabitedParent 0 (fun _ => value) := by
  rintro ⟨child, belongs, _⟩
  exact Nat.lt_irrefl 0 belongs.1

theorem later_parent_inhabited (value : ℕ) :
    force values model inhabitedParent 1 (fun _ => value) :=
  ⟨value, ⟨Nat.zero_lt_one, rfl⟩, rfl⟩

theorem upper_later_parent_inhabited (value : ℕ) :
    force upperValues upperModel inhabitedParent 1 (fun _ => some value) :=
  (bounded_agreement 1 value).mp (later_parent_inhabited value)

theorem bounded_negation_not_present_absence (value : ℕ) :
    ¬ force values model (.imply inhabitedParent .bottom) 0 (fun _ => value) := by
  intro absent
  exact absent 1 (homOfLE (Nat.zero_le 1)) (later_parent_inhabited value)

theorem infinitely_many_embedded_values : Function.Injective (valueMap.app 0) := by
  intro first second same
  exact Option.some.inj same

theorem added_value_outside_image (point : ℕ) :
    ¬ ∃ value, valueMap.app point value = none := by
  rintro ⟨value, impossible⟩
  change some value = none at impossible
  cases impossible

def everyValueInhabited : Formula 0 := .all (.exist (.member 0 1))

def emptyEnvironment (point : ℕ) : Environment values 0 point := Fin.elim0

def upperEmptyEnvironment (point : ℕ) : Environment upperValues 0 point := Fin.elim0

theorem lower_unbounded_universal :
    force values model everyValueInhabited 1 (emptyEnvironment 1) := by
  intro later arrow value
  exact ⟨value, Nat.lt_of_lt_of_le Nat.zero_lt_one (leOfHom arrow), rfl⟩

theorem upper_unbounded_universal_fails :
    ¬ force upperValues upperModel everyValueInhabited 1 (upperEmptyEnvironment 1) := by
  intro universal
  obtain ⟨child, value, _, impossible, _⟩ := universal 1 (𝟙 1) none
  change (none : Option ℕ) = some value at impossible
  cases impossible

/-- Injectivity and full literal member coverage do not preserve unrestricted
universal formulas on the larger value carrier. -/
theorem unbounded_preservation_fails :
    force values model everyValueInhabited 1 (emptyEnvironment 1) ∧
      ¬ force upperValues upperModel everyValueInhabited 1
        (mapEnvironment valueMap 1 (emptyEnvironment 1)) := by
  refine ⟨lower_unbounded_universal, ?_⟩
  have same : mapEnvironment valueMap 1 (emptyEnvironment 1) = upperEmptyEnvironment 1 := by
    funext index
    exact Fin.elim0 index
  simpa only [same] using upper_unbounded_universal_fails

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedFormulaComparisonControls
