import Mettapedia.TypeTheory.ContextualSmallFamilyUniverseCoherence
import Mettapedia.TypeTheory.ContextualSmallMapControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings

/-!
# Infinite growing and cyclic-parameter universe controls

Two complete future codes have equal present decoded types and different
future carriers. The actual infinite category and its growing positions
therefore distinguish code classification from present-carrier observation.
A second small displayed family depends on an arbitrary bare hyperset
parameter, including its cyclic value, without making that parameter
presheaf small at the original bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyUniverseControls

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualSmallFamilyUniverse
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafBaseChange

def threshold (bound : Nat) : Nat ⥤ Type where
  obj stage := {position : Fin (stage + 1) // bound ≤ stage}
  map {first second} step := TypeCat.ofHom fun position =>
    ⟨Fin.castLE (Nat.succ_le_succ (leOfHom step)) position.val, position.property.trans (leOfHom step)⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro position
    exact Subtype.ext (Fin.ext rfl)
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro position
    exact Subtype.ext (Fin.ext rfl)

def thresholdCode (bound stage : Nat) : Code stage :=
  ContextualSmallFamilyUniverse.restrict (Future.target stage) (threshold bound)

theorem equal_present_decode : decode (thresholdCode 1 0) = decode (thresholdCode 2 0) := by
  change {position : Fin 1 // 1 ≤ 0} = {position : Fin 1 // 2 ≤ 0}
  apply congrArg (fun condition : Prop => {position : Fin 1 // condition})
  apply propext
  exact ⟨fun impossible => (Nat.not_succ_le_self 0 impossible).elim,
    fun impossible => (Nat.not_succ_le_zero 1 impossible).elim⟩

theorem different_whole_codes : thresholdCode 1 0 ≠ thresholdCode 2 0 := by
  intro same
  let future : Future.Objects 0 := ⟨1, homOfLE (Nat.zero_le 1)⟩
  have types : (thresholdCode 1 0).obj future = (thresholdCode 2 0).obj future :=
    congrArg (fun code : Code 0 => code.obj future) same
  let original : (thresholdCode 1 0).obj future := ⟨⟨0, by decide⟩, Nat.le_refl 1⟩
  let impossible : (thresholdCode 2 0).obj future := cast types original
  exact Nat.not_succ_le_self 1 impossible.property

theorem present_decode_does_not_determine_code :
    decode (thresholdCode 1 0) = decode (thresholdCode 2 0) ∧ thresholdCode 1 0 ≠ thresholdCode 2 0 :=
  ⟨equal_present_decode, different_whole_codes⟩

theorem actual_future_becomes_inhabited :
    Nonempty (decode (codeMap (homOfLE (Nat.zero_le 1)) (thresholdCode 1 0))) ∧
      ¬ Nonempty (decode (codeMap (homOfLE (Nat.zero_le 1)) (thresholdCode 2 0))) := by
  constructor
  · exact ⟨⟨⟨0, by decide⟩, Nat.le_refl 1⟩⟩
  · rintro ⟨impossible⟩
    exact Nat.not_succ_le_self 1 impossible.property

def parameters : Nat ⥤ Type 1 := ContextualSmallMapControls.ambient

def cyclicSmall : parameters.Elements ⥤ Type where
  obj point := Fin (point.1 + 1) × {tag : Bool // tag = false ∨ point.2 = HSet.quineAtom}
  map {first second} step := TypeCat.ofHom fun member =>
    ⟨Fin.castLE (Nat.succ_le_succ (leOfHom step.1)) member.1,
      ⟨member.2.val, by
        rcases member.2.property with falseTag | cyclic
        · exact Or.inl falseTag
        · have materialEq : first.2 = second.2 := step.2
          exact Or.inr (materialEq.symm.trans cyclic)⟩⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro member
    exact Prod.ext (Fin.ext rfl) (Subtype.ext rfl)
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro member
    exact Prod.ext (Fin.ext rfl) (Subtype.ext rfl)

def parameter (stage : Nat) (material : HSet.{0}) : parameters.Elements := ⟨stage, material⟩

def falseMember (stage : Nat) (material : HSet.{0}) : cyclicSmall.obj (parameter stage material) :=
  ⟨⟨0, Nat.zero_lt_succ stage⟩, ⟨false, Or.inl rfl⟩⟩

def cyclicMember (stage : Nat) : cyclicSmall.obj (parameter stage HSet.quineAtom) :=
  ⟨⟨0, Nat.zero_lt_succ stage⟩, ⟨true, Or.inr rfl⟩⟩

theorem empty_members_have_false_tag (stage : Nat)
    (member : cyclicSmall.obj (parameter stage (∅ : HSet.{0}))) : member.2.val = false := by
  rcases member.2.property with falseTag | cyclic
  · exact falseTag
  · exact (HSet.empty_ne_quineAtom cyclic).elim

theorem cyclic_fibre_retains_extra_tag (stage : Nat) :
    (cyclicMember stage).2.val = true ∧
      ∀ member : cyclicSmall.obj (parameter stage (∅ : HSet.{0})), member.2.val = false :=
  ⟨rfl, empty_members_have_false_tag stage⟩

theorem parameter_object_has_no_small_cover {I : Type} (reading : I → parameters.obj 0) :
    ¬ Function.Surjective reading := ContextualSmallMapControls.ambient_has_no_small_global_cover reading

def operation : NaturalHom parameters universeFamily := classifier cyclicSmall

theorem actual_whole_family_decodes : decodedFamily operation = cyclicSmall := decoded_classifier_eq cyclicSmall

def selected (stage : Nat) : TotalAt cyclicSmall stage := ⟨HSet.quineAtom, cyclicMember stage⟩

theorem classification_whole_inverse (stage : Nat) :
    (classificationBackward cyclicSmall).app stage ((classificationForward cyclicSmall).app stage (selected stage)) =
      selected stage := classification_left cyclicSmall stage (selected stage)

theorem classified_retains_parameter (stage : Nat) :
    ((classificationForward cyclicSmall).app stage (selected stage)).val.2 = HSet.quineAtom := rfl

theorem classified_selected_value_heq (stage : Nat) :
    HEq ((classified cyclicSmall).app stage (selected stage)).2 (cyclicMember stage) :=
  classified_value_heq cyclicSmall stage (selected stage)

theorem material_parameter_changes_code :
    operation.app 0 HSet.quineAtom ≠ operation.app 0 (∅ : HSet.{0}) := by
  intro same
  have types : cyclicSmall.obj (parameter 0 HSet.quineAtom) =
      cyclicSmall.obj (parameter 0 (∅ : HSet.{0})) :=
    congrArg (fun code : Code 0 => decode code) same
  let comparison := typeEqualityEquiv types
  have unique : ∀ first second : cyclicSmall.obj (parameter 0 (∅ : HSet.{0})), first = second := by
    intro first second
    apply Prod.ext
    · exact Subsingleton.elim (α := Fin 1) _ _
    · exact Subtype.ext ((empty_members_have_false_tag 0 first).trans
        (empty_members_have_false_tag 0 second).symm)
  have members : cyclicMember 0 = falseMember 0 HSet.quineAtom :=
    comparison.injective (unique (comparison (cyclicMember 0)) (comparison (falseMember 0 HSet.quineAtom)))
  have impossible : true = false := congrArg (fun member : cyclicSmall.obj (parameter 0 HSet.quineAtom) =>
    member.2.val) members
  cases impossible

def newCyclicMember (stage : Nat) : cyclicSmall.obj (parameter (stage + 1) HSet.quineAtom) :=
  ⟨⟨stage + 1, Nat.lt_succ_self (stage + 1)⟩, ⟨true, Or.inr rfl⟩⟩

def cyclicMove (stage : Nat) : parameter stage HSet.quineAtom ⟶ parameter (stage + 1) HSet.quineAtom :=
  CategoryOfElements.homMk (F := parameters) _ _ (homOfLE (Nat.le_succ stage)) rfl

theorem genuinely_new_future_member (stage : Nat) :
    ¬ ∃ original : cyclicSmall.obj (parameter stage HSet.quineAtom),
      cyclicSmall.map (cyclicMove stage) original = newCyclicMember stage := by
  rintro ⟨original, same⟩
  have position : original.1.val = stage + 1 := congrArg
    (fun member : cyclicSmall.obj (parameter (stage + 1) HSet.quineAtom) => member.1.val) same
  exact (Nat.ne_of_lt original.1.isLt) position

theorem decoder_restriction_retains_new_future (stage : Nat) :
    Nonempty (decode (codeMap (homOfLE (Nat.le_succ stage)) (operation.app stage HSet.quineAtom))) :=
  ⟨newCyclicMember stage⟩

def terminalChange : NaturalHom (ContextualWitnessCover.terminal (E := Nat)) parameters where
  app _ _ := HSet.quineAtom
  naturality _ _ := rfl

def cyclicSection : (total (substitutedFamily cyclicSmall terminalChange)).sections :=
  ⟨fun stage => ⟨PUnit.unit, cyclicMember stage⟩, by
    intro first second step
    exact Sigma.ext rfl (heq_of_eq (Prod.ext (Fin.ext rfl) (Subtype.ext rfl)))⟩

def classifiedSection : (ClassificationPullback (substitutedFamily cyclicSmall terminalChange)).sections :=
  classificationSectionEquiv (substitutedFamily cyclicSmall terminalChange) cyclicSection

theorem classified_section_whole_inverse :
    (classificationSectionEquiv (substitutedFamily cyclicSmall terminalChange)).symm classifiedSection =
      cyclicSection :=
  (classificationSectionEquiv (substitutedFamily cyclicSmall terminalChange)).symm_apply_apply cyclicSection

theorem actual_substitution_square :
    (substitutedTotalMap cyclicSmall terminalChange).comp (classified cyclicSmall) =
      classified (substitutedFamily cyclicSmall terminalChange) := classified_substitution cyclicSmall terminalChange

def pairedParameters : Nat ⥤ Type 1 where
  obj _ := HSet.{0} × HSet.{0}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def selectFirst : NaturalHom pairedParameters parameters where
  app _ := Prod.fst
  naturality _ _ := rfl

def firstParameter : pairedParameters.obj 0 := (HSet.quineAtom, ∅)
def secondParameter : pairedParameters.obj 0 := (HSet.quineAtom, HSet.quineAtom)

theorem distinct_parameters : firstParameter ≠ secondParameter :=
  fun same => HSet.empty_ne_quineAtom (congrArg Prod.snd same)

theorem noninjective_parameter_map : ¬ Function.Injective (selectFirst.app 0) :=
  fun injective => distinct_parameters (injective (a₁ := firstParameter) (a₂ := secondParameter) rfl)

theorem equal_codes_distinct_parameters :
    (classifier (substitutedFamily cyclicSmall selectFirst)).app 0 firstParameter =
        (classifier (substitutedFamily cyclicSmall selectFirst)).app 0 secondParameter ∧
      firstParameter ≠ secondParameter :=
  ⟨(familyCode_substitution cyclicSmall selectFirst 0 firstParameter).trans
    (familyCode_substitution cyclicSmall selectFirst 0 secondParameter).symm, distinct_parameters⟩

def firstSelected : TotalAt (substitutedFamily cyclicSmall selectFirst) 0 :=
  ⟨firstParameter, cyclicMember 0⟩

def secondSelected : TotalAt (substitutedFamily cyclicSmall selectFirst) 0 :=
  ⟨secondParameter, cyclicMember 0⟩

theorem literal_classification_retains_distinct_parameters :
    (classificationForward (substitutedFamily cyclicSmall selectFirst)).app 0 firstSelected ≠
      (classificationForward (substitutedFamily cyclicSmall selectFirst)).app 0 secondSelected := by
  intro same
  exact distinct_parameters (congrArg (fun receipt :
    (ClassificationPullback (substitutedFamily cyclicSmall selectFirst)).obj 0 => receipt.val.2) same)

theorem actual_noninjective_substitution_square :
    (substitutedTotalMap cyclicSmall selectFirst).comp (classified cyclicSmall) =
      classified (substitutedFamily cyclicSmall selectFirst) := classified_substitution cyclicSmall selectFirst

namespace Histories

open LabelledContextPaths

def historyCode (label : Nat) : Code initial where
  obj future := PLift (∃ rest, future.2.val = label :: rest)
  map {first second} step := TypeCat.ofHom fun available => ⟨by
    obtain ⟨rest, starts⟩ := available.down
    have triangle := congrArg (fun arrow : initial ⟶ second.1 => arrow.val) step.2
    change first.2.val ++ step.1.val = second.2.val at triangle
    refine ⟨rest ++ step.1.val, ?_⟩
    rw [← triangle, starts]
    rfl⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro available
    exact Subsingleton.elim _ _
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro available
    exact Subsingleton.elim _ _

theorem same_present_decode (first second : Nat) : decode (historyCode first) = decode (historyCode second) := by
  change PLift (∃ rest, [] = first :: rest) = PLift (∃ rest, [] = second :: rest)
  apply congrArg (fun condition : Prop => PLift condition)
  apply propext
  constructor
  · rintro ⟨rest, impossible⟩
    cases impossible
  · rintro ⟨rest, impossible⟩
    cases impossible

/-- Infinitely many parallel arrows to the same future context are observed
by different whole codes even though all present decoded types coincide. -/
theorem history_codes_injective : Function.Injective historyCode := by
  intro first second same
  let future : Future.Objects initial := ⟨next, extension first⟩
  have types : (historyCode first).obj future = (historyCode second).obj future :=
    congrArg (fun code : Code initial => code.obj future) same
  let original : (historyCode first).obj future := ⟨⟨[], rfl⟩⟩
  let observed : (historyCode second).obj future := cast types original
  obtain ⟨rest, labels⟩ := observed.down
  exact (List.cons.inj labels).1

theorem same_endpoint_different_code_values :
    (⟨next, extension 0⟩ : Future.Objects initial).1 = (⟨next, extension 1⟩ : Future.Objects initial).1 ∧
      Nonempty ((historyCode 0).obj ⟨next, extension 0⟩) ∧
      ¬ Nonempty ((historyCode 0).obj ⟨next, extension 1⟩) := by
  refine ⟨rfl, ⟨⟨⟨[], rfl⟩⟩⟩, ?_⟩
  rintro ⟨observed⟩
  obtain ⟨rest, labels⟩ := observed.down
  exact Nat.zero_ne_one (List.cons.inj labels).1.symm

end Histories

end Mettapedia.TypeTheory.ContextualSmallFamilyUniverseControls
