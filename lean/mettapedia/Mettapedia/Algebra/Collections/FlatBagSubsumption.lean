import Mettapedia.Algebra.Collections.FlatBagUnifiers
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets

/-!
# Decidable flat-bag family factorization on finite active names

The target family supplies a finite alphabet of observed element outputs and
rest elements. Active variables supply safe fallback tokens. The checker
enumerates functions into that alphabet and verifies element equations,
multiset prefix containment and equality of the two common remainders.
The completeness proof clips arbitrary witnesses only where their outputs
cannot affect any source-family observation. The constant type need not be
finite.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.FlatBagSubsumption

open FlatElementEncoding (Element apply)
open FlatBagUnifiers (Family Answer RestSlot instantiate genericAnswer MoreGeneral)

variable {A X : Type*} [DecidableEq A] [DecidableEq X]

def mapped (family : Family A X) (assignment : X → Element A X) (slot : RestSlot) : Multiset (Element A X) :=
  (family.base slot).map (apply assignment)

def Checks (general specific : Family A X) (assignment : X → Element A X) : Prop :=
  (∀ name, specific.elements name = apply assignment (general.elements name)) ∧
    mapped general assignment .left ≤ specific.base .left ∧
    mapped general assignment .right ≤ specific.base .right ∧
    specific.base .left - mapped general assignment .left =
      specific.base .right - mapped general assignment .right

/-- Prefix containment is essential: equal truncated differences alone do
not certify a factorization. -/
theorem checks_iff (general specific : Family A X) (assignment : X → Element A X) :
    Checks general specific assignment ↔ ∃ common, genericAnswer specific = instantiate general assignment common := by
  constructor
  · rintro ⟨elements, left, right, equalRemainders⟩
    refine ⟨specific.base .left - mapped general assignment .left, ?_⟩
    apply Answer.ext
    · exact funext elements
    · funext slot
      cases slot with
      | left => exact (add_tsub_cancel_of_le left).symm
      | right =>
        change specific.base .right = mapped general assignment .right +
          (specific.base .left - mapped general assignment .left)
        rw [equalRemainders]
        exact (add_tsub_cancel_of_le right).symm
  · rintro ⟨common, represented⟩
    have elements := congrArg Answer.elements represented
    have rests := congrArg Answer.rest represented
    have restEq (slot : RestSlot) : specific.base slot = mapped general assignment slot + common := congrFun rests slot
    refine ⟨fun name => congrFun elements name, ?_, ?_, ?_⟩
    · rw [restEq]
      exact Multiset.le_add_right _ _
    · rw [restEq]
      exact Multiset.le_add_right _ _
    · rw [restEq .left, restEq .right, add_tsub_cancel_left, add_tsub_cancel_left]

variable [Fintype X]

def targetAlphabet (specific : Family A X) : Finset (Element A X) :=
  Finset.univ.image specific.elements ∪ (specific.base .left).toFinset ∪ (specific.base .right).toFinset ∪
    Finset.univ.image (Sum.inr : X → Element A X)

theorem element_mem_target (specific : Family A X) (name : X) : specific.elements name ∈ targetAlphabet specific := by
  simp only [targetAlphabet, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Finset.mem_image.mpr ⟨name, Finset.mem_univ _, rfl⟩)))

theorem base_mem_target (specific : Family A X) (slot : RestSlot) (element : Element A X)
    (member : element ∈ specific.base slot) : element ∈ targetAlphabet specific := by
  cases slot <;> simp [targetAlphabet, member]

theorem variable_mem_target (specific : Family A X) (name : X) : Sum.inr name ∈ targetAlphabet specific := by
  simp [targetAlphabet]

def clip (specific : Family A X) (assignment : X → Element A X) : X → ↑(targetAlphabet specific) :=
  fun name => if member : assignment name ∈ targetAlphabet specific then ⟨assignment name, member⟩
    else ⟨.inr name, variable_mem_target specific name⟩

theorem clip_apply_eq (specific : Family A X) (assignment : X → Element A X) (element : Element A X)
    (observed : apply assignment element ∈ targetAlphabet specific) :
    apply (fun name => (clip specific assignment name).val) element = apply assignment element := by
  cases element with
  | inl value => rfl
  | inr name =>
    change assignment name ∈ targetAlphabet specific at observed
    simp only [FlatElementEncoding.apply_variable, clip, dif_pos observed]

/-- A factorization witness's relevant outputs already occur in the target.
Clipping every other output therefore preserves all actual family fields. -/
theorem clipped_checks (general specific : Family A X) (assignment : X → Element A X)
    (common : Multiset (Element A X)) (represented : genericAnswer specific = instantiate general assignment common) :
    Checks general specific (fun name => (clip specific assignment name).val) := by
  have checked := (checks_iff general specific assignment).mpr ⟨common, represented⟩
  have elements (name : X) : apply (fun name => (clip specific assignment name).val) (general.elements name) =
      apply assignment (general.elements name) := by
    apply clip_apply_eq
    rw [← checked.1 name]
    exact element_mem_target specific name
  have restEq (slot : RestSlot) : specific.base slot = mapped general assignment slot + common :=
    congrFun (congrArg Answer.rest represented) slot
  have prefixes (slot : RestSlot) : mapped general (fun name => (clip specific assignment name).val) slot =
      mapped general assignment slot := by
    apply Multiset.map_congr rfl
    intro element member
    apply clip_apply_eq
    apply base_mem_target specific slot
    rw [restEq]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_map_of_mem (apply assignment) member))
  refine ⟨fun name => (checked.1 name).trans (elements name).symm, ?_, ?_, ?_⟩
  · rw [prefixes]
    exact checked.2.1
  · rw [prefixes]
    exact checked.2.2.1
  · rw [prefixes, prefixes]
    exact checked.2.2.2

instance (general specific : Family A X) (assignment : X → Element A X) : Decidable (Checks general specific assignment) := by
  unfold Checks
  infer_instance

/-- Actual finite candidates filtered by decidable algebraic conditions. -/
def candidates (general specific : Family A X) : Finset (X → ↑(targetAlphabet specific)) :=
  Finset.univ.filter fun encoded => Checks general specific (fun name => (encoded name).val)

def check (general specific : Family A X) : Bool := decide (candidates general specific).Nonempty

theorem check_sound (general specific : Family A X) (accepted : check general specific = true) : MoreGeneral general specific := by
  have nonempty : (candidates general specific).Nonempty := of_decide_eq_true accepted
  obtain ⟨encoded, member⟩ := nonempty
  have checked := (Finset.mem_filter.mp member).2
  obtain ⟨common, represented⟩ := (checks_iff general specific _).mp checked
  exact ⟨fun name => (encoded name).val, common, represented⟩

theorem check_complete (general specific : Family A X) (covers : MoreGeneral general specific) : check general specific = true := by
  obtain ⟨assignment, common, represented⟩ := covers
  apply decide_eq_true_eq.mpr
  exact ⟨clip specific assignment, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, clipped_checks general specific assignment common represented⟩⟩

theorem check_iff (general specific : Family A X) : check general specific = true ↔ MoreGeneral general specific :=
  ⟨check_sound general specific, check_complete general specific⟩

/-- The semantic relation is decidable because the finite checker is exact,
not because a semantic decision procedure was assumed. -/
instance decidableMoreGeneral : DecidableRel (MoreGeneral : Family A X → Family A X → Prop) :=
  fun general specific => decidable_of_iff (check general specific = true) (check_iff general specific)

namespace Controls

def freeFamily : Family Nat (Fin 1) := ⟨Sum.inr, fun _ => 0⟩
def commonExtension : Family Nat (Fin 1) := ⟨fun _ => .inl 7, fun _ => {.inl 8}⟩
def mismatchedRests : Family Nat (Fin 1) :=
  ⟨fun _ => .inl 7, fun slot => match slot with | .left => {.inl 8} | .right => 0⟩

theorem common_extension_is_accepted : check freeFamily commonExtension = true := by
  apply check_complete
  refine ⟨fun _ => .inl 7, {.inl 8}, ?_⟩
  apply Answer.ext
  · rfl
  · funext slot
    simp [genericAnswer, instantiate, freeFamily, commonExtension]

theorem distinct_remainders_are_rejected : check freeFamily mismatchedRests = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  obtain ⟨assignment, common, represented⟩ := check_sound freeFamily mismatchedRests accepted
  have left := congrFun (congrArg Answer.rest represented) RestSlot.left
  have right := congrFun (congrArg Answer.rest represented) RestSlot.right
  have leftEq : ({Sum.inl 8} : Multiset (Element Nat (Fin 1))) = common := by
    simpa [genericAnswer, instantiate, freeFamily, mismatchedRests] using left
  have rightEq : (0 : Multiset (Element Nat (Fin 1))) = common := by
    simpa [genericAnswer, instantiate, freeFamily, mismatchedRests] using right
  have impossible := leftEq.trans rightEq.symm
  simpa using congrArg Multiset.card impossible

def forcedPrefix : Family Nat (Fin 1) := ⟨Sum.inr, fun _ => {.inl 8}⟩

theorem equal_truncated_remainders_do_not_suffice :
    (freeFamily.base .left - mapped forcedPrefix Sum.inr .left) =
      (freeFamily.base .right - mapped forcedPrefix Sum.inr .right) ∧
      check forcedPrefix freeFamily = false := by
  refine ⟨rfl, Bool.eq_false_iff.mpr ?_⟩
  intro accepted
  obtain ⟨assignment, common, represented⟩ := check_sound forcedPrefix freeFamily accepted
  have left := congrFun (congrArg Answer.rest represented) RestSlot.left
  have impossible := congrArg Multiset.card left
  simp [genericAnswer, instantiate, freeFamily, forcedPrefix] at impossible

def hiddenVariable : Family Nat (Fin 1) := ⟨fun _ => .inl 0, fun _ => 0⟩

theorem unobserved_foreign_image_is_clipped (name : Fin 1) :
    (clip hiddenVariable (fun _ => .inl 999) name).val = .inr name := by
  simp [clip, targetAlphabet, hiddenVariable]

theorem no_active_variables_need_no_fallback :
    check (⟨Fin.elim0, fun _ => 0⟩ : Family Empty (Fin 0)) ⟨Fin.elim0, fun _ => 0⟩ = true :=
  check_complete _ _ (FlatBagUnifiers.MoreGeneral.refl _)

end Controls

end Mettapedia.Algebra.Collections.FlatBagSubsumption

#print axioms Mettapedia.Algebra.Collections.FlatBagSubsumption.check_iff
#print axioms Mettapedia.Algebra.Collections.FlatBagSubsumption.decidableMoreGeneral
