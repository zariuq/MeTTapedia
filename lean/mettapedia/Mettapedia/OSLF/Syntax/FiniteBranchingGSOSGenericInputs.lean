import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSPresentation
import Mettapedia.TypeTheory.IndexedPolynomialFreeFiniteSupport
import Mettapedia.CategoryTheory.FiniteSupportInterpolation
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin

/-!
# Distinct generic successors and finite target support

For finite action carriers each complete availability profile has an
independent finite carrier of positive occurrences. The generic behavior
contains exactly those distinct occurrence names. Arbitrary input behavior
is obtained by a separately supplied complete successor assignment.

Collapsing each nonempty action to one generic successor bounds every
target's leaf occurrences by a finite readout of the actual law. Variable
identifications preserve that occurrence count. This is the finite bound
used later to interpolate complete successor assignments away from the
names actually read by a target.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises.Generic

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Classical

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable [∀ sort, Finite (Actions sort)]

instance addressFinite {sort : S.Srt} (operator : S.Operator sort) :
    Finite (Address (Actions := Actions) operator) := by
  let _ : Finite (S.Position operator) := S.finite operator
  infer_instance

instance addressFintype {sort : S.Srt} (operator : S.Operator sort) :
    Fintype (Address (Actions := Actions) operator) := Fintype.ofFinite _

abbrev Counts {sort : S.Srt} (operator : S.Operator sort) :=
  Address (Actions := Actions) operator → Nat

/-- Complete finite multiplicities of separately named positive occurrences. -/
def pattern {sort : S.Srt} {operator : S.Operator sort} (counts : Counts (Actions := Actions) operator) :
    Pattern (Actions := Actions) operator where
  Occurrence := Σ address, Fin (counts address)
  finite := inferInstance
  address := Sigma.fst
  negative := Finset.univ.filter (fun address => counts address = 0)

abbrev Family {sort : S.Srt} {operator : S.Operator sort} (counts : Counts (Actions := Actions) operator) :=
  variableFamily (pattern counts)

def arguments {sort : S.Srt} {operator : S.Operator sort} (counts : Counts (Actions := Actions) operator) :
    S.Arguments ((sourceBehaviourFunctor S Actions).obj (Family counts)) operator :=
  fun position => (.original position, fun action =>
    Finset.univ.image (fun slot : Fin (counts ⟨position, action⟩) =>
      Variable.derivative (S := S) (Actions := Actions) (operator := operator) (pattern := pattern counts) ⟨⟨position, action⟩, slot⟩))

/-- A complete successor assignment with the original source arguments retained. -/
def assignment {sort : S.Srt} {operator : S.Operator sort}
    (counts : Counts (Actions := Actions) operator) {X : S.Families}
    (originals : S.Arguments X operator)
    (derivatives : ∀ address, Fin (counts address) → X PUnit.unit (S.argument operator address.1)) :
    Family counts ⟶ X :=
  Input.assignment (⟨originals, fun occurrence => derivatives occurrence.1 occurrence.2⟩ :
    Input (pattern counts) X)

theorem assigned_arguments {sort : S.Srt} {operator : S.Operator sort}
    (counts : Counts (Actions := Actions) operator) {X : S.Families}
    (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (derivatives : ∀ address, Fin (counts address) → X PUnit.unit (S.argument operator address.1))
    (covers : ∀ address, Finset.univ.image (derivatives address) = (supplied address.1).2 address.2) :
    mapArguments (assignment counts (fun position => (supplied position).1) derivatives)
      (arguments counts) = supplied := by
  funext position
  apply Prod.ext
  · rfl
  · funext action
    change Mettapedia.CategoryTheory.FinitePowerset.map
      (assignment counts (fun position => (supplied position).1) derivatives PUnit.unit (S.argument operator position))
      (Finset.univ.image (fun slot => Variable.derivative (S := S) (Actions := Actions) (operator := operator) (pattern := pattern counts) ⟨⟨position, action⟩, slot⟩)) = _
    change (Finset.univ.image (fun slot => Variable.derivative (S := S) (Actions := Actions) (operator := operator) (pattern := pattern counts) ⟨⟨position, action⟩, slot⟩)).image
      (assignment counts (fun position => (supplied position).1) derivatives PUnit.unit (S.argument operator position)) = _
    rw [Finset.image_image]
    exact covers ⟨position, action⟩

def readout {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (counts : Counts (Actions := Actions) operator) (action : Actions sort) :
    Finset (S.Term (Family counts) sort) :=
  law.app (Family counts) PUnit.unit sort ⟨operator, arguments counts⟩ action

/-- The complete assignment square follows from the supplied law's actual naturality. -/
theorem readout_assignment {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (counts : Counts (Actions := Actions) operator) (action : Actions sort)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (derivatives : ∀ address, Fin (counts address) → X PUnit.unit (S.argument operator address.1))
    (covers : ∀ address, Finset.univ.image (derivatives address) = (supplied address.1).2 address.2) :
    Mettapedia.CategoryTheory.FinitePowerset.map
      (S.rename (assignment counts (fun position => (supplied position).1) derivatives))
      (readout law counts action) = law.app X PUnit.unit sort ⟨operator, supplied⟩ action := by
  have natural := congrArg (fun mapping => mapping PUnit.unit sort ⟨operator, arguments counts⟩ action)
    (law.naturality (assignment counts (fun position => (supplied position).1) derivatives))
  change law.app X PUnit.unit sort ⟨operator,
      mapArguments (assignment counts (fun position => (supplied position).1) derivatives)
        (arguments counts)⟩ action = _ at natural
  rw [assigned_arguments counts supplied derivatives covers] at natural
  exact natural.symm

/-- Action-availability patterns are finite for the stated finite action profile. -/
abbrev Guard {sort : S.Srt} (operator : S.Operator sort) :=
  Address (Actions := Actions) operator → Bool

def enabled {sort : S.Srt} {operator : S.Operator sort}
    (counts : Counts (Actions := Actions) operator) : Guard (Actions := Actions) operator :=
  fun address => decide (0 < counts address)

def singletonCounts {sort : S.Srt} {operator : S.Operator sort}
    (guard : Guard (Actions := Actions) operator) : Counts (Actions := Actions) operator :=
  fun address => if guard address = true then 1 else 0

def boundedCounts {sort : S.Srt} {operator : S.Operator sort}
    (guard : Guard (Actions := Actions) operator) (capacity : Nat) : Counts (Actions := Actions) operator :=
  fun address => if guard address = true then capacity else 0

def inputGuard {X : S.Families} {sort : S.Srt} {operator : S.Operator sort}
    (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator) :
    Guard (Actions := Actions) operator :=
  fun address => decide ((supplied address.1).2 address.2 ≠ ∅)

def collapse {sort : S.Srt} {operator : S.Operator sort}
    (counts : Counts (Actions := Actions) operator) :
    Family counts ⟶ Family (singletonCounts (enabled counts)) :=
  assignment counts (fun position => Variable.original (S := S) (Actions := Actions) (operator := operator) (pattern := pattern (singletonCounts (enabled counts))) position) (fun address slot =>
    Variable.derivative (S := S) (Actions := Actions) (operator := operator) (pattern := pattern (singletonCounts (enabled counts))) ⟨address, ⟨0, by
      have positive : 0 < counts address := Nat.lt_of_le_of_lt (Nat.zero_le _) slot.isLt
      simp [singletonCounts, enabled, positive]⟩⟩)

theorem collapse_arguments {sort : S.Srt} {operator : S.Operator sort}
    (counts : Counts (Actions := Actions) operator) :
    mapArguments (collapse counts) (arguments counts) = arguments (singletonCounts (enabled counts)) := by
  unfold collapse
  refine assigned_arguments counts (arguments (singletonCounts (enabled counts)))
    (fun address slot => Variable.derivative (S := S) (Actions := Actions) (operator := operator) (pattern := pattern (singletonCounts (enabled counts)))
      ⟨address, ⟨0, by
        have positive : 0 < counts address := Nat.lt_of_le_of_lt (Nat.zero_le _) slot.isLt
        simp [singletonCounts, enabled, positive]⟩⟩) ?_
  intro address
  dsimp only [arguments]
  by_cases positive : 0 < counts address
  · have firstNonempty : (Finset.univ : Finset (Fin (counts address))).Nonempty :=
      ⟨⟨0, positive⟩, Finset.mem_univ _⟩
    have other : singletonCounts (enabled counts) address = 1 := by
      simp [singletonCounts, enabled, positive]
    apply Finset.ext
    intro value
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨slot, _, rfl⟩
      exact ⟨⟨0, by simp [other]⟩, Finset.mem_univ _, rfl⟩
    · rintro ⟨slot, _, rfl⟩
      refine ⟨⟨0, positive⟩, Finset.mem_univ _, ?_⟩
      congr 2
      apply Fin.ext
      have bound : slot.val < singletonCounts (enabled counts) address := slot.isLt
      omega
  · have first : counts address = 0 := by omega
    have other : singletonCounts (enabled counts) address = 0 := by
      simp [singletonCounts, enabled, positive]
    apply Finset.ext
    intro value
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨slot, _, _⟩
      have impossible := slot.isLt
      omega
    · rintro ⟨slot, _, _⟩
      have impossible : slot.val < singletonCounts (enabled counts) address := slot.isLt
      omega

def leafCount {X : S.Families} {sort : S.Srt} (term : S.Term X sort) : Nat :=
  IndexedPolynomial.Free.leafCount S.polynomial (fun shape => S.finite shape) PUnit.unit sort term

theorem leafCount_rename {X Y : S.Families} (mapping : X ⟶ Y) {sort : S.Srt}
    (term : S.Term X sort) : leafCount (S.rename mapping term) = leafCount term :=
  IndexedPolynomial.Free.leafCount_map S.polynomial (fun shape => S.finite shape)
    (fun base index => mapping base index) PUnit.unit sort term

/-- The finite generic readout bounds whole tree occurrences, independently
of the cardinalities of the separately supplied successor sets. -/
def budget {sort : S.Srt} {operator : S.Operator sort} (law : Law S Actions)
    (guard : Guard (Actions := Actions) operator) (action : Actions sort) : Nat :=
  (readout law (singletonCounts guard) action).sup leafCount

theorem leafCount_le_budget {sort : S.Srt} {operator : S.Operator sort} (law : Law S Actions)
    (counts : Counts (Actions := Actions) operator) (action : Actions sort)
    (term : S.Term (Family counts) sort) (member : term ∈ readout law counts action) :
    leafCount term ≤ budget law (enabled counts) action := by
  have natural := congrArg (fun mapping => mapping PUnit.unit sort ⟨operator, arguments counts⟩ action)
    (law.naturality (collapse counts))
  change law.app _ PUnit.unit sort ⟨operator, mapArguments (collapse counts) (arguments counts)⟩ action =
    Mettapedia.CategoryTheory.FinitePowerset.map (S.rename (collapse counts))
      (readout law counts action) at natural
  rw [collapse_arguments] at natural
  have mapped : S.rename (collapse counts) term ∈ readout law (singletonCounts (enabled counts)) action := by
    rw [readout, natural]
    exact (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mpr ⟨term, member, rfl⟩
  exact (leafCount_rename (collapse counts) term).symm.le.trans (Finset.le_sup mapped)

abbrev Name {sort : S.Srt} {operator : S.Operator sort} (counts : Counts (Actions := Actions) operator) :=
  S.Position operator ⊕ (Σ address, Fin (counts address))

def name {sort : S.Srt} {operator : S.Operator sort} (counts : Counts (Actions := Actions) operator) :
    ∀ base index, Family counts base index → Name counts :=
  fun base index value => match base, value with
  | .unit, .original position => .inl position
  | .unit, .derivative occurrence => .inr occurrence

def support {sort : S.Srt} {operator : S.Operator sort} {counts : Counts (Actions := Actions) operator}
    (term : S.Term (Family counts) sort) : Finset (Name counts) :=
  IndexedPolynomial.Free.support S.polynomial (fun shape => S.finite shape) (name counts)
    PUnit.unit sort term

def usedSlots {sort : S.Srt} {operator : S.Operator sort} {counts : Counts (Actions := Actions) operator}
    (term : S.Term (Family counts) sort) (address : Address (Actions := Actions) operator) :
    Finset (Fin (counts address)) :=
  Finset.univ.filter (fun slot => Sum.inr ⟨address, slot⟩ ∈ support term)

theorem usedSlots_card_le_count {sort : S.Srt} {operator : S.Operator sort}
    {counts : Counts (Actions := Actions) operator} (term : S.Term (Family counts) sort)
    (address : Address (Actions := Actions) operator) :
    (usedSlots term address).card ≤ counts address := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (by simp only [Finset.card_univ, Fintype.card_fin, le_refl])

theorem usedSlots_card_le {sort : S.Srt} {operator : S.Operator sort}
    {counts : Counts (Actions := Actions) operator} (term : S.Term (Family counts) sort)
    (address : Address (Actions := Actions) operator) :
    (usedSlots term address).card ≤ leafCount term := by
  have bound : (usedSlots term address).card ≤ (support term).card := by
    apply Finset.card_le_card_of_injOn (fun slot => Sum.inr ⟨address, slot⟩)
    · intro slot member
      exact (Finset.mem_filter.mp member).2
    · intro first _ second _ same
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj same)).2
  exact bound.trans (IndexedPolynomial.Free.support_card_le S.polynomial
    (fun shape => S.finite shape) (name counts) PUnit.unit sort term)

/-- Equality of supplied readings on the retained slots proves equality of
the complete relabeled target, preserving original argument positions. -/
theorem rename_assignment_eq {sort : S.Srt} {operator : S.Operator sort}
    {counts : Counts (Actions := Actions) operator} (term : S.Term (Family counts) sort)
    {X : S.Families} (originals : S.Arguments X operator)
    (first second : ∀ address, Fin (counts address) → X PUnit.unit (S.argument operator address.1))
    (agrees : ∀ address slot, slot ∈ usedSlots term address → first address slot = second address slot) :
    S.rename (assignment counts originals first) term = S.rename (assignment counts originals second) term := by
  apply IndexedPolynomial.Free.map_eq_of_support S.polynomial (fun shape => S.finite shape) (name counts)
  intro index value member
  cases value with
  | original position => rfl
  | derivative occurrence =>
      exact agrees occurrence.1 occurrence.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, member⟩)

end Mettapedia.OSLF.FiniteBranching.Premises.Generic
