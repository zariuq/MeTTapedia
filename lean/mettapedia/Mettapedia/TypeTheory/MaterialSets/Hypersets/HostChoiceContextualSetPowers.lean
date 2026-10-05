import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretation

/-!
# Original-bound internal powersets on complete futures

A child enumeration has original-bound receipts at every actual future.
Stable truth on these receipts is saturated across equal readings: identity
future moves compare duplicate receipts in both directions. The interpreted
predicate uses every receipt with that truth and has a constructed filtered
cover. Its actual set value is supplied by the proved inverse final structure.

These small codes enumerate every all-future subset of a set, not only its
present child subsets. The resulting internal powerset is natural and retains
the original receipt bound `u`, while set values inhabit `Type (u+1)`.
External host Choice supplies the child enumerations and final inverse.
Full proposition-valued receipt predicates are used explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetPowers

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open Mettapedia.TypeTheory.ContextualWitnessCover
open PowerClassPresheafBaseChange

universe u
variable {D : Type u} [Category.{u} D]

def Subset (point : D) (first second : sets.obj point) : Prop :=
  ∀ argument : Arguments sets point,
    (unfold.app point first).val.holds argument → (unfold.app point second).val.holds argument

theorem subset_iff_future_members (point : D) (first second : sets.obj point) :
    Subset point first second ↔
      ∀ (target : D) (arrow : point ⟶ target) (child : sets.obj target),
        Member target child (sets.map arrow first) → Member target child (sets.map arrow second) := by
  constructor
  · intro included target arrow child belongs
    exact (futureMember_iff arrow child second).mp
      (included ⟨⟨target, arrow⟩, child⟩ ((futureMember_iff arrow child first).mpr belongs))
  · intro included
    rintro ⟨⟨target, arrow⟩, child⟩ belongs
    exact (futureMember_iff arrow child second).mpr
      (included target arrow child ((futureMember_iff arrow child first).mp belongs))

theorem subset_refl (point : D) (value : sets.obj point) : Subset point value value :=
  fun _ belongs => belongs

theorem subset_trans (point : D) {first second third : sets.obj point}
    (earlier : Subset point first second) (later : Subset point second third) :
    Subset point first third := fun argument belongs => later argument (earlier argument belongs)

theorem subset_antisymm (point : D) {first second : sets.obj point}
    (forward : Subset point first second) (backward : Subset point second first) : first = second := by
  apply (internal_extensionality point first second).mp
  intro target arrow child
  exact ⟨(subset_iff_future_members point first second).mp forward target arrow child,
    (subset_iff_future_members point second first).mp backward target arrow child⟩

theorem empty_subset (point : D) (parent : sets.obj point) : Subset point (emptySet.val point) parent := by
  intro argument belongs
  change (unfold.app point (assemble.app point (emptyPower point))).val.holds argument at belongs
  rw [unfold_assemble] at belongs
  exact belongs.elim

theorem subset_empty_iff (point : D) (value : sets.obj point) :
    Subset point value (emptySet.val point) ↔ value = emptySet.val point :=
  ⟨fun included => subset_antisymm point included (empty_subset point value),
    fun same => same.symm ▸ subset_refl point (emptySet.val point)⟩

theorem subset_transport {point target : D} (arrow : point ⟶ target)
    {first second : sets.obj point} (included : Subset point first second) :
    Subset target (sets.map arrow first) (sets.map arrow second) := by
  intro argument belongs
  have firstEq := congrArg (fun power : Power sets target => power.val.holds argument)
    (unfold.naturality arrow first)
  have secondEq := congrArg (fun power : Power sets target => power.val.holds argument)
    (unfold.naturality arrow second)
  exact secondEq ▸ included ((futurePrecompose sets arrow).obj argument) (firstEq.symm ▸ belongs)

variable {point : D} {bound : sets.obj point}

/-- Closure includes identity moves between every pair of equally read receipts. -/
structure BoundedCode {predicate : Predicate (sets (D := D)) point} (enumeration : Enumeration predicate) where
  holds : (Σ future : Future.Objects point, enumeration.Carrier future) → Prop
  closed : ∀ {first second : Future.Objects point} (move : first ⟶ second)
    (old : enumeration.Carrier first) (next : enumeration.Carrier second),
    sets.map move.1 (enumeration.value first old) = enumeration.value second next →
      holds ⟨first, old⟩ → holds ⟨second, next⟩

namespace BoundedCode

variable {original : Predicate (sets (D := D)) point} {enumeration : Enumeration original}

theorem ext (first second : BoundedCode enumeration)
    (same : ∀ receipt, first.holds receipt ↔ second.holds receipt) : first = second := by
  cases first with
  | mk first firstLaw =>
    cases second with
    | mk second secondLaw =>
      have predicates : first = second := funext fun receipt => propext (same receipt)
      cases predicates
      rfl

theorem saturated (code : BoundedCode enumeration) (future : Future.Objects point)
    (first second : enumeration.Carrier future)
    (same : enumeration.value future first = enumeration.value future second) :
    code.holds ⟨future, first⟩ ↔ code.holds ⟨future, second⟩ := by
  constructor
  · exact code.closed (𝟙 future) first second
      ((congrArg (fun map => map (enumeration.value future first)) (sets.map_id future.1)).trans same)
  · exact code.closed (𝟙 future) second first
      ((congrArg (fun map => map (enumeration.value future second)) (sets.map_id future.1)).trans same.symm)

def predicate (code : BoundedCode enumeration) : Predicate sets point where
  holds argument := ∃ receipt : enumeration.Carrier argument.1,
    enumeration.value argument.1 receipt = argument.2 ∧ code.holds ⟨argument.1, receipt⟩
  closed {first second} move available := by
    obtain ⟨old, same, truth⟩ := available
    have oldMember := (enumeration.covered first.1 first.2).mpr ⟨old, same⟩
    have nextMember := original.closed move oldMember
    obtain ⟨next, nextEq⟩ := (enumeration.covered second.1 second.2).mp nextMember
    refine ⟨next, nextEq, code.closed move.1 old next ?_ truth⟩
    exact (congrArg (sets.map move.1.1) same).trans (move.2.trans nextEq.symm)

def filteredEnumeration (code : BoundedCode enumeration) : Enumeration code.predicate where
  Carrier future := {receipt : enumeration.Carrier future // code.holds ⟨future, receipt⟩}
  value future receipt := enumeration.value future receipt.val
  covered _ _ := ⟨fun ⟨receipt, same, truth⟩ => ⟨⟨receipt, truth⟩, same⟩,
    fun ⟨receipt, same⟩ => ⟨receipt.val, same, receipt.property⟩⟩

def power (code : BoundedCode enumeration) : Power sets point :=
  ⟨code.predicate, ⟨code.filteredEnumeration⟩⟩

noncomputable def value (code : BoundedCode enumeration) : sets.obj point :=
  assemble.app point code.power

theorem value_reading (code : BoundedCode enumeration) (future : Future.Objects point)
    (child : sets.obj future.1) :
    (unfold.app point code.value).val.holds ⟨future, child⟩ ↔
      ∃ receipt : enumeration.Carrier future,
        enumeration.value future receipt = child ∧ code.holds ⟨future, receipt⟩ := by
  rw [value, unfold_assemble]
  exact Iff.rfl

theorem value_bounded (code : BoundedCode enumeration) :
    ∀ argument, (unfold.app point code.value).val.holds argument → original.holds argument := by
  rintro ⟨future, child⟩ available
  obtain ⟨receipt, same, _⟩ := (code.value_reading future child).mp available
  exact (enumeration.covered future child).mpr ⟨receipt, same⟩

def classify (enumeration : Enumeration original) (value : sets.obj point) :
    BoundedCode enumeration where
  holds receipt := (unfold.app point value).val.holds ⟨receipt.1, enumeration.value receipt.1 receipt.2⟩
  closed {first second} move old next same available :=
    (unfold.app point value).val.closed
      (first := ⟨first, enumeration.value first old⟩)
      (second := ⟨second, enumeration.value second next⟩) ⟨move, same⟩ available

theorem classify_value (code : BoundedCode enumeration) : classify enumeration code.value = code := by
  apply ext
  rintro ⟨future, receipt⟩
  refine (code.value_reading future (enumeration.value future receipt)).trans ?_
  constructor
  · rintro ⟨other, same, truth⟩
    exact (code.saturated future other receipt same).mp truth
  · intro truth
    exact ⟨receipt, rfl, truth⟩

theorem value_classify (enumeration : Enumeration original)
    (value : sets.obj point) (included : ∀ argument,
      (unfold.app point value).val.holds argument → original.holds argument) :
    (classify enumeration value).value = value := by
  have powers : (classify enumeration value).power = unfold.app point value := by
    apply Subtype.ext
    apply Predicate.ext
    rintro ⟨future, child⟩
    constructor
    · rintro ⟨receipt, same, truth⟩
      change (unfold.app point value).val.holds ⟨future, enumeration.value future receipt⟩ at truth
      exact (congrArg (fun child => (unfold.app point value).val.holds ⟨future, child⟩) same) ▸ truth
    · intro belongs
      obtain ⟨receipt, same⟩ := (enumeration.covered future child).mp (included ⟨future, child⟩ belongs)
      refine ⟨receipt, same, ?_⟩
      change (unfold.app point value).val.holds ⟨future, enumeration.value future receipt⟩
      exact (congrArg (fun child => (unfold.app point value).val.holds ⟨future, child⟩) same).symm ▸ belongs
  exact (congrArg (assemble.app point) powers).trans (assemble_unfold point value)

theorem value_injective : Function.Injective (value : BoundedCode enumeration → sets.obj point) := by
  intro first second same
  exact (classify_value first).symm.trans
    ((congrArg (classify enumeration) same).trans (classify_value second))

noncomputable def subsetEquiv (enumeration : Enumeration (unfold.app point bound).val) :
    BoundedCode enumeration ≃ {value : sets.obj point // Subset point value bound} where
  toFun code := ⟨code.value, code.value_bounded⟩
  invFun value := classify enumeration value.val
  left_inv := classify_value
  right_inv value := Subtype.ext (value_classify enumeration value.val value.property)

def reindex {target : D} (arrow : point ⟶ target) (code : BoundedCode enumeration) :
    BoundedCode (restrictEnumeration arrow enumeration) where
  holds receipt := code.holds ⟨⟨receipt.1.1, arrow ≫ receipt.1.2⟩, receipt.2⟩
  closed {first second} move old next same truth := code.closed
    (first := ⟨first.1, arrow ≫ first.2⟩)
    (second := ⟨second.1, arrow ≫ second.2⟩)
    ⟨move.1, (Category.assoc arrow first.2 move.1).trans (congrArg (fun tail => arrow ≫ tail) move.2)⟩
      old next same truth

theorem power_reindex {target : D} (arrow : point ⟶ target) (code : BoundedCode enumeration) :
    (code.reindex arrow).power = restrictPower sets arrow code.power := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

theorem value_reindex {target : D} (arrow : point ⟶ target) (code : BoundedCode enumeration) :
    (code.reindex arrow).value = sets.map arrow code.value :=
  (congrArg (assemble.app target) (code.power_reindex arrow)).trans
    (assemble.naturality arrow code.power).symm

end BoundedCode

def powersetPredicate (point : D) (parent : sets.obj point) : Predicate sets point where
  holds argument := Subset argument.1.1 argument.2 (sets.map argument.1.2 parent)
  closed {first second} move included := by
    have transported := subset_transport move.1.1 included
    have parentEq : sets.map move.1.1 (sets.map first.1.2 parent) = sets.map second.1.2 parent :=
      (congrArg (fun map => map parent) (sets.map_comp first.1.2 move.1.1)).symm.trans
        (congrArg (fun arrow => sets.map arrow parent) move.1.2)
    have childEq : sets.map move.1.1 first.2 = second.2 := move.2
    exact (congrArg₂ (Subset second.1.1) childEq parentEq) ▸ transported

/-- The entire small receipt truth type codes every all-future subset. -/
noncomputable def powersetEnumeration (point : D) (parent : sets.obj point) :
    Enumeration (powersetPredicate point parent) where
  Carrier future := BoundedCode (HostChoiceContextualCoalgebraFinality.enumerations unfold
    future.1 (sets.map future.2 parent))
  value _ code := code.value
  covered future child := by
    constructor
    · intro included
      exact ⟨BoundedCode.classify _ child, BoundedCode.value_classify _ child included⟩
    · rintro ⟨code, same⟩
      exact same ▸ code.value_bounded

noncomputable def powersetPower (point : D) (parent : sets.obj point) : Power sets point :=
  ⟨powersetPredicate point parent, ⟨powersetEnumeration point parent⟩⟩

theorem powersetPower_restrict {point target : D} (arrow : point ⟶ target) (parent : sets.obj point) :
    restrictPower sets arrow (powersetPower point parent) = powersetPower target (sets.map arrow parent) := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  change Subset argument.1.1 argument.2 (sets.map (arrow ≫ argument.1.2) parent) ↔ _
  rw [sets.map_comp]
  exact Iff.rfl

noncomputable def powersetPowerHom : NaturalHom (sets (D := D)) (family sets) where
  app := powersetPower
  naturality := powersetPower_restrict

noncomputable def powersetSet : NaturalHom (sets (D := D)) sets := powersetPowerHom.comp assemble

theorem future_powerset {point target : D} (arrow : point ⟶ target)
    (parent : sets.obj point) (child : sets.obj target) :
    FutureMember arrow child (powersetSet.app point parent) ↔
      Subset target child (sets.map arrow parent) := by
  change (unfold.app point (assemble.app point (powersetPower point parent))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

theorem member_powerset (point : D) (parent child : sets.obj point) :
    Member point child (powersetSet.app point parent) ↔ Subset point child parent := by
  have result := future_powerset (𝟙 point) parent child
  rw [sets.map_id] at result
  exact result

theorem powerset_members_original_small (point : D) (parent : sets.obj point) :
    Nonempty (Enumeration (unfold.app point (powersetSet.app point parent)).val) := by
  have same : unfold.app point (powersetSet.app point parent) = powersetPower point parent :=
    unfold_assemble point _
  exact same.symm ▸ (powersetPower point parent).property

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetPowers
