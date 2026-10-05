import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor
import Mettapedia.TypeTheory.HostChoiceContextualSmallMaps

/-!
# Small fibres of maps on covered future powers

A uniform original-bound enumeration of each fibre of an authored natural
map constructs a cover of the inverse image of every covered future
predicate. Stable predicates on those receipts form an original-bound
type. Identity moves enforce saturation of duplicate receipts, and the
receipt code decodes to an actual covered predicate with proved inverses.
Filtering codes by the complete image equation enumerates each fibre of
the map on covered powers.

The final factory selects the uniform fibre data with external host Choice
from propositional smallness. Arguments may live in independently wider
universes. Receipt carriers and the code type stay at the context bound;
full Prop-valued predicates on those carriers are used explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceCoveredFuturePowerSmallMaps

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open PowerClassPresheafBaseChange
open Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualSmallMapConstructions

universe u v w
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w}
variable {point : D}

/-- Closure compares the actual transported values, including duplicate
receipts at identity arrows. The entire code type inhabits `Type u`. -/
structure ReceiptCode {predicate : Predicate A point}
    (enumeration : CoveredFuturePowerFamilies.Enumeration predicate) where
  holds : (Σ future : Future.Objects point, enumeration.Carrier future) → Prop
  closed : ∀ {first second : Future.Objects point} (move : first ⟶ second)
    (old : enumeration.Carrier first) (next : enumeration.Carrier second),
    A.map move.1 (enumeration.value first old) = enumeration.value second next →
      holds ⟨first, old⟩ → holds ⟨second, next⟩

namespace ReceiptCode

variable {original : Predicate A point}
variable {enumeration : CoveredFuturePowerFamilies.Enumeration original}

theorem ext (first second : ReceiptCode enumeration)
    (same : ∀ receipt, first.holds receipt ↔ second.holds receipt) : first = second := by
  cases first with
  | mk first firstLaw =>
    cases second with
    | mk second secondLaw =>
      have predicates : first = second := funext fun receipt => propext (same receipt)
      cases predicates
      rfl

theorem saturated (code : ReceiptCode enumeration) (future : Future.Objects point)
    (first second : enumeration.Carrier future)
    (same : enumeration.value future first = enumeration.value future second) :
    code.holds ⟨future, first⟩ ↔ code.holds ⟨future, second⟩ := by
  constructor
  · exact code.closed (𝟙 future) first second
      ((congrArg (fun map => map (enumeration.value future first)) (A.map_id future.1)).trans same)
  · exact code.closed (𝟙 future) second first
      ((congrArg (fun map => map (enumeration.value future second)) (A.map_id future.1)).trans same.symm)

def predicate (code : ReceiptCode enumeration) : Predicate A point where
  holds argument := ∃ receipt : enumeration.Carrier argument.1,
    enumeration.value argument.1 receipt = argument.2 ∧ code.holds ⟨argument.1, receipt⟩
  closed {first second} move available := by
    obtain ⟨old, same, truth⟩ := available
    have originalTruth := (enumeration.covered first.1 first.2).mpr ⟨old, same⟩
    obtain ⟨next, nextEq⟩ := (enumeration.covered second.1 second.2).mp
      (original.closed move originalTruth)
    refine ⟨next, nextEq, code.closed move.1 old next ?_ truth⟩
    exact (congrArg (A.map move.1.1) same).trans (move.2.trans nextEq.symm)

def filteredEnumeration (code : ReceiptCode enumeration) :
    CoveredFuturePowerFamilies.Enumeration code.predicate where
  Carrier future := {receipt : enumeration.Carrier future // code.holds ⟨future, receipt⟩}
  value future receipt := enumeration.value future receipt.val
  covered _ _ := ⟨fun ⟨receipt, same, truth⟩ => ⟨⟨receipt, truth⟩, same⟩,
    fun ⟨receipt, same⟩ => ⟨receipt.val, same, receipt.property⟩⟩

def power (code : ReceiptCode enumeration) : Power A point :=
  ⟨code.predicate, ⟨code.filteredEnumeration⟩⟩

theorem bounded (code : ReceiptCode enumeration) : Included code.predicate original := by
  rintro ⟨future, child⟩ ⟨receipt, same, _⟩
  exact (enumeration.covered future child).mpr ⟨receipt, same⟩

def classify (enumeration : CoveredFuturePowerFamilies.Enumeration original)
    (value : Predicate A point) : ReceiptCode enumeration where
  holds receipt := value.holds ⟨receipt.1, enumeration.value receipt.1 receipt.2⟩
  closed {first second} move old next same available :=
    value.closed (first := ⟨first, enumeration.value first old⟩)
      (second := ⟨second, enumeration.value second next⟩) ⟨move, same⟩ available

theorem classify_power (code : ReceiptCode enumeration) :
    classify enumeration code.power.val = code := by
  apply ext
  rintro ⟨future, receipt⟩
  constructor
  · rintro ⟨other, same, truth⟩
    exact (code.saturated future other receipt same).mp truth
  · intro truth
    exact ⟨receipt, rfl, truth⟩

theorem power_classify (enumeration : CoveredFuturePowerFamilies.Enumeration original)
    (value : Power A point) (included : Included value.val original) :
    (classify enumeration value.val).power = value := by
  apply Subtype.ext
  apply Predicate.ext
  rintro ⟨future, child⟩
  constructor
  · rintro ⟨receipt, same, truth⟩
    exact (congrArg (fun child => value.val.holds ⟨future, child⟩) same) ▸ truth
  · intro belongs
    obtain ⟨receipt, same⟩ := (enumeration.covered future child).mp (included ⟨future, child⟩ belongs)
    refine ⟨receipt, same, ?_⟩
    change value.val.holds ⟨future, enumeration.value future receipt⟩
    exact (congrArg (fun child => value.val.holds ⟨future, child⟩) same).symm ▸ belongs

def subpowerEquiv (enumeration : CoveredFuturePowerFamilies.Enumeration original) :
    ReceiptCode enumeration ≃ {value : Power A point // Included value.val original} where
  toFun code := ⟨code.power, code.bounded⟩
  invFun value := classify enumeration value.val.val
  left_inv := classify_power
  right_inv value := Subtype.ext (power_classify enumeration value.val value.property)

def reindex {target : D} (arrow : point ⟶ target) (code : ReceiptCode enumeration) :
    ReceiptCode (restrictEnumeration arrow enumeration) where
  holds receipt := code.holds ⟨⟨receipt.1.1, arrow ≫ receipt.1.2⟩, receipt.2⟩
  closed {first second} move old next same truth := code.closed
    (first := ⟨first.1, arrow ≫ first.2⟩) (second := ⟨second.1, arrow ≫ second.2⟩)
    ⟨move.1, (Category.assoc arrow first.2 move.1).trans (congrArg (fun tail => arrow ≫ tail) move.2)⟩
      old next same truth

theorem power_reindex {target : D} (arrow : point ⟶ target) (code : ReceiptCode enumeration) :
    (code.reindex arrow).power = restrictPower A arrow code.power := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

end ReceiptCode

variable (operation : NaturalHom A B)

/-- A target receipt and an original-small fibre receipt enumerate the
actual inverse image. Neither carrier contains a wide source value. -/
def inverseImageEnumeration (fibres : UniformEnumerations operation)
    (target : Predicate B point) (enumeration : CoveredFuturePowerFamilies.Enumeration target) :
    CoveredFuturePowerFamilies.Enumeration (inverseImage operation point target) where
  Carrier future := Σ code : enumeration.Carrier future,
    (fibres future.1 (enumeration.value future code)).Carrier
  value future code := ((fibres future.1 (enumeration.value future code.1)).value code.2).val
  covered future argument := by
    constructor
    · intro available
      obtain ⟨targetCode, targetEq⟩ := (enumeration.covered future (operation.app future.1 argument)).mp available
      let receipt : Fibre operation future.1 (enumeration.value future targetCode) := ⟨argument, targetEq.symm⟩
      obtain ⟨sourceCode, sourceEq⟩ := (fibres future.1 (enumeration.value future targetCode)).covered receipt
      exact ⟨⟨targetCode, sourceCode⟩, congrArg Subtype.val sourceEq⟩
    · rintro ⟨code, sourceEq⟩
      have mapped := ((fibres future.1 (enumeration.value future code.1)).value code.2).property
      exact (enumeration.covered future (operation.app future.1 argument)).mpr
        ⟨code.1, mapped.symm.trans (congrArg (operation.app future.1) sourceEq)⟩

def inversePower (fibres : UniformEnumerations operation) (target : Power B point)
    (enumeration : CoveredFuturePowerFamilies.Enumeration target.val) : Power A point :=
  ⟨inverseImage operation point target.val,
    ⟨inverseImageEnumeration operation fibres target.val enumeration⟩⟩

theorem inversePower_restrict (fibres : UniformEnumerations operation)
    {target : D} (arrow : point ⟶ target) (value : Power B point)
    (old : CoveredFuturePowerFamilies.Enumeration value.val)
    (next : CoveredFuturePowerFamilies.Enumeration (restrictPower B arrow value).val) :
    restrictPower A arrow (inversePower operation fibres value old) =
      inversePower operation fibres (restrictPower B arrow value) next := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

theorem source_bounded (value : Power B point) (source : Power A point)
    (same : imagePower operation point source = value) :
    Included source.val (inverseImage operation point value.val) := by
  intro argument available
  have projected : (imagePower operation point source).val.holds
      ((futureArguments operation point).obj argument) := ⟨argument.2, rfl, available⟩
  exact (congrArg (fun power : Power B point =>
    power.val.holds ((futureArguments operation point).obj argument)) same) ▸ projected

/-- The fibre code is a truth predicate on the small future receipt type,
filtered by the exact complete image equation. Its decoder is constructed. -/
def imageFibreEnumeration (fibres : UniformEnumerations operation) (value : Power B point)
    (enumeration : CoveredFuturePowerFamilies.Enumeration value.val) :
    ContextualImageFactorization.Enumeration.{u, max u v}
      (Fibre (imageHom operation) point value) where
  Carrier := {code : ReceiptCode (inverseImageEnumeration operation fibres value.val enumeration) //
    imagePower operation point code.power = value}
  value code := ⟨code.val.power, code.property⟩
  covered source := by
    let code := ReceiptCode.classify (inverseImageEnumeration operation fibres value.val enumeration) source.val.val
    have returns : code.power = source.val :=
      ReceiptCode.power_classify _ source.val (source_bounded operation value source.val source.property)
    refine ⟨⟨code, ?_⟩, Subtype.ext returns⟩
    exact (congrArg (imagePower operation point) returns).trans source.property

theorem imageHom_small_of_enumerations (fibres : UniformEnumerations operation) :
    SmallFibres (imageHom operation) := by
  intro point value
  obtain ⟨enumeration⟩ := value.property
  exact ⟨imageFibreEnumeration operation fibres value enumeration⟩

/-- External host Choice supplies the uniform original-small fibre data.
The power-map fibre construction and its original bound are the preceding
explicit enumeration, not an assumed closure axiom. -/
theorem imageHom_small (small : SmallFibres operation) : SmallFibres (imageHom operation) :=
  imageHom_small_of_enumerations operation
    (HostChoiceContextualSmallMaps.selectedEnumerations operation small)

/-- A small map also constructs an actual covered inverse-image map.
The selected target enumeration changes its receipts, not its full truth. -/
noncomputable def coveredInverse (small : SmallFibres operation) (point : D)
    (value : Power B point) : Power A point :=
  inversePower operation (HostChoiceContextualSmallMaps.selectedEnumerations operation small)
    value (Classical.choice value.property)

theorem coveredInverse_restrict (small : SmallFibres operation)
    {first second : D} (arrow : first ⟶ second) (value : Power B first) :
    restrictPower A arrow (coveredInverse operation small first value) =
      coveredInverse operation small second (restrictPower B arrow value) := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

noncomputable def inverseImageHom (small : SmallFibres operation) :
    NaturalHom (family B) (family A) where
  app := coveredInverse operation small
  naturality := coveredInverse_restrict operation small

theorem covered_adjunction (small : SmallFibres operation) (point : D)
    (source : Power A point) (target : Power B point) :
    Included (imagePower operation point source).val target.val ↔
      Included source.val (coveredInverse operation small point target).val :=
  image_inverseImage_adjunction operation point source.val target.val

/-- Actual contextual restriction sends a fibre into the fibre at the
restricted target. It retains every future index by the whole image square. -/
def imageFibreRestrict {first second : D} (arrow : first ⟶ second) (value : Power B first)
    (source : Fibre (imageHom operation) first value) :
    Fibre (imageHom operation) second (restrictPower B arrow value) :=
  ⟨restrictPower A arrow source.val,
    (imagePower_restrict operation arrow source.val).symm.trans
      (congrArg (restrictPower B arrow) source.property)⟩

theorem imageFibreRestrict_identity (value : Power B point)
    (source : Fibre (imageHom operation) point value) :
    (imageFibreRestrict operation (𝟙 point) value source).val = source.val :=
  restrictPower_identity A point source.val

theorem imageFibreRestrict_comp {first middle last : D}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (value : Power B first)
    (source : Fibre (imageHom operation) first value) :
    (imageFibreRestrict operation (earlier ≫ later) value source).val =
      (imageFibreRestrict operation later (restrictPower B earlier value)
        (imageFibreRestrict operation earlier value source)).val :=
  restrictPower_comp A earlier later source.val

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceCoveredFuturePowerSmallMaps
