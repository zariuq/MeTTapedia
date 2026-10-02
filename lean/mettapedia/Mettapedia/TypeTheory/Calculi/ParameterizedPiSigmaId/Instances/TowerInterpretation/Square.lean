import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Controls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Membership
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSet

/-!
# The reading square: model SN's truth reading and the tower's truth values

Model SN extends the consistency model, and reads proposition codes through it
by Lean propositions: implication is `→`, the quantifier `all@A` is `∀`, the
equation `eq@A` is `=` (`Consistency.Setting.truthReading`, the reading
`M.toModel.reading` of a model SN `M`). The tower reads propositions by truth
values `Ω = 𝒫 {∅}`, a quantifier by the trace product over the carrier's set,
and an equation by the truth value of equality of sets.

**The square** (`square_imp`, `square_all`, `square_eq`). On the carriers
without data, built from `prop`, rigid base types and functions
(`PureCarrier`), the carriers of the two readings correspond (`valEquiv`: a
proposition is a truth value, a rigid point is the point `∅`, a function is a
trace function), and `truthCode : Prop → ZFSet` carries the meaning of
implication, of the quantifier at every such carrier — `prop` itself included,
which is the impredicative quantifier `all@prop` — and of the equation to the
tower's. `truthCode` is a bijection onto `Ω` (`propEquiv`), so the two
readings are isomorphic on these carriers (`square_truth_iff` reads truth
back).

**Through the hyperset tower** (`ofZFSet_truthCode`, `square_all_tower`). The
well-founded hypersets have their own truth values, the separations
`HSet.sep (fun _ => P) {∅}` of the hyperset `{∅}`; the embedding of `ZFSet`
into the hyperset universe, which is the inverse of the equivalence
`wellFoundedPartEquivZFSet`, carries each `ZFSet` truth value to the hyperset
truth value of the same proposition. The three readings of a quantified code,
by model SN, by `ZFSet`, and by hypersets, agree.

**Negative control** (`square_fails_two_point_rigid`). The consistency model
reads a rigid base type as one point, so it makes any two points of it
equal. A tower reading that gives a rigid type two points reads the same
statement as false: the square commutes only when rigid types are read as
singletons, as `carrierSet` does.

Scope: this square is between readings of carriers and code formers. Its lift
to code *terms* needs the proposition layer inside the annotated judgment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace Square

open Presentation Presentation.TypedEquality.Impredicative
open Consistency (Carrier Kind Setting)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetTraceProducts (tracePiSet tracePiEquiv tracePiSet_congr)
open ZFSetTraceProofDecoding (truthCode mem_truthCode truthCode_subset)
open Controls (tracePiSet_truthCode)
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

variable {Head : Type}

/-! ## Carriers without data -/

/-- Carriers built from `prop`, rigid base types and functions. -/
inductive PureCarrier where
  | prop
  | rigid (T : DeclName)
  | arr (A B : PureCarrier)

/-- The consistency model's carrier. -/
def PureCarrier.toCarrier : PureCarrier → Carrier .gen
  | .prop => .prop
  | .rigid T => .rigid T
  | .arr A B => .arr A.toCarrier B.toCarrier

/-- The truth values `Ω = 𝒫 {∅}`. -/
noncomputable def omega : ZFSet.{u} := ZFSet.powerset {∅}

/-- The tower's set of a carrier: truth values at `prop`, the point `{∅}` at a
rigid type, and trace functions at a function type. -/
noncomputable def carrierSet : PureCarrier → ZFSet.{u}
  | .prop => omega
  | .rigid _ => {∅}
  | .arr A B => tracePiSet (carrierSet A) (fun _ => carrierSet B)

theorem truthCode_mem_omega (P : Prop) : truthCode P ∈ omega.{u} :=
  ZFSet.mem_powerset.mpr (truthCode_subset P)

theorem truthCode_empty_mem {x : ZFSet.{u}} (hx : x ⊆ {∅}) :
    truthCode ((∅ : ZFSet.{u}) ∈ x) = x := by
  apply ZFSet.ext
  intro z
  rw [mem_truthCode]
  constructor
  · rintro ⟨rfl, h⟩
    exact h
  · intro hz
    have e : z = ∅ := ZFSet.mem_singleton.mp (hx hz)
    exact ⟨e, e ▸ hz⟩

/-- **Propositions are truth values.** -/
noncomputable def propEquiv : Prop ≃ Elements omega.{u} where
  toFun P := ⟨truthCode P, truthCode_mem_omega P⟩
  invFun x := (∅ : ZFSet.{u}) ∈ x.1
  left_inv _ := propext ⟨fun h => ((mem_truthCode _ _).mp h).2,
    fun h => (mem_truthCode _ _).mpr ⟨rfl, h⟩⟩
  right_inv x := Subtype.ext (truthCode_empty_mem (ZFSet.mem_powerset.mp x.2))

/-- A rigid point is the point `∅`. -/
def pointEquiv : Unit ≃ Elements ({∅} : ZFSet.{u}) where
  toFun _ := ⟨∅, ZFSet.mem_singleton.mpr rfl⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv x := Subtype.ext (ZFSet.mem_singleton.mp x.2).symm

/-- **The carriers correspond**: a meaning of a carrier in the consistency
model's truth reading is an element of the carrier's set in the tower. -/
noncomputable def valEquiv (S : Setting Head) :
    (c : PureCarrier) → Carrier.Val S.numerals Prop c.toCarrier ≃ Elements (carrierSet.{u} c)
  | .prop => propEquiv
  | .rigid _ => pointEquiv
  | .arr A B =>
      (Equiv.arrowCongr (valEquiv S A) (valEquiv S B)).trans
        (tracePiEquiv (carrierSet A) (fun _ => carrierSet B)).symm

/-! ## The square -/

variable (S : Setting Head)

/-- Implication: the tower reads `P → Q` as the trace functions from the
proofs of `P` into the proofs of `Q`. -/
theorem square_imp (P Q : Prop) :
    truthCode.{u} (S.truthReading.impMeaning P Q) =
      tracePiSet (truthCode P) (fun _ => truthCode Q) := by
  rw [tracePiSet_truthCode]
  congr 1
  apply propext
  change (P → Q) ↔ ∀ x ∈ truthCode P, Q
  constructor
  · intro f x hx
    exact f ((mem_truthCode _ _).mp hx).2
  · intro f p
    exact f ∅ ((mem_truthCode _ _).mpr ⟨rfl, p⟩)

/-- The family on the tower's carrier set induced by a predicate on the
consistency model's carrier. -/
noncomputable def lift (c : PureCarrier) (φ : Carrier.Val S.numerals Prop c.toCarrier → Prop) :
    ZFSet.{u} → ZFSet.{u} :=
  fun x => truthCode (∃ hx : x ∈ carrierSet.{u} c, φ ((valEquiv S c).symm ⟨x, hx⟩))

/-- **The quantifier**, at every carrier without data, `prop` included: the
tower reads `∀ v, φ v` as the trace product of the induced family. -/
theorem square_all (c : PureCarrier) (φ : Carrier.Val S.numerals Prop c.toCarrier → Prop) :
    truthCode.{u} (S.truthReading.allMeaning c.toCarrier φ) =
      tracePiSet (carrierSet c) (lift S c φ) := by
  change _ = tracePiSet (carrierSet c)
    (fun x => truthCode (∃ hx : x ∈ carrierSet c, φ ((valEquiv S c).symm ⟨x, hx⟩)))
  rw [tracePiSet_truthCode]
  congr 1
  apply propext
  change (∀ v, φ v) ↔ ∀ x ∈ carrierSet c, ∃ hx : x ∈ carrierSet c, φ ((valEquiv S c).symm ⟨x, hx⟩)
  constructor
  · intro all x hx
    exact ⟨hx, all _⟩
  · intro all v
    obtain ⟨_, h⟩ := all _ ((valEquiv S c) v).2
    simpa using h

/-- **The equation**: the tower reads `v = w` as the truth value of the
equality of the corresponding sets, the identity reading of the model. -/
theorem square_eq (c : PureCarrier) (v w : Carrier.Val S.numerals Prop c.toCarrier) :
    truthCode.{u} (S.truthReading.eqMeaning c.toCarrier v w) =
      truthCode (((valEquiv S c) v).1 = ((valEquiv S c) w).1) := by
  congr 1
  apply propext
  change v = w ↔ _
  constructor
  · rintro rfl
    rfl
  · intro e
    exact (valEquiv S c).injective (Subtype.ext e)

/-- Reading truth back: a proposition holds exactly when its truth value
contains the empty proof. -/
theorem square_truth_iff (P : Prop) : (∅ : ZFSet.{u}) ∈ truthCode P ↔ P :=
  ⟨fun h => ((mem_truthCode _ _).mp h).2, fun h => (mem_truthCode _ _).mpr ⟨rfl, h⟩⟩

/-- The impredicative quantifier over propositions, `all@prop`, read two ways:
by model SN's truth reading and by the tower's trace product over `Ω`. -/
theorem square_all_prop (φ : Prop → Prop) :
    truthCode.{u} (S.truthReading.allMeaning Carrier.prop φ) =
      tracePiSet omega (lift S .prop φ) :=
  square_all S .prop φ

/-- **Model SN's reading**: for a model SN `M`, the square is about the truth
reading `M.toModel.reading` that model SN carries. -/
theorem square_modelSN {L : Type} [UniverseLevel.LevelOrder L] (M : ModelSN.SNModel Head L)
    (c : PureCarrier) (φ : Carrier.Val M.toSetting.numerals Prop c.toCarrier → Prop) :
    truthCode.{u} (M.toModel.reading.allMeaning c.toCarrier φ) =
      tracePiSet (carrierSet c) (lift M.toSetting c φ) :=
  square_all M.toSetting c φ

/-! ## Through the hyperset tower -/

/-- The hyperset truth value of a proposition: separation of the hyperset
`{∅}`. -/
def hTruth (P : Prop) : HSet.{u} := HSet.sep (fun _ => P) {∅}

/-- The embedding into hypersets carries truth values to hyperset truth
values. -/
theorem ofZFSet_truthCode (P : Prop) : HSet.ofZFSet (truthCode.{u} P) = hTruth P := by
  rw [truthCode, HSet.ofZFSet_sep, HSet.ofZFSet_singleton, HSet.ofZFSet_empty, hTruth]

/-- A hyperset truth value is well founded, so it lies in the well-founded
part. -/
theorem hTruth_wf (P : Prop) : (hTruth.{u} P).WF := by
  rw [← ofZFSet_truthCode]
  exact HSet.wf_ofZFSet _

/-- Reading truth back in the hyperset tower. -/
theorem empty_mem_hTruth (P : Prop) : (∅ : HSet.{u}) ∈ hTruth P ↔ P := by
  rw [hTruth, HSet.mem_sep, HSet.mem_singleton]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- **The three readings agree**: model SN's truth reading of a quantified
code, carried through `ZFSet` into the hyperset tower, is the hyperset truth
value of the same proposition, and it is the equivalence image of the
tower's trace product. -/
theorem square_all_tower (c : PureCarrier) (φ : Carrier.Val S.numerals Prop c.toCarrier → Prop) :
    HSet.ofZFSet (tracePiSet.{u} (carrierSet c) (lift S c φ)) =
      hTruth (S.truthReading.allMeaning c.toCarrier φ) :=
  (congrArg HSet.ofZFSet (square_all S c φ).symm).trans (ofZFSet_truthCode _)

/-- The same square in the well-founded part, through its equivalence with
`ZFSet`. -/
theorem square_all_wellFoundedPart (c : PureCarrier)
    (φ : Carrier.Val S.numerals Prop c.toCarrier → Prop) :
    (HSet.wellFoundedPartEquivZFSet.symm (tracePiSet.{u} (carrierSet c) (lift S c φ))).1 =
      hTruth (S.truthReading.allMeaning c.toCarrier φ) :=
  square_all_tower S c φ

/-! ## Negative control: two points at a rigid type -/

/-- A two-point set. -/
noncomputable def twoPoints : ZFSet.{u} := {∅, {∅}}

theorem empty_ne_singleton : (∅ : ZFSet.{u}) ≠ {∅} := by
  intro e
  have : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← e] at this
  exact ZFSet.notMem_empty _ this

/-- **The square fails if a rigid type has two points.** The consistency
model makes any two points of a rigid type equal; a tower reading of the rigid
type by two points makes the same statement false. -/
theorem square_fails_two_point_rigid (T : DeclName) :
    truthCode.{u} (S.truthReading.allMeaning (Carrier.rigid T) fun v =>
        S.truthReading.allMeaning (Carrier.rigid T) fun w =>
          S.truthReading.eqMeaning (Carrier.rigid T) v w) ≠
      tracePiSet twoPoints (fun x => tracePiSet twoPoints (fun y => truthCode (x = y))) := by
  intro e
  have lhs : (∅ : ZFSet.{u}) ∈ truthCode (S.truthReading.allMeaning (Carrier.rigid T) fun v =>
      S.truthReading.allMeaning (Carrier.rigid T) fun w =>
        S.truthReading.eqMeaning (Carrier.rigid T) v w) :=
    (square_truth_iff _).mpr (fun _ _ => rfl)
  rw [e] at lhs
  have inner : ∀ x, tracePiSet twoPoints (fun y => truthCode (x = y)) =
      truthCode (∀ y ∈ twoPoints.{u}, x = y) := fun x => tracePiSet_truthCode _ _
  simp only [inner, tracePiSet_truthCode] at lhs
  have all := (square_truth_iff _).mp lhs
  exact empty_ne_singleton (all ∅ (ZFSet.mem_insert _ _) {∅}
    (ZFSet.mem_insert_of_mem _ (ZFSet.mem_singleton.mpr rfl)))

/-- With the rigid type read as the singleton `{∅}`, as `carrierSet` does, the
same statement is true in the tower, matching the consistency model. -/
theorem square_one_point_rigid (T : DeclName) :
    tracePiSet (carrierSet.{u} (.rigid T))
        (fun x => tracePiSet (carrierSet (.rigid T)) (fun y => truthCode (x = y))) =
      truthCode (S.truthReading.allMeaning (Carrier.rigid T) fun v =>
        S.truthReading.allMeaning (Carrier.rigid T) fun w =>
          S.truthReading.eqMeaning (Carrier.rigid T) v w) := by
  have inner : ∀ x, tracePiSet (carrierSet.{u} (.rigid T)) (fun y => truthCode (x = y)) =
      truthCode (∀ y ∈ carrierSet.{u} (.rigid T), x = y) := fun x => tracePiSet_truthCode _ _
  simp only [inner, tracePiSet_truthCode]
  congr 1
  apply propext
  change (∀ x ∈ ({∅} : ZFSet.{u}), ∀ y ∈ ({∅} : ZFSet.{u}), x = y) ↔ ∀ _ _ : Unit, _ = _
  constructor
  · intro _ _ _
    rfl
  · intro _ x hx y hy
    rw [ZFSet.mem_singleton.mp hx, ZFSet.mem_singleton.mp hy]

end Square
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
