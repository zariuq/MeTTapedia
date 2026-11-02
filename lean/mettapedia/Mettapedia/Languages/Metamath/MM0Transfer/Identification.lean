import Mettapedia.Languages.Metamath.MM0Transfer.DistinctnessProjection

/-!
# Valid source-variable identification and derived theorem copies

A partition identifies source variables by a type-preserving map. Its exact
validity condition is that no retained distinctness pair is collapsed. The
target context is constructed by transporting hypotheses and the retained
relation; it is not an oracle for the conclusion. Proof transport uses the
original source substitution theorem.

This provides all valid identification instances, not merely the finite
partitions observed by an implementation's bundle scan. Correspondence to
the converter's canonical bundle labels and frame reordering is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM0Transfer.Identification

open _root_.Metamath
open Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport
  (renameExpr renameFormula TypePreserving)
open Mettapedia.Languages.Metamath.MM0Transfer.SourceSupport
open Mettapedia.Languages.Metamath.MM0Transfer.DistinctnessProjection

/-- A valid identification never merges the endpoints of a retained source pair. -/
def Valid (source : DJ) (identify : VR → VR) : Prop :=
  ∀ left right, source left right → identify left ≠ identify right

/-- The transported relation contains exactly images of actual source pairs. -/
def imageDJ (source : DJ) (identify : VR → VR) (valid : Valid source identify) : DJ where
  disj left right := ∃ sourceLeft sourceRight, source sourceLeft sourceRight ∧
    identify sourceLeft = left ∧ identify sourceRight = right
  irr := by
    rintro _ ⟨left, right, pair, leftImage, rightImage⟩
    exact valid left right pair (leftImage.trans rightImage.symm)
  symm := by
    rintro _ _ ⟨left, right, pair, leftImage, rightImage⟩
    exact ⟨right, left, source.symm pair, rightImage, leftImage⟩

theorem source_pair_maps {source : DJ} {identify : VR → VR}
    (valid : Valid source identify) {left right : VR} (pair : source left right) :
    imageDJ source identify valid (identify left) (identify right) :=
  ⟨left, right, pair, rfl, rfl⟩

theorem imageDJ_minimal {source target : DJ} {identify : VR → VR}
    (valid : Valid source identify)
    (preserved : ∀ left right, source left right → target (identify left) (identify right)) :
    imageDJ source identify valid ≤ target := by
  rintro _ _ ⟨left, right, pair, rfl, rfl⟩
  exact preserved left right pair

/-- The original source substitution condition holds in the constructed image. -/
theorem singleton_substitution_valid {source : DJ} {identify : VR → VR}
    (valid : Valid source identify) :
    source.subst (fun reference => (identify reference).expr)
      (imageDJ source identify valid) := by
  intro left right pair targetLeft targetRight inLeft inRight
  have leftImage : targetLeft = identify left := by simpa [Expr.mem, VR.expr] using inLeft
  have rightImage : targetRight = identify right := by simpa [Expr.mem, VR.expr] using inRight
  rw [leftImage, rightImage]
  exact source_pair_maps valid pair

/-- A collapsed retained pair admits no target distinctness relation at all. -/
theorem valid_iff_some_target (source : DJ) (identify : VR → VR) :
    Valid source identify ↔
      ∃ target : DJ, source.subst (fun reference => (identify reference).expr) target := by
  constructor
  · intro valid
    exact ⟨imageDJ source identify valid, singleton_substitution_valid valid⟩
  · rintro ⟨target, admitted⟩ left right pair
    exact target.ne (admitted left right pair (identify left) (identify right)
      (by simp [Expr.mem, VR.expr]) (by simp [Expr.mem, VR.expr]))

/-- Hypotheses are renamed in order; only the actual source relation is mapped. -/
def imageContext (source : Context) (identify : VR → VR)
    (valid : Valid source.dj identify) : Context :=
  ⟨source.hyps.map (renameFormula identify), imageDJ source.dj identify valid⟩

theorem renameFormula_eq_substitution (identify : VR → VR) (formula : Formula) :
    renameFormula identify formula =
      formula.subst (fun reference => (identify reference).expr) := by
  cases formula with
  | mk typecode expression =>
      exact congrArg (typecode, ·) (rename_eq_substitution identify expression)

/-- Every type-preserving valid identification transports the original source
proof. It does not install its conclusion as an axiom. -/
theorem derivation_identifies {axioms : Statement → Prop} {context : Context}
    {formula : Formula} (derived : Provable axioms context formula)
    (identify : VR → VR) (typed : TypePreserving identify)
    (valid : Valid context.dj identify) :
    Provable axioms (imageContext context identify valid) (renameFormula identify formula) := by
  rw [renameFormula_eq_substitution]
  apply Provable.trans' (fun reference => (identify reference).expr) derived
  · exact singleton_substitution_valid valid
  · intro hypothesis present
    rw [← renameFormula_eq_substitution]
    exact .hyp _ (List.mem_map.mpr ⟨hypothesis, present, rfl⟩)
  · intro reference
    change Provable axioms (imageContext context identify valid)
      (reference.type, (identify reference).expr)
    rw [← typed reference]
    exact .var (identify reference)

/-- Projecting regular/regular assumptions first licenses all subsequent valid
partitions. Only retained bound/regular or bound/bound pairs must be separate. -/
theorem derived_partition_instance {boundSort : CN → Prop}
    {axioms : Statement → Prop} (profile : AxiomProfile boundSort axioms)
    {context : Context}
    (boundHypotheses : AtomicHypotheses boundSort context)
    {formula : Formula} (derived : Provable axioms context formula)
    (identify : VR → VR) (typed : TypePreserving identify)
    (valid : Valid (projectDJ boundSort context.dj) identify) :
    Provable axioms (imageContext (projectContext boundSort context) identify valid)
      (renameFormula identify formula) :=
  derivation_identifies (derivation_projects profile boundHypotheses derived)
    identify typed valid

/-- Every original admissible source identification is also valid after the
regular/regular projection. -/
theorem valid_projected {boundSort : CN → Prop} {source : DJ} {identify : VR → VR}
    (valid : Valid source identify) : Valid (projectDJ boundSort source) identify :=
  fun left right pair => valid left right pair.1

/-- Finite bundle admission checks the original pair list, not just the number
of equivalence classes. -/
def checkPartition (pairs : List (VR × VR)) (identify : VR → VR) : Bool :=
  pairs.all fun pair => decide (identify pair.1 ≠ identify pair.2)

theorem checkPartition_iff (pairs : List (VR × VR)) (identify : VR → VR) :
    checkPartition pairs identify = true ↔
      ∀ pair ∈ pairs, identify pair.1 ≠ identify pair.2 := by
  simp [checkPartition]

/-- For a source-valid list without self-pairs, the finite check and original
declarative distinctness agree in both directions. -/
theorem checkPartition_iff_valid (pairs : List (VR × VR)) (identify : VR → VR)
    (noSelf : ∀ pair ∈ pairs, pair.1 ≠ pair.2) :
    checkPartition pairs identify = true ↔ Valid (DJ.mk' pairs) identify := by
  rw [checkPartition_iff]
  constructor
  · intro checked left right pair
    rcases pair.2 with present | present
    · exact checked (left, right) present
    · exact (checked (right, left) present).symm
  · intro valid pair present
    exact valid pair.1 pair.2 ⟨noSelf pair present, .inl present⟩

end Mettapedia.Languages.Metamath.MM0Transfer.Identification
