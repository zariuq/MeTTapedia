import Mettapedia.GSLT.LanguageDef.ContiguousSliceCompilation
import Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation
import Mettapedia.Languages.Metamath.InferenceAssertionFusedCompilation

/-!
# Slice and region compilation for Metamath assertion substitution

Metamath's source semantics retains an ordered finite substitution whose
replacement formulas are ordinary proof-relevant data.  This module lowers
those formula occurrences into one immutable token carrier plus compact
subslice handles and proves exact agreement with the existing relational
lookup semantics.

The same theorem is then used at a call-local region boundary.  A generated
realization may reset and reuse physical capacity only after publishing a
complete value observation.  Persistent handles instead retain their
immutable owner.  Thus allocation freedom and lifetime safety are consequences
of separate representation and region laws, not assumptions about an arena.
-/

namespace Mettapedia.Languages.Metamath.InferenceAssertionSliceCompilation

open Mettapedia.GSLT.LanguageDef.ContiguousSliceCompilation
open Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation
open Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceAssertionFusedCompilation

/-! ## A flat immutable substitution carrier -/

/-- The exact formula-token occurrence stored for each substitution binding. -/
def substitutionSequences (substitution : FiniteSubstitution) :
    List (List RuntimeSym) :=
  substitution.map fun binding => formulaTokens binding.replacement

/-- One append-only immutable carrier for every replacement occurrence. -/
def substitutionStorage : FiniteSubstitution → List RuntimeSym
  | [] => []
  | binding :: rest =>
      formulaTokens binding.replacement ++ substitutionStorage rest

theorem substitutionStorage_eq_pack_storage
    (substitution : FiniteSubstitution) :
    substitutionStorage substitution =
      (pack (substitutionSequences substitution)).storage := by
  induction substitution with
  | nil => rfl
  | cons binding rest inductionHypothesis =>
      simp [substitutionStorage, substitutionSequences, pack,
        inductionHypothesis]

/-- First-occurrence lookup lowered to a body subslice.  A match skips the
replacement typecode; a recursive result is shifted by the exact preceding
formula length. -/
def lookupBodySlice? : FiniteSubstitution → String → Option Slice
  | [], _ => none
  | binding :: rest, variableName =>
      if binding.variableName = variableName then
        some { offset := 1, length := binding.replacement.body.length }
      else
        (lookupBodySlice? rest variableName).map
          (Slice.shift (formulaTokens binding.replacement).length)

/-- The compact body handle observes exactly the deterministic first-occurrence
lookup.  This includes empty replacement bodies and absent variables. -/
theorem lookupBodySlice?_read
    (substitution : FiniteSubstitution) (variableName : String) :
    (lookupBodySlice? substitution variableName).map
        (Slice.read (substitutionStorage substitution)) =
      lookupBody? substitution variableName := by
  induction substitution with
  | nil => rfl
  | cons binding rest inductionHypothesis =>
      by_cases same : binding.variableName = variableName
      · simp [lookupBodySlice?, lookupBody?, substitutionStorage, same,
          formulaTokens, Slice.read]
      · simp only [lookupBodySlice?, lookupBody?, substitutionStorage, same,
          ↓reduceIte]
        cases selected : lookupBodySlice? rest variableName with
        | none =>
            have tailNone : lookupBody? rest variableName = none := by
              have reversed : none = lookupBody? rest variableName := by
                simpa [selected] using inductionHypothesis
              exact reversed.symm
            simp [tailNone]
        | some slice =>
            have tailSome :
                some (slice.read (substitutionStorage rest)) =
                  lookupBody? rest variableName := by
              simpa [selected] using inductionHypothesis
            simp [Slice.read_shift_append, tailSome]

/-- The provider passed to the fused matcher reads replacement bodies from
the immutable packed carrier. -/
def sliceLookupBody? (substitution : FiniteSubstitution) (variableName : String) :
    Option (List RuntimeSym) :=
  (lookupBodySlice? substitution variableName).map
    (Slice.read (substitutionStorage substitution))

theorem sliceLookupBody?_eq_lookupBody?
    (substitution : FiniteSubstitution) :
    sliceLookupBody? substitution = lookupBody? substitution := by
  funext variableName
  exact lookupBodySlice?_read substitution variableName

/-- Under the projection's unique-key invariant, slice selection is exactly
the existing relational lookup semantics at the body observation. -/
theorem lookupBodySlice?_eq_some_iff_of_unique
    {substitution : FiniteSubstitution}
    (unique : SubstitutionKeysUnique substitution)
    (variableName : String) (body : List RuntimeSym) :
    (lookupBodySlice? substitution variableName).map
          (Slice.read (substitutionStorage substitution)) = some body ↔
      ∃ replacement : ConstantHeadedFormula,
        LookupSemantics substitution variableName replacement ∧
          replacement.body = body := by
  rw [lookupBodySlice?_read]
  exact lookupBody?_eq_some_iff_of_unique unique variableName body

/-- Formula fusion remains exactly the relational Metamath semantics when its
lookup provider is physically realized by compact subslices. -/
theorem fusedMatch_formula_slices_iff
    {substitution : FiniteSubstitution}
    (unique : SubstitutionKeysUnique substitution)
    (source result : ConstantHeadedFormula) :
    fusedMatch (sliceLookupBody? substitution) (formulaTemplate source)
        (formulaTokens result) = some () ↔
      FormulaSubstitutionSemantics substitution source result := by
  rw [sliceLookupBody?_eq_lookupBody?]
  exact fusedMatch_formula_iff unique source result

/-! ## Whole assertion-template packing -/

/-- Mandatory hypotheses followed by the assertion conclusion, preserving
authored order and occurrence multiplicity. -/
def assertionTemplateFormulas (assertion : AssertionView) :
    List ConstantHeadedFormula :=
  assertion.hypotheses.map HypothesisView.formula ++ [assertion.formula]

def assertionTemplateSequences (assertion : AssertionView) :
    List (List RuntimeSym) :=
  (assertionTemplateFormulas assertion).map formulaTokens

def packedAssertionTemplates (assertion : AssertionView) :
    PackedSequences RuntimeSym :=
  pack (assertionTemplateSequences assertion)

/-- Packing preserves the complete ordered formula-token inventory. -/
theorem unpack_packedAssertionTemplates (assertion : AssertionView) :
    unpack (packedAssertionTemplates assertion) =
      assertionTemplateSequences assertion := by
  exact unpack_pack (assertionTemplateSequences assertion)

/-- One packed formula occurrence reads as the corresponding source token
occurrence without reconstructing neighboring formulas. -/
theorem packedAssertionTemplates_readAt?
    (assertion : AssertionView) (index : Nat) :
    (packedAssertionTemplates assertion).readAt? index =
      (assertionTemplateSequences assertion)[index]? := by
  exact PackedSequences.readAt?_pack
    (assertionTemplateSequences assertion) index

/-- Dropping the constant typecode from a selected full-formula handle yields
the exact source body.  The statement deliberately relates occurrence
indices, so equal formulas at different positions are not collapsed. -/
theorem packedAssertionTemplate_bodySlice
    (assertion : AssertionView) (index : Nat)
    (formula : ConstantHeadedFormula) (slice : Slice)
    (formulaAt : (assertionTemplateFormulas assertion)[index]? = some formula)
    (sliceAt : (packedAssertionTemplates assertion).slices[index]? = some slice) :
    (slice.dropPrefix 1).read (packedAssertionTemplates assertion).storage =
      formula.body := by
  have tokenAt :
      (assertionTemplateSequences assertion)[index]? =
        some (formulaTokens formula) := by
    simp [assertionTemplateSequences, formulaAt]
  have selected := packedAssertionTemplates_readAt? assertion index
  unfold PackedSequences.readAt? at selected
  rw [sliceAt, tokenAt] at selected
  simp only [Option.map_some, Option.some.injEq] at selected
  rw [Slice.read_dropPrefix, selected]
  simp [formulaTokens]

/-- A persistent selected formula retains its immutable owner; the derived
body view therefore remains meaningful beyond the local lookup operation. -/
def publishAssertionBodyAt? (assertion : AssertionView) (index : Nat) :
    Option (PublishedSlice RuntimeSym) :=
  (packedAssertionTemplates assertion).publishAt? index |>.map
    (PublishedSlice.dropPrefix 1)

/-- Owner-retaining publication of a selected body is exact, including for an
empty body.  No scratch-only numeric handle crosses the boundary. -/
theorem publishAssertionBodyAt?_read
    (assertion : AssertionView) (index : Nat)
    (formula : ConstantHeadedFormula) (published : PublishedSlice RuntimeSym)
    (formulaAt : (assertionTemplateFormulas assertion)[index]? = some formula)
    (publishedAt : publishAssertionBodyAt? assertion index = some published) :
    published.read = formula.body := by
  unfold publishAssertionBodyAt? PackedSequences.publishAt? at publishedAt
  cases sliceAt : (packedAssertionTemplates assertion).slices[index]? with
  | none => simp [sliceAt] at publishedAt
  | some slice =>
      simp [sliceAt] at publishedAt
      subst published
      exact packedAssertionTemplate_bodySlice assertion index formula slice
        formulaAt sliceAt

/-! ## Resettable call-local substitution regions -/

/-- One substitution plus the ordered variables observed by a caller. -/
structure SubstitutionQueryBatch where
  substitution : FiniteSubstitution
  queries : List String
  deriving DecidableEq, Repr

def sourceQueryObservation (batch : SubstitutionQueryBatch) :
    List (Option (List RuntimeSym)) :=
  batch.queries.map (lookupBody? batch.substitution)

/-- The publisher observes its supplied region through exact subslices.  It
does not capture a second copy of the token carrier. -/
def substitutionRegionCall (batch : SubstitutionQueryBatch) :
    RegionCall RuntimeSym (List (Option (List RuntimeSym))) where
  values := substitutionStorage batch.substitution
  publish := fun storage =>
    batch.queries.map fun variableName =>
      (lookupBodySlice? batch.substitution variableName).map
        (Slice.read storage)

theorem substitutionRegionCall_fresh_exact
    (batch : SubstitutionQueryBatch) :
    (substitutionRegionCall batch).publish
        (substitutionRegionCall batch).values =
      sourceQueryObservation batch := by
  unfold substitutionRegionCall sourceQueryObservation
  apply List.map_congr_left
  intro variableName member
  exact lookupBodySlice?_read batch.substitution variableName

/-- Reset-and-reuse preserves every batch, query, absence, and duplicate
occurrence observation in order.  Only complete lists cross the boundary. -/
theorem reusableSubstitutionRegions_exact
    (batches : List SubstitutionQueryBatch) :
    (observeReusableRegionCalls
        (batches.map substitutionRegionCall)).1 =
      batches.map sourceQueryObservation := by
  rw [observeReusableRegionCalls_exact]
  simp only [observeFreshRegionCalls, List.map_map]
  apply List.map_congr_left
  intro batch member
  exact substitutionRegionCall_fresh_exact batch

/-- The same lowering never allocates more logical sequence regions than
fresh-per-call execution. -/
theorem reusableSubstitutionRegions_allocationCount_le
    (batches : List SubstitutionQueryBatch) :
    reusableSequenceAllocationCount
        ((batches.map substitutionRegionCall).map (·.values)) ≤
      batches.length := by
  simpa using reusableRegionAllocationCount_le_fresh
    (batches.map substitutionRegionCall)

/-! ## Positive and refusing examples -/

namespace Examples

def replacementA : ConstantHeadedFormula :=
  ⟨"wff", [.const "A"]⟩

def replacementB : ConstantHeadedFormula :=
  ⟨"wff", [.const "B"]⟩

def emptyReplacement : ConstantHeadedFormula :=
  ⟨"wff", []⟩

def positiveSubstitution : FiniteSubstitution :=
  [⟨"x", replacementA⟩, ⟨"empty", emptyReplacement⟩]

theorem positive_slice_reads_body :
    (lookupBodySlice? positiveSubstitution "x").map
        (Slice.read (substitutionStorage positiveSubstitution)) =
      some [.const "A"] := by
  rfl

theorem empty_body_slice_is_exact :
    (lookupBodySlice? positiveSubstitution "empty").map
        (Slice.read (substitutionStorage positiveSubstitution)) =
      some [] := by
  rfl

def duplicateSubstitution : FiniteSubstitution :=
  [⟨"x", replacementA⟩, ⟨"x", replacementB⟩]

/-- The later duplicate remains visible in the relational source. -/
theorem duplicate_later_is_relationally_visible :
    LookupSemantics duplicateSubstitution "x" replacementB := by
  simp [LookupSemantics, duplicateSubstitution]

/-- The compact deterministic lowering chooses the first occurrence. -/
theorem duplicate_slice_selects_first :
    (lookupBodySlice? duplicateSubstitution "x").map
        (Slice.read (substitutionStorage duplicateSubstitution)) =
      some replacementA.body := by
  rfl

/-- Therefore projection uniqueness is a semantic admission premise, not a
performance hint. -/
theorem duplicate_keys_refused :
    ¬ SubstitutionKeysUnique duplicateSubstitution := by
  simp [SubstitutionKeysUnique, duplicateSubstitution]

def referenceBoundaryPlan : ReusePlan where
  lifetime := .callLocal
  boundary := .reference

/-- Scratch reuse is refused when the public result could retain a reference
instead of a complete value. -/
theorem reference_boundary_refuses_reuse :
    referenceBoundaryPlan.supportsReuse = false := by
  rfl

end Examples

#print axioms lookupBodySlice?_read
#print axioms lookupBodySlice?_eq_some_iff_of_unique
#print axioms fusedMatch_formula_slices_iff
#print axioms packedAssertionTemplate_bodySlice
#print axioms publishAssertionBodyAt?_read
#print axioms reusableSubstitutionRegions_exact
#print axioms Examples.duplicate_later_is_relationally_visible
#print axioms Examples.duplicate_keys_refused
#print axioms Examples.reference_boundary_refuses_reuse

end Mettapedia.Languages.Metamath.InferenceAssertionSliceCompilation
