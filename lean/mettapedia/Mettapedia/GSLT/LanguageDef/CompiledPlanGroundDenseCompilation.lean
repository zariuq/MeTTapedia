import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.CompiledPlanLowering
import Mettapedia.GSLT.LanguageDef.CompiledPlanTermSemantics

/-!
# Exact ground dense-head matching for compiled plans

The admitted `CGP1` carrier gives each rule a finite `UInt32` variable width.
When a dynamic goal is ground, the generated machine can compile every source
variable to a bounded slot and match the rule head directly: first occurrences
write a ground subtree, repeated occurrences compare against that slot, and
rigid constructors are traversed without materializing a substituted rule
head.

This module states the optimization at the exact typed-plan boundary.  The
source matcher uses the ordinary `UInt32 -> Option GroundTerm` substitution;
the compiled matcher uses only subtype-bounded slots.  A successful local
compiler equation and the environment decoder relate the two executions.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanGroundDenseCompilation

open CompiledPlanAdmission
open CompiledPlanTermSemantics

/-- A rule-local variable slot proved smaller than the generated width. -/
abbrev Slot (width : UInt32) := { slot : UInt32 // slot < width }

/-! ## Concrete atom-variable identity boundary -/

/-- The generic C atom carrier reserves raw variable identity zero.  A typed
compiled-plan slot is therefore represented by its widened value plus one.
The widening happens before addition, so even the greatest `UInt32` slot
cannot wrap the `UInt64` carrier. -/
def atomVariableId (slot : UInt32) : UInt64 := slot.toUInt64 + 1

theorem atomVariableId_toNat (slot : UInt32) :
    (atomVariableId slot).toNat = slot.toNat + 1 := by
  rw [atomVariableId, UInt64.toNat_add, UInt32.toUInt64_toNat]
  change (slot.toNat + 1) % 2 ^ 64 = slot.toNat + 1
  rw [Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt
    (Nat.succ_le_iff.mpr (UInt32.toNat_lt slot)) (by decide)

/-- No compiled slot aliases the atom carrier's reserved identity. -/
theorem atomVariableId_ne_zero (slot : UInt32) :
    atomVariableId slot ≠ 0 := by
  intro equal
  have observed := congrArg UInt64.toNat equal
  rw [atomVariableId_toNat] at observed
  simp at observed

/-- Raw atom variable identities preserve exact rule-local slot identity. -/
theorem atomVariableId_injective : Function.Injective atomVariableId := by
  intro left right equal
  have observed := congrArg UInt64.toNat equal
  rw [atomVariableId_toNat, atomVariableId_toNat] at observed
  exact UInt32.toNat_inj.mp (Nat.add_right_cancel observed)

/-- Subtracting the reserved one-based offset recovers the exact source slot
at the natural-number observation used by the generated interval checker. -/
theorem atomVariableId_offset_toNat (slot : UInt32) :
    (atomVariableId slot).toNat - 1 = slot.toNat := by
  rw [atomVariableId_toNat]
  exact Nat.add_sub_cancel_right slot.toNat 1

/-- A bounded compiled slot lands inside the raw half-open interval beginning
at one and having exactly the generated rule width. -/
theorem atomVariableId_bounded (slot : Slot width) :
    (atomVariableId slot.val).toNat < width.toNat + 1 := by
  rw [atomVariableId_toNat]
  exact Nat.add_lt_add_right
    (UInt32.lt_iff_toNat_lt.mp slot.property) 1

mutual

/-- Exact typed plan with every variable occurrence replaced by a bounded
rule-local slot. -/
inductive DenseTerm (width : UInt32) where
  | symbol (name : List UInt8)
  | variable (slot : Slot width)
  | string (value : List UInt8)
  | integer (value : Int64)
  | application (head : List UInt8) (arguments : DenseTerms width)
  deriving DecidableEq, Repr

inductive DenseTerms (width : UInt32) where
  | nil
  | cons (head : DenseTerm width) (tail : DenseTerms width)
  deriving DecidableEq, Repr

end

mutual

/-- Resolve every source variable through the rule's declared finite width. -/
def compileTerm? (width : UInt32) : Term -> Option (DenseTerm width)
  | .symbol name => some (.symbol name)
  | .variable slot =>
      if bounded : slot < width then some (.variable ⟨slot, bounded⟩)
      else none
  | .string value => some (.string value)
  | .integer value => some (.integer value)
  | .application head arguments => do
      let compiled <- compileTerms? width arguments
      some (.application head compiled)

def compileTerms? (width : UInt32) : Terms -> Option (DenseTerms width)
  | .nil => some .nil
  | .cons head tail => do
      let compiledHead <- compileTerm? width head
      let compiledTail <- compileTerms? width tail
      some (.cons compiledHead compiledTail)

end

mutual

/-- Every source term whose observed slots are below the declared width has a
bounded generated representation. -/
theorem compileTerm?_complete_of_all_lt
    (width : UInt32) (source : Term)
    (bounded : (CompiledPlanLowering.termUsedVariables source).all
      (fun slot => slot < width.toNat) = true) :
    ∃ compiled, compileTerm? width source = some compiled := by
  cases source with
  | symbol name => exact ⟨.symbol name, rfl⟩
  | «variable» slot =>
      have boundedDecision :
          decide (slot.toNat < width.toNat) = true := by
        simpa [CompiledPlanLowering.termUsedVariables] using bounded
      have slotNatBound : slot.toNat < width.toNat := by
        exact of_decide_eq_true boundedDecision
      have slotBound : slot < width :=
        UInt32.lt_iff_toNat_lt.mpr slotNatBound
      exact ⟨.variable ⟨slot, slotBound⟩, by simp [compileTerm?, slotBound]⟩
  | string value => exact ⟨.string value, rfl⟩
  | integer value => exact ⟨.integer value, rfl⟩
  | application head arguments =>
      obtain ⟨compiledArguments, argumentsCompiled⟩ :=
        compileTerms?_complete_of_all_lt width arguments bounded
      exact ⟨.application head compiledArguments,
        by simp [compileTerm?, argumentsCompiled]⟩

/-- The list-shaped bounded compiler is complete under the same local support
predicate. -/
theorem compileTerms?_complete_of_all_lt
    (width : UInt32) (source : Terms)
    (bounded : (CompiledPlanLowering.termsUsedVariables source).all
      (fun slot => slot < width.toNat) = true) :
    ∃ compiled, compileTerms? width source = some compiled := by
  cases source with
  | nil => exact ⟨.nil, rfl⟩
  | cons head tail =>
      have pieces :
          (CompiledPlanLowering.termUsedVariables head).all
              (fun slot => slot < width.toNat) = true ∧
            (CompiledPlanLowering.termsUsedVariables tail).all
              (fun slot => slot < width.toNat) = true := by
        simpa [CompiledPlanLowering.termsUsedVariables, List.all_append,
          Bool.and_eq_true] using bounded
      obtain ⟨compiledHead, headCompiled⟩ :=
        compileTerm?_complete_of_all_lt width head pieces.1
      obtain ⟨compiledTail, tailCompiled⟩ :=
        compileTerms?_complete_of_all_lt width tail pieces.2
      exact ⟨.cons compiledHead compiledTail,
        by simp [compileTerms?, headCompiled, tailCompiled]⟩

end


/-- Source substitution used by the ordinary directional ground matcher. -/
abbrev SourceEnvironment := Substitution

/-- Compiled bounded-slot environment. -/
abbrev DenseEnvironment (width : UInt32) := Slot width -> Option GroundTerm

def emptySourceEnvironment : SourceEnvironment := emptySubstitution

def emptyDenseEnvironment (_width : UInt32) : DenseEnvironment width :=
  fun _ => none

/-- Decode a bounded environment at the exact source substitution boundary. -/
def decodeDense (width : UInt32) (environment : DenseEnvironment width) :
    SourceEnvironment :=
  fun slot =>
    if bounded : slot < width then environment ⟨slot, bounded⟩ else none

def writeDense (environment : DenseEnvironment width)
    (slot : Slot width) (value : GroundTerm) : DenseEnvironment width :=
  fun candidate => if candidate = slot then some value else environment candidate

theorem decodeDense_empty (width : UInt32) :
    decodeDense width (emptyDenseEnvironment width) = emptySourceEnvironment := by
  funext slot
  simp [decodeDense, emptyDenseEnvironment, emptySourceEnvironment,
    emptySubstitution]

/-- One bounded write has exactly the ordinary source-slot observation. -/
theorem decodeDense_write (width : UInt32)
    (environment : DenseEnvironment width) (slot : Slot width)
    (value : GroundTerm) :
    decodeDense width (writeDense environment slot value) =
      write (decodeDense width environment) slot.val value := by
  funext candidate
  by_cases same : candidate = slot.val
  · subst candidate
    simp [decodeDense, writeDense, write, slot.property]
  · by_cases bounded : candidate < width
    · have different : (⟨candidate, bounded⟩ : Slot width) ≠ slot := by
        intro equality
        exact same (congrArg Subtype.val equality)
      simp [decodeDense, writeDense, write, bounded, same, different]
    · simp [decodeDense, write, bounded, same]

mutual

/-- Ordinary source matcher, written independently over unbounded source
slot names. -/
def matchSource :
    Term -> GroundTerm -> SourceEnvironment -> Option SourceEnvironment
  | .variable slot, target, environment =>
      match environment slot with
      | none => some (write environment slot target)
      | some previous => if target = previous then some environment else none
  | .symbol expected, .symbol actual, environment =>
      if expected = actual then some environment else none
  | .string expected, .string actual, environment =>
      if expected = actual then some environment else none
  | .integer expected, .integer actual, environment =>
      if expected = actual then some environment else none
  | .application expectedHead expectedArguments,
      .application actualHead actualArguments, environment =>
      if expectedHead = actualHead then
        matchSourceTerms expectedArguments actualArguments environment
      else none
  | _, _, _ => none

def matchSourceTerms :
    Terms -> GroundTerms -> SourceEnvironment -> Option SourceEnvironment
  | .nil, .nil, environment => some environment
  | .cons sourceHead sourceTail, .cons targetHead targetTail, environment =>
      match matchSource sourceHead targetHead environment with
      | none => none
      | some extended => matchSourceTerms sourceTail targetTail extended
  | _, _, _ => none

end

mutual

/-- Direct matcher over the bounded generated pattern. -/
def matchDense :
    DenseTerm width -> GroundTerm -> DenseEnvironment width ->
      Option (DenseEnvironment width)
  | .variable slot, target, environment =>
      match environment slot with
      | none => some (writeDense environment slot target)
      | some previous => if target = previous then some environment else none
  | .symbol expected, .symbol actual, environment =>
      if expected = actual then some environment else none
  | .string expected, .string actual, environment =>
      if expected = actual then some environment else none
  | .integer expected, .integer actual, environment =>
      if expected = actual then some environment else none
  | .application expectedHead expectedArguments,
      .application actualHead actualArguments, environment =>
      if expectedHead = actualHead then
        matchDenseTerms expectedArguments actualArguments environment
      else none
  | _, _, _ => none

def matchDenseTerms :
    DenseTerms width -> GroundTerms -> DenseEnvironment width ->
      Option (DenseEnvironment width)
  | .nil, .nil, environment => some environment
  | .cons sourceHead sourceTail, .cons targetHead targetTail, environment =>
      match matchDense sourceHead targetHead environment with
      | none => none
      | some extended => matchDenseTerms sourceTail targetTail extended
  | _, _, _ => none

end

/-! ## Closed-pattern decision boundary -/

mutual

/-- If the independently defined instantiator proves a source pattern closed,
matching that pattern cannot extend the environment: it is exactly equality
with the resulting ground term. -/
theorem matchSource_of_instantiate_empty
    (source : Term) (target expected : GroundTerm)
    (environment : SourceEnvironment)
    (closed : instantiateTerm emptySubstitution source = some expected) :
    matchSource source target environment =
      if expected = target then some environment else none := by
  cases source with
  | symbol name =>
      simp only [instantiateTerm] at closed
      cases closed
      cases target <;> simp [matchSource]
  | «variable» slot =>
      simp [instantiateTerm, emptySubstitution] at closed
  | string value =>
      simp only [instantiateTerm] at closed
      cases closed
      cases target <;> simp [matchSource]
  | integer value =>
      simp only [instantiateTerm] at closed
      cases closed
      cases target <;> simp [matchSource]
  | application head arguments =>
      simp only [instantiateTerm] at closed
      cases groundedEq : instantiateTerms emptySubstitution arguments with
      | none => simp [groundedEq] at closed
      | some grounded =>
          simp [groundedEq] at closed
          cases closed
          cases target with
          | symbol name => simp [matchSource]
          | string value => simp [matchSource]
          | integer value => simp [matchSource]
          | application targetHead targetArguments =>
              by_cases sameHead : head = targetHead
              · subst targetHead
                simpa [matchSource] using
                  matchSourceTerms_of_instantiate_empty
                    arguments targetArguments grounded environment groundedEq
              · simp [matchSource, sameHead]

/-- The list-shaped companion threads the unchanged environment across every
closed child and decides exactly the equality of the complete argument list. -/
theorem matchSourceTerms_of_instantiate_empty
    (sources : Terms) (targets expected : GroundTerms)
    (environment : SourceEnvironment)
    (closed : instantiateTerms emptySubstitution sources = some expected) :
    matchSourceTerms sources targets environment =
      if expected = targets then some environment else none := by
  cases sources with
  | nil =>
      simp only [instantiateTerms] at closed
      cases closed
      cases targets <;> simp [matchSourceTerms]
  | cons sourceHead sourceTail =>
      simp only [instantiateTerms] at closed
      cases headEq : instantiateTerm emptySubstitution sourceHead with
      | none => simp [headEq] at closed
      | some expectedHead =>
          cases tailEq : instantiateTerms emptySubstitution sourceTail with
          | none => simp [headEq, tailEq] at closed
          | some expectedTail =>
              simp [headEq, tailEq] at closed
              cases closed
              cases targets with
              | nil => simp [matchSourceTerms]
              | cons targetHead targetTail =>
                  rw [matchSourceTerms]
                  rw [matchSource_of_instantiate_empty
                    sourceHead targetHead expectedHead environment headEq]
                  by_cases sameHead : expectedHead = targetHead
                  · subst targetHead
                    simp
                    exact matchSourceTerms_of_instantiate_empty
                      sourceTail targetTail expectedTail environment tailEq
                  · simp [sameHead]

end

/-- A closed pattern can neither mint nor remove a binding. -/
theorem matchSource_closed_preserves_environment
    (source : Term) (target expected : GroundTerm)
    (environment result : SourceEnvironment)
    (closed : instantiateTerm emptySubstitution source = some expected)
    (matched : matchSource source target environment = some result) :
    result = environment := by
  rw [matchSource_of_instantiate_empty
    source target expected environment closed] at matched
  split at matched <;> simp_all

/-- Negative canary: a closed constructor mismatch remains a mismatch and
does not become a vacuous success through compilation. -/
example :
    matchSource (.application [1] .nil)
      (.application [2] .nil) emptySourceEnvironment = none := by
  decide

/-! The closed-pattern theorem is deliberately about ordinary matching.  An
enriched gradual matcher with an authored wildcard has a different algebra:
closed syntax need not factor through equality. -/

private def isWildcardSymbol (wildcard : List UInt8) : GroundTerm → Bool
  | .symbol name => name == wildcard
  | _ => false

mutual

private def matchGroundWithWildcard (wildcard : List UInt8) :
    GroundTerm → GroundTerm → Bool
  | left, right =>
      if isWildcardSymbol wildcard left || isWildcardSymbol wildcard right then
        true
      else
        match left, right with
        | .symbol expected, .symbol actual => expected == actual
        | .string expected, .string actual => expected == actual
        | .integer expected, .integer actual => expected == actual
        | .application expectedHead expectedArguments,
            .application actualHead actualArguments =>
            expectedHead == actualHead &&
              matchGroundTermsWithWildcard wildcard
                expectedArguments actualArguments
        | _, _ => false

private def matchGroundTermsWithWildcard (wildcard : List UInt8) :
    GroundTerms → GroundTerms → Bool
  | .nil, .nil => true
  | .cons expectedHead expectedTail, .cons actualHead actualTail =>
      matchGroundWithWildcard wildcard expectedHead actualHead &&
        matchGroundTermsWithWildcard wildcard expectedTail actualTail
  | _, _ => false

end

private def nestedWildcardPattern : GroundTerm :=
  .application [9] (.cons (.symbol [0]) .nil)

private def nestedWildcardTarget : GroundTerm :=
  .application [9] (.cons (.integer 7) .nil)

/-- Positive boundary canary: a nested authored wildcard accepts a distinct
closed target. -/
example :
    matchGroundWithWildcard [0] nestedWildcardPattern
      nestedWildcardTarget = true := by
  decide

/-- Negative equality canary: the same gradual success cannot be justified by
the ordinary closed-expression equality decision. -/
example : nestedWildcardPattern ≠ nestedWildcardTarget := by
  decide

/-! ## Exact representation refinement -/

mutual

/-- A successfully compiled bounded term has exactly the independent source
matcher semantics whenever the two environments have the same decoded
observation. -/
private def refineTerm
    (width : UInt32) (source : Term) (compiled : DenseTerm width)
    (accepted : compileTerm? width source = some compiled)
    (sourceEnvironment : SourceEnvironment)
    (denseEnvironment : DenseEnvironment width)
    (related : decodeDense width denseEnvironment = sourceEnvironment)
    (target : GroundTerm) :
    Option.map (decodeDense width)
        (matchDense compiled target denseEnvironment) =
      matchSource source target sourceEnvironment := by
  cases source with
  | symbol expected =>
      simp [compileTerm?] at accepted
      subst compiled
      cases target <;> simp [matchDense, matchSource, related]
  | «variable» slot =>
      unfold compileTerm? at accepted
      split at accepted
      next bounded =>
        simp at accepted
        subst compiled
        have lookupEq :
            denseEnvironment ⟨slot, bounded⟩ = sourceEnvironment slot := by
          have pointwise := congrFun related slot
          simpa [decodeDense, bounded] using pointwise
        cases denseEq : denseEnvironment ⟨slot, bounded⟩ with
        | none =>
            have sourceEq : sourceEnvironment slot = none := by
              rw [← lookupEq]
              exact denseEq
            simp only [matchDense, denseEq, Option.map_some, matchSource,
              sourceEq]
            rw [decodeDense_write width denseEnvironment ⟨slot, bounded⟩
              target, related]
        | some previous =>
            have sourceEq : sourceEnvironment slot = some previous := by
              rw [← lookupEq]
              exact denseEq
            by_cases same : target = previous
            · simp [matchDense, matchSource, denseEq, sourceEq, same, related]
            · simp [matchDense, matchSource, denseEq, sourceEq, same]
      next unbounded => simp at accepted
  | string expected =>
      simp [compileTerm?] at accepted
      subst compiled
      cases target <;> simp [matchDense, matchSource, related]
  | integer expected =>
      simp [compileTerm?] at accepted
      subst compiled
      cases target <;> simp [matchDense, matchSource, related]
  | application expectedHead sourceArguments =>
      unfold compileTerm? at accepted
      cases compiledEq : compileTerms? width sourceArguments with
      | none => simp [compiledEq] at accepted
      | some compiledArguments =>
          simp [compiledEq] at accepted
          subst compiled
          cases target with
          | symbol actual => simp [matchDense, matchSource]
          | string actual => simp [matchDense, matchSource]
          | integer actual => simp [matchDense, matchSource]
          | application actualHead actualArguments =>
              by_cases same : expectedHead = actualHead
              · simp [matchDense, matchSource, same]
                exact refineTerms width sourceArguments compiledArguments
                  compiledEq sourceEnvironment denseEnvironment related
                  actualArguments
              · simp [matchDense, matchSource, same]

/-- The list-shaped companion theorem threads exactly the environment returned
by each compiled child into the next child. -/
private def refineTerms
    (width : UInt32) (source : Terms) (compiled : DenseTerms width)
    (accepted : compileTerms? width source = some compiled)
    (sourceEnvironment : SourceEnvironment)
    (denseEnvironment : DenseEnvironment width)
    (related : decodeDense width denseEnvironment = sourceEnvironment)
    (target : GroundTerms) :
    Option.map (decodeDense width)
        (matchDenseTerms compiled target denseEnvironment) =
      matchSourceTerms source target sourceEnvironment := by
  cases source with
  | nil =>
      simp [compileTerms?] at accepted
      subst compiled
      cases target <;> simp [matchDenseTerms, matchSourceTerms, related]
  | cons sourceHead sourceTail =>
      unfold compileTerms? at accepted
      cases headEq : compileTerm? width sourceHead with
      | none => simp [headEq] at accepted
      | some compiledHead =>
          cases tailEq : compileTerms? width sourceTail with
          | none => simp [headEq, tailEq] at accepted
          | some compiledTail =>
              simp [headEq, tailEq] at accepted
              subst compiled
              cases target with
              | nil => simp [matchDenseTerms, matchSourceTerms]
              | cons targetHead targetTail =>
                  cases denseHeadEq :
                      matchDense compiledHead targetHead denseEnvironment with
                  | none =>
                      have sourceHeadEq :
                          matchSource sourceHead targetHead sourceEnvironment =
                            none := by
                        have refined := refineTerm width sourceHead compiledHead
                          headEq sourceEnvironment denseEnvironment related
                          targetHead
                        simpa [denseHeadEq] using refined.symm
                      simp [matchDenseTerms, matchSourceTerms, denseHeadEq,
                        sourceHeadEq]
                  | some extendedDense =>
                      have refinedHead := refineTerm width sourceHead compiledHead
                        headEq sourceEnvironment denseEnvironment related
                        targetHead
                      cases sourceHeadEq :
                          matchSource sourceHead targetHead sourceEnvironment with
                      | none =>
                          simp [denseHeadEq, sourceHeadEq] at refinedHead
                      | some extendedSource =>
                          have extendedRelated :
                              decodeDense width extendedDense =
                                extendedSource := by
                            simpa [denseHeadEq, sourceHeadEq] using refinedHead
                          simp only [matchDenseTerms, matchSourceTerms,
                            denseHeadEq, sourceHeadEq]
                          exact refineTerms width sourceTail compiledTail tailEq
                            extendedSource extendedDense extendedRelated
                            targetTail

end

theorem matchDense_compileTerm?
    (width : UInt32) (source : Term) (compiled : DenseTerm width)
    (accepted : compileTerm? width source = some compiled)
    (sourceEnvironment : SourceEnvironment)
    (denseEnvironment : DenseEnvironment width)
    (related : decodeDense width denseEnvironment = sourceEnvironment)
    (target : GroundTerm) :
    Option.map (decodeDense width)
        (matchDense compiled target denseEnvironment) =
      matchSource source target sourceEnvironment :=
  refineTerm width source compiled accepted sourceEnvironment denseEnvironment
    related target

theorem matchDense_compileTerms?
    (width : UInt32) (source : Terms) (compiled : DenseTerms width)
    (accepted : compileTerms? width source = some compiled)
    (sourceEnvironment : SourceEnvironment)
    (denseEnvironment : DenseEnvironment width)
    (related : decodeDense width denseEnvironment = sourceEnvironment)
    (target : GroundTerms) :
    Option.map (decodeDense width)
        (matchDenseTerms compiled target denseEnvironment) =
      matchSourceTerms source target sourceEnvironment :=
  refineTerms width source compiled accepted sourceEnvironment denseEnvironment
    related target

/-- Starting from empty environments, direct dense matching has exactly the
ordinary directional source-matching observation. -/
theorem compiledMatch_eq_sourceMatch
    (width : UInt32) (source : Term) (compiled : DenseTerm width)
    (accepted : compileTerm? width source = some compiled)
    (target : GroundTerm) :
    Option.map (decodeDense width)
        (matchDense compiled target (emptyDenseEnvironment width)) =
      matchSource source target emptySourceEnvironment := by
  exact matchDense_compileTerm? width source compiled accepted
    emptySourceEnvironment (emptyDenseEnvironment width)
    (decodeDense_empty width) target

/-! ## Admitted artifact and composable realization -/

/-- The artifact retains both the exact source term and the successful local
bounded-slot compiler equation. -/
structure AdmittedGroundHead where
  width : UInt32
  source : Term
  compiled : DenseTerm width
  compile_eq : compileTerm? width source = some compiled
  deriving DecidableEq, Repr

def admit? (width : UInt32) (source : Term) : Option AdmittedGroundHead :=
  match accepted : compileTerm? width source with
  | none => none
  | some compiled =>
      some { width, source, compiled, compile_eq := accepted }

/-- The admitted artifact exists whenever every observed source slot is below
the declared generated width. -/
theorem admit?_complete_of_all_lt
    (width : UInt32) (source : Term)
    (bounded : (CompiledPlanLowering.termUsedVariables source).all
      (fun slot => slot < width.toNat) = true) :
    ∃ admitted, admit? width source = some admitted := by
  obtain ⟨compiled, compiledEq⟩ :=
    compileTerm?_complete_of_all_lt width source bounded
  unfold admit?
  split
  next rejected =>
    rw [compiledEq] at rejected
    contradiction
  next generated accepted =>
    exact ⟨{ width, source, compiled := generated, compile_eq := accepted },
      rfl⟩

/-- Successful admission exposes the exact source-matcher observation without
requiring clients to inspect the dependent generated term. -/
theorem match_admit?_some
    (width : UInt32) (source : Term) (admitted : AdmittedGroundHead)
    (accepted : admit? width source = some admitted) (target : GroundTerm) :
    Option.map (decodeDense admitted.width)
        (matchDense admitted.compiled target
          (emptyDenseEnvironment admitted.width)) =
      matchSource source target emptySourceEnvironment := by
  unfold admit? at accepted
  split at accepted
  next rejected => simp at accepted
  next compiled compiledEq =>
      simp at accepted
      subst admitted
      exact compiledMatch_eq_sourceMatch width source compiled compiledEq target

/-- The bounded generated matcher is a computed realization of the
independently defined source matcher. -/
def groundDenseHeadRealization :
    Mettapedia.GSLT.SimpleRealization
      AdmittedGroundHead AdmittedGroundHead
      (GroundTerm -> Option SourceEnvironment) where
  compile := fun _ admitted => admitted
  observeSource := fun _ admitted target =>
    matchSource admitted.source target emptySourceEnvironment
  observeArtifact := fun _ admitted target =>
    Option.map (decodeDense admitted.width)
      (matchDense admitted.compiled target
        (emptyDenseEnvironment admitted.width))
  adequate := by
    intro _ admitted
    funext target
    exact compiledMatch_eq_sourceMatch admitted.width admitted.source
      admitted.compiled admitted.compile_eq target

/-! ## Exact work accounting -/

/-- The source instantiate-then-compare route materializes every source head
node before it can compare the result. -/
def sourceHeadMaterializations (admitted : AdmittedGroundHead) : Nat :=
  CompiledPlanLowering.termNodeCount admitted.source

/-- Direct matching traverses the compiled pattern and materializes no
intermediate rule-head nodes. -/
def compiledHeadMaterializations (_admitted : AdmittedGroundHead) : Nat := 0

theorem compiledHeadMaterializations_lt_source
    (admitted : AdmittedGroundHead) :
    compiledHeadMaterializations admitted <
      sourceHeadMaterializations admitted := by
  simpa [compiledHeadMaterializations, sourceHeadMaterializations] using
    CompiledPlanLowering.termNodeCount_positive admitted.source

/-! ## Independent witnesses and rejecting controls -/

private def parserShape : Term :=
  .application [1]
    (.cons (.string [2])
      (.cons (.variable 0)
        (.cons (.application [3] (.cons (.variable 0) .nil)) .nil)))

private def parserEqualTarget : GroundTerm :=
  .application [1]
    (.cons (.string [2])
      (.cons (.integer 4)
        (.cons (.application [3] (.cons (.integer 4) .nil)) .nil)))

private def parserUnequalTarget : GroundTerm :=
  .application [1]
    (.cons (.string [2])
      (.cons (.integer 4)
        (.cons (.application [3] (.cons (.integer 5) .nil)) .nil)))

/-- A parser/action-shaped nonlinear pattern compiles and accepts equal
repeated occurrences. -/
example :
    match admit? 1 parserShape with
    | none => false
    | some admitted =>
        (matchDense admitted.compiled parserEqualTarget
          (emptyDenseEnvironment admitted.width)).isSome = true := by
  rfl

/-- The same independently shaped pattern rejects unequal repeated
occurrences. -/
example :
    match admit? 1 parserShape with
    | none => false
    | some admitted =>
        (matchDense admitted.compiled parserUnequalTarget
          (emptyDenseEnvironment admitted.width)).isSome = false := by
  rfl

private def proofShape : Term :=
  .application [10]
    (.cons (.application [11] (.cons (.symbol [12]) .nil))
      (.cons (.variable 0) .nil))

/-- A proof/evaluator-shaped constructor-and-literal head independently
inhabits the same compiler fragment. -/
example : (compileTerm? 1 proofShape).isSome = true := by
  decide

/-- A source slot outside the rule-local generated width fails closed. -/
example : (compileTerm? 1 (.variable 1)).isSome = false := by
  decide


end Mettapedia.GSLT.LanguageDef.CompiledPlanGroundDenseCompilation
