import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
import Mettapedia.Languages.MeTTa.LeafPatchViewKernel

/-!
# Ground dense-head compilation

A first-order pattern matched against a ground term never needs symmetric
unification.  Once a generated finite inventory has resolved every source
variable to a bounded slot, the machine can traverse the pattern directly:
the first occurrence writes the ground subtree into its slot and every later
occurrence checks structural equality with that slot.

This module proves both refinement edges needed by that lowering.  The usual
association-list matcher is related to a functional source environment, and
the finite-slot matcher is related to that source environment through the
generated inventory decoder.  Their composition covers nonlinear patterns;
linearity is not an admission condition.  Unknown variables fail compilation,
and inconsistent repeated occurrences remain rejecting observations.
-/

namespace Mettapedia.GSLT.LanguageDef.GroundDenseHeadCompilation

open Mettapedia.Languages.MeTTa.LeafPatchViewKernel
open FiniteEnvironmentCompilation

variable {Symbol : Type} [DecidableEq Symbol]

/-- The generated pattern replaces authored variable identifiers with bounded
slots.  Ground terms are reused from the independent source matcher. -/
inductive DensePattern (Symbol Slot : Type) where
  | variable (slot : Slot)
  | symbol (value : Symbol)
  | node (left right : DensePattern Symbol Slot)
deriving DecidableEq, Repr

/-- Resolve every variable occurrence through one duplicate-free generated
inventory.  Repeated occurrences deliberately resolve to the same slot. -/
def compile? (inventory : Inventory Nat) :
    Pat Symbol -> Option (DensePattern Symbol inventory.Slot)
  | .var identifier =>
      (inventory.resolve? identifier).map DensePattern.variable
  | .sym value => some (.symbol value)
  | .node left right => do
      let compiledLeft <- compile? inventory left
      let compiledRight <- compile? inventory right
      pure (.node compiledLeft compiledRight)

/-- Interpret an association-list matcher environment extensionally. -/
def decodeListEnvironment (environment : List (Nat × Tm Symbol)) :
    SourceEnvironment Nat (Tm Symbol) :=
  fun identifier => lookup environment identifier

/-- Directional source matching into a functional environment.  This is the
ordinary ground-pattern algorithm, independent of finite-slot compilation. -/
def matchSource :
    Pat Symbol -> Tm Symbol -> SourceEnvironment Nat (Tm Symbol) ->
      Option (SourceEnvironment Nat (Tm Symbol))
  | .var identifier, term, environment =>
      match environment identifier with
      | none => some (writeSource environment (identifier, term))
      | some previous => if term = previous then some environment else none
  | .sym expected, .sym actual, environment =>
      if expected = actual then some environment else none
  | .sym _, .node _ _, _ => none
  | .node _ _, .sym _, _ => none
  | .node left right, .node actualLeft actualRight, environment =>
      match matchSource left actualLeft environment with
      | none => none
      | some extended => matchSource right actualRight extended

/-- Direct matching into the generated bounded-slot environment. -/
def matchDense (inventory : Inventory Nat) :
    DensePattern Symbol inventory.Slot -> Tm Symbol ->
      DenseEnvironment inventory (Tm Symbol) ->
      Option (DenseEnvironment inventory (Tm Symbol))
  | .variable slot, term, environment =>
      match environment slot with
      | none => some (writeDense inventory environment (slot, term))
      | some previous => if term = previous then some environment else none
  | .symbol expected, .sym actual, environment =>
      if expected = actual then some environment else none
  | .symbol _, .node _ _, _ => none
  | .node _ _, .sym _, _ => none
  | .node left right, .node actualLeft actualRight, environment =>
      match matchDense inventory left actualLeft environment with
      | none => none
      | some extended => matchDense inventory right actualRight extended

omit [DecidableEq Symbol] in
/-- Prepending an association-list binding has exactly the source
functional-write observation. -/
theorem decodeListEnvironment_cons
    (environment : List (Nat × Tm Symbol)) (identifier : Nat)
    (term : Tm Symbol) :
    decodeListEnvironment ((identifier, term) :: environment) =
      writeSource (decodeListEnvironment environment) (identifier, term) := by
  funext candidate
  by_cases same : candidate = identifier
  · subst candidate
    simp [decodeListEnvironment, lookup, writeSource]
  · have reverse : identifier ≠ candidate := Ne.symm same
    simp [decodeListEnvironment, lookup, writeSource, same, reverse]

/-- The existing association-list matcher and the independent functional
source matcher have the same complete environment observation. -/
theorem matchP_refines_matchSource
    (pattern : Pat Symbol) (term : Tm Symbol)
    (environment : List (Nat × Tm Symbol)) :
    Option.map decodeListEnvironment (matchP pattern term environment) =
      matchSource pattern term (decodeListEnvironment environment) := by
  induction pattern generalizing term environment with
  | var identifier =>
      cases previousEq : lookup environment identifier with
      | none =>
          simp [matchP, matchSource, decodeListEnvironment, previousEq,
            decodeListEnvironment_cons environment identifier term]
      | some previous =>
          by_cases same : term = previous
          · simp [matchP, matchSource, decodeListEnvironment, previousEq, same]
          · simp [matchP, matchSource, decodeListEnvironment, previousEq, same]
  | sym expected =>
      cases term with
      | sym actual =>
          by_cases same : expected = actual
          · simp [matchP, matchSource, same]
          · simp [matchP, matchSource, same]
      | node left right => simp [matchP, matchSource]
  | node left right leftInduction rightInduction =>
      cases term with
      | sym actual => simp [matchP, matchSource]
      | node actualLeft actualRight =>
          cases leftEq : matchP left actualLeft environment with
          | none =>
              have sourceLeft :
                  matchSource left actualLeft
                      (decodeListEnvironment environment) = none := by
                simpa [leftEq] using
                  (leftInduction actualLeft environment).symm
              simp [matchP, matchSource, leftEq, sourceLeft]
          | some extended =>
              have sourceLeft :
                  matchSource left actualLeft
                      (decodeListEnvironment environment) =
                    some (decodeListEnvironment extended) := by
                simpa [leftEq] using
                  (leftInduction actualLeft environment).symm
              simp only [matchP, matchSource, leftEq, sourceLeft]
              exact rightInduction actualRight extended

/-- Dense matching refines functional source matching whenever compilation
accepted the pattern and the two input environments decode to one another. -/
theorem matchDense_compile?
    (inventory : Inventory Nat)
    (source : Pat Symbol)
    (compiled : DensePattern Symbol inventory.Slot)
    (accepted : compile? inventory source = some compiled)
    (sourceEnvironment : SourceEnvironment Nat (Tm Symbol))
    (denseEnvironment : DenseEnvironment inventory (Tm Symbol))
    (related : decodeDense inventory denseEnvironment = sourceEnvironment)
    (term : Tm Symbol) :
    Option.map (decodeDense inventory)
        (matchDense inventory compiled term denseEnvironment) =
      matchSource source term sourceEnvironment := by
  induction source generalizing compiled term sourceEnvironment denseEnvironment with
  | var identifier =>
      unfold compile? at accepted
      cases selected : inventory.resolve? identifier with
      | none => simp [selected] at accepted
      | some slot =>
          simp [selected] at accepted
          subst compiled
          have lookupEq :
              denseEnvironment slot = sourceEnvironment identifier := by
            have pointwise := congrFun related identifier
            simpa [decodeDense, selected] using pointwise
          cases denseEq : denseEnvironment slot with
          | none =>
              have sourceEq : sourceEnvironment identifier = none := by
                rw [<- lookupEq]
                exact denseEq
              simp only [matchDense, denseEq, Option.map_some, matchSource,
                sourceEq]
              rw [decodeDense_writeDense inventory denseEnvironment identifier
                term slot selected, related]
          | some previous =>
              have sourceEq : sourceEnvironment identifier = some previous := by
                rw [<- lookupEq]
                exact denseEq
              by_cases same : term = previous
              · simp [matchDense, matchSource, denseEq, sourceEq, same, related]
              · simp [matchDense, matchSource, denseEq, sourceEq, same]
  | sym expected =>
      simp [compile?] at accepted
      subst compiled
      cases term with
      | sym actual =>
          by_cases same : expected = actual
          · simp [matchDense, matchSource, same, related]
          · simp [matchDense, matchSource, same]
      | node left right => simp [matchDense, matchSource]
  | node left right leftInduction rightInduction =>
      unfold compile? at accepted
      cases leftCompiledEq : compile? inventory left with
      | none => simp [leftCompiledEq] at accepted
      | some compiledLeft =>
          cases rightCompiledEq : compile? inventory right with
          | none => simp [leftCompiledEq, rightCompiledEq] at accepted
          | some compiledRight =>
              simp [leftCompiledEq, rightCompiledEq] at accepted
              subst compiled
              cases term with
              | sym actual => simp [matchDense, matchSource]
              | node actualLeft actualRight =>
                  cases denseLeftEq :
                      matchDense inventory compiledLeft actualLeft denseEnvironment with
                  | none =>
                      have sourceLeft :
                          matchSource left actualLeft sourceEnvironment = none := by
                        have refined := leftInduction compiledLeft
                          leftCompiledEq sourceEnvironment denseEnvironment related
                          actualLeft
                        simpa [denseLeftEq] using refined.symm
                      simp [matchDense, matchSource, denseLeftEq, sourceLeft]
                  | some extendedDense =>
                      have refinedLeft := leftInduction compiledLeft
                        leftCompiledEq sourceEnvironment denseEnvironment related
                        actualLeft
                      cases sourceLeftEq :
                          matchSource left actualLeft sourceEnvironment with
                      | none =>
                          simp [denseLeftEq, sourceLeftEq] at refinedLeft
                      | some extendedSource =>
                          have extendedRelated :
                              decodeDense inventory extendedDense = extendedSource := by
                            simpa [denseLeftEq, sourceLeftEq] using refinedLeft
                          simp only [matchDense, matchSource, denseLeftEq,
                            sourceLeftEq]
                          exact rightInduction compiledRight rightCompiledEq
                            extendedSource extendedDense extendedRelated actualRight

/-- Compilation plus dense matching has exactly the existing general
association-list matcher's extensional environment observation. -/
theorem compiledMatch_eq_sourceMatch
    (inventory : Inventory Nat)
    (source : Pat Symbol)
    (compiled : DensePattern Symbol inventory.Slot)
    (accepted : compile? inventory source = some compiled)
    (term : Tm Symbol) :
    Option.map (decodeDense inventory)
        (matchDense inventory compiled term
          (emptyDenseEnvironment inventory)) =
      Option.map decodeListEnvironment (matchP source term []) := by
  rw [matchDense_compile? inventory source compiled accepted
    (emptySourceEnvironment : SourceEnvironment Nat (Tm Symbol))
    (emptyDenseEnvironment inventory)
    (decodeDense_empty inventory) term]
  exact (matchP_refines_matchSource source term []).symm

/-- The admitted source retains the exact generated pattern and compiler
equation used by the runtime. -/
structure AdmittedGroundHead (inventory : Inventory Nat) where
  source : Pat Symbol
  compiled : DensePattern Symbol inventory.Slot
  /-- This equation pins `compiled` to the computing function's unique output.
  It is erased proof bookkeeping for the successful domain, not evidence
  accepted by a checker and not part of a runtime artifact. -/
  compile_eq : compile? inventory source = some compiled

def admit? (inventory : Inventory Nat) (source : Pat Symbol) :
    Option (AdmittedGroundHead (Symbol := Symbol) inventory) :=
  match accepted : compile? inventory source with
  | none => none
  | some compiled => some { source, compiled, compile_eq := accepted }

omit [DecidableEq Symbol] in
/-- Two successful compiler records for one source contain the same artifact.
An equation about the computing function has no artifact freedom; this is the
formal distinction from acceptance by existentially carried evidence. -/
theorem admitted_compiled_deterministic (inventory : Inventory Nat)
    (left right : AdmittedGroundHead (Symbol := Symbol) inventory)
    (same_source : left.source = right.source) :
    left.compiled = right.compiled := by
  have same_option : some left.compiled = some right.compiled := by
    calc
      some left.compiled = compile? inventory left.source := left.compile_eq.symm
      _ = compile? inventory right.source :=
        congrArg (compile? inventory) same_source
      _ = some right.compiled := right.compile_eq
  exact Option.some.inj same_option

/-- Ground dense-head lowering as a composable computed realization. -/
def groundDenseHeadRealization (inventory : Inventory Nat) :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedGroundHead (Symbol := Symbol) inventory)
      (DensePattern Symbol inventory.Slot)
      (Tm Symbol -> Option (SourceEnvironment Nat (Tm Symbol))) where
  compile := fun _ admitted => admitted.compiled
  observeSource := fun _ admitted term =>
    Option.map decodeListEnvironment (matchP admitted.source term [])
  observeArtifact := fun _ compiled term =>
    Option.map (decodeDense inventory)
      (matchDense inventory compiled term (emptyDenseEnvironment inventory))
  adequate := by
    intro _ admitted
    funext term
    exact compiledMatch_eq_sourceMatch inventory admitted.source
      admitted.compiled admitted.compile_eq term

/-! ## Positive, nonlinear, and rejecting controls -/

private def oneSlotInventory : Inventory Nat := {
  keys := [0]
  nodup := by simp }

private def repeatedPattern : Pat String :=
  .node (.var 0) (.node (.sym "tag") (.var 0))

private def onlySlot : oneSlotInventory.Slot := ⟨0, by decide⟩

private def repeatedCompiled : DensePattern String oneSlotInventory.Slot :=
  .node (.variable onlySlot)
    (.node (.symbol "tag") (.variable onlySlot))

private def equalGround : Tm String :=
  .node (.sym "same") (.node (.sym "tag") (.sym "same"))

private def unequalGround : Tm String :=
  .node (.sym "left") (.node (.sym "tag") (.sym "right"))

/-- Repeated variables compile to one repeated dense slot. -/
example : compile? oneSlotInventory repeatedPattern = some repeatedCompiled := by
  rfl

/-- Equal repeated occurrences are accepted without a linearity premise. -/
example :
    (matchDense oneSlotInventory repeatedCompiled equalGround
      (emptyDenseEnvironment oneSlotInventory)).isSome = true := by
  rfl

/-- Conflicting repeated occurrences remain rejected. -/
example :
    matchDense oneSlotInventory repeatedCompiled unequalGround
      (emptyDenseEnvironment oneSlotInventory) = none := by
  rfl

/-- A source variable absent from the generated inventory fails closed. -/
example : (compile? oneSlotInventory (.var 4 : Pat String)).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.GroundDenseHeadCompilation
