import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Parsing.HornCertificate

/-!
# Flat variable-head compilation

Some admitted first-order rules have a fixed relation head whose arguments
are all variable slots.  For that fragment, a generated machine need not
materialize an application node and then ask a general matcher to decompose
it again.  It can consume the arguments positionally while retaining the
ordinary substitution discipline for repeated variables.

This module gives the fragment a decidable recognizer, an explicit compiled
artifact, and an exact realization theorem.  Rules containing a rigid or
nested argument are rejected by this transform and remain available to the
general rule-machine path.
-/

namespace Mettapedia.GSLT.LanguageDef.FlatVariableHeadCompilation

open Mettapedia.GSLT.Parsing.HornCertificate

/-- Recover the variable slot at every argument position.  A rigid or nested
argument makes the head ineligible for this particular lowering. -/
def flatVariables? : Terms → Option (List Nat)
  | .nil => some []
  | .cons (.var identifier) tail => do
      let identifiers ← flatVariables? tail
      pure (identifier :: identifiers)
  | .cons _ _ => none

/-- The compact artifact retained for one admitted flat head. -/
structure FlatHead where
  relation : String
  slots : List Nat
  deriving DecidableEq, Repr

/-- Compile a source head exactly when every argument is a variable slot. -/
def compile? (head : Atom) : Option FlatHead := do
  let slots ← flatVariables? head.arguments
  pure { relation := head.relation, slots }

/-- Directly instantiate the positional variable inventory without first
constructing a source `Atom`. -/
def instantiateVariables
    (substitution : Substitution) : List Nat → Option GroundTerms
  | [] => some .nil
  | identifier :: identifiers => do
      let value ← instantiateTerm substitution (.var identifier)
      let tail ← instantiateVariables substitution identifiers
      pure (.cons value tail)

/-- Execute the compact artifact at the observation boundary. -/
def instantiateFlatHead
    (substitution : Substitution) (head : FlatHead) : Option GroundAtom := do
  let arguments ← instantiateVariables substitution head.slots
  pure { relation := head.relation, arguments }

/-- The positional argument program is exactly ordinary term-list
instantiation on every head accepted by the recognizer. -/
theorem instantiateTerms_eq_instantiateVariables_of_flatVariables?
    (substitution : Substitution) (arguments : Terms)
    (slots : List Nat)
    (accepted : flatVariables? arguments = some slots) :
    instantiateTerms substitution arguments =
      instantiateVariables substitution slots := by
  revert slots
  refine Terms.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun sourceArguments =>
      ∀ sourceSlots, flatVariables? sourceArguments = some sourceSlots →
        instantiateTerms substitution sourceArguments =
          instantiateVariables substitution sourceSlots)
    ?_ ?_ ?_ ?_ ?_ ?_ arguments
  · intro _
    trivial
  · intro _
    trivial
  · intro _
    trivial
  · intro _ _ _
    trivial
  · intro sourceSlots acceptedNil
    simp [flatVariables?] at acceptedNil
    subst sourceSlots
    rfl
  · intro argument tail _ tailInduction sourceSlots acceptedCons
    cases argument with
    | var identifier =>
        cases tailAccepted : flatVariables? tail with
        | none => simp [flatVariables?, tailAccepted] at acceptedCons
        | some tailSlots =>
            simp [flatVariables?, tailAccepted] at acceptedCons
            subst sourceSlots
            simp only [instantiateTerms, instantiateVariables,
              Option.bind_eq_bind]
            rw [tailInduction tailSlots tailAccepted]
    | atom name => simp [flatVariables?] at acceptedCons
    | integer value => simp [flatVariables?] at acceptedCons
    | app constructor nested => simp [flatVariables?] at acceptedCons

/-- Compiling and directly consuming a flat head preserves its complete
ground observation. -/
theorem instantiateFlatHead_eq_instantiateAtom_of_compile?
    (substitution : Substitution) (source : Atom) (compiled : FlatHead)
    (accepted : compile? source = some compiled) :
    instantiateFlatHead substitution compiled =
      instantiateAtom substitution source := by
  unfold compile? at accepted
  cases slotsEq : flatVariables? source.arguments with
  | none => simp [slotsEq] at accepted
  | some slots =>
      simp [slotsEq] at accepted
      subst compiled
      unfold instantiateFlatHead instantiateAtom
      rw [instantiateTerms_eq_instantiateVariables_of_flatVariables?
        substitution source.arguments slots slotsEq]

/-- Admission retains both the source and the exact compiler equation. -/
structure AdmittedFlatHead where
  source : Atom
  compiled : FlatHead
  compile_eq : compile? source = some compiled

/-- Run the local recognizer and retain its successful compilation witness. -/
def admit? (source : Atom) : Option AdmittedFlatHead :=
  match accepted : compile? source with
  | none => none
  | some compiled => some { source, compiled, compile_eq := accepted }

/-- Admission succeeds exactly when the compiler recognizes the head. -/
theorem admit?_isSome_eq_compile?_isSome (source : Atom) :
    (admit? source).isSome = (compile? source).isSome := by
  unfold admit?
  split <;> simp_all

/-- Flat-head lowering as a composable computed realization. -/
def flatHeadRealization :
    Mettapedia.GSLT.SimpleRealization
      AdmittedFlatHead FlatHead (Substitution → Option GroundAtom) where
  compile := fun _ admitted => admitted.compiled
  observeSource := fun _ admitted substitution =>
    instantiateAtom substitution admitted.source
  observeArtifact := fun _ compiled substitution =>
    instantiateFlatHead substitution compiled
  adequate := by
    intro _ admitted
    funext substitution
    exact instantiateFlatHead_eq_instantiateAtom_of_compile?
      substitution admitted.source admitted.compiled admitted.compile_eq

/-! ## Positive, repeated-slot, and rejection canaries -/

private def fourSlotHead : Atom := {
  relation := "step"
  arguments := .ofList [.var 0, .var 1, .var 2, .var 3] }

private def eightSlotHead : Atom := {
  relation := "route-row"
  arguments := .ofList [
    .var 0, .var 1, .var 2, .var 3,
    .var 4, .var 5, .var 6, .var 7] }

private def repeatedSlotHead : Atom := {
  relation := "same"
  arguments := .ofList [.var 0, .var 0] }

/-- Two independently shaped relation heads compile to their positional
inventories without changing relation identity. -/
example :
    compile? fourSlotHead = some {
      relation := "step", slots := [0, 1, 2, 3] } ∧
    compile? eightSlotHead = some {
      relation := "route-row", slots := [0, 1, 2, 3, 4, 5, 6, 7] } := by
  decide

/-- Repeated positions remain repeated; the transform does not silently
replace equality constraints by fresh variables. -/
example :
    compile? repeatedSlotHead = some {
      relation := "same", slots := [0, 0] } := by
  decide

/-- A substitution for a repeated slot is observed identically by the source
and compact artifacts. -/
example :
    let substitution : Substitution := [(0, .atom "value")]
    instantiateAtom substitution repeatedSlotHead =
      instantiateFlatHead substitution {
        relation := "same", slots := [0, 0] } := by
  decide

/-- Nested structure is outside this transform and fails closed. -/
example :
    (compile? {
      relation := "edge"
      arguments := .ofList [.app "node" (.ofList [.var 0]), .var 1]
    }).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.FlatVariableHeadCompilation
