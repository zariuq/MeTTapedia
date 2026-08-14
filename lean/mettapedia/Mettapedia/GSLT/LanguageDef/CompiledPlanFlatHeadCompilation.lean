import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.CompiledPlanTermSemantics

/-!
# Flat positional heads for compiled plans

An admitted application whose immediate arguments are all dense variable
slots can be consumed positionally.  The generated runtime need not construct
the rule-side outer application merely so a matcher can decompose it again.
Repeated slots are retained and therefore retain their equality constraint.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanFlatHeadCompilation

open CompiledPlanAdmission
open CompiledPlanTermSemantics

/-- Recover every immediate variable slot or reject the shape. -/
def flatVariables? : Terms -> Option (List UInt32)
  | .nil => some []
  | .cons (.variable slot) tail => do
      let slots <- flatVariables? tail
      some (slot :: slots)
  | .cons _ _ => none

/-- Compact outer head plus its positional dense slots. -/
structure FlatHead where
  head : List UInt8
  slots : List UInt32
  deriving DecidableEq, Repr

/-- Local shape recognizer and compiler. -/
def compile? : Term -> Option FlatHead
  | .application head arguments => do
      let slots <- flatVariables? arguments
      some { head, slots }
  | _ => none

def instantiateSlots (substitution : Substitution) :
    List UInt32 -> Option GroundTerms
  | [] => some .nil
  | slot :: slots => do
      let value <- substitution slot
      let tail <- instantiateSlots substitution slots
      some (.cons value tail)

def execute (substitution : Substitution)
    (compiled : FlatHead) : Option GroundTerm := do
  let arguments <- instantiateSlots substitution compiled.slots
  some (.application compiled.head arguments)

/-- Positional consumption is exactly ordinary term-list instantiation for
every shape accepted by the local recognizer. -/
theorem instantiateTerms_eq_instantiateSlots_of_flatVariables?
    (substitution : Substitution) (arguments : Terms) (slots : List UInt32)
    (accepted : flatVariables? arguments = some slots) :
    instantiateTerms substitution arguments =
      instantiateSlots substitution slots := by
  revert slots
  refine Terms.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun sourceArguments =>
      ∀ sourceSlots, flatVariables? sourceArguments = some sourceSlots ->
        instantiateTerms substitution sourceArguments =
          instantiateSlots substitution sourceSlots)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ arguments
  · intro _
    trivial
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
  · intro head tail _ tailInduction sourceSlots acceptedCons
    cases head with
    | «variable» slot =>
        cases tailAccepted : flatVariables? tail with
        | none => simp [flatVariables?, tailAccepted] at acceptedCons
        | some tailSlots =>
            simp [flatVariables?, tailAccepted] at acceptedCons
            subst sourceSlots
            simp only [instantiateTerms, instantiateSlots,
              Option.bind_eq_bind]
            rw [tailInduction tailSlots tailAccepted]
            rfl
    | symbol name => simp [flatVariables?] at acceptedCons
    | «string» value => simp [flatVariables?] at acceptedCons
    | integer value => simp [flatVariables?] at acceptedCons
    | application head nested => simp [flatVariables?] at acceptedCons

/-- Compiling and executing a flat head preserves the complete exact
typed-plan value. -/
theorem execute_eq_instantiateTerm_of_compile?
    (substitution : Substitution) (source : Term) (compiled : FlatHead)
    (accepted : compile? source = some compiled) :
    execute substitution compiled = instantiateTerm substitution source := by
  cases source with
  | application head arguments =>
      cases slotsAccepted : flatVariables? arguments with
      | none => simp [compile?, slotsAccepted] at accepted
      | some slots =>
          simp [compile?, slotsAccepted] at accepted
          subst compiled
          simp only [execute, instantiateTerm, Option.bind_eq_bind]
          rw [instantiateTerms_eq_instantiateSlots_of_flatVariables?
            substitution arguments slots slotsAccepted]
  | symbol name => simp [compile?] at accepted
  | «variable» slot => simp [compile?] at accepted
  | «string» value => simp [compile?] at accepted
  | integer value => simp [compile?] at accepted

structure AdmittedFlatHead where
  source : Term
  compiled : FlatHead
  compile_eq : compile? source = some compiled

def admit? (source : Term) : Option AdmittedFlatHead :=
  match accepted : compile? source with
  | none => none
  | some compiled => some { source, compiled, compile_eq := accepted }

/-- Flat positional lowering as a composable realization of exact plan-term
semantics. -/
def flatHeadRealization :
    Mettapedia.GSLT.SimpleRealization
      AdmittedFlatHead FlatHead (Substitution -> Option GroundTerm) where
  compile := fun _ source => source.compiled
  observeSource := fun _ source substitution =>
    instantiateTerm substitution source.source
  observeArtifact := fun _ compiled substitution =>
    execute substitution compiled
  adequate := by
    intro _ source
    funext substitution
    exact execute_eq_instantiateTerm_of_compile?
      substitution source.source source.compiled source.compile_eq

/-! ## Work accounting -/

/-- The generic route constructs one redundant outer application before it is
immediately decomposed. -/
def sourceOuterApplications (_ : AdmittedFlatHead) : Nat := 1

/-- The positional route consumes arguments without that construction. -/
def compiledOuterApplications (_ : AdmittedFlatHead) : Nat := 0

theorem compiledOuterApplications_lt_source (source : AdmittedFlatHead) :
    compiledOuterApplications source < sourceOuterApplications source := by
  simp [compiledOuterApplications, sourceOuterApplications]

/-! ## Independent witnesses and rejection boundaries -/

private def fourSlotHead : Term :=
  .application [1]
    (.cons (.variable 0)
      (.cons (.variable 1)
        (.cons (.variable 2) (.cons (.variable 3) .nil))))

/-- A wide positional head compiles to its exact dense slot inventory. -/
example : compile? fourSlotHead = some {
    head := [1], slots := [0, 1, 2, 3] } := by
  decide

/-- Repeated slots remain repeated. -/
example : compile?
    (.application [2]
      (.cons (.variable 0) (.cons (.variable 0) .nil))) =
      some { head := [2], slots := [0, 0] } := by
  decide

/-- Rigid or nested immediate arguments fail this optional recognizer. -/
example : (compile?
    (.application [3]
      (.cons (.application [4] (.cons (.variable 0) .nil)) .nil))).isSome =
      false := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanFlatHeadCompilation
