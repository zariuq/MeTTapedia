import Mettapedia.Languages.MeTTa.HE.HumanTypeSpec

/-!
# Named runtime refinements of the published human type layer

`HumanTypeSpec` remains the literal published core.  This module separates two
behaviors implemented by Hyperon runtimes where the published
pseudocode leaves the type service underspecified:

* R1: infer the result type of a function application;
* R2: treat `%Undefined%` as a wildcard recursively inside reduced types.

The refinements are named independently so conformance theorems can enumerate
their exact delta instead of silently broadening the published relation.  R2
is stated first; R1 uses the observation language introduced at the end.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypeSpec
open HumanMatchMergeSpec

/-! ## Observation language shared by R1 and R2 -/

/-- Homomorphic application of a type-variable valuation. -/
def applyTypeValuation (valuation : String → Atom) : Atom → Atom
  | .symbol name => .symbol name
  | .var name => valuation name
  | .grounded value => .grounded value
  | .expression atoms => .expression (atoms.map (applyTypeValuation valuation))

/-- A valuation satisfies every assignment and equality carried by a human
binding record. -/
def HumanTypeBindingSatisfied
    (valuation : String → Atom) (bindings : Bindings) : Prop :=
  (∀ name value, (name, value) ∈ bindings.assignments →
      valuation name = applyTypeValuation valuation value) ∧
    (∀ left right, (left, right) ∈ bindings.equalities →
      valuation left = valuation right)

/-! ## R2: recursive `%Undefined%` consistency -/

mutual

/-- Reduced-type consistency.  `%Undefined%` is a wildcard at every depth;
`Atom` is an ordinary symbol here and is special only at the outer
`match_types` boundary. -/
def ReducedTypeConsistent (valuation : String → Atom) : Atom → Atom → Prop
  | .symbol "%Undefined%", _ => True
  | _, .symbol "%Undefined%" => True
  | .symbol left, .symbol right => left = right
  | .var left, .var right => valuation left = valuation right
  | .var left, right => valuation left = applyTypeValuation valuation right
  | left, .var right => applyTypeValuation valuation left = valuation right
  | .grounded left, .grounded right => left = right
  | .expression left, .expression right =>
      ReducedTypeListConsistent valuation left right
  | _, _ => False

/-- Pointwise companion of `ReducedTypeConsistent`; unequal arities are
inconsistent. -/
def ReducedTypeListConsistent (valuation : String → Atom) :
    List Atom → List Atom → Prop
  | [], [] => True
  | left :: lefts, right :: rights =>
      ReducedTypeConsistent valuation left right ∧
        ReducedTypeListConsistent valuation lefts rights
  | _, _ => False

end

/-- R2 matching is stated observationally: the output binding record presents
exactly the incoming binding theory conjoined with recursive reduced-type
consistency.  Explicit satisfiability prevents an inconsistent binding record
from masquerading as a failed match. -/
structure R2ReducedTypeMatchRel
    (left right : Atom) (incoming output : Bindings) : Prop where
  satisfiable : ∃ valuation, HumanTypeBindingSatisfied valuation output
  solutions : ∀ valuation,
    HumanTypeBindingSatisfied valuation output ↔
      HumanTypeBindingSatisfied valuation incoming ∧
        ReducedTypeConsistent valuation left right

/-- Positive R2 example: nested `%Undefined%` accepts `Number`. -/
theorem r2_nested_undefined_number :
    R2ReducedTypeMatchRel
      (.expression [.symbol "List", .symbol "%Undefined%"])
      (.expression [.symbol "List", .symbol "Number"])
      Bindings.empty Bindings.empty := by
  constructor
  · exact ⟨fun name => .var name, by
      simp [HumanTypeBindingSatisfied, Bindings.empty]⟩
  · intro valuation
    simp [HumanTypeBindingSatisfied, Bindings.empty,
      ReducedTypeConsistent, ReducedTypeListConsistent]

/-- Negative R2 example: nested `Atom` is not a wildcard. -/
theorem r2_nested_atom_number_impossible :
    ¬∃ output,
      R2ReducedTypeMatchRel
        (.expression [.symbol "List", .symbol "Atom"])
        (.expression [.symbol "List", .symbol "Number"])
        Bindings.empty output := by
  rintro ⟨output, hmatch⟩
  rcases hmatch.satisfiable with ⟨valuation, hmodel⟩
  have hconsistent := (hmatch.solutions valuation).mp hmodel
  simp [ReducedTypeConsistent, ReducedTypeListConsistent] at hconsistent

/-- Published top-level gradual types together with R2's recursive
consistency.  Nested `Atom` remains ordinary. -/
def CorePlusR2TypeConsistent
    (valuation : String → Atom) (left right : Atom) : Prop :=
  left = Atom.undefinedType ∨ right = Atom.undefinedType ∨
    left = Atom.atomType ∨ right = Atom.atomType ∨
      ReducedTypeConsistent valuation left right

/-- Observational binding result of published top-level type matching plus the
named R2 recursive-consistency delta. -/
structure CorePlusR2TypeMatchRel
    (left right : Atom) (incoming output : Bindings) : Prop where
  satisfiable : ∃ valuation, HumanTypeBindingSatisfied valuation output
  solutions : ∀ valuation,
    HumanTypeBindingSatisfied valuation output ↔
      HumanTypeBindingSatisfied valuation incoming ∧
        CorePlusR2TypeConsistent valuation left right

/-! ## R1: application-result inference -/

/-- The inferred return atom is observed through every model of the type
bindings accumulated while checking the arguments.  This keeps internal type
variable presentation observational rather than imposing a convenience
quotient. -/
def R1ReturnTypeObserved
    (bindings : Bindings) (declared observed : Atom) : Prop :=
  (∃ valuation, HumanTypeBindingSatisfied valuation bindings) ∧
    ∀ valuation,
      HumanTypeBindingSatisfied valuation bindings →
        applyTypeValuation valuation declared =
          applyTypeValuation valuation observed

/-! ## α-variants of schematic annotation types -/

/-- Rename every type-variable leaf by a total name function. -/
def renameHumanTypeVars (ρ : String → String) : Atom → Atom
  | .symbol name => .symbol name
  | .var name => .var (ρ name)
  | .grounded value => .grounded value
  | .expression atoms => .expression (atoms.map (renameHumanTypeVars ρ))

/-- An α-variant presentation of a schematic annotation type: an injective
whole-scheme renaming of its type variables.  Injectivity keeps the variant
exactly as general as the original — a collapsing map would strengthen the
scheme and is excluded. -/
def TypeVariableRenamingOf (type type' : Atom) : Prop :=
  ∃ ρ : String → String, Function.Injective ρ ∧
    type' = renameHumanTypeVars ρ type

private theorem renameHumanTypeVars_id :
    ∀ type : Atom, renameHumanTypeVars id type = type := by
  intro type
  induction type using Atom.rec (motive_2 := fun atoms =>
    atoms.map (renameHumanTypeVars id) = atoms) with
  | symbol name => simp [renameHumanTypeVars]
  | var name => simp [renameHumanTypeVars]
  | grounded value => simp [renameHumanTypeVars]
  | expression atoms ih => simp [renameHumanTypeVars, ih]
  | nil => rfl
  | cons atom atoms ihAtom ihAtoms => simp [ihAtom, ihAtoms]

/-- Every type is an α-variant of itself. -/
@[refl] theorem TypeVariableRenamingOf.refl (type : Atom) :
    TypeVariableRenamingOf type type :=
  ⟨id, Function.injective_id, (renameHumanTypeVars_id type).symm⟩

mutual

/-- Type evidence available to the named refinement layer: one published-core
type, one explicitly witnessed R1 application result, or one explicitly
witnessed R3 state-wrapper result. -/
inductive RuntimeTypeEvidenceRel (space : Space) : Atom → Atom → Prop where
  | published {atom type : Atom} :
      TypeOfRel space atom type →
      RuntimeTypeEvidenceRel space atom type
  | application {expression inferredType : Atom} :
      R1ApplicationResultRel space expression inferredType →
      RuntimeTypeEvidenceRel space expression inferredType
  | stateValue {expression inferredType : Atom} :
      R3StateValueTypeRel space expression inferredType →
      RuntimeTypeEvidenceRel space expression inferredType

/-- R1 argument checking chooses one available actual type at each position
and threads the observational binding theory produced by core-plus-R2 type
matching.

Argument evidence is consumed **up to α-variance of the scheme**: annotation
type variables are schematic binders, so the matched actual type may be any
injective whole-scheme renaming of an evidenced type.  This is
positive-evidence closure at the consumption point only — it does not claim
the raw runtime `getTypes` emits arbitrary variants; exact candidate-set
semantics (and every negative premise over candidates) live in the
presentation-exact lane.  Its runtime witness is repair #7: capture-avoiding
freshening is the executable shadow of this rule, and the repair's canary
pair are its concrete instances. -/
inductive RuntimeArgumentsApplicableRel (space : Space) :
    List Atom → List Atom → Bindings → Bindings → Prop where
  | nil (bindings : Bindings) :
      RuntimeArgumentsApplicableRel space [] [] bindings bindings
  | cons {argument expectedType actualBase actualType : Atom}
      {arguments expectedTypes : List Atom}
      {incoming next output : Bindings} :
      RuntimeTypeEvidenceRel space argument actualBase →
      TypeVariableRenamingOf actualBase actualType →
      CorePlusR2TypeMatchRel expectedType actualType incoming next →
      RuntimeArgumentsApplicableRel space arguments expectedTypes next output →
      RuntimeArgumentsApplicableRel space
        (argument :: arguments) (expectedType :: expectedTypes)
        incoming output

/-- R1 application-result inference.  The function type and every argument
type are explicit derivation evidence; the inferred return is compared only
through the accumulated type-binding theory. -/
inductive R1ApplicationResultRel (space : Space) : Atom → Atom → Prop where
  | mk {expression inferredType operator functionBase functionType
        declaredReturnType : Atom}
      {arguments argumentTypes : List Atom} {typeBindings : Bindings} :
      expression = .expression (operator :: arguments) →
      RuntimeTypeEvidenceRel space operator functionBase →
      TypeVariableRenamingOf functionBase functionType →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      RuntimeArgumentsApplicableRel space arguments argumentTypes
        Bindings.empty typeBindings →
      R1ReturnTypeObserved typeBindings declaredReturnType inferredType →
      R1ApplicationResultRel space expression inferredType

/-- R3 exposes LeaTTa's state-handle representation rule exactly at the
syntax where the runtime applies it.  It is intentionally unrestricted:
source-level `(StateValue value)` expressions receive the same synthesized
type as wrappers produced internally by state resolution.  This records the
current representation leak rather than hiding it behind a reachability
premise.  A future migration to unforgeable grounded state handles can remove
this refinement and align the representation directly with Hyperon. -/
inductive R3StateValueTypeRel (space : Space) : Atom → Atom → Prop where
  | mk {value contentType : Atom} :
      RuntimeTypeEvidenceRel space value contentType →
      R3StateValueTypeRel space
        (.expression [.symbol "StateValue", value])
        (.expression [.symbol "StateMonad", contentType])

end

/-! ## Runtime applicability (published core plus named R1/R2/R3 deltas) -/

/-- One complete successful applicability path using the explicitly named
runtime type-evidence and recursive reduced-type matching refinements.  The
published `ApplicationSuccessRel` remains unchanged in `HumanTypeSpec`. -/
inductive RuntimeApplicationSuccessRel (space : Space) :
    Atom → Atom → Atom → Bindings → Bindings → Prop where
  | mk {expression functionType expectedType operator returnType : Atom}
      {arguments argumentTypes : List Atom}
      {bindings afterArguments output : Bindings} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      RuntimeArgumentsApplicableRel space arguments argumentTypes
        bindings afterArguments →
      CorePlusR2TypeMatchRel expectedType returnType afterArguments output →
      RuntimeApplicationSuccessRel space expression functionType expectedType
        bindings output

/-- Named refinement of published function applicability.  This relation
changes only the type-evidence and type-matching premises: R1/R3 may supply
runtime-only types, and R2 may match `%Undefined%` recursively.  Its outcomes
and first-failure shapes remain those of the published relation. -/
inductive RuntimeApplicabilityRel (space : Space) :
    Atom → Atom → Atom → Bindings → ApplicabilityOutcome → Prop where
  | success {expression functionType expectedType : Atom}
      {bindings output : Bindings} :
      RuntimeApplicationSuccessRel space expression functionType expectedType
        bindings output →
      RuntimeApplicabilityRel space expression functionType expectedType
        bindings (.success output)
  | wrongArity {expression functionType expectedType operator returnType : Atom}
      {arguments argumentTypes : List Atom} {bindings : Bindings} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      arguments.length ≠ argumentTypes.length →
      RuntimeApplicabilityRel space expression functionType expectedType
        bindings (.error (mkError expression .incorrectNumberOfArguments))
  | badArgument {expression functionType expectedType operator returnType : Atom}
      {argumentsBefore argumentsAfter : List Atom}
      {typesBefore typesAfter : List Atom}
      {badArgument expectedArgument actualType : Atom}
      {bindings beforeBad : Bindings} :
      expression = .expression
        (operator :: (argumentsBefore ++ badArgument :: argumentsAfter)) →
      FunctionTypeRel functionType
        (typesBefore ++ expectedArgument :: typesAfter) returnType →
      argumentsAfter.length = typesAfter.length →
      RuntimeArgumentsApplicableRel space argumentsBefore typesBefore
        bindings beforeBad →
      RuntimeTypeEvidenceRel space badArgument actualType →
      (∀ candidate,
        ¬CorePlusR2TypeMatchRel expectedArgument actualType beforeBad candidate) →
      (∀ output,
        ¬RuntimeApplicationSuccessRel space expression functionType expectedType
          bindings output) →
      RuntimeApplicabilityRel space expression functionType expectedType
        bindings (.error (mkError expression
          (.badArgType argumentsBefore.length expectedArgument actualType)))
  | badReturn {expression functionType expectedType operator returnType : Atom}
      {arguments argumentTypes : List Atom}
      {bindings afterArguments : Bindings} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      RuntimeArgumentsApplicableRel space arguments argumentTypes
        bindings afterArguments →
      (∀ candidate,
        ¬CorePlusR2TypeMatchRel expectedType returnType afterArguments candidate) →
      (∀ output,
        ¬RuntimeApplicationSuccessRel space expression functionType expectedType
          bindings output) →
      RuntimeApplicabilityRel space expression functionType expectedType
        bindings (.error (mkError expression (.badType expectedType returnType)))

/-! ## Constraint-carrying type packages -/

/-- A satisfiable, presentation-free type constraint theory.  Private type
variables live only in this semantic predicate; they never leak into the
evaluator's ordinary binding state. -/
structure RuntimeTypeTheory where
  Holds : (String → Atom) → Prop
  satisfiable : ∃ valuation, Holds valuation

/-- The unconstrained theory used by published literal types. -/
def RuntimeTypeTheory.empty : RuntimeTypeTheory where
  Holds := fun _ => True
  satisfiable := ⟨fun name => .var name, trivial⟩

/-- A type candidate together with the private theory under which its term is
meaningful.  Inferred types must travel as this package: projecting the term
alone loses exactly the constraints pinned by
`r1_observation_not_match_invariant_canary` below. -/
structure RuntimeTypePackage where
  theory : RuntimeTypeTheory
  term : Atom

/-- A published type has no private inference constraints. -/
def RuntimeTypePackage.published (type : Atom) : RuntimeTypePackage :=
  ⟨RuntimeTypeTheory.empty, type⟩

/-- One model of a packaged type's carried theory. -/
def RuntimeTypePackage.Satisfied
    (valuation : String → Atom) (package : RuntimeTypePackage) : Prop :=
  package.theory.Holds valuation

/-- The package presents one observed type without discarding its theory. -/
def RuntimeTypePackage.Observes
    (package : RuntimeTypePackage) (observed : Atom) : Prop :=
  ∀ valuation,
    package.Satisfied valuation →
      applyTypeValuation valuation package.term =
        applyTypeValuation valuation observed

/-- Type matching consumes a candidate package conjunctively.  The output is
another private type theory; it never becomes an evaluator binding record. -/
structure PackagedTypeMatchRel
    (expected : Atom) (actual : RuntimeTypePackage)
    (incoming output : RuntimeTypeTheory) : Prop where
  solutions : ∀ valuation,
    output.Holds valuation ↔
      incoming.Holds valuation ∧
        actual.Satisfied valuation ∧
          CorePlusR2TypeConsistent valuation expected actual.term

/-- A function skeleton observed under the package's carried theory.  The
skeleton is explicit evidence, so an inferred variable may be used as a
function only when its theory forces an arrow shape. -/
def PackagedFunctionTypeRel
    (package : RuntimeTypePackage) (argumentTypes : List Atom)
    (returnType : Atom) : Prop :=
  package.Observes
    (.expression (.symbol "->" :: (argumentTypes ++ [returnType])))

/-- The number of arguments in a packaged function type is well-defined even
when its leaves are presented observationally. -/
theorem PackagedFunctionTypeRel.argument_length_unique
    {package : RuntimeTypePackage}
    {leftArguments rightArguments : List Atom}
    {leftReturn rightReturn : Atom}
    (hleft : PackagedFunctionTypeRel package leftArguments leftReturn)
    (hright : PackagedFunctionTypeRel package rightArguments rightReturn) :
    leftArguments.length = rightArguments.length := by
  rcases package.theory.satisfiable with ⟨valuation, hmodel⟩
  have hleftEq := hleft valuation hmodel
  have hrightEq := hright valuation hmodel
  have harrows := hleftEq.symm.trans hrightEq
  simp only [applyTypeValuation, List.map_append, List.map_cons] at harrows
  have hlists := Atom.expression.inj harrows
  have hlengths := congrArg List.length hlists
  simp at hlengths
  omega

/-- An `A`-constrained inferred variable cannot later be rebound to `B` once
its binding theory is consumed as part of the match. -/
theorem packaged_match_preserves_inference_constraints
    (package : RuntimeTypePackage)
    (htheory : ∀ valuation,
      package.Satisfied valuation → valuation "t" = .symbol "A")
    (hterm : package.term = .var "t") :
    ¬∃ output,
      PackagedTypeMatchRel (.symbol "B") package
        RuntimeTypeTheory.empty output := by
  rintro ⟨output, hmatch⟩
  rcases output.satisfiable with ⟨valuation, hmodel⟩
  have hall := (hmatch.solutions valuation).mp hmodel
  have hpackage := htheory valuation hall.2.1
  have hconsistent := hall.2.2
  rw [hterm] at hconsistent
  simp [CorePlusR2TypeConsistent, ReducedTypeConsistent,
    Atom.undefinedType, Atom.atomType, applyTypeValuation,
    hpackage] at hconsistent

mutual

/-- Positive type evidence in its compositional form: every inferred term
retains the binding theory that gives it meaning.  Exact runtime precedence is
layered separately below; this relation is only the package-producing core. -/
inductive PackagedRuntimeTypeEvidenceRel (space : Space) :
    Atom → RuntimeTypePackage → Prop where
  | published {atom type : Atom} :
      TypeOfRel space atom type →
      PackagedRuntimeTypeEvidenceRel space atom
        (RuntimeTypePackage.published type)
  | application {expression : Atom} {package : RuntimeTypePackage} :
      R1ApplicationPackageRel space expression package →
      PackagedRuntimeTypeEvidenceRel space expression package
  | stateValue {expression : Atom} {package : RuntimeTypePackage} :
      R3StateValuePackageRel space expression package →
      PackagedRuntimeTypeEvidenceRel space expression package

/-- Left-to-right argument checking over type packages.  Each actual
candidate's private theory is conjoined by `PackagedTypeMatchRel` before the
next position is checked. -/
inductive PackagedRuntimeArgumentsApplicableRel (space : Space) :
    List Atom → List Atom → RuntimeTypeTheory → RuntimeTypeTheory → Prop where
  | nil (bindings : RuntimeTypeTheory) :
      PackagedRuntimeArgumentsApplicableRel space [] [] bindings bindings
  | cons {argument expectedType : Atom} {actual : RuntimeTypePackage}
      {arguments expectedTypes : List Atom}
      {incoming next output : RuntimeTypeTheory} :
      PackagedRuntimeTypeEvidenceRel space argument actual →
      PackagedTypeMatchRel expectedType actual incoming next →
      PackagedRuntimeArgumentsApplicableRel space arguments expectedTypes
        next output →
      PackagedRuntimeArgumentsApplicableRel space
        (argument :: arguments) (expectedType :: expectedTypes)
        incoming output

/-- R1 inference before choosing a concrete presentation: the result is the
declared return term paired with every constraint accumulated while observing
the operator's function skeleton and checking its arguments. -/
inductive R1ApplicationPackageRel (space : Space) :
    Atom → RuntimeTypePackage → Prop where
  | mk {expression operator declaredReturnType : Atom}
      {arguments argumentTypes : List Atom}
      {operatorPackage : RuntimeTypePackage}
      {typeTheory : RuntimeTypeTheory} :
      expression = .expression (operator :: arguments) →
      PackagedRuntimeTypeEvidenceRel space operator operatorPackage →
      PackagedFunctionTypeRel operatorPackage argumentTypes declaredReturnType →
      PackagedRuntimeArgumentsApplicableRel space arguments argumentTypes
        operatorPackage.theory typeTheory →
      R1ApplicationPackageRel space expression
        ⟨typeTheory, declaredReturnType⟩

/-- R3 preserves the content candidate's binding theory while wrapping its
term in the state-monad type constructor. -/
inductive R3StateValuePackageRel (space : Space) :
    Atom → RuntimeTypePackage → Prop where
  | mk {value : Atom} {content : RuntimeTypePackage} :
      PackagedRuntimeTypeEvidenceRel space value content →
      R3StateValuePackageRel space
        (.expression [.symbol "StateValue", value])
        ⟨content.theory,
          .expression [.symbol "StateMonad", content.term]⟩

end


/-! ## R1 boundary examples -/

private def r1Space : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "f",
      .expression [.symbol "->", .symbol "A", .symbol "B"]],
    .expression [.symbol ":", .symbol "a", .symbol "A"]]

private theorem r1_f_type :
    TypeOfRel r1Space (.symbol "f")
      (.expression [.symbol "->", .symbol "A", .symbol "B"]) := by
  refine ⟨[.expression [.symbol "->", .symbol "A", .symbol "B"]], ?_, by simp⟩
  apply TypesOfRel.symbolKnown
  · exact AnnotationTypesRel.hit
      (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil)
  · simp

private theorem r1_f_runtime_type
    {type : Atom}
    (h : RuntimeTypeEvidenceRel r1Space (.symbol "f") type) :
    type = .expression [.symbol "->", .symbol "A", .symbol "B"] := by
  cases h with
  | published htype =>
      rcases htype with ⟨types, htypes, hmem⟩
      cases htypes with
      | symbolKnown hannotations _ =>
          have hexpected : AnnotationTypesRel (.symbol "f") r1Space.atoms
              [.expression [.symbol "->", .symbol "A", .symbol "B"]] :=
            AnnotationTypesRel.hit
              (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil)
          have htypesEq := AnnotationTypesRel.unique hannotations hexpected
          subst types
          simpa using hmem
      | symbolUndefined hannotations =>
          have hexpected : AnnotationTypesRel (.symbol "f") r1Space.atoms
              [.expression [.symbol "->", .symbol "A", .symbol "B"]] :=
            AnnotationTypesRel.hit
              (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil)
          have hfalse := AnnotationTypesRel.unique hannotations hexpected
          simp at hfalse
  | application happ =>
      cases happ with
      | mk hshape => simp at hshape
  | stateValue hstate =>
      cases hstate

private theorem r1_a_type :
    TypeOfRel r1Space (.symbol "a") (.symbol "A") := by
  refine ⟨[.symbol "A"], ?_, by simp⟩
  apply TypesOfRel.symbolKnown
  · exact AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.hit AnnotationTypesRel.nil)
  · simp

private theorem corePlusR2_A_A :
    CorePlusR2TypeMatchRel (.symbol "A") (.symbol "A")
      Bindings.empty Bindings.empty := by
  constructor
  · exact ⟨fun name => .var name, by
      simp [HumanTypeBindingSatisfied, Bindings.empty]⟩
  · intro valuation
    simp [HumanTypeBindingSatisfied, Bindings.empty,
      CorePlusR2TypeConsistent, ReducedTypeConsistent,
      Atom.undefinedType, Atom.atomType]

private theorem r1_B_observed :
    R1ReturnTypeObserved Bindings.empty (.symbol "B") (.symbol "B") := by
  constructor
  · exact ⟨fun name => .var name, by
      simp [HumanTypeBindingSatisfied, Bindings.empty]⟩
  · intro valuation _
    rfl

/-- Positive R1 example: `f : (-> A B)` applied to `a : A` has inferred
result type `B`. -/
theorem r1_f_a_infers_B :
    R1ApplicationResultRel r1Space
      (.expression [.symbol "f", .symbol "a"]) (.symbol "B") := by
  apply R1ApplicationResultRel.mk
      (operator := .symbol "f")
      (arguments := [.symbol "a"])
      (functionType := .expression [.symbol "->", .symbol "A", .symbol "B"])
      (argumentTypes := [.symbol "A"])
      (declaredReturnType := .symbol "B")
      (typeBindings := Bindings.empty)
  · rfl
  · exact RuntimeTypeEvidenceRel.published r1_f_type
  · rfl
  · rfl
  · exact RuntimeArgumentsApplicableRel.cons
      (RuntimeTypeEvidenceRel.published r1_a_type)
      (TypeVariableRenamingOf.refl _)
      corePlusR2_A_A
      (RuntimeArgumentsApplicableRel.nil Bindings.empty)
  · exact r1_B_observed

/-- Negative R1 example: a nullary expression cannot use a function type that
requires one argument. -/
theorem r1_nullary_f_does_not_infer_B :
    ¬R1ApplicationResultRel r1Space
      (.expression [.symbol "f"]) (.symbol "B") := by
  intro hinfer
  cases hinfer with
  | mk hshape hoperator hrenaming hfunction harguments _ =>
      simp at hshape
      rcases hshape with ⟨rfl, rfl⟩
      cases harguments
      have hbase := r1_f_runtime_type hoperator
      subst hbase
      obtain ⟨ρ, _, rfl⟩ := hrenaming
      simp [renameHumanTypeVars, FunctionTypeRel] at hfunction

/-! ## Parametric R1 canaries -/

private def r1ParametricSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "id",
      .expression [.symbol "->", .var "t", .var "t"]],
    .expression [.symbol ":", .symbol "a", .symbol "A"]]

private def r1TBinding : Bindings :=
  Bindings.empty.assign "t" (.symbol "A")

private theorem r1TBinding_satisfied_iff (valuation : String → Atom) :
    HumanTypeBindingSatisfied valuation r1TBinding ↔
      valuation "t" = .symbol "A" := by
  simp [r1TBinding, HumanTypeBindingSatisfied, Bindings.empty,
    Bindings.assign, Bindings.isBound, Bindings.lookup,
    applyTypeValuation]

private theorem r1_id_type :
    TypeOfRel r1ParametricSpace (.symbol "id")
      (.expression [.symbol "->", .var "t", .var "t"]) := by
  refine ⟨[.expression [.symbol "->", .var "t", .var "t"]], ?_, by simp⟩
  apply TypesOfRel.symbolKnown
  · exact AnnotationTypesRel.hit
      (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil)
  · simp

private theorem r1_parametric_a_type :
    TypeOfRel r1ParametricSpace (.symbol "a") (.symbol "A") := by
  refine ⟨[.symbol "A"], ?_, by simp⟩
  apply TypesOfRel.symbolKnown
  · exact AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.hit AnnotationTypesRel.nil)
  · simp

private theorem corePlusR2_t_A :
    CorePlusR2TypeMatchRel (.var "t") (.symbol "A")
      Bindings.empty r1TBinding := by
  constructor
  · refine ⟨fun name => if name = "t" then .symbol "A" else .var name, ?_⟩
    rw [r1TBinding_satisfied_iff]
    simp
  · intro valuation
    rw [r1TBinding_satisfied_iff]
    simp [HumanTypeBindingSatisfied, Bindings.empty,
      CorePlusR2TypeConsistent, ReducedTypeConsistent,
      Atom.undefinedType, Atom.atomType, applyTypeValuation]

private theorem r1_t_observed_as_A :
    R1ReturnTypeObserved r1TBinding (.var "t") (.symbol "A") := by
  constructor
  · refine ⟨fun name => if name = "t" then .symbol "A" else .var name, ?_⟩
    rw [r1TBinding_satisfied_iff]
    simp
  · intro valuation hmodel
    simpa [applyTypeValuation] using r1TBinding_satisfied_iff valuation |>.mp hmodel

/-- Positive parametric R1 example: argument matching binds `$t` to `A`, so
`id : (-> $t $t)` applied to `a : A` has observed result type `A`. -/
theorem r1_id_a_infers_A :
    R1ApplicationResultRel r1ParametricSpace
      (.expression [.symbol "id", .symbol "a"]) (.symbol "A") := by
  apply R1ApplicationResultRel.mk
      (operator := .symbol "id")
      (arguments := [.symbol "a"])
      (functionType := .expression [.symbol "->", .var "t", .var "t"])
      (argumentTypes := [.var "t"])
      (declaredReturnType := .var "t")
      (typeBindings := r1TBinding)
  · rfl
  · exact RuntimeTypeEvidenceRel.published r1_id_type
  · rfl
  · rfl
  · exact RuntimeArgumentsApplicableRel.cons
      (RuntimeTypeEvidenceRel.published r1_parametric_a_type)
      (TypeVariableRenamingOf.refl _)
      corePlusR2_t_A
      (RuntimeArgumentsApplicableRel.nil r1TBinding)
  · exact r1_t_observed_as_A

/-- Negative observation canary: the same binding theory cannot present the
parametric return as unrelated type `B`. -/
theorem r1_t_not_observed_as_B :
    ¬R1ReturnTypeObserved r1TBinding (.var "t") (.symbol "B") := by
  rintro ⟨_, hall⟩
  let valuation : String → Atom :=
    fun name => if name = "t" then .symbol "A" else .var name
  have hmodel : HumanTypeBindingSatisfied valuation r1TBinding := by
    rw [r1TBinding_satisfied_iff]
    simp [valuation]
  have hEq := hall valuation hmodel
  simp [valuation, applyTypeValuation] at hEq

/-- The deliberately observational R1 boundary also admits the declared
variable itself as a presentation of its constrained value.  This is valid
as an observation, but the binding theory must not be discarded before a
later type match consumes the presentation. -/
theorem r1_id_a_observes_uninstantiated_t :
    R1ApplicationResultRel r1ParametricSpace
      (.expression [.symbol "id", .symbol "a"]) (.var "t") := by
  apply R1ApplicationResultRel.mk
      (operator := .symbol "id")
      (arguments := [.symbol "a"])
      (functionType := .expression [.symbol "->", .var "t", .var "t"])
      (argumentTypes := [.var "t"])
      (declaredReturnType := .var "t")
      (typeBindings := r1TBinding)
  · rfl
  · exact RuntimeTypeEvidenceRel.published r1_id_type
  · rfl
  · rfl
  · exact RuntimeArgumentsApplicableRel.cons
      (RuntimeTypeEvidenceRel.published r1_parametric_a_type)
      (TypeVariableRenamingOf.refl _)
      corePlusR2_t_A
      (RuntimeArgumentsApplicableRel.nil r1TBinding)
  · constructor
    · refine ⟨fun name => if name = "t" then .symbol "A" else .var name, ?_⟩
      rw [r1TBinding_satisfied_iff]
      simp
    · intro valuation _
      rfl

private def r1IdOperatorPackage : RuntimeTypePackage :=
  RuntimeTypePackage.published
    (.expression [.symbol "->", .var "t", .var "t"])

private def r1AArgumentPackage : RuntimeTypePackage :=
  RuntimeTypePackage.published (.symbol "A")

private def r1ATheory : RuntimeTypeTheory where
  Holds := fun valuation => valuation "t" = .symbol "A"
  satisfiable :=
    ⟨fun name => if name = "t" then .symbol "A" else .var name, by simp⟩

private def r1IdResultPackage : RuntimeTypePackage :=
  ⟨r1ATheory, .var "t"⟩

private theorem r1_id_operator_package_evidence :
    PackagedRuntimeTypeEvidenceRel r1ParametricSpace
      (.symbol "id") r1IdOperatorPackage := by
  exact PackagedRuntimeTypeEvidenceRel.published r1_id_type

private theorem r1_id_operator_function_package :
    PackagedFunctionTypeRel r1IdOperatorPackage [.var "t"] (.var "t") := by
  intro valuation _
  rfl

private theorem r1_a_package_evidence :
    PackagedRuntimeTypeEvidenceRel r1ParametricSpace
      (.symbol "a") r1AArgumentPackage := by
  exact PackagedRuntimeTypeEvidenceRel.published r1_parametric_a_type

private theorem packaged_t_A :
    PackagedTypeMatchRel (.var "t") r1AArgumentPackage
      RuntimeTypeTheory.empty r1ATheory := by
  constructor
  intro valuation
  simp [r1ATheory, r1AArgumentPackage, RuntimeTypePackage.published,
      RuntimeTypeTheory.empty, RuntimeTypePackage.Satisfied,
      CorePlusR2TypeConsistent,
      ReducedTypeConsistent, Atom.undefinedType, Atom.atomType,
      applyTypeValuation]

/-- Positive package witness for parametric R1 inference.  The return remains
the declared `$t`, but its `t = A` theory is retained in the result package. -/
theorem r1_id_a_infers_constraint_package :
    R1ApplicationPackageRel r1ParametricSpace
      (.expression [.symbol "id", .symbol "a"]) r1IdResultPackage := by
  change R1ApplicationPackageRel r1ParametricSpace
    (.expression [.symbol "id", .symbol "a"])
    ⟨r1ATheory, .var "t"⟩
  apply R1ApplicationPackageRel.mk
      (operator := .symbol "id")
      (arguments := [.symbol "a"])
      (argumentTypes := [.var "t"])
      (operatorPackage := r1IdOperatorPackage)
      (typeTheory := r1ATheory)
  · rfl
  · exact r1_id_operator_package_evidence
  · exact r1_id_operator_function_package
  · exact PackagedRuntimeArgumentsApplicableRel.cons
      r1_a_package_evidence packaged_t_A
      (PackagedRuntimeArgumentsApplicableRel.nil r1ATheory)

/-- Negative package canary: the retained `t = A` theory blocks a later
attempt to consume the inferred result as unrelated `B`. -/
theorem r1_id_a_constraint_package_rejects_B :
    ¬∃ output,
      PackagedTypeMatchRel (.symbol "B") r1IdResultPackage
        RuntimeTypeTheory.empty output := by
  apply packaged_match_preserves_inference_constraints r1IdResultPackage
  · intro valuation hmodel
    exact hmodel
  · rfl

private def r1TBindingB : Bindings :=
  Bindings.empty.assign "t" (.symbol "B")

private theorem r1TBindingB_satisfied_iff (valuation : String → Atom) :
    HumanTypeBindingSatisfied valuation r1TBindingB ↔
      valuation "t" = .symbol "B" := by
  simp [r1TBindingB, HumanTypeBindingSatisfied, Bindings.empty,
    Bindings.assign, Bindings.isBound, Bindings.lookup,
    applyTypeValuation]

private theorem B_matches_uninstantiated_t :
    CorePlusR2TypeMatchRel (.symbol "B") (.var "t")
      Bindings.empty r1TBindingB := by
  constructor
  · refine ⟨fun name => if name = "t" then .symbol "B" else .var name, ?_⟩
    rw [r1TBindingB_satisfied_iff]
    simp
  · intro valuation
    rw [r1TBindingB_satisfied_iff]
    simp [HumanTypeBindingSatisfied, Bindings.empty,
      CorePlusR2TypeConsistent, ReducedTypeConsistent,
      Atom.undefinedType, Atom.atomType, applyTypeValuation]
    constructor <;> intro h <;> exact h.symm

private theorem B_does_not_match_A :
    ¬∃ output,
      CorePlusR2TypeMatchRel (.symbol "B") (.symbol "A")
        Bindings.empty output := by
  rintro ⟨output, hmatch⟩
  rcases hmatch.satisfiable with ⟨valuation, hmodel⟩
  have hconsistent := (hmatch.solutions valuation).mp hmodel
  simp [HumanTypeBindingSatisfied, Bindings.empty,
    CorePlusR2TypeConsistent, ReducedTypeConsistent,
    Atom.undefinedType, Atom.atomType] at hconsistent

/-- Precision canary: R1's observation relation is not invariant under later
type matching if its internal binding theory is discarded.  The same inferred
return observes both concrete `A` and raw `$t`; only the latter can then be
rebound to unrelated `B`. -/
theorem r1_observation_not_match_invariant_canary :
    R1ApplicationResultRel r1ParametricSpace
        (.expression [.symbol "id", .symbol "a"]) (.symbol "A") ∧
      R1ApplicationResultRel r1ParametricSpace
        (.expression [.symbol "id", .symbol "a"]) (.var "t") ∧
      CorePlusR2TypeMatchRel (.symbol "B") (.var "t")
        Bindings.empty r1TBindingB ∧
      ¬∃ output,
        CorePlusR2TypeMatchRel (.symbol "B") (.symbol "A")
          Bindings.empty output :=
  ⟨r1_id_a_infers_A, r1_id_a_observes_uninstantiated_t,
    B_matches_uninstantiated_t, B_does_not_match_A⟩

/-! ## Runtime-applicability strictness canaries -/

private def runtimeApplicabilitySpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "xs",
      .expression [.symbol "List", .symbol "Number"]]]

private def runtimeListExpected : Atom :=
  .expression [.symbol "List", Atom.undefinedType]

private def runtimeListActual : Atom :=
  .expression [.symbol "List", .symbol "Number"]

private def runtimeFunctionType : Atom :=
  .expression [.symbol "->", runtimeListExpected, .symbol "R"]

private def runtimeCall : Atom :=
  .expression [.symbol "accept-list", .symbol "xs"]

private theorem runtime_xs_type :
    TypeOfRel runtimeApplicabilitySpace (.symbol "xs") runtimeListActual := by
  refine ⟨[runtimeListActual], ?_, by simp⟩
  apply TypesOfRel.symbolKnown
  · exact AnnotationTypesRel.hit AnnotationTypesRel.nil
  · simp

private theorem runtime_xs_type_unique {type : Atom}
    (h : TypeOfRel runtimeApplicabilitySpace (.symbol "xs") type) :
    type = runtimeListActual := by
  rcases h with ⟨types, htypes, hmem⟩
  cases htypes with
  | symbolKnown hannotations _ =>
      have hexpected : AnnotationTypesRel (.symbol "xs")
          runtimeApplicabilitySpace.atoms [runtimeListActual] :=
        AnnotationTypesRel.hit AnnotationTypesRel.nil
      have htypesEq := AnnotationTypesRel.unique hannotations hexpected
      subst types
      simpa using hmem
  | symbolUndefined hannotations =>
      have hexpected : AnnotationTypesRel (.symbol "xs")
          runtimeApplicabilitySpace.atoms [runtimeListActual] :=
        AnnotationTypesRel.hit AnnotationTypesRel.nil
      have hfalse := AnnotationTypesRel.unique hannotations hexpected
      simp at hfalse

private theorem runtimeListExpected_actual_r2 :
    CorePlusR2TypeMatchRel runtimeListExpected runtimeListActual
      Bindings.empty Bindings.empty := by
  constructor
  · exact ⟨fun name => .var name, by
      simp [HumanTypeBindingSatisfied, Bindings.empty]⟩
  · intro valuation
    simp [runtimeListExpected, runtimeListActual,
      HumanTypeBindingSatisfied, Bindings.empty,
      CorePlusR2TypeConsistent, ReducedTypeConsistent,
      ReducedTypeListConsistent, Atom.undefinedType, Atom.atomType]

private theorem runtimeReturn_r2 :
    CorePlusR2TypeMatchRel (.symbol "R") (.symbol "R")
      Bindings.empty Bindings.empty := by
  constructor
  · exact ⟨fun name => .var name, by
      simp [HumanTypeBindingSatisfied, Bindings.empty]⟩
  · intro valuation
    simp [HumanTypeBindingSatisfied, Bindings.empty,
      CorePlusR2TypeConsistent, ReducedTypeConsistent,
      Atom.undefinedType, Atom.atomType]

private theorem runtimeListExpected_actual_not_core
    {incoming output : Bindings} :
    ¬TypeMatchRel runtimeListExpected runtimeListActual incoming output := by
  intro hmatch
  obtain ⟨matched, hhuman, _⟩ := TypeMatchRel.structural_of_nonWildcard
    (by simp [runtimeListExpected, Atom.undefinedType])
    (by simp [runtimeListExpected, Atom.atomType])
    (by simp [runtimeListActual, Atom.undefinedType])
    (by simp [runtimeListActual, Atom.atomType]) hmatch
  cases hhuman with
  | expression hitems _ =>
      cases hitems with
      | cons _ _ htail =>
          cases htail with
          | cons hbad _ _ =>
              exact symbol_mismatch_not_match (by decide) _ hbad

/-- Positive refined applicability: R2 accepts `%Undefined%` recursively in
the declared list element type. -/
theorem runtime_applicability_accepts_nested_undefined :
    RuntimeApplicabilityRel runtimeApplicabilitySpace runtimeCall
      runtimeFunctionType (.symbol "R") Bindings.empty
      (.success Bindings.empty) := by
  apply RuntimeApplicabilityRel.success
  apply RuntimeApplicationSuccessRel.mk
      (operator := .symbol "accept-list")
      (arguments := [.symbol "xs"])
      (argumentTypes := [runtimeListExpected])
      (returnType := .symbol "R")
      (afterArguments := Bindings.empty)
  · rfl
  · rfl
  · exact RuntimeArgumentsApplicableRel.cons
      (RuntimeTypeEvidenceRel.published runtime_xs_type)
      (TypeVariableRenamingOf.refl _)
      runtimeListExpected_actual_r2
      (RuntimeArgumentsApplicableRel.nil Bindings.empty)
  · exact runtimeReturn_r2

/-- Strictness canary: the same application has no published-core successful
applicability derivation, because the core wildcard is top-level only. -/
theorem runtime_applicability_nested_undefined_strict :
    ¬∃ output,
      ApplicationSuccessRel runtimeApplicabilitySpace runtimeCall
        runtimeFunctionType (.symbol "R") Bindings.empty output := by
  rintro ⟨output, hsuccess⟩
  cases hsuccess with
  | mk hshape hfunction harguments hreturn =>
      rename_i operator returnType arguments argumentTypes afterArguments
      change Atom.expression [.symbol "accept-list", .symbol "xs"] =
        Atom.expression (_ :: _) at hshape
      have hargumentsEq : arguments = [.symbol "xs"] := by
        have htail := congrArg List.tail (Atom.expression.inj hshape)
        simpa using htail.symm
      subst arguments
      change Atom.expression
          [.symbol "->", runtimeListExpected, .symbol "R"] =
        Atom.expression
          (.symbol "->" :: (argumentTypes ++ [returnType])) at hfunction
      have hargumentTypesEq : argumentTypes = [runtimeListExpected] := by
        have htail := congrArg List.tail (Atom.expression.inj hfunction)
        have hdrop := congrArg List.dropLast htail
        simpa using hdrop.symm
      subst argumentTypes
      cases harguments with
      | cons htype hmatch _ =>
          have htypeEq := runtime_xs_type_unique htype
          subst_vars
          exact runtimeListExpected_actual_not_core hmatch

end Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement
