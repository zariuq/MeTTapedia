import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge

/-!
# Executable-independent HE type layer

This module gives relational counterparts of the published `get atom types`,
`match_types`, `type_cast`, `check_argument_type`, and
`check_if_function_type_is_applicable` pseudocode.  No constructor mentions an
executable type checker or a fuel budget.

The published type lookup boundary is made concrete using the visible rules in
the specification: direct `(: atom type)` declarations, intrinsic grounded
types, and `%Undefined%` when no type is available.  Declaration lookup scans
the atomspace in order because `type_cast` returns at the first type admitting
a match.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Match.Merge

/-! ## Type lookup -/

/-- Ordered extraction of direct `(: target type)` declarations from an
atomspace list.  This relation is the declarative counterpart of the
specification's request for the list of types of an atom from the space. -/
inductive AnnotationTypesRel (target : Atom) :
    List Atom → List Atom → Prop where
  | nil : AnnotationTypesRel target [] []
  | hit {type : Atom} {tail types : List Atom} :
      AnnotationTypesRel target tail types →
      AnnotationTypesRel target
        (.expression [.symbol ":", target, type] :: tail) (type :: types)
  | skip {head : Atom} {tail types : List Atom} :
      (∀ type, head ≠ .expression [.symbol ":", target, type]) →
      AnnotationTypesRel target tail types →
      AnnotationTypesRel target (head :: tail) types

/-- Ordered annotation extraction is functional. -/
theorem AnnotationTypesRel.unique
    {target : Atom} {atoms left right : List Atom}
    (hleft : AnnotationTypesRel target atoms left)
    (hright : AnnotationTypesRel target atoms right) : left = right := by
  induction hleft generalizing right with
  | nil =>
      cases hright
      rfl
  | hit htail ih =>
      cases hright with
      | hit hright => exact congrArg (List.cons _) (ih hright)
      | skip hskip _ => exact (hskip _ rfl).elim
  | skip hskip htail ih =>
      cases hright with
      | hit _ => exact (hskip _ rfl).elim
      | skip _ hright => exact ih hright

/-- Intrinsic type supplied by a grounded payload. -/
inductive IntrinsicGroundedTypeRel : GroundedValue → Atom → Prop where
  | int (value : Int) :
      IntrinsicGroundedTypeRel (.int value) (.symbol "Number")
  | bool (value : Bool) :
      IntrinsicGroundedTypeRel (.bool value) (.symbol "Bool")
  | string (value : String) :
      IntrinsicGroundedTypeRel (.string value) (.symbol "String")
  | custom (type payload : String) :
      IntrinsicGroundedTypeRel (.custom type payload) (.symbol type)

/-- The complete ordered type list assigned to an atom by the published
visible rules. -/
inductive TypesOfRel : Space → Atom → List Atom → Prop where
  | variable (space : Space) (name : String) :
      TypesOfRel space (.var name) [Atom.undefinedType]
  | groundedKnown {space : Space} {value : GroundedValue} {type : Atom} :
      IntrinsicGroundedTypeRel value type →
      type ≠ Atom.undefinedType →
      TypesOfRel space (.grounded value) [type]
  | groundedUndefined {space : Space} {value : GroundedValue} :
      IntrinsicGroundedTypeRel value Atom.undefinedType →
      TypesOfRel space (.grounded value) [Atom.undefinedType]
  | symbolKnown {space : Space} {name : String} {types : List Atom} :
      AnnotationTypesRel (.symbol name) space.atoms types →
      types ≠ [] →
      TypesOfRel space (.symbol name) types
  | symbolUndefined {space : Space} {name : String} :
      AnnotationTypesRel (.symbol name) space.atoms [] →
      TypesOfRel space (.symbol name) [Atom.undefinedType]
  | unit (space : Space) :
      TypesOfRel space (.expression []) [Atom.undefinedType]
  | expressionKnown {space : Space} {head : Atom} {tail types : List Atom} :
      AnnotationTypesRel (.expression (head :: tail)) space.atoms types →
      types ≠ [] →
      TypesOfRel space (.expression (head :: tail)) types
  | expressionUndefined {space : Space} {head : Atom} {tail : List Atom} :
      AnnotationTypesRel (.expression (head :: tail)) space.atoms [] →
      TypesOfRel space (.expression (head :: tail)) [Atom.undefinedType]

/-- One type in the complete ordered type list for an atom. -/
def TypeOfRel (space : Space) (atom type : Atom) : Prop :=
  ∃ types, TypesOfRel space atom types ∧ type ∈ types

/-! ## Type matching and casting -/

/-- Declarative `match_types`.  `%Undefined%` and `Atom` are wildcards; every
other case uses the already independent spec match and merge relations. -/
inductive TypeMatchRel : Atom → Atom → Bindings → Bindings → Prop where
  | undefinedLeft (right : Atom) (bindings : Bindings) :
      TypeMatchRel Atom.undefinedType right bindings bindings
  | atomLeft (right : Atom) (bindings : Bindings) :
      TypeMatchRel Atom.atomType right bindings bindings
  | undefinedRight (left : Atom) (bindings : Bindings) :
      TypeMatchRel left Atom.undefinedType bindings bindings
  | atomRight (left : Atom) (bindings : Bindings) :
      TypeMatchRel left Atom.atomType bindings bindings
  | structural {left right : Atom} {bindings matched output : Bindings} :
      left ≠ Atom.undefinedType →
      left ≠ Atom.atomType →
      right ≠ Atom.undefinedType →
      right ≠ Atom.atomType →
      MatchRel equalityGroundedSemantic left right matched →
      MergeRel equalityGroundedSemantic bindings matched output →
      TypeMatchRel left right bindings output

/-- Outside the two wildcard types, every type-match derivation exposes one
ordinary spec match followed by one spec merge. -/
theorem TypeMatchRel.structural_of_nonWildcard
    {left right : Atom} {bindings output : Bindings}
    (hLeftUndefined : left ≠ Atom.undefinedType)
    (hLeftAtom : left ≠ Atom.atomType)
    (hRightUndefined : right ≠ Atom.undefinedType)
    (hRightAtom : right ≠ Atom.atomType)
    (hmatch : TypeMatchRel left right bindings output) :
    ∃ matched,
      MatchRel equalityGroundedSemantic left right matched ∧
        MergeRel equalityGroundedSemantic bindings matched output := by
  cases hmatch with
  | undefinedLeft => exact (hLeftUndefined rfl).elim
  | atomLeft => exact (hLeftAtom rfl).elim
  | undefinedRight => exact (hRightUndefined rfl).elim
  | atomRight => exact (hRightAtom rfl).elim
  | structural _ _ _ _ hspec hmerge => exact ⟨_, hspec, hmerge⟩

/-- Relational `type_cast`, including the specification's first-success rule.
The reference interpreter calls `match_types(expected, actual, bindings)`;
this corrects the reversed operands printed in the prose pseudocode.  The
order matters when either type contains variables.  On total failure, one
error derivation is available for every discovered actual type. -/
inductive TypeCastRel (space : Space) (atom expectedType : Atom)
    (bindings : Bindings) : ResultPair → Prop where
  | success {types earlierTypes laterTypes : List Atom} {actualType : Atom}
      {output : Bindings} :
      TypesOfRel space atom types →
      types = earlierTypes ++ actualType :: laterTypes →
      (∀ earlier ∈ earlierTypes, ∀ candidate,
        ¬TypeMatchRel expectedType earlier bindings candidate) →
      TypeMatchRel expectedType actualType bindings output →
      TypeCastRel space atom expectedType bindings (atom, output)
  | failure {types : List Atom} {actualType : Atom} :
      TypesOfRel space atom types →
      actualType ∈ types →
      (∀ candidateType ∈ types, ∀ candidate,
        ¬TypeMatchRel expectedType candidateType bindings candidate) →
      TypeCastRel space atom expectedType bindings
        (mkError atom (.badType expectedType actualType), bindings)

/-! ## Function applicability -/

/-- A published function type `(-> arg₁ ... argₙ result)`.  The published
schema permits `n = 0`, represented by `(-> result)`; the bare `(->)` has no
return type and therefore has no witness. -/
def FunctionTypeRel (functionType : Atom) (argumentTypes : List Atom)
    (returnType : Atom) : Prop :=
  functionType =
    .expression (.symbol "->" :: (argumentTypes ++ [returnType]))

/-- The argument and return projections of one published arrow are unique.
This keeps arity and policy reasoning at the declarative boundary rather than
reconstructing list facts in every evaluator correspondence proof. -/
theorem FunctionTypeRel.unique
    {functionType : Atom}
    {leftArguments rightArguments : List Atom}
    {leftReturn rightReturn : Atom}
    (left : FunctionTypeRel functionType leftArguments leftReturn)
    (right : FunctionTypeRel functionType rightArguments rightReturn) :
    leftArguments = rightArguments ∧ leftReturn = rightReturn := by
  have parts : leftArguments ++ [leftReturn] =
      rightArguments ++ [rightReturn] := by
    rw [FunctionTypeRel] at left right
    exact List.cons.inj (Atom.expression.inj (left.symm.trans right)) |>.2
  constructor
  · have dropped := congrArg List.dropLast parts
    simpa [List.dropLast_concat] using dropped
  · have last := congrArg List.getLast? parts
    simpa [List.getLast?_concat] using last

/-- A successful left-to-right argument check.  Each step selects one actual
type and threads the bindings produced by declarative type matching. -/
inductive ArgumentsApplicableRel (space : Space) :
    List Atom → List Atom → Bindings → Bindings → Prop where
  | nil (bindings : Bindings) :
      ArgumentsApplicableRel space [] [] bindings bindings
  | cons {argument expectedType actualType : Atom}
      {arguments expectedTypes : List Atom}
      {bindings next output : Bindings} :
      TypeOfRel space argument actualType →
      TypeMatchRel expectedType actualType bindings next →
      ArgumentsApplicableRel space arguments expectedTypes next output →
      ArgumentsApplicableRel space
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings output

/-- One complete successful applicability path, including the return-type
check. -/
inductive ApplicationSuccessRel (space : Space) :
    Atom → Atom → Atom → Bindings → Bindings → Prop where
  | mk {expression functionType expectedType operator returnType : Atom}
      {arguments argumentTypes : List Atom}
      {bindings afterArguments output : Bindings} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      ArgumentsApplicableRel space arguments argumentTypes
        bindings afterArguments →
      TypeMatchRel expectedType returnType afterArguments output →
      ApplicationSuccessRel space expression functionType expectedType
        bindings output

/-- One observable outcome of function-type applicability. -/
inductive ApplicabilityOutcome where
  | success (bindings : Bindings)
  | error (errorAtom : Atom)
  deriving Repr

/-- Declarative `check_if_function_type_is_applicable`.  Error constructors
carry the same errors as the pseudocode and require absence of any complete
success whenever another type path could otherwise mask the error. -/
inductive ApplicabilityRel (space : Space) :
    Atom → Atom → Atom → Bindings → ApplicabilityOutcome → Prop where
  | success {expression functionType expectedType : Atom}
      {bindings output : Bindings} :
      ApplicationSuccessRel space expression functionType expectedType
        bindings output →
      ApplicabilityRel space expression functionType expectedType bindings
        (.success output)
  | wrongArity {expression functionType expectedType operator returnType : Atom}
      {arguments argumentTypes : List Atom} {bindings : Bindings} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      arguments.length ≠ argumentTypes.length →
      ApplicabilityRel space expression functionType expectedType bindings
        (.error (mkError expression .incorrectNumberOfArguments))
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
      ArgumentsApplicableRel space argumentsBefore typesBefore
        bindings beforeBad →
      TypeOfRel space badArgument actualType →
      (∀ candidate,
        ¬TypeMatchRel expectedArgument actualType beforeBad candidate) →
      (∀ output,
        ¬ApplicationSuccessRel space expression functionType expectedType
          bindings output) →
      ApplicabilityRel space expression functionType expectedType bindings
        (.error (mkError expression
          -- The pseudocode prints `idx - 1` despite iterating expression
          -- positions from one.  The reference evaluator and the documented
          -- `BadArgType` interface reports one-based argument positions.
          (.badArgType (argumentsBefore.length + 1)
            expectedArgument actualType)))
  | badReturn {expression functionType expectedType operator returnType : Atom}
      {arguments argumentTypes : List Atom}
      {bindings afterArguments : Bindings} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      ArgumentsApplicableRel space arguments argumentTypes
        bindings afterArguments →
      (∀ candidate,
        ¬TypeMatchRel expectedType returnType afterArguments candidate) →
      (∀ output,
        ¬ApplicationSuccessRel space expression functionType expectedType
          bindings output) →
      ApplicabilityRel space expression functionType expectedType bindings
        (.error (mkError expression (.badType expectedType returnType)))

/-! ## Boundary examples -/

private def declaredIntSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "x", .symbol "Int"]]

/-- Positive lookup: a direct type assignment is visible. -/
example : TypeOfRel declaredIntSpace (.symbol "x") (.symbol "Int") := by
  refine ⟨[.symbol "Int"], ?_, by simp⟩
  apply TypesOfRel.symbolKnown
  · change AnnotationTypesRel (.symbol "x")
      [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
      [.symbol "Int"]
    exact .hit .nil
  · simp

/-- Negative lookup: a variable with no intrinsic type is not assigned `Int`.-/
theorem variable_not_int_type :
    ¬TypeOfRel Space.empty (.var "x") (.symbol "Int") := by
  rintro ⟨types, htypes, hmem⟩
  cases htypes
  simp [Atom.undefinedType] at hmem

private theorem symbolTypeMatchEmpty (name : String)
    (hUndefined : name ≠ "%Undefined%") (hAtom : name ≠ "Atom") :
    TypeMatchRel (.symbol name) (.symbol name)
      Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural
  · simpa [Atom.undefinedType] using hUndefined
  · simpa [Atom.atomType] using hAtom
  · simpa [Atom.undefinedType] using hUndefined
  · simpa [Atom.atomType] using hAtom
  · exact MatchRel.symSym name semanticLoopFree_empty
  · exact MergeRel.mk
      (by simp [constraints, Bindings.empty])
      MergeConstraintsRel.nil

/-- Positive cast: the first declared type matches the expected type. -/
example : TypeCastRel declaredIntSpace (.symbol "x") (.symbol "Int")
    Bindings.empty (.symbol "x", Bindings.empty) := by
  apply TypeCastRel.success
      (types := [.symbol "Int"]) (earlierTypes := []) (laterTypes := [])
      (actualType := .symbol "Int")
  · apply TypesOfRel.symbolKnown
    · change AnnotationTypesRel (.symbol "x")
        [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
        [.symbol "Int"]
      exact .hit .nil
    · simp
  · rfl
  · simp
  · exact symbolTypeMatchEmpty "Int" (by decide) (by decide)

private theorem boolIntTypeMismatch (candidate : Bindings) :
    ¬TypeMatchRel (.symbol "Bool") (.symbol "Int")
      Bindings.empty candidate := by
  intro hmatch
  obtain ⟨matched, hspec, _⟩ := hmatch.structural_of_nonWildcard
    (by decide) (by decide) (by decide) (by decide)
  exact symbol_mismatch_not_match (by decide) matched hspec

/-- Negative cast outcome: an incompatible declared type produces the
published `BadType` error. -/
example : TypeCastRel declaredIntSpace (.symbol "x") (.symbol "Bool")
    Bindings.empty
    (mkError (.symbol "x") (.badType (.symbol "Bool") (.symbol "Int")),
      Bindings.empty) := by
  apply TypeCastRel.failure (types := [.symbol "Int"])
      (actualType := .symbol "Int")
  · apply TypesOfRel.symbolKnown
    · change AnnotationTypesRel (.symbol "x")
        [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
        [.symbol "Int"]
      exact .hit .nil
    · simp
  · simp
  · intro candidateType hmem candidate
    simp only [List.mem_singleton] at hmem
    subst candidateType
    exact boolIntTypeMismatch candidate

private def binaryNumberType : Atom :=
  .expression [
    .symbol "->", .symbol "Number", .symbol "Number", .symbol "Number"]

private def binaryNumberCall : Atom :=
  .expression [
    .symbol "add", .grounded (.int 1), .grounded (.int 2)]

private theorem groundedNumberType (value : Int) :
    TypeOfRel Space.empty (.grounded (.int value)) (.symbol "Number") := by
  refine ⟨[.symbol "Number"], ?_, by simp⟩
  exact TypesOfRel.groundedKnown (IntrinsicGroundedTypeRel.int value)
    (by simp [Atom.undefinedType])

/-- Positive applicability: both numeric arguments and the return type accept
a complete binding-threading path. -/
example : ApplicabilityRel Space.empty binaryNumberCall binaryNumberType
    Atom.undefinedType Bindings.empty (.success Bindings.empty) := by
  apply ApplicabilityRel.success
  apply ApplicationSuccessRel.mk
      (operator := .symbol "add")
      (arguments := [.grounded (.int 1), .grounded (.int 2)])
      (argumentTypes := [.symbol "Number", .symbol "Number"])
      (returnType := .symbol "Number")
      (afterArguments := Bindings.empty)
  · rfl
  · rfl
  · exact ArgumentsApplicableRel.cons (groundedNumberType 1)
      (symbolTypeMatchEmpty "Number" (by decide) (by decide))
      (ArgumentsApplicableRel.cons (groundedNumberType 2)
        (symbolTypeMatchEmpty "Number" (by decide) (by decide))
        (ArgumentsApplicableRel.nil Bindings.empty))
  · exact TypeMatchRel.undefinedLeft (.symbol "Number") Bindings.empty

/-- Negative applicability outcome: a unary call cannot inhabit a binary
function type and produces `IncorrectNumberOfArguments`. -/
theorem binary_function_rejects_unary_arity : ApplicabilityRel Space.empty
    (.expression [.symbol "add", .grounded (.int 1)]) binaryNumberType
    Atom.undefinedType Bindings.empty
    (.error (mkError
      (.expression [.symbol "add", .grounded (.int 1)])
      .incorrectNumberOfArguments)) := by
  apply ApplicabilityRel.wrongArity
      (operator := .symbol "add")
      (arguments := [.grounded (.int 1)])
      (argumentTypes := [.symbol "Number", .symbol "Number"])
      (returnType := .symbol "Number")
  · rfl
  · rfl
  · decide

/-- The published arrow schema admits the nullary case `(-> R)`. -/
theorem nullary_function_type :
    FunctionTypeRel
      (.expression [.symbol "->", .symbol "R"]) [] (.symbol "R") := by
  rfl

/-- A nullary call follows the ordinary successful applicability path. -/
theorem nullary_function_applicable :
    ApplicabilityRel Space.empty
      (.expression [.symbol "constant"])
      (.expression [.symbol "->", .symbol "R"])
      Atom.undefinedType Bindings.empty (.success Bindings.empty) := by
  apply ApplicabilityRel.success
  apply ApplicationSuccessRel.mk
      (operator := .symbol "constant")
      (arguments := [])
      (argumentTypes := [])
      (returnType := .symbol "R")
      (afterArguments := Bindings.empty)
  · rfl
  · exact nullary_function_type
  · exact ArgumentsApplicableRel.nil Bindings.empty
  · exact TypeMatchRel.undefinedLeft (.symbol "R") Bindings.empty

/-- The bare arrow has no return component and remains malformed. -/
theorem bare_arrow_not_function_type :
    ¬∃ argumentTypes returnType,
      FunctionTypeRel (.expression [.symbol "->"])
        argumentTypes returnType := by
  rintro ⟨argumentTypes, returnType, hfunction⟩
  simp [FunctionTypeRel] at hfunction

end Mettapedia.Languages.MeTTa.HE.Spec.Type
