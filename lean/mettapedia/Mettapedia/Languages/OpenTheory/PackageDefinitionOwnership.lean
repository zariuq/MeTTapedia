import Mettapedia.Languages.OpenTheory.Definitions

/-!
# Package-level ownership of OpenTheory definition names

OpenTheory definition commands construct provenance-sensitive symbols directly;
the article reader does not maintain a fresh-name table.  Printed-name clashes
are checked later when defined symbols from packages are combined.  Type
operator names and constant names occupy separate namespaces.

This module isolates that later ownership check.  It follows the behavior of
`PackageTheorems.addDefined` at OpenTheory revision
`f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1`: an unowned name becomes owned by
the current package, a repeated definition from the same package is accepted,
and ownership by a different package rejects the combination.
-/

namespace Mettapedia.Languages.OpenTheory

/-- Printed definition names, with the type-operator and constant namespaces
kept disjoint. -/
inductive DefinedSymbolName where
  | typeOperator : Name → DefinedSymbolName
  | constant : Name → DefinedSymbolName
deriving Repr, DecidableEq

/-- Extensional package ownership of printed definition names.  Finiteness is
carried by each package's definition list, not hidden in the lookup interface. -/
abbrev DefinitionOwnership (Package : Type) :=
  DefinedSymbolName → Option Package

namespace DefinitionOwnership

variable {Package : Type} [DecidableEq Package]

/-- No printed definition name is initially owned. -/
def empty : DefinitionOwnership Package := fun _name => none

/-- One name is compatible with a package when it is unowned or already owned
by that same package. -/
def compatibleName (ownership : DefinitionOwnership Package)
    (package : Package) (name : DefinedSymbolName) : Bool :=
  match ownership name with
  | none => true
  | some existing => decide (existing = package)

@[simp] theorem compatibleName_eq_true_iff
    (ownership : DefinitionOwnership Package) (package : Package)
    (name : DefinedSymbolName) :
    compatibleName ownership package name = true ↔
      ownership name = none ∨ ownership name = some package := by
  unfold compatibleName
  cases lookup : ownership name with
  | none => simp
  | some existing => simp

/-- Executable compatibility of every name in one package definition list. -/
def compatibleNames (ownership : DefinitionOwnership Package)
    (package : Package) : List DefinedSymbolName → Bool
  | [] => true
  | name :: names =>
      compatibleName ownership package name &&
        compatibleNames ownership package names

/-- Propositional package-name compatibility. -/
def Compatible (ownership : DefinitionOwnership Package)
    (package : Package) (names : List DefinedSymbolName) : Prop :=
  ∀ name ∈ names,
    ownership name = none ∨ ownership name = some package

@[simp] theorem compatibleNames_eq_true_iff
    (ownership : DefinitionOwnership Package) (package : Package)
    (names : List DefinedSymbolName) :
    compatibleNames ownership package names = true ↔
      Compatible ownership package names := by
  induction names with
  | nil => simp [compatibleNames, Compatible]
  | cons name names inductionHypothesis =>
      simp [compatibleNames, Compatible, inductionHypothesis]

/-- Assign every listed name to the package, leaving every other lookup
unchanged. -/
def assign (ownership : DefinitionOwnership Package) (package : Package)
    (names : List DefinedSymbolName) : DefinitionOwnership Package :=
  fun name => if name ∈ names then some package else ownership name

/-- Combine one package's defined names with the accumulated ownership table. -/
def addDefinitions (ownership : DefinitionOwnership Package)
    (package : Package) (names : List DefinedSymbolName) :
    Option (DefinitionOwnership Package) :=
  if compatibleNames ownership package names = true then
    some (assign ownership package names)
  else
    none

/-- Package combination succeeds exactly when no listed printed name is owned
by a different package. -/
theorem addDefinitions_isSome_iff
    (ownership : DefinitionOwnership Package) (package : Package)
    (names : List DefinedSymbolName) :
    (addDefinitions ownership package names).isSome = true ↔
      Compatible ownership package names := by
  by_cases compatible : compatibleNames ownership package names = true
  · simp [addDefinitions, compatible,
      (compatibleNames_eq_true_iff ownership package names).mp compatible]
  · have incompatible : ¬ Compatible ownership package names := by
      intro propositionallyCompatible
      exact compatible
        ((compatibleNames_eq_true_iff ownership package names).mpr
          propositionallyCompatible)
    simp [addDefinitions, compatible, incompatible]

/-- Exact successful result, not merely success of the Boolean gate. -/
theorem addDefinitions_eq_some_iff
    (ownership : DefinitionOwnership Package) (package : Package)
    (names : List DefinedSymbolName)
    (result : DefinitionOwnership Package) :
    addDefinitions ownership package names = some result ↔
      Compatible ownership package names ∧
        result = assign ownership package names := by
  by_cases compatible : compatibleNames ownership package names = true
  · have propositionallyCompatible :
        Compatible ownership package names :=
      (compatibleNames_eq_true_iff ownership package names).mp compatible
    simp only [addDefinitions, compatible, if_pos, Option.some.injEq,
      propositionallyCompatible, true_and]
    exact eq_comm
  · have incompatible : ¬ Compatible ownership package names := by
      intro propositionallyCompatible
      exact compatible
        ((compatibleNames_eq_true_iff ownership package names).mpr
          propositionallyCompatible)
    simp [addDefinitions, compatible, incompatible]

/-- Every listed name is owned by the added package after a successful
combination. -/
theorem owns_of_addDefinitions
    {ownership result : DefinitionOwnership Package} {package : Package}
    {names : List DefinedSymbolName}
    (accepted : addDefinitions ownership package names = some result)
    {name : DefinedSymbolName} (member : name ∈ names) :
    result name = some package := by
  have exactResult :=
    (addDefinitions_eq_some_iff ownership package names result).mp accepted
  rw [exactResult.2]
  simp [assign, member]

/-- Successful package combination preserves every unlisted ownership lookup. -/
theorem lookup_of_addDefinitions_of_not_mem
    {ownership result : DefinitionOwnership Package} {package : Package}
    {names : List DefinedSymbolName}
    (accepted : addDefinitions ownership package names = some result)
    {name : DefinedSymbolName} (notMember : name ∉ names) :
    result name = ownership name := by
  have exactResult :=
    (addDefinitions_eq_some_iff ownership package names result).mp accepted
  rw [exactResult.2]
  simp [assign, notMember]

/-- A name already owned by a different package forces rejection. -/
theorem addDefinitions_eq_none_of_cross_package
    (ownership : DefinitionOwnership Package) {package existing : Package}
    (different : existing ≠ package) (names : List DefinedSymbolName)
    {name : DefinedSymbolName} (member : name ∈ names)
    (owned : ownership name = some existing) :
    addDefinitions ownership package names = none := by
  have incompatible : ¬ Compatible ownership package names := by
    intro compatible
    rcases compatible name member with unowned | sameOwner
    · rw [owned] at unowned
      contradiction
    · have ownerEquality : existing = package :=
        Option.some.inj (owned.symm.trans sameOwner)
      exact different ownerEquality
  have executableIncompatible :
      compatibleNames ownership package names ≠ true := by
    intro executableCompatible
    exact incompatible
      ((compatibleNames_eq_true_iff ownership package names).mp
        executableCompatible)
  simp [addDefinitions, executableIncompatible]

end DefinitionOwnership

namespace ConstantDefinitionResult

/-- The printed constant name contributed by a constant definition. -/
def definedNames (result : ConstantDefinitionResult) :
    List DefinedSymbolName :=
  match result.constant with
  | .mk name _provenance => [.constant name]

end ConstantDefinitionResult

namespace TypeOperatorDefinitionResult

/-- The three separate printed names contributed by a type-operator
definition. -/
def definedNames (result : TypeOperatorDefinitionResult) :
    List DefinedSymbolName :=
  match result.typeOperator, result.abstractionConstant,
      result.representationConstant with
  | .mk typeName _typeProvenance, .mk abstractionName _abstractionProvenance,
      .mk representationName _representationProvenance =>
      [.typeOperator typeName, .constant abstractionName,
        .constant representationName]

end TypeOperatorDefinitionResult

end Mettapedia.Languages.OpenTheory
