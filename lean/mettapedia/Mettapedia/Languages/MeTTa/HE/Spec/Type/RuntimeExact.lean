import Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement

/-!
# Exact precedence for named runtime type refinements

`RuntimeTypeEvidenceRel` is intentionally a positive over-approximation: it
records published, R1, and R3 evidence without choosing between them.  That is
the right boundary for proving that every runtime output has semantic meaning,
but it cannot appear below a negative applicability premise.

This module gives the exact priority layer.  Candidate types are
`RuntimeTypePackage`s, so every inferred term retains its private binding
theory.  The ordered relation implements the named runtime delta without
mentioning an executable type service:

* direct annotations win for ordinary expressions;
* the R3 `StateValue` representation rule precedes ordinary expression lookup;
* otherwise, R1 scans operator candidates in order and emits one package for
  each applicable function candidate;
* `%Undefined%` is emitted only when that scan has no result.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeExact

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type
open Spec.Type.RuntimeRefinement

/-- One direct published type without private inference constraints. -/
def publishedPackage (type : Atom) : RuntimeTypePackage :=
  RuntimeTypePackage.published type

/-- Package every direct published type without adding private constraints. -/
def publishedPackages (types : List Atom) : List RuntimeTypePackage :=
  types.map publishedPackage

/-- A nonempty expression is not the forgeable R3 wrapper shape. -/
def NotStateValueShape (head : Atom) (tail : List Atom) : Prop :=
  ∀ value, head ≠ .symbol "StateValue" ∨ tail ≠ [value]

/-- Match already-selected argument packages against one function skeleton. -/
inductive PackagedArgumentListMatchRel (space : Space) :
    List Atom → List RuntimeTypePackage →
      RuntimeTypeTheory → RuntimeTypeTheory → Prop where
  | nil (bindings : RuntimeTypeTheory) :
      PackagedArgumentListMatchRel space [] [] bindings bindings
  | cons {expected : Atom} {actual : RuntimeTypePackage}
      {expecteds : List Atom} {actuals : List RuntimeTypePackage}
      {incoming next output : RuntimeTypeTheory} :
      PackagedTypeMatchRel expected actual incoming next →
      PackagedArgumentListMatchRel space expecteds actuals next output →
      PackagedArgumentListMatchRel space
        (expected :: expecteds) (actual :: actuals) incoming output

/-- One ordered operator candidate either contributes its constrained return
package or contributes no result.  Failure is the genuine absence of every
function-skeleton/argument-match derivation for this package. -/
inductive RuntimeApplicationPackageOutcomeRel (space : Space) :
    List RuntimeTypePackage → RuntimeTypePackage →
      Option RuntimeTypePackage → Prop where
  | success {argumentTypes : List Atom} {returnType : Atom}
      {typeTheory : RuntimeTypeTheory} :
      PackagedFunctionTypeRel operator argumentTypes returnType →
      PackagedArgumentListMatchRel space argumentTypes arguments
        operator.theory typeTheory →
      RuntimeApplicationPackageOutcomeRel space arguments operator
        (some ⟨typeTheory, returnType⟩)
  | failure :
      (∀ argumentTypes returnType typeTheory,
        ¬(PackagedFunctionTypeRel operator argumentTypes returnType ∧
          PackagedArgumentListMatchRel space argumentTypes arguments
            operator.theory typeTheory)) →
      RuntimeApplicationPackageOutcomeRel space arguments operator none

/-- Ordered `filterMap`-style scan of operator packages. -/
inductive RuntimeApplicationPackageScanRel (space : Space) :
    List RuntimeTypePackage → List RuntimeTypePackage →
      List RuntimeTypePackage → Prop where
  | nil (arguments : List RuntimeTypePackage) :
      RuntimeApplicationPackageScanRel space arguments [] []
  | skip {operator : RuntimeTypePackage}
      {operators results : List RuntimeTypePackage} :
      RuntimeApplicationPackageOutcomeRel space arguments operator none →
      RuntimeApplicationPackageScanRel space arguments operators results →
      RuntimeApplicationPackageScanRel space arguments
        (operator :: operators) results
  | emit {operator result : RuntimeTypePackage}
      {operators results : List RuntimeTypePackage} :
      RuntimeApplicationPackageOutcomeRel space arguments operator (some result) →
      RuntimeApplicationPackageScanRel space arguments operators results →
      RuntimeApplicationPackageScanRel space arguments
        (operator :: operators) (result :: results)

mutual

/-- Exact ordered candidate packages for one atom. -/
inductive RuntimeTypePackagesRel (space : Space) :
    Atom → List RuntimeTypePackage → Prop where
  | variable (name : String) :
      RuntimeTypePackagesRel space (.var name)
        [publishedPackage Atom.undefinedType]
  | grounded {value : GroundedValue} {type : Atom} :
      IntrinsicGroundedTypeRel value type →
      RuntimeTypePackagesRel space (.grounded value)
        [publishedPackage type]
  | symbolKnown {name : String} {types : List Atom} :
      AnnotationTypesRel (.symbol name) space.atoms types →
      types ≠ [] →
      RuntimeTypePackagesRel space (.symbol name) (publishedPackages types)
  | symbolUndefined {name : String} :
      AnnotationTypesRel (.symbol name) space.atoms [] →
      RuntimeTypePackagesRel space (.symbol name)
        [publishedPackage Atom.undefinedType]
  | unit :
      RuntimeTypePackagesRel space (.expression [])
        [publishedPackage Atom.undefinedType]
  | stateValue {value : Atom} {content : RuntimeTypePackage}
      {remaining : List RuntimeTypePackage} :
      RuntimeTypePackagesRel space value (content :: remaining) →
      RuntimeTypePackagesRel space
        (.expression [.symbol "StateValue", value])
        [⟨content.theory,
          .expression [.symbol "StateMonad", content.term]⟩]
  | expressionKnown {head : Atom} {tail types : List Atom} :
      NotStateValueShape head tail →
      AnnotationTypesRel (.expression (head :: tail)) space.atoms types →
      types ≠ [] →
      RuntimeTypePackagesRel space (.expression (head :: tail))
        (publishedPackages types)
  | expressionInferred {head : Atom} {tail : List Atom}
      {operatorPackages argumentPackages results : List RuntimeTypePackage} :
      NotStateValueShape head tail →
      AnnotationTypesRel (.expression (head :: tail)) space.atoms [] →
      RuntimeTypePackagesRel space head operatorPackages →
      RuntimeArgumentHeadPackagesRel space tail argumentPackages →
      RuntimeApplicationPackageScanRel space
        argumentPackages operatorPackages results →
      results ≠ [] →
      RuntimeTypePackagesRel space (.expression (head :: tail)) results
  | expressionUndefined {head : Atom} {tail : List Atom}
      {operatorPackages argumentPackages : List RuntimeTypePackage} :
      NotStateValueShape head tail →
      AnnotationTypesRel (.expression (head :: tail)) space.atoms [] →
      RuntimeTypePackagesRel space head operatorPackages →
      RuntimeArgumentHeadPackagesRel space tail argumentPackages →
      RuntimeApplicationPackageScanRel space
        argumentPackages operatorPackages [] →
      RuntimeTypePackagesRel space (.expression (head :: tail))
        [publishedPackage Atom.undefinedType]

/-- The runtime inference rule consults only the first type candidate of each
argument.  This relation extracts those heads in source order. -/
inductive RuntimeArgumentHeadPackagesRel (space : Space) :
    List Atom → List RuntimeTypePackage → Prop where
  | nil : RuntimeArgumentHeadPackagesRel space [] []
  | cons {argument : Atom} {arguments : List Atom}
      {head : RuntimeTypePackage} {tail : List RuntimeTypePackage}
      {heads : List RuntimeTypePackage} :
      RuntimeTypePackagesRel space argument (head :: tail) →
      RuntimeArgumentHeadPackagesRel space arguments heads →
      RuntimeArgumentHeadPackagesRel space
        (argument :: arguments) (head :: heads)

end

/-! ## Precedence canaries -/

private def exactStateValue : Atom :=
  .expression [.symbol "StateValue", .grounded (.int 1)]

private def exactStatePackage : RuntimeTypePackage :=
  publishedPackage (.expression [.symbol "StateMonad", .symbol "Number"])

/-- Positive R3 precedence: the wrapper has exactly one state-monad package. -/
theorem stateValue_exact_package :
    RuntimeTypePackagesRel Space.empty exactStateValue [exactStatePackage] := by
  change RuntimeTypePackagesRel Space.empty
    (.expression [.symbol "StateValue", .grounded (.int 1)])
    [⟨RuntimeTypeTheory.empty,
      .expression [.symbol "StateMonad", .symbol "Number"]⟩]
  apply RuntimeTypePackagesRel.stateValue
      (content := publishedPackage (.symbol "Number"))
      (remaining := [])
  exact RuntimeTypePackagesRel.grounded (IntrinsicGroundedTypeRel.int 1)

private theorem stateValue_packages_shape
    {packages : List RuntimeTypePackage}
    (htypes : RuntimeTypePackagesRel Space.empty exactStateValue packages) :
    ∃ theory term,
      packages =
        [⟨theory, .expression [.symbol "StateMonad", term]⟩] := by
  cases htypes with
  | stateValue hcontent =>
      exact ⟨_, _, rfl⟩
  | expressionKnown hnotState _ _ =>
      have hfalse := hnotState (.grounded (.int 1))
      simp at hfalse
  | expressionInferred hnotState _ _ _ _ _ =>
      have hfalse := hnotState (.grounded (.int 1))
      simp at hfalse
  | expressionUndefined hnotState _ _ _ _ =>
      have hfalse := hnotState (.grounded (.int 1))
      simp at hfalse

/-- Negative R3 precedence: the published expression fallback is not retained
beside the selected state-monad package. -/
theorem stateValue_not_published_fallback :
    ¬RuntimeTypePackagesRel Space.empty exactStateValue
      [publishedPackage Atom.undefinedType] := by
  intro htypes
  obtain ⟨theory, term, hshape⟩ := stateValue_packages_shape htypes
  have hpackage := (List.cons.inj hshape).1
  have hterm := congrArg RuntimeTypePackage.term hpackage
  simp [publishedPackage, RuntimeTypePackage.published,
    Atom.undefinedType] at hterm

private def exactR1Space : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "id",
      .expression [.symbol "->", .var "t", .var "t"]],
    .expression [.symbol ":", .symbol "a", .symbol "A"]]

private def exactIdOperator : RuntimeTypePackage :=
  publishedPackage
    (.expression [.symbol "->", .var "t", .var "t"])

private def exactAArgument : RuntimeTypePackage :=
  publishedPackage (.symbol "A")

private def exactATheory : RuntimeTypeTheory where
  Holds := fun valuation => valuation "t" = .symbol "A"
  satisfiable :=
    ⟨fun name => if name = "t" then .symbol "A" else .var name, by simp⟩

private def exactIdResult : RuntimeTypePackage :=
  ⟨exactATheory, .var "t"⟩

private theorem exact_id_function :
    PackagedFunctionTypeRel exactIdOperator [.var "t"] (.var "t") := by
  intro valuation _
  rfl

private theorem exact_t_matches_A :
    PackagedTypeMatchRel (.var "t") exactAArgument
      RuntimeTypeTheory.empty exactATheory := by
  constructor
  intro valuation
  simp [exactATheory, exactAArgument, publishedPackage,
    RuntimeTypePackage.published, RuntimeTypeTheory.empty,
    RuntimeTypePackage.Satisfied, CorePlusR2TypeConsistent,
    ReducedTypeConsistent, Atom.undefinedType, Atom.atomType,
    applyTypeValuation]

private theorem exact_id_arguments :
    PackagedArgumentListMatchRel exactR1Space [.var "t"] [exactAArgument]
      exactIdOperator.theory exactATheory := by
  apply PackagedArgumentListMatchRel.cons exact_t_matches_A
  exact PackagedArgumentListMatchRel.nil exactATheory

private theorem exact_id_outcome :
    RuntimeApplicationPackageOutcomeRel exactR1Space [exactAArgument]
      exactIdOperator (some exactIdResult) := by
  change RuntimeApplicationPackageOutcomeRel exactR1Space [exactAArgument]
    exactIdOperator (some ⟨exactATheory, .var "t"⟩)
  exact RuntimeApplicationPackageOutcomeRel.success
    exact_id_function exact_id_arguments

private theorem exact_id_scan :
    RuntimeApplicationPackageScanRel exactR1Space [exactAArgument]
      [exactIdOperator] [exactIdResult] := by
  apply RuntimeApplicationPackageScanRel.emit exact_id_outcome
  exact RuntimeApplicationPackageScanRel.nil [exactAArgument]

private theorem exact_id_operator_packages :
    RuntimeTypePackagesRel exactR1Space (.symbol "id") [exactIdOperator] := by
  change RuntimeTypePackagesRel exactR1Space (.symbol "id")
    (publishedPackages
      [.expression [.symbol "->", .var "t", .var "t"]])
  apply RuntimeTypePackagesRel.symbolKnown
  · exact AnnotationTypesRel.hit
      (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil)
  · simp

private theorem exact_a_packages :
    RuntimeTypePackagesRel exactR1Space (.symbol "a") [exactAArgument] := by
  change RuntimeTypePackagesRel exactR1Space (.symbol "a")
    (publishedPackages [.symbol "A"])
  apply RuntimeTypePackagesRel.symbolKnown
  · exact AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.hit AnnotationTypesRel.nil)
  · simp

/-- Positive R1 precedence: application inference returns a constrained
package, not the published expression fallback and not a bare orphaned `$t`. -/
theorem parametric_application_exact_package :
    RuntimeTypePackagesRel exactR1Space
      (.expression [.symbol "id", .symbol "a"])
      [exactIdResult] := by
  apply RuntimeTypePackagesRel.expressionInferred
      (operatorPackages := [exactIdOperator])
      (argumentPackages := [exactAArgument])
  · intro value
    exact Or.inl (by simp)
  · exact AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil)
  · exact exact_id_operator_packages
  · exact RuntimeArgumentHeadPackagesRel.cons exact_a_packages
      RuntimeArgumentHeadPackagesRel.nil
  · exact exact_id_scan
  · simp

end Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeExact
