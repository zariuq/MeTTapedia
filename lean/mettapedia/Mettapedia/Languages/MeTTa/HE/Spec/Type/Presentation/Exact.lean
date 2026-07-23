import Mettapedia.Languages.MeTTa.HE.Spec.Type.Instantiation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.FreshnessCore

/-!
# Ordered runtime type presentations

Positive type evidence is intentionally permissive, but evaluator error rules
need the exact precedence and candidate multiplicity of the runtime type
service.  This module states that ordered boundary using package-local finite
substitutions.  Inferred variables are alpha-renamed at their consumption
site, argument candidates are renamed in distinct scopes, and the resulting
substitution is discharged into the emitted return atom.

The relation remains executable-independent: freshening is an injective
alpha-variant satisfying a finite avoidance contract, matching is the spec
presentation relation, and no constructor mentions a runtime function or
fuel.  The concrete runtime correspondence is proved in the conformance
layer; until both directions are established, consumers must not treat the
relation as an executable characterization.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.Freshness

abbrev TypePackage := Spec.Type.Presentation.RuntimeTypePackage

/-- A literal candidate with no private inference substitution. -/
def publishedPackage (type : Atom) : TypePackage :=
  Spec.Type.Presentation.RuntimeTypePackage.published type

/-- Package the result of one local application-type inference fold. -/
def inferredPackage (substitution : TypeSubst) (rawReturn : Atom) :
    TypePackage :=
  ⟨substitution.apply rawReturn, rawReturn, substitution, rfl⟩

/-- R3 preserves the content package's private presentation while wrapping
both its raw and observed terms. -/
def stateMonadPackage (content : TypePackage) : TypePackage :=
  ⟨.expression [.symbol "StateMonad", content.observed],
    .expression [.symbol "StateMonad", content.rawTerm],
    content.substitution,
    by simp [TypeSubst.apply, content.presentation]⟩

/-- Observed atoms carried by an ordered package list. -/
def observedTypes (packages : List TypePackage) : List Atom :=
  packages.map (fun package => package.observed)

/-- A nonempty expression is not the forgeable R3 wrapper shape. -/
def NotStateValueShape (head : Atom) (tail : List Atom) : Prop :=
  ∀ value, head ≠ .symbol "StateValue" ∨ tail ≠ [value]

/-! ## Package-local alpha scopes -/

/-- One schematic type annotation may be renamed injectively at its inference
site, provided every renamed variable avoids the finite live-name set. -/
def TypeCandidateAlphaVariantRel
    (avoid : List String) (source target : Atom) : Prop :=
  ∃ rename : String → String,
    Function.Injective rename ∧
      target = renameTypeVars rename source ∧
      ∀ name ∈ TypeSubst.typeVars source, rename name ∉ avoid

/-- Forgetting the finite avoidance proof yields the positive refinement
layer's schematic-type renaming evidence. -/
theorem TypeCandidateAlphaVariantRel.toTypeVariableRenamingOf
    {avoid : List String} {source target : Atom}
    (variant : TypeCandidateAlphaVariantRel avoid source target) :
    TypeVariableRenamingOf source target := by
  rcases variant with ⟨rename, hinjective, hpresentation, _⟩
  exact ⟨rename, hinjective, hpresentation⟩

/-- Argument candidates are freshened left-to-right.  Each emitted candidate
extends the avoid set seen by all later arguments. -/
inductive ArgumentAlphaVariantsRel :
    List String → List Atom → List Atom → Prop where
  | nil (avoid : List String) : ArgumentAlphaVariantsRel avoid [] []
  | cons {avoid : List String} {source target : Atom}
      {sources targets : List Atom} :
      TypeCandidateAlphaVariantRel avoid source target →
      ArgumentAlphaVariantsRel
        (avoid ++ TypeSubst.typeVars target) sources targets →
      ArgumentAlphaVariantsRel avoid
        (source :: sources) (target :: targets)

/-- Operator candidates share the function-side avoid set.  Candidates are
scanned independently, so their private alpha scopes need not be conjoined. -/
inductive OperatorAlphaVariantsRel (avoid : List String) :
    List Atom → List Atom → Prop where
  | nil : OperatorAlphaVariantsRel avoid [] []
  | cons {source target : Atom} {sources targets : List Atom} :
      TypeCandidateAlphaVariantRel avoid source target →
      OperatorAlphaVariantsRel avoid sources targets →
      OperatorAlphaVariantsRel avoid
        (source :: sources) (target :: targets)

/-- The names visible at one type-inference boundary.  This is a semantic
scope description, not a concrete fresh-name generator. -/
def inferenceAvoidNames
    (space : Space) (context : Atom) (candidates : List Atom) : List String :=
  TypeSubst.typeVarsList (space.atoms ++ (context :: candidates))

/-! ## One application inference scan -/

/-- Match expected and selected actual types left-to-right while threading
the outer finite substitution. -/
inductive PresentationArgumentListMatchRel :
    List Atom → List Atom → TypeSubst → TypeSubst → Prop where
  | nil (substitution : TypeSubst) :
      PresentationArgumentListMatchRel [] [] substitution substitution
  | cons {expected actual : Atom} {expecteds actuals : List Atom}
      {incoming next output : TypeSubst} :
      CorePlusR2TypePresentationMatchRel incoming expected actual next →
      PresentationArgumentListMatchRel expecteds actuals next output →
      PresentationArgumentListMatchRel
        (expected :: expecteds) (actual :: actuals) incoming output

/-- One syntactic arrow candidate successfully checks every selected argument
and emits its locally instantiated return package. -/
inductive ApplicationPackageSuccessRel :
    List Atom → Atom → TypePackage → Prop where
  | mk {operatorType returnType : Atom}
      {expectedTypes actualTypes : List Atom}
      {substitution : TypeSubst} :
      operatorType =
        .expression (.symbol "->" :: (expectedTypes ++ [returnType])) →
      PresentationArgumentListMatchRel
        expectedTypes actualTypes [] substitution →
      ApplicationPackageSuccessRel actualTypes operatorType
        (inferredPackage substitution returnType)

/-- One ordered operator candidate either emits its inferred return package
or contributes no result. -/
inductive ApplicationPackageOutcomeRel :
    List Atom → Atom → Option TypePackage → Prop where
  | success {actualTypes : List Atom} {operatorType : Atom}
      {result : TypePackage} :
      ApplicationPackageSuccessRel actualTypes operatorType result →
      ApplicationPackageOutcomeRel actualTypes operatorType (some result)
  | failure {actualTypes : List Atom} {operatorType : Atom} :
      (∀ result,
        ¬ApplicationPackageSuccessRel actualTypes operatorType result) →
      ApplicationPackageOutcomeRel actualTypes operatorType none

/-- Ordered `filterMap`-style scan of all fresh operator candidates. -/
inductive ApplicationPackageScanRel (actualTypes : List Atom) :
    List Atom → List TypePackage → Prop where
  | nil : ApplicationPackageScanRel actualTypes [] []
  | skip {operatorType : Atom} {operatorTypes : List Atom}
      {results : List TypePackage} :
      ApplicationPackageOutcomeRel actualTypes operatorType none →
      ApplicationPackageScanRel actualTypes operatorTypes results →
      ApplicationPackageScanRel actualTypes
        (operatorType :: operatorTypes) results
  | emit {operatorType : Atom} {operatorTypes : List Atom}
      {result : TypePackage} {results : List TypePackage} :
      ApplicationPackageOutcomeRel actualTypes operatorType (some result) →
      ApplicationPackageScanRel actualTypes operatorTypes results →
      ApplicationPackageScanRel actualTypes
        (operatorType :: operatorTypes) (result :: results)

/-! ## Ordered Cartesian application scans -/

/-- Ordered Cartesian product with the first list as the outer (major)
dimension.  Unlike `List.sections`, this preserves the row-major order used
by the published application-type scan: for `[[a, b], [c, d]]` the choices
are `[[a, c], [a, d], [b, c], [b, d]]`.

This is a neutral finite-list combinator.  The conformance layer proves its
boundary equation with the repaired runtime's Cartesian helper. -/
def orderedCartesian {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | choices :: rest =>
      choices.flatMap fun choice =>
        (orderedCartesian rest).map fun tail => choice :: tail

/-- One operator candidate is checked against every ordered argument-type
choice.  The complete option row records failures as `none`; filtering the
row therefore preserves the order and multiplicity of all successes. -/
def ApplicationPackageOutcomeRowRel
    (argumentChoices : List (List Atom)) (operatorType : Atom)
    (results : List TypePackage) : Prop :=
  ∃ outcomes : List (Option TypePackage),
    List.Forall₂
      (fun actualTypes outcome =>
        ApplicationPackageOutcomeRel actualTypes operatorType outcome)
      argumentChoices outcomes ∧
    outcomes.filterMap id = results

/-- Operator-major, argument-choice-minor application scan.  Each operator
contributes one contiguous row, and flattening those rows gives the exact
published result order.  This is a thin assembly of the existing
one-candidate outcome relation, not a second matching relation. -/
def ApplicationPackageMatrixRel
    (argumentChoices : List (List Atom))
    (operatorTypes : List Atom) (results : List TypePackage) : Prop :=
  ∃ rows : List (List TypePackage),
    List.Forall₂
      (ApplicationPackageOutcomeRowRel argumentChoices)
      operatorTypes rows ∧
    rows.flatten = results

/-- Every operator presentation is capture-disjoint from every independently
freshened argument-choice presentation.  The global operator variant records
one-shot freshening provenance; this separate cell law is the semantic scope
fact consumed by every matrix cell. -/
def ApplicationPackageScopesSeparated
    (argumentChoices : List (List Atom))
    (operatorTypes : List Atom) : Prop :=
  ∀ actualTypes ∈ argumentChoices,
    ∀ operatorType ∈ operatorTypes,
      FreshFamiliesSeparated [operatorType] actualTypes

/-- Assemble the matrix-wide separation contract from its familiar
atom-by-atom support condition. -/
theorem ApplicationPackageScopesSeparated.mk
    {argumentChoices : List (List Atom)} {operatorTypes : List Atom}
    (separated : ∀ actualTypes ∈ argumentChoices,
      ∀ operatorType ∈ operatorTypes,
        ∀ name ∈ TypeSubst.typeVars operatorType,
          name ∉ TypeSubst.typeVarsList actualTypes) :
    ApplicationPackageScopesSeparated argumentChoices operatorTypes := by
  intro actualTypes actualMember operatorType operatorMember
    name operatorMemberVar argumentMemberVar
  exact separated actualTypes actualMember operatorType operatorMember name
    (by simpa [TypeSubst.typeVarsList] using operatorMemberVar)
    argumentMemberVar

/-- Eliminate the shared family contract at one operator/argument cell. -/
theorem ApplicationPackageScopesSeparated.atom
    {argumentChoices : List (List Atom)} {operatorTypes : List Atom}
    (separated : ApplicationPackageScopesSeparated
      argumentChoices operatorTypes)
    {actualTypes : List Atom} (actualMember : actualTypes ∈ argumentChoices)
    {operatorType : Atom} (operatorMember : operatorType ∈ operatorTypes)
    {name : String} (operatorOccurrence : name ∈ TypeSubst.typeVars operatorType) :
    name ∉ TypeSubst.typeVarsList actualTypes := by
  exact separated actualTypes actualMember operatorType operatorMember name
    (by simpa [TypeSubst.typeVarsList] using operatorOccurrence)

/-- A single successful operator/argument-choice cell forms a one-element
matrix without changing its package. -/
theorem ApplicationPackageMatrixRel.singleton_success
    {actualTypes : List Atom} {operatorType : Atom}
    {result : TypePackage}
    (success : ApplicationPackageSuccessRel
      actualTypes operatorType result) :
    ApplicationPackageMatrixRel
      [actualTypes] [operatorType] [result] := by
  refine ⟨[[result]], List.Forall₂.cons ?_ List.Forall₂.nil, rfl⟩
  refine ⟨[some result], List.Forall₂.cons ?_ List.Forall₂.nil, rfl⟩
  exact ApplicationPackageOutcomeRel.success success

/-- A single failing operator/argument-choice cell contributes the empty
row, preserving its negative position in the outcome witness. -/
theorem ApplicationPackageMatrixRel.singleton_failure
    {actualTypes : List Atom} {operatorType : Atom}
    (failure : ∀ result,
      ¬ApplicationPackageSuccessRel actualTypes operatorType result) :
    ApplicationPackageMatrixRel [actualTypes] [operatorType] [] := by
  refine ⟨[[]], List.Forall₂.cons ?_ List.Forall₂.nil, rfl⟩
  refine ⟨[none], List.Forall₂.cons ?_ List.Forall₂.nil, rfl⟩
  exact ApplicationPackageOutcomeRel.failure failure

/-! ## Exact priority relation -/

mutual

/-- Ordered package presentations selected for one atom.  Direct expression
annotations win, the R3 wrapper precedes ordinary expression lookup, R1 emits
every successful operator candidate, and `%Undefined%` is the fallback only
when the R1 scan is empty. -/
inductive RuntimeTypePackagesRel (space : Space) :
    Atom → List TypePackage → Prop where
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
      RuntimeTypePackagesRel space (.symbol name)
        (types.map publishedPackage)
  | symbolUndefined {name : String} :
      AnnotationTypesRel (.symbol name) space.atoms [] →
      RuntimeTypePackagesRel space (.symbol name)
        [publishedPackage Atom.undefinedType]
  | unit :
      RuntimeTypePackagesRel space (.expression [])
        [publishedPackage Atom.undefinedType]
  | stateValue {value : Atom} {content : TypePackage}
      {remaining : List TypePackage} :
      RuntimeTypePackagesRel space value (content :: remaining) →
      RuntimeTypePackagesRel space
        (.expression [.symbol "StateValue", value])
        [stateMonadPackage content]
  | expressionKnown {head : Atom} {tail types : List Atom} :
      NotStateValueShape head tail →
      AnnotationTypesRel (.expression (head :: tail)) space.atoms types →
      types ≠ [] →
      RuntimeTypePackagesRel space (.expression (head :: tail))
        (types.map publishedPackage)
  | expressionInferred {head : Atom} {tail : List Atom}
      {operatorPackages : List TypePackage}
      {argumentPackageLists : List (List TypePackage)}
      {rawArgumentLists : List (List Atom)} {rawOperators : List Atom}
      {avoid : List String}
      {freshArgumentChoices : List (List Atom)}
      {freshOperators : List Atom}
      {results : List TypePackage} :
      NotStateValueShape head tail →
      AnnotationTypesRel (.expression (head :: tail)) space.atoms [] →
      RuntimeTypePackagesRel space head operatorPackages →
      List.Forall₂ (RuntimeTypePackagesRel space)
        tail argumentPackageLists →
      argumentPackageLists.map observedTypes = rawArgumentLists →
      observedTypes operatorPackages = rawOperators →
      inferenceAvoidNames space (.expression (head :: tail))
        (rawOperators ++ rawArgumentLists.flatten) = avoid →
      List.Forall₂ (ArgumentAlphaVariantsRel avoid)
        (orderedCartesian rawArgumentLists) freshArgumentChoices →
      OperatorAlphaVariantsRel
        (avoid ++ TypeSubst.typeVarsList rawArgumentLists.flatten)
        rawOperators freshOperators →
      ApplicationPackageScopesSeparated
        freshArgumentChoices freshOperators →
      ApplicationPackageMatrixRel
        freshArgumentChoices freshOperators results →
      results ≠ [] →
      RuntimeTypePackagesRel space (.expression (head :: tail)) results
  | expressionUndefined {head : Atom} {tail : List Atom}
      {operatorPackages : List TypePackage}
      {argumentPackageLists : List (List TypePackage)}
      {rawArgumentLists : List (List Atom)} {rawOperators : List Atom}
      {avoid : List String}
      {freshArgumentChoices : List (List Atom)}
      {freshOperators : List Atom} :
      NotStateValueShape head tail →
      AnnotationTypesRel (.expression (head :: tail)) space.atoms [] →
      RuntimeTypePackagesRel space head operatorPackages →
      List.Forall₂ (RuntimeTypePackagesRel space)
        tail argumentPackageLists →
      argumentPackageLists.map observedTypes = rawArgumentLists →
      observedTypes operatorPackages = rawOperators →
      inferenceAvoidNames space (.expression (head :: tail))
        (rawOperators ++ rawArgumentLists.flatten) = avoid →
      List.Forall₂ (ArgumentAlphaVariantsRel avoid)
        (orderedCartesian rawArgumentLists) freshArgumentChoices →
      OperatorAlphaVariantsRel
        (avoid ++ TypeSubst.typeVarsList rawArgumentLists.flatten)
        rawOperators freshOperators →
      ApplicationPackageScopesSeparated
        freshArgumentChoices freshOperators →
      ApplicationPackageMatrixRel
        freshArgumentChoices freshOperators [] →
      RuntimeTypePackagesRel space (.expression (head :: tail))
        [publishedPackage Atom.undefinedType]

end

/-- Every exact-priority lookup selects at least one candidate package; the
undefined fallback is explicit rather than represented by an empty list. -/
theorem RuntimeTypePackagesRel.nonempty
    {space : Space} {atom : Atom} {packages : List TypePackage}
    (types : RuntimeTypePackagesRel space atom packages) : packages ≠ [] := by
  cases types <;> simp_all

/-! ## Alpha-exactness boundary -/

private def polymorphicNullarySpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "poly",
      .expression [.symbol "->", .var "t"]]]

private def polymorphicNullaryArrow : Atom :=
  .expression [.symbol "->", .var "t"]

private def polymorphicNullaryCall : Atom :=
  .expression [.symbol "poly"]

private def taggedTypeRename (tag name : String) : String :=
  tag ++ name

private theorem taggedTypeRename_injective (tag : String) :
    Function.Injective (taggedTypeRename tag) := by
  intro left right heq
  apply String.toList_injective
  have hlists := congrArg String.toList heq
  simp only [taggedTypeRename, String.toList_append] at hlists
  exact List.append_right_injective tag.toList hlists

private def polymorphicNullaryAvoid : List String :=
  inferenceAvoidNames polymorphicNullarySpace polymorphicNullaryCall
    [polymorphicNullaryArrow]

private theorem polymorphicNullaryVariant (tag : String)
    (htag : tag = "alpha#" ∨ tag = "beta#") :
    TypeCandidateAlphaVariantRel polymorphicNullaryAvoid
      polymorphicNullaryArrow
      (.expression [.symbol "->", .var (tag ++ "t")]) := by
  refine ⟨taggedTypeRename tag, taggedTypeRename_injective tag, ?_, ?_⟩
  · simp [polymorphicNullaryArrow, renameTypeVars, taggedTypeRename]
  · intro name hname
    simp [polymorphicNullaryArrow, TypeSubst.typeVars,
      TypeSubst.typeVarsList] at hname
    subst name
    rcases htag with rfl | rfl <;>
      simp [polymorphicNullaryAvoid, inferenceAvoidNames,
        polymorphicNullarySpace, polymorphicNullaryCall,
        polymorphicNullaryArrow, Space.ofList, TypeSubst.typeVars,
        TypeSubst.typeVarsList, taggedTypeRename]

private theorem polymorphicNullaryOperatorPackages :
    RuntimeTypePackagesRel polymorphicNullarySpace (.symbol "poly")
      [publishedPackage polymorphicNullaryArrow] := by
  exact RuntimeTypePackagesRel.symbolKnown
    (AnnotationTypesRel.hit AnnotationTypesRel.nil) (by simp)

private theorem polymorphicNullaryApplication (tag : String)
    (htag : tag = "alpha#" ∨ tag = "beta#") :
    RuntimeTypePackagesRel polymorphicNullarySpace polymorphicNullaryCall
      [inferredPackage [] (.var (tag ++ "t"))] := by
  apply RuntimeTypePackagesRel.expressionInferred
      (operatorPackages := [publishedPackage polymorphicNullaryArrow])
      (argumentPackageLists := [])
      (rawArgumentLists := [])
      (rawOperators := [polymorphicNullaryArrow])
      (avoid := polymorphicNullaryAvoid)
      (freshArgumentChoices := [[]])
      (freshOperators :=
        [.expression [.symbol "->", .var (tag ++ "t")]])
  · intro value
    exact Or.inl (by simp)
  · exact AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil
  · exact polymorphicNullaryOperatorPackages
  · exact List.Forall₂.nil
  · rfl
  · rfl
  · rfl
  · exact List.Forall₂.cons
      (ArgumentAlphaVariantsRel.nil _) List.Forall₂.nil
  · exact OperatorAlphaVariantsRel.cons
      (polymorphicNullaryVariant tag htag) OperatorAlphaVariantsRel.nil
  · simp [ApplicationPackageScopesSeparated, FreshFamiliesSeparated,
      AtomsAvoid, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · apply ApplicationPackageMatrixRel.singleton_success
    exact ApplicationPackageSuccessRel.mk
        (operatorType :=
          .expression [.symbol "->", .var (tag ++ "t")])
        (returnType := .var (tag ++ "t"))
        (expectedTypes := []) (actualTypes := [])
        (substitution := []) rfl
        (PresentationArgumentListMatchRel.nil [])
  · simp

/-- Exact runtime packages are intentionally not syntactically functional:
private inference names are alpha-scoped.  Candidate-set consumers must be
invariant under lawful package-local alpha variation rather than selecting a
convenient canonical spelling. -/
theorem runtimeTypePackages_not_syntactically_functional :
    ∃ left right,
      RuntimeTypePackagesRel polymorphicNullarySpace
        polymorphicNullaryCall left ∧
      RuntimeTypePackagesRel polymorphicNullarySpace
        polymorphicNullaryCall right ∧
      observedTypes left ≠ observedTypes right := by
  refine ⟨[inferredPackage [] (.var ("alpha#" ++ "t"))],
    [inferredPackage [] (.var ("beta#" ++ "t"))],
    polymorphicNullaryApplication "alpha#" (Or.inl rfl),
    polymorphicNullaryApplication "beta#" (Or.inr rfl), ?_⟩
  simp [observedTypes, inferredPackage]

/-! ## Boundary canaries -/

private theorem closedVariant (avoid : List String) (name : String) :
    TypeCandidateAlphaVariantRel avoid (.symbol name) (.symbol name) := by
  refine ⟨id, Function.injective_id,
    by simp [renameTypeVars], ?_⟩
  simp [TypeSubst.typeVars]

private def nullarySpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "constant",
      .expression [.symbol "->", .symbol "R"]]]

private theorem nullaryOperatorPackages :
    RuntimeTypePackagesRel nullarySpace (.symbol "constant")
      [publishedPackage
        (.expression [.symbol "->", .symbol "R"])] := by
  exact RuntimeTypePackagesRel.symbolKnown
    (AnnotationTypesRel.hit AnnotationTypesRel.nil) (by simp)

private theorem nullaryOperatorVariant :
    TypeCandidateAlphaVariantRel
      (inferenceAvoidNames nullarySpace (.expression [.symbol "constant"])
        [.expression [.symbol "->", .symbol "R"]])
      (.expression [.symbol "->", .symbol "R"])
      (.expression [.symbol "->", .symbol "R"]) := by
  refine ⟨id, Function.injective_id, ?_, ?_⟩
  · simp [renameTypeVars]
  · simp [TypeSubst.typeVars, TypeSubst.typeVarsList]

/-- Positive nullary canary: `(-> R)` is a function candidate and its
zero-argument application emits `R`. -/
theorem nullary_application_emits_return :
    RuntimeTypePackagesRel nullarySpace
      (.expression [.symbol "constant"])
      [publishedPackage (.symbol "R")] := by
  apply RuntimeTypePackagesRel.expressionInferred
      (operatorPackages :=
        [publishedPackage (.expression [.symbol "->", .symbol "R"])])
      (argumentPackageLists := [])
      (rawArgumentLists := [])
      (rawOperators := [.expression [.symbol "->", .symbol "R"]])
      (avoid := inferenceAvoidNames nullarySpace
        (.expression [.symbol "constant"])
        [.expression [.symbol "->", .symbol "R"]])
      (freshArgumentChoices := [[]])
      (freshOperators :=
        [.expression [.symbol "->", .symbol "R"]])
  · intro value
    exact Or.inl (by simp)
  · exact AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil
  · exact nullaryOperatorPackages
  · exact List.Forall₂.nil
  · rfl
  · rfl
  · rfl
  · exact List.Forall₂.cons
      (ArgumentAlphaVariantsRel.nil _) List.Forall₂.nil
  · exact OperatorAlphaVariantsRel.cons nullaryOperatorVariant
      OperatorAlphaVariantsRel.nil
  · simp [ApplicationPackageScopesSeparated, FreshFamiliesSeparated,
      AtomsAvoid, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · apply ApplicationPackageMatrixRel.singleton_success
    simpa [inferredPackage, publishedPackage,
        Spec.Type.Presentation.RuntimeTypePackage.published] using
        (ApplicationPackageSuccessRel.mk
          (operatorType :=
            .expression [.symbol "->", .symbol "R"])
          (returnType := .symbol "R")
          (expectedTypes := []) (actualTypes := [])
          (substitution := []) rfl
          (PresentationArgumentListMatchRel.nil []))
  · simp

/-! The repair-#7 scope canary uses the same source spelling `t` in an
operator annotation and an unrelated argument annotation. -/

private def scopedInferenceSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "g",
      .expression [.symbol "->", .var "t", .symbol "A", .symbol "R"]],
    .expression [.symbol ":", .symbol "b", .symbol "B"],
    .expression [.symbol ":", .symbol "k", .var "t"]]

private def scopedArgumentSubstitution : TypeSubst :=
  [("u", .symbol "A"), ("v", .symbol "B")]

private theorem scopedGPackages :
    RuntimeTypePackagesRel scopedInferenceSpace (.symbol "g")
      [publishedPackage
        (.expression [.symbol "->", .var "t", .symbol "A", .symbol "R"])] := by
  exact RuntimeTypePackagesRel.symbolKnown
    (AnnotationTypesRel.hit
      (AnnotationTypesRel.skip (by simp)
        (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil)))
    (by simp)

private theorem scopedBPackages :
    RuntimeTypePackagesRel scopedInferenceSpace (.symbol "b")
      [publishedPackage (.symbol "B")] := by
  exact RuntimeTypePackagesRel.symbolKnown
    (AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.hit
        (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil)))
    (by simp)

private theorem scopedKPackages :
    RuntimeTypePackagesRel scopedInferenceSpace (.symbol "k")
      [publishedPackage (.var "t")] := by
  exact RuntimeTypePackagesRel.symbolKnown
    (AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.skip (by simp)
        (AnnotationTypesRel.hit AnnotationTypesRel.nil)))
    (by simp)

private theorem scopedArgumentPackageLists :
    List.Forall₂ (RuntimeTypePackagesRel scopedInferenceSpace)
      [.symbol "b", .symbol "k"]
      [[publishedPackage (.symbol "B")],
        [publishedPackage (.var "t")]] := by
  exact List.Forall₂.cons scopedBPackages
    (List.Forall₂.cons scopedKPackages List.Forall₂.nil)

private theorem scopedBVariant (avoid : List String) :
    TypeCandidateAlphaVariantRel avoid (.symbol "B") (.symbol "B") :=
  closedVariant avoid "B"

private theorem scopedTtoUVariant :
    TypeCandidateAlphaVariantRel
      (inferenceAvoidNames scopedInferenceSpace
        (.expression [.symbol "g", .symbol "b", .symbol "k"])
        [.expression [.symbol "->", .var "t", .symbol "A", .symbol "R"],
          .symbol "B", .var "t"])
      (.var "t") (.var "u") := by
  refine ⟨Equiv.swap "t" "u", (Equiv.swap "t" "u").injective,
    by simp [renameTypeVars], ?_⟩
  simp [inferenceAvoidNames, scopedInferenceSpace, Space.ofList,
    TypeSubst.typeVars, TypeSubst.typeVarsList]

private theorem scopedArgumentsVariants :
    ArgumentAlphaVariantsRel
      (inferenceAvoidNames scopedInferenceSpace
        (.expression [.symbol "g", .symbol "b", .symbol "k"])
        [.expression [.symbol "->", .var "t", .symbol "A", .symbol "R"],
          .symbol "B", .var "t"])
      [.symbol "B", .var "t"] [.symbol "B", .var "u"] := by
  apply ArgumentAlphaVariantsRel.cons (scopedBVariant _)
  apply ArgumentAlphaVariantsRel.cons
  · simpa [TypeSubst.typeVars] using scopedTtoUVariant
  · exact ArgumentAlphaVariantsRel.nil _

private theorem scopedOperatorVariant :
    TypeCandidateAlphaVariantRel
      (inferenceAvoidNames scopedInferenceSpace
          (.expression [.symbol "g", .symbol "b", .symbol "k"])
          [.expression [.symbol "->", .var "t", .symbol "A", .symbol "R"],
            .symbol "B", .var "t"] ++
        TypeSubst.typeVarsList [.symbol "B", .var "t"])
      (.expression [.symbol "->", .var "t", .symbol "A", .symbol "R"])
      (.expression [.symbol "->", .var "v", .symbol "A", .symbol "R"]) := by
  refine ⟨Equiv.swap "t" "v", (Equiv.swap "t" "v").injective, ?_, ?_⟩
  · simp [renameTypeVars]
  · simp [inferenceAvoidNames, scopedInferenceSpace, Space.ofList,
      TypeSubst.typeVars, TypeSubst.typeVarsList]

private theorem scopedFirstMatch :
    CorePlusR2TypePresentationMatchRel []
      (.var "v") (.symbol "B") [("v", .symbol "B")] := by
  apply CorePlusR2TypePresentationMatchRel.reduced
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · simp [Atom.atomType]
  apply ReducedTypePresentationMatchRel.ordinary
      (resolvedLeft := .var "v") (resolvedRight := .symbol "B")
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [ReducedTypeLeafShape]
  · exact TypeSubst.apply_empty (.var "v")
  · exact TypeSubst.apply_empty (.symbol "B")
  · simpa [TypeSubst.bind, TypeSubst.apply, TypeSubst.lookup,
      TypeSubst.erase] using
      (AppliedReducedTypeMatchRel.bindLeft
        (substitution := []) (name := "v") (right := .symbol "B")
        (by simp [TypeSubst.typeVars]))

private theorem scopedSecondMatch :
    CorePlusR2TypePresentationMatchRel [("v", .symbol "B")]
      (.symbol "A") (.var "u") scopedArgumentSubstitution := by
  apply CorePlusR2TypePresentationMatchRel.reduced
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · simp [Atom.atomType]
  apply ReducedTypePresentationMatchRel.ordinary
      (resolvedLeft := .symbol "A") (resolvedRight := .var "u")
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [ReducedTypeLeafShape]
  · simp [TypeSubst.apply]
  · simp [TypeSubst.apply, TypeSubst.lookup]
  · simpa [scopedArgumentSubstitution, TypeSubst.bind,
      TypeSubst.apply, TypeSubst.lookup, TypeSubst.erase,
      TypeSubst.applyAssignment] using
      (AppliedReducedTypeMatchRel.bindRight
        (substitution := [("v", .symbol "B")])
        (left := .symbol "A") (name := "u")
        (by intro other; simp)
        (by simp [TypeSubst.typeVars]))

private theorem scopedArgumentsMatch :
    PresentationArgumentListMatchRel
      [.var "v", .symbol "A"] [.symbol "B", .var "u"]
      [] scopedArgumentSubstitution := by
  exact PresentationArgumentListMatchRel.cons scopedFirstMatch
    (PresentationArgumentListMatchRel.cons scopedSecondMatch
      (PresentationArgumentListMatchRel.nil scopedArgumentSubstitution))

/-- Repair-#7 canary: independent annotation variables with the same source
spelling are scoped apart before the application fold, so `(g b k)` infers
`R` rather than creating the false conjunction `t = B` and `t = A`. -/
theorem independent_annotation_variables_infer_return :
    RuntimeTypePackagesRel scopedInferenceSpace
      (.expression [.symbol "g", .symbol "b", .symbol "k"])
      [inferredPackage scopedArgumentSubstitution (.symbol "R")] := by
  apply RuntimeTypePackagesRel.expressionInferred
      (operatorPackages :=
        [publishedPackage
          (.expression [.symbol "->", .var "t", .symbol "A", .symbol "R"])])
      (argumentPackageLists :=
        [[publishedPackage (.symbol "B")],
          [publishedPackage (.var "t")]])
      (rawArgumentLists := [[.symbol "B"], [.var "t"]])
      (rawOperators :=
        [.expression [.symbol "->", .var "t", .symbol "A", .symbol "R"]])
      (avoid := inferenceAvoidNames scopedInferenceSpace
        (.expression [.symbol "g", .symbol "b", .symbol "k"])
        [.expression [.symbol "->", .var "t", .symbol "A", .symbol "R"],
          .symbol "B", .var "t"])
      (freshArgumentChoices := [[.symbol "B", .var "u"]])
      (freshOperators :=
        [.expression [.symbol "->", .var "v", .symbol "A", .symbol "R"]])
  · intro value
    exact Or.inl (by simp)
  · exact AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.skip (by simp)
        (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil))
  · exact scopedGPackages
  · exact scopedArgumentPackageLists
  · rfl
  · rfl
  · rfl
  · exact List.Forall₂.cons scopedArgumentsVariants List.Forall₂.nil
  · exact OperatorAlphaVariantsRel.cons scopedOperatorVariant
      OperatorAlphaVariantsRel.nil
  · simp [ApplicationPackageScopesSeparated, FreshFamiliesSeparated,
      AtomsAvoid, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · exact ApplicationPackageMatrixRel.singleton_success
      (ApplicationPackageSuccessRel.mk rfl scopedArgumentsMatch)
  · simp

private def malformedArrowSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "malformed",
      .expression [.symbol "->"]]]

private theorem malformedOperatorPackages :
    RuntimeTypePackagesRel malformedArrowSpace (.symbol "malformed")
      [publishedPackage (.expression [.symbol "->"])] := by
  exact RuntimeTypePackagesRel.symbolKnown
    (AnnotationTypesRel.hit AnnotationTypesRel.nil) (by simp)

private theorem malformedOperatorVariant :
    TypeCandidateAlphaVariantRel
      (inferenceAvoidNames malformedArrowSpace
        (.expression [.symbol "malformed"])
        [.expression [.symbol "->"]])
      (.expression [.symbol "->"])
      (.expression [.symbol "->"]) := by
  refine ⟨id, Function.injective_id,
    by simp [renameTypeVars], ?_⟩
  simp [TypeSubst.typeVars, TypeSubst.typeVarsList]

private theorem malformedArrowNoSuccess (result : TypePackage) :
    ¬ApplicationPackageSuccessRel []
      (.expression [.symbol "->"]) result := by
  intro hsuccess
  cases hsuccess with
  | @mk _ returnType expectedTypes _ _ hshape _ =>
      have := congrArg (fun atom => match atom with
        | .expression atoms => atoms.length
        | _ => 0) hshape
      simp at this

/-- Negative nullary boundary: bare `(->)` has no return component and
therefore contributes no inferred package; the ordinary undefined fallback
remains. -/
theorem bare_arrow_uses_undefined_fallback :
    RuntimeTypePackagesRel malformedArrowSpace
      (.expression [.symbol "malformed"])
      [publishedPackage Atom.undefinedType] := by
  apply RuntimeTypePackagesRel.expressionUndefined
      (operatorPackages := [publishedPackage (.expression [.symbol "->"])])
      (argumentPackageLists := [])
      (rawArgumentLists := [])
      (rawOperators := [.expression [.symbol "->"]])
      (avoid := inferenceAvoidNames malformedArrowSpace
        (.expression [.symbol "malformed"])
        [.expression [.symbol "->"]])
      (freshArgumentChoices := [[]])
      (freshOperators := [.expression [.symbol "->"]])
  · intro value
    exact Or.inl (by simp)
  · exact AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil
  · exact malformedOperatorPackages
  · exact List.Forall₂.nil
  · rfl
  · rfl
  · rfl
  · exact List.Forall₂.cons
      (ArgumentAlphaVariantsRel.nil _) List.Forall₂.nil
  · exact OperatorAlphaVariantsRel.cons malformedOperatorVariant
      OperatorAlphaVariantsRel.nil
  · simp [ApplicationPackageScopesSeparated, FreshFamiliesSeparated,
      AtomsAvoid, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · exact ApplicationPackageMatrixRel.singleton_failure
      malformedArrowNoSuccess

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
