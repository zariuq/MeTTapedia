import Mettapedia.Languages.Megalodon.EnvironmentDependency

/-!
# Executable checks for native environment dependency manifests

The checks inspect a finite set of existing native environment queries. Agreement
compares complete lookup results, including absence and definition transparency.
Closure follows each selected definition body and known proposition. Neither
check validates the declarations as mathematical axioms or claims that the
manifest is minimal. Together they decide sufficient premises for the existing
native frame theorems, not a new evaluator or proof kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.EnvironmentDependencyCheck

open MathdataKernel NativeSupport EnvironmentDependency

/-- A single native lookup has exactly the same result in both environments. -/
def queryAgrees (source target : Environment) : Dependency → Prop
  | .termName name => target.lookupTerm? name = source.lookupTerm? name
  | .primitive index => target.primitives[index]? = source.primitives[index]?
  | .knownName name => target.lookupKnown? name = source.lookupKnown? name

instance (source target : Environment) (dependency : Dependency) :
    Decidable (queryAgrees source target dependency) := by
  cases dependency <;> unfold queryAgrees <;> infer_instance

/-- Dependencies exposed by the selected lookup, not by shadowed declarations.
Absent lookups and declarations without bodies expose no further dependencies. -/
def declaredSupport (environment : Environment) : Dependency → Support
  | .termName name =>
      match environment.lookupTerm? name with
      | none => ∅
      | some declaration =>
          match declaration.definition with
          | none => ∅
          | some body => termSupport body
  | .primitive _ => ∅
  | .knownName name =>
      match environment.lookupKnown? name with
      | none => ∅
      | some proposition => termSupport proposition

/-- Finite, executable comparison of all queries in the manifest. -/
def agreementCheck (source target : Environment) (support : Support) : Bool :=
  decide (∀ dependency ∈ support, queryAgrees source target dependency)

/-- Finite, executable closure check, including names reached inside bodies. -/
def closureCheck (environment : Environment) (support : Support) : Bool :=
  decide (∀ dependency ∈ support, declaredSupport environment dependency ⊆ support)

/-- Check the sufficient local premises for exact native computation framing. -/
def frameCheck (source target : Environment) (support : Support) : Bool :=
  agreementCheck source target support && closureCheck source support

theorem agreement_iff_queries (source target : Environment) (support : Support) :
    Agreement source target support ↔
      ∀ dependency ∈ support, queryAgrees source target dependency := by
  constructor
  · intro agreement dependency member
    cases dependency with
    | termName name => exact agreement.term member
    | primitive index => exact agreement.primitive member
    | knownName name => exact agreement.known member
  · intro agrees
    exact ⟨fun member => agrees (.termName _) member,
      fun member => agrees (.primitive _) member,
      fun member => agrees (.knownName _) member⟩

theorem closed_iff_declaredSupport (environment : Environment) (support : Support) :
    Closed environment support ↔
      ∀ dependency ∈ support, declaredSupport environment dependency ⊆ support := by
  constructor
  · intro closed dependency member
    cases dependency with
    | termName name =>
        cases lookup : environment.lookupTerm? name with
        | none => simp [declaredSupport, lookup]
        | some declaration =>
            cases definition : declaration.definition with
            | none => simp [declaredSupport, lookup, definition]
            | some body =>
                simpa only [declaredSupport, lookup, definition] using
                  closed.body member lookup definition
    | primitive index => simp [declaredSupport]
    | knownName name =>
        cases lookup : environment.lookupKnown? name with
        | none => simp [declaredSupport, lookup]
        | some proposition =>
            simpa only [declaredSupport, lookup] using closed.known member lookup
  · intro closed
    constructor
    · intro name declaration body member lookup definition
      simpa only [declaredSupport, lookup, definition] using closed (.termName name) member
    · intro name proposition member lookup
      simpa only [declaredSupport, lookup] using closed (.knownName name) member

@[simp] theorem agreementCheck_iff (source target : Environment) (support : Support) :
    agreementCheck source target support = true ↔ Agreement source target support := by
  simp only [agreementCheck, decide_eq_true_eq, agreement_iff_queries]

@[simp] theorem closureCheck_iff (environment : Environment) (support : Support) :
    closureCheck environment support = true ↔ Closed environment support := by
  simp only [closureCheck, decide_eq_true_eq, closed_iff_declaredSupport]

@[simp] theorem frameCheck_iff (source target : Environment) (support : Support) :
    frameCheck source target support = true ↔
      Agreement source target support ∧ Closed source support := by
  simp only [frameCheck, Bool.and_eq_true, agreementCheck_iff, closureCheck_iff]

/-- An accepted manifest preserves successful results and normalization fuel failure. -/
theorem normalize_eq_of_frameCheck {source target : Environment} {support : Support}
    (checked : frameCheck source target support = true)
    {term : Tm} {fuel : Nat} (supported : termSupport term ⊆ support) :
    normalize target fuel term = normalize source fuel term := by
  obtain ⟨agreement, closed⟩ := (frameCheck_iff source target support).mp checked
  exact normalize_frame agreement closed supported

private def termDeclarationsSupport : List TermDecl → Support
  | [] => ∅
  | declaration :: rest =>
      (match declaration.definition with
        | none => ∅
        | some body => termSupport body) ∪ termDeclarationsSupport rest

private def knownDeclarationsSupport : List KnownDecl → Support
  | [] => ∅
  | declaration :: rest => termSupport declaration.proposition ∪ knownDeclarationsSupport rest

private theorem termSupport_subset_termDeclarationsSupport
    {declarations : List TermDecl} {name : Name} {declaration : TermDecl} {body : Tm}
    (lookup : lookupTermList? declarations name = some declaration)
    (definition : declaration.definition = some body) :
    termSupport body ⊆ termDeclarationsSupport declarations := by
  induction declarations with
  | nil => cases lookup
  | cons first rest ih =>
      simp only [lookupTermList?] at lookup
      split at lookup
      · cases lookup
        simpa only [termDeclarationsSupport, definition] using
          (Finset.subset_union_left : termSupport body ⊆
            termSupport body ∪ termDeclarationsSupport rest)
      · exact (ih lookup).trans Finset.subset_union_right

private theorem termSupport_subset_knownDeclarationsSupport
    {declarations : List KnownDecl} {name : Name} {proposition : Tm}
    (lookup : lookupKnownList? declarations name = some proposition) :
    termSupport proposition ⊆ knownDeclarationsSupport declarations := by
  induction declarations with
  | nil => cases lookup
  | cons first rest ih =>
      simp only [lookupKnownList?] at lookup
      split at lookup
      · cases lookup
        exact Finset.subset_union_left
      · exact (ih lookup).trans Finset.subset_union_right

/-- A finite closed overapproximation of the requested support. It includes the
dependencies of every stored body and known proposition, including unused and
shadowed declarations. This is not a least or reachability-based closure. -/
def conservativeSupport (environment : Environment) (requested : Support) : Support :=
  requested ∪ termDeclarationsSupport environment.terms ∪
    knownDeclarationsSupport environment.known

theorem subset_conservativeSupport (environment : Environment) (requested : Support) :
    requested ⊆ conservativeSupport environment requested :=
  Finset.subset_union_left.trans Finset.subset_union_left

theorem conservativeSupport_closed (environment : Environment) (requested : Support) :
    Closed environment (conservativeSupport environment requested) where
  body _ lookup definition :=
    (termSupport_subset_termDeclarationsSupport lookup definition).trans
      (Finset.subset_union_right.trans Finset.subset_union_left)
  known _ lookup :=
    (termSupport_subset_knownDeclarationsSupport lookup).trans Finset.subset_union_right

@[simp] theorem conservativeSupport_closureCheck
    (environment : Environment) (requested : Support) :
    closureCheck environment (conservativeSupport environment requested) = true :=
  (closureCheck_iff _ _).mpr (conservativeSupport_closed environment requested)

/-- Every finite native environment has a computably supplied closed manifest
covering a requested finite support. -/
theorem exists_closed_support (environment : Environment) (requested : Support) :
    ∃ support, requested ⊆ support ∧ closureCheck environment support = true :=
  ⟨conservativeSupport environment requested, subset_conservativeSupport _ _,
    conservativeSupport_closureCheck _ _⟩

namespace Examples

def source : Environment where
  primitives := [.prop]
  terms := [⟨"x", .prop, some (.named "y")⟩, ⟨"y", .prop, none⟩]
  known := [⟨"k", .named "x"⟩]

/-- The new declaration is not queried, even though its body mentions a new name. -/
def extended : Environment :=
  { source with terms := source.terms ++ [⟨"unrelated", .prop, some (.named "outside")⟩] }

def support : Support :=
  {.knownName "k", .termName "x", .termName "y", .primitive 0}

theorem selected_extension_accepted : frameCheck source extended support = true := by decide

theorem selected_definition_chain :
    declaredSupport source (.knownName "k") = {.termName "x"} ∧
      declaredSupport source (.termName "x") = {.termName "y"} := by decide

theorem unselected_body_need_not_be_closed :
    Dependency.termName "outside" ∉ support ∧
      closureCheck extended support = true := by decide

theorem missing_definition_dependency_rejected :
    closureCheck source {.knownName "k", .termName "x"} = false := by decide

theorem missing_known_dependency_rejected :
    closureCheck source {.knownName "k"} = false := by decide

/-- Missing entries are compared, not silently skipped. -/
theorem absent_term_lookup_rejected :
    agreementCheck source extended {.termName "unrelated"} = false := by decide

theorem absent_primitive_lookup_rejected :
    agreementCheck source { source with primitives := [.prop, .prop] }
      {.primitive 1} = false := by decide

theorem absent_known_lookup_rejected :
    agreementCheck source { source with known := source.known ++ [⟨"new", .named "y"⟩] }
      {.knownName "new"} = false := by decide

/-- Agreement on a missing entry is valid framing, not a declaration-validity claim. -/
theorem equally_absent_lookup_accepted :
    frameCheck source extended {.termName "missing"} = true := by decide

theorem equally_absent_lookup_still_untypable :
    inferTerm source 0 [] (.named "missing") = none ∧
      inferTerm extended 0 [] (.named "missing") = none := by decide

theorem changed_transparency_rejected :
    agreementCheck source { source with terms := [⟨"x", .prop, none⟩] }
      {.termName "x"} = false := by decide

theorem changed_definition_body_rejected :
    agreementCheck source { source with terms := [⟨"x", .prop, some (.prim 0)⟩] }
      {.termName "x"} = false := by decide

theorem changed_known_proposition_rejected :
    agreementCheck source { source with known := [⟨"k", .named "y"⟩] }
      {.knownName "k"} = false := by decide

theorem changed_primitive_type_rejected :
    agreementCheck source { source with primitives := [.base 0] }
      {.primitive 0} = false := by decide

/-- Lookup selection follows the native first-match rule, including shadowing. -/
theorem shadowed_declaration_ignored :
    frameCheck source
      { source with terms := source.terms ++ [⟨"x", .prop, some (.named "outside")⟩] }
      support = true := by decide

/-- A smaller closed manifest may omit dependencies retained by the conservative one. -/
theorem conservativeSupport_not_least :
    closureCheck extended {.termName "y"} = true ∧
      Dependency.termName "outside" ∈ conservativeSupport extended {.termName "y"} ∧
      Dependency.termName "outside" ∉ ({.termName "y"} : Support) := by decide

theorem accepted_manifest_frames_normalization (fuel : Nat) :
    normalize extended fuel (.named "x") = normalize source fuel (.named "x") :=
  normalize_eq_of_frameCheck selected_extension_accepted (by decide)

end Examples

#print axioms agreementCheck_iff
#print axioms closureCheck_iff
#print axioms frameCheck_iff
#print axioms normalize_eq_of_frameCheck
#print axioms conservativeSupport_closed
#print axioms exists_closed_support
#print axioms Examples.selected_extension_accepted
#print axioms Examples.missing_definition_dependency_rejected

end Mettapedia.Languages.Megalodon.EnvironmentDependencyCheck
