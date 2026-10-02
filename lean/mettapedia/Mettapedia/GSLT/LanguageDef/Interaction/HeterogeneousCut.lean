import Mettapedia.GSLT.LanguageDef.Interaction.Migration
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability

/-!
# Reading a cut where the contact is heterogeneous

A rule may bring two operands together in an ordered binary constructor whose
operands have different sorts.  Such a constructor is not a contact, and the
language is not thereby interactive.  One can still read the rule as if it
were a cut: name the two operands, and observe a residual in the contractum.

The reading supports one question, on the data axis only: does the observed
residual read anything the environment brought?  If not, it is the same
whatever the environment was.  If so, the authored contractum reads the
environment too, because the residual is one of its subterms.

A reading is anchored in the language: it names a rule of the language, whose
left side is a declared constructor applied to the two operands.  That
constructor has two operands that are not both of its result sort, and the
rule read is the interaction rule of no interactive presentation of the
language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- The variables of the environment operand that the program operand does
not share. -/
def environmentOwned (program environment : Pattern) : List String :=
  environment.schemaVariables.filter fun name => !program.schemaVariables.contains name

/-- The observed residual mentions a variable the environment brought. -/
def readsOwned (program environment observed : Pattern) : Bool :=
  (environmentOwned program environment).any fun name =>
    observed.schemaVariables.contains name

/-- The position of an observed residual on the data axis: binding when it
reads the environment, none when it does not. -/
def dataModeOf (program environment observed : Pattern) : MigrationMode :=
  if readsOwned program environment observed then .binding else .none

/-- A rule read as a cut across an ordered binary constructor that is not a
same-sort contact. -/
structure HeterogeneousCutReading (language : LanguageDef) where
  rule : RewriteRule
  ruleMember : rule ∈ language.rewrites
  contact : GrammarRule
  contactMember : contact ∈ language.terms
  sort : TypeDecl
  /-- The constructor is an ordered binary contact at its result sort. -/
  ordered : coreContactRepresentation? sort contact = some .binary
  /-- At no sort are its two operands and its result of one sort. -/
  heterogeneous : ∀ candidate : TypeDecl, contactRepresentation? candidate contact = none
  program : Pattern
  environment : Pattern
  /-- The rule's left side is the constructor applied to the two operands. -/
  source : rule.left = .apply contact.label [program, environment]
  /-- The residual observed. -/
  observed : Pattern
  position : OneHoleContext
  /-- The observed residual is the subterm of the contractum at that position. -/
  selects : position.fill observed = rule.right

/-- Filling a context keeps every schema variable of the inserted pattern. -/
theorem mem_schemaVariables_fill (context : OneHoleContext) {pattern : Pattern}
    {name : String} (membership : name ∈ pattern.schemaVariables) :
    name ∈ (context.fill pattern).schemaVariables := by
  induction context with
  | hole => exact membership
  | apply constructor before inner after recurse =>
      simp only [OneHoleContext.fill, Pattern.schemaVariables,
        Pattern.schemaVariablesList_eq_flatMap, List.mem_flatMap]
      exact ⟨inner.fill pattern, by simp, recurse⟩
  | lambda binder inner recurse =>
      simpa [OneHoleContext.fill, Pattern.schemaVariables] using recurse
  | multiLambda arity binders inner recurse =>
      simpa [OneHoleContext.fill, Pattern.schemaVariables] using recurse
  | substBody inner replacement recurse =>
      simpa [OneHoleContext.fill, Pattern.schemaVariables] using Or.inl recurse
  | substReplacement body inner recurse =>
      simpa [OneHoleContext.fill, Pattern.schemaVariables] using Or.inr recurse
  | collection collectionType before inner after rest recurse =>
      simp only [OneHoleContext.fill, Pattern.schemaVariables,
        Pattern.schemaVariablesList_eq_flatMap, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨inner.fill pattern, by simp, recurse⟩

namespace HeterogeneousCutReading

variable {language : LanguageDef}

/-- The variables the environment operand brings that the program operand
does not share. -/
def environmentVariables (reading : HeterogeneousCutReading language) : List String :=
  environmentOwned reading.program reading.environment

/-- The observed residual mentions a variable the environment brought. -/
def readsEnvironment (reading : HeterogeneousCutReading language) : Bool :=
  readsOwned reading.program reading.environment reading.observed

/-- The position of the observed residual on the data axis. -/
def dataMode (reading : HeterogeneousCutReading language) : MigrationMode :=
  dataModeOf reading.program reading.environment reading.observed

/-- A residual that does not read the environment is the same whatever the
environment brought: two matches that differ only on the environment's own
variables instantiate it to one term. -/
theorem observed_independent_of_environment
    (reading : HeterogeneousCutReading language)
    (silent : reading.readsEnvironment = false)
    {first second : Bindings}
    (agree : ∀ name, name ∉ reading.environmentVariables →
      first.find? (fun entry => entry.1 == name) =
        second.find? (fun entry => entry.1 == name)) :
    applyBindings first reading.observed = applyBindings second reading.observed := by
  apply applyBindings_congr
  intro name membership
  apply agree
  intro environmental
  have reads : reading.readsEnvironment = true := by
    simp only [readsEnvironment, readsOwned, List.any_eq_true, List.contains_iff_mem,
      Pattern.schemaVariables_eq_freeFvarNames]
    exact ⟨name, by simpa [environmentVariables, environmentOwned,
      Pattern.schemaVariables_eq_freeFvarNames] using environmental, membership⟩
  rw [silent] at reads
  cases reads

/-- A reading does not make its language interactive through that contact:
the constructor it reads across is not a same-sort contact at any sort, so no
interactive presentation selects it. -/
theorem contact_not_selected (reading : HeterogeneousCutReading language)
    (presentation : InteractivePresentation) :
    presentation.contactConstructor.1 ≠ reading.contact := by
  intro same
  have present := presentation.representsContact
  rw [same, reading.heterogeneous] at present
  cases present

/-! ## The residual is part of the authored contractum -/

/-- Every variable of the observed residual is a variable of the authored
contractum. -/
theorem observed_variables_in_contractum (reading : HeterogeneousCutReading language)
    {name : String} (membership : name ∈ reading.observed.schemaVariables) :
    name ∈ reading.rule.right.schemaVariables := by
  rw [← reading.selects]
  exact mem_schemaVariables_fill reading.position membership

/-- A reading in binding mode has a residual that reads the environment. -/
theorem readsEnvironment_of_binding (reading : HeterogeneousCutReading language)
    (binding : reading.dataMode = .binding) : reading.readsEnvironment = true := by
  cases reads : reading.readsEnvironment with
  | true => rfl
  | false =>
      have mode : reading.dataMode = .none := by
        have silent : readsOwned reading.program reading.environment reading.observed = false :=
          reads
        simp [dataMode, dataModeOf, silent]
      rw [mode] at binding
      cases binding

/-- **A residual that reads the environment makes the authored contractum
read it**: some variable that only the environment operand binds occurs in
the right side of the rule. -/
theorem contractum_reads_environment (reading : HeterogeneousCutReading language)
    (reads : reading.readsEnvironment = true) :
    ∃ name ∈ reading.environmentVariables, name ∈ reading.rule.right.schemaVariables := by
  simp only [readsEnvironment, readsOwned, List.any_eq_true, List.contains_iff_mem] at reads
  obtain ⟨name, owned, observed⟩ := reads
  exact ⟨name, owned, reading.observed_variables_in_contractum observed⟩

/-! ## The constructor read across -/

/-- **The constructor read across has two operands that are not both of its
result sort.**  This is what excludes it as a contact. -/
theorem operands_not_both_of_sort (reading : HeterogeneousCutReading language) :
    ∃ first firstType second secondType,
      reading.contact.params = [.simple first firstType, .simple second secondType] ∧
        ¬ (firstType = .base reading.sort.name ∧ secondType = .base reading.sort.name) := by
  have ordered := reading.ordered
  unfold coreContactRepresentation? at ordered
  split at ordered
  next category =>
    split at ordered
    next first firstType second secondType parameters =>
      refine ⟨first, firstType, second, secondType, parameters, ?_⟩
      rintro ⟨rfl, rfl⟩
      have excluded := reading.heterogeneous reading.sort
      simp [contactRepresentation?, category, parameters] at excluded
    next => cases ordered
    next => cases ordered
  next => cases ordered

/-- The constructor read across shares its label with the contact of no
interactive presentation of the language: a validated language declares one
constructor per label, and the constructor read across is a contact at no
sort. -/
theorem contact_label_ne (presentation : InteractivePresentation)
    (reading : HeterogeneousCutReading presentation.presentation.language) :
    reading.contact.label ≠ presentation.contactConstructor.1.label := by
  intro sameLabel
  have labels := LanguageDef.constructorLabels_nodup_of_validate_eq_nil _
    presentation.presentation.valid
  exact reading.contact_not_selected presentation
    (List.inj_on_of_nodup_map labels reading.contactMember presentation.contactConstructor.2
      sameLabel).symm

/-- **The rule read is the interaction rule of no interactive presentation
of its language.**  An interaction rule is headed by a same-sort contact, and
the rule read is headed by a constructor that is a contact at no sort. -/
theorem rule_not_interaction (presentation : InteractivePresentation)
    (reading : HeterogeneousCutReading presentation.presentation.language) :
    presentation.interactionRewrite.1 ≠ reading.rule := by
  intro same
  have headed := presentation.interactionHeaded
  rw [same, reading.source] at headed
  cases representation : presentation.contactRepresentation with
  | binary =>
      rw [representation] at headed
      exact reading.contact_label_ne presentation headed
  | collection kind =>
      rw [representation] at headed
      exact headed

end HeterogeneousCutReading

end Mettapedia.GSLT.LanguageDef
