import Mettapedia.GSLT.LanguageDef.InteractionCut
import Mettapedia.OSLF.MeTTaIL.BindingAgreement
import Mettapedia.OSLF.MeTTaIL.SchemaVariables

/-!
# What a contraction moves

An interaction cut contracts two introductions into a term built from their
continuations.  The instances differ in what the contraction does to those
continuations, and the difference is read here from the authored rule alone:
from the path between the root of each side of the rule and each occurrence
of a continuation variable.

* **Binding.**  A continuation occurs under a substitution: its instance is
  rewritten, and what it receives is the replacement of that substitution.
* **Spatial restructuring.**  No continuation is rewritten, but the reduction
  positions above a continuation differ between the redex and the contractum:
  something that was already running is running somewhere else.
* **Interface composition.**  No continuation is rewritten or relocated, and
  in the contractum the continuations sit beneath a constructor position that
  is neither an operand of the contact nor a reduction position: they are
  joined again, under a new guard.
* **None.**  The continuations are set free at the contact, as they were.

A reduction position is an argument position beneath which an authored
contextual rule reduces.  It is the only notion of place used: a constructor
position is a location when the language says reduction happens there, and a
guard otherwise.

In every mode but binding, each continuation appears in the reduct exactly as
it was matched (`released_verbatim`).  Under a substitution it does not.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- How a contraction treats what the two continuations hold. -/
inductive MigrationMode where
  /-- Pure release: both continuations are set free at the contact. -/
  | none
  /-- A continuation is instantiated through a binder. -/
  | binding
  /-- Nothing is instantiated; the locations around the continuations change. -/
  | spatial
  /-- Nothing is instantiated or relocated; the continuations are joined again
  beneath a new guard. -/
  | interface
deriving DecidableEq, Repr

/-! ## Places where a subterm is running -/

/-- The argument position a one-hole frame reduces beneath, when the frame is
a single constructor position, possibly under that position's binder. -/
def argumentPosition? : OneHoleContext → Option (String × Nat)
  | .apply label before .hole _ => some (label, before.length)
  | .apply label before (.lambda _ .hole) _ => some (label, before.length)
  | _ => none

/-- The argument positions beneath which an authored contextual rule reduces. -/
def reductionPositions (language : LanguageDef) : List (String × Nat) :=
  language.rewrites.flatMap fun rule =>
    (compileRuleContexts rule).filterMap argumentPosition?

/-- A reduction position is exactly a constructor position that some authored
rule names as the frame of a reduction hypothesis. -/
theorem mem_reductionPositions_iff {language : LanguageDef} {position : String × Nat} :
    position ∈ reductionPositions language ↔
      ∃ rule ∈ language.rewrites, ∃ frame : OneHoleContext,
        RuleAuthorizesContext rule frame ∧ argumentPosition? frame = some position := by
  simp only [reductionPositions, List.mem_flatMap, List.mem_filterMap,
    mem_compileRuleContexts_iff_authorized]

/-! ## Reading the path to a continuation -/

/-- Every occurrence of the schema variable sits under no substitution. -/
def releasedVerbatim (pattern : Pattern) (name : String) : Bool :=
  (zippersAt (.fvar name) pattern).all fun context => context.substitutionFree

/-- Some occurrence of the schema variable sits in the body of a substitution
whose replacement mentions one of the listed variables. -/
def bindsInto (pattern : Pattern) (name : String) (sources : List String) : Bool :=
  (zippersAt (.fvar name) pattern).any fun context =>
    context.substitutions.any fun replacement =>
      sources.any fun source => replacement.schemaVariables.contains source

/-- The reduction positions above each occurrence of the schema variable. -/
def locationsAbove (locations : List (String × Nat)) (pattern : Pattern)
    (name : String) : List (List (String × Nat)) :=
  (zippersAt (.fvar name) pattern).map fun context =>
    context.argumentFrames.filter fun frame => locations.contains frame

/-- The guards above each occurrence of the schema variable: argument
positions that are neither reduction positions nor operands of the contact. -/
def guardsAbove (locations : List (String × Nat)) (contactLabel : Option String)
    (pattern : Pattern) (name : String) : List (List (String × Nat)) :=
  (zippersAt (.fvar name) pattern).map fun context =>
    context.argumentFrames.filter fun frame =>
      !locations.contains frame && some frame.1 != contactLabel

/-- **Binding is substitution through a binder.**  When a variable is bound
into from a list of sources, the pattern is a context around a substitution
node whose body holds the variable and whose replacement mentions a source. -/
theorem exists_subst_of_bindsInto {pattern : Pattern} {name : String}
    {sources : List String} (binds : bindsInto pattern name sources = true) :
    ∃ (outer inner : OneHoleContext) (replacement : Pattern),
      pattern = outer.fill (.subst (inner.fill (.fvar name)) replacement) ∧
        ∃ source ∈ sources, source ∈ replacement.freeFvarNames := by
  simp only [bindsInto, List.any_eq_true, List.contains_iff_mem,
    Pattern.schemaVariables_eq_freeFvarNames] at binds
  obtain ⟨context, occurrence, replacement, substituted, source, listed, mentioned⟩ := binds
  have selected := (zippersAt_sound occurrence).fill_eq
  obtain ⟨outer, inner, equation⟩ :=
    OneHoleContext.exists_subst_of_mem_substitutions substituted (.fvar name)
  exact ⟨outer, inner, replacement, by rw [← selected, equation], source, listed, mentioned⟩

/-- **Release.**  A variable every occurrence of which sits under no
substitution appears, in each instance of the pattern, exactly as it was
bound: the instance is the instantiated context around the bound term. -/
theorem released_verbatim {pattern : Pattern} {name : String}
    (released : releasedVerbatim pattern name = true)
    (bindings : Bindings) {context : OneHoleContext}
    (occurrence : context ∈ zippersAt (.fvar name) pattern) :
    applyBindings bindings pattern =
      (context.instantiate bindings).fill (applyBindings bindings (.fvar name)) := by
  simp only [releasedVerbatim, List.all_eq_true] at released
  have selected := (zippersAt_sound occurrence).fill_eq
  rw [← selected]
  exact OneHoleContext.applyBindings_fill bindings context (released context occurrence) _

/-! ## The mode of a contraction -/

/-- The part of a rule that migration is read from: its two sides, the two
continuation variables, and the places of the language. -/
structure ContractionSchema where
  redex : Pattern
  contractum : Pattern
  programContinuation : String
  environmentContinuation : String
  /-- The label of a binary contact.  A collection contact has no argument
  position. -/
  contactLabel : Option String
  locations : List (String × Nat)

namespace ContractionSchema

/-- Both continuations are released as they were matched. -/
def released (schema : ContractionSchema) : Bool :=
  releasedVerbatim schema.contractum schema.programContinuation &&
    releasedVerbatim schema.contractum schema.environmentContinuation

/-- The reduction positions above a continuation differ between the two
sides of the rule. -/
def relocated (schema : ContractionSchema) : Bool :=
  locationsAbove schema.locations schema.redex schema.programContinuation !=
      locationsAbove schema.locations schema.contractum schema.programContinuation ||
    locationsAbove schema.locations schema.redex schema.environmentContinuation !=
      locationsAbove schema.locations schema.contractum schema.environmentContinuation

/-- In the contractum a continuation sits beneath a guard. -/
def guarded (schema : ContractionSchema) : Bool :=
  (guardsAbove schema.locations schema.contactLabel schema.contractum
      schema.programContinuation).any (fun frames => !frames.isEmpty) ||
    (guardsAbove schema.locations schema.contactLabel schema.contractum
      schema.environmentContinuation).any (fun frames => !frames.isEmpty)

/-- The migration mode of a contraction. -/
def mode (schema : ContractionSchema) : MigrationMode :=
  if !schema.released then .binding
  else if schema.relocated then .spatial
  else if schema.guarded then .interface
  else .none

/-- Exactly the binding mode instantiates a continuation. -/
theorem mode_eq_binding_iff (schema : ContractionSchema) :
    schema.mode = .binding ↔ schema.released = false := by
  unfold mode
  cases schema.released <;> cases schema.relocated <;> cases schema.guarded <;> simp

/-- In every other mode the program continuation appears in each instance of
the contractum exactly as it was matched. -/
theorem program_released_of_mode_ne_binding (schema : ContractionSchema)
    (notBinding : schema.mode ≠ .binding) (bindings : Bindings)
    {context : OneHoleContext}
    (occurrence : context ∈
      zippersAt (.fvar schema.programContinuation) schema.contractum) :
    applyBindings bindings schema.contractum =
      (context.instantiate bindings).fill
        (applyBindings bindings (.fvar schema.programContinuation)) := by
  have released : schema.released = true := by
    cases value : schema.released
    · exact absurd ((mode_eq_binding_iff schema).mpr value) notBinding
    · rfl
  simp only [ContractionSchema.released, Bool.and_eq_true] at released
  exact released_verbatim released.1 bindings occurrence

/-- And so does the environment continuation. -/
theorem environment_released_of_mode_ne_binding (schema : ContractionSchema)
    (notBinding : schema.mode ≠ .binding) (bindings : Bindings)
    {context : OneHoleContext}
    (occurrence : context ∈
      zippersAt (.fvar schema.environmentContinuation) schema.contractum) :
    applyBindings bindings schema.contractum =
      (context.instantiate bindings).fill
        (applyBindings bindings (.fvar schema.environmentContinuation)) := by
  have released : schema.released = true := by
    cases value : schema.released
    · exact absurd ((mode_eq_binding_iff schema).mpr value) notBinding
    · rfl
  simp only [ContractionSchema.released, Bool.and_eq_true] at released
  exact released_verbatim released.2 bindings occurrence

end ContractionSchema

namespace InteractionCutPresentation

/-- The variables the environment operand brings that the program operand
does not share. -/
def environmentVariables {theory : IGSLT} (cut : InteractionCutPresentation theory) :
    List String :=
  cut.environment.schemaTerm.schemaVariables.filter fun name =>
    !cut.program.schemaTerm.schemaVariables.contains name

/-- The variables the program operand brings that the environment operand
does not share. -/
def programVariables {theory : IGSLT} (cut : InteractionCutPresentation theory) :
    List String :=
  cut.program.schemaTerm.schemaVariables.filter fun name =>
    !cut.environment.schemaTerm.schemaVariables.contains name

/-- The contraction of a cut, as authored: the two sides of the selected
interaction rewrite and the two continuation variables the cut names. -/
def contractionSchema {theory : IGSLT} (cut : InteractionCutPresentation theory) :
    ContractionSchema where
  redex := theory.presentation.interactionRewrite.1.left
  contractum := cut.contractumSchema
  programContinuation := cut.program.continuationVariable.name
  environmentContinuation := cut.environment.continuationVariable.name
  contactLabel :=
    match theory.presentation.contactRepresentation with
    | .binary => some theory.presentation.contactConstructor.1.label
    | .collection _ => none
  locations := reductionPositions theory.presentation.presentation.language

/-- The migration mode of an interaction cut. -/
def migrationMode {theory : IGSLT} (cut : InteractionCutPresentation theory) :
    MigrationMode :=
  cut.contractionSchema.mode

/-- The program continuation receives a datum the environment brought. -/
def BindsFromEnvironment {theory : IGSLT} (cut : InteractionCutPresentation theory) :
    Prop :=
  bindsInto cut.contractumSchema cut.program.continuationVariable.name
    cut.environmentVariables = true

instance {theory : IGSLT} (cut : InteractionCutPresentation theory) :
    Decidable cut.BindsFromEnvironment :=
  inferInstanceAs (Decidable (_ = true))

/-- A cut that binds from the environment is in the binding mode. -/
theorem migrationMode_eq_binding_of_bindsFromEnvironment {theory : IGSLT}
    (cut : InteractionCutPresentation theory) (binds : cut.BindsFromEnvironment) :
    cut.migrationMode = .binding := by
  apply (ContractionSchema.mode_eq_binding_iff _).mpr
  simp only [BindsFromEnvironment, bindsInto, List.any_eq_true] at binds
  obtain ⟨context, occurrence, replacement, substituted, -⟩ := binds
  have notFree : context.substitutionFree = false := by
    cases free : context.substitutionFree
    · rfl
    · rw [OneHoleContext.substitutions_eq_nil_of_substitutionFree free] at substituted
      cases substituted
  have notReleased :
      releasedVerbatim cut.contractumSchema cut.program.continuationVariable.name = false := by
    cases released :
        releasedVerbatim cut.contractumSchema cut.program.continuationVariable.name
    · rfl
    · simp only [releasedVerbatim, List.all_eq_true] at released
      rw [released context occurrence] at notFree
      cases notFree
  simp [ContractionSchema.released, contractionSchema, notReleased]

end InteractionCutPresentation

end Mettapedia.GSLT.LanguageDef
