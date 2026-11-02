import Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInstallation
import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedKernelControls

/-!
# Actual symbolic exports keep local proof use through installation

A real protected local proof produces a closed result. The exported
declaration retains that local hypothesis, its parameter context and source
arguments. Installation is conservative at different later substitutions and
preserves the client's rights. Wrong source inventories and absent supplies
cannot obtain the advertised result.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInstallationControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open MM0ContextualSupport
open MM0Rewriting
open MM0LocatedActivation (Value locate)
open MM0LocatedKernelControls

def source : SchemaSchedules.SourceFiring (MM0LocatedKernel.SourceSchema ClientSource)
    (MM0LocatedKernel.Inputs Unit) Nat := ⟨.inl (.theorem_ 0), .inl arguments, picked⟩

def schedule : List (ConditionalSchedule.Firing Value Nat) := [(locate raw, picked)]

theorem source_is_computed : SchemaSchedules.lowerAll system.activate [source] = some schedule := by
  have computed : system.activate (.inl (.theorem_ 0)) (.inl arguments) = some (locate raw) :=
    located_activation_is_the_actual_premise_reading_rule
  simp [SchemaSchedules.lowerAll, SchemaSchedules.lower, source, schedule, computed]

theorem identity_solves_the_actual_result : (MM0LocatedActivation.action target).Models
    (MM0LocatedActivation.action target).identity (picked.result label (locate raw) before).equations := by
  intro equation member
  have alternatives : equation = ((Space.requests, request), (.requests, request)) ∨
      equation = ((Space.judgments, premise), (.judgments, premise)) := by
    simpa [Selection.result, Selection.problem, Selection.equations, picked, before, raw,
      RequestActivation.fromValues, locate, LocatedRequest.lift, label, location, payload] using member
  rcases alternatives with rfl | rfl <;> exact ⟨rfl, rfl⟩

def certificate : MM0SymbolicExport.Certificate system payload where
  sources := [source]
  schedule := schedule
  computed := source_is_computed
  authorized := by
    intro actual member
    have same : actual = source := by simpa using member
    subst actual
    constructor
    · exact List.mem_map.mpr ⟨.theorem_ 0, by decide +kernel, rfl⟩
    · intro occurrence made; rfl
  before := before
  enabled := by
    apply (ConditionalSchedule.compile_holds_iff _ _ _ _).mpr
    exact ⟨primitive_selection_is_valid, ⟨_, identity_solves_the_actual_result⟩⟩
  assignment := (MM0LocatedActivation.action target).identity
  solved := identity_solves_the_actual_result
  output := 2
  present := by decide +kernel
  protectedOutput := rfl
  conclusion := .term 0
  observed := (MM0ConstraintParameters.action target).apply_identity conclusion
  originOrder := [1]
  originDistinct := by decide
  originInventory := by decide +kernel
  decoded := by decide +kernel

theorem a_closed_output_keeps_its_actual_local_proof :
    certificate.declaration = ⟨target, [.var 0], .term 0⟩ := by decide +kernel

theorem used_occurrences_are_inferred : certificate.used = {1} := by decide +kernel

theorem omitted_used_proof_is_not_the_inferred_inventory :
    ([] : List Nat).toFinset ≠ certificate.used := by decide +kernel

theorem source_parameter_survives_the_closed_output : 0 ∈ certificate.parameterFootprint := by decide +kernel

theorem independent_symbolic_derivation :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target [.var 0] (.term 0) := by
  simpa only [a_closed_output_keeps_its_actual_local_proof] using certificate.justified theory_formed target_formed

def installation : MM0SchemaInstallation.Installation system payload where
  certificate := certificate
  index := 1
  fresh := rfl
  admitted := by decide +kernel

theorem the_actual_new_key_is_installed :
    installation.installed.theoremSignature 1 = some ⟨target, [.var 0], .term 0⟩ := by decide +kernel

theorem the_kernel_catalog_contains_the_new_key :
    .inl (.theorem_ 1) ∈ ((installation.rebuilt system).authority.process .kernel).schemas := by
  change .inl (.theorem_ 1) ∈ (catalog installation.installed).map Sum.inl
  exact List.mem_map.mpr ⟨.theorem_ 1, by simp [catalog, MM0SchemaInstallation.Installation.installed, installation], rfl⟩

theorem equal_formulas_at_distinct_initial_origins_keep_both_positions :
    MM0SymbolicExport.hypotheses target (fun _ : Nat => premise) [1, 9] = [.var 0, .var 0] := by
  decide +kernel

def installedRequest : Tm := requestValue (RuleKey.theorem_ 1).name [encode target (.var 0)]
def installedRaw : RuleInstance Tm := RequestActivation.fromValues
  MM0ConstraintTheoremApplication.falseHead MM0ConstraintTheoremApplication.trueHead
  installedRequest [premise] conclusion true

theorem installed_key_really_activates :
    MM0LocatedActivation.activate installation.installed target (.theorem_ 1) arguments = some (locate installedRaw) := by
  change (MM0ScopedCatalogActivation.activate installation.installed target (.theorem_ 1) arguments).map locate = _
  have known := the_actual_new_key_is_installed
  have admitted : Substitution.Admissible theory.termSignature declaration.arguments target arguments :=
    (Substitution.checkAdmissible_iff _ _ _ _).mp (by decide +kernel)
  change installation.installed.theoremSignature 1 = some declaration at known
  simp only [MM0ScopedCatalogActivation.activate, known, Option.bind_eq_bind, Option.bind_some]
  have same : MM0ScopedRequestActivation.activate theory.termSignature declaration.arguments target
      (RuleKey.theorem_ 1).name [proofPattern target.length (.var 0)]
      (proofPattern target.length (.term 0)) arguments = some installedRaw := by
    rw [MM0ScopedRequestActivation.activate_eq_source_of_admissible theory.termSignature declaration.arguments target target_formed
      (RuleKey.theorem_ 1).name [proofPattern target.length (.var 0)] (proofPattern target.length (.term 0)) arguments admitted
      (by intro pattern member; have equal : pattern = proofPattern target.length (.var 0) := by simpa using member
          subst pattern; exact MM0ScopedPatterns.judgmentPattern_ambient _ _ _)
      (MM0ScopedPatterns.judgmentPattern_ambient _ _ _)]
    apply (RequestActivation.activate_iff _ _ _ _ _ installedRaw).mpr
    refine ⟨installedRequest, [premise], conclusion, ?_, ?_, ?_, ?_⟩
    · exact theoremRequest_instantiation target arguments (admitted_arguments_supported target_formed admitted) (RuleKey.theorem_ 1).name
    · have instantiated := proofPattern_instantiation target arguments (admitted_arguments_supported target_formed admitted) (.var 0)
      change ((proofPattern target.length (.var 0)).inst (expressionAssignment target arguments)).bind
        (fun value => some [value]) = some [premise]
      rw [instantiated]
      rfl
    · exact proofPattern_instantiation target arguments (admitted_arguments_supported target_formed admitted) (.term 0)
    · have sourceData := (admitArguments_iff theory.termSignature declaration.arguments target (expressionAssignment target arguments) arguments).mpr
        ⟨admitted, fun _ _ => rfl⟩
      change installedRaw = RequestActivation.fromValues _ _ installedRequest [premise] conclusion
        (admitArguments theory.termSignature declaration.arguments target (expressionAssignment target arguments)).isSome
      rw [sourceData]
      rfl
  change (MM0ScopedRequestActivation.activate theory.termSignature declaration.arguments target
    (RuleKey.theorem_ 1).name [proofPattern target.length (.var 0)]
    (proofPattern target.length (.term 0)) arguments).map locate = _
  rw [same]
  rfl

def installedPayload (occurrence : Nat) : Tm := if occurrence = 0 then installedRequest else payload occurrence
def installedLabel (occurrence : Nat) : Value := (location occurrence, installedPayload occurrence)

theorem installed_selection_is_valid : picked.Valid (MM0LocatedActivation.action target)
    installedLabel (locate installedRaw) before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl,
    ⟨by decide, by decide, by decide, by decide, by simp [Selection.commit]⟩, ?_, ?_⟩
  · refine ⟨(MM0LocatedActivation.action target).identity, ?_⟩
    intro equation member
    have alternatives : equation = ((Space.requests, installedRequest), (.requests, installedRequest)) ∨
        equation = ((Space.judgments, premise), (.judgments, premise)) := by
      simpa [Selection.problem, Selection.equations, picked, before, installedRaw, RequestActivation.fromValues,
        locate, LocatedRequest.lift, installedLabel, location, installedPayload, payload] using member
    rcases alternatives with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · intro check member assignment _
    have same : check = .equal
        (Space.requests, ABTDataChecks.boolean MM0ConstraintTheoremApplication.falseHead MM0ConstraintTheoremApplication.trueHead true)
        (.requests, ABTDataChecks.boolean MM0ConstraintTheoremApplication.falseHead MM0ConstraintTheoremApplication.trueHead true) := by
      simpa [locate, LocatedRequest.lift, installedRaw, RequestActivation.fromValues, ABTDataChecks.check, Check.map] using member
    subst check
    exact ⟨rfl, rfl⟩

theorem rebuilt_kernel_executes_the_new_key :
    (installation.rebuilt system).Step installedPayload .kernel before
      (picked.result installedLabel (locate installedRaw) before) := by
  refine ⟨.inl (.theorem_ 1), the_kernel_catalog_contains_the_new_key, .inl arguments,
    locate installedRaw, installed_key_really_activates, picked, installed_selection_is_valid, ?_, rfl⟩
  intro occurrence made
  rfl

theorem the_new_key_publishes_only_a_base_derivable_conclusion :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target [.var 0] (.term 0) := by
  have prior : MM0LocatedKernel.ProtectedValid theory target [.var 0] location installedPayload before := by
    intro assignment solved occurrence present protectedHere
    have notRequest : occurrence ≠ 0 := by
      intro same
      subst occurrence
      change Space.requests = Space.judgments at protectedHere
      cases protectedHere
    simpa only [installedPayload, if_neg notRequest] using
      initial_protected_premise_is_an_assumption assignment solved occurrence present protectedHere
  obtain ⟨assignment, solved⟩ := installed_selection_is_valid.consistent
  have run : (installation.rebuilt system).Run installedPayload before [.kernel]
      (picked.result installedLabel (locate installedRaw) before) :=
    .cons rebuilt_kernel_executes_the_new_key (.nil _)
  exact installation.published_proof_is_base_derivable system theory_formed target_formed [.var 0]
    installedPayload run prior assignment solved 2 (by decide) rfl (.term 0)
    (MM0ConstraintParameters.proof_value_fixed_of_context target_formed (.term 0) assignment)

theorem client_send_right_does_not_increase :
    ((installation.rebuilt system).authority.process .client).rights .judgments .send = false :=
  congrFun (congrFun (installation.rebuilt_rights system .client) .judgments) .send

theorem client_primitive_sources_remain_the_same :
    (installation.rebuilt system).authority.process .client = actorProcess .client :=
  installation.rebuilt_client_process system .client (by decide)

theorem every_later_context_and_local_hypothesis_is_conservative
    (later : Context) (hypotheses : List Preterm) (expression : Preterm) :
    Derives installation.installed.termSignature installation.installed.definitionSignature
        installation.installed.theoremSignature later hypotheses expression ↔
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature later hypotheses expression :=
  installation.conservative theory_formed later hypotheses expression

def later : Context := [.regular 0 ∅, .regular 0 ∅]

theorem a_different_later_argument_is_admissible :
    Substitution.Admissible theory.termSignature target later [.var 1] :=
  (Substitution.checkAdmissible_iff _ _ _ _).mp (by decide +kernel)

theorem exported_derivation_reuses_a_different_later_argument :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature later [.var 1] (.term 0) := by
  apply certificate.instantiate_and_cut (movedHypotheses := [.var 1]) theory_formed target_formed a_different_later_argument_is_admissible
  · rw [a_closed_output_keeps_its_actual_local_proof]
    exact .cons (Preterm.Substitutes.var rfl) .nil
  · exact .term 0
  · intro hypothesis member
    exact .hypothesis member

theorem primitive_theory_has_no_proof_without_a_supplied_hypothesis (context : Context) (expression : Preterm) :
    ¬Derives theory.termSignature theory.definitionSignature theory.theoremSignature context [] expression := by
  intro derived
  induction derived using Derives.rec
      (motive_2 := fun expressions _ => ∀ value ∈ expressions, False) with
  | hypothesis member => exact List.not_mem_nil member
  | @theoremApp index actual arguments instance_ known instantiated children earlier =>
      have same : actual = declaration := by
        cases index with
        | zero => exact Option.some.inj known.symm
        | succ index => simp [Theory.theoremSignature, theory, List.lookup_cons] at known
      have lengths := instantiated.hypotheses.length_eq
      rw [same] at lengths
      cases emptyOrFirst : instance_.hypotheses with
      | nil => simp [declaration, emptyOrFirst] at lengths
      | cons first rest => exact earlier first (by simp [emptyOrFirst])
  | conversion _ _ earlier => exact earlier
  | nil => rename_i value member; cases member
  | cons _ _ first rest =>
      rename_i value member
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact rest value member

theorem no_export_can_erase_the_used_local_assumption :
    ¬∃ candidate : MM0SymbolicExport.Certificate system payload, candidate.declaration.hypotheses = [] := by
  rintro ⟨candidate, emptyHypotheses⟩
  have derived := candidate.justified theory_formed target_formed
  rw [emptyHypotheses] at derived
  exact primitive_theory_has_no_proof_without_a_supplied_hypothesis target candidate.conclusion derived

theorem installing_the_closed_schema_does_not_make_it_an_axiom :
    ¬Derives installation.installed.termSignature installation.installed.definitionSignature
      installation.installed.theoremSignature later [] (.term 0) := by
  intro derived
  exact primitive_theory_has_no_proof_without_a_supplied_hypothesis later (.term 0)
    ((installation.conservative theory_formed later [] (.term 0)).mp derived)

end Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInstallationControls
