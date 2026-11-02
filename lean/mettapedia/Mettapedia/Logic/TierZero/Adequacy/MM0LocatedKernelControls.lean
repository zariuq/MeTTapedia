import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedKernel

/-!
# Protected premise, source-origin and publication controls on the actual system

The primitive declaration consumes a local proof and produces a closed
conclusion. A client can post the same proof-shaped payload in request space,
but it cannot supply the kernel's protected read or publish a judgment.
The kernel's source key and inputs cannot be paired with a fabricated rule
that omits the used premise.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedKernelControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open MM0ContextualSupport
open MM0Rewriting
open MM0ConstraintTheoremApplication (falseHead trueHead)
open MM0LocatedActivation (Value locate)

def declaration : TheoremDecl := ⟨[.regular 0 ∅], [.var 0], .term 0⟩

def theory : Theory where
  sorts := [(0, { provable := true })]
  terms := [(0, ⟨[], 0, ∅⟩)]
  theorems := [(0, declaration)]

def target : Context := [.regular 0 ∅]
def arguments : List Preterm := [.var 0]
def request : Tm := requestValue (RuleKey.theorem_ 0).name [encode target (.var 0)]
def premise : Tm := proofValue target (.var 0)
def conclusion : Tm := proofValue target (.term 0)
def raw : RuleInstance Tm := RequestActivation.fromValues falseHead trueHead request [premise] conclusion true

theorem theory_formed : theory.WellFormed := by
  constructor
  · intro index term known
    cases index with
    | zero =>
        cases known
        exact (TermDecl.check_iff _ _).mp (by decide +kernel)
    | succ index => simp [Theory.termSignature, theory, List.lookup_cons] at known
  · intro index body known
    simp [Theory.definitionSignature, theory] at known
  · intro index payloadDecl known
    cases index with
    | zero =>
        cases known
        exact (TheoremDecl.check_iff _ _ _).mp (by decide +kernel)
    | succ index => simp [Theory.theoremSignature, theory, List.lookup_cons] at known

theorem target_formed : Context.WellFormed theory.sortSignature target :=
  (Context.check_iff _ _).mp (by decide +kernel)

theorem natural_activation_is_the_actual_premise_reading_rule :
    MM0ScopedCatalogActivation.activate theory target (.theorem_ 0) arguments = some raw := by
  have admitted : Substitution.Admissible theory.termSignature declaration.arguments target arguments :=
    (Substitution.checkAdmissible_iff _ _ _ _).mp (by decide +kernel)
  change MM0ScopedRequestActivation.activate theory.termSignature declaration.arguments target (RuleKey.theorem_ 0).name
    [proofPattern target.length (.var 0)] (proofPattern target.length (.term 0)) arguments = some raw
  rw [MM0ScopedRequestActivation.activate_eq_source_of_admissible theory.termSignature declaration.arguments target target_formed
    (RuleKey.theorem_ 0).name [proofPattern target.length (.var 0)] (proofPattern target.length (.term 0)) arguments admitted
    (by intro pattern member; have same : pattern = proofPattern target.length (.var 0) := by simpa using member
        subst pattern; exact MM0ScopedPatterns.judgmentPattern_ambient _ _ _)
    (MM0ScopedPatterns.judgmentPattern_ambient _ _ _)]
  apply (RequestActivation.activate_iff _ _ _ _ _ raw).mpr
  refine ⟨request, [premise], conclusion, ?_, ?_, ?_, ?_⟩
  · exact theoremRequest_instantiation target arguments (admitted_arguments_supported target_formed admitted) (RuleKey.theorem_ 0).name
  · have instantiated := proofPattern_instantiation target arguments (admitted_arguments_supported target_formed admitted) (.var 0)
    change ((proofPattern target.length (.var 0)).inst (expressionAssignment target arguments)).bind
      (fun value => some [value]) = some [premise]
    rw [instantiated]
    rfl
  · exact proofPattern_instantiation target arguments (admitted_arguments_supported target_formed admitted) (.term 0)
  · have sourceData := (admitArguments_iff theory.termSignature declaration.arguments target (expressionAssignment target arguments) arguments).mpr
      ⟨admitted, fun _ _ => rfl⟩
    change raw = RequestActivation.fromValues falseHead trueHead request [premise] conclusion
      (admitArguments theory.termSignature declaration.arguments target (expressionAssignment target arguments)).isSome
    rw [sourceData]
    rfl

theorem located_activation_is_the_actual_premise_reading_rule :
    MM0LocatedActivation.activate theory target (.theorem_ 0) arguments = some (locate raw) := by
  change (MM0ScopedCatalogActivation.activate theory target (.theorem_ 0) arguments).map locate = _
  rw [natural_activation_is_the_actual_premise_reading_rule]
  rfl

inductive Actor where
  | kernel | client
  deriving DecidableEq

inductive ClientSource where
  | forgeData | publishJudgment
  deriving DecidableEq

def location (occurrence : Nat) : Space := if occurrence = 0 ∨ occurrence = 9 then .requests else .judgments

def payload (occurrence : Nat) : Tm :=
  if occurrence = 0 then request else if occurrence = 1 ∨ occurrence = 9 then premise else conclusion

def clientActivation : ClientSource → Unit → Option (RuleInstance Value)
  | .forgeData, _ => some ⟨[], [], [], [], [(.requests, request), (.requests, premise)]⟩
  | .publishJudgment, _ => some ⟨[], [], [], [], [(.judgments, conclusion)]⟩

def actorProcess : Actor → SchemaPublicationAuthority.Process (MM0LocatedKernel.SourceSchema ClientSource) Space
  | .kernel => ⟨fun _ _ => true, (catalog theory).map Sum.inl⟩
  | .client => ⟨fun space _ => space == .requests,
      [.inr .forgeData, .inr .publishJudgment, .inl (.theorem_ 0)]⟩

def system : MM0LocatedKernel.System theory target ClientSource Unit Actor Nat location where
  clientActivation := clientActivation
  authority :=
    { process := actorProcess
      kernel := .kernel
      soleWriter := by
        intro actor notKernel occurrence protectedHere
        cases actor with
        | kernel => exact False.elim (notKernel rfl)
        | client =>
            change (location occurrence == Space.requests) = false
            rw [show location occurrence = Space.judgments from protectedHere]
            rfl }
  kernelSchemas := rfl

def label (occurrence : Nat) : Value := (location occurrence, payload occurrence)
def before : Configuration Value Nat := ⟨[], {0, 1}⟩
def picked : Selection Nat := ⟨[0], [1], [2]⟩
def empty : Configuration Value Nat := ⟨[], ∅⟩
def forgedBefore : Configuration Value Nat := ⟨[], {0, 9}⟩
def forgedSelection : Selection Nat := ⟨[0], [9], [2]⟩

theorem primitive_selection_is_valid : picked.Valid (MM0LocatedActivation.action target) label (locate raw) before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl,
    ⟨by decide, by decide, by decide, by decide, by simp [Selection.commit]⟩, ?_, ?_⟩
  · refine ⟨(MM0LocatedActivation.action target).identity, ?_⟩
    intro equation member
    have alternatives : equation = ((Space.requests, request), (.requests, request)) ∨
        equation = ((Space.judgments, premise), (.judgments, premise)) := by
      simpa [Selection.problem, Selection.equations, picked, before, raw, RequestActivation.fromValues,
        locate, LocatedRequest.lift, label, location, payload] using member
    rcases alternatives with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · intro check member assignment _
    have same : check = .equal
        (Space.requests, ABTDataChecks.boolean falseHead trueHead true)
        (.requests, ABTDataChecks.boolean falseHead trueHead true) := by
      simpa [locate, LocatedRequest.lift, raw, RequestActivation.fromValues, ABTDataChecks.check, Check.map] using member
    subst check
    exact ⟨rfl, rfl⟩

theorem kernel_performs_the_actual_catalog_step :
    system.Step payload .kernel before (picked.result label (locate raw) before) := by
  refine ⟨.inl (.theorem_ 0), ?_, .inl arguments, locate raw,
    located_activation_is_the_actual_premise_reading_rule, picked, primitive_selection_is_valid, ?_, rfl⟩
  · exact List.mem_map.mpr ⟨.theorem_ 0, by decide +kernel, rfl⟩
  · intro occurrence member
    rfl

theorem initial_protected_premise_is_an_assumption :
    MM0LocatedKernel.ProtectedValid theory target [.var 0] location payload before := by
  intro assignment _ occurrence member protectedHere
  have alternatives : occurrence = 0 ∨ occurrence = 1 := by simpa [before] using member
  rcases alternatives with rfl | rfl
  · change Space.requests = Space.judgments at protectedHere
    cases protectedHere
  · change ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target [.var 0]
      ((MM0ConstraintParameters.action target).apply assignment (proofValue target (.var 0)))
    rw [MM0ConstraintParameters.proof_value_fixed_of_context target_formed (.var 0) assignment]
    exact valid_proof (.hypothesis (by simp))

theorem the_closed_output_has_an_independent_mm0_derivation :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target [.var 0] (.term 0) := by
  obtain ⟨assignment, solved⟩ := primitive_selection_is_valid.consistent
  have run : system.Run payload before [.kernel] (picked.result label (locate raw) before) :=
    .cons kernel_performs_the_actual_catalog_step (.nil _)
  exact system.published_proof_is_derivable theory_formed target_formed [.var 0] payload run
    initial_protected_premise_is_an_assumption assignment solved 2 (by decide) rfl (.term 0)
    (MM0ConstraintParameters.proof_value_fixed_of_context target_formed (.term 0) assignment)

theorem unprotected_forgery_is_the_same_payload : payload 9 = payload 1 := rfl

theorem unprotected_forgery_cannot_supply_the_protected_read :
    ¬forgedSelection.Valid (MM0LocatedActivation.action target) label (locate raw) forgedBefore := by
  intro qualified
  have whereRead := LocatedRequest.read_space (MM0ConstraintParameters.action target) location payload
    Space.requests Space.judgments Space.requests Space.judgments qualified 9 (by simp [forgedSelection])
  change Space.requests = Space.judgments at whereRead
  cases whereRead

def fabricated : RuleInstance Tm := { raw with read := [] }

theorem an_actual_source_key_cannot_hide_its_used_premise :
    MM0LocatedActivation.activate theory target (.theorem_ 0) arguments ≠ some (locate fabricated) := by
  intro computed
  have equal := Option.some.inj (located_activation_is_the_actual_premise_reading_rule.symm.trans computed)
  have reads := congrArg RuleInstance.read equal
  simp [locate, LocatedRequest.lift, raw, fabricated, RequestActivation.fromValues] at reads

theorem unauthorized_client_cannot_publish_a_protected_output (equations : EquationStore Value) :
    ¬system.Step payload .client empty ⟨equations, {2}⟩ := by
  intro stepped
  have inherited := system.authority.nonwriter_creates_no_protected_occurrence system.activate
    (MM0LocatedActivation.action target) (fun occurrence => (location occurrence, payload occurrence))
    (actor := .client) (by decide) stepped (occurrence := 2) (by simp) rfl
  simp [empty] at inherited

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedKernelControls
