import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingCongruence
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingUnfolding
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingBasicConversions
import Mettapedia.Languages.MM0.Kernel.TheoryInvariant
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualCalculus

/-!
# A finite installed MM0 rule library on the actual guarded rewriting calculus

Rule keys select schemas from the admitted MM0 environment. Compiling a key
produces an ordinary guarded rewriting rule; it does not inspect any submitted proof.
The independent MM0 judgments validate every possible firing of every rule
in the resulting finite process.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

theorem theoremRule_preserves {sorts : SortSignature} {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature} {target : Context}
    {hypotheses : List Preterm} (formed : Context.WellFormed sorts target) (name : String)
    {index : Nat} {declaration : TheoremDecl} (known : theorems index = some declaration)
    (admitted : declaration.Admissible sorts signature)
    {before after : Multiset Tm}
    (valid : ∀ value ∈ before, ValidValue signature definitions theorems target hypotheses value)
    (step : Step ContextualPatterns.layer (theoremRule signature target name declaration) before after) :
    ∀ value ∈ after, ValidValue signature definitions theorems target hypotheses value := by
  have conclusionBounded : declaration.conclusion.VarsBelow declaration.arguments.length := by
    obtain ⟨_, _, typed, _, _⟩ := admitted.conclusion
    exact typed.varsBelow
  have hypothesesBounded : ∀ expression ∈ declaration.hypotheses, expression.VarsBelow declaration.arguments.length := by
    intro expression member
    obtain ⟨_, _, typed, _, _⟩ := admitted.hypotheses expression member
    exact typed.varsBelow
  apply argumentRule_preserves formed name _ _ _ _ _ _ valid step
  · intro pattern member
    obtain ⟨expression, expressionMember, rfl⟩ := List.mem_map.mp member
    exact judgmentPattern_vars_below _ _ _ _ (by simpa using hypothesesBounded expression expressionMember)
  · exact judgmentPattern_vars_below _ _ _ _ (by simpa using conclusionBounded)
  · intro arguments selected result accepted scopedArguments matched validSelected output
    obtain ⟨results, substitutedHypotheses, derivedHypotheses⟩ := proofPatterns_reflect
      target hypotheses arguments declaration.arguments.length (expressionAssignment target arguments)
      (fun _ _ => rfl) scopedArguments declaration.hypotheses selected hypothesesBounded matched
      (fun value member expression equal => (validSelected value member).1 expression equal)
    obtain ⟨conclusion, substitutedConclusion, same⟩ := proofPattern_reflect target arguments
      declaration.arguments.length (expressionAssignment target arguments) (fun _ _ => rfl) scopedArguments
      conclusionBounded ((ContextualPatterns.solves_iff _ _ _).mpr output)
    subst result
    exact valid_proof (.theoremApp (instantiation := ⟨results, conclusion⟩) known
      ⟨accepted, substitutedHypotheses, substitutedConclusion⟩ derivedHypotheses)

inductive RuleKey where
  | theorem_ (index : Nat)
  | basic (kind : BasicConversion) (sort : Nat)
  | congruence (symbol : Nat)
  | unfolding (symbol : Nat)
  deriving DecidableEq

def RuleKey.name : RuleKey → String
  | .theorem_ index => "thm/" ++ toString index
  | .basic .reflexivity sort => "refl/" ++ toString sort
  | .basic .symmetry sort => "symm/" ++ toString sort
  | .basic .transitivity sort => "trans/" ++ toString sort
  | .basic .transport sort => "transport/" ++ toString sort
  | .congruence symbol => "cong/" ++ toString symbol
  | .unfolding symbol => "unfold/" ++ toString symbol

def ruleFor (theory : Theory) (target : Context) (key : RuleKey) : Option (Rule Nat Tm Pat) :=
  match key with
  | .theorem_ index => (theory.theoremSignature index).map (theoremRule theory.termSignature target key.name)
  | .basic kind sort => some (kind.rule theory.termSignature target sort key.name)
  | .congruence symbol => (theory.termSignature symbol).map (congruenceRule theory.termSignature target key.name symbol)
  | .unfolding symbol => do
      let declaration ← theory.termSignature symbol
      let body ← theory.definitionSignature symbol
      some (unfoldingRule theory.termSignature target key.name symbol declaration body)

theorem ruleFor_preserves {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm)
    (key : RuleKey) {rule : Rule Nat Tm Pat} (compiled : ruleFor theory target key = some rule)
    {before after : Multiset Tm}
    (valid : ∀ value ∈ before, ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value)
    (step : Step ContextualPatterns.layer rule before after) :
    ∀ value ∈ after, ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
  cases key with
  | theorem_ index =>
      obtain ⟨declaration, known, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact theoremRule_preserves formed _ known (wellFormed.theorems _ _ known) valid step
  | basic kind sort =>
      have same : kind.rule theory.termSignature target sort (RuleKey.basic kind sort).name = rule := Option.some.inj compiled
      subst rule
      exact kind.preserves formed sort _ valid step
  | congruence symbol =>
      obtain ⟨declaration, known, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact congruenceRule_preserves formed _ known valid step
  | unfolding symbol =>
      cases knownTerm : theory.termSignature symbol with
      | none => simp [ruleFor, knownTerm] at compiled
      | some declaration =>
        cases knownBody : theory.definitionSignature symbol with
        | none => simp [ruleFor, knownBody] at compiled
        | some body =>
          have same : unfoldingRule theory.termSignature target (RuleKey.unfolding symbol).name symbol declaration body = rule := by
            simpa [ruleFor, knownTerm, knownBody] using compiled
          subst rule
          obtain ⟨actualDeclaration, actualLookup, bodyAdmitted⟩ := wellFormed.definitions _ _ knownBody
          have sameDeclaration := Option.some.inj (actualLookup.symm.trans knownTerm)
          subst actualDeclaration
          apply unfoldingRule_preserves formed _ knownTerm knownBody _ valid step
          simpa [Definition.Body.context] using bodyAdmitted.typed.varsBelow

theorem ruleFor_input (theory : Theory) (target : Context) (key : RuleKey)
    {rule : Rule Nat Tm Pat} (compiled : ruleFor theory target key = some rule) :
    ContextualPatterns.RuleInput rule := by
  cases key with
  | theorem_ index =>
      obtain ⟨declaration, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact theoremRule_input _ _ _ _
  | basic kind sort =>
      have same : kind.rule theory.termSignature target sort (RuleKey.basic kind sort).name = rule := Option.some.inj compiled
      subst rule
      exact kind.input _ _ _ _
  | congruence symbol =>
      obtain ⟨declaration, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact congruenceRule_input _ _ _ _ _
  | unfolding symbol =>
      cases knownTerm : theory.termSignature symbol with
      | none => simp [ruleFor, knownTerm] at compiled
      | some declaration =>
        cases knownBody : theory.definitionSignature symbol with
        | none => simp [ruleFor, knownBody] at compiled
        | some body =>
          have same : unfoldingRule theory.termSignature target (RuleKey.unfolding symbol).name symbol declaration body = rule := by
            simpa [ruleFor, knownTerm, knownBody] using compiled
          subst rule
          exact unfoldingRule_input _ _ _ _ _ _

inductive Space where
  | requests | judgments
  deriving DecidableEq

def space : Tm → Space
  | .node (.judgment tag) _ => if tag = "pf" ∨ tag = "cv" then .judgments else .requests
  | _ => .requests

theorem space_proof (target : Context) (expression : Preterm) : space (proofValue target expression) = .judgments := rfl
theorem space_conversion (target : Context) (sort : Nat) (left right : Preterm) :
    space (conversionValue target sort left right) = .judgments := rfl
theorem space_request (name : String) (arguments : List Tm) : space (requestValue name arguments) = .requests := by
  simp [space, requestValue, judgment, requestTag_ne_proof, requestTag_ne_conversion]

def calculus : Calculus Nat Tm Pat Space := ContextualPatterns.contextualCalculus space

def compileRules (theory : Theory) (target : Context) (keys : List RuleKey) : List (Contract × Rule Nat Tm Pat) :=
  keys.filterMap fun key => (ruleFor theory target key).map (fun rule => (.data, rule))

theorem compileRules_member (theory : Theory) (target : Context) (keys : List RuleKey)
    (installed : Contract × Rule Nat Tm Pat) :
    installed ∈ compileRules theory target keys ↔
      ∃ key ∈ keys, ∃ rule, ruleFor theory target key = some rule ∧ installed = (.data, rule) := by
  simp [compileRules, List.mem_filterMap, eq_comm]

def process (theory : Theory) (target : Context) (keys : List RuleKey) : calculus.Process where
  rights := fun _ _ => true
  rules := compileRules theory target keys
  formed := by
    intro installed member
    constructor <;> intro pattern occurs assignment term evidence <;> rfl

theorem process_inputs (theory : Theory) (target : Context) (keys : List RuleKey) :
    ContextualPatterns.ProcessInputs (process theory target keys) := by
  intro installed member
  obtain ⟨key, _, rule, found, rfl⟩ := (compileRules_member _ _ _ _).mp member
  exact (ContextualPatterns.ruleInputCheck_iff _).mpr (ruleFor_input theory target key found)

/-- Every actual process firing preserves independent MM0 validity. Formation
of the process above supplies rights; this separate theorem supplies logic. -/
theorem process_step_preserves {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (keys : List RuleKey)
    {before after : Multiset Tm}
    (valid : ∀ value ∈ before, ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value)
    (step : (process theory target keys).Step before after) :
    ∀ value ∈ after, ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
  obtain ⟨installed, member, fired⟩ := step
  obtain ⟨key, _, rule, found, rfl⟩ := (compileRules_member _ _ _ _).mp member
  exact ruleFor_preserves wellFormed formed hypotheses key found valid fired

theorem process_run_preserves {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (keys : List RuleKey)
    {before after : Multiset Tm}
    (valid : ∀ value ∈ before, ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value)
    (run : Relation.ReflTransGen (process theory target keys).Step before after) :
    ∀ value ∈ after, ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
  induction run with
  | refl => exact valid
  | tail preceding fired ih => exact process_step_preserves wellFormed formed hypotheses keys ih fired

/-- A client without theorem-space send authority cannot introduce a new
proof or conversion fact, regardless of its other rules or requests. -/
theorem client_step_preserves {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {target : Context} {hypotheses : List Preterm}
    (client : calculus.Process) (denied : client.rights .judgments .send = false)
    {before after : Multiset Tm} (step : client.Step before after)
    (valid : ∀ value ∈ before, ValidValue signature definitions theorems target hypotheses value) :
    ∀ value ∈ after, ValidValue signature definitions theorems target hypotheses value := by
  have noNew := step.no_make_without_send denied
  have old (value : Tm) (member : value ∈ after) (atJudgments : space value = .judgments) : value ∈ before := by
    have inSnapshot : value ∈ snapshot space .judgments after := Multiset.mem_filter.mpr ⟨member, atJudgments⟩
    exact (Multiset.mem_filter.mp (Multiset.mem_of_le noNew inSnapshot)).1
  intro value member
  constructor
  · intro expression same
    subst value
    exact (valid _ (old _ member (space_proof _ _))).1 expression rfl
  · intro sort left right same
    subst value
    exact (valid _ (old _ member (space_conversion _ _ _ _))).2 sort left right rfl

theorem system_run_preserves {I : Type*} {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (keys : List RuleKey)
    (system : TierZeroKernel.System calculus I .judgments)
    (installed : system.process system.kernel = process theory target keys)
    {before after : Multiset Tm} {schedule : List I}
    (valid : ∀ value ∈ before, ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value)
    (run : system.Run before schedule after) :
    ∀ value ∈ after, ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
  classical
  induction run with
  | nil => exact valid
  | @cons before middle after actor rest step tail ih =>
      apply ih
      by_cases kernel : actor = system.kernel
      · subst actor
        change (system.process system.kernel).Step before middle at step
        rw [installed] at step
        exact process_step_preserves wellFormed formed hypotheses keys valid step
      · exact client_step_preserves (system.process actor) (system.soleWriter actor kernel) step valid

theorem ruleFor_request (theory : Theory) (target : Context) (key : RuleKey)
    {rule : Rule Nat Tm Pat} (compiled : ruleFor theory target key = some rule) :
    ∃ request premises conclusion guard, rule = requestRule request premises conclusion guard := by
  cases key with
  | theorem_ index =>
      obtain ⟨declaration, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact ⟨_, _, _, _, rfl⟩
  | basic kind sort =>
      have same : kind.rule theory.termSignature target sort (RuleKey.basic kind sort).name = rule := Option.some.inj compiled
      subst rule
      exact ⟨_, _, _, _, rfl⟩
  | congruence symbol =>
      obtain ⟨declaration, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact ⟨_, _, _, _, rfl⟩
  | unfolding symbol =>
      cases knownTerm : theory.termSignature symbol with
      | none => simp [ruleFor, knownTerm] at compiled
      | some declaration =>
        cases knownBody : theory.definitionSignature symbol with
        | none => simp [ruleFor, knownBody] at compiled
        | some body =>
          have same : unfoldingRule theory.termSignature target (RuleKey.unfolding symbol).name symbol declaration body = rule := by
            simpa [ruleFor, knownTerm, knownBody] using compiled
          subst rule
          exact ⟨_, _, _, _, rfl⟩

theorem process_step_of_key (theory : Theory) (target : Context) (keys : List RuleKey)
    {key : RuleKey} (member : key ∈ keys) {rule : Rule Nat Tm Pat}
    (compiled : ruleFor theory target key = some rule) {before after : Multiset Tm}
    (fired : Step ContextualPatterns.layer rule before after) :
    (process theory target keys).Step before after :=
  ⟨(.data, rule), (compileRules_member _ _ _ _).mpr ⟨key, member, rule, compiled, rfl⟩, fired⟩

theorem process_step_frame {theory : Theory} {target : Context} {keys : List RuleKey}
    {before after : Multiset Tm} (step : (process theory target keys).Step before after) (extra : Multiset Tm) :
    (process theory target keys).Step (before + extra) (after + extra) := by
  obtain ⟨installed, member, fired⟩ := step
  obtain ⟨key, keyMember, rule, found, rfl⟩ := (compileRules_member _ _ _ _).mp member
  obtain ⟨request, premises, conclusion, guard, same⟩ := ruleFor_request theory target key found
  apply process_step_of_key theory target keys keyMember found
  rw [same] at fired ⊢
  exact requestRule_frame fired extra

theorem process_run_frame {theory : Theory} {target : Context} {keys : List RuleKey}
    {before after : Multiset Tm}
    (run : Relation.ReflTransGen (process theory target keys).Step before after) (extra : Multiset Tm) :
    Relation.ReflTransGen (process theory target keys).Step (before + extra) (after + extra) := by
  induction run with
  | refl => exact .refl
  | tail earlier fired ih => exact .tail ih (process_step_frame fired extra)

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
