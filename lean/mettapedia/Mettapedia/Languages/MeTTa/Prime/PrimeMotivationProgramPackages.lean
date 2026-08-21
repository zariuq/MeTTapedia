import Mettapedia.Languages.MeTTa.Prime.NativeProgramElaboration

/-!
# Complete source packages for the Prime motivation curriculum

Every definition below quotes one existing, runnable curriculum file at Lean
elaboration time.  The files remain ordinary HE or PeTTa programs: no source
declaration is rewritten into a private native spelling.  Quotation expands
to constructor data, and program planning subsequently preserves that data
declaration-for-declaration.

The paired-dialect comparison is deliberately scoped.  It states only that
the equation bags of these six curriculum pairs agree.  Evaluation commands
such as PeTTa `test` and HE `assertEqual` remain dialect-specific commands and
are not claimed to be a globally verified translator pair.
-/

namespace Mettapedia.Languages.MeTTa.Prime.PrimeMotivationProgramPackages

open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation
open Mettapedia.Languages.MeTTa.Prime.NativeProgramElaboration
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-! ## Supported shared rewrite core -/

/-- Recognize the curriculum subset whose reusable declarations are exactly
ordinary MeTTa equations.  Unsupported declaration forms reject the whole
compilation instead of being silently discarded. -/
def rewriteDeclarations? :
    List (ProgramCommand RuntimePattern) →
      Option (List (RuntimePattern × RuntimePattern))
  | [] => some []
  | .defineEq left right :: declarations => do
      let rest ← rewriteDeclarations? declarations
      pure ((left, right) :: rest)
  | _ :: _ => none

/-- Give each authored equation occurrence a stable source-order rule label.
This is public because source-adequacy proofs name the exact compiled rule
that witnesses a reduction. -/
def rewriteRulesFrom :
    Nat → List (RuntimePattern × RuntimePattern) → List RewriteRule
  | _, [] => []
  | index, (left, right) :: rules =>
      { name := s!"SOURCE_RULE_{index}"
        typeContext := []
        premises := []
        left := left
        right := right } :: rewriteRulesFrom (index + 1) rules

/-- The operational part of a rewrite rule.  Source-order labels retain
occurrence provenance, but do not affect structural matching or syntactic
substitution in the five-field core. -/
structure RewriteRuleBody where
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : RuntimePattern
  right : RuntimePattern
deriving DecidableEq

def rewriteRuleBody (rule : RewriteRule) : RewriteRuleBody :=
  ⟨rule.typeContext, rule.premises, rule.left, rule.right⟩

/-- Compiling equation occurrences preserves their operational bodies in
source order; only the provenance labels depend on the starting index. -/
theorem rewriteRulesFrom_bodies (start : Nat)
    (equations : List (RuntimePattern × RuntimePattern)) :
    (rewriteRulesFrom start equations).map rewriteRuleBody =
      equations.map fun equation =>
        ⟨[], [], equation.1, equation.2⟩ := by
  induction equations generalizing start with
  | nil => rfl
  | cons equation equations inductionHypothesis =>
      simp [rewriteRulesFrom, rewriteRuleBody, inductionHypothesis]

/-- A permutation of authored equations preserves every operational rule
body in both directions, while allowing its source-order provenance label to
change. -/
theorem rewriteRulesFrom_body_perm {first second :
    List (RuntimePattern × RuntimePattern)} (permutation : first.Perm second)
    (firstStart secondStart : Nat) :
    ((rewriteRulesFrom firstStart first).map rewriteRuleBody).Perm
      ((rewriteRulesFrom secondStart second).map rewriteRuleBody) := by
  rw [rewriteRulesFrom_bodies, rewriteRulesFrom_bodies]
  exact permutation.map _

/-- Every compiled source rule has an empty premise list. -/
theorem rewriteRulesFrom_premises_empty {start : Nat}
    {equations : List (RuntimePattern × RuntimePattern)} {rule : RewriteRule}
    (member : rule ∈ rewriteRulesFrom start equations) :
    rule.premises = [] := by
  have bodyMember : rewriteRuleBody rule ∈
      (rewriteRulesFrom start equations).map rewriteRuleBody :=
    List.mem_map_of_mem (f := rewriteRuleBody) member
  rw [rewriteRulesFrom_bodies] at bodyMember
  simp only [List.mem_map] at bodyMember
  obtain ⟨equation, _, bodyEq⟩ := bodyMember
  exact congrArg RewriteRuleBody.premises bodyEq.symm

/-- The five-field language generated from a supplied equation list. -/
def sourceLanguageFrom
    (equations : List (RuntimePattern × RuntimePattern)) : LanguageDef :=
  { name := "QuotedMeTTaRewriteCore"
    types := ["Pattern"]
    terms := []
    equations := []
    rewrites := rewriteRulesFrom 0 equations }

/-- Compile the supported authored equation core to the existing five-field
language presentation.  Failure is explicit when a reusable declaration is
outside the supported subset. -/
def sourceLanguage? (source : SourceProgram) : Option LanguageDef := do
  let rules ← rewriteDeclarations? (semanticDeclarations source)
  pure (sourceLanguageFrom rules)

/-! ## Equation-bag operational invariance -/

/-- Transport one source-equation step to a presentation containing a rule
with the same operational body.  The theorem is deliberately specialized to
the equation compiler: its rules have no premises, so source-order labels are
provenance only and cannot affect the reduction. -/
private theorem sourceStep_of_body_cover
    {first second : List (RuntimePattern × RuntimePattern)}
    (cover : ∀ rule, rule ∈ rewriteRulesFrom 0 first →
      ∃ rule', rule' ∈ rewriteRulesFrom 0 second ∧
        rewriteRuleBody rule' = rewriteRuleBody rule)
    {source target : RuntimePattern}
    (step : Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      (sourceLanguageFrom first) source target) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      (sourceLanguageFrom second) source target := by
  obtain ⟨_, bounded⟩ := step
  cases bounded with
  | @rule fuel _ _ rule initialBindings finalBindings member matched
      premises applied =>
      obtain ⟨rule', member', bodyEq⟩ := cover rule member
      have leftEq : rule'.left = rule.left :=
        congrArg RewriteRuleBody.left bodyEq
      have rightEq : rule'.right = rule.right :=
        congrArg RewriteRuleBody.right bodyEq
      have premiseEmpty : rule.premises = [] :=
        rewriteRulesFrom_premises_empty member
      have premiseEmpty' : rule'.premises = [] :=
        rewriteRulesFrom_premises_empty member'
      rw [premiseEmpty] at premises
      cases premises
      have matched' : initialBindings ∈
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
            (sourceLanguageFrom second) rule' source := by
        simpa [leftEq,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          using matched
      have applied' :
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
              (sourceLanguageFrom second) rule' initialBindings = target := by
        simpa [rightEq,
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic]
          using applied
      have premises' :
          Mettapedia.OSLF.MeTTaIL.ContextualStep.PremisesAt
            (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
              Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
            (sourceLanguageFrom second) fuel initialBindings rule'.premises
              initialBindings := by
        rw [premiseEmpty']
        exact .nil initialBindings
      exact ⟨fuel + 1, .rule member' matched' premises' applied'⟩

/-- Equation declarations have bag semantics at the ordinary source-language
boundary: permuting them leaves the declarative reduction relation unchanged.
Provenance labels may change, but the terms that can reduce do not. -/
theorem sourceLanguageFrom_step_iff_of_perm
    {first second : List (RuntimePattern × RuntimePattern)}
    (permutation : first.Perm second) (source target : RuntimePattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
          (sourceLanguageFrom first) source target ↔
      Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
          (sourceLanguageFrom second) source target := by
  have bodyPermutation := rewriteRulesFrom_body_perm permutation 0 0
  constructor
  · apply sourceStep_of_body_cover
    intro rule member
    have bodyMember : rewriteRuleBody rule ∈
        (rewriteRulesFrom 0 first).map rewriteRuleBody :=
      List.mem_map_of_mem (f := rewriteRuleBody) member
    have transported := bodyPermutation.mem_iff.mp bodyMember
    simpa only [List.mem_map] using transported
  · apply sourceStep_of_body_cover
    intro rule member
    have bodyMember : rewriteRuleBody rule ∈
        (rewriteRulesFrom 0 second).map rewriteRuleBody :=
      List.mem_map_of_mem (f := rewriteRuleBody) member
    have transported := bodyPermutation.symm.mem_iff.mp bodyMember
    simpa only [List.mem_map] using transported

private def orderExampleFirst : RuntimePattern × RuntimePattern :=
  (.fvar "a", .fvar "b")

private def orderExampleSecond : RuntimePattern × RuntimePattern :=
  (.fvar "c", .fvar "d")

/-- Positive control: swapping two authored equations preserves every
declarative source step. -/
theorem source_equation_swap_preserves_steps (source target : RuntimePattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        (sourceLanguageFrom [orderExampleFirst, orderExampleSecond])
        source target ↔
      Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        (sourceLanguageFrom [orderExampleSecond, orderExampleFirst])
        source target :=
  sourceLanguageFrom_step_iff_of_perm
    (List.Perm.swap orderExampleFirst orderExampleSecond []).symm source target

/-- Negative control: the source-order provenance labels do change under the
same swap.  The operational invariance theorem therefore does real work; it
is not record equality disguised as semantics. -/
theorem source_equation_swap_changes_provenance :
    sourceLanguageFrom [orderExampleFirst, orderExampleSecond] ≠
      sourceLanguageFrom [orderExampleSecond, orderExampleFirst] := by
  intro same
  have rewritesEq := congrArg LanguageDef.rewrites same
  simp [sourceLanguageFrom, rewriteRulesFrom, orderExampleFirst,
    orderExampleSecond] at rewritesEq

/-- Every successfully compiled source language uses exact syntactic
equality; no authored equation is smuggled into the GSLT equivalence. -/
theorem sourceLanguage?_equations_empty {source : SourceProgram}
    {language : LanguageDef} (compiled : sourceLanguage? source = some language) :
    language.equations = [] := by
  unfold sourceLanguage? at compiled
  cases equation : rewriteDeclarations? (semanticDeclarations source) with
  | none => simp [equation] at compiled
  | some rules =>
      simp [equation] at compiled
      subst language
      rfl

structure LessonPair where
  petta : SourceProgram
  he : SourceProgram
  equationBagsAgree : equationBag petta = equationBag he
  /-- The ordered, reusable declaration core is identical.  Only the
  dialect-specific observation commands are excluded. -/
  semanticDeclarationsAgree :
    semanticDeclarations petta = semanticDeclarations he
  pettaLanguage : LanguageDef
  pettaCompiles : sourceLanguage? petta = some pettaLanguage
  heCompilesToSameLanguage : sourceLanguage? he = some pettaLanguage

def dfa : LessonPair where
  petta := metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/01_dfa_petta.metta"
  he := metta_program_file% he
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/01_dfa_he.metta"
  equationBagsAgree := by rfl
  semanticDeclarationsAgree := by rfl
  pettaLanguage := (sourceLanguage? (metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/01_dfa_petta.metta")).get (by rfl)
  pettaCompiles := by rfl
  heCompilesToSameLanguage := by rfl

def protocol : LessonPair where
  petta := metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/02_protocol_petta.metta"
  he := metta_program_file% he
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/02_protocol_he.metta"
  equationBagsAgree := by rfl
  semanticDeclarationsAgree := by rfl
  pettaLanguage := (sourceLanguage? (metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/02_protocol_petta.metta")).get (by rfl)
  pettaCompiles := by rfl
  heCompilesToSameLanguage := by rfl

def parallelMap : LessonPair where
  petta := metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/03_parallel_map_petta.metta"
  he := metta_program_file% he
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/03_parallel_map_he.metta"
  equationBagsAgree := by rfl
  semanticDeclarationsAgree := by rfl
  pettaLanguage := (sourceLanguage? (metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/03_parallel_map_petta.metta")).get (by rfl)
  pettaCompiles := by rfl
  heCompilesToSameLanguage := by rfl

def proofAutomaton : LessonPair where
  petta := metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/04_proof_automaton_petta.metta"
  he := metta_program_file% he
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/04_proof_automaton_he.metta"
  equationBagsAgree := by rfl
  semanticDeclarationsAgree := by rfl
  pettaLanguage := (sourceLanguage? (metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/04_proof_automaton_petta.metta")).get (by rfl)
  pettaCompiles := by rfl
  heCompilesToSameLanguage := by rfl

def gradualDemand : LessonPair where
  petta := metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/05_gradual_demand_petta.metta"
  he := metta_program_file% he
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/05_gradual_demand_he.metta"
  equationBagsAgree := by rfl
  semanticDeclarationsAgree := by rfl
  pettaLanguage := (sourceLanguage? (metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/05_gradual_demand_petta.metta")).get (by rfl)
  pettaCompiles := by rfl
  heCompilesToSameLanguage := by rfl

def languagePromotion : LessonPair where
  petta := metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/06_language_promotion_petta.metta"
  he := metta_program_file% he
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/06_language_promotion_he.metta"
  equationBagsAgree := by rfl
  semanticDeclarationsAgree := by rfl
  pettaLanguage := (sourceLanguage? (metta_program_file% petta
    "../../../../../../MettaKernel/Curriculum/PrimeMotivation/06_language_promotion_petta.metta")).get (by rfl)
  pettaCompiles := by rfl
  heCompilesToSameLanguage := by rfl

/-- All twelve complete authored programs, with no representative-expression
substitution. -/
def allPrograms : List SourceProgram :=
  [ dfa.petta, dfa.he
  , protocol.petta, protocol.he
  , parallelMap.petta, parallelMap.he
  , proofAutomaton.petta, proofAutomaton.he
  , gradualDemand.petta, gradualDemand.he
  , languagePromotion.petta, languagePromotion.he ]

def rawPackages : List ProgramPlan :=
  allPrograms.map (prepareProgram rawPolicy)

def commandPatterns : PlannedCommand → List PlannedPattern
  | .empty | .setFuel _ | .newSpace _ => []
  | .eval term | .fact term => [term]
  | .defineEq left right | .defineType left right |
      .import left right | .addAtom left right | .removeAtom left right =>
      [left, right]
  | .defineRule left right premises => left :: right :: premises
  | .relationFact _ arguments | .builtinFact _ arguments |
      .directive _ arguments => arguments

def plannedPatterns (package : ProgramPlan) : List PlannedPattern :=
  package.planned.flatMap fun row => commandPatterns row.2

def countMode (mode : PreparationMode) (package : ProgramPlan) : Nat :=
  (plannedPatterns package).countP fun planned => planned.kind == mode

/-! ## Out-of-band native islands over unchanged source -/

/-- Recognize the successful result shape of the language-promotion lesson.
This recognizer sees ordinary MeTTa syntax; it does not require an authored
`native:*` marker. -/
def isPromotedData : RuntimePattern → Bool
  | Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "Some" [_] => true
  | _ => false

/-- Compile one ordinary result value as data in the native universe. -/
def encodeAsNativeData (source : RuntimePattern) : RuntimePattern :=
  Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "native:pattern" [source]

def promotionDataPolicy : PreparationPolicy where
  choose := fun _ _ source =>
    if isPromotedData source then .eager else .raw
  encode := fun _ _ source => encodeAsNativeData source
  revision := 1
  dialect := "petta"
  authority := "prime-data-promotion-v1"

def typedLanguagePromotion : ProgramPlan :=
  prepareProgram promotionDataPolicy languagePromotion.petta

theorem all_programs_are_quoted : allPrograms.length = 12 := by
  rfl

/-- Every raw package erases to its own complete authored program. -/
theorem raw_packages_preserve_sources (package : ProgramPlan)
    (_ : package ∈ rawPackages) :
    eraseRows package.planned = package.source := by
  exact package.erases

/-- Three ordinary `Some` result shapes are recognized and intrinsically
typed as native data, without changing the authored program. -/
theorem typed_language_promotion_count :
    countMode .eager typedLanguagePromotion = 3 := by
  rfl

theorem typed_language_promotion_preserves_source :
    eraseRows typedLanguagePromotion.planned = languagePromotion.petta :=
  typedLanguagePromotion.erases

/-- Every eager island in every program package is backed by intrinsic native
typing evidence, not by a Boolean recognition flag. -/
theorem eager_island_has_intrinsic_typing (package : ProgramPlan)
    (planned : PlannedPattern) (_ : planned ∈ plannedPatterns package)
    (eager : planned.kind = .eager) :
    ∃ result, elaborate planned.plan.nativeCandidate = .ok result := by
  exact planned.plan.eager_has_intrinsic_typing eager

/-- Negative control: the complete DFA and protocol programs are distinct,
even though both are valid members of the supported curriculum subset. -/
theorem dfa_ne_protocol : dfa.petta ≠ protocol.petta := by
  decide

/-- Negative control: a reusable fact is not silently erased by the rewrite-
only compiler. -/
theorem fact_program_rejected_by_rewrite_compiler :
    sourceLanguage? (metta_program% petta "(fact datum)") = none := by
  rfl

#print axioms LessonPair.equationBagsAgree
#print axioms LessonPair.semanticDeclarationsAgree
#print axioms LessonPair.pettaCompiles
#print axioms LessonPair.heCompilesToSameLanguage
#print axioms sourceLanguageFrom_step_iff_of_perm
#print axioms source_equation_swap_preserves_steps
#print axioms source_equation_swap_changes_provenance
#print axioms raw_packages_preserve_sources
#print axioms typed_language_promotion_count
#print axioms typed_language_promotion_preserves_source
#print axioms eager_island_has_intrinsic_typing
#print axioms dfa_ne_protocol
#print axioms fact_program_rejected_by_rewrite_compiler

end Mettapedia.Languages.MeTTa.Prime.PrimeMotivationProgramPackages
