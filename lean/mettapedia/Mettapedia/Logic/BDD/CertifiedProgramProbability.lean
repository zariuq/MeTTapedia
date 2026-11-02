import Mettapedia.Logic.NormalProgramCertificates
import Mettapedia.Logic.BDD.RecursiveNormalCompilation

/-!+# Automatic certified probability for finite ground programs

Stratification is checked before choosing a classical compilation route.
Tight programs use Clark completion; other stratified programs also receive
loop formulas. Non-stratifiable programs return `none`, including programs
with multiple stable models. No distribution over those models is invented.

Analysis, certificate checking and BDD construction are executable. The exact
`ENNReal` probability wrapper uses the existing certified weighted counter;
it is not an executable real-number evaluator. Both full Tseitin and
polarity-directed clausification project auxiliaries before counting.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.CertifiedProgramProbability

open scoped ENNReal
open LP NormalProgramSemantics NormalProgramCertificates ClarkCompletion
open NormalCompletion RecursiveNormalCompilation
open ClausificationCounting (Method)

variable {σ : LPSignature} [DecidableEq (GroundAtom σ)] {n : Nat}

inductive RouteKind where
  | completion
  | loopFormulas
  deriving DecidableEq, Repr

inductive Analysis (rules : List (NormalClause σ)) where
  | completion (stratification : StratificationCertificate rules) (tightness : TightCertificate rules)
  | loopFormulas (stratification : StratificationCertificate rules) (notTight : ¬ Tight rules)

def Analysis.kind {rules : List (NormalClause σ)} : Analysis rules → RouteKind
  | .completion _ _ => .completion
  | .loopFormulas _ _ => .loopFormulas

def Analysis.stratification {rules : List (NormalClause σ)} : Analysis rules → StratificationCertificate rules
  | .completion certificate _ | .loopFormulas certificate _ => certificate

omit [DecidableEq (GroundAtom σ)] in
theorem Analysis.completion_iff {rules : List (NormalClause σ)} (analysis : Analysis rules) :
    analysis.kind = .completion ↔ Tight rules := by
  cases analysis with
  | completion strata certificate => exact ⟨fun _ => certificate.sound, fun _ => rfl⟩
  | loopFormulas strata notTight => simp [Analysis.kind, notTight]

/-- Stratification comes first: positive acyclicity alone does not certify probability. -/
def analyze? (rules : List (NormalClause σ)) : Option (Analysis rules) :=
  match findStratification rules with
  | none => none
  | some strata => match found : findTight rules with
    | some tightness => some (.completion strata tightness)
    | none => some (.loopFormulas strata (fun tight => by
        have present := (findTight_isSome rules).mpr tight
        simp [found] at present))

theorem analyze?_isSome (rules : List (NormalClause σ)) :
    (analyze? rules).isSome ↔ isStratifiable rules := by
  have same : (analyze? rules).isSome = (findStratification rules).isSome := by
    cases found : findStratification rules with
    | none => simp [analyze?, found]
    | some strata =>
      simp only [analyze?, found]
      split <;> rfl
  rw [same, findStratification_isSome]

theorem analyze?_none_iff (rules : List (NormalClause σ)) :
    analyze? rules = none ↔ ¬ isStratifiable rules := by
  constructor
  · intro absent stratifiable
    have present := (analyze?_isSome rules).mpr stratifiable
    simp [absent] at present
  · intro notStratifiable
    cases found : analyze? rules with
    | none => rfl
    | some analysis => exact (notStratifiable ⟨analysis.stratification.strata, analysis.stratification.respects⟩).elim

def route? (rules : List (NormalClause σ)) : Option RouteKind := (analyze? rules).map Analysis.kind

theorem route?_completion_iff (rules : List (NormalClause σ)) :
    route? rules = some .completion ↔ isStratifiable rules ∧ Tight rules := by
  cases found : analyze? rules with
  | none =>
    have absent := (analyze?_none_iff rules).mp found
    simp [route?, found, absent]
  | some analysis =>
    have stratifiable : isStratifiable rules := ⟨analysis.stratification.strata, analysis.stratification.respects⟩
    simp [route?, found, stratifiable, analysis.completion_iff]

theorem route?_loopFormulas_iff (rules : List (NormalClause σ)) :
    route? rules = some .loopFormulas ↔ isStratifiable rules ∧ ¬ Tight rules := by
  cases found : analyze? rules with
  | none =>
    have absent := (analyze?_none_iff rules).mp found
    simp [route?, found, absent]
  | some analysis =>
    have stratifiable : isStratifiable rules := ⟨analysis.stratification.strata, analysis.stratification.respects⟩
    have kind : analysis.kind = .loopFormulas ↔ ¬ Tight rules := by
      rw [← analysis.completion_iff]
      cases analysis.kind <;> simp
    simp [route?, found, stratifiable, kind]

/-- Build the finite carrier from the supplied source, then compile actual clauses. -/
def Analysis.compile {rules : List (NormalClause σ)} (analysis : Analysis rules) (method : Method)
    (facts : Fin n → GroundAtom σ) (goals : List (GoalLit σ)) : BDD n :=
  let table := programTable facts rules goals
  match analysis with
  | .completion _ _ => programBDD method table facts rules goals
  | .loopFormulas _ _ => loopProgramBDD method table facts rules goals

theorem Analysis.compile_ordered {rules : List (NormalClause σ)} (analysis : Analysis rules)
    (method : Method) (facts : Fin n → GroundAtom σ) (goals : List (GoalLit σ)) :
    (analysis.compile method facts goals).Ordered none := by
  cases analysis with
  | completion _ _ => exact programBDD_ordered _ _ _ _ _
  | loopFormulas _ _ => exact loopProgramBDD_ordered _ _ _ _ _

theorem Analysis.compile_source (prog : ProbMeTTaSourceProgram σ n) (analysis : Analysis prog.normalRules)
    (method : Method) (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit σ)) (choice : Fin n → Bool) :
    (analysis.compile method prog.probFacts goals).eval choice = sourceEvent prog s goals choice := by
  cases analysis with
  | completion _ tightness =>
    exact programBDD_source method _ prog (programTable_covers _ _ _) tightness.sound s stratified goals choice
  | loopFormulas _ _ =>
    exact loopProgramBDD_source method _ prog (programTable_covers _ _ _) s stratified goals choice

def compile? (method : Method) (prog : ProbMeTTaSourceProgram σ n) (goals : List (GoalLit σ)) : Option (BDD n) :=
  (analyze? prog.normalRules).map fun analysis => analysis.compile method prog.probFacts goals

/-- Exact semantic probability, with unsupported programs distinguished from probability zero. -/
noncomputable def probability? (method : Method) (prog : ProbMeTTaSourceProgram σ n)
    (goals : List (GoalLit σ)) : Option ℝ≥0∞ :=
  (compile? method prog goals).map fun diagram => bdd_wmc diagram prog.probs

theorem compile?_none_iff (method : Method) (prog : ProbMeTTaSourceProgram σ n) (goals : List (GoalLit σ)) :
    compile? method prog goals = none ↔ ¬ isStratifiable prog.normalRules := by
  simp [compile?, analyze?_none_iff]

theorem probability?_none_iff (method : Method) (prog : ProbMeTTaSourceProgram σ n) (goals : List (GoalLit σ)) :
    probability? method prog goals = none ↔ ¬ isStratifiable prog.normalRules := by
  simp [probability?, compile?_none_iff]

theorem compile?_ordered (method : Method) (prog : ProbMeTTaSourceProgram σ n) (goals : List (GoalLit σ))
    {diagram : BDD n} (compiled : compile? method prog goals = some diagram) : diagram.Ordered none := by
  cases found : analyze? prog.normalRules with
  | none => simp [compile?, found] at compiled
  | some analysis =>
    have same : analysis.compile method prog.probFacts goals = diagram := by simpa [compile?, found] using compiled
    rw [← same]
    exact analysis.compile_ordered method prog.probFacts goals

theorem compile?_source (method : Method) (prog : ProbMeTTaSourceProgram σ n) (goals : List (GoalLit σ))
    {diagram : BDD n} (compiled : compile? method prog goals = some diagram)
    (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (choice : Fin n → Bool) : diagram.eval choice = sourceEvent prog s goals choice := by
  cases found : analyze? prog.normalRules with
  | none => simp [compile?, found] at compiled
  | some analysis =>
    have same : analysis.compile method prog.probFacts goals = diagram := by simpa [compile?, found] using compiled
    rw [← same]
    exact analysis.compile_source prog method s stratified goals choice

theorem probability?_eq_queryProb (method : Method) (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit σ)) :
    probability? method prog goals = some
      (Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb prog.probs
        (fun world => sourceEvent prog s goals (WMPLNBDDWMCExact.worldAssignmentEquiv n world))) := by
  cases found : analyze? prog.normalRules with
  | none => exact ((analyze?_none_iff _).mp found ⟨s, stratified⟩).elim
  | some analysis =>
    simp only [probability?, compile?, found, Option.map_some, Option.some.injEq]
    exact WMPLNBDDWMCExact.bdd_wmc_eq_queryProb _ (analysis.compile_ordered method prog.probFacts goals)
      _ prog.probs_le_one _ (fun world => analysis.compile_source prog method s stratified goals
        (WMPLNBDDWMCExact.worldAssignmentEquiv n world))

theorem probability?_correct (method : Method) (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit σ)) :
    probability? method prog goals = some (weightedSat (sourceEvent prog s goals) prog.probs) := by
  cases found : analyze? prog.normalRules with
  | none => exact ((analyze?_none_iff _).mp found ⟨s, stratified⟩).elim
  | some analysis =>
    simp only [probability?, compile?, found, Option.map_some, Option.some.injEq]
    rw [bdd_wmc_correct _ (analysis.compile_ordered method prog.probFacts goals) _ prog.probs_le_one]
    simp only [weightedSat, analysis.compile_source prog method s stratified goals]

section ExistingSourceAPI

universe u v
variable {τ : LPSignature.{u, u, v, u}} [DecidableEq (GroundAtom τ)]

theorem probability?_eq_loopCount (method : Method) (table : AtomTable (GroundAtom τ))
    (prog : ProbMeTTaSourceProgram τ n) (covers : Covers table prog.probFacts prog.normalRules)
    (s : Stratification τ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit τ)) : probability? method prog goals = some (loopProgramCount method table prog goals) := by
  rw [probability?_correct method prog s stratified, loopProgramCount_correct method table prog covers s stratified]

theorem probability?_eq_completionCount (method : Method) (table : AtomTable (GroundAtom τ))
    (prog : ProbMeTTaSourceProgram τ n) (covers : Covers table prog.probFacts prog.normalRules)
    (tight : Tight prog.normalRules) (s : Stratification τ)
    (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s) (goals : List (GoalLit τ)) :
    probability? method prog goals = some (programCount method table prog goals) := by
  rw [probability?_eq_loopCount method table prog covers s stratified, loopProgramCount_eq_of_tight _ _ _ tight]

/-- Every answer comes from a stratified source model and is its ProbLog probability. -/
theorem probability?_some_iff (method : Method) (prog : ProbMeTTaSourceProgram τ n)
    (goals : List (GoalLit τ)) (value : ℝ≥0∞) : probability? method prog goals = some value ↔
      ∃ s, (∀ c ∈ prog.normalRules, respectsStratification c s) ∧
        value = Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb prog.probs
          (fun world => sourceEvent prog s goals (WMPLNBDDWMCExact.worldAssignmentEquiv n world)) := by
  constructor
  · intro answered
    cases found : analyze? prog.normalRules with
    | none => simp [probability?, compile?, found] at answered
    | some analysis =>
      let s := analysis.stratification
      refine ⟨s.strata, s.respects, ?_⟩
      exact Option.some.inj (answered.symm.trans (probability?_eq_queryProb method prog s.strata s.respects goals))
  · rintro ⟨s, valid, rfl⟩
    exact probability?_eq_queryProb method prog s valid goals

theorem probability?_methods_agree (prog : ProbMeTTaSourceProgram τ n) (goals : List (GoalLit τ)) :
    probability? .full prog goals = probability? .polarityDirected prog goals := by
  by_cases stratifiable : isStratifiable prog.normalRules
  · obtain ⟨s, valid⟩ := stratifiable
    have full := probability?_correct .full prog s valid goals
    have polarity := probability?_correct .polarityDirected prog s valid goals
    exact full.trans polarity.symm
  · rw [(probability?_none_iff .full prog goals).mpr stratifiable,
      (probability?_none_iff .polarityDirected prog goals).mpr stratifiable]

variable [IsEmpty τ.functionSymbols] [Nonempty (GroundTerm τ)]

theorem probability?_eq_probExact (method : Method) (prog : ProbMeTTaSourceProgram τ n)
    (s : Stratification τ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (query : GroundAtom τ) : probability? method prog [.pos query] = some (prog.probExact s query) := by
  rw [probability?_correct method prog s stratified, sourceEvent_eq_probExact]

end ExistingSourceAPI

namespace Controls

open NormalCompletion.Controls
open Mettapedia.GSLT.OpenEnded.PrologContrasts (Atom)

def deterministicSource {A : Type} (rules : List (NormalClause (signature A))) :
    ProbMeTTaSourceProgram (signature A) 0 where
  probFacts := Fin.elim0
  probs := Fin.elim0
  probs_le_one i := Fin.elim0 i
  normalRules := rules
  facts_injective i := Fin.elim0 i

theorem liar_and_choice_rejected : route? liarRules = none ∧ route? choiceRules = none := by decide

theorem positive_acyclicity_does_not_suffice :
    (findTight liarRules).isSome = true ∧ (findTight choiceRules).isSome = true ∧
      (findStratification liarRules).isNone = true ∧ (findStratification choiceRules).isNone = true := by decide

theorem no_probability_for_liar_or_choice (method : Method) (goals : List (GoalLit (signature Atom))) :
    probability? method (deterministicSource liarRules) goals = none ∧
      probability? method (deterministicSource choiceRules) goals = none :=
  ⟨(probability?_none_iff _ _ _).mpr liar_not_stratifiable,
    (probability?_none_iff _ _ _).mpr choice_not_stratifiable⟩

theorem self_loop_takes_loop_route : route? loopRules = some .loopFormulas := by decide

theorem self_loop_answers_zero (method : Method) :
    probability? method loopSource [.pos (atom ())] = some 0 := by
  rw [probability?_eq_probExact method loopSource (zeroStratum Unit) loop_stratified, loop_source_probability_zero]

theorem tight_negation_takes_completion_route : route? negativeRules = some .completion := by decide

theorem tight_negation_answers_two_thirds (method : Method) :
    probability? method (negativeSource (1/3) third_le_one) [.pos (atom true)] = some (2/3) := by
  rw [probability?_eq_completionCount method negativeTable _ negative_covers negative_tight negativeStratum
    negative_stratified, negative_probability_two_thirds]

theorem tight_negation_routes_agree (method : Method) :
    programCount method negativeTable (negativeSource (1/3) third_le_one) [.pos (atom true)] =
      loopProgramCount method negativeTable (negativeSource (1/3) third_le_one) [.pos (atom true)] :=
  (loopProgramCount_eq_of_tight _ _ _ negative_tight _).symm

def oddNegativeCycle : List (NormalClause (signature (Fin 3))) :=
  [⟨atom 0, [.neg (atom 1)]⟩, ⟨atom 1, [.neg (atom 2)]⟩, ⟨atom 2, [.neg (atom 0)]⟩]

def evenNegativeCycle : List (NormalClause (signature (Fin 4))) :=
  [⟨atom 0, [.neg (atom 1)]⟩, ⟨atom 1, [.neg (atom 2)]⟩,
    ⟨atom 2, [.neg (atom 3)]⟩, ⟨atom 3, [.neg (atom 0)]⟩]

def mixedCycle : List (NormalClause (signature Bool)) :=
  [⟨atom false, [.neg (atom true)]⟩, ⟨atom true, [.pos (atom false)]⟩]

/-- Even negative cycles can have stable models but still admit no stratification. -/
theorem signed_cycles_rejected : route? oddNegativeCycle = none ∧
    route? evenNegativeCycle = none ∧ route? mixedCycle = none := by decide

theorem empty_program_takes_completion_route : route? ([] : List (NormalClause (signature Unit))) =
    some .completion := by decide

theorem empty_program_answers_one (method : Method) : probability? method emptySource [] = some 1 := by
  have tight : Tight ([] : List (NormalClause (signature Unit))) :=
    TightCertificate.sound ⟨fun _ => 0, fun _ h => by cases h⟩
  rw [probability?_eq_completionCount method emptyTable emptySource (programTable_covers _ _ _) tight
    (zeroStratum Unit) (fun _ h => by cases h), empty_program_count]

theorem empty_false_event (choice : Fin 0 → Bool) :
    sourceEvent emptySource (zeroStratum Unit) [.pos (atom ())] choice = false := by
  have unique : choice = Fin.elim0 := Subsingleton.elim _ _
  subst choice
  have tight : Tight ([] : List (NormalClause (signature Unit))) :=
    TightCertificate.sound ⟨fun _ => 0, fun _ h => by cases h⟩
  apply Bool.eq_iff_iff.mpr
  rw [sourceEvent_completion emptyTable emptySource (programTable_covers _ _ _) tight
    (zeroStratum Unit) (fun _ h => by cases h)]
  decide

theorem zero_answer_is_not_rejection (method : Method) :
    probability? method emptySource [.pos (atom ())] = some 0 ∧
      probability? method emptySource [.pos (atom ())] ≠ none := by
  have answer := probability?_correct method emptySource (zeroStratum Unit)
    (fun _ h => by cases h) [.pos (atom ())]
  rw [funext empty_false_event, weightedSat_false] at answer
  simp [answer]

theorem invalid_certificates_rejected :
    checkTightRank loopRules (fun _ => 0) = false ∧
      checkStratification negativeRules (fun _ => 0) = false := by decide

/-- The undefined negative premise is included and receives the required lower stratum. -/
theorem body_only_atom_checked : atom false ∈ (dependencyTable negativeRules).atoms ∧
    (findStratification negativeRules).isSome = true := by decide

def guardedNegativeLoop : List (NormalClause (signature Unit)) :=
  [⟨atom (), [.neq (atom ()) (atom ()), .neg (atom ())]⟩]

theorem false_guard_does_not_erase_dependencies : route? guardedNegativeLoop = none := by decide

theorem duplicate_rules_keep_classification :
    route? (negativeRules ++ negativeRules) = route? negativeRules ∧
      route? (loopRules ++ loopRules) = route? loopRules ∧
      route? (choiceRules ++ choiceRules) = route? choiceRules := by decide

end Controls

end Mettapedia.Logic.BDDCore.CertifiedProgramProbability
