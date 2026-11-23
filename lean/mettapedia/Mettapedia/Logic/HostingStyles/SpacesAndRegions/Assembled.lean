import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Generated

/-!
# The candidate of spaces and regions, assembled

`assembledOver` sends a list of constructors to the presentation of spaces
and regions over them: an ambient space outside every term, the run of an
atom in a space as a contained region, and every root step headed by a
constructor of atoms and **generated from the list** (`generatedRoots`,
`generatedRunRoots`).

* `spacesAndRegions` is the presentation over the constructors of the
  candidate in which atoms reduce.  **Its rewrites are those of `allHeaded`**
  (`spacesAndRegions_rewrites`), and it is that presentation
  (`spacesAndRegions_eq_allHeaded`): what is proved of `allHeaded` is proved
  of it.
* **Over every list of constructors the generated root steps cover every
  constructor of atoms other than the run** (`assembledOver_root_step`,
  `assembledOver_runRoot_step`): an atom headed by such a constructor steps to
  every answer of the ambient space for it, and its run to the run of every
  answer of the space of the run.

## A hand-written list that misses a constructor

`constructorsWithPair` adds one constructor of atoms, the pair, to the
constructors of the candidate.  `writtenWithPair` keeps the root steps as
they were written by hand, and `generatedWithPair` is the presentation
assembled over the longer list.  Both pass the declaration gate
(`writtenWithPair_validate`, `generatedWithPair_validate`).

* The written heads no longer cover the constructors of atoms
  (`writtenWithPair_misses`); the generated root steps do
  (`generatedWithPair_covers`).
* **The step that is lost.**  At the ambient space that stores the rule
  `pair(unit, unit) = unit`, the pair of two unit atoms steps to the unit atom
  in `generatedWithPair` (`generatedWithPair_pair_steps`) and has no step in
  `writtenWithPair`, at any ambient space and under any evaluator
  (`writtenWithPair_pair_normal`).  The same holds of its run in that space
  (`generatedWithPair_runPair_steps`, `writtenWithPair_runPair_normal`).
* Nothing else differs: every step of `writtenWithPair` is a step of
  `generatedWithPair` (`generatedWithPair_keeps_written`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti.Language
  (betaRule betaLeft appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule
    lamBodyRule appLeft piLeft lamLeft fixedRules)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions

/-! ## The presentation over a list of constructors -/

/-- **The rewrites of spaces and regions over a list of constructors**: beta,
the six congruences and the release; the generated root steps; the six
congruences beneath a run; the generated root steps of a run; and beta,
release and the step of a run, each beneath a run. -/
def assembledRewrites (spell : GrammarRule → RootSpelling) (constructors : List GrammarRule) :
    List RewriteRule :=
  (fixedRules ++ [releaseRule]) ++ generatedRoots spell constructors ++ spatialCongruences ++
    generatedRunRoots spell constructors ++ [runBetaRule, runReleaseRule, runRunRule]

/-- The rewrites over a list of constructors, in five groups. -/
theorem mem_assembledRewrites {spell : GrammarRule → RootSpelling} {constructors : List GrammarRule}
    {rule : RewriteRule} :
    rule ∈ assembledRewrites spell constructors ↔
      rule ∈ fixedRules ++ [releaseRule] ∨ rule ∈ generatedRoots spell constructors ∨
        rule ∈ spatialCongruences ∨ rule ∈ generatedRunRoots spell constructors ∨
          rule ∈ [runBetaRule, runReleaseRule, runRunRule] := by
  simp only [assembledRewrites, List.mem_append]
  tauto

/-- The rewrites over more constructors include those over fewer. -/
theorem assembledRewrites_mono {spell : GrammarRule → RootSpelling} {fewer more : List GrammarRule}
    (included : ∀ constructor ∈ fewer, constructor ∈ more) :
    ∀ rule ∈ assembledRewrites spell fewer, rule ∈ assembledRewrites spell more := by
  intro rule member
  rcases mem_assembledRewrites.mp member with plain | root | spatial | runRoot | beneath
  · exact mem_assembledRewrites.mpr (.inl plain)
  · exact mem_assembledRewrites.mpr (.inr (.inl (generatedRoots_mono included rule root)))
  · exact mem_assembledRewrites.mpr (.inr (.inr (.inl spatial)))
  · exact mem_assembledRewrites.mpr
      (.inr (.inr (.inr (.inl (generatedRunRoots_mono included rule runRoot)))))
  · exact mem_assembledRewrites.mpr (.inr (.inr (.inr (.inr beneath))))

/-- **The presentation of spaces and regions over a list of constructors**:
the three sorts and the equation of quotation and dropping of the candidate
in which atoms reduce, the given constructors, and the rewrites generated
from them. -/
def assembledOver (name : String) (constructors : List GrammarRule) : LanguageDef :=
  { name := name
    types := [MeTTaZero.atomType, MeTTaZero.spaceType, nameType]
    terms := constructors
    equations := [quoteDropEquation]
    rewrites := assembledRewrites spellingOf constructors }

/-- **The candidate of spaces and regions**: the presentation over the
constructors of the candidate in which atoms reduce.  It keeps the name
under which the presentation with every root step headed was written, so
that the two are one presentation. -/
def spacesAndRegions : LanguageDef := assembledOver allHeaded.name atomsReduce.terms

/-- **Its rewrites are those of `allHeaded`.** -/
theorem spacesAndRegions_rewrites : spacesAndRegions.rewrites = allHeaded.rewrites := by
  rfl

/-- **It is the presentation `allHeaded`**, with its root steps generated. -/
theorem spacesAndRegions_eq_allHeaded : spacesAndRegions = allHeaded := by
  rfl

/-! ## Over every list of constructors the generated root steps cover -/

variable {admits : Pattern → Bool}

/-- **An atom headed by a constructor of atoms other than the run steps to
every answer of the ambient space for it**, in the presentation over every
list of constructors that has the constructor. -/
theorem assembledOver_root_step (name : String) {constructors : List GrammarRule}
    {constructor : GrammarRule} (declared : constructor ∈ constructors)
    (takes : takesRootSteps constructor = true) {arguments : List Pattern}
    (arity : arguments.length = constructor.params.length) {ambientSpace answer : Pattern}
    (found : answer ∈ admittedAnswers admits ambientSpace (.apply constructor.label arguments)) :
    Step (regionEvaluator admits ambientSpace) (assembledOver name constructors)
      (.apply constructor.label arguments) answer :=
  generatedRoot_step (spell := spellingOf) (constructors := constructors)
    (fun _ member => mem_assembledRewrites.mpr (.inr (.inl member))) declared takes
    (spellingOf_fits constructor) arity found

/-- **And its run in a space steps to the run of every answer of that space
for it**, at every ambient space. -/
theorem assembledOver_runRoot_step (name : String) {constructors : List GrammarRule}
    {constructor : GrammarRule} (declared : constructor ∈ constructors)
    (takes : takesRootSteps constructor = true) {arguments : List Pattern}
    (arity : arguments.length = constructor.params.length) (ambientSpace : Pattern)
    {space answer : Pattern}
    (found : answer ∈ admittedAnswers admits space (.apply constructor.label arguments)) :
    Step (regionEvaluator admits ambientSpace) (assembledOver name constructors)
      (runPattern space (.apply constructor.label arguments)) (runPattern space answer) :=
  generatedRunRoot_step (spell := spellingOf) (constructors := constructors)
    (fun _ member => mem_assembledRewrites.mpr (.inr (.inr (.inr (.inl member))))) declared takes
    (spellingOf_fits constructor) arity ambientSpace found

/-! ## A hand-written list that misses a constructor -/

/-- **A constructor of atoms added later**: the pair of two atoms. -/
def pairConstructor : GrammarRule :=
  plainConstructor "prime-pair" "Atom"
    [.simple "first" (.base "Atom"), .simple "second" (.base "Atom")]

/-- The constructors of the candidate in which atoms reduce, and the pair. -/
def constructorsWithPair : List GrammarRule := atomsReduce.terms ++ [pairConstructor]

/-- **The pair, with the root steps written by hand**: the constructors with
the pair and the rewrites of `allHeaded`, which were written before the pair
was added. -/
def writtenWithPair : LanguageDef :=
  { name := "metta-prime-spaces-and-regions-pair-written-roots"
    types := [MeTTaZero.atomType, MeTTaZero.spaceType, nameType]
    terms := constructorsWithPair
    equations := [quoteDropEquation]
    rewrites := allHeaded.rewrites }

/-- **The pair, with the root steps generated**: the presentation of spaces
and regions over the constructors with the pair. -/
def generatedWithPair : LanguageDef :=
  assembledOver "metta-prime-spaces-and-regions-pair" constructorsWithPair

/-- The two have the same sorts, constructors and equation. -/
theorem withPair_same_statics :
    writtenWithPair.types = generatedWithPair.types ∧
      writtenWithPair.terms = generatedWithPair.terms ∧
        writtenWithPair.equations = generatedWithPair.equations :=
  ⟨rfl, rfl, rfl⟩

/-- The generated presentation has two rewrites more: the two root steps of
the pair. -/
theorem withPair_rewrite_counts :
    writtenWithPair.rewrites.length = 33 ∧ generatedWithPair.rewrites.length = 35 := by
  decide

/-- The root step of the pair, as the generator writes it. -/
def pairRoot : RewriteRule :=
  headedRootRule "Root:prime-pair" (.apply "prime-pair" [.fvar "part0", .fvar "part1"])

/-- The root step of a run of the pair, as the generator writes it. -/
def pairRunRoot : RewriteRule :=
  headedRunRootRule "RunRoot:prime-pair" (.apply "prime-pair" [.fvar "part0", .fvar "part1"])

/-- **The rewrites generated over the constructors with the pair**: those of
`allHeaded`, with the root step of the pair after the eight root steps and
its root step of a run after the eight root steps of a run. -/
theorem generatedWithPair_rewrites : generatedWithPair.rewrites =
    (fixedRules ++ [releaseRule]) ++ (headedRoots ++ [pairRoot]) ++ spatialCongruences ++
      (headedRunRoots ++ [pairRunRoot]) ++ [runBetaRule, runReleaseRule, runRunRule] := by
  rfl

/-- **Negative**: over the constructors with the pair the rewrites are not
those of `allHeaded`. -/
theorem generatedWithPair_rewrites_ne : generatedWithPair.rewrites ≠ allHeaded.rewrites := by
  intro same
  have lengths := congrArg List.length same
  revert lengths
  decide

/-- The rewrites of an atom pass their rows of the declaration gate, in
every language with the three sorts and the constructors with the pair. -/
theorem withPair_atomRules_checked {lang : LanguageDef}
    (types : lang.typeNames = ["Atom", "Space", "CandidateName"])
    (signatures : RewriteValidationCertificate.constructorSignatures lang =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("prime-run", 2), ("App", 2), ("Lam", 2), ("Pi", 2),
        ("prime-pair", 2)])
    (labels : RewriteValidationCertificate.constructorLabels lang =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "prime-run", "App", "Lam", "Pi", "prime-pair"]) :
    ∀ rewrite ∈ [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
        lamDomainRule, lamBodyRule, releaseRule] ++ headedRoots ++ [pairRoot],
      RewriteValidationCertificate.check lang rewrite = true := by
  intro rewrite member
  simp only [headedRoots, pairRoot, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.premiseTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      types, signatures, labels,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft, releaseRule, headedRootRule,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- The rewrites about a run pass their rows of the declaration gate, in
every such language. -/
theorem withPair_runRules_checked {lang : LanguageDef}
    (types : lang.typeNames = ["Atom", "Space", "CandidateName"])
    (signatures : RewriteValidationCertificate.constructorSignatures lang =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("prime-run", 2), ("App", 2), ("Lam", 2), ("Pi", 2),
        ("prime-pair", 2)])
    (labels : RewriteValidationCertificate.constructorLabels lang =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "prime-run", "App", "Lam", "Pi", "prime-pair"]) :
    ∀ rewrite ∈ spatialCongruences ++ headedRunRoots ++ [pairRunRoot] ++
        [runBetaRule, runReleaseRule, runRunRule],
      RewriteValidationCertificate.check lang rewrite = true := by
  intro rewrite member
  simp only [spatialCongruences, headedRunRoots, pairRunRoot, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.premiseTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      types, signatures, labels,
      betaLeft, appLeft, piLeft, lamLeft, headedRunRootRule, runAppFunctionRule,
      runAppArgumentRule, runPiDomainRule, runPiBodyRule, runLamDomainRule, runLamBodyRule,
      runBetaRule, runReleaseRule, runRunRule, runPattern,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- Every rewrite of the written presentation with the pair passes its row
of the declaration gate. -/
theorem writtenWithPair_rewrites_checked :
    ∀ rewrite ∈ writtenWithPair.rewrites,
      RewriteValidationCertificate.check writtenWithPair rewrite = true := by
  intro rewrite member
  rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
  · exact withPair_atomRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_left _ (List.mem_append_left _ plain))
  · exact withPair_atomRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_left _ (List.mem_append_right _ root))
  · exact withPair_runRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ spatial)))
  · exact withPair_runRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ runRoot)))
  · exact withPair_runRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_right _ beneath)

/-- Every rewrite of the generated presentation with the pair passes its row
of the declaration gate. -/
theorem generatedWithPair_rewrites_checked :
    ∀ rewrite ∈ generatedWithPair.rewrites,
      RewriteValidationCertificate.check generatedWithPair rewrite = true := by
  intro rewrite member
  have split : rewrite ∈ fixedRules ++ [releaseRule] ∨ rewrite ∈ headedRoots ∨
      rewrite ∈ [pairRoot] ∨ rewrite ∈ spatialCongruences ∨ rewrite ∈ headedRunRoots ∨
        rewrite ∈ [pairRunRoot] ∨ rewrite ∈ [runBetaRule, runReleaseRule, runRunRule] := by
    rw [generatedWithPair_rewrites] at member
    simp only [List.mem_append] at member ⊢
    tauto
  rcases split with plain | root | pair | spatial | runRoot | pairRun | beneath
  · exact withPair_atomRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_left _ (List.mem_append_left _ plain))
  · exact withPair_atomRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_left _ (List.mem_append_right _ root))
  · exact withPair_atomRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_right _ pair)
  · exact withPair_runRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ spatial)))
  · exact withPair_runRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ runRoot)))
  · exact withPair_runRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_left _ (List.mem_append_right _ pairRun))
  · exact withPair_runRules_checked (by decide) (by decide) (by decide) rewrite
      (List.mem_append_right _ beneath)

/-- **The written presentation with the pair passes the declaration gate.** -/
theorem writtenWithPair_validate : writtenWithPair.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks
    (RewriteValidationCertificate.validate_signature_of_plain_equations (lang := writtenWithPair)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel) writtenWithPair_rewrites_checked

/-- **The generated presentation with the pair passes the declaration gate.** -/
theorem generatedWithPair_validate : generatedWithPair.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks
    (RewriteValidationCertificate.validate_signature_of_plain_equations (lang := generatedWithPair)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel) generatedWithPair_rewrites_checked

/-- **The written heads miss the pair**: it is a declared constructor of
atoms other than the run, and it heads no written root step. -/
theorem writtenWithPair_misses :
    pairConstructor ∈ writtenWithPair.terms ∧ pairConstructor.category = "Atom" ∧
      pairConstructor.label ≠ "prime-run" ∧ pairConstructor.label ∉ atomRootHeads := by
  decide

/-- **The generated root steps cover the pair**: its root step and its root
step of a run are among the rewrites. -/
theorem generatedWithPair_covers :
    pairRoot ∈ generatedWithPair.rewrites ∧ pairRunRoot ∈ generatedWithPair.rewrites := by
  rw [generatedWithPair_rewrites]
  simp

/-! ### The step that is lost -/

/-- The pair of the unit atom with itself. -/
def unitPair : Pattern := .apply "prime-pair" [unitAtom, unitAtom]

/-- The space that stores one rule: the pair of two unit atoms is the unit
atom. -/
def pairSpace : Pattern := spaceOfAtoms [.apply "=" [unitPair, unitAtom]]

/-- That space answers the pair of two unit atoms with the unit atom. -/
theorem pairSpace_answers : unitAtom ∈ admittedAnswers anySubject pairSpace unitPair := by
  refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
  rw [show contract pairSpace = pairSpace by decide, show contract unitPair = unitPair by decide]
  refine mem_matchResults_spaceOfAtoms.mpr ⟨_, List.mem_singleton.mpr rfl, ?_⟩
  rw [atomResults_equation _ (by decide) (by decide)]
  simp [unitPair, unitAtom, asRule, asRuleList, matchPattern, matchArgs, mergeBindings,
    applyBindings]

/-- **With generated root steps the pair steps**, at the ambient space that
stores its rule. -/
theorem generatedWithPair_pair_steps :
    Step (regionEvaluator anySubject pairSpace) generatedWithPair unitPair unitAtom :=
  assembledOver_root_step (constructor := pairConstructor) _ (by decide) (by decide) (by decide)
    pairSpace_answers

/-- **And its run in that space steps**, at every ambient space. -/
theorem generatedWithPair_runPair_steps (ambientSpace : Pattern) :
    Step (regionEvaluator anySubject ambientSpace) generatedWithPair
      (runPattern pairSpace unitPair) (runPattern pairSpace unitAtom) :=
  assembledOver_runRoot_step (constructor := pairConstructor) _ (by decide) (by decide)
    (by decide) ambientSpace pairSpace_answers

/-- Every left side of `allHeaded` is headed by the run or by one of the
eight constructors of the written root steps. -/
theorem allHeaded_left_heads : ∀ rule ∈ allHeaded.rewrites,
    ∃ label parameters, rule.left = .apply label parameters ∧
      label ∈ "prime-run" :: atomRootHeads := by
  intro rule member
  rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
    rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, _, rfl, by decide⟩
  · obtain ⟨name, label, parameters, rfl, -, listed⟩ := headedRoots_shape rule root
    exact ⟨label, parameters, rfl, List.mem_cons_of_mem _ listed⟩
  · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inl spatial)
    exact ⟨_, _, shape, by decide⟩
  · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inl runRoot))
    exact ⟨_, _, shape, by decide⟩
  · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inr beneath))
    exact ⟨_, _, shape, by decide⟩

/-- Every rewrite of `allHeaded` about a run has a subject headed by the run
or by one of the eight constructors of the written root steps. -/
theorem allHeaded_runRule_subject {rule : RewriteRule}
    (member : rule ∈ spatialCongruences ∨ rule ∈ headedRunRoots ∨
      rule ∈ [runBetaRule, runReleaseRule, runRunRule]) :
    ∃ space label parameters, rule.left = runPattern space (.apply label parameters) ∧
      label ∈ "prime-run" :: atomRootHeads := by
  rcases member with spatial | runRoot | beneath
  · simp only [spatialCongruences, List.mem_cons, List.not_mem_nil, or_false] at spatial
    rcases spatial with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by decide⟩
  · obtain ⟨name, rootName, label, parameters, rfl, paired, -⟩ := headedRunRoots_shape rule runRoot
    obtain ⟨otherName, otherLabel, otherParameters, same, -, listed⟩ :=
      headedRoots_shape _ paired
    have shape : Pattern.apply label parameters = .apply otherLabel otherParameters :=
      congrArg RewriteRule.left same
    simp only [Pattern.apply.injEq] at shape
    exact ⟨_, label, parameters, rfl, List.mem_cons_of_mem _ (shape.1 ▸ listed)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at beneath
    rcases beneath with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by decide⟩

/-- **With the root steps written by hand the pair has no step**: at every
ambient space, under every evaluator, whatever its parts are. -/
theorem writtenWithPair_pair_normal (base : BasePremiseEvaluator) (arguments : List Pattern)
    (target : Pattern) : ¬ Step base writtenWithPair (.apply "prime-pair" arguments) target := by
  rintro ⟨fuel, step⟩
  cases fuel with
  | zero => cases step
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, -, -⟩ := exists_rule_of_stepAt step
      obtain ⟨label, parameters, left, listed⟩ := allHeaded_left_heads rule member
      rw [left] at matched
      refine apply_not_matched (label := label) (other := "prime-pair") ?_ matched
      rintro rfl
      exact absurd listed (by decide)

/-- **And neither has its run**, in any space, at every ambient space and
under every evaluator. -/
theorem writtenWithPair_runPair_normal (base : BasePremiseEvaluator) (space : Pattern)
    (arguments : List Pattern) (target : Pattern) :
    ¬ Step base writtenWithPair (runPattern space (.apply "prime-pair" arguments)) target := by
  rintro ⟨fuel, step⟩
  cases fuel with
  | zero => cases step
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, -, -⟩ := exists_rule_of_stepAt step
      rcases mem_allHeaded_rewrites.mp member with plain | root | rest
      · obtain ⟨label, parameters, left, listed⟩ :=
          allHeaded_left_heads rule (mem_allHeaded_rewrites.mpr (.inl plain))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · exact absurd matched (headedRoots_not_matched_run root)
      · obtain ⟨pattern, label, parameters, left, listed⟩ := allHeaded_runRule_subject rest
        rw [left] at matched
        obtain ⟨first, second, firstBindings, secondBindings, shape, -, inSubject, -⟩ :=
          matched_apply_two (label := "prime-run") matched
        obtain ⟨-, rfl⟩ := runPattern_injective shape
        refine apply_not_matched (label := label) (other := "prime-pair") ?_ inSubject
        rintro rfl
        exact absurd listed (by decide)

/-- **Nothing else differs**: every step of the presentation with the
written root steps is a step of the one with the generated root steps, at
every ambient space and under every guard. -/
theorem generatedWithPair_keeps_written {ambientSpace source target : Pattern}
    (step : Step (regionEvaluator admits ambientSpace) writtenWithPair source target) :
    Step (regionEvaluator admits ambientSpace) generatedWithPair source target :=
  Step.transport (lang := writtenWithPair) (lang' := generatedWithPair)
    (fun rule member => assembledRewrites_mono (spell := spellingOf)
      (fewer := atomsReduce.terms) (more := constructorsWithPair)
      (fun _ listed => List.mem_append_left _ listed) rule
      (show rule ∈ assembledRewrites spellingOf atomsReduce.terms from member))
    (fun _ _ _ _ _ _ answered => answered) step

#print axioms mem_assembledRewrites
#print axioms assembledRewrites_mono
#print axioms spacesAndRegions_rewrites
#print axioms spacesAndRegions_eq_allHeaded
#print axioms generatedWithPair_rewrites
#print axioms generatedWithPair_rewrites_ne
#print axioms writtenWithPair_rewrites_checked
#print axioms generatedWithPair_rewrites_checked
#print axioms withPair_atomRules_checked
#print axioms withPair_runRules_checked
#print axioms assembledOver_root_step
#print axioms assembledOver_runRoot_step
#print axioms withPair_same_statics
#print axioms withPair_rewrite_counts
#print axioms writtenWithPair_validate
#print axioms generatedWithPair_validate
#print axioms writtenWithPair_misses
#print axioms generatedWithPair_covers
#print axioms pairSpace_answers
#print axioms generatedWithPair_pair_steps
#print axioms generatedWithPair_runPair_steps
#print axioms allHeaded_left_heads
#print axioms allHeaded_runRule_subject
#print axioms writtenWithPair_pair_normal
#print axioms writtenWithPair_runPair_normal
#print axioms generatedWithPair_keeps_written

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
