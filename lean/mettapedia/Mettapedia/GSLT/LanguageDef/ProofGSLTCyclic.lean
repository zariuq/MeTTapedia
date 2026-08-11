import Mettapedia.GSLT.LanguageDef.ProofGSLTAmbient

/-!
# Cyclic pre-proofs: where the automaton goes

A proof need not be a finite tree.  In fixed-point logics — the modal
`mu`-calculus, and every system with inductive and coinductive definitions —
the natural proof object is a **finite graph with back edges**: a derivation
whose open leaves point back at an ancestor.  Such an object denotes an
infinite regular tree.  Whether that tree is a proof is decided by a
condition on its infinite paths, and that condition is checked by an
automaton rather than by a fold over nodes.

This module locates that discipline inside the present framework and proves
exactly what it costs.

The first observation is that no new format is needed.  A cyclic pre-proof
cut at its back edges is an *open* derivation whose open context lists the
companion judgments, and `RawOpenProof.premise` is already the back edge.
The machinery is present.

What is absent is the **discharge principle**: the licence to pass from an
open pre-proof of `J` from `J` to a closed proof of `J`.  The central result
below is that this licence cannot be indexed by provability, because the
one-node pre-proof `premise 0` witnesses `J` from `J` for *every* pattern
whatsoever — including patterns that are not judgments of the presentation
at all.  A discharge rule triggered by the mere existence of a circular
pre-proof therefore proves everything.

That is not a defect of this fixture.  It is the reason cyclic proof theory
is unavoidably proof-relevant, and it is the ambient/shadow distinction
arriving from an entirely independent direction: discharge must inspect the
proof object, so a framework that truncates derivations to provability
cannot express fixed-point reasoning at all.

The rest of the module measures the gap.  Both a sound coinductive cycle and
an unsound inductive one pass every local check; both unfold to arbitrary
finite depth with every unfolding accepted; and the accepted unfoldings never
lose the open leaf.  So the global condition is not the limit of the local
ones — which is precisely why it is an automaton and not a fold.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.Cyclic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofGSLT

/-! ## The back edge is already in the format

`RawOpenProof.premise i` cites the `i`th open assumption.  Cutting a cyclic
pre-proof at its back edges turns each companion into exactly such a
citation, so the existing open-proof format carries cyclic pre-proofs with no
extension.  The following holds of every presentation and every pattern — it
is the trivial companion, and its unrestricted generality is the whole
problem. -/
theorem identity_open_proof_checks (presentation : ValidatedPresentation)
    (goal : Pattern) :
    checkOpenRaw presentation [goal] goal (.premise 0) = true := by
  rw [checkOpenRaw]
  simp

/-- Circular checkability is therefore *universal*: for any presentation and
any pattern at all, some pre-proof takes that pattern from itself. -/
theorem circular_checkability_is_universal
    (presentation : ValidatedPresentation) (goal : Pattern) :
    ∃ proof, checkOpenRaw presentation [goal] goal proof = true :=
  ⟨.premise 0, identity_open_proof_checks presentation goal⟩

/-! ## A two-polarity fixture

One body, two fixed points over it, and the fold/unfold pair for each.  Every
rule is sound read as a rule: a least and a greatest fixed point both satisfy
their unfolding equation.  The presentation deliberately has **no axioms**,
so it derives nothing outright; all the interest is in what cycles are
allowed to conclude. -/

private def tmType : TypeDecl := TypeDecl.plain "Tm"

private def constructor0 (label : String) : GrammarRule :=
  { label := label, category := "Tm", params := [], syntaxPattern := [] }

private def constructor1 (label : String) : GrammarRule :=
  { label := label, category := "Tm"
    params := [.simple "arg" (.base "Tm")], syntaxPattern := [] }

/-- The greatest fixed point. -/
def nuFormula : Pattern := .apply "cy-nu" []

/-- The least fixed point. -/
def muFormula : Pattern := .apply "cy-mu" []

/-- The shared body, applied to a fixed point. -/
def body (argument : Pattern) : Pattern := .apply "cy-body" [argument]

/-- The single judgment form. -/
def holds (formula : Pattern) : Pattern := .apply "Holds" [formula]

/-- A pattern that is not a judgment of the presentation.  Used to show that
unrestricted discharge proves genuine nonsense, not merely unprovable
judgments. -/
def bogus : Pattern := .apply "cy-bogus" []

private def cyclicTerms : List GrammarRule :=
  [constructor0 "cy-nu", constructor0 "cy-mu", constructor0 "cy-bogus",
    constructor1 "cy-body"]

private def cyclicJudgments : List JudgmentDecl := [{ head := "Holds", arity := 1 }]

/-- Greatest-fixed-point unfolding.  On a cycle this is the *productive*
step: it is what licenses coinduction. -/
private def nuUnfold : RuleSchema :=
  { id := ⟨"cy-nu-unfold"⟩
    metavariables := []
    premises := [holds nuFormula]
    conclusion := holds (body nuFormula)
    sideConditions := [] }

/-- Greatest-fixed-point folding. -/
private def nuFold : RuleSchema :=
  { id := ⟨"cy-nu-fold"⟩
    metavariables := []
    premises := [holds (body nuFormula)]
    conclusion := holds nuFormula
    sideConditions := [] }

/-- Least-fixed-point unfolding.  Structurally identical to its greatest
counterpart, and on a cycle it licenses nothing. -/
private def muUnfold : RuleSchema :=
  { id := ⟨"cy-mu-unfold"⟩
    metavariables := []
    premises := [holds muFormula]
    conclusion := holds (body muFormula)
    sideConditions := [] }

/-- Least-fixed-point folding. -/
private def muFold : RuleSchema :=
  { id := ⟨"cy-mu-fold"⟩
    metavariables := []
    premises := [holds (body muFormula)]
    conclusion := holds muFormula
    sideConditions := [] }

private def cyclicLanguage : LanguageDef :=
  { name := "cyclic-fixed-point"
    types := [tmType]
    terms := cyclicTerms
    equations := []
    rewrites := [] }

private def cyclicCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  { judgments := cyclicJudgments
    rules := [nuUnfold, nuFold, muUnfold, muFold] }

private def cyclic : Presentation :=
  { language := cyclicLanguage, calculus := cyclicCalculus }

private theorem cyclic_validate : cyclic.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [cyclic, cyclicLanguage, tmType, cyclicTerms, constructor0,
      constructor1, LanguageDef.typeNames, TermParam.typeExpr,
      TypeExpr.baseNames, TypeDecl.plain]

theorem cyclic_valid : cyclic.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [cyclic_validate]
  simp [cyclic, cyclicCalculus, cyclicLanguage, tmType, cyclicTerms, constructor0,
    constructor1, nuUnfold, nuFold, muUnfold, muFold, holds, body,
    nuFormula, muFormula, cyclicJudgments,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.ruleIds, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Presentation.conversionDeclarationValid]
  decide

/-- The fixture presentation, admitted. -/
def cyclicValidated : ValidatedPresentation := ⟨cyclic, cyclic_valid⟩

/-! ## The discharge principle cannot be indexed by provability

Every rule of the fixture concludes a `Holds` judgment, so nothing derives
`bogus`.  This needs no induction: one rule application already fixes the
head of the conclusion. -/
/-- **The fixture proves nothing at all.**  Interpret every judgment as
false.  Each rule has a premise, so every rule application is vacuously
sound, and the generic soundness boundary then rules out closed derivations
outright.

This is the semantic complement to the syntactic result below: circular
pre-proofs of `Holds nu` and `Holds mu` both exist and both check, while
neither judgment has any closed proof.  Discharge is therefore not a
derivable convenience — it is the entire content of cyclic proof. -/
theorem no_closed_derivation {goal : Pattern}
    (derivation : Derivation cyclicValidated goal) : False := by
  refine Derivation.sound_of_ruleApplications (fun _ => False) ?_ derivation
  intro ruleInstance premises conclusion application allPremises
  have premisesNil : premises = [] := by
    rcases premises with _ | ⟨head, tail⟩
    · rfl
    · exact absurd (allPremises head (by simp)) id
  subst premisesNil
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  simp only [instantiateRule?] at executable
  cases lookup : cyclicValidated.1.lookupRule? ruleInstance.ruleId with
  | none => simp [lookup] at executable
  | some rule =>
      simp only [lookup] at executable
      have ruleCases : rule = nuUnfold ∨ rule = nuFold ∨
          rule = muUnfold ∨ rule = muFold := by
        have member := List.mem_of_find?_eq_some lookup
        simpa [cyclicValidated, cyclic, cyclicCalculus, cyclicLanguage] using member
      rcases ruleCases with rfl | rfl | rfl | rfl <;>
        simp [nuUnfold, nuFold, muUnfold, muFold,
          RuleSchema.sideConditionsHold, instantiateSchemas?,
          instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
          holds, body, nuFormula, muFormula] at executable

theorem no_derivation_of_bogus :
    ¬ Nonempty (Derivation cyclicValidated bogus) := by
  rintro ⟨derivation⟩
  exact no_closed_derivation derivation

/-- **The central result.**  No discharge principle indexed by the
*existence* of a circular pre-proof can be sound, because circular
checkability holds of every pattern whatsoever.  Applied to a pattern that
is not even a judgment, such a principle proves nonsense.

The discharge licence must therefore consult the pre-proof itself.  This is
the ambient/shadow distinction arriving from fixed-point logic: a framework
that keeps only provability cannot state the condition that makes cyclic
reasoning sound, so it cannot host fixed-point reasoning at all. -/
theorem discharge_cannot_factor_through_provability :
    ¬ ∀ goal : Pattern,
        (∃ proof, checkOpenRaw cyclicValidated [goal] goal proof = true) →
        Nonempty (Derivation cyclicValidated goal) := by
  intro discharge
  exact no_derivation_of_bogus
    (discharge bogus (circular_checkability_is_universal cyclicValidated bogus))

/-! ## Two cycles that no local check separates -/

private def nuUnfoldInstance : RuleInstance := ⟨⟨"cy-nu-unfold"⟩, []⟩
private def nuFoldInstance : RuleInstance := ⟨⟨"cy-nu-fold"⟩, []⟩
private def muUnfoldInstance : RuleInstance := ⟨⟨"cy-mu-unfold"⟩, []⟩
private def muFoldInstance : RuleInstance := ⟨⟨"cy-mu-fold"⟩, []⟩

private theorem nuUnfold_instantiates :
    instantiateRule? cyclicValidated nuUnfoldInstance =
      some ([holds nuFormula], holds (body nuFormula)) := by
  simp [instantiateRule?, cyclicValidated, cyclic, cyclicLanguage,
    cyclicCalculus, nuUnfoldInstance, nuUnfold, nuFold, muUnfold, muFold,
    Presentation.lookupRule?, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, holds, body, nuFormula]

private theorem nuFold_instantiates :
    instantiateRule? cyclicValidated nuFoldInstance =
      some ([holds (body nuFormula)], holds nuFormula) := by
  simp [instantiateRule?, cyclicValidated, cyclic, cyclicLanguage,
    cyclicCalculus, nuFoldInstance, nuUnfold, nuFold, muUnfold, muFold,
    Presentation.lookupRule?, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, holds, body, nuFormula]

private theorem muUnfold_instantiates :
    instantiateRule? cyclicValidated muUnfoldInstance =
      some ([holds muFormula], holds (body muFormula)) := by
  simp [instantiateRule?, cyclicValidated, cyclic, cyclicLanguage,
    cyclicCalculus, muUnfoldInstance, nuUnfold, nuFold, muUnfold, muFold,
    Presentation.lookupRule?, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, holds, body, muFormula]

private theorem muFold_instantiates :
    instantiateRule? cyclicValidated muFoldInstance =
      some ([holds (body muFormula)], holds muFormula) := by
  simp [instantiateRule?, cyclicValidated, cyclic, cyclicLanguage,
    cyclicCalculus, muFoldInstance, nuUnfold, nuFold, muUnfold, muFold,
    Presentation.lookupRule?, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, holds, body, muFormula]

/-- The coinductive cycle: unfold the greatest fixed point, then fold it
back.  Read as a graph, the leaf is a back edge to the root. -/
def nuCycle : RawOpenProof :=
  .node nuFoldInstance [.node nuUnfoldInstance [.premise 0]]

/-- The inductive cycle.  Structurally identical, opposite polarity. -/
def muCycle : RawOpenProof :=
  .node muFoldInstance [.node muUnfoldInstance [.premise 0]]

theorem nuCycle_checks :
    checkOpenRaw cyclicValidated [holds nuFormula] (holds nuFormula) nuCycle
      = true := by
  simp only [nuCycle, checkOpenRaw, nuFold_instantiates, nuUnfold_instantiates,
    checkOpenRawChildren]
  simp

theorem muCycle_checks :
    checkOpenRaw cyclicValidated [holds muFormula] (holds muFormula) muCycle
      = true := by
  simp only [muCycle, checkOpenRaw, muFold_instantiates, muUnfold_instantiates,
    checkOpenRawChildren]
  simp

/-! ## The unfoldings

A cyclic pre-proof denotes an infinite regular tree.  Its finite
approximations are obtained by unwinding the back edge a bounded number of
times, and the open leaf survives every one of them. -/

/-- **The cyclic object read as a generator.**  A cycle body is a function
from a pre-proof to a pre-proof; unwinding iterates it from the trivial
companion.  This is the finite-state reading: the back edge is the loop, and
the loop body is the transition. -/
def unwindCycle (step : RawOpenProof → RawOpenProof) : Nat → RawOpenProof
  | 0 => .premise 0
  | n + 1 => step (unwindCycle step n)

/-- **Generator correctness, in general.**  If the cycle body preserves
checking against a fixed goal and context, then *every* depth it emits is
accepted.  A fixed finite description therefore certifies an infinite family
of finite open proofs — and nothing in this statement mentions which fixed
point is involved, which is exactly why acceptance cannot separate the two
polarities. -/
theorem unwindCycle_checks {presentation : ValidatedPresentation}
    {goal : Pattern} {step : RawOpenProof → RawOpenProof}
    (stepPreserves : ∀ proof, checkOpenRaw presentation [goal] goal proof = true →
      checkOpenRaw presentation [goal] goal (step proof) = true) (n : Nat) :
    checkOpenRaw presentation [goal] goal (unwindCycle step n) = true := by
  induction n with
  | zero => exact identity_open_proof_checks presentation goal
  | succ n inductionHypothesis => exact stepPreserves _ inductionHypothesis

/-- The coinductive cycle body. -/
def nuStep (proof : RawOpenProof) : RawOpenProof :=
  .node nuFoldInstance [.node nuUnfoldInstance [proof]]

/-- The inductive cycle body. -/
def muStep (proof : RawOpenProof) : RawOpenProof :=
  .node muFoldInstance [.node muUnfoldInstance [proof]]

/-- The `n`-fold unwinding of the coinductive cycle. -/
def nuUnwind (n : Nat) : RawOpenProof := unwindCycle nuStep n

/-- The `n`-fold unwinding of the inductive cycle. -/
def muUnwind (n : Nat) : RawOpenProof := unwindCycle muStep n

mutual

/-- How many open assumptions the pre-proof still cites. -/
def openLeafCount : RawOpenProof → Nat
  | .premise _ => 1
  | .node _ children => openLeafCountList children

/-- Ordered-child companion of `openLeafCount`. -/
def openLeafCountList : List RawOpenProof → Nat
  | [] => 0
  | proof :: proofs => openLeafCount proof + openLeafCountList proofs

end

/-- **Every finite unwinding of the coinductive cycle is accepted.**  The
finite graph is a finite presentation of an infinite family of finite open
proofs — this is the sense in which one may compute with the infinite object
by holding only a finite one. -/
theorem nuUnwind_checks (n : Nat) :
    checkOpenRaw cyclicValidated [holds nuFormula] (holds nuFormula)
      (nuUnwind n) = true := by
  refine unwindCycle_checks (fun proof checks => ?_) n
  simp only [nuStep, checkOpenRaw, nuFold_instantiates, nuUnfold_instantiates,
    checkOpenRawChildren]
  simp [checks]

/-- **And every finite unwinding of the inductive cycle is accepted too.**
Local checking never separates the two polarities, at any depth. -/
theorem muUnwind_checks (n : Nat) :
    checkOpenRaw cyclicValidated [holds muFormula] (holds muFormula)
      (muUnwind n) = true := by
  refine unwindCycle_checks (fun proof checks => ?_) n
  simp only [muStep, checkOpenRaw, muFold_instantiates, muUnfold_instantiates,
    checkOpenRawChildren]
  simp [checks]

/-- Unwinding costs rule nodes linearly, so the cyclic pre-proof is a strictly
more compact presentation of the same family the deeper one goes. -/
theorem nuUnwind_ruleCount (n : Nat) : (nuUnwind n).ruleCount = 2 * n := by
  induction n with
  | zero => simp [nuUnwind, unwindCycle, RawOpenProof.ruleCount]
  | succ n inductionHypothesis =>
      simp only [nuUnwind, unwindCycle, nuStep, RawOpenProof.ruleCount]
      simp only [nuUnwind] at inductionHypothesis
      simp [RawOpenProof.ruleCount, inductionHypothesis]
      omega

/-- The open leaf is never discharged by unwinding: the assumption is present
at every finite depth.  Acceptance of all finite approximations therefore
does not converge to a closed proof, which is exactly why the fixed-point
condition is a statement about infinite paths rather than the limit of the
finite checks. -/
theorem nuUnwind_still_open (n : Nat) :
    openLeafCount (nuUnwind n) = 1 := by
  induction n with
  | zero => simp [nuUnwind, unwindCycle, openLeafCount]
  | succ n inductionHypothesis =>
      simp only [nuUnwind, unwindCycle, nuStep]
      simp only [nuUnwind] at inductionHypothesis
      simpa [openLeafCount, openLeafCountList] using inductionHypothesis

/-- The generated family is unbounded while its generator is fixed.  That
gap is the practical payoff of holding the cycle rather than an unwinding:
replay follows the back edge in bounded memory, and the depth is a run-time
parameter rather than a property of the stored artefact. -/
theorem unwinding_is_unbounded (bound : Nat) :
    ∃ n, bound < (nuUnwind n).ruleCount := by
  refine ⟨bound + 1, ?_⟩
  rw [nuUnwind_ruleCount]
  omega

/-! ## The guard, and why it is not a local check

The condition that separates the two cycles is a property of the *rules
traversed on the cycle*, not of the endpoints.  Reading it off a pre-proof is
immediate; the point is that no function of the checker's verdict can
compute it. -/

/-- Which fixed point a rule belongs to.  On a cycle, a greatest-fixed-point
unfolding is productive and licenses discharge; a least-fixed-point unfolding
does not. -/
inductive FixedPointPolarity where
  | greatest
  | least
  | neutral
deriving Repr, DecidableEq

/-- The polarity declaration for the fixture. -/
def polarityOf (id : RuleId) : FixedPointPolarity :=
  if id = ⟨"cy-nu-unfold"⟩ then .greatest
  else if id = ⟨"cy-mu-unfold"⟩ then .least
  else .neutral

mutual

/-- Every rule identifier occurring in an open pre-proof. -/
def proofRuleIds : RawOpenProof → List RuleId
  | .premise _ => []
  | .node ruleInstance children =>
      ruleInstance.ruleId :: proofRuleIdsList children

/-- Ordered-child companion of `proofRuleIds`. -/
def proofRuleIdsList : List RawOpenProof → List RuleId
  | [] => []
  | proof :: proofs => proofRuleIds proof ++ proofRuleIdsList proofs

end

/-- Discharge is licensed when the cycle passes through a greatest-fixed-point
unfolding and through no least-fixed-point unfolding.  This is the fixture's
instance of the trace condition of cyclic proof theory; in general the
condition ranges over infinite paths and is decided by an automaton, and the
present form is what that automaton reports on a single simple cycle. -/
def dischargeLicensed (proof : RawOpenProof) : Bool :=
  (proofRuleIds proof).any (fun id => polarityOf id == .greatest) &&
    !(proofRuleIds proof).any (fun id => polarityOf id == .least)

theorem nuCycle_licensed : dischargeLicensed nuCycle = true := by
  simp [dischargeLicensed, nuCycle, proofRuleIds, proofRuleIdsList, nuFoldInstance, nuUnfoldInstance, polarityOf]

theorem muCycle_not_licensed : dischargeLicensed muCycle = false := by
  simp [dischargeLicensed, muCycle, proofRuleIds, proofRuleIdsList, muFoldInstance, muUnfoldInstance, polarityOf]

/-- The trivial companion is refused: it traverses no rule at all, so there is
nothing productive on the cycle. -/
theorem identity_not_licensed : dischargeLicensed (.premise 0) = false := by
  simp [dischargeLicensed, proofRuleIds]

/-- **The guard is not a local check.**  The trivial companion and the
coinductive cycle prove the *same goal from the same context*, both are
accepted, and they receive opposite verdicts.  So the discharge licence is
not a function of the goal, the context, and the checker's answer — it reads
the derivation.  Any implementation that hands the checker only its verdict
has thrown away what the licence needs. -/
theorem guard_not_determined_by_goal_and_acceptance :
    ¬ ∃ verdict : Pattern → List Pattern → Bool → Bool,
        ∀ proof : RawOpenProof,
          ∀ context goal,
            checkOpenRaw cyclicValidated context goal proof = true →
            verdict goal context
                (checkOpenRaw cyclicValidated context goal proof) =
              dischargeLicensed proof := by
  rintro ⟨verdict, agrees⟩
  have identityCase :=
    agrees (.premise 0) [holds nuFormula] (holds nuFormula)
      (identity_open_proof_checks _ _)
  have cycleCase :=
    agrees nuCycle [holds nuFormula] (holds nuFormula) nuCycle_checks
  rw [identity_open_proof_checks, identity_not_licensed] at identityCase
  rw [nuCycle_checks, nuCycle_licensed] at cycleCase
  rw [identityCase] at cycleCase
  exact Bool.false_ne_true cycleCase

/-! ## Where the side condition lives

Side conditions in this framework come at three strengths, and the fixture
above is the first thing in the tree that needs the third.

* **Per-step, argument-local.**  `RuleSchema.sideConditionsHold` reads only
  the arguments of one rule instance.  Everything built so far is here.
* **Per-step against a global frame.**  A step is checked locally, but
  against data carried by the whole article — Metamath's distinct-variable
  conditions are of this kind.  Acceptance stays a fold.
* **Genuinely global.**  The condition quantifies over paths of the proof
  graph and is not the limit of any sequence of per-step checks.  Fixed-point
  discharge is of this kind, by `guard_not_determined_by_goal_and_acceptance`.

Only the third strength requires new trusted machinery, and this module
delimits what that machinery must be handed: the derivation, not its
verdict. -/
inductive SideConditionStrength where
  | argumentLocal
  | stepAgainstFrame
  | globalOverPaths
deriving Repr, DecidableEq

/-- The fixture's discharge condition sits at the strongest level, and the
separation theorem above is what places it there. -/
def dischargeStrength : SideConditionStrength := .globalOverPaths

end Mettapedia.GSLT.LanguageDef.ProofGSLT.Cyclic
