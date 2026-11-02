import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
import Mettapedia.GSLT.LanguageDef.EquationOccurrence
import Mettapedia.GSLT.LanguageDef.MeTTaILSubtermMatchAutomata
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderContextualExecution
import Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution
import Mettapedia.GSLT.Core.RouteTrace

/-!
# Occurrence-preserving execution of first-order authored equations

Equation orientations are matching work, never entries added to the directed
rewrite list. The admitted fragment uses the existing first-order pattern and
relation-premise plans. Scoped binding metadata is refused, rather than erased.

The executable receipts retain the physical declaration occurrence, orientation,
initial and completed bindings, the ordinal chosen at every premise, and the
constructed target. Premise ordinals decorate the canonical ordered query fold;
they do not define another premise evaluator or equality relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open MeTTaILFirstOrderRuleCompilation
open EquationSemantics

/-- Adapt the canonical occurrence orientation to the existing equation-to-rule
matching adapter. Its treatment of binding sites remains authoritative. -/
def equationRule (equation : Equation) : EquationOrientation → RewriteRule
  | .forward => ScopedEquationExecution.orientedRule equation .forward
  | .reverse => ScopedEquationExecution.orientedRule equation .reverse

/-- Read back an admitted forward plan as its authored equation. -/
def equationOfPlan (plan : RulePlan) : Equation :=
  { name := plan.name
    typeContext := plan.typeContext
    premises := erasePremisePlans plan.premises
    left := plan.left.erase
    right := plan.right.erase }

@[simp] theorem equationRule_forward_plan (plan : RulePlan) :
    equationRule (equationOfPlan plan) .forward = plan.erase := rfl

/-- Reverse matching reuses the same premise plans and administrative fields. -/
def orientedPlan (plan : RulePlan) : EquationOrientation → RulePlan
  | .forward => plan
  | .reverse => { plan with left := plan.right, right := plan.left }

@[simp] theorem orientedPlan_erase (plan : RulePlan) (orientation : EquationOrientation) :
    (orientedPlan plan orientation).erase = equationRule (equationOfPlan plan) orientation := by
  cases orientation <;> rfl

@[simp] theorem orientedPlan_premises (plan : RulePlan) (orientation : EquationOrientation) :
    (orientedPlan plan orientation).premises = plan.premises := by
  cases orientation <;> rfl

/-- Compile only the forward matching view; exact readback subsequently admits
both orientations without making either a directed language rule. -/
def compileEquation? (equation : Equation) : Option RulePlan :=
  compileRule? (equationRule equation .forward)

theorem compileEquation?_annotated_none (equation : Equation)
    (spec : RuleBindingSpec) (annotated : equation.bindings = some spec) :
    compileEquation? equation = none := by
  apply compileRule?_annotated_none _ spec
  exact annotated

theorem equation_of_compileEquation? (equation : Equation) (plan : RulePlan)
    (accepted : compileEquation? equation = some plan) : (equationOfPlan plan) = equation := by
  have erased := erase_of_compileRule? (equationRule equation .forward) plan accepted
  cases equation
  cases plan
  simp only [equationRule, ScopedEquationExecution.orientedRule, RulePlan.erase,
    RewriteRule.mk.injEq] at erased
  rcases erased with ⟨name, types, premises, left, right, bindings⟩
  simp only [equationOfPlan, Equation.mk.injEq]
  exact ⟨name, types, premises, left, right, bindings⟩

def compileEquations? : List Equation → Option (List RulePlan)
  | [] => some []
  | equation :: equations => do
      let plan ← compileEquation? equation
      let plans ← compileEquations? equations
      pure (plan :: plans)

theorem equations_of_compileEquations? (source : List Equation) (plans : List RulePlan)
    (accepted : compileEquations? source = some plans) :
    plans.map equationOfPlan = source := by
  induction source generalizing plans with
  | nil => simp [compileEquations?] at accepted; subst plans; rfl
  | cons equation equations ih =>
      cases head : compileEquation? equation with
      | none => simp [compileEquations?, head] at accepted
      | some plan =>
          cases tail : compileEquations? equations with
          | none => simp [compileEquations?, head, tail] at accepted
          | some rest =>
              simp [compileEquations?, head, tail] at accepted
              subst plans
              simp only [List.map_cons, equation_of_compileEquation? equation plan head,
                ih rest tail]

/-- Exact ordered admission of the authored equation list. Existing `RulePlan`
is the executable row carrier; the source identity remains an equation. -/
structure EquationProgram (source : List Equation) where
  plans : List RulePlan
  equations_eq_source : plans.map equationOfPlan = source

def compileEquationProgram? (source : List Equation) : Option (EquationProgram source) :=
  match accepted : compileEquations? source with
  | none => none
  | some plans => some ⟨plans, equations_of_compileEquations? source plans accepted⟩

theorem EquationProgram.bindingMetadata_none {source : List Equation}
    (program : EquationProgram source) :
    ∀ equation ∈ source, equation.bindings = none := by
  intro equation member
  rw [← program.equations_eq_source] at member
  obtain ⟨plan, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Ordinals decorate the ordered alternatives produced by an existing query. -/
def traceBranches (next : Nat) (choices : List Bindings)
    (continuation : Bindings → List (List Nat × Bindings)) : List (List Nat × Bindings) :=
  (choices.zipIdx next).flatMap fun branch =>
    (continuation branch.1).map fun trace => (branch.2 :: trace.1, trace.2)

/-- The canonical premise fold with its completed-branch ordinals retained. -/
def premiseTraces (relations : RelationEnv) (language : LanguageDef) :
    List PremisePlan → Bindings → List (List Nat × Bindings)
  | [], seed => [([], seed)]
  | plan :: plans, seed =>
      traceBranches 0 (plan.run relations language seed)
        (premiseTraces relations language plans)

theorem traceBranches_projection (next : Nat) (choices : List Bindings)
    (continuation : Bindings → List (List Nat × Bindings)) :
    (traceBranches next choices continuation).map Prod.snd =
      choices.flatMap (fun seed => (continuation seed).map Prod.snd) := by
  unfold traceBranches
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  have mapped := congrArg (List.flatMap (fun seed => (continuation seed).map Prod.snd))
    (List.zipIdx_map_fst next choices)
  simpa only [List.flatMap_map, Function.comp_def] using mapped

/-- Removing only the provenance decoration recovers the existing canonical
premise fold, with its complete authored order and multiplicity. -/
theorem premiseTraces_projection (relations : RelationEnv) (language : LanguageDef)
    (plans : List PremisePlan) (seed : Bindings) :
    (premiseTraces relations language plans seed).map Prod.snd =
      runPremisePlans relations language plans seed := by
  induction plans generalizing seed with
  | nil => rfl
  | cons plan plans ih =>
      rw [premiseTraces, traceBranches_projection, runPremisePlans]
      congr 1
      funext next
      exact ih next

/-- Replay checks every branch ordinal; missing, future or extra ordinals are
refused. Branches refer to the completed canonical query list, not raw rows. -/
def replayPremises? (relations : RelationEnv) (language : LanguageDef) :
    List PremisePlan → Bindings → List Nat → Option Bindings
  | [], seed, [] => some seed
  | plan :: plans, seed, choice :: choices => do
      let next ← (plan.run relations language seed)[choice]?
      replayPremises? relations language plans next choices
  | _, _, _ => none

theorem mem_traceBranches_zero (choices : List Bindings)
    (continuation : Bindings → List (List Nat × Bindings)) (path : List Nat) (result : Bindings) :
    (path, result) ∈ traceBranches 0 choices continuation ↔
      ∃ choice rest next, path = choice :: rest ∧ choices[choice]? = some next ∧
        (rest, result) ∈ continuation next := by
  simp only [traceBranches, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨next, choice⟩, member, ⟨⟨rest, final⟩, continuationd, same⟩⟩
    cases same
    exact ⟨choice, rest, next, rfl, List.mk_mem_zipIdx_iff_getElem?.mp member, continuationd⟩
  · rintro ⟨choice, rest, next, rfl, found, continuationd⟩
    exact ⟨(next, choice), List.mk_mem_zipIdx_iff_getElem?.mpr found,
      (rest, result), continuationd, rfl⟩

theorem replayPremises?_iff (relations : RelationEnv) (language : LanguageDef)
    (plans : List PremisePlan) (seed : Bindings) (path : List Nat) (result : Bindings) :
    replayPremises? relations language plans seed path = some result ↔
      (path, result) ∈ premiseTraces relations language plans seed := by
  induction plans generalizing seed path with
  | nil => cases path <;> simp [replayPremises?, premiseTraces, eq_comm]
  | cons plan plans ih =>
      rw [premiseTraces, mem_traceBranches_zero]
      cases path with
      | nil => simp [replayPremises?]
      | cons choice choices =>
          simp only [List.cons.injEq, exists_and_left]
          cases found : (plan.run relations language seed)[choice]? with
          | none => simp [replayPremises?, found]
          | some next => simp [replayPremises?, found, ih]

/-- A concrete equation receipt, whose fields are all checked by replay. -/
structure Receipt where
  equationIndex : Nat
  orientation : EquationOrientation
  initialBindings : Bindings
  choices : List Nat
  finalBindings : Bindings
  target : Pattern
deriving DecidableEq, Repr

/-- Execute one equation orientation, decorating the canonical matching and
premise results rather than replacing their semantics. -/
def rowReceipts (relations : RelationEnv) (language : LanguageDef) (index : Nat)
    (orientation : EquationOrientation) (plan : RulePlan) (source : Pattern) : List Receipt :=
  let oriented := orientedPlan plan orientation
  (oriented.left.run source).flatMap fun initial =>
    (premiseTraces relations language oriented.premises initial).map fun trace =>
      ⟨index, orientation, initial, trace.1, trace.2, oriented.right.instantiate trace.2⟩

/-- Search order is authored declaration order, forward then reverse, followed
by canonical matching and each premise's authored alternative order. -/
def rootReceipts (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : Pattern) : List Receipt :=
  plans.zipIdx.flatMap fun row =>
    rowReceipts relations language row.2 .forward row.1 source ++
      rowReceipts relations language row.2 .reverse row.1 source

theorem mem_rowReceipts_iff (relations : RelationEnv) (language : LanguageDef) (index : Nat)
    (orientation : EquationOrientation) (plan : RulePlan) (source : Pattern) (receipt : Receipt) :
    receipt ∈ rowReceipts relations language index orientation plan source ↔
      receipt.equationIndex = index ∧ receipt.orientation = orientation ∧
      receipt.initialBindings ∈ (orientedPlan plan orientation).left.run source ∧
      (receipt.choices, receipt.finalBindings) ∈
        premiseTraces relations language plan.premises receipt.initialBindings ∧
      (orientedPlan plan orientation).right.instantiate receipt.finalBindings = receipt.target := by
  cases receipt
  simp only [rowReceipts, List.mem_flatMap, List.mem_map, Receipt.mk.injEq,
    orientedPlan_premises]
  aesop

theorem mem_rootReceipts_iff (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : Pattern) (receipt : Receipt) :
    receipt ∈ rootReceipts relations language plans source ↔
      ∃ plan, plans[receipt.equationIndex]? = some plan ∧
        receipt ∈ rowReceipts relations language receipt.equationIndex receipt.orientation plan source := by
  simp only [rootReceipts, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨⟨plan, index⟩, declared, produced | produced⟩
    · have fields := (mem_rowReceipts_iff relations language index .forward plan source receipt).mp produced
      rw [fields.1]
      refine ⟨plan, List.mk_mem_zipIdx_iff_getElem?.mp declared, ?_⟩
      simpa only [fields.2.1] using produced
    · have fields := (mem_rowReceipts_iff relations language index .reverse plan source receipt).mp produced
      rw [fields.1]
      refine ⟨plan, List.mk_mem_zipIdx_iff_getElem?.mp declared, ?_⟩
      simpa only [fields.2.1] using produced
  · rintro ⟨plan, declared, produced⟩
    refine ⟨(plan, receipt.equationIndex), List.mk_mem_zipIdx_iff_getElem?.mpr declared, ?_⟩
    cases orientation : receipt.orientation with
    | forward => exact Or.inl (by simpa only [orientation] using produced)
    | reverse => exact Or.inr (by simpa only [orientation] using produced)

/-- Validation within an already selected oriented row checks the canonical
matching seed, every premise choice, completed bindings and actual target. -/
def validateRowReceipt? (relations : RelationEnv) (language : LanguageDef)
    (plan : RulePlan) (source : Pattern) (initial : Bindings) (choices : List Nat)
    (completed : Bindings) (claimed : Pattern) : Option Pattern := do
  guard (initial ∈ plan.left.run source)
  let final ← replayPremises? relations language plan.premises initial choices
  guard (final = completed)
  let actual := plan.right.instantiate final
  guard (actual = claimed)
  pure actual

/-- Validation checks the physical row and its explicit orientation before
checking the whole canonical instance witness. -/
def validateReceipt? (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : Pattern) (receipt : Receipt) : Option Pattern := do
  let plan ← plans[receipt.equationIndex]?
  validateRowReceipt? relations language (orientedPlan plan receipt.orientation) source
    receipt.initialBindings receipt.choices receipt.finalBindings receipt.target

theorem validateReceipt?_iff (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : Pattern) (receipt : Receipt) (target : Pattern) :
    validateReceipt? relations language plans source receipt = some target ↔
      receipt ∈ rootReceipts relations language plans source ∧ target = receipt.target := by
  rw [mem_rootReceipts_iff]
  cases declared : plans[receipt.equationIndex]? with
  | none => simp [validateReceipt?, declared]
  | some plan =>
      simp only [Option.some.injEq]
      simp only [exists_eq_left' ]
      rw [mem_rowReceipts_iff]
      cases replayed : replayPremises? relations language plan.premises receipt.initialBindings receipt.choices with
      | none =>
          have absent : (receipt.choices, receipt.finalBindings) ∉
              premiseTraces relations language plan.premises receipt.initialBindings := by
            rw [← replayPremises?_iff, replayed]
            simp
          simp [validateReceipt?, validateRowReceipt?, declared, orientedPlan_premises, replayed, absent]
      | some final =>
          have trace := replayPremises?_iff relations language plan.premises
            receipt.initialBindings receipt.choices receipt.finalBindings
          rw [replayed] at trace
          simp only [Option.some.injEq] at trace
          by_cases same : final = receipt.finalBindings
          · subst final
            have traced := trace.mp rfl
            simp [validateReceipt?, validateRowReceipt?, declared, orientedPlan_premises, replayed, guard, traced]
            aesop
          · have absent := mt trace.mpr same
            simp [validateReceipt?, validateRowReceipt?, declared, orientedPlan_premises, replayed, guard, same, absent]

/-- Refusal is exactly absence from the witnessed frontier, not a conclusion
that two terms are inequivalent. -/
theorem validateReceipt?_eq_none_iff (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : Pattern) (receipt : Receipt) :
    validateReceipt? relations language plans source receipt = none ↔
      receipt ∉ rootReceipts relations language plans source := by
  cases found : validateReceipt? relations language plans source receipt with
  | none =>
      have refused : receipt ∉ rootReceipts relations language plans source := by
        intro present
        have accepted := (validateReceipt?_iff relations language plans source receipt receipt.target).mpr ⟨present, rfl⟩
        rw [found] at accepted
        contradiction
      simp [refused]
  | some target =>
      have present := (validateReceipt?_iff relations language plans source receipt target).mp found
      simp [present.1]

/-- Erasure of the receipt search is the existing oriented first-order row
executor. This theorem removes only the retained evidence fields. -/
theorem rowReceipts_projection (relations : RelationEnv) (language : LanguageDef) (index : Nat)
    (orientation : EquationOrientation) (plan : RulePlan) (source : Pattern) :
    (rowReceipts relations language index orientation plan source).map Receipt.target =
      (orientedPlan plan orientation).run relations language source := by
  unfold rowReceipts RulePlan.run
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro initial _
  have projection := congrArg (List.map (orientedPlan plan orientation).right.instantiate)
    (premiseTraces_projection relations language (orientedPlan plan orientation).premises initial)
  simpa only [List.map_map, Function.comp_def] using projection

private theorem traced_premises (relations : RelationEnv) (language : LanguageDef)
    (plans : List PremisePlan) (initial final : Bindings) (choices : List Nat) (fuel : Nat)
    (traced : (choices, final) ∈ premiseTraces relations language plans initial) :
    PremisesAt (engineBasePremises relations) language fuel initial (erasePremisePlans plans) final := by
  apply (premisesAt_engineBase_iff_mem_applyPremisesWithEnv (noncontextual_erasePremisePlans plans)).mpr
  rw [← runPremisePlans_eq_applyPremisesWithEnv, ← premiseTraces_projection]
  exact List.mem_map.mpr ⟨(choices, final), traced, rfl⟩

/-- Every emitted receipt yields the existing proof-relevant authored instance.
The physical occurrence stays in the receipt even for duplicate declarations. -/
theorem receipt_witness {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source : Pattern) (receipt : Receipt)
    (produced : receipt ∈ rootReceipts relations language program.plans source) (fuel : Nat) :
    ∃ witness : DeclaredEquationInstanceWitness (engineBasePremises relations) language source receipt.target,
      witness.orientation = receipt.orientation ∧ witness.finalBindings = receipt.finalBindings := by
  obtain ⟨plan, declared, produced⟩ := (mem_rootReceipts_iff _ _ _ _ _).mp produced
  have planMember := List.mem_of_getElem? declared
  have equationMember : equationOfPlan plan ∈ language.equations := by
    rw [← program.equations_eq_source]
    exact List.mem_map_of_mem planMember
  have fields := (mem_rowReceipts_iff _ _ _ _ _ _ _).mp produced
  have premises := traced_premises relations language plan.premises receipt.initialBindings
    receipt.finalBindings receipt.choices fuel fields.2.2.2.1
  cases orientation : receipt.orientation with
  | forward =>
      have matched : receipt.initialBindings ∈ matchPattern (equationOfPlan plan).left source := by
        simpa only [orientation, orientedPlan, equationOfPlan, run_eq_matchPattern] using fields.2.2.1
      have target : applyBindings receipt.finalBindings (equationOfPlan plan).right = receipt.target := by
        simpa only [orientation, orientedPlan, equationOfPlan, instantiate_eq_applyBindings] using fields.2.2.2.2
      refine ⟨.forward fuel ⟨equationOfPlan plan, equationMember⟩ (readsRaw_of_none rfl) receipt.initialBindings
        receipt.finalBindings matched premises target, ?_, rfl⟩
      rfl
  | reverse =>
      have matched : receipt.initialBindings ∈ matchPattern (equationOfPlan plan).right source := by
        simpa only [orientation, orientedPlan, equationOfPlan, run_eq_matchPattern] using fields.2.2.1
      have target : applyBindings receipt.finalBindings (equationOfPlan plan).left = receipt.target := by
        simpa only [orientation, orientedPlan, equationOfPlan, instantiate_eq_applyBindings] using fields.2.2.2.2
      refine ⟨.reverse fuel ⟨equationOfPlan plan, equationMember⟩ (readsRaw_of_none rfl) receipt.initialBindings
        receipt.finalBindings matched premises target, ?_, rfl⟩
      rfl

theorem EquationProgram.noncontextual_premises {source : List Equation}
    (program : EquationProgram source) :
    ∀ equation ∈ source, NoncontextualPremises equation.premises := by
  intro equation member
  rw [← program.equations_eq_source] at member
  obtain ⟨plan, _, rfl⟩ := List.mem_map.mp member
  exact noncontextual_erasePremisePlans plan.premises

/-- No emitted target invents an authored equation instance. -/
theorem rootReceipts_sound {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source target : Pattern)
    (produced : target ∈ (rootReceipts relations language program.plans source).map Receipt.target)
    (fuel : Nat) : EquationInstanceAt (engineBasePremises relations) language fuel source target := by
  obtain ⟨receipt, member, rfl⟩ := List.mem_map.mp produced
  obtain ⟨witness, _, _⟩ := receipt_witness program source receipt member fuel
  cases witness with
  | forward _ equation raw initial final matched premises target =>
      have exactPremises := (premisesAt_engineBase_iff_mem_applyPremisesWithEnv
        (program.noncontextual_premises equation.1 equation.2)).mp premises
      exact .forward equation.2 raw matched
        ((premisesAt_engineBase_iff_mem_applyPremisesWithEnv
          (program.noncontextual_premises equation.1 equation.2)).mpr exactPremises) target
  | reverse _ equation raw initial final matched premises target =>
      have exactPremises := (premisesAt_engineBase_iff_mem_applyPremisesWithEnv
        (program.noncontextual_premises equation.1 equation.2)).mp premises
      exact .reverse equation.2 raw matched
        ((premisesAt_engineBase_iff_mem_applyPremisesWithEnv
          (program.noncontextual_premises equation.1 equation.2)).mpr exactPremises) target

/-- Every canonical authored instance has a receipt at an actual source-list
occurrence, in the specified orientation and with all premise choices retained. -/
theorem rootReceipts_complete {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source target : Pattern) (fuel : Nat)
    (instanceAt : EquationInstanceAt (engineBasePremises relations) language fuel source target) :
    target ∈ (rootReceipts relations language program.plans source).map Receipt.target := by
  cases instanceAt with
  | @forward equation _ _ initial final declared _ matched premises target_eq =>
      rw [← program.equations_eq_source] at declared
      obtain ⟨plan, member, erased⟩ := List.mem_map.mp declared
      obtain ⟨index, located⟩ := List.mem_iff_getElem?.mp member
      have completed : final ∈ runPremisePlans relations language plan.premises initial := by
        rw [runPremisePlans_eq_applyPremisesWithEnv]
        apply (premisesAt_engineBase_iff_mem_applyPremisesWithEnv
          (noncontextual_erasePremisePlans plan.premises)).mp
        simpa only [← erased, equationOfPlan] using premises
      rw [← premiseTraces_projection] at completed
      obtain ⟨⟨choices, bindings⟩, traced, same⟩ := List.mem_map.mp completed
      change bindings = final at same
      subst bindings
      let receipt : Receipt := ⟨index, .forward, initial, choices, final, target⟩
      apply List.mem_map.mpr
      refine ⟨receipt, ?_, rfl⟩
      apply (mem_rootReceipts_iff _ _ _ _ _).mpr
      refine ⟨plan, located, (mem_rowReceipts_iff _ _ _ _ _ _ _).mpr ⟨rfl, rfl, ?_, traced, ?_⟩⟩
      · simpa only [orientedPlan, run_eq_matchPattern, ← erased, equationOfPlan] using matched
      · simpa only [orientedPlan, instantiate_eq_applyBindings, ← erased, equationOfPlan] using target_eq
  | @reverse equation _ _ initial final declared _ matched premises target_eq =>
      rw [← program.equations_eq_source] at declared
      obtain ⟨plan, member, erased⟩ := List.mem_map.mp declared
      obtain ⟨index, located⟩ := List.mem_iff_getElem?.mp member
      have completed : final ∈ runPremisePlans relations language plan.premises initial := by
        rw [runPremisePlans_eq_applyPremisesWithEnv]
        apply (premisesAt_engineBase_iff_mem_applyPremisesWithEnv
          (noncontextual_erasePremisePlans plan.premises)).mp
        simpa only [← erased, equationOfPlan] using premises
      rw [← premiseTraces_projection] at completed
      obtain ⟨⟨choices, bindings⟩, traced, same⟩ := List.mem_map.mp completed
      change bindings = final at same
      subst bindings
      let receipt : Receipt := ⟨index, .reverse, initial, choices, final, target⟩
      apply List.mem_map.mpr
      refine ⟨receipt, ?_, rfl⟩
      apply (mem_rootReceipts_iff _ _ _ _ _).mpr
      refine ⟨plan, located, (mem_rowReceipts_iff _ _ _ _ _ _ _).mpr ⟨rfl, rfl, ?_, traced, ?_⟩⟩
      · simpa only [orientedPlan, run_eq_matchPattern, ← erased, equationOfPlan] using matched
      · simpa only [orientedPlan, instantiate_eq_applyBindings, ← erased, equationOfPlan] using target_eq
  | declared member notRaw _ =>
      rw [← program.equations_eq_source] at member
      obtain ⟨plan, _, rfl⟩ := List.mem_map.mp member
      rw [readsRaw_of_none rfl] at notRaw
      cases notRaw

/-- Exact support of the canonical instance relation at every finite premise
fuel. Order and multiplicity are retained by the stronger list-valued executor. -/
theorem rootReceipts_iff_instanceAt {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source target : Pattern) (fuel : Nat) :
    target ∈ (rootReceipts relations language program.plans source).map Receipt.target ↔
      EquationInstanceAt (engineBasePremises relations) language fuel source target :=
  ⟨fun accepted => rootReceipts_sound program source target accepted fuel,
    rootReceipts_complete program source target fuel⟩

theorem rootReceipts_iff_instance {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source target : Pattern) :
    target ∈ (rootReceipts relations language program.plans source).map Receipt.target ↔
      EquationInstance (engineBasePremises relations) language source target := by
  constructor
  · exact fun accepted => ⟨0, rootReceipts_sound program source target accepted 0⟩
  · rintro ⟨fuel, instanceAt⟩
    exact rootReceipts_complete program source target fuel instanceAt


/-- A validated atomic receipt plugs through the existing structural context.
This is equational congruence, separate from an authored reduction context. -/
theorem validated_context_step {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (context : OneHoleContext)
    (source target : Pattern) (receipt : Receipt)
    (checked : validateReceipt? relations language program.plans source receipt = some target) :
    EquationContextStep (engineBasePremises relations) language (context.fill source) (context.fill target) := by
  obtain ⟨member, same⟩ := (validateReceipt?_iff _ _ _ _ _ _).mp checked
  subst target
  obtain ⟨witness, _, _⟩ := receipt_witness program source receipt member 0
  exact .inContext context (Or.inl witness.erase)

theorem validated_context_equivalent {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (context : OneHoleContext)
    (source target : Pattern) (receipt : Receipt)
    (checked : validateReceipt? relations language program.plans source receipt = some target) :
    EquationEquiv (engineBasePremises relations) language (context.fill source) (context.fill target) :=
  .rel _ _ (validated_context_step program context source target receipt checked)

/-- A contextual receipt records the physical site and both the atomic and
whole-term target. Context reconstruction remains the existing zipper law. -/
structure PositionedReceipt where
  position : SubtermMatching.Position
  atomic : Receipt
  target : Pattern
deriving DecidableEq, Repr

/-- Search authored equation instances in preorder, retaining declaration and
premise occurrences inside each physical subterm position. -/
def contextualReceipts (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) : List PositionedReceipt :=
  (MeTTaILSubtermMatchAutomata.subterms source).flatMap fun site =>
    match MeTTaILSubtermMatchAutomata.selectSite? source site.1 with
    | none => []
    | some (context, focus) =>
        (rootReceipts relations language plans focus.erase).map fun receipt =>
          ⟨site.1, receipt, context.fill receipt.target⟩

/-- Reconstruct positioned receipts at one physical site. Unsupported positions
produce no contextual result. The context is the canonical resolved context. -/
def liftReceipts (position : SubtermMatching.Position) (source : PatternPlan)
    (receipts : List Receipt) : List PositionedReceipt :=
  match MeTTaILSubtermMatchAutomata.selectSite? source position with
  | none => []
  | some (context, _) => receipts.map fun receipt =>
      ⟨position, receipt, context.fill receipt.target⟩

/-- Adapt the retained matcher's ordered positions to the authored equation
frontier. Its binding payload is unchanged and does not authorize an equation. -/
def frontierFromMatches (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan)
    (foundMatches : List MeTTaILSubtermMatchAutomata.BoundMatch) : List PositionedReceipt :=
  foundMatches.flatMap fun matched =>
    match MeTTaILSubtermMatchAutomata.selectSite? source matched.location.position with
    | none => []
    | some (_, focus) => liftReceipts matched.location.position source
        (rootReceipts relations language plans focus.erase)

/-- The proved canonical matcher supplies exactly one occurrence at every
existing physical subterm, in its original preorder. -/
theorem wildcard_reference (name : String) (subject : PatternPlan) :
    MeTTaILSubtermMatchAutomata.reference [.fvar name] subject =
      (MeTTaILSubtermMatchAutomata.subterms subject).map fun site =>
        (⟨⟨site.1, 0⟩, [(name, site.2.erase)]⟩ : MeTTaILSubtermMatchAutomata.BoundMatch) := by
  simp only [MeTTaILSubtermMatchAutomata.reference, List.zipIdx_cons, List.zipIdx_nil,
    List.flatMap_cons, List.flatMap_nil, matchPattern, List.map_cons, List.map_nil, List.append_nil]
  exact List.flatMap_pure_eq_map _ _

/-- The matcher-fed source frontier is the existing canonical contextual
frontier, including duplicate authored and query occurrences. -/
theorem frontierFromMatches_wildcard (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (name : String) :
    frontierFromMatches relations language plans source
      (MeTTaILSubtermMatchAutomata.reference [.fvar name] source) =
      contextualReceipts relations language plans source := by
  rw [wildcard_reference]
  simp only [frontierFromMatches, List.flatMap_map, contextualReceipts]
  apply List.flatMap_congr
  intro site member
  cases selected : MeTTaILSubtermMatchAutomata.selectSite? source site.1 with
  | none => rfl
  | some focused => simp only [liftReceipts, selected]

theorem mem_contextualReceipts_iff (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (receipt : PositionedReceipt) :
    receipt ∈ contextualReceipts relations language plans source ↔
      ∃ context focus,
        MeTTaILSubtermMatchAutomata.selectSite? source receipt.position = some (context, focus) ∧
        receipt.atomic ∈ rootReceipts relations language plans focus.erase ∧
        receipt.target = context.fill receipt.atomic.target := by
  constructor
  · intro member
    obtain ⟨⟨position, ignoredFocus⟩, _, member⟩ := List.mem_flatMap.mp member
    cases selected : MeTTaILSubtermMatchAutomata.selectSite? source position with
    | none => simp only [selected, List.not_mem_nil] at member
    | some site =>
        simp only [selected] at member
        change receipt ∈ (rootReceipts relations language plans site.2.erase).map
          (fun atomic => (⟨position, atomic, site.1.fill atomic.target⟩ : PositionedReceipt)) at member
        obtain ⟨atomic, atomicMember, rfl⟩ := List.mem_map.mp member
        exact ⟨site.1, site.2, selected, atomicMember, rfl⟩
  · rintro ⟨context, focus, selected, atomicMember, same⟩
    apply List.mem_flatMap.mpr
    refine ⟨(receipt.position, focus),
      (MeTTaILSubtermMatchAutomata.selectSite?_exists_iff source receipt.position focus).mp ⟨context, selected⟩, ?_⟩
    simp only [selected]
    apply List.mem_map.mpr
    refine ⟨receipt.atomic, atomicMember, ?_⟩
    cases receipt
    congr 1
    exact same.symm

/-- A contextual target is checked only after resolving the source site,
validating its atomic receipt, and reconstructing the whole term. -/
def validatePositionedReceipt? (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (receipt : PositionedReceipt) : Option Pattern := do
  let (context, focus) ← MeTTaILSubtermMatchAutomata.selectSite? source receipt.position
  let target ← validateReceipt? relations language plans focus.erase receipt.atomic
  let reconstructed := context.fill target
  guard (reconstructed = receipt.target)
  pure reconstructed

theorem validatePositionedReceipt?_iff (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (receipt : PositionedReceipt) (target : Pattern) :
    validatePositionedReceipt? relations language plans source receipt = some target ↔
      receipt ∈ contextualReceipts relations language plans source ∧ target = receipt.target := by
  rw [mem_contextualReceipts_iff]
  cases selected : MeTTaILSubtermMatchAutomata.selectSite? source receipt.position with
  | none => simp [validatePositionedReceipt?, selected]
  | some site =>
      rcases site with ⟨context, focus⟩
      cases replayed : validateReceipt? relations language plans focus.erase receipt.atomic with
      | none =>
          have absent := (validateReceipt?_eq_none_iff _ _ _ _ _).mp replayed
          simp [validatePositionedReceipt?, selected, replayed, absent]
      | some actual =>
          obtain ⟨atomicMember, rfl⟩ := (validateReceipt?_iff _ _ _ _ _ _).mp replayed
          simp [validatePositionedReceipt?, selected, replayed, guard, atomicMember]
          aesop

/-- Successful positioned validation is one canonical authored equation step
in its reconstructed context; rewrite-context permissions are not involved. -/
theorem validated_positioned_step {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source : PatternPlan)
    (receipt : PositionedReceipt) (target : Pattern)
    (checked : validatePositionedReceipt? relations language program.plans source receipt = some target) :
    EquationContextStep (engineBasePremises relations) language source.erase target := by
  obtain ⟨member, same⟩ := (validatePositionedReceipt?_iff _ _ _ _ _ _).mp checked
  obtain ⟨context, focus, selected, atomicMember, target_eq⟩ :=
    (mem_contextualReceipts_iff _ _ _ _ _).mp member
  have validated := (validateReceipt?_iff _ _ _ _ _ _).mpr ⟨atomicMember, rfl⟩
  have step := validated_context_step program context focus.erase receipt.atomic.target receipt.atomic validated
  rw [MeTTaILSubtermMatchAutomata.selectSite?_fill selected] at step
  simpa only [same, target_eq] using step

/-- The contextual search contains precisely the atomic frontier at each
resolved site, retaining the site even when another site looks identical. -/
theorem contextualReceipts_at_site (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source focus : PatternPlan) (position : SubtermMatching.Position)
    (context : OneHoleContext)
    (selected : MeTTaILSubtermMatchAutomata.selectSite? source position = some (context, focus))
    (atomic : Receipt) :
    (⟨position, atomic, context.fill atomic.target⟩ : PositionedReceipt) ∈
        contextualReceipts relations language plans source ↔
      atomic ∈ rootReceipts relations language plans focus.erase := by
  rw [mem_contextualReceipts_iff]
  simp [selected]

/-- Literal provider admission ensures every atomic result remains compilable.
The term compiler is checked independently of equation execution. -/
theorem rootReceipt_firstOrder (relations : RelationEnv) (language : LanguageDef)
    (providersFirstOrder : FirstOrderRelations relations) (plans : List RulePlan)
    (source : PatternPlan) (receipt : Receipt)
    (member : receipt ∈ rootReceipts relations language plans source.erase) :
    isMatchCorrectAux receipt.target = true := by
  obtain ⟨plan, _, rowMember⟩ := (mem_rootReceipts_iff _ _ _ _ _).mp member
  have targetMember : receipt.target ∈
      (rowReceipts relations language receipt.equationIndex receipt.orientation plan source.erase).map Receipt.target :=
    List.mem_map.mpr ⟨receipt, rowMember, rfl⟩
  rw [rowReceipts_projection] at targetMember
  exact RulePlan.run_firstOrder relations language providersFirstOrder
    (orientedPlan plan receipt.orientation) source.erase (isMatchCorrect_erase source) receipt.target targetMember

theorem validated_positioned_firstOrder (relations : RelationEnv) (language : LanguageDef)
    (providersFirstOrder : FirstOrderRelations relations) (plans : List RulePlan)
    (source : PatternPlan) (receipt : PositionedReceipt) (target : Pattern)
    (checked : validatePositionedReceipt? relations language plans source receipt = some target) :
    isMatchCorrectAux target = true := by
  obtain ⟨member, same⟩ := (validatePositionedReceipt?_iff _ _ _ _ _ _).mp checked
  obtain ⟨context, focus, selected, atomicMember, reconstructed⟩ :=
    (mem_contextualReceipts_iff _ _ _ _ _).mp member
  rw [same, reconstructed]
  apply MeTTaILSubtermMatchAutomata.firstOrder_fill context focus.erase receipt.atomic.target
  · rw [MeTTaILSubtermMatchAutomata.selectSite?_fill selected]
    exact isMatchCorrect_erase source
  · exact rootReceipt_firstOrder relations language providersFirstOrder plans focus receipt.atomic atomicMember

/-- Replay serialized contextual receipts against their actual preceding
endpoint. Each intermediate pattern is admitted by the existing compiler. -/
def replayContextPath? (relations : RelationEnv) (language : LanguageDef) (plans : List RulePlan)
    (source : PatternPlan) : List PositionedReceipt → Option PatternPlan
  | [] => some source
  | receipt :: receipts => do
      let target ← validatePositionedReceipt? relations language plans source receipt
      let next ← compilePattern? target
      replayContextPath? relations language plans next receipts

/-- Checked evidence decorating an edge of the existing finite-route carrier.
The checker computes its evidence from the complete positioned receipt. -/
structure CheckedPositionedReceipt (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source target : PatternPlan) where
  receipt : PositionedReceipt
  checked : validatePositionedReceipt? relations language plans source receipt = some target.erase

open Mettapedia.GSLT.Ultrainfinite

theorem replayContextPath?_iff_route (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source target : PatternPlan) (receipts : List PositionedReceipt) :
    replayContextPath? relations language plans source receipts = some target ↔
      ∃ route : Route (CheckedPositionedReceipt relations language plans) source target,
        route.trace (fun edge => edge.receipt) = receipts := by
  induction receipts generalizing source with
  | nil =>
      constructor
      · intro accepted
        simp only [replayContextPath?, Option.some.injEq] at accepted
        subst target
        exact ⟨.refl source, rfl⟩
      · rintro ⟨route, events⟩
        cases route with
        | refl => rfl
        | cons edge rest => simp [Route.trace] at events
  | cons receipt receipts ih =>
      constructor
      · intro accepted
        cases validated : validatePositionedReceipt? relations language plans source receipt with
        | none => simp [replayContextPath?, validated] at accepted
        | some actual =>
            cases compiled : compilePattern? actual with
            | none => simp [replayContextPath?, validated, compiled] at accepted
            | some next =>
                have continued : replayContextPath? relations language plans next receipts = some target := by
                  simpa [replayContextPath?, validated, compiled] using accepted
                obtain ⟨rest, events⟩ := (ih next).mp continued
                have same := erase_of_compilePattern? actual next compiled
                exact ⟨.cons ⟨receipt, same ▸ validated⟩ rest, by simp [Route.trace, events]⟩
      · rintro ⟨route, events⟩
        cases route with
        | refl => simp [Route.trace] at events
        | @cons _ middle _ edge rest =>
            simp only [Route.trace, List.cons.injEq] at events
            rcases events with ⟨rfl, remaining⟩
            have continued := (ih middle).mpr ⟨rest, remaining⟩
            simpa only [replayContextPath?, edge.checked, Option.bind_eq_bind, Option.bind_some,
              compilePattern?_erase] using continued

/-- Finite receipt routes erase to the canonical authored contextual equation
steps. This constructs independent equation evidence for every checked edge. -/
def checkedRoute (relations : RelationEnv) (language : LanguageDef)
    (program : EquationProgram language.equations) :
    {source target : PatternPlan} → Route (CheckedPositionedReceipt relations language program.plans) source target →
      Route (fun left right => PLift (EquationContextStep (engineBasePremises relations) language left right))
        source.erase target.erase
  | _, _, .refl source => .refl source.erase
  | source, _, .cons edge rest =>
      .cons ⟨validated_positioned_step program source edge.receipt _ edge.checked⟩ (checkedRoute relations language program rest)

theorem checkedRoute_equivalent {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) {source target : PatternPlan}
    (route : Route (CheckedPositionedReceipt relations language program.plans) source target) :
    EquationEquiv (engineBasePremises relations) language source.erase target.erase := by
  induction route with
  | refl source => exact .refl source.erase
  | cons edge rest ih =>
      exact .trans _ _ _ (.rel _ _ (validated_positioned_step program _ edge.receipt _ edge.checked)) ih

theorem replayContextPath?_sound {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source target : PatternPlan) (receipts : List PositionedReceipt)
    (accepted : replayContextPath? relations language program.plans source receipts = some target) :
    EquationEquiv (engineBasePremises relations) language source.erase target.erase := by
  obtain ⟨route, _⟩ := (replayContextPath?_iff_route _ _ _ _ _ _).mp accepted
  exact checkedRoute_equivalent program route

/-- A forward contextual receipt, or the same original receipt supplied at its
predecessor to certify a reversed edge. The predecessor is existing plan data. -/
abbrev SignedReceipt := PositionedReceipt ⊕ (PatternPlan × PositionedReceipt)

/-- Reversal checks the original oriented witness at its supplied predecessor
and compares the computed whole target with the current endpoint. Matching the
reversed pattern cannot replace this check when a source variable is discarded. -/
def validateSignedReceipt? (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) : SignedReceipt → Option PatternPlan
  | .inl receipt => do
      let target ← validatePositionedReceipt? relations language plans source receipt
      compilePattern? target
  | .inr (predecessor, receipt) => do
      let actual ← validatePositionedReceipt? relations language plans predecessor receipt
      guard (actual = source.erase)
      pure predecessor

@[simp] theorem validateSignedReceipt?_forward_iff (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source target : PatternPlan) (receipt : PositionedReceipt) :
    validateSignedReceipt? relations language plans source (.inl receipt) = some target ↔
      validatePositionedReceipt? relations language plans source receipt = some target.erase := by
  cases checked : validatePositionedReceipt? relations language plans source receipt with
  | none => simp [validateSignedReceipt?, checked]
  | some actual =>
      simp only [validateSignedReceipt?, checked, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq]
      constructor
      · intro compiled
        exact (erase_of_compilePattern? actual target compiled).symm
      · intro same
        simpa only [same] using compilePattern?_erase target

@[simp] theorem validateSignedReceipt?_previous_iff (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source target predecessor : PatternPlan) (receipt : PositionedReceipt) :
    validateSignedReceipt? relations language plans source (.inr (predecessor, receipt)) = some target ↔
      validatePositionedReceipt? relations language plans predecessor receipt = some source.erase ∧
      target = predecessor := by
  cases checked : validatePositionedReceipt? relations language plans predecessor receipt with
  | none => simp [validateSignedReceipt?, checked]
  | some actual =>
      by_cases same : actual = source.erase
      · simp [validateSignedReceipt?, checked, guard, same, eq_comm]
      · simp [validateSignedReceipt?, checked, guard, same]

/-- Replay uses the standard monadic fold. The validator earns every edge at
its actual preceding endpoint, including every signed reversal. -/
def replaySignedPath? (relations : RelationEnv) (language : LanguageDef) (plans : List RulePlan)
    (source : PatternPlan) (receipts : List SignedReceipt) : Option PatternPlan :=
  receipts.foldlM (init := source) (validateSignedReceipt? relations language plans)

abbrev CheckedSignedReceipt (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) := Route.CheckedEvent (validateSignedReceipt? relations language plans)

theorem replaySignedPath?_iff_route (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source target : PatternPlan) (receipts : List SignedReceipt) :
    replaySignedPath? relations language plans source receipts = some target ↔
      ∃ route : Route (CheckedSignedReceipt relations language plans) source target,
        route.trace (fun edge => edge.val) = receipts :=
  Route.foldlM_iff_checked_route (validateSignedReceipt? relations language plans) source target receipts

theorem validated_signed_equivalent {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source target : PatternPlan) (receipt : SignedReceipt)
    (checked : validateSignedReceipt? relations language program.plans source receipt = some target) :
    EquationEquiv (engineBasePremises relations) language source.erase target.erase := by
  cases receipt with
  | inl receipt =>
      exact .rel _ _ (validated_positioned_step program source receipt target.erase
        ((validateSignedReceipt?_forward_iff _ _ _ _ _ _).mp checked))
  | inr previous =>
      obtain ⟨originalChecked, rfl⟩ :=
        (validateSignedReceipt?_previous_iff relations language program.plans source target previous.1 previous.2).mp checked
      exact .symm _ _ (.rel _ _ (validated_positioned_step program previous.1 previous.2 source.erase originalChecked))

theorem checkedSignedRoute_equivalent {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) {source target : PatternPlan}
    (route : Route (CheckedSignedReceipt relations language program.plans) source target) :
    EquationEquiv (engineBasePremises relations) language source.erase target.erase := by
  induction route with
  | refl source => exact .refl source.erase
  | cons edge rest ih =>
      exact .trans _ _ _ (validated_signed_equivalent program _ _ edge.val edge.property) ih

theorem replaySignedPath?_sound {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source target : PatternPlan) (receipts : List SignedReceipt)
    (accepted : replaySignedPath? relations language program.plans source receipts = some target) :
    EquationEquiv (engineBasePremises relations) language source.erase target.erase := by
  obtain ⟨route, _⟩ := (replaySignedPath?_iff_route _ _ _ _ _ _).mp accepted
  exact checkedSignedRoute_equivalent program route

theorem replaySignedPath?_ordinary (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (receipts : List PositionedReceipt) :
    replaySignedPath? relations language plans source (receipts.map Sum.inl) =
      replayContextPath? relations language plans source receipts := by
  induction receipts generalizing source with
  | nil => rfl
  | cons receipt receipts ih =>
      simp only [replaySignedPath?, List.map_cons, List.foldlM_cons, validateSignedReceipt?, replayContextPath?]
      cases checked : validatePositionedReceipt? relations language plans source receipt with
      | none => simp
      | some actual =>
          cases compiled : compilePattern? actual with
          | none => simp [compiled]
          | some next =>
              simpa only [checked, compiled, Option.bind_eq_bind, Option.bind_some, replaySignedPath?] using ih next

theorem replayContextPath?_fold (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (receipts : List PositionedReceipt) :
    receipts.foldlM (init := source)
        (fun subject receipt => validateSignedReceipt? relations language plans subject (.inl receipt)) =
      replayContextPath? relations language plans source receipts := by
  induction receipts generalizing source with
  | nil => rfl
  | cons receipt receipts ih =>
      simp only [List.foldlM_cons, validateSignedReceipt?, replayContextPath?]
      cases checked : validatePositionedReceipt? relations language plans source receipt with
      | none => simp
      | some actual =>
          cases compiled : compilePattern? actual with
          | none => simp [compiled]
          | some next =>
              simpa only [checked, compiled, Option.bind_eq_bind, Option.bind_some, validateSignedReceipt?] using ih next

/-! ## Directed execution between checked equation routes -/

/-- The operational projection removes only the authored equation list. Every
directed row, its binding annotations and its premise-carried permissions stay
unchanged. Generated collection laws are not removed: clients must separately
admit this view as equation free before using the equation-free executor. -/
def directedView (language : LanguageDef) : LanguageDef :=
  { language with equations := [] }

@[simp] theorem directedView_name (language : LanguageDef) :
    (directedView language).name = language.name := rfl
@[simp] theorem directedView_types (language : LanguageDef) :
    (directedView language).types = language.types := rfl
@[simp] theorem directedView_terms (language : LanguageDef) :
    (directedView language).terms = language.terms := rfl
@[simp] theorem directedView_equations (language : LanguageDef) :
    (directedView language).equations = [] := rfl
@[simp] theorem directedView_rewrites (language : LanguageDef) :
    (directedView language).rewrites = language.rewrites := rfl

/-- The projection cannot admit a bag, set or collection algebra by forgetting
its declaration: all three inventories are preserved. -/
theorem directedView_equation_free_iff (language : LanguageDef) :
    (directedView language).isEquationFree = true ↔
      language.usesCollection .hashBag = false ∧
      language.usesCollection .hashSet = false ∧
      language.hasAlgebraDeclarations = false := by
  simp [directedView, LanguageDef.isEquationFree, LanguageDef.usesCollection,
    LanguageDef.hasAlgebraDeclarations, and_assoc]

/-- Removing the separate authored equation list preserves and reflects the
actual contextual derivation, including recursive premise depth. -/
theorem directedView_stepAt_iff (relations : RelationEnv) (language : LanguageDef)
    (fuel : Nat) (source target : Pattern) :
    StepAt (engineBasePremises relations) (directedView language) fuel source target ↔
      StepAt (engineBasePremises relations) language fuel source target := by
  constructor <;> intro evidence
  · exact StepAt.mono_rules (lang₁ := directedView language) (lang₂ := language)
      (fun _ member => member) evidence
  · exact StepAt.mono_rules (lang₁ := language) (lang₂ := directedView language)
      (fun _ member => member) evidence

theorem directedView_step_iff (relations : RelationEnv) (language : LanguageDef)
    (source target : Pattern) :
    Step (engineBasePremises relations) (directedView language) source target ↔
      Step (engineBasePremises relations) language source target := by
  constructor <;> intro evidence
  · exact Step.mono_rules (lang₁ := directedView language) (lang₂ := language)
      (fun _ member => member) evidence
  · exact Step.mono_rules (lang₁ := language) (lang₂ := directedView language)
      (fun _ member => member) evidence

/-- Filter actual results with a checked continuation path. The surrounding
executor supplies the results; this operation retains their order and duplicates. -/
def afterPathResults (finish : PatternPlan → Option PatternPlan) (results : List Pattern) : List Pattern :=
  results.filterMap fun result => do
    let subject ← compilePattern? result
    let target ← finish subject
    pure target.erase

theorem mem_afterPathResults_iff (finish : PatternPlan → Option PatternPlan)
    (results : List Pattern) (target : PatternPlan) :
    target.erase ∈ afterPathResults finish results ↔
      ∃ contractum : PatternPlan, contractum.erase ∈ results ∧ finish contractum = some target := by
  constructor
  · intro member
    obtain ⟨result, resultMember, checked⟩ := List.mem_filterMap.mp member
    cases compiled : compilePattern? result with
    | none => simp [compiled] at checked
    | some contractum =>
        cases replayed : finish contractum with
        | none => simp [compiled, replayed] at checked
        | some actual =>
            have same : actual.erase = target.erase := by
              simpa [compiled, replayed] using checked
            have actualEq := PatternPlan.erase_injective same
            subst actual
            exact ⟨contractum, (erase_of_compilePattern? result contractum compiled) ▸ resultMember, replayed⟩
  · rintro ⟨contractum, member, checked⟩
    apply List.mem_filterMap.mpr
    exact ⟨contractum.erase, member, by simp [compilePattern?_erase, checked]⟩

/-- Check the supplied post-route independently at each directed result. The
filter retains original result order and duplicate successful derivations. -/
def afterReceipts (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (receipts : List PositionedReceipt) (results : List Pattern) : List Pattern :=
  afterPathResults (fun subject => replayContextPath? relations language plans subject receipts) results

theorem mem_afterReceipts_iff (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (receipts : List PositionedReceipt) (results : List Pattern)
    (target : PatternPlan) :
    target.erase ∈ afterReceipts relations language plans receipts results ↔
      ∃ contractum : PatternPlan, contractum.erase ∈ results ∧
        replayContextPath? relations language plans contractum receipts = some target :=
  mem_afterPathResults_iff (fun subject => replayContextPath? relations language plans subject receipts) results target

/-- The shared directed frontier between two checked endpoint continuations.
Neither continuation adds an entry to the language's directed rewrite list. -/
def witnessedFrontier (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef) (depth : Nat) (source : PatternPlan)
    (before after : PatternPlan → Option PatternPlan) : List Pattern :=
  match before source with
  | none => []
  | some redex => afterPathResults after
      (MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises relations)
        (directedView language) depth redex)

theorem witnessedFrontier_iff_executions (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef)
    (viewAdmitted : (directedView language).isEquationFree = true) (source target : PatternPlan)
    (before after : PatternPlan → Option PatternPlan) :
    (∃ depth, target.erase ∈ witnessedFrontier strategy relations language depth source before after) ↔
      ∃ redex contractum : PatternPlan, before source = some redex ∧
        Step (engineBasePremises relations) language redex.erase contractum.erase ∧
        after contractum = some target := by
  constructor
  · rintro ⟨depth, observed⟩
    cases replayed : before source with
    | none => simp [witnessedFrontier, replayed] at observed
    | some redex =>
        rw [witnessedFrontier, replayed, mem_afterPathResults_iff] at observed
        obtain ⟨contractum, directed, finished⟩ := observed
        have step := (MeTTaILMatchAutomataExecution.runAt_iff_gslt_step strategy relations
          (directedView language) viewAdmitted redex contractum.erase).mp ⟨depth, directed⟩
        have primitive := (Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReducesUsing_iff_langReducesUsing_of_equation_free
          relations viewAdmitted redex.erase contractum.erase).mp step
        exact ⟨redex, contractum, rfl, (directedView_step_iff _ _ _ _).mp primitive, finished⟩
  · rintro ⟨redex, contractum, replayed, directed, completed⟩
    have primitive := (directedView_step_iff _ _ _ _).mpr directed
    have semantic := (Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReducesUsing_iff_langReducesUsing_of_equation_free
      relations viewAdmitted redex.erase contractum.erase).mpr primitive
    obtain ⟨depth, member⟩ := (MeTTaILMatchAutomataExecution.runAt_iff_gslt_step strategy relations
      (directedView language) viewAdmitted redex contractum.erase).mpr semantic
    refine ⟨depth, ?_⟩
    rw [witnessedFrontier, replayed, mem_afterPathResults_iff]
    exact ⟨contractum, member, completed⟩

/-- One directed frontier surrounded by the supplied, validated equation
routes. An empty result refuses this witness; it is not an inequivalence or
irreducibility decision. The directed list comes from the shared executor. -/
def witnessedReducts (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef) (plans : List RulePlan)
    (depth : Nat) (source : PatternPlan) (before after : List PositionedReceipt) : List Pattern :=
  witnessedFrontier strategy relations language depth source
    (fun subject => replayContextPath? relations language plans subject before)
    (fun subject => replayContextPath? relations language plans subject after)

/-- Exact witness correspondence. The two equation routes retain their whole
ordered certificate traces; the middle edge is the original directed step. -/
theorem witnessedReducts_iff_routes (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (plans : List RulePlan) (source target : PatternPlan) (before after : List PositionedReceipt) :
    (∃ depth, target.erase ∈ witnessedReducts strategy relations language plans depth source before after) ↔
      ∃ redex contractum : PatternPlan,
        (∃ route : Route (CheckedPositionedReceipt relations language plans) source redex,
          route.trace (fun edge => edge.receipt) = before) ∧
        Step (engineBasePremises relations) language redex.erase contractum.erase ∧
        (∃ route : Route (CheckedPositionedReceipt relations language plans) contractum target,
          route.trace (fun edge => edge.receipt) = after) := by
  unfold witnessedReducts
  rw [witnessedFrontier_iff_executions strategy relations language viewAdmitted]
  simp only [replayContextPath?_iff_route]

/-- Every accepted witnessed frontier observation constructs a genuine step
of the original GSLT modulo its original equations. -/
theorem witnessedReducts_sound (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (compiled : EquationProgram language.equations) (depth : Nat)
    (source target : PatternPlan) (before after : List PositionedReceipt)
    (observed : target.erase ∈ witnessedReducts strategy relations language compiled.plans depth source before after) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing relations language).Step source.erase target.erase := by
  obtain ⟨redex, contractum, ⟨started, _⟩, directed, ⟨finished, _⟩⟩ :=
    (witnessedReducts_iff_routes strategy relations language viewAdmitted compiled.plans source target before after).mp
      ⟨depth, observed⟩
  exact ⟨redex.erase, contractum.erase, checkedRoute_equivalent compiled started,
    directed, checkedRoute_equivalent compiled finished⟩

def afterSignedReceipts (relations : RelationEnv) (language : LanguageDef) (plans : List RulePlan)
    (receipts : List SignedReceipt) (results : List Pattern) : List Pattern :=
  afterPathResults (fun subject => replaySignedPath? relations language plans subject receipts) results

def signedWitnessedReducts (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef) (plans : List RulePlan)
    (depth : Nat) (source : PatternPlan) (before after : List SignedReceipt) : List Pattern :=
  witnessedFrontier strategy relations language depth source
    (fun subject => replaySignedPath? relations language plans subject before)
    (fun subject => replaySignedPath? relations language plans subject after)

theorem signedWitnessedReducts_iff_routes (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (plans : List RulePlan) (source target : PatternPlan) (before after : List SignedReceipt) :
    (∃ depth, target.erase ∈ signedWitnessedReducts strategy relations language plans depth source before after) ↔
      ∃ redex contractum : PatternPlan,
        (∃ route : Route (CheckedSignedReceipt relations language plans) source redex,
          route.trace (fun edge => edge.val) = before) ∧
        Step (engineBasePremises relations) language redex.erase contractum.erase ∧
        (∃ route : Route (CheckedSignedReceipt relations language plans) contractum target,
          route.trace (fun edge => edge.val) = after) := by
  unfold signedWitnessedReducts
  rw [witnessedFrontier_iff_executions strategy relations language viewAdmitted]
  simp only [replaySignedPath?_iff_route]

theorem signedWitnessedReducts_sound (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (compiled : EquationProgram language.equations) (depth : Nat)
    (source target : PatternPlan) (before after : List SignedReceipt)
    (observed : target.erase ∈ signedWitnessedReducts strategy relations language compiled.plans depth source before after) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing relations language).Step source.erase target.erase := by
  obtain ⟨redex, contractum, ⟨started, _⟩, directed, ⟨finished, _⟩⟩ :=
    (signedWitnessedReducts_iff_routes strategy relations language viewAdmitted compiled.plans source target before after).mp
      ⟨depth, observed⟩
  exact ⟨redex.erase, contractum.erase, checkedSignedRoute_equivalent compiled started,
    directed, checkedSignedRoute_equivalent compiled finished⟩

namespace Controls

def atom (name : String) : PatternPlan := .application name []
def conditional : RulePlan :=
  ⟨"choose-out", [], [⟨"choose", [.metavariable "x", .metavariable "y"]⟩], .metavariable "x", .application "out" [.metavariable "y"]⟩
def language : LanguageDef :=
  { name := "EquationOccurrences", types := [], terms := [], equations := [equationOfPlan conditional], rewrites := [] }
def relations : RelationEnv :=
  ⟨fun name _ => if name = "choose" then
    [[(atom "a").erase, (atom "b").erase], [(atom "a").erase, (atom "b").erase],
      [(atom "a").erase, (atom "c").erase]] else []⟩
def compiled : EquationProgram language.equations := ⟨[conditional], rfl⟩
def seed : Bindings := [("x", (atom "a").erase)]
def final (name : String) : Bindings := ("y", (atom name).erase) :: seed
def expected (index branch : Nat) (name : String) : Receipt :=
  ⟨index, .forward, seed, [branch], final name, .apply "out" [(atom name).erase]⟩

theorem duplicate_query_occurrences :
    premiseTraces relations language conditional.premises seed =
      [([0], final "b"), ([1], final "b"), ([2], final "c")] := by decide +kernel

private theorem conditional_forward (index : Nat) :
    rowReceipts relations language index .forward conditional (atom "a").erase =
      [expected index 0 "b", expected index 1 "b", expected index 2 "c"] := by
  have traces := duplicate_query_occurrences
  simp only [conditional, seed, atom, PatternPlan.erase] at traces
  simp [rowReceipts, orientedPlan, conditional, PatternPlan.run, atom, PatternPlan.erase, traces,
    expected, final, seed, PatternPlan.instantiate]

private theorem conditional_reverse (index : Nat) :
    rowReceipts relations language index .reverse conditional (atom "a").erase = [] := by
  simp [rowReceipts, orientedPlan, conditional, PatternPlan.run, atom, PatternPlan.erase]

theorem conditional_frontier :
    rootReceipts relations language [conditional] (atom "a").erase =
      [expected 0 0 "b", expected 0 1 "b", expected 0 2 "c"] := by
  simp [rootReceipts, conditional_forward, conditional_reverse]

theorem duplicate_declaration_occurrences :
    rootReceipts relations language [conditional, conditional] (atom "a").erase =
      [expected 0 0 "b", expected 0 1 "b", expected 0 2 "c", expected 1 0 "b", expected 1 1 "b", expected 1 2 "c"] := by
  simp [rootReceipts, conditional_forward, conditional_reverse]

theorem receipt_accepted :
    validateReceipt? relations language compiled.plans (atom "a").erase (expected 0 1 "b") =
      some (.apply "out" [(atom "b").erase]) := by
  apply (validateReceipt?_iff _ _ _ _ _ _).mpr
  refine ⟨?_, rfl⟩
  rw [show compiled.plans = [conditional] from rfl, conditional_frontier]
  decide +kernel

theorem wrong_target_refused :
    validateReceipt? relations language compiled.plans (atom "a").erase
      { expected 0 1 "b" with target := .apply "out" [(atom "c").erase] } = none := by
  apply (validateReceipt?_eq_none_iff _ _ _ _ _).mpr
  rw [show compiled.plans = [conditional] from rfl, conditional_frontier]
  decide +kernel

theorem wrong_completed_bindings_refused :
    validateReceipt? relations language compiled.plans (atom "a").erase
      { expected 0 1 "b" with finalBindings := final "c" } = none := by decide +kernel

theorem future_declaration_refused :
    validateReceipt? relations language compiled.plans (atom "a").erase (expected 1 1 "b") = none := by decide +kernel

theorem extra_query_ordinal_refused :
    replayPremises? relations language [] seed [0] = none := rfl

theorem scoped_metadata_refused :
    compileEquation? { equationOfPlan conditional with bindings := some ⟨[], []⟩ } = none :=
  compileEquation?_annotated_none _ _ rfl

theorem contextual_certificate :
    EquationContextStep (engineBasePremises relations) language
      (.apply "Box" [(atom "a").erase]) (.apply "Box" [.apply "out" [(atom "b").erase]]) :=
  validated_context_step compiled (.apply "Box" [] .hole []) _ _ _ receipt_accepted

def pair : PatternPlan := .application "pair" [atom "a", atom "a"]
def firstTarget : PatternPlan := .application "pair" [atom "a", .application "out" [atom "b"]]
def secondTarget : PatternPlan := .application "pair" [.application "out" [atom "c"], .application "out" [atom "b"]]
def firstPositioned : PositionedReceipt := ⟨[1], expected 0 1 "b", firstTarget.erase⟩
def secondPositioned : PositionedReceipt := ⟨[0], expected 0 2 "c", secondTarget.erase⟩

private theorem pair_second_site :
    MeTTaILSubtermMatchAutomata.selectSite? pair [1] =
      some (.apply "pair" [(atom "a").erase] .hole [], atom "a") := by
  simp [MeTTaILSubtermMatchAutomata.selectSite?, pair, erasePatterns]

private theorem firstTarget_first_site :
    MeTTaILSubtermMatchAutomata.selectSite? firstTarget [0] =
      some (.apply "pair" [] .hole [(.application "out" [atom "b"] : PatternPlan).erase], atom "a") := by
  simp [MeTTaILSubtermMatchAutomata.selectSite?, firstTarget, erasePatterns]

private theorem receipt_two_accepted :
    validateReceipt? relations language compiled.plans (atom "a").erase (expected 0 2 "c") =
      some (.apply "out" [(atom "c").erase]) := by
  apply (validateReceipt?_iff _ _ _ _ _ _).mpr
  refine ⟨?_, rfl⟩
  rw [show compiled.plans = [conditional] from rfl, conditional_frontier]
  decide +kernel

theorem positioned_receipt_accepted :
    validatePositionedReceipt? relations language compiled.plans pair firstPositioned = some firstTarget.erase := by
  simp only [validatePositionedReceipt?, firstPositioned, pair_second_site, Option.bind_eq_bind,
    Option.bind_some, receipt_accepted]
  simp [OneHoleContext.fill, firstTarget, PatternPlan.erase, erasePatterns, guard]

theorem positioned_future_site_refused :
    validatePositionedReceipt? relations language compiled.plans pair
      { firstPositioned with position := [2] } = none := by
  simp [validatePositionedReceipt?, firstPositioned, pair, MeTTaILSubtermMatchAutomata.selectSite?]

theorem positioned_wrong_sibling_refused :
    validatePositionedReceipt? relations language compiled.plans pair
      { firstPositioned with target := (.application "pair" [.application "out" [atom "b"], atom "a"] : PatternPlan).erase } =
      none := by
  simp only [validatePositionedReceipt?, firstPositioned, pair_second_site, Option.bind_eq_bind,
    Option.bind_some, receipt_accepted]
  simp [OneHoleContext.fill, PatternPlan.erase, erasePatterns, atom, guard]

private theorem second_positioned_accepted :
    validatePositionedReceipt? relations language compiled.plans firstTarget secondPositioned = some secondTarget.erase := by
  simp only [validatePositionedReceipt?, secondPositioned, firstTarget_first_site, Option.bind_eq_bind,
    Option.bind_some, receipt_two_accepted]
  simp [OneHoleContext.fill, secondTarget, PatternPlan.erase, erasePatterns, guard]

theorem checked_two_step_path :
    replayContextPath? relations language compiled.plans pair [firstPositioned, secondPositioned] = some secondTarget := by
  simp [replayContextPath?, positioned_receipt_accepted, second_positioned_accepted, compilePattern?_erase]

theorem checked_path_has_exact_route :
    ∃ route : Route (CheckedPositionedReceipt relations language compiled.plans) pair secondTarget,
      route.trace (fun edge => edge.receipt) = [firstPositioned, secondPositioned] :=
  (replayContextPath?_iff_route _ _ _ _ _ _).mp checked_two_step_path

theorem checked_path_equivalent :
    EquationEquiv (engineBasePremises relations) language pair.erase secondTarget.erase :=
  replayContextPath?_sound compiled pair secondTarget [firstPositioned, secondPositioned] checked_two_step_path

/-! Reversal of a conditional equation which discards a matched variable. -/

def discardConditional : RulePlan :=
  ⟨"discard-left", [], [⟨"allowed", [.metavariable "y"]⟩],
    .application "drop" [.metavariable "x", .metavariable "y"], .metavariable "y"⟩
def discardPredecessor : PatternPlan := .application "drop" [atom "a", atom "b"]
def discardRelations : RelationEnv :=
  ⟨fun name _ => if name = "allowed" then [[(atom "b").erase], [(atom "b").erase]] else []⟩
def discardLanguage : LanguageDef :=
  { name := "ConditionalDiscard", types := [], terms := [],
    equations := [equationOfPlan discardConditional], rewrites := [] }
def discardCompiled : EquationProgram discardLanguage.equations := ⟨[discardConditional], rfl⟩
def discardSeed : Bindings := [("y", (atom "b").erase), ("x", (atom "a").erase)]
def discardReceipt : PositionedReceipt :=
  ⟨[], ⟨0, .forward, discardSeed, [0], discardSeed, (atom "b").erase⟩, (atom "b").erase⟩

theorem discarded_original_receipt_checked :
    validatePositionedReceipt? discardRelations discardLanguage discardCompiled.plans
      discardPredecessor discardReceipt = some (atom "b").erase := by
  apply (validatePositionedReceipt?_iff _ _ _ _ _ _).mpr
  refine ⟨(mem_contextualReceipts_iff _ _ _ _ _).mpr ?_, rfl⟩
  refine ⟨.hole, discardPredecessor, by simp [MeTTaILSubtermMatchAutomata.selectSite?, discardReceipt], ?_, rfl⟩
  apply (mem_rootReceipts_iff _ _ _ _ _).mpr
  refine ⟨discardConditional, rfl, (mem_rowReceipts_iff _ _ _ _ _ _ _).mpr ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · have matched : discardConditional.left.run discardPredecessor.erase = [discardSeed] := by decide +kernel
    simpa only [orientedPlan, matched, discardReceipt] using List.mem_singleton_self discardSeed
  · have traced : premiseTraces discardRelations discardLanguage discardConditional.premises discardSeed =
        [([0], discardSeed), ([1], discardSeed)] := by decide +kernel
    simp [discardReceipt, traced]
  · simp [discardReceipt, orientedPlan, discardConditional, PatternPlan.instantiate, discardSeed]

/-- Matching the reversed side cannot recover the original x=a binding.
Both allowed-query occurrences remain present, with the unresolved x explicit. -/
theorem reverse_matching_cannot_recover_discarded_variable :
    (rowReceipts discardRelations discardLanguage 0 .reverse discardConditional (atom "b").erase).map Receipt.target =
      [.apply "drop" [.fvar "x", (atom "b").erase],
        .apply "drop" [.fvar "x", (atom "b").erase]] := by
  have traces : premiseTraces discardRelations discardLanguage discardConditional.premises [("y", (atom "b").erase)] =
      [([0], [("y", (atom "b").erase)]), ([1], [("y", (atom "b").erase)])] := by decide +kernel
  simp only [discardConditional] at traces
  simp [rowReceipts, orientedPlan, discardConditional, PatternPlan.run, traces,
    PatternPlan.instantiate]

theorem checked_previous_recovers_discarded_variable :
    validateSignedReceipt? discardRelations discardLanguage discardCompiled.plans (atom "b")
      (.inr (discardPredecessor, discardReceipt)) = some discardPredecessor :=
  (validateSignedReceipt?_previous_iff _ _ _ _ _ _ _).mpr ⟨discarded_original_receipt_checked, rfl⟩

theorem signed_conditional_roundtrip :
    replaySignedPath? discardRelations discardLanguage discardCompiled.plans discardPredecessor
      [.inl discardReceipt, .inr (discardPredecessor, discardReceipt)] = some discardPredecessor := by
  have forward := (validateSignedReceipt?_forward_iff _ _ _ _ _ _).mpr discarded_original_receipt_checked
  simp only [replaySignedPath?, List.foldlM_cons, forward, Option.bind_eq_bind, Option.bind_some,
    checked_previous_recovers_discarded_variable, List.foldlM_nil, Option.pure_def]

private def forgedPredecessor : PatternPlan := .application "drop" [atom "c", atom "b"]
private theorem forged_predecessor_original_refused :
    validatePositionedReceipt? discardRelations discardLanguage discardCompiled.plans forgedPredecessor discardReceipt = none := by
  have atomic : validateReceipt? discardRelations discardLanguage discardCompiled.plans forgedPredecessor.erase discardReceipt.atomic = none :=
    (validateReceipt?_eq_none_iff _ _ _ _ _).mpr (by decide +kernel)
  have localRead := atomic
  simp only [discardReceipt] at localRead
  simp [validatePositionedReceipt?, MeTTaILSubtermMatchAutomata.selectSite?, discardReceipt, localRead]

theorem signed_forged_predecessor_refused :
    validateSignedReceipt? discardRelations discardLanguage discardCompiled.plans (atom "b")
      (.inr (forgedPredecessor, discardReceipt)) = none := by
  simp [validateSignedReceipt?, forged_predecessor_original_refused]

theorem signed_wrong_current_endpoint_refused :
    validateSignedReceipt? discardRelations discardLanguage discardCompiled.plans (atom "c")
      (.inr (discardPredecessor, discardReceipt)) = none := by
  simp [validateSignedReceipt?, discarded_original_receipt_checked, atom, PatternPlan.erase, guard]

theorem signed_conditional_route_equivalent :
    EquationEquiv (engineBasePremises discardRelations) discardLanguage (atom "b").erase discardPredecessor.erase :=
  validated_signed_equivalent discardCompiled _ _ _ checked_previous_recovers_discarded_variable

end Controls

#print axioms Controls.discarded_original_receipt_checked
#print axioms Controls.reverse_matching_cannot_recover_discarded_variable
#print axioms Controls.checked_previous_recovers_discarded_variable
#print axioms Controls.signed_conditional_roundtrip
#print axioms Controls.signed_forged_predecessor_refused
#print axioms Controls.signed_wrong_current_endpoint_refused
#print axioms Controls.signed_conditional_route_equivalent
#print axioms validateSignedReceipt?_forward_iff
#print axioms validateSignedReceipt?_previous_iff
#print axioms replaySignedPath?_iff_route
#print axioms validated_signed_equivalent
#print axioms checkedSignedRoute_equivalent
#print axioms replaySignedPath?_sound
#print axioms replaySignedPath?_ordinary
#print axioms witnessedFrontier_iff_executions
#print axioms signedWitnessedReducts_iff_routes
#print axioms signedWitnessedReducts_sound
#print axioms rootReceipts_iff_instanceAt
#print axioms validateReceipt?_iff
#print axioms mem_contextualReceipts_iff
#print axioms validatePositionedReceipt?_iff
#print axioms validated_positioned_step
#print axioms validated_positioned_firstOrder
#print axioms replayContextPath?_iff_route
#print axioms checkedRoute
#print axioms checkedRoute_equivalent
#print axioms replayContextPath?_sound
#print axioms directedView_equation_free_iff
#print axioms directedView_stepAt_iff
#print axioms directedView_step_iff
#print axioms mem_afterReceipts_iff
#print axioms witnessedReducts_iff_routes
#print axioms witnessedReducts_sound
#print axioms Controls.positioned_receipt_accepted
#print axioms Controls.positioned_future_site_refused
#print axioms Controls.positioned_wrong_sibling_refused
#print axioms Controls.checked_two_step_path
#print axioms Controls.checked_path_equivalent


open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.Ultrainfinite
open MeTTaILFirstOrderRuleCompilation EquationSemantics

/-- A canonical structural context in an admitted source has an actual
physical position. Sibling order and the distinguished occurrence are kept. -/
theorem selectSite?_of_fill (context : OneHoleContext) (focus : Pattern)
    (source : PatternPlan) (filled : context.fill focus = source.erase) :
    ∃ position focusPlan,
      MeTTaILSubtermMatchAutomata.selectSite? source position = some (context, focusPlan) ∧
        focusPlan.erase = focus := by
  induction context generalizing source with
  | hole => exact ⟨[], source, by simp [MeTTaILSubtermMatchAutomata.selectSite?], filled.symm⟩
  | apply head before inner after ih =>
      cases source with
      | metavariable name => simp [OneHoleContext.fill, PatternPlan.erase] at filled
      | bound index => simp [OneHoleContext.fill, PatternPlan.erase] at filled
      | application sourceHead children =>
          simp only [OneHoleContext.fill, PatternPlan.erase, Pattern.apply.injEq] at filled
          rcases filled with ⟨rfl, childrenEqual⟩
          have focusAt : (erasePatterns children)[before.length]? = some (inner.fill focus) := by
            rw [← childrenEqual]
            simp
          have mapped : (children[before.length]?).map PatternPlan.erase = some (inner.fill focus) := by
            simpa [erasePatterns_eq_map] using focusAt
          cases read : children[before.length]? with
          | none => simp [read] at mapped
          | some child =>
              simp only [read, Option.map_some, Option.some.injEq] at mapped
              obtain ⟨path, focusPlan, selected, exactFocus⟩ := ih child mapped.symm
              have beforeEqual : erasePatterns (children.take before.length) = before := by
                have taken := congrArg (List.take before.length) childrenEqual
                simpa [erasePatterns_eq_map] using taken.symm
              have afterEqual : erasePatterns (children.drop (before.length + 1)) = after := by
                have dropped := congrArg (List.drop (before.length + 1)) childrenEqual
                simpa [erasePatterns_eq_map] using dropped.symm
              refine ⟨before.length :: path, focusPlan, ?_, exactFocus⟩
              simp [MeTTaILSubtermMatchAutomata.selectSite?, read, selected, beforeEqual, afterEqual]
  | lambda name inner ih =>
      cases source <;> simp [OneHoleContext.fill, PatternPlan.erase] at filled
  | multiLambda arity names inner ih =>
      cases source <;> simp [OneHoleContext.fill, PatternPlan.erase] at filled
  | substBody inner replacement ih =>
      cases source <;> simp [OneHoleContext.fill, PatternPlan.erase] at filled
  | substReplacement body inner ih =>
      cases source <;> simp [OneHoleContext.fill, PatternPlan.erase] at filled
  | collection kind before inner after rest ih =>
      cases source <;> simp [OneHoleContext.fill, PatternPlan.erase] at filled

/-- Every canonical contextual equation step from an admitted source occurs
in the existing frontier when the language declares no derived laws. -/
theorem contextualReceipts_complete {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source : PatternPlan) (target : Pattern)
    (step : EquationContextStep (engineBasePremises relations) language source.erase target) :
    target ∈ (contextualReceipts relations language program.plans source).map PositionedReceipt.target := by
  generalize sourceEqual : source.erase = sourcePattern at step
  cases step with
  | @inContext context focus replacement generator =>
      obtain ⟨position, focusPlan, selected, exactFocus⟩ := selectSite?_of_fill context focus source sourceEqual.symm
      rcases generator with authored | derived
      · obtain ⟨fuel, instanceAt⟩ := authored
        have complete := rootReceipts_complete program focus replacement fuel instanceAt
        obtain ⟨receipt, member, exactTarget⟩ := List.mem_map.mp complete
        refine List.mem_map.mpr ⟨⟨position, receipt, context.fill receipt.target⟩, ?_, ?_⟩
        · apply (mem_contextualReceipts_iff _ _ _ _ _).mpr
          exact ⟨context, focusPlan, selected, by simpa only [exactFocus] using member, rfl⟩
        · exact congrArg context.fill exactTarget
      · obtain ⟨noBags, noSets, noAlgebra⟩ := (directedView_equation_free_iff language).mp viewAdmitted
        exact False.elim (no_derivedInstance_of_no_derived_laws noBags noSets noAlgebra focus replacement derived)

theorem contextualReceipts_iff_step {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source : PatternPlan) (target : Pattern) :
    target ∈ (contextualReceipts relations language program.plans source).map PositionedReceipt.target ↔
      EquationContextStep (engineBasePremises relations) language source.erase target := by
  constructor
  · intro present
    obtain ⟨receipt, member, exactTarget⟩ := List.mem_map.mp present
    exact validated_positioned_step program source receipt target
      ((validatePositionedReceipt?_iff _ _ _ _ _ _).mpr ⟨member, exactTarget.symm⟩)
  · exact contextualReceipts_complete program viewAdmitted source target

/-- Select the first existing contextual witness for this endpoint. This
chooses a receipt from the ordered frontier; it never manufactures bindings. -/
def findPositionedReceipt? (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (target : Pattern) : Option PositionedReceipt :=
  (contextualReceipts relations language plans source).find? (fun receipt => receipt.target == target)

/-- Forward acquisition has priority. The other branch checks an original
receipt at the supplied predecessor before reversing that checked edge. -/
def findSignedReceipt? (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source target : PatternPlan) : Option SignedReceipt :=
  match findPositionedReceipt? relations language plans source target.erase with
  | some receipt => some (.inl receipt)
  | none => (findPositionedReceipt? relations language plans target source.erase).map
      (fun receipt => .inr (target, receipt))

theorem findPositionedReceipt?_sound (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (target : Pattern) (receipt : PositionedReceipt)
    (found : findPositionedReceipt? relations language plans source target = some receipt) :
    validatePositionedReceipt? relations language plans source receipt = some target := by
  apply (validatePositionedReceipt?_iff _ _ _ _ _ _).mpr
  have same : receipt.target = target := by
    simpa only [beq_iff_eq] using List.find?_some found
  exact ⟨List.mem_of_find?_eq_some found, same.symm⟩

theorem findPositionedReceipt?_isSome_iff {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source : PatternPlan) (target : Pattern) :
    (findPositionedReceipt? relations language program.plans source target).isSome = true ↔
      EquationContextStep (engineBasePremises relations) language source.erase target := by
  rw [← contextualReceipts_iff_step program viewAdmitted source target]
  simp only [findPositionedReceipt?, List.find?_isSome, beq_iff_eq, List.mem_map]

theorem findSignedReceipt?_sound (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source target : PatternPlan) (receipt : SignedReceipt)
    (found : findSignedReceipt? relations language plans source target = some receipt) :
    validateSignedReceipt? relations language plans source receipt = some target := by
  cases forward : findPositionedReceipt? relations language plans source target.erase with
  | some positioned =>
      simp only [findSignedReceipt?, forward, Option.some.injEq] at found
      subst receipt
      exact (validateSignedReceipt?_forward_iff _ _ _ _ _ _).mpr
        (findPositionedReceipt?_sound _ _ _ _ _ _ forward)
  | none =>
      cases previous : findPositionedReceipt? relations language plans target source.erase with
      | none => simp [findSignedReceipt?, forward, previous] at found
      | some positioned =>
          simp only [findSignedReceipt?, forward, previous, Option.map_some, Option.some.injEq] at found
          subst receipt
          exact (validateSignedReceipt?_previous_iff _ _ _ _ _ _ _).mpr
            ⟨findPositionedReceipt?_sound _ _ _ _ _ _ previous, rfl⟩

theorem findSignedReceipt?_isSome_iff {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source target : PatternPlan) :
    (findSignedReceipt? relations language program.plans source target).isSome = true ↔
      Relation.SymmGen (EquationContextStep (engineBasePremises relations) language) source.erase target.erase := by
  have forwardSupport := findPositionedReceipt?_isSome_iff (relations := relations) program viewAdmitted source target.erase
  have previousSupport := findPositionedReceipt?_isSome_iff (relations := relations) program viewAdmitted target source.erase
  cases forward : findPositionedReceipt? relations language program.plans source target.erase with
  | some positioned =>
      have supported := forwardSupport.mp (by simp [forward])
      simp [findSignedReceipt?, forward, Relation.SymmGen, supported]
  | none =>
      have unsupported : ¬ EquationContextStep (engineBasePremises relations) language source.erase target.erase := by
        intro step
        have impossible := forwardSupport.mpr step
        simp [forward] at impossible
      simp only [findSignedReceipt?, forward, Option.isSome_map, Relation.SymmGen, unsupported, false_or]
      exact previousSupport

theorem findSignedReceipt?_complete {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source target : PatternPlan)
    (step : Relation.SymmGen (EquationContextStep (engineBasePremises relations) language) source.erase target.erase) :
    ∃ receipt, findSignedReceipt? relations language program.plans source target = some receipt ∧
      validateSignedReceipt? relations language program.plans source receipt = some target := by
  have supported := (findSignedReceipt?_isSome_iff program viewAdmitted source target).mpr step
  cases found : findSignedReceipt? relations language program.plans source target with
  | none => simp [found] at supported
  | some receipt => exact ⟨receipt, rfl, findSignedReceipt?_sound _ _ _ _ _ _ found⟩

/-- Acquire an ordered receipt for each supplied adjacent endpoint. Failure
refuses that finite sequence; it does not claim global inequivalence. -/
def acquireSignedPath? (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) : List PatternPlan → Option (List SignedReceipt)
  | [] => some []
  | target :: targets => do
      let receipt ← findSignedReceipt? relations language plans source target
      let receipts ← acquireSignedPath? relations language plans target targets
      pure (receipt :: receipts)

/-- Compile independent canonical path evidence through the same acquisition
operation used by the native endpoint-list interface. -/
def compileSignedRoute? (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) {source target : PatternPlan}
    (path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) source target) :
    Option (List SignedReceipt) :=
  acquireSignedPath? relations language plans source (path.trace (fun {_source target} _ => target))

@[simp] theorem compileSignedRoute?_refl (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) :
    compileSignedRoute? relations language plans (.refl source) = some [] := rfl

@[simp] theorem compileSignedRoute?_cons (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) {source middle target : PatternPlan}
    (edge : PLift (Relation.SymmGen (EquationContextStep (engineBasePremises relations) language)
      source.erase middle.erase))
    (rest : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) middle target) :
    compileSignedRoute? relations language plans (.cons edge rest) = (do
      let receipt ← findSignedReceipt? relations language plans source middle
      let receipts ← compileSignedRoute? relations language plans rest
      pure (receipt :: receipts)) := rfl

/-- Every acquired edge is replayed at its actual preceding endpoint. -/
theorem acquireSignedPath?_replays (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (endpoints : List PatternPlan)
    (receipts : List SignedReceipt)
    (accepted : acquireSignedPath? relations language plans source endpoints = some receipts) :
    replaySignedPath? relations language plans source receipts =
      some (endpoints.foldl (fun _ next => next) source) := by
  induction endpoints generalizing source receipts with
  | nil =>
      simp only [acquireSignedPath?, Option.some.injEq] at accepted
      subst receipts
      rfl
  | cons target targets ih =>
      cases found : findSignedReceipt? relations language plans source target with
      | none => simp [acquireSignedPath?, found] at accepted
      | some receipt =>
          cases continued : acquireSignedPath? relations language plans target targets with
          | none => simp [acquireSignedPath?, found, continued] at accepted
          | some remaining =>
              simp only [acquireSignedPath?, found, continued, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at accepted
              subst receipts
              have checked := findSignedReceipt?_sound relations language plans source target receipt found
              simpa only [replaySignedPath?, List.foldlM_cons, checked, Option.bind_eq_bind,
                Option.bind_some, List.foldl_cons] using ih target remaining continued

/-- Acquisition keeps exactly one receipt per demanded adjacency. -/
theorem acquireSignedPath?_length (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (endpoints : List PatternPlan)
    (receipts : List SignedReceipt)
    (accepted : acquireSignedPath? relations language plans source endpoints = some receipts) :
    receipts.length = endpoints.length := by
  induction endpoints generalizing source receipts with
  | nil =>
      simp only [acquireSignedPath?, Option.some.injEq] at accepted
      subst receipts
      rfl
  | cons target targets ih =>
      cases found : findSignedReceipt? relations language plans source target with
      | none => simp [acquireSignedPath?, found] at accepted
      | some receipt =>
          cases continued : acquireSignedPath? relations language plans target targets with
          | none => simp [acquireSignedPath?, found, continued] at accepted
          | some remaining =>
              simp only [acquireSignedPath?, found, continued, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at accepted
              subst receipts
              simpa only [List.length_cons] using congrArg (· + 1) (ih target remaining continued)

theorem compileSignedRoute?_complete {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    {source target : PatternPlan}
    (path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) source target) :
    ∃ receipts, compileSignedRoute? relations language program.plans path = some receipts ∧
      replaySignedPath? relations language program.plans source receipts = some target := by
  induction path with
  | refl source => exact ⟨[], rfl, rfl⟩
  | @cons source middle target edge rest ih =>
      obtain ⟨receipt, found, checked⟩ := findSignedReceipt?_complete program viewAdmitted source middle edge.down
      obtain ⟨receipts, compiled, replayed⟩ := ih
      refine ⟨receipt :: receipts, ?_, ?_⟩
      · simp only [compileSignedRoute?_cons, found, compiled, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · simpa only [replaySignedPath?, List.foldlM_cons, checked, Option.bind_eq_bind, Option.bind_some] using replayed

theorem validated_signed_canonical_edge {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) (source target : PatternPlan) (receipt : SignedReceipt)
    (checked : validateSignedReceipt? relations language program.plans source receipt = some target) :
    Relation.SymmGen (EquationContextStep (engineBasePremises relations) language) source.erase target.erase := by
  cases receipt with
  | inl positioned => exact Or.inl (validated_positioned_step program source positioned target.erase
      ((validateSignedReceipt?_forward_iff _ _ _ _ _ _).mp checked))
  | inr previous =>
      obtain ⟨accepted, same⟩ := (validateSignedReceipt?_previous_iff _ _ _ _ _ _ _).mp checked
      subst target
      exact Or.inr (validated_positioned_step program previous.1 previous.2 source.erase accepted)

theorem checkedSignedRoute_has_canonicalRoute {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations) {source target : PatternPlan}
    (route : Route (CheckedSignedReceipt relations language program.plans) source target) :
    Nonempty (Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) source target) := by
  induction route with
  | refl source => exact ⟨.refl source⟩
  | @cons source middle target edge rest ih =>
      obtain ⟨canonicalRest⟩ := ih
      exact ⟨.cons ⟨validated_signed_canonical_edge program source middle edge.val edge.property⟩ canonicalRest⟩

theorem replaySignedPath?_exists_iff_canonical_route {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source target : PatternPlan) :
    (∃ receipts, replaySignedPath? relations language program.plans source receipts = some target) ↔
      Nonempty (Route (fun left right => PLift (Relation.SymmGen
        (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) source target) := by
  constructor
  · rintro ⟨receipts, accepted⟩
    obtain ⟨route, _⟩ := (replaySignedPath?_iff_route _ _ _ _ _ _).mp accepted
    exact checkedSignedRoute_has_canonicalRoute program route
  · rintro ⟨path⟩
    obtain ⟨receipts, _, accepted⟩ := compileSignedRoute?_complete program viewAdmitted path
    exact ⟨receipts, accepted⟩

/-- Admit every vertex of this actual route. The endpoint trace is taken from
the existing route itself, including intermediate vertices in order. -/
def routeFirstOrder? {Step : Pattern → Pattern → Type*} {source target : Pattern}
    (path : Route Step source target) : Bool :=
  (source :: path.trace (fun {_source target} _ => target)).all isMatchCorrectAux

@[simp] theorem routeFirstOrder?_refl {Step : Pattern → Pattern → Type*}
    (source : Pattern) : routeFirstOrder? (Route.refl (Step := Step) source) = isMatchCorrectAux source := by
  simp [routeFirstOrder?, Route.trace]

@[simp] theorem routeFirstOrder?_cons {Step : Pattern → Pattern → Type*}
    {source middle target : Pattern} (edge : Step source middle) (rest : Route Step middle target) :
    routeFirstOrder? (.cons edge rest) = (isMatchCorrectAux source && routeFirstOrder? rest) := rfl

/-- A raw canonical route whose actual vertices are admitted translates to
the existing pattern-plan carrier, retaining each canonical edge. -/
theorem canonicalRoute_has_planRoute (Step : Pattern → Pattern → Prop)
    {source target : Pattern} (path : Route (fun left right => PLift (Step left right)) source target)
    (admitted : routeFirstOrder? path = true) (sourcePlan : PatternPlan)
    (sourceExact : sourcePlan.erase = source) :
    ∃ targetPlan : PatternPlan, targetPlan.erase = target ∧
      Nonempty (Route (fun left right => PLift (Step left.erase right.erase)) sourcePlan targetPlan) := by
  induction path generalizing sourcePlan with
  | refl source => exact ⟨sourcePlan, sourceExact, ⟨.refl sourcePlan⟩⟩
  | @cons source middle target edge rest ih =>
      have facts : isMatchCorrectAux source = true ∧ routeFirstOrder? rest = true := by
        simpa only [routeFirstOrder?_cons, Bool.and_eq_true] using admitted
      have restAdmitted := facts.2
      have middleFacts : isMatchCorrectAux middle = true ∧
          (rest.trace (fun {_source target} _ => target)).all isMatchCorrectAux = true := by
        simpa only [routeFirstOrder?, List.all_cons, Bool.and_eq_true] using restAdmitted
      have middleAdmitted := middleFacts.1
      have someMiddle : (compilePattern? middle).isSome = true := by
        rw [compilePattern?_isSome_eq_isMatchCorrectAux, middleAdmitted]
      cases compiled : compilePattern? middle with
      | none => simp [compiled] at someMiddle
      | some middlePlan =>
          have middleExact := erase_of_compilePattern? middle middlePlan compiled
          obtain ⟨targetPlan, targetExact, ⟨planRest⟩⟩ := ih restAdmitted middlePlan middleExact
          refine ⟨targetPlan, targetExact, ⟨.cons ?_ planRest⟩⟩
          exact ⟨by simpa only [sourceExact, middleExact] using edge.down⟩

/-- Canonical forward steps preserve this fragment because their actual
frontier targets preserve it, including every returned premise binding. -/
theorem canonical_context_step_firstOrder {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (providersFirstOrder : FirstOrderRelations relations) (source : PatternPlan) (target : Pattern)
    (step : EquationContextStep (engineBasePremises relations) language source.erase target) :
    isMatchCorrectAux target = true := by
  obtain ⟨receipt, member, targetExact⟩ := List.mem_map.mp
    (contextualReceipts_complete program viewAdmitted source target step)
  exact validated_positioned_firstOrder relations language providersFirstOrder program.plans source receipt target
    ((validatePositionedReceipt?_iff _ _ _ _ _ _).mpr ⟨member, targetExact.symm⟩)

/-- For forward routes, admission of the starting term earns admission of
every intermediate term. This does not make a claim about reversed edges. -/
theorem canonical_forward_route_firstOrder {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (providersFirstOrder : FirstOrderRelations relations) {source target : Pattern}
    (path : Route (fun left right => PLift
      (EquationContextStep (engineBasePremises relations) language left right)) source target)
    (sourceAdmitted : isMatchCorrectAux source = true) : routeFirstOrder? path = true := by
  induction path with
  | refl source => simpa only [routeFirstOrder?_refl] using sourceAdmitted
  | @cons source middle target edge rest ih =>
      have someSource : (compilePattern? source).isSome = true := by
        rw [compilePattern?_isSome_eq_isMatchCorrectAux, sourceAdmitted]
      cases compiled : compilePattern? source with
      | none => simp [compiled] at someSource
      | some sourcePlan =>
          have sourceExact := erase_of_compilePattern? source sourcePlan compiled
          have middleAdmitted := canonical_context_step_firstOrder program viewAdmitted providersFirstOrder
            sourcePlan middle (by simpa only [sourceExact] using edge.down)
          simp only [routeFirstOrder?_cons, sourceAdmitted, Bool.true_and]
          exact ih middleAdmitted

/-- Canonical symmetric routes earn actual receipts when their intermediate
vertices pass the independently computed fragment admission. -/
theorem admitted_canonical_route_has_receipts {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source target : PatternPlan)
    (path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises relations) language) left right)) source.erase target.erase)
    (admitted : routeFirstOrder? path = true) :
    ∃ receipts, replaySignedPath? relations language program.plans source receipts = some target := by
  obtain ⟨actualTarget, targetExact, ⟨planPath⟩⟩ := canonicalRoute_has_planRoute _ path admitted source rfl
  have same : actualTarget = target := PatternPlan.erase_injective targetExact
  subst actualTarget
  obtain ⟨receipts, _, replayed⟩ := compileSignedRoute?_complete program viewAdmitted planPath
  exact ⟨receipts, replayed⟩

/-- Erase plan vertices without changing canonical edge evidence. -/
def erasePatternRoute (Step : Pattern → Pattern → Prop) {source target : PatternPlan} :
    Route (fun left right => PLift (Step left.erase right.erase)) source target →
      Route (fun left right => PLift (Step left right)) source.erase target.erase
  | .refl source => .refl source.erase
  | .cons edge rest => .cons edge (erasePatternRoute Step rest)

theorem erasePatternRoute_firstOrder (Step : Pattern → Pattern → Prop) {source target : PatternPlan}
    (path : Route (fun left right => PLift (Step left.erase right.erase)) source target) :
    routeFirstOrder? (erasePatternRoute Step path) = true := by
  induction path with
  | refl source => simp only [erasePatternRoute, routeFirstOrder?_refl, isMatchCorrect_erase]
  | cons edge rest ih => simp only [erasePatternRoute, routeFirstOrder?_cons, isMatchCorrect_erase, Bool.true_and, ih]

/-- Receipt existence preserves and reflects independent canonical finite
routes whose actual intermediate terms are all admitted. -/
theorem replaySignedPath?_exists_iff_admitted_canonical_route {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source target : PatternPlan) :
    (∃ receipts, replaySignedPath? relations language program.plans source receipts = some target) ↔
      ∃ path : Route (fun left right => PLift (Relation.SymmGen
        (EquationContextStep (engineBasePremises relations) language) left right)) source.erase target.erase,
        routeFirstOrder? path = true := by
  constructor
  · intro receipts
    obtain ⟨path⟩ := (replaySignedPath?_exists_iff_canonical_route program viewAdmitted source target).mp receipts
    exact ⟨erasePatternRoute _ path, erasePatternRoute_firstOrder _ path⟩
  · rintro ⟨path, admitted⟩
    exact admitted_canonical_route_has_receipts program viewAdmitted source target path admitted

/-- One acquired receipt is retained for every edge of the supplied route.
Acquisition does not skip a failed edge or collapse repeated endpoints. -/
theorem compileSignedRoute?_length (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) {source target : PatternPlan}
    (path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) source target)
    (receipts : List SignedReceipt) (compiled : compileSignedRoute? relations language plans path = some receipts) :
    receipts.length = path.length := by
  have length := acquireSignedPath?_length relations language plans source _ receipts compiled
  simpa only [Route.trace_length] using length

/-- Endpoint-list acquisition succeeds exactly when the original canonical
symmetric step judgment has a finite route with these ordered endpoints.
The supplied list bounds the search and retains every intermediate vertex. -/
theorem acquireSignedPath?_isSome_iff_route {relations : RelationEnv} {language : LanguageDef}
    (program : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source : PatternPlan) (endpoints : List PatternPlan) :
    (acquireSignedPath? relations language program.plans source endpoints).isSome = true ↔
      ∃ target, ∃ path : Route (fun left right => PLift (Relation.SymmGen
        (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) source target,
        path.trace (fun {_source target} _ => target) = endpoints := by
  induction endpoints generalizing source with
  | nil =>
      constructor
      · intro _
        exact ⟨source, .refl source, rfl⟩
      · intro _
        rfl
  | cons middle endpoints ih =>
      constructor
      · intro accepted
        cases found : findSignedReceipt? relations language program.plans source middle with
        | none => simp [acquireSignedPath?, found] at accepted
        | some receipt =>
            cases continued : acquireSignedPath? relations language program.plans middle endpoints with
            | none => simp [acquireSignedPath?, found, continued] at accepted
            | some receipts =>
                obtain ⟨target, rest, traced⟩ := (ih middle).mp (by simp only [continued, Option.isSome_some])
                have checked := findSignedReceipt?_sound relations language program.plans source middle receipt found
                have edge := validated_signed_canonical_edge program source middle receipt checked
                exact ⟨target, .cons ⟨edge⟩ rest, by simp only [Route.trace, traced]⟩
      · rintro ⟨target, path, traced⟩
        obtain ⟨receipts, acquired, _⟩ := compileSignedRoute?_complete program viewAdmitted path
        change acquireSignedPath? relations language program.plans source
          (path.trace (fun {_source target} _ => target)) = some receipts at acquired
        rw [traced] at acquired
        simp only [acquired, Option.isSome_some]

namespace RepresentabilityControls

open Controls

theorem conditional_first_acquisition :
    findPositionedReceipt? relations language compiled.plans (atom "a")
      (.apply "out" [(atom "b").erase]) =
      some ⟨[], expected 0 0 "b", .apply "out" [(atom "b").erase]⟩ := by
  have root := conditional_frontier
  simp only [findPositionedReceipt?, contextualReceipts, compiled]
  simp only [atom] at root
  simp [MeTTaILSubtermMatchAutomata.subterms, MeTTaILSubtermMatchAutomata.subtermsList,
    MeTTaILSubtermMatchAutomata.selectSite?, atom, OneHoleContext.fill, expected]
  rw [root]
  decide +kernel

def conditionalTarget : PatternPlan := .application "out" [atom "b"]

private theorem conditional_step :
    EquationContextStep (engineBasePremises relations) language (atom "a").erase conditionalTarget.erase :=
  validated_context_step compiled .hole (atom "a").erase conditionalTarget.erase (expected 0 1 "b") receipt_accepted

/-- The independent canonical evidence uses the second duplicate premise
branch; deterministic acquisition genuinely finds the first branch instead. -/
def conditionalRoute : Route (fun left right => PLift (Relation.SymmGen
    (EquationContextStep (engineBasePremises relations) language) left.erase right.erase))
    (atom "a") conditionalTarget := .cons ⟨Or.inl conditional_step⟩ (.refl _)

theorem conditional_route_acquired :
    compileSignedRoute? relations language compiled.plans conditionalRoute =
      some [.inl ⟨[], expected 0 0 "b", conditionalTarget.erase⟩] := by
  have located := conditional_first_acquisition
  change findPositionedReceipt? relations language compiled.plans (atom "a") conditionalTarget.erase =
    some ⟨[], expected 0 0 "b", conditionalTarget.erase⟩ at located
  simp only [conditionalRoute, compileSignedRoute?_cons, compileSignedRoute?_refl, findSignedReceipt?, located,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem absent_endpoint_refused :
    findSignedReceipt? discardRelations discardLanguage discardCompiled.plans (atom "b") (atom "c") = none := by
  have tracesB : premiseTraces discardRelations discardLanguage discardConditional.premises [("y", (atom "b").erase)] =
      [([0], [("y", (atom "b").erase)]), ([1], [("y", (atom "b").erase)])] := by decide +kernel
  have tracesC : premiseTraces discardRelations discardLanguage discardConditional.premises [("y", (atom "c").erase)] = [] := by
    decide +kernel
  have rootB : rootReceipts discardRelations discardLanguage [discardConditional] (atom "b").erase =
      [⟨0, .reverse, [("y", (atom "b").erase)], [0], [("y", (atom "b").erase)],
        .apply "drop" [.fvar "x", (atom "b").erase]⟩,
       ⟨0, .reverse, [("y", (atom "b").erase)], [1], [("y", (atom "b").erase)],
        .apply "drop" [.fvar "x", (atom "b").erase]⟩] := by
    simp only [discardConditional, atom, PatternPlan.erase, erasePatterns] at tracesB
    simp [rootReceipts, rowReceipts, orientedPlan, discardConditional, PatternPlan.run,
      atom, PatternPlan.erase, erasePatterns, tracesB, PatternPlan.instantiate]
  have rootC : rootReceipts discardRelations discardLanguage [discardConditional] (atom "c").erase = [] := by
    simp only [discardConditional, atom, PatternPlan.erase, erasePatterns] at tracesC
    simp [rootReceipts, rowReceipts, orientedPlan, discardConditional, PatternPlan.run,
      atom, PatternPlan.erase, erasePatterns, tracesC]
  simp only [atom] at rootB rootC
  simp [findSignedReceipt?, findPositionedReceipt?, contextualReceipts,
    MeTTaILSubtermMatchAutomata.subterms, MeTTaILSubtermMatchAutomata.subtermsList,
    MeTTaILSubtermMatchAutomata.selectSite?, atom, discardCompiled, rootB, rootC, OneHoleContext.fill]
  decide +kernel

def hiddenPredecessor : Pattern := .apply "drop" [.lambda none (.bvar 0), (atom "b").erase]
def hiddenSeed : Bindings := [("y", (atom "b").erase), ("x", .lambda none (.bvar 0))]
def hiddenReceipt : Receipt := ⟨0, .forward, hiddenSeed, [0], hiddenSeed, (atom "b").erase⟩

theorem hidden_original_receipt_checked :
    validateReceipt? discardRelations discardLanguage discardCompiled.plans hiddenPredecessor hiddenReceipt =
      some (atom "b").erase := by
  apply (validateReceipt?_iff _ _ _ _ _ _).mpr
  refine ⟨(mem_rootReceipts_iff _ _ _ _ _).mpr ?_, rfl⟩
  refine ⟨discardConditional, rfl, (mem_rowReceipts_iff _ _ _ _ _ _ _).mpr ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · have matched : discardConditional.left.run hiddenPredecessor = [hiddenSeed] := by decide +kernel
    simpa only [orientedPlan, hiddenReceipt, matched] using List.mem_singleton_self hiddenSeed
  · have traced : premiseTraces discardRelations discardLanguage discardConditional.premises hiddenSeed =
        [([0], hiddenSeed), ([1], hiddenSeed)] := by decide +kernel
    simp [hiddenReceipt, traced]
  · simp [hiddenReceipt, orientedPlan, discardConditional, PatternPlan.instantiate, hiddenSeed]

theorem hidden_original_step :
    EquationContextStep (engineBasePremises discardRelations) discardLanguage hiddenPredecessor (atom "b").erase := by
  exact validated_context_step discardCompiled .hole hiddenPredecessor (atom "b").erase hiddenReceipt
    hidden_original_receipt_checked

/-- Both endpoints are first-order, but a legitimate reversed conditional
edge exposes the discarded binder payload at its intermediate predecessor. -/
def binderExcursion : Route (fun left right => PLift (Relation.SymmGen
    (EquationContextStep (engineBasePremises discardRelations) discardLanguage) left right))
    (atom "b").erase (atom "b").erase :=
  .cons ⟨Or.inr hidden_original_step⟩ (.cons ⟨Or.inl hidden_original_step⟩ (.refl _))

theorem binder_excursion_endpoints_admitted :
    isMatchCorrectAux (atom "b").erase = true := isMatchCorrect_erase _

theorem hidden_predecessor_unrepresentable : compilePattern? hiddenPredecessor = none := by
  simp [hiddenPredecessor, compilePattern?, compilePatterns?]

theorem binder_excursion_intermediate_refused : routeFirstOrder? binderExcursion = false := by
  simp [binderExcursion, routeFirstOrder?, Route.trace, hiddenPredecessor, isMatchCorrectAux, isMatchCorrectListAux]

theorem binder_excursion_canonical_equivalence :
    EquationEquiv (engineBasePremises discardRelations) discardLanguage (atom "b").erase (atom "b").erase := by
  exact .trans _ _ _ (.symm _ _ (.rel _ _ hidden_original_step)) (.rel _ _ hidden_original_step)

end RepresentabilityControls

#print axioms acquireSignedPath?_isSome_iff_route
#print axioms wildcard_reference
#print axioms frontierFromMatches_wildcard
#print axioms acquireSignedPath?_replays
#print axioms acquireSignedPath?_length
#print axioms erasePatternRoute_firstOrder
#print axioms replaySignedPath?_exists_iff_admitted_canonical_route
#print axioms compileSignedRoute?_length
#print axioms RepresentabilityControls.conditional_first_acquisition
#print axioms RepresentabilityControls.conditional_route_acquired
#print axioms RepresentabilityControls.absent_endpoint_refused
#print axioms RepresentabilityControls.hidden_original_receipt_checked
#print axioms RepresentabilityControls.hidden_original_step
#print axioms RepresentabilityControls.hidden_predecessor_unrepresentable
#print axioms RepresentabilityControls.binder_excursion_intermediate_refused
#print axioms RepresentabilityControls.binder_excursion_canonical_equivalence
#print axioms routeFirstOrder?_cons
#print axioms canonicalRoute_has_planRoute
#print axioms canonical_context_step_firstOrder
#print axioms canonical_forward_route_firstOrder
#print axioms admitted_canonical_route_has_receipts
#print axioms selectSite?_of_fill
#print axioms contextualReceipts_complete
#print axioms contextualReceipts_iff_step
#print axioms findPositionedReceipt?_sound
#print axioms findPositionedReceipt?_isSome_iff
#print axioms findSignedReceipt?_sound
#print axioms findSignedReceipt?_isSome_iff
#print axioms findSignedReceipt?_complete
#print axioms compileSignedRoute?_complete
#print axioms validated_signed_canonical_edge
#print axioms checkedSignedRoute_has_canonicalRoute
#print axioms replaySignedPath?_exists_iff_canonical_route


/-- Acquire one receipt per supplied endpoint and replay that same ordered
receipt list. Both phases use the existing canonical equation operations. -/
def acquireReplayPath? (relations : RelationEnv) (language : LanguageDef)
    (plans : List RulePlan) (source : PatternPlan) (endpoints : List PatternPlan) : Option PatternPlan := do
  let receipts ← acquireSignedPath? relations language plans source endpoints
  replaySignedPath? relations language plans source receipts

/-- Exact finite endpoint traces for the computed acquisition/replay
continuation. The right-hand route is the independent canonical judgment. -/
theorem acquireReplayPath?_iff_canonical_route {relations : RelationEnv} {language : LanguageDef}
    (compiled : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source target : PatternPlan) (endpoints : List PatternPlan) :
    acquireReplayPath? relations language compiled.plans source endpoints = some target ↔
      ∃ path : Route (fun left right => PLift (Relation.SymmGen
        (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) source target,
        path.trace (fun {_source target} _ => target) = endpoints := by
  constructor
  · intro finished
    cases acquired : acquireSignedPath? relations language compiled.plans source endpoints with
    | none => simp [acquireReplayPath?, acquired] at finished
    | some receipts =>
        have replayed : replaySignedPath? relations language compiled.plans source receipts = some target := by
          simpa only [acquireReplayPath?, acquired, Option.bind_eq_bind, Option.bind_some] using finished
        obtain ⟨actualTarget, path, traced⟩ :=
          (acquireSignedPath?_isSome_iff_route (relations := relations) compiled viewAdmitted source endpoints).mp
            (by simp only [acquired, Option.isSome_some])
        obtain ⟨actualReceipts, recompiled, replayedActual⟩ := compileSignedRoute?_complete compiled viewAdmitted path
        change acquireSignedPath? relations language compiled.plans source
          (path.trace (fun {_source target} _ => target)) = some actualReceipts at recompiled
        rw [traced, acquired] at recompiled
        have sameReceipts : receipts = actualReceipts := Option.some.inj recompiled
        subst actualReceipts
        have sameTarget : target = actualTarget := Option.some.inj (replayed.symm.trans replayedActual)
        subst actualTarget
        exact ⟨path, traced⟩
  · rintro ⟨path, traced⟩
    obtain ⟨receipts, acquired, replayed⟩ := compileSignedRoute?_complete compiled viewAdmitted path
    change acquireSignedPath? relations language compiled.plans source
      (path.trace (fun {_source target} _ => target)) = some receipts at acquired
    rw [traced] at acquired
    simp only [acquireReplayPath?, acquired, Option.bind_eq_bind, Option.bind_some, replayed]

/-- The same ordered post-frontier filter, now with a supplied endpoint list
instead of preconstructed receipts. Duplicate directed results stay duplicate. -/
def acquiredAfterResults (relations : RelationEnv) (language : LanguageDef) (plans : List RulePlan)
    (endpoints : List PatternPlan) (results : List Pattern) : List Pattern :=
  afterPathResults (fun subject => acquireReplayPath? relations language plans subject endpoints) results

/-- Actual directed execution between two acquired canonical continuations.
Equality never changes the language's authored directed rows or permissions. -/
def acquiredWitnessedReducts (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef) (plans : List RulePlan)
    (depth : Nat) (source : PatternPlan) (before after : List PatternPlan) : List Pattern :=
  witnessedFrontier strategy relations language depth source
    (fun subject => acquireReplayPath? relations language plans subject before)
    (fun subject => acquireReplayPath? relations language plans subject after)

/-- Preservation and reflection retain both exact endpoint-list traces and
an original directed firing between their canonical equation routes. -/
theorem acquiredWitnessedReducts_iff_canonical_routes
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (relations : RelationEnv) (language : LanguageDef)
    (compiled : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true)
    (source target : PatternPlan) (before after : List PatternPlan) :
    (∃ depth, target.erase ∈ acquiredWitnessedReducts strategy relations language compiled.plans depth
      source before after) ↔
      ∃ redex contractum : PatternPlan,
        (∃ path : Route (fun left right => PLift (Relation.SymmGen
          (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) source redex,
          path.trace (fun {_source target} _ => target) = before) ∧
        Step (engineBasePremises relations) language redex.erase contractum.erase ∧
        (∃ path : Route (fun left right => PLift (Relation.SymmGen
          (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) contractum target,
          path.trace (fun {_source target} _ => target) = after) := by
  unfold acquiredWitnessedReducts
  rw [witnessedFrontier_iff_executions strategy relations language viewAdmitted]
  simp only [acquireReplayPath?_iff_canonical_route compiled viewAdmitted]

/-- A finite symmetric route of the original contextual equation judgment
constructs its canonical least equivalence evidence. -/
theorem canonicalRoute_equivalent {relations : RelationEnv} {language : LanguageDef}
    {source target : PatternPlan}
    (path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises relations) language) left.erase right.erase)) source target) :
    EquationEquiv (engineBasePremises relations) language source.erase target.erase := by
  induction path with
  | refl source => exact .refl source.erase
  | cons edge rest ih =>
      apply Relation.EqvGen.trans _ _ _ _ ih
      rcases edge.down with forward | backward
      · exact .rel _ _ forward
      · exact .symm _ _ (.rel _ _ backward)

/-- Every acquired frontier observation is a step of the original GSLT
modulo its original equations. The middle relation is still directed. -/
theorem acquiredWitnessedReducts_sound (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (language : LanguageDef) (compiled : EquationProgram language.equations)
    (viewAdmitted : (directedView language).isEquationFree = true) (depth : Nat)
    (source target : PatternPlan) (before after : List PatternPlan)
    (observed : target.erase ∈ acquiredWitnessedReducts strategy relations language compiled.plans depth
      source before after) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing relations language).Step source.erase target.erase := by
  obtain ⟨redex, contractum, ⟨started, _⟩, directed, ⟨finished, _⟩⟩ :=
    (acquiredWitnessedReducts_iff_canonical_routes strategy relations language compiled viewAdmitted
      source target before after).mp ⟨depth, observed⟩
  exact ⟨redex.erase, contractum.erase, canonicalRoute_equivalent started,
    directed, canonicalRoute_equivalent finished⟩

#print axioms canonicalRoute_equivalent
#print axioms acquireReplayPath?_iff_canonical_route
#print axioms acquiredWitnessedReducts_iff_canonical_routes
#print axioms acquiredWitnessedReducts_sound

end Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation
