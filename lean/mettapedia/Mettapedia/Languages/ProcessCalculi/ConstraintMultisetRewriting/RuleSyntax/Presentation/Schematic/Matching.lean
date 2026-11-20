import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Language

/-!
# The framework's step of a program with unknowns, on stores of ground rows

**A firing by matching** (`MatchFires r θ rows rest`): a ground instantiation `θ` of the rule's unknowns such
that the instances of the take patterns beside `rest` are the store's rows, the instance of every read
pattern is a row of `rest`, and every tell and equation guard has equal instances.

For a program of the fragment (`RangeRestrictedPositive`) and a relation environment that adds nothing to the
builtin equality (`noEq`):

* `step_sound`: a primitive step of the presented language from a store is a firing by matching, to the
  store of the made rows' instances beside the rest. The instantiation is the one the framework's final
  bindings determine (`groundOf`); range restriction makes it ground on every unknown the rule writes.
* `step_prefix`: conversely every firing by matching is a primitive step, from the arrangement with the
  taken rows first.
* `semanticStep_storeCode_iff`, `diamond_storeCode_iff`: **the framework's step modulo equations and its
  generated possibility** at a store are firings by matching.
* `semanticStep_beside`: **the parallel context rule holds**: a step of a store is a step of the store
  beside further rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator engineBasePremises PremiseAt PremisesAt StepAt)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule applyBindingsForRule_eq_syntactic)
open Mettapedia.OSLF.Framework.TypeSynthesis (langSemanticReducesUsing langDiamondUsing langDiamondUsing_spec
  langGSLTUsing)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (EquationPredicate)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv StepModuloEquations)
open NamesOnTheStep (Expr)

/-- **A firing of a rule by matching, on a store of ground rows.** -/
structure MatchFires (r : SRule) (θ : ℕ → Expr) (rows rest : List Expr) : Prop where
  takes : (r.body.take.map (inst θ) ++ rest).Perm rows
  reads : ∀ q ∈ r.body.read, inst θ q ∈ rest
  equations : ∀ e ∈ equationsOf r, inst θ e.1 = inst θ e.2

/-- **The parallel context rule, on firings by matching**: a firing of a store is a firing of the store
beside further rows. -/
theorem MatchFires.beside {r : SRule} {θ : ℕ → Expr} {rows rest : List Expr} (fires : MatchFires r θ rows rest)
    (extra : List Expr) : MatchFires r θ (rows ++ extra) (rest ++ extra) where
  takes := by
    rw [← List.append_assoc]
    exact fires.takes.append_right extra
  reads q member := List.mem_append_left _ (fires.reads q member)
  equations := fires.equations

theorem premiseAt_relationQuery_iff {base : BasePremiseEvaluator} {L : LanguageDef} {fuel : ℕ} {b res : Bindings}
    {relation : String} {arguments : List Pattern} :
    PremiseAt base L fuel b (.relationQuery relation arguments) res ↔
      res ∈ base L b (.relationQuery relation arguments) := by
  constructor
  · intro premise
    cases premise with
    | relationQuery member => exact member
  · exact PremiseAt.relationQuery

theorem premiseAt_engine_iff {relEnv : RelationEnv} {L : LanguageDef} {fuel : ℕ} {b res : Bindings}
    {relation : String} {arguments : List Pattern} :
    PremiseAt (engineBasePremises relEnv) L fuel b (.relationQuery relation arguments) res ↔
      res ∈ premiseStepWithEnv relEnv L b (.relationQuery relation arguments) :=
  premiseAt_relationQuery_iff

/-- The rest a read premise names. -/
def readRestOf : Premise → Option String
  | .relationQuery _ [_, .collection _ _ rest] => rest
  | _ => none

/-- The pattern a read premise reads. -/
def readPatternOf : Premise → Option Pattern
  | .relationQuery _ [_, .collection _ [pattern] _] => some pattern
  | _ => none

/-- The two sides of a premise of an equation. -/
def sidesOf : Premise → Option (Pattern × Pattern)
  | .relationQuery _ [left, right] => some (left, right)
  | _ => none

/-! ## Matching the takes -/

/-- **The takes match a bag where it divides into rows the patterns' codes are sent to and a remainder**, which
the rest captures. -/
theorem matchBag_terms {rest : String} : ∀ {ps : List Tm} {terms : List Pattern} {bindings : Bindings},
    MatchBagRel (ps.map termCode) (some rest) .hashBag terms bindings →
      ∃ chosen remainder, (chosen ++ remainder).Perm terms ∧
        List.Forall₂ (fun p t => ∀ final, BindingsExtends bindings final → applyBindings final (termCode p) = t)
          ps chosen ∧
        BindingsExtends [(rest, .collection .hashBag remainder none)] bindings
  | [], terms, bindings, matched => by
      simp only [List.map_nil] at matched
      cases matched
      exact ⟨[], terms, .refl _, .nil, extends_refl _⟩
  | p :: ps, terms, bindings, matched => by
      rw [List.map_cons] at matched
      cases matched with
      | cons index bound head tail merged =>
          obtain ⟨chosen, remainder, perm, each, restExt⟩ := matchBag_terms tail
          refine ⟨terms[index] :: chosen, remainder, ?_, ?_, extends_trans restExt (extends_right merged)⟩
          · rw [List.cons_append]
            exact (perm.cons _).trans (List.getElem_cons_eraseIdx_perm bound)
          · refine .cons (fun final ext => matchRel_correct_of_extends head (isMatchCorrect_termCode p)
              (extends_trans (extends_left merged) ext)) ?_
            exact List.Forall₂.imp (fun _ _ holds final ext => holds final (extends_trans (extends_right merged) ext))
              each

/-- **Bindings that send patterns to rows determine the instantiation**: the instances are the rows, and each
unknown is bound to its row. -/
theorem decode_forall₂ {final : Bindings} : ∀ {ps : List Tm} {rows : List Expr},
    List.Forall₂ (fun p t => applyBindings final (termCode p) = t) ps (rows.map rowCode) →
      ps.map (inst (groundOf final)) = rows ∧ ∀ p ∈ ps, ∀ x ∈ p.freeVars,
        final.find? (·.1 == unknownName x) = some (unknownName x, rowCode (groundOf final x))
  | [], [], _ => ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩
  | [], _ :: _, related => by cases related
  | _ :: _, [], related => by cases related
  | p :: ps, e :: es, related => by
      cases related with
      | cons head tail =>
          obtain ⟨instHead, varsHead⟩ := applyBindings_termCode_eq_rowCode final p e head
          obtain ⟨instTail, varsTail⟩ := decode_forall₂ tail
          refine ⟨by rw [List.map_cons, instHead, instTail], fun p' member => ?_⟩
          rcases List.mem_cons.mp member with rfl | member
          · exact varsHead
          · exact varsTail p' member

/-- **The takes match a bag that begins with their instances**, with bindings agreeing with the
instantiation. -/
theorem matchBag_prefix (f : String → Option Pattern) (θ : ℕ → Expr)
    (agreeθ : ∀ x, f (unknownName x) = some (rowCode (θ x))) (rest : String) (remainder : List Pattern)
    (restAgrees : f rest = some (.collection .hashBag remainder none)) : ∀ ps : List Tm,
    ∃ bs, MatchBagRel (ps.map termCode) (some rest) .hashBag ((ps.map (inst θ)).map rowCode ++ remainder) bs ∧
      Agrees f bs ∧ (rest, .collection .hashBag remainder none) ∈ bs ∧
      ∀ p ∈ ps, ∀ x ∈ p.freeVars, (unknownName x, rowCode (θ x)) ∈ bs
  | [] => ⟨[(rest, .collection .hashBag remainder none)], .nilRest, fun e member => by
      rw [List.mem_singleton.mp member]
      exact restAgrees, List.mem_singleton_self _, fun _ member => absurd member List.not_mem_nil⟩
  | p :: ps => by
      obtain ⟨tailBindings, tailMatch, tailAgrees, tailRest, tailVars⟩ :=
        matchBag_prefix f θ agreeθ rest remainder restAgrees ps
      obtain ⟨hb, headMatch, headSub, headAll⟩ := matchRel_termCode θ p
      have headAgrees : Agrees f hb := fun e member => by
        obtain ⟨x, -, rfl⟩ := headSub e member
        exact agreeθ x
      obtain ⟨bs, merged, agrees, -, super⟩ := merge_exists f tailBindings hb headAgrees tailAgrees
      refine ⟨bs, ?_, agrees, super _ (List.mem_append_right _ tailRest), fun p' member x vars => ?_⟩
      · rw [List.map_cons, List.map_cons, List.map_cons, List.cons_append]
        exact .cons 0 (by simp) headMatch tailMatch merged
      · rcases List.mem_cons.mp member with rfl | member
        · exact super _ (List.mem_append_left _ (headAll x vars))
        · exact super _ (List.mem_append_right _ (tailVars p' member x vars))

/-! ## The assignment of a firing by matching -/

/-- The bindings a firing by matching makes: the rest, the remainder of each read, and each unknown's row. -/
noncomputable def firingAssignment (θ : ℕ → Expr) (rest : List Expr) (reads : List Tm) (n : String) :
    Option Pattern := by
  classical
  exact if n = "rest" then some (.collection .hashBag (rest.map rowCode) none)
    else if found : ∃ j, j < reads.length ∧ readRestName j = n then
      some (readBag rest (inst θ (reads.getD found.choose (.var 0))))
    else assignment θ n

theorem firingAssignment_unknown (θ : ℕ → Expr) (rest : List Expr) (reads : List Tm) (x : ℕ) :
    firingAssignment θ rest reads (unknownName x) = some (rowCode (θ x)) := by
  classical
  unfold firingAssignment
  rw [if_neg (unknownName_ne_rest x), dif_neg (fun ⟨j, _, same⟩ => unknownName_ne_readRestName x j same.symm)]
  exact assignment_unknown θ x

theorem firingAssignment_rest (θ : ℕ → Expr) (rest : List Expr) (reads : List Tm) :
    firingAssignment θ rest reads "rest" = some (.collection .hashBag (rest.map rowCode) none) := by
  classical
  unfold firingAssignment
  rw [if_pos rfl]

theorem firingAssignment_read (θ : ℕ → Expr) (rest : List Expr) (reads : List Tm) {j : ℕ} (bound : j < reads.length) :
    firingAssignment θ rest reads (readRestName j) = some (readBag rest (inst θ reads[j])) := by
  classical
  have found : ∃ i, i < reads.length ∧ readRestName i = readRestName j := ⟨j, bound, rfl⟩
  unfold firingAssignment
  rw [if_neg (readRestName_ne_rest j), dif_pos found]
  have chosen : found.choose = j := readRestName_injective found.choose_spec.2
  rw [chosen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]

/-! ## The right side -/

theorem restResolution_bound {b : Bindings} {B : List Pattern}
    (found : b.find? (·.1 == "rest") = some ("rest", .collection .hashBag B none)) :
    restResolution b .hashBag (some "rest") = (B, none) := by
  simp [restResolution, found]

theorem right_instantiated (b : Bindings) (θ : ℕ → Expr) (produce : List Tm) (rest : List Expr)
    (restFound : b.find? (·.1 == "rest") = some ("rest", .collection .hashBag (rest.map rowCode) none))
    (bound : ∀ p ∈ produce, ∀ x ∈ p.freeVars,
      b.find? (·.1 == unknownName x) = some (unknownName x, rowCode (θ x))) :
    applyBindings b (.collection .hashBag (produce.map termCode) (some "rest")) =
      storeCode (produce.map (inst θ) ++ rest) := by
  rw [applyBindings_collection, restResolution_bound restFound, storeCode, List.map_append]
  congr 2
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun p member => applyBindings_termCode_of_lookup b θ p (bound p member)

theorem applyBindingsForRule_schematic (L : LanguageDef) (index : ℕ) (r : SRule) (b : Bindings) :
    applyBindingsForRule L (schematicRewrite index r) b =
      applyBindings b (.collection .hashBag (r.body.produce.map termCode) (some "rest")) := by
  rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _ (schematicRewrite_aligned index r)]
  rfl

theorem readPremise_mem {r : SRule} {q : Tm} (member : q ∈ r.body.read) :
    ∃ j, ∃ bound : j < r.body.read.length, r.body.read[j] = q ∧ readPremise j q ∈ r.body.read.mapIdx readPremise := by
  obtain ⟨j, bound, found⟩ := List.mem_iff_getElem.mp member
  exact ⟨j, bound, found, List.mem_mapIdx.mpr ⟨j, bound, by rw [found]⟩⟩

/-! ## The step, one rule at a time -/

variable {relEnv : RelationEnv} {rules : List SRule}

/-- **A primitive step of the presented language from a store is a firing by matching.** -/
theorem step_sound (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {rows : List Expr} {target : Pattern}
    (step : Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) (presentSchematic rules)
      (storeCode rows) target) :
    ∃ r ∈ rules, ∃ θ rest, MatchFires r θ rows rest ∧ target = storeCode (r.body.produce.map (inst θ) ++ rest) := by
  obtain ⟨fuel, stepAt⟩ := step
  cases stepAt with
  | @rule fuel' source' target' rule initial final ruleMember matched premises targetEq =>
  obtain ⟨r, inRules, index, rfl⟩ := of_mem_rewrites ruleMember
  have restricted := (fragment r inRules).2.2
  rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
  change MatchRel (.collection .hashBag (r.body.take.map termCode) (some "rest"))
    (.collection .hashBag (rows.map rowCode) none) initial at matched
  cases matched with
  | collection _ bagMatch =>
  obtain ⟨chosen, remainder, perm, takeEach, restExt⟩ := matchBag_terms bagMatch
  have codes : ∀ t ∈ chosen ++ remainder, ∃ e, t = rowCode e := by
    intro t member
    obtain ⟨e, -, same⟩ := List.mem_map.mp (perm.subset member)
    exact ⟨e, same.symm⟩
  obtain ⟨chosenRows, rfl⟩ := exists_rows fun t member => codes t (List.mem_append_left _ member)
  obtain ⟨remRows, rfl⟩ := exists_rows fun t member => codes t (List.mem_append_right _ member)
  have rowsPerm : (chosenRows ++ remRows).Perm rows := by
    rw [← List.map_append] at perm
    exact (List.map_perm_map_iff rowCode_injective).mp perm
  have restFoundInitial :
      initial.find? (·.1 == "rest") = some ("rest", .collection .hashBag (remRows.map rowCode) none) :=
    restExt _ _ (by simp)
  change PremisesAt _ _ _ initial (premisesOf r) final at premises
  obtain ⟨mid, readsAt, equationsAt⟩ := premisesAt_append.mp premises
  obtain ⟨initialMid, -, readsHold⟩ := premisesAt_sound (base := engineBasePremises relEnv)
    (fun p => ∃ j q, p = readPremise j q)
    (fun b => b.find? (·.1 == "rest") = some ("rest", .collection .hashBag (remRows.map rowCode) none))
    (fun p b => ∀ j q, p = readPremise j q → applyBindings b (termCode q) ∈ remRows.map rowCode)
    (fun b p res allowed inv premise => by
      obtain ⟨j, q, rfl⟩ := allowed
      have member : res ∈ premiseStepWithEnv relEnv (presentSchematic rules) b (readPremise j q) :=
        premiseAt_engine_iff.mp premise
      obtain ⟨extended, holds⟩ := readPremise_sound relEnv noEq inv member
      refine ⟨extended, extended _ _ inv, fun final' finalExt j' q' same => ?_⟩
      have patterns := congrArg readPatternOf same
      simp only [readPatternOf, readPremise, Option.some.injEq] at patterns
      rw [← patterns]
      exact holds final' finalExt)
    (fun p member => by
      obtain ⟨j, -, rfl⟩ := List.mem_mapIdx.mp member
      exact ⟨j, _, rfl⟩)
    restFoundInitial readsAt
  obtain ⟨midFinal, -, equationsHold⟩ := premisesAt_sound (base := engineBasePremises relEnv)
    (fun p => ∃ e, p = equationPremise e) (fun _ => True)
    (fun p b => ∀ e, p = equationPremise e → applyBindings b (termCode e.1) = applyBindings b (termCode e.2))
    (fun b p res allowed _ premise => by
      obtain ⟨e, rfl⟩ := allowed
      have member : res ∈ premiseStepWithEnv relEnv (presentSchematic rules) b (equationPremise e) :=
        premiseAt_engine_iff.mp premise
      obtain ⟨extended, holds⟩ := equationPremise_sound relEnv noEq member
      refine ⟨extended, trivial, fun final' finalExt e' same => ?_⟩
      have sides := congrArg sidesOf same
      simp only [sidesOf, equationPremise, Option.some.injEq, Prod.mk.injEq] at sides
      rw [← sides.1, ← sides.2]
      exact holds final' finalExt)
    (fun p member => by
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp member
      exact ⟨e, rfl⟩)
    trivial equationsAt
  have initialFinal : BindingsExtends initial final := extends_trans initialMid midFinal
  -- the takes
  obtain ⟨takeInst, takeVars⟩ := decode_forall₂ (final := final)
    (List.Forall₂.imp (fun _ _ holds => holds final initialFinal) takeEach)
  -- the reads
  have readFacts : ∀ q ∈ r.body.read, inst (groundOf final) q ∈ remRows ∧ ∀ x ∈ q.freeVars,
      final.find? (·.1 == unknownName x) = some (unknownName x, rowCode (groundOf final x)) := by
    intro q member
    obtain ⟨j, -, -, premiseMember⟩ := readPremise_mem member
    have inRest := readsHold _ premiseMember final midFinal j q rfl
    obtain ⟨e, inRem, same⟩ := List.mem_map.mp inRest
    obtain ⟨instQ, varsQ⟩ := applyBindings_termCode_eq_rowCode final q e same.symm
    exact ⟨instQ ▸ inRem, varsQ⟩
  have boundFound : ∀ x, Bound r x →
      final.find? (·.1 == unknownName x) = some (unknownName x, rowCode (groundOf final x)) := by
    rintro x ⟨t, member, vars⟩
    rcases List.mem_append.mp member with taken | read
    · exact takeVars t taken x vars
    · exact (readFacts t read).2 x vars
  have instantiated : ∀ t ∈ written r,
      applyBindings final (termCode t) = rowCode (inst (groundOf final) t) := fun t member =>
    applyBindings_termCode_of_lookup final _ t fun x vars => boundFound x (restricted t member x vars)
  refine ⟨r, inRules, groundOf final, remRows, ⟨?_, fun q member => (readFacts q member).1, ?_⟩, ?_⟩
  · rw [takeInst]
    exact rowsPerm
  · intro e member
    have equal := equationsHold _ (List.mem_map_of_mem member) final (extends_refl _) e rfl
    have written := mem_written_of_equation member
    rw [instantiated _ written.1, instantiated _ written.2] at equal
    exact rowCode_injective equal
  · rw [← targetEq, applyBindingsForRule_schematic]
    exact right_instantiated final _ _ remRows (initialFinal _ _ restFoundInitial) fun p member x vars =>
      boundFound x (restricted p (mem_written_of_produce member) x vars)

/-- **Every firing by matching is a primitive step**, from the arrangement with the taken rows first. -/
theorem step_prefix (noEq : ∀ args, relEnv.tuples "eq" args = []) {r : SRule} (member : r ∈ rules)
    (restricted : RangeRestricted r) {θ : ℕ → Expr} {rest : List Expr}
    (reads : ∀ q ∈ r.body.read, inst θ q ∈ rest) (equations : ∀ e ∈ equationsOf r, inst θ e.1 = inst θ e.2) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) (presentSchematic rules)
      (storeCode (r.body.take.map (inst θ) ++ rest)) (storeCode (r.body.produce.map (inst θ) ++ rest)) := by
  obtain ⟨index, presented⟩ := exists_mem_rewrites member
  have agreeθ := firingAssignment_unknown θ rest r.body.read
  obtain ⟨initial, bagMatch, initialAgrees, restIn, takeVars⟩ := matchBag_prefix (firingAssignment θ rest r.body.read)
    θ agreeθ "rest" (rest.map rowCode) (firingAssignment_rest θ rest r.body.read) r.body.take
  obtain ⟨mid, readsAt, ⟨midAgrees, -⟩, initialMid, readVars⟩ := premisesAt_complete
    (base := engineBasePremises relEnv) (L := presentSchematic rules) (fuel := 0)
    (fun p => ∃ j, ∃ bound : j < r.body.read.length, p = readPremise j r.body.read[j])
    (fun b => Agrees (firingAssignment θ rest r.body.read) b ∧
      ("rest", .collection .hashBag (rest.map rowCode) none) ∈ b)
    (fun p b => ∀ j (bound : j < r.body.read.length), p = readPremise j r.body.read[j] →
      ∀ x ∈ (r.body.read[j]).freeVars, (unknownName x, rowCode (θ x)) ∈ b)
    (fun _ _ _ holds super j bound same x vars => super _ (holds j bound same x vars))
    (fun b p allowed inv => by
      obtain ⟨j, bound, rfl⟩ := allowed
      obtain ⟨res, resMember, resAgrees, resSuper, resVars⟩ := readPremise_complete relEnv noEq
        (presentSchematic rules) (firingAssignment θ rest r.body.read) θ agreeθ inv.1 inv.2
        (reads _ (List.getElem_mem bound)) (firingAssignment_read θ rest r.body.read bound)
      refine ⟨res, premiseAt_engine_iff.mpr resMember, ⟨resAgrees, resSuper _ inv.2⟩, resSuper,
        fun j' bound' same x vars => ?_⟩
      have names := congrArg readRestOf same
      simp only [readRestOf, readPremise, Option.some.injEq] at names
      have indices : j = j' := readRestName_injective names
      subst indices
      exact resVars x vars)
    (ps := r.body.read.mapIdx readPremise) (fun p member => by
      obtain ⟨j, bound, rfl⟩ := List.mem_mapIdx.mp member
      exact ⟨j, bound, rfl⟩)
    initial ⟨initialAgrees, restIn⟩
  have midBound : ∀ x, Bound r x → (unknownName x, rowCode (θ x)) ∈ mid := by
    rintro x ⟨t, inPatterns, vars⟩
    rcases List.mem_append.mp inPatterns with taken | read
    · exact initialMid _ (takeVars t taken x vars)
    · obtain ⟨j, bound, found, premiseMember⟩ := readPremise_mem read
      refine readVars _ premiseMember j bound ?_ x (by rw [found]; exact vars)
      rw [found]
  obtain ⟨final, equationsAt, ⟨finalAgrees, finalBound⟩, midFinal, -⟩ := premisesAt_complete
    (base := engineBasePremises relEnv) (L := presentSchematic rules) (fuel := 0)
    (fun p => ∃ e ∈ equationsOf r, p = equationPremise e)
    (fun b => Agrees (firingAssignment θ rest r.body.read) b ∧ ∀ x, Bound r x → (unknownName x, rowCode (θ x)) ∈ b)
    (fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (fun b p allowed inv => by
      obtain ⟨e, inEquations, rfl⟩ := allowed
      have written := mem_written_of_equation inEquations
      obtain ⟨res, resMember, resAgrees, resSuper⟩ := equationPremise_complete relEnv noEq (presentSchematic rules)
        (firingAssignment θ rest r.body.read) θ agreeθ inv.1
        (fun x vars => inv.2 x (restricted _ written.1 x vars)) (equations e inEquations)
      exact ⟨res, premiseAt_engine_iff.mpr resMember,
        ⟨resAgrees, fun x bound => resSuper _ (inv.2 x bound)⟩, resSuper, trivial⟩)
    (ps := (equationsOf r).map equationPremise) (fun p member => by
      obtain ⟨e, inEquations, rfl⟩ := List.mem_map.mp member
      exact ⟨e, inEquations, rfl⟩)
    mid ⟨midAgrees, midBound⟩
  refine ⟨1, .rule presented ?_ (premisesAt_append.mpr ⟨mid, readsAt, equationsAt⟩) ?_⟩
  · rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
    show MatchRel (.collection .hashBag (r.body.take.map termCode) (some "rest"))
      (.collection .hashBag ((r.body.take.map (inst θ) ++ rest).map rowCode) none) initial
    rw [List.map_append]
    exact .collection (by decide) bagMatch
  · rw [applyBindingsForRule_schematic]
    exact right_instantiated final θ _ rest (find?_of_agrees finalAgrees (midFinal _ (initialMid _ restIn)))
      fun p inProduce x vars =>
        find?_of_agrees finalAgrees (finalBound x (restricted p (mem_written_of_produce inProduce) x vars))

/-! ## The framework's step and possibility on stores -/

/-- **The framework's step modulo equations from a store is a firing by matching**, to a term equal, modulo
the equations, to the store of the made rows beside the rest. -/
theorem semanticStep_storeCode_iff (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {rows : List Expr} {target : Pattern} :
    langSemanticReducesUsing relEnv (presentSchematic rules) (storeCode rows) target ↔
      ∃ r ∈ rules, ∃ θ rest, MatchFires r θ rows rest ∧
        EquationEquiv (engineBasePremises relEnv) (presentSchematic rules)
          (storeCode (r.body.produce.map (inst θ) ++ rest)) target := by
  change StepModuloEquations (engineBasePremises relEnv) (presentSchematic rules) (storeCode rows) target ↔ _
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    obtain ⟨arranged, rfl, perm⟩ := storeCode_of_equationEquiv presentSchematic_equations presentSchematic_noAlgebra
      before
    obtain ⟨r, member, θ, rest, fires, rfl⟩ := step_sound noEq fragment step
    exact ⟨r, member, θ, rest, ⟨fires.takes.trans perm.symm, fires.reads, fires.equations⟩, after⟩
  · rintro ⟨r, member, θ, rest, fires, after⟩
    exact ⟨storeCode (r.body.take.map (inst θ) ++ rest), storeCode (r.body.produce.map (inst θ) ++ rest),
      equationEquiv_storeCode_of_perm presentSchematic_formers presentSchematic_store fires.takes.symm,
      step_prefix noEq member (fragment r member).2.2 fires.reads fires.equations, after⟩

/-- **The framework's generated possibility at a store**: some firing by matching leads to a store, of the
made rows' instances beside the rest, with the property. -/
theorem diamond_storeCode_iff (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r)
    (φ : EquationPredicate (langGSLTUsing relEnv (presentSchematic rules))) (rows : List Expr) :
    (langDiamondUsing relEnv (presentSchematic rules) φ).1 (storeCode rows) ↔
      ∃ r ∈ rules, ∃ θ rest, MatchFires r θ rows rest ∧ φ.1 (storeCode (r.body.produce.map (inst θ) ++ rest)) := by
  refine (langDiamondUsing_spec relEnv (presentSchematic rules) φ (storeCode rows)).trans ?_
  constructor
  · rintro ⟨target, step, holds⟩
    obtain ⟨r, member, θ, rest, fires, after⟩ := (semanticStep_storeCode_iff noEq fragment).mp step
    exact ⟨r, member, θ, rest, fires, (φ.2 after).mpr holds⟩
  · rintro ⟨r, member, θ, rest, fires, holds⟩
    exact ⟨_, (semanticStep_storeCode_iff noEq fragment).mpr ⟨r, member, θ, rest, fires, Relation.EqvGen.refl _⟩,
      holds⟩

/-- **The parallel context rule holds**: a step of a store is a step of the store beside further rows. -/
theorem semanticStep_beside (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {rows next : List Expr} (extra : List Expr)
    (step : langSemanticReducesUsing relEnv (presentSchematic rules) (storeCode rows) (storeCode next)) :
    langSemanticReducesUsing relEnv (presentSchematic rules) (storeCode (rows ++ extra))
      (storeCode (next ++ extra)) := by
  obtain ⟨r, member, θ, rest, fires, after⟩ := (semanticStep_storeCode_iff noEq fragment).mp step
  have reached := (equationEquiv_storeCode_iff presentSchematic_equations presentSchematic_noAlgebra
    presentSchematic_formers presentSchematic_store).mp after
  refine (semanticStep_storeCode_iff noEq fragment).mpr ⟨r, member, θ, rest ++ extra, fires.beside extra, ?_⟩
  rw [← List.append_assoc]
  exact equationEquiv_storeCode_of_perm presentSchematic_formers presentSchematic_store (reached.append_right extra)

#print axioms MatchFires.beside
#print axioms matchBag_terms
#print axioms decode_forall₂
#print axioms matchBag_prefix
#print axioms right_instantiated
#print axioms step_sound
#print axioms step_prefix
#print axioms semanticStep_storeCode_iff
#print axioms diamond_storeCode_iff
#print axioms semanticStep_beside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic
