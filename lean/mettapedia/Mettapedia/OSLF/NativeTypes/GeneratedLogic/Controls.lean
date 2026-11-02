import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Invariance
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Transfer
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Generated
import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Controls: the generated logic

Two small languages. `tiny` has processes `Nil`, `Out p`, `Par p q` and an abstraction `Abs`, the rule
`Out p ~> p`, and the congruence `Par p q ~> Par p' q if p ~> p'` for the left component only.
`tinyComm` adds the equation `Par p q = Par q p`. `soup` is a bag of atoms `A` and `B`.

- **Sites.** At `Par (Out Nil) Nil`, a step of `Out` happens at the site of the congruence: the label
  `under 1 (rule 0)` admits it, while `rule 0` and `under 1 (rule 1)` do not.
- **Object terms.** A schema pattern, here one holding a pending substitution, steps in the raw
  reference relation but is not a state, so it is no predecessor in the language's structure.
- **Equations.** At `Par Nil (Out Nil)` nothing steps in `tiny`, since the congruence covers the left
  component only. In `tinyComm` the commuted term steps at the same site, and it is built by `Par` from
  an `Out` and `Nil`. Equivalent terms satisfy the same closed formulas (`commuted_agree`); without the
  equation the two are told apart.
- **Separation.** The bag `{A, B}` splits into `{A}` and `{B}`, and, by the bag law, into `{B}` and
  `{A}`. It does not split into two parts each holding `A`, since splitting keeps the number of `A`s.
- **Types.** `Nil` is a closed term of type `Proc`. The body of `λx. x` is open, so it has no type. Some
  `Proc` term fires, and not every `Proc` term steps.
- **Hom types.** `λx. Out x` sends every argument to an `Out`, and does not send every `Proc` to `Nil`.
- **Certificates.** A two-element abstraction of `tiny`, recording whether a rule can fire at the root,
  proves at once that every term whose root is neither `Out` nor `Par` is stuck.
- **Φ(L).** Each language generates its own formers and not the other's; a bag carrier is read through
  the collection formers, not as a constructor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern Bindings)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.WellSorted
  (checkOpenPatternWellSorted_sound FreeTypeContext UsesBareCollection
    isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.EquationSemantics
  (DerivedInstance CollectionCarrierRule usesCollection_eq_true_of_collectionTypedAt
    no_algebraRule_of_hasAlgebraDeclarations_eq_false)
open Formula NativeStructure

/-! ## The languages -/

def proc : TypeExpr := .base "Proc"

def nilTerm : Pattern := .apply "Nil" []
def out (process : Pattern) : Pattern := .apply "Out" [process]
def par (first second : Pattern) : Pattern := .apply "Par" [first, second]

/-- `Out p ~> p`. -/
def fire : RewriteRule :=
  { name := "Fire", typeContext := [], premises := [], left := out (.fvar "p"), right := .fvar "p" }

/-- `Par p q ~> Par p' q if p ~> p'`: the congruence for the left component. -/
def parLeft : RewriteRule :=
  { name := "ParLeft", typeContext := [], premises := [.congruence (.fvar "p") (.fvar "p'")],
    left := par (.fvar "p") (.fvar "q"), right := par (.fvar "p'") (.fvar "q") }

def parRule : GrammarRule :=
  { label := "Par", category := "Proc", params := [.simple "p" proc, .simple "q" proc], syntaxPattern := [] }

def grammar : List GrammarRule :=
  [{ label := "Nil", category := "Proc", params := [], syntaxPattern := [] },
   { label := "Out", category := "Proc", params := [.simple "p" proc], syntaxPattern := [] },
   parRule,
   { label := "Abs", category := "Proc", params := [.abstractionNamed none "body" (.arrow proc proc)],
     syntaxPattern := [] }]

def tiny : LanguageDef :=
  { name := "Tiny", types := ["Proc"], terms := grammar, equations := [], rewrites := [fire, parLeft] }

/-- `Par p q = Par q p`. -/
def parComm : Equation :=
  { name := "ParComm", typeContext := [], premises := [], left := par (.fvar "p") (.fvar "q"),
    right := par (.fvar "q") (.fvar "p") }

def tinyComm : LanguageDef := { tiny with name := "TinyComm", equations := [parComm] }

abbrev Tiny : NativeStructure Pattern := referenceStructure RelationEnv.empty tiny
abbrev TinyComm : NativeStructure Pattern := referenceStructure RelationEnv.empty tinyComm

/-! ## Steps of an equation-free language -/

theorem tiny_equationFree : tiny.isEquationFree = true := by decide

theorem tiny_equivalent {first second : Pattern} :
    ObjectEquivalent RelationEnv.empty tiny .syntax first second ↔ first = second :=
  objectEquivalent_iff_eq_of_isEquationFree tiny_equationFree

/-- A listed step between states, whose witness the label admits, is a step of the structure. -/
theorem step_of_listed {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ} {source target : Pattern}
    {label : StepLabel} (sourceState : IsState source) (targetState : IsState target)
    (listed : ∃ entry ∈ stepsAt relEnv language fuel source, entry.2 = target ∧ label.admits entry.1 = true) :
    (referenceStructure relEnv language).step source label target := by
  obtain ⟨⟨witness, result⟩, member, rfl, admitted⟩ := listed
  exact ⟨sourceState, targetState, source, result, witness, placed_self admitted _, sourceState,
    stepValid_of_mem_stepsAt relEnv language member, targetState, Relation.EqvGen.refl _, StepLabel.base_admits admitted⟩

/-- In `tiny`, a step with a label of the term's own is a valid witness between states that the label admits. -/
theorem tiny_step {source target : Pattern} {label : StepLabel} (own : label.isContext = false) :
    Tiny.step source label target ↔ IsState source ∧ IsState target ∧
      ∃ witness, StepValid RelationEnv.empty tiny source witness target ∧ label.admits witness = true := by
  constructor
  · rintro ⟨sourceState, targetState, redex, contractum, witness, before, -, valid, -, after, admitted⟩
    rw [placed_iff own, tiny_equivalent] at before
    rw [tiny_equivalent] at after
    subst before after
    exact ⟨sourceState, targetState, witness, valid, StepLabel.admits_of_base own admitted⟩
  · rintro ⟨sourceState, targetState, witness, valid, admitted⟩
    exact ⟨sourceState, targetState, source, target, witness, placed_self admitted _, sourceState, valid, targetState,
      Relation.EqvGen.refl _, StepLabel.base_admits admitted⟩

/-- No step starts where no rule matches. -/
theorem no_stepValid_of_unmatched {source target : Pattern} {witness : Witness}
    (unmatched : ∀ rule ∈ tiny.rewrites, matchPattern rule.left source = []) :
    ¬ StepValid RelationEnv.empty tiny source witness target := by
  intro valid
  cases valid with
  | rule found matched _ =>
    rw [matchPatternForRule_eq_syntactic, unmatched _ (List.mem_of_getElem? found)] at matched
    cases matched

theorem nil_stuck {target : Pattern} {witness : Witness} :
    ¬ StepValid RelationEnv.empty tiny nilTerm witness target :=
  no_stepValid_of_unmatched (by decide +kernel)

/-- `Fire` does not step a term its left side does not match. -/
theorem not_fire {source target : Pattern} {initial : Bindings} {witnesses : List Witness}
    (unmatched : matchPattern fire.left source = []) :
    ¬ StepValid RelationEnv.empty tiny source (.rule 0 initial witnesses) target := by
  intro valid
  cases valid with
  | rule found matched _ =>
    simp only [tiny, List.getElem?_cons_zero, Option.some.injEq] at found
    subst found
    rw [matchPatternForRule_eq_syntactic, unmatched] at matched
    cases matched

/-- `tiny` has two rules. -/
theorem not_beyond {source target : Pattern} {index : ℕ} {initial : Bindings} {witnesses : List Witness} :
    ¬ StepValid RelationEnv.empty tiny source (.rule (index + 2) initial witnesses) target := by
  intro valid
  cases valid with
  | rule found _ _ => simp [tiny] at found

theorem out_no_congruence {target : Pattern} {initial : Bindings} {witnesses : List Witness} :
    ¬ StepValid RelationEnv.empty tiny (out nilTerm) (.rule 1 initial witnesses) target := by
  intro valid
  cases valid with
  | rule found matched _ =>
    simp only [tiny, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
    subst found
    rw [matchPatternForRule_eq_syntactic,
      show matchPattern parLeft.left (out nilTerm) = [] by decide +kernel] at matched
    cases matched

/-- The only premise witness of `ParLeft` at `Par x y` is a step of `x`. -/
theorem parLeft_premise {first second target : Pattern} {initial : Bindings} {witnesses : List Witness}
    (valid : StepValid RelationEnv.empty tiny (par first second) (.rule 1 initial witnesses) target) :
    ∃ step candidate matched result, witnesses = [.premiseStep step candidate matched result] ∧
      ∃ stepTarget, StepValid RelationEnv.empty tiny first step stepTarget := by
  cases valid with
  | rule found matched premises =>
    simp only [tiny, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
    subst found
    rw [matchPatternForRule_eq_syntactic] at matched
    have bindings : matchPattern parLeft.left (par first second) = [[("q", second), ("p", first)]] := by
      simp [parLeft, par, matchPattern, Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
        Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]
    rw [bindings, List.mem_singleton] at matched
    subst matched
    have depth : Mettapedia.OSLF.MeTTaIL.Match.captureDepth "p" 0 (captureSites parLeft) = some 0 := by
      decide +kernel
    cases premises with
    | cons premise rest =>
      cases rest
      cases premise with
      | base based _ => simp [Mettapedia.OSLF.MeTTaIL.ReferenceStep.isBase] at based
      | @step _ _ _ _ _ _ _ candidate innerStep endpoints innerValid _ _ =>
        simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
        obtain ⟨rfl, rfl⟩ := endpoints
        refine ⟨innerStep, candidate, _, _, rfl, candidate, ?_⟩
        simpa [Mettapedia.OSLF.MeTTaIL.Match.applyBindingsScoped, stepDepth, inPlaceDepth, depth,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero] using innerValid

/-! ## Sites -/

/-- **A step at the site of the congruence**: `Par (Out Nil) Nil` steps by `Out` under `ParLeft`. -/
theorem fires_under_congruence :
    Tiny.sat Env.closed (.possibly (.under 1 (.rule 0)) .top) (par (out nilTerm) nilTerm) :=
  ⟨par nilTerm nilTerm, step_of_listed (fuel := 2) (by decide) (by decide) (by decide +kernel), trivial⟩

/-- `Out` does not fire at the root of `Par (Out Nil) Nil`. -/
theorem not_fires_at_root : ¬ Tiny.sat Env.closed (.possibly (.rule 0) .top) (par (out nilTerm) nilTerm) := by
  rintro ⟨next, step, -⟩
  obtain ⟨-, -, witness, valid, admitted⟩ := (tiny_step rfl).mp step
  cases witness with
  | rule index initial witnesses =>
    simp only [StepLabel.admits, ruleOf, beq_iff_eq, Option.some.injEq] at admitted
    subst admitted
    exact not_fire (by decide +kernel) valid
  | _ => cases valid

/-- The step under `ParLeft` fires `Out`, not `ParLeft` again. -/
theorem not_under_congruence_twice :
    ¬ Tiny.sat Env.closed (.possibly (.under 1 (.rule 1)) .top) (par (out nilTerm) nilTerm) := by
  rintro ⟨next, step, -⟩
  obtain ⟨-, -, witness, valid, admitted⟩ := (tiny_step rfl).mp step
  cases witness with
  | rule index initial witnesses =>
    simp only [StepLabel.admits, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at admitted
    obtain ⟨rfl, inner, member, innerAdmitted⟩ := admitted
    obtain ⟨innerStep, candidate, matched, result, rfl, stepTarget, innerValid⟩ := parLeft_premise valid
    simp only [premiseStepsList, premiseSteps, List.append_nil, List.mem_singleton] at member
    subst member
    cases inner with
    | rule index' initial' witnesses' =>
      simp only [ruleOf, Option.some.injEq] at innerAdmitted
      subst innerAdmitted
      exact out_no_congruence innerValid
    | _ => simp [ruleOf] at innerAdmitted
  | _ => cases valid

/-! ## Object terms -/

/-- `Drop p q ~> p`. -/
def drop : RewriteRule :=
  { name := "Drop", typeContext := [], premises := [], left := .apply "Drop" [.fvar "p", .fvar "q"],
    right := .fvar "p" }

def dropLanguage : LanguageDef :=
  { name := "Drop", types := ["Proc"], terms := [], equations := [], rewrites := [drop] }

/-- A schema pattern: `Drop Nil` applied to a pending substitution. -/
def schemaDrop : Pattern := .apply "Drop" [nilTerm, .subst (.bvar 0) nilTerm]

/-- The raw reference relation steps the schema pattern to `Nil`. -/
theorem schema_raw_step : Step RelationEnv.empty dropLanguage schemaDrop nilTerm := by
  obtain ⟨⟨witness, result⟩, member, same⟩ :
      ∃ entry ∈ stepsAt RelationEnv.empty dropLanguage 1 schemaDrop, entry.2 = nilTerm := by decide +kernel
  simp only at same
  subst same
  exact ⟨witness, stepValid_of_mem_stepsAt RelationEnv.empty dropLanguage member⟩

/-- **A schema pattern is no predecessor** in the language's structure: it is not a state. -/
theorem schema_not_predecessor :
    ¬ (referenceStructure RelationEnv.empty dropLanguage).step schemaDrop .any nilTerm :=
  fun step => absurd step.1.2 (by decide)

/-- A state that drops its second component is a predecessor of `Nil`. -/
theorem state_predecessor :
    (referenceStructure RelationEnv.empty dropLanguage).step (.apply "Drop" [nilTerm, nilTerm]) .any nilTerm :=
  step_of_listed (fuel := 1) (by decide) (by decide) (by decide +kernel)

/-! ## Equations -/

/-- Without the equation, `Par Nil (Out Nil)` is stuck: the congruence covers the left component. -/
theorem right_component_stuck : ¬ Tiny.sat Env.closed (.possibly .any .top) (par nilTerm (out nilTerm)) := by
  rintro ⟨next, step, -⟩
  obtain ⟨-, -, witness, valid, -⟩ := (tiny_step rfl).mp step
  cases witness with
  | rule index initial witnesses =>
    match index, valid with
    | 0, valid => exact not_fire (by decide +kernel) valid
    | 1, valid =>
      obtain ⟨_, _, _, _, _, _, innerValid⟩ := parLeft_premise valid
      exact nil_stuck innerValid
    | _ + 2, valid => exact not_beyond valid
  | _ => cases valid

/-- `Par Nil (Out Nil) = Par (Out Nil) Nil` by commutativity. -/
theorem commuted_equivalent :
    ObjectEquivalent RelationEnv.empty tinyComm .syntax (par nilTerm (out nilTerm)) (par (out nilTerm) nilTerm) := by
  have authored : AuthoredEquation RelationEnv.empty tinyComm (par nilTerm (out nilTerm))
      (Mettapedia.OSLF.MeTTaIL.Match.applyBindingsScoped (captureSitesOf parComm.left parComm.premises)
        [("q", out nilTerm), ("p", nilTerm)] 0 parComm.right) :=
    .forward (equation := parComm) (by simp [tinyComm]) rfl (by decide +kernel) (.nil _)
  have instantiated : Mettapedia.OSLF.MeTTaIL.Match.applyBindingsScoped
      (captureSitesOf parComm.left parComm.premises) [("q", out nilTerm), ("p", nilTerm)] 0 parComm.right =
        par (out nilTerm) nilTerm := by decide +kernel
  rw [instantiated] at authored
  exact Relation.EqvGen.rel _ _ ⟨by decide, by decide, EquationStep.inContext .hole (Or.inl authored)⟩

/-- **Modulo commutativity, the commuted term steps at the site of the congruence.** -/
theorem fires_modulo_commutativity :
    TinyComm.sat Env.closed (.possibly (.under 1 (.rule 0)) .top) (par nilTerm (out nilTerm)) :=
  ⟨par nilTerm nilTerm,
    (referenceStructure_saturated RelationEnv.empty tinyComm).stepSource
      (Indistinct.of_states (by decide) (by decide) (ObjectEquivalent.equivalence.symm commuted_equivalent))
      (step_of_listed (fuel := 2) (by decide) (by decide) (by decide +kernel)),
    trivial⟩

/-- `Par` of an `Out` and `Nil`. -/
def parOfOutAndNil : Formula 0 := .built "Par" (.cons (.built "Out" (.cons .top .nil)) (.cons (.is nilTerm) .nil))

/-- **Modulo commutativity, `Par Nil (Out Nil)` is built by `Par` from an `Out` and `Nil`.** -/
theorem built_modulo_commutativity : TinyComm.sat Env.closed parOfOutAndNil (par nilTerm (out nilTerm)) :=
  ⟨[out nilTerm, nilTerm], ⟨by decide, commuted_equivalent⟩,
    ⟨⟨[nilTerm], ⟨by decide, Relation.EqvGen.refl _⟩, trivial, trivial⟩, ⟨by decide, Relation.EqvGen.refl _⟩, trivial⟩⟩

/-- Without the equation it is not: its first argument is `Nil`. -/
theorem not_built_without_equation : ¬ Tiny.sat Env.closed parOfOutAndNil (par nilTerm (out nilTerm)) := by
  rintro ⟨parts, ⟨-, isBuilt⟩, arguments⟩
  rw [tiny_equivalent] at isBuilt
  cases isBuilt
  obtain ⟨⟨outParts, ⟨-, isOut⟩, -⟩, -⟩ := arguments
  rw [tiny_equivalent] at isOut
  simp [nilTerm] at isOut

/-- **Equivalent terms satisfy the same closed formulas.** -/
theorem commuted_agree (formula : Formula 0) :
    TinyComm.sat Env.closed formula (par nilTerm (out nilTerm)) ↔
      TinyComm.sat Env.closed formula (par (out nilTerm) nilTerm) :=
  sat_respects_equivalent RelationEnv.empty tinyComm formula (by decide) (by decide) commuted_equivalent

/-- Without the equation, a formula tells the two apart. -/
theorem tiny_tells_commuted_apart :
    Tiny.sat Env.closed (.possibly .any .top) (par (out nilTerm) nilTerm) ∧
      ¬ Tiny.sat Env.closed (.possibly .any .top) (par nilTerm (out nilTerm)) :=
  ⟨⟨par nilTerm nilTerm, step_of_listed (fuel := 2) (by decide) (by decide) (by decide +kernel), trivial⟩,
    right_component_stuck⟩

/-! ## Types -/

theorem nil_typed : Tiny.sat Env.closed (.typed proc) nilTerm :=
  ⟨by decide, nilTerm, Relation.EqvGen.refl _, checkCarrierTyped_eq_true_iff.mp (by decide +kernel)⟩

/-- **An open body has no type**: the body of `λx. x` is the bound variable. -/
theorem open_body_untyped : Tiny.sat Env.closed (.body (.untyped proc)) (.lambda none (.bvar 0)) := by
  refine ⟨.bvar 0, ⟨by decide, none, Relation.EqvGen.refl _⟩, ?_⟩
  rintro ⟨-, representative, isRepresentative, wellSorted⟩
  rw [tiny_equivalent] at isRepresentative
  subst isRepresentative
  exact absurd (checkCarrierTyped_eq_true_iff.mpr wellSorted) (by decide +kernel)

/-- **Some `Proc` term fires.** -/
theorem some_proc_fires : Tiny.sat Env.closed (.someOf proc (.possibly (.rule 0) .top)) nilTerm :=
  ⟨out nilTerm, ⟨by decide, out nilTerm, Relation.EqvGen.refl _, checkCarrierTyped_eq_true_iff.mp (by decide +kernel)⟩,
    nilTerm, step_of_listed (fuel := 1) (by decide) (by decide) (by decide +kernel), trivial⟩

/-- **Not every `Proc` term steps**: `Nil` does not. -/
theorem not_every_proc_steps : ¬ Tiny.sat Env.closed (.everyOf proc (.possibly .any .top)) nilTerm := by
  intro every
  obtain ⟨next, step, -⟩ := every nilTerm nil_typed
  obtain ⟨-, -, witness, valid, -⟩ := (tiny_step rfl).mp step
  exact nil_stuck valid

/-! ## Hom types -/

theorem apply_out (value : Pattern) :
    Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar value (out (.bvar 0)) = out value := by
  simp [out, Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar,
    Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

/-- **`λx. Out x` sends every argument to an `Out`.** -/
theorem maps_to_out :
    Tiny.sat Env.closed (.mapsAll (.untyped proc) (.built "Out" (.cons .top .nil))) (.lambda none (out (.bvar 0))) := by
  refine ⟨out (.bvar 0), ⟨by decide, none, Relation.EqvGen.refl _⟩, fun value => ?_⟩
  by_cases object : IsObject value
  · refine Or.inr ⟨[value], ⟨?_, ?_⟩, trivial, trivial⟩
    · change IsObject (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar value (out (.bvar 0)))
      rw [apply_out]
      show isObjectPattern (.apply "Out" [value]) = true
      simpa [isObjectPattern, isObjectPatternList] using object
    · change ObjectEquivalent RelationEnv.empty tiny .syntax
        (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar value (out (.bvar 0))) (.apply "Out" [value])
      rw [apply_out]
      exact Relation.EqvGen.refl _
  · exact Or.inl fun typed => object typed.1

/-- It does not send every `Proc` to `Nil`: it sends `Nil` to `Out Nil`. -/
theorem not_maps_to_nil :
    ¬ Tiny.sat Env.closed (.mapsAll (.untyped proc) (.is nilTerm)) (.lambda none (out (.bvar 0))) := by
  rintro ⟨inner, ⟨-, name, isBody⟩, every⟩
  rw [tiny_equivalent] at isBody
  cases isBody
  rcases every nilTerm with untyped | ⟨-, isNil⟩
  · exact untyped nil_typed
  · change ObjectEquivalent RelationEnv.empty tiny .syntax
      (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar nilTerm (out (.bvar 0))) nilTerm at isNil
    rw [apply_out, tiny_equivalent] at isNil
    simp [out, nilTerm] at isNil

/-! ## Certificates -/

/-- Whether a rule of `tiny` can fire at the root of a term. -/
def mayFire : Pattern → Bool
  | .apply label _ => label == "Out" || label == "Par"
  | _ => false

/-- **A two-element abstraction of `tiny`**: whether a rule can fire at the root. Only such terms step;
every shape, type, name and relation is allowed. -/
def fireAbstraction : NativeStructure Bool where
  step source _ _ := source = true
  built _ _ _ := True
  split _ _ _ _ := True
  empty _ _ := True
  single _ _ _ := True
  body _ _ := True
  multiBody _ _ _ := True
  bound _ _ := True
  typed _ _ := True
  named _ _ := True
  same first second := first = second
  apply inner _ := inner
  inRelation _ _ := True

theorem label_of_mem_matchPattern {label : String} {arguments : List Pattern} {source : Pattern}
    {bindings : Bindings} (member : bindings ∈ matchPattern (.apply label arguments) source) :
    ∃ parts, source = .apply label parts := by
  cases source with
  | apply label' parts =>
    refine ⟨parts, ?_⟩
    rw [matchPattern] at member
    by_cases same : label = label'
    · rw [same]
    · simp [same] at member
  | _ => simp [matchPattern] at member

theorem mayFire_of_step {source target : Pattern} {label : StepLabel} (own : label.isContext = false)
    (step : Tiny.step source label target) : mayFire source = true := by
  obtain ⟨-, -, witness, valid, -⟩ := (tiny_step own).mp step
  cases valid with
  | @rule _ index rule _ _ _ found matched _ =>
    rw [matchPatternForRule_eq_syntactic] at matched
    match index, found with
    | 0, found =>
      simp only [tiny, List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      obtain ⟨parts, rfl⟩ := label_of_mem_matchPattern matched
      rfl
    | 1, found =>
      simp only [tiny, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      obtain ⟨parts, rfl⟩ := label_of_mem_matchPattern matched
      rfl
    | _ + 2, found => simp [tiny] at found

/-- The abstraction is a homomorphism. -/
def fireHom : Hom Tiny fireAbstraction where
  map := mayFire
  step := mayFire_of_step
  built := fun _ => trivial
  split := fun _ => trivial
  empty := fun _ => trivial
  single := fun _ => trivial
  body := fun _ => trivial
  multiBody := fun _ => trivial
  bound := fun _ => trivial
  typed := fun _ => trivial
  named := fun _ => trivial
  inRelation := fun _ => trivial

/-- **The certificate**: every term whose root is neither `Out` nor `Par` is stuck. -/
theorem stuck_of_not_mayFire {term : Pattern} (cannot : mayFire term = false) :
    Tiny.sat Env.closed (.necessarily .any .bot) term :=
  fireHom.sat_of_hom_universal (.necessarily .any .bot) rfl (sourceEnv := Env.closed) (targetEnv := Env.closed)
    (fun index => index.elim0) term
    fun next step => by
      change mayFire term = true at step
      rw [cannot] at step
      cases step

/-- An abstraction is stuck, whatever its body. -/
theorem abs_stuck (body : Pattern) : Tiny.sat Env.closed (.necessarily .any .bot) (.apply "Abs" [.lambda none body]) :=
  stuck_of_not_mayFire rfl

/-- `Out Nil` is not stuck, and the abstraction does not claim it is. -/
theorem out_not_stuck : ¬ Tiny.sat Env.closed (.necessarily .any .bot) (out nilTerm) :=
  fun stuck => stuck nilTerm (step_of_listed (fuel := 1) (by decide) (by decide) (by decide +kernel))

/-! ## Separation -/

def atomA : Pattern := .apply "A" []
def atomB : Pattern := .apply "B" []
def soup (elements : List Pattern) : Pattern := .collection .hashBag elements none

def soupRule : GrammarRule :=
  { label := "Soup", category := "Proc", params := [.simple "ps" (.collection .hashBag proc)], syntaxPattern := [] }

def soupLanguage : LanguageDef :=
  { name := "Soup", types := ["Proc"],
    terms := [{ label := "A", category := "Proc", params := [], syntaxPattern := [] },
      { label := "B", category := "Proc", params := [], syntaxPattern := [] }, soupRule],
    equations := [], rewrites := [] }

abbrev Soup : NativeStructure Pattern := referenceStructure RelationEnv.empty soupLanguage

/-- `{A}` and `{B}`. -/
def oneEach (first second : Pattern) : Formula 0 :=
  .split .hashBag (.single .hashBag (.is first)) (.single .hashBag (.is second))

/-- **`{A, B}` splits into `{A}` and `{B}`.** -/
theorem soup_splits : Soup.sat Env.closed (oneEach atomA atomB) (soup [atomA, atomB]) :=
  ⟨soup [atomA], soup [atomB], ⟨by decide, [atomA], [atomB], Relation.EqvGen.refl _, rfl, rfl⟩,
    ⟨atomA, ⟨by decide, Relation.EqvGen.refl _⟩, ⟨by decide, Relation.EqvGen.refl _⟩⟩,
    ⟨atomB, ⟨by decide, Relation.EqvGen.refl _⟩, ⟨by decide, Relation.EqvGen.refl _⟩⟩⟩

/-- **By the bag law, `{A, B}` also splits into `{B}` and `{A}`.** -/
theorem soup_splits_commuted : Soup.sat Env.closed (oneEach atomB atomA) (soup [atomA, atomB]) := by
  have permuted : ObjectEquivalent RelationEnv.empty soupLanguage .syntax (soup [atomA, atomB]) (soup [atomB, atomA]) :=
    Relation.EqvGen.rel _ _ ⟨by decide, by decide, EquationStep.inContext .hole (Or.inr
      (DerivedInstance.bagPerm_of_sorted (category := soupRule.category)
        ⟨FreeTypeContext.empty, [], (checkOpenPatternWellSorted_sound (by decide +kernel)).1⟩
        (List.Perm.swap atomB atomA [])))⟩
  exact ⟨soup [atomB], soup [atomA], ⟨by decide, [atomB], [atomA], permuted, rfl, rfl⟩,
    ⟨atomB, ⟨by decide, Relation.EqvGen.refl _⟩, ⟨by decide, Relation.EqvGen.refl _⟩⟩,
    ⟨atomA, ⟨by decide, Relation.EqvGen.refl _⟩, ⟨by decide, Relation.EqvGen.refl _⟩⟩⟩

mutual
/-- The number of `A`s in a term. -/
def countA : Pattern → ℕ
  | .apply label arguments => (if label = "A" then 1 else 0) + countAList arguments
  | .lambda _ inner => countA inner
  | .multiLambda _ _ inner => countA inner
  | .subst inner replacement => countA inner + countA replacement
  | .collection _ elements _ => countAList elements
  | .bvar _ | .fvar _ => 0

def countAList : List Pattern → ℕ
  | [] => 0
  | pattern :: patterns => countA pattern + countAList patterns
end

theorem countAList_append (first second : List Pattern) :
    countAList (first ++ second) = countAList first + countAList second := by
  induction first with
  | nil => simp [countAList]
  | cons pattern patterns previous => simp only [List.cons_append, countAList, previous]; omega

theorem countAList_perm {first second : List Pattern} (perm : first.Perm second) :
    countAList first = countAList second := by
  induction perm with
  | nil => rfl
  | cons _ _ previous => simp only [countAList, previous]
  | swap => simp only [countAList]; omega
  | trans _ _ first second => exact first.trans second

theorem countA_fill (context : OneHoleContext) {first second : Pattern} (same : countA first = countA second) :
    countA (context.fill first) = countA (context.fill second) := by
  induction context with
  | hole => exact same
  | apply _ before inner after previous =>
    simp only [OneHoleContext.fill, countA, countAList_append, countAList, previous]
  | lambda _ inner previous => simp only [OneHoleContext.fill, countA, previous]
  | multiLambda _ _ inner previous => simp only [OneHoleContext.fill, countA, previous]
  | substBody inner _ previous => simp only [OneHoleContext.fill, countA, previous]
  | substReplacement _ inner previous => simp only [OneHoleContext.fill, countA, previous]
  | collection _ before inner after _ previous =>
    simp only [OneHoleContext.fill, countA, countAList_append, countAList, previous]

/-- **The equations of `soup` keep the number of `A`s**: its only laws permute bags. -/
theorem countA_equivalent {first second : Pattern}
    (equivalent : Equivalent RelationEnv.empty soupLanguage first second) : countA first = countA second := by
  induction equivalent with
  | rel _ _ step =>
    cases step with
    | inContext context generator =>
      refine countA_fill context ?_
      rcases generator with authored | derived
      · cases authored with
        | forward member _ _ _ => simp [soupLanguage] at member
        | reverse member _ _ _ => simp [soupLanguage] at member
        | declared member _ _ => simp [soupLanguage] at member
        | premised member _ _ _ => simp [soupLanguage] at member
      · cases derived with
        | bagPerm _ _ perm => exact countAList_perm perm
        | setPerm declaration kindTyped _ =>
          exact absurd (usesCollection_eq_true_of_collectionTypedAt declaration kindTyped) (by decide)
        | setDedup declaration kindTyped =>
          exact absurd (usesCollection_eq_true_of_collectionTypedAt declaration kindTyped) (by decide)
        | flatten algebraRule _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false (by decide) algebraRule).elim
        | singleton algebraRule _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false (by decide) algebraRule).elim
        | unitElim algebraRule _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false (by decide) algebraRule).elim
        | emptyUnit algebraRule _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false (by decide) algebraRule).elim
  | refl => rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **`{A, B}` does not split into two parts each holding `A`.** -/
theorem soup_no_double : ¬ Soup.sat Env.closed (oneEach atomA atomA) (soup [atomA, atomB]) := by
  rintro ⟨first, second, ⟨-, left, right, isSplit, rfl, rfl⟩, ⟨leftMember, ⟨-, leftSingle⟩, ⟨-, leftNamed⟩⟩,
    ⟨rightMember, ⟨-, rightSingle⟩, ⟨-, rightNamed⟩⟩⟩
  have total := countA_equivalent isSplit.equivalent
  have leftCount := countA_equivalent leftSingle.equivalent
  have rightCount := countA_equivalent rightSingle.equivalent
  have leftAtom := countA_equivalent leftNamed.equivalent
  have rightAtom := countA_equivalent rightNamed.equivalent
  have soupCount : countA (soup [atomA, atomB]) = 1 := by decide
  have atomCount : countA atomA = 1 := by decide
  simp only [countA, countAList, countAList_append] at total leftCount rightCount
  omega

/-! ## Φ(L) -/

theorem par_not_bare : ¬ UsesBareCollection parRule := by
  rintro ⟨_, _, _, shape⟩
  simp [parRule, GrammarRule.bareParams] at shape

theorem generated_site : GeneratedBy tiny (.possibly (.under 1 (.rule 0)) .top : Formula 0) := by
  simp [GeneratedBy, LabelOf, tiny]

theorem not_generated_rule : ¬ GeneratedBy tiny (.possibly (.rule 2) .top : Formula 0) := by
  simp [GeneratedBy, LabelOf, tiny]

theorem generated_par : GeneratedBy tiny (.built "Par" (.cons .top (.cons .top .nil)) : Formula 0) :=
  ⟨⟨parRule, by simp [tiny, grammar], rfl, rfl, par_not_bare⟩, trivial, trivial, trivial⟩

theorem not_generated_bag : ¬ GeneratedBy tiny (.empty .hashBag : Formula 0) := by
  simp only [GeneratedBy]
  decide

theorem generated_split : GeneratedBy soupLanguage (oneEach atomA atomB) :=
  ⟨by decide, ⟨by decide, proc, checkOpenPatternWellSorted_sound (by decide +kernel)⟩,
    ⟨by decide, proc, checkOpenPatternWellSorted_sound (by decide +kernel)⟩⟩

/-- **A bag carrier is not a constructor**: its terms are bare collections. -/
theorem soup_carrier_not_constructor : ¬ GeneratedBy soupLanguage (.built "Soup" (.cons .top .nil) : Formula 0) := by
  rintro ⟨⟨rule, member, named, -, notBare⟩, -⟩
  simp only [soupLanguage, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simp at named
  · simp at named
  · exact notBare ⟨"ps", .hashBag, proc, rfl⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls
