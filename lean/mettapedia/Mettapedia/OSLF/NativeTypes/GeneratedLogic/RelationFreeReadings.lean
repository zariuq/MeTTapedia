import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BoundedMorphism

/-!
# Readings without relations

A native structure answers the atoms of declared relations through relation tuples, which a relation environment
supplies. When a language's rules and equations have no premises, nothing else in its structure depends on the
environment.

- **Formulas without relations** (`Formula.relationFree`) mention no declared relation. They hold alike in two
  structures that differ only in their relations (`NativeStructure.sat_withRelations`).
- **Generated substructures** (`NativeStructure.GeneratedBy`): what some elements reach through their own steps, parts,
  members, bodies and applications, the least generated set containing them (`generatedBy_generated`). A generated set
  generates itself (`generatedBy_iff`), and what holds in the substructure it generates is what holds in its own
  (`sat_generatedBy_iff`).
- **Languages without premises read alike in every relation environment** (`referenceStructure_withRelations`): in two
  environments their structures differ only in their relations.
-/

set_option autoImplicit false

universe u

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-! ## Formulas without relations -/

namespace Formula

mutual
/-- **The formulas that mention no declared relation.** -/
def relationFree : {n : ℕ} → Formula n → Bool
  | _, .possibly _ formula | _, .necessarily _ formula | _, .sometimeBefore _ formula
  | _, .alwaysBefore _ formula | _, .atLeast _ _ _ formula | _, .allButFewer _ _ _ formula
  | _, .mu formula | _, .nu formula | _, .single _ formula | _, .everySingle _ formula | _, .body formula
  | _, .everyBody formula | _, .multiBody _ formula | _, .everyMultiBody _ formula | _, .someOf _ formula
  | _, .everyOf _ formula => relationFree formula
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right
  | _, .mapsAll left right | _, .mapsSome left right => relationFree left && relationFree right
  | _, .built _ arguments | _, .everyBuilt _ arguments => relationFreeList arguments
  | _, .inRelation _ | _, .notInRelation _ => false
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _ | _, .typed _
  | _, .untyped _ | _, .is _ | _, .isNot _ => true

/-- Every formula of the list mentions no declared relation. -/
def relationFreeList : {n : ℕ} → Formulas n → Bool
  | _, .nil => true
  | _, .cons formula formulas => relationFree formula && relationFreeList formulas
end

end Formula

namespace NativeStructure

variable {Carrier : Type u}

/-- **The structure with other relations**, everything else kept. -/
abbrev withRelations (S : NativeStructure Carrier) (relations : Carrier → String → Prop) : NativeStructure Carrier :=
  { S with inRelation := relations }

section WithRelations

variable (S : NativeStructure Carrier) (relations : Carrier → String → Prop)

mutual
/-- **A formula without relations holds alike**, whatever the relations. -/
theorem sat_withRelations : ∀ {n : ℕ} (formula : Formula n), formula.relationFree = true →
    ∀ (env : Env Carrier n) (element : Carrier),
      (S.withRelations relations).sat env formula element ↔ S.sat env formula element
  | _, .top, _, _, _ | _, .bot, _, _, _ | _, .var _, _, _, _ | _, .empty _, _, _, _ | _, .nonEmpty _, _, _, _
  | _, .bound _, _, _, _ | _, .notBound _, _, _, _ | _, .typed _, _, _, _ | _, .untyped _, _, _, _
  | _, .is _, _, _, _ | _, .isNot _, _, _, _ => by simp only [sat]
  | _, .inRelation _, free, _, _ | _, .notInRelation _, free, _, _ => by simp [Formula.relationFree] at free
  | _, .and left right, free, env, element | _, .or left right, free, env, element
  | _, .split _ left right, free, env, element | _, .everySplit _ left right, free, env, element
  | _, .mapsAll left right, free, env, element | _, .mapsSome left right, free, env, element => by
    simp only [Formula.relationFree, Bool.and_eq_true] at free
    simp only [sat, sat_withRelations left free.1, sat_withRelations right free.2]
  | _, .mu formula, free, env, element | _, .nu formula, free, env, element => by
    simp only [Formula.relationFree] at free
    simp only [sat, sat_withRelations formula free]
  | _, .possibly _ formula, free, env, element | _, .necessarily _ formula, free, env, element
  | _, .sometimeBefore _ formula, free, env, element | _, .alwaysBefore _ formula, free, env, element
  | _, .single _ formula, free, env, element | _, .everySingle _ formula, free, env, element
  | _, .body formula, free, env, element | _, .everyBody formula, free, env, element
  | _, .multiBody _ formula, free, env, element | _, .everyMultiBody _ formula, free, env, element
  | _, .someOf _ formula, free, env, element | _, .everyOf _ formula, free, env, element => by
    simp only [Formula.relationFree] at free
    simp only [sat, sat_withRelations formula free]
  | _, .atLeast _ _ _ formula, free, env, element | _, .allButFewer _ _ _ formula, free, env, element => by
    simp only [Formula.relationFree] at free
    simp only [sat, sat_withRelations formula free]
    exact Iff.rfl
  | _, .built _ arguments, free, env, element => by
    simp only [Formula.relationFree] at free
    simp only [sat, satAll_withRelations arguments free]
  | _, .everyBuilt _ arguments, free, env, element => by
    simp only [Formula.relationFree] at free
    simp only [sat, satSome_withRelations arguments free]

/-- Lists of formulas without relations hold alike everywhere, whatever the relations. -/
theorem satAll_withRelations : ∀ {n : ℕ} (formulas : Formulas n), Formula.relationFreeList formulas = true →
    ∀ {env : Env Carrier n} {parts : List Carrier},
      (S.withRelations relations).satAll env formulas parts ↔ S.satAll env formulas parts
  | _, .nil, _, _, [] | _, .nil, _, _, _ :: _ | _, .cons _ _, _, _, [] => by simp only [satAll]
  | _, .cons formula formulas, free, env, part :: parts => by
    simp only [Formula.relationFreeList, Bool.and_eq_true] at free
    simp only [satAll, sat_withRelations formula free.1, satAll_withRelations formulas free.2]

/-- Lists of formulas without relations hold alike somewhere, whatever the relations. -/
theorem satSome_withRelations : ∀ {n : ℕ} (formulas : Formulas n), Formula.relationFreeList formulas = true →
    ∀ {env : Env Carrier n} {parts : List Carrier},
      (S.withRelations relations).satSome env formulas parts ↔ S.satSome env formulas parts
  | _, .nil, _, _, [] | _, .nil, _, _, _ :: _ | _, .cons _ _, _, _, [] => by simp only [satSome]
  | _, .cons formula formulas, free, env, part :: parts => by
    simp only [Formula.relationFreeList, Bool.and_eq_true] at free
    simp only [satSome, sat_withRelations formula free.1, satSome_withRelations formulas free.2]
end

end WithRelations

/-! ## Generated substructures -/

section GeneratedBy

variable (S : NativeStructure Carrier) (P : Carrier → Prop)

/-- **The elements generated by some**: they, and what their elements reach through their own steps, parts, members and
bodies, and the applications of their bodies. -/
inductive GeneratedBy : Carrier → Prop
  | base {element : Carrier} : P element → GeneratedBy element
  | step {source : Carrier} {label : StepLabel} {target : Carrier} : label.isContext = false → GeneratedBy source →
      S.step source label target → GeneratedBy target
  | built {element : Carrier} {constructor : String} {parts : List Carrier} {part : Carrier} : GeneratedBy element →
      S.built element constructor parts → part ∈ parts → GeneratedBy part
  | splitLeft {element : Carrier} {kind : CollType} {first second : Carrier} : GeneratedBy element →
      S.split element kind first second → GeneratedBy first
  | splitRight {element : Carrier} {kind : CollType} {first second : Carrier} : GeneratedBy element →
      S.split element kind first second → GeneratedBy second
  | single {element : Carrier} {kind : CollType} {member : Carrier} : GeneratedBy element →
      S.single element kind member → GeneratedBy member
  | body {element inner : Carrier} : GeneratedBy element → S.body element inner → GeneratedBy inner
  | multiBody {element : Carrier} {arity : ℕ} {inner : Carrier} : GeneratedBy element →
      S.multiBody element arity inner → GeneratedBy inner
  | apply {inner argument : Carrier} : GeneratedBy inner → GeneratedBy argument → GeneratedBy (S.apply inner argument)

/-- **What some elements generate is generated.** -/
theorem generatedBy_generated : S.Generated (S.GeneratedBy P) where
  step own holds step := .step own holds step
  built holds built _ member := .built holds built member
  split holds split := ⟨.splitLeft holds split, .splitRight holds split⟩
  single holds single := .single holds single
  body holds body := .body holds body
  multiBody holds body := .multiBody holds body
  apply inner argument := .apply inner argument

variable {S P}

/-- **A generated set generates itself.** -/
theorem generatedBy_iff (generated : S.Generated P) {element : Carrier} : S.GeneratedBy P element ↔ P element := by
  constructor
  · intro holds
    induction holds with
    | base holds => exact holds
    | step own _ step ih => exact generated.step own ih step
    | built _ built member ih => exact generated.built ih built _ member
    | splitLeft _ split ih => exact (generated.split ih split).1
    | splitRight _ split ih => exact (generated.split ih split).2
    | single _ single ih => exact generated.single ih single
    | body _ body ih => exact generated.body ih body
    | multiBody _ body ih => exact generated.multiBody ih body
    | apply _ _ inner argument => exact generated.apply inner argument
  · exact .base

/-- **Two descriptions of one generated set give one substructure.** -/
theorem restrict_sat_congr {Q : Carrier → Prop} (same : ∀ element, P element ↔ Q element) (first : S.Generated P)
    (second : S.Generated Q) (formula : Formula 0) {element : Carrier} (inP : P element) (inQ : Q element) :
    (restrict first).sat Env.closed formula ⟨element, inP⟩ ↔ (restrict second).sat Env.closed formula ⟨element, inQ⟩ := by
  obtain rfl : P = Q := funext fun element => propext (same element)
  exact Iff.rfl

/-- **What holds in the substructure a generated set generates** is what holds in its own. -/
theorem sat_generatedBy_iff (generated : S.Generated P) (formula : Formula 0) {element : Carrier} :
    (∃ holds : S.GeneratedBy P element,
        (restrict (S.generatedBy_generated P)).sat Env.closed formula ⟨element, holds⟩) ↔
      ∃ holds : P element, (restrict generated).sat Env.closed formula ⟨element, holds⟩ := by
  have same : ∀ element, S.GeneratedBy P element ↔ P element := fun _ => generatedBy_iff generated
  constructor
  · rintro ⟨holds, satisfied⟩
    exact ⟨(same element).mp holds, (restrict_sat_congr same _ generated formula holds _).mp satisfied⟩
  · rintro ⟨holds, satisfied⟩
    exact ⟨(same element).mpr holds, (restrict_sat_congr same _ generated formula _ holds).mpr satisfied⟩

omit P in
/-- **Equal structures and equal generators generate the same substructure.** -/
theorem sat_generatedBy_congr {S' : NativeStructure Carrier} {P P' : Carrier → Prop} (sameStructure : S = S')
    (sameGenerators : P = P') (formula : Formula 0) (element : Carrier) (first : S.Generated (S.GeneratedBy P))
    (second : S'.Generated (S'.GeneratedBy P')) :
    (∃ holds : S.GeneratedBy P element, (restrict first).sat Env.closed formula ⟨element, holds⟩) ↔
      ∃ holds : S'.GeneratedBy P' element, (restrict second).sat Env.closed formula ⟨element, holds⟩ := by
  subst sameStructure sameGenerators
  exact Iff.rfl

/-- **A generated set stays generated with other relations.** -/
theorem Generated.withRelations (generated : S.Generated P) (relations : Carrier → String → Prop) :
    (S.withRelations relations).Generated P :=
  ⟨generated.step, generated.built, generated.split, generated.single, generated.body, generated.multiBody,
    generated.apply⟩

/-- **Restricting commutes with replacing the relations.** -/
theorem restrict_withRelations (generated : S.Generated P) (relations : Carrier → String → Prop) :
    restrict (generated.withRelations relations) =
      (restrict generated).withRelations fun element relation => relations element.1 relation :=
  rfl

end GeneratedBy

end NativeStructure

/-! ## Languages without premises in every relation environment -/

/-- **A language without premises**: neither its rules nor its equations have any. -/
structure PremiseFree (language : LanguageDef) : Prop where
  rules : ∀ rule ∈ language.rewrites, rule.premises = []
  equations : ∀ equation ∈ language.equations, equation.premises = []

section Environments

variable {relEnv relEnv' : RelationEnv} {language : LanguageDef}

theorem premisesValid_transfer {sites : Pattern} {initial final : Bindings} {premises : List Premise}
    {witnesses : List Witness} {policy : InternalBoundaryPolicy} (none : premises = [])
    (valid : PremisesValid relEnv language sites initial premises witnesses final policy) :
    PremisesValid relEnv' language sites initial premises witnesses final policy := by
  subst none
  cases valid with
  | nil => exact .nil _
  | equationalNil => exact .equationalNil _
  | presentedNil => exact .presentedNil _

theorem stepValid_transfer (free : PremiseFree language) {source target : Pattern} {witness : Witness}
    {policy : InternalBoundaryPolicy} (valid : StepValid relEnv language source witness target policy) :
    StepValid relEnv' language source witness target policy := by
  cases valid with
  | rule found matched premises =>
    exact .rule found matched (premisesValid_transfer (free.rules _ (List.mem_of_getElem? found)) premises)
  | equationalRule found matched premises =>
    exact .equationalRule found matched (premisesValid_transfer (free.rules _ (List.mem_of_getElem? found)) premises)
  | presentedRule found matched premises =>
    exact .presentedRule found matched (premisesValid_transfer (free.rules _ (List.mem_of_getElem? found)) premises)

theorem authoredEquation_transfer (free : PremiseFree language) {source target : Pattern}
    (step : AuthoredEquation relEnv language source target) : AuthoredEquation relEnv' language source target := by
  cases step with
  | forward member undeclared matched premises =>
    exact .forward member undeclared matched (premisesValid_transfer (free.equations _ member) premises)
  | reverse member undeclared matched premises =>
    exact .reverse member undeclared matched (premisesValid_transfer (free.equations _ member) premises)
  | declared member notRaw produced => exact .declared member notRaw produced
  | premised member _ premised _ => exact absurd (free.equations _ member) premised

theorem equationStep_transfer (free : PremiseFree language) {first second : Pattern}
    (step : EquationStep relEnv language first second) : EquationStep relEnv' language first second := by
  cases step with
  | inContext context generator => exact .inContext context (generator.imp (authoredEquation_transfer free) id)

variable {reading : LanguageReading}

theorem objectEquivalent_transfer (free : PremiseFree language) (syntactic : reading.equations = .syntax)
    {first second : Pattern} (equivalent : ObjectEquivalent relEnv language reading first second) :
    ObjectEquivalent relEnv' language reading first second := by
  refine Relation.EqvGen.mono (fun before after step => ?_) _ _ equivalent
  obtain ⟨beforeObject, afterObject, equation⟩ := step
  refine ⟨beforeObject, afterObject, ?_⟩
  rw [syntactic] at equation ⊢
  exact equationStep_transfer free equation

theorem placed_transfer (free : PremiseFree language) (syntactic : reading.equations = .syntax) :
    ∀ {label : StepLabel} {source redex : Pattern},
      Placed relEnv language reading label source redex → Placed relEnv' language reading label source redex
  | .context _ _ _, _, _, ⟨presentation, presents, state, plugged, placed⟩ =>
    ⟨presentation, objectEquivalent_transfer free syntactic presents, state, plugged, placed_transfer free syntactic placed⟩
  | .any, _, _, placed | .rule _, _, _, placed | .under _ _, _, _, placed => objectEquivalent_transfer free syntactic placed

theorem ruleValid_transfer (free : PremiseFree language) :
    ∀ {rules : RuleReading} {source : Pattern} {witness : Witness} {target : Pattern},
      RuleValid relEnv language rules source witness target → RuleValid relEnv' language rules source witness target
  | .reference, _, _, _, valid => stepValid_transfer free valid
  | .interpreted _ _, _, _, _, valid => valid
  | .modulo _ _, _, _, _, valid => stepValid_transfer free valid
  | .moduloTabled _ _ _ _ _, _, _, _, valid => stepValid_transfer free valid

variable (relEnv relEnv') in
/-- **A language without premises has one structure in every relation environment**, but for its relations, when
its equations are read as the syntax theory. -/
theorem referenceStructure_withRelations (free : PremiseFree language) (syntactic : reading.equations = .syntax) :
    ∃ relations, referenceStructure relEnv language reading =
      (referenceStructure relEnv' language reading).withRelations relations := by
  have equivalent : ObjectEquivalent relEnv language reading = ObjectEquivalent relEnv' language reading := by
    funext first second
    exact propext ⟨objectEquivalent_transfer free syntactic, objectEquivalent_transfer free syntactic⟩
  have placed : Placed relEnv language reading = Placed relEnv' language reading := by
    funext label source redex
    exact propext ⟨placed_transfer free syntactic, placed_transfer free syntactic⟩
  have valid : RuleValid relEnv language reading.rules = RuleValid relEnv' language reading.rules := by
    funext source witness target
    exact propext ⟨ruleValid_transfer free, ruleValid_transfer free⟩
  refine ⟨fun element relation => IsObject element ∧ ∃ representative,
    ObjectEquivalent relEnv' language reading element representative ∧
      [representative] ∈ Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language relation [representative] ++
        relEnv.tuples relation [representative], ?_⟩
  unfold referenceStructure
  rw [equivalent, placed, valid]

end Environments

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
