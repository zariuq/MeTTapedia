import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Semantics
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.OSLF.MeTTaIL.ReferenceStepDisciplines
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CarrierTyping

/-!
# The native structure of a language

A language's terms carry its generated logic (`referenceStructure`). Its elements are the language's
object terms: patterns without a pending explicit substitution or an open collection tail, which occur
only in rule schemas (`IsObject`). Its states are the closed object terms (`IsState`). Terms are read
modulo the equations, through object terms (`ObjectEquivalent`), in a reading of the equations
(`EquationReading`):
- **the syntax theory** (`EquationReading.syntax`, the default): every instance of an authored equation, whatever
  it binds its variables to;
- **a binding discipline** (`.instances`): the instances whose bindings the discipline admits
  (`ReferenceStep.EquationDiscipline`);
- **the typed reading** (`.typed`): the judgment `⊢ s ≡ t : S` between closed object terms of one sort, as the
  equations of a sorted presentation relate terms of a sort, that keep the scope policy of a reflection profile (a
  quotation seals what it quotes); with the empty profile, typing alone. It reads each instance at the sort and binder
  context of the place it rewrites (`ReferenceStep.TypedEquivalent`).

Each reading is contained in the syntax theory (`ObjectEquivalent.toSyntax`), and in an equation-free language they
are all equality and give one structure (`referenceStructure_eq_of_isEquationFree`).
- A step is a reference step between states, taken by an equivalent closed redex. A rule label admits
  the steps whose witness fires that rule. A site label `under i l` admits the steps of rule `i` that
  have a premise step admitted by `l`. A chain of site labels therefore follows a step through the
  contexts that congruence rules provide, down to the rule that fires.
- An object term is built by a constructor, split, empty, a singleton, an abstraction or a bound
  variable when some equivalent term has that shape. Bodies of abstractions are open object terms, so
  they have shapes but no steps.
- An object term has a type when some equivalent term is a closed object term of that type, and a term
  names the object terms equivalent to it. Two terms are the same element when they are equivalent.
- A body is applied to an argument by instantiating its outermost bound variable.
- An object term holds a declared relation when a query of the relation at some equivalent term succeeds: the
  relation's tuples there, builtin or provided, include that term.

Types are those of closed terms, so the quantifiers `someOf` and `everyOf` range over the closed terms
of a type. An abstraction's body is open, so its type is read through the hom formers. The past
modalities range over states only: a schema pattern is not a predecessor.

Every relation is read through the equivalence, so native types do not depend on the representative
chosen (`Invariance`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted (OpenPatternWellSorted FreeTypeContext isObjectPattern)

/-- The rule a step witness fires. -/
def ruleOf : Witness → Option ℕ
  | .rule index _ _ => some index
  | _ => none

mutual
/-- The step witnesses a premise witness contains, including those for each element of a quantified
premise. -/
def premiseSteps : Witness → List Witness
  | .premiseStep step _ _ _ => [step]
  | .forAll bodies => premiseStepsList bodies
  | _ => []

/-- The step witnesses among a list of premise witnesses. -/
def premiseStepsList : List Witness → List Witness
  | [] => []
  | witness :: witnesses => premiseSteps witness ++ premiseStepsList witnesses
end

/-- Whether a step label admits a step with this witness. -/
def StepLabel.admits : StepLabel → Witness → Bool
  | .any, _ => true
  | .rule index, witness => ruleOf witness == some index
  | .under index label, .rule index' _ premises =>
    index' == index && (premiseStepsList premises).any label.admits
  | .under _ _, _ => false
  | .context _ _ _, _ => false

/-! ## Object terms and states -/

/-- **An object term**: no pending explicit substitution and no open collection tail. -/
abbrev IsObject (pattern : Pattern) : Prop := isObjectPattern pattern = true

/-- **A state**: a closed object term. -/
abbrev IsState (pattern : Pattern) : Prop := pattern.isWellScopedAt 0 = true ∧ IsObject pattern

/-! ## Readings of the equations -/

open Mettapedia.OSLF.MeTTaIL.ReferenceStep (EquationDiscipline DisciplinedStep TypedStep)
open Mettapedia.OSLF.MeTTaIL.Reflection (ReflectionProfile)

/-- **The types at which the typed judgment identifies closed terms.** -/
inductive JudgmentTypes where
  /-- The sorts: the base types. -/
  | sorts
  /-- The element types: the sorts and the types of the constructors' parameters, binder types among them. -/
  | elements
  /-- Every type. -/
  | all
  deriving DecidableEq, Repr

/-- Whether a language's judgment types include a type. -/
def JudgmentTypes.Admits (language : LanguageDef) : JudgmentTypes → TypeExpr → Prop
  | .sorts, type => ∃ sort, type = .base sort
  | .elements, type => (∃ sort, type = .base sort) ∨
      ∃ rule ∈ language.terms, ∃ param ∈ rule.params,
        Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? param = some type
  | .all, _ => True

/-- **How the generated logic reads a language's equations.** -/
inductive EquationReading where
  /-- Through the instances a binding discipline admits; admitting every binding, the syntax theory. -/
  | instances (discipline : EquationDiscipline)
  /-- As the typed judgment `Γ ⊢ s ≡ t : T` between object terms of a judgment type that keep a reflection
  profile's scope policy, over the instances a discipline admits. The terms have no free bound variable; their free
  variables are names of one sort, when a sort is given (`names`), and they have none otherwise. -/
  | typed (discipline : EquationDiscipline) (profile : ReflectionProfile) (types : JudgmentTypes)
      (names : Option String)
  deriving DecidableEq, Repr

/-- The context of a typed reading's free names: every free variable has the sort, or there is none. -/
def EquationReading.nameContext : Option String → FreeTypeContext
  | none => FreeTypeContext.empty
  | some sort => fun _ => some (.base sort)

/-- **The syntax theory**: every instance of an authored equation, whatever it binds its variables to. -/
abbrev EquationReading.syntax : EquationReading := .instances .raw

/-- One equation step in a reading. -/
def readingStep (relEnv : RelationEnv) (language : LanguageDef) : EquationReading → Pattern → Pattern → Prop
  | .instances .raw => EquationStep relEnv language
  | .instances discipline => DisciplinedStep relEnv language discipline
  | .typed discipline profile types names => fun first second =>
    ∃ type, types.Admits language type ∧ TypedStep relEnv language discipline (EquationReading.nameContext names) []
      type (Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted.ReflectiveScopeSafeAt profile 0) first second

/-! ## Readings of the rules -/

open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (RuleInterpretation)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)

/-- **The equivalence of terms with one canonical form.** -/
def canonSetoid (canon : Pattern → Pattern) : Setoid Pattern where
  r first second := canon first = canon second
  iseqv := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩

/-- **The listed presentations of a term's class**: those listed for its canonical form that have that form. -/
def listedPresent (canon : Pattern → Pattern) (presentations : Pattern → List Pattern) (term : Pattern) :
    List Pattern :=
  (presentations (canon term)).filter fun shown => canon shown == canon term

theorem canon_eq_of_mem_listedPresent {canon : Pattern → Pattern} {presentations : Pattern → List Pattern}
    {term shown : Pattern} (listed : shown ∈ listedPresent canon presentations term) : canon shown = canon term := by
  simpa using (List.mem_filter.mp listed).2

/-- **How the generated logic reads a language's rules.** -/
inductive RuleReading where
  /-- Through the reference relation: witnessed derivations, which rule and context labels read. -/
  | reference
  /-- Through an interpretation of matching and instantiation, such as a reflection profile's. Its steps carry no
  witness, so only the plain modalities read them. -/
  | interpreted (interpretation : RuleInterpretation) (base : BasePremiseEvaluator)
  /-- Through the reference relation with every internal boundary read modulo canonical forms: a premise steps any
  presentation of its child, and its target and a relation's answers are matched at any presentations of their
  values (the equational internal boundary policy, with the equivalence of terms with one canonical form). Its steps
  are listed at the listed presentations of each child's class. -/
  | modulo (canon : Pattern → Pattern) (presentations : Pattern → List Pattern)
  /-- As `modulo`, its steps listed by a table given as evidence: the presentations it visits and its entries, each a
  presentation, a witness and a contractum, with whether the table was found complete. A listed entry is one the witness
  checker accepts; the table lists every step of a visited presentation, up to its rule and contractum, when every entry
  checks and a round over the table adds nothing. A premise's child may be of its term's own class, so a table is how
  such steps are listed. -/
  | moduloTabled (canon : Pattern → Pattern) (presentations : Pattern → List Pattern) (todo : List Pattern)
      (table : List (Pattern × Witness × Pattern)) (complete : Bool)

/-- Whether a reading of the rules is the reference relation. -/
def RuleReading.isReference : RuleReading → Bool
  | .reference => true
  | .interpreted _ _ => false
  | .modulo _ _ => false
  | .moduloTabled _ _ _ _ _ => false

theorem RuleReading.eq_reference {rules : RuleReading} (reference : rules.isReference = true) :
    rules = .reference := by
  cases rules with
  | reference => rfl
  | interpreted => cases reference
  | modulo => cases reference
  | moduloTabled => cases reference

/-- **One rule step in a reading of the rules**: a valid witness of the reference relation, or a step of the
interpretation with the witness of no rule. -/
def RuleValid (relEnv : RelationEnv) (language : LanguageDef) : RuleReading → Pattern → Witness → Pattern → Prop
  | .reference => StepValid relEnv language
  | .interpreted interpretation base => fun source witness target =>
    witness = .base [] ∧ Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step interpretation base language source target
  | .modulo canon _ => fun source witness target =>
    StepValid relEnv language source witness target (.equational (canonSetoid canon))
  | .moduloTabled canon _ _ _ _ => fun source witness target =>
    StepValid relEnv language source witness target (.equational (canonSetoid canon))

/-- **A reading of a language**: how its equations are read and how its rules fire. -/
structure LanguageReading where
  equations : EquationReading := .syntax
  rules : RuleReading := .reference

/-- **The syntax theory with the reference relation**: the default reading. -/
abbrev LanguageReading.syntax : LanguageReading := {}

/-- One equation step between object terms, in a reading. -/
def ObjectStep (relEnv : RelationEnv) (language : LanguageDef) (reading : LanguageReading) (first second : Pattern) :
    Prop :=
  IsObject first ∧ IsObject second ∧ readingStep relEnv language reading.equations first second

/-- **Equivalence of object terms modulo the equations**, in a reading, through object terms. -/
def ObjectEquivalent (relEnv : RelationEnv) (language : LanguageDef) (reading : LanguageReading) :
    Pattern → Pattern → Prop :=
  Relation.EqvGen (ObjectStep relEnv language reading)

variable {relEnv : RelationEnv} {language : LanguageDef} {reading : LanguageReading}

/-- A step in a reading is a step of a discipline: of the one it reads instances through. -/
theorem readingStep_disciplined {equations : EquationReading} {first second : Pattern}
    (step : readingStep relEnv language equations first second) :
    ∃ discipline, DisciplinedStep relEnv language discipline first second := by
  match equations, step with
  | .instances .raw, step => exact ⟨.raw, Mettapedia.OSLF.MeTTaIL.ReferenceStep.disciplinedStep_raw_iff.mpr step⟩
  | .instances .sorted, step => exact ⟨.sorted, step⟩
  | .instances .fresh, step => exact ⟨.fresh, step⟩
  | .instances .closed, step => exact ⟨.closed, step⟩
  | .typed discipline _ _ _, ⟨_, _, step⟩ => exact ⟨discipline, step.2.2⟩

/-- The binding discipline a reading of the equations reads instances through. -/
def EquationReading.discipline : EquationReading → EquationDiscipline
  | .instances discipline => discipline
  | .typed discipline _ _ _ => discipline

/-- **A step in a reading is a step of its discipline.** -/
theorem readingStep_discipline {equations : EquationReading} {first second : Pattern}
    (step : readingStep relEnv language equations first second) :
    DisciplinedStep relEnv language equations.discipline first second := by
  match equations, step with
  | .instances .raw, step => exact Mettapedia.OSLF.MeTTaIL.ReferenceStep.disciplinedStep_raw_iff.mpr step
  | .instances .sorted, step => exact step
  | .instances .fresh, step => exact step
  | .instances .closed, step => exact step
  | .typed _ _ _ _, ⟨_, _, step⟩ => exact step.2.2

/-- **A step in any reading is a step of the syntax theory.** -/
theorem readingStep_toSyntax {equations : EquationReading} {first second : Pattern}
    (step : readingStep relEnv language equations first second) :
    EquationStep relEnv language first second := by
  obtain ⟨discipline, step⟩ := readingStep_disciplined step
  exact Mettapedia.OSLF.MeTTaIL.ReferenceStep.disciplinedStep_raw_iff.mp
    (step.mono (loose := .raw) (by cases discipline <;> decide))

theorem ObjectEquivalent.equivalence : Equivalence (ObjectEquivalent relEnv language reading) :=
  Relation.EqvGen.is_equivalence _

/-- Equivalent object terms are equal or both object terms. -/
theorem ObjectEquivalent.objects {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language reading first second) :
    first = second ∨ (IsObject first ∧ IsObject second) := by
  induction equivalent with
  | rel _ _ step => exact Or.inr ⟨step.1, step.2.1⟩
  | refl => exact Or.inl rfl
  | symm _ _ _ previous =>
    rcases previous with same | ⟨first, second⟩
    · exact Or.inl same.symm
    · exact Or.inr ⟨second, first⟩
  | trans _ _ _ _ _ first second =>
    rcases first with rfl | ⟨firstObject, middleObject⟩
    · exact second
    · rcases second with rfl | ⟨-, secondObject⟩
      · exact Or.inr ⟨firstObject, middleObject⟩
      · exact Or.inr ⟨firstObject, secondObject⟩

/-- An object term is equivalent only to object terms. -/
theorem ObjectEquivalent.object_right {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language reading first second) (object : IsObject first) :
    IsObject second := by
  rcases equivalent.objects with rfl | ⟨-, secondObject⟩
  · exact object
  · exact secondObject

/-- **Every reading is contained in the syntax theory.** -/
theorem ObjectEquivalent.toSyntax {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language reading first second) :
    ObjectEquivalent relEnv language .syntax first second :=
  Relation.EqvGen.mono (fun _ _ step => ⟨step.1, step.2.1, readingStep_toSyntax step.2.2⟩) _ _ equivalent

/-- Equivalence through object terms is equivalence. -/
theorem ObjectEquivalent.equivalent {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language reading first second) : Equivalent relEnv language first second :=
  Relation.EqvGen.mono (fun _ _ step => readingStep_toSyntax step.2.2) _ _ equivalent

/-- **In an equation-free language, equivalence of object terms is equality**, in every reading. -/
theorem objectEquivalent_iff_eq_of_isEquationFree (free : language.isEquationFree = true) {first second : Pattern} :
    ObjectEquivalent relEnv language reading first second ↔ first = second :=
  ⟨fun equivalent => (equivalent_iff_eq_of_isEquationFree free).mp equivalent.equivalent,
    fun same => same ▸ Relation.EqvGen.refl _⟩

/-- **The typed reading is contained in the reading of its discipline's instances.** -/
theorem ObjectEquivalent.typed_instances {discipline : EquationDiscipline} {profile : ReflectionProfile}
    {types : JudgmentTypes} {names : Option String} {rules : RuleReading} {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language ⟨.typed discipline profile types names, rules⟩ first second) :
    ObjectEquivalent relEnv language ⟨.instances discipline, rules⟩ first second := by
  refine Relation.EqvGen.mono (fun _ _ step => ⟨step.1, step.2.1, ?_⟩) _ _ equivalent
  obtain ⟨_, _, typedStep⟩ := step.2.2
  cases discipline with
  | raw => exact Mettapedia.OSLF.MeTTaIL.ReferenceStep.disciplinedStep_raw_iff.mp typedStep.2.2
  | sorted => exact typedStep.2.2
  | fresh => exact typedStep.2.2
  | closed => exact typedStep.2.2

/-- **A term placed in a context**: the context's hole, a metavariable, instantiated by the term as a rule instantiates
its right side, scope-correctly: under binders the term's variables still point past them. A hole in a collection's
rest takes the term's elements. -/
def plug (hole : String) (context term : Pattern) : Pattern :=
  Mettapedia.OSLF.MeTTaIL.Match.applyBindingsScoped (.fvar hole) [(hole, term)] 0 context

variable (relEnv language)

/-- **Where a step with the label starts, from a term**: the term up to the equations, or, under a context label, some
presentation of the term placed in the context, a state, and from there inward. -/
def Placed (reading : LanguageReading) : StepLabel → Pattern → Pattern → Prop
  | .context hole context label, source, redex => ∃ presentation,
      ObjectEquivalent relEnv language reading source presentation ∧ IsState presentation ∧
        IsState (plug hole context presentation) ∧ Placed reading label (plug hole context presentation) redex
  | .any, source, redex => ObjectEquivalent relEnv language reading source redex
  | .rule _, source, redex => ObjectEquivalent relEnv language reading source redex
  | .under _ _, source, redex => ObjectEquivalent relEnv language reading source redex

variable {relEnv language} in
/-- **A label that is not a context starts its steps at the term**, up to the equations. -/
theorem placed_iff {reading : LanguageReading} {label : StepLabel} (own : label.isContext = false)
    {source redex : Pattern} :
    Placed relEnv language reading label source redex ↔ ObjectEquivalent relEnv language reading source redex := by
  cases label with
  | context => cases own
  | any => exact Iff.rfl
  | rule => exact Iff.rfl
  | under => exact Iff.rfl

/-- **A context label admits none of the term's own steps**: a label admitting a witness is not a context. -/
theorem StepLabel.isContext_of_admits {label : StepLabel} {witness : Witness} (admits : label.admits witness = true) :
    label.isContext = false := by
  cases label with
  | context => cases admits
  | any => rfl
  | rule => rfl
  | under => rfl

/-- A label admitting a witness is its own base. -/
theorem StepLabel.base_admits {label : StepLabel} {witness : Witness} (admits : label.admits witness = true) :
    label.base.admits witness = true := by
  rw [StepLabel.base_of_isContext (StepLabel.isContext_of_admits admits)]
  exact admits

/-- A label that is not a context admits what its base admits. -/
theorem StepLabel.admits_of_base {label : StepLabel} {witness : Witness} (own : label.isContext = false)
    (admits : label.base.admits witness = true) : label.admits witness = true := by
  rw [StepLabel.base_of_isContext own] at admits
  exact admits

variable {relEnv language} in
/-- A label admitting a witness starts its steps at the term. -/
theorem placed_self {reading : LanguageReading} {label : StepLabel} {witness : Witness}
    (admits : label.admits witness = true) (term : Pattern) : Placed relEnv language reading label term term :=
  (placed_iff (StepLabel.isContext_of_admits admits)).mpr (Relation.EqvGen.refl _)

variable {relEnv language} in
/-- **Where a step starts is read up to the equations.** -/
theorem Placed.of_equivalent {reading : LanguageReading} {label : StepLabel} {first second redex : Pattern}
    (equivalent : ObjectEquivalent relEnv language reading second first)
    (placed : Placed relEnv language reading label first redex) : Placed relEnv language reading label second redex := by
  cases label with
  | context hole context label =>
    obtain ⟨presentation, presents, state, placedState, inner⟩ := placed
    exact ⟨presentation, Relation.EqvGen.trans _ _ _ equivalent presents, state, placedState, inner⟩
  | any => exact Relation.EqvGen.trans _ _ _ equivalent placed
  | rule => exact Relation.EqvGen.trans _ _ _ equivalent placed
  | under => exact Relation.EqvGen.trans _ _ _ equivalent placed

/-- **The native structure of a language**: its object terms modulo its equations, with its reference
steps between states. -/
def referenceStructure (reading : LanguageReading := .syntax) : NativeStructure Pattern where
  step source label target := IsState source ∧ IsState target ∧ ∃ redex contractum witness,
    Placed relEnv language reading label source redex ∧ IsState redex ∧
      RuleValid relEnv language reading.rules redex witness contractum ∧
      IsState contractum ∧ ObjectEquivalent relEnv language reading contractum target ∧
        label.base.admits witness = true
  built element constructor parts := IsObject element ∧ ObjectEquivalent relEnv language reading element (.apply constructor parts)
  split element kind first second := IsObject element ∧ ∃ left right,
    ObjectEquivalent relEnv language reading element (.collection kind (left ++ right) none) ∧
      first = .collection kind left none ∧ second = .collection kind right none
  empty element kind := IsObject element ∧ ObjectEquivalent relEnv language reading element (.collection kind [] none)
  single element kind member := IsObject element ∧
    ObjectEquivalent relEnv language reading element (.collection kind [member] none)
  body element inner := IsObject element ∧ ∃ name, ObjectEquivalent relEnv language reading element (.lambda name inner)
  multiBody element arity inner := IsObject element ∧
    ∃ names, ObjectEquivalent relEnv language reading element (.multiLambda arity names inner)
  bound element index := IsObject element ∧ ObjectEquivalent relEnv language reading element (.bvar index)
  typed element type := IsObject element ∧ ∃ representative, ObjectEquivalent relEnv language reading element representative ∧
    CarrierTyped language type representative
  named element term := IsObject element ∧ ObjectEquivalent relEnv language reading element term
  same first second := ObjectEquivalent relEnv language reading first second
  apply inner value := Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar value inner
  inRelation element relation := IsObject element ∧ ∃ representative, ObjectEquivalent relEnv language reading element representative ∧
    [representative] ∈ Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language relation [representative] ++
      relEnv.tuples relation [representative]

/-! ## Readings that agree -/

variable {relEnv language} in
/-- Readings with the same equations have the same equivalence of object terms. -/
theorem objectEquivalent_congr {first second : LanguageReading} (equations : first.equations = second.equations)
    (source target : Pattern) :
    ObjectEquivalent relEnv language first source target = ObjectEquivalent relEnv language second source target := by
  have steps : ObjectStep relEnv language first = ObjectStep relEnv language second := by
    funext before after
    simp only [ObjectStep, equations]
  simp only [ObjectEquivalent, steps]

variable {relEnv language} in
theorem placed_congr {first second : LanguageReading} (equations : first.equations = second.equations) :
    ∀ (label : StepLabel) (source redex : Pattern),
      Placed relEnv language first label source redex = Placed relEnv language second label source redex
  | .context hole context label, source, redex => by
    simp only [Placed, objectEquivalent_congr equations, placed_congr equations label]
  | .any, source, redex => by simp only [Placed, objectEquivalent_congr equations]
  | .rule _, source, redex => by simp only [Placed, objectEquivalent_congr equations]
  | .under _ _, source, redex => by simp only [Placed, objectEquivalent_congr equations]

variable {relEnv language} in
/-- **Readings with the same equations whose rules step alike have one reference structure.** -/
theorem referenceStructure_congr {first second : LanguageReading} (equations : first.equations = second.equations)
    (rules : ∀ source witness target, RuleValid relEnv language first.rules source witness target ↔
      RuleValid relEnv language second.rules source witness target) :
    referenceStructure relEnv language first = referenceStructure relEnv language second := by
  have valid : ∀ source witness target, RuleValid relEnv language first.rules source witness target =
      RuleValid relEnv language second.rules source witness target := fun source witness target =>
    propext (rules source witness target)
  unfold referenceStructure
  simp only [objectEquivalent_congr equations, placed_congr equations, valid]

/-- **Whether a query of a relation at a term succeeds**: the relation's tuples there, builtin or provided, include
the term. -/
def relationHolds (relation : String) (term : Pattern) : Bool :=
  decide ([term] ∈ Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language relation [term] ++
    relEnv.tuples relation [term])

variable {relEnv language}

theorem inRelation_of_relationHolds {relation : String} {term : Pattern} (object : IsObject term)
    (holds : relationHolds relEnv language relation term = true) :
    (referenceStructure relEnv language reading).inRelation term relation :=
  ⟨object, term, Relation.EqvGen.refl _, of_decide_eq_true holds⟩

/-- The builtin relations are not unary. -/
theorem builtinRelationTuples_single (language : LanguageDef) (relation : String) (term : Pattern) :
    Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language relation [term] = [] := by
  unfold Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples
  split <;> simp_all

/-- **Whether a query of a relation at a term succeeds** is whether the provided tuples there include the term. -/
theorem relationHolds_iff (relEnv : RelationEnv) (language : LanguageDef) (relation : String) (term : Pattern) :
    relationHolds relEnv language relation term = true ↔ [term] ∈ relEnv.tuples relation [term] := by
  simp [relationHolds, builtinRelationTuples_single]

/-- **Without provided relations no term is in a relation**: the builtin relations are not unary. -/
theorem not_inRelation_empty {language : LanguageDef} {term : Pattern} {relation : String} :
    ¬ (referenceStructure RelationEnv.empty language reading).inRelation term relation := by
  rintro ⟨-, representative, -, member⟩
  simp [builtinRelationTuples_single, RelationEnv.empty] at member

/-- **In an equation-free language a term is in a relation exactly when it is an object and the query at it
succeeds.** -/
theorem inRelation_iff_of_isEquationFree (free : language.isEquationFree = true) {relation : String}
    {term : Pattern} :
    (referenceStructure relEnv language reading).inRelation term relation ↔
      IsObject term ∧ relationHolds relEnv language relation term = true := by
  constructor
  · rintro ⟨object, representative, equivalent, member⟩
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    subst equivalent
    exact ⟨object, decide_eq_true member⟩
  · rintro ⟨object, holds⟩
    exact inRelation_of_relationHolds object holds

/-- **Readings with the same equivalence place terms alike**, in any languages. -/
theorem placed_eq_of_objectEquivalent_eq {otherEnv : RelationEnv} {other : LanguageDef}
    {first second : LanguageReading}
    (same : ObjectEquivalent relEnv language first = ObjectEquivalent otherEnv other second) :
    Placed relEnv language first = Placed otherEnv other second := by
  funext label
  induction label with
  | any => funext source redex; simp only [Placed, same]
  | rule _ => funext source redex; simp only [Placed, same]
  | under _ _ _ => funext source redex; simp only [Placed, same]
  | context hole context label inner => funext source redex; simp only [Placed, same, inner]

/-- **In an equation-free language every reading of the equations gives the one structure**, for a reading of the
rules. -/
theorem referenceStructure_eq_of_isEquationFree (free : language.isEquationFree = true) (reading : LanguageReading) :
    referenceStructure relEnv language reading = referenceStructure relEnv language { rules := reading.rules } := by
  have same : ObjectEquivalent relEnv language reading =
      ObjectEquivalent relEnv language { rules := reading.rules } := by
    funext first second
    exact propext ((objectEquivalent_iff_eq_of_isEquationFree free).trans
      (objectEquivalent_iff_eq_of_isEquationFree free).symm)
  unfold referenceStructure
  rw [placed_eq_of_objectEquivalent_eq same, same]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
