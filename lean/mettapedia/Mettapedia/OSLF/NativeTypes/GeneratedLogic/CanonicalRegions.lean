import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedExploration
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
import Mettapedia.OSLF.MeTTaIL.ReferenceStepTabled

/-!
# Closed regions modulo equations

A language with equations reads terms modulo them, so a closed region must list terms up to
equivalence. This works through canonical forms, for the behavioural formulas: steps forward, counting
forward, singletons, fixed points and the connectives (`Formula.behaviouralForward`).

- **Step morphisms** (`StepMorphism`): steps go forward and come back, identity is preserved and
  reflected, and terms name the same elements. Along one, every behavioural formula is preserved and
  reflected (`StepMorphism.sat_iff`).
- **The contract a language provides** (`Canonical`, `Coherent`):
  - canonical forms: each object term is equivalent to its canonical form, and equivalent terms have
    the same one;
  - coherence: a step from any term equivalent to a canonical state is matched, up to canonical form and
    with the same labels, by a step listed at that state.
- **The canonical structure** (`canonicalStructure`): canonical terms with the language's steps to them.
  Taking canonical forms is a step morphism from the language's structure onto it (`canonMorphism`).
- **A closed canonical region** (`canonicalRegion`): canonical terms without repetition, each state
  completely listed at its presentations, with the canonical forms of its listed successors in the
  region. Its inclusion is a
  step morphism into the canonical structure (`regionMorphism`), so the finite evaluator's verdict on it is
  exact (`canonical_check_iff`), and `decideCanonical` grows such a region from a term.
- **Presentations**: a region lists each state's steps at its presentations (`listedAt`), terms with the state as
  canonical form, and checks that they are. Presenting each state as itself (`List.singleton`) suffices when rules
  fire at canonical forms or their steps are simulated there. A set read modulo idempotence needs presentations
  with members written more than once, since a rule may consume one copy and leave another.
- **Sufficient conditions for coherence**: canonical forms that simulate steps
  (`coherent_of_simulation`), in particular rules that fire only on canonical terms
  (`coherent_of_canonical_redexes`).
- **Admitted labels**: a language read modulo its equations may derive one step by different rules in
  different presentations, so its rule and site labels need not survive the equations. Coherence on a set of
  admitted labels (`CoherentOn`) compares only those; coherence is the case of all labels, and coherence for
  plain steps (`CoherentPlain`) compares none. With it a closed canonical region decides every behavioural
  formula whose modalities are all admitted (`canonical_check_iff_on`, `decideCanonical_sound_on`). This rests
  on morphisms on admitted labels (`LabelMorphism`), of which step morphisms are the case of all labels.
- **Equation-free languages** satisfy the contract with the identity (`identity_canonical`,
  `identity_coherent`). A language with equations needs a canonicalizer for them and a proof of
  coherence for its rules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

universe u v

/-! ## The behavioural fragment -/

namespace Formula

/-- **Forward behavioural formulas**: steps and counting forward, singletons, fixed points and the
connectives. -/
def behaviouralForward : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ | _, .is _ | _, .isNot _ => true
  | _, .and left right | _, .or left right => behaviouralForward left && behaviouralForward right
  | _, .mu inner | _, .nu inner => behaviouralForward inner
  | _, .possibly label formula | _, .necessarily label formula => !label.isContext && behaviouralForward formula
  | _, .atLeast _ .forward label formula | _, .allButFewer _ .forward label formula =>
    !label.isContext && behaviouralForward formula
  | _, _ => false

end Formula

/-! ## Step morphisms -/

/-- **A label admitted among the term's own**: admissible, and not a context. -/
def StepLabel.admittedBy (admissible : StepLabel → Bool) (label : StepLabel) : Bool :=
  admissible label && !label.isContext

theorem StepLabel.admissible_of_admittedBy {admissible : StepLabel → Bool} {label : StepLabel}
    (admitted : label.admittedBy admissible = true) : admissible label = true := by
  simp only [StepLabel.admittedBy, Bool.and_eq_true] at admitted
  exact admitted.1

theorem StepLabel.isContext_of_admittedBy {admissible : StepLabel → Bool} {label : StepLabel}
    (admitted : label.admittedBy admissible = true) : label.isContext = false := by
  simp only [StepLabel.admittedBy, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at admitted
  exact admitted.2

namespace Formula

/-- **Behavioural formulas over admitted labels**: the forward behavioural fragment with every step label
admitted among the term's own. -/
def behaviouralIn (admissible : StepLabel → Bool) : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ | _, .is _ | _, .isNot _ => true
  | _, .and left right | _, .or left right => behaviouralIn admissible left && behaviouralIn admissible right
  | _, .mu inner | _, .nu inner => behaviouralIn admissible inner
  | _, .possibly label formula | _, .necessarily label formula =>
      label.admittedBy admissible && behaviouralIn admissible formula
  | _, .atLeast _ .forward label formula | _, .allButFewer _ .forward label formula =>
      label.admittedBy admissible && behaviouralIn admissible formula
  | _, _ => false

/-- With every label admitted, it is the forward behavioural fragment. -/
theorem behaviouralIn_all : ∀ {n : ℕ} (formula : Formula n),
    behaviouralIn (fun _ => true) formula = behaviouralForward formula
  | _, .top | _, .bot | _, .var _ | _, .is _ | _, .isNot _ => rfl
  | _, .and left right | _, .or left right => by
    simp only [behaviouralIn, behaviouralForward, behaviouralIn_all left, behaviouralIn_all right]
  | _, .mu inner | _, .nu inner => by simp only [behaviouralIn, behaviouralForward, behaviouralIn_all inner]
  | _, .possibly _ inner | _, .necessarily _ inner => by
    simp only [behaviouralIn, behaviouralForward, behaviouralIn_all inner, StepLabel.admittedBy, Bool.true_and]
  | _, .atLeast _ .forward _ inner | _, .allButFewer _ .forward _ inner => by
    simp only [behaviouralIn, behaviouralForward, behaviouralIn_all inner, StepLabel.admittedBy, Bool.true_and]
  | _, .atLeast _ .backward _ _ | _, .allButFewer _ .backward _ _ | _, .sometimeBefore _ _ | _, .alwaysBefore _ _
  | _, .built _ _ | _, .everyBuilt _ _ | _, .split _ _ _ | _, .everySplit _ _ _ | _, .empty _ | _, .nonEmpty _
  | _, .single _ _ | _, .everySingle _ _ | _, .body _ | _, .everyBody _ | _, .multiBody _ _
  | _, .everyMultiBody _ _ | _, .bound _ | _, .notBound _ | _, .typed _ | _, .untyped _ | _, .mapsAll _ _
  | _, .mapsSome _ _ | _, .someOf _ _ | _, .everyOf _ _ | _, .inRelation _ | _, .notInRelation _ => rfl

end Formula

/-- **A step morphism on admitted labels**: steps with an admitted label go forward and come back, identity
is preserved and reflected, and the terms name the same elements. -/
structure LabelMorphism {Source : Type u} {Target : Type v} (S : NativeStructure Source)
    (T : NativeStructure Target) (admissible : StepLabel → Bool) where
  map : Source → Target
  step : ∀ {source label target}, label.admittedBy admissible = true → S.step source label target →
    T.step (map source) label (map target)
  stepBack : ∀ {source label target'}, label.admittedBy admissible = true → T.step (map source) label target' →
    ∃ target, S.step source label target ∧ map target = target'
  sameIff : ∀ first second, S.same first second ↔ T.same (map first) (map second)
  namedIff : ∀ element term, S.named element term ↔ T.named (map element) term

namespace LabelMorphism

variable {Source : Type u} {Target : Type v} {S : NativeStructure Source} {T : NativeStructure Target}
  {admissible : StepLabel → Bool} (morphism : LabelMorphism S T admissible)

/-- Environments related by preimage. -/
def EnvPreimage {n : ℕ} (sourceEnv : Env Source n) (targetEnv : Env Target n) : Prop :=
  ∀ index element, element ∈ sourceEnv index ↔ morphism.map element ∈ targetEnv index

theorem EnvPreimage.extend {n : ℕ} {sourceEnv : Env Source n} {targetEnv : Env Target n}
    (related : morphism.EnvPreimage sourceEnv targetEnv) (set : Set Target) :
    morphism.EnvPreimage (sourceEnv.extend (morphism.map ⁻¹' set)) (targetEnv.extend set) := by
  intro index element
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Iff.rfl
  · exact related index element

theorem envPreimage_closed : morphism.EnvPreimage Env.closed Env.closed := fun index => index.elim0

/-- Steps from an image come from steps from the element, a list at a time. -/
theorem stepsBack {element : Source} {label : StepLabel} (admitted : label.admittedBy admissible = true) :
    ∀ {targets : List Target}, (∀ target ∈ targets, T.step (morphism.map element) label target) →
      ∃ sources : List Source, sources.map morphism.map = targets ∧ ∀ source ∈ sources, S.step element label source
  | [], _ => ⟨[], rfl, fun _ member => nomatch member⟩
  | target :: targets, steps => by
    obtain ⟨source, step, rfl⟩ := morphism.stepBack admitted (steps target List.mem_cons_self)
    obtain ⟨sources, same, rest⟩ := stepsBack admitted fun other member => steps other (List.mem_cons_of_mem _ member)
    refine ⟨source :: sources, by rw [List.map_cons, same], fun other member => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact step
    · exact rest other member

/-- **Counting steps with an admitted label is preserved and reflected.** -/
theorem atLeast_steps_iff {count : ℕ} {element : Source} {label : StepLabel}
    (admitted : label.admittedBy admissible = true)
    {holds : Source → Prop} {holds' : Target → Prop} (same : ∀ other, holds other ↔ holds' (morphism.map other)) :
    (S.AtLeast count fun other => S.step element label other ∧ holds other) ↔
      T.AtLeast count fun other => T.step (morphism.map element) label other ∧ holds' other := by
  constructor
  · rintro ⟨witnesses, length, distinct, all⟩
    refine ⟨witnesses.map morphism.map, by rw [List.length_map, length],
      List.pairwise_map.mpr (distinct.imp fun differs identified => differs ((morphism.sameIff _ _).mpr identified)), ?_⟩
    intro other member
    obtain ⟨origin, originMember, rfl⟩ := List.mem_map.mp member
    exact ⟨morphism.step admitted (all origin originMember).1, (same origin).mp (all origin originMember).2⟩
  · rintro ⟨witnesses, length, distinct, all⟩
    obtain ⟨sources, mapped, steps⟩ := morphism.stepsBack admitted fun other member => (all other member).1
    subst mapped
    refine ⟨sources, by rw [← length, List.length_map],
      (List.pairwise_map.mp distinct).imp fun differs identified => differs ((morphism.sameIff _ _).mp identified),
      fun other member => ⟨steps other member, (same other).mpr (all _ (List.mem_map_of_mem member)).2⟩⟩

/-- **Along a step morphism on admitted labels, a behavioural formula over those labels holds at an element
exactly when it holds at its image.** -/
theorem sat_iff : ∀ {n : ℕ} (formula : Formula n), formula.behaviouralIn admissible = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, morphism.EnvPreimage sourceEnv targetEnv →
      ∀ element, S.sat sourceEnv formula element ↔ T.sat targetEnv formula (morphism.map element)
  | _, .top, _, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _, _ => Iff.rfl
  | _, .and left right, behavioural, _, _, related, element => by
    simp only [Formula.behaviouralIn, Bool.and_eq_true] at behavioural
    exact and_congr (sat_iff left behavioural.1 related element) (sat_iff right behavioural.2 related element)
  | _, .or left right, behavioural, _, _, related, element => by
    simp only [Formula.behaviouralIn, Bool.and_eq_true] at behavioural
    exact or_congr (sat_iff left behavioural.1 related element) (sat_iff right behavioural.2 related element)
  | _, .var index, _, _, _, related, element => related index element
  | _, .mu inner, behavioural, sourceEnv, targetEnv, related, element => by
    constructor
    · intro holds closed closedHolds
      exact holds (morphism.map ⁻¹' closed) fun other otherHolds =>
        closedHolds _ ((sat_iff inner behavioural (related.extend morphism closed) other).mp otherHolds)
    · intro holds closed closedHolds
      let pushed : Set Target := {image | ∀ origin, morphism.map origin = image → origin ∈ closed}
      have inside : ∀ origin, morphism.map origin ∈ pushed → origin ∈ closed :=
        fun origin member => member origin rfl
      have pushedHolds := holds pushed fun image imageHolds origin originMaps => by
        subst originMaps
        exact closedHolds origin (S.sat_mono inner (sourceEnv.extend_sub fun other member => inside other member) origin
          ((sat_iff inner behavioural (related.extend morphism pushed) origin).mpr imageHolds))
      exact inside element pushedHolds
  | _, .nu inner, behavioural, sourceEnv, targetEnv, related, element => by
    constructor
    · rintro ⟨invariant, member, preserved⟩
      refine ⟨morphism.map '' invariant, ⟨element, member, rfl⟩, ?_⟩
      rintro _ ⟨other, otherMember, rfl⟩
      exact (sat_iff inner behavioural (related.extend morphism (morphism.map '' invariant)) other).mp
        (S.sat_mono inner (sourceEnv.extend_sub fun origin inside => Set.mem_image_of_mem morphism.map inside) other
          (preserved other otherMember))
    · rintro ⟨invariant, member, preserved⟩
      exact ⟨morphism.map ⁻¹' invariant, member, fun other otherMember =>
        (sat_iff inner behavioural (related.extend morphism invariant) other).mpr (preserved _ otherMember)⟩
  | _, .possibly _ formula, behavioural, _, _, related, element => by
    simp only [Formula.behaviouralIn, Bool.and_eq_true] at behavioural
    constructor
    · rintro ⟨next, step, holds⟩
      exact ⟨morphism.map next, morphism.step behavioural.1 step, (sat_iff formula behavioural.2 related next).mp holds⟩
    · rintro ⟨next', step', holds'⟩
      obtain ⟨next, step, rfl⟩ := morphism.stepBack behavioural.1 step'
      exact ⟨next, step, (sat_iff formula behavioural.2 related next).mpr holds'⟩
  | _, .necessarily _ formula, behavioural, _, _, related, element => by
    simp only [Formula.behaviouralIn, Bool.and_eq_true] at behavioural
    constructor
    · intro every next' step'
      obtain ⟨next, step, rfl⟩ := morphism.stepBack behavioural.1 step'
      exact (sat_iff formula behavioural.2 related next).mp (every next step)
    · intro every next step
      exact (sat_iff formula behavioural.2 related next).mpr (every _ (morphism.step behavioural.1 step))
  | _, .atLeast _ .forward _ formula, behavioural, _, _, related, _ => by
    simp only [Formula.behaviouralIn, Bool.and_eq_true] at behavioural
    exact morphism.atLeast_steps_iff behavioural.1 fun other => sat_iff formula behavioural.2 related other
  | _, .allButFewer _ .forward _ formula, behavioural, _, _, related, _ => by
    simp only [Formula.behaviouralIn, Bool.and_eq_true] at behavioural
    exact not_congr (morphism.atLeast_steps_iff behavioural.1 fun other =>
      not_congr (sat_iff formula behavioural.2 related other))
  | _, .is term, _, _, _, _, element => morphism.namedIff element term
  | _, .isNot term, _, _, _, _, element => not_congr (morphism.namedIff element term)
  | _, .sometimeBefore _ _, behavioural, _, _, _, _ | _, .alwaysBefore _ _, behavioural, _, _, _, _
  | _, .atLeast _ .backward _ _, behavioural, _, _, _, _ | _, .allButFewer _ .backward _ _, behavioural, _, _, _, _
  | _, .built _ _, behavioural, _, _, _, _ | _, .everyBuilt _ _, behavioural, _, _, _, _
  | _, .split _ _ _, behavioural, _, _, _, _ | _, .everySplit _ _ _, behavioural, _, _, _, _
  | _, .empty _, behavioural, _, _, _, _ | _, .nonEmpty _, behavioural, _, _, _, _
  | _, .single _ _, behavioural, _, _, _, _ | _, .everySingle _ _, behavioural, _, _, _, _
  | _, .body _, behavioural, _, _, _, _ | _, .everyBody _, behavioural, _, _, _, _
  | _, .multiBody _ _, behavioural, _, _, _, _ | _, .everyMultiBody _ _, behavioural, _, _, _, _
  | _, .bound _, behavioural, _, _, _, _ | _, .notBound _, behavioural, _, _, _, _
  | _, .typed _, behavioural, _, _, _, _ | _, .untyped _, behavioural, _, _, _, _
  | _, .mapsAll _ _, behavioural, _, _, _, _ | _, .mapsSome _ _, behavioural, _, _, _, _
  | _, .someOf _ _, behavioural, _, _, _, _ | _, .everyOf _ _, behavioural, _, _, _, _ => by
    simp [Formula.behaviouralIn] at behavioural

end LabelMorphism

/-- **A step morphism**: the elements' own steps go forward and come back, identity is preserved and reflected, and
the terms name the same elements. -/
structure StepMorphism {Source : Type u} {Target : Type v} (S : NativeStructure Source)
    (T : NativeStructure Target) where
  map : Source → Target
  step : ∀ {source label target}, label.isContext = false → S.step source label target →
    T.step (map source) label (map target)
  stepBack : ∀ {source label target'}, label.isContext = false → T.step (map source) label target' →
    ∃ target, S.step source label target ∧ map target = target'
  sameIff : ∀ first second, S.same first second ↔ T.same (map first) (map second)
  namedIff : ∀ element term, S.named element term ↔ T.named (map element) term

namespace StepMorphism

variable {Source : Type u} {Target : Type v} {S : NativeStructure Source} {T : NativeStructure Target}
  (morphism : StepMorphism S T)

/-- A step morphism is one on any set of admitted labels. -/
def toLabel (admissible : StepLabel → Bool) : LabelMorphism S T admissible :=
  ⟨morphism.map, fun admitted step => morphism.step (StepLabel.isContext_of_admittedBy admitted) step,
    fun admitted step => morphism.stepBack (StepLabel.isContext_of_admittedBy admitted) step, morphism.sameIff,
    morphism.namedIff⟩

/-- Environments related by preimage. -/
def EnvPreimage {n : ℕ} (sourceEnv : Env Source n) (targetEnv : Env Target n) : Prop :=
  ∀ index element, element ∈ sourceEnv index ↔ morphism.map element ∈ targetEnv index

theorem EnvPreimage.extend {n : ℕ} {sourceEnv : Env Source n} {targetEnv : Env Target n}
    (related : morphism.EnvPreimage sourceEnv targetEnv) (set : Set Target) :
    morphism.EnvPreimage (sourceEnv.extend (morphism.map ⁻¹' set)) (targetEnv.extend set) := by
  intro index element
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Iff.rfl
  · exact related index element

theorem envPreimage_closed : morphism.EnvPreimage Env.closed Env.closed := fun index => index.elim0

/-- **Counting steps is preserved and reflected.** -/
theorem atLeast_steps_iff {count : ℕ} {element : Source} {label : StepLabel} (own : label.isContext = false)
    {holds : Source → Prop}
    {holds' : Target → Prop} (same : ∀ other, holds other ↔ holds' (morphism.map other)) :
    (S.AtLeast count fun other => S.step element label other ∧ holds other) ↔
      T.AtLeast count fun other => T.step (morphism.map element) label other ∧ holds' other :=
  (morphism.toLabel fun _ => true).atLeast_steps_iff (by rw [StepLabel.admittedBy, own]; rfl) same

/-- **Along a step morphism, a behavioural formula holds at an element exactly when it holds at its
image.** -/
theorem sat_iff {n : ℕ} (formula : Formula n) (behavioural : formula.behaviouralForward = true)
    {sourceEnv : Env Source n} {targetEnv : Env Target n} (related : morphism.EnvPreimage sourceEnv targetEnv)
    (element : Source) : S.sat sourceEnv formula element ↔ T.sat targetEnv formula (morphism.map element) :=
  (morphism.toLabel fun _ => true).sat_iff formula (by rw [Formula.behaviouralIn_all]; exact behavioural) related
    element

end StepMorphism

/-! ## The steps a reading of the rules lists -/

open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (rewriteAt mem_rewriteAt_iff_stepAt)

/-- **The steps a reading of the rules lists at a term**, with some fuel: the reference relation's witnessed steps, or
the interpretation's contracta with the witness of no rule. -/
def ruleSteps (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) :
    RuleReading → Pattern → List (Witness × Pattern)
  | .reference => stepsAt relEnv language fuel
  | .interpreted interpretation base => fun term =>
    (rewriteAt interpretation base language fuel term).map fun target => (.base [], target)
  | .modulo canon presentations => presentedStepsAt relEnv language (listedPresent canon presentations) fuel
  | .moduloTabled canon presentations _ table _ => fun shown =>
    (tableStepper table shown).filter fun step =>
      checkPresentedStep relEnv language (listedPresent canon presentations) shown step.1 == some step.2

/-- **Whether the fuel lists a reading's steps at a term completely**: the reference relation checks it; an
interpretation claims nothing, and canonical forms coherent for it are coherent at the fuel they list at. -/
def ruleEnough (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) : RuleReading → Pattern → Bool
  | .reference => enough relEnv language fuel
  | .interpreted _ _ => fun _ => true
  | .modulo canon presentations => presentedEnough relEnv language (listedPresent canon presentations) fuel
  | .moduloTabled _ _ todo _ complete => fun shown => complete && decide (shown ∈ todo)

/-- **Every listed step is a step of the reading.** -/
theorem ruleValid_of_mem_ruleSteps {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ} {rules : RuleReading}
    {source : Pattern} {entry : Witness × Pattern} (member : entry ∈ ruleSteps relEnv language fuel rules source) :
    RuleValid relEnv language rules source entry.1 entry.2 := by
  obtain ⟨witness, target⟩ := entry
  cases rules with
  | reference => exact stepValid_of_mem_stepsAt relEnv language member
  | interpreted interpretation base =>
    obtain ⟨contractum, listed, same⟩ := List.mem_map.mp member
    cases same
    exact ⟨rfl, fuel, mem_rewriteAt_iff_stepAt.mp listed⟩
  | modulo canon presentations =>
    exact stepValid_equational_of_presented (fun _ _ listed => (canon_eq_of_mem_listedPresent listed).symm) _
      (stepValid_of_mem_presentedStepsAt member)
  | moduloTabled canon presentations todo table complete =>
    obtain ⟨-, checked⟩ := List.mem_filter.mp member
    exact stepValid_equational_of_presented (fun _ _ listed => (canon_eq_of_mem_listedPresent listed).symm) _
      (stepValid_of_checkPresentedStep _ (by simpa using checked))

/-! ## Canonical forms and coherence -/

variable (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (canon : Pattern → Pattern)
  (domain : Pattern → Bool) (presentations : Pattern → List Pattern)

/-- **Canonical forms on a domain of admitted terms**, in a reading of the equations: admitted terms are object
terms; the domain is closed under the equivalence, contains the canonical forms of its terms, and contains the
contractum of a step from an admitted state when it contains that contractum's canonical form; each admitted term is
equivalent to its canonical form, an admitted term and anything equivalent to it have the same one, and canonical
forms keep closedness. -/
structure Canonical (reading : LanguageReading := .syntax) : Prop where
  object : ∀ {term}, domain term = true → IsObject term
  admitted_canon : ∀ {term}, domain term = true → domain (canon term) = true
  invariant : ∀ {first second}, domain first = true → ObjectEquivalent relEnv language reading first second →
    domain second = true
  stepsAdmitted : ∀ {redex : Pattern} {witness : Witness} {contractum : Pattern}, domain redex = true → IsState redex →
    RuleValid relEnv language reading.rules redex witness contractum → domain (canon contractum) = true →
      domain contractum = true
  equivalent : ∀ {term}, domain term = true → ObjectEquivalent relEnv language reading term (canon term)
  same : ∀ {first second}, domain first = true → ObjectEquivalent relEnv language reading first second →
    canon first = canon second
  closed : ∀ {term}, domain term = true → (canon term).isWellScopedAt 0 = term.isWellScopedAt 0

/-- **Canonical forms on a domain read off canonical forms**: a term is admitted exactly when its canonical form is.
Such forms are canonical forms on their domain (`CanonicalDetermined.canonical`). -/
structure CanonicalDetermined (reading : LanguageReading := .syntax) : Prop where
  object : ∀ {term}, domain term = true → IsObject term
  determined : ∀ term, domain (canon term) = domain term
  equivalent : ∀ {term}, domain term = true → ObjectEquivalent relEnv language reading term (canon term)
  same : ∀ {first second}, domain first = true → ObjectEquivalent relEnv language reading first second →
    canon first = canon second
  closed : ∀ {term}, domain term = true → (canon term).isWellScopedAt 0 = term.isWellScopedAt 0

/-- **The steps listed at a state**: those listed at each of its presentations, terms with the state as canonical
form at which the language's rules may fire. -/
def listedAt (state : Pattern) (rules : RuleReading := .reference) : List (Witness × Pattern) :=
  (presentations state).flatMap (ruleSteps relEnv language fuel rules)

/-- Whether the fuel lists the steps at every presentation of a state completely. -/
def enoughAt (state : Pattern) (rules : RuleReading := .reference) : Bool :=
  (presentations state).all (ruleEnough relEnv language fuel rules)

/-- **Coherence**: a step from any state equivalent to an admitted canonical state is matched, up to
canonical form and with the same labels, by a step listed at that state, wherever the fuel lists it
completely. -/
def Coherent (reading : LanguageReading := .syntax) : Prop :=
  ∀ {state redex : Pattern} {witness : Witness} {contractum : Pattern}, IsState state → domain state = true →
    canon state = state → enoughAt relEnv language fuel presentations state reading.rules = true →
      ObjectEquivalent relEnv language reading state redex → IsState redex →
        RuleValid relEnv language reading.rules redex witness contractum →
        ∃ entry ∈ listedAt relEnv language fuel presentations state reading.rules,
          (∀ label : StepLabel, label.admits witness = label.admits entry.1) ∧ canon entry.2 = canon contractum

/-- The plain step label: `◇` and `□` without a rule or a site. -/
def plainLabel : StepLabel → Bool
  | .any => true
  | _ => false

/-- **Coherence for plain steps**: a step from any state equivalent to an admitted canonical state is
matched, up to canonical form, by a step listed at that state, wherever the fuel lists it completely. The
labels of the two steps are not compared. -/
def CoherentPlain (reading : LanguageReading := .syntax) : Prop :=
  ∀ {state redex : Pattern} {witness : Witness} {contractum : Pattern}, IsState state → domain state = true →
    canon state = state → enoughAt relEnv language fuel presentations state reading.rules = true →
      ObjectEquivalent relEnv language reading state redex → IsState redex →
        RuleValid relEnv language reading.rules redex witness contractum →
        ∃ entry ∈ listedAt relEnv language fuel presentations state reading.rules, canon entry.2 = canon contractum

variable {relEnv language fuel canon domain presentations} {reading : LanguageReading}

theorem mem_listedAt {state : Pattern} {rules : RuleReading} {entry : Witness × Pattern} :
    entry ∈ listedAt relEnv language fuel presentations state rules ↔
      ∃ shown ∈ presentations state, entry ∈ ruleSteps relEnv language fuel rules shown := by
  simp only [listedAt, List.mem_flatMap]

theorem enoughAt_iff {state : Pattern} {rules : RuleReading} :
    enoughAt relEnv language fuel presentations state rules = true ↔
      ∀ shown ∈ presentations state, ruleEnough relEnv language fuel rules shown = true := by
  simp only [enoughAt, List.all_eq_true]

theorem listedAt_singleton (state : Pattern) :
    listedAt relEnv language fuel List.singleton state = stepsAt relEnv language fuel state := by
  simp [listedAt, List.singleton, ruleSteps]

theorem enoughAt_singleton (state : Pattern) :
    enoughAt relEnv language fuel List.singleton state = enough relEnv language fuel state := by
  simp [enoughAt, List.singleton, ruleEnough]

/-- Coherence is coherence for plain steps. -/
theorem Coherent.plain (coherent : Coherent relEnv language fuel canon domain presentations reading) :
    CoherentPlain relEnv language fuel canon domain presentations reading := by
  intro state redex witness contractum stateIs admitted canonState complete before redexState valid
  obtain ⟨entry, member, -, same⟩ := coherent stateIs admitted canonState complete before redexState valid
  exact ⟨entry, member, same⟩

variable (relEnv language fuel canon domain presentations) in
/-- **Coherence on admitted labels**: a step from any state equivalent to an admitted canonical state is
matched, up to canonical form and alike on the admitted labels, by a step listed at that state, wherever the
fuel lists it completely. -/
def CoherentOn (admissible : StepLabel → Bool) (reading : LanguageReading := .syntax) : Prop :=
  ∀ {state redex : Pattern} {witness : Witness} {contractum : Pattern}, IsState state → domain state = true →
    canon state = state → enoughAt relEnv language fuel presentations state reading.rules = true →
      ObjectEquivalent relEnv language reading state redex → IsState redex →
        RuleValid relEnv language reading.rules redex witness contractum →
        ∃ entry ∈ listedAt relEnv language fuel presentations state reading.rules,
          (∀ label : StepLabel, admissible label = true → label.admits witness = label.admits entry.1) ∧
            canon entry.2 = canon contractum

/-- Coherence is coherence on any admitted labels. -/
theorem Coherent.on (coherent : Coherent relEnv language fuel canon domain presentations reading) (admissible : StepLabel →
  Bool) :
    CoherentOn relEnv language fuel canon domain presentations admissible reading := by
  intro state redex witness contractum stateIs admitted canonState complete before redexState valid
  obtain ⟨entry, member, labels, same⟩ := coherent stateIs admitted canonState complete before redexState valid
  exact ⟨entry, member, fun label _ => labels label, same⟩

/-- Coherence on admitted labels is coherence for plain steps. -/
theorem CoherentOn.plain {admissible : StepLabel → Bool}
    (coherent : CoherentOn relEnv language fuel canon domain presentations admissible reading) :
    CoherentPlain relEnv language fuel canon domain presentations reading := by
  intro state redex witness contractum stateIs admitted canonState complete before redexState valid
  obtain ⟨entry, member, -, same⟩ := coherent stateIs admitted canonState complete before redexState valid
  exact ⟨entry, member, same⟩

/-- Coherence for plain steps is coherence on the plain label. -/
theorem CoherentPlain.on (coherent : CoherentPlain relEnv language fuel canon domain presentations reading) :
    CoherentOn relEnv language fuel canon domain presentations plainLabel reading := by
  intro state redex witness contractum stateIs admitted canonState complete before redexState valid
  obtain ⟨entry, member, same⟩ := coherent stateIs admitted canonState complete before redexState valid
  refine ⟨entry, member, fun label plain => ?_, same⟩
  cases label with
  | any => rfl
  | rule _ => cases plain
  | under _ _ => cases plain
  | context _ _ _ => cases plain

/-- **Canonical forms read off canonical forms are canonical forms on their domain.** -/
theorem CanonicalDetermined.canonical (forms : CanonicalDetermined relEnv language canon domain reading) :
    Canonical relEnv language canon domain reading where
  object := forms.object
  admitted_canon admitted := (forms.determined _).trans admitted
  invariant {first second} admitted equivalent := by
    rw [← forms.determined second, ← forms.same admitted equivalent, forms.determined]
    exact admitted
  stepsAdmitted {_ _ contractum} _ _ _ canonAdmitted := (forms.determined contractum).symm.trans canonAdmitted
  equivalent := forms.equivalent
  same := forms.same
  closed := forms.closed

namespace Canonical

variable (canonical : Canonical relEnv language canon domain reading)
include canonical

theorem idempotent {term : Pattern} (admitted : domain term = true) : canon (canon term) = canon term :=
  canonical.same (canonical.admitted_canon admitted)
    (ObjectEquivalent.equivalence.symm (canonical.equivalent admitted))

theorem state {term : Pattern} (admitted : domain term = true) (state : IsState term) : IsState (canon term) :=
  ⟨(canonical.closed admitted).trans state.1, canonical.object (canonical.admitted_canon admitted)⟩

theorem state_of_canon {term : Pattern} (admitted : domain term = true) (state : IsState (canon term)) :
    IsState term :=
  ⟨(canonical.closed admitted).symm.trans state.1, canonical.object admitted⟩

theorem indistinct {term : Pattern} (admitted : domain term = true) :
    Indistinct relEnv language reading term (canon term) :=
  Or.inr ⟨canonical.object admitted, canonical.object (canonical.admitted_canon admitted), by
    show term.isWellScopedAt 0 = true ↔ (canon term).isWellScopedAt 0 = true
    rw [canonical.closed admitted], canonical.equivalent admitted⟩

/-- **Canonical forms decide equivalence** among admitted terms. -/
theorem equivalent_iff {first second : Pattern} (firstAdmitted : domain first = true)
    (secondAdmitted : domain second = true) :
    ObjectEquivalent relEnv language reading first second ↔ canon first = canon second := by
  refine ⟨canonical.same firstAdmitted, fun same => ?_⟩
  refine ObjectEquivalent.equivalence.trans (canonical.equivalent firstAdmitted) ?_
  rw [same]
  exact ObjectEquivalent.equivalence.symm (canonical.equivalent secondAdmitted)

end Canonical

/-! ## The part of the structure a term reaches -/

variable (relEnv language reading)

/-- The terms a term reaches in its own steps, of any label. -/
def Reached (start : Pattern) : Pattern → Prop :=
  Relation.ReflTransGen (fun source target => ∃ label, label.isContext = false ∧
    (referenceStructure relEnv language reading).step source label target) start

/-- **The part of the language's structure a term reaches**, with its steps, identity and names. -/
def reachableStructure (start : Pattern) : NativeStructure {term // Reached relEnv language reading start term} where
  step source label target := (referenceStructure relEnv language reading).step source.val label target.val
  built _ _ _ := False
  split _ _ _ _ := False
  empty _ _ := False
  single _ _ _ := False
  body _ _ := False
  multiBody _ _ _ := False
  bound _ _ := False
  typed _ _ := False
  named element term := (referenceStructure relEnv language reading).named element.val term
  same first second := (referenceStructure relEnv language reading).same first.val second.val
  apply inner _ := inner
  inRelation element relation := (referenceStructure relEnv language reading).inRelation element.val relation

variable {relEnv language reading}

/-- **The reached part sits inside the language's structure**: the steps from a reached term are all
reached. -/
def reachableMorphism (start : Pattern) :
    StepMorphism (reachableStructure relEnv language reading start) (referenceStructure relEnv language reading) where
  map := Subtype.val
  step _ step := step
  stepBack := by
    intro source label target own step
    exact ⟨⟨target, source.2.tail ⟨label, own, step⟩⟩, step, rfl⟩
  sameIff _ _ := Iff.rfl
  namedIff _ _ := Iff.rfl

/-! ## The canonical structure -/

variable (relEnv language canon domain reading)

/-- **The canonical structure**: admitted canonical terms, with the language's steps to them, identity as
equality, and each admitted term naming its canonical form. -/
def canonicalStructure : NativeStructure Pattern where
  step source label target := (referenceStructure relEnv language reading).step source label target ∧ domain target = true ∧
    canon target = target
  built _ _ _ := False
  split _ _ _ _ := False
  empty _ _ := False
  single _ _ _ := False
  body _ _ := False
  multiBody _ _ _ := False
  bound _ _ := False
  typed _ _ := False
  named element term := IsObject term ∧ domain term = true ∧ canon term = element
  same first second := first = second
  apply inner _ := inner
  inRelation element relation := (referenceStructure relEnv language reading).inRelation element relation

variable {relEnv language canon domain reading}

/-- **Taking canonical forms is a step morphism** from the part a term reaches onto the canonical structure,
when everything reached is admitted. -/
def canonMorphism (canonical : Canonical relEnv language canon domain reading) {start : Pattern}
    (admitted : ∀ term, Reached relEnv language reading start term → domain term = true) :
    StepMorphism (reachableStructure relEnv language reading start) (canonicalStructure relEnv language canon domain reading) where
  map term := canon term.val
  step := by
    intro source label target _ step
    have saturated := referenceStructure_saturated relEnv language reading
    exact ⟨saturated.stepTarget (canonical.indistinct (admitted _ target.2))
        (saturated.stepSource (canonical.indistinct (admitted _ source.2)) step),
      canonical.admitted_canon (admitted _ target.2), canonical.idempotent (admitted _ target.2)⟩
  stepBack := by
    intro source label target' own step
    have saturated := referenceStructure_saturated relEnv language reading
    have original : (referenceStructure relEnv language reading).step source.val label target' :=
      saturated.stepSource (saturated.equivalence.symm (canonical.indistinct (admitted _ source.2))) step.1
    exact ⟨⟨target', source.2.tail ⟨label, own, original⟩⟩, original, step.2.2⟩
  sameIff first second := canonical.equivalent_iff (admitted _ first.2) (admitted _ second.2)
  namedIff element term := by
    constructor
    · rintro ⟨-, equivalent⟩
      exact ⟨equivalent.object_right (canonical.object (admitted _ element.2)),
        canonical.invariant (admitted _ element.2) equivalent,
        (canonical.same (admitted _ element.2) equivalent).symm⟩
    · rintro ⟨-, termAdmitted, same⟩
      exact ⟨canonical.object (admitted _ element.2),
        (canonical.equivalent_iff (admitted _ element.2) termAdmitted).mpr same.symm⟩

/-! ## Closed canonical regions -/

variable (relEnv language fuel canon domain presentations) (region : List Pattern)

/-- **A closed canonical region**: admitted canonical terms without repetition; each state completely listed
at the fuel at its presentations, which have it as canonical form, with the canonical forms of its listed
successors in the region. -/
def canonicalRegion (rules : RuleReading := .reference) : Bool :=
  decide region.Nodup && region.all fun term => domain term && canon term == term &&
    (!isStateBool term ||
      ((presentations term).all (fun shown => domain shown && canon shown == term) &&
        enoughAt relEnv language fuel presentations term rules &&
        (listedAt relEnv language fuel presentations term rules).all fun entry => canon entry.2 ∈ region))

/-- **The steps listed at each state of a region**, listed once. -/
def regionListings (rules : RuleReading := .reference) : List (List (Witness × Pattern)) :=
  region.map fun term => listedAt relEnv language fuel presentations term rules

/-- The canonical region as a finite structure over its listings. -/
def explorationOf (listings : List (List (Witness × Pattern))) : FiniteStructure (Fin region.length) where
  elements := List.finRange region.length
  complete := List.mem_finRange
  step source label target := isStateBool region[source] && isStateBool region[target] &&
    (listings.getD source.1 []).any fun entry => canon entry.2 == region[target] && label.admits entry.1
  built _ _ _ := false
  split _ _ _ _ := false
  empty _ _ := false
  single _ _ _ := false
  body _ _ := false
  multiBody _ _ _ := false
  bound _ _ := false
  typed _ _ := false
  named element term := isObjectPattern term && domain term && canon term == region[element]
  same first second := decide (first = second)
  apply inner _ := inner
  inRelation element relation := isObjectPattern region[element] && relationHolds relEnv language relation region[element]

/-- **The canonical region as a finite structure**: its steps lead to the canonical forms of listed
successors, and each admitted term names its canonical form. Each state's steps are listed once. -/
def canonicalExploration (rules : RuleReading := .reference) : FiniteStructure (Fin region.length) :=
  explorationOf relEnv language canon domain region (regionListings relEnv language fuel presentations region rules)

variable {relEnv language fuel canon domain presentations region}

theorem regionListings_getD {rules : RuleReading} (index : Fin region.length) :
    (regionListings relEnv language fuel presentations region rules).getD index.1 [] =
      listedAt relEnv language fuel presentations region[index] rules := by
  simp [regionListings, List.getD_eq_getElem?_getD]

theorem canonicalRegion_parts {rules : RuleReading}
    (closed : canonicalRegion relEnv language fuel canon domain presentations region rules = true) :
    region.Nodup ∧ ∀ term ∈ region, domain term = true ∧ canon term = term ∧
      (isStateBool term = true → (∀ shown ∈ presentations term, domain shown = true ∧ canon shown = term) ∧
        enoughAt relEnv language fuel presentations term rules = true ∧
        ∀ entry ∈ listedAt relEnv language fuel presentations term rules, canon entry.2 ∈ region) := by
  simp only [canonicalRegion, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at closed
  refine ⟨closed.1, fun term member => ⟨(closed.2 term member).1.1, (closed.2 term member).1.2, fun state => ?_⟩⟩
  rcases (closed.2 term member).2 with notState | listed
  · rw [notState] at state
    cases state
  · exact ⟨listed.1.1, listed.1.2, listed.2⟩

/-- **A closed canonical region's inclusion is a step morphism**, given canonical forms and coherence. -/
def regionMorphism (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading)
    (closed : canonicalRegion relEnv language fuel canon domain presentations region reading.rules = true) :
    StepMorphism (canonicalExploration relEnv language fuel canon domain presentations region reading.rules).native
      (canonicalStructure relEnv language canon domain reading) where
  map index := region[index]
  step := by
    intro source label target own checked
    change (_ && _ && _) = true at checked
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, regionListings_getD] at checked
    obtain ⟨⟨sourceState, targetState⟩, entry, member, same, admits⟩ := checked
    obtain ⟨sourceAdmitted, sourceCanon, sourceListing⟩ :=
      (canonicalRegion_parts closed).2 _ (List.getElem_mem source.2)
    obtain ⟨targetAdmitted, targetCanon, -⟩ := (canonicalRegion_parts closed).2 _ (List.getElem_mem target.2)
    obtain ⟨shown, shownMember, listed⟩ := mem_listedAt.mp member
    obtain ⟨shownAdmitted, shownCanon⟩ := (sourceListing sourceState).1 shown shownMember
    have sourceIsState : IsState region[source] := by simpa [isStateBool] using sourceState
    have targetIsState : IsState region[target] := by simpa [isStateBool] using targetState
    have contractumAdmitted : domain entry.2 = true :=
      canonical.stepsAdmitted shownAdmitted (canonical.state_of_canon shownAdmitted (shownCanon ▸ sourceIsState))
        (ruleValid_of_mem_ruleSteps listed) (same ▸ targetAdmitted)
    have contractumState : IsState entry.2 := canonical.state_of_canon contractumAdmitted (same ▸ targetIsState)
    refine ⟨⟨sourceIsState, targetIsState, shown, entry.2, entry.1,
      (placed_iff own).mpr ((canonical.equivalent_iff sourceAdmitted shownAdmitted).mpr (sourceCanon.trans shownCanon.symm)),
      canonical.state_of_canon shownAdmitted (shownCanon ▸ sourceIsState),
      ruleValid_of_mem_ruleSteps listed, contractumState,
      (canonical.equivalent_iff contractumAdmitted targetAdmitted).mpr (same.trans targetCanon.symm),
      StepLabel.base_admits admits⟩, targetAdmitted, targetCanon⟩
  stepBack := by
    intro source label target' own step
    obtain ⟨⟨sourceState, targetState, redex, contractum, witness, before, redexState, valid, contractumState, after,
      admits⟩, targetAdmitted, canonTarget⟩ := step
    rw [placed_iff own] at before
    replace admits := StepLabel.admits_of_base own admits
    obtain ⟨-, members⟩ := canonicalRegion_parts closed
    obtain ⟨sourceAdmitted, canonSource, listing⟩ := members _ (List.getElem_mem source.2)
    obtain ⟨-, complete, successors⟩ := listing (isStateBool_of_isState sourceState)
    obtain ⟨entry, member, sameLabels, sameCanon⟩ :=
      coherent sourceState sourceAdmitted canonSource complete before redexState valid
    have reached : canon entry.2 = target' :=
      sameCanon.trans ((canonical.same targetAdmitted (ObjectEquivalent.equivalence.symm after)).symm.trans canonTarget)
    obtain ⟨target, isTarget⟩ := exists_index (successors entry member)
    refine ⟨target, ?_, isTarget.trans reached⟩
    show (_ && _ && _) = true
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, regionListings_getD]
    refine ⟨⟨isStateBool_of_isState sourceState, isStateBool_of_isState (by rw [isTarget, reached]; exact targetState)⟩,
      entry, member, isTarget.symm, (sameLabels label).symm.trans admits⟩
  sameIff first second := by
    change decide (first = second) = true ↔ region[first] = region[second]
    rw [decide_eq_true_iff]
    constructor
    · rintro rfl
      rfl
    · intro same
      exact Fin.ext ((List.Nodup.getElem_inj_iff (canonicalRegion_parts closed).1).mp same)
  namedIff element term := by
    change (isObjectPattern term && domain term && canon term == region[element]) = true ↔ _
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun ⟨⟨object, admitted⟩, same⟩ => ⟨object, admitted, same⟩,
      fun ⟨object, admitted, same⟩ => ⟨⟨object, admitted⟩, same⟩⟩

/-- **Everything an admitted term reaches is admitted**, with its canonical form in a closed region that
lists the term's: each step is matched at a listed canonical state, whose successors' canonical forms the
region lists. -/
theorem reaches_admitted (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentPlain relEnv language fuel canon domain presentations reading)
    (closed : canonicalRegion relEnv language fuel canon domain presentations region reading.rules = true) {start : Pattern}
    (admitted : domain start = true) (listed : canon start ∈ region) :
    ∀ {term}, Reached relEnv language reading start term → domain term = true ∧ canon term ∈ region := by
  intro term reached
  induction reached with
  | refl => exact ⟨admitted, listed⟩
  | tail _ step previous =>
    obtain ⟨sourceAdmitted, sourceListed⟩ := previous
    obtain ⟨label, own, sourceState, targetState, redex, contractum, witness, before, redexState, valid, contractumState,
      after, admits⟩ := step
    rw [placed_iff own] at before
    obtain ⟨-, members⟩ := canonicalRegion_parts closed
    obtain ⟨-, canonSource, listing⟩ := members _ sourceListed
    have canonState := canonical.state sourceAdmitted sourceState
    obtain ⟨-, complete, successors⟩ := listing (isStateBool_of_isState canonState)
    obtain ⟨entry, member, sameCanon⟩ :=
      coherent canonState (canonical.admitted_canon sourceAdmitted) canonSource complete
        (ObjectEquivalent.equivalence.trans (ObjectEquivalent.equivalence.symm (canonical.equivalent sourceAdmitted))
          before) redexState valid
    have entryListed := successors entry member
    have contractumAdmitted : domain contractum = true :=
      canonical.stepsAdmitted (canonical.invariant sourceAdmitted before) redexState valid
        (sameCanon ▸ (members _ entryListed).1)
    refine ⟨canonical.invariant contractumAdmitted after, ?_⟩
    rw [← canonical.same contractumAdmitted after, ← sameCanon]
    exact entryListed

/-- **A closed canonical region decides every behavioural formula** at the admitted terms whose canonical
forms it lists, both ways. -/
theorem canonical_check_iff (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading)
    (closed : canonicalRegion relEnv language fuel canon domain presentations region reading.rules = true) {formula : Formula 0}
    (behavioural : formula.behaviouralForward = true) {index : Fin region.length} {term : Pattern}
    (admitted : domain term = true) (listed : canon term = region[index]) :
    (canonicalExploration relEnv language fuel canon domain presentations region reading.rules).check formula index = true ↔
      (referenceStructure relEnv language reading).sat Env.closed formula term := by
  have allAdmitted : ∀ other, Reached relEnv language reading term other → domain other = true := fun _ reached =>
    (reaches_admitted canonical coherent.plain closed admitted (listed ▸ List.getElem_mem index.2) reached).1
  have regionSide := (regionMorphism canonical coherent closed).sat_iff formula behavioural
    (StepMorphism.envPreimage_closed _) index
  have canonSide := (canonMorphism canonical allAdmitted).sat_iff formula behavioural
    (StepMorphism.envPreimage_closed _) ⟨term, Relation.ReflTransGen.refl⟩
  have reachSide := (reachableMorphism (relEnv := relEnv) (language := language) (reading := reading) term).sat_iff
    formula behavioural
    (StepMorphism.envPreimage_closed _)
    ⟨term, Relation.ReflTransGen.refl⟩
  rw [FiniteStructure.check_iff]
  refine regionSide.trans (Iff.trans ?_ (canonSide.symm.trans reachSide))
  show (canonicalStructure relEnv language canon domain reading).sat Env.closed formula region[index] ↔
    (canonicalStructure relEnv language canon domain reading).sat Env.closed formula (canon term)
  rw [listed]

/-! ## Growing a canonical region -/

variable (relEnv language fuel canon presentations)

/-- What a term adds to a canonical region: the canonical forms of its listed successors when it is a
state. -/
abbrev nextCanonical (state : Pattern) (rules : RuleReading := .reference) : List Pattern :=
  if isStateBool state then (listedAt relEnv language fuel presentations state rules).map (canon ·.2) else []

/-- Grow a canonical region from a term: add the canonical forms of the listed successors of states,
without repetition, the term's canonical form first. -/
def growCanonical (term : Pattern) (rounds : ℕ) (rules : RuleReading := .reference) : List Pattern :=
  match rounds with
  | 0 => [canon term]
  | rounds + 1 =>
    let earlier := growCanonical term rounds rules
    addNew earlier (earlier.flatMap fun state => nextCanonical relEnv language fuel canon presentations state rules)

theorem growCanonical_first (term : Pattern) (rules : RuleReading) :
    ∀ rounds, ∃ rest, growCanonical relEnv language fuel canon presentations term rounds rules = canon term :: rest
  | 0 => ⟨[], rfl⟩
  | rounds + 1 => by
    obtain ⟨rest, same⟩ := growCanonical_first term rules rounds
    obtain ⟨extra, extended⟩ := addNew_extends (growCanonical relEnv language fuel canon presentations term rounds rules)
      ((growCanonical relEnv language fuel canon presentations term rounds rules).flatMap fun state =>
        nextCanonical relEnv language fuel canon presentations state rules)
    refine ⟨rest ++ extra, ?_⟩
    simp only [growCanonical]
    rw [extended, same, List.cons_append]

theorem growCanonical_length_pos (term : Pattern) (rounds : ℕ) (rules : RuleReading := .reference) :
    0 < (growCanonical relEnv language fuel canon presentations term rounds rules).length := by
  obtain ⟨rest, same⟩ := growCanonical_first relEnv language fuel canon presentations term rules rounds
  rw [same]
  exact Nat.succ_pos _

variable (domain)

/-- **Decide a behavioural formula at a term modulo the equations**: the exact verdict when the grown
canonical region closes, nothing otherwise. -/
def decideCanonical (formula : Formula 0) (term : Pattern) (rounds : ℕ) (rules : RuleReading := .reference) :
    Option Bool :=
  if domain term && canonicalRegion relEnv language fuel canon domain presentations
    (growCanonical relEnv language fuel canon presentations term rounds rules) rules then
    some ((canonicalExploration relEnv language fuel canon domain presentations
      (growCanonical relEnv language fuel canon presentations term rounds rules) rules).check
      formula ⟨0, growCanonical_length_pos relEnv language fuel canon presentations term rounds rules⟩)
  else none

variable {relEnv language fuel canon domain presentations} {reading : LanguageReading}

theorem growCanonical_zero (term : Pattern) (rounds : ℕ) (rules : RuleReading := .reference) :
    (growCanonical relEnv language fuel canon presentations term rounds rules)[(⟨0,
      growCanonical_length_pos relEnv language fuel canon presentations term rounds rules⟩ :
        Fin (growCanonical relEnv language fuel canon presentations term rounds rules).length)] = canon term := by
  obtain ⟨rest, same⟩ := growCanonical_first relEnv language fuel canon presentations term rules rounds
  simp only [Fin.getElem_fin]
  simp [same]

/-- **A verdict from a closed canonical region is exact.** The region lists the term's canonical form, so
the term is admitted. -/
theorem decideCanonical_sound (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading)
    {formula : Formula 0} (behavioural : formula.behaviouralForward = true) {term : Pattern} {rounds : ℕ}
    {verdict : Bool} (decided : decideCanonical relEnv language fuel canon domain presentations formula term rounds
      reading.rules = some verdict) :
    (verdict = true ↔ (referenceStructure relEnv language reading).sat Env.closed formula term) := by
  unfold decideCanonical at decided
  split at decided
  · rename_i checked
    obtain ⟨admitted, closed⟩ := Bool.and_eq_true_iff.mp checked
    cases decided
    have listed := growCanonical_zero (relEnv := relEnv) (language := language) (fuel := fuel) (canon := canon)
      (presentations := presentations) term rounds reading.rules
    exact canonical_check_iff canonical coherent closed behavioural admitted listed.symm
  · cases decided

/-! ## Admitted labels -/

/-- **A closed canonical region's inclusion is a step morphism on admitted labels**, given canonical forms and
coherence on those labels. -/
def regionMorphismOn {admissible : StepLabel → Bool} (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentOn relEnv language fuel canon domain presentations admissible reading)
    (closed : canonicalRegion relEnv language fuel canon domain presentations region reading.rules = true) :
    LabelMorphism (canonicalExploration relEnv language fuel canon domain presentations region reading.rules).native
      (canonicalStructure relEnv language canon domain reading) admissible where
  map index := region[index]
  step := by
    intro source label target admittedLabel checked
    have own := StepLabel.isContext_of_admittedBy admittedLabel
    change (_ && _ && _) = true at checked
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, regionListings_getD] at checked
    obtain ⟨⟨sourceState, targetState⟩, entry, member, same, admits⟩ := checked
    obtain ⟨sourceAdmitted, sourceCanon, sourceListing⟩ :=
      (canonicalRegion_parts closed).2 _ (List.getElem_mem source.2)
    obtain ⟨targetAdmitted, targetCanon, -⟩ := (canonicalRegion_parts closed).2 _ (List.getElem_mem target.2)
    obtain ⟨shown, shownMember, listed⟩ := mem_listedAt.mp member
    obtain ⟨shownAdmitted, shownCanon⟩ := (sourceListing sourceState).1 shown shownMember
    have sourceIsState : IsState region[source] := by simpa [isStateBool] using sourceState
    have targetIsState : IsState region[target] := by simpa [isStateBool] using targetState
    have contractumAdmitted : domain entry.2 = true :=
      canonical.stepsAdmitted shownAdmitted (canonical.state_of_canon shownAdmitted (shownCanon ▸ sourceIsState))
        (ruleValid_of_mem_ruleSteps listed) (same ▸ targetAdmitted)
    have contractumState : IsState entry.2 := canonical.state_of_canon contractumAdmitted (same ▸ targetIsState)
    refine ⟨⟨sourceIsState, targetIsState, shown, entry.2, entry.1,
      (placed_iff own).mpr ((canonical.equivalent_iff sourceAdmitted shownAdmitted).mpr (sourceCanon.trans shownCanon.symm)),
      canonical.state_of_canon shownAdmitted (shownCanon ▸ sourceIsState),
      ruleValid_of_mem_ruleSteps listed, contractumState,
      (canonical.equivalent_iff contractumAdmitted targetAdmitted).mpr (same.trans targetCanon.symm),
      StepLabel.base_admits admits⟩, targetAdmitted, targetCanon⟩
  stepBack := by
    intro source label target' admittedLabel step
    have own := StepLabel.isContext_of_admittedBy admittedLabel
    obtain ⟨⟨sourceState, targetState, redex, contractum, witness, before, redexState, valid, contractumState, after,
      admits⟩, targetAdmitted, canonTarget⟩ := step
    rw [placed_iff own] at before
    replace admits := StepLabel.admits_of_base own admits
    obtain ⟨-, members⟩ := canonicalRegion_parts closed
    obtain ⟨sourceAdmitted, canonSource, listing⟩ := members _ (List.getElem_mem source.2)
    obtain ⟨-, complete, successors⟩ := listing (isStateBool_of_isState sourceState)
    obtain ⟨entry, member, sameLabels, sameCanon⟩ :=
      coherent sourceState sourceAdmitted canonSource complete before redexState valid
    have reached : canon entry.2 = target' :=
      sameCanon.trans ((canonical.same targetAdmitted (ObjectEquivalent.equivalence.symm after)).symm.trans canonTarget)
    obtain ⟨target, isTarget⟩ := exists_index (successors entry member)
    refine ⟨target, ?_, isTarget.trans reached⟩
    show (_ && _ && _) = true
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, regionListings_getD]
    exact ⟨⟨isStateBool_of_isState sourceState, isStateBool_of_isState (by rw [isTarget, reached]; exact targetState)⟩,
      entry, member, isTarget.symm,
      (sameLabels label (StepLabel.admissible_of_admittedBy admittedLabel)).symm.trans admits⟩
  sameIff first second := by
    change decide (first = second) = true ↔ region[first] = region[second]
    rw [decide_eq_true_iff]
    constructor
    · rintro rfl
      rfl
    · intro same
      exact Fin.ext ((List.Nodup.getElem_inj_iff (canonicalRegion_parts closed).1).mp same)
  namedIff element term := by
    change (isObjectPattern term && domain term && canon term == region[element]) = true ↔ _
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun ⟨⟨object, admitted⟩, same⟩ => ⟨object, admitted, same⟩,
      fun ⟨object, admitted, same⟩ => ⟨⟨object, admitted⟩, same⟩⟩

/-- **A closed canonical region decides every behavioural formula over admitted labels** at the admitted
terms whose canonical forms it lists, given coherence on those labels. -/
theorem canonical_check_iff_on {admissible : StepLabel → Bool} (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentOn relEnv language fuel canon domain presentations admissible reading)
    (closed : canonicalRegion relEnv language fuel canon domain presentations region reading.rules = true) {formula : Formula 0}
    (behavioural : formula.behaviouralIn admissible = true) {index : Fin region.length} {term : Pattern}
    (admitted : domain term = true) (listed : canon term = region[index]) :
    (canonicalExploration relEnv language fuel canon domain presentations region reading.rules).check formula index = true ↔
      (referenceStructure relEnv language reading).sat Env.closed formula term := by
  have allAdmitted : ∀ other, Reached relEnv language reading term other → domain other = true := fun _ reached =>
    (reaches_admitted canonical coherent.plain closed admitted (listed ▸ List.getElem_mem index.2) reached).1
  have regionSide := (regionMorphismOn canonical coherent closed).sat_iff formula behavioural
    (LabelMorphism.envPreimage_closed _) index
  have canonSide := ((canonMorphism canonical allAdmitted).toLabel admissible).sat_iff formula behavioural
    (LabelMorphism.envPreimage_closed _) ⟨term, Relation.ReflTransGen.refl⟩
  have reachSide := ((reachableMorphism (relEnv := relEnv) (language := language) (reading := reading)
    term).toLabel admissible).sat_iff
    formula behavioural (LabelMorphism.envPreimage_closed _) ⟨term, Relation.ReflTransGen.refl⟩
  rw [FiniteStructure.check_iff]
  refine regionSide.trans (Iff.trans ?_ (canonSide.symm.trans reachSide))
  show (canonicalStructure relEnv language canon domain reading).sat Env.closed formula region[index] ↔
    (canonicalStructure relEnv language canon domain reading).sat Env.closed formula (canon term)
  rw [listed]

/-- **The canonical decision is sound for behavioural formulas over admitted labels**, given coherence on those
labels. -/
theorem decideCanonical_sound_on {admissible : StepLabel → Bool} (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentOn relEnv language fuel canon domain presentations admissible reading)
    {formula : Formula 0} (behavioural : formula.behaviouralIn admissible = true) {term : Pattern} {rounds : ℕ}
    {verdict : Bool} (decided : decideCanonical relEnv language fuel canon domain presentations formula term rounds
      reading.rules = some verdict) :
    (verdict = true ↔ (referenceStructure relEnv language reading).sat Env.closed formula term) := by
  unfold decideCanonical at decided
  split at decided
  · rename_i checked
    obtain ⟨admitted, closed⟩ := Bool.and_eq_true_iff.mp checked
    cases decided
    have listed := growCanonical_zero (relEnv := relEnv) (language := language) (fuel := fuel) (canon := canon)
      (presentations := presentations) term rounds reading.rules
    exact canonical_check_iff_on canonical coherent closed behavioural admitted listed.symm
  · cases decided

/-! ## Sufficient conditions -/

/-- **Coherence when canonical forms simulate steps**: a step from an admitted state is matched, with the
same labels and up to canonical form, by a step from its canonical form. A state equivalent to an admitted
canonical one has that one as its canonical form, so the matching step is listed there. -/
theorem coherent_of_simulation (canonical : Canonical relEnv language canon domain reading)
    (simulates : ∀ {redex witness contractum}, IsState redex → domain redex = true →
      StepValid relEnv language redex witness contractum →
      ∃ witness' contractum', StepValid relEnv language (canon redex) witness' contractum' ∧
        (∀ label : StepLabel, label.admits witness = label.admits witness') ∧ canon contractum' = canon contractum)
    (reference : reading.rules = .reference := by rfl) :
    Coherent relEnv language fuel canon domain List.singleton reading := by
  intro state redex witness contractum _ stateAdmitted canonState complete before redexState valid
  rw [reference] at complete valid ⊢
  obtain ⟨witness', contractum', simulated, sameLabels, sameCanon⟩ :=
    simulates redexState (canonical.invariant stateAdmitted before) valid
  have same : canon redex = state := ((canonical.same stateAdmitted before).symm).trans canonState
  rw [same] at simulated
  rw [enoughAt_singleton] at complete
  exact ⟨(witness', contractum'), by rw [listedAt_singleton]; exact mem_stepsAt_of_enough complete simulated,
    sameLabels, sameCanon⟩

/-- **Coherence for plain steps when canonical forms simulate steps**: a step from an admitted state is matched,
up to canonical form and with any labels, by a step from its canonical form. -/
theorem coherentPlain_of_simulation (canonical : Canonical relEnv language canon domain reading)
    (simulates : ∀ {redex witness contractum}, IsState redex → domain redex = true →
      StepValid relEnv language redex witness contractum →
      ∃ witness' contractum', StepValid relEnv language (canon redex) witness' contractum' ∧
        canon contractum' = canon contractum) (reference : reading.rules = .reference := by rfl) :
    CoherentPlain relEnv language fuel canon domain List.singleton reading := by
  intro state redex witness contractum _ stateAdmitted canonState complete before redexState valid
  rw [reference] at complete valid ⊢
  obtain ⟨witness', contractum', simulated, sameCanon⟩ :=
    simulates redexState (canonical.invariant stateAdmitted before) valid
  have same : canon redex = state := ((canonical.same stateAdmitted before).symm).trans canonState
  rw [same] at simulated
  rw [enoughAt_singleton] at complete
  exact ⟨(witness', contractum'), by rw [listedAt_singleton]; exact mem_stepsAt_of_enough complete simulated,
    sameCanon⟩

/-- **Coherence for plain steps when presentations of canonical forms simulate steps**: a step from an admitted
state is matched, up to canonical form, by a step from some presentation of its canonical form. A state equivalent to
an admitted canonical one has that one as its canonical form, so the matching step is listed at it. -/
theorem coherentPlain_of_presented_simulation (canonical : Canonical relEnv language canon domain reading)
    (simulates : ∀ {redex witness contractum}, IsState redex → domain redex = true →
      StepValid relEnv language redex witness contractum →
      ∃ shown ∈ presentations (canon redex), ∃ witness' contractum',
        StepValid relEnv language shown witness' contractum' ∧ canon contractum' = canon contractum)
    (reference : reading.rules = .reference := by rfl) :
    CoherentPlain relEnv language fuel canon domain presentations reading := by
  intro state redex witness contractum _ stateAdmitted canonState complete before redexState valid
  rw [reference] at complete valid ⊢
  obtain ⟨shown, presented, witness', contractum', simulated, sameCanon⟩ :=
    simulates redexState (canonical.invariant stateAdmitted before) valid
  have same : canon redex = state := ((canonical.same stateAdmitted before).symm).trans canonState
  rw [same] at presented
  have enoughShown := (enoughAt_iff.mp complete) shown presented
  exact ⟨(witness', contractum'), mem_listedAt.mpr ⟨shown, presented, mem_stepsAt_of_enough enoughShown simulated⟩,
    sameCanon⟩

/-- **Coherence when rules fire only on canonical terms**: a step from an equivalent of a canonical state is
then a step from the state itself. -/
theorem coherent_of_canonical_redexes (canonical : Canonical relEnv language canon domain reading)
    (redexes : ∀ {redex witness contractum}, domain redex = true → StepValid relEnv language redex witness contractum →
      canon redex = redex) (reference : reading.rules = .reference := by rfl) :
    Coherent relEnv language fuel canon domain List.singleton reading :=
  coherent_of_simulation canonical (fun {_ witness contractum} _ admitted valid =>
    ⟨witness, contractum, (redexes admitted valid).symm ▸ valid, fun _ => rfl, rfl⟩) reference

/-- **Equivalence is a congruence** for contexts that keep object terms object terms. -/
theorem ObjectEquivalent.fill (context : OneHoleContext)
    (objects : ∀ pattern, IsObject pattern → IsObject (context.fill pattern)) {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language .syntax first second) :
    ObjectEquivalent relEnv language .syntax (context.fill first) (context.fill second) := by
  induction equivalent with
  | rel first second step =>
    obtain ⟨firstObject, secondObject, step⟩ := step
    cases step with
    | inContext inner generator =>
      refine Relation.EqvGen.rel _ _ ⟨objects _ firstObject, objects _ secondObject, ?_⟩
      rw [← OneHoleContext.fill_comp, ← OneHoleContext.fill_comp]
      exact .inContext _ generator
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ previous => exact Relation.EqvGen.symm _ _ previous
  | trans _ _ _ _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- **Changing list entries one at a time**, inside a constructor or collection: when each entry is
equivalent to its image, the whole is equivalent to the image of every entry. -/
theorem ObjectEquivalent.list_congr (map : Pattern → Pattern)
    (mapObject : ∀ pattern, IsObject pattern → IsObject (map pattern)) (wrap : List Pattern → Pattern)
    (frame : List Pattern → List Pattern → OneHoleContext)
    (fills : ∀ before after pattern, (frame before after).fill pattern = wrap (before ++ pattern :: after))
    (objects : ∀ patterns : List Pattern, (∀ pattern ∈ patterns, IsObject pattern) → IsObject (wrap patterns)) :
    ∀ (patterns done : List Pattern), (∀ pattern ∈ done, IsObject pattern) →
      (∀ pattern ∈ patterns, IsObject pattern ∧ ObjectEquivalent relEnv language .syntax pattern (map pattern)) →
      ObjectEquivalent relEnv language .syntax (wrap (done ++ patterns)) (wrap (done ++ patterns.map map))
  | [], _, _, _ => by rw [List.map_nil]; exact Relation.EqvGen.refl _
  | pattern :: patterns, done, doneObjects, each => by
    obtain ⟨patternObject, patternEquivalent⟩ := each pattern List.mem_cons_self
    have first := patternEquivalent.fill (frame done patterns) (fun other otherObject => by
      rw [fills]
      refine objects _ fun member inside => ?_
      rcases List.mem_append.mp inside with inside | inside
      · exact doneObjects member inside
      · rcases List.mem_cons.mp inside with rfl | inside
        · exact otherObject
        · exact (each member (List.mem_cons_of_mem _ inside)).1)
    have rest := ObjectEquivalent.list_congr map mapObject wrap frame fills objects patterns (done ++ [map pattern])
      (fun member inside => by
        rcases List.mem_append.mp inside with inside | inside
        · exact doneObjects member inside
        · rw [List.mem_singleton] at inside
          subst inside
          exact mapObject pattern patternObject)
      fun member inside => each member (List.mem_cons_of_mem _ inside)
    rw [fills, fills] at first
    rw [List.append_assoc, List.singleton_append, List.append_assoc, List.singleton_append] at rest
    rw [List.map_cons]
    exact Relation.EqvGen.trans _ _ _ first rest

/-! ## Equation-free languages -/

/-- **An equation-free language has the identity as canonical forms**, on its object terms. -/
theorem identity_canonical (free : language.isEquationFree = true) :
    Canonical relEnv language id (fun term => isObjectPattern term) reading :=
  CanonicalDetermined.canonical
    { object := fun admitted => admitted
      determined := fun _ => rfl
      equivalent := fun _ => Relation.EqvGen.refl _
      same := fun _ equivalent => (objectEquivalent_iff_eq_of_isEquationFree free).mp equivalent
      closed := fun _ => rfl }

/-- **And its listing is coherent**: an equivalent state is the state itself. -/
theorem identity_coherent (free : language.isEquationFree = true) (reference : reading.rules = .reference := by rfl) :
    Coherent relEnv language fuel id (fun term => isObjectPattern term) List.singleton reading := by
  intro state redex witness contractum _ _ _ complete before _ valid
  rw [reference] at complete valid ⊢
  rw [← (objectEquivalent_iff_eq_of_isEquationFree free).mp before] at valid
  rw [enoughAt_singleton] at complete
  exact ⟨(witness, contractum), by rw [listedAt_singleton]; exact mem_stepsAt_of_enough complete valid,
    fun _ => rfl, rfl⟩

/-! ## Canonical forms as a parameter -/

/-- **Canonical forms with their domain and contract**, in a reading of the equations, which the front door takes for
a language with equations. -/
structure CanonicalForms (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) where
  /-- The reading of the equations the forms are canonical for: by default the syntax theory. -/
  reading : LanguageReading := .syntax
  canon : Pattern → Pattern
  domain : Pattern → Bool
  canonical : Canonical relEnv language canon domain reading
  /-- The presentations at which a state's steps are listed: by default the state itself. -/
  presentations : Pattern → List Pattern := List.singleton
  /-- The step labels the canonical forms keep. -/
  labels : StepLabel → Bool
  coherent : CoherentOn relEnv language fuel canon domain presentations labels reading

/-- Canonical forms that keep every label. -/
def CanonicalForms.ofCoherent {canon : Pattern → Pattern} {domain : Pattern → Bool}
    {presentations : Pattern → List Pattern} (canonical : Canonical relEnv language canon domain reading)
    (coherent : Coherent relEnv language fuel canon domain presentations reading) :
    CanonicalForms relEnv language fuel :=
  ⟨reading, canon, domain, canonical, presentations, fun _ => true, coherent.on _⟩

/-- Canonical forms that keep plain steps. -/
def CanonicalForms.ofPlain {canon : Pattern → Pattern} {domain : Pattern → Bool}
    {presentations : Pattern → List Pattern} (canonical : Canonical relEnv language canon domain reading)
    (coherent : CoherentPlain relEnv language fuel canon domain presentations reading) :
    CanonicalForms relEnv language fuel :=
  ⟨reading, canon, domain, canonical, presentations, plainLabel, coherent.on⟩

/-- The identity, for an equation-free language, in a reading of its equations with the reference relation for its
rules: all readings of the equations agree there. -/
def CanonicalForms.identity (free : language.isEquationFree = true) (equations : EquationReading := .syntax) :
    CanonicalForms relEnv language fuel :=
  .ofCoherent (reading := { equations := equations }) (identity_canonical free) (identity_coherent free)

/-- **Canonical forms, if any, are for a reading.** Without canonical forms, every reading of the equations with the
reference relation for the rules. -/
def FormsFor : Option (CanonicalForms relEnv language fuel) → LanguageReading → Prop
  | none, reading => reading.rules = .reference
  | some forms, reading => forms.reading = reading

/-- Whether canonical forms, if any, read the rules by the reference relation. -/
def formsReference : Option (CanonicalForms relEnv language fuel) → Bool
  | none => true
  | some forms => forms.reading.rules.isReference

/-- **Evidence about the reference relation holds in a reading** the forms are for, when they read the rules by it. -/
theorem reference_of_formsFor {forms : Option (CanonicalForms relEnv language fuel)} {reading : LanguageReading}
    (compatible : FormsFor forms reading) (reference : formsReference forms = true) : reading.rules = .reference := by
  cases forms with
  | none => exact compatible
  | some forms =>
    have same : forms.reading = reading := compatible
    rw [← same]
    exact RuleReading.eq_reference reference

/-- The reading canonical forms are for; the syntax theory without them. -/
def formsReading : Option (CanonicalForms relEnv language fuel) → LanguageReading
  | none => .syntax
  | some forms => forms.reading

theorem formsFor_formsReading (forms : Option (CanonicalForms relEnv language fuel)) :
    FormsFor forms (formsReading forms) := by
  cases forms with
  | none => rfl
  | some forms => rfl

theorem formsFor_none {reading : LanguageReading} (reference : reading.rules = .reference := by rfl) :
    FormsFor (none : Option (CanonicalForms relEnv language fuel)) reading :=
  reference

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
