import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
import Mettapedia.OSLF.MeTTaIL.PatternCountability

/-!
# The authored presentation meets the step

The authored event presentation (`Presentation.language`) has one rewrite, `Execute`: a request
`Request s f` becomes `At t` when `prepared(s, f, t)` and `permitted(s, f)` hold. Its OSLF is
generated from its own reduction span (`langSpanUsing`); `Presentation.diamond_reads` reads that
diamond off the root executor. The step has its own span, the admitted firings
(`StepSpan.firingSpan`). This module interprets the presentation into an arbitrary step, through
an exact encoding of states and firings (`Presentation.Encoding`) and the step's own preparation
and admission (`Presentation.effectQueries` at `P.eventAdmission`), and compares the two spans.

## The presentation's steps are the step's admitted firings

`presentation_step_iff`: under the step's queries, a presentation step is exactly an admitted
firing, from its request to its result at rest. Nothing else steps: a state at rest is inert
(`at_rest_no_step`), and so is every pattern that is not a request.

## The two diamonds agree after choosing a firing

The presentation authors execution, not the choice of a firing. That choice is the span
`chooseSpan`, from a state at rest to each of its requests, admitted or not. Then, for every
predicate on patterns:

* `diamond_meets_step`: possibility over firings is the pullback, along the state's code at
  rest, of possibility over choices of possibility over the presentation;
* `forwardBox_meets_step`: successor necessity, likewise;
* `predecessorBox_meets_step`: predecessor necessity is the pullback of the presentation's
  predecessor necessity of the choices' predecessor necessity (the composite read backward);
* `diamond_meets_successors`: through `StepSpan.firing_diamond_eq`, the same for the successor
  relation;
* `diamond_reads_at_request`: through `Presentation.diamond_reads`, the presentation's generated
  diamond at a request is exactly "this firing is admitted and its result satisfies the
  observation".

So the exact observation on which they agree is `atOf* ∘ ◇_choose ∘ ◇_presentation`: the step's
possibility is the presentation's possibility after an existential choice of the firing.

## Controls: neither diamond alone is the other

* `presentation_alone_misses_the_step`: at a state's own code the presentation's diamond is false
  for every observation (`at_rest_inert`), while the step can fire there.
* `request_le_state` and `request_strictly_stronger`: at a request the presentation's diamond
  implies the step's at the state, and is strictly stronger: a refused firing beside an admitted
  one.
* Both, on a real store effect (`Controls`): two tell firings over Boolean equation stores, coded
  by window 9's exact store codec, one admitted and one refused at the empty store.

## Boundary: the first-order step's firings have no exact code

The comparison needs an exact encoding of firings into patterns. A first-order firing
(`AnnotatedRuns.Firing`) carries predicate queries, each with a region `S → T → Bool`. When the
substitutions are infinite and terms exist, there are uncountably many firings, while patterns are
countable, so no injective code exists (`no_pattern_code`). The presentation therefore meets the
first-order step through firings without predicate queries; queries add no successor
(`ProgramAdequacy.program_succ_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.PresentationMeetsStep

open Interface
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities
open Presentation
open StepSpan

universe uO uT uH uOcc uS uF

/-! ## The authored rule matches requests only -/

/-- The presentation's one rewrite, `Execute`. -/
def executeRule : RewriteRule := language.rewrites[0]'(by decide +kernel)

theorem rewrites_eq : language.rewrites = [executeRule] := rfl

/-- The left side of `Execute` matches nothing but a request. -/
theorem matchRequest_nil {p : Pattern} (notRequest : ∀ a b, p ≠ request a b) :
    matchPattern (.apply "Request" [.fvar "s", .fvar "f"]) p = [] := by
  cases p with
  | apply c args =>
      by_cases named : c = "Request"
      · subst named
        match args, notRequest with
        | [], _ => simp [matchPattern]
        | [_], _ => simp [matchPattern]
        | [a, b], notRequest => exact (notRequest a b rfl).elim
        | _ :: _ :: _ :: _, _ => simp [matchPattern]
      · have different : "Request" ≠ c := fun same => named same.symm
        simp [matchPattern, different]
  | bvar _ => simp [matchPattern]
  | fvar _ => simp [matchPattern]
  | lambda _ _ => simp [matchPattern]
  | multiLambda _ _ _ => simp [matchPattern]
  | subst _ _ => simp [matchPattern]
  | collection _ _ _ => simp [matchPattern]

/-- **Only requests step**, under every relation environment. -/
theorem no_step_unless_request (relations : RelationEnv) {p q : Pattern}
    (step : langSemanticReducesUsing relations language p q) : ∃ a b, p = request a b := by
  have member : q ∈ rewriteStepWithPremisesUsing relations language p :=
    (root_iff_semantic relations p q).mpr step
  by_contra notRequest
  have notRequest' : ∀ a b, p ≠ request a b := fun a b same => notRequest ⟨a, b, same⟩
  have unmatched : Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule language
      executeRule p = [] := by
    change matchPattern (.apply "Request" [.fvar "s", .fvar "f"]) p = []
    exact matchRequest_nil notRequest'
  simp only [rewriteStepWithPremisesUsing, rewrites_eq, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, applyRuleWithPremisesUsing, unmatched] at member
  exact List.not_mem_nil member

/-- **A state at rest never steps**, under every relation environment. -/
theorem at_rest_no_step (relations : RelationEnv) (t q : Pattern) :
    ¬ langSemanticReducesUsing relations language (atState t) q := by
  intro step
  obtain ⟨a, b, same⟩ := no_step_unless_request relations step
  have named := (Pattern.apply.inj same).1
  exact absurd named (by decide)

/-! ## The presentation interpreted into a step -/

section Interpretation

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}
  {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **A state at rest**: the code of a state, as the presentation's process `At`. -/
def atOf (code : Encoding State Firing) (s : State) : Pattern :=
  atState (code.state.view (sort := ()) s)

/-- **A request**: the codes of a state and of one of its firings. -/
def requestOf (code : Encoding State Firing) (c : (s : State) × Firing s) : Pattern :=
  request (code.state.view (sort := ()) c.1) (code.firing.view (sort := ()) c)

theorem atOf_injective (code : Encoding State Firing) : Function.Injective (atOf code) := by
  intro s t same
  have parts := Pattern.apply.inj same
  exact code.state.view_injective (List.cons.inj parts.2).1

theorem requestOf_injective (code : Encoding State Firing) :
    Function.Injective (requestOf code) := by
  intro c d same
  have parts := Pattern.apply.inj same
  exact code.firing.view_injective (List.cons.inj (List.cons.inj parts.2).2).1

/-- **Choosing a firing**: from a state at rest to each of its requests, admitted or not. The
presentation does not author this half. -/
def chooseSpan (code : Encoding State Firing) : ReductionSpan Pattern where
  Edge := (s : State) × Firing s
  source c := atOf code c.1
  target c := requestOf code c

variable (P : Interface.Step X O State Firing) (code : Encoding State Firing)
  (decision : Decisions P.effectCore P.eventAdmission)

/-- The step's preparation and admission, as the presentation's relation queries. -/
abbrev relations : RelationEnv :=
  (effectQueries P.effectCore P.eventAdmission code decision).relations

/-- **The presentation's reduction span** under the step's queries. -/
abbrev presentationSpan : ReductionSpan Pattern := langSpanUsing (relations P code decision) language

/-- **The presentation's steps are exactly the step's admitted firings**, from the request to the
result at rest. -/
theorem presentation_step_iff {p q : Pattern} :
    langSemanticReducesUsing (relations P code decision) language p q ↔
      ∃ (c : (s : State) × Firing s) (a : P.Admits c.2),
        p = requestOf code c ∧ q = atOf code (P.result c.2 a) := by
  constructor
  · intro step
    obtain ⟨a, b, rfl⟩ := no_step_unless_request _ step
    have member := (root_iff_semantic _ (request a b) q).mpr step
    obtain ⟨c, p, sourceEq, firingEq, allowed, targetEq⟩ :=
      execution_reflects P.effectCore P.eventAdmission code decision member
    refine ⟨c, (P.eventAdmission_iff c.2 p).mp allowed, ?_, ?_⟩
    · subst sourceEq
      subst firingEq
      rfl
    · rw [targetEq]
      rfl
  · rintro ⟨⟨s, f⟩, a, rfl, rfl⟩
    apply (root_iff_semantic _ _ _).mp
    exact (execution_iff_prepared P.effectCore P.eventAdmission code decision f).mpr
      ⟨P.prepares a, (P.eventAdmission_iff f _).mpr a, rfl⟩

/-- The presentation's generated diamond is OSLF's possibility over its reduction span. -/
theorem langDiamond_iff (ψ : Pattern → Prop) (p : Pattern) :
    langDiamondUsing (relations P code decision) language (observation (relations P code decision) ψ) p ↔
      derivedDiamond (presentationSpan P code decision) ψ p := by
  rw [langDiamondUsing_spec]
  constructor
  · rintro ⟨q, step, holds⟩
    exact ⟨⟨(p, q), step⟩, rfl, holds⟩
  · rintro ⟨⟨⟨p', q⟩, step⟩, rfl, holds⟩
    exact ⟨q, step, holds⟩

/-- Possibility over the presentation, pointwise. -/
theorem presentation_diamond_iff (ψ : Pattern → Prop) (p : Pattern) :
    derivedDiamond (presentationSpan P code decision) ψ p ↔
      ∃ (c : (s : State) × Firing s) (a : P.Admits c.2),
        p = requestOf code c ∧ ψ (atOf code (P.result c.2 a)) := by
  constructor
  · rintro ⟨⟨⟨p', q⟩, step⟩, rfl, holds⟩
    obtain ⟨c, a, sourceEq, targetEq⟩ := (presentation_step_iff P code decision).mp step
    refine ⟨c, a, sourceEq, ?_⟩
    have reached : q = atOf code (P.result c.2 a) := targetEq
    rw [← reached]
    exact holds
  · rintro ⟨c, a, rfl, holds⟩
    exact ⟨⟨(requestOf code c, atOf code (P.result c.2 a)),
      (presentation_step_iff P code decision).mpr ⟨c, a, rfl, rfl⟩⟩, rfl, holds⟩

/-- **At a request, the presentation's possibility reads exactly that firing**: it is admitted
and its result satisfies the observation. -/
theorem request_diamond_iff (ψ : Pattern → Prop) {s : State} (f : Firing s) :
    derivedDiamond (presentationSpan P code decision) ψ (requestOf code ⟨s, f⟩) ↔
      ∃ a : P.Admits f, ψ (atOf code (P.result f a)) := by
  rw [presentation_diamond_iff]
  constructor
  · rintro ⟨c, a, same, holds⟩
    have equal : c = ⟨s, f⟩ := (requestOf_injective code same).symm
    subst equal
    exact ⟨a, holds⟩
  · rintro ⟨a, holds⟩
    exact ⟨⟨s, f⟩, a, rfl, holds⟩

/-- **`Presentation.diamond_reads` at a request**: the generated diamond, read off the root
executor, holds exactly when this firing is admitted and its result satisfies the observation. -/
theorem diamond_reads_at_request (ψ : Pattern → Prop) {s : State} (f : Firing s) :
    langDiamondUsing (relations P code decision) language (observation (relations P code decision) ψ)
        (requestOf code ⟨s, f⟩) ↔
      ∃ a : P.Admits f, ψ (atOf code (P.result f a)) := by
  rw [diamond_reads]
  constructor
  · rintro ⟨q, member, holds⟩
    have step := (root_iff_semantic _ _ _).mp member
    obtain ⟨c, a, same, reached⟩ := (presentation_step_iff P code decision).mp step
    have equal : c = ⟨s, f⟩ := (requestOf_injective code same).symm
    subst equal
    exact ⟨a, reached ▸ holds⟩
  · rintro ⟨a, holds⟩
    refine ⟨_, (root_iff_semantic _ _ _).mpr ((presentation_step_iff P code decision).mpr
      ⟨⟨s, f⟩, a, rfl, rfl⟩), holds⟩

/-- Possibility over choices, at a state at rest: some firing's request satisfies it. -/
theorem choose_diamond_iff (χ : Pattern → Prop) (s : State) :
    derivedDiamond (chooseSpan code) χ (atOf code s) ↔ ∃ f : Firing s, χ (requestOf code ⟨s, f⟩) := by
  constructor
  · rintro ⟨⟨s', f⟩, same, holds⟩
    have equal : s' = s := atOf_injective code same
    subst equal
    exact ⟨f, holds⟩
  · rintro ⟨f, holds⟩
    exact ⟨⟨s, f⟩, rfl, holds⟩

/-- Successor necessity over choices, at a state at rest: every firing's request satisfies it. -/
theorem choose_forwardBox_iff (χ : Pattern → Prop) (s : State) :
    derivedForwardBox (chooseSpan code) χ (atOf code s) ↔ ∀ f : Firing s, χ (requestOf code ⟨s, f⟩) := by
  constructor
  · intro all f
    exact all ⟨s, f⟩ rfl
  · rintro all ⟨s', f⟩ same
    have equal : s' = s := atOf_injective code same
    subst equal
    exact all f

/-- Possibility over the step's firings, pointwise. -/
theorem firing_diamond_iff (φ : State → Prop) (s : State) :
    derivedDiamond (firingSpan P) φ s ↔ ∃ (f : Firing s) (a : P.Admits f), φ (P.result f a) := by
  constructor
  · rintro ⟨⟨s', f, a⟩, rfl, holds⟩
    exact ⟨f, a, holds⟩
  · rintro ⟨f, a, holds⟩
    exact ⟨⟨s, f, a⟩, rfl, holds⟩

/-- **Possibility: the step is the presentation after a choice of firing.** -/
theorem diamond_meets_step (ψ : Pattern → Prop) :
    pb (atOf code) (derivedDiamond (chooseSpan code) (derivedDiamond (presentationSpan P code decision) ψ)) =
      derivedDiamond (firingSpan P) (pb (atOf code) ψ) := by
  funext s
  apply propext
  change derivedDiamond (chooseSpan code) _ (atOf code s) ↔ _
  rw [choose_diamond_iff, firing_diamond_iff]
  constructor
  · rintro ⟨f, possible⟩
    obtain ⟨a, holds⟩ := (request_diamond_iff P code decision ψ f).mp possible
    exact ⟨f, a, holds⟩
  · rintro ⟨f, a, holds⟩
    exact ⟨f, (request_diamond_iff P code decision ψ f).mpr ⟨a, holds⟩⟩

/-- **Successor necessity: likewise.** -/
theorem forwardBox_meets_step (ψ : Pattern → Prop) :
    pb (atOf code)
        (derivedForwardBox (chooseSpan code) (derivedForwardBox (presentationSpan P code decision) ψ)) =
      derivedForwardBox (firingSpan P) (pb (atOf code) ψ) := by
  funext s
  apply propext
  change derivedForwardBox (chooseSpan code) _ (atOf code s) ↔ _
  rw [choose_forwardBox_iff]
  constructor
  · rintro all ⟨s', f, a⟩ rfl
    exact all f ⟨(requestOf code ⟨s', f⟩, atOf code (P.result f a)),
      (presentation_step_iff P code decision).mpr ⟨⟨s', f⟩, a, rfl, rfl⟩⟩ rfl
  · intro all f ⟨⟨p, q⟩, step⟩ same
    obtain ⟨c, a, sourceEq, targetEq⟩ := (presentation_step_iff P code decision).mp step
    have at_request : p = requestOf code ⟨s, f⟩ := same
    have equal : c = ⟨s, f⟩ := requestOf_injective code (sourceEq.symm.trans at_request)
    subst equal
    have reached : q = atOf code (P.result f a) := targetEq
    show ψ q
    rw [reached]
    exact all ⟨s, f, a⟩ rfl

/-- **Predecessor necessity: the composite read backward.** -/
theorem predecessorBox_meets_step (ψ : Pattern → Prop) :
    pb (atOf code)
        (derivedBox (presentationSpan P code decision) (derivedBox (chooseSpan code) ψ)) =
      derivedBox (firingSpan P) (pb (atOf code) ψ) := by
  funext s
  apply propext
  constructor
  · rintro all ⟨s', f, a⟩ reached
    have step := (presentation_step_iff P code decision).mpr ⟨⟨s', f⟩, a, rfl, rfl⟩
    exact all ⟨(requestOf code ⟨s', f⟩, atOf code (P.result f a)), step⟩
      (congrArg (atOf code) reached) ⟨s', f⟩ rfl
  · intro all ⟨⟨p, q⟩, step⟩ arrives c chosen
    obtain ⟨d, a, sourceEq, targetEq⟩ := (presentation_step_iff P code decision).mp step
    have equal : c = d := requestOf_injective code (chosen.trans sourceEq)
    subst equal
    have result : P.result c.2 a = s := atOf_injective code (targetEq.symm.trans arrives)
    exact all ⟨c.1, c.2, a⟩ result

/-- **Through `StepSpan.firing_diamond_eq`, the same for the successor relation.** -/
theorem diamond_meets_successors (ψ : Pattern → Prop) :
    pb (atOf code) (derivedDiamond (chooseSpan code) (derivedDiamond (presentationSpan P code decision) ψ)) =
      derivedDiamond (FragmentsOfTheStep.TransitionMaps.span (Succ P)) (pb (atOf code) ψ) := by
  rw [diamond_meets_step, firing_diamond_eq]

/-! ## Controls: neither diamond alone is the other -/

/-- **A state at rest is inert in the presentation**, for every observation. -/
theorem at_rest_inert (ψ : Pattern → Prop) (s : State) :
    ¬ derivedDiamond (presentationSpan P code decision) ψ (atOf code s) := by
  rintro ⟨⟨⟨p, q⟩, step⟩, same, _⟩
  have rest : p = atOf code s := same
  subst rest
  exact at_rest_no_step _ _ q step

/-- **The presentation alone misses the step**: where a firing is admitted, the step can fire,
and the presentation's diamond at the state's own code is false. -/
theorem presentation_alone_misses_the_step {s : State} {f : Firing s} (a : P.Admits f) :
    derivedDiamond (firingSpan P) (fun _ => True) s ∧
      ¬ derivedDiamond (presentationSpan P code decision) (fun _ => True) (atOf code s) :=
  ⟨(firing_diamond_iff P (fun _ => True) s).mpr ⟨f, a, trivial⟩,
    at_rest_inert P code decision (fun _ => True) s⟩

/-- **At a request, the presentation's possibility implies the step's at the state.** -/
theorem request_le_state (φ : State → Prop) {s : State} (f : Firing s)
    (possible : derivedDiamond (presentationSpan P code decision) (di (atOf code) φ)
      (requestOf code ⟨s, f⟩)) :
    derivedDiamond (firingSpan P) φ s := by
  obtain ⟨a, t, same, holds⟩ := (request_diamond_iff P code decision _ f).mp possible
  have equal : t = P.result f a := atOf_injective code same
  subst equal
  exact (firing_diamond_iff P φ s).mpr ⟨f, a, holds⟩

/-- **The request's possibility is strictly stronger**: a refused firing beside an admitted one. -/
theorem request_strictly_stronger {s : State} {f g : Firing s} (refused : ¬ P.Admits f)
    (admitted : P.Admits g) :
    derivedDiamond (firingSpan P) (fun _ => True) s ∧
      ¬ derivedDiamond (presentationSpan P code decision) (di (atOf code) (fun _ => True))
        (requestOf code ⟨s, f⟩) ∧
      derivedDiamond (presentationSpan P code decision) (di (atOf code) (fun _ => True))
        (requestOf code ⟨s, g⟩) := by
  refine ⟨(firing_diamond_iff P _ s).mpr ⟨g, admitted, trivial⟩, fun possible => ?_,
    (request_diamond_iff P code decision _ g).mpr ⟨admitted, _, rfl, trivial⟩⟩
  obtain ⟨a, _⟩ := (request_diamond_iff P code decision _ f).mp possible
  exact refused a

end Interpretation

/-! ## Controls on a real store effect -/

namespace Controls

open Presentation.Controls (frame Store effect prepares statePresentation storePattern readStore
  readStore_pattern boolPattern readBool readBool_pattern)

/-- **Two tell firings at every Boolean equation store**: both tell `true = false`, as window 9's
store effect does. -/
def twoTells : EffectCore frame Nat Store (fun _ => Bool) where
  frame s := effect.frame s
  knowledge s := effect.knowledge s
  present s := effect.present s
  selection {s} _ := effect.selection (s := s) ()
  target {s} _ := effect.target (s := s) ()
  extension {s} _ := effect.extension (s := s) ()
  information {s} _ := effect.information (s := s) ()
  information_refines {s} _ := effect.information_refines (s := s) ()
  Shapes {s} _ := effect.Shapes (s := s) ()
  preparedResult {s} _ p := effect.preparedResult (s := s) () p
  present_preparedResult {s} _ p := effect.present_preparedResult (s := s) () p
  preparedSettle {s} _ p := effect.preparedSettle (s := s) () p
  result_refines {s} _ p := effect.result_refines (s := s) () p

/-- Admission: the firing `true` where the store lacks the equation; `false` never. -/
def twoTellsStep : Interface.Step frame Nat Store (fun _ => Bool) :=
  Interface.Step.ofEffect twoTells fun {s} b _ => b = true ∧ (true, false) ∉ s

/-- The firings' codes: the store and the bit. -/
def firingPresentation : PatternPresentation ((_ : Store) × Bool) where
  key := ⟨"tcalc.two-tells", 1⟩
  expand p := match p with
    | .apply "Tell" [s, b] => (readStore s).bind fun store => (readBool b).map fun bit => ⟨store, bit⟩
    | _ => none
  view c := .apply "Tell" [storePattern c.1, boolPattern c.2]
  expand_view c := by
    rcases c with ⟨s, b⟩
    simp [readStore_pattern]

def encoding : Encoding Store (fun _ => Bool) := ⟨statePresentation, firingPresentation⟩

noncomputable def decisions : Decisions twoTellsStep.effectCore twoTellsStep.eventAdmission :=
  Decisions.ofClassical _ _

theorem tell_admitted : twoTellsStep.Admits (s := []) true :=
  ⟨prepares [] (), rfl, by simp⟩

theorem silent_refused : ¬ twoTellsStep.Admits (s := []) false := by
  rintro ⟨_, bad, _⟩
  cases bad

/-- **Control, the presentation alone**: at the empty store the step fires, and the presentation's
diamond at the store's own code is false. -/
theorem empty_store_presentation_alone :
    derivedDiamond (firingSpan twoTellsStep) (fun _ => True) [] ∧
      ¬ derivedDiamond (presentationSpan twoTellsStep encoding decisions) (fun _ => True)
        (atOf encoding []) :=
  presentation_alone_misses_the_step twoTellsStep encoding decisions tell_admitted

/-- **Control, the request**: at the empty store the step fires; the request of the refused
firing has no execution, and the request of the admitted one has. -/
theorem empty_store_request_strict :
    derivedDiamond (firingSpan twoTellsStep) (fun _ => True) [] ∧
      ¬ derivedDiamond (presentationSpan twoTellsStep encoding decisions)
        (di (atOf encoding) (fun _ => True)) (requestOf encoding ⟨[], false⟩) ∧
      derivedDiamond (presentationSpan twoTellsStep encoding decisions)
        (di (atOf encoding) (fun _ => True)) (requestOf encoding ⟨[], true⟩) :=
  request_strictly_stronger twoTellsStep encoding decisions silent_refused tell_admitted

/-- **Positive: the two diamonds agree after the choice**, at the empty store, for the observation
"the store holds the told equation". -/
theorem empty_store_agrees :
    pb (atOf encoding) (derivedDiamond (chooseSpan encoding)
        (derivedDiamond (presentationSpan twoTellsStep encoding decisions)
          (di (atOf encoding) fun s => (true, false) ∈ s))) [] := by
  rw [diamond_meets_step]
  refine (firing_diamond_iff twoTellsStep _ []).mpr ⟨true, tell_admitted, _, rfl, ?_⟩
  show (true, false) ∈ ([] : Store) ++ [(true, false)]
  simp

end Controls

/-! ## Boundary: first-order firings have no exact code -/

/-- **No exact code for the first-order step's firings**: with infinitely many substitutions and
some term, the predicate query regions `S → T → Bool` make the first-order firings uncountable, so
no injective code into patterns exists. -/
theorem no_pattern_code {T : Type*} {S : Type*} {O : Type*} [Infinite S] [Nonempty T]
    (rule : RuleInstance T) (selection : ConstraintMultisetRewriting.Selection O) :
    ¬ ∃ code : AnnotatedRuns.Firing T S O → Pattern, Function.Injective code := by
  classical
  rintro ⟨code, injective⟩
  let e : ℕ ↪ S := Infinite.natEmbedding S
  let firing : Set ℕ → AnnotatedRuns.Firing T S O := fun A =>
    ⟨rule, [⟨fun s _ => decide (∃ n ∈ A, e n = s), ∅⟩], selection⟩
  have firingInjective : Function.Injective firing := by
    intro A B same
    obtain ⟨t⟩ := ‹Nonempty T›
    have queries := congrArg AnnotatedRuns.Firing.queries same
    simp only [firing, List.cons.injEq, PredicateQueryAdmission.Query.mk.injEq, and_true] at queries
    ext n
    have atN := congrFun (congrFun queries (e n)) t
    simp only [decide_eq_decide] at atN
    constructor
    · intro inA
      obtain ⟨m, inB, hit⟩ := atN.mp ⟨n, inA, rfl⟩
      rw [e.injective hit] at inB
      exact inB
    · intro inB
      obtain ⟨m, inA, hit⟩ := atN.mpr ⟨n, inB, rfl⟩
      rw [e.injective hit] at inA
      exact inA
  obtain ⟨g, gInjective⟩ := Countable.exists_injective_nat Pattern
  exact Function.cantor_injective (g ∘ code ∘ firing) (gInjective.comp (injective.comp firingInjective))

#print axioms matchRequest_nil
#print axioms no_step_unless_request
#print axioms at_rest_no_step
#print axioms presentation_step_iff
#print axioms langDiamond_iff
#print axioms request_diamond_iff
#print axioms diamond_reads_at_request
#print axioms diamond_meets_step
#print axioms forwardBox_meets_step
#print axioms predecessorBox_meets_step
#print axioms diamond_meets_successors
#print axioms at_rest_inert
#print axioms presentation_alone_misses_the_step
#print axioms request_le_state
#print axioms request_strictly_stronger
#print axioms Controls.empty_store_presentation_alone
#print axioms Controls.empty_store_request_strict
#print axioms Controls.empty_store_agrees
#print axioms no_pattern_code

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.PresentationMeetsStep
