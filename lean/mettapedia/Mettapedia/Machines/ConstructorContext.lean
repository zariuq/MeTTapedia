import Mettapedia.GSLT.LanguageDef.ContextStackEvaluation
import Mathlib.Data.List.Induction

/-!
# Constructor contexts and their summary actions

Contexts list frames from outermost to innermost. A frame stores the already
evaluated children on either side of one hole. The core laws do not assume a
particular value representation, summary algebra, or constructor arity.

A summary algebra must respect constructor application. Its action on a hole
then composes along contexts. The action requires neither commutativity nor
associativity of the constructor's summary function. Allocation-dependent
parameters belong in the frame label. The suffix pass computes every cell's
summary, with exactly one summary application per cell.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConstructorContext

universe u v w

structure Frame (Label : Type u) (Value : Type v) where
  label : Label
  before : List Value
  after : List Value
  deriving Repr

variable {Label : Type u} {Value : Type v} {Summary : Type w}

namespace Frame

def apply (build : Label → List Value → Value) (frame : Frame Label Value)
    (hole : Value) : Value :=
  build frame.label (frame.before ++ hole :: frame.after)

def map (f : Value → Summary) (frame : Frame Label Value) : Frame Label Summary :=
  ⟨frame.label, frame.before.map f, frame.after.map f⟩

@[simp] theorem map_map {Other : Type*} (f : Value → Summary) (g : Summary → Other)
    (frame : Frame Label Value) :
    (frame.map f).map g = frame.map (g ∘ f) := by
  cases frame
  simp [map, List.map_map]

end Frame

/-- The outermost frame is first. The empty context is a genuine hole. -/
def plug (build : Label → List Value → Value) (frames : List (Frame Label Value))
    (value : Value) : Value :=
  frames.foldr (Frame.apply build) value

@[simp] theorem plug_nil (build : Label → List Value → Value) (value : Value) :
    plug build [] value = value := rfl

@[simp] theorem plug_cons (build : Label → List Value → Value)
    (frame : Frame Label Value) (rest : List (Frame Label Value)) (value : Value) :
    plug build (frame :: rest) value = frame.apply build (plug build rest value) := rfl

/-- Context concatenation acts as ordered composition. -/
theorem plug_append (build : Label → List Value → Value)
    (outer inner : List (Frame Label Value)) (value : Value) :
    plug build (outer ++ inner) value = plug build outer (plug build inner value) := by
  simp [plug, List.foldr_append]

/-- The executor records frames innermost first. -/
theorem stack_eq_plug (build : Label → List Value → Value)
    (frames : List (Frame Label Value)) (value : Value) :
    GSLT.LanguageDef.ContextStackEvaluation.plug
      (frames.reverse.map (Frame.apply build)) value = plug build frames value := by
  induction frames using List.reverseRecOn generalizing value with
  | nil => rfl
  | append_singleton frames frame ih =>
      simp only [List.reverse_append, List.reverse_singleton,
        List.map_cons, List.singleton_append,
        GSLT.LanguageDef.ContextStackEvaluation.plug_cons]
      rw [ih, plug_append]
      rfl

/-- The existing tail-recursion-modulo-context evaluator, instantiated with
these constructor frames, returns the same completed value at every fuel. -/
theorem with_contexts_refines {Call : Type*}
    (build : Label → List Value → Value)
    (step : Call → Option (GSLT.LanguageDef.ContextStackEvaluation.Step Value Call))
    (fuel : Nat) (frames : List (Frame Label Value)) (call : Call) :
    GSLT.LanguageDef.ContextStackEvaluation.withContexts step fuel
      (frames.reverse.map (Frame.apply build)) call =
    (GSLT.LanguageDef.ContextStackEvaluation.direct step fuel call).map (plug build frames) := by
  rw [GSLT.LanguageDef.ContextStackEvaluation.withContexts_eq]
  congr 1
  funext value
  exact stack_eq_plug build frames value

/-- Compatibility of two constructor algebras; instantiated below by actual
folds and also usable for representation changes. -/
structure SummaryAlgebra (Label : Type u) (Value : Type v) (Summary : Type w) where
  build : Label → List Value → Value
  observe : Value → Summary
  combine : Label → List Summary → Summary
  build_observe : ∀ label children,
    observe (build label children) = combine label (children.map observe)

namespace SummaryAlgebra

variable (A : SummaryAlgebra Label Value Summary)

def act (frame : Frame Label Value) (hole : Summary) : Summary :=
  (frame.map A.observe).apply A.combine hole

/-- A frame acts on the hole's summary. The fixed children are summarized
once; their order and the hole position are retained. -/
theorem observe_frame (frame : Frame Label Value) (value : Value) :
    A.observe (frame.apply A.build value) = A.act frame (A.observe value) := by
  simp [Frame.apply, A.build_observe, act, Frame.map, List.map_append]

/-- An observer-respecting constructor algebra respects every context. -/
theorem observe_plug (frames : List (Frame Label Value)) (value : Value) :
    A.observe (plug A.build frames value) = frames.foldr A.act (A.observe value) := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      rw [plug_cons, A.observe_frame, ih]
      rfl

/-- The summary action has the same ordered composition law as contexts. -/
theorem action_append (outer inner : List (Frame Label Value)) (s : Summary) :
    (outer ++ inner).foldr A.act s = outer.foldr A.act (inner.foldr A.act s) := by
  rw [List.foldr_append]

/-- One backward pass returns every cell's summary, including the filled
value as the final entry. -/
def summaries (frames : List (Frame Label Value)) (value : Value) : List Summary :=
  frames.scanr A.act (A.observe value)

theorem summaries_at (frames : List (Frame Label Value)) (value : Value)
    (index : Nat) (within : index ≤ frames.length) :
    (A.summaries frames value)[index]? =
      some (A.observe (plug A.build (frames.drop index) value)) := by
  rw [summaries, List.getElem?_scanr_of_lt (by omega), A.observe_plug]

/-- Instrument the summary applications, not the surrounding allocator. -/
def meteredSummary (frames : List (Frame Label Value)) (value : Value) : Summary × Nat :=
  frames.foldr (fun frame result => (A.act frame result.1, result.2 + 1))
    (A.observe value, 0)

theorem summary_pass_exact (frames : List (Frame Label Value)) (value : Value) :
    A.meteredSummary frames value = (A.observe (plug A.build frames value), frames.length) := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      change (A.act frame (A.meteredSummary rest value).1,
        (A.meteredSummary rest value).2 + 1) = _
      rw [ih, plug_cons, A.observe_frame]
      rfl

end SummaryAlgebra

/-- Earlier effectful children have already run in the original order. The
last call alone supplies the hole. State includes traces or handler state if
these are observations of the language. -/
theorem evaluated_prefix_last_call {State : Type*}
    (build : Label → List Value → Value) (label : Label)
    (earlier : State → List Value × State) (last : State → Value × State)
    (suffix : List Value) (state : State) :
    (let (values, state') := earlier state
     let (answer, state'') := last state'
     (build label (values ++ answer :: suffix), state'')) =
    (let (values, state') := earlier state
     let frame : Frame Label Value := ⟨label, values, suffix⟩
     let result := last state'
     (frame.apply build result.1, result.2)) := by
  rcases h : earlier state with ⟨values, next⟩
  cases last next
  rfl

/-- Apply a context to each result of an arbitrary lawful effectful producer.
The producer is unchanged: only completed result values are mapped. -/
def mapAnswers {M : Type v → Type w} [Functor M]
    (build : Label → List Value → Value) (frames : List (Frame Label Value))
    (producer : M Value) : M Value := (plug build frames) <$> producer

theorem mapAnswers_append {M : Type v → Type w} [Functor M] [LawfulFunctor M]
    (build : Label → List Value → Value) (outer inner : List (Frame Label Value))
    (producer : M Value) :
    mapAnswers build (outer ++ inner) producer =
      mapAnswers build outer (mapAnswers build inner producer) := by
  simp only [mapAnswers, Functor.map_map]
  congr 1
  funext value
  exact plug_append build outer inner value

namespace Controls

/-- Context actions need not commute. -/
theorem order_matters :
    let build : Nat → List Nat → Nat := fun label xs => label + 2 * xs.sum
    let a : Frame Nat Nat := ⟨1, [], []⟩
    let b : Frame Nat Nat := ⟨2, [], []⟩
    plug build [a, b] 0 ≠ plug build [b, a] 0 := by decide

/-- Selecting a last call does not license moving it past another effect. -/
theorem reordering_effects_changes_answer :
    let first : Nat → Nat × Nat := fun n => (n, n + 1)
    let last : Nat → Nat × Nat := fun n => (n, 2 * n)
    (let a := first 1; let b := last a.2; ([a.1, b.1], b.2)) ≠
    (let b := last 1; let a := first b.2; ([a.1, b.1], a.2)) := by decide

end Controls

end Mettapedia.Machines.ConstructorContext
