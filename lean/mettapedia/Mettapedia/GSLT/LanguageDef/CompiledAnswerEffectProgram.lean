import Mettapedia.GSLT.Dynamics.AnswerEffect

/-!
# Compiled answer-effect control around deterministic islands

This module separates two independent parts of an evaluator:

* an answer-effect control program supplies semantic zero, finite choice, and
  sequencing;
* an indexed family `Op` supplies deterministic, total operations.

The deterministic operations are intentionally abstract.  They may be scalar
VM fragments, constructor observers, space-index probes, or another verified
backend.  Changing a source calculus or physical evaluator does not change the
answer-control interface.

`Source` is a small source calculus with an explicit guarded computation.
`Source.compile` lowers a guard to a deterministic Boolean operation followed
by answer-effect control.  Exact denotational adequacy proves both preservation
and no invention at the declared answer profile.  Naturality then transports
the same compiled program from ordered streams to occurrence bags or finite
support through the existing answer-effect morphisms.

Physical execution is partial even though semantic operations are total.
`none` means that a particular realization declined an operation; it is never
identified with semantic zero.  The separating example at the end makes this
boundary executable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectProgram

open Mettapedia.GSLT.Dynamics.AnswerEffects

universe u

/-- A finite answer-control program whose leaves may invoke deterministic,
response-indexed operations. -/
inductive Program (Op : Type → Type) (Answer : Type u) : Type (max u 1) where
  | pure (answer : Answer)
  | zero
  | choice (left right : Program Op Answer)
  | perform {Response : Type} (operation : Op Response)
      (next : Response → Program Op Answer)

namespace Program

/-- Dependent sequencing preserves answer control and threads the
continuation through deterministic operations. -/
def bind {Op : Type → Type} {Answer OtherAnswer : Type u}
    (program : Program Op Answer)
    (next : Answer → Program Op OtherAnswer) : Program Op OtherAnswer :=
  match program with
  | .pure answer => next answer
  | .zero => .zero
  | .choice left right => .choice (bind left next) (bind right next)
  | .perform operation continuation =>
      .perform operation fun response => bind (continuation response) next

/-- A Boolean deterministic island controls only whether the continuation has
an answer.  False is semantic zero, not an inert datum. -/
def guard {Op : Type → Type} {Answer : Type u}
    (test : Op Bool) (next : Program Op Answer) : Program Op Answer :=
  .perform test fun accepted => if accepted then next else .zero

/-- Interpret deterministic operations and answer control independently. -/
def denote {Op : Type → Type} {Answer : Type u}
    (effect : AnswerEffect.{u})
    (semantics : {Response : Type} → Op Response → Response) :
    Program Op Answer → effect.Carrier Answer
  | .pure answer => effect.pure answer
  | .zero => effect.empty
  | .choice left right =>
      effect.choice (denote effect semantics left)
        (denote effect semantics right)
  | .perform operation next => denote effect semantics (next (semantics operation))

@[simp] theorem denote_pure {Op : Type → Type} {Answer : Type u}
    (effect : AnswerEffect.{u})
    (semantics : {Response : Type} → Op Response → Response)
    (answer : Answer) :
    denote effect semantics (.pure answer) = effect.pure answer :=
  rfl

@[simp] theorem denote_zero {Op : Type → Type} {Answer : Type u}
    (effect : AnswerEffect.{u})
    (semantics : {Response : Type} → Op Response → Response) :
    denote effect semantics (.zero : Program Op Answer) = effect.empty :=
  rfl

@[simp] theorem denote_choice {Op : Type → Type} {Answer : Type u}
    (effect : AnswerEffect.{u})
    (semantics : {Response : Type} → Op Response → Response)
    (left right : Program Op Answer) :
    denote effect semantics (.choice left right) =
      effect.choice (denote effect semantics left)
        (denote effect semantics right) :=
  rfl

@[simp] theorem denote_perform {Op : Type → Type} {Answer : Type u}
    {Response : Type}
    (effect : AnswerEffect.{u})
    (semantics : {Result : Type} → Op Result → Result)
    (operation : Op Response) (next : Response → Program Op Answer) :
    denote effect semantics (.perform operation next) =
      denote effect semantics (next (semantics operation)) :=
  rfl

@[simp] theorem denote_guard {Op : Type → Type} {Answer : Type u}
    (effect : AnswerEffect.{u})
    (semantics : {Response : Type} → Op Response → Response)
    (test : Op Bool) (next : Program Op Answer) :
    denote effect semantics (guard test next) =
      if semantics test then denote effect semantics next else effect.empty := by
  cases accepted : semantics test <;> simp [guard, accepted]

/-- Compiled sequencing is exactly answer-effect sequencing. -/
theorem denote_bind {Op : Type → Type} {Answer OtherAnswer : Type u}
    (effect : AnswerEffect.{u})
    (semantics : {Response : Type} → Op Response → Response)
    (program : Program Op Answer)
    (next : Answer → Program Op OtherAnswer) :
    denote effect semantics (bind program next) =
      effect.bind (denote effect semantics program)
        (fun answer => denote effect semantics (next answer)) := by
  induction program with
  | pure answer => simp [bind, denote, effect.pure_bind]
  | zero => simp [bind, denote, effect.empty_bind]
  | choice left right leftInduction rightInduction =>
      simp only [bind, denote, leftInduction, rightInduction,
        effect.choice_bind]
  | @perform Response operation continuation inductionHypothesis =>
      simp only [bind, denote]
      exact inductionHypothesis (semantics operation)

/-- Every answer-effect morphism commutes with interpretation of the compiled
program.  The target may forget order or multiplicity only to the extent
declared by that morphism. -/
theorem denote_natural {Op : Type → Type} {Answer : Type u}
    {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target)
    (semantics : {Response : Type} → Op Response → Response)
    (program : Program Op Answer) :
    morphism.map (denote source semantics program) =
      denote target semantics program := by
  induction program with
  | pure answer => exact morphism.map_pure answer
  | zero => exact morphism.map_empty
  | choice left right leftInduction rightInduction =>
      rw [denote, morphism.map_choice, leftInduction, rightInduction]
      rfl
  | @perform Response operation continuation inductionHypothesis =>
      exact inductionHypothesis (semantics operation)

/-- Semantic work counts only deterministic operations actually demanded by
the selected branches.  It is a reference cost, not a claim about a concrete
runtime instruction count. -/
def work {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response) :
    Program Op Answer → Nat
  | .pure _ | .zero => 0
  | .choice left right => work semantics left + work semantics right
  | .perform operation next => work semantics (next (semantics operation)) + 1

end Program

/-! ## Source calculus and two-sided adequacy -/

/-- A source answer calculus with deterministic sequencing and a fused guard.
`guard` is deliberately a source constructor rather than an encoding through
choice, so its lowering has a semantic obligation. -/
inductive Source (Op : Type → Type) (Answer : Type u) : Type (max u 1) where
  | pure (answer : Answer)
  | empty
  | choice (left right : Source Op Answer)
  | letDet {Response : Type} (operation : Op Response)
      (next : Response → Source Op Answer)
  | guard (test : Op Bool) (next : Source Op Answer)

namespace Source

/-- Direct source denotation at an explicitly selected answer profile. -/
def denote {Op : Type → Type} {Answer : Type u}
    (effect : AnswerEffect.{u})
    (semantics : {Response : Type} → Op Response → Response) :
    Source Op Answer → effect.Carrier Answer
  | .pure answer => effect.pure answer
  | .empty => effect.empty
  | .choice left right =>
      effect.choice (denote effect semantics left)
        (denote effect semantics right)
  | .letDet operation next => denote effect semantics (next (semantics operation))
  | .guard test next =>
      if semantics test then denote effect semantics next else effect.empty

/-- Lower source answer control to the explicit operational program. -/
def compile {Op : Type → Type} {Answer : Type u} :
    Source Op Answer → Program Op Answer
  | .pure answer => .pure answer
  | .empty => .zero
  | .choice left right => .choice (compile left) (compile right)
  | .letDet operation next => .perform operation fun response => compile (next response)
  | .guard test next => Program.guard test (compile next)

/-- Compilation preserves and reflects the exact declared observation.  This
is stronger than one-way simulation: the target can neither lose authorized
answers nor invent new ones. -/
theorem compile_adequate {Op : Type → Type} {Answer : Type u}
    (effect : AnswerEffect.{u})
    (semantics : {Response : Type} → Op Response → Response)
    (source : Source Op Answer) :
    Program.denote effect semantics (compile source) =
      denote effect semantics source := by
  induction source with
  | pure answer => simp [compile, denote]
  | empty => simp [compile, denote]
  | choice left right leftInduction rightInduction =>
      simp [compile, denote, leftInduction, rightInduction]
  | @letDet Response operation next inductionHypothesis =>
      simpa [compile, denote] using inductionHypothesis (semantics operation)
  | guard test next inductionHypothesis =>
      cases accepted : semantics test <;>
        simp [compile, denote, Program.denote_guard, accepted,
          inductionHypothesis]

/-- Ordered execution has a compositional occurrence-bag observation. -/
theorem compiled_ordered_to_occurrences {Op : Type → Type}
    {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response)
    (source : Source Op Answer) :
    listToBag.map
        (Program.denote listEffect semantics (compile source)) =
      Program.denote bagEffect semantics (compile source) :=
  Program.denote_natural listToBag semantics (compile source)

end Source

/-! ## Partial physical realizations -/

/-- A physical provider may decline an operation.  Every returned result must
agree with the total semantic authority. -/
structure Realizer (Op : Type → Type)
    (semantics : {Response : Type} → Op Response → Response) where
  run? : {Response : Type} → Op Response → Option Response
  sound : ∀ {Response : Type} (operation : Op Response) (response : Response),
    run? operation = some response → response = semantics operation

namespace Realizer

/-- Execute a compiled program when this physical provider realizes every
deterministic operation reached by the program.  The returned natural number
counts those realized operations. -/
def executeWithCost? {Op : Type → Type}
    {semantics : {Response : Type} → Op Response → Response}
    (realizer : Realizer Op semantics) (effect : AnswerEffect.{u})
    {Answer : Type u} :
    Program Op Answer → Option (effect.Carrier Answer × Nat)
  | .pure answer => some (effect.pure answer, 0)
  | .zero => some (effect.empty, 0)
  | .choice left right =>
      match executeWithCost? realizer effect left,
          executeWithCost? realizer effect right with
      | some (leftAnswers, leftCost), some (rightAnswers, rightCost) =>
          some (effect.choice leftAnswers rightAnswers, leftCost + rightCost)
      | _, _ => none
  | .perform operation next =>
      match realizer.run? operation with
      | none => none
      | some response =>
          match executeWithCost? realizer effect (next response) with
          | none => none
          | some (answers, cost) => some (answers, cost + 1)

/-- Successful physical execution is exact and reports the reference semantic
work. -/
theorem executeWithCost?_sound {Op : Type → Type}
    {semantics : {Response : Type} → Op Response → Response}
    (realizer : Realizer Op semantics) (effect : AnswerEffect.{u})
    {Answer : Type u} (program : Program Op Answer)
    (answers : effect.Carrier Answer) (cost : Nat)
    (executed : executeWithCost? realizer effect program = some (answers, cost)) :
    answers = Program.denote effect semantics program ∧
      cost = Program.work semantics program := by
  induction program generalizing answers cost with
  | pure answer =>
      simp [executeWithCost?] at executed
      constructor
      · change answers = effect.pure answer
        exact executed.1.symm
      · change cost = 0
        exact executed.2.symm
  | zero =>
      simp [executeWithCost?] at executed
      constructor
      · change answers = effect.empty
        exact executed.1.symm
      · change cost = 0
        exact executed.2.symm
  | choice left right leftInduction rightInduction =>
      simp only [executeWithCost?] at executed
      cases leftEquation : executeWithCost? realizer effect left with
      | none => simp [leftEquation] at executed
      | some leftResult =>
          obtain ⟨leftAnswers, leftCost⟩ := leftResult
          cases rightEquation : executeWithCost? realizer effect right with
          | none => simp [leftEquation, rightEquation] at executed
          | some rightResult =>
              obtain ⟨rightAnswers, rightCost⟩ := rightResult
              simp [leftEquation, rightEquation] at executed
              obtain ⟨leftExact, leftWork⟩ :=
                leftInduction leftAnswers leftCost leftEquation
              obtain ⟨rightExact, rightWork⟩ :=
                rightInduction rightAnswers rightCost rightEquation
              constructor
              · calc
                  answers = effect.choice leftAnswers rightAnswers :=
                    executed.1.symm
                  _ = effect.choice
                        (Program.denote effect semantics left)
                        (Program.denote effect semantics right) :=
                    congrArg₂ effect.choice leftExact rightExact
                  _ = Program.denote effect semantics (.choice left right) := rfl
              · calc
                  cost = leftCost + rightCost := executed.2.symm
                  _ = Program.work semantics left +
                        Program.work semantics right :=
                    congrArg₂ Nat.add leftWork rightWork
                  _ = Program.work semantics (.choice left right) := rfl
  | @perform Response operation next inductionHypothesis =>
      simp only [executeWithCost?] at executed
      cases responseEquation : realizer.run? operation with
      | none => simp [responseEquation] at executed
      | some response =>
          cases resultEquation :
              executeWithCost? realizer effect (next response) with
          | none => simp [responseEquation, resultEquation] at executed
          | some result =>
              obtain ⟨resultAnswers, resultCost⟩ := result
              simp [responseEquation, resultEquation] at executed
              have responseExact :=
                realizer.sound operation response responseEquation
              obtain ⟨resultExact, resultWork⟩ :=
                inductionHypothesis response resultAnswers resultCost resultEquation
              subst response
              constructor
              · calc
                  answers = resultAnswers := executed.1.symm
                  _ = Program.denote effect semantics
                        (next (semantics operation)) := resultExact
                  _ = Program.denote effect semantics
                        (.perform operation next) := rfl
              · calc
                  cost = resultCost + 1 := executed.2.symm
                  _ = Program.work semantics (next (semantics operation)) + 1 :=
                    congrArg (fun value => value + 1) resultWork
                  _ = Program.work semantics (.perform operation next) := rfl

end Realizer

/-! ## Executable positive and negative controls -/

/-- Two concrete deterministic probes suffice to separate semantic operations
from physical admission. -/
inductive Probe : Type → Type where
  | accepted : Probe Bool
  | rejected : Probe Bool
  | unavailable : Probe Bool

def probeSemantics : {Response : Type} → Probe Response → Response
  | _, .accepted => true
  | _, .rejected => false
  | _, .unavailable => true

def partialProbeRealizer : Realizer Probe probeSemantics where
  run?
    | .accepted => some true
    | .rejected => some false
    | .unavailable => none
  sound := by
    intro Response operation response result
    cases operation <;> simp [probeSemantics] at result ⊢ <;> simp_all

/-- Guard lowering fuses deterministic observation with answer control while
preserving the ordered answer exactly. -/
theorem guard_lowering_positive :
    Program.denote listEffect probeSemantics
        (Source.compile
          (Source.guard Probe.accepted (Source.pure (7 : Nat)))) = [7] ∧
      Program.denote listEffect probeSemantics
        (Source.compile
          (Source.guard Probe.rejected (Source.pure (7 : Nat)))) = [] := by
  constructor <;> rfl

/-- Choice order is visible in an ordered stream but disappears at the
occurrence-bag observation. -/
theorem choice_order_boundary :
    Program.denote listEffect probeSemantics
        (Program.choice (Program.pure false) (Program.pure true)) ≠
      Program.denote listEffect probeSemantics
        (Program.choice (Program.pure true) (Program.pure false)) ∧
    listToBag.map
        (Program.denote listEffect probeSemantics
          (Program.choice (Program.pure false) (Program.pure true))) =
      listToBag.map
        (Program.denote listEffect probeSemantics
          (Program.choice (Program.pure true) (Program.pure false))) := by
  constructor
  · change [false, true] ≠ [true, false]
    decide
  · change (([false, true] : List Bool) : Multiset Bool) =
      (([true, false] : List Bool) : Multiset Bool)
    decide

/-- A declined physical operation is not semantic zero: the denotation still
contains an authorized answer even though this provider cannot execute it. -/
theorem decline_is_not_zero :
    partialProbeRealizer.executeWithCost? listEffect
        (Program.perform Probe.unavailable fun _ => Program.pure (9 : Nat)) = none ∧
      Program.denote listEffect probeSemantics
        (Program.perform Probe.unavailable fun _ => Program.pure (9 : Nat)) = [9] := by
  constructor <;> rfl

/-- Mapping source empty to a datum invents behavior, demonstrating why a
one-way source simulation is not a sufficient compilation contract. -/
theorem datum_for_zero_invents_answer :
    Program.denote listEffect probeSemantics (Program.pure (5 : Nat)) = [5] ∧
      Source.denote listEffect probeSemantics (Source.empty : Source Probe Nat) = [] ∧
      Program.denote listEffect probeSemantics (Program.pure (5 : Nat)) ≠
        Source.denote listEffect probeSemantics (Source.empty : Source Probe Nat) := by
  change [5] = [5] ∧ ([] : List Nat) = [] ∧ [5] ≠ []
  decide

#print axioms Program.denote_bind
#print axioms Program.denote_natural
#print axioms Source.compile_adequate
#print axioms Source.compiled_ordered_to_occurrences
#print axioms Realizer.executeWithCost?_sound
#print axioms guard_lowering_positive
#print axioms choice_order_boundary
#print axioms decline_is_not_zero
#print axioms datum_for_zero_invents_answer

end Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectProgram
