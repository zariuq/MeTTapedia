import Mettapedia.TypeTheory.BubbleConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory

/-!
# Conversion evidence is a run

A bubble declares the steps it treats as definitional, and its conversion is the free conversion
those steps generate (`BubbleConversion.Bubbles.Conv`). This module presents the declared steps of
one bubble, in one judgment fibre, as an instance of the step interface
(`Interface.EffectCore`, `Interface.Step`), and proves that conversion evidence and runs correspond.

* **Frames** (`conversionFrames`). A frame is an identification of the terms of the fibre: an
  equivalence relation. A morphism is a coarsening, and it acts on terms as the identity. A solution
  of a store of equations is an identification that contains them, so an ask of the knowledge is
  consequence over every identification (`models_iff`).
* **The step** (`core`, `conversionStep`). A state is a conversion goal: the term reached, the
  equations told so far, and one occurrence. A candidate (`Claim`) names a next term, with a
  declared step forwards, a declared step backwards, or no evidence. Its effect takes the goal's
  occurrence, makes the next one, and tells the equation between the two terms. Every candidate is
  prepared (`prepared`); the step admits exactly the candidates that carry a declared step
  (`admits_iff`).
* **Runs are zigzags** (`zigzagRunEquiv`): runs from a goal that end at a term are in bijection
  with the alternating words of declared steps between the two terms.
* **Conversion trees modulo five laws are runs** (`runOfConv_eq_iff`). Two conversion trees give the
  same run exactly when they are related by associativity, the two unit laws, and the three laws of
  reversal (`Laws`). Every run is the run of a tree (`runOfConv_convOfRun`). Two different trees
  can have one run (`Controls.unit_same_run`). Cancellation is not among the laws: a step followed
  by its reverse is a run of two firings, not the empty run (`Controls.roundTrip_not_cancelled`).
* **The one law, for conversion.** Knowledge only refines along a run (`Step.Run.models_start`):
  every identification that validates the last ledger validates the first
  (`models_first_of_models_last`). The last ledger entails the conversion of the first term with
  the last (`run_entails`), and an identification that contains the declared steps and validates
  the first ledger validates the last (`models_last_of_model`). So along a run the identifications
  compatible with the knowledge only shrink, and never below the models of the bubble.

## Controls (`Controls`)

* A bubble with no declared step: the candidate that asserts `false ≐ true` is prepared and
  refused (`claimed_prepared`, `claimed_refused`), and no run leaves `false` (`no_run_reaches`).
  Under an admission that asks for no evidence the same candidate is an event whose knowledge is
  not valid in a model of the bubble (`unchecked_unsound`). The refinement law holds for that event
  too (`EffectCore.event_models`): the law gives monotonicity, and admission by evidence gives
  soundness.
* On the dependent comparison core with the recursion equations of addition:
  `Vec (n + 0)` reaches `Vec n` by one firing (`addZeroRun_last`); `Vec (0 + n)` reaches `Vec n` by
  no run (`zeroAdd_no_run`), although it does with the left-unit equation (`zeroAddRun_last`).

Scope: one bubble and one judgment fibre, with terms as the bubble presents them. The occurrence
part is a single token; contexts, substitution and binding are those of the bubble's own step
relation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ConversionRuns

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.FreeConversion
open Mettapedia.TypeTheory.JudgmentalEquality

universe u uIndex uState uBubble uStep

/-! ## Frames of identifications -/

/-- One way of identifying the terms of a fibre: an equivalence relation on them. -/
structure Identification (T : Type u) where
  rel : T → T → Prop
  equivalence : Equivalence rel

namespace Identification

variable {T : Type u}

/-- The identification that identifies nothing. -/
def equality : Identification T :=
  ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩

/-- The identification that identifies everything. -/
def total : Identification T :=
  ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩

end Identification

/-- The frames of a fibre: identifications of its terms, with coarsenings as morphisms. A
coarsening acts on terms as the identity; what changes is which terms count as equal. -/
def conversionFrames (T : Type u) :
    Frames (fun _ : Identification T => T)
      (fun fine coarse : Identification T => PLift (∀ s t : T, fine.rel s t → coarse.rel s t)) where
  E := fun {identification} s t => identification.rel s t
  equivalence := fun identification => identification.equivalence
  act := fun _ term => term
  id := fun _ => ⟨fun _ _ related => related⟩
  comp := fun later earlier => ⟨fun s t related => later.down s t (earlier.down s t related)⟩
  act_id := fun _ => rfl
  act_comp := fun _ _ _ => rfl
  preserves := fun {_ _} coarsening {_ _} related => coarsening.down _ _ related

/-- Every identification coarsens equality. -/
def fromEquality {T : Type u} (model : Identification T) :
    PLift (∀ s t : T, (Identification.equality (T := T)).rel s t → model.rel s t) :=
  ⟨fun s t same => by
    cases (show s = t from same)
    exact model.equivalence.refl s⟩

/-- A coarsening solves a store exactly when its target contains the store's equations. -/
theorem models_iff {T : Type u} {fine coarse : Identification T}
    (coarsening : PLift (∀ s t : T, fine.rel s t → coarse.rel s t)) (store : EquationStore T) :
    (conversionFrames T).Models coarsening store ↔ ∀ e ∈ store, coarse.rel e.1 e.2 :=
  Iff.rfl

/-! ## Goals, candidates and the effect of a conversion firing -/

variable {Index : Type uIndex}

/-- A conversion goal in one fibre: the term reached, the equations told so far, and the
occurrence that stands for the goal. -/
structure Goal (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (index : Index) where
  cursor : B.State index
  ledger : EquationStore (B.State index)
  clock : Nat

/-- A candidate conversion firing at a term: the next term, with a declared step towards it, a
declared step from it, or no evidence at all. -/
inductive Claim (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (bubble : B.Bubble)
    {index : Index} (source : B.State index) : Type (max uState uStep) where
  | forward (target : B.State index) (step : B.Step bubble source target) : Claim B bubble source
  | backward (target : B.State index) (step : B.Step bubble target source) : Claim B bubble source
  | asserted (target : B.State index) : Claim B bubble source

namespace Claim

variable {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {bubble : B.Bubble} {index : Index}
  {source : B.State index}

/-- The term a candidate moves to. -/
def target : Claim B bubble source → B.State index
  | forward target _ => target
  | backward target _ => target
  | asserted target => target

/-- A candidate is witnessed when it carries a declared step. -/
def Witnessed : Claim B bubble source → Prop
  | forward _ _ => True
  | backward _ _ => True
  | asserted _ => False

end Claim

section Core

variable (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (bubble : B.Bubble) (index : Index)

/-- The effect of a conversion candidate, before any permission: take the goal's occurrence, make
the next one, tell the equation between the term reached and the next term, and move there. -/
def core : EffectCore (conversionFrames (B.State index)) Nat (Goal B index)
    (fun goal => Claim B bubble goal.cursor) where
  frame := fun _ => Identification.equality
  knowledge := fun goal => goal.ledger
  present := fun goal => {goal.clock}
  selection := fun {goal} _ => ⟨[goal.clock], [], [goal.clock + 1]⟩
  target := fun _ => Identification.equality
  extension := fun _ => ⟨fun _ _ related => related⟩
  information := fun {goal} claim => goal.ledger ++ [(goal.cursor, claim.target)]
  information_refines := by
    intro goal claim model coarsening solved e member
    exact solved e (List.mem_append_left _ member)
  Shapes := fun _ => True
  preparedResult := fun {goal} claim _ =>
    ⟨claim.target, goal.ledger ++ [(goal.cursor, claim.target)], goal.clock + 1⟩
  present_preparedResult := by
    intro goal claim _
    ext occurrence
    simp [fire, Selection.commit]
  preparedSettle := fun _ _ => ⟨fun _ _ related => related⟩
  result_refines := by
    intro goal claim _ model coarsening solved
    exact solved

/-- Admission by evidence: a candidate is permitted when it carries a declared step. -/
def witnessed : (core B bubble index).Admission := fun claim _ => claim.Witnessed

/-- Admission that asks for no evidence; the negative control. -/
def unchecked : (core B bubble index).Admission := fun _ _ => True

/-- **The conversion step of a bubble**: the effect of its candidates, admitted by evidence. -/
def conversionStep : Step (conversionFrames (B.State index)) Nat (Goal B index)
    (fun goal => Claim B bubble goal.cursor) :=
  Step.ofEffect (core B bubble index) (witnessed B bubble index)

/-- Every candidate is prepared: its occurrence is present, the next one is fresh, and the
identification of everything solves whatever it tells. -/
theorem prepared {goal : Goal B index} (claim : Claim B bubble goal.cursor) :
    (core B bubble index).Prepares claim := by
  refine ⟨trivial, ⟨?_, ?_, ?_, ?_, ?_⟩, Identification.total, ⟨fun _ _ _ => trivial⟩,
    fun _ _ => trivial⟩
  all_goals simp [core, Selection.commit]

/-- **The step admits exactly the witnessed candidates.** -/
theorem admits_iff {goal : Goal B index} (claim : Claim B bubble goal.cursor) :
    (conversionStep B bubble index).Admits claim ↔ claim.Witnessed :=
  ⟨fun admitted => admitted.elim fun _ seen => seen,
    fun seen => ⟨prepared B bubble index claim, seen⟩⟩

end Core

/-! ## Zigzags: alternating words of declared steps -/

/-- A zigzag between two terms: a word of declared steps, each taken forwards or backwards. -/
inductive Zigzag (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (bubble : B.Bubble)
    {index : Index} : B.State index → B.State index → Type (max uState uStep) where
  | nil (state : B.State index) : Zigzag B bubble state state
  | forward {source middle target : B.State index} (step : B.Step bubble source middle)
      (rest : Zigzag B bubble middle target) : Zigzag B bubble source target
  | backward {source middle target : B.State index} (step : B.Step bubble middle source)
      (rest : Zigzag B bubble middle target) : Zigzag B bubble source target

/-- The reflexivity tree of a bubble's conversion. -/
abbrev convRefl (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (bubble : B.Bubble)
    {index : Index} (state : B.State index) : B.Conv bubble state state :=
  ConversionEvidence.refl (computation := computation B.State (B.Step bubble)) state

namespace Zigzag

variable {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {bubble : B.Bubble} {index : Index}

/-- Concatenation. -/
def append : {source middle target : B.State index} → Zigzag B bubble source middle →
    Zigzag B bubble middle target → Zigzag B bubble source target
  | _, _, _, nil _, later => later
  | _, _, _, forward step rest, later => forward step (append rest later)
  | _, _, _, backward step rest, later => backward step (append rest later)

/-- Reversal: the word backwards, each step in the other direction. -/
def reverse : {source target : B.State index} → Zigzag B bubble source target →
    Zigzag B bubble target source
  | _, _, nil state => nil state
  | _, _, forward step rest => append (reverse rest) (backward step (nil _))
  | _, _, backward step rest => append (reverse rest) (forward step (nil _))

/-- The number of declared steps written in a zigzag. -/
def length : {source target : B.State index} → Zigzag B bubble source target → Nat
  | _, _, nil _ => 0
  | _, _, forward _ rest => length rest + 1
  | _, _, backward _ rest => length rest + 1

theorem append_nil : ∀ {source target : B.State index} (path : Zigzag B bubble source target),
    append path (nil target) = path
  | _, _, nil _ => rfl
  | _, _, forward step rest => congrArg (forward step) (append_nil rest)
  | _, _, backward step rest => congrArg (backward step) (append_nil rest)

theorem append_assoc : ∀ {a b c d : B.State index} (first : Zigzag B bubble a b)
    (second : Zigzag B bubble b c) (third : Zigzag B bubble c d),
    append (append first second) third = append first (append second third)
  | _, _, _, _, nil _, _, _ => rfl
  | _, _, _, _, forward step rest, second, third =>
      congrArg (forward step) (append_assoc rest second third)
  | _, _, _, _, backward step rest, second, third =>
      congrArg (backward step) (append_assoc rest second third)

theorem reverse_append : ∀ {a b c : B.State index} (first : Zigzag B bubble a b)
    (second : Zigzag B bubble b c),
    reverse (append first second) = append (reverse second) (reverse first)
  | _, _, _, nil _, second => (append_nil (reverse second)).symm
  | _, _, _, forward step rest, second => by
      show append (reverse (append rest second)) (backward step (nil _)) =
        append (reverse second) (append (reverse rest) (backward step (nil _)))
      rw [reverse_append rest second, append_assoc]
  | _, _, _, backward step rest, second => by
      show append (reverse (append rest second)) (forward step (nil _)) =
        append (reverse second) (append (reverse rest) (forward step (nil _)))
      rw [reverse_append rest second, append_assoc]

theorem reverse_reverse : ∀ {source target : B.State index} (path : Zigzag B bubble source target),
    reverse (reverse path) = path
  | _, _, nil _ => rfl
  | _, _, forward step rest => by
      show reverse (append (reverse rest) (backward step (nil _))) = forward step rest
      rw [reverse_append, reverse_reverse rest]
      rfl
  | _, _, backward step rest => by
      show reverse (append (reverse rest) (forward step (nil _))) = backward step rest
      rw [reverse_append, reverse_reverse rest]
      rfl

/-- The zigzag of a conversion tree: its declared steps in order, reversed under each symmetry. -/
def ofConv : {source target : B.State index} → B.Conv bubble source target →
    Zigzag B bubble source target
  | _, _, .step step => forward step (nil _)
  | _, _, .refl state => nil state
  | _, _, .symm path => reverse (ofConv path)
  | _, _, .trans first second => append (ofConv first) (ofConv second)

/-- The conversion tree of a zigzag, associated to the right. -/
def toConv : {source target : B.State index} → Zigzag B bubble source target →
    B.Conv bubble source target
  | _, _, nil state => convRefl B bubble state
  | _, _, forward step rest => ConversionEvidence.trans (ConversionEvidence.step step) (toConv rest)
  | _, _, backward step rest =>
      ConversionEvidence.trans (ConversionEvidence.symm (ConversionEvidence.step step)) (toConv rest)

/-- Every zigzag is the zigzag of its tree. -/
theorem ofConv_toConv : ∀ {source target : B.State index} (path : Zigzag B bubble source target),
    ofConv (toConv path) = path
  | _, _, nil _ => rfl
  | _, _, forward step rest => congrArg (forward step) (ofConv_toConv rest)
  | _, _, backward step rest => congrArg (backward step) (ofConv_toConv rest)

/-- Read a zigzag at an equal target. -/
def castTarget {source target target' : B.State index} (same : target' = target)
    (path : Zigzag B bubble source target') : Zigzag B bubble source target :=
  same ▸ path

theorem castTarget_eq_of_heq {source target target' : B.State index} (same : target' = target)
    {first : Zigzag B bubble source target'} {second : Zigzag B bubble source target}
    (alike : HEq first second) : castTarget same first = second := by
  subst same
  exact eq_of_heq alike

theorem forward_heq {source middle target target' : B.State index}
    (step : B.Step bubble source middle) (same : target' = target)
    {first : Zigzag B bubble middle target'} {second : Zigzag B bubble middle target}
    (alike : HEq first second) : HEq (forward step first) (forward step second) := by
  subst same
  obtain rfl := eq_of_heq alike
  exact HEq.rfl

theorem backward_heq {source middle target target' : B.State index}
    (step : B.Step bubble middle source) (same : target' = target)
    {first : Zigzag B bubble middle target'} {second : Zigzag B bubble middle target}
    (alike : HEq first second) : HEq (backward step first) (backward step second) := by
  subst same
  obtain rfl := eq_of_heq alike
  exact HEq.rfl

end Zigzag

/-! ## Runs are zigzags -/

section Runs

variable {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {bubble : B.Bubble} {index : Index}

/-- A witnessed candidate, placed in front of a zigzag from its target. -/
def Claim.zigzag {source target : B.State index} :
    (claim : Claim B bubble source) → claim.Witnessed → Zigzag B bubble claim.target target →
      Zigzag B bubble source target
  | .forward _ step, _, rest => Zigzag.forward step rest
  | .backward _ step, _, rest => Zigzag.backward step rest
  | .asserted _, seen, _ => False.elim seen

/-- The zigzag of a run: the declared steps of its firings, in order. -/
def zigzagOfRun : {goal : Goal B index} → (run : (conversionStep B bubble index).Run goal) →
    Zigzag B bubble goal.cursor run.last.cursor
  | _, .nil goal => Zigzag.nil goal.cursor
  | _, .cons claim admitted rest =>
      claim.zigzag ((admits_iff B bubble index claim).mp admitted) (zigzagOfRun rest)

/-- The run of a zigzag from a goal with a given ledger and occurrence. -/
def runOfZigzag : {source target : B.State index} → Zigzag B bubble source target →
    (ledger : EquationStore (B.State index)) → (clock : Nat) →
    (conversionStep B bubble index).Run ⟨source, ledger, clock⟩
  | source, _, .nil _, ledger, clock =>
      Step.Run.nil (P := conversionStep B bubble index) (Goal.mk source ledger clock)
  | source, _, .forward (middle := middle) step rest, ledger, clock =>
      Step.Run.cons (P := conversionStep B bubble index) (s := Goal.mk source ledger clock)
        (Claim.forward middle step)
        ((admits_iff B bubble index (goal := Goal.mk source ledger clock)
          (Claim.forward middle step)).mpr trivial)
        (runOfZigzag rest (ledger ++ [(source, middle)]) (clock + 1))
  | source, _, .backward (middle := middle) step rest, ledger, clock =>
      Step.Run.cons (P := conversionStep B bubble index) (s := Goal.mk source ledger clock)
        (Claim.backward middle step)
        ((admits_iff B bubble index (goal := Goal.mk source ledger clock)
          (Claim.backward middle step)).mpr trivial)
        (runOfZigzag rest (ledger ++ [(source, middle)]) (clock + 1))

theorem last_runOfZigzag : ∀ {source target : B.State index}
    (path : Zigzag B bubble source target) (ledger : EquationStore (B.State index)) (clock : Nat),
    (runOfZigzag path ledger clock).last.cursor = target
  | _, _, .nil _, _, _ => rfl
  | _, _, .forward _ rest, _, _ => last_runOfZigzag rest _ _
  | _, _, .backward _ rest, _, _ => last_runOfZigzag rest _ _

/-- A run is the run of its zigzag. -/
theorem runOfZigzag_zigzagOfRun : ∀ {goal : Goal B index}
    (run : (conversionStep B bubble index).Run goal),
    runOfZigzag (zigzagOfRun run) goal.ledger goal.clock = run
  | _, .nil _ => rfl
  | _, .cons (.forward middle step) admitted rest =>
      congrArg (Step.Run.cons (P := conversionStep B bubble index) (Claim.forward middle step)
        admitted) (runOfZigzag_zigzagOfRun rest)
  | _, .cons (.backward middle step) admitted rest =>
      congrArg (Step.Run.cons (P := conversionStep B bubble index) (Claim.backward middle step)
        admitted) (runOfZigzag_zigzagOfRun rest)
  | _, .cons (.asserted target) admitted _ =>
      False.elim ((admits_iff B bubble index (Claim.asserted target)).mp admitted)

/-- A zigzag is the zigzag of its run. -/
theorem zigzagOfRun_runOfZigzag : ∀ {source target : B.State index}
    (path : Zigzag B bubble source target) (ledger : EquationStore (B.State index)) (clock : Nat),
    HEq (zigzagOfRun (runOfZigzag path ledger clock)) path
  | _, _, .nil _, _, _ => HEq.rfl
  | _, _, .forward step rest, _, _ =>
      Zigzag.forward_heq step (last_runOfZigzag rest _ _) (zigzagOfRun_runOfZigzag rest _ _)
  | _, _, .backward step rest, _, _ =>
      Zigzag.backward_heq step (last_runOfZigzag rest _ _) (zigzagOfRun_runOfZigzag rest _ _)

/-- **Runs are zigzags.** The runs of the conversion step from a goal that end at a term are in
bijection with the zigzags of declared steps between the two terms. -/
def zigzagRunEquiv (source target : B.State index) (ledger : EquationStore (B.State index))
    (clock : Nat) :
    Zigzag B bubble source target ≃
      {run : (conversionStep B bubble index).Run ⟨source, ledger, clock⟩ //
        run.last.cursor = target} where
  toFun path := ⟨runOfZigzag path ledger clock, last_runOfZigzag path ledger clock⟩
  invFun run := Zigzag.castTarget run.property (zigzagOfRun run.val)
  left_inv path := Zigzag.castTarget_eq_of_heq _ (zigzagOfRun_runOfZigzag path ledger clock)
  right_inv := by
    rintro ⟨run, ends⟩
    subst ends
    exact Subtype.ext (runOfZigzag_zigzagOfRun run)

/-! ## Conversion trees and runs -/

/-- The run of a conversion tree. -/
def runOfConv {source target : B.State index} (path : B.Conv bubble source target)
    (ledger : EquationStore (B.State index)) (clock : Nat) :
    (conversionStep B bubble index).Run ⟨source, ledger, clock⟩ :=
  runOfZigzag (Zigzag.ofConv path) ledger clock

/-- The conversion tree of a run. -/
def convOfRun {goal : Goal B index} (run : (conversionStep B bubble index).Run goal) :
    B.Conv bubble goal.cursor run.last.cursor :=
  (zigzagOfRun run).toConv

theorem last_runOfConv {source target : B.State index} (path : B.Conv bubble source target)
    (ledger : EquationStore (B.State index)) (clock : Nat) :
    (runOfConv path ledger clock).last.cursor = target :=
  last_runOfZigzag _ _ _

/-- **Every run is the run of a conversion tree**, its own. -/
theorem runOfConv_convOfRun {goal : Goal B index}
    (run : (conversionStep B bubble index).Run goal) :
    runOfConv (convOfRun run) goal.ledger goal.clock = run := by
  unfold runOfConv convOfRun
  rw [Zigzag.ofConv_toConv]
  exact runOfZigzag_zigzagOfRun run

/-- **Conversion is reachability by runs.** Two terms are convertible in a bubble exactly when a
run of its conversion step leads from one to the other, from any ledger and occurrence. -/
theorem conv_iff_run {source target : B.State index} (ledger : EquationStore (B.State index))
    (clock : Nat) :
    Nonempty (B.Conv bubble source target) ↔
      ∃ run : (conversionStep B bubble index).Run ⟨source, ledger, clock⟩,
        run.last.cursor = target := by
  constructor
  · rintro ⟨path⟩
    exact ⟨runOfConv path ledger clock, last_runOfConv path ledger clock⟩
  · rintro ⟨run, ends⟩
    subst ends
    exact ⟨convOfRun run⟩

/-! ## The laws that identify conversion trees with the same run -/

/-- The equations between conversion trees that hold of runs: associativity, the two unit laws,
and the three laws of reversal. Cancellation of a step against its reverse is not one of them. -/
inductive Laws {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {bubble : B.Bubble}
    {index : Index} :
    {source target : B.State index} → B.Conv bubble source target → B.Conv bubble source target →
      Prop where
  | refl {source target : B.State index} (path : B.Conv bubble source target) : Laws path path
  | symm {source target : B.State index} {first second : B.Conv bubble source target} :
      Laws first second → Laws second first
  | trans {source target : B.State index} {first second third : B.Conv bubble source target} :
      Laws first second → Laws second third → Laws first third
  | congrTrans {source middle target : B.State index}
      {first first' : B.Conv bubble source middle} {second second' : B.Conv bubble middle target} :
      Laws first first' → Laws second second' →
        Laws (ConversionEvidence.trans first second) (ConversionEvidence.trans first' second')
  | congrSymm {source target : B.State index} {first first' : B.Conv bubble source target} :
      Laws first first' → Laws (ConversionEvidence.symm first) (ConversionEvidence.symm first')
  | assoc {a b c d : B.State index} (first : B.Conv bubble a b) (second : B.Conv bubble b c)
      (third : B.Conv bubble c d) :
      Laws (ConversionEvidence.trans (ConversionEvidence.trans first second) third)
        (ConversionEvidence.trans first (ConversionEvidence.trans second third))
  | leftUnit {source target : B.State index} (path : B.Conv bubble source target) :
      Laws (ConversionEvidence.trans (convRefl B bubble source) path) path
  | rightUnit {source target : B.State index} (path : B.Conv bubble source target) :
      Laws (ConversionEvidence.trans path (convRefl B bubble target)) path
  | symmTrans {source middle target : B.State index} (first : B.Conv bubble source middle)
      (second : B.Conv bubble middle target) :
      Laws (ConversionEvidence.symm (ConversionEvidence.trans first second))
        (ConversionEvidence.trans (ConversionEvidence.symm second) (ConversionEvidence.symm first))
  | symmRefl (state : B.State index) :
      Laws (ConversionEvidence.symm (convRefl B bubble state)) (convRefl B bubble state)
  | symmSymm {source target : B.State index} (path : B.Conv bubble source target) :
      Laws (ConversionEvidence.symm (ConversionEvidence.symm path)) path

/-- Trees related by the laws have the same zigzag. -/
theorem ofConv_respects {source target : B.State index}
    {first second : B.Conv bubble source target} (related : Laws first second) :
    Zigzag.ofConv first = Zigzag.ofConv second := by
  induction related with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  | congrTrans _ _ ihFirst ihSecond => exact congrArg₂ Zigzag.append ihFirst ihSecond
  | congrSymm _ ih => exact congrArg Zigzag.reverse ih
  | assoc first second third => exact Zigzag.append_assoc _ _ _
  | leftUnit path => rfl
  | rightUnit path => exact Zigzag.append_nil _
  | symmTrans first second => exact Zigzag.reverse_append _ _
  | symmRefl state => rfl
  | symmSymm path => exact Zigzag.reverse_reverse _

theorem toConv_append : ∀ {a b c : B.State index} (first : Zigzag B bubble a b)
    (second : Zigzag B bubble b c),
    Laws (Zigzag.toConv (Zigzag.append first second))
      (ConversionEvidence.trans (Zigzag.toConv first) (Zigzag.toConv second))
  | _, _, _, .nil _, _ => Laws.symm (Laws.leftUnit _)
  | _, _, _, .forward _ rest, second =>
      Laws.trans (Laws.congrTrans (Laws.refl _) (toConv_append rest second))
        (Laws.symm (Laws.assoc _ _ _))
  | _, _, _, .backward _ rest, second =>
      Laws.trans (Laws.congrTrans (Laws.refl _) (toConv_append rest second))
        (Laws.symm (Laws.assoc _ _ _))

theorem toConv_reverse : ∀ {a b : B.State index} (path : Zigzag B bubble a b),
    Laws (Zigzag.toConv (Zigzag.reverse path)) (ConversionEvidence.symm (Zigzag.toConv path))
  | _, _, .nil state => Laws.symm (Laws.symmRefl state)
  | _, _, .forward _ rest =>
      Laws.trans (toConv_append _ _)
        (Laws.trans (Laws.congrTrans (toConv_reverse rest) (Laws.rightUnit _))
          (Laws.symm (Laws.symmTrans _ _)))
  | _, _, .backward _ rest =>
      Laws.trans (toConv_append _ _)
        (Laws.trans
          (Laws.congrTrans (toConv_reverse rest)
            (Laws.trans (Laws.rightUnit _) (Laws.symm (Laws.symmSymm _))))
          (Laws.symm (Laws.symmTrans _ _)))

/-- Every conversion tree is related by the laws to the tree of its zigzag. -/
theorem laws_toConv_ofConv : ∀ {source target : B.State index}
    (path : B.Conv bubble source target), Laws (Zigzag.toConv (Zigzag.ofConv path)) path
  | _, _, .step _ => Laws.rightUnit _
  | _, _, .refl _ => Laws.refl _
  | _, _, .symm path => Laws.trans (toConv_reverse _) (Laws.congrSymm (laws_toConv_ofConv path))
  | _, _, .trans first second =>
      Laws.trans (toConv_append _ _)
        (Laws.congrTrans (laws_toConv_ofConv first) (laws_toConv_ofConv second))

/-- Two conversion trees have the same zigzag exactly when the laws relate them. -/
theorem ofConv_eq_iff {source target : B.State index}
    {first second : B.Conv bubble source target} :
    Zigzag.ofConv first = Zigzag.ofConv second ↔ Laws first second := by
  constructor
  · intro same
    have fromFirst := Laws.symm (laws_toConv_ofConv first)
    rw [same] at fromFirst
    exact Laws.trans fromFirst (laws_toConv_ofConv second)
  · exact ofConv_respects

/-- **Conversion trees modulo the laws are runs.** Two conversion trees give the same run exactly
when the laws relate them. -/
theorem runOfConv_eq_iff {source target : B.State index}
    (first second : B.Conv bubble source target) (ledger : EquationStore (B.State index))
    (clock : Nat) :
    runOfConv first ledger clock = runOfConv second ledger clock ↔ Laws first second := by
  rw [← ofConv_eq_iff]
  constructor
  · intro same
    exact (zigzagRunEquiv source target ledger clock).injective (Subtype.ext same)
  · intro same
    unfold runOfConv
    rw [same]

/-! ## The one law, read for conversion -/

/-- Told equations stay told. -/
theorem ledger_subset : ∀ {goal : Goal B index} (run : (conversionStep B bubble index).Run goal),
    ∀ e ∈ goal.ledger, e ∈ run.last.ledger
  | _, .nil _, _, member => member
  | _, .cons _ _ rest, e, member => ledger_subset rest e (List.mem_append_left _ member)

/-- **Knowledge only refines along a conversion run**: an identification that validates the last
ledger validates the first. This is `Step.Run.models_start` at the conversion step. -/
theorem models_first_of_models_last {goal : Goal B index}
    (run : (conversionStep B bubble index).Run goal) (model : Identification (B.State index))
    (holds : ∀ e ∈ run.last.ledger, model.rel e.1 e.2) : ∀ e ∈ goal.ledger, model.rel e.1 e.2 :=
  run.models_start (b := model) (fromEquality model) holds

/-- **The knowledge after a run entails the conversion it witnesses**: every identification that
contains the last ledger identifies the first term with the last. -/
theorem run_entails : ∀ {goal : Goal B index} (run : (conversionStep B bubble index).Run goal),
    (conversionFrames (B.State index)).Entails (a := Identification.equality) run.last.ledger
      (fun model _ => model.rel goal.cursor run.last.cursor)
  | _, .nil goal => fun model _ _ => model.equivalence.refl goal.cursor
  | goal, .cons claim _ rest => fun model coarsening solved =>
      model.equivalence.trans
        (solved (goal.cursor, claim.target)
          (ledger_subset rest _ (List.mem_append_right _ (List.mem_singleton_self _))))
        (run_entails rest model coarsening solved)

/-- A witnessed candidate tells an equation that every model of the bubble validates. -/
theorem Claim.valid {source : B.State index} (claim : Claim B bubble source)
    (seen : claim.Witnessed) (model : Identification (B.State index))
    (contains : ∀ s t : B.State index, B.Step bubble s t → model.rel s t) :
    model.rel source claim.target := by
  cases claim with
  | forward target step => exact contains _ _ step
  | backward target step => exact model.equivalence.symm (contains _ _ step)
  | asserted target => exact False.elim seen

/-- **Runs never refine below the models of the bubble**: an identification that contains every
declared step and validates the first ledger validates the last. -/
theorem models_last_of_model (model : Identification (B.State index))
    (contains : ∀ s t : B.State index, B.Step bubble s t → model.rel s t) :
    ∀ {goal : Goal B index} (run : (conversionStep B bubble index).Run goal),
      (∀ e ∈ goal.ledger, model.rel e.1 e.2) → ∀ e ∈ run.last.ledger, model.rel e.1 e.2
  | _, .nil _, holds => holds
  | goal, .cons claim admitted rest, holds =>
      models_last_of_model model contains rest (by
        intro e member
        rcases List.mem_append.mp member with old | told
        · exact holds e old
        · obtain rfl := List.mem_singleton.mp told
          exact claim.valid ((admits_iff B bubble index claim).mp admitted) model contains)

/-- **Soundness of conversion runs**: a run from a goal relates its first and last terms in every
identification that contains the declared steps and validates the goal's ledger. -/
theorem run_sound (model : Identification (B.State index))
    (contains : ∀ s t : B.State index, B.Step bubble s t → model.rel s t)
    {goal : Goal B index} (run : (conversionStep B bubble index).Run goal)
    (holds : ∀ e ∈ goal.ledger, model.rel e.1 e.2) : model.rel goal.cursor run.last.cursor :=
  run_entails run model (fromEquality model) (models_last_of_model model contains run holds)

end Runs

/-! ## Controls -/

namespace Controls

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr
open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- Two terms and a bubble that declares no step. -/
def silent : Bubbles.{0, 0, 0, 0} Unit where
  State := fun _ => Bool
  Bubble := Unit
  Step := fun _ {_} _ _ => PEmpty

/-- The goal at `false`, with nothing told. -/
def start : Goal silent () := ⟨false, [], 0⟩

/-- The candidate that asserts `false ≐ true` with no evidence. -/
def claimed : Claim silent () (index := ()) start.cursor := .asserted true

/-- The unevidenced candidate is prepared: nothing about its effect is wrong. -/
theorem claimed_prepared : (core silent () ()).Prepares claimed := prepared silent () () claimed

/-- **A conversion that is not a run is refused**: the candidate is not admitted by the step. -/
theorem claimed_refused : ¬ (conversionStep silent () ()).Admits claimed :=
  fun admitted => (admits_iff silent () () claimed).mp admitted

theorem silent_zigzag : ∀ {source target : Bool},
    Zigzag silent () (index := ()) source target → source = target
  | _, _, .nil _ => rfl
  | _, _, .forward step _ => PEmpty.elim step
  | _, _, .backward step _ => PEmpty.elim step

/-- No run of the bubble without steps leaves `false`. -/
theorem no_run_reaches (run : (conversionStep silent () ()).Run start) :
    run.last.cursor = false :=
  (silent_zigzag (zigzagOfRun run)).symm

/-- Under the admission that asks for no evidence, the candidate is an event. -/
def uncheckedEvent :
    (core silent () ()).Event (unchecked silent () ()) start ⟨true, [(false, true)], 1⟩ :=
  ⟨claimed, claimed_prepared, trivial, rfl⟩

/-- **Without admission by evidence the knowledge leaves the models of the bubble**: equality is a
model of the bubble without steps, and it does not validate the ledger of the unchecked event. -/
theorem unchecked_unsound :
    (∀ s t : Bool, silent.Step () (index := ()) s t → (Identification.equality (T := Bool)).rel s t) ∧
      ¬ ∀ e ∈ (core silent () ()).knowledge (⟨true, [(false, true)], 1⟩ : Goal silent ()),
        (Identification.equality (T := Bool)).rel e.1 e.2 := by
  refine ⟨fun _ _ step => PEmpty.elim step, fun holds => ?_⟩
  exact Bool.false_ne_true (holds (false, true) (List.mem_singleton_self _))

/-- One term, and a bubble with a declared loop for each Boolean. -/
def loops : Bubbles.{0, 0, 0, 0} Unit where
  State := fun _ => Unit
  Bubble := Unit
  Step := fun _ {_} _ _ => Bool

/-- The number of constructors of a conversion tree of the loop bubble. -/
def treeSize : {source target : Unit} → loops.Conv () (index := ()) source target → Nat
  | _, _, .step _ => 1
  | _, _, .refl _ => 1
  | _, _, .symm path => treeSize path + 1
  | _, _, .trans first second => treeSize first + treeSize second + 1

/-- One declared step, as a conversion. -/
def loopStep : loops.Conv () (index := ()) () () :=
  ConversionEvidence.step (computation := computation loops.State (loops.Step ()))
    (source := ()) (target := ()) false

/-- A declared step followed by its reverse. -/
def roundTrip : loops.Conv () (index := ()) () () :=
  ConversionEvidence.trans loopStep (ConversionEvidence.symm loopStep)

/-- **Cancellation is not a law of runs**: a step followed by its reverse is not related to the
empty conversion, and its zigzag has two steps. -/
theorem roundTrip_not_cancelled : ¬ Laws roundTrip (convRefl loops () (index := ()) ()) := by
  intro related
  exact absurd (congrArg Zigzag.length (ofConv_respects related)) (by decide)

/-- **Two different trees, one run**: a step followed by the empty conversion is another tree than
the step, and the right unit law gives both the same run. -/
theorem unit_same_run :
    ConversionEvidence.trans loopStep (convRefl loops () (index := ()) ()) ≠ loopStep ∧
      runOfConv (ConversionEvidence.trans loopStep (convRefl loops () (index := ()) ())) [] 0 =
        runOfConv loopStep [] 0 := by
  refine ⟨fun same => ?_, (runOfConv_eq_iff _ _ [] 0).mpr (Laws.rightUnit loopStep)⟩
  exact absurd (congrArg (treeSize (source := ()) (target := ())) same) (by decide)

/-- The bubbles of the dependent comparison core over the arithmetic signature. -/
abbrev arithBubbles : Bubbles.{0, 0, 0, 0} Unit := coreBubbles (Base := Unit) (Const := ArithConst)

/-- `Vec (n + 0)` reaches `Vec n` by one firing of the recursion equations. -/
def addZeroZigzag :
    Zigzag arithBubbles Rule (index := ()) (vec (addE (bvar 1) zeroE)) (vec (bvar 1)) :=
  Zigzag.forward (B := arithBubbles) (bubble := Rule) (index := ())
    (source := vec (addE (bvar 1) zeroE)) (middle := vec (bvar 1)) (target := vec (bvar 1))
    (PLift.up (Rewrite.appArgument (Rewrite.root (Rule.addZero (bvar 1)))))
    (Zigzag.nil (B := arithBubbles) (bubble := Rule) (index := ()) (vec (bvar 1)))

/-- Its run, from the goal with nothing told. -/
def addZeroRun : (conversionStep arithBubbles Rule ()).Run ⟨vec (addE (bvar 1) zeroE), [], 0⟩ :=
  runOfZigzag addZeroZigzag [] 0

theorem addZeroRun_last : addZeroRun.last.cursor = vec (bvar 1) :=
  last_runOfZigzag addZeroZigzag [] 0

/-- **No run of the recursion equations takes `Vec (0 + n)` to `Vec n`**, from any ledger: the
equation is true in the standard model and is not a conversion of this bubble. -/
theorem zeroAdd_no_run (ledger : EquationStore AExpr) (clock : Nat)
    (run : (conversionStep arithBubbles Rule ()).Run ⟨vec (addE zeroE (bvar 1)), ledger, clock⟩) :
    run.last.cursor ≠ vec (bvar 1) := by
  intro ends
  have path : arithBubbles.Conv Rule (index := ()) (vec (addE zeroE (bvar 1))) (vec (bvar 1)) :=
    ends ▸ convOfRun run
  have same := bubble_conv_norm false path
  simp [Arith.norm, appNorm, addNorm, vec, addE, zeroE] at same

/-- With the left-unit equation declared, it is one firing. -/
def zeroAddZigzag :
    Zigzag arithBubbles RulePlus (index := ()) (vec (addE zeroE (bvar 1))) (vec (bvar 1)) :=
  Zigzag.forward (B := arithBubbles) (bubble := RulePlus) (index := ())
    (source := vec (addE zeroE (bvar 1))) (middle := vec (bvar 1)) (target := vec (bvar 1))
    (PLift.up (Rewrite.appArgument (Rewrite.root (RulePlus.zeroAdd (bvar 1)))))
    (Zigzag.nil (B := arithBubbles) (bubble := RulePlus) (index := ()) (vec (bvar 1)))

/-- Its run, from the goal with nothing told. -/
def zeroAddRun : (conversionStep arithBubbles RulePlus ()).Run ⟨vec (addE zeroE (bvar 1)), [], 0⟩ :=
  runOfZigzag zeroAddZigzag [] 0

theorem zeroAddRun_last : zeroAddRun.last.cursor = vec (bvar 1) :=
  last_runOfZigzag zeroAddZigzag [] 0

end Controls

/-! ## Axiom audit -/

#print axioms conversionStep
#print axioms prepared
#print axioms admits_iff
#print axioms zigzagRunEquiv
#print axioms runOfConv_convOfRun
#print axioms conv_iff_run
#print axioms ofConv_eq_iff
#print axioms runOfConv_eq_iff
#print axioms models_first_of_models_last
#print axioms run_entails
#print axioms models_last_of_model
#print axioms run_sound
#print axioms Controls.claimed_prepared
#print axioms Controls.claimed_refused
#print axioms Controls.no_run_reaches
#print axioms Controls.unchecked_unsound
#print axioms Controls.roundTrip_not_cancelled
#print axioms Controls.unit_same_run
#print axioms Controls.addZeroRun_last
#print axioms Controls.zeroAdd_no_run
#print axioms Controls.zeroAddRun_last

end Mettapedia.TypeTheory.ConversionRuns
