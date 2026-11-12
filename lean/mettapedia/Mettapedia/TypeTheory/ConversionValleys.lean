import Mettapedia.TypeTheory.ConversionRuns
import Mettapedia.Logic.Relation.NormalFormDecision

/-!
# What a decided bubble buys: evidence that can be computed

In `ConversionRuns` the evidence of a conversion is a zigzag of declared steps, and a checker is
handed it. When a bubble is confluent, or decided by normal forms, the evidence has a canonical
shape that needs no search for peaks: run both sides forwards.

* **Valleys** (`Valley`): a zigzag that goes forwards from the first term to a common term and
  then backwards to the second. A valley exists exactly when the two terms have a common reduct
  (`valley_iff_join`), and every valley is a conversion (`conv_of_valley`).
* **In a confluent bubble every conversion has a valley** (`conv_iff_valley`).
* **In a bubble decided by normal forms, a conversion holds exactly when both sides run forwards
  to one normal term** (`conv_iff_common_normal_form`). This is what promotion into a decided
  bubble gives in the reading by runs: the evidence is computed by running.

## Controls (`Controls`)

* `fork`: one term steps to two others. The two are convertible (`fork_converts`) and have no
  valley (`fork_no_valley`): the evidence passes through a peak and has to be supplied.
* `entry`: two terms step to a third. They have a valley (`entry_valley`).

Scope: one bubble and one fibre. Confluence and the decision by normal forms are hypotheses here;
`PromotionAdmission` is where the tree establishes them for first-order rules.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ConversionValleys

open _root_.Relation
open Mettapedia.Logic.Relation (IsNormal IsNormalFormOf Confluent DecidedOn)
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.FreeConversion
open Mettapedia.TypeTheory.JudgmentalEquality
open Mettapedia.TypeTheory.ConversionRuns

universe uIndex uState uBubble uStep

variable {Index : Type uIndex}

/-- The declared steps of a bubble in one fibre, with their evidence forgotten. -/
def stepRel (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (bubble : B.Bubble)
    (index : Index) : B.State index → B.State index → Prop :=
  fun s t => Nonempty (B.Step bubble s t)

section Shapes

variable {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {bubble : B.Bubble} {index : Index}

/-- A zigzag all of whose steps are taken forwards. -/
def IsForward : {s t : B.State index} → Zigzag B bubble s t → Prop
  | _, _, .nil _ => True
  | _, _, .forward _ rest => IsForward rest
  | _, _, .backward _ _ => False

/-- A zigzag all of whose steps are taken backwards. -/
def IsBackward : {s t : B.State index} → Zigzag B bubble s t → Prop
  | _, _, .nil _ => True
  | _, _, .forward _ _ => False
  | _, _, .backward _ rest => IsBackward rest

theorem isForward_append : ∀ {a b c : B.State index} (first : Zigzag B bubble a b)
    (second : Zigzag B bubble b c), IsForward first → IsForward second →
      IsForward (first.append second)
  | _, _, _, .nil _, _, _, later => later
  | _, _, _, .forward _ rest, second, earlier, later => isForward_append rest second earlier later
  | _, _, _, .backward _ _, _, earlier, _ => False.elim earlier

theorem isBackward_append : ∀ {a b c : B.State index} (first : Zigzag B bubble a b)
    (second : Zigzag B bubble b c), IsBackward first → IsBackward second →
      IsBackward (first.append second)
  | _, _, _, .nil _, _, _, later => later
  | _, _, _, .forward _ _, _, earlier, _ => False.elim earlier
  | _, _, _, .backward _ rest, second, earlier, later => isBackward_append rest second earlier later

/-- The reverse of a forward zigzag is a backward one. -/
theorem isBackward_reverse : ∀ {a b : B.State index} (path : Zigzag B bubble a b),
    IsForward path → IsBackward path.reverse
  | _, _, .nil _, _ => trivial
  | _, _, .forward step rest, forward =>
      isBackward_append rest.reverse (Zigzag.backward step (Zigzag.nil _))
        (isBackward_reverse rest forward) trivial
  | _, _, .backward _ _, forward => False.elim forward

/-- A reduction is a forward zigzag. -/
theorem forward_of_reflTransGen {s t : B.State index}
    (steps : ReflTransGen (stepRel B bubble index) s t) :
    ∃ path : Zigzag B bubble s t, IsForward path := by
  induction steps with
  | refl => exact ⟨Zigzag.nil s, trivial⟩
  | tail _ step ih =>
      obtain ⟨path, forward⟩ := ih
      obtain ⟨evidence⟩ := step
      exact ⟨path.append (Zigzag.forward evidence (Zigzag.nil _)),
        isForward_append path _ forward trivial⟩

theorem reflTransGen_of_forward : ∀ {s t : B.State index} (path : Zigzag B bubble s t),
    IsForward path → ReflTransGen (stepRel B bubble index) s t
  | _, _, .nil _, _ => ReflTransGen.refl
  | _, _, .forward step rest, forward =>
      ReflTransGen.head ⟨step⟩ (reflTransGen_of_forward rest forward)
  | _, _, .backward _ _, forward => False.elim forward

theorem reflTransGen_of_backward : ∀ {s t : B.State index} (path : Zigzag B bubble s t),
    IsBackward path → ReflTransGen (stepRel B bubble index) t s
  | _, _, .nil _, _ => ReflTransGen.refl
  | _, _, .forward _ _, backward => False.elim backward
  | _, _, .backward step rest, backward =>
      (reflTransGen_of_backward rest backward).tail ⟨step⟩

end Shapes

section Valleys

variable (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (bubble : B.Bubble) {index : Index}

/-- **A valley between two terms**: forwards from the first to a common term, then backwards to
the second. -/
def Valley (s t : B.State index) : Prop :=
  ∃ (common : B.State index) (down : Zigzag B bubble s common) (up : Zigzag B bubble common t),
    IsForward down ∧ IsBackward up

variable {B bubble}

/-- **A valley exists exactly when the two terms have a common reduct.** -/
theorem valley_iff_join {s t : B.State index} :
    Valley B bubble s t ↔ Join (ReflTransGen (stepRel B bubble index)) s t := by
  constructor
  · rintro ⟨common, down, up, forward, backward⟩
    exact ⟨common, reflTransGen_of_forward down forward, reflTransGen_of_backward up backward⟩
  · rintro ⟨common, fromFirst, fromSecond⟩
    obtain ⟨down, forward⟩ := forward_of_reflTransGen fromFirst
    obtain ⟨back, forward'⟩ := forward_of_reflTransGen fromSecond
    exact ⟨common, down, back.reverse, forward, isBackward_reverse back forward'⟩

/-- Every valley is a conversion. -/
theorem conv_of_valley {s t : B.State index} (valley : Valley B bubble s t) :
    Nonempty (B.Conv bubble s t) :=
  valley.elim fun _ rest => rest.elim fun down rest' => rest'.elim fun up _ =>
    ⟨(down.append up).toConv⟩

/-- Conversion of a bubble is the equivalence closure of its declared steps. -/
theorem conv_iff_eqvGen {s t : B.State index} :
    Nonempty (B.Conv bubble s t) ↔ EqvGen (stepRel B bubble index) s t :=
  (ConversionEvidence.support_iff_nonempty_evidence
    (computation B.State (B.Step bubble))).symm

/-- **In a confluent bubble every conversion has a valley.** -/
theorem conv_iff_valley (confluent : Confluent (stepRel B bubble index)) {s t : B.State index} :
    Nonempty (B.Conv bubble s t) ↔ Valley B bubble s t :=
  conv_iff_eqvGen.trans (confluent.eqvGen_iff_join.trans valley_iff_join.symm)

/-- **In a bubble decided by normal forms, a conversion holds exactly when both sides run forwards
to one normal term.** -/
theorem conv_iff_common_normal_form {S : Set (B.State index)}
    (decided : DecidedOn (stepRel B bubble index) S) {s t : B.State index} (inS : s ∈ S)
    (inT : t ∈ S) :
    Nonempty (B.Conv bubble s t) ↔
      ∃ normal, IsNormalFormOf (stepRel B bubble index) s normal ∧
        IsNormalFormOf (stepRel B bubble index) t normal := by
  rw [conv_iff_eqvGen]
  constructor
  · intro converted
    obtain ⟨first, firstForm⟩ := decided.1 s inS
    obtain ⟨second, secondForm⟩ := decided.1 t inT
    have same := (decided.2 s inS t inT first second firstForm secondForm).mp converted
    subst same
    exact ⟨first, firstForm, secondForm⟩
  · rintro ⟨normal, firstForm, secondForm⟩
    exact (decided.2 s inS t inT normal normal firstForm secondForm).mpr rfl

end Valleys

/-! ## Controls -/

namespace Controls

/-- A fork: the term `none` steps to every other term. -/
def fork : Bubbles.{0, 0, 0, 0} Unit where
  State := fun _ => Option Bool
  Bubble := Unit
  Step := fun _ {_} s t => PLift (s = none ∧ t ≠ none)

/-- The step of the fork to one of its two targets, as a conversion. -/
def forkStep (b : Bool) : fork.Conv () (index := ()) none (some b) :=
  ConversionEvidence.step (computation := computation fork.State (fork.Step ()))
    (source := none) (target := some b) (PLift.up ⟨rfl, Option.some_ne_none b⟩)

/-- **The two targets of the fork are convertible.** -/
theorem fork_converts : Nonempty (fork.Conv () (index := ()) (some true) (some false)) :=
  ⟨ConversionEvidence.trans (ConversionEvidence.symm (forkStep true)) (forkStep false)⟩

theorem fork_some_normal (b : Bool) : IsNormal (stepRel fork () ()) (some b) :=
  fun _ step => step.elim fun evidence => Option.some_ne_none b (PLift.down evidence).1

/-- **They have no valley**: their conversion passes through a peak, and no run forwards from
both sides meets. -/
theorem fork_no_valley : ¬ Valley fork () (index := ()) (some true) (some false) := by
  intro valley
  obtain ⟨common, fromTrue, fromFalse⟩ := valley_iff_join.mp valley
  have atTrue := (fork_some_normal true).reflTransGen_eq fromTrue
  have atFalse := (fork_some_normal false).reflTransGen_eq fromFalse
  have clash : (some true : Option Bool) = some false := atTrue.symm.trans atFalse
  exact absurd clash (by decide)

/-- An entry: every other term steps to `none`. -/
def entry : Bubbles.{0, 0, 0, 0} Unit where
  State := fun _ => Option Bool
  Bubble := Unit
  Step := fun _ {_} s t => PLift (s ≠ none ∧ t = none)

/-- **The two sources of the entry have a valley**, through the term they both step to. -/
theorem entry_valley : Valley entry () (index := ()) (some true) (some false) :=
  ⟨none,
    Zigzag.forward (B := entry) (bubble := ()) (index := ()) (source := some true)
      (middle := none) (target := none) (PLift.up ⟨Option.some_ne_none true, rfl⟩)
      (Zigzag.nil (B := entry) (bubble := ()) (index := ()) none),
    Zigzag.backward (B := entry) (bubble := ()) (index := ()) (source := none)
      (middle := some false) (target := some false) (PLift.up ⟨Option.some_ne_none false, rfl⟩)
      (Zigzag.nil (B := entry) (bubble := ()) (index := ()) (some false)),
    trivial, trivial⟩

end Controls

/-! ## Axiom audit -/

#print axioms valley_iff_join
#print axioms conv_of_valley
#print axioms conv_iff_valley
#print axioms conv_iff_common_normal_form
#print axioms Controls.fork_converts
#print axioms Controls.fork_no_valley
#print axioms Controls.entry_valley

end Mettapedia.TypeTheory.ConversionValleys
