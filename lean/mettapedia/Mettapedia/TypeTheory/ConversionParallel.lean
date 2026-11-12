import Mettapedia.TypeTheory.ConversionRuns

/-!
# Two conversion goals side by side

A type with two indices needs two conversions, and neither waits for the other. This module puts
two goals of the conversion step of `ConversionRuns` side by side, as one effect with two
occurrences, and proves the interchange of their firings.

* **States** (`Pair`): two goals, each with its own term, ledger and occurrence. The knowledge of
  a pair is what both goals were told (`knowledgeOf`).
* **Candidates** (`PairClaim`): a candidate at the left goal or at the right goal. Its effect
  takes and remakes the occurrence of its own goal and leaves the other goal untouched
  (`selectionOf`, `resultOf`); the step admits it by evidence (`pairStep`, `pair_admits_iff`).
* **The diamond, on the nose** (`diamond`): a candidate at the left goal and one at the right
  goal lead to the same pair in either order.
* **Interchange** (`interchange`, `interchange_traces`): the two orders are both runs, end at the
  same pair, and trace the same zigzag at each goal (`leftZigzag`, `rightZigzag`).
* **Runs of the pair reach exactly the pairs of conversions** (`pair_conv_iff`).

"Parallel" here is the side-by-side composition of two goals. It is not parallel reduction, the
technique by which other modules of the tree prove confluence of a conversion.

Scope: two goals of one bubble in one fibre, each with its own ledger, so that the two orders
agree as states and not only up to a permutation of what was told. That every two runs with the
same two traces differ by exchanges of adjacent firings at different goals is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ConversionParallel

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.ConversionRuns

universe uIndex uState uBubble uStep

variable {Index : Type uIndex}

/-- Two conversion goals side by side, each with its own ledger and occurrence. -/
structure Pair (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (index : Index) where
  left : Goal B index
  right : Goal B index

section Core

variable (B : Bubbles.{uIndex, uState, uBubble, uStep} Index) (bubble : B.Bubble) (index : Index)

/-- A candidate at a pair: a candidate at its left goal or at its right goal. -/
abbrev PairClaim (pair : Pair B index) : Type (max uState uStep) :=
  Claim B bubble pair.left.cursor ⊕ Claim B bubble pair.right.cursor

variable {B bubble index}

/-- The occurrences a candidate takes and makes: those of its own goal. -/
def selectionOf {pair : Pair B index} : PairClaim B bubble index pair → Selection (Bool × Nat)
  | .inl _ => ⟨[(false, pair.left.clock)], [], [(false, pair.left.clock + 1)]⟩
  | .inr _ => ⟨[(true, pair.right.clock)], [], [(true, pair.right.clock + 1)]⟩

/-- The pair after a candidate: its own goal moves, is told the equation and gets a new
occurrence; the other goal is untouched. -/
def resultOf {pair : Pair B index} : PairClaim B bubble index pair → Pair B index
  | .inl claim =>
      ⟨⟨claim.target, pair.left.ledger ++ [(pair.left.cursor, claim.target)], pair.left.clock + 1⟩,
        pair.right⟩
  | .inr claim =>
      ⟨pair.left,
        ⟨claim.target, pair.right.ledger ++ [(pair.right.cursor, claim.target)],
          pair.right.clock + 1⟩⟩

/-- The knowledge of a pair: what both goals were told. -/
def knowledgeOf (pair : Pair B index) : EquationStore (B.State index) :=
  pair.left.ledger ++ pair.right.ledger

theorem knowledge_subset_result {pair : Pair B index} (claim : PairClaim B bubble index pair) :
    ∀ e ∈ knowledgeOf pair, e ∈ knowledgeOf (resultOf claim) := by
  intro e member
  cases claim with
  | inl claim =>
      rcases List.mem_append.mp member with inLeft | inRight
      · exact List.mem_append_left _ (List.mem_append_left _ inLeft)
      · exact List.mem_append_right _ inRight
  | inr claim =>
      rcases List.mem_append.mp member with inLeft | inRight
      · exact List.mem_append_left _ inLeft
      · exact List.mem_append_right _ (List.mem_append_left _ inRight)

/-- A candidate at a pair is witnessed when the candidate of its goal is. -/
def WitnessedAt {pair : Pair B index} : PairClaim B bubble index pair → Prop
  | .inl claim => claim.Witnessed
  | .inr claim => claim.Witnessed

variable (B bubble index)

/-- The effect of a candidate at a pair, before any permission. -/
def pairCore : EffectCore (conversionFrames (B.State index)) (Bool × Nat) (Pair B index)
    (fun pair => PairClaim B bubble index pair) where
  frame := fun _ => Identification.equality
  knowledge := fun pair => knowledgeOf pair
  present := fun pair => {(false, pair.left.clock), (true, pair.right.clock)}
  selection := fun {_} claim => selectionOf claim
  target := fun _ => Identification.equality
  extension := fun _ => ⟨fun _ _ related => related⟩
  information := fun {_} claim => knowledgeOf (resultOf claim)
  information_refines := by
    intro pair claim model coarsening solved e member
    exact solved e (knowledge_subset_result claim e member)
  Shapes := fun _ => True
  preparedResult := fun {_} claim _ => resultOf claim
  present_preparedResult := by
    intro pair claim _
    cases claim with
    | inl claim =>
        ext ⟨side, clock⟩
        cases side <;> simp [fire, Selection.commit, selectionOf, resultOf]
    | inr claim =>
        ext ⟨side, clock⟩
        cases side <;> simp [fire, Selection.commit, selectionOf, resultOf]
  preparedSettle := fun _ _ => ⟨fun _ _ related => related⟩
  result_refines := by
    intro pair claim _ model coarsening solved
    exact solved

/-- **The conversion step of two goals side by side**, admitted by evidence. -/
def pairStep : Step (conversionFrames (B.State index)) (Bool × Nat) (Pair B index)
    (fun pair => PairClaim B bubble index pair) :=
  Step.ofEffect (pairCore B bubble index) (fun claim _ => WitnessedAt claim)

/-- Every candidate at a pair is prepared: its occurrence is present and the next one is fresh. -/
theorem pair_prepared {pair : Pair B index} (claim : PairClaim B bubble index pair) :
    (pairCore B bubble index).Prepares claim := by
  refine ⟨trivial, ?_, Identification.total, ⟨fun _ _ _ => trivial⟩, fun _ _ => trivial⟩
  cases claim with
  | inl claim =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pairCore, Selection.commit, selectionOf]
  | inr claim =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pairCore, Selection.commit, selectionOf]

/-- The step admits exactly the witnessed candidates. -/
theorem pair_admits_iff {pair : Pair B index} (claim : PairClaim B bubble index pair) :
    (pairStep B bubble index).Admits claim ↔ WitnessedAt claim :=
  ⟨fun admitted => admitted.elim fun _ seen => seen,
    fun seen => ⟨pair_prepared B bubble index claim, seen⟩⟩

end Core

section Interchange

variable {B : Bubbles.{uIndex, uState, uBubble, uStep} Index} {bubble : B.Bubble} {index : Index}

/-- **The diamond, on the nose.** A candidate at the left goal and a candidate at the right goal
lead to the same pair in either order. -/
theorem diamond {pair : Pair B index} (leftClaim : Claim B bubble pair.left.cursor)
    (rightClaim : Claim B bubble pair.right.cursor) :
    resultOf (pair := resultOf (Sum.inl leftClaim : PairClaim B bubble index pair))
        (Sum.inr rightClaim) =
      resultOf (pair := resultOf (Sum.inr rightClaim : PairClaim B bubble index pair))
        (Sum.inl leftClaim) :=
  rfl

/-- The run that fires at the left goal and then at the right one. -/
def leftThenRight (pair : Pair B index) (leftClaim : Claim B bubble pair.left.cursor)
    (rightClaim : Claim B bubble pair.right.cursor) (leftSeen : leftClaim.Witnessed)
    (rightSeen : rightClaim.Witnessed) : (pairStep B bubble index).Run pair :=
  Step.Run.cons (P := pairStep B bubble index) (s := pair) (Sum.inl leftClaim)
    ((pair_admits_iff B bubble index (pair := pair) (Sum.inl leftClaim)).mpr leftSeen)
    (Step.Run.cons (P := pairStep B bubble index)
      (s := resultOf (Sum.inl leftClaim : PairClaim B bubble index pair)) (Sum.inr rightClaim)
      ((pair_admits_iff B bubble index
        (pair := resultOf (Sum.inl leftClaim : PairClaim B bubble index pair))
        (Sum.inr rightClaim)).mpr rightSeen)
      (Step.Run.nil (P := pairStep B bubble index) _))

/-- The run that fires at the right goal and then at the left one. -/
def rightThenLeft (pair : Pair B index) (leftClaim : Claim B bubble pair.left.cursor)
    (rightClaim : Claim B bubble pair.right.cursor) (leftSeen : leftClaim.Witnessed)
    (rightSeen : rightClaim.Witnessed) : (pairStep B bubble index).Run pair :=
  Step.Run.cons (P := pairStep B bubble index) (s := pair) (Sum.inr rightClaim)
    ((pair_admits_iff B bubble index (pair := pair) (Sum.inr rightClaim)).mpr rightSeen)
    (Step.Run.cons (P := pairStep B bubble index)
      (s := resultOf (Sum.inr rightClaim : PairClaim B bubble index pair)) (Sum.inl leftClaim)
      ((pair_admits_iff B bubble index
        (pair := resultOf (Sum.inr rightClaim : PairClaim B bubble index pair))
        (Sum.inl leftClaim)).mpr leftSeen)
      (Step.Run.nil (P := pairStep B bubble index) _))

/-- **Interchange.** The two orders are both runs, and they end at the same pair. -/
theorem interchange (pair : Pair B index) (leftClaim : Claim B bubble pair.left.cursor)
    (rightClaim : Claim B bubble pair.right.cursor) (leftSeen : leftClaim.Witnessed)
    (rightSeen : rightClaim.Witnessed) :
    (leftThenRight pair leftClaim rightClaim leftSeen rightSeen).last =
      (rightThenLeft pair leftClaim rightClaim leftSeen rightSeen).last :=
  rfl

/-- The zigzag a run traces at the left goal. -/
def leftZigzag : {pair : Pair B index} → (run : (pairStep B bubble index).Run pair) →
    Zigzag B bubble pair.left.cursor run.last.left.cursor
  | _, .nil pair => Zigzag.nil pair.left.cursor
  | _, .cons (.inl claim) admitted rest =>
      claim.zigzag ((pair_admits_iff B bubble index (Sum.inl claim)).mp admitted) (leftZigzag rest)
  | _, .cons (.inr _) _ rest => leftZigzag rest

/-- The zigzag a run traces at the right goal. -/
def rightZigzag : {pair : Pair B index} → (run : (pairStep B bubble index).Run pair) →
    Zigzag B bubble pair.right.cursor run.last.right.cursor
  | _, .nil pair => Zigzag.nil pair.right.cursor
  | _, .cons (.inl _) _ rest => rightZigzag rest
  | _, .cons (.inr claim) admitted rest =>
      claim.zigzag ((pair_admits_iff B bubble index (Sum.inr claim)).mp admitted) (rightZigzag rest)

/-- The two orders trace the same zigzag at each goal. -/
theorem interchange_traces (pair : Pair B index) (leftClaim : Claim B bubble pair.left.cursor)
    (rightClaim : Claim B bubble pair.right.cursor) (leftSeen : leftClaim.Witnessed)
    (rightSeen : rightClaim.Witnessed) :
    leftZigzag (leftThenRight pair leftClaim rightClaim leftSeen rightSeen) =
        leftZigzag (rightThenLeft pair leftClaim rightClaim leftSeen rightSeen) ∧
      rightZigzag (leftThenRight pair leftClaim rightClaim leftSeen rightSeen) =
        rightZigzag (rightThenLeft pair leftClaim rightClaim leftSeen rightSeen) :=
  ⟨rfl, rfl⟩

/-- Every zigzag at the right goal is followed by a run that leaves the left goal as it is. -/
theorem right_reach : ∀ {s t : B.State index}, Zigzag B bubble s t → ∀ (left : Goal B index)
    (ledger : EquationStore (B.State index)) (clock : Nat),
    ∃ run : (pairStep B bubble index).Run ⟨left, ⟨s, ledger, clock⟩⟩,
      run.last.right.cursor = t ∧ run.last.left = left
  | s, _, .nil _, left, ledger, clock =>
      ⟨Step.Run.nil (P := pairStep B bubble index) (Pair.mk left (Goal.mk s ledger clock)), rfl, rfl⟩
  | s, _, .forward (middle := middle) step rest, left, ledger, clock =>
      (right_reach rest left (ledger ++ [(s, middle)]) (clock + 1)).elim fun run ends =>
        ⟨Step.Run.cons (P := pairStep B bubble index) (s := Pair.mk left (Goal.mk s ledger clock))
          (Sum.inr (Claim.forward middle step))
          ((pair_admits_iff B bubble index (pair := Pair.mk left (Goal.mk s ledger clock))
            (Sum.inr (Claim.forward middle step))).mpr trivial) run, ends⟩
  | s, _, .backward (middle := middle) step rest, left, ledger, clock =>
      (right_reach rest left (ledger ++ [(s, middle)]) (clock + 1)).elim fun run ends =>
        ⟨Step.Run.cons (P := pairStep B bubble index) (s := Pair.mk left (Goal.mk s ledger clock))
          (Sum.inr (Claim.backward middle step))
          ((pair_admits_iff B bubble index (pair := Pair.mk left (Goal.mk s ledger clock))
            (Sum.inr (Claim.backward middle step))).mpr trivial) run, ends⟩

/-- Every pair of zigzags is followed by a run of the pair, the left one first. -/
theorem pair_reach : ∀ {s t : B.State index}, Zigzag B bubble s t → ∀ {s' t' : B.State index},
    Zigzag B bubble s' t' → ∀ (ledger : EquationStore (B.State index)) (clock : Nat)
      (ledger' : EquationStore (B.State index)) (clock' : Nat),
      ∃ run : (pairStep B bubble index).Run ⟨⟨s, ledger, clock⟩, ⟨s', ledger', clock'⟩⟩,
        run.last.left.cursor = t ∧ run.last.right.cursor = t'
  | s, _, .nil _, _, _, second, ledger, clock, ledger', clock' =>
      (right_reach second (Goal.mk s ledger clock) ledger' clock').elim fun run ends =>
        ⟨run, congrArg Goal.cursor ends.2, ends.1⟩
  | s, _, .forward (middle := middle) step rest, s', _, second, ledger, clock, ledger', clock' =>
      (pair_reach rest second (ledger ++ [(s, middle)]) (clock + 1) ledger' clock').elim
        fun run ends =>
          ⟨Step.Run.cons (P := pairStep B bubble index)
            (s := Pair.mk (Goal.mk s ledger clock) (Goal.mk s' ledger' clock'))
            (Sum.inl (Claim.forward middle step))
            ((pair_admits_iff B bubble index
              (pair := Pair.mk (Goal.mk s ledger clock) (Goal.mk s' ledger' clock'))
              (Sum.inl (Claim.forward middle step))).mpr trivial) run, ends⟩
  | s, _, .backward (middle := middle) step rest, s', _, second, ledger, clock, ledger', clock' =>
      (pair_reach rest second (ledger ++ [(s, middle)]) (clock + 1) ledger' clock').elim
        fun run ends =>
          ⟨Step.Run.cons (P := pairStep B bubble index)
            (s := Pair.mk (Goal.mk s ledger clock) (Goal.mk s' ledger' clock'))
            (Sum.inl (Claim.backward middle step))
            ((pair_admits_iff B bubble index
              (pair := Pair.mk (Goal.mk s ledger clock) (Goal.mk s' ledger' clock'))
              (Sum.inl (Claim.backward middle step))).mpr trivial) run, ends⟩

/-- **Runs of two goals side by side reach exactly the pairs of conversions.** -/
theorem pair_conv_iff {s t s' t' : B.State index} :
    (∃ run : (pairStep B bubble index).Run ⟨⟨s, [], 0⟩, ⟨s', [], 0⟩⟩,
        run.last.left.cursor = t ∧ run.last.right.cursor = t') ↔
      Nonempty (B.Conv bubble s t) ∧ Nonempty (B.Conv bubble s' t') := by
  constructor
  · rintro ⟨run, atLeft, atRight⟩
    subst atLeft
    subst atRight
    exact ⟨⟨(leftZigzag run).toConv⟩, ⟨(rightZigzag run).toConv⟩⟩
  · rintro ⟨⟨first⟩, ⟨second⟩⟩
    exact pair_reach (Zigzag.ofConv first) (Zigzag.ofConv second) [] 0 [] 0

end Interchange

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.ConversionRuns.Controls

/-- In the bubble with no declared step, a pair of goals at `false` and `false`. -/
def silentPair : Pair silent () := ⟨⟨false, [], 0⟩, ⟨false, [], 0⟩⟩

/-- **A candidate with no evidence is refused at a pair too.** -/
theorem silent_pair_refused :
    ¬ (pairStep silent () ()).Admits
      (Sum.inl (Claim.asserted true) : PairClaim silent () () silentPair) :=
  fun admitted =>
    (pair_admits_iff silent () () (pair := silentPair) (Sum.inl (Claim.asserted true))).mp admitted

/-- **No run of that pair moves either goal.** -/
theorem silent_pair_stays (run : (pairStep silent () ()).Run silentPair) :
    run.last.left.cursor = false ∧ run.last.right.cursor = false :=
  ⟨(silent_zigzag (leftZigzag run)).symm, (silent_zigzag (rightZigzag run)).symm⟩

/-- In the bubble with declared loops, the two orders of two firings end at the same pair. -/
theorem loops_interchange :
    (leftThenRight (B := loops) (bubble := ()) (index := ()) ⟨⟨(), [], 0⟩, ⟨(), [], 0⟩⟩
        (Claim.forward () false) (Claim.forward () true) trivial trivial).last =
      (rightThenLeft (B := loops) (bubble := ()) (index := ()) ⟨⟨(), [], 0⟩, ⟨(), [], 0⟩⟩
        (Claim.forward () false) (Claim.forward () true) trivial trivial).last :=
  rfl

end Controls

/-! ## Axiom audit -/

#print axioms pairStep
#print axioms pair_admits_iff
#print axioms diamond
#print axioms interchange
#print axioms interchange_traces
#print axioms pair_conv_iff
#print axioms Controls.silent_pair_refused
#print axioms Controls.silent_pair_stays
#print axioms Controls.loops_interchange

end Mettapedia.TypeTheory.ConversionParallel
