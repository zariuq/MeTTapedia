import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullIndependence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# Independence at dependent frames: controls

The frame is `X : U0, x : X, g : Ground` (`triple`), in the cumulative tower. Rows are labelled `X`,
as a term of `U0` (`xUniverse`).

**Each clause of independence is needed.** In every negative control both firings are admitted at
the state, every other clause holds, and the step refuses the second firing after the first:
* `takes_clash_refused`: both take row `0`;
* `take_read_refused`: the first takes row `0`, which the second reads;
* `makes_clash_refused`: both make occurrence `1`;
* `tells_clash_refused`: the first tells `X ≐ Ground`, the second `X ≐ Ground → Ground`; each is
  solvable, the joint information is not;
* `query_written_refused`: the first makes the row `Ground`, inside the region of the second's
  absence query of `Ground`.

**The positive control** (`independent_pair`, `positive_diamond`): under the knowledge
`X ≐ Ground → Ground`, a firing that takes row `0` and makes row `1 : X` and a firing that asks the
absence of `Ground` and makes row `2 : Ground → Ground` are independent; the absence query is
unwritten because no solution equates `X` with `Ground`. The diamond closes in the step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.IndependenceControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open DependentFull.Controls
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

/-! ## The frame and its facts -/

/-- A state at `triple` whose rows are all `X : U0`. -/
def stateAt (K : EquationStore (TotalTerm triple)) (present : Finset Nat) : State Tower.rules Nat :=
  ⟨triple, K, present, fun _ => xUniverse⟩

/-- A store of reflexive equations is solved by the identity. -/
theorem solvable_refl {Δ : Context Tower.rules} (K : EquationStore (TotalTerm Δ))
    (reflexive : ∀ e ∈ K, e.1 = e.2) : (frames setting.levels).Solvable K :=
  ⟨Δ, 𝟙 Δ, fun e member => by
    show (frames setting.levels).E _ _
    rw [reflexive e member]
    exact ((frames setting.levels).equivalence _).refl _⟩

theorem toGround_solves :
    (frames setting.levels).E ((frames setting.levels).act toGround xUniverse)
      ((frames setting.levels).act toGround groundUniverse) := by
  show (frames setting.levels).E (xUniverse.reindex toGround) (groundUniverse.reindex toGround)
  rw [show xUniverse.reindex toGround = groundUniverse.reindex toGround from
    totalTerm_ext (TypeOver.ext rfl rfl) rfl]
  exact ((frames setting.levels).equivalence _).refl _

theorem toArrow_solves :
    (frames setting.levels).E ((frames setting.levels).act toArrow xUniverse)
      ((frames setting.levels).act toArrow arrowUniverse) := by
  show (frames setting.levels).E (xUniverse.reindex toArrow) (arrowUniverse.reindex toArrow)
  rw [show xUniverse.reindex toArrow = arrowUniverse.reindex toArrow from
    totalTerm_ext (TypeOver.ext rfl rfl) rfl]
  exact ((frames setting.levels).equivalence _).refl _

theorem refl_solves {Θ : Context Tower.rules} (τ : Θ ⟶ triple) (t : TotalTerm triple) :
    (frames setting.levels).E ((frames setting.levels).act τ t) ((frames setting.levels).act τ t) :=
  ((frames setting.levels).equivalence _).refl _

/-- `X` as a type of `U0`, at a solution: its code. -/
theorem typeEq_of_equal {Θ : Context Tower.rules} (τ : Θ ⟶ triple) {s t : TotalTerm triple}
    (sType : s.1 = smallUniverse _)
    (equated : (frames setting.levels).E ((frames setting.levels).act τ s) ((frames setting.levels).act τ t)) :
    TypeEq Tower.rules Θ.raw (subst τ.substitution s.2.code) (subst τ.substitution t.2.code) := by
  have k := equated.2
  have level : subst τ.substitution s.1.code = .head (.sort Tower.zero) := by
    rw [sType]
    rfl
  change Equal Tower.rules Θ.raw (subst τ.substitution s.2.code) (subst τ.substitution t.2.code)
    (subst τ.substitution s.1.code) at k
  rw [level] at k
  exact ⟨.sort Tower.zero, .sort _, k⟩

/-- **Under `X ≐ Ground → Ground`, no solution equates `Ground` with `X`.** -/
theorem ground_apart {Θ : Context Tower.rules} (τ : Θ ⟶ triple)
    (known : (frames setting.levels).E ((frames setting.levels).act τ xUniverse)
      ((frames setting.levels).act τ arrowUniverse)) :
    ¬ (frames setting.levels).E ((frames setting.levels).act τ groundUniverse)
      ((frames setting.levels).act τ xUniverse) := by
  intro equated
  have typeX : TypeEq Tower.rules Θ.raw (subst τ.substitution (.var 2)) arrow :=
    typeEq_of_equal τ rfl known
  have typeG : TypeEq Tower.rules Θ.raw ground (subst τ.substitution (.var 2)) :=
    typeEq_of_equal τ rfl equated
  exact ground_arrow_clash Θ.formed (typeG.trans setting.levels typeX)

/-! ## Firings -/

/-- Take row `0` with the pattern `X`. -/
def takeX : Plain setting.levels Nat triple := ⟨[0], [], [xUniverse], [], [], [], [], []⟩

/-- Read row `0` with the pattern `X`. -/
def readX : Plain setting.levels Nat triple := ⟨[], [0], [], [xUniverse], [], [], [], []⟩

/-- Make occurrence `1` with the row `X`. -/
def makeOne : Plain setting.levels Nat triple :=
  ⟨[], [], [], [], [(1, Make.ofRow xUniverse)], [], [], []⟩

/-- Tell `X ≐ Ground`. -/
def tellGround : Plain setting.levels Nat triple :=
  ⟨[], [], [], [], [], [(xUniverse, groundUniverse)], [], []⟩

/-- Tell `X ≐ Ground → Ground`. -/
def tellArrow : Plain setting.levels Nat triple :=
  ⟨[], [], [], [], [], [(xUniverse, arrowUniverse)], [], []⟩

/-- Make occurrence `1` with the row `Ground`. -/
def makeGround : Plain setting.levels Nat triple :=
  ⟨[], [], [], [], [(1, Make.ofRow groundUniverse)], [], [], []⟩

/-- Ask the absence of `Ground`. -/
def askNoGround : Plain setting.levels Nat triple :=
  ⟨[], [], [], [], [], [], [], [Query.absent setting.levels Nat groundUniverse]⟩

/-! ## Admissions -/

theorem takeX_admitted (K : EquationStore (TotalTerm triple)) (solvable : (frames setting.levels).Solvable
    (K ++ [(xUniverse, xUniverse)])) : takeX.Admits (stateAt K {0}).toLocal := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (Plain.enabled_iff _ _).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun o _ inside => absurd inside List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
    solvable, fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩⟩
  obtain rfl := List.mem_singleton.mp member
  exact Finset.mem_singleton_self 0

theorem readX_admitted : readX.Admits (stateAt [] {0}).toLocal := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil, fun o member => ?_,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
    solvable_refl _ fun e member => ?_, fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    rfl

/-- A firing that only makes rows is admitted where its occurrences are fresh and the knowledge is
solvable. -/
theorem maker_admitted (K : EquationStore (TotalTerm triple)) (present : Finset Nat) (o : Nat)
    (t : TotalTerm triple) (fresh : o ∉ present) (solvable : (frames setting.levels).Solvable K) :
    (⟨[], [], [], [], [(o, Make.ofRow t)], [], [], []⟩ : Plain setting.levels Nat triple).Admits
      (stateAt K present).toLocal := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o' member => ?_⟩, ?_, fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · obtain rfl := List.mem_singleton.mp member
    exact fresh
  · show (frames setting.levels).Solvable (K ++ ([] : EquationStore (TotalTerm triple)))
    rw [List.append_nil]
    exact solvable

theorem teller_admitted (e : Equation (TotalTerm triple)) (solvable : (frames setting.levels).Solvable [e]) :
    (⟨[], [], [], [], [], [e], [], []⟩ : Plain setting.levels Nat triple).Admits (stateAt [] {0}).toLocal :=
  ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩, solvable,
    fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩⟩

theorem tellGround_admitted : tellGround.Admits (stateAt [] {0}).toLocal :=
  teller_admitted _ ⟨_, toGround, fun e member => by
    obtain rfl := List.mem_singleton.mp member
    exact toGround_solves⟩

theorem tellArrow_admitted : tellArrow.Admits (stateAt [] {0}).toLocal :=
  teller_admitted _ ⟨_, toArrow, fun e member => by
    obtain rfl := List.mem_singleton.mp member
    exact toArrow_solves⟩

theorem askNoGround_admitted : askNoGround.Admits (stateAt [] ∅).toLocal := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩, solvable_refl _ fun _ member => ?_, ?_⟩
  · exact absurd member List.not_mem_nil
  · intro b τ _
    refine ⟨fun _ member => absurd member List.not_mem_nil, fun q member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    exact (Query.absent_holds_iff _ _ _ τ).mpr fun o present => absurd present (Finset.notMem_empty o)

/-! ## Each clause is needed -/

theorem solvable_nil : (frames setting.levels).Solvable ([] : EquationStore (TotalTerm triple)) :=
  solvable_refl _ fun _ member => absurd member List.not_mem_nil

theorem takeX_admitted_here : takeX.Admits (stateAt [] {0}).toLocal :=
  takeX_admitted [] (solvable_refl _ fun e member => by
    obtain rfl := List.mem_singleton.mp member
    rfl)

/-- **Both firings of every negative control are admitted by the step at the state.** -/
theorem negatives_admitted :
    (Plain.toFiring (s := stateAt [] {0}) takeX).Admits ∧ (Plain.toFiring (s := stateAt [] {0}) readX).Admits ∧
      (Plain.toFiring (s := stateAt [] {0}) makeOne).Admits ∧
      (Plain.toFiring (s := stateAt [] {0}) tellGround).Admits ∧
      (Plain.toFiring (s := stateAt [] {0}) tellArrow).Admits ∧
      (Plain.toFiring (s := stateAt [] ∅) makeGround).Admits ∧
      (Plain.toFiring (s := stateAt [] ∅) askNoGround).Admits :=
  ⟨(Plain.admits_toFiring _).mpr takeX_admitted_here, (Plain.admits_toFiring _).mpr readX_admitted,
    (Plain.admits_toFiring _).mpr (maker_admitted [] {0} 1 xUniverse (by decide) solvable_nil),
    (Plain.admits_toFiring _).mpr tellGround_admitted, (Plain.admits_toFiring _).mpr tellArrow_admitted,
    (Plain.admits_toFiring _).mpr (maker_admitted [] ∅ 1 groundUniverse (Finset.notMem_empty 1) solvable_nil),
    (Plain.admits_toFiring _).mpr askNoGround_admitted⟩

/-- The step refuses a residual whenever one order's clauses fail at the state's frame. -/
theorem refused_of {s : State Tower.rules Nat} {f g : Plain setting.levels Nat s.frame}
    (first : (Plain.toFiring f).Admits) (second : g.Admits s.toLocal)
    (fails : ¬ ((∀ o ∈ g.taken, o ∉ f.taken) ∧ (∀ o ∈ g.read, o ∉ f.taken) ∧
      (∀ o ∈ g.made, o ∉ f.made) ∧ (frames setting.levels).Solvable (joint s.toLocal f g))) :
    ¬ (Plain.toFiring (Plain.residual f g first)).Admits := fun admitted =>
  fails (residual_clauses ((Plain.admits_toFiring f).mp first) second _
    ((Plain.admits_residual_iff f g first).mp admitted))

/-- **Disjoint takes are needed**: both firings take row `0`. -/
theorem takes_clash_refused (first : (Plain.toFiring (s := stateAt [] {0}) takeX).Admits) :
    ¬ (Plain.toFiring (Plain.residual (s := stateAt [] {0}) takeX takeX first)).Admits :=
  refused_of first takeX_admitted_here
    fun ⟨apart, _⟩ => apart 0 (List.mem_singleton_self 0) (List.mem_singleton_self 0)

/-- **Reads must not be taken**: the first takes row `0`, which the second reads. -/
theorem take_read_refused (first : (Plain.toFiring (s := stateAt [] {0}) takeX).Admits) :
    ¬ (Plain.toFiring (Plain.residual (s := stateAt [] {0}) takeX readX first)).Admits :=
  refused_of first readX_admitted
    fun ⟨_, kept, _⟩ => kept 0 (List.mem_singleton_self 0) (List.mem_singleton_self 0)

/-- **Distinct made occurrences are needed**: both firings make occurrence `1`. -/
theorem makes_clash_refused (first : (Plain.toFiring (s := stateAt [] {0}) makeOne).Admits) :
    ¬ (Plain.toFiring (Plain.residual (s := stateAt [] {0}) makeOne makeOne first)).Admits :=
  refused_of first (maker_admitted [] {0} 1 xUniverse (by decide) solvable_nil)
    fun ⟨_, _, apart, _⟩ => apart 1 (List.mem_singleton_self 1) (List.mem_singleton_self 1)

theorem tells_joint : joint (stateAt [] {0}).toLocal tellGround tellArrow =
    [(xUniverse, groundUniverse), (xUniverse, arrowUniverse)] := rfl

/-- The joint information of the two tells is refuted. -/
theorem tells_joint_refuted :
    ¬ (frames setting.levels).Solvable (joint (stateAt [] {0}).toLocal tellGround tellArrow) := by
  rintro ⟨Θ, τ, solved⟩
  have solved : (frames setting.levels).Models τ
      [(xUniverse, groundUniverse), (xUniverse, arrowUniverse)] := solved
  have ground : (frames setting.levels).E ((frames setting.levels).act τ xUniverse)
      ((frames setting.levels).act τ groundUniverse) :=
    solved (xUniverse, groundUniverse) (List.mem_cons.mpr (.inl rfl))
  have arrow' : (frames setting.levels).E ((frames setting.levels).act τ xUniverse)
      ((frames setting.levels).act τ arrowUniverse) :=
    solved (xUniverse, arrowUniverse) (List.mem_cons.mpr (.inr (List.mem_singleton_self _)))
  exact ground_apart τ arrow' (((frames setting.levels).equivalence Θ).symm ground)

/-- **Consistent joint information is needed**: `X ≐ Ground` and `X ≐ Ground → Ground` are each
admitted, and not after each other. -/
theorem tells_clash_refused (first : (Plain.toFiring (s := stateAt [] {0}) tellGround).Admits) :
    ¬ (Plain.toFiring (Plain.residual (s := stateAt [] {0}) tellGround tellArrow first)).Admits :=
  refused_of first tellArrow_admitted fun ⟨_, _, _, solvable⟩ => tells_joint_refuted solvable

/-- **The query clause is needed**: the first firing makes the row `Ground`, inside the region of
the second's absence query of `Ground`. Both are admitted at the state with no rows; the second is
refused after the first. -/
theorem query_written_refused (first : (Plain.toFiring (s := stateAt [] ∅) makeGround).Admits) :
    ¬ (Plain.toFiring (Plain.residual (s := stateAt [] ∅) makeGround askNoGround first)).Admits := by
  intro admitted
  have after := (Plain.admits_residual_iff (s := stateAt [] ∅) makeGround askNoGround first).mp admitted
  obtain ⟨-, -, -, queries⟩ := after
  have holds := (queries triple (𝟙 triple) (Frames.models_nil _)).2 _
    (List.mem_singleton_self _)
  have absent := (Query.absent_holds_iff _ _ _ (𝟙 triple)).mp holds 1
    ((makeGround.mem_fire_iff _ 1).mpr (.inr (List.mem_singleton_self 1)))
  exact absent (refl_solves (𝟙 triple) groundUniverse)

/-! ## The positive control -/

/-- The knowledge `X ≐ Ground → Ground`. -/
def arrowKnown : EquationStore (TotalTerm triple) := [(xUniverse, arrowUniverse)]

/-- Take row `0` with the pattern `X` and make row `1 : X`. -/
def consume : Plain setting.levels Nat triple :=
  ⟨[0], [], [xUniverse], [], [(1, Make.ofRow xUniverse)], [], [], []⟩

/-- Ask the absence of `Ground` and make row `2 : Ground → Ground`. -/
def observe : Plain setting.levels Nat triple :=
  ⟨[], [], [], [], [(2, Make.ofRow arrowUniverse)], [], [], [Query.absent setting.levels Nat groundUniverse]⟩

theorem arrowKnown_solved {Θ : Context Tower.rules} {τ : Θ ⟶ triple} {K : EquationStore (TotalTerm triple)}
    (inside : (xUniverse, arrowUniverse) ∈ K) (solved : (frames setting.levels).Models τ K) :
    (frames setting.levels).E ((frames setting.levels).act τ xUniverse)
      ((frames setting.levels).act τ arrowUniverse) :=
  solved _ inside

theorem consume_information : consume.information (stateAt arrowKnown {0}).toLocal =
    [(xUniverse, arrowUniverse), (xUniverse, xUniverse)] := rfl

theorem observe_information : observe.information (stateAt arrowKnown {0}).toLocal =
    [(xUniverse, arrowUniverse)] := rfl

theorem pair_joint : joint (stateAt arrowKnown {0}).toLocal consume observe =
    [(xUniverse, arrowUniverse), (xUniverse, xUniverse)] := rfl

theorem consume_admitted : consume.Admits (stateAt arrowKnown {0}).toLocal := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (Plain.enabled_iff _ _).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ inside => absurd inside List.not_mem_nil, fun o member => ?_⟩, ⟨_, toArrow, ?_⟩,
    fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    decide
  · intro e member
    rw [consume_information] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact toArrow_solves
    obtain rfl := List.mem_singleton.mp member
    exact refl_solves toArrow xUniverse

theorem observe_admitted : observe.Admits (stateAt arrowKnown {0}).toLocal := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o member => ?_⟩, ⟨_, toArrow, fun e member => ?_⟩, fun b τ solved => ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · obtain rfl := List.mem_singleton.mp member
    decide
  · rw [observe_information] at member
    obtain rfl := List.mem_singleton.mp member
    exact toArrow_solves
  · refine ⟨fun _ member => absurd member List.not_mem_nil, fun q member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    refine (Query.absent_holds_iff _ _ _ τ).mpr fun o _ => ?_
    exact ground_apart τ (arrowKnown_solved (K := observe.information (stateAt arrowKnown {0}).toLocal)
      (List.mem_append_left _ (List.mem_singleton_self _)) solved)

/-- **The two firings are independent**: disjoint takes, no read taken, distinct made occurrences,
solvable joint information, and the absence query unwritten, since no joint solution equates `X`
with `Ground`. -/
theorem independent_pair : Independent (stateAt arrowKnown {0}).toLocal consume observe where
  takes_apart := fun _ _ inside => absurd inside List.not_mem_nil
  left_keeps_reads := fun _ _ inside => absurd inside List.not_mem_nil
  right_keeps_reads := fun _ inside => absurd inside List.not_mem_nil
  made_apart := fun o one two => by
    obtain rfl := List.mem_singleton.mp one
    exact absurd (List.mem_singleton.mp two) (by decide)
  joint_solvable := ⟨_, toArrow, fun e member => by
    rw [pair_joint] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact toArrow_solves
    obtain rfl := List.mem_singleton.mp member
    exact refl_solves toArrow xUniverse⟩
  left_unwritten := fun q member b τ solved => by
    obtain rfl := List.mem_singleton.mp member
    have known := arrowKnown_solved (K := joint (stateAt arrowKnown {0}).toLocal consume observe)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))) solved
    rintro (⟨o, -, inside⟩ | ⟨m, made, typed, inside⟩)
    · exact ground_apart τ known inside
    · obtain rfl := List.mem_singleton.mp made
      exact ground_apart τ known inside
  right_unwritten := fun _ member => absurd member List.not_mem_nil

/-- **The diamond closes in the step** for the independent pair. -/
theorem positive_diamond (first : (Plain.toFiring (s := stateAt arrowKnown {0}) consume).Admits)
    (second : (Plain.toFiring (s := stateAt arrowKnown {0}) observe).Admits) :
    ∃ (afterFirst : (Plain.toFiring (Plain.residual (s := stateAt arrowKnown {0}) consume observe first)).Admits)
      (afterSecond : (Plain.toFiring (Plain.residual (s := stateAt arrowKnown {0}) observe consume second)).Admits),
      State.Agree (levels := setting.levels) ((Plain.toFiring (Plain.residual (s := stateAt arrowKnown {0}) consume observe first)).after afterFirst)
        ((Plain.toFiring (Plain.residual (s := stateAt arrowKnown {0}) observe consume second)).after afterSecond) :=
  diamond first second independent_pair

/-- Both firings of the positive control are admitted by the step. -/
theorem positive_admitted :
    (Plain.toFiring (s := stateAt arrowKnown {0}) consume).Admits ∧
      (Plain.toFiring (s := stateAt arrowKnown {0}) observe).Admits :=
  ⟨(Plain.admits_toFiring _).mpr consume_admitted, (Plain.admits_toFiring _).mpr observe_admitted⟩

end DependentFull.IndependenceControls

#print axioms DependentFull.IndependenceControls.ground_apart
#print axioms DependentFull.IndependenceControls.negatives_admitted
#print axioms DependentFull.IndependenceControls.takes_clash_refused
#print axioms DependentFull.IndependenceControls.take_read_refused
#print axioms DependentFull.IndependenceControls.makes_clash_refused
#print axioms DependentFull.IndependenceControls.tells_joint_refuted
#print axioms DependentFull.IndependenceControls.tells_clash_refused
#print axioms DependentFull.IndependenceControls.query_written_refused
#print axioms DependentFull.IndependenceControls.independent_pair
#print axioms DependentFull.IndependenceControls.positive_admitted
#print axioms DependentFull.IndependenceControls.positive_diamond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
