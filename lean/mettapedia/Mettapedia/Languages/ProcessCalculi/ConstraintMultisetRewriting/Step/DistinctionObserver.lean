import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGeneric
import Mettapedia.GSLT.Distinction.StatusObservers
import Mettapedia.GSLT.Distinction.BehaviouralMetric

/-!
# Distinction observers of transform programs

An observer of a transform program reads states, not substitution frames.
Its exact update condition is equality of labelled successor-observation sets
on each encoding fibre. Together with preservation of current observations,
this is exactly bisimulation of the encoding kernel. Quotient transitions
then lift from every representative; an existential quotient cannot invent a
transition by silently switching representatives.

The existing distinction-calculus behavioural tolerance applies to the same
observed step. Raw tolerances and constraint-solver frame maps remain separate
objects with their own laws.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionObserver
open Interface
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction
open Mettapedia.Cybernetics.DistinctionCalculus

universe uOb uT uH uO uS uF uL uV uQ
variable {Obj : Type uOb} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uS}
  {Fir : State → Type uF} {L : Type uL} {V : Type uV} {Q : Type uQ}
  (P : Interface.Step X O State Fir) (offers : L → (s : State) → Fir s → Prop)

def observed (read : State → V) : System (Race.Generic.gslt P offers) :=
  (Race.Generic.system P offers).withReading read (fun same => congrArg read same)

def successors (encode : State → Q) (s : State) (label : L) : Set Q :=
  {q | ∃ t, Race.Generic.Moves P offers s label t ∧ encode t = q}

/-- Update compatibility includes enabling and both directions of nondeterminism. -/
def Stable (encode : State → Q) : Prop :=
  ∀ s t, encode s = encode t → ∀ label,
    successors P offers encode s label = successors P offers encode t label

def Reads (encode : State → Q) (read : State → V) : Prop :=
  ∀ s t, encode s = encode t → read s = read t

theorem stable_iff_matching (encode : State → Q) :
    Stable P offers encode ↔
      ∀ s t, encode s = encode t → ∀ label s', Race.Generic.Moves P offers s label s' →
        ∃ t', Race.Generic.Moves P offers t label t' ∧ encode s' = encode t' := by
  constructor
  · intro stable s t same label s' move
    have member : encode s' ∈ successors P offers encode s label := ⟨s', move, rfl⟩
    rw [stable s t same label] at member
    obtain ⟨t', moved, equal⟩ := member
    exact ⟨t', moved, equal.symm⟩
  · intro matching s t same label
    ext value
    constructor
    · rintro ⟨s', move, rfl⟩
      obtain ⟨t', moved, equal⟩ := matching s t same label s' move
      exact ⟨t', moved, equal.symm⟩
    · rintro ⟨t', move, rfl⟩
      obtain ⟨s', moved, equal⟩ := matching t s same.symm label t' move
      exact ⟨s', moved, equal.symm⟩

/-- Exact abstraction is a behavioural property, with the protected observations stated. -/
theorem exact_iff_kernel_bisimulation (encode : State → Q) (read : State → V) :
    Stable P offers encode ∧ Reads encode read ↔
      (observed P offers read).IsBisimulation (fun s t => encode s = encode t) := by
  change Stable P offers encode ∧ Reads encode read ↔
    ((Race.Generic.system P offers).withReading read (fun same => congrArg read same)).IsBisimulation _
  rw [System.withReading_isBisimulation_iff]
  constructor
  · rintro ⟨stable, reads⟩
    have matching := (stable_iff_matching P offers encode).mp stable
    exact ⟨⟨fun s t same label s' move => matching s t same label s' move,
      fun s t same label t' move => by
        obtain ⟨s', moved, equal⟩ := matching t s same.symm label t' move
        exact ⟨s', moved, equal.symm⟩⟩, fun s t same => reads s t same⟩
  · rintro ⟨⟨forth, _⟩, reads⟩
    exact ⟨(stable_iff_matching P offers encode).mpr (fun s t same label s' move =>
      forth same label move), fun s t same => reads same⟩

theorem exact_preserves_modal (encode : State → Q) (read : State → V)
    (exactView : Stable P offers encode ∧ Reads encode read) {s t : State}
    (same : encode s = encode t) (formula : Formula V L) :
    (observed P offers read).sat formula s ↔ (observed P offers read).sat formula t :=
  (observed P offers read).logicallyEquivalent_of_bisimilar
    ⟨_, (exact_iff_kernel_bisimulation P offers encode read).mp exactView, same⟩ formula

/-- Existential quotient transitions; their adequacy requires stability. -/
def quotientMoves (encode : State → Q) (q : Q) (label : L) (q' : Q) : Prop :=
  ∃ s t, encode s = q ∧ Race.Generic.Moves P offers s label t ∧ encode t = q'

/-- Every quotient transition lifts from every representative, rather than only some one. -/
theorem quotient_lifts (encode : State → Q) (stable : Stable P offers encode)
    (s : State) (label : L) (q' : Q) :
    quotientMoves P offers encode (encode s) label q' ↔
      ∃ t, Race.Generic.Moves P offers s label t ∧ encode t = q' := by
  constructor
  · rintro ⟨r, t, same, move, eqn⟩
    obtain ⟨u, moved, eqn'⟩ := (stable_iff_matching P offers encode).mp stable r s same label t move
    exact ⟨u, moved, eqn'.symm.trans eqn⟩
  · rintro ⟨t, move, eqn⟩
    exact ⟨s, t, rfl, move, eqn⟩

/-- Finite branching is about actual admitted results, not all raw syntactic firings. -/
theorem observed_imageFinite (read : State → V)
    (finite : ∀ label s, {t | Race.Generic.Moves P offers s label t}.Finite) :
    (observed P offers read).ImageFiniteModulo := by
  intro label s
  refine ⟨{t | Race.Generic.Moves P offers s label t}, finite label s, ?_⟩
  intro t move
  exact ⟨t, move, rfl⟩

/-- The established d-calc metric observes the actual labelled transform transitions. -/
noncomputable def graded (read : State → V) (discount : ℝ)
    (nonneg : 0 ≤ discount) (bounded : discount ≤ 1) :=
  GradedSystem.ofSystem (observed P offers read) discount nonneg bounded

theorem graded_zero_iff (read : State → V) (discount : ℝ)
    (nonneg : 0 ≤ discount) (bounded : discount ≤ 1) (positive : 0 < discount)
    (finite : ∀ label s, {t | Race.Generic.Moves P offers s label t}.Finite) (s t : State) :
    (graded P offers read discount nonneg bounded).logicalDistance s t = 0 ↔
      (observed P offers read).Bisimilar s t :=
  GradedSystem.logicalDistance_ofSystem_eq_zero_iff _ nonneg bounded
    (observed_imageFinite P offers read finite) positive s t

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionObserver
