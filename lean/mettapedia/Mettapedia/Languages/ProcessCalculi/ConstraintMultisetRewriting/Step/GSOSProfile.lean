import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationControls
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSControls
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSFinalBialgebra
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSCongruence

/-! # A branching transform profile with an independent GSOS interpretation

Candidates contain a path through binary choices, an action and a proposed
leaf target. Preparation checks the path; admission checks the leaf transition.
The target syntax is constructed directly from the candidate. Its agreement
with the separately defined finite GSOS coalgebra is a theorem.

This profile has stopped processes, choice and process constants with specified
behaviour. It uses set-valued observations, no binders and no syntactic tests.
Its state is actual process syntax; its constraint store is empty. The profile
does not assert congruence for reflection or multiplicity-sensitive observers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GSOSProfile

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.FiniteBranching
open GSOSControls (signature actions naturals stopped choose law)
open IndexedPolynomial
open Interface
open Classical

abbrev Term := signature.Term naturals ()

/-- Read a leaf by a structural path, independently of transition semantics. -/
def leafAt : Term → List Bool → Option Nat
  | .roll (.inl value) _, [] => some value
  | .roll (.inr .choose) children, bit :: rest => leafAt (children bit) rest
  | _, _ => none

def Reaches (term : Term) (leaf : Nat) : Prop := ∃ path, leafAt term path = some leaf

theorem reaches_pure (value leaf : Nat) : Reaches (GSOSControls.pure value) leaf ↔ leaf = value := by
  constructor
  · rintro ⟨path, found⟩
    cases path with
    | nil => exact (Option.some.inj found).symm
    | cons _ _ => cases found
  · rintro rfl
    exact ⟨[], rfl⟩

theorem reaches_stopped (leaf : Nat) : ¬ Reaches stopped leaf := by
  rintro ⟨path, found⟩
  cases path <;> cases found

theorem reaches_choose (left right : Term) (leaf : Nat) :
    Reaches (choose left right) leaf ↔ Reaches left leaf ∨ Reaches right leaf := by
  constructor
  · rintro ⟨path, found⟩
    cases path with
    | nil => cases found
    | cons bit rest =>
      cases bit with
      | false => exact Or.inl ⟨rest, found⟩
      | true => exact Or.inr ⟨rest, found⟩
  · rintro (⟨path, found⟩ | ⟨path, found⟩)
    · exact ⟨false :: path, found⟩
    · exact ⟨true :: path, found⟩

/-- Two initial action-7 branches, only one of which later offers action 9. -/
def LeafAllows (source action target : Nat) : Prop :=
  (source = 0 ∧ action = 7 ∧ target = 1) ∨
  (source = 2 ∧ action = 7 ∧ target = 3) ∨
  (source = 1 ∧ action = 9 ∧ target = 4)

def leafSuccessors (source action : Nat) : Finset Nat :=
  (if source = 0 ∧ action = 7 then {1} else ∅) ∪
  (if source = 2 ∧ action = 7 then {3} else ∅) ∪
  (if source = 1 ∧ action = 9 then {4} else ∅)

theorem leaf_successors_iff (source action target : Nat) :
    target ∈ leafSuccessors source action ↔ LeafAllows source action target := by
  simp only [leafSuccessors, LeafAllows, Finset.mem_union]
  split_ifs <;> simp_all

def leafSteps : VariableCoalgebra signature actions naturals :=
  fun _ _ => ↾leafSuccessors

def leaves : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := naturals
  str := leafSteps

abbrev operational := IndexedGSOS.Operational.liftObject (lawEquiv signature actions law) leaves

def successors (term : Term) (action : Nat) : Finset Term :=
  Operational.coalgebra law leafSteps PUnit.unit () term action

theorem successors_pure (value action : Nat) :
    successors (GSOSControls.pure value) action = FinitePowerset.map GSOSControls.pure (leafSuccessors value action) := rfl

theorem successors_stopped (action : Nat) : successors stopped action = ∅ := by
  change Operational.coalgebra law leafSteps PUnit.unit ()
    (Free.node signature.polynomial .stopped _) action = ∅
  rw [Operational.coalgebra_node]
  exact FinitePowerset.map_empty _

theorem successors_choose (left right : Term) (action : Nat) :
    successors (choose left right) action = successors left action ∪ successors right action :=
  GSOSControls.operational_choice leafSteps left right action

private theorem term_induction (M : Term → Prop)
    (onPure : ∀ value, M (GSOSControls.pure value))
    (onStopped : M stopped)
    (onChoose : ∀ left right, M left → M right → M (choose left right))
    (term : Term) : M term := by
  let motive : (sort : Unit) → signature.Term naturals sort → Prop :=
    fun sort => match sort with | () => M
  have all : ∀ sort (tree : signature.Term naturals sort), motive sort tree := by
    intro sort tree
    refine Fix.rec (motive := motive) ?_ tree
    intro index shape children ih
    cases index
    cases shape with
    | inl value =>
      have same : children = (fun position => position.elim) := by
        funext position
        exact position.elim
      subst children
      exact onPure value
    | inr operator =>
      cases operator with
      | stopped =>
        have same : children = (fun position => position.elim) := by
          funext position
          exact position.elim
        subst children
        exact onStopped
      | choose =>
        have same : children = (fun (bit : Bool) => if bit then children true else children false) := by
          funext bit
          cases bit <;> rfl
        change M (Free.node signature.polynomial GSOSControls.Operator.choose children)
        rw [same]
        exact onChoose (children false) (children true) (ih false) (ih true)
  exact all () term

theorem successor_iff (term target : Term) (action : Nat) :
    target ∈ successors term action ↔
      ∃ source output, Reaches term source ∧ LeafAllows source action output ∧ target = GSOSControls.pure output := by
  induction term using term_induction with
  | onPure value =>
    rw [successors_pure]
    simp only [FinitePowerset.map, Finset.mem_image, leaf_successors_iff, reaches_pure]
    aesop
  | onStopped =>
    rw [successors_stopped]
    simp only [Finset.notMem_empty, reaches_stopped, false_and, exists_false]
  | onChoose left right ihLeft ihRight =>
    rw [successors_choose, Finset.mem_union, ihLeft, ihRight]
    simp only [reaches_choose]
    aesop

structure Candidate where
  path : List Bool
  action : Nat
  output : Nat

def effect : EffectCore Presentation.Controls.frame Nat Term (fun _ => Candidate) where
  frame _ := ()
  knowledge _ := []
  present _ := ∅
  selection _ := ⟨[], [], []⟩
  target _ := ()
  extension _ := id
  information _ := []
  information_refines := by intros; exact Frames.models_nil _
  Shapes {s} candidate := ∃ leaf, leafAt s candidate.path = some leaf
  preparedResult candidate _ := GSOSControls.pure candidate.output
  present_preparedResult _ _ := by
    ext occurrence
    simp [MeTTaCalculus.OccurrenceCommits.fire, Selection.commit]
  preparedSettle _ _ := id
  result_refines := by intros; exact Frames.models_nil _

def permission : effect.Admission := fun {source} candidate _ =>
  ∃ leaf, leafAt source candidate.path = some leaf ∧
    LeafAllows leaf candidate.action candidate.output

def step : Interface.Step Presentation.Controls.frame Nat Term (fun _ => Candidate) :=
  Interface.Step.ofEffect effect permission

theorem candidate_prepares {source : Term} (candidate : Candidate)
    (found : ∃ leaf, leafAt source candidate.path = some leaf) : effect.Prepares (s := source) candidate :=
  ⟨found, EvidenceInterface.Controls.enabled_nothing ∅, ⟨(), id, Frames.models_nil _⟩⟩

/-- Both directions relate actual indexed transform events to the independent
GSOS transition relation. Candidates are searched by structural paths. -/
theorem event_iff_successor (source target : Term) (action : Nat) :
    (∃ event : effect.Event permission source target, event.firing.action = action) ↔
      target ∈ successors source action := by
  rw [successor_iff]
  constructor
  · rintro ⟨event, action_eq⟩
    obtain ⟨leaf, found, allowed⟩ := event.permitted
    refine ⟨leaf, event.firing.output, ⟨event.firing.path, found⟩, ?_, event.target_eq.symm⟩
    simpa only [action_eq] using allowed
  · rintro ⟨leaf, output, ⟨path, found⟩, allowed, rfl⟩
    let candidate : Candidate := ⟨path, action, output⟩
    exact ⟨⟨candidate, candidate_prepares candidate ⟨leaf, found⟩,
      ⟨leaf, found, allowed⟩, rfl⟩, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GSOSProfile
