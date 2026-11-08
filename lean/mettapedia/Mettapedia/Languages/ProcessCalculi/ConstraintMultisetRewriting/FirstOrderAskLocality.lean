import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# First-order asks are local to closed store components

An equation component is closed when no existing equation crosses its boundary.
Consistent new equations outside that component preserve every observation
depending only on it, including entailed, refuted and unresolved verdicts.

For an absence or count observation, dependencies include the shared labels it
inspects. A closed query alone does not make such an observation independent of
bindings. The conditions below are sufficient locality bounds, not a claim of
minimal support or native incremental-index correctness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderAskLocality

open Mettapedia.Logic.LP

universe u v
variable {signature : LPSignature.{u, u, v, u}} [DecidableEq signature.vars]

def equationSupport (equation : Equation (Term signature)) : Finset signature.vars :=
  equation.1.freeVars ∪ equation.2.freeVars

def Closed (component : Set signature.vars) (equations : EquationStore (Term signature)) : Prop :=
  ∀ equation ∈ equations,
    (∀ name ∈ equationSupport equation, name ∈ component) ∨
      (∀ name ∈ equationSupport equation, name ∉ component)

def Avoids (component : Set signature.vars) (equations : EquationStore (Term signature)) : Prop :=
  ∀ equation ∈ equations, ∀ name ∈ equationSupport equation, name ∉ component

def ReadsOnly (component : Set signature.vars) (observation : Subst signature → Prop) : Prop :=
  ∀ first second, (∀ name ∈ component, first name = second name) →
    (observation first ↔ observation second)

theorem solves_congr {first second : Subst signature} {equation : Equation (Term signature)}
    (agree : ∀ name ∈ equationSupport equation, first name = second name) :
    (FirstOrder.action signature).Solves first equation ↔
      (FirstOrder.action signature).Solves second equation := by
  change first.applyTerm equation.1 = first.applyTerm equation.2 ↔
    second.applyTerm equation.1 = second.applyTerm equation.2
  rw [Subst.applyTerm_congr (t := equation.1) (fun name member =>
    agree name (Finset.mem_union_left _ member)),
    Subst.applyTerm_congr (t := equation.2) (fun name member =>
      agree name (Finset.mem_union_right _ member))]

theorem entails_local (component : Set signature.vars)
    (old added : EquationStore (Term signature)) (closed : Closed component old)
    (avoids : Avoids component added)
    (consistent : (FirstOrder.action signature).Consistent (old ++ added))
    (observation : Subst signature → Prop) (reads : ReadsOnly component observation) :
    (FirstOrder.action signature).Entails (old ++ added) observation ↔
      (FirstOrder.action signature).Entails old observation := by
  classical
  constructor
  · intro entailed first firstModel
    obtain ⟨second, secondModel⟩ := consistent
    let glued : Subst signature := fun name => if name ∈ component then first name else second name
    have model : (FirstOrder.action signature).Models glued (old ++ added) := by
      intro equation member
      rcases List.mem_append.mp member with inOld | inAdded
      · rcases closed equation inOld with inside | outside
        · exact (solves_congr (fun name inEquation => by
            simp [glued, inside name inEquation])).mpr (firstModel equation inOld)
        · exact (solves_congr (fun name inEquation => by
            simp [glued, outside name inEquation])).mpr
              (secondModel equation (List.mem_append_left _ inOld))
      · exact (solves_congr (fun name inEquation => by
          simp [glued, avoids equation inAdded name inEquation])).mpr
            (secondModel equation (List.mem_append_right _ inAdded))
    exact (reads glued first (fun name inside => by simp [glued, inside])).mp
      (entailed glued model)
  · exact (FirstOrder.action signature).entails_of_refines
      ((FirstOrder.action signature).append_refines old added)

theorem verdicts_local (component : Set signature.vars)
    (old added : EquationStore (Term signature)) (closed : Closed component old)
    (avoids : Avoids component added)
    (consistent : (FirstOrder.action signature).Consistent (old ++ added))
    (observation : Subst signature → Prop) (reads : ReadsOnly component observation) :
    ((FirstOrder.action signature).Entails (old ++ added) observation ↔
      (FirstOrder.action signature).Entails old observation) ∧
    ((FirstOrder.action signature).Entails (old ++ added) (fun assignment => ¬ observation assignment) ↔
      (FirstOrder.action signature).Entails old (fun assignment => ¬ observation assignment)) :=
  ⟨entails_local component old added closed avoids consistent observation reads,
    entails_local component old added closed avoids consistent _
      (fun first second agree => not_congr (reads first second agree))⟩

theorem equality_reads_support (component : Set signature.vars) (left right : Term signature)
    (supported : ∀ name ∈ equationSupport (left, right), name ∈ component) :
    ReadsOnly component ((FirstOrder.action signature).Solves · (left, right)) := by
  intro first second agree
  exact solves_congr (fun name member => agree name (supported name member))

theorem absent_reads_query_and_rows {O : Type*} [DecidableEq O]
    (component : Set signature.vars) (label : O → Term signature)
    (world : Finset O) (query : Term signature)
    (querySupport : ∀ name ∈ query.freeVars, name ∈ component)
    (rowSupport : ∀ occurrence ∈ world, ∀ name ∈ (label occurrence).freeVars, name ∈ component) :
    ReadsOnly component (fun assignment =>
      (Check.absent query).Holds (FirstOrder.action signature) assignment label world) := by
  intro first second agree
  have querySame := Subst.applyTerm_congr (t := query)
    (fun name member => agree name (querySupport name member))
  have rowSame := fun occurrence present => Subst.applyTerm_congr (t := label occurrence)
    (fun name member => agree name (rowSupport occurrence present name member))
  change (∀ occurrence ∈ world, ¬ first.applyTerm query = first.applyTerm (label occurrence)) ↔
    (∀ occurrence ∈ world, ¬ second.applyTerm query = second.applyTerm (label occurrence))
  constructor
  · intro absent occurrence present
    rw [← querySame, ← rowSame occurrence present]
    exact absent occurrence present
  · intro absent occurrence present
    rw [querySame, rowSame occurrence present]
    exact absent occurrence present

theorem count_reads_query_and_rows {O : Type*} [DecidableEq O]
    (component : Set signature.vars) (label : O → Term signature)
    (world : Finset O) (query : Term signature) (number : Nat)
    (querySupport : ∀ name ∈ query.freeVars, name ∈ component)
    (rowSupport : ∀ occurrence ∈ world, ∀ name ∈ (label occurrence).freeVars, name ∈ component) :
    ReadsOnly component (fun assignment =>
      (Check.count query number).Holds (FirstOrder.action signature) assignment label world) := by
  classical
  intro first second agree
  have querySame := Subst.applyTerm_congr (t := query)
    (fun name member => agree name (querySupport name member))
  have regions : Check.matches (FirstOrder.action signature) first label world query =
      Check.matches (FirstOrder.action signature) second label world query := by
    ext occurrence
    simp only [Check.matches, Finset.mem_filter]
    by_cases present : occurrence ∈ world
    · have rowSame := Subst.applyTerm_congr (t := label occurrence)
        (fun name member => agree name (rowSupport occurrence present name member))
      change (occurrence ∈ world ∧ first.applyTerm query = first.applyTerm (label occurrence)) ↔
        (occurrence ∈ world ∧ second.applyTerm query = second.applyTerm (label occurrence))
      rw [querySame, rowSame]
    · simp [present]
  change (Check.matches (FirstOrder.action signature) first label world query).card = number ↔
    (Check.matches (FirstOrder.action signature) second label world query).card = number
  rw [regions]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderAskLocality
