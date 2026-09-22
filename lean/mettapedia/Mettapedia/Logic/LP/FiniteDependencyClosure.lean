import Mettapedia.Logic.LP.PropositionalChainer
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Sets

/-!
# Computed least closure of finite dependencies

A dependency edge is the unary Horn rule `{source} -> dependency`. The existing
proved saturation algorithm therefore computes the least dependency-closed set
containing the requested roots. `within` restricts this computation to an explicit
finite carrier, so the ambient name type need not be finite. Its closure theorem
requires the carrier to contain every outgoing dependency; nothing is silently
discarded under that hypothesis.

Least syntactic closure is not a minimal dynamic read set. A checker may visit
only some of these dependencies on a particular execution path.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.FiniteDependencyClosure

variable {α : Type*} [DecidableEq α]

def edge (source target : α) : PropRule α := ⟨{source}, target⟩

section Finite

variable [Fintype α]

/-- One unary rule per declared dependency, with no quadratic edge enumeration. -/
def program (dependencies : α → Finset α) : PropProgram α :=
  Finset.univ.biUnion fun source => (dependencies source).image (edge source)

theorem mem_program (dependencies : α → Finset α) (rule : PropRule α) :
    rule ∈ program dependencies ↔
      ∃ source target, target ∈ dependencies source ∧ rule = edge source target := by
  simp [program, eq_comm]

def closure (dependencies : α → Finset α) (roots : Finset α) : Finset α :=
  saturate (program dependencies) roots

theorem roots_subset (dependencies : α → Finset α) (roots : Finset α) :
    roots ⊆ closure dependencies roots := saturate_contains_facts _ _

theorem closed (dependencies : α → Finset α) (roots : Finset α)
    {source : α} (member : source ∈ closure dependencies roots) :
    dependencies source ⊆ closure dependencies roots := by
  intro target dependency
  apply rule_closed_saturate (r := edge source target)
  · exact (mem_program _ _).mpr ⟨source, target, dependency, rfl⟩
  · simpa [edge, closure] using member

theorem least (dependencies : α → Finset α) (roots candidate : Finset α)
    (contains : roots ⊆ candidate)
    (isClosed : ∀ source ∈ candidate, dependencies source ⊆ candidate) :
    closure dependencies roots ⊆ candidate := by
  intro target member
  apply derivable_subset_of_closed (program dependencies) roots candidate contains
      (fun rule ruleMember premises => ?_) target (saturate_sound _ _ _ member)
  obtain ⟨source, target, dependency, rfl⟩ := (mem_program _ _).mp ruleMember
  exact isClosed source (premises (by simp [edge])) dependency

theorem closure_mono (dependencies : α → Finset α) {left right : Finset α}
    (included : left ⊆ right) : closure dependencies left ⊆ closure dependencies right :=
  least _ _ _ (included.trans (roots_subset _ _)) (fun _ => closed _ _)

@[simp] theorem closure_idempotent (dependencies : α → Finset α) (roots : Finset α) :
    closure dependencies (closure dependencies roots) = closure dependencies roots :=
  Finset.Subset.antisymm
    (least _ _ _ Finset.Subset.rfl (fun _ => closed _ _)) (roots_subset _ _)

end Finite

/-- Compute dependency closure inside a finite carrier. Dependencies outside the
carrier are filtered, so use `within_closed` only with its explicit closure premise. -/
def within (dependencies : α → Finset α) (carrier roots : Finset α) : Finset α :=
  (closure (fun x : carrier => (dependencies x).subtype (· ∈ carrier))
    (roots.subtype (· ∈ carrier))).map (Function.Embedding.subtype _)

theorem within_subset (dependencies : α → Finset α) (carrier roots : Finset α) :
    within dependencies carrier roots ⊆ carrier := by
  intro target member
  exact Finset.property_of_mem_map_subtype _ member

theorem roots_subset_within (dependencies : α → Finset α) (carrier roots : Finset α)
    (contained : roots ⊆ carrier) : roots ⊆ within dependencies carrier roots := by
  intro target member
  apply Finset.mem_map.mpr
  refine ⟨⟨target, contained member⟩, roots_subset _ _ ?_, rfl⟩
  exact Finset.mem_subtype.mpr member

theorem within_closed (dependencies : α → Finset α) (carrier roots : Finset α)
    (carrierClosed : ∀ source ∈ carrier, dependencies source ⊆ carrier)
    {source : α} (member : source ∈ within dependencies carrier roots) :
    dependencies source ⊆ within dependencies carrier roots := by
  obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_map.mp member
  intro target dependency
  have targetMember := carrierClosed source source.property dependency
  apply Finset.mem_map.mpr
  refine ⟨⟨target, targetMember⟩, closed _ _ sourceMember ?_, rfl⟩
  exact Finset.mem_subtype.mpr dependency

theorem within_least (dependencies : α → Finset α) (carrier roots candidate : Finset α)
    (contains : roots ⊆ candidate)
    (isClosed : ∀ source ∈ candidate, dependencies source ⊆ candidate) :
    within dependencies carrier roots ⊆ candidate := by
  intro target member
  obtain ⟨target, targetMember, rfl⟩ := Finset.mem_map.mp member
  have bounded : closure (fun x : carrier => (dependencies x).subtype (· ∈ carrier))
      (roots.subtype (· ∈ carrier)) ⊆ candidate.subtype (· ∈ carrier) := by
    apply least
    · exact Finset.subtype_mono contains
    · intro source member dependency depends
      exact Finset.mem_subtype.mpr
        (isClosed source (Finset.mem_subtype.mp member) (Finset.mem_subtype.mp depends))
  exact Finset.mem_subtype.mp (bounded targetMember)

/-- Any two closed finite carriers containing the roots compute the same set. -/
theorem within_independent (dependencies : α → Finset α) (left right roots : Finset α)
    (leftContains : roots ⊆ left) (rightContains : roots ⊆ right)
    (leftClosed : ∀ source ∈ left, dependencies source ⊆ left)
    (rightClosed : ∀ source ∈ right, dependencies source ⊆ right) :
    within dependencies left roots = within dependencies right roots := by
  apply Finset.Subset.antisymm
  · exact within_least _ _ _ _ (roots_subset_within _ _ _ rightContains)
      (fun _ => within_closed _ _ _ rightClosed)
  · exact within_least _ _ _ _ (roots_subset_within _ _ _ leftContains)
      (fun _ => within_closed _ _ _ leftClosed)

namespace Controls

def dependencies : Nat → Finset Nat
  | 0 => {1}
  | 1 => {0, 2}
  | _ => ∅

/-- A cycle terminates and reaches its outgoing leaf without adding an isolated node. -/
theorem cyclic_closure : within dependencies {0, 1, 2, 3} {0} = {0, 1, 2} := by decide

/-- A missing edge target demonstrates why the finite-carrier premise matters. -/
theorem truncated_carrier_is_not_closed :
    within dependencies {0, 1} {0} = {0, 1} ∧
      ¬ (∀ source ∈ ({0, 1} : Finset Nat), dependencies source ⊆ {0, 1}) := by decide

end Controls

#print axioms within_closed
#print axioms within_least
#print axioms within_independent

end Mettapedia.Logic.LP.FiniteDependencyClosure
