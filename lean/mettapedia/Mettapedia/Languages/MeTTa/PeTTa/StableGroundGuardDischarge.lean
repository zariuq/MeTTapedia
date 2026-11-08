import Mettapedia.Languages.MeTTa.PeTTa.StableGroundTypeReturn
import Mettapedia.Languages.MeTTa.PeTTa.StableTypeCallerBinding

/-!
# Readonly discharge of a ground uninterpreted return guard

The query is the actual bound query and the join is the actual incremental
first-order refinement. A previously established structural range succeeds
once and returns the entering caller substitution literally unchanged.
The paired input check has one reply; erasing its private row binding still
requires the caller's row-variable-clear/readback admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StableGroundGuardDischarge

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.ConjunctiveUnification (applyTerm_of_isGround)
open IntrinsicTypeFacts (signature TypeTerm Declaration)
open IndependentTypeOutput (Path freshSupply)
open StableGroundTypeQueries (GroundUninterpreted groundSchema admitted_is_ground schema_is_ground
  fresh_singleton bound_own_singleton)

def join (caller : Subst signature) (reply expected : TypeTerm) : Option (Subst signature) :=
  (unifyTotal [(caller.applyTerm reply, caller.applyTerm expected)]).map fun refinement =>
    refinement ∘ₛ caller

def check (library : List Declaration) (fuel : Nat) (path : Path) (caller : Subst signature)
    (subject expected : TypeTerm) : Option (List (Subst signature)) :=
  (StableIntrinsicTypeQuery.run library freshSupply fuel path (caller.applyTerm subject)
    (some (caller.applyTerm expected))).map fun replies =>
      replies.flatMap fun reply => (join caller reply expected).toList

theorem ground_self_match_is_identity (value : TypeTerm) (ground : value.isGround) :
    unifyTotal [(value, value)] = some (Subst.id signature) := by
  obtain ⟨theta, accepted⟩ := unifyTotal_complete (equations := [(value, value)])
    ⟨Subst.id signature, by intro pair member; cases List.mem_singleton.mp member; rfl⟩
  have empty : eqVars [(value, value)] = ∅ := by
    simp [eqVars, (Term.isGround_iff_freeVars_empty value).mp ground]
  have identity : theta = Subst.id signature := by
    funext name
    exact (unifyTotal_relevantIdempotent _ _ accepted).fixes name (by simp [empty])
  simpa only [identity] using accepted

theorem join_entailed_ground_is_readonly (caller : Subst signature) (expected value : TypeTerm)
    (assigned : caller.applyTerm expected = value) (ground : value.isGround) :
    join caller value expected = some caller := by
  simp only [join, assigned, applyTerm_of_isGround caller ground, ground_self_match_is_identity value ground,
    Option.map_some, Subst.comp_id_left]

/-- The real return query and caller join have exactly one outcome and make
no caller substitution change. No functional-space assumption is used. -/
theorem return_guard_readonly (library : List Declaration) (fuel : Nat) (path : Path)
    (caller : Subst signature) (subject expected : TypeTerm)
    (admitted : GroundUninterpreted library (caller.applyTerm subject))
    (enough : (caller.applyTerm subject).size ≤ fuel)
    (assigned : caller.applyTerm expected = groundSchema (caller.applyTerm subject)) :
    check library fuel path caller subject expected = some [caller] := by
  unfold check
  rw [assigned, bound_own_singleton library fuel path _ admitted enough]
  simp only [Option.map_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    join_entailed_ground_is_readonly caller expected _ assigned (schema_is_ground library _ admitted),
    Option.toList_some]

theorem variable_requirement_is_fresh (library : List Declaration) (fuel : Nat)
    (path : Path) (subject : TypeTerm) (name : Nat) :
    StableIntrinsicTypeQuery.run library freshSupply fuel path subject (some (.var name)) =
      StableIntrinsicTypeQuery.run library freshSupply fuel path subject none := by
  cases fuel <;> rfl

/-- The input query has one principal reply under the actual current row
environment. Its later private binding is not silently assumed unread. -/
theorem input_query_singleton (library : List Declaration) (fuel : Nat) (path : Path)
    (caller : Subst signature) (subject : TypeTerm) (name : Nat)
    (admitted : GroundUninterpreted library (caller.applyTerm subject))
    (enough : (caller.applyTerm subject).size ≤ fuel) :
    StableIntrinsicTypeQuery.run library freshSupply fuel path (caller.applyTerm subject) (some (.var name)) =
      some [groundSchema (caller.applyTerm subject)] := by
  rw [variable_requirement_is_fresh]
  exact fresh_singleton library freshSupply fuel path _ admitted enough

theorem join_ground_to_variable (caller : Subst signature) (expected value : TypeTerm) (name : Nat)
    (unbound : caller.applyTerm expected = .var name) (ground : value.isGround) :
    join caller value expected = some (Subst.single name value ∘ₛ caller) := by
  have notVariable : ∀ other, value ≠ .var other := by
    intro other same
    subst value
    exact ground
  have absent : name ∉ value.freeVars := by
    simp [(Term.isGround_iff_freeVars_empty value).mp ground]
  simp only [join, unbound, applyTerm_of_isGround caller ground,
    Mettapedia.Logic.LP.IndependentOutputUnification.nonvariable_output_match name value notVariable absent,
    Option.map_some]

/-- The actual input guard has exactly one incremental refinement. Its
type-variable assignment is recorded explicitly, rather than erased by fiat. -/
theorem input_guard_single_refinement (library : List Declaration) (fuel : Nat) (path : Path)
    (caller : Subst signature) (subject expected : TypeTerm) (name : Nat)
    (unbound : caller.applyTerm expected = .var name)
    (admitted : GroundUninterpreted library (caller.applyTerm subject))
    (enough : (caller.applyTerm subject).size ≤ fuel) :
    check library fuel path caller subject expected =
      some [Subst.single name (groundSchema (caller.applyTerm subject)) ∘ₛ caller] := by
  unfold check
  rw [unbound, input_query_singleton library fuel path caller subject name admitted enough]
  simp only [Option.map_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    join_ground_to_variable caller expected _ name unbound (schema_is_ground library _ admitted),
    Option.toList_some]

/-- Omitting that input refinement is invisible only to caller observations
whose reached terms do not mention the row's private type name. -/
theorem input_refinement_preserves_independent_observations (caller : Subst signature)
    (name : Nat) (type : TypeTerm) (observations : List TypeTerm)
    (privateName : ∀ observation ∈ observations, name ∉ (caller.applyTerm observation).freeVars) :
    observations.map (Subst.single name type ∘ₛ caller).applyTerm =
      observations.map caller.applyTerm := by
  apply List.map_congr_left
  intro observation present
  rw [Subst.applyTerm_comp]
  apply Subst.applyTerm_eq_self
  intro other occurs
  exact Subst.single_ne type (fun same => privateName observation present (same ▸ occurs))

end Mettapedia.Languages.MeTTa.PeTTa.StableGroundGuardDischarge
