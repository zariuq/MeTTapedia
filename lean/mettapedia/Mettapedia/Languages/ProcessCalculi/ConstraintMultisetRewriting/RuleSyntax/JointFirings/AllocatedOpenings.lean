import Mettapedia.Machines.NameSupplies.PortableNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.FreshNamespaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Singletons
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricOpenControls
import Mathlib.Logic.Encodable.Basic

/-!
# Allocating joint openings from live supplies

Draw coordinates from disjoint live supplies index independent ranges of
first-order unknowns above the caller's retained variables. The ranges need
only an exact code, so replacing a wire representation by exact local
interning has the same freshness criterion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AllocatedOpenings

open Mettapedia.Logic.LP
open Mettapedia.Machines.NameSupplies (Pool ShareSupply ShareName WellShared shareDiscipline
  next_names_distinct next_name_fresh)
open Mettapedia.Machines.NameSupplies.PortableNames (Name serialize serialize_injective)
open OneFrame (Terms frames ext)
open SchematicRows

def address (issuer : ℕ) (stamp : ShareName) : ℕ :=
  Encodable.encode (serialize ⟨issuer, stamp⟩)

theorem address_injective (issuer : ℕ) : Function.Injective (address issuer) := by
  intro left right same
  exact congrArg Name.stamp (serialize_injective (Encodable.encode_injective same))

private theorem draw_addresses_nodup (issuer : ℕ) (pool : Pool ShareSupply ShareName)
    (shared : WellShared pool) (supplies : List ShareSupply)
    (available : (supplies : Multiset ShareSupply) ≤ pool.live) :
    (supplies.map fun supply => address issuer (shareDiscipline.draw supply).1).Nodup := by
  induction supplies with
  | nil => simp
  | cons first rest ih =>
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih ((Multiset.le_cons_self _ _).trans available)⟩
      intro used
      obtain ⟨other, inRest, same⟩ := List.mem_map.mp used
      have pair : ({first, other} : Multiset ShareSupply) ≤ ↑(first :: rest) := by
        rw [Multiset.insert_eq_cons, ← Multiset.cons_coe, Multiset.cons_le_cons_iff]
        exact Multiset.singleton_le.mpr (Multiset.mem_coe.mpr inRest)
      exact next_names_distinct shared (pair.trans available) ((address_injective issuer same).symm)

section FirstOrder

variable {signature : LPSignature} [DecidableEq signature.vars]
  {O : Type*} {P : Program (Terms (Term signature))}
  (slots : signature.vars ≃ ℕ) (bound issuer : ℕ)

abbrev X := frames (FirstOrder.action signature)
abbrev E := ext (FirstOrder.action signature)
abbrev Candidate := ShareSupply × OneMember (FirstOrder.action signature) O P

def openFrom (supply : ShareSupply) : Subst signature :=
  FreshNamespaces.opening slots bound (address issuer (shareDiscipline.draw supply).1)

/-- A bag using the next draws of a submultiset of live supplies has genuinely
jointly fresh openings, including when the entry state has unknowns. -/
theorem bag_fresh (pool : Pool ShareSupply ShareName) (shared : WellShared pool)
    (s : State (Terms (Term signature)) O)
    (candidates : List (Candidate (O := O) (P := P)))
    (available : (candidates.map Prod.fst : Multiset ShareSupply) ≤ pool.live)
    (opened : ∀ candidate ∈ candidates, candidate.2.opening = openFrom slots bound issuer candidate.1)
    (below : ∀ term, s.Mentions term → ∀ name ∈ term.freeVars, slots name < bound) :
    Bag.Fresh X s (⟨PUnit.unit, candidates.map Prod.snd⟩ : Bag O E P s.frame) := by
  cases s with
  | mk frame knowledge present label =>
    cases frame
    let selected := candidates.map fun entry =>
      (address issuer (shareDiscipline.draw entry.1).1, entry.2)
    have distinct : (selected.map Prod.fst).Nodup := by
      simpa [selected, List.map_map, Function.comp_def] using
        draw_addresses_nodup issuer pool shared (candidates.map Prod.fst) available
    have faithful : ∀ entry ∈ selected, entry.2.opening = FreshNamespaces.opening slots bound entry.1 := by
      intro entry inside
      obtain ⟨candidate, candidateIn, rfl⟩ := List.mem_map.mp inside
      exact opened candidate candidateIn
    simpa [selected, List.map_map, Function.comp_def] using
      FreshNamespaces.fresh slots bound knowledge present label selected distinct faithful below

/-- The singleton case assigns an actual rule firing the private variables
of its next draw. The draw is unused in the allocator on entry. -/
theorem firing_fresh (pool : Pool ShareSupply ShareName) (shared : WellShared pool)
    (s : State (Terms (Term signature)) O) (supply : ShareSupply)
    (live : supply ∈ pool.live) (member : OneMember (FirstOrder.action signature) O P)
    (opened : member.opening = openFrom slots bound issuer supply)
    (below : ∀ term, s.Mentions term → ∀ name ∈ term.freeVars, slots name < bound) :
    (shareDiscipline.draw supply).1 ∉ pool.drawn ∧ member.firing.Fresh X s := by
  refine ⟨next_name_fresh shared live, ?_⟩
  cases s with
  | mk frame knowledge present label =>
    cases frame
    apply (Bag.fresh_single X _ member).mp
    exact bag_fresh slots bound issuer pool shared _ [(supply, member)]
      (Multiset.singleton_le.mpr live) (by simpa) below

end FirstOrder

#print axioms address_injective
#print axioms bag_fresh
#print axioms firing_fresh

section Controls

open Mettapedia.Machines.NameSupplies (wholeSupply wellShared_whole wellShared_step pieces_two)
open SymmetricMatches.OpenControls (source source_term spawnProgram spawnRule)
open FirstOrderLicence.Controls (signature c x)

private def allocatedSpawn (supply : ShareSupply) (made : ℕ) :
    OneMember (FirstOrder.action signature) ℕ spawnProgram :=
  ⟨spawnRule, rfl, openFrom (Equiv.refl ℕ) 0 41 supply, ⟨[], [], [made]⟩, []⟩

private def forkLeft : ShareSupply := shareDiscipline.piece wholeSupply 2 0
private def forkRight : ShareSupply := shareDiscipline.piece wholeSupply 2 1

private def forked : Pool ShareSupply ShareName :=
  (⟨{wholeSupply}, []⟩ : Pool ShareSupply ShareName).step shareDiscipline (.fork wholeSupply 2)

private def pair (left right : ShareSupply) : Bag ℕ (E (signature := signature)) spawnProgram PUnit.unit :=
  ⟨PUnit.unit, [allocatedSpawn left 10, allocatedSpawn right 11]⟩

/-- Two forked workers can allocate independent variables and publish both
results in one firing of the existing spawn rule. -/
theorem forked_openings_fire :
    (pair forkLeft forkRight).Admits X source ∧
      ((pair forkLeft forkRight).result X source).present = {0, 10, 11} := by
  have live : ([forkLeft, forkRight] : Multiset ShareSupply) ≤ forked.live := by
    simp [forked, Pool.step, Mettapedia.Machines.NameSupplies.Operation.produced, pieces_two,
      forkLeft, forkRight, Mettapedia.Machines.NameSupplies.Operation.consumed]
    exact le_refl _
  have shared : WellShared forked := wellShared_step _ wellShared_whole _ (le_refl _)
  have ready : (pair forkLeft forkRight).Fresh X source := by
    apply bag_fresh (Equiv.refl ℕ) 0 41 forked shared source
      [(forkLeft, allocatedSpawn forkLeft 10), (forkRight, allocatedSpawn forkRight 11)] live
    · rintro ⟨supply, member⟩ inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with same | same <;> cases same <;> rfl
    · intro term mentioned variableName free
      rw [source_term mentioned] at free
      exact False.elim ((show variableName ∉ (c 1).freeVars from by simp [c, Term.freeVars]) free)
  refine ⟨⟨⟨ready, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, by decide, by decide, fun _ impossible => absurd impossible List.not_mem_nil⟩,
    ⟨PUnit.unit, Subst.id signature, fun _ impossible => absurd impossible List.not_mem_nil⟩,
    ?_⟩, by decide⟩
  · intro m inside
    have listed : m ∈ [allocatedSpawn forkLeft 10, allocatedSpawn forkRight 11] := inside
    rcases List.mem_cons.mp listed with rfl | rest
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp rest
      exact ⟨rfl, rfl, rfl, rfl⟩
  · intro b assignment _ m inside
    have listed : m ∈ [allocatedSpawn forkLeft 10, allocatedSpawn forkRight 11] := inside
    rcases (List.mem_cons.mp listed).imp id List.mem_singleton.mp with rfl | rfl <;>
      exact ⟨fun _ outside => absurd outside List.not_mem_nil,
        fun _ outside => absurd outside List.not_mem_nil⟩

/-- Copying a draw may satisfy the individual openings while failing joint
freshness. Here two occurrences would require the same variable to take
independently prescribed, distinct constants. -/
theorem copying_opening_refused : ¬ (pair forkLeft forkLeft).Admits X source := by
  intro admitted
  have fresh := admitted.1.1 PUnit.unit (Subst.id signature)
  have both := fresh (fun _ => c 0 : Subst signature) (fun _ => c 1 : Subst signature)
  obtain ⟨assignment, ⟨_, first⟩, second⟩ := both
  have term : x ∈ spawnRule.terms := by simp [spawnRule, Rule.terms]
  have zero := first x term
  have one := second x term
  change assignment.applyTerm ((openFrom (Equiv.refl ℕ) 0 41 forkLeft).applyTerm x) = c 0 at zero
  change assignment.applyTerm ((openFrom (Equiv.refl ℕ) 0 41 forkLeft).applyTerm x) = c 1 at one
  cases zero.symm.trans one

end Controls

#print axioms forked_openings_fire
#print axioms copying_opening_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AllocatedOpenings
