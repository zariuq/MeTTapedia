import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.CoalescedGroundDemands
import Mettapedia.Logic.LP.Substitution

/-!
# Guard-aware sharing of symbolic demand

A symbolic demand describes a family of ground call tags. A syntactic
specializing substitution is not sufficient: it must carry a client's
allowed instantiation to one allowed by the general demand. For a
finite supplied call universe, the resulting cover serves each
specialized call by the existing coalesced module reading.

The guard here is a restriction on *which calls are asked*. Guards
that inspect an answer's hidden derivation or effects are not domain
restrictions; sharing a table for those requires retaining more than
the call and public result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading

open Mettapedia.Logic.LP
open scoped Mettapedia.Logic.LP
open SetStoreSyntax (consequence)

universe u

structure GuardedDemand (ρ : LPSignature) where
  pattern : Term ρ
  allows : Subst ρ → Prop

namespace GuardedDemand

variable {ρ : LPSignature}

def tags (demand : GuardedDemand ρ) : Set (Term ρ) :=
  {call | call.isGround ∧ ∃ θ, demand.allows θ ∧ θ.applyTerm demand.pattern = call}

structure Factors (wide narrow : GuardedDemand ρ) where
  specialization : Subst ρ
  pattern : specialization.applyTerm wide.pattern = narrow.pattern
  permits : ∀ θ, narrow.allows θ → wide.allows (θ ∘ₛ specialization)

theorem Factors.covers {wide narrow : GuardedDemand ρ} (specialized : wide.Factors narrow) :
    narrow.tags ⊆ wide.tags := by
  rintro call ⟨ground, θ, permitted, produces⟩
  refine ⟨ground, θ ∘ₛ specialized.specialization, specialized.permits θ permitted, ?_⟩
  rw [Subst.applyTerm_comp, specialized.pattern, produces]

/-- Enumerate the covered calls of a supplied finite universe. The
predicate deciding membership may be supplied by a separate solver;
this definition does not claim termination of arbitrary guards. -/
def finiteCover (wide : GuardedDemand ρ) [DecidablePred (· ∈ wide.tags)]
    (universeOfCalls : Finset (Term ρ)) : Finset (Term ρ) :=
  universeOfCalls.filter (· ∈ wide.tags)

theorem cover_ground (wide : GuardedDemand ρ) [DecidablePred (· ∈ wide.tags)]
    (universeOfCalls : Finset (Term ρ)) :
    ∀ call ∈ wide.finiteCover universeOfCalls, call.isGround :=
  fun _ member => (Finset.mem_filter.mp member).2.1

theorem covered {wide narrow : GuardedDemand ρ} [DecidablePred (· ∈ wide.tags)]
    (specialized : wide.Factors narrow) (universeOfCalls : Finset (Term ρ))
    {call : Term ρ} (inUniverse : call ∈ universeOfCalls) (client : call ∈ narrow.tags) :
    call ∈ wide.finiteCover universeOfCalls :=
  Finset.mem_filter.mpr ⟨inUniverse, specialized.covers client⟩

end GuardedDemand

variable {σ : LPSignature.{u, u, u, u}} {L : Type u}
  [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L]

/-- One coalesced table for a guarded symbolic family serves any
covered client exactly as that concrete variant would be evaluated.
The finite universe is an input contract, not implicitly all terms. -/
theorem tagged_symbolic_cover_serves_client
    {M : L → ModuleRule (readingSignature σ L)} {Rel : Finset (Atom (readingSignature σ L))}
    (rr : ∀ l, RangeRestricted (M l)) (relGround : ∀ atom ∈ Rel, atom.isGround)
    {wide narrow : GuardedDemand (readingSignature σ L)} [DecidablePred (· ∈ wide.tags)]
    (specialized : wide.Factors narrow) (universeOfCalls : Finset (Term (readingSignature σ L)))
    {call : Term (readingSignature σ L)} (listed : call ∈ universeOfCalls) (asked : call ∈ narrow.tags)
    (value : Term (readingSignature σ L)) :
    valueRow call value ∈ coalescedRows M Rel (wide.finiteCover universeOfCalls) ↔
      valueRow call value ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed call Rel) :=
  coalesced_value_iff_variant (wide.finiteCover universeOfCalls) rr
    (wide.cover_ground universeOfCalls) relGround (GuardedDemand.covered specialized universeOfCalls listed asked) value

namespace GuardControls

private abbrev BooleanConstants : LPSignature :=
  ⟨Bool, Unit, Empty, Empty.elim, Empty, Empty.elim⟩

private def target (which : Bool) : GuardedDemand BooleanConstants :=
  ⟨.const which, fun assignment => assignment () = .const which⟩

private def general (required : Bool) : GuardedDemand BooleanConstants :=
  ⟨.var (), fun assignment => assignment () = .const required⟩

private def chooseTag (chosen : Bool) : Subst BooleanConstants := fun _ => .const chosen

theorem matching_guard_has_a_specialization :
    Nonempty ((general true).Factors (target true)) :=
  ⟨⟨chooseTag true, rfl, fun _ _ => rfl⟩⟩

theorem syntax_alone_can_cover_a_call_that_the_guard_rejects :
    (chooseTag true).applyTerm (general false).pattern = (target true).pattern ∧
      ¬ (target true).tags ⊆ (general false).tags := by
  refine ⟨rfl, fun covers => ?_⟩
  have asked : Term.const true ∈ (target true).tags := ⟨by trivial, chooseTag true, rfl, rfl⟩
  obtain ⟨_, assignment, refused, produces⟩ := covers asked
  change assignment () = Term.const false at refused
  change assignment () = Term.const true at produces
  exact Bool.noConfusion (Term.const.inj (refused.symm.trans produces))

end GuardControls

#print axioms GuardedDemand.Factors.covers
#print axioms tagged_symbolic_cover_serves_client
#print axioms GuardControls.matching_guard_has_a_specialization
#print axioms GuardControls.syntax_alone_can_cover_a_call_that_the_guard_rejects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
