import Mettapedia.GSLT.Dynamics.CapabilityGeneratedObservationDomain

/-!
# Universal property of capability-generated observation domains

The capability-generated domain is defined by a proof-relevant construction
tree, but its public meaning should not depend on inspecting that syntax.  This
module proves the corresponding universal property: it is the least declared
operational domain containing every accepted history and closed under the
supplied chronological and authorized independent-parallel operations.

The authorization carried by a parallel node remains load-bearing.  Closure
under a commutative container operation alone cannot manufacture an
independence witness.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics

universe uEvent uContainer uValue uAuthority

namespace ObservationDiscipline.OperationalDomain

/-- An operational observation domain closed under exactly the two supplied
collection capabilities.  The parallel clause consumes the complete
proof-relevant authorization article. -/
structure CapabilityClosed {Event : Type uEvent}
    {discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event}
    (chronological : ChronologicalCapability discipline.collection)
    (parallel : IndependentParallelCapability discipline.collection)
    (Independent : discipline.collection.Container →
      discipline.collection.Container → Type uAuthority)
    extends discipline.OperationalDomain where
  sequential_closed : ∀ {first second result},
    contains first → contains second →
      chronological.algebra.op first second = some result →
        contains result
  independentlyParallel_closed : ∀ {first second result},
    contains first → contains second →
      WitnessCollector.IndependentCombination discipline.collection parallel
        Independent first second result →
        contains result

/-- The syntax-generated domain is itself closed under both constructors. -/
def capabilityGeneratedClosed {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (chronological : ChronologicalCapability discipline.collection)
    (parallel : IndependentParallelCapability discipline.collection)
    (Independent : discipline.collection.Container →
      discipline.collection.Container → Type uAuthority) :
    CapabilityClosed chronological parallel Independent where
  toOperationalDomain :=
    capabilityGenerated discipline chronological parallel Independent
  sequential_closed := by
    rintro first second result ⟨firstConstruction⟩ ⟨secondConstruction⟩ combines
    exact ⟨.sequential firstConstruction secondConstruction combines⟩
  independentlyParallel_closed := by
    rintro first second result ⟨firstConstruction⟩ ⟨secondConstruction⟩
      combination
    exact ⟨.independentlyParallel firstConstruction secondConstruction
      combination⟩

/-- **Least-domain theorem.**  Every capability construction lands in every
operational domain closed under the same capabilities and authorization
family. -/
theorem capabilityGenerated_least {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (chronological : ChronologicalCapability discipline.collection)
    (parallel : IndependentParallelCapability discipline.collection)
    (Independent : discipline.collection.Container →
      discipline.collection.Container → Type uAuthority)
    (closed : CapabilityClosed chronological parallel Independent)
    {result : discipline.collection.Container}
    (member :
      (capabilityGenerated discipline chronological parallel Independent
        ).contains result) :
    closed.contains result := by
  obtain ⟨construction⟩ := member
  induction construction with
  | history events collected =>
      exact closed.reachable_mem ⟨events, collected⟩
  | sequential first second combines firstMember secondMember =>
      exact closed.sequential_closed firstMember secondMember combines
  | independentlyParallel first second combination firstMember secondMember =>
      exact closed.independentlyParallel_closed firstMember secondMember
        combination

/-- **Exact universal characterization.**  A container belongs to the
capability-generated domain exactly when it belongs to every operational
domain closed under the same capabilities. -/
theorem capabilityGenerated_contains_iff_forall_closed {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (chronological : ChronologicalCapability discipline.collection)
    (parallel : IndependentParallelCapability discipline.collection)
    (Independent : discipline.collection.Container →
      discipline.collection.Container → Type uAuthority)
    (result : discipline.collection.Container) :
    (capabilityGenerated discipline chronological parallel Independent
      ).contains result ↔
      ∀ closed : CapabilityClosed chronological parallel Independent,
        closed.contains result := by
  constructor
  · intro member closed
    exact capabilityGenerated_least discipline chronological parallel
      Independent closed member
  · intro member
    exact member
      (capabilityGeneratedClosed discipline chronological parallel Independent)

end ObservationDiscipline.OperationalDomain

/-! ## A strict-extension and refusal canary -/

namespace CapabilityGeneratedUniversalCanary

open ObservationDiscipline.OperationalDomain

/-- Every raw history has the same flat observation state. -/
def collector : WitnessCollector Unit where
  Container := Bool
  collect := fun _ => some false

/-- Chronological composition is Boolean disjunction with unit `false`. -/
def chronologicalAlgebra : Mettapedia.GSLT.PartialMonoid Bool where
  unit := false
  op := fun first second => some (first || second)
  unit_op := by
    intro value
    cases value <;> rfl
  op_unit := by
    intro value
    cases value <;> rfl
  op_assoc := by
    intro first second third
    cases first <;> cases second <;> cases third <;> rfl

/-- Independent composition is Boolean equivalence with unit `true`.
In particular, two flat `false` observations combine to `true`. -/
def parallelAlgebra : Mettapedia.GSLT.PartialMonoid Bool where
  unit := true
  op := fun first second => some (first == second)
  unit_op := by
    intro value
    cases value <;> rfl
  op_unit := by
    intro value
    cases value <;> rfl
  op_assoc := by
    intro first second third
    cases first <;> cases second <;> cases third <;> rfl

def discipline : ObservationDiscipline Unit where
  collection := collector
  Value := Bool
  readout := id

def chronological : ChronologicalCapability collector where
  algebra := chronologicalAlgebra
  collect_nil := rfl
  collect_append := by
    intro first second
    rfl

def parallel : IndependentParallelCapability collector where
  algebra := parallelAlgebra
  commutative := by
    intro first second
    cases first <;> cases second <;> rfl

def permitAll (_ _ : Bool) : Type := Unit
def refuseAll (_ _ : Bool) : Type := Empty

def falseHistory :
    WitnessCollector.CapabilityCollection collector chronological parallel
      permitAll false :=
  .history [] rfl

/-- An authorization witnesses the state that raw collection cannot reach. -/
def authorizedParallelTrue :
    WitnessCollector.CapabilityCollection collector chronological parallel
      permitAll true :=
  .independentlyParallel falseHistory falseHistory
    { authorization := ()
      combines := rfl }

theorem true_not_history_reachable : ¬ collector.Reachable true := by
  rintro ⟨events, collected⟩
  simp [collector] at collected

/-- Capability closure is genuinely larger than raw history reachability in
this model.  The added state is justified by a retained parallel authority,
not by carrier membership. -/
theorem capabilityGenerated_strictly_extends_reachable :
    (capabilityGenerated discipline chronological parallel permitAll
      ).contains true ∧
      ¬ collector.Reachable true :=
  ⟨⟨authorizedParallelTrue⟩, true_not_history_reachable⟩

/-- By the universal property, every suitably closed operational domain must
contain the authorized parallel result. -/
theorem every_closed_domain_contains_true :
    ∀ closed : CapabilityClosed (discipline := discipline)
        chronological parallel permitAll,
      closed.contains true :=
  (capabilityGenerated_contains_iff_forall_closed discipline chronological
    parallel permitAll true).1 ⟨authorizedParallelTrue⟩

/-- Replacing permission by an empty authorization family makes the same
parallel article uninhabitable. -/
theorem refusal_does_not_mint_parallel_true :
    IsEmpty
      (WitnessCollector.IndependentCombination collector parallel refuseAll
        false false true) :=
  ⟨fun combination => Empty.elim combination.authorization⟩

private def refusingConstructionResultFalse {result : Bool} :
    WitnessCollector.CapabilityCollection collector chronological parallel
      refuseAll result → result = false
  | .history events collected => by
      simpa [collector] using collected.symm
  | .sequential first second combines => by
      have firstFalse := refusingConstructionResultFalse first
      have secondFalse := refusingConstructionResultFalse second
      cases firstFalse
      cases secondFalse
      change some false = some result at combines
      exact (Option.some.inj combines).symm
  | .independentlyParallel first second combination =>
      Empty.elim combination.authorization

/-- The refusing domain cannot reach the extra state by a different
construction tree: histories and sequential composition remain `false`, and
every parallel node would require an inhabitant of the empty authorization
family. -/
theorem refusal_does_not_generate_true :
    ¬ (capabilityGenerated discipline chronological parallel refuseAll
      ).contains true := by
  rintro ⟨construction⟩
  have impossible : true = false := refusingConstructionResultFalse construction
  cases impossible

end CapabilityGeneratedUniversalCanary

/-! ## Axiom audit -/

#print axioms ObservationDiscipline.OperationalDomain.capabilityGeneratedClosed
#print axioms ObservationDiscipline.OperationalDomain.capabilityGenerated_least
#print axioms ObservationDiscipline.OperationalDomain.capabilityGenerated_contains_iff_forall_closed
#print axioms CapabilityGeneratedUniversalCanary.capabilityGenerated_strictly_extends_reachable
#print axioms CapabilityGeneratedUniversalCanary.every_closed_domain_contains_true
#print axioms CapabilityGeneratedUniversalCanary.refusal_does_not_mint_parallel_true
#print axioms CapabilityGeneratedUniversalCanary.refusal_does_not_generate_true

end Mettapedia.GSLT.Dynamics
