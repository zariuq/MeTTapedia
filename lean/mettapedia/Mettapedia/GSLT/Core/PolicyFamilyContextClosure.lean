import Mettapedia.GSLT.Core.PolicyFamilyOperationClosure
import Mathlib.Combinatorics.Quiver.Path

/-!
# Observations closed under declared operation contexts

A typed operation graph specifies which future interactions a consumer may
perform. Closing its observations under finite paths constructs an
operation-stable policy family. Its equivalence is the greatest relation
that both preserves the original observations and is stable under every
declared operation. The construction reuses Mathlib paths and the existing
policy quotient and executable readout interfaces.

This determines safe observational collisions relative to supplied consumers
and operations. It does not determine a most efficient representation, a
finite recognizer, or a global observer. Operations are supplied total state
maps; partial, effectful or nondeterministic interactions must first specify
their state/outcome interpretation. No raw operation becomes admitted merely
by appearing in a graph.

The existing refresh workload has an exact two-Boolean readout: present
emptiness and whether the retained count is zero. Arbitrary repeated refresh
does not require retaining the entire count. Adding decrement invalidates
that same readout. Thus operation promises, not one global information grade,
determine which distinctions may safely disappear.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.PolicyFamily.ContextClosure

universe uScope uEdge uState uPolicy uResult uReadout

section General

variable {Scope : Type uScope} [Quiver.{uEdge} Scope]
  {State : Scope → Type uState}

/-- The actual action of a finite path in the declared typed operation graph. -/
def runPath (execute : ∀ {a b : Scope}, (a ⟶ b) → State a → State b)
    {a : Scope} : {b : Scope} → Quiver.Path a b → State a → State b
  | _, .nil => id
  | _, .cons path operation => execute operation ∘ runPath execute path

@[simp] theorem runPath_comp
    (execute : ∀ {a b : Scope}, (a ⟶ b) → State a → State b)
    {a b c : Scope} (first : Quiver.Path a b) (second : Quiver.Path b c)
    (state : State a) :
    runPath execute (first.comp second) state =
      runPath execute second (runPath execute first state) := by
  induction second with
  | nil => rfl
  | cons previous operation ih =>
      simp only [Quiver.Path.comp_cons, runPath, Function.comp_apply, ih]

/-- Policies ask an original consumer after a finite permitted interaction.
The result type belongs to that consumer at the path's actual target scope. -/
def family (execute : ∀ {a b : Scope}, (a ⟶ b) → State a → State b)
    (base : (a : Scope) → PolicyFamily.{uState, uPolicy, uResult} (State a))
    (a : Scope) : PolicyFamily (State a) where
  Policy := Σ b : Scope, Quiver.Path a b × (base b).Policy
  Result := fun policy => (base policy.1).Result policy.2.2
  decide := fun policy state =>
    (base policy.1).decide policy.2.2 (runPath execute policy.2.1 state)

variable (execute : ∀ {a b : Scope}, (a ⟶ b) → State a → State b)
  (base : (a : Scope) → PolicyFamily.{uState, uPolicy, uResult} (State a))

/-- Prefixing the actual operation constructs the policy-coordinate witness;
congruence is subsequently derived, not assumed as an input. -/
def operationReindex {a b : Scope} (operation : a ⟶ b) :
    OperationReindex (family execute base a) (family execute base b)
      (execute operation) where
  select := fun policy => ⟨policy.1, operation.toPath.comp policy.2.1, policy.2.2⟩
  mapResult := fun _ => id
  agrees := by
    intro policy state
    change (base policy.1).decide policy.2.2
      (runPath execute (operation.toPath.comp policy.2.1) state) = _
    rw [runPath_comp]
    rfl

theorem preserves_base {a : Scope} {first second : State a}
    (same : (family execute base a).PolicyEquivalent first second) :
    (base a).PolicyEquivalent first second := by
  intro policy
  exact same ⟨a, .nil, policy⟩

theorem operation_stable {a b : Scope} (operation : a ⟶ b)
    {first second : State a}
    (same : (family execute base a).PolicyEquivalent first second) :
    (family execute base b).PolicyEquivalent (execute operation first) (execute operation second) :=
  (operationReindex execute base operation).preserves_policyEquivalent same

/-- Every observation-preserving relation stable under the declared
operations is contained in the contextual policy equivalence. No equivalence
axioms for the supplied relation are needed. -/
theorem greatest
    (relation : (a : Scope) → State a → State a → Prop)
    (observations : ∀ a first second, relation a first second →
      (base a).PolicyEquivalent first second)
    (stable : ∀ {a b : Scope} (operation : a ⟶ b) {first second : State a},
      relation a first second → relation b (execute operation first) (execute operation second))
    {a : Scope} {first second : State a} (related : relation a first second) :
    (family execute base a).PolicyEquivalent first second := by
  rintro ⟨b, path, policy⟩
  have transported : relation b (runPath execute path first) (runPath execute path second) := by
    clear policy
    induction path with
    | nil => exact related
    | cons previous operation ih => exact stable operation ih
  exact observations b _ _ transported policy

/-- Supporting every contextual policy forces the contextual vector to
factor through the proposed readout. This is informational sufficiency, not
a runtime-cost or representation-optimality theorem. -/
theorem least_sufficient {a : Scope} :
    (family execute base a).SupportsReadout (family execute base a).vector ∧
      ∀ (Readout : Type uReadout) (readout : State a → Readout),
        (family execute base a).SupportsReadout readout →
          NonFactorization.Factors readout (family execute base a).vector :=
  (family execute base a).vector_isLeastSufficient

/-- Requesting fewer consumers preserves every promised future operation.
Different restrictions need not be comparable. -/
def restrictConsumers {Requested : Scope → Type*}
    (select : (a : Scope) → Requested a → (base a).Policy) (a : Scope) :
    OperationReindex (family execute base a)
      (family execute (fun b => (base b).reindex (select b)) a) id where
  select := fun policy => ⟨policy.1, policy.2.1, select policy.1 policy.2.2⟩
  mapResult := fun _ => id
  agrees := fun _ _ => rfl

end General

namespace Refresh

open OperationClosureCanary

inductive Scope where
  | cache

inductive Operation where
  | refresh

instance : Quiver Scope where
  Hom := fun _ _ => Operation

def execute {a b : Scope} (_operation : a ⟶ b) : State → State := refresh

def base (_scope : Scope) : PolicyFamily State := currentAnswer

def observations : PolicyFamily State := family execute base .cache

/-- Two bits, independently read from the original state. This intentionally
forgets nonzero count magnitudes and every cache tag. -/
def twoBits (state : State) : Bool × Bool :=
  (state.reportedEmpty, state.count == 0)

def refreshBits (bits : Bool × Bool) : Bool × Bool := (bits.2, bits.2)

theorem twoBits_refresh (state : State) :
    twoBits (refresh state) = refreshBits (twoBits state) := rfl

theorem equivalent_of_twoBits {first second : State}
    (same : twoBits first = twoBits second) :
    observations.PolicyEquivalent first second := by
  apply greatest execute base (fun _ x y => twoBits x = twoBits y) ?_ ?_ same
  · intro scope x y equal policy
    exact congrArg Prod.fst equal
  · intro a b operation x y equal
    exact congrArg refreshBits equal

theorem twoBits_of_equivalent {first second : State}
    (same : observations.PolicyEquivalent first second) :
    twoBits first = twoBits second := by
  apply Prod.ext
  · exact same ⟨.cache, .nil, ()⟩
  · exact same ⟨.cache,
      (show Scope.cache ⟶ Scope.cache from Operation.refresh).toPath, ()⟩

theorem equivalent_iff_twoBits (first second : State) :
    observations.PolicyEquivalent first second ↔ twoBits first = twoBits second :=
  ⟨twoBits_of_equivalent, equivalent_of_twoBits⟩

/-- Explicit canonical state, not a choice of an unknown representative. -/
def representative (bits : Bool × Bool) : State :=
  ⟨if bits.2 then 0 else 1, bits.1, 0⟩

theorem representative_section : Function.RightInverse representative twoBits := by
  rintro ⟨present, zero⟩
  cases present <;> cases zero <;> rfl

def realization : observations.ReadoutRealization twoBits :=
  observations.readoutRealizationOfSection twoBits representative representative_section
    (fun _ _ same => equivalent_of_twoBits same)

/-- The finite two-bit view is not merely sufficient: every readout that
supports the entire declared workload must reconstruct both bits. -/
theorem twoBits_is_least : observations.SupportsReadout twoBits ∧
    ∀ (Readout : Type uReadout) (readout : State → Readout),
      observations.SupportsReadout readout → NonFactorization.Factors readout twoBits := by
  refine ⟨⟨realization⟩, ?_⟩
  rintro Readout readout ⟨runner⟩
  refine ⟨fun observed =>
    (runner.run ⟨.cache, .nil, ()⟩ observed,
      runner.run ⟨.cache,
        (show Scope.cache ⟶ Scope.cache from Operation.refresh).toPath, ()⟩ observed), ?_⟩
  intro state
  apply Prod.ext
  · exact runner.agrees ⟨.cache, .nil, ()⟩ state
  · exact runner.agrees ⟨.cache,
      (show Scope.cache ⟶ Scope.cache from Operation.refresh).toPath, ()⟩ state

theorem nonzero_magnitudes_can_be_forgotten :
    (⟨2, false, 4⟩ : State) ≠ ⟨3, false, 9⟩ ∧
      observations.PolicyEquivalent ⟨2, false, 4⟩ ⟨3, false, 9⟩ :=
  ⟨by decide, equivalent_of_twoBits rfl⟩

theorem present_answer_is_not_enough :
    ¬ observations.SupportsReadout State.reportedEmpty := by
  apply observations.not_supportsReadout_of_policy_collision State.reportedEmpty
    (first := ⟨0, false, 4⟩) (second := ⟨1, false, 4⟩) rfl
    ⟨.cache, (show Scope.cache ⟶ Scope.cache from Operation.refresh).toPath, ()⟩
  change true ≠ false
  decide

/-- A new operation promise makes an old compact view inadequate. -/
def decrement (state : State) : State :=
  { state with count := state.count - 1, reportedEmpty := state.count - 1 == 0 }

theorem decrement_requires_more_information :
    ¬ NonFactorization.Factors twoBits (twoBits ∘ decrement) := by
  intro factors
  have same : twoBits (⟨1, false, 4⟩ : State) = twoBits ⟨2, false, 4⟩ := rfl
  have impossible := factors.constantOnFibers _ _ same
  have different : twoBits (decrement (⟨1, false, 4⟩ : State)) ≠
      twoBits (decrement ⟨2, false, 4⟩) := by decide
  exact different impossible

end Refresh

#print axioms operationReindex
#print axioms operation_stable
#print axioms greatest
#print axioms least_sufficient
#print axioms restrictConsumers
#print axioms Refresh.equivalent_iff_twoBits
#print axioms Refresh.twoBits_is_least
#print axioms Refresh.nonzero_magnitudes_can_be_forgotten
#print axioms Refresh.present_answer_is_not_enough
#print axioms Refresh.decrement_requires_more_information

end Mettapedia.GSLT.Core.PolicyFamily.ContextClosure
