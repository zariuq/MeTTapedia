import Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary

/-!
# The information order on Cost² observation keys

`CostTwoCacheReplayBoundary` characterizes which individual observations may
factor through a cache or replay key.  This module organizes those facts into
an information order.

A fine key refines a coarse key when the coarse key can be recovered by
forgetting information from the fine key.  Safe policies then move
contravariantly: every policy supported by the coarse key is supported by the
fine one.  An exact replay key refines every other key, while a collision in a
coarse key makes some exact replay fail.

Concrete language witnesses and replay failures are supplied by separate
annexes over this generic information order.
-/

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

universe uState uFine uCoarse uValue uOther

/-! ## Generic information order -/

/-- `fine` retains at least the information retained by `coarse`: a fixed
forgetful map recovers the coarse key from the fine one. -/
def KeyRefines {State : Type uState} {Fine : Type uFine}
    {Coarse : Type uCoarse} (fine : State → Fine) (coarse : State → Coarse) :
    Prop :=
  ∃ forget : Fine → Coarse, coarse = forget ∘ fine

/-- Key refinement is exactly policy safety when the coarser key itself is
read as the policy. -/
theorem keyRefines_iff_policySafe
    {State : Type uState} {Fine : Type uFine} {Coarse : Type uCoarse}
    (fine : State → Fine) (coarse : State → Coarse) :
    KeyRefines fine coarse ↔ PolicySafe fine coarse :=
  Iff.rfl

theorem KeyRefines.refl
    {State : Type uState} {Key : Type uFine} (key : State → Key) :
    KeyRefines key key := by
  exact ⟨id, by funext state; rfl⟩

theorem KeyRefines.trans
    {State : Type uState} {Fine : Type uFine} {Middle : Type uCoarse}
    {Coarse : Type uOther}
    {fine : State → Fine} {middle : State → Middle}
    {coarse : State → Coarse}
    (fineMiddle : KeyRefines fine middle)
    (middleCoarse : KeyRefines middle coarse) :
    KeyRefines fine coarse := by
  rcases fineMiddle with ⟨forgetMiddle, middleFactors⟩
  rcases middleCoarse with ⟨forgetCoarse, coarseFactors⟩
  refine ⟨forgetCoarse ∘ forgetMiddle, funext fun state => ?_⟩
  calc
    coarse state = forgetCoarse (middle state) := congrFun coarseFactors state
    _ = forgetCoarse (forgetMiddle (fine state)) :=
      congrArg forgetCoarse (congrFun middleFactors state)
    _ = ((forgetCoarse ∘ forgetMiddle) ∘ fine) state := rfl

/-- Policy safety is monotone in retained information. -/
theorem KeyRefines.policySafe
    {State : Type uState} {Fine : Type uFine} {Coarse : Type uCoarse}
    {Value : Type uValue}
    {fine : State → Fine} {coarse : State → Coarse}
    (refines : KeyRefines fine coarse) {policy : State → Value}
    (safe : PolicySafe coarse policy) :
    PolicySafe fine policy := by
  exact refines.trans safe

/-- A key from which the entire state can be replayed refines every other
key on that state. -/
theorem ExactReplayKey.refines
    {State : Type uState} {Fine : Type uFine} {Coarse : Type uCoarse}
    {fine : State → Fine} (exact : ExactReplayKey fine)
    (coarse : State → Coarse) :
    KeyRefines fine coarse := by
  rcases exact with ⟨decode, recovers⟩
  refine ⟨coarse ∘ decode, funext fun state => ?_⟩
  simp only [Function.comp_apply, recovers state]

/-- Exact keys are equivalent in the information preorder, even when their
representations differ. -/
theorem exactReplayKeys_mutuallyRefine
    {State : Type uState} {LeftKey : Type uFine} {RightKey : Type uCoarse}
    {left : State → LeftKey} {right : State → RightKey}
    (leftExact : ExactReplayKey left) (rightExact : ExactReplayKey right) :
    KeyRefines left right ∧ KeyRefines right left :=
  ⟨ExactReplayKey.refines leftExact right,
    ExactReplayKey.refines rightExact left⟩

/-- Strict refinement retains every observation of the coarse key and at
least one additional distinction. -/
def StrictlyRefines {State : Type uState} {Fine : Type uFine}
    {Coarse : Type uCoarse} (fine : State → Fine) (coarse : State → Coarse) :
    Prop :=
  KeyRefines fine coarse ∧ ¬ KeyRefines coarse fine

/-- A collided pair is an executable replay negative: every decoder must be
wrong on at least one member of the pair. -/
theorem collision_forces_decode_failure
    {State : Type uState} {Key : Type uFine} {key : State → Key}
    {left right : State} (different : left ≠ right)
    (collision : key left = key right) (decode : Key → State) :
    decode (key left) ≠ left ∨ decode (key right) ≠ right := by
  by_contra bothRecover
  push Not at bothRecover
  apply different
  calc
    left = decode (key left) := bothRecover.1.symm
    _ = decode (key right) := congrArg decode collision
    _ = right := bothRecover.2

/-! ## Small positive and negative controls -/

def boolExactKey : Bool → Bool := id

def boolCollapsedKey : Bool → Unit := fun _ => ()

/-- Retaining a Boolean strictly refines forgetting it. -/
theorem bool_exact_strictlyRefines_collapsed :
    StrictlyRefines boolExactKey boolCollapsedKey := by
  constructor
  · exact ExactReplayKey.refines
      (⟨id, fun _ => rfl⟩ : ExactReplayKey boolExactKey) boolCollapsedKey
  · intro collapsedRefinesExact
    have identitySafe : PolicySafe boolCollapsedKey (id : Bool → Bool) := by
      simpa [boolExactKey] using
        (keyRefines_iff_policySafe boolCollapsedKey boolExactKey).1
          collapsedRefinesExact
    have collapsedExact : ExactReplayKey boolCollapsedKey :=
      (exactReplayKey_iff_identityPolicySafe boolCollapsedKey).2 identitySafe
    exact collision_prevents_exactReplayKey
      (key := boolCollapsedKey) (left := false) (right := true)
      (by decide) rfl collapsedExact

/-- Every decoder for the collapsed Boolean key misreplays one of the two
states. -/
theorem bool_collapsed_decode_failure (decode : Unit → Bool) :
    decode (boolCollapsedKey false) ≠ false ∨
      decode (boolCollapsedKey true) ≠ true :=
  collision_forces_decode_failure
    (key := boolCollapsedKey) (left := false) (right := true)
    (by decide) rfl decode

/-! ## Policy separation -/

/-- A nonconstant Boolean observation distinguishes some pair of states. -/
theorem exists_policy_distinguished_pair
    {State : Type uState} (policy : State → Bool)
    (nonconstant : ¬ ∃ value : Bool, ∀ state, policy state = value) :
    ∃ left right, policy left ≠ policy right := by
  classical
  by_contra noPair
  push Not at noPair
  by_cases inhabited : Nonempty State
  · rcases inhabited with ⟨seed⟩
    exact nonconstant ⟨policy seed, fun state => noPair state seed⟩
  · exact nonconstant ⟨false, fun state => False.elim (inhabited ⟨state⟩)⟩

#print axioms keyRefines_iff_policySafe
#print axioms KeyRefines.trans
#print axioms ExactReplayKey.refines
#print axioms collision_forces_decode_failure
#print axioms bool_exact_strictlyRefines_collapsed
#print axioms exists_policy_distinguished_pair

end Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder
