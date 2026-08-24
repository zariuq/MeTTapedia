import Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel

/-!
# Cost² cache and replay boundary for Prime

The Cost² obstruction says that compact erasure identifies proof-relevant
elaborations which later observations can distinguish.  This module states
the exact consequence at Prime's abstract implementation boundary.

A key is safe for one policy precisely when that policy factors through the
key.  An exact replay key has a left inverse; equivalently, it is safe for the
identity policy, and therefore for every policy.  For a split erasure, policy
safety is exactly fibre invariance.

Concrete languages instantiate this interface in separate annexes.  The
interface does not prescribe representation fields: an exact key must retain
precisely the information needed by policies that are not invariant under its
erasure.
-/

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

universe uState uKey uValue

/-! ## Generic policy and replay keys -/

/-- A key is safe for a particular policy when the policy can be evaluated
from the key alone. -/
def PolicySafe {State : Type uState} {Key : Type uKey} {Value : Type uValue}
    (key : State → Key) (policy : State → Value) : Prop :=
  ∃ keyedPolicy : Key → Value, policy = keyedPolicy ∘ key

/-- Every policy with one fixed value type factors through the key. -/
def AllPoliciesSafe {State : Type uState} {Key : Type uKey}
    (key : State → Key) (Value : Type uValue) : Prop :=
  ∀ policy : State → Value, PolicySafe key policy

/-- An exact replay key admits a decoder which recovers every retained state.
This is the function-level content of `ExactCodec`. -/
def ExactReplayKey {State : Type uState} {Key : Type uKey}
    (key : State → Key) : Prop :=
  ∃ decode : Key → State, Function.LeftInverse decode key

/-- For a split erasure, cache safety is exactly constancy on its fibres. -/
theorem policySafe_iff_fiberInvariant_of_split
    {State : Type uState} {Key : Type uKey} {Value : Type uValue}
    (key : State → Key) (select : Key → State)
    (splits : ∀ compact, key (select compact) = compact)
    (policy : State → Value) :
    PolicySafe key policy ↔
      ∀ left right, key left = key right → policy left = policy right := by
  exact Mettapedia.GSLT.GSLT.policy_factors_iff_fiberInvariant
    key select splits policy

/-- Exact replay is equivalent to safety for the identity observation. -/
theorem exactReplayKey_iff_identityPolicySafe
    {State : Type uState} {Key : Type uKey} (key : State → Key) :
    ExactReplayKey key ↔ PolicySafe key (id : State → State) := by
  constructor
  · rintro ⟨decode, recovers⟩
    refine ⟨decode, funext fun state => ?_⟩
    exact (recovers state).symm
  · rintro ⟨decode, factors⟩
    refine ⟨decode, fun state => ?_⟩
    exact (congrFun factors state).symm

/-- Once a key can replay the complete state, every later policy factors
through it. -/
theorem ExactReplayKey.policySafe
    {State : Type uState} {Key : Type uKey} {Value : Type uValue}
    {key : State → Key} (exact : ExactReplayKey key)
    (policy : State → Value) : PolicySafe key policy := by
  rcases exact with ⟨decode, recovers⟩
  refine ⟨policy ∘ decode, funext fun state => ?_⟩
  simp only [Function.comp_apply, recovers state]

/-- Exact replay is equivalent to safety for all state-valued policies.  The
identity policy is the sole necessary test; all other policies follow by
postcomposition. -/
theorem exactReplayKey_iff_allStatePoliciesSafe
    {State : Type uState} {Key : Type uKey} (key : State → Key) :
    ExactReplayKey key ↔ AllPoliciesSafe key State := by
  constructor
  · intro exact policy
    exact exact.policySafe policy
  · intro everyPolicy
    exact (exactReplayKey_iff_identityPolicySafe key).2 (everyPolicy id)

/-- A collision prevents exact replay. -/
theorem collision_prevents_exactReplayKey
    {State : Type uState} {Key : Type uKey} {key : State → Key}
    {left right : State} (different : left ≠ right)
    (collision : key left = key right) :
    ¬ ExactReplayKey key := by
  rintro ⟨decode, recovers⟩
  apply different
  calc
    left = decode (key left) := (recovers left).symm
    _ = decode (key right) := congrArg decode collision
    _ = right := recovers right

/-- The encoding function of every abstract Prime exact codec is an exact
replay key. -/
theorem exactCodec_encode_exactReplayKey {State : Type uState}
    (codec : ExactCodec State) : ExactReplayKey codec.encode :=
  ⟨codec.decode, codec.decode_encode⟩

/-- Consequently every future policy can be evaluated from an exact receipt
representation without reconstructing information that was erased. -/
theorem exactCodec_policySafe {State : Type uState} {Value : Type uValue}
    (codec : ExactCodec State) (policy : State → Value) :
    PolicySafe codec.encode policy :=
  (exactCodec_encode_exactReplayKey codec).policySafe policy

/-! ## One Cost elaboration fibre -/

/-- Compact erasure restricted to one elaboration fibre.  Every elaboration
has the same checked compact term by construction. -/
def compactFibreKey {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort) :
    CostOpenElaboration source term →
      ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
        source.costWholeLanguage targetFree targetBound targetSort :=
  fun _ => term

/-- The proof-relevant key retains the elaboration itself. -/
def provenanceKey {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort} :
    CostOpenElaboration source term → CostOpenElaboration source term :=
  id

/-- On one fibre, factoring through compact syntax is exactly being a
constant policy. -/
theorem compactFibreKey_policySafe_iff_constant
    {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort)
    {Value : Type uValue}
    (policy : CostOpenElaboration source term → Value) :
    PolicySafe (compactFibreKey term) policy ↔
      ∃ value : Value, ∀ elaboration, policy elaboration = value := by
  constructor
  · rintro ⟨keyedPolicy, factors⟩
    refine ⟨keyedPolicy term, fun elaboration => ?_⟩
    exact congrFun factors elaboration
  · rintro ⟨value, constant⟩
    refine ⟨fun _ => value, funext fun elaboration => ?_⟩
    exact constant elaboration

/-- The retained proof-relevant identity key is exact. -/
theorem provenanceKey_exactReplayKey
    {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort} :
    ExactReplayKey (provenanceKey (source := source) (term := term)) := by
  exact ⟨id, fun _ => rfl⟩

/-- Every policy on a Cost elaboration fibre is safe under the retained
provenance key. -/
theorem provenanceKey_policySafe
    {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort}
    {Value : Type uValue}
    (policy : CostOpenElaboration source term → Value) :
    PolicySafe (provenanceKey (source := source) (term := term)) policy :=
  provenanceKey_exactReplayKey.policySafe policy

#print axioms policySafe_iff_fiberInvariant_of_split
#print axioms exactReplayKey_iff_allStatePoliciesSafe
#print axioms collision_prevents_exactReplayKey
#print axioms exactCodec_policySafe
#print axioms compactFibreKey_policySafe_iff_constant
#print axioms provenanceKey_exactReplayKey

end Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
