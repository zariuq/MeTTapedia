import Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyFamilyObservationBridge

/-!
# Cost² keys at the abstract implementation boundary

The complete dependent Cost elaboration carrier has a global compact erasure,
not merely one constant key on each elaboration fibre.  Its canonical compiler
is a section.  This module proves the implementation criterion induced by that
split map:

* a policy may run from the compact key exactly when it is invariant on every
  compact-erasure fibre;
* the compact key is an exact receipt representation exactly when compact
  erasure is faithful; and
* concrete languages may admit compact-derived hot policies while refusing
  exact replay from that same key.

The distinction is abstract.  No representation fields or runtime ABI are
prescribed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoImplementationKeyContract

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

universe uValue

/-! ## The global split compact carrier -/

/-- All intrinsically indexed compact Cost terms over one continued language
authority. -/
abbrev CompactCostCarrier (source : CIGSLT) :=
  Σ index : CostElaborationIndex source,
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage index.targetFree index.targetBound
        index.targetSort

/-- Forget only proof-relevant Cost elaboration while retaining the complete
typed compact term and all of its indices. -/
def compactCarrierKey (source : CIGSLT) :
    CostElaborationFiber source → CompactCostCarrier source
  | ⟨index, term, _elaboration⟩ => ⟨index, term⟩

/-- The independently defined total Cost compiler selects one elaboration of
every compact carrier element. -/
def selectCompactCarrier (source : CIGSLT) :
    CompactCostCarrier source → CostElaborationFiber source
  | ⟨index, term⟩ =>
      ⟨index, CostOpenElaboration.compileTerm source term⟩

@[simp] theorem compactCarrierKey_selectCompactCarrier
    (source : CIGSLT) (compact : CompactCostCarrier source) :
    compactCarrierKey source (selectCompactCarrier source compact) = compact := by
  rcases compact with ⟨index, term⟩
  rfl

/-- Global compact-key safety is exactly invariance under changes of retained
elaboration evidence at fixed compact syntax. -/
theorem compactCarrierKey_policySafe_iff_fiberInvariant
    (source : CIGSLT) {Value : Type uValue}
    (policy : CostElaborationFiber source → Value) :
    PolicySafe (compactCarrierKey source) policy ↔
      ∀ left right,
        compactCarrierKey source left = compactCarrierKey source right →
          policy left = policy right := by
  exact policySafe_iff_fiberInvariant_of_split
    (compactCarrierKey source) (selectCompactCarrier source)
    (compactCarrierKey_selectCompactCarrier source) policy

/-! ## Exact receipt criterion -/

/-- The global compact Cost key admits exact replay precisely when compact
erasure is faithful in every dependent typed fibre. -/
theorem compactCarrierKey_exactReplay_iff_erasureFaithful
    (source : CIGSLT) :
    ExactReplayKey (compactCarrierKey source) ↔
      source.CostCompactErasureFaithful := by
  constructor
  · rintro ⟨decode, recovers⟩ targetFree targetBound targetSort left right erased
    rcases left with ⟨leftTerm, leftElaboration⟩
    rcases right with ⟨rightTerm, rightElaboration⟩
    dsimp only [CIGSLT.costOpenElaborationCarrier,
      CostOpenElaboration.erase] at erased
    subst rightTerm
    let index : CostElaborationIndex source :=
      ⟨targetFree, targetBound, targetSort⟩
    let leftTotal : CostElaborationFiber source :=
      ⟨index, leftTerm, leftElaboration⟩
    let rightTotal : CostElaborationFiber source :=
      ⟨index, leftTerm, rightElaboration⟩
    have totalEquality : leftTotal = rightTotal := by
      apply recovers.injective
      rfl
    have fiberEquality :
        (⟨leftTerm, leftElaboration⟩ : CostElabTerm source
          targetFree targetBound targetSort) =
        ⟨leftTerm, rightElaboration⟩ :=
      eq_of_heq (Sigma.mk.inj totalEquality).2
    have elaborationEquality : leftElaboration = rightElaboration := by
      exact eq_of_heq (Sigma.mk.inj fiberEquality).2
    subst rightElaboration
    rfl
  · intro faithful
    refine ⟨selectCompactCarrier source, ?_⟩
    rintro ⟨index, term, elaboration⟩
    have fiberEquality :
        CostOpenElaboration.compileTerm source term =
          (⟨term, elaboration⟩ : CostElabTerm source
            index.targetFree index.targetBound index.targetSort) :=
      faithful index.targetFree index.targetBound index.targetSort rfl
    exact congrArg (Sigma.mk index) fiberEquality

/-- A faithful compact carrier therefore supplies a genuine exact codec; this
is a derived implementation option, not a field imposed on every backend. -/
def compactExactCodec (source : CIGSLT)
    (faithful : source.CostCompactErasureFaithful) :
    ExactCodec (CostElaborationFiber source) where
  Representation := CompactCostCarrier source
  encode := compactCarrierKey source
  decode := selectCompactCarrier source
  decode_encode := by
    rintro ⟨index, term, elaboration⟩
    have fiberEquality :
        CostOpenElaboration.compileTerm source term =
          (⟨term, elaboration⟩ : CostElabTerm source
            index.targetFree index.targetBound index.targetSort) :=
      faithful index.targetFree index.targetBound index.targetSort rfl
    exact congrArg (Sigma.mk index) fiberEquality

/-! ## Policy-only hot keys remain available -/

/-- Any observation authored directly over compact syntax has an executable
realization from the compact key, even when that key cannot replay the full
proof-relevant state. -/
def compactDerivedPolicyRealization
    (source : CIGSLT) {Value : Type uValue}
    (observeCompact : CompactCostCarrier source → Value) :
    PolicyRealization (compactCarrierKey source)
      (observeCompact ∘ compactCarrierKey source) where
  run := observeCompact
  agrees := rfl

/-- Policy-only NIK admission of a compact-derived observation. -/
def compactDerivedPolicyAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (source : CIGSLT) {Value : Type uValue}
    (observeCompact : CompactCostCarrier source → Value) :
    PolicyKeyAdmission dependencies revision
      (singlePolicyRequest
        (observeCompact ∘ compactCarrierKey source) False)
      (compactCarrierKey source) where
  realize := fun _ => compactDerivedPolicyRealization source observeCompact
  replay := fun impossible => False.elim impossible

/-- The strongest nontrivial compact observation—the complete compact key
itself—runs without claiming that elaboration provenance can be replayed. -/
def compactIdentityPolicyAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (source : CIGSLT) :
    PolicyKeyAdmission dependencies revision
      (singlePolicyRequest (compactCarrierKey source) False)
      (compactCarrierKey source) :=
  compactDerivedPolicyAdmission dependencies revision source id

/-! ## Axiom audit -/

#print axioms compactCarrierKey_policySafe_iff_fiberInvariant
#print axioms compactCarrierKey_exactReplay_iff_erasureFaithful
#print axioms compactExactCodec
#print axioms compactDerivedPolicyAdmission

end Mettapedia.Languages.MeTTa.Prime.CostTwoImplementationKeyContract
