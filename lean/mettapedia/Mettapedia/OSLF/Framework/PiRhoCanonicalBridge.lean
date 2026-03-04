import Mettapedia.Languages.ProcessCalculi.PiCalculus.Main
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.LanguageMorphism
import Mettapedia.OSLF.Formula
import Mettapedia.Logic.ModalMuCalculus
import Mettapedia.Logic.OSLFKripkeBridge
import Mettapedia.Logic.OSLFImageFinite
import Mettapedia.Logic.OSLFKSUnificationSketch
import Mettapedia.Logic.OSLFDistinctionGraph

/-!
# π→ρ Canonical Package Bridge (Pre-OSLF)

This module consumes the canonical pre-OSLF π→ρ correspondence package from
`PiCalculus/Main.lean` and exposes an OSLF-morphism-facing endpoint shape.
-/

namespace Mettapedia.OSLF.Framework.PiRhoCanonicalBridge

open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- OSLF-morphism-facing endpoint extracted from the canonical π→ρ prelude
package: reserved-name hygiene, RF forward clause, one-step backward outcomes,
trace-sensitive target-sensitive star decomposition, RF trace reflection, and
freshness-threaded non-RF admin correspondence. -/
abbrev CalcPreludeLangMorphismEndpoint
    (N : Finset String)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) : Prop :=
  Disjoint N fullEncodeReservedNames ∧
  CalcRFForwardClause N ∧
  CalcBackwardOneStepOutcomeClause N ∧
  CalcBackwardStarTraceTargetSensitiveClause N ∧
  CalcBackwardRFTraceClause N ∧
  CalcNonRFAdminFreshClause N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh

/-- Direct hook from `CalcPreludeCanonicalPackage` into the OSLF
morphism-facing endpoint shape. -/
theorem calcPreludeCanonicalPackage_to_langMorphismEndpoint
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hcanon : CalcPreludeCanonicalPackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh) :
    CalcPreludeLangMorphismEndpoint N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  exact ⟨hcanon.userObs.disjoint_reserved,
    hcanon.userObs.prelude.forward_rf,
    hcanon.userObs.prelude.backward_one_step,
    hcanon.backward_star_trace_target_sensitive,
    hcanon.backward_rf_trace,
    hcanon.userObs.prelude.nonRF_admin_fresh⟩

/-- End-to-end pre-OSLF theorem in `OSLF/Framework`: instantiate the canonical
π→ρ package and immediately consume it through the morphism-facing endpoint. -/
theorem piRho_canonical_package_end_to_end
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    CalcPreludeLangMorphismEndpoint N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  exact calcPreludeCanonicalPackage_to_langMorphismEndpoint
    (hcanon :=
      calculus_correspondence_prelude_canonical_package
        (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh)

/-! ## Domain-Indexed Semantic Morphism

The canonical pre-OSLF package naturally yields a semantic morphism on the
encoded/fresh source domain. This is the intended endpoint for downstream OSLF
proofs (instead of an unconstrained total map over all patterns).
-/

/-- Domain predicate for the canonical backward API: encoded-source classifiers
with freshness threading. -/
abbrev EncodedFreshDomain (N : Finset String) : Pattern → Prop :=
  BackwardAdminReflection.EncodedSCStepSourceFresh N

/-- Canonical domain-indexed semantic morphism extracted from the pre-OSLF
package. This records exactly the endpoint obligations used downstream:
RF forward simulation, one-step/star fresh backward outcomes on the encoded
domain, star trace/target-sensitive decomposition, RF trace reflection, and
non-RF admin freshness clause. -/
structure CalcPreludeDomainIndexedSemanticMorphism
    (N : Finset String)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) : Prop where
  disjoint_reserved : Disjoint N fullEncodeReservedNames
  forward_rf : CalcRFForwardClause N
  one_step_fresh_outcome :
    ∀ {src tgt : Pattern},
      EncodedFreshDomain N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt) →
      ∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds
  star_fresh_outcome :
    ∀ {src tgt : Pattern},
      EncodedFreshDomain N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      ∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds
  backward_star_trace_target_sensitive :
    CalcBackwardStarTraceTargetSensitiveClause N
  backward_rf_trace :
    CalcBackwardRFTraceClause N
  nonRF_admin_fresh :
    CalcNonRFAdminFreshClause N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh

/-- The domain-indexed semantic morphism is induced by the canonical pre-OSLF
package object. -/
theorem calcPreludeCanonicalPackage_to_domainIndexedSemanticMorphism
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hcanon : CalcPreludeCanonicalPackage N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh) :
    CalcPreludeDomainIndexedSemanticMorphism N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  refine
    { disjoint_reserved := hcanon.userObs.disjoint_reserved
      forward_rf := hcanon.userObs.prelude.forward_rf
      one_step_fresh_outcome := ?_
      star_fresh_outcome := ?_
      backward_star_trace_target_sensitive := hcanon.backward_star_trace_target_sensitive
      backward_rf_trace := hcanon.backward_rf_trace
      nonRF_admin_fresh := hcanon.userObs.prelude.nonRF_admin_fresh }
  · intro src tgt hsrc hstep
    exact BackwardAdminReflection.weak_backward_outcome_fresh_of_encodedSC_step_source_fresh
      (N := N) (src := src) (tgt := tgt) hsrc hstep
  · intro src tgt hsrc hstep
    exact BackwardAdminReflection.weak_backward_outcome_fresh_of_encodedSC_star_source_fresh
      (N := N) (src := src) (tgt := tgt) hsrc hstep

/-- Canonical OSLF endpoint: instantiate the pre-OSLF package and expose it as
the domain-indexed semantic morphism. -/
theorem piRho_canonical_domainIndexedSemanticMorphism_end_to_end
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    CalcPreludeDomainIndexedSemanticMorphism N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  exact calcPreludeCanonicalPackage_to_domainIndexedSemanticMorphism
    (hcanon :=
      calculus_correspondence_prelude_canonical_package
        (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh)

/-! ## End-to-End OSLF Formula Consumption

Consume the canonical package through the bridge and derive an OSLF formula
fact over the ρ star relation (`◇ ⊤`).
-/

/-- Star-level ρ reachability relation used as an OSLF relation argument. -/
abbrev rhoCoreStarRel : Pattern → Pattern → Prop :=
  fun p q => Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar p q)

/-- One-step derived ρ reachability relation (admin layer). -/
abbrev rhoDerivedStepRel : Pattern → Pattern → Prop :=
  fun p q =>
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived p q)

/-- Star-level derived ρ reachability relation (admin layer). -/
abbrev rhoDerivedStarRel : Pattern → Pattern → Prop :=
  fun p q =>
    Nonempty
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar p q)

/-- Canonical executable one-step core relation used for HM-ready endpoint
consumption. -/
abbrev rhoCoreCanonicalRel : Pattern → Pattern → Prop :=
  Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
    Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc

/-- Canonical executable one-step extended/derived-facing relation used for
HM-ready endpoint consumption. -/
abbrev rhoDerivedCanonicalRel : Pattern → Pattern → Prop :=
  Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
    Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalcSetExt

/-- Concrete image-finiteness for the canonical executable core relation. -/
theorem imageFinite_rhoCoreCanonicalRel
    (p : Pattern) : Set.Finite {q : Pattern | rhoCoreCanonicalRel p q} := by
  simpa [rhoCoreCanonicalRel] using
    Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces
      Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc p

/-- Concrete image-finiteness for the canonical executable derived-facing
relation. -/
theorem imageFinite_rhoDerivedCanonicalRel
    (p : Pattern) : Set.Finite {q : Pattern | rhoDerivedCanonicalRel p q} := by
  simpa [rhoDerivedCanonicalRel] using
    Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces
      Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalcSetExt p

/-- `◇⊤` over core-star always holds (via reflexivity). -/
theorem sem_diaTop_coreStar_refl {I : Mettapedia.OSLF.Formula.AtomSem} (p : Pattern) :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel I
      (.dia .top) p := by
  exact ⟨p,
    ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar.refl p⟩,
    trivial⟩

/-- Inductive modal fragment used by the canonical endpoint-level transfer:
atoms + Boolean connectives + `◇` + `□` (no `⊥` constructor). -/
inductive EndpointDiaBoxFragment : Mettapedia.OSLF.Formula.OSLFFormula → Prop where
  | top : EndpointDiaBoxFragment .top
  | atom (a : String) : EndpointDiaBoxFragment (.atom a)
  | and {φ ψ} :
      EndpointDiaBoxFragment φ →
      EndpointDiaBoxFragment ψ →
      EndpointDiaBoxFragment (.and φ ψ)
  | or {φ ψ} :
      EndpointDiaBoxFragment φ →
      EndpointDiaBoxFragment ψ →
      EndpointDiaBoxFragment (.or φ ψ)
  | imp {φ ψ} :
      EndpointDiaBoxFragment φ →
      EndpointDiaBoxFragment ψ →
      EndpointDiaBoxFragment (.imp φ ψ)
  | dia {φ} :
      EndpointDiaBoxFragment φ →
      EndpointDiaBoxFragment (.dia φ)
  | box {φ} :
      EndpointDiaBoxFragment φ →
      EndpointDiaBoxFragment (.box φ)

/-- Broader endpoint fragment: full boolean/modal syntax of `OSLFFormula`
(`⊤, ⊥, atom, ∧, ∨, →, ◇, □`). -/
inductive EndpointBroadFragment : Mettapedia.OSLF.Formula.OSLFFormula → Prop where
  | top : EndpointBroadFragment .top
  | bot : EndpointBroadFragment .bot
  | atom (a : String) : EndpointBroadFragment (.atom a)
  | and {φ ψ} :
      EndpointBroadFragment φ →
      EndpointBroadFragment ψ →
      EndpointBroadFragment (.and φ ψ)
  | or {φ ψ} :
      EndpointBroadFragment φ →
      EndpointBroadFragment ψ →
      EndpointBroadFragment (.or φ ψ)
  | imp {φ ψ} :
      EndpointBroadFragment φ →
      EndpointBroadFragment ψ →
      EndpointBroadFragment (.imp φ ψ)
  | dia {φ} :
      EndpointBroadFragment φ →
      EndpointBroadFragment (.dia φ)
  | box {φ} :
      EndpointBroadFragment φ →
      EndpointBroadFragment (.box φ)

/-- Legacy dia/box endpoint fragment embeds into the broader fragment. -/
theorem EndpointDiaBoxFragment.to_broad
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (h : EndpointDiaBoxFragment φ) :
    EndpointBroadFragment φ := by
  induction h with
  | top => exact EndpointBroadFragment.top
  | atom a => exact EndpointBroadFragment.atom a
  | and hφ hψ ihφ ihψ => exact EndpointBroadFragment.and ihφ ihψ
  | or hφ hψ ihφ ihψ => exact EndpointBroadFragment.or ihφ ihψ
  | imp hφ hψ ihφ ihψ => exact EndpointBroadFragment.imp ihφ ihψ
  | dia hφ ihφ => exact EndpointBroadFragment.dia ihφ
  | box hφ ihφ => exact EndpointBroadFragment.box ihφ

/-- Endpoint broad fragment embeds into the generic framework broad fragment. -/
theorem EndpointBroadFragment.to_framework
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (h : EndpointBroadFragment φ) :
    Mettapedia.OSLF.Framework.LangMorphism.BroadFragment φ := by
  induction h with
  | top => exact Mettapedia.OSLF.Framework.LangMorphism.BroadFragment.top
  | bot => exact Mettapedia.OSLF.Framework.LangMorphism.BroadFragment.bot
  | atom a => exact Mettapedia.OSLF.Framework.LangMorphism.BroadFragment.atom a
  | and hφ hψ ihφ ihψ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.BroadFragment.and ihφ ihψ
  | or hφ hψ ihφ ihψ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.BroadFragment.or ihφ ihψ
  | imp hφ hψ ihφ ihψ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.BroadFragment.imp ihφ ihψ
  | dia hφ ihφ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.BroadFragment.dia ihφ
  | box hφ ihφ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.BroadFragment.box ihφ

/-- Endpoint dia/box fragment embeds into the generic framework dia/box
fragment. -/
theorem EndpointDiaBoxFragment.to_framework
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (h : EndpointDiaBoxFragment φ) :
    Mettapedia.OSLF.Framework.LangMorphism.DiaBoxFragment φ := by
  induction h with
  | top => exact Mettapedia.OSLF.Framework.LangMorphism.DiaBoxFragment.top
  | atom a => exact Mettapedia.OSLF.Framework.LangMorphism.DiaBoxFragment.atom a
  | and hφ hψ ihφ ihψ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.DiaBoxFragment.and ihφ ihψ
  | or hφ hψ ihφ ihψ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.DiaBoxFragment.or ihφ ihψ
  | imp hφ hψ ihφ ihψ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.DiaBoxFragment.imp ihφ ihψ
  | dia hφ ihφ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.DiaBoxFragment.dia ihφ
  | box hφ ihφ =>
      exact Mettapedia.OSLF.Framework.LangMorphism.DiaBoxFragment.box ihφ

/-- Semantic invariance on the broad endpoint fragment under explicit
atom-preservation assumptions (`I` and `J` agree on atoms). -/
theorem sem_iff_of_endpointBroadFragment
    {R : Pattern → Pattern → Prop}
    {I J : Mettapedia.OSLF.Formula.AtomSem}
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointBroadFragment φ)
    (hAtomIff : ∀ a p, I a p ↔ J a p) :
    ∀ p, Mettapedia.OSLF.Formula.sem R I φ p ↔
      Mettapedia.OSLF.Formula.sem R J φ p := by
  exact Mettapedia.OSLF.Framework.LangMorphism.sem_iff_of_broadFragment
    (R := R) (I := I) (J := J) (φ := φ) hfrag.to_framework hAtomIff

/-- Dia/box endpoint fragment inherits the broad-fragment atom-preservation
invariance theorem. -/
theorem sem_iff_of_endpointDiaBoxFragment
    {R : Pattern → Pattern → Prop}
    {I J : Mettapedia.OSLF.Formula.AtomSem}
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    (hAtomIff : ∀ a p, I a p ↔ J a p) :
    ∀ p, Mettapedia.OSLF.Formula.sem R I φ p ↔
      Mettapedia.OSLF.Formula.sem R J φ p := by
  exact Mettapedia.OSLF.Framework.LangMorphism.sem_iff_of_diaBoxFragment
    (R := R) (I := I) (J := J) (φ := φ) hfrag.to_framework hAtomIff

/-- One-way transfer on the broad endpoint fragment under explicit
atom-preservation equivalence assumptions. -/
theorem sem_transfer_of_endpointBroadFragment
    {R : Pattern → Pattern → Prop}
    {I J : Mettapedia.OSLF.Formula.AtomSem}
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointBroadFragment φ)
    (hAtomIff : ∀ a p, I a p ↔ J a p)
    {p : Pattern}
    (hsem : Mettapedia.OSLF.Formula.sem R I φ p) :
    Mettapedia.OSLF.Formula.sem R J φ p :=
  (sem_iff_of_endpointBroadFragment hfrag hAtomIff p).1 hsem

/-- One-way transfer on the dia/box endpoint fragment under explicit
atom-preservation equivalence assumptions. -/
theorem sem_transfer_of_endpointDiaBoxFragment
    {R : Pattern → Pattern → Prop}
    {I J : Mettapedia.OSLF.Formula.AtomSem}
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    (hAtomIff : ∀ a p, I a p ↔ J a p)
    {p : Pattern}
    (hsem : Mettapedia.OSLF.Formula.sem R I φ p) :
    Mettapedia.OSLF.Formula.sem R J φ p :=
  (sem_iff_of_endpointDiaBoxFragment hfrag hAtomIff p).1 hsem

/-- Formula-induction transfer principle for the endpoint dia/box fragment.

If all atoms are true and every state satisfies `◇⊤`, then every formula in the
inductive endpoint fragment is true at every state. -/
theorem sem_of_endpointDiaBoxFragment_on_domain
    {R : Pattern → Pattern → Prop}
    {D : Pattern → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    (hAtomDomain : ∀ a p, D p → I a p)
    (hDomainBackward : ∀ {p q}, D p → R q p → D q)
    (hDiaDomain : ∀ p, D p → ∃ q, R p q ∧ D q) :
    ∀ p, D p → Mettapedia.OSLF.Formula.sem R I φ p := by
  exact Mettapedia.OSLF.Framework.LangMorphism.sem_of_diaBoxFragment_on_domain
    (R := R) (D := D) (I := I) (φ := φ)
    hfrag.to_framework hAtomDomain hDomainBackward hDiaDomain

/-- Core-star relation is reflexive. -/
theorem rhoCoreStarRel_refl (p : Pattern) : rhoCoreStarRel p p :=
  ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar.refl p⟩

/-- Core-star relation is transitive. -/
theorem rhoCoreStarRel_trans {p q r : Pattern}
    (hpq : rhoCoreStarRel p q) (hqr : rhoCoreStarRel q r) :
    rhoCoreStarRel p r := by
  rcases hpq with ⟨hpq'⟩
  rcases hqr with ⟨hqr'⟩
  exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar.trans hpq' hqr'⟩

/-- Derived-star relation is reflexive. -/
theorem rhoDerivedStarRel_refl (p : Pattern) : rhoDerivedStarRel p p :=
  ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar.refl p⟩

/-- Derived-star relation is transitive. -/
theorem rhoDerivedStarRel_trans {p q r : Pattern}
    (hpq : rhoDerivedStarRel p q) (hqr : rhoDerivedStarRel q r) :
    rhoDerivedStarRel p r := by
  rcases hpq with ⟨hpq'⟩
  rcases hqr with ⟨hqr'⟩
  exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar.trans hpq' hqr'⟩

/-- Reachable encoded-domain carrier: a fixed encoded/fresh source plus any
derived-star reachable state. -/
abbrev EncodedFreshReachableDomain
    (N : Finset String) (src : Pattern) (p : Pattern) : Prop :=
  EncodedFreshDomain N src ∧ rhoDerivedStarRel src p

/-- Source state is always in its own reachable encoded-domain carrier. -/
theorem encodedFreshReachableDomain_refl
    {N : Finset String} {src : Pattern}
    (hsrc : EncodedFreshDomain N src) :
    EncodedFreshReachableDomain N src src :=
  ⟨hsrc, rhoDerivedStarRel_refl src⟩

/-- Reachable encoded-domain carrier is forward-closed under derived-star. -/
theorem encodedFreshReachableDomain_closed
    {N : Finset String} {src p q : Pattern}
    (hdom : EncodedFreshReachableDomain N src p)
    (hpq : rhoDerivedStarRel p q) :
    EncodedFreshReachableDomain N src q := by
  rcases hdom with ⟨hsrc, hsp⟩
  exact ⟨hsrc, rhoDerivedStarRel_trans hsp hpq⟩

/-- Explicit finite subrelation witness for HM-converse use on potentially
infinite ambient relations. -/
structure FiniteSubrelation (R : Pattern → Pattern → Prop) where
  rel : Pattern → Pattern → Prop
  subset : ∀ {p q : Pattern}, rel p q → R p q
  imageFinite : ∀ p : Pattern, Set.Finite {q : Pattern | rel p q}

/-- HM converse on an explicitly finite subrelation. -/
theorem hm_converse_of_finiteSubrelation
    {R : Pattern → Pattern → Prop}
    (S : FiniteSubrelation R)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {p q : Pattern}
    (hobs :
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq S.rel I p q) :
    Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar S.rel p q := by
  exact
    Mettapedia.Logic.OSLFKSUnificationSketch.hm_converse_schema
      (R := S.rel)
      (I := I)
      (hImageFinite := S.imageFinite)
      hobs

/-- Reachability-scoped finite subrelation of `rhoCoreStarRel` anchored at
`root`: every related successor is exactly `root`, gated by `p ⇝* root`. -/
def reachableCoreStarFiniteSubrelation (root : Pattern) :
    FiniteSubrelation rhoCoreStarRel where
  rel := fun p q => q = root ∧ rhoCoreStarRel p root
  subset := by
    intro p q hrel
    rcases hrel with ⟨hq, hp⟩
    simpa [hq] using hp
  imageFinite := by
    intro p
    refine Set.Finite.subset (Set.finite_singleton root) ?_
    intro q hq
    simpa [Set.mem_singleton_iff] using hq.1

/-- Reachability-scoped finite subrelation of `rhoDerivedStarRel` anchored at
`root`: every related successor is exactly `root`, gated by `p ⇝ᵈ* root`. -/
def reachableDerivedStarFiniteSubrelation (root : Pattern) :
    FiniteSubrelation rhoDerivedStarRel where
  rel := fun p q => q = root ∧ rhoDerivedStarRel p root
  subset := by
    intro p q hrel
    rcases hrel with ⟨hq, hp⟩
    simpa [hq] using hp
  imageFinite := by
    intro p
    refine Set.Finite.subset (Set.finite_singleton root) ?_
    intro q hq
    simpa [Set.mem_singleton_iff] using hq.1

/-- HM-ready converse wrapper for the canonical core-star endpoint relation.
The relation-specific image-finiteness obligation is explicit. -/
theorem hm_converse_rhoCoreStarRel
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (hImageFinite : ∀ p : Pattern, Set.Finite {q : Pattern | rhoCoreStarRel p q})
    {p q : Pattern}
    (hobs :
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq
        rhoCoreStarRel I p q) :
    Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar rhoCoreStarRel p q := by
  exact
    Mettapedia.Logic.OSLFKSUnificationSketch.hm_converse_schema
      (R := rhoCoreStarRel)
      (I := I)
      (hImageFinite := hImageFinite)
      hobs

/-- HM-ready converse wrapper for the canonical derived-star endpoint relation.
The relation-specific image-finiteness obligation is explicit. -/
theorem hm_converse_rhoDerivedStarRel
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (hImageFinite : ∀ p : Pattern, Set.Finite {q : Pattern | rhoDerivedStarRel p q})
    {p q : Pattern}
    (hobs :
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq
        rhoDerivedStarRel I p q) :
    Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar rhoDerivedStarRel p q := by
  exact
    Mettapedia.Logic.OSLFKSUnificationSketch.hm_converse_schema
      (R := rhoDerivedStarRel)
      (I := I)
      (hImageFinite := hImageFinite)
      hobs

/-- HM-ready converse wrapper for the canonical executable core relation, with
concrete image-finiteness discharged. -/
theorem hm_converse_rhoCoreCanonicalRel
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {p q : Pattern}
    (hobs :
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq
        rhoCoreCanonicalRel I p q) :
    Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar
      rhoCoreCanonicalRel p q := by
  exact
    Mettapedia.Logic.OSLFKSUnificationSketch.hm_converse_schema
      (R := rhoCoreCanonicalRel)
      (I := I)
      (hImageFinite := imageFinite_rhoCoreCanonicalRel)
      hobs

/-- HM-ready converse wrapper for the canonical executable derived-facing
relation, with concrete image-finiteness discharged. -/
theorem hm_converse_rhoDerivedCanonicalRel
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {p q : Pattern}
    (hobs :
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq
        rhoDerivedCanonicalRel I p q) :
    Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar
      rhoDerivedCanonicalRel p q := by
  exact
    Mettapedia.Logic.OSLFKSUnificationSketch.hm_converse_schema
      (R := rhoDerivedCanonicalRel)
      (I := I)
      (hImageFinite := imageFinite_rhoDerivedCanonicalRel)
      hobs

/-- Full classical HM iff on the canonical executable core relation:
observer-indistinguishability coincides with full bisimilarity under explicit
forward/backward image-finiteness (forward is discharged here). -/
theorem hm_iff_fullBisim_rhoCoreCanonicalRel
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (hPredFinite : ∀ p : Pattern, Set.Finite {q : Pattern | rhoCoreCanonicalRel q p})
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      rhoCoreCanonicalRel I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      rhoCoreCanonicalRel I p q := by
  exact
    Mettapedia.Logic.OSLFDistinctionGraph.indist_iff_fullBisim_imageFinite
      (R := rhoCoreCanonicalRel)
      (I := I)
      (hImageFinite := imageFinite_rhoCoreCanonicalRel)
      (hPredFinite := hPredFinite)
      p q

/-- Full classical HM iff on the canonical executable derived-facing relation:
observer-indistinguishability coincides with full bisimilarity under explicit
forward/backward image-finiteness (forward is discharged here). -/
theorem hm_iff_fullBisim_rhoDerivedCanonicalRel
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (hPredFinite : ∀ p : Pattern, Set.Finite {q : Pattern | rhoDerivedCanonicalRel q p})
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      rhoDerivedCanonicalRel I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      rhoDerivedCanonicalRel I p q := by
  exact
    Mettapedia.Logic.OSLFDistinctionGraph.indist_iff_fullBisim_imageFinite
      (R := rhoDerivedCanonicalRel)
      (I := I)
      (hImageFinite := imageFinite_rhoDerivedCanonicalRel)
      (hPredFinite := hPredFinite)
      p q

/-- Restrict a relation to a finite carrier on both source and target. -/
abbrev finiteCarrierRel
    (R : Pattern → Pattern → Prop)
    (carrier : Finset Pattern) : Pattern → Pattern → Prop :=
  fun p q => p ∈ carrier ∧ q ∈ carrier ∧ R p q

/-- Forward image-finiteness for finite-carrier restricted relations. -/
theorem imageFinite_finiteCarrierRel
    (R : Pattern → Pattern → Prop)
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | finiteCarrierRel R carrier p q} := by
  refine Set.Finite.subset carrier.finite_toSet ?_
  intro q hq
  exact hq.2.1

/-- Backward image-finiteness for finite-carrier restricted relations. -/
theorem predFinite_finiteCarrierRel
    (R : Pattern → Pattern → Prop)
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | finiteCarrierRel R carrier q p} := by
  refine Set.Finite.subset carrier.finite_toSet ?_
  intro q hq
  exact hq.1

/-- Scoped canonical executable core relation over a finite carrier. -/
abbrev rhoCoreCanonicalRelOn
    (carrier : Finset Pattern) : Pattern → Pattern → Prop :=
  finiteCarrierRel rhoCoreCanonicalRel carrier

/-- Scoped canonical executable derived-facing relation over a finite carrier. -/
abbrev rhoDerivedCanonicalRelOn
    (carrier : Finset Pattern) : Pattern → Pattern → Prop :=
  finiteCarrierRel rhoDerivedCanonicalRel carrier

/-- Forward image-finiteness for scoped canonical executable core relation. -/
theorem imageFinite_rhoCoreCanonicalRelOn
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | rhoCoreCanonicalRelOn carrier p q} := by
  simpa [rhoCoreCanonicalRelOn] using
    imageFinite_finiteCarrierRel rhoCoreCanonicalRel carrier p

/-- Backward image-finiteness for scoped canonical executable core relation. -/
theorem predFinite_rhoCoreCanonicalRelOn
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | rhoCoreCanonicalRelOn carrier q p} := by
  simpa [rhoCoreCanonicalRelOn] using
    predFinite_finiteCarrierRel rhoCoreCanonicalRel carrier p

/-- Forward image-finiteness for scoped canonical executable derived-facing
relation. -/
theorem imageFinite_rhoDerivedCanonicalRelOn
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | rhoDerivedCanonicalRelOn carrier p q} := by
  simpa [rhoDerivedCanonicalRelOn] using
    imageFinite_finiteCarrierRel rhoDerivedCanonicalRel carrier p

/-- Backward image-finiteness for scoped canonical executable derived-facing
relation. -/
theorem predFinite_rhoDerivedCanonicalRelOn
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | rhoDerivedCanonicalRelOn carrier q p} := by
  simpa [rhoDerivedCanonicalRelOn] using
    predFinite_finiteCarrierRel rhoDerivedCanonicalRel carrier p

/-- Full classical HM iff on finite-carrier-scoped core canonical relation,
with both image-finiteness sides discharged by construction. -/
theorem hm_iff_fullBisim_rhoCoreCanonicalRelOn
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (carrier : Finset Pattern)
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      (rhoCoreCanonicalRelOn carrier) I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoCoreCanonicalRelOn carrier) I p q := by
  exact
    Mettapedia.Logic.OSLFDistinctionGraph.indist_iff_fullBisim_imageFinite
      (R := rhoCoreCanonicalRelOn carrier)
      (I := I)
      (hImageFinite := imageFinite_rhoCoreCanonicalRelOn carrier)
      (hPredFinite := predFinite_rhoCoreCanonicalRelOn carrier)
      p q

/-- Full classical HM iff on finite-carrier-scoped derived canonical relation,
with both image-finiteness sides discharged by construction. -/
theorem hm_iff_fullBisim_rhoDerivedCanonicalRelOn
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (carrier : Finset Pattern)
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      (rhoDerivedCanonicalRelOn carrier) I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoDerivedCanonicalRelOn carrier) I p q := by
  exact
    Mettapedia.Logic.OSLFDistinctionGraph.indist_iff_fullBisim_imageFinite
      (R := rhoDerivedCanonicalRelOn carrier)
      (I := I)
      (hImageFinite := imageFinite_rhoDerivedCanonicalRelOn carrier)
      (hPredFinite := predFinite_rhoDerivedCanonicalRelOn carrier)
      p q

/-- Assumption-free concrete canary: HM iff on scoped core canonical relation
over a two-state carrier. -/
theorem hm_iff_fullBisim_rhoCoreCanonicalRelOn_pair_canary
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      (rhoCoreCanonicalRelOn ({p, q} : Finset Pattern)) I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoCoreCanonicalRelOn ({p, q} : Finset Pattern)) I p q := by
  simpa using
    hm_iff_fullBisim_rhoCoreCanonicalRelOn
      (I := I) ({p, q} : Finset Pattern) p q

/-- Assumption-free concrete canary: HM iff on scoped derived canonical relation
over a two-state carrier. -/
theorem hm_iff_fullBisim_rhoDerivedCanonicalRelOn_pair_canary
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      (rhoDerivedCanonicalRelOn ({p, q} : Finset Pattern)) I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoDerivedCanonicalRelOn ({p, q} : Finset Pattern)) I p q := by
  simpa using
    hm_iff_fullBisim_rhoDerivedCanonicalRelOn
      (I := I) ({p, q} : Finset Pattern) p q

/-- Scoped SC-quotiented canonical executable core relation on a finite carrier.
Source/target are restricted to `carrier`, and the canonical step is taken up
to ρ structural congruence on both ends. -/
abbrev rhoCoreCanonicalSCQuotRelOn
    (carrier : Finset Pattern) : Pattern → Pattern → Prop :=
  fun p q =>
    p ∈ carrier ∧
    q ∈ carrier ∧
    ∃ p' q',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p p' ∧
      rhoCoreCanonicalRel p' q' ∧
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence q' q

/-- Scoped SC-quotiented canonical executable derived-facing relation on a
finite carrier. -/
abbrev rhoDerivedCanonicalSCQuotRelOn
    (carrier : Finset Pattern) : Pattern → Pattern → Prop :=
  fun p q =>
    p ∈ carrier ∧
    q ∈ carrier ∧
    ∃ p' q',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p p' ∧
      rhoDerivedCanonicalRel p' q' ∧
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence q' q

/-- Forward image-finiteness for scoped SC-quotiented core relation. -/
theorem imageFinite_rhoCoreCanonicalSCQuotRelOn
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | rhoCoreCanonicalSCQuotRelOn carrier p q} := by
  refine Set.Finite.subset carrier.finite_toSet ?_
  intro q hq
  exact hq.2.1

/-- Backward image-finiteness for scoped SC-quotiented core relation. -/
theorem predFinite_rhoCoreCanonicalSCQuotRelOn
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | rhoCoreCanonicalSCQuotRelOn carrier q p} := by
  refine Set.Finite.subset carrier.finite_toSet ?_
  intro q hq
  exact hq.1

/-- Forward image-finiteness for scoped SC-quotiented derived relation. -/
theorem imageFinite_rhoDerivedCanonicalSCQuotRelOn
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | rhoDerivedCanonicalSCQuotRelOn carrier p q} := by
  refine Set.Finite.subset carrier.finite_toSet ?_
  intro q hq
  exact hq.2.1

/-- Backward image-finiteness for scoped SC-quotiented derived relation. -/
theorem predFinite_rhoDerivedCanonicalSCQuotRelOn
    (carrier : Finset Pattern)
    (p : Pattern) :
    Set.Finite {q : Pattern | rhoDerivedCanonicalSCQuotRelOn carrier q p} := by
  refine Set.Finite.subset carrier.finite_toSet ?_
  intro q hq
  exact hq.1

/-- Full classical HM iff on scoped SC-quotiented canonical core relation.
Both image-finiteness sides are discharged globally for this chosen relation
family. -/
theorem hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (carrier : Finset Pattern)
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      (rhoCoreCanonicalSCQuotRelOn carrier) I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoCoreCanonicalSCQuotRelOn carrier) I p q := by
  exact
    Mettapedia.Logic.OSLFDistinctionGraph.indist_iff_fullBisim_imageFinite
      (R := rhoCoreCanonicalSCQuotRelOn carrier)
      (I := I)
      (hImageFinite := imageFinite_rhoCoreCanonicalSCQuotRelOn carrier)
      (hPredFinite := predFinite_rhoCoreCanonicalSCQuotRelOn carrier)
      p q

/-- Full classical HM iff on scoped SC-quotiented canonical derived relation.
Both image-finiteness sides are discharged globally for this chosen relation
family. -/
theorem hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (carrier : Finset Pattern)
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      (rhoDerivedCanonicalSCQuotRelOn carrier) I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoDerivedCanonicalSCQuotRelOn carrier) I p q := by
  exact
    Mettapedia.Logic.OSLFDistinctionGraph.indist_iff_fullBisim_imageFinite
      (R := rhoDerivedCanonicalSCQuotRelOn carrier)
      (I := I)
      (hImageFinite := imageFinite_rhoDerivedCanonicalSCQuotRelOn carrier)
      (hPredFinite := predFinite_rhoDerivedCanonicalSCQuotRelOn carrier)
      p q

/-- Assumption-free concrete canary: HM iff on scoped SC-quotiented core
relation over a two-state carrier. -/
theorem hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn_pair_canary
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      (rhoCoreCanonicalSCQuotRelOn ({p, q} : Finset Pattern)) I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoCoreCanonicalSCQuotRelOn ({p, q} : Finset Pattern)) I p q := by
  simpa using
    hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn
      (I := I) ({p, q} : Finset Pattern) p q

/-- Assumption-free concrete canary: HM iff on scoped SC-quotiented derived
relation over a two-state carrier. -/
theorem hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn_pair_canary
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (p q : Pattern) :
    Mettapedia.Logic.OSLFDistinctionGraph.indistObs
      (rhoDerivedCanonicalSCQuotRelOn ({p, q} : Finset Pattern)) I p q
    ↔
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoDerivedCanonicalSCQuotRelOn ({p, q} : Finset Pattern)) I p q := by
  simpa using
    hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn
      (I := I) ({p, q} : Finset Pattern) p q

/-- Lift a concrete canonical core step into the scoped SC-quotiented core
relation (nontrivial edge witness). -/
theorem rhoCoreCanonicalSCQuotRelOn_of_core_step
    (carrier : Finset Pattern)
    {p q : Pattern}
    (hp : p ∈ carrier)
    (hq : q ∈ carrier)
    (hstep : rhoCoreCanonicalRel p q) :
    rhoCoreCanonicalSCQuotRelOn carrier p q := by
  refine ⟨hp, hq, p, q, ?_, hstep, ?_⟩
  · exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl p
  · exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl q

/-- Lift a concrete canonical derived-facing step into the scoped SC-quotiented
derived relation (nontrivial edge witness). -/
theorem rhoDerivedCanonicalSCQuotRelOn_of_derived_step
    (carrier : Finset Pattern)
    {p q : Pattern}
    (hp : p ∈ carrier)
    (hq : q ∈ carrier)
    (hstep : rhoDerivedCanonicalRel p q) :
    rhoDerivedCanonicalSCQuotRelOn carrier p q := by
  refine ⟨hp, hq, p, q, ?_, hstep, ?_⟩
  · exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl p
  · exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl q

/-- Regression canary: a nontrivial scoped SC-quotiented core edge is preserved
while the same endpoint yields full bisimilarity via assumption-free HM iff. -/
theorem hm_scoped_coreSC_edge_preservation_canary
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (carrier : Finset Pattern)
    {p q : Pattern}
    (hp : p ∈ carrier)
    (hq : q ∈ carrier)
    (hstep : rhoCoreCanonicalRel p q)
    (hobs :
      Mettapedia.Logic.OSLFDistinctionGraph.indistObs
        (rhoCoreCanonicalSCQuotRelOn carrier) I p q) :
    rhoCoreCanonicalSCQuotRelOn carrier p q ∧
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoCoreCanonicalSCQuotRelOn carrier) I p q := by
  refine ⟨rhoCoreCanonicalSCQuotRelOn_of_core_step carrier hp hq hstep, ?_⟩
  exact (hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn I carrier p q).1 hobs

/-- Regression canary: a nontrivial scoped SC-quotiented derived edge is
preserved while the same endpoint yields full bisimilarity via assumption-free
HM iff. -/
theorem hm_scoped_derivedSC_edge_preservation_canary
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (carrier : Finset Pattern)
    {p q : Pattern}
    (hp : p ∈ carrier)
    (hq : q ∈ carrier)
    (hstep : rhoDerivedCanonicalRel p q)
    (hobs :
      Mettapedia.Logic.OSLFDistinctionGraph.indistObs
        (rhoDerivedCanonicalSCQuotRelOn carrier) I p q) :
    rhoDerivedCanonicalSCQuotRelOn carrier p q ∧
    Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
      (rhoDerivedCanonicalSCQuotRelOn carrier) I p q := by
  refine ⟨rhoDerivedCanonicalSCQuotRelOn_of_derived_step carrier hp hq hstep, ?_⟩
  exact (hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn I carrier p q).1 hobs

attribute
  [deprecated rhoCoreCanonicalSCQuotRelOn (since := "2026-03-04")]
  rhoCoreCanonicalRelOn

attribute
  [deprecated rhoDerivedCanonicalSCQuotRelOn (since := "2026-03-04")]
  rhoDerivedCanonicalRelOn

attribute
  [deprecated imageFinite_rhoCoreCanonicalSCQuotRelOn (since := "2026-03-04")]
  imageFinite_rhoCoreCanonicalRelOn

attribute
  [deprecated predFinite_rhoCoreCanonicalSCQuotRelOn (since := "2026-03-04")]
  predFinite_rhoCoreCanonicalRelOn

attribute
  [deprecated imageFinite_rhoDerivedCanonicalSCQuotRelOn (since := "2026-03-04")]
  imageFinite_rhoDerivedCanonicalRelOn

attribute
  [deprecated predFinite_rhoDerivedCanonicalSCQuotRelOn (since := "2026-03-04")]
  predFinite_rhoDerivedCanonicalRelOn

attribute
  [deprecated hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn (since := "2026-03-04")]
  hm_iff_fullBisim_rhoCoreCanonicalRelOn

attribute
  [deprecated hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn (since := "2026-03-04")]
  hm_iff_fullBisim_rhoDerivedCanonicalRelOn

attribute
  [deprecated hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn_pair_canary (since := "2026-03-04")]
  hm_iff_fullBisim_rhoCoreCanonicalRelOn_pair_canary

attribute
  [deprecated hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn_pair_canary (since := "2026-03-04")]
  hm_iff_fullBisim_rhoDerivedCanonicalRelOn_pair_canary

/-- Predecessor-domain pair for two endpoints under the same relation. -/
abbrev PredDomainPair
    (R : Pattern → Pattern → Prop) (src tgt : Pattern) (p : Pattern) : Prop :=
  R p src ∨ R p tgt

/-- Backward-closure of predecessor-domain pairs under transitive relations. -/
theorem predDomainPair_backward_closed
    {R : Pattern → Pattern → Prop}
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    {src tgt p q : Pattern}
    (hpair : PredDomainPair R src tgt p)
    (hqp : R q p) :
    PredDomainPair R src tgt q := by
  cases hpair with
  | inl hpsrc => exact Or.inl (htrans hqp hpsrc)
  | inr hptgt => exact Or.inr (htrans hqp hptgt)

/-- Endpoint dia/box fragment semantics at a target state from a predecessor-domain
atom contract. Atoms are required only on predecessors of the target state. -/
theorem sem_of_endpointDiaBoxFragment_at_predDomain
    {R : Pattern → Pattern → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    (hrefl : ∀ p, R p p)
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (p0 : Pattern)
    (hAtomPred : ∀ a p, R p p0 → I a p) :
    Mettapedia.OSLF.Formula.sem R I φ p0 := by
  exact sem_of_endpointDiaBoxFragment_on_domain
    (R := R)
    (D := fun p => R p p0)
    hfrag
    (fun a p hp => hAtomPred a p hp)
    (fun {_p _q} hp hqp => htrans hqp hp)
    (fun p hp => ⟨p, hrefl p, hp⟩)
    p0
    (hrefl p0)

/-- Reachable-state semantic preservation on the encoded/fresh domain:
for any state reachable from an encoded source, predecessor-domain atom
assumptions at that state are sufficient to recover fragment semantics there,
together with source-side fresh backward-outcome evidence. -/
theorem CalcPreludeDomainIndexedSemanticMorphism.transfer_reachable_state_predDomain
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    {src p : Pattern}
    (hreachDom : EncodedFreshReachableDomain N src p)
    (hAtomPred : ∀ a q, rhoDerivedStarRel q p → I a q) :
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ p := by
  rcases hreachDom with ⟨hsrc, hreach⟩
  refine ⟨hend.star_fresh_outcome hsrc hreach, ?_⟩
  exact sem_of_endpointDiaBoxFragment_at_predDomain
    (R := rhoDerivedStarRel) (I := I) (φ := φ)
    hfrag rhoDerivedStarRel_refl
    (fun {a b c} hab hbc => rhoDerivedStarRel_trans hab hbc)
    p
    hAtomPred

/-- A richer OSLF reachability fragment used to lift beyond the base `◇⊤`
claim while staying fully generic over the underlying relation. -/
abbrev RichReachabilitySem
    (R : Pattern → Pattern → Prop) (p : Pattern) : Prop :=
  Mettapedia.OSLF.Formula.sem R (fun _ _ => True) (.and (.dia .top) .top) p
  ∧ Mettapedia.OSLF.Formula.sem R (fun _ _ => True) (.or (.dia .top) .bot) p
  ∧ Mettapedia.OSLF.Formula.sem R (fun _ _ => True) (.imp .top (.dia .top)) p
  ∧ Mettapedia.OSLF.Formula.sem R (fun _ _ => True) (.box .top) p

/-- Generic lift from `◇⊤` to a richer modal fragment built from
`∧, ∨, →, □` over the same relation. -/
theorem rich_reachabilitySem_of_sem_diaTop
    {R : Pattern → Pattern → Prop} {p : Pattern}
    (hDia :
      Mettapedia.OSLF.Formula.sem R (fun _ _ => True) (.dia .top) p) :
    RichReachabilitySem R p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨hDia, trivial⟩
  · exact Or.inl hDia
  · intro _hTop
    exact hDia
  · intro _q _hrel
    trivial

/-- `◇⊤` over derived-star always holds (via reflexivity). -/
theorem sem_diaTop_derivedStar_refl {I : Mettapedia.OSLF.Formula.AtomSem} (p : Pattern) :
    Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I
      (.dia .top) p := by
  exact ⟨p,
    ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar.refl p⟩,
    trivial⟩

/-- Domain-indexed one-step formula preservation over `EncodedFreshDomain`:
the endpoint returns a fresh backward outcome and witnesses `◇⊤` over the
derived one-step relation at the source. -/
theorem encodedFreshDomain_sem_diaTop_of_one_step
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hstep :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt)) :
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧
    Mettapedia.OSLF.Formula.sem rhoDerivedStepRel (fun _ _ => True)
      (.dia .top) src := by
  refine ⟨hend.one_step_fresh_outcome hsrc hstep, ?_⟩
  exact ⟨tgt, hstep, trivial⟩

/-- Domain-indexed star-level formula preservation over `EncodedFreshDomain`:
the endpoint returns a fresh backward outcome and witnesses `◇⊤` over the
derived-star relation at the source. -/
theorem encodedFreshDomain_sem_diaTop_of_star
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hstep :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt)) :
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧
    Mettapedia.OSLF.Formula.sem rhoDerivedStarRel (fun _ _ => True)
      (.dia .top) src := by
  refine ⟨hend.star_fresh_outcome hsrc hstep, ?_⟩
  exact ⟨tgt, hstep, trivial⟩

/-- Reusable morphism-style RF semantic transfer:
from the endpoint's RF forward clause, derive `◇⊤` for encoded RF sources over
core ρ-star reachability. -/
theorem CalcPreludeDomainIndexedSemanticMorphism.transfer_rf_sem_diaTop_star
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel (fun _ _ => True)
      (.dia .top) (encode P0 n v) := by
  rcases hend.forward_rf hstep hrf hsafe n v with ⟨T, hstar, _hbisim⟩
  exact ⟨T, hstar, trivial⟩

/-- Parameterized-atom version of RF `◇⊤` transfer through the canonical endpoint. -/
theorem CalcPreludeDomainIndexedSemanticMorphism.transfer_rf_sem_diaTop_star_paramAtom
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel I
      (.dia .top) (encode P0 n v) := by
  rcases hend.forward_rf hstep hrf hsafe n v with ⟨T, hstar, _hbisim⟩
  exact ⟨T, hstar, trivial⟩

/-- LanguageMorphism-style RF semantic transfer on the richer fragment. -/
theorem CalcPreludeDomainIndexedSemanticMorphism.transfer_rf_rich_fragment_star
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) :
    RichReachabilitySem rhoCoreStarRel (encode P0 n v) := by
  exact rich_reachabilitySem_of_sem_diaTop
    (hend.transfer_rf_sem_diaTop_star hstep hrf hsafe)

/-- Parameterized-atom star-domain transfer over the endpoint dia/box fragment:
from an encoded/fresh source and a derived-star witness, obtain the fresh
backward outcome and fragment semantics at both source and reached target. -/
theorem CalcPreludeDomainIndexedSemanticMorphism.transfer_domain_star_reachable_fragment_paramAtom_reachableAtoms
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    {src tgt : Pattern}
    (hAtomReach :
      ∀ a p,
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src p) →
        I a p)
    (hDomainBackward :
      ∀ {p q : Pattern},
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src p) →
        rhoDerivedStarRel q p →
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src q))
    (hsrc : EncodedFreshDomain N src)
    (hreach :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt)) :
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt := by
  have hOut : ∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds :=
    hend.star_fresh_outcome hsrc hreach
  have hSrcReach :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src src) :=
    ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar.refl src⟩
  have hSrcSem :
      Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src :=
    sem_of_endpointDiaBoxFragment_on_domain
      (R := rhoDerivedStarRel)
      (D := fun p =>
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src p))
      hfrag
      hAtomReach
      hDomainBackward
      (fun p hp => ⟨p, rhoDerivedStarRel_refl p, hp⟩)
      src
      hSrcReach
  have hTgtSem :
      Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt :=
    sem_of_endpointDiaBoxFragment_on_domain
      (R := rhoDerivedStarRel)
      (D := fun p =>
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src p))
      hfrag
      hAtomReach
      hDomainBackward
      (fun p hp => ⟨p, rhoDerivedStarRel_refl p, hp⟩)
      tgt
      hreach
  exact ⟨hOut, hSrcSem, hTgtSem⟩

/-- Stronger reachable-domain transfer contract: a single predecessor-domain
atom assumption over both endpoints (`src` and `tgt`) is sufficient to prove
fragment semantics at both states. -/
theorem CalcPreludeDomainIndexedSemanticMorphism.transfer_domain_star_reachable_fragment_paramAtom_predDomainPair
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hreach :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt))
    (hAtomPredPair : ∀ a p, PredDomainPair rhoDerivedStarRel src tgt p → I a p) :
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt := by
  have hOut : ∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds :=
    hend.star_fresh_outcome hsrc hreach
  let D : Pattern → Prop := PredDomainPair rhoDerivedStarRel src tgt
  have hDomainBackward :
      ∀ {p q : Pattern}, D p → rhoDerivedStarRel q p → D q := by
    intro p q hp hqp
    exact predDomainPair_backward_closed
      (R := rhoDerivedStarRel) (src := src) (tgt := tgt) (p := p) (q := q)
      (htrans := fun {a b c} hab hbc => rhoDerivedStarRel_trans hab hbc)
      (hpair := hp) (hqp := hqp)
  have hDiaDomain : ∀ p, D p → ∃ q, rhoDerivedStarRel p q ∧ D q := by
    intro p hp
    exact ⟨p, rhoDerivedStarRel_refl p, hp⟩
  have hSrcSem :
      Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src :=
    sem_of_endpointDiaBoxFragment_on_domain
      (R := rhoDerivedStarRel) (D := D) hfrag
      (hAtomDomain := hAtomPredPair)
      (hDomainBackward := hDomainBackward)
      (hDiaDomain := hDiaDomain)
      src
      (Or.inl (rhoDerivedStarRel_refl src))
  have hTgtSem :
      Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt :=
    sem_of_endpointDiaBoxFragment_on_domain
      (R := rhoDerivedStarRel) (D := D) hfrag
      (hAtomDomain := hAtomPredPair)
      (hDomainBackward := hDomainBackward)
      (hDiaDomain := hDiaDomain)
      tgt
      (Or.inr (rhoDerivedStarRel_refl tgt))
  exact ⟨hOut, hSrcSem, hTgtSem⟩

/-- Reusable morphism-style domain transfer for one-step encoded/fresh sources:
returns both fresh backward outcome data and `◇⊤` over the derived one-step
relation. -/
theorem CalcPreludeDomainIndexedSemanticMorphism.transfer_domain_oneStep_sem_diaTop
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hstep :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived src tgt)) :
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧
    Mettapedia.OSLF.Formula.sem rhoDerivedStepRel (fun _ _ => True)
      (.dia .top) src :=
  encodedFreshDomain_sem_diaTop_of_one_step hend hsrc hstep

/-- Reusable morphism-style domain transfer for star encoded/fresh sources:
returns both fresh backward outcome data and `◇⊤` over the derived-star
relation. -/
theorem CalcPreludeDomainIndexedSemanticMorphism.transfer_domain_star_sem_diaTop
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hstep :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt)) :
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧
    Mettapedia.OSLF.Formula.sem rhoDerivedStarRel (fun _ _ => True)
      (.dia .top) src :=
  encodedFreshDomain_sem_diaTop_of_star hend hsrc hstep

/-- Domain-preservation package over reachable encoded states: claims extend
from an `EncodedFreshDomain` source to any target reached by derived-star.
This yields both source-side fresh outcomes and rich-fragment semantics on
both source and reached target. -/
theorem CalcPreludeDomainIndexedSemanticMorphism.transfer_domain_star_reachable_rich
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hreach :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt)) :
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧ RichReachabilitySem rhoDerivedStarRel src
    ∧ RichReachabilitySem rhoDerivedStarRel tgt := by
  have hOutAndDia :
      (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
      ∧
      Mettapedia.OSLF.Formula.sem rhoDerivedStarRel (fun _ _ => True) (.dia .top) src :=
    hend.transfer_domain_star_sem_diaTop hsrc hreach
  refine ⟨hOutAndDia.1, ?_, ?_⟩
  · exact rich_reachabilitySem_of_sem_diaTop hOutAndDia.2
  · exact rich_reachabilitySem_of_sem_diaTop (sem_diaTop_derivedStar_refl tgt)

/-- LanguageMorphism-level semantic transfer wrapper derived directly from the
canonical endpoint. -/
structure CalcPreludeLanguageMorphismSemanticTransfer
    (N : Finset String)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) : Prop where
  preserves_diamond_rf :
    ∀ {P0 P1 : Process},
      (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) →
      Mettapedia.OSLF.Formula.sem rhoCoreStarRel (fun _ _ => True)
        (.dia .top) (encode P0 n v)
  preserves_rich_rf :
    ∀ {P0 P1 : Process},
      (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
      (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
      (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) →
      RichReachabilitySem rhoCoreStarRel (encode P0 n v)
  preserves_domain_reachable_rich :
    ∀ {src tgt : Pattern},
      EncodedFreshDomain N src →
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
      ∧ RichReachabilitySem rhoDerivedStarRel src
      ∧ RichReachabilitySem rhoDerivedStarRel tgt

/-- Build the LanguageMorphism-level semantic transfer wrapper from the
canonical domain-indexed endpoint. -/
theorem calcPreludeDomainIndexedSemanticMorphism_to_langMorphismSemanticTransfer
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh) :
    CalcPreludeLanguageMorphismSemanticTransfer
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  refine
    { preserves_diamond_rf := ?_
      preserves_rich_rf := ?_
      preserves_domain_reachable_rich := ?_ }
  · intro P0 P1 hstep hrf hsafe
    exact hend.transfer_rf_sem_diaTop_star hstep hrf hsafe
  · intro P0 P1 hstep hrf hsafe
    exact hend.transfer_rf_rich_fragment_star hstep hrf hsafe
  · intro src tgt hsrc hreach
    exact hend.transfer_domain_star_reachable_rich hsrc hreach

/-- Canonical parameterized-atom theorem family for downstream OSLF/Framework
consumers: RF dia/box-fragment semantics plus reachable-domain fragment
preservation, both exposed from the endpoint only. -/
theorem calculus_canonical_paramAtom_fragment_predDomain_claim_of_endpoint
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh) :
    (∀ (I : Mettapedia.OSLF.Formula.AtomSem) {φ : Mettapedia.OSLF.Formula.OSLFFormula},
      (hfrag : EndpointDiaBoxFragment φ) →
      ∀ {P0 P1 : Process},
        (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
        (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
        (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) →
        (hAtomPred : ∀ a p, rhoCoreStarRel p (encode P0 n v) → I a p) →
        Mettapedia.OSLF.Formula.sem rhoCoreStarRel I φ (encode P0 n v))
    ∧
    (∀ (I : Mettapedia.OSLF.Formula.AtomSem) {φ : Mettapedia.OSLF.Formula.OSLFFormula},
      (hfrag : EndpointDiaBoxFragment φ) →
      ∀ {src tgt : Pattern},
        EncodedFreshDomain N src →
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
        (hAtomPredSrc : ∀ a p, rhoDerivedStarRel p src → I a p) →
        (hAtomPredTgt : ∀ a p, rhoDerivedStarRel p tgt → I a p) →
        (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
        ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src
        ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt) := by
  refine ⟨?_, ?_⟩
  · intro I φ hfrag P0 P1 hstep hrf hsafe hAtomPred
    exact sem_of_endpointDiaBoxFragment_at_predDomain
      (R := rhoCoreStarRel) (I := I) (φ := φ)
      hfrag
      rhoCoreStarRel_refl
      (fun {a b c} hab hbc => rhoCoreStarRel_trans hab hbc)
      (encode P0 n v)
      hAtomPred
  · intro I φ hfrag src tgt hsrc hreach hAtomPredSrc hAtomPredTgt
    have hOut : ∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds :=
      hend.star_fresh_outcome hsrc hreach
    have hSrcSem :
        Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src :=
      sem_of_endpointDiaBoxFragment_at_predDomain
        (R := rhoDerivedStarRel) (I := I) (φ := φ)
        hfrag
        rhoDerivedStarRel_refl
        (fun {a b c} hab hbc => rhoDerivedStarRel_trans hab hbc)
        src
        hAtomPredSrc
    have hTgtSem :
        Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt :=
      sem_of_endpointDiaBoxFragment_at_predDomain
        (R := rhoDerivedStarRel) (I := I) (φ := φ)
        hfrag
        rhoDerivedStarRel_refl
        (fun {a b c} hab hbc => rhoDerivedStarRel_trans hab hbc)
        tgt
        hAtomPredTgt
    exact ⟨hOut, hSrcSem, hTgtSem⟩

/-- LanguageMorphism-style parameterized-atom transfer where atom assumptions
are required only on predecessor domains of the evaluated states. -/
structure CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
    (N : Finset String)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) : Prop where
  preserves_fragment_rf_param_predDomain :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem) {φ : Mettapedia.OSLF.Formula.OSLFFormula},
      (hfrag : EndpointDiaBoxFragment φ) →
      ∀ {P0 P1 : Process},
        (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1) →
        (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0) →
        (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) →
        (hAtomPred : ∀ a p, rhoCoreStarRel p (encode P0 n v) → I a p) →
        Mettapedia.OSLF.Formula.sem rhoCoreStarRel I φ (encode P0 n v)
  preserves_domain_reachable_fragment_param_predDomain :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem) {φ : Mettapedia.OSLF.Formula.OSLFFormula},
      (hfrag : EndpointDiaBoxFragment φ) →
      ∀ {src tgt : Pattern},
        EncodedFreshDomain N src →
        Nonempty
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
        (hAtomPredSrc : ∀ a p, rhoDerivedStarRel p src → I a p) →
        (hAtomPredTgt : ∀ a p, rhoDerivedStarRel p tgt → I a p) →
        (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
        ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src
        ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt

/-- Build the predecessor-domain LanguageMorphism-style parameterized-atom
transfer wrapper from the canonical domain-indexed endpoint. -/
theorem calcPreludeDomainIndexedSemanticMorphism_to_langMorphismSemanticTransferParamAtomPredDomain
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hend : CalcPreludeDomainIndexedSemanticMorphism
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh) :
    CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  rcases calculus_canonical_paramAtom_fragment_predDomain_claim_of_endpoint hend with
    ⟨hRFPred, hDomPred⟩
  refine
    { preserves_fragment_rf_param_predDomain := ?_
      preserves_domain_reachable_fragment_param_predDomain := ?_ }
  · intro I φ hfrag P0 P1 hstep hrf hsafe hAtomPred
    exact hRFPred I hfrag hstep hrf hsafe hAtomPred
  · intro I φ hfrag src tgt hsrc hreach hAtomPredSrc hAtomPredTgt
    exact hDomPred I hfrag hsrc hreach hAtomPredSrc hAtomPredTgt

/-- Generic framework-level transfer bundle consumed from the predecessor-domain
wrapper: one RF fragment judgment plus one derived-star reachable-domain
fragment judgment in a single theorem. -/
theorem CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain.transfer_fragment_bundle
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hwrap : CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep)
    (hAtomPredRF : ∀ a p, rhoCoreStarRel p (encode P0 n v) → I a p)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hreach :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt))
    (hAtomPredSrc : ∀ a p, rhoDerivedStarRel p src → I a p)
    (hAtomPredTgt : ∀ a p, rhoDerivedStarRel p tgt → I a p) :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel I φ (encode P0 n v)
    ∧
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt := by
  refine ⟨?_, ?_⟩
  · exact hwrap.preserves_fragment_rf_param_predDomain I hfrag hstep hrf hsafe hAtomPredRF
  · exact hwrap.preserves_domain_reachable_fragment_param_predDomain
      I hfrag hsrc hreach hAtomPredSrc hAtomPredTgt

/-- Generic bundle variant using a single predecessor-domain atom assumption
over both endpoint states (`src`, `tgt`). -/
theorem CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain.transfer_fragment_bundle_predDomainPair
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hwrap : CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep)
    (hAtomPredRF : ∀ a p, rhoCoreStarRel p (encode P0 n v) → I a p)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hreach :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt))
    (hAtomPredPair : ∀ a p, PredDomainPair rhoDerivedStarRel src tgt p → I a p) :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel I φ (encode P0 n v)
    ∧
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt := by
  exact hwrap.transfer_fragment_bundle
    I hfrag hstep hrf hsafe hAtomPredRF
    hsrc hreach
    (fun a p hp => hAtomPredPair a p (Or.inl hp))
    (fun a p hp => hAtomPredPair a p (Or.inr hp))

/-- Atom-preserving variant of the pred-domain bundle:
semantic conclusions are produced under a target atom interpretation `J`,
using local predecessor-domain atom equivalence from a source interpretation `I`.
This keeps nontrivial atoms as first-class assumptions (no global `hAtomAll`). -/
theorem CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain.transfer_fragment_bundle_predDomainPair_atomIff
    {N : Finset String}
    {x : Name} {P : Process}
    {nuListenerBody seedListenerBody : Pattern}
    {xr yr : Name} {Pr : Process} {n v : String}
    {hfresh : EncodingFresh P}
    (hwrap : CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh)
    (I J : Mettapedia.OSLF.Formula.AtomSem)
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep)
    (hAtomPredRFI : ∀ a p, rhoCoreStarRel p (encode P0 n v) → I a p)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hreach :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt))
    (hAtomPredPairI : ∀ a p, PredDomainPair rhoDerivedStarRel src tgt p → I a p)
    (hAtomPredRFIff :
      ∀ a p, rhoCoreStarRel p (encode P0 n v) → (I a p ↔ J a p))
    (hAtomPredPairIff :
      ∀ a p, PredDomainPair rhoDerivedStarRel src tgt p → (I a p ↔ J a p)) :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel J φ (encode P0 n v)
    ∧
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel J φ src
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel J φ tgt := by
  have hBundleI :
      Mettapedia.OSLF.Formula.sem rhoCoreStarRel I φ (encode P0 n v)
      ∧
      (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
      ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src
      ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt :=
    hwrap.transfer_fragment_bundle_predDomainPair
      I hfrag hstep hrf hsafe hAtomPredRFI
      hsrc hreach hAtomPredPairI
  have hPredRFJ : ∀ a p, rhoCoreStarRel p (encode P0 n v) → J a p := by
    intro a p hp
    exact (hAtomPredRFIff a p hp).1 (hAtomPredRFI a p hp)
  have hPredSrcJ : ∀ a p, rhoDerivedStarRel p src → J a p := by
    intro a p hp
    exact (hAtomPredPairIff a p (Or.inl hp)).1 (hAtomPredPairI a p (Or.inl hp))
  have hPredTgtJ : ∀ a p, rhoDerivedStarRel p tgt → J a p := by
    intro a p hp
    exact (hAtomPredPairIff a p (Or.inr hp)).1 (hAtomPredPairI a p (Or.inr hp))
  refine ⟨?_, hBundleI.2.1, ?_, ?_⟩
  · exact sem_of_endpointDiaBoxFragment_at_predDomain
      (R := rhoCoreStarRel) (I := J) (φ := φ)
      hfrag
      rhoCoreStarRel_refl
      (fun {a b c} hab hbc => rhoCoreStarRel_trans hab hbc)
      (encode P0 n v)
      hPredRFJ
  · exact sem_of_endpointDiaBoxFragment_at_predDomain
      (R := rhoDerivedStarRel) (I := J) (φ := φ)
      hfrag
      rhoDerivedStarRel_refl
      (fun {a b c} hab hbc => rhoDerivedStarRel_trans hab hbc)
      src
      hPredSrcJ
  · exact sem_of_endpointDiaBoxFragment_at_predDomain
      (R := rhoDerivedStarRel) (I := J) (φ := φ)
      hfrag
      rhoDerivedStarRel_refl
      (fun {a b c} hab hbc => rhoDerivedStarRel_trans hab hbc)
      tgt
      hPredTgtJ

/-! ## End-to-End OSLF Formula Consumption

Consume the canonical package through the bridge and derive OSLF semantic facts.
-/

/-- End-to-end theorem consuming the canonical package through the OSLF bridge:
from RF forward correspondence, derive an OSLF `◇⊤` witness over ρ-star. -/
theorem piRho_canonical_package_end_to_end_sem_diaTop_star
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel (fun _ _ => True)
      (.dia .top) (encode P0 n v) := by
  have hend :
      CalcPreludeDomainIndexedSemanticMorphism N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh :=
    piRho_canonical_domainIndexedSemanticMorphism_end_to_end
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  exact hend.transfer_rf_sem_diaTop_star hstep hrf hsafe

/-- CoreMain-facing canonical endpoint alias for the pred-domain default. -/
theorem piRho_coreMain_predDomain_endpoint
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  have hend :
      CalcPreludeDomainIndexedSemanticMorphism
        N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh :=
    piRho_canonical_domainIndexedSemanticMorphism_end_to_end
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  exact calcPreludeDomainIndexedSemanticMorphism_to_langMorphismSemanticTransferParamAtomPredDomain hend

/-- CoreMain-facing framework transfer endpoint:
consume the canonical pred-domain wrapper directly and produce RF + derived-star
bundle transfer with a single pair-domain atom assumption. -/
theorem piRho_coreMain_predDomain_transfer_bundle_end_to_end
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep)
    (hAtomPredRF : ∀ a p, rhoCoreStarRel p (encode P0 n v) → I a p)
    {src tgt : Pattern}
    (hsrc : EncodedFreshDomain N src)
    (hreach :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt))
    (hAtomPredPair : ∀ a p, PredDomainPair rhoDerivedStarRel src tgt p → I a p) :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel I φ (encode P0 n v)
    ∧
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt := by
  have hwrap :
      CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
        N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh :=
    piRho_coreMain_predDomain_endpoint
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  exact hwrap.transfer_fragment_bundle_predDomainPair
    I hfrag hstep hrf hsafe hAtomPredRF
    hsrc hreach hAtomPredPair

/-- CoreMain-facing reachable-state endpoint over the encoded/fresh domain:
consume predecessor-domain atom assumptions at a reachable state and obtain
that state's fragment semantics plus source-side fresh-outcome evidence. -/
theorem piRho_coreMain_predDomain_reachable_state_end_to_end
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {φ : Mettapedia.OSLF.Formula.OSLFFormula}
    (hfrag : EndpointDiaBoxFragment φ)
    {src p : Pattern}
    (hreachDom : EncodedFreshReachableDomain N src p)
    (hAtomPred : ∀ a q, rhoDerivedStarRel q p → I a q) :
    (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
    ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ p := by
  have hend :
      CalcPreludeDomainIndexedSemanticMorphism
        N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh :=
    piRho_canonical_domainIndexedSemanticMorphism_end_to_end
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  exact hend.transfer_reachable_state_predDomain I hfrag hreachDom hAtomPred

/-- Canonical CoreMain-facing π→ρ semantic contract:
pred-domain default endpoint, bundled RF+derived-star transfer, reachable-state
transfer, and HM-ready converse wrappers on the chosen canonical relations. -/
structure PiRhoCoreMainCanonicalContract
    (N : Finset String)
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) : Type where
  endpoint :
    CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  transfer_bundle_predDomainPair :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem) {φ : Mettapedia.OSLF.Formula.OSLFFormula},
      (hfrag : EndpointDiaBoxFragment φ) →
      ∀ {P0 P1 : Process}
        (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
        (_hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
        (_hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep)
        (_hAtomPredRF : ∀ a p, rhoCoreStarRel p (encode P0 n v) → I a p) {src tgt : Pattern}
        (_hsrc : EncodedFreshDomain N src)
        (_hreach :
          Nonempty
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt))
        (_hAtomPredPair : ∀ a p, PredDomainPair rhoDerivedStarRel src tgt p → I a p),
        Mettapedia.OSLF.Formula.sem rhoCoreStarRel I φ (encode P0 n v)
        ∧
        (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
        ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ src
        ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ tgt
  reachable_state_predDomain :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem) {φ : Mettapedia.OSLF.Formula.OSLFFormula},
      (hfrag : EndpointDiaBoxFragment φ) →
      ∀ {src p : Pattern}
        (_hreachDom : EncodedFreshReachableDomain N src p)
        (_hAtomPred : ∀ a q, rhoDerivedStarRel q p → I a q),
        (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
        ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ p
  reachable_state_predDomain_closed :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem) {φ : Mettapedia.OSLF.Formula.OSLFFormula},
      (hfrag : EndpointDiaBoxFragment φ) →
      ∀ {src p q : Pattern}
        (_hreachDom : EncodedFreshReachableDomain N src p)
        (_hpq : rhoDerivedStarRel p q)
        (_hAtomPred : ∀ a r, rhoDerivedStarRel r q → I a r),
        (∃ seeds, BackwardAdminReflection.WeakBackwardOutcomeFreshAt N src seeds)
        ∧ Mettapedia.OSLF.Formula.sem rhoDerivedStarRel I φ q
  reachable_coreStar_subrel :
    Pattern → FiniteSubrelation rhoCoreStarRel
  reachable_derivedStar_subrel :
    Pattern → FiniteSubrelation rhoDerivedStarRel
  hm_converse_coreStar_subrel :
    ∀ (S : FiniteSubrelation rhoCoreStarRel) (I : Mettapedia.OSLF.Formula.AtomSem)
      {p q : Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq S.rel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar S.rel p q
  hm_converse_derivedStar_subrel :
    ∀ (S : FiniteSubrelation rhoDerivedStarRel) (I : Mettapedia.OSLF.Formula.AtomSem)
      {p q : Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq S.rel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar S.rel p q
  hm_converse_coreCanonical :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem) {p q : Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq rhoCoreCanonicalRel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar rhoCoreCanonicalRel p q
  hm_converse_derivedCanonical :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem) {p q : Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq rhoDerivedCanonicalRel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar rhoDerivedCanonicalRel p q

/-- End-to-end construction of the canonical CoreMain-facing π→ρ semantic
contract. -/
def piRho_coreMain_canonical_contract_end_to_end
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    PiRhoCoreMainCanonicalContract
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh := by
  refine
    { endpoint := piRho_coreMain_predDomain_endpoint
        (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
      transfer_bundle_predDomainPair := ?_
      reachable_state_predDomain := ?_
      reachable_state_predDomain_closed := ?_
      reachable_coreStar_subrel := ?_
      reachable_derivedStar_subrel := ?_
      hm_converse_coreStar_subrel := ?_
      hm_converse_derivedStar_subrel := ?_
      hm_converse_coreCanonical := ?_
      hm_converse_derivedCanonical := ?_ }
  · intro I φ hfrag P0 P1 hstep hrf hsafe hAtomPredRF src tgt hsrc hreach hAtomPredPair
    exact piRho_coreMain_predDomain_transfer_bundle_end_to_end
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
      I hfrag hstep hrf hsafe hAtomPredRF hsrc hreach hAtomPredPair
  · intro I φ hfrag src p hreachDom hAtomPred
    exact piRho_coreMain_predDomain_reachable_state_end_to_end
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
      I hfrag hreachDom hAtomPred
  · intro I φ hfrag src p q hreachDom hpq hAtomPred
    exact piRho_coreMain_predDomain_reachable_state_end_to_end
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
      I hfrag
      (encodedFreshReachableDomain_closed hreachDom hpq)
      hAtomPred
  · intro root
    exact reachableCoreStarFiniteSubrelation root
  · intro root
    exact reachableDerivedStarFiniteSubrelation root
  · intro S I p q hobsEq
    exact hm_converse_of_finiteSubrelation (S := S) I hobsEq
  · intro S I p q hobsEq
    exact hm_converse_of_finiteSubrelation (S := S) I hobsEq
  · intro I p q hobsEq
    exact hm_converse_rhoCoreCanonicalRel I hobsEq
  · intro I p q hobsEq
    exact hm_converse_rhoDerivedCanonicalRel I hobsEq

/-- Concrete nontrivial RF canary using predecessor-domain atoms (not
`hAtomAll`): atoms are indexed by predecessor reachability to the encoded
source state. -/
theorem predDomain_rf_fragment_canary_nontrivial :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel
      (fun _ p => rhoCoreStarRel p (encode .nil "n_init" "v_init"))
      (.box (.atom "rf_pred"))
      (encode .nil "n_init" "v_init") := by
  have hobsNil : ((∅ : Finset String) ⊆ Process.freeNames .nil) := by
    intro a ha
    simp at ha
  have hwrap :
      CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
        (∅ : Finset String)
        "x" .nil rhoNil rhoNil "ns_x" "_drop" .nil "n_init" "v_init"
        Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil :=
    piRho_coreMain_predDomain_endpoint
      (N := (∅ : Finset String))
      "x" .nil rhoNil rhoNil "ns_x" "_drop" .nil "n_init" "v_init"
      hobsNil
      Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil
  have hrf :
      Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree .nil := by
    simp [Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree]
  have hsafeRefl :
      Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe
        (Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF.refl .nil) := by
    simp [Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe]
  exact hwrap.preserves_fragment_rf_param_predDomain
    (I := fun _ p => rhoCoreStarRel p (encode .nil "n_init" "v_init"))
    (φ := .box (.atom "rf_pred"))
    (hfrag := EndpointDiaBoxFragment.box (EndpointDiaBoxFragment.atom "rf_pred"))
    (hstep := Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF.refl .nil)
    (hrf := hrf) (hsafe := hsafeRefl)
    (hAtomPred := fun _ p hp => hp)

/-- Stronger RF canary using predecessor-domain atoms with an actual non-refl
COMM RF trace. -/
theorem predDomain_rf_fragment_canary_nontrivial_progress :
    Mettapedia.OSLF.Formula.sem rhoCoreStarRel
      (fun _ p =>
        rhoCoreStarRel p
          (encode
            (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
            "n_init" "v_init"))
      (.box (.atom "rf_pred_prog"))
      (encode
        (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
        "n_init" "v_init") := by
  let Psrc : Process := Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w")
  have hobsNil : ((∅ : Finset String) ⊆ Process.freeNames .nil) := by
    intro a ha
    simp at ha
  have hwrap :
      CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
        (∅ : Finset String)
        "x" .nil rhoNil rhoNil "ns_x" "_drop" .nil "n_init" "v_init"
        Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil :=
    piRho_coreMain_predDomain_endpoint
      (N := (∅ : Finset String))
      "x" .nil rhoNil rhoNil "ns_x" "_drop" .nil "n_init" "v_init"
      hobsNil
      Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil
  have hrf :
      Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree Psrc := by
    simp [Psrc,
      Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree]
  refine hwrap.preserves_fragment_rf_param_predDomain
    (I := fun _ p => rhoCoreStarRel p (encode Psrc "n_init" "v_init"))
    (φ := .box (.atom "rf_pred_prog"))
    (hfrag := EndpointDiaBoxFragment.box (EndpointDiaBoxFragment.atom "rf_pred_prog"))
    (P0 := Psrc) (P1 := .nil)
    (hstep := ?_)
    (hrf := hrf) (hsafe := ?_)
    (hAtomPred := fun _ p hp => hp)
  · simpa [Psrc] using
      (Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF.step
        (Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.ReducesRF.comm
          "alpha" "u" "w" .nil)
        (Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF.refl .nil))
  · refine ⟨?_, trivial⟩
    exact ⟨by decide,
      by simp [Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.BarendregtFor]⟩

/-- Concrete nontrivial derived-star canary using predecessor-domain atoms (not
`hAtomAll`): atoms are indexed by predecessor reachability to the encoded
replication source. -/
theorem predDomain_derivedStar_fragment_canary_nontrivial :
    ∃ seeds,
      BackwardAdminReflection.WeakBackwardOutcomeFreshAt (∅ : Finset String)
        (encode (.replicate "rx" "ry" .nil) "n_src" "v_src") seeds
      ∧
      Mettapedia.OSLF.Formula.sem rhoDerivedStarRel
        (fun _ p =>
          rhoDerivedStarRel p (encode (.replicate "rx" "ry" .nil) "n_src" "v_src"))
        (.box (.atom "ds_pred"))
        (encode (.replicate "rx" "ry" .nil) "n_src" "v_src") := by
  let src : Pattern := encode (.replicate "rx" "ry" .nil) "n_src" "v_src"
  have hobsNil : ((∅ : Finset String) ⊆ Process.freeNames .nil) := by
    intro a ha
    simp at ha
  have hwrap :
      CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
        (∅ : Finset String)
        "x" .nil rhoNil rhoNil "ns_x" "_drop" .nil "n_init" "v_init"
        Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil :=
    piRho_coreMain_predDomain_endpoint
      (N := (∅ : Finset String))
      "x" .nil rhoNil rhoNil "ns_x" "_drop" .nil "n_init" "v_init"
      hobsNil
      Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil
  have hsrc :
      EncodedFreshDomain (∅ : Finset String) src := by
    exact BackwardAdminReflection.EncodedSCStepSourceFresh.admin
      (BackwardAdminReflection.AdminSourceFresh.replicate
        "rx" "ry" .nil "n_src" "v_src"
        (by intro a ha; simp at ha)
        (Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFreshAt_nil "n_src" "v_src"))
  have hreach :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src src) :=
    ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar.refl src⟩
  have hdomain :=
    hwrap.preserves_domain_reachable_fragment_param_predDomain
      (I := fun _ p => rhoDerivedStarRel p src)
      (φ := .box (.atom "ds_pred"))
      (hfrag := EndpointDiaBoxFragment.box (EndpointDiaBoxFragment.atom "ds_pred"))
      (src := src) (tgt := src)
      hsrc hreach
      (fun _ p hp => hp)
      (fun _ p hp => hp)
  rcases hdomain with ⟨hout, hsemSrc, _hsemTgt⟩
  rcases hout with ⟨seeds, hout⟩
  exact ⟨seeds, by simpa [src] using hout, by simpa [src] using hsemSrc⟩

/-- Stronger derived-star canary using predecessor-domain atoms with an actual
non-refl derived-star witness from encoded replication unfolding. -/
theorem predDomain_derivedStar_fragment_canary_nontrivial_progress :
    ∃ (tgt : Pattern) (seeds : Finset Name),
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
          (encode (.replicate "rx" "ry" .nil) "n_src" "v_src") tgt)
      ∧ BackwardAdminReflection.WeakBackwardOutcomeFreshAt (∅ : Finset String)
          (encode (.replicate "rx" "ry" .nil) "n_src" "v_src") seeds
      ∧
      Mettapedia.OSLF.Formula.sem rhoDerivedStarRel
        (fun _ p =>
          PredDomainPair rhoDerivedStarRel
            (encode (.replicate "rx" "ry" .nil) "n_src" "v_src") tgt p)
        (.box (.atom "ds_pred_prog"))
        (encode (.replicate "rx" "ry" .nil) "n_src" "v_src")
      ∧
      Mettapedia.OSLF.Formula.sem rhoDerivedStarRel
        (fun _ p =>
          PredDomainPair rhoDerivedStarRel
            (encode (.replicate "rx" "ry" .nil) "n_src" "v_src") tgt p)
        (.box (.atom "ds_pred_prog")) tgt := by
  let src : Pattern := encode (.replicate "rx" "ry" .nil) "n_src" "v_src"
  have hobsNil : ((∅ : Finset String) ⊆ Process.freeNames .nil) := by
    intro a ha
    simp at ha
  have hwrap :
      CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
        (∅ : Finset String)
        "x" .nil rhoNil rhoNil "ns_x" "_drop" .nil "n_init" "v_init"
        Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil :=
    piRho_coreMain_predDomain_endpoint
      (N := (∅ : Finset String))
      "x" .nil rhoNil rhoNil "ns_x" "_drop" .nil "n_init" "v_init"
      hobsNil
      Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFresh_nil
  have hsrc :
      EncodedFreshDomain (∅ : Finset String) src := by
    exact BackwardAdminReflection.EncodedSCStepSourceFresh.admin
      (BackwardAdminReflection.AdminSourceFresh.replicate
        "rx" "ry" .nil "n_src" "v_src"
        (by intro a ha; simp at ha)
        (Mettapedia.Languages.ProcessCalculi.PiCalculus.encodingFreshAt_nil "n_src" "v_src"))
  rcases EncodingMorphism.forward_single_step_replicate_derived (N := (∅ : Finset String))
      "rx" "ry" .nil "n_src" "v_src" with ⟨tgt, hreach, _hbisim⟩
  have hdomain :=
    hwrap.preserves_domain_reachable_fragment_param_predDomain
      (I := fun _ p => PredDomainPair rhoDerivedStarRel src tgt p)
      (φ := .box (.atom "ds_pred_prog"))
      (hfrag := EndpointDiaBoxFragment.box (EndpointDiaBoxFragment.atom "ds_pred_prog"))
      (src := src) (tgt := tgt)
      hsrc hreach
      (fun _ p hp => Or.inl hp)
      (fun _ p hp => Or.inr hp)
  rcases hdomain with ⟨hout, hsemSrc, hsemTgt⟩
  rcases hout with ⟨seeds, hout⟩
  exact ⟨tgt, seeds, by simpa [src] using hreach, by simpa [src] using hout,
    by simpa [src] using hsemSrc, hsemTgt⟩

/-- Foundation-modal connection for the canonical `◇⊤` claim:
the OSLF endpoint is translated into Foundation Kripke satisfaction via the
existing `OSLFKripkeBridge` forward correspondence. -/
theorem piRho_canonical_sem_diaTop_star_to_foundation
    (enc : Mettapedia.Logic.OSLFKripkeBridge.AtomEncoding)
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) :
    LO.Modal.Formula.Kripke.Satisfies
      (Mettapedia.Logic.OSLFKripkeBridge.oslfForwardModel
        rhoCoreStarRel (fun _ _ => True) enc)
      (encode P0 n v)
      (Mettapedia.Logic.OSLFKripkeBridge.translateForward enc (.dia .top)) := by
  have hSem :
      Mettapedia.OSLF.Formula.sem rhoCoreStarRel (fun _ _ => True)
        (.dia .top) (encode P0 n v) :=
    piRho_canonical_package_end_to_end_sem_diaTop_star
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v
      hobs hfresh hstep hrf hsafe
  have hDiaOnly : Mettapedia.Logic.OSLFKripkeBridge.diaOnly (.dia .top) := by
    simp [Mettapedia.Logic.OSLFKripkeBridge.diaOnly]
  exact
    (Mettapedia.Logic.OSLFKripkeBridge.sem_iff_satisfies_forward
      (enc := enc) (R := rhoCoreStarRel) (I := fun _ _ => True)
      (φ := .dia .top) hDiaOnly (p := encode P0 n v)).mp hSem

/-- Parameterized-atom Foundation-modal connection for the canonical `◇⊤`
claim: same endpoint as above, but for any atom interpretation `I`. -/
theorem piRho_canonical_sem_diaTop_star_to_foundation_paramAtom
    (enc : Mettapedia.Logic.OSLFKripkeBridge.AtomEncoding)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) :
    LO.Modal.Formula.Kripke.Satisfies
      (Mettapedia.Logic.OSLFKripkeBridge.oslfForwardModel
        rhoCoreStarRel I enc)
      (encode P0 n v)
      (Mettapedia.Logic.OSLFKripkeBridge.translateForward enc (.dia .top)) := by
  have hend :
      CalcPreludeDomainIndexedSemanticMorphism
        N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh :=
    piRho_canonical_domainIndexedSemanticMorphism_end_to_end
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  have hSem :
      Mettapedia.OSLF.Formula.sem rhoCoreStarRel I (.dia .top) (encode P0 n v) :=
    hend.transfer_rf_sem_diaTop_star_paramAtom I hstep hrf hsafe
  have hDiaOnly : Mettapedia.Logic.OSLFKripkeBridge.diaOnly (.dia .top) := by
    simp [Mettapedia.Logic.OSLFKripkeBridge.diaOnly]
  exact
    (Mettapedia.Logic.OSLFKripkeBridge.sem_iff_satisfies_forward
      (enc := enc) (R := rhoCoreStarRel) (I := I)
      (φ := .dia .top) hDiaOnly (p := encode P0 n v)).mp hSem

/-! ## Modal μ/ν Bridge

Bridge the OSLF relation view to the modal μ-calculus LTS view and expose a
single end-to-end theorem that includes both μ (`eventually`) and ν (`always`)
formula endpoints on the same encoded ρ state.
-/

/-- Build a modal μ-calculus LTS from any binary relation on patterns. -/
def relationLTS (R : Pattern → Pattern → Prop) :
    Mettapedia.Logic.ModalMuCalculus.LTS Pattern Unit where
  trans := fun p _ q => R p q
  final := Set.univ

/-- OSLF `◇⊤` implies modal μ-calculus `⟨()⟩⊤` on the induced relation LTS. -/
theorem oslf_diaTop_to_modalMu_diamond_tt
    {R : Pattern → Pattern → Prop} {p : Pattern}
    (h : Mettapedia.OSLF.Formula.sem R (fun _ _ => True) (.dia .top) p) :
    Mettapedia.Logic.ModalMuCalculus.satisfies
      (relationLTS R)
      Mettapedia.Logic.ModalMuCalculus.Env.empty
      (Mettapedia.Logic.ModalMuCalculus.Formula.diamond ()
        Mettapedia.Logic.ModalMuCalculus.Formula.tt)
      p := by
  rcases h with ⟨q, hRq, _⟩
  exact ⟨q, hRq, trivial⟩

/-- On any relation-LTS, the μ-formula `eventually ⊤` holds at every state. -/
theorem modalMu_eventually_tt_true
    (R : Pattern → Pattern → Prop) (p : Pattern) :
    Mettapedia.Logic.ModalMuCalculus.satisfies
      (relationLTS R)
      Mettapedia.Logic.ModalMuCalculus.Env.empty
      (Mettapedia.Logic.ModalMuCalculus.Formula.eventually ()
        Mettapedia.Logic.ModalMuCalculus.Formula.tt)
      p := by
  unfold Mettapedia.Logic.ModalMuCalculus.Formula.eventually
  intro X hclosed
  exact hclosed p (Or.inl trivial)

/-- On any relation-LTS, the ν-formula `always ⊤` holds at every state. -/
theorem modalMu_always_tt_true
    (R : Pattern → Pattern → Prop) (p : Pattern) :
    Mettapedia.Logic.ModalMuCalculus.satisfies
      (relationLTS R)
      Mettapedia.Logic.ModalMuCalculus.Env.empty
      (Mettapedia.Logic.ModalMuCalculus.Formula.always ()
        Mettapedia.Logic.ModalMuCalculus.Formula.tt)
      p := by
  unfold Mettapedia.Logic.ModalMuCalculus.Formula.always
  refine ⟨Set.univ, trivial, ?_⟩
  intro t _ht
  constructor
  · trivial
  · intro t' _htrans
    trivial

/-- End-to-end μ/ν bridge theorem consuming the canonical package:
derives modal μ-calculus endpoints (`diamond`, `eventually`, `always`) for
the encoded ρ state from the same canonical package assumptions. -/
theorem piRho_canonical_package_end_to_end_modalMu_bridge
    {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P)
    {P0 P1 : Process}
    (hstep : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiStepRF P0 P1)
    (hrf : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree P0)
    (hsafe : Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.MultiCommSafe hstep) :
    Mettapedia.Logic.ModalMuCalculus.satisfies
      (relationLTS rhoCoreStarRel)
      Mettapedia.Logic.ModalMuCalculus.Env.empty
      (Mettapedia.Logic.ModalMuCalculus.Formula.diamond ()
        Mettapedia.Logic.ModalMuCalculus.Formula.tt)
      (encode P0 n v)
    ∧
    Mettapedia.Logic.ModalMuCalculus.satisfies
      (relationLTS rhoCoreStarRel)
      Mettapedia.Logic.ModalMuCalculus.Env.empty
      (Mettapedia.Logic.ModalMuCalculus.Formula.eventually ()
        Mettapedia.Logic.ModalMuCalculus.Formula.tt)
      (encode P0 n v)
    ∧
    Mettapedia.Logic.ModalMuCalculus.satisfies
      (relationLTS rhoCoreStarRel)
      Mettapedia.Logic.ModalMuCalculus.Env.empty
      (Mettapedia.Logic.ModalMuCalculus.Formula.always ()
        Mettapedia.Logic.ModalMuCalculus.Formula.tt)
      (encode P0 n v) := by
  have hSem :
      Mettapedia.OSLF.Formula.sem rhoCoreStarRel (fun _ _ => True)
        (.dia .top) (encode P0 n v) :=
    piRho_canonical_package_end_to_end_sem_diaTop_star
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v
      hobs hfresh hstep hrf hsafe
  have hDia :
      Mettapedia.Logic.ModalMuCalculus.satisfies
        (relationLTS rhoCoreStarRel)
        Mettapedia.Logic.ModalMuCalculus.Env.empty
        (Mettapedia.Logic.ModalMuCalculus.Formula.diamond ()
          Mettapedia.Logic.ModalMuCalculus.Formula.tt)
        (encode P0 n v) :=
    oslf_diaTop_to_modalMu_diamond_tt (R := rhoCoreStarRel) (p := encode P0 n v) hSem
  have hMu :
      Mettapedia.Logic.ModalMuCalculus.satisfies
        (relationLTS rhoCoreStarRel)
        Mettapedia.Logic.ModalMuCalculus.Env.empty
        (Mettapedia.Logic.ModalMuCalculus.Formula.eventually ()
          Mettapedia.Logic.ModalMuCalculus.Formula.tt)
        (encode P0 n v) :=
    modalMu_eventually_tt_true rhoCoreStarRel (encode P0 n v)
  have hNu :
      Mettapedia.Logic.ModalMuCalculus.satisfies
        (relationLTS rhoCoreStarRel)
        Mettapedia.Logic.ModalMuCalculus.Env.empty
        (Mettapedia.Logic.ModalMuCalculus.Formula.always ()
          Mettapedia.Logic.ModalMuCalculus.Formula.tt)
        (encode P0 n v) :=
    modalMu_always_tt_true rhoCoreStarRel (encode P0 n v)
  exact ⟨hDia, ⟨hMu, hNu⟩⟩

end Mettapedia.OSLF.Framework.PiRhoCanonicalBridge
