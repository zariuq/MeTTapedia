import Mettapedia.OSLF.Framework.WMCalculusRuleShape
import Mettapedia.OSLF.Framework.WMCalculusSideConditionProvider
import Mettapedia.OSLF.Framework.WMCalculusRewriteCompletenessBoundary

/-!
# The rules as they stood were wrong: counterexamples, and a certified run

`ledgerModel` is a world model for every axis of the maximal vertex.  A state is
a ledger of observation identities; the evidence for "`o` was recorded" is its
count, as positive evidence; forgetting a scope deletes its identities;
compatible ledgers share no identity; the trust policy `none` keeps every
identity; the Kripke reading takes the identities as points and satisfaction as
equality.

**Negative controls.**  Each rule below is a WM rule as it stood before this
pass, kept as a control in no rule list.  Each is invalid in the ledger model:
a valuation satisfies its premises, its left side denotes a value, and its right
side denotes a different one or nothing.  The firing controls show the same
defect on the calculus itself.

* singleton refutation with right side `EvidenceZero`, under its premise
  `kripkeNotSat` (`oldSingletonRefutation_invalid`, `oldSingletonRefutation_fires`):
  the law gives `⟨0, 1⟩` (`oldSingletonRefutation_values`);
* the two singleton rules without premises, which both fire on one term and give
  `⟨1, 0⟩` and `⟨0, 0⟩` where the law gives `⟨0, 1⟩`
  (`premiseFreeSingletonSat_invalid`, `premiseFreeSingletonPair_fires`);
* the fallback pair without premises (`premiseFreeFallbackIncompatible_invalid`,
  `premiseFreeFallbackCompatible_invalid`);
* additive fallback evidence and the all-trusting policy without the
  compatibility premise (`premiseFreeSourceEvidenceAdd_invalid`,
  `premiseFreePolicyTrustedAll_invalid`), and partial revision, which gives a
  state where the law leaves the revision undefined
  (`premiseFreePartialRevision_defines_undefined`); all five fire on their left sides
  (`premiseFreeProvenance_fire`);
* the cascade bound under the premise that `Q` is finite, which every finite
  set satisfies: the empty space bounds nothing (`finiteSpaceCascade_invalid`);
* the swap anomaly with right side `EvidenceZero`, an evidence value where the
  anomaly is a cost (`evidenceZeroAnomaly_invalid`);
* query transport without its premise, whose right-side-only metavariable `q2`
  leaks as a free name (`premiseFreeQueryTransport_invalid`,
  `premiseFreeQueryTransport_fires`);
* the two right-side-only shapes fail the well-formedness check, the two-argument
  pullback relation clashes with the three-argument one, and the two-argument
  pullback pattern has no denotation in any model
  (`premiseFree_rightNames_unbound`, `oldBlackwell_arities_clash`,
  `oldPullback_undenoted`).

**A certified run.**  In the maximal calculus with its congruence rules, under
the exact provider, the term `KripkeEvidence(Revise(Singleton(0), Singleton(1)), 0)`
runs in three steps (evidence additivity at the root, then the two singleton
rules under `Combine`) to `Combine(EvidenceOne, EvidenceOneNegative)`.  The
soundness theorem certifies the derived fact that the two-point ledger has
evidence `⟨1, 0⟩ + ⟨0, 1⟩` at the formula `0` (`twoPoint_evidence`).

**Completeness fails in the core.**  The two associations of three observations
denote the same evidence in every lawful reading and have no common reduct
(`semantic_assoc_not_joinable`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusCounterexamples

open scoped ENNReal
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusPatternDenotation
open Mettapedia.OSLF.Framework.WMCalculusDenotationalSoundness
open Mettapedia.OSLF.Framework.WMCalculusSideConditionProvider
open Mettapedia.OSLF.Framework.WMCalculusRuleShape
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric (AdditiveWorldModel)
open Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting (SupportTrackedForgettingLayer)
open Mettapedia.PLN.WorldModel.WorldModelOverlap (OverlapLayer)
open Mettapedia.PLN.WorldModel.GenericWorldModelForgetting (GenericWorldModelZeroPreserving)
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization (crispEvidence crispWorldModel)

/-! ## The ledger model -/

/-- The evidence for "`o` was recorded": its count, as positive evidence. -/
noncomputable def ledgerExtract (ledger : Multiset ℕ) (o : ℕ) : BinaryEvidence :=
  ⟨(ledger.count o : ℝ≥0∞), 0⟩

noncomputable instance ledgerWorld : AdditiveWorldModel (Multiset ℕ) ℕ BinaryEvidence where
  extract := ledgerExtract
  extract_add ledger ledger' o := by
    apply BinaryEvidence.ext' <;> simp [ledgerExtract, BinaryEvidence.hplus_def, Multiset.count_add]

@[simp] theorem extract_ledger (ledger : Multiset ℕ) (o : ℕ) :
    AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := BinaryEvidence) ledger o =
      ledgerExtract ledger o := rfl

/-- Deleting a scope's identities from a ledger. -/
def ledgerForgetting :
    SupportTrackedForgettingLayer (Multiset ℕ) (Finset ℕ) ℕ BinaryEvidence ℕ where
  inScope S o := o ∈ S
  forget S ledger := ledger.filter (· ∉ S)
  idempotent S ledger := by simp [Multiset.filter_filter]
  outsideInvariant := by
    intro S ledger o outside
    show ledgerExtract (ledger.filter (· ∉ S)) o = ledgerExtract ledger o
    rw [ledgerExtract, ledgerExtract, Multiset.count_filter_of_pos (p := fun x => x ∉ S) outside]
  scopeFootprint S := S
  support ledger o := (ledger.filter (· = o)).toFinset
  forget_add S ledger ledger' := Multiset.filter_add _ _ _
  forget_eq_zero_of_supported := by
    intro S Δ supported
    refine Multiset.filter_eq_nil.mpr fun o member outside => outside (supported o ?_)
    simp [member]
  forget_eq_self_of_clean := by
    intro S W clean
    refine Multiset.filter_eq_self.mpr fun o member inside => ?_
    exact Finset.disjoint_left.mp (clean o) (by simp [member]) inside

theorem ledger_zeroPreserving :
    GenericWorldModelZeroPreserving (State := Multiset ℕ) (Query := ℕ) (Ev := BinaryEvidence) :=
  fun o => by
    show (⟨((0 : Multiset ℕ).count o : ℝ≥0∞), 0⟩ : BinaryEvidence) = 0
    rw [Multiset.count_zero, Nat.cast_zero]
    rfl

/-- Ledgers merge additively. -/
noncomputable def ledgerOverlap : OverlapLayer (Multiset ℕ) ℕ BinaryEvidence Unit where
  merge := (· + ·)
  overlap _ _ _ := ()
  combine first second _ := first + second
  independent _ _ _ := True
  evidence_merge first second o := AdditiveWorldModel.extract_add first second o
  additive_of_independent first second o _ := AdditiveWorldModel.extract_add first second o

/-- The identity `0` as the hypothesis `true`, every other identity as `false`. -/
def ledgerHypotheses : Multiset ℕ →+ Multiset Bool where
  toFun ledger := ledger.map fun n => decide (n = 0)
  map_zero' := Multiset.map_zero _
  map_add' first second := Multiset.map_add _ first second

noncomputable def ledgerWeights : Multiset ℕ →+ (Bool → ℝ≥0∞) where
  toFun ledger hypothesis := ((ledgerHypotheses ledger).count hypothesis : ℝ≥0∞)
  map_zero' := by funext hypothesis; simp
  map_add' first second := by funext hypothesis; simp [Multiset.count_add]

/-- The ledger model. -/
noncomputable def ledgerModel : WMModel (Multiset ℕ) ℕ BinaryEvidence where
  Scope := Finset ℕ
  Supp := ℕ
  forgetting := ledgerForgetting
  zeroPreserving := ledger_zeroPreserving
  Ov := Unit
  overlap := ledgerOverlap
  compatible first second := ∀ o ∈ first, o ∉ second
  compatible_symm := fun separate o inSecond inFirst => separate o inFirst inSecond
  Policy := Option (Finset ℕ)
  gate policy ledger := match policy with
    | none => ledger
    | some trusted => ledger.filter (· ∈ trusted)
  trustAll := none
  gate_trustAll _ := rfl
  FQuery := Bool
  fixpointModel := crispWorldModel (fun (_ : ℕ) (b : Bool) => b = true)
  Θ := Bool
  Ω := Bool
  Act := Bool
  fintypeΘ := inferInstance
  fintypeΩ := inferInstance
  fintypeAct := inferInstance
  hypotheses := ledgerHypotheses
  weights := ledgerWeights
  Point := ℕ
  ModalQuery := ℕ
  satisfies point formula := point = formula
  points := AddMonoidHom.id _
  singleton point := {point}
  points_singleton _ := rfl
  ofBinary := AddMonoidHom.id _

/-- Short names for the denotation and the meaning in the ledger model. -/
local notation "𝔇" => denote (algebra ledgerModel)

theorem one_ne_zero_evidence : (⟨1, 0⟩ : BinaryEvidence) ≠ ⟨0, 1⟩ := by
  intro same
  have := congrArg BinaryEvidence.pos same
  simp at this

theorem refutation_ne_zero : (⟨0, 1⟩ : BinaryEvidence) ≠ 0 := by
  intro same
  have := congrArg BinaryEvidence.neg same
  simp [show (0 : BinaryEvidence) = ⟨0, 0⟩ from rfl] at this

/-! ## Singleton refutation -/

/-- Singleton refutation with its old right side. -/
def oldSingletonRefutation : RewriteRule :=
  { ruleKripkeSingletonNotSat with
    name := "WM_KripkeSingletonNotSat_OldRight_Control"
    right := pEvidenceZero }

/-- The rule metavariables read as the point `1` and the formula `0`. -/
def refutingPoint : String → Option (WMValue ledgerModel)
  | "pk" => some (.point (1 : ℕ))
  | "phi" => some (.modalQuery (0 : ℕ))
  | _ => none

theorem refutingPoint_evidence :
    𝔇 refutingPoint (pKripkeEvidence (pSingleton (.fvar "pk")) (.fvar "phi")) =
      some (.evidence ⟨0, 1⟩) := by
  rw [den_kripkeEvidence.mpr ⟨{1}, (0 : ℕ), den_singleton.mpr ⟨(1 : ℕ), rfl, rfl⟩, rfl, rfl⟩]
  congr 2
  exact Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.crispEvidence_singleton_of_not_satisfies
    _ (1 : ℕ) (0 : ℕ)
    (fun h => absurd (show (1 : ℕ) = 0 from h) (by decide))

/-- **The old refutation rule is invalid**: at a refuting point its premise
holds, its left side denotes `⟨0, 1⟩` and its right side `0`. -/
theorem oldSingletonRefutation_invalid :
    ¬ RuleValid (algebra ledgerModel) (meaning ledgerModel) oldSingletonRefutation := by
  intro valid
  have holds : ∀ premise ∈ oldSingletonRefutation.premises,
      PremiseHolds (algebra ledgerModel) (meaning ledgerModel) refutingPoint premise := by
    intro premise member
    simp only [oldSingletonRefutation, ruleKripkeSingletonNotSat, List.mem_singleton] at member
    subst member
    refine ⟨[.point (1 : ℕ), .modalQuery (0 : ℕ)], rfl, ?_⟩
    rw [meaning_of_parse ledgerModel (by decide : WMRelation.parse "kripkeNotSat" = some .kripkeNotSat)]
    exact ⟨(1 : ℕ), (0 : ℕ), rfl, rfl, fun h => absurd (show (1 : ℕ) = 0 from h) (by decide)⟩
  have right := valid refutingPoint holds _ refutingPoint_evidence
  rw [show oldSingletonRefutation.right = pEvidenceZero from rfl, den_evidenceZero] at right
  exact refutation_ne_zero (WMValue.evidence.inj (Option.some.inj right)).symm

/-! ## The singleton pair without premises -/

def premiseFreeSingletonSat : RewriteRule :=
  { ruleKripkeSingletonSat with name := "WM_KripkeSingletonSat_PremiseFree_Control", premises := [] }

def premiseFreeSingletonNotSat : RewriteRule :=
  { oldSingletonRefutation with
    name := "WM_KripkeSingletonNotSat_PremiseFree_Control", premises := [] }

/-- Without its premise, singleton satisfaction gives `⟨1, 0⟩` at a refuting
point. -/
theorem premiseFreeSingletonSat_invalid :
    ¬ RuleValid (algebra ledgerModel) (meaning ledgerModel) premiseFreeSingletonSat := by
  intro valid
  have right := valid refutingPoint (by simp [premiseFreeSingletonSat]) _ refutingPoint_evidence
  rw [show premiseFreeSingletonSat.right = pEvidenceOne from rfl, den_evidenceOne] at right
  exact one_ne_zero_evidence (WMValue.evidence.inj (Option.some.inj right))

/-- The maximal calculus with the two premise-free singleton rules added. -/
def withPremiseFreeSingletons : LanguageDef :=
  { wmFullVertexLanguageDef wmFullVertexMaximal with
    rewrites := premiseFreeSingletonSat :: premiseFreeSingletonNotSat ::
      (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites }

def pointOne : Pattern := .fvar "p1"
def formulaZero : Pattern := .fvar "f0"

/-- A premise-free rule fires at the root on a term its left side matches. -/
theorem premiseFree_fires {env : RelationEnv} {lang : LanguageDef} {rule : RewriteRule}
    (member : rule ∈ lang.rewrites) (premisesNil : rule.premises = [])
    {source target : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern rule.left source)
    (aligned : ruleDepthAligned rule = true)
    (applied : applyBindings bindings rule.right = target) :
    langReducesUsing env lang source target := by
  unfold langReducesUsing
  refine step_of_rule (initialBindings := bindings) (finalBindings := bindings) member
    (by rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
        exact matched)
    (by rw [premisesNil]; exact .nil) (by rw [premisesNil]; simp [applyPremisesWithEnv]) ?_
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_applyBindings _ _ _
    aligned]
  exact applied

/-- **Both premise-free singleton rules fire on one term**, giving `EvidenceOne`
and `EvidenceZero`. -/
theorem premiseFreeSingletonPair_fires :
    langReducesUsing RelationEnv.empty withPremiseFreeSingletons
        (pKripkeEvidence (pSingleton pointOne) formulaZero) pEvidenceOne ∧
      langReducesUsing RelationEnv.empty withPremiseFreeSingletons
        (pKripkeEvidence (pSingleton pointOne) formulaZero) pEvidenceZero := by
  constructor
  · refine premiseFree_fires (rule := premiseFreeSingletonSat)
      (bindings := [("phi", formulaZero), ("pk", pointOne)])
      (by simp [withPremiseFreeSingletons]) rfl ?_ (by decide +kernel)
      (by simp [premiseFreeSingletonSat, ruleKripkeSingletonSat, pEvidenceOne, applyBindings])
    simp [premiseFreeSingletonSat, ruleKripkeSingletonSat, pKripkeEvidence, pSingleton,
      pointOne, formulaZero, matchPattern, matchArgs, mergeBindings]
  · refine premiseFree_fires (rule := premiseFreeSingletonNotSat)
      (bindings := [("phi", formulaZero), ("pk", pointOne)])
      (by simp [withPremiseFreeSingletons]) rfl ?_ (by decide +kernel)
      (by simp [premiseFreeSingletonNotSat, oldSingletonRefutation, pEvidenceZero, applyBindings])
    simp [premiseFreeSingletonNotSat, oldSingletonRefutation, ruleKripkeSingletonNotSat,
      pKripkeEvidence, pSingleton, pointOne, formulaZero, matchPattern, matchArgs, mergeBindings]

/-! ## Provenance without the compatibility premise -/

def premiseFreeFallbackCompatible : RewriteRule :=
  { ruleFallbackCompatible with name := "WM_FallbackCompatible_PremiseFree_Control", premises := [] }

def premiseFreeFallbackIncompatible : RewriteRule :=
  { ruleFallbackIncompatible with
    name := "WM_FallbackIncompatible_PremiseFree_Control", premises := [] }

def premiseFreeSourceEvidenceAdd : RewriteRule :=
  { ruleSourceEvidenceAdd with name := "WM_SourceEvidenceAdd_PremiseFree_Control", premises := [] }

def premiseFreePolicyTrustedAll : RewriteRule :=
  { rulePolicyTrustedAllCompatible with
    name := "WM_PolicyTrustedAllCompatible_PremiseFree_Control", premises := [] }

def premiseFreePartialRevision : RewriteRule :=
  { rulePartialRevisionCompatible with
    name := "WM_PartialRevisionCompatible_PremiseFree_Control", premises := [] }

/-- `W1 = {0}`, `W2 = {1}`: compatible ledgers. -/
def separateLedgers : String → Option (WMValue ledgerModel)
  | "W1" => some (.state {0})
  | "W2" => some (.state {1})
  | "q" => some (.query 0)
  | _ => none

/-- `W1 = W2 = {0}`: ledgers that share the identity `0`. -/
def sharedLedgers : String → Option (WMValue ledgerModel)
  | "W1" => some (.state {0})
  | "W2" => some (.state {0})
  | "q" => some (.query 0)
  | _ => none

theorem separate_compatible : ledgerModel.compatible {0} {1} := by
  show ∀ o ∈ ({0} : Multiset ℕ), o ∉ ({1} : Multiset ℕ)
  intro o member
  simp only [Multiset.mem_singleton] at member
  subst member
  simp

theorem shared_incompatible : ¬ ledgerModel.compatible {0} {0} := by
  intro separate
  exact separate 0 (by simp) (by simp)

/-- Without its premise, the incompatible fallback keeps only the left ledger of
two compatible ledgers, where the law adds them. -/
theorem premiseFreeFallbackIncompatible_invalid :
    ¬ RuleValid (algebra ledgerModel) (meaning ledgerModel) premiseFreeFallbackIncompatible := by
  intro valid
  have left : 𝔇 separateLedgers premiseFreeFallbackIncompatible.left =
      some (.state (ledgerModel.fallbackRevision {0} {1})) :=
    den_fallbackRevision.mpr ⟨{0}, {1}, rfl, rfl, rfl⟩
  have right := valid separateLedgers (by simp [premiseFreeFallbackIncompatible]) _ left
  rw [ledgerModel.fallbackRevision_of_compatible separate_compatible] at right
  have values : ({0} : Multiset ℕ) = {0} + {1} :=
    WMValue.state.inj (Option.some.inj right)
  exact absurd (congrArg Multiset.card values) (by simp)

/-- Without its premise, the compatible fallback adds two ledgers that share an
identity, where the law keeps the left one. -/
theorem premiseFreeFallbackCompatible_invalid :
    ¬ RuleValid (algebra ledgerModel) (meaning ledgerModel) premiseFreeFallbackCompatible := by
  intro valid
  have left : 𝔇 sharedLedgers premiseFreeFallbackCompatible.left =
      some (.state (ledgerModel.fallbackRevision {0} {0})) :=
    den_fallbackRevision.mpr ⟨{0}, {0}, rfl, rfl, rfl⟩
  have right := valid sharedLedgers (by simp [premiseFreeFallbackCompatible]) _ left
  rw [ledgerModel.fallbackRevision_of_not_compatible shared_incompatible] at right
  obtain ⟨x, y, hx, hy, same⟩ := den_revise.mp right
  obtain rfl : ({0} : Multiset ℕ) = x := WMValue.state.inj (Option.some.inj hx)
  obtain rfl : ({0} : Multiset ℕ) = y := WMValue.state.inj (Option.some.inj hy)
  have values : ({0} : Multiset ℕ) = {0} + {0} := WMValue.state.inj same
  exact absurd (congrArg Multiset.card values) (by simp)

/-- Without its premise, additive fallback evidence counts a shared identity
twice: the law gives `⟨1, 0⟩`, the rule `⟨2, 0⟩`. -/
theorem premiseFreeSourceEvidenceAdd_invalid :
    ¬ RuleValid (algebra ledgerModel) (meaning ledgerModel) premiseFreeSourceEvidenceAdd := by
  intro valid
  have left : 𝔇 sharedLedgers premiseFreeSourceEvidenceAdd.left =
      some (.evidence (ledgerExtract (ledgerModel.fallbackRevision {0} {0}) 0)) :=
    den_extract.mpr ⟨_, 0, den_fallbackRevision.mpr ⟨{0}, {0}, rfl, rfl, rfl⟩, rfl, rfl⟩
  have right := valid sharedLedgers (by simp [premiseFreeSourceEvidenceAdd]) _ left
  rw [ledgerModel.fallbackRevision_of_not_compatible shared_incompatible] at right
  obtain ⟨a, b, ha, hb, same⟩ := den_combine.mp right
  obtain ⟨x, z, hx, hz, ⟨⟩⟩ := den_extract.mp ha
  obtain ⟨x', z', hx', hz', ⟨⟩⟩ := den_extract.mp hb
  obtain rfl : ({0} : Multiset ℕ) = x := WMValue.state.inj (Option.some.inj hx)
  obtain rfl : ({0} : Multiset ℕ) = x' := WMValue.state.inj (Option.some.inj hx')
  obtain rfl : (0 : ℕ) = z := WMValue.query.inj (Option.some.inj hz)
  obtain rfl : (0 : ℕ) = z' := WMValue.query.inj (Option.some.inj hz')
  have values := congrArg BinaryEvidence.pos (WMValue.evidence.inj same)
  have doubled : (1 : ℝ≥0∞) = 1 + 1 := by
    simpa [ledgerExtract, BinaryEvidence.hplus_def] using values
  norm_num at doubled

/-- Without its premise, the all-trusting policy adds two ledgers that share an
identity, where the law keeps the left one. -/
theorem premiseFreePolicyTrustedAll_invalid :
    ¬ RuleValid (algebra ledgerModel) (meaning ledgerModel) premiseFreePolicyTrustedAll := by
  intro valid
  have left : 𝔇 sharedLedgers premiseFreePolicyTrustedAll.left =
      some (.state (ledgerModel.gate ledgerModel.trustAll
        (ledgerModel.fallbackRevision {0} {0}))) :=
    den_policyRevisedState.mpr ⟨_, {0}, {0}, den_trustedAll, rfl, rfl, rfl⟩
  have right := valid sharedLedgers (by simp [premiseFreePolicyTrustedAll]) _ left
  rw [ledgerModel.gate_trustAll, ledgerModel.fallbackRevision_of_not_compatible shared_incompatible]
    at right
  obtain ⟨x, y, hx, hy, same⟩ := den_revise.mp right
  obtain rfl : ({0} : Multiset ℕ) = x := WMValue.state.inj (Option.some.inj hx)
  obtain rfl : ({0} : Multiset ℕ) = y := WMValue.state.inj (Option.some.inj hy)
  have values : ({0} : Multiset ℕ) = {0} + {0} := WMValue.state.inj same
  exact absurd (congrArg Multiset.card values) (by simp)

/-- Without its premise, partial revision rewrites the revision of two ledgers
that share an identity, which the law leaves undefined, to a defined state. -/
theorem premiseFreePartialRevision_defines_undefined :
    𝔇 sharedLedgers premiseFreePartialRevision.left = none ∧
      𝔇 sharedLedgers premiseFreePartialRevision.right = some (.state ({0} + {0})) := by
  constructor
  · cases defined : 𝔇 sharedLedgers premiseFreePartialRevision.left with
    | none => rfl
    | some v =>
        obtain ⟨x, y, z, hx, hy, revised, _⟩ := den_partialRevision.mp defined
        obtain rfl : ({0} : Multiset ℕ) = x := WMValue.state.inj (Option.some.inj hx)
        obtain rfl : ({0} : Multiset ℕ) = y := WMValue.state.inj (Option.some.inj hy)
        have undefined : ledgerModel.partialRevision {0} {0} = none := by
          classical
          simp [WMModel.partialRevision, shared_incompatible]
        rw [undefined] at revised
        cases revised
  · exact den_revise.mpr ⟨{0}, {0}, rfl, rfl, rfl⟩

/-- The maximal calculus with the five premise-free provenance rules added. -/
def withPremiseFreeProvenance : LanguageDef :=
  { wmFullVertexLanguageDef wmFullVertexMaximal with
    rewrites := premiseFreeFallbackCompatible :: premiseFreeFallbackIncompatible ::
      premiseFreeSourceEvidenceAdd :: premiseFreePolicyTrustedAll :: premiseFreePartialRevision ::
      (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites }

/-- **The premise-free provenance rules fire** on their own left sides, read as
terms over handles named like their metavariables; `separateLedgers` and
`sharedLedgers` read those handles, and there the two sides differ as above. -/
theorem premiseFreeProvenance_fire :
    langReducesUsing RelationEnv.empty withPremiseFreeProvenance
        premiseFreeFallbackIncompatible.left premiseFreeFallbackIncompatible.right ∧
      langReducesUsing RelationEnv.empty withPremiseFreeProvenance
        premiseFreeFallbackCompatible.left premiseFreeFallbackCompatible.right ∧
      langReducesUsing RelationEnv.empty withPremiseFreeProvenance
        premiseFreeSourceEvidenceAdd.left premiseFreeSourceEvidenceAdd.right ∧
      langReducesUsing RelationEnv.empty withPremiseFreeProvenance
        premiseFreePolicyTrustedAll.left premiseFreePolicyTrustedAll.right ∧
      langReducesUsing RelationEnv.empty withPremiseFreeProvenance
        premiseFreePartialRevision.left premiseFreePartialRevision.right := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine premiseFree_fires (rule := premiseFreeFallbackIncompatible)
      (bindings := [("W2", .fvar "W2"), ("W1", .fvar "W1")])
      (by simp [withPremiseFreeProvenance]) rfl ?_ (by decide +kernel) ?_
    · simp [premiseFreeFallbackIncompatible, ruleFallbackIncompatible, pFallbackRevision,
        matchPattern, matchArgs, mergeBindings]
    · simp [premiseFreeFallbackIncompatible, ruleFallbackIncompatible, applyBindings]
  · refine premiseFree_fires (rule := premiseFreeFallbackCompatible)
      (bindings := [("W2", .fvar "W2"), ("W1", .fvar "W1")])
      (by simp [withPremiseFreeProvenance]) rfl ?_ (by decide +kernel) ?_
    · simp [premiseFreeFallbackCompatible, ruleFallbackCompatible, pFallbackRevision,
        matchPattern, matchArgs, mergeBindings]
    · simp [premiseFreeFallbackCompatible, ruleFallbackCompatible, pRevise, applyBindings]
  · refine premiseFree_fires (rule := premiseFreeSourceEvidenceAdd)
      (bindings := [("q", .fvar "q"), ("W2", .fvar "W2"), ("W1", .fvar "W1")])
      (by simp [withPremiseFreeProvenance]) rfl ?_ (by decide +kernel) ?_
    · simp [premiseFreeSourceEvidenceAdd, ruleSourceEvidenceAdd, pExtract, pFallbackRevision,
        matchPattern, matchArgs, mergeBindings]
    · simp [premiseFreeSourceEvidenceAdd, ruleSourceEvidenceAdd, pCombine, pExtract,
        applyBindings]
  · refine premiseFree_fires (rule := premiseFreePolicyTrustedAll)
      (bindings := [("W1", .fvar "W1"), ("W2", .fvar "W2")])
      (by simp [withPremiseFreeProvenance]) rfl ?_ (by decide +kernel) ?_
    · simp [premiseFreePolicyTrustedAll, rulePolicyTrustedAllCompatible, pPolicyRevisedState,
        pTrustedAll, matchPattern, matchArgs, mergeBindings]
    · simp [premiseFreePolicyTrustedAll, rulePolicyTrustedAllCompatible, pRevise, applyBindings]
  · refine premiseFree_fires (rule := premiseFreePartialRevision)
      (bindings := [("W2", .fvar "W2"), ("W1", .fvar "W1")])
      (by simp [withPremiseFreeProvenance]) rfl ?_ (by decide +kernel) ?_
    · simp [premiseFreePartialRevision, rulePartialRevisionCompatible, pPartialRevision,
        matchPattern, matchArgs, mergeBindings]
    · simp [premiseFreePartialRevision, rulePartialRevisionCompatible, pRevise, applyBindings]

/-! ## The cascade bound -/

/-- `false` yields `true` at the empty ledger. -/
noncomputable def falseYieldsTrue :
    WMConsequenceRuleOn (Multiset ℕ) ledgerModel.FQuery where
  side ledger := ledger = 0
  premise := false
  conclusion := true
  sound := by
    intro ledger empty
    subst empty
    show (crispEvidence (fun (_ : ℕ) (b : Bool) => b = true) 0 false).toStrength ≤
      (crispEvidence (fun (_ : ℕ) (b : Bool) => b = true) 0 true).toStrength
    rw [Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.crispEvidence_zero,
      Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.crispEvidence_zero]

/-- The cascade rule under the premise that `Q` is finite. -/
def finiteSpaceCascade : RewriteRule :=
  { ruleCascadeAtCard with
    name := "WM_CascadeAtCard_FiniteSpace_Control"
    premises := [.relationQuery "finiteSpace" [.fvar "Q"]] }

/-- Every query space of the ledger model is finite, so `finiteSpace` holds of
each of them. -/
def finiteSpaceMeaning : RelationMeaning (WMValue ledgerModel) := fun relation values =>
  if relation = "finiteSpace" then ∃ Q, values = [.querySpace Q] else meaning ledgerModel relation values

/-- `R = {false ↦ true}`, `W = 0`, `seed = {false}`, `Q = ∅`. -/
noncomputable def emptySpace : String → Option (WMValue ledgerModel)
  | "R" => some (.ruleSet {falseYieldsTrue})
  | "W" => some (.state 0)
  | "seed" => some (.querySet {false})
  | "Q" => some (.querySpace ∅)
  | _ => none

/-- **The finite-space premise is too weak**: the empty space is finite, the
iteration bounded by its cardinality stops at the seed, and the closure reaches
`true`. -/
theorem finiteSpaceCascade_invalid :
    ¬ RuleValid (algebra ledgerModel) finiteSpaceMeaning finiteSpaceCascade := by
  intro valid
  have holds : ∀ premise ∈ finiteSpaceCascade.premises,
      PremiseHolds (algebra ledgerModel) finiteSpaceMeaning emptySpace premise := by
    intro premise member
    simp only [finiteSpaceCascade, List.mem_singleton] at member
    subst member
    exact ⟨[.querySpace ∅], rfl, by simp [finiteSpaceMeaning]⟩
  have left : 𝔇 emptySpace finiteSpaceCascade.left =
      some (.querySet (Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.immediateIter
        (State := Multiset ℕ) (Query := ledgerModel.FQuery) {falseYieldsTrue} 0 {false} 0)) :=
    den_immediateIter.mpr ⟨_, 0, {false}, 0, rfl, rfl, rfl, den_card.mpr ⟨∅, rfl, rfl⟩, rfl⟩
  have right := valid emptySpace holds _ left
  obtain ⟨R, x, seed, hR, hx, hseed, same⟩ := den_leastClosure.mp right
  obtain rfl : ({falseYieldsTrue} : Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      (Multiset ℕ) ledgerModel.FQuery) = R := WMValue.ruleSet.inj (Option.some.inj hR)
  obtain rfl : (0 : Multiset ℕ) = x := WMValue.state.inj (Option.some.inj hx)
  obtain rfl : ({false} : Set ledgerModel.FQuery) = seed := WMValue.querySet.inj (Option.some.inj hseed)
  have sets := WMValue.querySet.inj same
  have reached : true ∈ Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
      (State := Multiset ℕ) (Query := ledgerModel.FQuery) {falseYieldsTrue} 0 {false} :=
    Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.immediateIter_subset_leastRuleClosure
      (State := Multiset ℕ) (Query := ledgerModel.FQuery) {falseYieldsTrue} 0 {false} 1
      (Or.inr ⟨falseYieldsTrue, rfl, rfl, rfl, rfl⟩)
  rw [← sets] at reached
  exact absurd reached (by
    show true ∉ ({false} : Set Bool)
    simp)

/-! ## The swap anomaly is a cost -/

def evidenceZeroAnomaly : RewriteRule :=
  { ruleSwapAnomalyZero with name := "WM_SwapAnomalyZero_EvidenceZero_Control", right := pEvidenceZero }

/-- With right side `EvidenceZero`, a vanishing swap anomaly becomes evidence:
the anomaly is the cost `0`, the right side the evidence `0`. -/
theorem evidenceZeroAnomaly_invalid :
    ¬ RuleValid (algebra ledgerModel) (meaning ledgerModel) evidenceZeroAnomaly := by
  intro valid
  have counts : AdditiveWorldModel.queryObservationCount (State := Multiset ℕ) (Query := ℕ)
      (Ev := BinaryEvidence) (ledgerModel.overlap.merge {0} {1}) 0 =
    AdditiveWorldModel.queryObservationCount (State := Multiset ℕ) (Query := ℕ)
      (Ev := BinaryEvidence) (ledgerModel.overlap.merge {1} {0}) 0 := by
    show AdditiveWorldModel.queryObservationCount (State := Multiset ℕ) (Query := ℕ)
      (Ev := BinaryEvidence) ({0} + {1}) 0 =
        AdditiveWorldModel.queryObservationCount (State := Multiset ℕ) (Query := ℕ)
          (Ev := BinaryEvidence) ({1} + {0}) 0
    rw [add_comm ({0} : Multiset ℕ) {1}]
  have holds : ∀ premise ∈ evidenceZeroAnomaly.premises,
      PremiseHolds (algebra ledgerModel) (meaning ledgerModel) separateLedgers premise := by
    intro premise member
    simp only [evidenceZeroAnomaly, ruleSwapAnomalyZero, List.mem_singleton] at member
    subst member
    refine ⟨[.state {0}, .state {1}, .query 0], rfl, ?_⟩
    rw [meaning_of_parse ledgerModel (by decide : WMRelation.parse "equalCounts" = some .equalCounts)]
    exact ⟨{0}, {1}, 0, rfl, rfl, rfl, counts⟩
  have left : 𝔇 separateLedgers evidenceZeroAnomaly.left =
      some (.cost (Mettapedia.PLN.WorldModel.OrderCost.SwapAnomalyCount (State := Multiset ℕ)
        (Query := ℕ) (Ev := BinaryEvidence) ledgerModel.overlap {0} {1} 0)) :=
    den_swapAnomaly.mpr ⟨{0}, {1}, 0, rfl, rfl, rfl, rfl⟩
  have right := valid separateLedgers holds _ left
  rw [show evidenceZeroAnomaly.right = pEvidenceZero from rfl, den_evidenceZero] at right
  cases right

/-! ## Query transport and its right-side-only metavariable -/

def premiseFreeQueryTransport : RewriteRule :=
  { ruleQueryEquivTransport with name := "WM_QueryEquivTransport_PremiseFree_Control", premises := [] }

/-- `W = {0}`, `q1 = 0`, and a name `q2` that happens to denote the query `1`. -/
def leakedName : String → Option (WMValue ledgerModel)
  | "W" => some (.state {0})
  | "q1" => some (.query 0)
  | "q2" => some (.query 1)
  | _ => none

/-- Without its premise, query transport reads whatever `q2` names: here the
evidence at `0` is `⟨1, 0⟩` and at `1` it is `⟨0, 0⟩`. -/
theorem premiseFreeQueryTransport_invalid :
    ¬ RuleValid (algebra ledgerModel) (meaning ledgerModel) premiseFreeQueryTransport := by
  intro valid
  have left : 𝔇 leakedName premiseFreeQueryTransport.left =
      some (.evidence (ledgerExtract {0} 0)) := den_genericEvidence.mpr ⟨{0}, 0, rfl, rfl, rfl⟩
  have right := valid leakedName (by simp [premiseFreeQueryTransport]) _ left
  obtain ⟨x, z, hx, hz, same⟩ := den_genericEvidence.mp right
  obtain rfl : ({0} : Multiset ℕ) = x := WMValue.state.inj (Option.some.inj hx)
  obtain rfl : (1 : ℕ) = z := WMValue.query.inj (Option.some.inj hz)
  have values := congrArg BinaryEvidence.pos (WMValue.evidence.inj same)
  simp [ledgerExtract] at values

/-- The maximal calculus with premise-free query transport added. -/
def withPremiseFreeQueryTransport : LanguageDef :=
  { wmFullVertexLanguageDef wmFullVertexMaximal with
    rewrites := premiseFreeQueryTransport :: (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites }

/-- **It fires and leaks the metavariable** `q2` into the reduct as a free name. -/
theorem premiseFreeQueryTransport_fires :
    langReducesUsing RelationEnv.empty withPremiseFreeQueryTransport
      (pGenericEvidence (.fvar "s0") (.fvar "q0")) (pGenericEvidence (.fvar "s0") (.fvar "q2")) := by
  refine premiseFree_fires (rule := premiseFreeQueryTransport)
    (bindings := [("q1", .fvar "q0"), ("W", .fvar "s0")])
    (by simp [withPremiseFreeQueryTransport]) rfl ?_ (by decide +kernel) ?_
  · simp [premiseFreeQueryTransport, ruleQueryEquivTransport, pGenericEvidence, matchPattern,
      matchArgs, mergeBindings]
  · simp [premiseFreeQueryTransport, ruleQueryEquivTransport, pGenericEvidence, applyBindings]

/-! ## Shapes -/

def premiseFreeUtilityTransport : RewriteRule :=
  { ruleBlackwellUtilityTransport with
    name := "WM_BlackwellUtilityTransport_PremiseFree_Control", premises := [] }

/-- The old pullback: no strong channel, and a two-argument relation. -/
def oldPullback : RewriteRule :=
  { ruleBlackwellPullback with
    name := "WM_BlackwellPullback_TwoArgument_Control"
    typeContext := [("W", .base "State"), ("k", .base "Channel"), ("q", .base "Query")]
    premises := [.relationQuery "blackwellFactors" [.fvar "k", .fvar "q"]]
    left := pExperimentEvidence (.fvar "W") (.apply "BlackwellPullback" [.fvar "k", .fvar "q"]) }

/-- Both right-side-only shapes fail the well-formedness check. -/
theorem premiseFree_rightNames_unbound :
    rightNamesBound premiseFreeQueryTransport = false ∧
      rightNamesBound premiseFreeUtilityTransport = false := by
  decide +kernel

/-- The old pullback relation clashes with the utility relation's arity. -/
theorem oldBlackwell_arities_clash :
    aritiesUnique (relationCalls [oldPullback, ruleBlackwellUtilityTransport]) = false := by
  decide +kernel

/-- A pullback that names no strong channel denotes nothing, in every model. -/
theorem oldPullback_undenoted {State Query Ev : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore.ConjugateEvidence Ev]
    [AdditiveWorldModel State Query Ev] (M : WMModel State Query Ev)
    (ν : String → Option (WMValue M)) (k q : Pattern) :
    denote (algebra M) ν (.apply "BlackwellPullback" [k, q]) = none := by
  rw [denote_apply_two, algebra_op_of_parse M
    (by decide : WMLabel.parse "BlackwellPullback" = some .blackwellPullback)]
  cases denote (algebra M) ν k <;> cases denote (algebra M) ν q <;> rfl

/-! ## A certified run -/

def pointZero : Pattern := .fvar "p0"

/-- The handle table of the run: two points and a formula. -/
def ledgerHandles : String → Option (WMValue ledgerModel)
  | "p0" => some (.point (0 : ℕ))
  | "p1" => some (.point (1 : ℕ))
  | "f0" => some (.modalQuery (0 : ℕ))
  | _ => none

/-- The exact provider over the run's handles. -/
noncomputable abbrev ledgerProvider : CheckedRelationProvider ledgerModel :=
  exactProvider ledgerModel [pointZero, pointOne, formulaZero] ledgerHandles

abbrev maximalWithCong : LanguageDef := wmFullVertexLanguageDefWithCong wmFullVertexMaximal

theorem kripkeSat_row :
    [pointZero, formulaZero] ∈
      (providerEnv ledgerProvider).tuples "kripkeSat" [pointZero, formulaZero] := by
  have candidates : [pointZero, formulaZero].map ledgerProvider.candidates =
      [[pointZero], [formulaZero]] := rfl
  refine (exactProvider_rows _ _ (by decide : WMRelation.parse "kripkeSat" = some .kripkeSat)
    (by rw [candidates]; exact List.mem_singleton.mpr rfl)).mpr ?_
  exact ⟨[.point (0 : ℕ), .modalQuery (0 : ℕ)], rfl, (0 : ℕ), (0 : ℕ), rfl, rfl, rfl⟩

theorem kripkeNotSat_row :
    [pointOne, formulaZero] ∈
      (providerEnv ledgerProvider).tuples "kripkeNotSat" [pointOne, formulaZero] := by
  have candidates : [pointOne, formulaZero].map ledgerProvider.candidates =
      [[pointOne], [formulaZero]] := rfl
  refine (exactProvider_rows _ _
    (by decide : WMRelation.parse "kripkeNotSat" = some .kripkeNotSat)
    (by rw [candidates]; exact List.mem_singleton.mpr rfl)).mpr ?_
  exact ⟨[.point (1 : ℕ), .modalQuery (0 : ℕ)], rfl, (1 : ℕ), (0 : ℕ), rfl, rfl,
    fun h => absurd (show (1 : ℕ) = 0 from h) (by decide)⟩

theorem kripkeSat_step {env : RelationEnv} (pk phi : Pattern)
    (row : [pk, phi] ∈ env.tuples "kripkeSat" [pk, phi]) :
    langReducesUsing env maximalWithCong (pKripkeEvidence (pSingleton pk) phi) pEvidenceOne := by
  unfold langReducesUsing
  let bs : Bindings := [("phi", phi), ("pk", pk)]
  have member : ruleKripkeSingletonSat ∈ maximalWithCong.rewrites :=
    rules_subset_congRules_full _ _ (by rw [maximalRules_eq]; simp [maximalRuleList])
  refine step_of_rule (initialBindings := bs) (finalBindings := bs) member ?_
    (.relationQuery .nil) ?_ ?_
  · simp [bs, ruleKripkeSingletonSat, pKripkeEvidence, pSingleton, matchPattern, matchArgs,
      mergeBindings]
  · simp [bs, ruleKripkeSingletonSat, applyPremisesWithEnv, premiseStepWithEnv,
      relationQueryStep, builtinRelationTuples, applyBindings, mergeBindings]
    exact ⟨_, row, by
      simp [matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings]⟩
  · simp [Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings, bs, ruleKripkeSingletonSat,
      pEvidenceOne]

theorem kripkeNotSat_step {env : RelationEnv} (pk phi : Pattern)
    (row : [pk, phi] ∈ env.tuples "kripkeNotSat" [pk, phi]) :
    langReducesUsing env maximalWithCong (pKripkeEvidence (pSingleton pk) phi)
      pEvidenceOneNegative := by
  unfold langReducesUsing
  let bs : Bindings := [("phi", phi), ("pk", pk)]
  have member : ruleKripkeSingletonNotSat ∈ maximalWithCong.rewrites :=
    rules_subset_congRules_full _ _ (by rw [maximalRules_eq]; simp [maximalRuleList])
  refine step_of_rule (initialBindings := bs) (finalBindings := bs) member ?_
    (.relationQuery .nil) ?_ ?_
  · simp [bs, ruleKripkeSingletonNotSat, pKripkeEvidence, pSingleton, matchPattern, matchArgs,
      mergeBindings]
  · simp [bs, ruleKripkeSingletonNotSat, applyPremisesWithEnv, premiseStepWithEnv,
      relationQueryStep, builtinRelationTuples, applyBindings, mergeBindings]
    exact ⟨_, row, by
      simp [matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings]⟩
  · simp [Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings, bs, ruleKripkeSingletonNotSat,
      pEvidenceOneNegative]

theorem combineCongLeft_step {env : RelationEnv} {e1 e1' e2 : Pattern}
    (inner : langReducesUsing env maximalWithCong e1 e1') :
    langReducesUsing env maximalWithCong (pCombine e1 e2) (pCombine e1' e2) := by
  unfold langReducesUsing at inner ⊢
  have member : ruleCombineCongLeft ∈ maximalWithCong.rewrites := by
    simp [maximalWithCong, wmFullVertexLanguageDefWithCong, allCongruenceRules,
      coreCongruenceRules]
  refine step_of_single_congruence_rule (lang := maximalWithCong) (rule := ruleCombineCongLeft)
    (initialBindings := [("e2", e2), ("e1", e1)])
    (finalBindings := [("e1p", e1'), ("e2", e2), ("e1", e1)])
    (premiseBindings := [("e1p", e1')]) (premiseSource := .fvar "e1")
    (premiseTarget := .fvar "e1p") (candidate := e1') member ?_ rfl ?_ ?_ ?_ ?_
  · simp [ruleCombineCongLeft, pCombine, matchPattern, matchArgs, mergeBindings]
  · simpa [applyBindings] using inner
  · simp [matchPattern]
  · simp [mergeBindings]
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_applyBindings _
      ruleCombineCongLeft _ (by decide +kernel)]
    simp [ruleCombineCongLeft, pCombine, applyBindings]

theorem combineCongRight_step {env : RelationEnv} {e1 e2 e2' : Pattern}
    (inner : langReducesUsing env maximalWithCong e2 e2') :
    langReducesUsing env maximalWithCong (pCombine e1 e2) (pCombine e1 e2') := by
  unfold langReducesUsing at inner ⊢
  have member : ruleCombineCongRight ∈ maximalWithCong.rewrites := by
    simp [maximalWithCong, wmFullVertexLanguageDefWithCong, allCongruenceRules,
      coreCongruenceRules]
  refine step_of_single_congruence_rule (lang := maximalWithCong) (rule := ruleCombineCongRight)
    (initialBindings := [("e2", e2), ("e1", e1)])
    (finalBindings := [("e2p", e2'), ("e2", e2), ("e1", e1)])
    (premiseBindings := [("e2p", e2')]) (premiseSource := .fvar "e2")
    (premiseTarget := .fvar "e2p") (candidate := e2') member ?_ rfl ?_ ?_ ?_ ?_
  · simp [ruleCombineCongRight, pCombine, matchPattern, matchArgs, mergeBindings]
  · simpa [applyBindings] using inner
  · simp [matchPattern]
  · simp [mergeBindings]
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_applyBindings _
      ruleCombineCongRight _ (by decide +kernel)]
    simp [ruleCombineCongRight, pCombine, applyBindings]

/-- The maximal calculus with the old refutation rule added. -/
def withOldRefutation : LanguageDef :=
  { wmFullVertexLanguageDef wmFullVertexMaximal with
    rewrites := oldSingletonRefutation :: (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites }

/-- **The old refutation rule fires** on a row of the checked provider, and
rewrites the refuting singleton to `EvidenceZero`. -/
theorem oldSingletonRefutation_fires :
    langReducesUsing (providerEnv ledgerProvider) withOldRefutation
      (pKripkeEvidence (pSingleton pointOne) formulaZero) pEvidenceZero := by
  unfold langReducesUsing
  let bs : Bindings := [("phi", formulaZero), ("pk", pointOne)]
  refine step_of_rule (initialBindings := bs) (finalBindings := bs)
    (rule := oldSingletonRefutation) (by simp [withOldRefutation]) ?_ (.relationQuery .nil) ?_ ?_
  · simp [bs, oldSingletonRefutation, ruleKripkeSingletonNotSat, pKripkeEvidence, pSingleton,
      matchPattern, matchArgs, mergeBindings]
  · simp [bs, oldSingletonRefutation, ruleKripkeSingletonNotSat, applyPremisesWithEnv,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples, applyBindings, mergeBindings]
    exact ⟨_, kripkeNotSat_row, by
      simp [matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings]⟩
  · simp [Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings, bs, oldSingletonRefutation,
      pEvidenceZero]

/-- There the source denotes `⟨0, 1⟩` and the reduct `0`. -/
theorem oldSingletonRefutation_values :
    𝔇 ledgerHandles (pKripkeEvidence (pSingleton pointOne) formulaZero) =
        some (.evidence ⟨0, 1⟩) ∧
      𝔇 ledgerHandles pEvidenceZero = some (.evidence 0) := by
  refine ⟨?_, den_evidenceZero⟩
  rw [den_kripkeEvidence.mpr ⟨{1}, (0 : ℕ), den_singleton.mpr ⟨(1 : ℕ), rfl, rfl⟩, rfl, rfl⟩]
  congr 2
  exact Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.crispEvidence_singleton_of_not_satisfies
    _ (1 : ℕ) (0 : ℕ) (fun h => absurd (show (1 : ℕ) = 0 from h) (by decide))

/-- The two-point Kripke term. -/
def twoPointTerm : Pattern :=
  pKripkeEvidence (pRevise (pSingleton pointZero) (pSingleton pointOne)) formulaZero

/-- Its normal form: one observation for, one against. -/
def twoPointNormalForm : Pattern := pCombine pEvidenceOne pEvidenceOneNegative

/-- **The run**: evidence additivity at the root, then the two singleton rules
under `Combine`, each on a provider row. -/
theorem twoPoint_run :
    Relation.ReflTransGen (langReducesUsing (providerEnv ledgerProvider) maximalWithCong)
      twoPointTerm twoPointNormalForm := by
  have additivity : langReducesUsing (providerEnv ledgerProvider) maximalWithCong twoPointTerm
      (pCombine (pKripkeEvidence (pSingleton pointZero) formulaZero)
        (pKripkeEvidence (pSingleton pointOne) formulaZero)) := by
    apply congReducesUsing_of_reducesUsing_full
    unfold langReducesUsing
    exact Step.mono_relEnv (RelationEnv.empty_le _)
      (wmFullLangReduces_kripkeEvidenceAdd wmFullVertexMaximal rfl _ _ _)
  have satisfied := combineCongLeft_step
    (e2 := pKripkeEvidence (pSingleton pointOne) formulaZero)
    (kripkeSat_step pointZero formulaZero kripkeSat_row)
  have refuted := combineCongRight_step (e1 := pEvidenceOne)
    (kripkeNotSat_step pointOne formulaZero kripkeNotSat_row)
  exact ((Relation.ReflTransGen.single additivity).tail satisfied).tail refuted

theorem twoPointTerm_denotes :
    𝔇 ledgerHandles twoPointTerm =
      some (.evidence (crispEvidence (fun (point formula : ℕ) => point = formula)
        ({0} + {1}) 0)) :=
  den_kripkeEvidence.mpr ⟨{0} + {1}, (0 : ℕ),
    den_revise.mpr ⟨{0}, {1}, den_singleton.mpr ⟨(0 : ℕ), rfl, rfl⟩,
      den_singleton.mpr ⟨(1 : ℕ), rfl, rfl⟩, rfl⟩, rfl, rfl⟩

theorem twoPointNormalForm_denotes :
    𝔇 ledgerHandles twoPointNormalForm = some (.evidence (⟨1, 0⟩ + ⟨0, 1⟩)) :=
  den_combine.mpr ⟨_, _, den_evidenceOne, den_evidenceOneNegative, rfl⟩

/-- **The derived fact, certified by soundness**: the two-point ledger has one
observation for and one against the formula `0`.  The value is read off the
run's normal form; the soundness of the run, under the checked provider,
certifies that it is the model's evidence. -/
theorem twoPoint_evidence :
    crispEvidence (fun (point formula : ℕ) => point = formula) ({0} + {1}) 0 =
      ⟨1, 0⟩ + ⟨0, 1⟩ := by
  have certified := provider_run_sound ledgerProvider wmFullVertexMaximal twoPoint_run _
    twoPointTerm_denotes
  rw [show ledgerProvider.valuation = ledgerHandles from rfl, twoPointNormalForm_denotes]
    at certified
  exact (WMValue.evidence.inj (Option.some.inj certified)).symm

/-! ## Completeness fails in the core

Two closed evidence terms of the core agree in every lawful reading exactly
when their normal forms, multisets of state and query atoms, agree
(`allReadingsAgree_iff_normalForm_eq`).  Rewriting does not realize that
equality: the core has no associativity rule for `Combine`, and its contextual
steps keep the root partition of a pure evidence term
(`pure_contextStepStar_invariant`).  So two associations of three observations
are denotationally equal and have no common reduct. -/

section Completeness

open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusRewriteCompletenessBoundary

/-- **Denotational equality is not joinability**: the two associations of
three observations denote the same evidence in every lawful reading, and no
term is reachable from both by contextual core steps. -/
theorem semantic_assoc_not_joinable :
    (∀ (State Query V : Type) (R : WMReading State Query V),
      R.CoreLaws → R.denote leftAssoc = R.denote rightAssoc) ∧
    ¬ ∃ t, WMContextStepStar leftAssoc t ∧ WMContextStepStar rightAssoc t := by
  refine ⟨semantic_assoc_not_contextually_reachable.1, ?_⟩
  rintro ⟨t, fromLeft, fromRight⟩
  exact rootGroups_assoc_distinct
    ((pure_contextStepStar_invariant leftAssoc_pure fromLeft).2.trans
      (pure_contextStepStar_invariant rightAssoc_pure fromRight).2.symm)

end Completeness

#print axioms oldSingletonRefutation_invalid
#print axioms oldSingletonRefutation_fires
#print axioms oldSingletonRefutation_values
#print axioms premiseFreeSingletonSat_invalid
#print axioms premiseFreeSingletonPair_fires
#print axioms premiseFreeFallbackIncompatible_invalid
#print axioms premiseFreeFallbackCompatible_invalid
#print axioms premiseFreeSourceEvidenceAdd_invalid
#print axioms premiseFreePolicyTrustedAll_invalid
#print axioms premiseFreePartialRevision_defines_undefined
#print axioms premiseFreeProvenance_fire
#print axioms finiteSpaceCascade_invalid
#print axioms evidenceZeroAnomaly_invalid
#print axioms premiseFreeQueryTransport_invalid
#print axioms premiseFreeQueryTransport_fires
#print axioms premiseFree_rightNames_unbound
#print axioms oldBlackwell_arities_clash
#print axioms oldPullback_undenoted
#print axioms twoPoint_run
#print axioms twoPoint_evidence
#print axioms semantic_assoc_not_joinable

end Mettapedia.OSLF.Framework.WMCalculusCounterexamples
