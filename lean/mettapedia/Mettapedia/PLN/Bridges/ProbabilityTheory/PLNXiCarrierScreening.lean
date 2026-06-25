import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiRuleRegistry
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
import Mettapedia.Logic.WMMarkovCanonical

/-!
# PLN Xi Carrier-Specific Screening Rules

Parameterizes the generic `DeductionScreeningOff` / source / sink side conditions
over concrete evidence carriers (Normal-Gamma, Dirichlet).

## Architecture

`WMRewriteRule.derive` returns binary `BinaryEvidence` (pos/neg). Carrier-specific
screening works by:
1. Extracting carrier-level views from the WM state (`view`)
2. Combining at carrier level (`combine`)
3. Projecting back to `BinaryEvidence` (`proj`)
4. Proving the screening-off condition

Since there are no coercions between `NormalGammaEvidence` / `MultiEvidence`
and `BinaryEvidence`, the projection is explicit.

## Carrier Family

A `CarrierFamily` bundles a view, projection, and combiner for any
carrier evidence type. Carrier-specific rules are direct `WMRewriteRule`
instances — they bypass the generic `combine : BinaryEvidence → BinaryEvidence → BinaryEvidence`
parameter and read from the state at carrier level.

All theorems are fully proved (0 sorry).
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.PLNXiCarrierScreening

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridge
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiRuleRegistry
open Mettapedia.OSLF.Framework.EvidenceSemantics
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax

open scoped ENNReal

/-! ## §1 Carrier Family -/

section CarrierFamily

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-- A carrier family bundles a view function (extracting carrier-level
evidence from WM state + query), a projection to binary `BinaryEvidence`, and
a carrier-level combiner. This parameterizes rule construction over the
distribution family. -/
structure CarrierFamily (CarrierEv : Type*) where
  /-- Extract carrier-level evidence from a WM state for a given query. -/
  view : State → AtomQuery Atom → CarrierEv
  /-- Project carrier evidence to binary BinaryEvidence (pos/neg counts). -/
  proj : CarrierEv → BinaryEvidence
  /-- Combine two carrier evidence values (used for deduction screening). -/
  combine : CarrierEv → CarrierEv → CarrierEv

/-- Carrier-level deduction screening: the carrier combine + projection
correctly computes link A→C evidence from link A→B and B→C evidence. -/
def CarrierDeductionScreeningOff {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) : Prop :=
  ∀ W : State,
    cf.proj (cf.combine
      (cf.view W (AtomQuery.link A B))
      (cf.view W (AtomQuery.link B C))) =
    AtomQuery.linkEvidence (State := State) (Atom := Atom) W A C

/-- Build a deduction WMRewriteRule from a carrier family + screening proof. -/
def carrierDeduction {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  { side := CarrierDeductionScreeningOff cf A B C
    conclusion := AtomQuery.link A C
    derive := fun W =>
      cf.proj (cf.combine (cf.view W (AtomQuery.link A B))
                           (cf.view W (AtomQuery.link B C)))
    sound := fun hSO W => hSO W }

/-- Carrier-level source rule screening: Bayes-invert B→A to A→B at
carrier level, then combine with B→C. -/
def CarrierSourceRuleScreeningOff {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) : Prop :=
  ∀ W : State,
    cf.proj (cf.combine
      (cf.view W (AtomQuery.link B A))
      (cf.view W (AtomQuery.link B C))) =
    AtomQuery.linkEvidence (State := State) (Atom := Atom) W A C

/-- Build a source rule WMRewriteRule from a carrier family. -/
def carrierSourceRule {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  { side := CarrierSourceRuleScreeningOff cf A B C
    conclusion := AtomQuery.link A C
    derive := fun W =>
      cf.proj (cf.combine (cf.view W (AtomQuery.link B A))
                           (cf.view W (AtomQuery.link B C)))
    sound := fun hSO W => hSO W }

/-- Carrier-level sink rule screening: combine A→B with C→B at carrier level. -/
def CarrierSinkRuleScreeningOff {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) : Prop :=
  ∀ W : State,
    cf.proj (cf.combine
      (cf.view W (AtomQuery.link A B))
      (cf.view W (AtomQuery.link C B))) =
    AtomQuery.linkEvidence (State := State) (Atom := Atom) W A C

/-- Build a sink rule WMRewriteRule from a carrier family. -/
def carrierSinkRule {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  { side := CarrierSinkRuleScreeningOff cf A B C
    conclusion := AtomQuery.link A C
    derive := fun W =>
      cf.proj (cf.combine (cf.view W (AtomQuery.link A B))
                           (cf.view W (AtomQuery.link C B)))
    sound := fun hSO W => hSO W }

/-- Carrier deduction derives the correct value (unfold helper). -/
theorem carrierDeduction_derives {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) (W : State) :
    (carrierDeduction cf A B C).derive W =
      cf.proj (cf.combine (cf.view W (AtomQuery.link A B))
                           (cf.view W (AtomQuery.link B C))) := rfl

end CarrierFamily

/-! ## §1b Query-Indexed Carrier Family -/

section QueryIndexedCarrierFamily

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-- Query-indexed carrier families generalize `CarrierFamily` by allowing the
binary projection to depend on the query being answered. This is the right
interface when the additive carrier retains more structure than the binary
view, such as Markov row evidence where the queried target state selects the
"positive" coordinate. -/
structure QueryIndexedCarrierFamily (CarrierEv : Type*) where
  /-- Extract carrier-level evidence from a WM state for a given query. -/
  view : State → AtomQuery Atom → CarrierEv
  /-- Project carrier evidence to binary `BinaryEvidence` for a given query. -/
  proj : AtomQuery Atom → CarrierEv → BinaryEvidence
  /-- Combine two carrier values at the carrier level. -/
  combine : CarrierEv → CarrierEv → CarrierEv

/-- Any query-independent carrier family can be used as a query-indexed one by
ignoring the extra query argument in the projection. -/
def CarrierFamily.toQueryIndexed {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv) :
    QueryIndexedCarrierFamily (State := State) (Atom := Atom) CarrierEv where
  view := cf.view
  proj := fun _ => cf.proj
  combine := cf.combine

/-- Carrier-level deduction screening with query-indexed projection. -/
def QueryIndexedCarrierDeductionScreeningOff {CarrierEv : Type*}
    (cf : QueryIndexedCarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) : Prop :=
  ∀ W : State,
    cf.proj (AtomQuery.link A C)
      (cf.combine
        (cf.view W (AtomQuery.link A B))
        (cf.view W (AtomQuery.link B C))) =
    AtomQuery.linkEvidence (State := State) (Atom := Atom) W A C

/-- Build a deduction rewrite rule from a query-indexed carrier family. -/
def queryIndexedCarrierDeduction {CarrierEv : Type*}
    (cf : QueryIndexedCarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  { side := QueryIndexedCarrierDeductionScreeningOff cf A B C
    conclusion := AtomQuery.link A C
    derive := fun W =>
      cf.proj (AtomQuery.link A C)
        (cf.combine (cf.view W (AtomQuery.link A B))
          (cf.view W (AtomQuery.link B C)))
    sound := fun hSO W => hSO W }

/-- Carrier-level source-rule screening with query-indexed projection. -/
def QueryIndexedCarrierSourceRuleScreeningOff {CarrierEv : Type*}
    (cf : QueryIndexedCarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) : Prop :=
  ∀ W : State,
    cf.proj (AtomQuery.link A C)
      (cf.combine
        (cf.view W (AtomQuery.link B A))
        (cf.view W (AtomQuery.link B C))) =
    AtomQuery.linkEvidence (State := State) (Atom := Atom) W A C

/-- Build a source-rule rewrite from a query-indexed carrier family. -/
def queryIndexedCarrierSourceRule {CarrierEv : Type*}
    (cf : QueryIndexedCarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  { side := QueryIndexedCarrierSourceRuleScreeningOff cf A B C
    conclusion := AtomQuery.link A C
    derive := fun W =>
      cf.proj (AtomQuery.link A C)
        (cf.combine (cf.view W (AtomQuery.link B A))
          (cf.view W (AtomQuery.link B C)))
    sound := fun hSO W => hSO W }

/-- Carrier-level sink-rule screening with query-indexed projection. -/
def QueryIndexedCarrierSinkRuleScreeningOff {CarrierEv : Type*}
    (cf : QueryIndexedCarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) : Prop :=
  ∀ W : State,
    cf.proj (AtomQuery.link A C)
      (cf.combine
        (cf.view W (AtomQuery.link A B))
        (cf.view W (AtomQuery.link C B))) =
    AtomQuery.linkEvidence (State := State) (Atom := Atom) W A C

/-- Build a sink-rule rewrite from a query-indexed carrier family. -/
def queryIndexedCarrierSinkRule {CarrierEv : Type*}
    (cf : QueryIndexedCarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  { side := QueryIndexedCarrierSinkRuleScreeningOff cf A B C
    conclusion := AtomQuery.link A C
    derive := fun W =>
      cf.proj (AtomQuery.link A C)
        (cf.combine (cf.view W (AtomQuery.link A B))
          (cf.view W (AtomQuery.link C B)))
    sound := fun hSO W => hSO W }

/-- Unfold helper for query-indexed carrier deduction. -/
theorem queryIndexedCarrierDeduction_derives {CarrierEv : Type*}
    (cf : QueryIndexedCarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom) (W : State) :
    (queryIndexedCarrierDeduction cf A B C).derive W =
      cf.proj (AtomQuery.link A C)
        (cf.combine (cf.view W (AtomQuery.link A B))
          (cf.view W (AtomQuery.link B C))) := rfl

end QueryIndexedCarrierFamily

/-! ## §2 OSLF Bridges for Carrier Rules -/

section CarrierOSLF

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-- Carrier deduction lifts to OSLF atom evidence. -/
theorem carrierDeduction_semE_atom {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom)
    (hSO : CarrierDeductionScreeningOff cf A B C)
    (R : Pattern → Pattern → Prop) (W : State)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C) :
    semE R (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (carrierDeduction cf A B C).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (carrierDeduction cf A B C) hSO W enc a p hEnc

/-- Carrier deduction gives threshold atom truth. -/
theorem carrierDeduction_threshold_atom {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom)
    (hSO : CarrierDeductionScreeningOff cf A B C)
    (R : Pattern → Pattern → Prop) (W : State) (tau : ℝ≥0∞)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((carrierDeduction cf A B C).derive W)) :
    sem R (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (carrierDeduction cf A B C) hSO W tau enc a p hEnc hTau

/-- Carrier source rule lifts to OSLF atom evidence. -/
theorem carrierSourceRule_semE_atom {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom)
    (hSO : CarrierSourceRuleScreeningOff cf A B C)
    (R : Pattern → Pattern → Prop) (W : State)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C) :
    semE R (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (carrierSourceRule cf A B C).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (carrierSourceRule cf A B C) hSO W enc a p hEnc

/-- Carrier sink rule lifts to OSLF atom evidence. -/
theorem carrierSinkRule_semE_atom {CarrierEv : Type*}
    (cf : CarrierFamily (State := State) (Atom := Atom) CarrierEv)
    (A B C : Atom)
    (hSO : CarrierSinkRuleScreeningOff cf A B C)
    (R : Pattern → Pattern → Prop) (W : State)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C) :
    semE R (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (carrierSinkRule cf A B C).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (carrierSinkRule cf A B C) hSO W enc a p hEnc

end CarrierOSLF

/-! ## §3 Normal-Gamma Carrier Instantiation -/

section NormalGammaCarrier

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-- A Normal-Gamma carrier family, parameterized over the view, projection,
and combiner. These are supplied by the concrete WM model. -/
def normalGammaCarrier
    (nnView : State → AtomQuery Atom → NormalGammaEvidence)
    (nnProj : NormalGammaEvidence → BinaryEvidence)
    (nnCombine : NormalGammaEvidence → NormalGammaEvidence → NormalGammaEvidence) :
    CarrierFamily (State := State) (Atom := Atom) NormalGammaEvidence :=
  { view := nnView
    proj := nnProj
    combine := nnCombine }

/-- Normal-Gamma deduction rule as a WMRewriteRule. -/
def xi_normalGamma_deduction
    (nnView : State → AtomQuery Atom → NormalGammaEvidence)
    (nnProj : NormalGammaEvidence → BinaryEvidence)
    (nnCombine : NormalGammaEvidence → NormalGammaEvidence → NormalGammaEvidence)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  carrierDeduction (normalGammaCarrier nnView nnProj nnCombine) A B C

/-- Normal-Gamma source rule as a WMRewriteRule. -/
def xi_normalGamma_sourceRule
    (nnView : State → AtomQuery Atom → NormalGammaEvidence)
    (nnProj : NormalGammaEvidence → BinaryEvidence)
    (nnCombine : NormalGammaEvidence → NormalGammaEvidence → NormalGammaEvidence)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  carrierSourceRule (normalGammaCarrier nnView nnProj nnCombine) A B C

/-- Normal-Gamma sink rule as a WMRewriteRule. -/
def xi_normalGamma_sinkRule
    (nnView : State → AtomQuery Atom → NormalGammaEvidence)
    (nnProj : NormalGammaEvidence → BinaryEvidence)
    (nnCombine : NormalGammaEvidence → NormalGammaEvidence → NormalGammaEvidence)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  carrierSinkRule (normalGammaCarrier nnView nnProj nnCombine) A B C

end NormalGammaCarrier

/-! ## §4 Dirichlet Carrier Instantiation -/

section DirichletCarrier

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]
variable {k : ℕ}

/-- A Dirichlet carrier family for k-categorical evidence. -/
def dirichletCarrier
    (dirView : State → AtomQuery Atom → MultiEvidence k)
    (dirProj : MultiEvidence k → BinaryEvidence)
    (dirCombine : MultiEvidence k → MultiEvidence k → MultiEvidence k) :
    CarrierFamily (State := State) (Atom := Atom) (MultiEvidence k) :=
  { view := dirView
    proj := dirProj
    combine := dirCombine }

/-- Dirichlet deduction rule as a WMRewriteRule. -/
def xi_dirichlet_deduction
    (dirView : State → AtomQuery Atom → MultiEvidence k)
    (dirProj : MultiEvidence k → BinaryEvidence)
    (dirCombine : MultiEvidence k → MultiEvidence k → MultiEvidence k)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  carrierDeduction (dirichletCarrier dirView dirProj dirCombine) A B C

/-- Dirichlet source rule as a WMRewriteRule. -/
def xi_dirichlet_sourceRule
    (dirView : State → AtomQuery Atom → MultiEvidence k)
    (dirProj : MultiEvidence k → BinaryEvidence)
    (dirCombine : MultiEvidence k → MultiEvidence k → MultiEvidence k)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  carrierSourceRule (dirichletCarrier dirView dirProj dirCombine) A B C

/-- Dirichlet sink rule as a WMRewriteRule. -/
def xi_dirichlet_sinkRule
    (dirView : State → AtomQuery Atom → MultiEvidence k)
    (dirProj : MultiEvidence k → BinaryEvidence)
    (dirCombine : MultiEvidence k → MultiEvidence k → MultiEvidence k)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  carrierSinkRule (dirichletCarrier dirView dirProj dirCombine) A B C

end DirichletCarrier

/-! ## §4b Query-Indexed Dirichlet Carrier Instantiation -/

section QueryIndexedDirichletCarrier

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]
variable {k : ℕ}

/-- A query-indexed Dirichlet carrier family for `k`-categorical evidence. -/
def queryIndexedDirichletCarrier
    (dirView : State → AtomQuery Atom → MultiEvidence k)
    (dirProj : AtomQuery Atom → MultiEvidence k → BinaryEvidence)
    (dirCombine : MultiEvidence k → MultiEvidence k → MultiEvidence k) :
    QueryIndexedCarrierFamily (State := State) (Atom := Atom) (MultiEvidence k) :=
  { view := dirView
    proj := dirProj
    combine := dirCombine }

/-- Query-indexed Dirichlet deduction rule as a WM rewrite rule. -/
def xi_queryIndexed_dirichlet_deduction
    (dirView : State → AtomQuery Atom → MultiEvidence k)
    (dirProj : AtomQuery Atom → MultiEvidence k → BinaryEvidence)
    (dirCombine : MultiEvidence k → MultiEvidence k → MultiEvidence k)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  queryIndexedCarrierDeduction
    (queryIndexedDirichletCarrier dirView dirProj dirCombine) A B C

/-- Query-indexed Dirichlet source rule as a WM rewrite rule. -/
def xi_queryIndexed_dirichlet_sourceRule
    (dirView : State → AtomQuery Atom → MultiEvidence k)
    (dirProj : AtomQuery Atom → MultiEvidence k → BinaryEvidence)
    (dirCombine : MultiEvidence k → MultiEvidence k → MultiEvidence k)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  queryIndexedCarrierSourceRule
    (queryIndexedDirichletCarrier dirView dirProj dirCombine) A B C

/-- Query-indexed Dirichlet sink rule as a WM rewrite rule. -/
def xi_queryIndexed_dirichlet_sinkRule
    (dirView : State → AtomQuery Atom → MultiEvidence k)
    (dirProj : AtomQuery Atom → MultiEvidence k → BinaryEvidence)
    (dirCombine : MultiEvidence k → MultiEvidence k → MultiEvidence k)
    (A B C : Atom) :
    WMRewriteRule State (AtomQuery Atom) :=
  queryIndexedCarrierSinkRule
    (queryIndexedDirichletCarrier dirView dirProj dirCombine) A B C

end QueryIndexedDirichletCarrier

/-! ## §4c Markov Transition Carrier -/

section MarkovCarrier

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
open Mettapedia.Logic.WMMarkovCanonical

variable {k : ℕ}

/-- Markov XiPLN queries are transition atoms `i → j`, represented by the
existing `AtomQuery (Fin k)` link surface. -/
abbrev MarkovXiQuery (k : ℕ) := MarkovTransitionQuery k

/-- Query-indexed Dirichlet carrier for Markov transition multisets. The view
extracts the source row evidence; the query-indexed projection picks the target
coordinate as positive evidence and collapses the remaining outgoing counts into
negative evidence. -/
noncomputable def markovDirichletQueryCarrier :
    QueryIndexedCarrierFamily
      (State := MarkovTransitionWMState k)
      (Atom := Fin k)
      (MultiEvidence k) where
  view W q := markov_rowExtract (k := k) W (markov_transitionQuerySource q)
  proj q e := markov_queryBinaryProjection (k := k) q e
  combine := (· + ·)

@[simp] theorem markovDirichletQueryCarrier_view_link
    (W : MarkovTransitionWMState k) (prev next : Fin k) :
    (markovDirichletQueryCarrier (k := k)).view W (.link prev next) =
      markov_rowExtract (k := k) W prev :=
  rfl

@[simp] theorem markovDirichletQueryCarrier_proj_link
    (e : MultiEvidence k) (prev next : Fin k) :
    (markovDirichletQueryCarrier (k := k)).proj (.link prev next) e =
      markov_binaryEvidenceOfRowEvidence e next :=
  rfl

/-- Markov query-indexed deduction rule wrapper. -/
noncomputable def xi_markovDirichlet_deduction
    (A B C : Fin k) :
    WMRewriteRule (MarkovTransitionWMState k) (AtomQuery (Fin k)) :=
  queryIndexedCarrierDeduction
    (State := MarkovTransitionWMState k) (Atom := Fin k)
    (markovDirichletQueryCarrier (k := k)) A B C

/-- Markov query-indexed source-rule wrapper. -/
noncomputable def xi_markovDirichlet_sourceRule
    (A B C : Fin k) :
    WMRewriteRule (MarkovTransitionWMState k) (AtomQuery (Fin k)) :=
  queryIndexedCarrierSourceRule
    (State := MarkovTransitionWMState k) (Atom := Fin k)
    (markovDirichletQueryCarrier (k := k)) A B C

/-- Markov query-indexed sink-rule wrapper. -/
noncomputable def xi_markovDirichlet_sinkRule
    (A B C : Fin k) :
    WMRewriteRule (MarkovTransitionWMState k) (AtomQuery (Fin k)) :=
  queryIndexedCarrierSinkRule
    (State := MarkovTransitionWMState k) (Atom := Fin k)
    (markovDirichletQueryCarrier (k := k)) A B C

/-- Unfold helper for the Markov query-indexed deduction carrier. -/
theorem xi_markovDirichlet_deduction_derives
    (A B C : Fin k) (W : MarkovTransitionWMState k) :
    (xi_markovDirichlet_deduction (k := k) A B C).derive W =
      markov_queryBinaryProjection (k := k) (.link A C)
        (markov_rowExtract (k := k) W A + markov_rowExtract (k := k) W B) := by
  rfl

/-- Unfold helper for the Markov query-indexed source rule. -/
theorem xi_markovDirichlet_sourceRule_derives
    (A B C : Fin k) (W : MarkovTransitionWMState k) :
    (xi_markovDirichlet_sourceRule (k := k) A B C).derive W =
      markov_queryBinaryProjection (k := k) (.link A C)
        (markov_rowExtract (k := k) W B + markov_rowExtract (k := k) W B) := by
  rfl

/-- Unfold helper for the Markov query-indexed sink rule. -/
theorem xi_markovDirichlet_sinkRule_derives
    (A B C : Fin k) (W : MarkovTransitionWMState k) :
    (xi_markovDirichlet_sinkRule (k := k) A B C).derive W =
      markov_queryBinaryProjection (k := k) (.link A C)
        (markov_rowExtract (k := k) W A + markov_rowExtract (k := k) W C) := by
  rfl

end MarkovCarrier

/-! ## §5 ξPLN Carrier Packaging -/

section XiPackaging

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-- Build a ξPLN package from a set of carrier-derived rules. -/
def xiFromCarrierRules
    (enc : String → Pattern → AtomQuery Atom)
    (carrierRules : Set (WMRewriteRule State (AtomQuery Atom))) :
    XiPLN (State := State) (Query := AtomQuery Atom) :=
  { queryOfAtom := enc
    rulesE := carrierRules
    rulesS := ∅ }

/-- Carrier-derived rules compose with the ξPLN soundness theorem:
if a carrier rule derives evidence `e` for an atom, `semE` of that atom = `e`. -/
theorem xiFromCarrierRules_sound
    (enc : String → Pattern → AtomQuery Atom)
    (carrierRules : Set (WMRewriteRule State (AtomQuery Atom)))
    (R : Pattern → Pattern → Prop)
    {W : State} {a : String} {p : Pattern} {e : BinaryEvidence}
    (hDer : XiDerivesAtomEvidence
      (xiFromCarrierRules enc carrierRules) W a p e) :
    semE R (wmEvidenceAtomSemQ W enc) (.atom a) p = e :=
  xiDerivesAtomEvidence_sound
    (xiFromCarrierRules enc carrierRules) R hDer

end XiPackaging

end Mettapedia.PLN.Bridges.ProbabilityTheory.PLNXiCarrierScreening
