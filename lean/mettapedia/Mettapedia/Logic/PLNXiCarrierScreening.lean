import Mettapedia.Logic.PLNXiRuleRegistry
import Mettapedia.Logic.EvidenceNormalGamma
import Mettapedia.Logic.EvidenceDirichlet

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

namespace Mettapedia.Logic.PLNXiCarrierScreening

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWMOSLFBridge
open Mettapedia.Logic.PLNXiRuleRegistry
open Mettapedia.Logic.OSLFEvidenceSemantics
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

open Mettapedia.Logic.EvidenceNormalGamma

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

open Mettapedia.Logic.EvidenceDirichlet

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

end Mettapedia.Logic.PLNXiCarrierScreening
