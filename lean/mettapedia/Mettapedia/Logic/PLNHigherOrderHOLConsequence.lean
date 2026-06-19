import Mettapedia.Logic.PLNHigherOrderHOLSoundness
import Mettapedia.Logic.PLNWorldModelCalculus

namespace Mettapedia.Logic.PLNHigherOrderHOLConsequence

universe u v w

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.Logic.PLNWorldModel

variable {Base : Type u} {Const : Ty Base → Type v}

abbrev HOLQuery (Const : Ty Base → Type v) :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery (Base := Base) Const

abbrev HOLState (Base : Type u) (Const : Ty Base → Type v) :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState Base Const

/-- Classical higher-order theory surface for the HO WM-PLN layer. -/
abbrev ClassicalHOLTheory :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.ClassicalHOLTheory
    (Base := Base) (Const := Const)

/-- Classical higher-order query surface over `WithParams Const`. -/
abbrev ClassicalHOLQuery :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.ClassicalHOLQuery
    (Base := Base) (Const := Const)

/-- Classical higher-order state surface built from Henkin models of a theory. -/
abbrev ClassicalHOLState :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.ClassicalHOLState
    (Base := Base) (Const := Const)

/-- Sound finite theory-relative higher-order implication derivability. -/
abbrev HOLDerivableImpOnTheory
    (T : ClassicalHOLTheory (Base := Base) (Const := Const))
    (φ ψ : ClassicalHOLQuery (Base := Base) (Const := Const)) : Prop :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.derivableImpOnTheory
    (Base := Base) (Const := Const) T φ ψ

/-- The extensional closed-theory implication surface used by the classical HOL
completeness development. This is stronger than the sound finite-derivation
surface and should not be silently identified with it. -/
abbrev HOLExtensionalProvImpOnTheory
    (T : ClassicalHOLTheory (Base := Base) (Const := Const))
    (φ ψ : ClassicalHOLQuery (Base := Base) (Const := Const)) : Prop :=
  ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ)

abbrev HOLProvImp (φ ψ : HOLQuery Const) : Prop :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvImp (Const := Const) φ ψ

abbrev HOLProvIff (φ ψ : HOLQuery Const) : Prop :=
  Mettapedia.Logic.PLNHigherOrderHOLRules.HOLProvIff (Base := Base) (Const := Const) φ ψ

abbrev HOLWMQueryEq (φ ψ : HOLQuery Const) : Prop :=
  WMQueryEq
    (State := Multiset (HenkinModel.{u, v, w} Base Const))
    (Query := HOLQuery Const) φ ψ

abbrev HOLWMStrengthEq (φ ψ : HOLQuery Const) : Prop :=
  ∀ W : Multiset (HenkinModel.{u, v, w} Base Const),
    BinaryWorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const) W φ =
      BinaryWorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const) W ψ

/-- Proof-backed WM strength transport for higher-order HOL queries. -/
theorem holProvImp_to_WMStrengthLE {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) :
    WMStrengthLE (State := HOLState Base Const) (Query := HOLQuery Const) φ ψ :=
  Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_multisetConsequence
    (Base := Base) (Const := Const) h

/-- Proof-backed WM query equivalence for higher-order HOL queries. -/
theorem holProvIff_to_WMQueryEq {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    HOLWMQueryEq (Base := Base) (Const := Const) φ ψ :=
  Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_queryEq
    (Base := Base) (Const := Const) h

/-- Proof-backed WM strength equality for higher-order HOL queries. -/
theorem holProvIff_to_WMStrengthEq {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    HOLWMStrengthEq (Base := Base) (Const := Const) φ ψ :=
  Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_strengthEq
    (Base := Base) (Const := Const) h

/-- A proved HOL implication packages as a global WM consequence rule. -/
noncomputable def wmConsequenceRule_of_holProvImp {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) :
    WMConsequenceRule (HOLState Base Const) (HOLQuery Const) where
  side := True
  premise := φ
  conclusion := ψ
  sound := by
    intro _ W
    exact Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_multisetConsequence
      (Base := Base) (Const := Const) h W

/-- A proved HOL implication packages as a state-indexed WM consequence rule. -/
noncomputable def wmConsequenceRuleOn_of_holProvImp {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) :
    WMConsequenceRuleOn (HOLState Base Const) (HOLQuery Const) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_holProvImp (Base := Base) (Const := Const) h)

/-- Apply the proof-backed WM consequence rule directly at a world-model state. -/
theorem holProvImp_to_WMConsequenceRuleOn_apply {φ ψ : HOLQuery Const}
    (h : HOLProvImp (Const := Const) φ ψ) (W : HOLState Base Const) :
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ :=
  Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_multisetConsequence
    (Base := Base) (Const := Const) h W

/-- Sound finite theory-relative higher-order derivability transports to
singleton WM consequence on theory-model states. -/
theorem holDerivableImpOnTheory_to_singletonConsequence
    {T : ClassicalHOLTheory (Base := Base) (Const := Const)}
    {φ ψ : ClassicalHOLQuery (Base := Base) (Const := Const)}
    (h : HOLDerivableImpOnTheory (Base := Base) (Const := Const) T φ ψ) :
    Mettapedia.Logic.PLNWorldModelHOLCompleteness.singletonConsequenceOnTheory
      (Base := Base) (Const := Const) T φ ψ :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.derivableImpOnTheory_implies_singletonStrengthLEOnTheory
    (Base := Base) (Const := Const) h

/-- Package sound finite theory-relative higher-order derivability as a
state-indexed WM consequence rule. -/
noncomputable def wmConsequenceRuleOn_of_holDerivableImpOnTheory
    {T : ClassicalHOLTheory (Base := Base) (Const := Const)}
    {φ ψ : ClassicalHOLQuery (Base := Base) (Const := Const)}
    (h : HOLDerivableImpOnTheory (Base := Base) (Const := Const) T φ ψ) :
    WMConsequenceRuleOn
      (ClassicalHOLState (Base := Base) (Const := Const))
      (ClassicalHOLQuery (Base := Base) (Const := Const)) :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.wmConsequenceRuleOn_of_derivableImpOnTheory
    (Base := Base) (Const := Const) T φ ψ h

/-- Classical singleton consequence on theory-model states yields provability in
the extensional closed-theory implication surface used by HOL completeness. -/
theorem classical_singletonConsequenceOnTheory_to_holExtensionalProvImpOnTheory
    {T : ClassicalHOLTheory (Base := Base) (Const := Const)}
    {φ ψ : ClassicalHOLQuery (Base := Base) (Const := Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ χ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hEM : ∀ χ ∈ EMSchema Const, χ ∈ T)
    (hImp0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) (.imp φ ψ))
    (h : Mettapedia.Logic.PLNWorldModelHOLCompleteness.singletonConsequenceOnTheory
      (Base := Base) (Const := Const) T φ ψ) :
    HOLExtensionalProvImpOnTheory (Base := Base) (Const := Const) T φ ψ :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.provable_imp_onTheory_of_singletonConsequenceOnTheory_classical
    (Base := Base) (Const := Const) enum henum hT0 hEM hImp0 h

/-- Sound finite theory-relative derivability embeds into the stronger
extensional closed-theory proof surface once the classical completeness
side-conditions are supplied. This names the honest relation between the two
surfaces without treating them as definitionally identical. -/
theorem holDerivableImpOnTheory_to_holExtensionalProvImpOnTheory_classical
    {T : ClassicalHOLTheory (Base := Base) (Const := Const)}
    {φ ψ : ClassicalHOLQuery (Base := Base) (Const := Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ χ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hEM : ∀ χ ∈ EMSchema Const, χ ∈ T)
    (hImp0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) (.imp φ ψ))
    (h :
      HOLDerivableImpOnTheory (Base := Base) (Const := Const) T φ ψ) :
    HOLExtensionalProvImpOnTheory (Base := Base) (Const := Const) T φ ψ :=
  classical_singletonConsequenceOnTheory_to_holExtensionalProvImpOnTheory
    (Base := Base)
    (Const := Const)
    enum
    henum
    hT0
    hEM
    hImp0
    (holDerivableImpOnTheory_to_singletonConsequence
      (Base := Base)
      (Const := Const)
      h)

/-- A proved HOL equivalence packages as a sound WM query rewrite. -/
noncomputable def wmRewriteRule_of_holProvIff {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    WMRewriteRule (HOLState Base Const) (HOLQuery Const) where
  side := True
  conclusion := ψ
  derive := fun W => BinaryWorldModel.evidence (State := HOLState Base Const) (Query := HOLQuery Const) W φ
  sound := by
    intro _ W
    exact holProvIff_to_WMQueryEq (Base := Base) (Const := Const) h W

end Mettapedia.Logic.PLNHigherOrderHOLConsequence
