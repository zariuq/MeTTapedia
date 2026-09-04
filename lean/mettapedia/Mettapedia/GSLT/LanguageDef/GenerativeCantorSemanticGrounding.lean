import Mettapedia.GSLT.Core.GenerativeCantorAtomlessness
import Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
import Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

/-!
# Finite-stage semantics for the Cantor atomless NIK authority

The Cantor-clopen semantic carrier is exhaustively presented by finite Boolean
prefix stages.  This module transports the existing first-order semantics
across that presentation.

A `FiniteClopenCode` retains its stage level and finite prefix region.
`StagedSatisfies` interprets existential quantifiers by ranging over such
codes.  Surjectivity of finite-stage realization proves that this staged
semantics is equivalent to ordinary quantification over all Cantor clopens.

The resulting staged authority and the existing cold-carrier authority have
the same executable decision procedure but independently stated meanings.
Exact authority translations in both directions prove semantic host
irrelevance for this selected fragment.  This does not claim that finite-stage
generation alone proves a verifier implementation correct.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.Ultrainfinite.GenerativeCantorAtomlessness
open TopologicalSpace

/-! ## Finite codes for every semantic element -/

/-- One Cantor clopen represented at an explicitly retained finite prefix
level. -/
structure FiniteClopenCode where
  level : Nat
  stage : FiniteBooleanStage level

/-- Interpret a finite prefix code in the ambient Cantor-clopen algebra. -/
noncomputable def FiniteClopenCode.decode
    (code : FiniteClopenCode) : CantorAlgebra :=
  realize code.level code.stage

/-- Exhaustivity of the generative presentation makes decoding surjective. -/
theorem decode_surjective : Function.Surjective FiniteClopenCode.decode := by
  intro region
  obtain ⟨level, stage, realized⟩ := cantorGeneration_exhaustive region
  exact ⟨⟨level, stage⟩, realized⟩

/-- A valuation whose values retain finite-stage provenance. -/
abbrev CodeValuation (arity : Nat) := Fin arity → FiniteClopenCode

/-- Decode a finite-stage valuation pointwise. -/
noncomputable def decodeValuation {arity : Nat}
    (valuation : CodeValuation arity) : Fin arity → CantorAlgebra :=
  fun index => (valuation index).decode

theorem decodeValuation_extend {arity : Nat} (value : FiniteClopenCode)
    (valuation : CodeValuation arity) :
    decodeValuation (extendValuation value valuation) =
      extendValuation value.decode (decodeValuation valuation) := by
  funext index
  exact Fin.cases rfl (fun _tail => rfl) index

/-! ## First-order semantics over unbounded finite stages -/

/-- First-order Boolean semantics in which every quantified value is supplied
by a finite prefix-stage code. -/
noncomputable def StagedSatisfies :
    {arity : Nat} → Formula arity → CodeValuation arity → Prop
  | _, .equation claim, valuation =>
      claim.left.eval (decodeValuation valuation) =
        claim.right.eval (decodeValuation valuation)
  | _, .falsum, _valuation => False
  | _, .conjunction left right, valuation =>
      StagedSatisfies left valuation ∧ StagedSatisfies right valuation
  | _, .negation body, valuation => ¬ StagedSatisfies body valuation
  | _, .existsF body, valuation =>
      ∃ value : FiniteClopenCode,
        StagedSatisfies body (extendValuation value valuation)

/-- Staged quantification is exactly ordinary Cantor-clopen quantification.
The existential case is the substantive one and uses surjectivity of finite
stage realization in both directions. -/
theorem stagedSatisfies_iff_satisfies :
    {arity : Nat} → (formula : Formula arity) →
      (valuation : CodeValuation arity) →
      StagedSatisfies formula valuation ↔
        Satisfies formula (decodeValuation valuation)
  | _, .equation _claim, _valuation => Iff.rfl
  | _, .falsum, _valuation => Iff.rfl
  | _, .conjunction left right, valuation =>
      and_congr (stagedSatisfies_iff_satisfies left valuation)
        (stagedSatisfies_iff_satisfies right valuation)
  | _, .negation body, valuation =>
      not_congr (stagedSatisfies_iff_satisfies body valuation)
  | _, .existsF body, valuation => by
      constructor
      · rintro ⟨code, staged⟩
        refine ⟨code.decode, ?_⟩
        have decoded :=
          (stagedSatisfies_iff_satisfies body
            (extendValuation code valuation)).mp staged
        simpa only [decodeValuation_extend] using decoded
      · rintro ⟨value, satisfied⟩
        obtain ⟨code, decoded⟩ := decode_surjective value
        refine ⟨code, ?_⟩
        apply (stagedSatisfies_iff_satisfies body
          (extendValuation code valuation)).mpr
        simpa only [decodeValuation_extend, decoded] using satisfied

/-- The unique closed staged valuation. -/
def emptyCodeValuation : CodeValuation 0 := Fin.elim0

theorem decode_emptyCodeValuation :
    decodeValuation emptyCodeValuation =
      emptyValuation (B := CantorAlgebra) := by
  funext index
  exact Fin.elim0 index

/-- Cold meaning restated through unbounded finite-stage quantification. -/
def StagedMeaning (formula : Formula 0) : Prop :=
  StagedSatisfies formula emptyCodeValuation

theorem stagedMeaning_iff_coldMeaning (formula : Formula 0) :
    StagedMeaning formula ↔ ColdMeaning formula := by
  rw [StagedMeaning, stagedSatisfies_iff_satisfies,
    decode_emptyCodeValuation]
  rfl

/-! ## Exact NIK authority and bidirectional transport -/

/-- The finite decision procedure qualified against staged meaning. -/
def stagedDecisionKernel : Checker.DecisionKernel (Formula 0) StagedMeaning where
  decide := decideClosed
  correct := by
    intro formula
    exact (decisionKernel.correct formula).trans
      (stagedMeaning_iff_coldMeaning formula).symm

def stagedTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _kind => ()
  Claim := fun _kind => Formula 0
  Scope := fun _kind => StagedMeaning
  Meaning := fun _kind => StagedMeaning
  scope_sound := by
    intro _kind _formula meaningful
    exact meaningful

def stagedContract : AuthorityContract stagedTheory where
  Certificate := fun _kind => Unit
  checker := fun _kind => stagedDecisionKernel.toChecker
  scopeAuthority := fun _kind => stagedDecisionKernel.authority

/-- Transport staged semantics into the ordinary cold Cantor carrier. -/
def stagedToCold : AuthorityTranslation stagedContract contract where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind formula => formula
  mapCertificate := fun _kind certificate => certificate
  check_commutes := by
    intro kind _formula certificate
    cases kind
    cases certificate
    rfl
  meaning_preserved := by
    intro _kind formula meaningful
    exact (stagedMeaning_iff_coldMeaning formula).mp meaningful

/-- Transport cold Cantor semantics back to its exhaustive finite-stage
presentation. -/
def coldToStaged : AuthorityTranslation contract stagedContract where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind formula => formula
  mapCertificate := fun _kind certificate => certificate
  check_commutes := by
    intro kind _formula certificate
    cases kind
    cases certificate
    rfl
  meaning_preserved := by
    intro _kind formula meaningful
    exact (stagedMeaning_iff_coldMeaning formula).mpr meaningful

theorem stagedToCold_conservative :
    stagedToCold.toTheoryTranslation.Conservative where
  scope_reflecting := by
    intro _kind formula meaningful
    exact (stagedMeaning_iff_coldMeaning formula).mpr meaningful
  meaning_reflecting := by
    intro _kind formula meaningful
    exact (stagedMeaning_iff_coldMeaning formula).mpr meaningful

theorem coldToStaged_conservative :
    coldToStaged.toTheoryTranslation.Conservative where
  scope_reflecting := by
    intro _kind formula meaningful
    exact (stagedMeaning_iff_coldMeaning formula).mp meaningful
  meaning_reflecting := by
    intro _kind formula meaningful
    exact (stagedMeaning_iff_coldMeaning formula).mp meaningful

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary

theorem properPart_replays :
    (stagedContract.checker ()).check properPartSentence () = true :=
  properPartSentence_decides_true

theorem properPart_has_stagedMeaning :
    stagedTheory.Meaning () properPartSentence :=
  (stagedDecisionKernel.correct properPartSentence).mp properPart_replays

theorem properPart_has_finite_code :
    ∃ code : FiniteClopenCode,
      code.decode ≠ (⊥ : CantorAlgebra) ∧
        code.decode ≠ (⊤ : CantorAlgebra) := by
  simpa [stagedTheory, StagedMeaning, StagedSatisfies, properPartSentence,
    equalsBottom, equalsTop, x, decodeValuation, extendValuation,
    BooleanAlgebraIdentityDecision.Term.eval] using
      properPart_has_stagedMeaning

def noProperPartSentence : Formula 0 := .negation properPartSentence

theorem noProperPart_not_stagedMeaning :
    ¬ stagedTheory.Meaning () noProperPartSentence := by
  intro impossible
  exact impossible properPart_has_stagedMeaning

theorem noProperPart_rejected :
    (stagedContract.checker ()).check noProperPartSentence () = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact noProperPart_not_stagedMeaning
    ((stagedDecisionKernel.correct noProperPartSentence).mp accepted)

end Canary

#print axioms decode_surjective
#print axioms decodeValuation_extend
#print axioms stagedSatisfies_iff_satisfies
#print axioms stagedMeaning_iff_coldMeaning
#print axioms stagedDecisionKernel
#print axioms stagedToCold
#print axioms coldToStaged
#print axioms stagedToCold_conservative
#print axioms coldToStaged_conservative
#print axioms Canary.properPart_replays
#print axioms Canary.properPart_has_stagedMeaning
#print axioms Canary.properPart_has_finite_code
#print axioms Canary.noProperPart_rejected

end Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding
