import Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
import Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority
import Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

/-!
# Equational Boolean authority inside the atomless first-order theory

Universal closure embeds every Boolean identity into the richer first-order
atomless theory.  The semantic translation is conservative: no equational
truth is gained or lost.

The corresponding exact authority translation does not exist between the
current contracts.  The source truth-table checker intentionally distinguishes
complete from incomplete certificates, while the target direct decision
kernel intentionally erases evidence to `Unit`.  Two source certificates for
the same true identity therefore receive different replay results that no
target certificate map can preserve.  This is an operational distinction,
not a semantic failure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AtomlessBooleanEquationalEmbedding

open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanTermProfileBridge
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision.Canary
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority.Canary

universe u

private abbrev equationalTheory :=
  Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority.theory

private abbrev equationalContract :=
  Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority.contract

private abbrev firstOrderTheory :=
  Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.theory

private abbrev firstOrderContract :=
  Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.contract

/-! ## Universal closure -/

/-- Universal quantification in the negation/existential basis. -/
def forallFormula {arity : Nat} (body : Formula (arity + 1)) :
    Formula arity :=
  .negation (.existsF (.negation body))

theorem satisfies_forallFormula_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (body : Formula (arity + 1)) (valuation : Fin arity -> B) :
    Satisfies (forallFormula body) valuation <->
      forall value : B, Satisfies body (extendValuation value valuation) := by
  classical
  simp [forallFormula, Satisfies]

/-- Close every free variable, preserving the de Bruijn-zero binder order. -/
def universalClosure : {arity : Nat} -> Formula arity -> Formula 0
  | 0, formula => formula
  | _arity + 1, formula => universalClosure (forallFormula formula)

/-- Universal closure has exactly the expected all-valuations semantics. -/
theorem satisfies_universalClosure_iff
    {B : Type u} [BooleanAlgebra B] :
    {arity : Nat} -> (formula : Formula arity) ->
      Satisfies (universalClosure formula) (emptyValuation (B := B)) <->
        forall valuation : Fin arity -> B, Satisfies formula valuation := by
  intro arity
  induction arity with
  | zero =>
      intro formula
      constructor
      · intro satisfied valuation
        simpa only [universalClosure,
          Subsingleton.elim valuation (emptyValuation (B := B))] using satisfied
      · intro allSatisfied
        exact allSatisfied (emptyValuation (B := B))
  | succ arity inductionHypothesis =>
      intro formula
      rw [universalClosure, inductionHypothesis]
      constructor
      · intro allTails valuation
        have allHeads :=
          (satisfies_forallFormula_iff formula
            (fun index => valuation index.succ)).mp
            (allTails (fun index => valuation index.succ))
        have atHead := allHeads (valuation 0)
        rwa [extendValuation_head_tail valuation] at atHead
      · intro allValuations tailValuation
        apply (satisfies_forallFormula_iff formula tailValuation).mpr
        intro value
        exact allValuations (extendValuation value tailValuation)

/-- Embed an arity-indexed equation as its closed universal sentence. -/
def equationSentence {arity : Nat} (equation : Equation (Fin arity)) :
    Formula 0 :=
  universalClosure (.equation equation)

theorem equationSentence_coldMeaning_iff_validInCantor
    {arity : Nat} (equation : Equation (Fin arity)) :
    Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.ColdMeaning
        (equationSentence equation) <->
      ValidIn CantorAlgebra equation := by
  simpa [equationSentence,
    Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.ColdMeaning,
    ValidIn, Satisfies] using
    (satisfies_universalClosure_iff
      (B := CantorAlgebra) (.equation equation))

theorem equationSentence_coldMeaning_iff_boolValid
    {arity : Nat} (equation : Equation (Fin arity)) :
    Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.ColdMeaning
        (equationSentence equation) <->
      BoolValid equation :=
  (equationSentence_coldMeaning_iff_validInCantor equation).trans
    (boolValid_iff_cantorValid equation).symm

/-! ## Conservative semantic embedding -/

/-- The equational theory enters the first-order atomless theory by universal
closure. -/
def theoryTranslation : TheoryTranslation equationalTheory firstOrderTheory where
  mapKind := fun _arity => ()
  mapSignature := id
  signature_commutes := by intro _arity; rfl
  mapClaim := fun _arity equation => equationSentence equation
  scope_preserved := by
    intro _arity equation valid
    exact (equationSentence_coldMeaning_iff_boolValid equation).mpr valid
  meaning_preserved := by
    intro _arity equation valid
    exact (equationSentence_coldMeaning_iff_validInCantor equation).mpr valid

/-- Universal closure invents neither equational scope nor equational
meaning. -/
theorem theoryTranslation_conservative : theoryTranslation.Conservative where
  scope_reflecting := by
    intro _arity equation meaningful
    exact (equationSentence_coldMeaning_iff_boolValid equation).mp meaningful
  meaning_reflecting := by
    intro _arity equation meaningful
    exact (equationSentence_coldMeaning_iff_validInCantor equation).mp
      meaningful

/-! ## Exact evidence transport is impossible for these two contracts -/

/-- Certificate-sensitive truth-table replay cannot commute with a target
checker whose evidence fibre is `Unit`. -/
theorem no_exact_authorityTranslation :
    ¬ Nonempty (AuthorityTranslation equationalContract firstOrderContract) := by
  rintro ⟨translation⟩
  have targetCertificateSubsingleton :
      Subsingleton
        (firstOrderContract.Certificate (translation.mapKind 2)) := by
    change Subsingleton Unit
    infer_instance
  have mappedCertificateEqual :
      translation.mapCertificate 2 (fullTruthTable (Var := Fin 2)) =
        translation.mapCertificate 2
          [separatingAssignment] :=
    targetCertificateSubsingleton.elim _ _
  have checksEqual :
      (equationalContract.checker 2).check distributiveIdentity
          (fullTruthTable (Var := TwoVar)) =
        (equationalContract.checker 2).check distributiveIdentity
          [separatingAssignment] := by
    calc
      (equationalContract.checker 2).check distributiveIdentity
            (fullTruthTable (Var := TwoVar)) =
          (firstOrderContract.checker (translation.mapKind 2)).check
            (translation.mapClaim 2 distributiveIdentity)
            (translation.mapCertificate 2
              (fullTruthTable (Var := TwoVar))) :=
        (translation.check_commutes 2 distributiveIdentity
          (fullTruthTable (Var := TwoVar))).symm
      _ = (firstOrderContract.checker (translation.mapKind 2)).check
            (translation.mapClaim 2 distributiveIdentity)
            (translation.mapCertificate 2 [separatingAssignment]) := by
        rw [mappedCertificateEqual]
      _ = (equationalContract.checker 2).check distributiveIdentity
            [separatingAssignment] :=
        translation.check_commutes 2 distributiveIdentity
          [separatingAssignment]
  rw [distributive_replays,
    incomplete_distributive_certificate_rejected] at checksEqual
  exact Bool.noConfusion checksEqual

/-! ## Controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision.Canary

theorem distributive_sentence_has_coldMeaning :
    firstOrderTheory.Meaning () (equationSentence distributiveIdentity) :=
  theoryTranslation.meaning_preserved 2 distributiveIdentity
    distributive_cantor_valid

theorem falseIdentity_sentence_not_coldMeaning :
    ¬ firstOrderTheory.Meaning () (equationSentence falseIdentity) := by
  intro meaningful
  exact falseIdentity_not_cantorValid
    ((equationSentence_coldMeaning_iff_validInCantor falseIdentity).mp
      meaningful)

end Canary

#print axioms satisfies_forallFormula_iff
#print axioms satisfies_universalClosure_iff
#print axioms equationSentence_coldMeaning_iff_validInCantor
#print axioms theoryTranslation
#print axioms theoryTranslation_conservative
#print axioms no_exact_authorityTranslation
#print axioms Canary.distributive_sentence_has_coldMeaning
#print axioms Canary.falseIdentity_sentence_not_coldMeaning

end Mettapedia.GSLT.LanguageDef.AtomlessBooleanEquationalEmbedding
