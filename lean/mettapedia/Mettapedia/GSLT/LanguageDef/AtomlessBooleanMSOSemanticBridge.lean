import Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
import Mettapedia.Logic.Metaphysics.UltrainfinitismTwoSemantics

/-!
# The decidable atomless first-order authority inside ultrainfinitist MSO

The atomless Boolean decision language is exactly a first-order fragment of
the monadic second-order language used by the ultrainfinitist model.  This file
defines the syntax translation and proves semantic agreement over every
Boolean algebra and every second-order quantifier family.

The image contains no second-order quantifiers, so its truth is independent of
the chosen Henkin family.  This gives both a positive bridge and a sharp
boundary: the genuinely family-sensitive existential-ultrafilter sentence is
not representable by any translated first-order formula.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AtomlessBooleanMSOSemanticBridge

open Mettapedia.Foundations.Gunk
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
open Mettapedia.Logic.Metaphysics

universe u

/-! ## Exact first-order embedding -/

/-- Translate a Boolean term into the first-order term language underlying
ultrainfinitist MSO. -/
def translateTerm {arity : Nat} : Term (Fin arity) -> BATerm arity
  | .atom name => .fvar name
  | .bottom => .bot
  | .top => .top
  | .meet left right => .inf (translateTerm left) (translateTerm right)
  | .join left right => .sup (translateTerm left) (translateTerm right)
  | .complement body => .compl (translateTerm body)

@[simp] theorem eval_translateTerm
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (term : Term (Fin arity)) (valuation : Fin arity -> B) :
    (translateTerm term).eval valuation = term.eval valuation := by
  induction term with
  | atom name => rfl
  | bottom => rfl
  | top => rfl
  | meet left right leftIH rightIH =>
      simp [translateTerm, Term.eval, leftIH, rightIH]
  | join left right leftIH rightIH =>
      simp [translateTerm, Term.eval, leftIH, rightIH]
  | complement body bodyIH =>
      simp [translateTerm, Term.eval, bodyIH]

/-- Embed the ordinary first-order language as the zero-set-variable fragment
of MSO. -/
def translateFormula : {arity : Nat} -> Formula arity -> MSO arity 0
  | _, .equation claim =>
      .eq (translateTerm claim.left) (translateTerm claim.right)
  | _, .falsum => .fls
  | _, .conjunction left right =>
      .and (translateFormula left) (translateFormula right)
  | _, .negation body => .not (translateFormula body)
  | _, .existsF body => .exFO (translateFormula body)

/-- The image contains no second-order binders. -/
theorem translateFormula_soqf :
    {arity : Nat} -> (formula : Formula arity) ->
      SOQuantFree (translateFormula formula)
  | _, .equation _ => by simp [translateFormula, SOQuantFree]
  | _, .falsum => by simp [translateFormula, SOQuantFree]
  | _, .conjunction left right => by
      exact ⟨translateFormula_soqf left, translateFormula_soqf right⟩
  | _, .negation body => translateFormula_soqf body
  | _, .existsF body => translateFormula_soqf body

theorem extendValuation_eq_finCons
    {B : Type u} {arity : Nat} (value : B)
    (valuation : Fin arity -> B) :
    extendValuation value valuation = Fin.cons value valuation := by
  funext index
  refine Fin.cases ?_ (fun _tailIndex => ?_) index
  · rfl
  · rfl

/-- Translation preserves and reflects the independently defined carrier
semantics.  The second-order family is arbitrary because the translated
formula has no second-order variables or binders. -/
theorem sat_translateFormula_iff
    {B : Type u} [BooleanAlgebra B] {family : Set (Set B)} :
    {arity : Nat} -> (formula : Formula arity) ->
      (valuation : Fin arity -> B) ->
      Sat family valuation Fin.elim0 (translateFormula formula) <->
        Satisfies formula valuation
  | _, .equation claim, valuation => by
      simp [translateFormula, Satisfies]
  | _, .falsum, _valuation => Iff.rfl
  | _, .conjunction left right, valuation => by
      exact and_congr
        (sat_translateFormula_iff left valuation)
        (sat_translateFormula_iff right valuation)
  | _, .negation body, valuation => by
      exact not_congr (sat_translateFormula_iff body valuation)
  | _, .existsF body, valuation => by
      simpa [translateFormula, Sat, Satisfies,
        extendValuation_eq_finCons] using
        (exists_congr fun value =>
          sat_translateFormula_iff body
            (extendValuation value valuation))

/-- Closed translation agrees with source semantics at every second-order
family. -/
theorem satSentence_translateFormula_iff
    {B : Type u} [BooleanAlgebra B] (family : Set (Set B))
    (formula : Formula 0) :
    SatSentence family (translateFormula formula) <->
      Satisfies formula (emptyValuation (B := B)) := by
  simpa [SatSentence, emptyValuation] using
    (sat_translateFormula_iff (family := family) formula
      (emptyValuation (B := B)))

/-- Every translated first-order sentence is invariant under a change of
second-order quantifier family. -/
theorem translatedSentence_family_invariant
    {B : Type u} [BooleanAlgebra B]
    (first second : Set (Set B)) (formula : Formula 0) :
    SatSentence first (translateFormula formula) <->
      SatSentence second (translateFormula formula) := by
  simpa [SatSentence] using
    (sat_soqf_congr (𝒮 := first) (𝒮' := second)
      (translateFormula formula) (translateFormula_soqf formula)
      Fin.elim0 Fin.elim0)

/-! ## A source-level sentence for atomlessness -/

/-- Classical implication in the negation/conjunction basis. -/
def implication {arity : Nat} (antecedent consequent : Formula arity) :
    Formula arity :=
  .negation (.conjunction antecedent (.negation consequent))

/-- Universal quantification in the negation/existential basis. -/
def forallF {arity : Nat} (body : Formula (arity + 1)) : Formula arity :=
  .negation (.existsF (.negation body))

def termEquation {arity : Nat}
    (left right : Term (Fin arity)) : Formula arity :=
  .equation ⟨left, right⟩

def nonzero {arity : Nat} (term : Term (Fin arity)) : Formula arity :=
  .negation (termEquation term .bottom)

def below {arity : Nat}
    (small large : Term (Fin arity)) : Formula arity :=
  termEquation (.meet small large) small

def strictNonzeroPart {arity : Nat}
    (small large : Term (Fin arity)) : Formula arity :=
  .conjunction (nonzero small)
    (.conjunction (below small large)
      (.negation (termEquation small large)))

private def outerElement : Term (Fin 1) := .atom 0
private def innerPart : Term (Fin 2) := .atom 0
private def innerElement : Term (Fin 2) := .atom (Fin.succ 0)

@[simp] private theorem eval_outerElement
    {B : Type u} [BooleanAlgebra B] (element : B) :
    outerElement.eval
      (extendValuation element (emptyValuation (B := B))) = element := by
  rfl

@[simp] private theorem eval_innerPart
    {B : Type u} [BooleanAlgebra B] (part element : B) :
    innerPart.eval
      (extendValuation part
        (extendValuation element (emptyValuation (B := B)))) = part := by
  rfl

@[simp] private theorem eval_innerElement
    {B : Type u} [BooleanAlgebra B] (part element : B) :
    innerElement.eval
      (extendValuation part
        (extendValuation element (emptyValuation (B := B)))) = element := by
  change
    (extendValuation element (emptyValuation (B := B))) 0 = element
  rfl

/-- Every nonzero element has a strictly smaller nonzero part. -/
def gunkSentence : Formula 0 :=
  forallF
    (implication (nonzero outerElement)
      (.existsF (strictNonzeroPart innerPart innerElement)))

theorem satisfies_implication_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (antecedent consequent : Formula arity)
    (valuation : Fin arity -> B) :
    Satisfies (implication antecedent consequent) valuation <->
      (Satisfies antecedent valuation ->
        Satisfies consequent valuation) := by
  classical
  simp [implication, Satisfies]

theorem satisfies_forallF_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (body : Formula (arity + 1)) (valuation : Fin arity -> B) :
    Satisfies (forallF body) valuation <->
      forall value : B,
        Satisfies body (extendValuation value valuation) := by
  classical
  simp [forallF, Satisfies]

theorem satisfies_nonzero_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (term : Term (Fin arity)) (valuation : Fin arity -> B) :
    Satisfies (nonzero term) valuation <-> term.eval valuation ≠ ⊥ := by
  rfl

theorem satisfies_strictNonzeroPart_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (small large : Term (Fin arity)) (valuation : Fin arity -> B) :
    Satisfies (strictNonzeroPart small large) valuation <->
      small.eval valuation ≠ ⊥ /\ small.eval valuation < large.eval valuation := by
  change
    (small.eval valuation ≠ ⊥ /\
      ((small.eval valuation ⊓ large.eval valuation = small.eval valuation) /\
        small.eval valuation ≠ large.eval valuation)) <-> _
  constructor
  · rintro ⟨smallNonzero, belowLarge, distinct⟩
    exact ⟨smallNonzero,
      lt_of_le_of_ne (inf_eq_left.mp belowLarge) distinct⟩
  · rintro ⟨smallNonzero, strictlyBelow⟩
    exact ⟨smallNonzero,
      inf_eq_left.mpr strictlyBelow.le, strictlyBelow.ne⟩

/-- The source sentence has exactly the established mereological
atomlessness semantics. -/
theorem satisfies_gunkSentence_iff_isGunky
    {B : Type u} [BooleanAlgebra B] :
    Satisfies gunkSentence (emptyValuation (B := B)) <-> IsGunky B := by
  rw [gunkSentence, satisfies_forallF_iff]
  constructor
  · intro allElements element elementNonzero
    have implicationAtElement :=
      (satisfies_implication_iff
        (nonzero outerElement)
        (.existsF (strictNonzeroPart innerPart innerElement))
        (extendValuation element (emptyValuation (B := B)))).mp
        (allElements element)
    have antecedent :
        Satisfies (nonzero outerElement)
          (extendValuation element (emptyValuation (B := B))) := by
      apply (satisfies_nonzero_iff outerElement _).mpr
      simpa only [eval_outerElement] using elementNonzero
    obtain ⟨part, partIsStrict⟩ := implicationAtElement antecedent
    have semanticPart :=
      (satisfies_strictNonzeroPart_iff innerPart innerElement
        (extendValuation part
          (extendValuation element (emptyValuation (B := B))))).mp
        partIsStrict
    exact ⟨part, by
      simpa only [eval_innerPart, eval_innerElement] using semanticPart⟩
  · intro gunky element
    apply (satisfies_implication_iff
      (nonzero outerElement)
      (.existsF (strictNonzeroPart innerPart innerElement))
      (extendValuation element (emptyValuation (B := B)))).mpr
    intro antecedent
    have elementNonzero : element ≠ ⊥ := by
      have semanticNonzero :=
        (satisfies_nonzero_iff outerElement
          (extendValuation element (emptyValuation (B := B)))).mp antecedent
      simpa only [eval_outerElement] using semanticNonzero
    obtain ⟨part, partNonzero, partBelow⟩ := gunky element elementNonzero
    refine ⟨part, ?_⟩
    apply (satisfies_strictNonzeroPart_iff innerPart innerElement
      (extendValuation part
        (extendValuation element (emptyValuation (B := B))))).mpr
    simpa only [eval_innerPart, eval_innerElement] using
      And.intro partNonzero partBelow

/-- The translated source atomlessness sentence and the manuscript's native
MSO atomlessness sentence agree at every second-order family. -/
theorem translated_gunkSentence_iff_gunkAx
    {B : Type u} [BooleanAlgebra B] (family : Set (Set B)) :
    SatSentence family (translateFormula gunkSentence) <->
      SatSentence family gunkAx :=
  (satSentence_translateFormula_iff family gunkSentence).trans
    (satisfies_gunkSentence_iff_isGunky.trans
      sat_gunkAx_iff_isGunky.symm)

/-- In every genuine Henkin model, the translated first-order gunk sentence
also agrees with the second-order free-ultrafilter sentence. -/
theorem translated_gunkSentence_iff_freeUFAx_henkin
    {B : Type u} [BooleanAlgebra B] (henkin : HenkinFamily B) :
    SatSentence henkin.family (translateFormula gunkSentence) <->
      SatSentence henkin.family freeUFAx :=
  (satSentence_translateFormula_iff henkin.family gunkSentence).trans
    (satisfies_gunkSentence_iff_isGunky.trans
      (sat_freeUFAx_iff_isGunky_henkin henkin).symm)

/-! ## Checker qualification and the second-order boundary -/

theorem gunkSentence_decides_true :
    decideClosed gunkSentence = true :=
  (decideClosed_eq_true_iff_satisfies isGunky_clopens_cantor
    gunkSentence).mpr
    (satisfies_gunkSentence_iff_isGunky.mpr isGunky_clopens_cantor)

theorem gunkSentence_replays :
    (contract.checker ()).check gunkSentence () = true := by
  change decideClosed gunkSentence = true
  exact gunkSentence_decides_true

/-- Direct finite checking is exact for the translated sentence in every
second-order family. -/
theorem checker_accepts_iff_mso_family
    (family : Set (Set CantorAlgebra)) (formula : Formula 0) :
    (contract.checker ()).check formula () = true <->
      SatSentence family (translateFormula formula) := by
  change decideClosed formula = true <-> _
  exact
    (decideClosed_eq_true_iff_satisfies isGunky_clopens_cantor formula).trans
      (satSentence_translateFormula_iff family formula).symm

/-- An accepted first-order gunk sentence warrants the manuscript's
second-order free-ultrafilter claim in the selected standard model. -/
theorem accepted_gunk_entails_standard_freeUFAx
    (accepted : (contract.checker ()).check gunkSentence () = true) :
    SatSentence (Set.univ : Set (Set CantorAlgebra)) freeUFAx := by
  have sourceMeaning :
      Satisfies gunkSentence
        (emptyValuation (B := CantorAlgebra)) :=
    (decideClosed_eq_true_iff_satisfies isGunky_clopens_cantor
      gunkSentence).mp accepted
  exact sat_freeUFAx_iff_isGunky.mpr
    (satisfies_gunkSentence_iff_isGunky.mp sourceMeaning)

/-- The family-sensitive existential-ultrafilter sentence is not uniformly
representable by any formula in the translated first-order language. -/
theorem no_firstOrder_formula_represents_existsUFAx :
    ¬ (∃ formula : Formula 0,
      ∀ family : Set (Set CantorAlgebra),
        SatSentence family (translateFormula formula) <->
          SatSentence family existsUFAx) := by
  rintro ⟨formula, represents⟩
  rcases sigma11_not_family_absolute with
    ⟨standardExists, family, familyDoesNotExist⟩
  have translatedStandard :
      SatSentence (Set.univ : Set (Set CantorAlgebra))
        (translateFormula formula) :=
    (represents Set.univ).mpr standardExists
  have translatedFamily :
      SatSentence family (translateFormula formula) :=
    (translatedSentence_family_invariant Set.univ family formula).mp
      translatedStandard
  exact familyDoesNotExist ((represents family).mp translatedFamily)

#print axioms eval_translateTerm
#print axioms translateFormula_soqf
#print axioms sat_translateFormula_iff
#print axioms translatedSentence_family_invariant
#print axioms satisfies_gunkSentence_iff_isGunky
#print axioms translated_gunkSentence_iff_freeUFAx_henkin
#print axioms checker_accepts_iff_mso_family
#print axioms accepted_gunk_entails_standard_freeUFAx
#print axioms no_firstOrder_formula_represents_existsUFAx

end Mettapedia.GSLT.LanguageDef.AtomlessBooleanMSOSemanticBridge
