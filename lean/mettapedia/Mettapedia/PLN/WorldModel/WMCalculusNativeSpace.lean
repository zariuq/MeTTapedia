import Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
import Mettapedia.OSLF.Framework.WMCalculusNativeObservation

/-!
# Multiplicity-space observations in the native predicate fibration

The additive-space WM reading supplies genuine state-observation predicates
to the language's full presheaf fibration. Their membership tests are exactly
weighted candidate-list counts; operational rewrites transport these
predicates in every context. For the complete query type `List Atom`, singleton
candidate lists separate multiplicity spaces, so behavioral agreement is
literal equality in this particular reading.

Candidate lists are not claimed to be a matcher with variable bindings.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WMCalculusNativeSpace

open _root_.CategoryTheory
open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeObservation
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading

variable {Atom : Type}

private abbrev wmLanguage : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- A fixed candidate-list count is a native type on multiplicity spaces. -/
def spaceCountNativeType
    (world : String → MSpace Atom) (query : String → List Atom)
    (candidates : List Atom) (count : ℕ) :
    FullPresheafGrothendieckObj wmLanguage :=
  observationNativeType (additiveReading (Ev := ℕ) world query) .state
    (fun state => weightedAnswers state candidates = count)

/-- Membership of an encoded state term computes exactly the announced
candidate-list count. -/
theorem spaceCountNativeType_encoded_iff
    (world : String → MSpace Atom) (query : String → List Atom)
    (candidates : List Atom) (count : ℕ)
    (X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj wmLanguage))
    (term : WMTerm .state) :
    (ULift.up (Mettapedia.OSLF.Framework.WMCalculusEncoding.encodeWM term) :
      (languageProgramObj wmLanguage).obj X) ∈
      (spaceCountNativeType world query candidates count).fiber.obj X ↔
        weightedAnswers ((additiveReading (Ev := ℕ) world query).denote term)
          candidates = count := by
  exact observationPredicate_encoded_iff
    (additiveReading (Ev := ℕ) world query) .state
    (fun state => weightedAnswers state candidates = count) X term

/-- Every contextual operational rewrite transports fixed-count native
types. This is the dependent observation law used by the space consumer. -/
def spaceCountRewriteTransport
    (world : String → MSpace Atom) (query : String → List Atom)
    (candidates : List Atom) (count : ℕ)
    {Γ : languagePresheafObj wmLanguage}
    {p q : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p q) :
    FullPresheafGrothendieckHom wmLanguage
      (observationInContext (additiveReading (Ev := ℕ) world query) .state
        (fun state => weightedAnswers state candidates = count) Γ p)
      (observationInContext (additiveReading (Ev := ℕ) world query) .state
        (fun state => weightedAnswers state candidates = count) Γ q) :=
  observationRewriteTransport
    (additiveReading (Ev := ℕ) world query)
    (additiveReading_coreLaws world query)
    .state (fun state => weightedAnswers state candidates = count)
    (state_query_eq_invariant
      (additiveReading (Ev := ℕ) world query) candidates count)
    step

/-- Singleton candidate lists separate states: unlike the general WM
interface, this full-query space reading has no hidden state distinctions. -/
theorem spaceAgree_iff_eq
    (world : String → MSpace Atom) (query : String → List Atom)
    (first second : MSpace Atom) :
    (additiveReading (Ev := ℕ) world query).Agree .state first second ↔
      first = second := by
  constructor
  · intro agree
    funext atom
    have one := agree [atom]
    change weightedAnswers first [atom] = weightedAnswers second [atom] at one
    simpa [weightedAnswers] using one
  · intro equal
    subst second
    intro candidates
    rfl

/-- The tempting reading that treats a conjunctive pair count as an
additive WM extraction. It is deliberately a counterexample, not an
instance of the WM laws. -/
def pairCountCandidate : WMReading (MSpace Unit) (List Unit × List Unit) ℕ where
  revise := sUnion
  extract := fun state patterns => pairCount state patterns.1 patterns.2
  combine := Nat.add
  zero := 0
  world := fun _ _ => 0
  query := fun _ => ([], [])

/-- Even with semiring-valued evidence, a conjunctive count is not a
homomorphism from space union to addition: mixed-source pairs are lost. -/
theorem pairCountCandidate_not_coreLaws : ¬ pairCountCandidate.CoreLaws := by
  intro laws
  obtain ⟨left, right, first, second, crossTerms⟩ := pairCount_not_additive
  exact crossTerms (laws.extract_revise left right (first, second))

end Mettapedia.PLN.WorldModel.WMCalculusNativeSpace
