import Mettapedia.Languages.MeTTa.MeTTaZero
import Mettapedia.GSLT.Core.AnnotatedHorn

/-!
# The positive Horn fragment of MeTTa Zero

Positive Horn inference embeds into the public-query component of MeTTa Zero
when its derivation witnesses are stored as occurrences of ordinary atoms.
The embedding preserves occurrence identity, and counting those occurrences
is exactly the natural-number annotated Horn semantics.

This is deliberately a fragment theorem, not an identification of MeTTa Zero
with Horn logic.  The final section proves the missing direction: projecting a
unified reflective space to its non-rule facts cannot preserve observation of
rules as ordinary data.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZeroHornFragment

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.AnnotatedHorn
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

universe u

/-! ## A lawful occurrence-space model -/

/-- Exact matching for closed query patterns, together with the public
wildcard required to enumerate the unified space. -/
def occurrenceMatcher (pattern atom : Pattern) : Multiset Bindings :=
  match pattern with
  | .fvar name => {[(name, atom)]}
  | _ => if pattern = atom then {[]} else 0

/-- The concrete multiset instance of the query-first Zero model. -/
def occurrenceModel : Model where
  Space := Multiset Pattern
  contents := id
  matchAtoms := occurrenceMatcher
  groundApply := fun _ => 0

def occurrenceModelLawful : Lawful occurrenceModel where
  wildcard_match := by
    intro name atom
    rfl

/-- A wrapper separating function-free Horn facts from equation-shaped
reflective atoms. -/
def hornFact (atom : String) : Pattern :=
  .apply "horn-fact" [.apply atom []]

/-- Store one indistinguishable fact occurrence for every derivation witness. -/
def witnessSpace (atom : String) (witnesses : Multiset α) : Multiset Pattern :=
  witnesses.map fun _ => hornFact atom

/-- Exact public querying recovers the complete occurrence bag. -/
theorem query_witnessSpace (atom : String) (witnesses : Multiset α) :
    query occurrenceModel (witnessSpace atom witnesses)
        (hornFact atom) (hornFact atom) =
      witnessSpace atom witnesses := by
  induction witnesses using Multiset.induction_on with
  | empty => rfl
  | @cons witness witnesses inductionHypothesis =>
      have spaceCons :
          witnessSpace atom (witness ::ₘ witnesses) =
            hornFact atom ::ₘ witnessSpace atom witnesses := by
        simp [witnessSpace]
      have tail :
          ((witnessSpace atom witnesses).bind fun stored =>
          (occurrenceMatcher (hornFact atom) stored).map fun bindings =>
            applyBindings bindings (hornFact atom)) =
            witnessSpace atom witnesses := by
        simpa only [query, occurrenceModel, id_eq] using inductionHypothesis
      rw [spaceCons]
      dsimp only [query, occurrenceModel]
      simp only [id_eq]
      rw [Multiset.cons_bind]
      rw [tail]
      simp [occurrenceMatcher, hornFact, applyBindings]

/-- Counting the Zero query result is the natural-number annotated Horn step.
This is `card_stepBag` transported through the occurrence-space query. -/
theorem query_count_eq_stepCount (rules : List (DefiniteRule String))
    (assign : String → Multiset α) (atom : String) :
    Multiset.count (hornFact atom)
        (query occurrenceModel
          (witnessSpace atom (stepBag rules assign atom))
          (hornFact atom) (hornFact atom)) =
      stepCount rules (fun other => Multiset.card (assign other)) atom := by
  rw [query_witnessSpace]
  simp [witnessSpace, card_stepBag]

/-! ## Observation-indexed GSLT embedding -/

/-- The one-query GSLT exposed by a positive Horn step. -/
inductive HornStepTerm where
  | request
  | answer (occurrence : Nat)
deriving DecidableEq

/-- An occurrence is available exactly when the annotated Horn count contains
that copy. -/
inductive HornStep (rules : List (DefiniteRule String))
    (assign : String → Multiset α) (atom : String) :
    HornStepTerm → HornStepTerm → Prop where
  | found {occurrence}
      (copy : occurrence <
        stepCount rules (fun other => Multiset.card (assign other)) atom) :
      HornStep rules assign atom .request (.answer occurrence)

def hornStepGSLT (rules : List (DefiniteRule String))
    (assign : String → Multiset α) (atom : String) : GSLT where
  Term := HornStepTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := HornStep rules assign atom
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

private def hornSpace (rules : List (DefiniteRule String))
    (assign : String → Multiset α) (atom : String) : Multiset Pattern :=
  witnessSpace atom (stepBag rules assign atom)

private def embedTerm (rules : List (DefiniteRule String))
    (assign : String → Multiset α) (atom : String) :
    HornStepTerm → QueryTerm occurrenceModel
  | .request =>
      .request (hornSpace rules assign atom) (hornFact atom) (hornFact atom)
  | .answer occurrence =>
      .answer (hornSpace rules assign atom) (hornFact atom) (hornFact atom)
        occurrence (hornFact atom)

/-- The positive Horn step embeds faithfully into Zero's public query GSLT. -/
def hornQueryEmbedding (rules : List (DefiniteRule String))
    (assign : String → Multiset α) (atom : String) :
    GSLT.Embedding (hornStepGSLT rules assign atom)
      (queryGSLT occurrenceModel) where
  toFun := embedTerm rules assign atom
  injective := by
    intro source target equal
    cases source <;> cases target <;> cases equal <;> rfl
  equiv_iff := by
    intro source target
    change embedTerm rules assign atom source = embedTerm rules assign atom target ↔
      source = target
    constructor
    · intro equal
      cases source <;> cases target <;> cases equal <;> rfl
    · intro equal
      cases equal
      rfl
  step_iff := by
    intro source target
    cases source <;> cases target
    · constructor <;> intro step <;> cases step
    · change
        (queryGSLT occurrenceModel).Step
            (.request (hornSpace rules assign atom)
              (hornFact atom) (hornFact atom))
            (.answer (hornSpace rules assign atom)
              (hornFact atom) (hornFact atom) _ (hornFact atom)) ↔
          HornStep rules assign atom .request (.answer _)
      unfold hornSpace
      rw [queryGSLT_step_iff, query_count_eq_stepCount]
      constructor
      · exact HornStep.found
      · intro step
        cases step
        assumption
    · constructor <;> intro step <;> cases step
    · constructor <;> intro step <;> cases step

/-- The observation named by the Horn embedding: requests are unobserved and
answers retain the exact occurrence identifier. -/
def hornOccurrence : HornStepTerm → Option Nat
  | .request => none
  | .answer occurrence => some occurrence

def zeroQueryOccurrence : QueryTerm occurrenceModel → Option Nat
  | .request _ _ _ => none
  | .answer _ _ _ occurrence _ => some occurrence

/-- The Horn embedding explicitly preserves answer occurrences. -/
def hornQueryObservedEmbedding (rules : List (DefiniteRule String))
    (assign : String → Multiset α) (atom : String) :
    GSLT.Embedding.Observed (hornStepGSLT rules assign atom)
      (queryGSLT occurrenceModel) (Option Nat) where
  toEmbedding := hornQueryEmbedding rules assign atom
  observeSource := hornOccurrence
  observeTarget := zeroQueryOccurrence
  preserves := by
    intro term
    cases term <;> rfl

/-! ## The reflection boundary -/

/-- Horn-facing projection: retain non-equation facts and discard rule atoms. -/
def hornProjection (space : Multiset Pattern) : Multiset Pattern :=
  space.filter fun atom => (viewEquation? atom).isNone

/-- Reflective observation: retain exactly equation-shaped atoms as data. -/
def reflectedRules (space : Multiset Pattern) : Multiset Pattern :=
  space.filter fun atom => (viewEquation? atom).isSome

private def leftRule : Pattern :=
  .apply "=" [.apply "left" [], .apply "answer" []]

private def rightRule : Pattern :=
  .apply "=" [.apply "right" [], .apply "answer" []]

private theorem rules_have_same_horn_projection :
    hornProjection {leftRule} = hornProjection {rightRule} := by
  rfl

private theorem rules_have_distinct_reflection :
    reflectedRules {leftRule} ≠ reflectedRules {rightRule} := by
  have left : reflectedRules {leftRule} = {leftRule} := by rfl
  have right : reflectedRules {rightRule} = {rightRule} := by rfl
  rw [left, right]
  intro equal
  have counts := congrArg (Multiset.count leftRule) equal
  simp [leftRule, rightRule] at counts

private def reflectionFiber :
    NonTrivialFiber hornProjection reflectedRules where
  left := {leftRule}
  right := {rightRule}
  sameShadow := rules_have_same_horn_projection
  differentValue := rules_have_distinct_reflection

/-- A Horn projection cannot determine Zero's rule-as-data observation.
Answer preservation for the positive fragment therefore does not imply
reflection preservation for the whole language. -/
theorem reflection_does_not_factor_through_horn :
    ¬ Factors hornProjection reflectedRules :=
  reflectionFiber.not_factors

end Mettapedia.Languages.MeTTa.MeTTaZeroHornFragment
