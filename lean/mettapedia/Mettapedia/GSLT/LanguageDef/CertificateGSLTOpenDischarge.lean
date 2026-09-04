import Mettapedia.GSLT.LanguageDef.CertificateGSLTJudgmentAuthority

/-!
# Discharging open CertificateGSLT derivations

An open derivation is a proof plan whose ordered context records the
obligations that remain to be justified.  Discharge plugs a closed derivation
into every occurrence of that context and only then produces a closed proof.

This is the proof-theoretic boundary needed by assumption-sensitive
algorithms.  A search procedure may propose a conditional result, but source
provenance, a heuristic score, or the mere name of an assumption cannot close
it.  Closure requires a checked derivation for every ordered obligation.

The construction is inherited from the substitution algebra of open
derivations.  Its staged-discharge law is associativity of substitution, and
its model law says that syntactic discharge is interpreted by supplying the
semantic values of the discharged evidence.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

mutual

/-- Close a proof plan by supplying a checked proof for every ordered
obligation occurrence. -/
def OpenDerivation.discharge
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern}
    (derivation : OpenDerivation definition context goal)
    (evidence : DerivationList definition context) :
    Derivation definition goal :=
  (derivation.bind
    (OpenDerivationList.ofClosed (context := []) evidence)).close

/-- Discharge an ordered vector of proof plans against one checked evidence
environment. -/
def OpenDerivationList.discharge
    {definition : ValidatedCalculusLanguageDef}
    {context goals : List Pattern}
    (derivations : OpenDerivationList definition context goals)
    (evidence : DerivationList definition context) :
    DerivationList definition goals :=
  (derivations.bind
    (OpenDerivationList.ofClosed (context := []) evidence)).close

end

/-- The context of assumptions is the identity proof plan: discharging it
returns exactly the supplied occurrence-indexed evidence vector. -/
@[simp] theorem OpenDerivationList.discharge_assumptionEnvironment
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    (evidence : DerivationList definition context) :
    (assumptionEnvironment definition context).discharge evidence =
      evidence := by
  unfold OpenDerivationList.discharge
  rw [OpenDerivationList.assumptionEnvironment_bind]
  exact OpenDerivationList.close_ofClosed evidence

/-- Discharging in two stages agrees with first discharging the intermediate
evidence vector.  Hence proof planning can refine obligations incrementally
without changing the final certificate. -/
theorem OpenDerivation.discharge_bind
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext middleContext : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition sourceContext goal)
    (first : OpenDerivationList definition middleContext sourceContext)
    (second : DerivationList definition middleContext) :
    (derivation.bind first).discharge second =
      derivation.discharge (first.discharge second) := by
  unfold OpenDerivation.discharge OpenDerivationList.discharge
  rw [OpenDerivation.bind_assoc]
  simp only [OpenDerivationList.ofClosed_close]

/-- The staged-discharge law holds pointwise for an ordered vector of proof
plans. -/
theorem OpenDerivationList.discharge_bind
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext middleContext goals : List Pattern}
    (derivations : OpenDerivationList definition sourceContext goals)
    (first : OpenDerivationList definition middleContext sourceContext)
    (second : DerivationList definition middleContext) :
    (derivations.bind first).discharge second =
      derivations.discharge (first.discharge second) := by
  unfold OpenDerivationList.discharge
  rw [OpenDerivationList.bind_assoc]
  simp only [OpenDerivationList.ofClosed_close]

namespace Model

/-- Model semantics sends syntactic discharge to application of the open
proof's denotation to the denotations of its checked evidence. -/
theorem denote_discharge {object : Object} (model : Model object)
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation object.definition context goal)
    (evidence : DerivationList object.definition context) :
    model.denote (derivation.discharge evidence) =
      model.denoteOpen derivation (model.denoteList evidence) := by
  unfold OpenDerivation.discharge
  rw [denote_close, denoteOpen_bind, denoteOpenList_ofClosed]

/-- Pointwise semantic compatibility for discharge of an ordered vector. -/
theorem denoteList_discharge {object : Object} (model : Model object)
    {context goals : List Pattern}
    (derivations : OpenDerivationList object.definition context goals)
    (evidence : DerivationList object.definition context) :
    model.denoteList (derivations.discharge evidence) =
      model.denoteOpenList derivations (model.denoteList evidence) := by
  unfold OpenDerivationList.discharge
  rw [denoteList_close, denoteOpenList_bind, denoteOpenList_ofClosed]

end Model

/-! ## Lifting exact authorities to ordered obligation contexts -/

namespace ExactJudgmentEncoding

variable {Claim : Type*} {Meaning : Claim → Prop}
variable {definition : ValidatedCalculusLanguageDef}

/-- Pointwise completeness of an exact judgment encoding lifts to an ordered
context.  Repeated equal claims are supplied at repeated positions rather
than quotiented to a set. -/
theorem context_complete
    (adequacy : ExactJudgmentEncoding Claim Meaning definition) :
    ∀ (claims : List Claim),
      (∀ claim ∈ claims, Meaning claim) →
        Nonempty (DerivationList definition
          (claims.map adequacy.toJudgmentEncodingAdequacy.encode)) := by
  intro claims
  induction claims with
  | nil =>
      intro _
      exact ⟨.nil⟩
  | cons claim claims inductionHypothesis =>
      intro allMeaning
      obtain ⟨head⟩ := adequacy.derivation_complete claim
        (allMeaning claim (by simp))
      obtain ⟨tail⟩ := inductionHypothesis (by
        intro tailClaim member
        exact allMeaning tailClaim (by simp [member]))
      exact ⟨.cons head tail⟩

/-- Pointwise soundness of an exact judgment encoding lifts to an ordered
context of checked derivations. -/
theorem context_sound
    (adequacy : ExactJudgmentEncoding Claim Meaning definition) :
    ∀ (claims : List Claim),
      DerivationList definition
          (claims.map adequacy.toJudgmentEncodingAdequacy.encode) →
        ∀ claim ∈ claims, Meaning claim := by
  intro claims
  induction claims with
  | nil =>
      intro _ claim member
      simp at member
  | cons first rest inductionHypothesis =>
      intro evidence claim member
      cases evidence with
      | cons head tail =>
          rcases List.mem_cons.mp member with equality | tailMember
          · subst equality
            exact adequacy.derivation_sound _ ⟨head⟩
          · exact inductionHypothesis tail claim tailMember

/-- Exact single-judgment adequacy therefore extends to exact existence of an
ordered evidence environment. -/
theorem context_correspondence
    (adequacy : ExactJudgmentEncoding Claim Meaning definition)
    (claims : List Claim) :
    Nonempty (DerivationList definition
        (claims.map adequacy.toJudgmentEncodingAdequacy.encode)) ↔
      ∀ claim ∈ claims, Meaning claim := by
  constructor
  · rintro ⟨evidence⟩
    exact adequacy.context_sound claims evidence
  · exact adequacy.context_complete claims

/-- A proof plan closes whenever an exact authority establishes every one of
its ordered semantic side conditions.  This theorem does not manufacture
those conditions: `allMeaning` is precisely the remaining authority gate. -/
theorem discharge_of_all
    (adequacy : ExactJudgmentEncoding Claim Meaning definition)
    (claims : List Claim) {goal : Pattern}
    (plan : OpenDerivation definition
      (claims.map adequacy.toJudgmentEncodingAdequacy.encode) goal)
    (allMeaning : ∀ claim ∈ claims, Meaning claim) :
    Nonempty (Derivation definition goal) := by
  obtain ⟨evidence⟩ := adequacy.context_complete claims allMeaning
  exact ⟨plan.discharge evidence⟩

end ExactJudgmentEncoding

/-! ## Occurrence and closure canaries -/

namespace OpenDischargeCanary

variable {definition : ValidatedCalculusLanguageDef} {goal : Pattern}

/-- A one-hole plan remembers that its result is conditional on the sole
ordered obligation occurrence. -/
def oneHole : OpenDerivation definition [goal] goal :=
  .assumption ⟨0, by simp⟩

/-- Positive canary: checked evidence closes the corresponding one-hole plan
without changing that evidence's proof identity. -/
theorem oneHole_discharge (evidence : Derivation definition goal) :
    oneHole.discharge (.cons evidence .nil) = evidence := by
  simp [oneHole, OpenDerivation.discharge,
    OpenDerivationList.ofClosed, OpenDerivationList.get,
    OpenDerivation.bind]

/-- First occurrence of a duplicated, propositionally equal obligation. -/
def firstDuplicate : OpenDerivation definition [goal, goal] goal :=
  .assumption ⟨0, by simp⟩

/-- Second occurrence of the same judgment remains a separate proof hole. -/
def secondDuplicate : OpenDerivation definition [goal, goal] goal :=
  .assumption ⟨1, by simp⟩

/-- Negative canary: equal judgments at two context positions are not
identified as one assumption occurrence. -/
theorem duplicate_obligation_occurrences_are_distinct :
    firstDuplicate (definition := definition) (goal := goal) ≠
      secondDuplicate := by
  intro equality
  have indexEquality : (⟨0, by simp⟩ : Fin 2) = ⟨1, by simp⟩ := by
    injection equality
  have valueEquality : 0 = 1 := congrArg Fin.val indexEquality
  omega

end OpenDischargeCanary

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
