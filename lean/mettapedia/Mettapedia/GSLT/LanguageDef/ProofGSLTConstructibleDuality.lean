import Mettapedia.GSLT.LanguageDef.ProofGSLTRuleJoin

/-!
# Certificate duality: two evidence lanes and Belnap's four statuses

Constructible-duality and strong-negation logics treat verification and
refutation as independent constructive processes: evidence for and evidence
against are separately built objects, neither defined as the other's
absence.  This module formalizes the common **evidence-status fragment**:
two offered certificates are checked independently and summarized by the
four values of Belnap's `FOUR`.

The generic checker is neutral about negation, but can host this discipline.
A positive lane and a negative lane are two goals checked against offered
certificates; the four joint outcomes are Belnap's values:

* `established`  — the positive certificate checks;
* `refuted`      — the negative certificate checks;
* `conflicted`   — both check: conflict is *checked evidence on both
  sides*; it causes no unrelated conclusion unless a rule says so;
* `undetermined` — neither checks: absence of proof is not refutation.

The framework adds neither free contextual congruence nor an implicit
ex-falso principle.  The congruence half is the compiled counterexample
`congruence_is_not_free`; the ex-falso half is `no_explosion` in
`ProofGSLTConstructibleDualityCanary`, with `explosion_is_authorable`
showing one explicit ex-falso instance is authorable rather than a framework
law.

Both of Belnap's orders are defined: the knowledge/approximation order and
the truth order.  Evidence arrival realizes the first operationally:
supplying more accepted evidence only moves a verdict upward
(`fourOfLanes_knowledge_mono`) — evidence arrival is monotone in
knowledge, the anytime discipline of the budget layer extended to both
lanes.

This is not yet Patterson's full logic: no connectives, Kripke semantics,
judgment-level strong negation, or lane-swapping presentation interpretation
is claimed.  `FourVerdict.strongNegation` is only the corresponding operation
on the four evidence statuses.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Belnap's four values as joint verdicts of two certificate lanes. -/
inductive FourVerdict where
  | established
  | refuted
  | conflicted
  | undetermined
deriving Repr, DecidableEq

namespace FourVerdict

/-- Belnap's knowledge (approximation) order: `undetermined` below
everything, `conflicted` above everything, `established` and `refuted`
incomparable in between. -/
def knowledgeLE (lower upper : FourVerdict) : Bool :=
  lower = upper || lower = .undetermined || upper = .conflicted

@[simp] theorem knowledgeLE_refl (verdict : FourVerdict) :
    knowledgeLE verdict verdict = true := by
  simp [knowledgeLE]

theorem knowledgeLE_trans {first second third : FourVerdict}
    (lower : knowledgeLE first second = true)
    (upper : knowledgeLE second third = true) :
    knowledgeLE first third = true := by
  cases first <;> cases second <;> cases third <;> simp_all [knowledgeLE]

theorem knowledgeLE_antisymm {first second : FourVerdict}
    (forward : knowledgeLE first second = true)
    (backward : knowledgeLE second first = true) :
    first = second := by
  cases first <;> cases second <;> simp_all [knowledgeLE]

/-- Belnap's truth order: `refuted` below everything, `established` above
everything, and `undetermined` and `conflicted` incomparable between them. -/
def truthLE (lower upper : FourVerdict) : Bool :=
  lower = upper || lower = .refuted || upper = .established

@[simp] theorem truthLE_refl (verdict : FourVerdict) :
    truthLE verdict verdict = true := by
  simp [truthLE]

theorem truthLE_trans {first second third : FourVerdict}
    (lower : truthLE first second = true)
    (upper : truthLE second third = true) :
    truthLE first third = true := by
  cases first <;> cases second <;> cases third <;> simp_all [truthLE]

theorem truthLE_antisymm {first second : FourVerdict}
    (forward : truthLE first second = true)
    (backward : truthLE second first = true) :
    first = second := by
  cases first <;> cases second <;> simp_all [truthLE]

/-- Strong negation on evidence statuses swaps support and opposition.  It
does not by itself define a negation connective on object judgments. -/
def strongNegation : FourVerdict → FourVerdict
  | .established => .refuted
  | .refuted => .established
  | .conflicted => .conflicted
  | .undetermined => .undetermined

@[simp] theorem strongNegation_involutive (verdict : FourVerdict) :
    strongNegation (strongNegation verdict) = verdict := by
  cases verdict <;> rfl

/-- Status negation preserves the information order. -/
theorem strongNegation_knowledgeLE (first second : FourVerdict) :
    knowledgeLE (strongNegation first) (strongNegation second) =
      knowledgeLE first second := by
  cases first <;> cases second <;> rfl

/-- Status negation reverses the truth order. -/
theorem strongNegation_truthLE (first second : FourVerdict) :
    truthLE (strongNegation first) (strongNegation second) =
      truthLE second first := by
  cases first <;> cases second <;> rfl

/-- Positive and negative evidence are incomparable in the knowledge order. -/
theorem established_refuted_knowledge_incomparable :
    knowledgeLE .established .refuted = false ∧
      knowledgeLE .refuted .established = false := by
  decide

/-- Neither and both are incomparable in the truth order. -/
theorem undetermined_conflicted_truth_incomparable :
    truthLE .undetermined .conflicted = false ∧
      truthLE .conflicted .undetermined = false := by
  decide

end FourVerdict

/-- Joint verdict of the two lanes' acceptance bits. -/
def fourOfLanes (positiveAccepted negativeAccepted : Bool) : FourVerdict :=
  match positiveAccepted, negativeAccepted with
  | true, true => .conflicted
  | true, false => .established
  | false, true => .refuted
  | false, false => .undetermined

/-- The four statuses are exactly the product of positive and negative
acceptance bits. -/
def fourEquivLanes : FourVerdict ≃ Bool × Bool where
  toFun := fun
    | .established => (true, false)
    | .refuted => (false, true)
    | .conflicted => (true, true)
    | .undetermined => (false, false)
  invFun := fun lanes => fourOfLanes lanes.1 lanes.2
  left_inv verdict := by cases verdict <;> rfl
  right_inv lanes := by
    rcases lanes with ⟨positive, negative⟩
    cases positive <;> cases negative <;> rfl

/-- Evidence arrival is monotone in the knowledge order: acceptance bits
that only rise move the joint verdict only upward.  Belnap's approximation
order, realized by certificate arrival. -/
theorem fourOfLanes_knowledge_mono
    {positive positive' negative negative' : Bool}
    (positiveRises : positive = true → positive' = true)
    (negativeRises : negative = true → negative' = true) :
    FourVerdict.knowledgeLE (fourOfLanes positive negative)
      (fourOfLanes positive' negative') = true := by
  cases positive <;> cases positive' <;> cases negative <;>
    cases negative' <;> simp_all [fourOfLanes, FourVerdict.knowledgeLE]

/-- Whether an offered certificate is accepted for a goal; no certificate
is never acceptance. -/
def laneAccepted (presentation : ValidatedPresentation) (goal : Pattern) :
    Option RawProof → Bool
  | none => false
  | some proof => checkRaw presentation goal proof

/-- The four-valued verdict of a positive and a negative goal against
offered certificates. -/
def pairedVerdict (presentation : ValidatedPresentation)
    (positiveGoal negativeGoal : Pattern)
    (positiveCertificate negativeCertificate : Option RawProof) :
    FourVerdict :=
  fourOfLanes (laneAccepted presentation positiveGoal positiveCertificate)
    (laneAccepted presentation negativeGoal negativeCertificate)

private theorem laneAccepted_true {presentation : ValidatedPresentation}
    {goal : Pattern} {certificate : Option RawProof}
    (accepted : laneAccepted presentation goal certificate = true) :
    Nonempty (Derivation presentation goal) := by
  cases certificate with
  | none => simp [laneAccepted] at accepted
  | some proof => exact checkRaw_soundness accepted

/-- An established verdict certifies the positive judgment. -/
theorem pairedVerdict_established_sound
    {presentation : ValidatedPresentation}
    {positiveGoal negativeGoal : Pattern}
    {positiveCertificate negativeCertificate : Option RawProof}
    (established : pairedVerdict presentation positiveGoal negativeGoal
      positiveCertificate negativeCertificate = .established) :
    Nonempty (Derivation presentation positiveGoal) := by
  unfold pairedVerdict fourOfLanes at established
  cases acceptedPositive : laneAccepted presentation positiveGoal
      positiveCertificate with
  | true => exact laneAccepted_true acceptedPositive
  | false =>
      exfalso
      rw [acceptedPositive] at established
      cases acceptedNegative : laneAccepted presentation negativeGoal
          negativeCertificate <;>
        rw [acceptedNegative] at established <;> cases established

/-- A refuted verdict certifies the negative judgment. -/
theorem pairedVerdict_refuted_sound
    {presentation : ValidatedPresentation}
    {positiveGoal negativeGoal : Pattern}
    {positiveCertificate negativeCertificate : Option RawProof}
    (refuted : pairedVerdict presentation positiveGoal negativeGoal
      positiveCertificate negativeCertificate = .refuted) :
    Nonempty (Derivation presentation negativeGoal) := by
  unfold pairedVerdict fourOfLanes at refuted
  cases acceptedNegative : laneAccepted presentation negativeGoal
      negativeCertificate with
  | true => exact laneAccepted_true acceptedNegative
  | false =>
      exfalso
      rw [acceptedNegative] at refuted
      cases acceptedPositive : laneAccepted presentation positiveGoal
          positiveCertificate <;>
        rw [acceptedPositive] at refuted <;> cases refuted

/-- A conflicted verdict certifies *both* judgments: checked evidence on
both sides, held together without explosion. -/
theorem pairedVerdict_conflicted_sound
    {presentation : ValidatedPresentation}
    {positiveGoal negativeGoal : Pattern}
    {positiveCertificate negativeCertificate : Option RawProof}
    (conflicted : pairedVerdict presentation positiveGoal negativeGoal
      positiveCertificate negativeCertificate = .conflicted) :
    Nonempty (Derivation presentation positiveGoal) ∧
      Nonempty (Derivation presentation negativeGoal) := by
  unfold pairedVerdict fourOfLanes at conflicted
  cases acceptedPositive : laneAccepted presentation positiveGoal
      positiveCertificate <;>
    rw [acceptedPositive] at conflicted <;>
    cases acceptedNegative : laneAccepted presentation negativeGoal
        negativeCertificate <;>
      rw [acceptedNegative] at conflicted
  case true.true =>
      exact ⟨laneAccepted_true acceptedPositive,
        laneAccepted_true acceptedNegative⟩
  all_goals cases conflicted

/-- Erasures of two typed derivations produce a conflicted paired verdict.
Together with `pairedVerdict_conflicted_sound`, this pins the positive case in
both directions for explicitly supplied evidence. -/
theorem pairedVerdict_conflicted_complete
    {presentation : ValidatedPresentation}
    {positiveGoal negativeGoal : Pattern}
    (positive : Derivation presentation positiveGoal)
    (negative : Derivation presentation negativeGoal) :
    pairedVerdict presentation positiveGoal negativeGoal
      (some positive.erase) (some negative.erase) = .conflicted := by
  simp [pairedVerdict, laneAccepted, fourOfLanes, checkRaw_erase]

/-- A supplied positive derivation and an empty negative offer produce the
established status.  This is about offered evidence, not non-derivability of
the negative goal. -/
theorem pairedVerdict_established_of_derivation
    {presentation : ValidatedPresentation}
    {positiveGoal negativeGoal : Pattern}
    (positive : Derivation presentation positiveGoal) :
    pairedVerdict presentation positiveGoal negativeGoal
      (some positive.erase) none = .established := by
  simp [pairedVerdict, laneAccepted, fourOfLanes, checkRaw_erase]

/-- A supplied negative derivation and an empty positive offer produce the
refuted status.  This is about offered evidence, not non-derivability of the
positive goal. -/
theorem pairedVerdict_refuted_of_derivation
    {presentation : ValidatedPresentation}
    {positiveGoal negativeGoal : Pattern}
    (negative : Derivation presentation negativeGoal) :
    pairedVerdict presentation positiveGoal negativeGoal
      none (some negative.erase) = .refuted := by
  simp [pairedVerdict, laneAccepted, fourOfLanes, checkRaw_erase]

/-- Supplying certificates where none were offered moves the verdict only
upward in the knowledge order. -/
theorem pairedVerdict_knowledge_mono_from_empty
    {presentation : ValidatedPresentation}
    {positiveGoal negativeGoal : Pattern}
    (positiveCertificate negativeCertificate : Option RawProof) :
    FourVerdict.knowledgeLE
      (pairedVerdict presentation positiveGoal negativeGoal none none)
      (pairedVerdict presentation positiveGoal negativeGoal
        positiveCertificate negativeCertificate) = true := by
  apply fourOfLanes_knowledge_mono <;> simp [laneAccepted]

end Mettapedia.GSLT.LanguageDef.ProofGSLT
