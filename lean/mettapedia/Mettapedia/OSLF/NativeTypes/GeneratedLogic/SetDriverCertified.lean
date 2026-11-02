import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetDriver
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPastControls

/-!
# The set driver with proof terms

At a hereditary term, the set driver's questions in two fragments come with closed proof terms of the package
(`askSetCertified`): past modalities and quantifiers over a type with guarded fixed-point bodies
(`compilePastFixedVerdict`) or plain bodies (`compilePastVerdict`), and the regional types of the core profile
(`compileVerdict`). Both are stated as one family of sentences (`pastSentence`),
which on a regional type is its native type sentence (`pastSentence_eq_native`).

- **Decided**: on a context-free formula of either fragment the certificate is a proof or a refutation, never open
  (`askSetCertified_decides`).
- **Exact**: it is a proof exactly where the hereditary reading holds (`askSetCertified_proved_iff`).
- **It agrees with every answer of the set driver** (`askSetCertified_agrees`).
- Past types whose bodies have guarded fixed points are certified too (`compilePastFixedVerdict`).
- Controls: some set containing `0` has a member with a member, some set containing `0` is well-founded, no set has an
  endless descent, and `0` has no member with a member, each certified (`certified_controls`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The sentence of a regional type is its native type sentence.** -/
theorem pastSentence_eq_native {formula : Formula 0} (regional : formula.regional = true) (term : Pattern) :
    pastSentence formula term = nativeTypeSentence formula term := by
  cases formula <;> first | rfl | simp [Formula.regional] at regional

section Package

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseInterpretation (embed)

variable {L : Type} [LevelOrder L]

/-- **A certificate of the set driver**: a closed proof term of the proposition or of its negation, or the driver's
answer where no fragment with proof terms applies. -/
inductive SetCertificate (formula : Formula 0) (term : Pattern) where
  | proved (proofTerm : {proofTerm : CTm (Head L) 0 //
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (pastSentence formula term))))})
  | refuted (proofTerm : {proofTerm : CTm (Head L) 0 //
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (pastSentence formula term)))))})
  | uncertified (answer : Option Bool)

namespace SetCertificate

variable {formula : Formula 0} {term : Pattern}

/-- Whether the certificate proves the proposition. -/
def isProved : SetCertificate (L := L) formula term → Bool
  | .proved _ => true
  | _ => false

/-- Whether the certificate is left without a proof term. -/
def isUncertified : SetCertificate (L := L) formula term → Bool
  | .uncertified _ => true
  | _ => false

end SetCertificate

/-- A proof term of a regional type's native type sentence, as one of its sentence. -/
def regionalProved {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (found : {proofTerm : CTm (Head L) 0 //
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (nativeTypeSentence formula term))))}) :
    {proofTerm : CTm (Head L) 0 //
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (pastSentence formula term))))} :=
  ⟨found.1, by rw [pastSentence_eq_native regional]; exact found.2⟩

/-- A proof term of a regional type's refuted native type sentence, as one of its sentence's negation. -/
def regionalRefuted {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (found : {proofTerm : CTm (Head L) 0 //
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (nativeTypeSentence formula term)))))}) :
    {proofTerm : CTm (Head L) 0 //
      CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (pastSentence formula term)))))} :=
  ⟨found.1, by rw [pastSentence_eq_native regional]; exact found.2⟩

/-- **The set driver with proof terms**: at a hereditary term, a past type with a plain body or a regional type of the
core profile is proved or refuted by a closed proof term of the package; anything else keeps the driver's answer. -/
def askSetCertified (formula : Formula 0) (term : Pattern) : SetCertificate (L := L) formula term :=
  if hereditaryTerm : hereditary membership hfRule.category term = true then
    if fixed : formula.pastFixed = true then
      (compilePastFixedVerdict (L := L) fixed ((hereditary_iff _).mp hereditaryTerm)).elim .proved .refuted
    else if past : formula.pastPlain = true then
      (compilePastVerdict (L := L) past ((hereditary_iff _).mp hereditaryTerm)).elim .proved .refuted
    else if regional : formula.regionalWith false = true then
      (compileVerdict (L := L) regional ((hereditary_iff _).mp hereditaryTerm)).elim
        (fun found => .proved (regionalProved (Formula.regional_of_regionalWith _ regional) found))
        (fun found => .refuted (regionalRefuted (Formula.regional_of_regionalWith _ regional) found))
    else .uncertified (askHereditary formula term)
  else .uncertified (askHereditary formula term)

theorem compilePastVerdict_isLeft {formula : Formula 0} (past : formula.pastPlain = true) {term : Pattern}
    (holds : IsHF term) : (compilePastVerdict (L := L) past holds).isLeft = (compilePastSentence past holds).isLeft := by
  unfold compilePastVerdict
  cases compilePastSentence past holds <;> rfl

theorem compileVerdict_isLeft {formula : Formula 0} (regional : formula.regionalWith false = true) {term : Pattern}
    (holds : IsHF term) : (compileVerdict (L := L) regional holds).isLeft = (compileSentence regional holds).isLeft := by
  unfold compileVerdict
  cases compileSentence regional holds <;> rfl

theorem isProved_elim {formula : Formula 0} {term : Pattern} {α β : Type}
    (proved : α → SetCertificate (L := L) formula term) (refuted : β → SetCertificate (L := L) formula term)
    (provedIs : ∀ a, (proved a).isProved = true) (refutedIs : ∀ b, (refuted b).isProved = false) :
    ∀ found : α ⊕ β, (found.elim proved refuted).isProved = found.isLeft
  | .inl a => provedIs a
  | .inr b => refutedIs b

theorem isUncertified_elim {formula : Formula 0} {term : Pattern} {α β : Type}
    (proved : α → SetCertificate (L := L) formula term) (refuted : β → SetCertificate (L := L) formula term)
    (provedIs : ∀ a, (proved a).isUncertified = false) (refutedIs : ∀ b, (refuted b).isUncertified = false) :
    ∀ found : α ⊕ β, (found.elim proved refuted).isUncertified = false
  | .inl a => provedIs a
  | .inr b => refutedIs b

/-- **Decided**: a context-free past type with a plain body, or regional type of the core profile, at a hereditary
term gets a proof term of its proposition or of its negation. -/
theorem askSetCertified_decides {formula : Formula 0} {term : Pattern} (holds : IsHF term)
    (fragment : formula.pastFixed = true ∨ formula.pastPlain = true ∨ formula.regionalWith false = true) :
    (askSetCertified (L := L) formula term).isUncertified = false := by
  have hereditaryTerm : hereditary membership hfRule.category term = true := (hereditary_iff _).mpr holds
  unfold askSetCertified
  rw [dif_pos hereditaryTerm]
  by_cases fixed : formula.pastFixed = true
  · rw [dif_pos fixed]
    exact isUncertified_elim _ _ (fun _ => rfl) (fun _ => rfl) _
  · rw [dif_neg fixed]
    by_cases past : formula.pastPlain = true
    · rw [dif_pos past]
      exact isUncertified_elim _ _ (fun _ => rfl) (fun _ => rfl) _
    · rw [dif_neg past, dif_pos ((fragment.resolve_left fixed).resolve_left past)]
      exact isUncertified_elim _ _ (fun _ => rfl) (fun _ => rfl) _

/-- **Exact**: the certificate proves the proposition exactly where the hereditary reading holds. -/
theorem askSetCertified_proved_iff {formula : Formula 0} {term : Pattern} (holds : IsHF term)
    (free : formula.contextFree = true)
    (fragment : formula.pastFixed = true ∨ formula.pastPlain = true ∨ formula.regionalWith false = true) :
    (askSetCertified (L := L) formula term).isProved = true ↔ HFNative.sat Env.closed formula ⟨term, holds⟩ := by
  have hereditaryTerm : hereditary membership hfRule.category term = true := (hereditary_iff _).mpr holds
  unfold askSetCertified
  rw [dif_pos hereditaryTerm]
  by_cases fixed : formula.pastFixed = true
  · rw [dif_pos fixed, isProved_elim _ _ (fun _ => rfl) (fun _ => rfl), compilePastFixedVerdict_isLeft,
      compilePastFixedSentence_isLeft_iff, sat_iff_hfSets formula free]
    rfl
  rw [dif_neg fixed]
  by_cases past : formula.pastPlain = true
  · rw [dif_pos past, isProved_elim _ _ (fun _ => rfl) (fun _ => rfl), compilePastVerdict_isLeft,
      compilePastSentence_isLeft_iff, sat_iff_hfSets formula free]
    rfl
  · have regional := (fragment.resolve_left fixed).resolve_left past
    rw [dif_neg past, dif_pos regional, isProved_elim _ _ (fun _ => rfl) (fun _ => rfl), compileVerdict_isLeft,
      compileSentence_isLeft_iff, hereditary_iff_membership (Formula.forward_of_regional formula
        (Formula.regional_of_regionalWith _ regional)) holds]

/-- **The certificate agrees with every answer of the set driver** in either fragment. -/
theorem askSetCertified_agrees {formula : Formula 0} {term : Pattern} {answer : Bool}
    (answered : askHereditary formula term = some answer)
    (fragment : formula.pastFixed = true ∨ formula.pastPlain = true ∨ formula.regionalWith false = true) :
    (askSetCertified (L := L) formula term).isProved = answer := by
  have free : formula.contextFree = true := by
    unfold askHereditary at answered
    split at answered
    · rename_i fit
      exact (Bool.and_eq_true_iff.mp fit).2
    · cases answered
  obtain ⟨holds, exact⟩ := askHereditary_sound answered
  have proved := askSetCertified_proved_iff (L := L) holds free fragment
  cases answer <;> cases certified : (askSetCertified (L := L) formula term).isProved <;> simp_all

/-- **Controls**: some set containing `0` has a member with a member, and `0` has no member with a member, each with
its proof term. -/
theorem certified_controls :
    (askSetCertified (L := L) (.sometimeBefore .any deep) zero).isProved = true ∧
      (askSetCertified (L := L) (.sometimeBefore .any fixWellFounded) zero).isProved = true ∧
      (askSetCertified (L := L) (.someOf (.base "Set") fixEndlessDescent) zero).isProved = false ∧
      (askSetCertified (L := L) deep zero).isProved = false ∧
      (askSetCertified (L := L) deep zero).isUncertified = false := by
  have deepFixed : (Formula.sometimeBefore .any deep).pastFixed = true := by decide +kernel
  refine ⟨(askSetCertified_proved_iff zero_hf rfl (Or.inl deepFixed)).mpr ?_,
    (askSetCertified_proved_iff zero_hf rfl (Or.inl admitted_controls.1)).mpr ?_, ?_, ?_,
    askSetCertified_decides zero_hf (Or.inr (Or.inr rfl))⟩
  · exact (sat_iff_hfSets _ rfl ⟨zero, zero_hf⟩).mpr ((pastVerdict_iff rfl zero_hf).mp verdict_zero_deep)
  · exact (sat_iff_hfSets _ rfl ⟨zero, zero_hf⟩).mpr
      ((pastFixedVerdict_iff admitted_controls.1 zero_hf).mp fixed_verdict_zero_wellFounded)
  · cases certified : (askSetCertified (L := L) (.someOf (.base "Set") fixEndlessDescent) zero).isProved
    · rfl
    · exact absurd ((sat_iff_hfSets _ rfl ⟨zero, zero_hf⟩).mp
        ((askSetCertified_proved_iff zero_hf rfl (Or.inl admitted_controls.2.2.2.2.2.1)).mp certified)) no_illFounded_set
  · cases certified : (askSetCertified (L := L) deep zero).isProved
    · rfl
    · have holds := (sat_iff_hfSets _ rfl ⟨zero, zero_hf⟩).mp
        ((askSetCertified_proved_iff zero_hf rfl (Or.inr (Or.inr rfl))).mp certified)
      obtain ⟨_, ⟨_, member⟩, _⟩ := holds
      change _ ∈ zfOf (set []) at member
      simp [zfOf_set, mem_zfOfList] at member

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
