import Foet.EthicsCore

set_option autoImplicit false

namespace Foet

universe u

/-
Virtue-style “aspect” judgments (Virtuous/Vicious/Neutral) and their translation
to/from `ValueJudgmentSentence`.

This is a minimal, type-checking-friendly bridge layer for the ESOWIKI “Virtue Ethics”
and “Target-Centered Virtue Ethics” pages: before modeling concrete virtues/agents,
we can already ensure the plumbing between paradigms is well-typed and semantics-respecting.
-/

/-- A coarse-grained virtue/vice/neutral tag, used by minimal virtue paradigms. -/
inductive VirtueAspect : Type
  | Virtuous
  | Vicious
  | Neutral
  deriving DecidableEq, Repr

def virtueAspectToMoralValue : VirtueAspect → MoralValueAttribute
  | .Virtuous => .MorallyGood
  | .Vicious => .MorallyBad
  | .Neutral => .MorallyPermissible

def moralValueToVirtueAspect : MoralValueAttribute → VirtueAspect
  | .MorallyGood => .Virtuous
  | .MorallyBad => .Vicious
  | .MorallyPermissible => .Neutral

theorem moralValueToVirtueAspect_virtueAspectToMoralValue (v : VirtueAspect) :
    moralValueToVirtueAspect (virtueAspectToMoralValue v) = v := by
  cases v <;> rfl

theorem virtueAspectToMoralValue_moralValueToVirtueAspect (m : MoralValueAttribute) :
    virtueAspectToMoralValue (moralValueToVirtueAspect m) = m := by
  cases m <;> rfl

/-- Minimal “virtue desire” sentence: a virtue-aspect attached to a formula. -/
structure VirtueDesireSentence (World : Type u) : Type (max u 1) where
  aspect : VirtueAspect
  formula : Formula World

/-- Minimal “virtue target” sentence: a virtue-aspect attached to a formula. -/
structure VirtueTargetSentence (World : Type u) : Type (max u 1) where
  aspect : VirtueAspect
  formula : Formula World

abbrev VirtueDesireTheory (World : Type u) : Type (max u 1) :=
  Theory (VirtueDesireSentence World)

abbrev VirtueTargetTheory (World : Type u) : Type (max u 1) :=
  Theory (VirtueTargetSentence World)

/-- ESOWIKI name: “Target-Centered Virtue Ethics Theory”. -/
abbrev TargetCenteredVirtueEthicsTheory (World : Type u) : Type (max u 1) :=
  VirtueTargetTheory World

/-- Translation: virtue-desire sentence → virtue-target sentence (field copy). -/
def VirtueDesireSentence.toTarget {World : Type u} (s : VirtueDesireSentence World) : VirtueTargetSentence World :=
  { aspect := s.aspect, formula := s.formula }

/-- Translation: virtue-target sentence → virtue-desire sentence (field copy). -/
def VirtueTargetSentence.toDesire {World : Type u} (s : VirtueTargetSentence World) : VirtueDesireSentence World :=
  { aspect := s.aspect, formula := s.formula }

theorem VirtueDesireSentence.toTarget_toDesire {World : Type u} (s : VirtueDesireSentence World) :
    s.toTarget.toDesire = s := by
  cases s <;> rfl

theorem VirtueTargetSentence.toDesire_toTarget {World : Type u} (s : VirtueTargetSentence World) :
    s.toDesire.toTarget = s := by
  cases s <;> rfl

/-- Translation: virtue-target sentence → value-judgment sentence (tag mapping only). -/
def VirtueTargetSentence.toValue {World : Type u} (s : VirtueTargetSentence World) : ValueJudgmentSentence World :=
  { tag := virtueAspectToMoralValue s.aspect, formula := s.formula }

/-- Translation: value-judgment sentence → virtue-target sentence (tag mapping only). -/
def ValueJudgmentSentence.toVirtueTarget {World : Type u} (s : ValueJudgmentSentence World) : VirtueTargetSentence World :=
  { aspect := moralValueToVirtueAspect s.tag, formula := s.formula }

theorem VirtueTargetSentence.toValue_toVirtueTarget {World : Type u} (s : VirtueTargetSentence World) :
    s.toValue.toVirtueTarget = s := by
  cases s with
  | mk aspect formula =>
    simp [VirtueTargetSentence.toValue, ValueJudgmentSentence.toVirtueTarget,
      moralValueToVirtueAspect_virtueAspectToMoralValue]

theorem ValueJudgmentSentence.toVirtueTarget_toValue {World : Type u} (s : ValueJudgmentSentence World) :
    s.toVirtueTarget.toValue = s := by
  cases s with
  | mk tag formula =>
    simp [VirtueTargetSentence.toValue, ValueJudgmentSentence.toVirtueTarget,
      virtueAspectToMoralValue_moralValueToVirtueAspect]

def VirtueTargetTheory.toValueJudgmentTheory {World : Type u} (T : VirtueTargetTheory World) : ValueJudgmentTheory World :=
  Theory.map VirtueTargetSentence.toValue T

def ValueJudgmentTheory.toVirtueTargetTheory {World : Type u} (T : ValueJudgmentTheory World) : VirtueTargetTheory World :=
  Theory.map ValueJudgmentSentence.toVirtueTarget T

def VirtueDesireTheory.toVirtueTargetTheory {World : Type u} (T : VirtueDesireTheory World) : VirtueTargetTheory World :=
  Theory.map VirtueDesireSentence.toTarget T

/-- A minimal semantics for virtue-desire sentences. -/
structure VirtueDesireSemantics (World : Type u) : Type (max u 1) where
  desires : VirtueAspect → Formula World → Formula World

/-- A minimal semantics for virtue-target sentences. -/
structure VirtueTargetSemantics (World : Type u) : Type (max u 1) where
  targets : VirtueAspect → Formula World → Formula World

def VirtueDesireSemantics.sat {World : Type u} (sem : VirtueDesireSemantics World) (w : World)
    (s : VirtueDesireSentence World) : Prop :=
  sem.desires s.aspect s.formula w

def VirtueTargetSemantics.sat {World : Type u} (sem : VirtueTargetSemantics World) (w : World)
    (s : VirtueTargetSentence World) : Prop :=
  sem.targets s.aspect s.formula w

def virtueDesireSemantics (World : Type u) (sem : VirtueDesireSemantics World) :
    Semantics (VirtueDesireSentence World) World :=
  ⟨fun w s => VirtueDesireSemantics.sat sem w s⟩

def virtueTargetSemantics (World : Type u) (sem : VirtueTargetSemantics World) :
    Semantics (VirtueTargetSentence World) World :=
  ⟨fun w s => VirtueTargetSemantics.sat sem w s⟩

/-- Satisfaction commutes with desire→target translation under semantic alignment. -/
theorem VirtueDesireSemantics.sat_iff_sat_toTarget {World : Type u}
    (semD : VirtueDesireSemantics World) (semT : VirtueTargetSemantics World)
    (h_align : ∀ a φ w, semD.desires a φ w ↔ semT.targets a φ w)
    (w : World) (s : VirtueDesireSentence World) :
    (virtueDesireSemantics World semD).Sat w s ↔ (virtueTargetSemantics World semT).Sat w s.toTarget := by
  exact h_align s.aspect s.formula w

/-- Satisfaction commutes with target→value translation under semantic alignment. -/
theorem VirtueTargetSemantics.sat_iff_sat_toValue {World : Type u}
    (semT : VirtueTargetSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semT.targets a φ w ↔ semV.morally (virtueAspectToMoralValue a) φ w)
    (w : World) (s : VirtueTargetSentence World) :
    (virtueTargetSemantics World semT).Sat w s ↔ (valueJudgmentSemantics World semV).Sat w s.toValue := by
  exact h_align s.aspect s.formula w

/-- Satisfaction commutes with value→target translation under semantic alignment. -/
theorem ValueJudgmentSentence.sat_iff_sat_toVirtueTarget {World : Type u}
    (semT : VirtueTargetSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semT.targets a φ w ↔ semV.morally (virtueAspectToMoralValue a) φ w)
    (w : World) (s : ValueJudgmentSentence World) :
    (valueJudgmentSemantics World semV).Sat w s ↔ (virtueTargetSemantics World semT).Sat w s.toVirtueTarget := by
  cases s with
  | mk tag formula =>
    have h :=
      h_align (moralValueToVirtueAspect tag) formula w
    simpa [ValueJudgmentSentence.toVirtueTarget, virtueTargetSemantics, VirtueTargetSemantics.sat,
      valueJudgmentSemantics, ValueSemantics.sat,
      virtueAspectToMoralValue_moralValueToVirtueAspect] using h.symm

/-- Entailment preservation/equivalence for the virtue-target → value-judgment translation. -/
theorem entails_virtueTarget_iff_entails_value {World : Type u}
    (semT : VirtueTargetSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semT.targets a φ w ↔ semV.morally (virtueAspectToMoralValue a) φ w)
    (T : VirtueTargetTheory World) (s : VirtueTargetSentence World) :
    Entails (virtueTargetSemantics World semT) T s ↔
      Entails (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) s.toValue := by
  simpa [VirtueTargetTheory.toValueJudgmentTheory] using
    (entails_map_iff
      (sem₁ := virtueTargetSemantics World semT)
      (sem₂ := valueJudgmentSemantics World semV)
      (f := VirtueTargetSentence.toValue)
      (h_sat := fun w s => VirtueTargetSemantics.sat_iff_sat_toValue (semT := semT) (semV := semV) h_align w s)
      (T := T) (s := s))

end Foet

