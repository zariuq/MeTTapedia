import Mettapedia.Ethics.StructuredSentence
import Mettapedia.Ethics.UtilitarianToValue
import Mettapedia.Ethics.VirtueToValue

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u v w

/-- Semantics for unmodalized formulas. -/
def formulaSemantics (World : Type u) : Semantics (Formula World) World :=
  ⟨fun w φ => φ w⟩

def sumSemantics {A : Type u} {B : Type v} {M : Type w}
    (semA : Semantics A M) (semB : Semantics B M) : Semantics (Sum A B) M :=
  ⟨fun m s =>
    match s with
    | .inl a => semA.Sat m a
    | .inr b => semB.Sat m b⟩

abbrev StructuredImperativeAtom (World : Type u) : Type (max u 1) :=
  Sum (DeonticSentence World) (Formula World)

abbrev StructuredValueAtom (World : Type u) : Type (max u 1) :=
  Sum (ValueJudgmentSentence World) (Formula World)

def imperativeToValueAtom {World : Type u} :
    StructuredImperativeAtom World → StructuredValueAtom World
  | .inl s => .inl s.toValue
  | .inr φ => .inr φ

theorem sat_imperativeToValueAtom_iff {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (w : World) (a : StructuredImperativeAtom World) :
    (sumSemantics (deonticSemantics World semD) (formulaSemantics World)).Sat w a ↔
      (sumSemantics (valueJudgmentSemantics World semV) (formulaSemantics World)).Sat w
        (imperativeToValueAtom a) := by
  cases a with
  | inl s =>
      simpa [sumSemantics, imperativeToValueAtom] using
        (DeonticSemantics.sat_iff_sat_toValue (semD := semD) (semV := semV) h_align w s)
  | inr φ =>
      rfl

theorem sat_structuredImperative_iff_sat_structuredValue {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (w : World) (s : StructuredSentence World (StructuredImperativeAtom World)) :
    (StructuredSentence.semantics (World := World)
        (sumSemantics (deonticSemantics World semD) (formulaSemantics World))).Sat w s ↔
      (StructuredSentence.semantics (World := World)
        (sumSemantics (valueJudgmentSemantics World semV) (formulaSemantics World))).Sat w
        (StructuredSentence.map imperativeToValueAtom s) := by
  simpa using
    (StructuredSentence.sat_map_iff
      (World := World)
      (sem₁ := sumSemantics (deonticSemantics World semD) (formulaSemantics World))
      (sem₂ := sumSemantics (valueJudgmentSemantics World semV) (formulaSemantics World))
      (f := imperativeToValueAtom)
      (h_sat := sat_imperativeToValueAtom_iff (semD := semD) (semV := semV) h_align)
      (m := w) (s := s))

theorem entails_structuredImperative_iff_entails_structuredValue {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (T : Theory (StructuredSentence World (StructuredImperativeAtom World)))
    (s : StructuredSentence World (StructuredImperativeAtom World)) :
    Entails
        (StructuredSentence.semantics (World := World)
          (sumSemantics (deonticSemantics World semD) (formulaSemantics World)))
        T s ↔
      Entails
        (StructuredSentence.semantics (World := World)
          (sumSemantics (valueJudgmentSemantics World semV) (formulaSemantics World)))
        (Theory.map (StructuredSentence.map imperativeToValueAtom) T)
        (StructuredSentence.map imperativeToValueAtom s) := by
  simpa using
    (StructuredSentence.entails_map_iff
      (World := World)
      (sem₁ := sumSemantics (deonticSemantics World semD) (formulaSemantics World))
      (sem₂ := sumSemantics (valueJudgmentSemantics World semV) (formulaSemantics World))
      (f := imperativeToValueAtom)
      (h_sat := sat_imperativeToValueAtom_iff (semD := semD) (semV := semV) h_align)
      (T := T) (s := s))

abbrev StructuredUtilityAtom (World : Type u) : Type (max u 1) :=
  Sum (UtilityAssignmentSentence World) (Formula World)

def utilitarianToValueAtom {World : Type u} :
    StructuredUtilityAtom World → StructuredValueAtom World
  | .inl s => .inl s.toValue
  | .inr φ => .inr φ

theorem sat_utilitarianToValueAtom_iff {World : Type u}
    (semU : UtilityAssignmentSemantics World) (w : World) (a : StructuredUtilityAtom World) :
    (sumSemantics (utilityAssignmentSemantics World semU) (formulaSemantics World)).Sat w a ↔
      (sumSemantics
          (valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
          (formulaSemantics World)).Sat w
        (utilitarianToValueAtom a) := by
  cases a with
  | inl s =>
      simpa [sumSemantics, utilitarianToValueAtom] using
        (UtilityAssignmentSemantics.sat_iff_sat_toValue (semU := semU) w s)
  | inr φ =>
      rfl

theorem sat_structuredUtilitarian_iff_sat_structuredValue {World : Type u}
    (semU : UtilityAssignmentSemantics World) (w : World)
    (s : StructuredSentence World (StructuredUtilityAtom World)) :
    (StructuredSentence.semantics (World := World)
        (sumSemantics (utilityAssignmentSemantics World semU) (formulaSemantics World))).Sat w s ↔
      (StructuredSentence.semantics (World := World)
        (sumSemantics
          (valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
          (formulaSemantics World))).Sat w
        (StructuredSentence.map utilitarianToValueAtom s) := by
  simpa using
    (StructuredSentence.sat_map_iff
      (World := World)
      (sem₁ := sumSemantics (utilityAssignmentSemantics World semU) (formulaSemantics World))
      (sem₂ := sumSemantics
        (valueJudgmentSemantics World (valueSemanticsOfUtility World semU))
        (formulaSemantics World))
      (f := utilitarianToValueAtom)
      (h_sat := sat_utilitarianToValueAtom_iff (World := World) (semU := semU))
      (m := w) (s := s))

abbrev StructuredVirtueTargetAtom (World : Type u) : Type (max u 1) :=
  Sum (VirtueTargetSentence World) (Formula World)

def virtueTargetToValueAtom {World : Type u} :
    StructuredVirtueTargetAtom World → StructuredValueAtom World
  | .inl s => .inl s.toValue
  | .inr φ => .inr φ

theorem sat_virtueTargetToValueAtom_iff {World : Type u}
    (semT : VirtueTargetSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semT.targets a φ w ↔ semV.morally (virtueAspectToMoralValue a) φ w)
    (w : World) (a : StructuredVirtueTargetAtom World) :
    (sumSemantics (virtueTargetSemantics World semT) (formulaSemantics World)).Sat w a ↔
      (sumSemantics (valueJudgmentSemantics World semV) (formulaSemantics World)).Sat w
        (virtueTargetToValueAtom a) := by
  cases a with
  | inl s =>
      simpa [sumSemantics, virtueTargetToValueAtom] using
        (VirtueTargetSemantics.sat_iff_sat_toValue (semT := semT) (semV := semV) h_align w s)
  | inr φ =>
      rfl

theorem sat_structuredVirtueTarget_iff_sat_structuredValue {World : Type u}
    (semT : VirtueTargetSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semT.targets a φ w ↔ semV.morally (virtueAspectToMoralValue a) φ w)
    (w : World) (s : StructuredSentence World (StructuredVirtueTargetAtom World)) :
    (StructuredSentence.semantics (World := World)
        (sumSemantics (virtueTargetSemantics World semT) (formulaSemantics World))).Sat w s ↔
      (StructuredSentence.semantics (World := World)
        (sumSemantics (valueJudgmentSemantics World semV) (formulaSemantics World))).Sat w
        (StructuredSentence.map virtueTargetToValueAtom s) := by
  simpa using
    (StructuredSentence.sat_map_iff
      (World := World)
      (sem₁ := sumSemantics (virtueTargetSemantics World semT) (formulaSemantics World))
      (sem₂ := sumSemantics (valueJudgmentSemantics World semV) (formulaSemantics World))
      (f := virtueTargetToValueAtom)
      (h_sat := sat_virtueTargetToValueAtom_iff (World := World) (semT := semT) (semV := semV) h_align)
      (m := w) (s := s))

end Mettapedia.Ethics
