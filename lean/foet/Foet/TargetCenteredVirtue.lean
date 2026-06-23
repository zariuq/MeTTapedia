import Foet.Translation
import Foet.SumoEthicsSig
import Foet.Paradigms
import Foet.UtilitarianToValue

set_option autoImplicit false

namespace Foet

universe u v

/-
Target-centered virtue ethics (TCVE) with *explicit* virtue attributes.

This is closer to the FOET KIF fragments:
  - `virtueTarget ?VIRTUE ?FORM`
  - `∀AGENT [ attribute(AGENT,VIRTUE) ⇒ desires(AGENT,FORM) ]`

Key point: some translations *introduce* a virtue existentially. We represent the
translation as a relation `R : S₁ → S₂ → Prop` and keep the existential vs
witness-carrying choice external via `Translates` vs `Witnessed`.
-/

/-! ## Sentence fragments -/

/-- KIF: `virtueTarget ?VIRTUE ?FORM`. -/
structure SimpleVirtueTargetSentence (World : Type u) (Virtue : Type v) : Type (max u v) where
  virtue : Virtue
  formula : Formula World

/-- KIF: `∀AGENT [ attribute(AGENT,VIRTUE) ⇒ desires(AGENT,FORM) ]` (typed view). -/
structure MinimalVirtueDesireSentence (World : Type u) (Virtue : Type v) : Type (max u v) where
  virtue : Virtue
  formula : Formula World

abbrev SimpleVirtueTargetTheory (World : Type u) (Virtue : Type v) : Type (max u v) :=
  Theory (SimpleVirtueTargetSentence World Virtue)

abbrev MinimalVirtueDesireTheory (World : Type u) (Virtue : Type v) : Type (max u v) :=
  Theory (MinimalVirtueDesireSentence World Virtue)

/-- ESOWIKI name: “Target-Centered Virtue Ethics Theory” (virtue-attribute version). -/
abbrev TargetCenteredVirtueEthicsTheoryAttr (World : Type u) (Virtue : Type v) : Type (max u v) :=
  SimpleVirtueTargetTheory World Virtue

/-! ## Deterministic translations (functions) -/

/-- KIF: `SimpleVirtueDesireToTargetSentenceFn` (typed, field-copy). -/
def MinimalVirtueDesireSentence.toTarget {World : Type u} {Virtue : Type v}
    (s : MinimalVirtueDesireSentence World Virtue) : SimpleVirtueTargetSentence World Virtue :=
  { virtue := s.virtue, formula := s.formula }

/-- KIF: `TargetSentenceToSimpleVirtueDesireFn` (typed, field-copy). -/
def SimpleVirtueTargetSentence.toDesire {World : Type u} {Virtue : Type v}
    (s : SimpleVirtueTargetSentence World Virtue) : MinimalVirtueDesireSentence World Virtue :=
  { virtue := s.virtue, formula := s.formula }

theorem MinimalVirtueDesireSentence.toTarget_toDesire {World : Type u} {Virtue : Type v}
    (s : MinimalVirtueDesireSentence World Virtue) :
    s.toTarget.toDesire = s := by
  cases s <;> rfl

theorem SimpleVirtueTargetSentence.toDesire_toTarget {World : Type u} {Virtue : Type v}
    (s : SimpleVirtueTargetSentence World Virtue) :
    s.toDesire.toTarget = s := by
  cases s <;> rfl

/-- KIF: `TargetSentenceToValueJudgmentSentenceFn` (“the target is morally good. Period.”). -/
def SimpleVirtueTargetSentence.toValue {World : Type u} {Virtue : Type v}
    (s : SimpleVirtueTargetSentence World Virtue) : ValueJudgmentSentence World :=
  { tag := .MorallyGood, formula := s.formula }

def MinimalVirtueDesireTheory.toTargetTheory {World : Type u} {Virtue : Type v}
    (T : MinimalVirtueDesireTheory World Virtue) : SimpleVirtueTargetTheory World Virtue :=
  Theory.map (fun s => MinimalVirtueDesireSentence.toTarget (World := World) (Virtue := Virtue) s) T

def SimpleVirtueTargetTheory.toValueJudgmentTheory {World : Type u} {Virtue : Type v}
    (T : SimpleVirtueTargetTheory World Virtue) : ValueJudgmentTheory World :=
  Theory.map (fun s => SimpleVirtueTargetSentence.toValue (World := World) (Virtue := Virtue) s) T

/-- KIF: `VirtueDesireToImperativeSentenceFn` (virtue-desire ⇒ obligation). -/
def MinimalVirtueDesireSentence.toImperative {World : Type u} {Virtue : Type v}
    (s : MinimalVirtueDesireSentence World Virtue) : DeonticSentence World :=
  { tag := .Obligation, formula := s.formula }

def MinimalVirtueDesireTheory.toImperativeTheory {World : Type u} {Virtue : Type v}
    (T : MinimalVirtueDesireTheory World Virtue) : DeontologicalImperativeTheory World :=
  Theory.map (fun s => MinimalVirtueDesireSentence.toImperative (World := World) (Virtue := Virtue) s) T

/-! ## Semantics -/

structure TCVEVirtueTargetSemantics (World : Type u) (Virtue : Type v) : Type (max u v 1) where
  targets : Virtue → Formula World → Formula World

structure TCVEVirtueDesireSemantics (World : Type u) (Virtue : Type v) : Type (max u v 1) where
  desires : Virtue → Formula World → Formula World

def TCVEVirtueTargetSemantics.sat {World : Type u} {Virtue : Type v}
    (sem : TCVEVirtueTargetSemantics World Virtue) (w : World)
    (s : SimpleVirtueTargetSentence World Virtue) : Prop :=
  sem.targets s.virtue s.formula w

def TCVEVirtueDesireSemantics.sat {World : Type u} {Virtue : Type v}
    (sem : TCVEVirtueDesireSemantics World Virtue) (w : World)
    (s : MinimalVirtueDesireSentence World Virtue) : Prop :=
  sem.desires s.virtue s.formula w

def tcveVirtueTargetSemantics (World : Type u) (Virtue : Type v)
    (sem : TCVEVirtueTargetSemantics World Virtue) :
    Semantics (SimpleVirtueTargetSentence World Virtue) World :=
  ⟨fun w s => TCVEVirtueTargetSemantics.sat sem w s⟩

def tcveVirtueDesireSemantics (World : Type u) (Virtue : Type v)
    (sem : TCVEVirtueDesireSemantics World Virtue) :
    Semantics (MinimalVirtueDesireSentence World Virtue) World :=
  ⟨fun w s => TCVEVirtueDesireSemantics.sat sem w s⟩

def MinimalVirtueDesireSentence.toFormula {World : Type u} (sig : SumoEthicsSig World)
    (s : MinimalVirtueDesireSentence World sig.VirtueAttribute) : Formula World :=
  sig.virtueDesireFormula s.virtue s.formula

/-- A canonical evaluator for minimal virtue-desire sentences from a `SumoEthicsSig`. -/
def tcveVirtueDesireSemanticsOfSig {World : Type u} (sig : SumoEthicsSig World) :
    Semantics (MinimalVirtueDesireSentence World sig.VirtueAttribute) World :=
  ⟨fun w s => (s.toFormula sig) w⟩

/-! ## Satisfaction/entailment preservation for deterministic directions -/

theorem TCVEVirtueDesireSemantics.sat_iff_sat_toTarget {World : Type u} {Virtue : Type v}
    (semD : TCVEVirtueDesireSemantics World Virtue) (semT : TCVEVirtueTargetSemantics World Virtue)
    (h_align : ∀ v φ w, semD.desires v φ w ↔ semT.targets v φ w)
    (w : World) (s : MinimalVirtueDesireSentence World Virtue) :
    (tcveVirtueDesireSemantics World Virtue semD).Sat w s ↔
      (tcveVirtueTargetSemantics World Virtue semT).Sat w s.toTarget := by
  exact h_align s.virtue s.formula w

theorem entails_tcveDesire_iff_entails_tcveTarget {World : Type u} {Virtue : Type v}
    (semD : TCVEVirtueDesireSemantics World Virtue) (semT : TCVEVirtueTargetSemantics World Virtue)
    (h_align : ∀ v φ w, semD.desires v φ w ↔ semT.targets v φ w)
    (T : MinimalVirtueDesireTheory World Virtue) (s : MinimalVirtueDesireSentence World Virtue) :
    Entails (tcveVirtueDesireSemantics World Virtue semD) T s ↔
      Entails (tcveVirtueTargetSemantics World Virtue semT) (T.toTargetTheory) s.toTarget := by
  simpa [MinimalVirtueDesireTheory.toTargetTheory] using
    (entails_map_iff
      (sem₁ := tcveVirtueDesireSemantics World Virtue semD)
      (sem₂ := tcveVirtueTargetSemantics World Virtue semT)
      (f := fun s => MinimalVirtueDesireSentence.toTarget (World := World) (Virtue := Virtue) s)
      (h_sat := fun w s => TCVEVirtueDesireSemantics.sat_iff_sat_toTarget
        (semD := semD) (semT := semT) h_align w s)
      (T := T) (s := s))

theorem TCVEVirtueDesireSemantics.sat_iff_sat_toImperative {World : Type u} {Virtue : Type v}
    (semD : TCVEVirtueDesireSemantics World Virtue) (semI : DeonticSemantics World)
    (h_align : ∀ v φ w, semD.desires v φ w ↔ semI.deontic .Obligation φ w)
    (w : World) (s : MinimalVirtueDesireSentence World Virtue) :
    (tcveVirtueDesireSemantics World Virtue semD).Sat w s ↔
      (deonticSemantics World semI).Sat w s.toImperative := by
  exact h_align s.virtue s.formula w

theorem entails_tcveDesire_iff_entails_imperative {World : Type u} {Virtue : Type v}
    (semD : TCVEVirtueDesireSemantics World Virtue) (semI : DeonticSemantics World)
    (h_align : ∀ v φ w, semD.desires v φ w ↔ semI.deontic .Obligation φ w)
    (T : MinimalVirtueDesireTheory World Virtue) (s : MinimalVirtueDesireSentence World Virtue) :
    Entails (tcveVirtueDesireSemantics World Virtue semD) T s ↔
      Entails (deonticSemantics World semI) (T.toImperativeTheory) s.toImperative := by
  simpa [MinimalVirtueDesireTheory.toImperativeTheory] using
    (entails_map_iff
      (sem₁ := tcveVirtueDesireSemantics World Virtue semD)
      (sem₂ := deonticSemantics World semI)
      (f := fun s => MinimalVirtueDesireSentence.toImperative (World := World) (Virtue := Virtue) s)
      (h_sat := fun w s => TCVEVirtueDesireSemantics.sat_iff_sat_toImperative
        (semD := semD) (semI := semI) h_align w s)
      (T := T) (s := s))

theorem TCVEVirtueTargetSemantics.sat_iff_sat_toValue {World : Type u} {Virtue : Type v}
    (semT : TCVEVirtueTargetSemantics World Virtue) (semV : ValueSemantics World)
    (h_align : ∀ v φ w, semT.targets v φ w ↔ semV.morally .MorallyGood φ w)
    (w : World) (s : SimpleVirtueTargetSentence World Virtue) :
    (tcveVirtueTargetSemantics World Virtue semT).Sat w s ↔
      (valueJudgmentSemantics World semV).Sat w s.toValue := by
  exact h_align s.virtue s.formula w

theorem entails_tcveTarget_iff_entails_value {World : Type u} {Virtue : Type v}
    (semT : TCVEVirtueTargetSemantics World Virtue) (semV : ValueSemantics World)
    (h_align : ∀ v φ w, semT.targets v φ w ↔ semV.morally .MorallyGood φ w)
    (T : SimpleVirtueTargetTheory World Virtue) (s : SimpleVirtueTargetSentence World Virtue) :
    Entails (tcveVirtueTargetSemantics World Virtue semT) T s ↔
      Entails (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) s.toValue := by
  simpa [SimpleVirtueTargetTheory.toValueJudgmentTheory] using
    (entails_map_iff
      (sem₁ := tcveVirtueTargetSemantics World Virtue semT)
      (sem₂ := valueJudgmentSemantics World semV)
      (f := fun s => SimpleVirtueTargetSentence.toValue (World := World) (Virtue := Virtue) s)
      (h_sat := fun w s => TCVEVirtueTargetSemantics.sat_iff_sat_toValue
        (semT := semT) (semV := semV) h_align w s)
      (T := T) (s := s))

/-! ## Existential-introducing KIF translations as relations -/

/-- KIF: `ValueJudgmentSentenceToTargetFn` (MorallyGood ⇒ ∃virtue. virtueTarget(virtue, φ)). -/
def valueJudgmentToTargetRel (World : Type u) (Virtue : Type v) :
    TranslationRel (ValueJudgmentSentence World) (SimpleVirtueTargetSentence World Virtue) :=
  fun vjs vt => vjs.tag = .MorallyGood ∧ vt.formula = vjs.formula

/-- KIF: `ImperativeToVirtueDesireFn` (Obligation ⇒ ∃virtue. desire(virtue, φ)). -/
def imperativeToVirtueDesireRel (World : Type u) (Virtue : Type v) :
    TranslationRel (DeonticSentence World) (MinimalVirtueDesireSentence World Virtue) :=
  fun imps vdes => imps.tag = .Obligation ∧ vdes.formula = imps.formula

def negate {World : Type u} (φ : Formula World) : Formula World :=
  fun w => ¬ φ w

/-- KIF: `UtilityAssignmentToVirtueDesireFn` (sign-based; permissibility/0 omitted). -/
def utilityAssignmentToVirtueDesireRel (World : Type u) (Virtue : Type v) :
    TranslationRel (UtilityAssignmentSentence World) (MinimalVirtueDesireSentence World Virtue) :=
  fun uas vdes =>
    (uas.tag > 0 ∧ vdes.formula = uas.formula) ∨
    (uas.tag < 0 ∧ vdes.formula = negate uas.formula)

/-! ### Witnessed vs Prop-level translations -/

def witnessedValueJudgmentToTarget {World : Type u} {Virtue : Type v}
    (v : Virtue) (s : ValueJudgmentSentence World) (hGood : s.tag = .MorallyGood) :
    Witnessed (valueJudgmentToTargetRel World Virtue) s :=
  ⟨{ virtue := v, formula := s.formula }, by
    exact ⟨hGood, rfl⟩⟩

def witnessedImperativeToVirtueDesire {World : Type u} {Virtue : Type v}
    (v : Virtue) (s : DeonticSentence World) (hObl : s.tag = .Obligation) :
    Witnessed (imperativeToVirtueDesireRel World Virtue) s :=
  ⟨{ virtue := v, formula := s.formula }, by
    exact ⟨hObl, rfl⟩⟩

theorem translates_valueJudgmentToTarget_of_nonempty {World : Type u} {Virtue : Type v}
    (hV : Nonempty Virtue) (s : ValueJudgmentSentence World) (hGood : s.tag = .MorallyGood) :
    Translates (valueJudgmentToTargetRel World Virtue) s := by
  rcases hV with ⟨v⟩
  exact witnessed_to_translates (s := s) (witnessedValueJudgmentToTarget (World := World) (Virtue := Virtue) v s hGood)

/-! ### First “loop” facts for existential translations -/

theorem witnessedValueJudgmentToTarget_toValue {World : Type u} {Virtue : Type v}
    (v : Virtue) (s : ValueJudgmentSentence World) (hGood : s.tag = .MorallyGood) :
    (witnessedValueJudgmentToTarget (World := World) (Virtue := Virtue) v s hGood).fst.toValue = s := by
  cases s with
  | mk tag formula =>
    cases hGood
    rfl

def GoodOnly {World : Type u} (T : ValueJudgmentTheory World) : Prop :=
  ∀ s, s ∈ T → s.tag = .MorallyGood

def valueViaTargetRoundTrip {World : Type u} (Virtue : Type v) (T : ValueJudgmentTheory World) :
    ValueJudgmentTheory World :=
  Theory.map (fun t => SimpleVirtueTargetSentence.toValue (World := World) (Virtue := Virtue) t)
    (Theory.relMap (valueJudgmentToTargetRel World Virtue) T)

theorem valueViaTargetRoundTrip_eq_of_goodOnly {World : Type u} {Virtue : Type v}
    (hV : Nonempty Virtue) (T : ValueJudgmentTheory World) (hGoodOnly : GoodOnly (World := World) T) :
    valueViaTargetRoundTrip (World := World) Virtue T = T := by
  rcases hV with ⟨v⟩
  funext s
  apply propext
  constructor
  · intro hs
    rcases hs with ⟨t, ht, htEq⟩
    rcases ht with ⟨s₁, hs₁, hR⟩
    rcases hR with ⟨hTag, hForm⟩
    -- `t.toValue` is always morally good; under `hR`, it matches `s₁`, so the round-trip is in `T`.
    have hsEq : s = s₁ := by
      cases s with
      | mk tagS formulaS =>
        cases s₁ with
        | mk tag1 formula1 =>
          have hTagS : tagS = MoralValueAttribute.MorallyGood := by
            have h := congrArg (fun x : ValueJudgmentSentence World => x.tag) htEq
            have : MoralValueAttribute.MorallyGood = tagS := by
              simpa [SimpleVirtueTargetSentence.toValue] using h
            exact this.symm
          have hFormulaS : formulaS = t.formula := by
            have h := congrArg (fun x : ValueJudgmentSentence World => x.formula) htEq
            have : t.formula = formulaS := by
              simpa [SimpleVirtueTargetSentence.toValue] using h
            exact this.symm
          have hTag1 : tag1 = MoralValueAttribute.MorallyGood := by
            simpa using hTag
          have hFormula1 : t.formula = formula1 := by
            simpa using hForm
          have hTagEq : tagS = tag1 := by
            calc
              tagS = MoralValueAttribute.MorallyGood := hTagS
              _ = tag1 := hTag1.symm
          have hFormulaEq : formulaS = formula1 := by
            calc
              formulaS = t.formula := hFormulaS
              _ = formula1 := hFormula1
          cases hTagEq
          cases hFormulaEq
          rfl
    rw [hsEq]; exact hs₁
  · intro hs
    have hTag : s.tag = .MorallyGood :=
      hGoodOnly s hs
    -- pick any virtue witness `v`.
    let t : SimpleVirtueTargetSentence World Virtue := { virtue := v, formula := s.formula }
    have hR : valueJudgmentToTargetRel World Virtue s t :=
      ⟨hTag, rfl⟩
    have ht : t ∈ Theory.relMap (valueJudgmentToTargetRel World Virtue) T :=
      Theory.mem_relMap_of_mem (T := T) (hs₁ := hs) (hR := hR)
    refine ⟨t, ht, ?_⟩
    cases s with
    | mk tag formula =>
      cases hTag
      rfl

theorem valueJudgmentToTargetRel_sound {World : Type u} {Virtue : Type v}
    (semV : ValueSemantics World) (semT : TCVEVirtueTargetSemantics World Virtue)
    (h_align : ∀ v φ w, semT.targets v φ w ↔ semV.morally .MorallyGood φ w) :
    RelSound (valueJudgmentSemantics World semV) (tcveVirtueTargetSemantics World Virtue semT)
      (valueJudgmentToTargetRel World Virtue) := by
  intro w s₁ s₂ hR hSat
  rcases hR with ⟨hTag, hForm⟩
  dsimp [valueJudgmentSemantics, ValueSemantics.sat] at hSat
  dsimp [tcveVirtueTargetSemantics, TCVEVirtueTargetSemantics.sat]
  have hGood : semV.morally .MorallyGood s₁.formula w := by
    simpa [hTag] using hSat
  have hGood' : semV.morally .MorallyGood s₂.formula w := by
    simpa [hForm] using hGood
  exact (h_align s₂.virtue s₂.formula w).2 hGood'

theorem valueJudgmentToTargetRel_complete {World : Type u} {Virtue : Type v}
    (semV : ValueSemantics World) (semT : TCVEVirtueTargetSemantics World Virtue)
    (h_align : ∀ v φ w, semT.targets v φ w ↔ semV.morally .MorallyGood φ w) :
    RelComplete (valueJudgmentSemantics World semV) (tcveVirtueTargetSemantics World Virtue semT)
      (valueJudgmentToTargetRel World Virtue) := by
  intro w s₁ s₂ hR hSat
  rcases hR with ⟨hTag, hForm⟩
  dsimp [tcveVirtueTargetSemantics, TCVEVirtueTargetSemantics.sat] at hSat
  dsimp [valueJudgmentSemantics, ValueSemantics.sat]
  have hGood : semV.morally .MorallyGood s₂.formula w :=
    (h_align s₂.virtue s₂.formula w).1 hSat
  have hGood' : semV.morally .MorallyGood s₁.formula w := by
    simpa [hForm] using hGood
  simpa [hTag] using hGood'

end Foet
