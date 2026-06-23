import Foet.Theory
import Foet.AfpGewirth.GewirthArgument

set_option autoImplicit false

namespace Foet
namespace AFP
namespace Gewirth

/-!
Bridge layer: treats the Gewirth development as a first-class FOET theory
(a set of sentences) with a semantics and entailment.

Key design choice (mirrors the AFP session):

- Most explications are asserted under Kaplan/LD indexical validity `⌊_⌋ᴰ`.
- The interference explication is asserted under classical modal validity `⌊_⌋`
  (see AFP comment in `GewirthArgument.thy`).

To keep this explicit and extensible, we represent a sentence as a formula `m`
tagged by the intended validity mode.
-/

/-! ### Sentence layer -/

inductive Validity : Type
  | ld
  | mod
  deriving DecidableEq, Repr

structure Sentence : Type where
  mode : Validity
  φ : m

def holds : Sentence → Prop
  | ⟨.ld, φ⟩ => ⌊φ⌋ᴰ
  | ⟨.mod, φ⟩ => ⌊φ⌋

@[simp] theorem holds_ld (φ : m) : holds ⟨.ld, φ⟩ ↔ ⌊φ⌋ᴰ := Iff.rfl
@[simp] theorem holds_mod (φ : m) : holds ⟨.mod, φ⟩ ↔ ⌊φ⌋ := Iff.rfl

/-! ### FOET semantics instance -/

def semantics : Semantics Sentence Unit :=
  ⟨fun _ s => holds s⟩

/-! ### Theory layer -/

/-! A named catalogue for the *fixed* (non-schematic) axioms. -/

inductive FixedAxiomName : Type
  | Good1
  | Good2
  | Good3
  | FWB1
  | FWB2
  | FWB3
  | EssPPA
  deriving DecidableEq, Repr

def fixedAxiom : FixedAxiomName → Sentence
  | .Good1 => ⟨.ld, ax_Good1⟩
  | .Good2 => ⟨.ld, ax_Good2⟩
  | .Good3 => ⟨.ld, ax_Good3⟩
  | .FWB1 => ⟨.ld, ax_FWB1⟩
  | .FWB2 => ⟨.ld, ax_FWB2⟩
  | .FWB3 => ⟨.ld, ax_FWB3⟩
  | .EssPPA => ⟨.ld, ax_essentialPPA⟩

/-!
The Gewirth ethical theory, as a *set of sentences*:

- includes the fixed explications above, and
- includes the schematic OIOAC axiom for all formulas `φ : m`, and
- includes the schematic interference explication for all formulas `φ : m`.
-/
def theory : Theory Sentence :=
  fun s =>
    (∃ n : FixedAxiomName, s = fixedAxiom n) ∨
      (∃ φ : m, s = ⟨.ld, ax_OIOAC φ⟩) ∨
        (∃ φ : m, s = ⟨.mod, ax_Interference φ⟩)

/-! ### Assumption interface (parametric proof target) -/

class Assumptions : Prop where
  EssPPA_valid : ⌊ax_essentialPPA⌋ᴰ
  Good1_valid : ⌊ax_Good1⌋ᴰ
  Good2_valid : ⌊ax_Good2⌋ᴰ
  Good3_valid : ⌊ax_Good3⌋ᴰ
  FWB1_valid : ⌊ax_FWB1⌋ᴰ
  FWB2_valid : ⌊ax_FWB2⌋ᴰ
  FWB3_valid : ⌊ax_FWB3⌋ᴰ
  OIOAC_valid : ∀ φ : m, ⌊ax_OIOAC φ⌋ᴰ
  Interference_valid : ∀ φ : m, ⌊ax_Interference φ⌋

/-! The existing AFP-style axioms instantiate the interface. -/
instance : Assumptions where
  EssPPA_valid := essentialPPA
  Good1_valid := explicationGoodness1
  Good2_valid := explicationGoodness2
  Good3_valid := explicationGoodness3
  FWB1_valid := explicationFWB1
  FWB2_valid := explicationFWB2
  FWB3_valid := explicationFWB3
  OIOAC_valid := fun φ => OIOAC φ
  Interference_valid := fun φ => explicationInterference φ

/-!
Build the assumptions interface from any FOET model that satisfies the sentence-set theory.

This is the key step that makes the ontology connection *non-decorative*:
`Entails` will now genuinely depend on the theory-as-a-set.
-/
@[reducible] def assumptionsOfModels (hM : Models semantics () theory) : Assumptions := by
  classical
  refine
    { EssPPA_valid := ?_
      Good1_valid := ?_
      Good2_valid := ?_
      Good3_valid := ?_
      FWB1_valid := ?_
      FWB2_valid := ?_
      FWB3_valid := ?_
      OIOAC_valid := ?_
      Interference_valid := ?_ }
  ·
    have hm : holds (fixedAxiom .EssPPA) := hM (fixedAxiom .EssPPA) (by
      left; exact ⟨.EssPPA, rfl⟩)
    simpa [fixedAxiom] using hm
  ·
    have hm : holds (fixedAxiom .Good1) := hM (fixedAxiom .Good1) (by
      left; exact ⟨.Good1, rfl⟩)
    simpa [fixedAxiom] using hm
  ·
    have hm : holds (fixedAxiom .Good2) := hM (fixedAxiom .Good2) (by
      left; exact ⟨.Good2, rfl⟩)
    simpa [fixedAxiom] using hm
  ·
    have hm : holds (fixedAxiom .Good3) := hM (fixedAxiom .Good3) (by
      left; exact ⟨.Good3, rfl⟩)
    simpa [fixedAxiom] using hm
  ·
    have hm : holds (fixedAxiom .FWB1) := hM (fixedAxiom .FWB1) (by
      left; exact ⟨.FWB1, rfl⟩)
    simpa [fixedAxiom] using hm
  ·
    have hm : holds (fixedAxiom .FWB2) := hM (fixedAxiom .FWB2) (by
      left; exact ⟨.FWB2, rfl⟩)
    simpa [fixedAxiom] using hm
  ·
    have hm : holds (fixedAxiom .FWB3) := hM (fixedAxiom .FWB3) (by
      left; exact ⟨.FWB3, rfl⟩)
    simpa [fixedAxiom] using hm
  ·
    intro φ
    have hm : holds ⟨.ld, ax_OIOAC φ⟩ := hM ⟨.ld, ax_OIOAC φ⟩ (by
      right; left; exact ⟨φ, rfl⟩)
    simpa using hm
  ·
    intro φ
    have hm : holds ⟨.mod, ax_Interference φ⟩ := hM ⟨.mod, ax_Interference φ⟩ (by
      right; right; exact ⟨φ, rfl⟩)
    simpa using hm

/-! ### PGC as a consequence of the sentence-set theory -/

section
  variable [GA : Assumptions]

  private theorem InterferenceWith_fromAssumptions (φ : m) :
      ⌊(◇ₐ φ) ↔ₘ (∀ₘ (fun b : e => ¬ₘ (InterferesWith b φ)))⌋ := by
    classical
    intro ctx w0
    have hInterf :
        (∃ₘ (fun b : e => InterferesWith b φ) ctx w0) ↔ ¬ ◇ₐ φ ctx w0 := by
      -- `ax_Interference φ` is exactly this equivalence.
      simpa [ax_Interference, mexists, mnot, miff] using (GA.Interference_valid φ ctx w0)
    constructor
    · intro hDia
      have : ¬ (∃ b : e, InterferesWith b φ ctx w0) := by
        intro hex
        exact (hInterf.mp hex) hDia
      simpa [mforall, mnot, mexists, not_exists] using this
    · intro hNoInterf
      have hNoEx : ¬ (∃ b : e, InterferesWith b φ ctx w0) := by
        simpa [mforall, mnot, mexists, not_exists] using hNoInterf
      have hNN : ¬ ¬ ◇ₐ φ ctx w0 := by
        intro hNotDia
        have hex : ∃ b : e, InterferesWith b φ ctx w0 :=
          hInterf.mpr hNotDia
        exact hNoEx hex
      exact Classical.not_not.mp hNN

  private theorem RightTo_of_ActsOnPurpose_fromAssumptions (C : c) (I : e) (E : m) :
      ⌊ActsOnPurpose I E⌋₍C₎ → ⌊RightTo I FWB⌋₍C₎ := by
    classical
    intro hActs

    have hGoodE : ⌊Good I E⌋₍C₎ := by
      have hAx : ⌊ax_Good1⌋₍C₎ := GA.Good1_valid C
      have hAx' : ∀ a : e, ∀ P : m, ActsOnPurpose a P C (World C) → Good a P C (World C) := by
        simpa [ax_Good1, ldtruectx, mforall, mimp] using hAx
      exact hAx' I E hActs

    have hNeedsAll : ⌊∀ₘ (fun P : m => NeedsForPurpose I FWB P)⌋ᴰ := by
      intro ctx
      have hAx : ⌊ax_FWB1⌋₍ctx₎ := GA.FWB1_valid ctx
      have hAx' : ∀ P : m, ∀ a : e, NeedsForPurpose a FWB P ctx (World ctx) := by
        simpa [ax_FWB1, ldtruectx, mforall] using hAx
      have : ∀ P : m, NeedsForPurpose I FWB P ctx (World ctx) := fun P => hAx' P I
      simpa [ldtruectx, mforall] using this

    have hDiapFWB : ◇ₚ (FWB I) C (World C) := by
      have hAx : ⌊ax_FWB2⌋₍C₎ := GA.FWB2_valid C
      have hAx' : ∀ a : e, ◇ₚ (FWB a) C (World C) := by
        simpa [ax_FWB2, ldtruectx, mforall] using hAx
      exact hAx' I

    have hOcondFWB : O⟨FWB I | □ᴰ (Good I (FWB I))⟩ C (World C) := by
      have hAx : ⌊ax_Good3⌋₍C₎ := GA.Good3_valid C
      have hAx' :
          ∀ φ : m, ∀ a : e,
            (◇ₚ φ C (World C) → O⟨φ | □ᴰ (Good a φ)⟩ C (World C)) := by
        simpa [ax_Good3, ldtruectx, mforall, mimp] using hAx
      exact hAx' (FWB I) I hDiapFWB

    have hLdGoodFWB : ⌊Good I (FWB I)⌋ᴰ := by
      have hOb : ob (□ᴰ (Good I (FWB I)) C) ((FWB I) C) := by
        simpa [Ocond, boxD] using hOcondFWB
      have hInst : instantiated (inter (□ᴰ (Good I (FWB I)) C) ((FWB I) C)) :=
        sem_5ab (X := □ᴰ (Good I (FWB I)) C) (Y := (FWB I) C) hOb
      rcases hInst with ⟨v, hv⟩
      exact hv.1

    have hExistsGoodNeeds : ∃ P : m, ⌊(Good I P) ∧ₘ (NeedsForPurpose I FWB P)⌋ᴰ := by
      refine ⟨FWB I, ?_⟩
      have hNeeds : ⌊NeedsForPurpose I FWB (FWB I)⌋ᴰ := by
        intro ctx
        have hAll : ∀ P : m, NeedsForPurpose I FWB P ctx (World ctx) := by
          simpa [ldtruectx, mforall] using hNeedsAll ctx
        exact hAll (FWB I)
      intro ctx
      have hGood : ⌊Good I (FWB I)⌋₍ctx₎ := hLdGoodFWB ctx
      have hNeed : ⌊NeedsForPurpose I FWB (FWB I)⌋₍ctx₎ := hNeeds ctx
      exact And.intro hGood hNeed

    have hLdGoodFWB' : ⌊Good I (FWB I)⌋ᴰ := by
      rcases hExistsGoodNeeds with ⟨P, hP⟩
      intro ctx
      have hAx : ⌊ax_Good2⌋₍ctx₎ := GA.Good2_valid ctx
      have hAx' :
          ∀ P0 : m, ∀ M0 : p, ∀ a0 : e,
            ((Good a0 P0) ∧ₘ (NeedsForPurpose a0 M0 P0)) ctx (World ctx) →
              Good a0 (M0 a0) ctx (World ctx) := by
        simpa [ax_Good2, ldtruectx, mforall, mimp] using hAx
      have hPrem : (Good I P ∧ₘ NeedsForPurpose I FWB P) ctx (World ctx) := by
        simpa [ldtruectx, mand] using hP ctx
      exact hAx' P FWB I hPrem

    have hBoxA : □ₚ (□ᴰ (Good I (FWB I))) C (World C) := by
      intro v hv
      simpa [boxD] using hLdGoodFWB'

    have hDiapNotFWB : ◇ₚ (¬ₘ (FWB I)) C (World C) := by
      have hAx : ⌊ax_FWB3⌋₍C₎ := GA.FWB3_valid C
      have hAx' : ∀ a : e, ◇ₚ (¬ₘ (FWB a)) C (World C) := by
        simpa [ax_FWB3, ldtruectx, mforall] using hAx
      exact hAx' I

    have hOiFWB : Oᵢ (FWB I) C (World C) := by
      have hCJ := (CJ_14p (A := □ᴰ (Good I (FWB I))) (B := FWB I)) C (World C)
      apply hCJ
      refine ⟨hOcondFWB, hBoxA, hDiapFWB, ?_⟩
      exact hDiapNotFWB

    have hOiDiaFWB : Oᵢ (◇ₐ (FWB I)) C (World C) := by
      have hAx : ⌊ax_OIOAC (FWB I)⌋₍C₎ := GA.OIOAC_valid (FWB I) C
      have hImp : Oᵢ (FWB I) C (World C) → Oᵢ (◇ₐ (FWB I)) C (World C) := by
        simpa [ax_OIOAC, ldtruectx, mimp] using hAx
      exact hImp hOiFWB

    have hEq : ∀ v, pv (World C) v →
        (◇ₐ (FWB I) C v ↔ (∀ₘ (fun a : e => ¬ₘ (InterferesWith a (FWB I)))) C v) := by
      intro v hv
      have hAll :
          ∀ a : e, (◇ₐ (FWB a) C v ↔ (∀ₘ (fun b : e => ¬ₘ (InterferesWith b (FWB a)))) C v) := by
        intro a
        simpa [mforall, miff] using (InterferenceWith_fromAssumptions (GA := GA) (FWB a) C v)
      exact hAll I

    have hOiNonInterf :
        Oᵢ (∀ₘ (fun a : e => ¬ₘ (InterferesWith a (FWB I)))) C (World C) := by
      exact (Oi_congr C (World C) (◇ₐ (FWB I))
        (∀ₘ (fun a : e => ¬ₘ (InterferesWith a (FWB I)))) hEq).1 hOiDiaFWB

    simpa [RightTo, ldtruectx] using hOiNonInterf

  private theorem RightTo_of_PPA_fromAssumptions (C : c) (I : e) :
      ⌊PPA I⌋₍C₎ → ⌊RightTo I FWB⌋₍C₎ := by
    intro hPPA
    rcases hPPA with ⟨E, hE⟩
    exact RightTo_of_ActsOnPurpose_fromAssumptions (GA := GA) C I E hE

  theorem PGC_strong_fromAssumptions : ⌊φPGC_strong⌋ᴰ := by
    intro C
    have : ∀ x : e, PPA x C (World C) → RightTo x FWB C (World C) := by
      intro x hPPA
      exact RightTo_of_PPA_fromAssumptions (GA := GA) C x hPPA
    simpa [φPGC_strong, ldtruectx, mforall, mimp] using this

end

def s_PGC_strong : Sentence :=
  ⟨.ld, φPGC_strong⟩

theorem entails_PGC_strong : Entails semantics theory s_PGC_strong := by
  intro _ hM
  letI : Assumptions := assumptionsOfModels hM
  -- The proof in `GewirthArgument.lean` is an AFP port; it should be reused only
  -- through the assumption interface at the ontology boundary.
  have h : ⌊φPGC_strong⌋ᴰ :=
    PGC_strong_fromAssumptions
  simpa [semantics, s_PGC_strong, holds] using h

/-!
Compatibility aliases (older names used during development).

Keep these as `abbrev`s so downstream imports remain stable even if we further
polish naming.
-/

abbrev ValidityMode := Validity
abbrev Sent := Sentence
abbrev denotes := holds
abbrev gewirthSemantics := semantics
abbrev AxName := FixedAxiomName
abbrev catalogue := fixedAxiom
abbrev GewirthTheory := theory
abbrev GewirthAssumptions := Assumptions

end Gewirth
end AFP
end Foet
