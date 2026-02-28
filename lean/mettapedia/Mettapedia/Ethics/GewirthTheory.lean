import Mettapedia.Ethics.GewirthPGC
import Mettapedia.Ethics.Core

set_option autoImplicit false

/-!
# Gewirth Theory: PGC as a Semantic Theory

Packages the PGC proof as a formal theory using `Entails`/`Models` from
`Mettapedia.Ethics.Core`.  The mathematical content is in `GewirthPGC.lean`;
this module adds metatheoretic wrapping.

## Contents

- §1 PGCModel and PGCAssumptionTheory
- §2 Semantics and entailment (entails_PGC_strong)
- §3 AFP-aligned theory (full DDL frame + PGC)

Ported from `foet/Foet/GewirthTheory.lean` with Mettapedia namespace.
-/

namespace Mettapedia.Ethics.Gewirth

open Mettapedia.Ethics (Semantics Theory Models Entails Formula)
open Mettapedia.Ethics.Gewirth

universe u

/-! ## §1 PGCModel and PGCAssumptionTheory -/

/-- The carrier type of PGC models (a `PGCInterpretation`). -/
abbrev PGCModel : Type (u + 1) :=
  PGCInterpretation

/-- The Gewirth PGC *assumption set* (all statements except the goal `PGC_strong`),
    as a `Theory` in the Mettapedia.Ethics sense. -/
def PGCAssumptionTheory : Theory PGCStatementName :=
  fun s => s ≠ .PGC_strong

/-! ## §2 Semantics and Entailment -/

/-- Satisfaction relation for `PGCStatementName`s in a `PGCModel`: each name
    is interpreted as the corresponding proposition over the interpretation. -/
def pgcSemantics : Semantics PGCStatementName PGCModel :=
  ⟨fun m s => PGCStatement m s⟩

/-- The PGC assumption theory (semantically) entails `PGC_strong`. -/
theorem entails_PGC_strong :
    Entails pgcSemantics PGCAssumptionTheory .PGC_strong := by
  intro m hm
  have hAssm : PGCAssumptions m := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hm .sem_5a            (by intro h; cases h)
    · exact hm .sem_5b            (by intro h; cases h)
    · exact hm .sem_5e            (by intro h; cases h)
    · exact hm .explicationGoodness1   (by intro h; cases h)
    · exact hm .explicationGoodness2   (by intro h; cases h)
    · exact hm .explicationGoodness3   (by intro h; cases h)
    · exact hm .explicationFWB1        (by intro h; cases h)
    · exact hm .explicationFWB2        (by intro h; cases h)
    · exact hm .explicationFWB3        (by intro h; cases h)
    · exact hm .OIOAC              (by intro h; cases h)
    · exact hm .explicationInterference (by intro h; cases h)
  exact PGC_strong_ofAssumptions m hAssm

/-! ## §3 AFP-Aligned Theory -/

/-- Additional frame axioms from the AFP Carmo-Jones DDL embedding,
    kept separate from `PGCAssumptionTheory` because the PGC proof does not require them. -/
inductive PGCAFPExtraSentence : Type
  | sem_3a   -- av is serial: ∀ w, ∃ w', av w w'
  | sem_4a   -- av ⊆ pv:      ∀ w w', av w w' → pv w w'
  | sem_4b   -- pv reflexive: ∀ w, pv w w
  | sem_5c   -- ob conjunction
  | sem_5d   -- ob transfer
  deriving DecidableEq, Repr

/-- A full AFP-aligned sentence type: minimal PGC sentences + the extra DDL frame axioms. -/
inductive PGCAFPSentence : Type
  | base  (s : PGCStatementName)
  | extra (s : PGCAFPExtraSentence)
  deriving DecidableEq, Repr

/-- The AFP-aligned theory: all sentences except `PGC_strong`. -/
def PGCAFPTheory : Theory PGCAFPSentence :=
  fun s => s ≠ .base .PGC_strong

/-- Satisfaction for the full AFP-aligned sentence type.
    The base cases delegate to `pgcSemantics`; the extra cases add the
    remaining DDLPlusFrame conditions. -/
def pgcAfpSemantics : Semantics PGCAFPSentence PGCModel :=
  ⟨fun m s =>
    match s with
    | .base sBase => pgcSemantics.Sat m sBase
    | .extra .sem_3a =>
        ∀ w : m.World, Instantiated (m.av w)
    | .extra .sem_4a =>
        ∀ w : m.World, Subset (m.av w) (m.pv w)
    | .extra .sem_4b =>
        ∀ w : m.World, m.pv w w
    | .extra .sem_5c =>
        ∀ X Y Z : Formula m.World,
          Instantiated (Inter (Inter X Y) Z) → m.ob X Y → m.ob X Z →
          m.ob X (Inter Y Z)
    | .extra .sem_5d =>
        ∀ X Y Z : Formula m.World,
          Subset Y X → m.ob X Y → Subset X Z →
          m.ob Z (fun v => (Z v ∧ ¬ X v) ∨ Y v)⟩

/-- Full AFP-aligned route: if a model satisfies the CJDDLplus frame axioms in
    addition to the Gewirth explications, then it satisfies `PGC_strong`.

    This makes explicit that the extra axioms are not needed: the proof works
    under the weaker `PGCAssumptionTheory`, hence also under the stronger AFP one. -/
theorem entails_PGC_strong_from_AFPTheory :
    Entails pgcAfpSemantics PGCAFPTheory (.base .PGC_strong) := by
  intro m hm
  have hmBase : Models pgcSemantics m PGCAssumptionTheory := by
    intro s hs
    have : PGCAFPSentence.base s ∈ PGCAFPTheory := by
      intro hEq
      exact hs (by cases hEq; rfl)
    exact hm (.base s) this
  exact entails_PGC_strong m hmBase

#check @entails_PGC_strong
#check @entails_PGC_strong_from_AFPTheory

end Mettapedia.Ethics.Gewirth
