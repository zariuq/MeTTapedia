import Mettapedia.OSLF.Framework.PyashCoreModel
import Mettapedia.OSLF.Framework.LanguageMorphism
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Logic.DDLPlus.Core
import Mettapedia.Logic.DDLPlus.Theorems
import Mettapedia.Logic.DDLPlus.DTSBridge
import Mettapedia.Logic.GovernanceReasoning.Core

/-!
# Governance OSLF Instance: DDLPlus over PyashCore Semantics

## Architecture

```
PyashCore LanguageDef (operational engine)
    │
    │  av v v' := langReduces pyashCore v v'     (one-step dispatch)
    │  pv v v' := LangReducesStar pyashCore v v' (multi-step futures)
    │
    ├──→ OSLF pipeline: langOSLF pyashCore "State"  (pyashCoreOSLF)
    │       ◇ = langDiamond pyashCore  (can-reduce-to)
    │       □ = langBox pyashCore      (must-reduce-to-only)
    │       ◇ ⊣ □ via pyashCoreGalois
    │
    └──→ DDLPlus semantic bridge (c = Unit, w = Pattern):
            □ₐ/◇ₐ ≅ langBox/langDiamond (same definition, specialised)
            sem_4b: pv reflexive ✓  (LangReducesStar is reflexive)
            sem_4a: av ⊆ pv ✓       (one-step ⊆ multi-step)
            sem_3a: av serial only on reducible states
```

## Governance Language Correspondence

PyashCore moods map to deontic modalities:
- `MDo`   → actual obligation Oₐ (imperative/action)
- `MPrah` → permission / ideal obligation Oᵢ (permissive/normative)
- `MYa`   → assertion (descriptive, non-deontic)
- `MDef`  → definition (norm creation)

## Three-Layer Integration

```
Layer 3: DDLPlus abstract deontic logic (Core, Theorems)
    ↑ frames instantiated by
Layer 2: GovernanceReasoning (DTS, Bridge, Judgments)
    ↑ operational semantics from
Layer 1: PyashCore (reduction, dispatch, state machine)
```
-/

namespace Mettapedia.OSLF.Framework.GovernanceInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.PyashCoreInstance
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Logic.DDLPlus.Core
open Mettapedia.Logic.DDLPlus.Theorems
open Mettapedia.Logic.DDLPlus.DTSBridge
open Mettapedia.Logic.GovernanceReasoning.Core

/-! ## §1 PyashCore OSLF (re-export)

`pyashCoreOSLF` and `pyashCoreGalois` are already proven in PyashCoreModel. -/

/-- The governance OSLF type system = PyashCore with process sort "State". -/
abbrev govOSLF := pyashCoreOSLF

/-- The governance Galois connection ◇ ⊣ □. -/
theorem govGalois :
    GaloisConnection (langDiamond pyashCore) (langBox pyashCore) :=
  pyashCoreGalois

/-! ## §2 Accessibility Structure

PyashCore's reduction gives DDLPlus-style accessibility relations. -/

/-- pv (multi-step) is reflexive — satisfies DDLPlus sem_4b. -/
theorem pyashCore_pv_reflexive (p : Pattern) :
    LangReducesStar pyashCore p p :=
  .refl p

/-- av ⊆ pv: one-step ⊆ multi-step — satisfies DDLPlus sem_4a. -/
theorem pyashCore_av_subset_pv {p q : Pattern}
    (h : langReduces pyashCore p q) :
    LangReducesStar pyashCore p q :=
  .single h

/-! ## §3 DDLPlus/OSLF Modal Correspondence

The OSLF modal operators have an important polarity distinction from DDLPlus:

- `langDiamond` (◇) = step-FUTURE: `∃ q, langReduces p q ∧ φ q`
  This matches DDLPlus `dia_a` when `av = langReduces`.
- `langBox` (□)    = step-PAST:   `∀ q, langReduces q p → φ q`
  This is NOT DDLPlus `box_a` (which is future). It is the left-adjoint
  to ◇ in the Galois connection ◇ ⊣ □. -/

/-- ◇ₐφ (DDLPlus, av = langReduces) = langDiamond pyashCore φ (step-future). -/
theorem diaa_eq_langDiamond (φ : Pattern → Prop) (p : Pattern) :
    (∃ q, langReduces pyashCore p q ∧ φ q) ↔ langDiamond pyashCore φ p :=
  (langDiamond_spec pyashCore φ p).symm

/-- OSLF langBox is the step-past operator: all predecessors satisfy φ. -/
theorem langBox_is_past (φ : Pattern → Prop) (p : Pattern) :
    langBox pyashCore φ p ↔ ∀ q, langReduces pyashCore q p → φ q :=
  langBox_spec pyashCore φ p

/-! ## §4 Seriality and Axiom D

Axiom D (□φ → ◇φ) holds for pv by reflexivity.
For av, it holds on reducible states. -/

/-- Axiom D for pv holds by reflexivity — no states are pv-dead-ends. -/
theorem govAxiomD_pv (φ : Pattern → Prop) (p : Pattern)
    (h : ∀ q, LangReducesStar pyashCore p q → φ q) :
    ∃ q, LangReducesStar pyashCore p q ∧ φ q :=
  ⟨p, .refl p, h p (.refl p)⟩

/-- Axiom D for av holds on reducible states. -/
theorem govAxiomD_av (φ : Pattern → Prop) (p : Pattern)
    (hred : ∃ q, langReduces pyashCore p q)
    (h : ∀ q, langReduces pyashCore p q → φ q) :
    ∃ q, langReduces pyashCore p q ∧ φ q :=
  let ⟨q, hq⟩ := hred; ⟨q, hq, h q hq⟩

/-! ## §6 Parameterized Governance DDLPlus Frame

Combines PyashCore's av/pv structure with an abstract obligation predicate
satisfying DDLPlus sem_5a–sem_5e.  The `ob` predicate comes from the
GovernanceReasoning layer (DTS/Bridge/Judgments).

`GovFrame w` is parameterized over the world type `w` so that it can be
instantiated at the subtype `{p // live p}` without subtype-coercion issues. -/

/-- A governance frame over world type `w`: abstract DDLPlus obligation structure.

    `ob X Y` = "norm Y is obligatory in governance context X".
    Provided by the governance reasoning layer, not the operational semantics. -/
structure GovFrame (w : Type*) where
  ob : WProp w → WProp w → Prop
  ob_not_bot  : ∀ X, ¬ ob X (fun _ => False)
  ob_cong     : ∀ X Y Z, (∀ v, (X v ∧ Y v) ↔ (X v ∧ Z v)) → (ob X Y ↔ ob X Z)
  ob_conj     : ∀ X Y Z, (∃ v, X v ∧ Y v ∧ Z v) → ob X Y → ob X Z →
                  ob X (fun v => Y v ∧ Z v)
  ob_transfer : ∀ X Y Z, (∀ v, Y v → X v) → ob X Y → (∀ v, X v → Z v) →
                  ob Z (fun v => (Z v ∧ ¬ X v) ∨ Y v)
  ob_restrict : ∀ X Y Z, (∀ v, Y v → X v) → ob X Z → (∃ v, Y v ∧ Z v) → ob Y Z

/-! ## §7 Closed Accessibility (closed under successors)

`ClosedGovAccessibility` is parameterized by an abstract one-step relation `step`
so that any reactive process language — not just PyashCore — can provide a valid
governance accessibility context.  For PyashCore, set `step := langReduces pyashCore`.
For the `GovNormCycle` reactive loop language, `step` is the deliberate ↔ enact cycle. -/

/-- A closed governance accessibility context: live is closed under successors.

    The `step` relation is abstract — it can be `langReduces pyashCore`, a norm-cycle
    relation, or any other one-step process relation.  The DDLPlus `av` is `step` and
    `pv` is the reflexive-transitive closure of `step`. -/
structure ClosedGovAccessibility where
  live   : Pattern → Prop
  /-- The one-step accessibility relation for this governance context. -/
  step   : Pattern → Pattern → Prop
  /-- Every live state has at least one live successor. -/
  serial : ∀ p, live p → ∃ q, step p q
  /-- Successors of live states are also live. -/
  closed : ∀ p q, live p → step p q → live q

/-- A GovFrame (at the live-subtype world) + ClosedGovAccessibility induces
    a DDLPlusFrame on live states.  The world type is `{p : Pattern // ga.live p}`.

    `av = ga.step`, `pv = Relation.ReflTransGen ga.step` (reflexive-transitive closure).
    sem_4a and sem_4b follow from reflexive-transitive closure axioms. -/
noncomputable def govDDLFrameClosed
    (ga : ClosedGovAccessibility)
    (gf : GovFrame { p : Pattern // ga.live p }) :
    DDLPlusFrame { p : Pattern // ga.live p } where
  av  := fun ⟨p, _⟩ ⟨q, _⟩ => ga.step p q
  pv  := fun ⟨p, _⟩ ⟨q, _⟩ => Relation.ReflTransGen ga.step p q
  ob  := gf.ob
  sem_3a := fun ⟨p, hp⟩ =>
    let ⟨q, hq⟩ := ga.serial p hp
    ⟨⟨q, ga.closed p q hp hq⟩, hq⟩
  sem_4a := fun _ _ h => Relation.ReflTransGen.single h
  sem_4b := fun _ => Relation.ReflTransGen.refl
  sem_5a := gf.ob_not_bot
  sem_5b := gf.ob_cong
  sem_5c := gf.ob_conj
  sem_5d := gf.ob_transfer
  sem_5e := gf.ob_restrict

/-! ## §8 DDLPlus Theorems for Governance

With govDDLFrameClosed, all CJ theorems apply to governance reasoning. -/

/-- CJ_3: □ₚ-states imply □ₐ-states (possible → actual necessity).
    If φ holds in all reachable PyashCore futures, it holds in all one-step successors. -/
theorem gov_CJ3 (ga : ClosedGovAccessibility)
    (gf : GovFrame { p : Pattern // ga.live p })
    (φ : Meaning Unit { p : Pattern // ga.live p })
    (ctx : Unit) (v : { p : Pattern // ga.live p }) :
    box_p (govDDLFrameClosed ga gf) φ ctx v →
    box_a (govDDLFrameClosed ga gf) φ ctx v :=
  CJ_3 (govDDLFrameClosed ga gf) φ ctx v

/-- Axiom D: □ₐ-necessity implies ◇ₐ-possibility.
    Seriality of the governance state machine (every live state has a successor)
    guarantees the DDLPlus axiom D. -/
theorem gov_axiomD (ga : ClosedGovAccessibility)
    (gf : GovFrame { p : Pattern // ga.live p })
    (φ : Meaning Unit { p : Pattern // ga.live p })
    (ctx : Unit) (v : { p : Pattern // ga.live p }) :
    box_a (govDDLFrameClosed ga gf) φ ctx v →
    dia_a (govDDLFrameClosed ga gf) φ ctx v :=
  axiomD_actual (govDDLFrameClosed ga gf) φ ctx v

/-- CJ_4: Contradictions cannot be obligatory in any governance context. -/
theorem gov_CJ4 (ga : ClosedGovAccessibility)
    (gf : GovFrame { p : Pattern // ga.live p })
    (A : Meaning Unit { p : Pattern // ga.live p }) :
    modal_valid (pnot (cond_obl (govDDLFrameClosed ga gf) pbot A)) :=
  CJ_4 (govDDLFrameClosed ga gf) A

/-- Kant's law: if governance norm φ is □ₐ-necessary, it cannot be actually obligatory. -/
theorem gov_kant (ga : ClosedGovAccessibility)
    (gf : GovFrame { p : Pattern // ga.live p })
    (φ : Meaning Unit { p : Pattern // ga.live p })
    (ctx : Unit) (v : { p : Pattern // ga.live p })
    (hbox : box_a (govDDLFrameClosed ga gf) φ ctx v) :
    ¬ actual_obl (govDDLFrameClosed ga gf) φ ctx v :=
  box_a_implies_not_actual_obl (govDDLFrameClosed ga gf) ctx v φ hbox

/-! ## §9 Deontic Vocabulary from PyashCore Moods -/

/-- "do" mood = action statement (actual obligation). -/
def isMoodDo : Pattern → Prop | .apply "MDo" [] => True | _ => False

/-- "prah" mood = normative statement (permission/ideal obligation). -/
def isMoodPrah : Pattern → Prop | .apply "MPrah" [] => True | _ => False

/-- "ya" mood = assertion (non-deontic). -/
def isMoodYa : Pattern → Prop | .apply "MYa" [] => True | _ => False

/-- A "do"-sentence is a governance action statement. -/
def isGovActionSentence (sent : Pattern) : Prop :=
  ∃ v rts, sent = .apply "SentenceCore" [.apply "MDo" [], v, rts]

/-- A "prah"-sentence is a governance norm statement. -/
def isGovNormSentence (sent : Pattern) : Prop :=
  ∃ v rts, sent = .apply "SentenceCore" [.apply "MPrah" [], v, rts]

/-- A governance context (live state) = a non-Done PyashCore state. -/
def isGovLive : Pattern → Prop
  | .apply "State" [instr, _, _, _] => instr ≠ .apply "Done" []
  | _ => False

/-! ## §10 Summary -/

#check @govOSLF
#check @govGalois
#check @govDDLFrameClosed
#check @gov_CJ3
#check @gov_axiomD
#check @gov_CJ4

end Mettapedia.OSLF.Framework.GovernanceInstance
