import Mettapedia.Logic.DDLPlus.Core
import Mettapedia.Logic.DDLPlus.Theorems
import Mettapedia.Logic.GovernanceReasoning.Core

/-!
# DDL+ ↔ DTS Bridge and Foundation KD Correspondence

## Contents

- §1 Axiom D for DDL+ frames (av-serial ⇒ □ₐφ → ◇ₐφ)
- §2 Axiom D ↔ seriality equivalence (semantic KD characterisation)
- §3 DDL+ frame → DTS (monadic restriction with consistency hypothesis)
- §4 Actual obligation: satisfiability and violability from sem_5ab

## Architecture

```
DDL+ Frame (sem_3a: av serial, sem_5a: ¬ob X ⊥, ...)
    │
    ├──→ KD semantic frame (serial accessibility)
    │      └── axiomD_actual: □ₐφ → ◇ₐφ
    │
    ├──→ DTS (monadic: ob at fixed context, + consistency hyp)
    │      └── ob_implies_pe = axiom D (□ₐφ → ◇ₐφ)
    │
    └──→ Axiom T for pv (reflexive: □ₚφ → φ)
```

## Note on DTS consistency

DDL+ sem_5a prevents `ob(X, ⊥)` but does NOT prevent `ob(X, p) ∧ ob(X, ¬p)`
simultaneously when `X ∩ p ∩ ¬p` is empty (which it always is). Hence DTS
consistency (OB(p) → ¬OB(¬p)) requires an explicit hypothesis beyond the
base DDL+ axioms. This matches the Isabelle development where DTS is an
independent axiomatisation, not derived from DDL+.

## References

- Carmo, J. & Jones, A. (2002). "Deontic Logic and Contrary-to-Duties"
- Foundation/Modal/Entailment/Basic.lean (class KD = K + axiomD)
- Foundation/Modal/Kripke/Logic/KD.lean (KD ↔ serial frames)
-/

namespace Mettapedia.Logic.DDLPlus.DTSBridge

open Mettapedia.Logic.DDLPlus.Core
open Mettapedia.Logic.GovernanceReasoning.Core

/-! ## §1 Axiom D for DDL+ Frames

The key semantic consequence of seriality (sem_3a). -/

variable {w : Type*} (F : DDLPlusFrame w)

/-- The actual-version accessibility of a DDLPlusFrame is serial.
    This is exactly semantic condition sem_3a. -/
theorem av_serial : ∀ v : w, ∃ v', F.av v v' :=
  F.sem_3a

/-- Axiom D (□φ → ◇φ) holds for box_a/dia_a.
    This is the key semantic consequence of seriality (sem_3a).
    Foundation defines `class KD extends K, HasAxiomD` where `HasAxiomD` = `□φ → ◇φ`.
    KD is Kripke-complete for serial frames (Foundation/Modal/Kripke/Logic/KD.lean).
    Our sem_3a (av is serial) is exactly the Kripke condition for KD. -/
theorem axiomD_actual {c : Type*} (φ : Meaning c w) (ctx : c) (v : w) :
    box_a F φ ctx v → dia_a F φ ctx v := by
  intro hbox
  obtain ⟨v', hav⟩ := F.sem_3a v
  exact ⟨v', hav, hbox v' hav⟩

/-- Axiom D holds for box_p/dia_p (pv is reflexive, hence serial). -/
theorem axiomD_possible {c : Type*} (φ : Meaning c w) (ctx : c) (v : w) :
    box_p F φ ctx v → dia_p F φ ctx v :=
  fun hbox => ⟨v, F.sem_4b v, hbox v (F.sem_4b v)⟩

/-- Axiom T (□φ → φ, reflexivity) holds for box_p since pv is reflexive (sem_4b). -/
theorem axiomT_possible {c : Type*} (φ : Meaning c w) (ctx : c) (v : w) :
    box_p F φ ctx v → φ ctx v :=
  fun hbox => hbox v (F.sem_4b v)

/-! ## §2 Axiom D ↔ Seriality

The definitive characterisation: axiom D for □ₐ/◇ₐ is equivalent to
av-seriality. This is the semantic content of Foundation's KD completeness
theorem for serial Kripke frames. -/

/-- Axiom D for actual modality ↔ seriality of av.
    This is the semantic bridge to Foundation's KD completeness:
    `Foundation/Modal/Kripke/Logic/KD.lean` proves KD ↔ serial frames. -/
theorem axiomD_iff_seriality :
    (∀ v : w, ∃ v', F.av v v') ↔
    (∀ (c : Type) (φ : Meaning c w) (ctx : c) (v : w),
      box_a F φ ctx v → dia_a F φ ctx v) := by
  constructor
  · intro hser _ φ ctx v hbox
    obtain ⟨v', hav⟩ := hser v
    exact ⟨v', hav, hbox v' hav⟩
  · intro hD v
    have h : dia_a F (ptop (c := Unit)) () v :=
      hD Unit ptop () v (fun _ _ => trivial)
    exact ⟨h.choose, h.choose_spec.1⟩

/-! ## §3 DDL+ Frame → DTS

A DDLPlusFrame with a fixed accessibility set induces a DTS on WProp,
given an explicit consistency hypothesis. The consistency hypothesis is
needed because DDL+ sem_5a (¬ob X ⊥) only prevents obligations to
contradictions, not mutual obligations to p and ¬p separately. -/

/-- A DDLPlusFrame with fixed accessibility set induces a DTS,
    given a consistency hypothesis ensuring ob(R, p) and ob(R, ¬p)
    cannot both hold.

    The consistency hypothesis is NOT derivable from DDL+ axioms alone
    (sem_5c requires the conjunction witness `∃ v, R v ∧ p v ∧ ¬p v`,
    which is always empty). It must be provided as a frame property. -/
def frameToDTS (R : WProp w)
    (hcons : ∀ p : WProp w, F.ob R p → ¬ F.ob R (WProp.compl p)) :
    DTS (WProp w) where
  ob := fun p => F.ob R p
  neg := WProp.compl
  neg_neg := by intro p; ext v; simp [WProp.compl]
  consistent := hcons

/-- The DTS induced by a DDLPlusFrame satisfies axiom D (OB → PE).
    This is a direct consequence of the DTS structure. -/
theorem frameToDTS_axiomD (R : WProp w)
    (hcons : ∀ p : WProp w, F.ob R p → ¬ F.ob R (WProp.compl p))
    (p : WProp w) :
    (frameToDTS F R hcons).ob p → (frameToDTS F R hcons).pe p :=
  (frameToDTS F R hcons).ob_implies_pe p

/-! ## §4 Actual Obligation: Satisfiability and Violability

For the actual obligation operator Oₐ (which includes a violation clause),
semantic consequences are stronger than for bare conditional obligation. -/

/-- Actual obligation implies ◇ₐφ (the obligation is satisfiable).
    This follows from sem_5ab: ob(av v, φ ctx) implies ∃ v', av v v' ∧ φ ctx v'. -/
theorem actual_obl_implies_dia {c : Type*} (ctx : c) (v : w) (φ : Meaning c w)
    (hoa : actual_obl F φ ctx v) : dia_a F φ ctx v :=
  let ⟨v', hav, hφ⟩ := F.sem_5ab hoa.1
  ⟨v', hav, hφ⟩

/-- Actual obligation implies ◇ₐ(¬φ) (violation is possible).
    This is directly from the violation clause in the definition of Oₐ. -/
theorem actual_obl_implies_dia_neg {c : Type*} (ctx : c) (v : w) (φ : Meaning c w)
    (hoa : actual_obl F φ ctx v) : dia_a F (pnot φ) ctx v :=
  let ⟨v', hav, hna⟩ := hoa.2
  ⟨v', hav, hna⟩

/-- Ideal obligation implies ◇ₚφ (the obligation is satisfiable). -/
theorem ideal_obl_implies_dia {c : Type*} (ctx : c) (v : w) (φ : Meaning c w)
    (hoi : ideal_obl F φ ctx v) : dia_p F φ ctx v :=
  let ⟨v', hpv, hφ⟩ := F.sem_5ab hoi.1
  ⟨v', hpv, hφ⟩

/-- Ideal obligation implies ◇ₚ(¬φ) (violation is possible). -/
theorem ideal_obl_implies_dia_neg {c : Type*} (ctx : c) (v : w) (φ : Meaning c w)
    (hoi : ideal_obl F φ ctx v) : dia_p F (pnot φ) ctx v :=
  let ⟨v', hpv, hna⟩ := hoi.2
  ⟨v', hpv, hna⟩

/-- Kant's law for actual obligation: □ₐφ implies ¬Oₐφ.
    If φ is necessary, it cannot be obligatory (no violation possible).
    CJDDLplus.thy:162. -/
theorem box_a_implies_not_actual_obl {c : Type*} (ctx : c) (v : w) (φ : Meaning c w)
    (hbox : box_a F φ ctx v) : ¬ actual_obl F φ ctx v :=
  fun ⟨_, v', hav, hna⟩ => hna (hbox v' hav)

/-- Kant's law for ideal obligation: □ₚφ implies ¬Oᵢφ. -/
theorem box_p_implies_not_ideal_obl {c : Type*} (ctx : c) (v : w) (φ : Meaning c w)
    (hbox : box_p F φ ctx v) : ¬ ideal_obl F φ ctx v :=
  fun ⟨_, v', hpv, hna⟩ => hna (hbox v' hpv)

end Mettapedia.Logic.DDLPlus.DTSBridge
