import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchFundamental
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchValidityControls

/-!
# Controls: the fundamental lemma relative to the constants a derivation uses

* **Positive: stages of constants** (`sucMoveZero_valid`). The closed derivation of
  `sucMove zero : eqAt zero → eqAt (suc zero)` uses `sucMove`, adequate by the lemma within
  the constants of its right side, and, in its declared type, `eqAt`, adequate by the lemma
  within the constants of its own right side, with the numbers. Within all of them the
  lemma makes the typing valid.
* **Negative: a constant outside the allowed ones is not covered.** No typing of `sucMove`
  (`sucMove_not_within`), nor of `sucMove zero` (`sucMoveZero_not_within`), is derivable
  within the constants of `sucMove`'s right side; within one more constant, `sucMove`
  itself, both are (`csucMove_typed_within`, `sucMoveZero_typed_within`).
* **Negative: the constants' adequacy is needed.** Under the core weak-head reduction,
  which takes no step at a numeral addition inspects, every other hypothesis of the
  lemma holds: the reading is valid, the non-universe heads are rigid ground types, head
  equality is trivial on them, and the decoder is stuck at universes
  (`coreReduction_decoderStuck`). The typing `add 0 (add 0 0) : num` is derivable within
  `num`, `zero` and `add` (`stuckZero_typed_within`), and it is not valid
  (`stuckZero_not_valid`): its denotation is zero, at whose tag the relation asks it to
  reduce to zero, and it takes no core step. So the allowed constants are not all adequate
  there (`stuckAllowed_not_adequate`); `num` and `zero` are, so addition is not
  (`add_not_constAdequate_core`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal (TypedAt natI)
open Package (jName eqAtName sucMoveName)

namespace CodeModel
namespace FundamentalControls

open ValidityControls (coreReduction stuckZero stuckZero_eq stuckZero_normal)

/-! ## Positive: stages of constants -/

section Stages

/-- The constants up to the successor move: those of its right side, and itself. -/
abbrev sucMoveStageAllowed : DeclName → Bool :=
  allowedIn [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName]

/-- The constants up to the successor move are adequate: the successor move by the lemma
within the constants of its right side (`constAdequateAt_sucMove'`). -/
theorem sucMoveStageAllowed_adequate :
    ∀ {c : DeclName}, sucMoveStageAllowed c = true →
      ConstAdequateAt objectChurchReading objectHeadReduction c :=
  consts_allowedIn fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact constAdequateAt_num objectExtension
    · exact constAdequateAt_zero objectExtension
    · exact constAdequateAt_suc objectExtension
    · exact constAdequateAt_add objectExtension
    · exact constAdequateAt_j objectExtension
    · exact constAdequateAt_eqAt objectExtension
    · exact constAdequateAt_sucMove' objectExtension

variable {A : DeclName → Bool}

/-- The declared type of the successor move, formed within `num`, `suc` and `eqAt`. -/
theorem csucMoveType_formed_within (hn : A numN = true) (hs : A sucN = true)
    (he : A eqAtName = true) :
    CTyped (objectChurch.restrict A) .nil (liftTm Package.sucMoveType) cU0 := by
  show CTyped (objectChurch.restrict A) .nil
    (.pi cnum (.pi (ceqAt (.var 0)) (ceqAt (csuc (.var 1))))) cU0
  exact cpiT_within (cnum_typed_within hn) (cpiT_within (ceqAt_typed_within he hn (.var 0))
    (ceqAt_typed_within he hn (csuc_typed_within hs hn (.var 1))))

/-- The successor move at its declared type, within constants that include it. -/
theorem csucMove_typed_within {n : Nat} {Γ : CCtx Tower.Head n} (hm : A sucMoveName = true)
    (hn : A numN = true) (hs : A sucN = true) (he : A eqAtName = true) :
    CTyped (objectChurch.restrict A) Γ (.const sucMoveName)
      (liftTm Package.sucMoveType).liftClosed :=
  cconst_within Package.sucMoveType hm (by decide) (by decide) (csucMoveType_formed_within hn hs he)

/-- `⊢ sucMove zero : eqAt zero → eqAt (suc zero)`, within the constants up to the successor
move. -/
theorem sucMoveZero_typed_within :
    CTyped (objectChurch.restrict sucMoveStageAllowed) .nil (.app (.const sucMoveName) czero)
      (.pi (ceqAt czero) (ceqAt (csuc czero))) :=
  .appElim (A := cnum) (B := .pi (ceqAt (.var 0)) (ceqAt (csuc (.var 1))))
    (csucMove_typed_within rfl rfl rfl rfl) (czero_typed_within rfl rfl)

/-- **Positive control: the lemma on a closed derivation using stages of constants.** The
typing of `sucMove zero` is valid: its constants are adequate, the successor move by the
lemma within the constants of its right side, and `eqAt` by the lemma within those of its
own. -/
theorem sucMoveZero_valid :
    (CStatement.typing .nil (.app (.const sucMoveName) czero)
      (.pi (ceqAt czero) (ceqAt (csuc czero)))).Valid objectChurchReading objectHeadReduction :=
  objectExtension.valid_within sucMoveStageAllowed_adequate sucMoveZero_typed_within .nil

end Stages

/-! ## Negative: a constant outside the allowed ones -/

section Outside

/-- **The successor move is not covered within the constants of its right side**: no
typing of it is derivable there, since it is not declared there. -/
theorem sucMove_not_within {n : Nat} {Γ : CCtx Tower.Head n} (T : CTm Tower.Head n) :
    ¬ CTyped (objectChurch.restrict sucMoveAllowed) Γ (.const sucMoveName) T := by
  intro h
  obtain ⟨type, u, declared, -⟩ := h.generation
  rw [ChurchRules.restrict_undeclared (by decide)] at declared
  cases declared

/-- **Nor is `sucMove zero`**: a typing of an application types its function. -/
theorem sucMoveZero_not_within {n : Nat} {Γ : CCtx Tower.Head n} (T : CTm Tower.Head n) :
    ¬ CTyped (objectChurch.restrict sucMoveAllowed) Γ (.app (.const sucMoveName) czero) T := by
  intro h
  obtain ⟨A', B, tf, -, -⟩ := h.generation
  exact sucMove_not_within _ tf

end Outside

/-! ## Negative: the constants' adequacy is needed -/

section Needed

/-- The constants of `add 0 (add 0 0)`: `num`, `zero` and `add`. -/
abbrev stuckAllowed : DeclName → Bool := allowedIn [numN, zeroN, addN]

/-- `⊢ add 0 (add 0 0) : num`, within `num`, `zero` and `add`. -/
theorem stuckZero_typed_within :
    CTyped (objectChurch.restrict stuckAllowed) .nil (stuckZero : CTm Tower.Head 0) cnum :=
  cadd_typed_within rfl rfl (czero_typed_within rfl rfl)
    (cadd_typed_within rfl rfl (czero_typed_within rfl rfl) (czero_typed_within rfl rfl))

/-- **The decoder is stuck at universes under the core reduction**, whose steps are steps
of the object package's reduction. -/
theorem coreReduction_decoderStuck : coreReduction.DecoderStuckAtUniverses :=
  fun hu u s => objectExtension.decoderStuck hu u (s.step objectHeadReduction)

/-- **`add 0 (add 0 0) : num` is not valid under the core reduction**: its denotation is
zero, at whose tag the relation asks it to reduce to zero, and it takes no core step. -/
theorem stuckZero_not_valid :
    ¬ (CStatement.typing .nil (stuckZero : CTm Tower.Head 0) cnum).Valid objectChurchReading
      coreReduction := by
  intro h
  have hs :
      (cinterp objectChurchReading (stuckZero : CTm Tower.Head 0) Env.nil).Mem (.tag .zero) := by
    rw [objectChurch_soundnessFacts.equality (stuckZero_eq (Γ := .nil)) Env.nil trivial]
    show (objectChurchReading.const zeroN).Mem (.tag .zero)
    rw [objectChurchReading_zero]
    exact Ideal.zeroI_mem_zero
  have hT :
      TypedAt (cinterp objectChurchReading (cnum : CTm Tower.Head 0) Env.nil) (.tag .zero) := by
    rw [cinterp_cnum]
    exact ⟨Elem.nat, Ideal.below_nat, Ideal.nat_type, tyTok_tag_zero.2 List.mem_cons_self⟩
  have r := h.1 Env.nil trivial (Δ := .nil) .nil SubstRel.nil (.tag .zero) hs hT
  obtain ⟨-, hred, -⟩ := RT.tm_zero_iff.1 r
  have e := coreReduction.red_normal stuckZero_normal hred.1
  cases e

/-- **The constants' adequacy is needed**: under the core reduction every other hypothesis
of the fundamental lemma holds, and its conclusion fails for a derivation within `num`,
`zero` and `add`; so these constants are not all adequate there. -/
theorem stuckAllowed_not_adequate :
    ¬ ∀ {c : DeclName}, stuckAllowed c = true →
      ConstAdequateAt objectChurchReading coreReduction c :=
  fun consts => stuckZero_not_valid (CDerivable.valid ConvRules.objectLevels
    objectChurchReading_valid
    objectExtension.groundHeads objectRules_groundHeadEq coreReduction_decoderStuck consts
    stuckZero_typed_within CCtxFormed.nil)

/-- `zero` is adequate under every head reduction of the object package. -/
theorem adequate_czero_at (H : HeadReduction objectChurch objectRigid) :
    Adequate objectChurchReading H .nil czero cnum := by
  intro ρ _ m Δ σ σ' _ _ s hs _
  have hs' : ent Elem.zero s = true := by
    have h : (objectChurchReading.const zeroN).Mem s := hs
    rwa [objectChurchReading_zero] at h
  refine RT.closed' hs' fun q hq => ?_
  rw [List.mem_singleton.1 hq]
  exact RT.tm_zero_iff.2 ⟨CRedTy.refl ⟨_, .sort _, cnum_typed⟩, CRedTm.refl czero_typed,
    CRedTm.refl czero_typed⟩

/-- **Addition is not adequate under the core reduction**: `num` and `zero` are, so the
failure of `stuckAllowed_not_adequate` is addition's. -/
theorem add_not_constAdequate_core : ¬ ConstAdequateAt objectChurchReading coreReduction addN := by
  intro hadd
  refine stuckAllowed_not_adequate (consts_allowedIn fun c hc => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ConstAdequateAt.of_adequate (objectChurch_declared (c := numN) (T := Package.U0)
      (by decide) rfl) ((adequateType_typeAt objectExtension (H := coreReduction) (.base .num)
        (.nil : CCtx Tower.Head 0)).adequate ConvRules.objectLevels objectChurch_soundnessFacts
          (.sort Tower.zero))
  · exact ConstAdequateAt.of_adequate (objectChurch_declared (c := zeroN) (T := Package.numT)
      (by decide) rfl) (adequate_czero_at coreReduction)
  · exact hadd

end Needed

end FundamentalControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
