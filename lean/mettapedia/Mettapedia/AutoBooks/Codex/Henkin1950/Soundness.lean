import Mettapedia.AutoBooks.Codex.Henkin1950.Semantics
import Mettapedia.Logic.HOL.Soundness

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-- Closed theorems in the trusted HOL derivation system over Henkin's paper signature. -/
abbrev Theorem (φ : Sentence) : Prop := Derivation.Theorem Primitive φ

/-- Open derivations from no assumptions, for paper axiom schemata with free variables. -/
abbrev TheoremInContext {Γ : Ctx Atom} (φ : Formula Γ) : Prop :=
  Derivation Primitive [] φ

/-- The trusted HOL soundness theorem, specialized to the Henkin (1950) signature. -/
theorem theorem_validInGeneral {φ : Sentence} :
    Theorem φ → ValidInGeneral φ := by
  intro h M
  exact Mettapedia.Logic.HOL.Soundness.theorem_sound h M.toHenkinModel

/-- Open theorem soundness for paper schemata with free variables. -/
theorem theoremInContext_validInGeneral {Γ : Ctx Atom} {φ : Formula Γ} :
    TheoremInContext φ → ValidInGeneralCtx φ := by
  intro h M ρ hρ
  exact Mettapedia.Logic.HOL.Soundness.derivation_sound h hρ (by
    intro ψ hψ
    nomatch hψ)

/-- Theorem 2, forward open-formula form: every theorem is valid in the
paper's general-model sense under all admissible assignments. -/
theorem theorem2_forward_ctx {Γ : Ctx Atom} {φ : Formula Γ} :
    TheoremInContext φ → ValidInGeneralCtx φ :=
  theoremInContext_validInGeneral

/-- Theorem 2, forward closed-sentence specialization. -/
theorem theorem2_forward_sentence {φ : Sentence} :
    Theorem φ → ValidInGeneral φ :=
  theorem_validInGeneral

/-- The trusted HOL theorem system does not prove falsity over Henkin's paper
signature, because falsity is not valid in general models. -/
theorem not_theorem_bot : ¬ Theorem (.bot : Sentence) := by
  intro h
  exact not_validInGeneral_bot (theorem_validInGeneral h)

/-- Standard soundness follows because every standard model is a general model. -/
theorem theorem_validInStandard {φ : Sentence} :
    Theorem φ → ValidInStandard φ := by
  intro h
  exact validInStandard_of_validInGeneral (theorem_validInGeneral h)

/-- Positive canary: every sentence implies itself in all general models. -/
theorem imp_self_validInGeneral (φ : Sentence) :
    ValidInGeneral (.imp φ φ) :=
  theorem_validInGeneral (Derivation.theorem_imp_refl (Const := Primitive) φ)

/-- Positive canary: every sentence implies itself in all standard models. -/
theorem imp_self_validInStandard (φ : Sentence) :
    ValidInStandard (.imp φ φ) :=
  theorem_validInStandard (Derivation.theorem_imp_refl (Const := Primitive) φ)

end Mettapedia.AutoBooks.Codex.Henkin1950
