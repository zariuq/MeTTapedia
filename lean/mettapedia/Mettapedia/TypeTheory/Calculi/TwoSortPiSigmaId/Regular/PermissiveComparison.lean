import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Typing
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing

/-! # Regular typing as a strict subrelation of permissive typing -/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming

/-- Forgetting the regularity witnesses recovers an authored intrinsic typing
derivation. -/
theorem RegularHasType.toHasType (h : RegularHasType Γ t A) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A := by
  induction h with
  | u0_type Γ => exact .u0_type Γ
  | var i => exact .var i
  | pi_form _ _ ihA ihB => exact .pi_form ihA ihB
  | sigma_form _ _ ihA ihB => exact .sigma_form ihA ihB
  | lam_intro _ _ _ ihA ihB ihBody => exact .lam_intro ihBody
  | app_elim _ _ _ _ ihA ihf iha ihB => exact .app_elim ihf iha
  | pair_intro _ _ _ _ ihA iha ihb ihB => exact .pair_intro iha ihb
  | fst_elim _ _ _ ihA ihp ihB => exact .fst_elim ihp
  | snd_elim _ _ _ ihA ihp ihB => exact .snd_elim ihp
  | id_form _ _ _ ihA iha ihb => exact .id_form ihA iha ihb
  | refl_intro _ _ ihA iha => exact .refl_intro iha
  | conv_type ht hB hconv iht ihB => exact .conv iht hconv.toConv
  | conv_sort ht hconv iht => exact .conv iht hconv.toConv

/-- Forgetting presupposition evidence yields the original permissive
intrinsic judgment. -/
theorem RegularJudgment.toHasType (h : RegularJudgment Γ t A) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A :=
  h.typing.toHasType

/-- The original raw judgment permits a lambda over `U1`, even though `U1`
has no type in this two-sort fragment. -/
theorem raw_allows_untyped_lambda_domain :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType (.nil : Ctx 0)
      (.lam (.var 0)) (.pi .u1 .u1) := by
  apply Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.lam_intro
  exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.var 0

/-! ### Specification ablations

Each presupposition is separated by a positive inhabitant and a negative
witness.  This makes the choice of spine auditable rather than editorial. -/

/-- The raw context syntax admits the top sort as an assumption. -/
def rawTopSortContext : Ctx 1 :=
  .snoc .nil .u1

/-- Raw variable typing consumes that malformed assumption without checking
its presupposition. -/
theorem raw_types_variable_in_top_sort_context :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType
      rawTopSortContext (.var 0) .u1 := by
  simpa [rawTopSortContext, rename] using
    (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.var
      (Γ := rawTopSortContext) (i := (0 : Fin 1)))

/-- Context formation rejects the same raw telescope. -/
theorem rawTopSortContext_not_regular : ¬ RegularCtx rawTopSortContext := by
  intro regular
  cases regular with
  | snoc hnil hTop => exact no_regular_u1_term hTop

/-- Consequently the malformed variable fact cannot cross the actual kernel
judgment boundary even though the underlying raw typing proposition holds. -/
theorem no_regular_judgment_in_top_sort_context :
    ¬ RegularJudgment rawTopSortContext (.var 0) .u1 := by
  intro judgment
  exact rawTopSortContext_not_regular judgment.context

/-- The permissive authored relation is a model of every regular rule after
presupposition evidence is forgotten. -/
theorem rawRegularRuleModel : RegularRuleModel
    (fun Γ t A =>
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A) where
  u0_type := fun Γ => .u0_type Γ
  var := fun i => .var i
  pi_form := fun hA hB => .pi_form hA hB
  sigma_form := fun hA hB => .sigma_form hA hB
  lam_intro := fun _hA _hB hBody => .lam_intro hBody
  app_elim := fun _hA hf ha _hB => .app_elim hf ha
  pair_intro := fun _hA ha hb _hB => .pair_intro ha hb
  fst_elim := fun _hA hp _hB => .fst_elim hp
  snd_elim := fun _hA hp _hB => .snd_elim hp
  id_form := fun hA ha hb => .id_form hA ha hb
  refl_intro := fun _hA ha => .refl_intro ha
  conv_type := fun ht _hB hconv => .conv ht hconv.toConv
  conv_sort := fun ht hconv => .conv ht hconv.toConv

/-- The forgetful inclusion follows from least rule closure, independently of
the hand-written structural proof above. -/
theorem regular_le_raw : TypingRelation.LE
    (fun Γ t A => RegularHasType Γ t A)
    (fun Γ t A =>
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A) :=
  RegularHasType.least rawRegularRuleModel

/-- The inclusion is strict: raw typing contains a concrete derivation that
the presupposition-closed relation rejects. -/
theorem raw_not_le_regular : ¬ TypingRelation.LE
    (fun Γ t A =>
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A)
    (fun Γ t A => RegularHasType Γ t A) := by
  intro inclusion
  exact regular_rejects_untyped_lambda_domain
    (inclusion raw_allows_untyped_lambda_domain)

/-- Exact ablation result for rule presuppositions: the regular relation is a
proper subrelation of the permissive authored relation. -/
theorem regular_strictly_below_raw :
    TypingRelation.LE
        (fun Γ t A => RegularHasType Γ t A)
        (fun Γ t A =>
          Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A) ∧
      ¬ TypingRelation.LE
        (fun Γ t A =>
          Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A)
        (fun Γ t A => RegularHasType Γ t A) :=
  ⟨regular_le_raw, raw_not_le_regular⟩

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular
