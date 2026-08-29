import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularNormalization

/-!
# Subject reduction for the regular Pure kernel

The executable regular checker normalizes inferred types before inspecting
their heads.  This is sound only if regular formation is preserved along the
normalization path.  This module proves that prerequisite for the
presupposition-closed `RegularHasType` judgment.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Confluence
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing

private def regularTmOf {Γ : Ctx n} {term type : PureTm n}
    (_ : RegularHasType Γ term type) : PureTm n := term

namespace ConstantFreeConv

/-- Between declaration-free endpoints, raw conversion has a canonical
fragment-internal representative obtained from Church--Rosser.  This does not
identify proof fibres: it constructs a new fragment-respecting path. -/
theorem of_conv {left right : PureTm n} (conversion : Conv left right)
    (leftPure : ConstantFree left) (rightPure : ConstantFree right) :
    ConstantFreeConv left right := by
  rcases church_rosser_conv conversion with ⟨common, leftSteps, rightSteps⟩
  exact .trans (leftPure.redStar leftSteps).1
    (.symm (rightPure.redStar rightSteps).1)

/-- Fragment conversion is injective at dependent-function constructors. -/
theorem pi_injective {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (conversion : ConstantFreeConv (.pi A B) (.pi A' B')) :
    ConstantFreeConv A A' ∧ ConstantFreeConv B B' := by
  have pure := conversion.constantFree_both
  cases pure.1 with
  | pi hA hB =>
      cases pure.2 with
      | pi hA' hB' =>
          have components := pi_injectivity conversion.toConv
          exact ⟨of_conv components.1 hA hA', of_conv components.2 hB hB'⟩

/-- Fragment conversion is injective at dependent-pair constructors. -/
theorem sigma_injective {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (conversion : ConstantFreeConv (.sigma A B) (.sigma A' B')) :
    ConstantFreeConv A A' ∧ ConstantFreeConv B B' := by
  have pure := conversion.constantFree_both
  cases pure.1 with
  | sigma hA hB =>
      cases pure.2 with
      | sigma hA' hB' =>
          have components := sigma_injectivity conversion.toConv
          exact ⟨of_conv components.1 hA hA', of_conv components.2 hB hB'⟩

/-- Converting the argument converts its occurrences in a dependent family. -/
theorem inst0_argument {left right : PureTm n} {body : PureTm (n + 1)}
    (conversion : ConstantFreeConv left right) (bodyPure : ConstantFree body) :
    ConstantFreeConv (inst0 left body) (inst0 right body) := by
  rcases church_rosser_conv conversion.toConv with
    ⟨common, leftSteps, rightSteps⟩
  have leftPath := redStar_inst0_argument body leftSteps
  have rightPath := redStar_inst0_argument body rightSteps
  have endpoints := conversion.constantFree_both
  exact .trans ((endpoints.1.inst0 bodyPure).redStar leftPath).1
    (.symm ((endpoints.2.inst0 bodyPure).redStar rightPath).1)

/-- Converting a dependent family converts its instantiation. -/
theorem inst0_body {argument : PureTm n} {left right : PureTm (n + 1)}
    (conversion : ConstantFreeConv left right)
    (argumentPure : ConstantFree argument) :
    ConstantFreeConv (inst0 argument left) (inst0 argument right) := by
  simpa [inst0] using conversion.subst (subst0 argument)
    (fun index => Fin.cases argumentPure (fun preceding => .var preceding) index)

end ConstantFreeConv

namespace RegularCtxMor

/-- Identity syntax transports from a context headed by `source` to one headed
by a convertible `target`.  Formation of both endpoints is explicit. -/
def convertHead {Γ : Ctx n} {source target : PureTm n}
    (sourceFormed : RegularHasType Γ source .u1)
    (conversion : ConstantFreeConv source target) :
    RegularCtxMor (.snoc Γ source) (.snoc Γ target) ids where
  typing := by
    intro index
    refine Fin.cases ?_ ?_ index
    · have variableTyping : RegularHasType (.snoc Γ target) (.var 0)
          (rename wk target) := by
        simpa [lookup_snoc_zero] using
          (RegularHasType.var (Γ := .snoc Γ target) (i := (0 : Fin (n + 1))))
      have sourceWeak : RegularHasType (.snoc Γ target)
          (rename wk source) .u1 := sourceFormed.weaken
      have converted := RegularHasType.conv_type variableTyping sourceWeak
        ((conversion.rename wk).symm)
      simpa [lookup_snoc_zero, subst_ids, ids] using converted
    · intro preceding
      simpa [lookup_snoc_succ, subst_ids, ids, Renaming.rename] using
        (RegularHasType.var
          (Γ := .snoc Γ target) (i := Fin.succ preceding))
  constantFree := fun index => .var index

end RegularCtxMor

/-- Regular typing transports across conversion of the newest context type. -/
theorem RegularHasType.context_convert_head
    {Γ : Ctx n} {source target : PureTm n} {term type : PureTm (n + 1)}
    (sourceFormed : RegularHasType Γ source .u1)
    (conversion : ConstantFreeConv source target)
    (typing : RegularHasType (.snoc Γ source) term type) :
    RegularHasType (.snoc Γ target) term type := by
  simpa [subst_ids] using
    typing.subst (RegularCtxMor.convertHead sourceFormed conversion)

/-! ## Generation for the two computational introduction forms -/

private theorem regular_lam_generation_aux
    {Γ : Ctx n} {term C : PureTm n} (typing : RegularHasType Γ term C) :
    ∀ {body : PureTm (n + 1)}, term = .lam body →
      ∃ A B,
        RegularHasType Γ A .u1 ∧
        RegularHasType (.snoc Γ A) B .u1 ∧
        RegularHasType (.snoc Γ A) body B ∧
        Conv (.pi A B) C := by
  induction typing with
  | lam_intro hA hB hBody ihA ihB ihBody =>
      intro body equal
      cases equal
      exact ⟨_, _, hA, hB, hBody, Relation.EqvGen.refl _⟩
  | conv_type term target conversion ihTerm ihTarget =>
      intro body equal
      rcases ihTerm equal with ⟨A, B, hA, hB, hBody, hPi⟩
      exact ⟨A, B, hA, hB, hBody,
        Relation.EqvGen.trans _ _ _ hPi conversion.toConv⟩
  | conv_sort term conversion ihTerm =>
      intro body equal
      rcases ihTerm equal with ⟨A, B, hA, hB, hBody, hPi⟩
      exact ⟨A, B, hA, hB, hBody,
        Relation.EqvGen.trans _ _ _ hPi conversion.toConv⟩
  | u0_type => simp
  | var => simp
  | pi_form => simp
  | sigma_form => simp
  | app_elim => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

theorem regular_lam_generation
    {Γ : Ctx n} {body : PureTm (n + 1)} {C : PureTm n}
    (typing : RegularHasType Γ (.lam body) C) :
    ∃ A B,
      RegularHasType Γ A .u1 ∧
      RegularHasType (.snoc Γ A) B .u1 ∧
      RegularHasType (.snoc Γ A) body B ∧
      Conv (.pi A B) C :=
  regular_lam_generation_aux typing rfl

private theorem regular_pair_generation_aux
    {Γ : Ctx n} {term C : PureTm n} (typing : RegularHasType Γ term C) :
    ∀ {first second : PureTm n}, term = .pair first second →
      ∃ A B,
        RegularHasType Γ A .u1 ∧
        RegularHasType Γ first A ∧
        RegularHasType Γ second (inst0 first B) ∧
        RegularHasType (.snoc Γ A) B .u1 ∧
        Conv (.sigma A B) C := by
  induction typing with
  | pair_intro hA hFirst hSecond hB ihA ihFirst ihSecond ihB =>
      intro first second equal
      cases equal
      exact ⟨_, _, hA, hFirst, hSecond, hB, Relation.EqvGen.refl _⟩
  | conv_type term target conversion ihTerm ihTarget =>
      intro first second equal
      rcases ihTerm equal with
        ⟨A, B, hA, hFirst, hSecond, hB, hSigma⟩
      exact ⟨A, B, hA, hFirst, hSecond, hB,
        Relation.EqvGen.trans _ _ _ hSigma conversion.toConv⟩
  | conv_sort term conversion ihTerm =>
      intro first second equal
      rcases ihTerm equal with
        ⟨A, B, hA, hFirst, hSecond, hB, hSigma⟩
      exact ⟨A, B, hA, hFirst, hSecond, hB,
        Relation.EqvGen.trans _ _ _ hSigma conversion.toConv⟩
  | u0_type => simp
  | var => simp
  | pi_form => simp
  | sigma_form => simp
  | lam_intro => simp
  | app_elim => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

theorem regular_pair_generation
    {Γ : Ctx n} {first second C : PureTm n}
    (typing : RegularHasType Γ (.pair first second) C) :
    ∃ A B,
      RegularHasType Γ A .u1 ∧
      RegularHasType Γ first A ∧
      RegularHasType Γ second (inst0 first B) ∧
      RegularHasType (.snoc Γ A) B .u1 ∧
      Conv (.sigma A B) C :=
  regular_pair_generation_aux typing rfl

/-! ## Preservation -/

/-- One-step reduction preserves the presupposition-closed regular judgment. -/
theorem RegularHasType.subject_reduction
    {Γ : Ctx n} {term reduct type : PureTm n}
    (context : RegularCtx Γ) (typing : RegularHasType Γ term type)
    (step : Red term reduct) : RegularHasType Γ reduct type := by
  induction typing with
  | u0_type => cases step
  | var => cases step
  | @pi_form n Γ A B hA hB ihA ihB =>
      cases step with
      | congPiDom domainStep =>
          have hA' := ihA context domainStep
          have sourcePure := (hA.constantFree_both context.constantFreeCtx).1
          have conversion : ConstantFreeConv A _ :=
            .rel ⟨domainStep, sourcePure, sourcePure.red domainStep⟩
          exact .pi_form hA'
            (RegularHasType.context_convert_head hA conversion hB)
      | congPiCod codomainStep =>
          exact .pi_form hA (ihB (.snoc context hA) codomainStep)
  | @sigma_form n Γ A B hA hB ihA ihB =>
      cases step with
      | congSigmaDom domainStep =>
          have hA' := ihA context domainStep
          have sourcePure := (hA.constantFree_both context.constantFreeCtx).1
          have conversion : ConstantFreeConv A _ :=
            .rel ⟨domainStep, sourcePure, sourcePure.red domainStep⟩
          exact .sigma_form hA'
            (RegularHasType.context_convert_head hA conversion hB)
      | congSigmaCod codomainStep =>
          exact .sigma_form hA (ihB (.snoc context hA) codomainStep)
  | @lam_intro n Γ A body B hA hB hBody ihA ihB ihBody =>
      cases step with
      | congLam bodyStep =>
          exact .lam_intro hA hB
            (ihBody (.snoc context hA) bodyStep)
  | @app_elim n Γ function argument A B hA hFunction hArgument hB
      ihA ihFunction ihArgument ihB =>
      cases step with
      | betaPi body argument =>
          rcases regular_lam_generation hFunction with
            ⟨A₁, B₁, hA₁, hB₁, hBody, piConversion⟩
          have components := pi_injectivity piConversion
          have contextPure := context.constantFreeCtx
          have sourceA := (hA₁.constantFree_both contextPure).1
          have targetA := (hA.constantFree_both contextPure).1
          have domainConversion : ConstantFreeConv A₁ A :=
            ConstantFreeConv.of_conv components.1 sourceA targetA
          have sourceB :=
            (hB₁.constantFree_both
              (RegularCtx.snoc context hA₁).constantFreeCtx).1
          have targetB :=
            (hB.constantFree_both
              (RegularCtx.snoc context hA).constantFreeCtx).1
          have codomainConversion : ConstantFreeConv B₁ B :=
            ConstantFreeConv.of_conv components.2 sourceB targetB
          have argumentAtSource : RegularHasType Γ argument A₁ :=
            .conv_type hArgument hA₁ domainConversion.symm
          have contractum : RegularHasType Γ (inst0 argument body)
              (inst0 argument B₁) :=
            hBody.instantiate argumentAtSource contextPure
          have targetFormed : RegularHasType Γ (inst0 argument B) .u1 :=
            hB.instantiate hArgument contextPure
          exact .conv_type contractum targetFormed
            (codomainConversion.inst0_body
              (hArgument.constantFree_both contextPure).1)
      | congAppFun functionStep =>
          exact .app_elim hA (ihFunction context functionStep) hArgument hB
      | congAppArg argumentStep =>
          have argumentTyping := ihArgument context argumentStep
          have applicationTyping :=
            RegularHasType.app_elim hA hFunction argumentTyping hB
          have contextPure := context.constantFreeCtx
          have argumentPure :=
            (hArgument.constantFree_both contextPure).1
          have reductPure := argumentPure.red argumentStep
          have argumentConversion : ConstantFreeConv argument _ :=
            .rel ⟨argumentStep, argumentPure, reductPure⟩
          have bodyPure :=
            (hB.constantFree_both
              (RegularCtx.snoc context hA).constantFreeCtx).1
          have targetFormed : RegularHasType Γ (inst0 argument B) .u1 :=
            hB.instantiate hArgument contextPure
          exact .conv_type applicationTyping targetFormed
            (argumentConversion.inst0_argument bodyPure).symm
  | @pair_intro n Γ first second A B hA hFirst hSecond hB
      ihA ihFirst ihSecond ihB =>
      cases step with
      | congPairFst firstStep =>
          have firstTyping := ihFirst context firstStep
          have contextPure := context.constantFreeCtx
          have firstPure := (hFirst.constantFree_both contextPure).1
          have firstConversion : ConstantFreeConv first _ :=
            .rel ⟨firstStep, firstPure, firstPure.red firstStep⟩
          have bodyPure :=
            (hB.constantFree_both
              (RegularCtx.snoc context hA).constantFreeCtx).1
          have secondTargetFormed : RegularHasType Γ (inst0 _ B) .u1 :=
            hB.instantiate firstTyping contextPure
          have secondTyping := RegularHasType.conv_type hSecond
            secondTargetFormed
            (firstConversion.inst0_argument bodyPure)
          exact .pair_intro hA firstTyping secondTyping hB
      | congPairSnd secondStep =>
          exact .pair_intro hA hFirst
            (ihSecond context secondStep) hB
  | @fst_elim n Γ pair A B hA hPair hB ihA ihPair ihB =>
      cases step with
      | betaSigmaFst first second =>
          rcases regular_pair_generation hPair with
            ⟨A₁, B₁, hA₁, hFirst, hSecond, hB₁, sigmaConversion⟩
          have components := sigma_injectivity sigmaConversion
          have contextPure := context.constantFreeCtx
          have sourceA := (hA₁.constantFree_both contextPure).1
          have targetA := (hA.constantFree_both contextPure).1
          exact .conv_type hFirst hA
            (ConstantFreeConv.of_conv components.1 sourceA targetA)
      | congFst pairStep =>
          exact .fst_elim hA (ihPair context pairStep) hB
  | @snd_elim n Γ pair A B hA hPair hB ihA ihPair ihB =>
      cases step with
      | betaSigmaSnd first second =>
          rcases regular_pair_generation hPair with
            ⟨A₁, B₁, hA₁, hFirst, hSecond, hB₁, sigmaConversion⟩
          have components := sigma_injectivity sigmaConversion
          have contextPure := context.constantFreeCtx
          have sourceB :=
            (hB₁.constantFree_both
              (RegularCtx.snoc context hA₁).constantFreeCtx).1
          have targetB :=
            (hB.constantFree_both
              (RegularCtx.snoc context hA).constantFreeCtx).1
          have codomainConversion : ConstantFreeConv B₁ B :=
            ConstantFreeConv.of_conv components.2 sourceB targetB
          have firstPure := (hFirst.constantFree_both contextPure).1
          have secondPure := (hSecond.constantFree_both contextPure).1
          have pairPure : ConstantFree (.pair first reduct) := by
            exact .pair firstPure secondPure
          have projectionConversion :
              ConstantFreeConv first (.fst (.pair first reduct)) :=
            (ConstantFreeConv.rel ⟨Red.betaSigmaFst first reduct,
              .fst pairPure, firstPure⟩).symm
          have throughCodomain :=
            (codomainConversion.inst0_body firstPure).trans
              (projectionConversion.inst0_argument targetB)
          have targetFormed :
              RegularHasType Γ
                (inst0 (.fst (.pair first reduct)) B) .u1 :=
            hB.instantiate (.fst_elim hA hPair hB) contextPure
          exact RegularHasType.conv_type hSecond targetFormed throughCodomain
      | congSnd pairStep =>
          have pairTyping := ihPair context pairStep
          have projected := RegularHasType.snd_elim hA pairTyping hB
          have contextPure := context.constantFreeCtx
          have pairPure := (hPair.constantFree_both contextPure).1
          have reductPure := pairPure.red pairStep
          have fstConversion : ConstantFreeConv (.fst pair) (.fst _) :=
            .rel ⟨.congFst pairStep, .fst pairPure, .fst reductPure⟩
          have bodyPure :=
            (hB.constantFree_both
              (RegularCtx.snoc context hA).constantFreeCtx).1
          have targetFormed : RegularHasType Γ (inst0 (.fst pair) B) .u1 :=
            hB.instantiate (.fst_elim hA hPair hB) contextPure
          exact .conv_type projected targetFormed
            (fstConversion.inst0_argument bodyPure).symm
  | @id_form n Γ A left right hA hLeft hRight ihA ihLeft ihRight =>
      cases step with
      | congIdTy typeStep =>
          have typeTyping := ihA context typeStep
          have contextPure := context.constantFreeCtx
          have typePure := (hA.constantFree_both contextPure).1
          have typeConversion : ConstantFreeConv A _ :=
            .rel ⟨typeStep, typePure, typePure.red typeStep⟩
          exact .id_form typeTyping
            (.conv_type hLeft typeTyping typeConversion)
            (.conv_type hRight typeTyping typeConversion)
      | congIdLeft leftStep =>
          exact .id_form hA (ihLeft context leftStep) hRight
      | congIdRight rightStep =>
          exact .id_form hA hLeft (ihRight context rightStep)
  | @refl_intro n Γ term A hA hTerm ihA ihTerm =>
      cases step with
      | congRefl termStep =>
          have termTyping := ihTerm context termStep
          have contextPure := context.constantFreeCtx
          have typePure := (hA.constantFree_both contextPure).1
          have termPure := (hTerm.constantFree_both contextPure).1
          have reductPure := termPure.red termStep
          let reductTerm : PureTm n := regularTmOf termTyping
          have oldIdentityPure : ConstantFree (.id A term term) :=
            .id typePure termPure termPure
          have middlePure : ConstantFree (.id A reductTerm term) :=
            .id typePure reductPure termPure
          have newIdentityPure : ConstantFree (.id A reductTerm reductTerm) :=
            .id typePure reductPure reductPure
          have identityConversion :
              ConstantFreeConv (.id A term term)
                (.id A reductTerm reductTerm) :=
            (ConstantFreeConv.rel ⟨.congIdLeft termStep,
              oldIdentityPure, middlePure⟩).trans
              (ConstantFreeConv.rel ⟨.congIdRight termStep,
                middlePure, newIdentityPure⟩)
          simpa [reductTerm] using
            (RegularHasType.conv_type (.refl_intro hA termTyping)
              (.id_form hA hTerm hTerm) identityConversion.symm)
  | conv_type term target conversion ihTerm ihTarget =>
      exact .conv_type (ihTerm context step) target conversion
  | conv_sort term conversion ihTerm =>
      exact .conv_sort (ihTerm context step) conversion

/-- A finite normalization path preserves regular typing. -/
theorem RegularHasType.subject_reduction_star
    {Γ : Ctx n} {term reduct type : PureTm n}
    (context : RegularCtx Γ) (typing : RegularHasType Γ term type)
    (steps : RedStar term reduct) : RegularHasType Γ reduct type := by
  induction steps with
  | refl => exact typing
  | tail earlier finalStep ih =>
      exact ih.subject_reduction context finalStep

/-! ## Axiom audit -/

#print axioms ConstantFreeConv.of_conv
#print axioms ConstantFreeConv.pi_injective
#print axioms ConstantFreeConv.sigma_injective
#print axioms RegularHasType.context_convert_head
#print axioms regular_lam_generation
#print axioms regular_pair_generation
#print axioms RegularHasType.subject_reduction
#print axioms RegularHasType.subject_reduction_star

end Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
