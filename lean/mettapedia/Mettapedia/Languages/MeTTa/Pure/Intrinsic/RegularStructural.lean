import Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

/-!
# Structural metatheory of the regular Pure judgment

The regular judgment is intended to be presupposition-closed: under a regular
context, every synthesized result is either the distinguished top sort `U1`
or is itself a well-formed type below `U1`.  This module proves that statement.

The proof is not obtained by adding formation checks to every elimination
rule.  Instead, renaming, simultaneous substitution, and inversion are proved
once, then application and dependent projections inherit formation from the
dependent family they eliminate.  The introduction rules retain exactly the
non-derivable premises: lambda codomain formation, dependent-pair domain
formation, and identity-carrier formation for reflexivity.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing

/-! ## Conversion is structural -/

namespace ConstantFreeConv

/-- Fragment-internal conversion commutes with renaming, including every
intermediate term in its proof fibre. -/
theorem rename {left right : PureTm n} (conversion : ConstantFreeConv left right)
    (ρ : Ren n m) :
    ConstantFreeConv (rename ρ left) (rename ρ right) := by
  induction conversion with
  | rel edge =>
      exact .rel ⟨red_rename edge.1 ρ,
        edge.2.1.rename ρ, edge.2.2.rename ρ⟩
  | refl term pure => exact .refl _ (pure.rename ρ)
  | symm conversion ih => exact .symm ih
  | trans left right ihLeft ihRight => exact .trans ihLeft ihRight

/-- Fragment-internal conversion commutes with a declaration-free
substitution, including every intermediate term in its proof fibre. -/
theorem subst {left right : PureTm n} (conversion : ConstantFreeConv left right)
    (substitution : Sub n m) (pure : ∀ index, ConstantFree (substitution index)) :
    ConstantFreeConv (subst substitution left) (subst substitution right) := by
  induction conversion with
  | rel edge =>
      exact .rel ⟨red_subst edge.1 substitution,
        edge.2.1.subst pure, edge.2.2.subst pure⟩
  | refl term termPure => exact .refl _ (termPure.subst pure)
  | symm conversion ih => exact .symm ih
  | trans left right ihLeft ihRight => exact .trans ihLeft ihRight

end ConstantFreeConv

/-! ## Renaming and weakening -/

namespace RegularHasType

/-- Regular typing is stable under a context-respecting renaming. -/
theorem rename {Γ : Ctx n} {term type : PureTm n}
    (typing : RegularHasType Γ term type) :
    ∀ {m : Nat} {Δ : Ctx m} {ρ : Ren n m},
      CtxRen Γ Δ ρ →
        RegularHasType Δ (Renaming.rename ρ term) (Renaming.rename ρ type) := by
  induction typing with
  | u0_type Γ =>
      intro m Δ ρ compatible
      simpa [Renaming.rename] using (RegularHasType.u0_type Δ)
  | var index =>
      intro m Δ ρ compatible
      simpa [Renaming.rename, compatible index] using
        (RegularHasType.var (Γ := Δ) (ρ index))
  | @pi_form n Γ A B hA hB ihA ihB =>
      intro m Δ ρ compatible
      have mappedA := ihA compatible
      have mappedB := ihB (CtxRen.snoc compatible A)
      simpa [Renaming.rename] using RegularHasType.pi_form mappedA mappedB
  | @sigma_form n Γ A B hA hB ihA ihB =>
      intro m Δ ρ compatible
      have mappedA := ihA compatible
      have mappedB := ihB (CtxRen.snoc compatible A)
      simpa [Renaming.rename] using RegularHasType.sigma_form mappedA mappedB
  | @lam_intro n Γ A body B hA hB hBody ihA ihB ihBody =>
      intro m Δ ρ compatible
      have mappedA := ihA compatible
      have extended := CtxRen.snoc compatible A
      have mappedB := ihB extended
      have mappedBody := ihBody extended
      simpa [Renaming.rename] using
        RegularHasType.lam_intro mappedA mappedB mappedBody
  | @app_elim n Γ function argument A B hA hf ha hB ihA ihf iha ihB =>
      intro m Δ ρ compatible
      simpa [Renaming.rename, rename_inst0] using
        RegularHasType.app_elim (ihA compatible) (ihf compatible) (iha compatible)
          (ihB (CtxRen.snoc compatible A))
  | @pair_intro n Γ first second A B hA ha hb hB ihA iha ihb ihB =>
      intro m Δ ρ compatible
      have mappedSecond : RegularHasType Δ (Renaming.rename ρ second)
          (inst0 (Renaming.rename ρ first) (Renaming.rename (liftRen ρ) B)) := by
        simpa [rename_inst0] using ihb compatible
      simpa [Renaming.rename] using
        RegularHasType.pair_intro (ihA compatible) (iha compatible)
          mappedSecond (ihB (CtxRen.snoc compatible A))
  | @fst_elim n Γ pair A B hA hp hB ihA ihp ihB =>
      intro m Δ ρ compatible
      simpa [Renaming.rename] using
        RegularHasType.fst_elim (ihA compatible) (ihp compatible)
          (ihB (CtxRen.snoc compatible A))
  | @snd_elim n Γ pair A B hA hp hB ihA ihp ihB =>
      intro m Δ ρ compatible
      simpa [Renaming.rename, rename_inst0] using
        RegularHasType.snd_elim (ihA compatible) (ihp compatible)
          (ihB (CtxRen.snoc compatible A))
  | @id_form n Γ A left right hA hLeft hRight ihA ihLeft ihRight =>
      intro m Δ ρ compatible
      simpa [Renaming.rename] using
        RegularHasType.id_form (ihA compatible) (ihLeft compatible)
          (ihRight compatible)
  | @refl_intro n Γ term A hA hTerm ihA ihTerm =>
      intro m Δ ρ compatible
      simpa [Renaming.rename] using
        RegularHasType.refl_intro (ihA compatible) (ihTerm compatible)
  | @conv_type n Γ term A B hTerm hB conversion ihTerm ihB =>
      intro m Δ ρ compatible
      exact RegularHasType.conv_type (ihTerm compatible) (ihB compatible)
        (conversion.rename ρ)
  | @conv_sort n Γ term A hTerm conversion ihTerm =>
      intro m Δ ρ compatible
      simpa [Renaming.rename] using
        RegularHasType.conv_sort (ihTerm compatible)
          (conversion.rename ρ)

/-- Weakening by one binder preserves regular typing. -/
theorem weaken {Γ : Ctx n} {term type U : PureTm n}
    (typing : RegularHasType Γ term type) :
    RegularHasType (.snoc Γ U) (Renaming.rename wk term)
      (Renaming.rename wk type) := by
  have compatible : CtxRen Γ (.snoc Γ U) wk := by
    intro index
    simp [wk]
  exact typing.rename compatible

end RegularHasType

/-! ## Simultaneous substitution -/

/-- A simultaneous substitution which preserves the regular typing assigned
to every source variable and remains inside the declaration-free syntax. -/
structure RegularCtxMor (source : Ctx n) (target : Ctx m)
    (substitution : Sub n m) : Prop where
  typing : ∀ index : Fin n,
    RegularHasType target (substitution index)
      (subst substitution (lookup source index))
  constantFree : ∀ index, ConstantFree (substitution index)

namespace RegularCtxMor

/-- A regular context morphism lifts through corresponding context
extensions. -/
theorem lift {Γ : Ctx n} {Δ : Ctx m} {substitution : Sub n m}
    (morphism : RegularCtxMor Γ Δ substitution) (A : PureTm n) :
    RegularCtxMor (.snoc Γ A) (.snoc Δ (subst substitution A))
      (liftSub substitution) := by
  refine ⟨?_, ?_⟩
  · intro index
    refine Fin.cases ?_ ?_ index
    · simpa [RegularCtxMor, lookup_snoc_zero, liftSub, subst_liftSub_wk] using
        (RegularHasType.var
          (Γ := .snoc Δ (subst substitution A)) (i := (0 : Fin (m + 1))))
    · intro preceding
      have mapped := (morphism.typing preceding).weaken
        (U := subst substitution A)
      simpa [RegularCtxMor, lookup_snoc_succ, liftSub, subst_liftSub_wk] using mapped
  · intro index
    refine Fin.cases (.var 0) (fun preceding =>
      (morphism.constantFree preceding).rename wk) index

end RegularCtxMor

namespace RegularHasType

/-- Generic simultaneous substitution for the regular judgment. -/
theorem subst {Γ : Ctx n} {term type : PureTm n}
    (typing : RegularHasType Γ term type) :
    ∀ {m : Nat} {Δ : Ctx m} {substitution : Sub n m},
      RegularCtxMor Γ Δ substitution →
        RegularHasType Δ (Substitution.subst substitution term)
          (Substitution.subst substitution type) := by
  induction typing with
  | u0_type Γ =>
      intro m Δ substitution morphism
      simpa [Substitution.subst] using RegularHasType.u0_type Δ
  | var index =>
      intro m Δ substitution morphism
      exact morphism.typing index
  | @pi_form n Γ A B hA hB ihA ihB =>
      intro m Δ substitution morphism
      have mappedA := ihA morphism
      have mappedB := ihB (RegularCtxMor.lift morphism A)
      simpa [Substitution.subst] using RegularHasType.pi_form mappedA mappedB
  | @sigma_form n Γ A B hA hB ihA ihB =>
      intro m Δ substitution morphism
      have mappedA := ihA morphism
      have mappedB := ihB (RegularCtxMor.lift morphism A)
      simpa [Substitution.subst] using RegularHasType.sigma_form mappedA mappedB
  | @lam_intro n Γ A body B hA hB hBody ihA ihB ihBody =>
      intro m Δ substitution morphism
      have mappedA := ihA morphism
      have lifted := RegularCtxMor.lift morphism A
      have mappedB := ihB lifted
      have mappedBody := ihBody lifted
      simpa [Substitution.subst] using
        RegularHasType.lam_intro mappedA mappedB mappedBody
  | @app_elim n Γ function argument A B hA hf ha hB ihA ihf iha ihB =>
      intro m Δ substitution morphism
      simpa [Substitution.subst, subst_inst0] using
        RegularHasType.app_elim (ihA morphism) (ihf morphism) (iha morphism)
          (ihB (RegularCtxMor.lift morphism A))
  | @pair_intro n Γ first second A B hA ha hb hB ihA iha ihb ihB =>
      intro m Δ substitution morphism
      have mappedSecond : RegularHasType Δ
          (Substitution.subst substitution second)
          (inst0 (Substitution.subst substitution first)
            (Substitution.subst (liftSub substitution) B)) := by
        simpa [subst_inst0] using ihb morphism
      simpa [Substitution.subst] using
        RegularHasType.pair_intro (ihA morphism) (iha morphism)
          mappedSecond (ihB (RegularCtxMor.lift morphism A))
  | @fst_elim n Γ pair A B hA hp hB ihA ihp ihB =>
      intro m Δ substitution morphism
      simpa [Substitution.subst] using
        RegularHasType.fst_elim (ihA morphism) (ihp morphism)
          (ihB (RegularCtxMor.lift morphism A))
  | @snd_elim n Γ pair A B hA hp hB ihA ihp ihB =>
      intro m Δ substitution morphism
      simpa [Substitution.subst, subst_inst0] using
        RegularHasType.snd_elim (ihA morphism) (ihp morphism)
          (ihB (RegularCtxMor.lift morphism A))
  | @id_form n Γ A left right hA hLeft hRight ihA ihLeft ihRight =>
      intro m Δ substitution morphism
      simpa [Substitution.subst] using
        RegularHasType.id_form (ihA morphism) (ihLeft morphism)
          (ihRight morphism)
  | @refl_intro n Γ term A hA hTerm ihA ihTerm =>
      intro m Δ substitution morphism
      simpa [Substitution.subst] using
        RegularHasType.refl_intro (ihA morphism) (ihTerm morphism)
  | @conv_type n Γ term A B hTerm hB conversion ihTerm ihB =>
      intro m Δ substitution morphism
      exact RegularHasType.conv_type (ihTerm morphism) (ihB morphism)
        (conversion.subst substitution morphism.constantFree)
  | @conv_sort n Γ term A hTerm conversion ihTerm =>
      intro m Δ substitution morphism
      simpa [Substitution.subst] using
        RegularHasType.conv_sort (ihTerm morphism)
          (conversion.subst substitution morphism.constantFree)

end RegularHasType

/-! ## Singleton substitution and formation inversion -/

/-- Substituting for the newest variable cancels weakening. -/
theorem regular_subst0_wk_cancel (argument term : PureTm n) :
    Substitution.subst (subst0 argument) (Renaming.rename wk term) = term := by
  calc
    Substitution.subst (subst0 argument) (Renaming.rename wk term) =
        Substitution.subst (fun index => subst0 argument (wk index)) term := by
      simpa using subst_rename (σ := subst0 argument) (ρ := wk) (t := term)
    _ = Substitution.subst ids term := by
      apply subst_ext
      intro index
      rfl
    _ = term := subst_ids term

/-- Replacing the newest variable by a regularly typed term is a regular
context morphism. -/
def RegularCtxMor.instantiate {Γ : Ctx n} {A argument : PureTm n}
    (argumentTyping : RegularHasType Γ argument A)
    (contextPure : ConstantFreeCtx Γ) :
    RegularCtxMor (.snoc Γ A) Γ (subst0 argument) where
  typing := by
    intro index
    refine Fin.cases ?_ ?_ index
    · simpa [lookup_snoc_zero, regular_subst0_wk_cancel] using argumentTyping
    · intro preceding
      simpa [lookup_snoc_succ, regular_subst0_wk_cancel] using
        (RegularHasType.var (Γ := Γ) preceding)
  constantFree := by
    intro index
    refine Fin.cases ?_ (fun preceding => .var preceding) index
    exact (argumentTyping.constantFree_both contextPure).1

/-- Dependent instantiation preserves regular typing. -/
theorem RegularHasType.instantiate
    {Γ : Ctx n} {A argument : PureTm n} {term type : PureTm (n + 1)}
    (typing : RegularHasType (.snoc Γ A) term type)
    (argumentTyping : RegularHasType Γ argument A)
    (contextPure : ConstantFreeCtx Γ) :
    RegularHasType Γ (inst0 argument term) (inst0 argument type) := by
  simpa [inst0] using
    typing.subst (RegularCtxMor.instantiate argumentTyping contextPure)

/-- Formation inversion for a syntactic dependent function type.  Conversion
may change the type assigned to the code, but never the code itself. -/
theorem RegularHasType.pi_components_formed
    {Γ : Ctx n} {term type : PureTm n}
    (typing : RegularHasType Γ term type) :
    ∀ {A : PureTm n} {B : PureTm (n + 1)}, term = .pi A B →
      RegularHasType Γ A .u1 ∧
        RegularHasType (.snoc Γ A) B .u1 := by
  induction typing with
  | pi_form hA hB ihA ihB =>
      intro domain codomain equal
      cases equal
      exact ⟨hA, hB⟩
  | conv_type hTerm hType conversion ihTerm ihType => exact ihTerm
  | conv_sort hTerm conversion ihTerm => exact ihTerm
  | u0_type => simp
  | var => simp
  | sigma_form => simp
  | lam_intro => simp
  | app_elim => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

/-- Formation inversion for a syntactic dependent pair type. -/
theorem RegularHasType.sigma_components_formed
    {Γ : Ctx n} {term type : PureTm n}
    (typing : RegularHasType Γ term type) :
    ∀ {A : PureTm n} {B : PureTm (n + 1)}, term = .sigma A B →
      RegularHasType Γ A .u1 ∧
        RegularHasType (.snoc Γ A) B .u1 := by
  induction typing with
  | sigma_form hA hB ihA ihB =>
      intro domain codomain equal
      cases equal
      exact ⟨hA, hB⟩
  | conv_type hTerm hType conversion ihTerm ihType => exact ihTerm
  | conv_sort hTerm conversion ihTerm => exact ihTerm
  | u0_type => simp
  | var => simp
  | pi_form => simp
  | lam_intro => simp
  | app_elim => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

/-- Formation inversion for the carrier of a syntactic identity type. -/
theorem RegularHasType.id_carrier_formed
    {Γ : Ctx n} {term type : PureTm n}
    (typing : RegularHasType Γ term type) :
    ∀ {A left right : PureTm n}, term = .id A left right →
      RegularHasType Γ A .u1 := by
  induction typing with
  | id_form hA hLeft hRight ihA ihLeft ihRight =>
      intro carrier left right equal
      cases equal
      exact hA
  | conv_type hTerm hType conversion ihTerm ihType => exact ihTerm
  | conv_sort hTerm conversion ihTerm => exact ihTerm
  | u0_type => simp
  | var => simp
  | pi_form => simp
  | sigma_form => simp
  | lam_intro => simp
  | app_elim => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | refl_intro => simp

/-! ## The presupposition theorem -/

/-- Every type retrieved from a regular context is itself well formed. -/
theorem RegularCtx.lookup_formed {Γ : Ctx n} (context : RegularCtx Γ)
    (index : Fin n) : RegularHasType Γ (lookup Γ index) .u1 := by
  induction context with
  | nil => exact Fin.elim0 index
  | @snoc n Γ A context hA ih =>
      refine Fin.cases ?_ ?_ index
      · simpa [lookup_snoc_zero, Renaming.rename] using hA.weaken (U := A)
      · intro preceding
        simpa [lookup_snoc_succ, Renaming.rename] using
          (ih preceding).weaken (U := A)

/-- **Global presupposition closure.**  In a regular context, every regular
typing result is either the distinguished untyped top sort or a type which is
itself regularly formed below that sort. -/
theorem RegularHasType.type_presupposed
    (typing : RegularHasType Γ term type) (context : RegularCtx Γ) :
    type = .u1 ∨ RegularHasType Γ type .u1 := by
  induction typing with
  | u0_type => exact .inl rfl
  | var index => exact .inr (context.lookup_formed index)
  | pi_form => exact .inl rfl
  | sigma_form => exact .inl rfl
  | lam_intro hA hB hBody ihA ihB ihBody =>
      exact .inr (.pi_form hA hB)
  | app_elim hA function argument hB ihA ihFunction ihArgument ihB =>
      exact .inr (hB.instantiate argument context.constantFreeCtx)
  | pair_intro hA first second hB ihA ihFirst ihSecond ihB =>
      exact .inr (.sigma_form hA hB)
  | fst_elim hA pair hB ihA ihPair ihB =>
      exact .inr hA
  | snd_elim hA pair hB ihA ihPair ihB =>
      have firstTyping := RegularHasType.fst_elim hA pair hB
      exact .inr (hB.instantiate firstTyping context.constantFreeCtx)
  | id_form => exact .inl rfl
  | refl_intro hA term ihA ihTerm =>
      exact .inr (.id_form hA term term)
  | conv_type term hB conversion ihTerm ihB => exact .inr hB
  | conv_sort => exact .inl rfl

/-- The full judgment boundary exposes the presupposition theorem without a
second context argument. -/
theorem RegularJudgment.type_presupposed (judgment : RegularJudgment Γ term type) :
    type = .u1 ∨ RegularHasType Γ type .u1 :=
  judgment.typing.type_presupposed judgment.context

/-! ## Specification ablations -/

/-- The permissive raw calculus accepts a lambda whose codomain is the untyped
top sort.  Its domain is well formed, so this isolates the missing codomain
presupposition. -/
theorem raw_allows_unformed_lambda_codomain :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType (.nil : Ctx 0)
      (.lam .u0) (.pi .u0 .u1) := by
  exact .lam_intro (.u0_type _)

/-- The regular kernel rejects the same lambda because `U1` cannot be the
codomain family of a formed dependent function. -/
theorem regular_rejects_unformed_lambda_codomain :
    ¬ RegularHasType (.nil : Ctx 0) (.lam .u0) (.pi .u0 .u1) := by
  intro typing
  rcases typing.type_presupposed .nil with impossible | formed
  · cases impossible
  · exact no_regular_u1_term (formed.pi_components_formed rfl).2

/-- The permissive raw calculus accepts reflexivity over the untyped top sort;
this isolates the missing carrier-formation presupposition. -/
theorem raw_allows_refl_over_unformed_carrier :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType (.nil : Ctx 0)
      (.refl .u0) (.id .u1 .u0 .u0) := by
  exact .refl_intro (.u0_type _)

/-- The regular kernel rejects reflexivity over that carrier. -/
theorem regular_rejects_refl_over_unformed_carrier :
    ¬ RegularHasType (.nil : Ctx 0) (.refl .u0) (.id .u1 .u0 .u0) := by
  intro typing
  rcases typing.type_presupposed .nil with impossible | formed
  · cases impossible
  · exact no_regular_u1_term (formed.id_carrier_formed rfl)

/-- A regular one-variable context used to isolate the old dependent-pair
domain omission. -/
def pairAblationContext : Ctx 1 := .snoc .nil .u0

theorem pairAblationContext_regular : RegularCtx pairAblationContext :=
  regularCtx_u0

/-- The permissive raw calculus can form a pair over `U1` itself while the
surrounding context remains regular. -/
theorem raw_allows_pair_over_unformed_domain :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType pairAblationContext
      (.pair .u0 (.var 0)) (.sigma .u1 .u0) := by
  apply Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType.pair_intro
  · exact .u0_type _
  · simpa [pairAblationContext, lookup_snoc_zero, Renaming.rename, inst0,
      Substitution.subst] using
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType.var
        (Γ := pairAblationContext) (i := (0 : Fin 1)))

/-- The regular kernel rejects that pair because its dependent-pair type would
force the untyped top sort to be a formed domain. -/
theorem regular_rejects_pair_over_unformed_domain :
    ¬ RegularHasType pairAblationContext
      (.pair .u0 (.var 0)) (.sigma .u1 .u0) := by
  intro typing
  rcases typing.type_presupposed pairAblationContext_regular with
    impossible | formed
  · cases impossible
  · exact no_regular_u1_term (formed.sigma_components_formed rfl).1

/-- Positive canary: the ordinary identity function synthesizes a genuinely
formed dependent function type. -/
theorem regular_identity_result_formed :
    RegularHasType (.nil : Ctx 0) (.pi .u0 .u0) .u1 := by
  rcases regular_identity_judgment.type_presupposed with impossible | formed
  · cases impossible
  · exact formed

#print axioms ConstantFreeConv.rename
#print axioms ConstantFreeConv.subst
#print axioms RegularHasType.rename
#print axioms RegularHasType.subst
#print axioms RegularHasType.type_presupposed
#print axioms regular_rejects_unformed_lambda_codomain
#print axioms regular_rejects_refl_over_unformed_carrier
#print axioms regular_rejects_pair_over_unformed_domain
#print axioms regular_identity_result_formed

end Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
