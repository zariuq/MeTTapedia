import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUnifier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternBinding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPair

/-!
# Proved contextual solver cases share one frame contract

Binding, distinct-variable spine binding, different-hole pairs and same-hole
pairs supply actual principal frame answers. Their proofs have independent
scope, occurrence and factorization laws. The common contract supports
composition and fresh-frame execution without supplying an assumed solver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierProfiles

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature}

theorem binding {V : Type} [DecidableEq V] {declaration : V → MetaArity S}
    (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    (absent : identity ∉ support body) :
    ContextualFrameUnifier.Principal [(generator declaration identity, body)]
      (ContextualBinding.answer identity body) := by
  constructor
  · exact (ContextualBinding.principal identity body absent).sound
  · intro Variables next candidate solved
    have same := solved (generator declaration identity, body) (by simp)
    rw [instantiate_generator] at same
    exact ⟨candidate, fun other => congrFun (ContextualBinding.candidate_factors identity body candidate same) other⟩

theorem binding_on_spine {V : Type} [DecidableEq V] {declaration : V → MetaArity S}
    (identity : V) {Γ : Ctx S} (rho : Ren S (declaration identity).1 Γ)
    (inverse : Strengthener (S := signature S declaration) rho)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    (absent : identity ∉ support body) :
    ContextualFrameUnifier.Principal
      [(rename (S := signature S declaration) rho (generator declaration identity),
        rename (S := signature S declaration) rho body)] (ContextualBinding.answer identity body) := by
  constructor
  · exact (ContextualPatternBinding.principal_on_spine identity rho inverse body absent).sound
  · intro Variables next candidate solved
    have same := solved
      (rename (S := signature S declaration) rho (generator declaration identity),
        rename (S := signature S declaration) rho body) (by simp)
    rw [ContextualFamily.instantiate_rename, ContextualFamily.instantiate_rename, instantiate_generator] at same
    let nextInverse : Strengthener (S := signature S next) rho :=
      ⟨inverse.un, inverse.un_rho, inverse.rho_un⟩
    exact ⟨candidate, fun other => congrFun (ContextualBinding.candidate_factors identity body candidate
      (rename_injective nextInverse same)) other⟩

theorem flexible_pair {Other : Type} {L R Γ : Ctx S}
    {left : Ren S L Γ} {right : Ren S R Γ}
    (pullback : ScopePullback left right) (result : S.Srt) (others : Other → MetaArity S) :
    ContextualFrameUnifier.Principal
      [(rename (S := signature S (ContextualFlexPair.sourceDeclarations L R result others)) left
          (generator (ContextualFlexPair.sourceDeclarations L R result others) (.inl false)),
        rename (S := signature S (ContextualFlexPair.sourceDeclarations L R result others)) right
          (generator (ContextualFlexPair.sourceDeclarations L R result others) (.inl true)))]
      (ContextualFlexPair.answer pullback result others) := by
  constructor
  · intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    exact ContextualFlexPair.sound pullback result others
  · intro Variables next candidate solved
    exact ContextualFlexPair.factors pullback result others next candidate
      (solved _ (List.mem_singleton_self _))

theorem same_hole {Other : Type} {Δ Γ : Ctx S} {left right : Ren S Δ Γ}
    (equalizer : ScopeEqualizer left right) (result : S.Srt) (others : Other → MetaArity S) :
    ContextualFrameUnifier.Principal
      [(rename (S := signature S (ContextualSelfPair.declarations Δ result others)) left
          (generator (ContextualSelfPair.declarations Δ result others) (.inl ())),
        rename (S := signature S (ContextualSelfPair.declarations Δ result others)) right
          (generator (ContextualSelfPair.declarations Δ result others) (.inl ())))]
      (ContextualSelfPair.answer equalizer result others) := by
  constructor
  · intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    exact ContextualSelfPair.sound equalizer result others
  · intro Variables next candidate solved
    exact ContextualSelfPair.factors equalizer result others next candidate
      (solved _ (List.mem_singleton_self _))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierProfiles
