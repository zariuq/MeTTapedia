import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFamilies
import Mettapedia.OSLF.Syntax.BindingScopeEqualizerFinite
import Mettapedia.OSLF.Syntax.ContextualFamilyDeclarations

/-!
# One flexible hole at two parameter maps

The retained parameter equalizer determines a fresh helper for a same-hole
equation. Every solution factors through that helper, while all unrelated
declarations remain available. The construction uses the existing binding
terms and applies to the declared structural-equality profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPair

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Other Next : Type} {Δ Γ : Ctx S}
  {left right : Ren S Δ Γ}

abbrev declarations (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :
    Unit ⊕ Other → MetaArity S := sumDeclarations (fun _ => (parameters, result)) others

def inFamily (equalizer : Mettapedia.OSLF.Binding.ScopeEqualizer left right)
    (next : Next → MetaArity S) :
    Mettapedia.OSLF.Binding.ScopeEqualizer (S := signature S next) left right where
  context := equalizer.context
  inclusion := equalizer.inclusion
  commutes := equalizer.commutes
  recover := equalizer.recover
  recover_inclusion := equalizer.recover_inclusion
  recover_pair := equalizer.recover_pair

def answer (equalizer : Mettapedia.OSLF.Binding.ScopeEqualizer left right)
    (result : S.Srt) (others : Other → MetaArity S) :
    Assignment (declarations Δ result others) (declarations equalizer.context result others)
  | .inl _ => rename (S := signature S (declarations equalizer.context result others)) equalizer.inclusion
      (generator (declarations equalizer.context result others) (.inl ()))
  | .inr identity => generator (declarations equalizer.context result others) (.inr identity)

theorem sound (equalizer : Mettapedia.OSLF.Binding.ScopeEqualizer left right)
    (result : S.Srt) (others : Other → MetaArity S) :
    instantiate (answer equalizer result others)
        (rename (S := signature S (declarations Δ result others)) left
          (generator (declarations Δ result others) (.inl ()))) =
      instantiate (answer equalizer result others)
        (rename (S := signature S (declarations Δ result others)) right
          (generator (declarations Δ result others) (.inl ()))) := by
  rw [ContextualFamily.instantiate_rename, ContextualFamily.instantiate_rename,
    instantiate_generator]
  simp only [answer, rename_comp]
  have maps : (fun sort position => left sort (equalizer.inclusion sort position)) =
      (fun sort position => right sort (equalizer.inclusion sort position)) := by
    funext sort position
    exact equalizer.commutes sort position
  rw [maps]

theorem factors (equalizer : Mettapedia.OSLF.Binding.ScopeEqualizer left right)
    (result : S.Srt) (others : Other → MetaArity S)
    (next : Next → MetaArity S) (candidate : Assignment (declarations Δ result others) next)
    (solved :
      instantiate candidate
          (rename (S := signature S (declarations Δ result others)) left
            (generator (declarations Δ result others) (.inl ()))) =
        instantiate candidate
          (rename (S := signature S (declarations Δ result others)) right
            (generator (declarations Δ result others) (.inl ())))) :
    ∃ residual : Assignment (declarations equalizer.context result others) next,
      ∀ identity, candidate identity = instantiate residual (answer equalizer result others identity) := by
  rw [ContextualFamily.instantiate_rename, ContextualFamily.instantiate_rename,
    instantiate_generator] at solved
  obtain ⟨common, restored⟩ := (inFamily equalizer next).factor_term (candidate (.inl ())) solved
  let residual : Assignment (declarations equalizer.context result others) next
    | .inl _ => common
    | .inr identity => candidate (.inr identity)
  refine ⟨residual, ?_⟩
  intro identity
  cases identity with
  | inl singleton =>
      cases singleton
      change candidate (.inl ()) = instantiate residual
        (rename (S := signature S (declarations equalizer.context result others)) equalizer.inclusion
          (generator (declarations equalizer.context result others) (.inl ())))
      rw [ContextualFamily.instantiate_rename, instantiate_generator]
      exact restored.symm
  | inr identity => exact (instantiate_generator residual (.inr identity)).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPair
