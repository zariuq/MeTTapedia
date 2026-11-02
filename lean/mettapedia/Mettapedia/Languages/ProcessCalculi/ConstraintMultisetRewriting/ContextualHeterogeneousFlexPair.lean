import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUpdate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierProfiles
import Mettapedia.OSLF.Syntax.BindingScopePullbackFinite
import Mettapedia.OSLF.Syntax.SignatureMorphismMetas

/-!
# Flexible pairs with independently presented result-sort indices

The result-sort equality is explicit before reusing the common pullback
solver. Its elimination transports the complete source family and equation;
it does not identify different sorts or erase their parameter interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualHeterogeneousFlexPair

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {Other : Type} [DecidableEq Other]

abbrev declarations (left right : Ctx S) (first second : S.Srt) (others : Other → MetaArity S) :
    Bool ⊕ Other → MetaArity S := pairDeclarations (left, first) (right, second) others

/-- The output frame is fixed before the source-sort equality transports the
second image. Retained equations do not determine that frame's identity. -/
def answer (L R : Ctx S) (first second : S.Srt) (same : first = second)
    (others : Other → MetaArity S) {Γ : Ctx S} (left : Ren S L Γ) (right : Ren S R Γ) :
    Assignment (declarations L R first second others)
      (ContextualFlexPair.targetDeclarations (ScopePullback.Finite.build left right).context first others) :=
  let pullback := ScopePullback.Finite.build left right
  let target := ContextualFlexPair.targetDeclarations pullback.context first others
  fun identity => match identity with
  | .inl false => rename (S := signature S target) pullback.toLeft (generator target (.inl ()))
  | .inl true => castMetaBody (V := signature S target) (congrArg (fun sort => (R, sort)) same)
      (rename (S := signature S target) pullback.toRight (generator target (.inl ())))
  | .inr identity => generator target (.inr identity)

def apply (L R : Ctx S) (first second : S.Srt) (same : first = second)
    (others : Other → MetaArity S) {Γ : Ctx S}
    (left : Ren S L Γ) (right : Ren S R Γ) (rest : Problem (declarations L R first second others)) :
    ContextualFrameUpdate.Update
      ((observe (rename (S := signature S (declarations L R first second others)) left
          (generator (declarations L R first second others) (.inl false))),
        observe (rename (S := signature S (declarations L R first second others)) right
          (generator (declarations L R first second others) (.inl true)))) :: rest) := by
  let pullback := ScopePullback.Finite.build (S := S) left right
  let computed := answer L R first second same others left right
  exact ⟨Unit ⊕ Other, inferInstance,
    ContextualFlexPair.targetDeclarations pullback.context first others,
    computed, mapProblem computed rest, by
      cases same
      change Reduction _ (ContextualFlexPair.answer pullback first others)
        (mapProblem (ContextualFlexPair.answer pullback first others) rest)
      exact of_principal_prefix (ContextualUnifierProfiles.flexible_pair pullback first others) rest⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualHeterogeneousFlexPair
