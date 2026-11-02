import Mettapedia.OSLF.Syntax.ContextualFamilyComposition
import Mettapedia.OSLF.Syntax.SignatureMorphismMetas

/-!
# Arity-preserving reindexing of contextual declarations

Changing a declaration's identity preserves both its parameter context and
result sort. Reindexing uses the existing contextual assignment and body
transport. It commutes with instantiation, composes, and has an inverse when
the underlying identity maps do. Object binding and the term syntax are
unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W X : Type}
  {source : V → MetaArity S} {target : W → MetaArity S} {next : X → MetaArity S}

theorem instantiate_castMetaBody (assignment : Assignment source target)
    {first second : MetaArity S} (same : first = second)
    (body : Term (signature S source) first.1 first.2) :
    instantiate assignment (castMetaBody (V := signature S source) same body) =
      castMetaBody (V := signature S target) same (instantiate assignment body) := by
  cases same
  rfl

theorem castMetaBody_trans {T : Signature} {first second third : MetaArity T}
    (one : first = second) (two : second = third) (body : Term T first.1 first.2) :
    castMetaBody two (castMetaBody one body) = castMetaBody (one.trans two) body := by
  cases one
  cases two
  rfl

def reindex (identities : V → W) (preserves : ∀ identity, target (identities identity) = source identity) :
    Assignment source target :=
  fun identity => castMetaBody (V := signature S target) (preserves identity) (generator target (identities identity))

theorem instantiate_reindex (identities : V → W)
    (preserves : ∀ identity, target (identities identity) = source identity)
    (assignment : Assignment target next) (identity : V) :
    instantiate assignment (reindex identities preserves identity) =
      castMetaBody (V := signature S next) (preserves identity) (assignment (identities identity)) := by
  simp only [reindex, instantiate_castMetaBody, instantiate_generator]

theorem reindex_compose (first : V → W) (second : W → X)
    (firstPreserves : ∀ identity, target (first identity) = source identity)
    (secondPreserves : ∀ identity, next (second identity) = target identity) :
    Assignment.compose (reindex second secondPreserves) (reindex first firstPreserves) =
      reindex (fun identity => second (first identity))
        (fun identity => (secondPreserves (first identity)).trans (firstPreserves identity)) := by
  funext identity
  rw [Assignment.compose, instantiate_reindex]
  exact castMetaBody_trans _ _ _

theorem cast_generator_of_identity {first second : V} (same : first = second)
    (preserves : source first = source second) :
    castMetaBody (V := signature S source) preserves (generator source first) = generator source second := by
  cases same
  rfl

theorem reindex_left_inverse (forward : V → W) (backward : W → V)
    (forwardPreserves : ∀ identity, target (forward identity) = source identity)
    (backwardPreserves : ∀ identity, source (backward identity) = target identity)
    (inverse : Function.LeftInverse backward forward) :
    Assignment.compose (reindex backward backwardPreserves) (reindex forward forwardPreserves) = generator source := by
  rw [reindex_compose]
  funext identity
  exact cast_generator_of_identity (inverse identity) _

theorem instantiate_reindex_inverse (forward : V → W) (backward : W → V)
    (forwardPreserves : ∀ identity, target (forward identity) = source identity)
    (backwardPreserves : ∀ identity, source (backward identity) = target identity)
    (inverse : Function.LeftInverse backward forward)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) :
    instantiate (reindex backward backwardPreserves) (instantiate (reindex forward forwardPreserves) term) = term := by
  rw [instantiate_comp]
  change instantiate (Assignment.compose (reindex backward backwardPreserves) (reindex forward forwardPreserves)) term = term
  rw [reindex_left_inverse forward backward forwardPreserves backwardPreserves inverse, instantiate_identity]

end Mettapedia.OSLF.Binding.ContextualFamily
