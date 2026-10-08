import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationComposition

/-!
# Coherence of complete authored translation data

Identity and association compare the complete target object and arrow
expressions. The declaration trees remain independently authored: equality
of data yields equality of the generated quotient functors, without claiming
equality of the retained local admission trees.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax

open _root_.CategoryTheory

universe k

variable {C D H J : Type k} [Category.{k} C] [Category.{k} D] [Category.{k} H] [Category.{k} J]
variable {symbols nextSymbols lastSymbols finalSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {final : Signature (C := H) (symbols := lastSymbols)}
variable {endSignature : Signature (C := J) (symbols := finalSymbols)}

namespace TranslationData

@[ext] theorem ext {before after : TranslationData (C := C) (symbols := symbols)
    (D := D) (nextSymbols := nextSymbols)}
    (base : before.base = after.base) (objects : before.objects = after.objects)
    (arrows : before.arrows = after.arrows) : before = after := by
  cases before
  cases after
  cases base
  cases objects
  cases arrows
  rfl

theorem identity_compose (mapping : TranslationData (C := C) (symbols := symbols)
    (D := D) (nextSymbols := nextSymbols)) : identity.compose mapping = mapping :=
  ext (Functor.id_comp mapping.base) rfl rfl

theorem compose_identity (mapping : TranslationData (C := C) (symbols := symbols)
    (D := D) (nextSymbols := nextSymbols)) : mapping.compose identity = mapping :=
  ext (Functor.comp_id mapping.base)
    (funext (fun origin => ObjectCode.translate_identity (mapping.objects origin)))
    (funext (fun origin => ArrowCode.translate_identity (mapping.arrows origin)))

theorem compose_assoc
    (first : TranslationData (C := C) (symbols := symbols) (D := D) (nextSymbols := nextSymbols))
    (middle : TranslationData (C := D) (symbols := nextSymbols) (D := H) (nextSymbols := lastSymbols))
    (last : TranslationData (C := H) (symbols := lastSymbols) (D := J) (nextSymbols := finalSymbols)) :
    (first.compose middle).compose last = first.compose (middle.compose last) :=
  ext (Functor.assoc first.base middle.base last.base)
    (funext (fun origin => ObjectCode.translate_compose middle last (first.objects origin)))
    (funext (fun origin => ArrowCode.translate_compose middle last (first.arrows origin)))

end TranslationData

namespace Translation

theorem functor_congr_data {before after : Translation signature next}
    (same : before.data = after.data) : before.functor = after.functor := by
  cases before
  cases after
  cases same
  rfl

theorem identity_compose_data (headers : HeaderFormation signature) (mapping : Translation signature next) :
    ((identity headers).compose mapping).data = mapping.data :=
  TranslationData.identity_compose mapping.data

theorem compose_identity_data (headers : HeaderFormation next) (mapping : Translation signature next) :
    (mapping.compose (identity headers)).data = mapping.data :=
  TranslationData.compose_identity mapping.data

theorem compose_assoc_data (first : Translation signature next) (middle : Translation next final)
    (last : Translation final endSignature) :
    ((first.compose middle).compose last).data = (first.compose (middle.compose last)).data :=
  TranslationData.compose_assoc first.data middle.data last.data

end Translation

end Mettapedia.CategoryTheory.RelativeClosedSyntax
