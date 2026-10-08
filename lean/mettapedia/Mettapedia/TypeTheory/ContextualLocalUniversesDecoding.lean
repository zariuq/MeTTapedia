import Mettapedia.TypeTheory.ContextualLocalUniverses
import Mettapedia.GSLT.Core.ContextualStrictCwfMorphism

/-!
# Decoding local family presentations as a contextual morphism

The family map decodes the supplied parameter family along its actual name.
It carries every supplied term, commutes with contextual substitution and
preserves terminal context and selected comprehension. The context category
is unchanged; the type map forgets external presentation data.

The aligned type universe includes context and substitution universes. This
is a size condition on external presentations, not an internal universe
capability. The standard set-family and native presheaf models have this
alignment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualLocalUniverses

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

universe u v w'

def familyDecoder (C : Cwf.{u, v, max u v, w'}) : CwfFamilyMorphism (localCwf C) C where
  base := 𝟭 C.base.Context
  family := {
    app := fun _ => {
      onIndex := LocalType.decoded
      onFibre := fun _ term => term }
    naturality := by
      intro source target substitution
      apply IndexedFamily.Hom.ext
      · funext type
        exact type.decoded_reindex substitution.unop
      · intro type term
        exact substituteTerm_heq term substitution.unop }

@[simp] theorem familyDecoder_type (C : Cwf.{u, v, max u v, w'})
    {context : C.Ctx} (type : LocalType C context) :
    (familyDecoder C).mapType type = type.decoded := rfl

@[simp] theorem familyDecoder_term (C : Cwf.{u, v, max u v, w'})
    {context : C.Ctx} {type : LocalType C context} (term : Term C context type) :
    (familyDecoder C).mapTerm term = term := rfl

/-- Decoding preserves the actual contextual comprehension structure; its
family action was constructed and its naturality was proved above. -/
def strictDecoder (C : CwfWithTerminal.{u, v, max u v, w'}) :
    StrictCwfMorphism (localCwfWithTerminal C) C where
  toFamilyMorphism := familyDecoder C.toCwf
  empty_preserved := rfl
  extension_preserved := fun _ _ => rfl
  projection_preserved := by
    intro context type
    change C.toCwf.wk type.decoded =
      C.toCwf.compS (C.toCwf.wk type.decoded) (C.toCwf.idS _)
    exact (C.toCwf.comp_id _).symm
  variable_preserved := by
    intro context type
    change HEq (genericVariable type)
      (C.toCwf.tmSub (C.toCwf.vz type.decoded) (C.toCwf.idS _))
    exact (genericVariable_heq type).trans
      ((heq_of_eq (C.toCwf.tmSub_id _)).trans (cast_heq _ _)).symm

/-- No supplied term is lost by the decoder at its actual decoded type. -/
def termEquiv (C : Cwf.{u, v, max u v, w'}) {context : C.Ctx}
    (type : LocalType C context) :
    (localCwf C).Tm context type ≃ C.Tm context ((familyDecoder C).mapType type) where
  toFun := (familyDecoder C).mapTerm
  invFun := fun term => term
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem decoder_substitution (C : Cwf.{u, v, max u v, w'}) {source target : C.Ctx}
    {type : LocalType C target} (term : Term C target type)
    (substitution : C.Sub source target) :
    HEq ((familyDecoder C).mapTerm ((localCwf C).tmSub term substitution))
      (C.tmSub ((familyDecoder C).mapTerm term) substitution) :=
  substituteTerm_heq term substitution

end Mettapedia.TypeTheory.ContextualLocalUniverses
