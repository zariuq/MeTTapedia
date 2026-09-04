import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticContextualCategory

/-!
# The declaration-aware syntax inhabits the contextual ladder

The cumulative-tower presentation already supplies formed telescopes, typed
simultaneous substitutions, reindexed types and terms, and context
comprehension.  This file packages those existing objects as the generic
`ContextualLadder.Cwf`; it introduces no new syntax, typing judgment, or
conversion relation.

The bridge uses proof-carrying raw syntactic equality.  In particular, it
does not quotient types by conversion.  A later semantic or judgmental model
may choose a different equality boundary, but that choice is not needed to
establish the structural CwF laws here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace SyntacticContextual

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

variable {Head : Type}

/-! ## The live syntax as a CwF -/

/-- Heterogeneous equality across equal type indices is exactly equality
after transporting the right-hand term back to the source fibre. -/
theorem Term.eq_cast_of_heq {rules : Rules Head}
    {context : FormedContext rules} {source target : TypeOver context}
    (equalTypes : source = target) (left : Term context source)
    (right : Term context target) (equalTerms : HEq left right) :
    left = _root_.cast (congrArg (Term context) equalTypes.symm) right := by
  cases equalTypes
  exact eq_of_heq equalTerms

/-- Transport induced by equality of type indices preserves the retained raw
term code. -/
@[simp]
theorem Term.castCongrArg_code {rules : Rules Head}
    {context : FormedContext rules} {source target : TypeOver context}
    (equalTypes : source = target) (term : Term context source) :
    (_root_.cast (congrArg (Term context) equalTypes) term).code =
      term.code := by
  cases equalTypes
  rfl

/-- The declaration-aware syntactic contextual category, with its existing
type and term fibres, is a category with families. -/
@[reducible] def asCwf (rules : Rules Head) : Cwf := by
  refine
    { Ctx := FormedContext rules
      Sub := ContextHom
      idS := fun context =>
        { substitution := ids
          typed := CtxMor.identity rules context.context }
      compS := fun {Γ Δ Θ}
          (later : ContextHom (rules := rules) Δ Θ)
          (earlier : ContextHom Γ Δ) =>
        { substitution := subComp earlier.substitution later.substitution
          typed := CtxMor.comp later.typed earlier.typed }
      id_comp := ?_
      comp_id := ?_
      comp_assoc := ?_
      Ty := TypeOver
      tySub := fun type substitution => type.reindex substitution
      tySub_id := ?_
      tySub_comp := ?_
      Tm := Term
      tmSub := fun term substitution => term.reindex substitution
      tmSub_id := ?_
      tmSub_comp := ?_
      ext := extendContext
      wk := fun type => projectionHom _ type
      vz := fun type => newestVariable _ type
      pair := fun substitution _ term => extendHom substitution term
      wk_pair := ?_
      vz_pair := ?_
      pair_eta := ?_ }
  · intro _ _ substitution
    apply ContextHom.ext
    exact subComp_ids_right substitution.substitution
  · intro _ _ substitution
    apply ContextHom.ext
    exact subComp_ids_left substitution.substitution
  · intro _ _ _ _ later middle earlier
    apply ContextHom.ext
    exact subComp_assoc earlier.substitution middle.substitution
      later.substitution
  · intro _ type
    exact TypeOver.reindex_id type
  · intro _ _ _ type later earlier
    exact TypeOver.reindex_comp type earlier later
  · intro _ _ term
    exact Term.eq_cast_of_heq (TypeOver.reindex_id _) _ term
      (Term.reindex_id term)
  · intro _ _ _ _ term later earlier
    exact Term.eq_cast_of_heq
      (TypeOver.reindex_comp _ earlier later) _ _
      (Term.reindex_comp term earlier later)
  · intro _ _ substitution type term
    exact extendHom_projection substitution term
  · intro _ _ substitution type term
    let equalTypes := newestVariable_extendHom_type substitution term
    let left :=
      (newestVariable _ type).reindex (extendHom substitution term)
    have equalCodes : left.code = term.code := rfl
    exact Term.eq_cast_of_heq equalTypes left term
      (Term.heq_of_type_eq_of_code_eq equalTypes left term equalCodes)
  · intro _ _ type substitution
    apply ContextHom.ext
    dsimp only [extendHom]
    rw [Term.castCongrArg_code
      (TypeOver.reindex_comp type substitution
        (projectionHom _ type)).symm]
    change
      consSub (substitution.substitution (newestIndex _ type))
          (subComp substitution.substitution projection) =
        substitution.substitution
    have projected :
        subComp substitution.substitution projection =
          (fun index => substitution.substitution index.succ) := by
      funext index
      rfl
    rw [projected]
    exact consSub_eta substitution.substitution

/-- The declaration-aware syntax with its existing empty telescope,
packaged as a full standard cwf. -/
def asCwfWithTerminal (rules : Rules Head) : CwfWithTerminal where
  toCwf := asCwf rules
  empty := emptyContext rules
  toEmpty := toEmpty
  toEmpty_unique := by
    intro context substitution
    exact toEmpty_unique context substitution

/-! ## Comparison with the pre-existing context category -/

/-- Unwrap the base-category object introduced by the generic CwF interface.
Its morphisms are the original typed simultaneous substitutions. -/
def baseToSyntactic (rules : Rules Head) :
    (asCwf rules).base.Context ⥤ FormedContext rules where
  obj context := context.val
  map substitution := substitution

/-- The comparison loses no context morphisms. -/
def baseToSyntacticFullyFaithful (rules : Rules Head) :
    (baseToSyntactic rules).FullyFaithful where
  preimage substitution := substitution

/-- Every original formed telescope is literally represented by a generic
base-category object. -/
theorem baseToSyntactic_surjective_on_objects (rules : Rules Head) :
    Function.Surjective (baseToSyntactic rules).obj := by
  intro context
  exact ⟨⟨context⟩, rfl⟩

/-! ## Positive and negative structural witnesses -/

/-- Positive: comprehension in the packaged CwF is the live telescope
extension, not a parallel construction. -/
theorem asCwf_ext_eq_extendContext (rules : Rules Head)
    (context : FormedContext rules) (type : TypeOver context) :
    (asCwf rules).ext context type = extendContext context type := rfl

/-- Negative: distinct raw term components remain distinct after packaging as
CwF pairing arrows. -/
theorem asCwf_pair_ne_of_term_code_ne (rules : Rules Head)
    {source target : FormedContext rules} {type : TypeOver target}
    (substitution : (asCwf rules).Sub source target)
    {left right : (asCwf rules).Tm source
      ((asCwf rules).tySub type substitution)}
    (different : left.code ≠ right.code) :
    (asCwf rules).pair substitution type left ≠
      (asCwf rules).pair substitution type right :=
  extendHom_ne_of_term_code_ne substitution different

#print axioms asCwf
#print axioms asCwfWithTerminal
#print axioms baseToSyntacticFullyFaithful
#print axioms baseToSyntactic_surjective_on_objects
#print axioms asCwf_ext_eq_extendContext
#print axioms asCwf_pair_ne_of_term_code_ne

end SyntacticContextual
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
