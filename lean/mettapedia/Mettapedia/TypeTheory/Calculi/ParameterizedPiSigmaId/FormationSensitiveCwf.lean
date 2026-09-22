import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ContextualLadderBridge
import Mettapedia.GSLT.Core.ContextualStrictCwfMorphism

/-!
# The formation-sensitive source in the shared CwF interface

This is an adapter for the cumulative presentation's existing formed
contexts, types, terms and substitutions. No typing relation is introduced.
In particular, source and target context formation remain independent of
component typing of a substitution.

Forgetting the additional formation premises is a strict CwF morphism into
the older permissive presentation. This direction does not assert that a
permissively typed term has a formation-sensitive derivation. Both source
models retain raw syntax; conversion classes are a separate interpretation.
The shared CwF and its general interpretation laws remain in the independent
contextual/type-theory library.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

variable {Head : Type} {rules : Rules Head}

@[simp] theorem Term.castCongrArg_code {context : Context rules}
    {source target : TypeOver context} (same : source = target)
    (term : Term context source) :
    (_root_.cast (congrArg (Term context) same) term).code = term.code := by
  cases same
  rfl

theorem Term.heq_of_type_eq_of_code_eq {context : Context rules}
    {source target : TypeOver context} (same : source = target)
    (left : Term context source) (right : Term context target)
    (codes : left.code = right.code) : HEq left right := by
  cases same
  exact heq_of_eq (Term.ext codes)

/-- The source CwF uses precisely the previously formed category and its
capture-avoiding substitution and comprehension operations. -/
def asCwf (rules : Rules Head) : Cwf where
  Ctx := Context rules
  Sub := Hom (rules := rules)
  idS := fun context => ⟨ids, identityTyped context.raw⟩
  compS := fun {Γ Δ Θ} (later : Hom Δ Θ) (earlier : Hom Γ Δ) =>
    ⟨subComp earlier.substitution later.substitution, compositionTyped earlier.typed later.typed⟩
  id_comp := fun morphism => Hom.ext (subComp_ids_right morphism.substitution)
  comp_id := fun morphism => Hom.ext (subComp_ids_left morphism.substitution)
  comp_assoc := fun later middle earlier => Hom.ext
    (subComp_assoc earlier.substitution middle.substitution later.substitution)
  Ty := TypeOver
  tySub := TypeOver.reindex
  tySub_id := TypeOver.reindex_id
  tySub_comp := fun type later earlier => type.reindex_comp earlier later
  Tm := Term
  tmSub := Term.reindex
  tmSub_id := by
    intro context type term
    apply Term.ext
    rw [Term.castCongrArg_code type.reindex_id.symm]
    exact subst_ids term.code
  tmSub_comp := by
    intro first middle last type term later earlier
    change term.reindex (earlier ≫ later) =
      _root_.cast (congrArg (Term first) (type.reindex_comp earlier later).symm)
        ((term.reindex later).reindex earlier)
    apply Term.ext
    rw [Term.castCongrArg_code (type.reindex_comp earlier later).symm]
    exact (subst_subComp earlier.substitution later.substitution term.code).symm
  ext := extend
  wk := fun type => projectionHom _ type
  vz := fun type => newest _ type
  pair := fun morphism _ term => pair morphism term
  wk_pair := fun morphism _ term => pair_projection morphism term
  vz_pair := by
    intro source target morphism type term
    apply Term.ext
    rw [Term.castCongrArg_code (by
      rw [← type.reindex_comp, pair_projection])]
    rfl
  pair_eta := by
    intro source target type morphism
    apply Hom.ext
    dsimp only [pair]
    rw [Term.castCongrArg_code (type.reindex_comp morphism
      (projectionHom target type)).symm]
    exact consSub_eta morphism.substitution

def asCwfWithTerminal (rules : Rules Head) : CwfWithTerminal where
  toCwf := asCwf rules
  empty := empty rules
  toEmpty := toEmpty
  toEmpty_unique := toEmpty_unique

/-- The categorical wrapper retains every source substitution, including
its actual formation-sensitive component judgments. -/
def baseToFormed (rules : Rules Head) :
    (asCwf rules).base.Context ⥤ Context rules where
  obj context := context.val
  map morphism := morphism

def baseToFormedFullyFaithful (rules : Rules Head) :
    (baseToFormed rules).FullyFaithful where
  preimage morphism := morphism

/-- Erasure of formation premises, on contexts and simultaneous substitutions. -/
def forgetBase (rules : Rules Head) :
    (asCwf rules).base.Context ⥤ (SyntacticContextual.asCwf rules).base.Context where
  obj context := ⟨context.val.toRaw⟩
  map morphism := morphism.toRaw

def forgetFamily (rules : Rules Head) :
    CwfFamilyMorphism (asCwf rules) (SyntacticContextual.asCwf rules) where
  base := forgetBase rules
  family := {
    app := fun _ => { onIndex := TypeOver.toRaw, onFibre := fun _ => Term.toRaw }
    naturality := by
      intro source target morphism
      apply IndexedFamily.Hom.ext
      · rfl
      · intro type term
        rfl }

/-- Erasing formation premises preserves the actual empty telescope,
extension, projection and generic variable, rather than only term codes. -/
def forgetStrict (rules : Rules Head) :
    StrictCwfMorphism (asCwfWithTerminal rules)
      (SyntacticContextual.asCwfWithTerminal rules) where
  toFamilyMorphism := forgetFamily rules
  empty_preserved := rfl
  extension_preserved _ _ := rfl
  projection_preserved context type := by
    apply SyntacticContextual.ContextHom.ext
    exact (subComp_ids_left projection).symm
  variable_preserved context type := by
    apply SyntacticContextual.Term.heq_of_type_eq_of_code_eq
    · apply SyntacticContextual.TypeOver.ext
      · exact (subst_ids _).symm
      · rfl
    · rfl

#print axioms asCwfWithTerminal
#print axioms forgetStrict

end FormationSensitiveContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
