import Mettapedia.GSLT.Core.SemanticTransport
import Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

/-!
# Denotation squares and NIK semantic refinements

An exact proposition-valued denotation square supplies the meaning-preserving
part of a NIK operational refinement.  The implication is deliberately
one-way: a refinement preserves membership in a selected semantic fibre,
whereas a denotation square equates the complete selected denotations of every
term.

Revision currentness and profitability are not mentioned by this bridge and
remain separate NIK judgments.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKDenotationSquareRefinement

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

universe uTerm

/-- Regard a proposition-valued semantic invariant as the semantic fibre of
an operational admission object. -/
def operationalObjectOfInvariant
    {system : GSLT.{uTerm}}
    (invariant : SemanticInvariant system Prop) : OperationalObject where
  theory := system
  Meaning := invariant.denote

/-- An exact denotation square with identity meaning map supplies a one-way
semantic refinement. -/
def refinementOfDenotationSquare
    {source target : GSLT.{uTerm}}
    {realization : OperationalRealization source target}
    {sourceInvariant : SemanticInvariant source Prop}
    {targetInvariant : SemanticInvariant target Prop}
    (square : DenotationSquare realization sourceInvariant targetInvariant
      _root_.id) :
    Refinement (operationalObjectOfInvariant sourceInvariant)
      (operationalObjectOfInvariant targetInvariant) where
  realization := realization
  preservesMeaning := by
    intro term meaningful
    change targetInvariant.denote (realization.mapTerm term)
    rw [square.commutes]
    exact meaningful

@[simp] theorem refinementOfDenotationSquare_realization
    {source target : GSLT.{uTerm}}
    {realization : OperationalRealization source target}
    {sourceInvariant : SemanticInvariant source Prop}
    {targetInvariant : SemanticInvariant target Prop}
    (square : DenotationSquare realization sourceInvariant targetInvariant
      _root_.id) :
    (refinementOfDenotationSquare square).realization = realization :=
  rfl

theorem refinementOfDenotationSquare_preserves
    {source target : GSLT.{uTerm}}
    {realization : OperationalRealization source target}
    {sourceInvariant : SemanticInvariant source Prop}
    {targetInvariant : SemanticInvariant target Prop}
    (square : DenotationSquare realization sourceInvariant targetInvariant
      _root_.id)
    (term : source.Term) (meaningful : sourceInvariant.denote term) :
    targetInvariant.denote (realization.mapTerm term) :=
  (refinementOfDenotationSquare square).preservesMeaning term meaningful

/-- The bridge respects composition: composing exact semantic squares and
then extracting a refinement agrees with composing the extracted
refinements. -/
theorem refinementOfDenotationSquare_comp
    {source middle target : GSLT.{uTerm}}
    {earlier : OperationalRealization source middle}
    {later : OperationalRealization middle target}
    {sourceInvariant : SemanticInvariant source Prop}
    {middleInvariant : SemanticInvariant middle Prop}
    {targetInvariant : SemanticInvariant target Prop}
    (earlierSquare : DenotationSquare earlier sourceInvariant middleInvariant
      _root_.id)
    (laterSquare : DenotationSquare later middleInvariant targetInvariant
      _root_.id) :
    Refinement.comp
        (refinementOfDenotationSquare earlierSquare)
        (refinementOfDenotationSquare laterSquare) =
      refinementOfDenotationSquare
        (DenotationSquare.comp earlierSquare laterSquare) := by
  rfl

/-! ## The converse fails -/

namespace Canary

/-- A discrete two-term operational system isolates semantic strength from
rewrite behavior. -/
abbrev booleanSystem : GSLT := GSLT.discrete Bool

/-- Only `true` belongs to the selected source fibre. -/
def positiveInvariant : SemanticInvariant booleanSystem Prop where
  denote value := value = true
  equation := fun equal => congrArg (fun value => value = true) equal
  rewrite := fun impossible => impossible.elim

/-- Every term belongs to the coarser target fibre. -/
def indiscriminateInvariant : SemanticInvariant booleanSystem Prop where
  denote _ := True
  equation := fun _ => rfl
  rewrite := fun impossible => impossible.elim

/-- Identity execution preserves membership from the narrower fibre into the
coarser one. -/
def weakRefinement :
    Refinement (operationalObjectOfInvariant positiveInvariant)
      (operationalObjectOfInvariant indiscriminateInvariant) where
  realization := OperationalRealization.id booleanSystem
  preservesMeaning := fun _ _ => trivial

theorem weakRefinement_preserves_true :
    (operationalObjectOfInvariant indiscriminateInvariant).Meaning
      (weakRefinement.realization.mapTerm true) :=
  trivial

/-- One-way fibre preservation does not imply equality of complete
denotations. -/
theorem weak_refinement_has_no_exact_denotation_square :
    ¬ DenotationSquare (OperationalRealization.id booleanSystem)
      positiveInvariant indiscriminateInvariant _root_.id := by
  intro square
  have impossible : false = true :=
    Eq.mp (square.commutes false) trivial
  exact Bool.false_ne_true impossible

end Canary

/-! ## Axiom audit -/

#print axioms refinementOfDenotationSquare
#print axioms refinementOfDenotationSquare_preserves
#print axioms refinementOfDenotationSquare_comp
#print axioms Canary.weak_refinement_has_no_exact_denotation_square

end Mettapedia.GSLT.LanguageDef.NIKDenotationSquareRefinement
