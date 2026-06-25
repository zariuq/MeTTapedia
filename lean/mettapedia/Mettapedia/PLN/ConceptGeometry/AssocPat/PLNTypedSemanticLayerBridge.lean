import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel

/-!
# Typed Semantic-Layer Gate for Intensional WM-PLN

This module packages the small representation-layer lesson used by the
Chapter-12 ASSOC/PAT work: semantic layer tags should select the existing
inheritance channels, not define a second inheritance semantics.
-/

namespace Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel

/-- Coarse semantic layer tag for inheritance-facing statements.  The tag is a
gate into the already-existing inheritance query channels. -/
inductive SemanticInheritanceLayer where
  | extensional
  | preextensional
  | intensional
  | mixed
  deriving DecidableEq, Repr

/-- Choice of intensional evidence method when a semantic layer asks for an
intensional channel. -/
inductive IntensionalMethod where
  | assoc
  | pat
  deriving DecidableEq, Repr

namespace SemanticInheritanceLayer

/-- Semantic layer tags select the existing typed inheritance sort.  Extensional
and mixed layers ignore the method; preextensional/intensional layers choose
between the ASSOC and PAT channels. -/
def toInheritanceSort
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod) :
    InheritanceSort :=
  match layer with
  | .extensional => .extensional
  | .mixed => .mixed
  | .preextensional =>
      match method with
      | .assoc => .intensionalAssoc
      | .pat => .intensionalPAT
  | .intensional =>
      match method with
      | .assoc => .intensionalAssoc
      | .pat => .intensionalPAT

@[simp] theorem toInheritanceSort_extensional (method : IntensionalMethod) :
    toInheritanceSort .extensional method = .extensional := by
  cases method <;> rfl

@[simp] theorem toInheritanceSort_mixed (method : IntensionalMethod) :
    toInheritanceSort .mixed method = .mixed := by
  cases method <;> rfl

@[simp] theorem toInheritanceSort_preextensional_assoc :
    toInheritanceSort .preextensional .assoc = .intensionalAssoc := rfl

@[simp] theorem toInheritanceSort_preextensional_pat :
    toInheritanceSort .preextensional .pat = .intensionalPAT := rfl

@[simp] theorem toInheritanceSort_intensional_assoc :
    toInheritanceSort .intensional .assoc = .intensionalAssoc := rfl

@[simp] theorem toInheritanceSort_intensional_pat :
    toInheritanceSort .intensional .pat = .intensionalPAT := rfl

/-- Negative canary: preextensional ASSOC does not collapse to the extensional
channel. -/
theorem toInheritanceSort_preextensional_assoc_ne_extensional :
    toInheritanceSort .preextensional .assoc ≠ .extensional := by
  decide

/-- Negative canary: intensional PAT does not collapse to the extensional
channel. -/
theorem toInheritanceSort_intensional_pat_ne_extensional :
    toInheritanceSort .intensional .pat ≠ .extensional := by
  decide

end SemanticInheritanceLayer

namespace InheritanceQueryBuilder

variable {State Atom Query : Type}
variable [EvidenceType State]
variable [WorldModelSigma State InheritanceSort (InheritanceQueryFamily Query)]

/-- Typed query selected by a semantic layer tag.  This is the query-level
version of the gate: it selects the existing extensional, ASSOC, PAT, or mixed
query constructor. -/
def semanticLayerQ
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    Sigma (InheritanceQueryFamily Query) :=
  match layer, method with
  | .extensional, _ => extQ enc a b
  | .mixed, _ => mixedQ enc a b
  | .preextensional, .assoc => assocQ enc a b
  | .preextensional, .pat => patQ enc a b
  | .intensional, .assoc => assocQ enc a b
  | .intensional, .pat => patQ enc a b

@[simp] theorem semanticLayerQ_extensional
    (method : IntensionalMethod)
    (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerQ .extensional method enc a b = extQ enc a b := by
  cases method <;> rfl

@[simp] theorem semanticLayerQ_mixed
    (method : IntensionalMethod)
    (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerQ .mixed method enc a b = mixedQ enc a b := by
  cases method <;> rfl

@[simp] theorem semanticLayerQ_preextensional_assoc
    (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerQ .preextensional .assoc enc a b = assocQ enc a b := rfl

@[simp] theorem semanticLayerQ_preextensional_pat
    (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerQ .preextensional .pat enc a b = patQ enc a b := rfl

@[simp] theorem semanticLayerQ_intensional_assoc
    (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerQ .intensional .assoc enc a b = assocQ enc a b := rfl

@[simp] theorem semanticLayerQ_intensional_pat
    (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerQ .intensional .pat enc a b = patQ enc a b := rfl

@[simp] theorem semanticLayerQ_sort
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    (semanticLayerQ layer method enc a b).1 =
      SemanticInheritanceLayer.toInheritanceSort layer method := by
  cases layer <;> cases method <;> rfl

/-- Evidence selected by a semantic layer tag.  This is just a typed gate over
the existing extensional, ASSOC, PAT, and mixed evidence projections. -/
def semanticLayerEvidence
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    BinaryEvidence :=
  WorldModelSigma.evidence (State := State) (Srt := InheritanceSort)
    (Query := InheritanceQueryFamily Query) W (semanticLayerQ layer method enc a b)

@[simp] theorem semanticLayerEvidence_extensional
    (method : IntensionalMethod)
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerEvidence .extensional method W enc a b =
      extensionalEvidence W enc a b := by
  cases method <;> rfl

@[simp] theorem semanticLayerEvidence_mixed
    (method : IntensionalMethod)
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerEvidence .mixed method W enc a b =
      mixedEvidence W enc a b := by
  cases method <;> rfl

@[simp] theorem semanticLayerEvidence_preextensional_assoc
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerEvidence .preextensional .assoc W enc a b =
      intensionalAssocEvidence W enc a b := rfl

@[simp] theorem semanticLayerEvidence_preextensional_pat
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerEvidence .preextensional .pat W enc a b =
      intensionalPATEvidence W enc a b := rfl

@[simp] theorem semanticLayerEvidence_intensional_assoc
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerEvidence .intensional .assoc W enc a b =
      intensionalAssocEvidence W enc a b := rfl

@[simp] theorem semanticLayerEvidence_intensional_pat
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerEvidence .intensional .pat W enc a b =
      intensionalPATEvidence W enc a b := rfl

/-- Additivity is inherited from the selected evidence channel. -/
@[simp] theorem semanticLayerEvidence_add
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (W₁ W₂ : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    semanticLayerEvidence layer method W₁ enc a b +
        semanticLayerEvidence layer method W₂ enc a b =
      semanticLayerEvidence layer method (W₁ + W₂) enc a b := by
  symm
  simpa [semanticLayerEvidence] using
    (WorldModelSigma.evidence_add (State := State) (Srt := InheritanceSort)
      (Query := InheritanceQueryFamily Query) W₁ W₂ (semanticLayerQ layer method enc a b))

end InheritanceQueryBuilder

end Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel
