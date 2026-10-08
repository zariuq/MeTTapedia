import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPresheafCertificates
import Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution

/-!
# Decoding generated comprehension certificates

Independently evaluated domain and predicate expressions determine the
actual chosen native refinement type. The generated term certificate has
that type because both successful type reads come from the same authored
evaluator. Its canonical decoder then retains an actual domain inhabitant
together with membership in the evaluated predicate. No separate whole-term
membership or predicate-respecting implementation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPresheafComprehensionCertificates

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSliceSubstitution
open NativeLocalTypeFormers
open RefinementPresheafCertificates

universe u
variable {C : Type u} [Category.{u} C]
variable {S : Refinement.Symbols.{u}} {D : Refinement.Signature S} {n : Nat}
variable {context : Refinement.ContextExpr S n} {term : Refinement.TermExpr S n}
variable {domain : Refinement.TypeExpr S n} {predicate : Refinement.PropExpr S (n + 1)}
variable {P : Cᵒᵖ ⥤ Type u}

variable (interpretation : Interpretation D context term (.comprehension domain predicate) P)

local instance semanticCategory : Category.{u} interpretation.semanticContext.1.Elements :=
  categoryOfElements (interpretation.semanticContext.1 : Cᵒᵖ ⥤ Type u)

variable (A : NativeType interpretation.semanticContext.1)
variable (selected : Subfunctor ((Refinement.NativeModel C).toCwf.ext
  interpretation.semanticContext.1 A))
variable (domainRead : interpretation.model.evaluateType interpretation.semanticContext domain = some A)
variable (predicateRead : interpretation.model.evaluatePredicate
  (interpretation.semanticContext.snoc A) predicate = some selected)

include domainRead predicateRead in
/-- Equality comes from independently formed successful evaluator reads. -/
theorem interpreted_type :
    interpretation.semanticType = PresheafNativeStableRefinement.chosen A selected :=
  Option.some.inj (interpretation.typeRead.symm.trans
    (interpretation.model.evaluate_comprehension interpretation.semanticContext domain predicate A selected
      domainRead predicateRead))

/-- The actual chosen-type decoder exposes the complete selected domain value. -/
noncomputable def decoder :
    interpretation.decodedFamily ≅ PresheafNativePredicateRefinement.displayed A.decoded selected :=
  eqToIso (congrArg (fun type : NativeType interpretation.semanticContext.1 => type.decoded)
    (interpreted_type interpretation A selected domainRead predicateRead)) ≪≫
      PresheafNativeStableRefinement.decodeIso A selected

def selectedValueFamily : DisplayedFamily P :=
  reindexDisplayed interpretation.interface (PresheafNativePredicateRefinement.displayed A.decoded selected)

noncomputable def selectedValueReadout : interpretation.certificates ⟶
    selectedValueFamily interpretation A selected :=
  interpretation.valueReadout ≫ (reindexFunctor interpretation.interface).map
    (decoder interpretation A selected domainRead predicateRead).hom

theorem selectedValue_membership (point : P.Elements)
    (certificate : interpretation.Certificate point) :
    (⟨(interpretation.interface.mapElements.obj point).2,
      ((selectedValueReadout interpretation A selected domainRead predicateRead).app point certificate).val⟩ :
        (totalSpace A.decoded).obj point.1) ∈ selected.obj point.1 :=
  ((selectedValueReadout interpretation A selected domainRead predicateRead).app point certificate).property

/-- The decoder is applied to the actual generated evaluator value. -/
theorem selectedValue_computes (point : P.Elements)
    (tree : Refinement.Derivation D (.term context term (.comprehension domain predicate))) :
    (selectedValueReadout interpretation A selected domainRead predicateRead).app point
      ((interpretation.certificateSection tree).val point) =
      (decoder interpretation A selected domainRead predicateRead).hom.app
        (interpretation.interface.mapElements.obj point)
          ((interpretation.nativeSection tree).val (interpretation.interface.mapElements.obj point)) := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPresheafComprehensionCertificates
