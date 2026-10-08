import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPredicates
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualCwf

/-!
# First-class propositions in the generated source model

The ordinary proposition type has terms modulo actual generated term equations.
Quotation and predicate readout are inverse natural maps between these terms
and generated predicate classes. The term fibre also compares to the constructed
category with families. No internal type universe or unrestricted subobject
classifier on the raw source category is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

def propositionsType (context : Context D) : TypeOver context :=
  ⟨.propositions, conclude (.propositionType context.raw) ⟨context.formed.judgment, trivial⟩⟩

def quotePredicate {context : Context D} (predicate : PredicateOver context) :
    Term context (propositionsType context) :=
  ⟨.quote predicate.code, conclude (.quote context.raw predicate.code) ⟨predicate.formed, trivial⟩⟩

def holdsProposition {context : Context D} (term : Term context (propositionsType context)) :
    PredicateOver context :=
  ⟨.holds term.code, conclude (.holdsFormation context.raw term.code) ⟨term.typed, trivial⟩⟩

def propositionTermSetoid (context : Context D) : Setoid (Term context (propositionsType context)) where
  r first second := Holds D (.termEq context.raw first.code second.code .propositions)
  iseqv := ⟨termEquality_refl, termEquality_symm, termEquality_trans⟩

def QPropositionTerm (context : Context D) := _root_.Quotient (propositionTermSetoid context)

def QPropositionTerm.mk {context : Context D} (term : Term context (propositionsType context)) :
    QPropositionTerm context := _root_.Quotient.mk _ term

theorem QPropositionTerm.mk_eq_iff {context : Context D}
    (first second : Term context (propositionsType context)) :
    QPropositionTerm.mk first = QPropositionTerm.mk second ↔
      Holds D (.termEq context.raw first.code second.code .propositions) := _root_.Quotient.eq

def QPredicate.quote {context : Context D} (predicate : QPredicate context) : QPropositionTerm context :=
  _root_.Quotient.map quotePredicate (fun first second same =>
    conclude (.quoteCongruence context.raw first.code second.code) ⟨same, trivial⟩) predicate

def QPropositionTerm.holds {context : Context D} (term : QPropositionTerm context) : QPredicate context :=
  _root_.Quotient.map holdsProposition (fun first second same =>
    conclude (.holdsCongruence context.raw first.code second.code) ⟨same, trivial⟩) term

@[simp] theorem QPredicate.holds_quote {context : Context D} (predicate : QPredicate context) :
    predicate.quote.holds = predicate := by
  refine _root_.Quotient.inductionOn predicate fun formed => ?_
  exact _root_.Quotient.sound
    (conclude (.holdsQuote context.raw formed.code) ⟨formed.formed, trivial⟩)

@[simp] theorem QPropositionTerm.quote_holds {context : Context D} (term : QPropositionTerm context) :
    term.holds.quote = term := by
  refine _root_.Quotient.inductionOn term fun typed => ?_
  exact _root_.Quotient.sound
    (conclude (.quoteHolds context.raw typed.code) ⟨typed.typed, trivial⟩)

def propositionEquiv (context : Context D) : QPredicate context ≃ QPropositionTerm context where
  toFun := QPredicate.quote
  invFun := QPropositionTerm.holds
  left_inv := QPredicate.holds_quote
  right_inv := QPropositionTerm.quote_holds

def substituteProposition {source target : Context D}
    (term : Term target (propositionsType target)) (morphism : source ⟶ target) :
    Term source (propositionsType source) :=
  ⟨term.code.substitute morphism.substitution,
    conclude (.substituteTerm source.raw target.raw morphism.substitution term.code .propositions)
      ⟨morphism.admitted, term.typed, trivial⟩⟩

def QPropositionTerm.reindex {source target : Context D} (term : QPropositionTerm target)
    (morphism : source ⟶ target) : QPropositionTerm source :=
  _root_.Quotient.map (fun typed => substituteProposition typed morphism)
    (fun first second same =>
      conclude (.substituteTermEquality source.raw target.raw morphism.substitution
        first.code second.code .propositions) ⟨morphism.admitted, same, trivial⟩) term

theorem QPropositionTerm.reindex_id {context : Context D} (term : QPropositionTerm context) :
    term.reindex (𝟙 context) = term := by
  refine _root_.Quotient.inductionOn term fun typed => ?_
  apply congrArg QPropositionTerm.mk
  exact Term.ext (TermExpr.substitute_identity typed.code)

theorem QPropositionTerm.reindex_comp {source middle target : Context D}
    (term : QPropositionTerm target) (earlier : source ⟶ middle) (later : middle ⟶ target) :
    term.reindex (earlier ≫ later) = (term.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn term fun typed => ?_
  apply congrArg QPropositionTerm.mk
  exact Term.ext (TermExpr.substitute_comp later.substitution earlier.substitution typed.code).symm

theorem QPropositionTerm.reindex_congruent {source target : Context D}
    (term : QPropositionTerm target) {first second : source ⟶ target}
    (same : homEquality D first second) : term.reindex first = term.reindex second := by
  refine _root_.Quotient.inductionOn term fun typed => ?_
  exact _root_.Quotient.sound
    (conclude (.termSubstitutionCongruence source.raw target.raw first.substitution
      second.substitution typed.code .propositions) ⟨same, typed.typed, trivial⟩)

theorem quote_reindex {source target : Context D} (predicate : QPredicate target)
    (morphism : source ⟶ target) :
    (predicate.reindex morphism).quote = predicate.quote.reindex morphism := by
  refine _root_.Quotient.inductionOn predicate fun _ => rfl

theorem holds_reindex {source target : Context D} (term : QPropositionTerm target)
    (morphism : source ⟶ target) :
    (term.reindex morphism).holds = term.holds.reindex morphism := by
  refine _root_.Quotient.inductionOn term fun _ => rfl

def QPropositionTerm.rawPresheaf (D : Signature S) : (Context D)ᵒᵖ ⥤ Type u where
  obj context := QPropositionTerm context.unop
  map morphism := TypeCat.ofHom fun term => term.reindex morphism.unop
  map_id _ := by ext term; exact QPropositionTerm.reindex_id term
  map_comp first second := by
    ext term
    exact QPropositionTerm.reindex_comp term second.unop first.unop

def QPropositionTerm.presheaf (D : Signature S) : (quotientContext D)ᵒᵖ ⥤ Type u :=
  (_root_.CategoryTheory.Quotient.lift (homEquality D) (QPropositionTerm.rawPresheaf D).rightOp
    (fun _ _ _ _ same => Quiver.Hom.unop_inj
      (by ext term; exact QPropositionTerm.reindex_congruent term same))).leftOp

theorem quote_natural {source target : quotientContext D} (morphism : source ⟶ target)
    (predicate : QPredicate target.as) :
    ((QPredicate.presheaf D).map morphism.op predicate).quote =
      (QPropositionTerm.presheaf D).map morphism.op predicate.quote := by
  revert predicate
  refine Quot.inductionOn morphism (fun raw predicate => ?_)
  exact quote_reindex predicate raw

def nativePropositionIso (D : Signature S) : QPredicate.presheaf D ≅ QPropositionTerm.presheaf D :=
  NatIso.ofComponents (fun context => (propositionEquiv context.unop.as).toIso) (by
    intro source target arrow
    ext predicate
    exact quote_natural arrow.unop predicate)

def propositionTermToCwf {context : Context D} (term : QPropositionTerm context) :
    QuotientCwf.Tm ((quotientProjection D).obj context) (QType.mk (propositionsType context)) :=
  _root_.Quotient.lift (fun typed : Term context (propositionsType context) =>
    ⟨QTerm.mk typed, rfl⟩) (fun _ _ same =>
      Subtype.ext (_root_.Quotient.sound ⟨typeEquality_refl (propositionsType context), same⟩)) term

noncomputable def propositionTermFromCwf {context : Context D}
    (term : QuotientCwf.Tm ((quotientProjection D).obj context) (QType.mk (propositionsType context))) :
    QPropositionTerm context :=
  QPropositionTerm.mk (QuotientCwf.termRepresentative (propositionsType context) term.val term.property)

theorem propositionTermToCwf_from {context : Context D}
    (term : QuotientCwf.Tm ((quotientProjection D).obj context) (QType.mk (propositionsType context))) :
    propositionTermToCwf (propositionTermFromCwf term) = term :=
  Subtype.ext (QuotientCwf.termRepresentative_class (propositionsType context) term.val term.property)

theorem propositionTermFromCwf_to {context : Context D} (term : QPropositionTerm context) :
    propositionTermFromCwf (propositionTermToCwf term) = term := by
  refine _root_.Quotient.inductionOn term fun typed => ?_
  apply (QPropositionTerm.mk_eq_iff _ _).mpr
  exact ((QTerm.mk_eq_iff _ typed).mp
    (QuotientCwf.termRepresentative_class (propositionsType context) (QTerm.mk typed) rfl)).2

noncomputable def propositionCwfEquiv (context : Context D) : QPropositionTerm context ≃
    QuotientCwf.Tm ((quotientProjection D).obj context) (QType.mk (propositionsType context)) where
  toFun := propositionTermToCwf
  invFun := propositionTermFromCwf
  left_inv := propositionTermFromCwf_to
  right_inv := propositionTermToCwf_from

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual
