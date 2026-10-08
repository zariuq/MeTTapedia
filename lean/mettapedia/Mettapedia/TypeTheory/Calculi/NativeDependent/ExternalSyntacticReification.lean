import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticVariables
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalInterpretation

/-!
# Source value and substitution reification

A source value is reified by an actual generated typed term with its authored
code. Complete term classes retain the dependent annotation, so checking a
value at an equal family earns a generated conversion. Successful telescope
assembly then reconstructs an admitted source substitution with every supplied
argument in its original position.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open SyntacticTelescopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

def TermReadout (context : QuotientCwf.QContext D) (code : TermExpr S context.as.arity)
    (value : Value (QuotientCwf.cwf D) context) : Prop :=
  ∃ annotation : TypeOver context.as, ∃ term : Term context.as annotation,
    term.code = code ∧ QTerm.mk term = value.2.val

def TypeReadout (context : QuotientCwf.QContext D) (code : TypeExpr S context.as.arity)
    (value : QuotientCwf.Ty context) : Prop :=
  ∃ annotation : TypeOver context.as, annotation.code = code ∧ QType.mk annotation = value

theorem value_ext {context : QuotientCwf.QContext D}
    {first second : Value (QuotientCwf.cwf D) context}
    (classes : first.2.val = second.2.val) : first = second := by
  cases first with
  | mk firstType firstTerm =>
    cases second with
    | mk secondType secondTerm =>
      have types : firstType = secondType :=
        firstTerm.property.symm.trans ((congrArg QTerm.type classes).trans secondTerm.property)
      cases types
      have terms : firstTerm = secondTerm := Subtype.ext classes
      cases terms
      rfl

theorem term_readout_class {context : QuotientCwf.QContext D}
    {annotation : TypeOver context.as} (term : Term context.as annotation) :
    TermReadout context term.code ⟨QType.mk annotation, ⟨QTerm.mk term, rfl⟩⟩ :=
  ⟨annotation, term, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem retype {context : QuotientCwf.QContext D} {code : TermExpr S context.as.arity}
    {value : Value (QuotientCwf.cwf D) context} (readout : TermReadout context code value)
    (annotation : TypeOver context.as) (same : value.1 = QType.mk annotation) :
    ∃ term : Term context.as annotation, term.code = code ∧ QTerm.mk term = value.2.val := by
  rcases readout with ⟨original, term, codeRead, classRead⟩
  have types : QType.mk original = QType.mk annotation :=
    (congrArg QTerm.type classRead).trans (value.2.property.trans same)
  let converted := term.convertType annotation ((QType.mk_eq_iff _ _).mp types)
  exact ⟨converted, codeRead, (QTerm.mk_convertType term annotation _).trans classRead⟩

theorem checked_retype {context : QuotientCwf.QContext D}
    {code : TermExpr S context.as.arity} {value : Value (QuotientCwf.cwf D) context}
    (readout : TermReadout context code value) (annotation : TypeOver context.as)
    (term : QuotientCwf.Tm context (QType.mk annotation))
    (checked : Value.atType? value (QType.mk annotation) = some term) :
    ∃ actual : Term context.as annotation, actual.code = code ∧ QTerm.mk actual = term.val := by
  have values := (Value.atType?_eq_some_iff _ _ _).mp checked
  subst value
  exact retype readout annotation rfl

set_option backward.isDefEq.respectTransparency false in
theorem project_pair {source target : Context D} (morphism : source ⟶ target)
    (family : QType target)
    (term : Term source ((QuotientCwf.typeRepresentative family).reindex morphism))
    (supplied : QuotientCwf.Tm ((quotientProjection D).obj source)
      (QuotientCwf.tySub family (QuotientCwf.project morphism)))
    (classes : QTerm.mk term = supplied.val) :
    QuotientCwf.project (Contextual.pair morphism term) =
      QuotientCwf.pair (QuotientCwf.project morphism) family supplied := by
  apply QuotientCwf.pair_unique family
  · calc
      _ = QuotientCwf.project (Contextual.pair morphism term ≫
          projectionHom target (QuotientCwf.typeRepresentative family)) :=
        ((quotientProjection D).map_comp _ _).symm
      _ = QuotientCwf.project morphism :=
        congrArg QuotientCwf.project (Contextual.pair_projection morphism term)
      _ = _ := (QuotientCwf.wk_pair _ _ _).symm
  · exact (QuotientCwf.raw_newest_pair _ morphism term).trans
      (classes.trans (QuotientCwf.vz_pair_value _ _ supplied).symm)

set_option backward.isDefEq.respectTransparency false in
theorem components_readout : {n : Nat} → {target : QuotientCwf.QContext D} →
    (telescope : Telescope (QuotientCwf.withTerminal D) n target) →
    (source : Context D) → (codes : Fin n → TermExpr S source.arity) →
    (morphism : (quotientProjection D).obj source ⟶ target) →
    (∀ index, TermReadout _ (codes index) (telescope.components morphism index)) →
    ∃ actual : source ⟶ target.as,
      QuotientCwf.project actual = morphism ∧
      ∀ index, actual.substitution (Fin.cast (telescope_arity telescope).symm index) = codes index
  | _, _, .nil, source, _, morphism, _ =>
      ⟨toEmpty source, ((QuotientCwf.withTerminal D).toEmpty_unique _ morphism).symm,
        fun index => Fin.elim0 index⟩
  | _, _, @Telescope.snoc _ n target previous family, source, codes, morphism, readouts => by
      rcases components_readout previous source (fun index => codes index.succ)
        (morphism ≫ QuotientCwf.wk family)
        (fun index => by
          simpa only [Telescope.components_succ, QuotientCwf.withTerminal, QuotientCwf.cwf]
            using readouts index.succ) with
        ⟨rawOlder, oldClass, oldCodes⟩
      let value := (previous.snoc family).components morphism 0
      have atType : value.1 = QType.mk
          ((QuotientCwf.typeRepresentative family).reindex rawOlder) := by
        change QuotientCwf.tySub (QuotientCwf.tySub family (QuotientCwf.wk family)) morphism = _
        calc
          _ = QuotientCwf.tySub family (morphism ≫ QuotientCwf.wk family) :=
            (QuotientCwf.tySub_comp _ _ _).symm
          _ = QuotientCwf.tySub family (QuotientCwf.project rawOlder) :=
            (congrArg (QuotientCwf.tySub family) oldClass).symm
          _ = _ := (congrArg (fun type => type.reindex rawOlder)
            (QuotientCwf.typeRepresentative_class family)).symm
      rcases retype (readouts 0) ((QuotientCwf.typeRepresentative family).reindex rawOlder) atType with
        ⟨rawNewest, newCode, newClass⟩
      let rawPair := Contextual.pair rawOlder rawNewest
      have classRead : QuotientCwf.project rawPair = morphism := by
        apply QuotientCwf.pair_unique family
        · calc
            _ = QuotientCwf.project (rawPair ≫ projectionHom target.as
                (QuotientCwf.typeRepresentative family)) := ((quotientProjection D).map_comp _ _).symm
            _ = QuotientCwf.project rawOlder :=
              congrArg QuotientCwf.project (Contextual.pair_projection rawOlder rawNewest)
            _ = _ := oldClass
        · exact (QuotientCwf.raw_newest_pair _ rawOlder rawNewest).trans newClass
      refine ⟨rawPair, classRead, ?_⟩
      intro index
      cases index using Fin.cases with
      | zero =>
          rw [cast_zero (telescope_arity previous).symm]
          exact newCode
      | succ preceding =>
          rw [cast_succ (telescope_arity previous).symm]
          exact oldCodes preceding

theorem assemble_readout {n : Nat} {target : QuotientCwf.QContext D}
    (telescope : Telescope (QuotientCwf.withTerminal D) n target)
    (source : Context D) (codes : Fin n → TermExpr S source.arity)
    (supplied : Fin n → Option (Value (QuotientCwf.cwf D) ((quotientProjection D).obj source)))
    (readouts : ∀ index value, supplied index = some value → TermReadout _ (codes index) value)
    (morphism : (quotientProjection D).obj source ⟶ target)
    (assembled : telescope.assemble? supplied = some morphism) :
    ∃ actual : source ⟶ target.as,
      QuotientCwf.project actual = morphism ∧
      ∀ index, actual.substitution (Fin.cast (telescope_arity telescope).symm index) = codes index :=
  components_readout telescope source codes morphism (fun index =>
    readouts index _ (Telescope.assemble?_sound telescope supplied morphism assembled index))

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification
