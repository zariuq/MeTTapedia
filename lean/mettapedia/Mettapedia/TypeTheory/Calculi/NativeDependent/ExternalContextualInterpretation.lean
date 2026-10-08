import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalEvidenceExtraction
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualCwf
import Mettapedia.GSLT.Core.ContextualLadderBaseCategory

/-!
# Interpretation of generated contextual equation classes

A model supplies local dependent constructors, their computational equations
and the interpretations of its primitive declarations. Generated soundness
then earns actual values of every admitted telescope, family, section and
substitution. Typed equation soundness earns descent to the independently
authored contextual quotient; the evaluator readouts retain the witnesses.

The construction admits independently sized target carriers. No global
interpretation or classifying property is included in the model data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe u c s t m
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c, s, t, m}}

/-- Only primitive declaration realization and local constructor equations
qualify the independently supplied model. -/
structure QualifiedModel (D : Signature S) (C : CwfWithTerminal.{c, s, t, m}) where
  data : ModelData S C
  realization : SignatureRealization data D
  products_substitution : StrictPiSubstitution data.products
  products_beta : PiBeta data.products
  products_eta : PiEta data.products products_substitution.1

variable (model : QualifiedModel D C)

noncomputable def contextValue (context : Context D) :
    ContextualModelTelescopes.Context C context.arity :=
  (Classical.choice context.formed.judgment).contextValue model.data model.realization
    model.products_substitution model.products_beta model.products_eta

theorem context_readout (context : Context D) :
    model.data.evaluateContext context.raw = some (contextValue model context) :=
  (Classical.choice context.formed.judgment).contextValue_readout model.data model.realization
    model.products_substitution model.products_beta model.products_eta

noncomputable def rawType {context : Context D} (type : TypeOver context) :
    C.toCwf.Ty (contextValue model context).1 :=
  (Classical.choice type.formed).typeValue model.data model.realization
    model.products_substitution model.products_beta model.products_eta _ (context_readout model context)

theorem type_readout {context : Context D} (type : TypeOver context) :
    model.data.evaluateType (contextValue model context) type.code = some (rawType model type) :=
  (Classical.choice type.formed).typeValue_readout model.data model.realization
    model.products_substitution model.products_beta model.products_eta _ (context_readout model context)

theorem rawType_congruent {context : Context D} {first second : TypeOver context}
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    rawType model first = rawType model second :=
  (Classical.choice first.formed).typeValue_equation model.data model.realization
    model.products_substitution model.products_beta model.products_eta
    (Classical.choice second.formed) (Classical.choice same) _ (context_readout model context)

noncomputable def typeValue {context : Context D} (type : QType context) :
    C.toCwf.Ty (contextValue model context).1 :=
  _root_.Quotient.lift (rawType model) (fun _ _ same => rawType_congruent model same) type

@[simp] theorem typeValue_mk {context : Context D} (type : TypeOver context) :
    typeValue model (QType.mk type) = rawType model type := rfl

noncomputable def rawTerm {context : Context D} {type : TypeOver context} (term : Term context type) :
    C.toCwf.Tm (contextValue model context).1 (rawType model type) :=
  (Classical.choice term.typed).termSection model.data model.realization
    model.products_substitution model.products_beta model.products_eta _ _
      (context_readout model context) (type_readout model type)

theorem term_readout {context : Context D} {type : TypeOver context} (term : Term context type) :
    model.data.evaluateTerm (contextValue model context) term.code =
      some ⟨rawType model type, rawTerm model term⟩ :=
  (Classical.choice term.typed).termSection_readout model.data model.realization
    model.products_substitution model.products_beta model.products_eta _ _
      (context_readout model context) (type_readout model type)

noncomputable def rawTotal {context : Context D} (term : TotalTerm context) :
    ContextualModelTelescopes.Value C.toCwf (contextValue model context).1 :=
  ⟨rawType model term.1, rawTerm model term.2⟩

theorem rawTotal_congruent {context : Context D} {first second : TotalTerm context}
    (same : (totalTermSetoid context).r first second) :
    rawTotal model first = rawTotal model second := by
  rcases ((Classical.choice same.2).sound model.data model.realization
    model.products_substitution model.products_beta model.products_eta).termEqAt
      (contextValue model context) (rawType model first.1)
      (context_readout model context) (type_readout model first.1) with
        ⟨value, firstRead, secondRead⟩
  exact Option.some.inj ((term_readout model first.2).symm.trans
    (firstRead.trans (secondRead.symm.trans (term_readout model second.2))))

noncomputable def totalValue {context : Context D} (term : QTerm context) :
    ContextualModelTelescopes.Value C.toCwf (contextValue model context).1 :=
  _root_.Quotient.lift (rawTotal model) (fun _ _ same => rawTotal_congruent model same) term

@[simp] theorem totalValue_mk {context : Context D} {type : TypeOver context} (term : Term context type) :
    totalValue model (QTerm.mk term) = ⟨rawType model type, rawTerm model term⟩ := rfl

theorem totalValue_type {context : Context D} (term : QTerm context) :
    (totalValue model term).1 = typeValue model term.type := by
  induction term using _root_.Quotient.inductionOn with
  | h representative => rfl

/-- A fibre equation transports the retained section to the exact supplied
semantic family. The total-term quotient was formed independently. -/
noncomputable def termValue {context : QuotientCwf.QContext D} {type : QuotientCwf.Ty context}
    (term : QuotientCwf.Tm context type) :
    C.toCwf.Tm (contextValue model context.as).1 (typeValue model type) :=
  cast (congrArg (C.toCwf.Tm (contextValue model context.as).1)
    ((totalValue_type model term.val).trans (congrArg (typeValue model) term.property)))
      (totalValue model term.val).2

theorem termValue_retains_section {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type) :
    HEq (termValue model term) (totalValue model term.val).2 := cast_heq _ _

noncomputable def rawArrow {source target : Context D} (morphism : source ⟶ target) :
    C.toCwf.Sub (contextValue model source).1 (contextValue model target).1 :=
  (Classical.choice morphism.admitted).substitutionArrow model.data model.realization
    model.products_substitution model.products_beta model.products_eta _ _
      (context_readout model source) (context_readout model target)

theorem arrow_readout {source target : Context D} (morphism : source ⟶ target) :
    model.data.evaluateSubstitution (contextValue model source) (contextValue model target)
      morphism.substitution = some (rawArrow model morphism) :=
  (Classical.choice morphism.admitted).substitutionArrow_readout model.data model.realization
    model.products_substitution model.products_beta model.products_eta _ _
      (context_readout model source) (context_readout model target)

theorem rawArrow_congruent {source target : Context D} {first second : source ⟶ target}
    (same : homEquality D first second) : rawArrow model first = rawArrow model second :=
  (Classical.choice first.admitted).substitutionArrow_equation model.data model.realization
    model.products_substitution model.products_beta model.products_eta
    (Classical.choice second.admitted) (Classical.choice same) _ _
      (context_readout model source) (context_readout model target)

theorem rawArrow_id (context : Context D) :
    rawArrow model (𝟙 context) = C.toCwf.idS (contextValue model context).1 :=
  (Classical.choice (𝟙 context : context ⟶ context).admitted).substitutionArrow_unique
    model.data model.realization model.products_substitution model.products_beta model.products_eta
      _ _ (context_readout model context) (context_readout model context) _
        (model.data.evaluateSubstitution_identity (contextValue model context))

theorem rawArrow_comp {source middle target : Context D}
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    rawArrow model (earlier ≫ later) = C.toCwf.compS (rawArrow model later) (rawArrow model earlier) :=
  (Classical.choice (earlier ≫ later).admitted).substitutionArrow_unique model.data model.realization
    model.products_substitution model.products_beta model.products_eta
      _ _ (context_readout model source) (context_readout model target) _
        (model.data.evaluateSubstitution_composition model.products_substitution _ _ _
          later.substitution earlier.substitution (rawArrow model later) (rawArrow model earlier)
            (arrow_readout model later) (arrow_readout model earlier))

noncomputable def rawFunctor : Context D ⥤ C.toCwf.base.Context where
  obj context := ⟨(contextValue model context).1⟩
  map morphism := rawArrow model morphism
  map_id := rawArrow_id model
  map_comp := rawArrow_comp model

/-- Typed equation soundness earns categorical descent to the authored arrow
quotient, rather than assuming that the parser factors through it. -/
noncomputable def quotientFunctor : quotientContext D ⥤ C.toCwf.base.Context :=
  _root_.CategoryTheory.Quotient.lift (homEquality D) (rawFunctor model)
    (fun _ _ _ _ same => rawArrow_congruent model same)

@[simp] theorem quotientFunctor_object (context : quotientContext D) :
    (quotientFunctor model).obj context = ⟨(contextValue model context.as).1⟩ := rfl

@[simp] theorem quotientFunctor_project {source target : Context D} (morphism : source ⟶ target) :
    (quotientFunctor model).map ((quotientProjection D).map morphism) = rawArrow model morphism := rfl


noncomputable def arrowSubstitution {source target : Context D} (morphism : source ⟶ target) :
    ModelSubstitution model.data (contextValue model source) (contextValue model target)
      morphism.substitution :=
  ModelSubstitution.ofEvaluated model.data _ _ _ _ (arrow_readout model morphism)

theorem rawType_reindex {source target : Context D} (type : TypeOver target)
    (morphism : source ⟶ target) :
    rawType model (type.reindex morphism) = C.toCwf.tySub (rawType model type) (rawArrow model morphism) :=
  (Classical.choice (type.reindex morphism).formed).typeValue_unique
    model.data model.realization model.products_substitution model.products_beta model.products_eta
      _ (context_readout model source) _
        (model.data.evaluateType_substitute model.products_substitution type.code _ _
          morphism.substitution (arrowSubstitution model morphism) _ (type_readout model type))

theorem rawTotal_reindex {source target : Context D} (term : TotalTerm target)
    (morphism : source ⟶ target) :
    rawTotal model (term.reindex morphism) = (rawTotal model term).substitute (rawArrow model morphism) :=
  Option.some.inj ((term_readout model (term.2.reindex morphism)).symm.trans
    (model.data.evaluateTerm_substitute model.products_substitution term.2.code _ _
      morphism.substitution (arrowSubstitution model morphism) _ (term_readout model term.2)))

theorem typeValue_reindex {source target : Context D} (type : QType target)
    (morphism : source ⟶ target) :
    typeValue model (type.reindex morphism) = C.toCwf.tySub (typeValue model type) (rawArrow model morphism) := by
  induction type using _root_.Quotient.inductionOn with
  | h representative => exact rawType_reindex model representative morphism

theorem totalValue_reindex {source target : Context D} (term : QTerm target)
    (morphism : source ⟶ target) :
    totalValue model (term.reindex morphism) = (totalValue model term).substitute (rawArrow model morphism) := by
  induction term using _root_.Quotient.inductionOn with
  | h representative => exact rawTotal_reindex model representative morphism

theorem type_substitution {source target : quotientContext D} (type : QType target.as)
    (morphism : source ⟶ target) :
    typeValue model (QuotientCwf.tySub type morphism) =
      C.toCwf.tySub (typeValue model type) ((quotientFunctor model).map morphism) := by
  induction morphism using Quot.inductionOn with
  | h representative => exact typeValue_reindex model type representative

theorem total_substitution {source target : quotientContext D} (term : QTerm target.as)
    (morphism : source ⟶ target) :
    totalValue model (QuotientCwf.totalSub term morphism) =
      (totalValue model term).substitute ((quotientFunctor model).map morphism) := by
  induction morphism using Quot.inductionOn with
  | h representative => exact totalValue_reindex model term representative

theorem term_substitution {source target : quotientContext D} {type : QType target.as}
    (term : QuotientCwf.Tm target type) (morphism : source ⟶ target) :
    HEq (termValue model (QuotientCwf.tmSub term morphism))
      (C.toCwf.tmSub (termValue model term) ((quotientFunctor model).map morphism)) := by
  have values := total_substitution model term.val morphism
  have types := (totalValue_type model term.val).trans (congrArg (typeValue model) term.property)
  exact (termValue_retains_section model (QuotientCwf.tmSub term morphism)).trans
    ((Sigma.mk.inj values).2.trans
      (TypeOver.tmSub_heq types (termValue_retains_section model term).symm
        ((quotientFunctor model).map morphism)))

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Interpretation
