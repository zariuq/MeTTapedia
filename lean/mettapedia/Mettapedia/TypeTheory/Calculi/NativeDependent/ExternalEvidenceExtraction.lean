import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSoundness

/-!
# Canonical semantic sections of generated certificates

Successful interpretation of a generated term judgment proves that its actual
authored expression evaluator has a value at the supplied context and type.
The value is obtained from that evaluator. Its readout determines it uniquely,
independently of the supplied derivation and converted annotation proof.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}}
  {D : Signature S} {n : Nat}

namespace Interprets

theorem termChecked_isSome {model : ModelData S C} {context : ContextExpr S n}
    {term : TermExpr S n} {type : TypeExpr S n}
    (interpreted : Interprets model (.term context term type)) (Γ : Context C n)
    (A : C.toCwf.Ty Γ.1) (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    (ModelData.check? (model.evaluateTerm Γ term) A).isSome := by
  rcases interpreted.termAt Γ A contextRead typeRead with ⟨value, sectionRead⟩
  exact Option.isSome_iff_exists.mpr ⟨value,
    (ModelData.check?_eq_some_iff _ _ _).mpr sectionRead⟩

end Interprets

namespace Derivation

variable (model : ModelData S C) (realization : SignatureRealization model D)
  (stable : StrictPiSubstitution model.products) (beta : PiBeta model.products)
  (eta : PiEta model.products stable.1)
  {context : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}

include model realization stable beta eta

theorem contextValue_isSome (derivation : Derivation D (.context context)) :
    (model.evaluateContext context).isSome :=
  Option.isSome_iff_exists.mpr (derivation.sound model realization stable beta eta)

noncomputable def contextValue (derivation : Derivation D (.context context)) : Context C n :=
  (model.evaluateContext context).get (derivation.contextValue_isSome model realization stable beta eta)

theorem contextValue_readout (derivation : Derivation D (.context context)) :
    model.evaluateContext context = some (derivation.contextValue model realization stable beta eta) :=
  (Option.some_get _).symm

theorem contextValue_unique (derivation : Derivation D (.context context))
    (Γ : Context C n) (contextRead : model.evaluateContext context = some Γ) :
    derivation.contextValue model realization stable beta eta = Γ :=
  Option.some.inj ((derivation.contextValue_readout model realization stable beta eta).symm.trans contextRead)

theorem contextValue_derivation_independent
    (first second : Derivation D (.context context)) :
    first.contextValue model realization stable beta eta = second.contextValue model realization stable beta eta :=
  first.contextValue_unique model realization stable beta eta _
    (second.contextValue_readout model realization stable beta eta)

theorem contextValue_equation {other : ContextExpr S n}
    (first : Derivation D (.context context)) (second : Derivation D (.context other))
    (equation : Derivation D (.contextEq context other)) :
    first.contextValue model realization stable beta eta = second.contextValue model realization stable beta eta := by
  have read := (equation.sound model realization stable beta eta).contextEqAt _
    (first.contextValue_readout model realization stable beta eta)
  exact (second.contextValue_unique model realization stable beta eta _ read).symm

theorem typeValue_isSome (derivation : Derivation D (.type context type))
    (Γ : Context C n) (contextRead : model.evaluateContext context = some Γ) :
    (model.evaluateType Γ type).isSome :=
  Option.isSome_iff_exists.mpr
    ((derivation.sound model realization stable beta eta).typeAt Γ contextRead)

noncomputable def typeValue (derivation : Derivation D (.type context type))
    (Γ : Context C n) (contextRead : model.evaluateContext context = some Γ) : C.toCwf.Ty Γ.1 :=
  (model.evaluateType Γ type).get
    (derivation.typeValue_isSome model realization stable beta eta Γ contextRead)

theorem typeValue_readout (derivation : Derivation D (.type context type))
    (Γ : Context C n) (contextRead : model.evaluateContext context = some Γ) :
    model.evaluateType Γ type = some (derivation.typeValue model realization stable beta eta Γ contextRead) :=
  (Option.some_get _).symm

theorem typeValue_unique (derivation : Derivation D (.type context type))
    (Γ : Context C n) (contextRead : model.evaluateContext context = some Γ)
    (A : C.toCwf.Ty Γ.1) (typeRead : model.evaluateType Γ type = some A) :
    derivation.typeValue model realization stable beta eta Γ contextRead = A :=
  Option.some.inj ((derivation.typeValue_readout model realization stable beta eta Γ contextRead).symm.trans typeRead)

theorem typeValue_derivation_independent (first second : Derivation D (.type context type))
    (Γ : Context C n) (contextRead : model.evaluateContext context = some Γ) :
    first.typeValue model realization stable beta eta Γ contextRead =
      second.typeValue model realization stable beta eta Γ contextRead :=
  first.typeValue_unique model realization stable beta eta Γ contextRead _
    (second.typeValue_readout model realization stable beta eta Γ contextRead)

theorem typeValue_equation {other : TypeExpr S n}
    (first : Derivation D (.type context type)) (second : Derivation D (.type context other))
    (equation : Derivation D (.typeEq context type other))
    (Γ : Context C n) (contextRead : model.evaluateContext context = some Γ) :
    first.typeValue model realization stable beta eta Γ contextRead =
      second.typeValue model realization stable beta eta Γ contextRead := by
  have read := (equation.sound model realization stable beta eta).typeEqAt Γ _ contextRead
    (first.typeValue_readout model realization stable beta eta Γ contextRead)
  exact (second.typeValue_unique model realization stable beta eta Γ contextRead _ read).symm

/-- The generated judgment supplies the successful-check proof; the returned
value is read from the authored raw expression evaluator. -/
noncomputable def termSection (derivation : Derivation D (.term context term type))
    (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) : C.toCwf.Tm Γ.1 A :=
  (ModelData.check? (model.evaluateTerm Γ term) A).get
    ((derivation.sound model realization stable beta eta).termChecked_isSome
      Γ A contextRead typeRead)

theorem termSection_checked (derivation : Derivation D (.term context term type))
    (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    ModelData.check? (model.evaluateTerm Γ term) A =
      some (derivation.termSection model realization stable beta eta Γ A contextRead typeRead) :=
  (Option.some_get _).symm

theorem termSection_readout (derivation : Derivation D (.term context term type))
    (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    model.evaluateTerm Γ term = some ⟨A,
      derivation.termSection model realization stable beta eta Γ A contextRead typeRead⟩ :=
  (ModelData.check?_eq_some_iff _ _ _).mp
    (derivation.termSection_checked model realization stable beta eta Γ A contextRead typeRead)

theorem termSection_unique (derivation : Derivation D (.term context term type))
    (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) (value : C.toCwf.Tm Γ.1 A)
    (sectionRead : model.evaluateTerm Γ term = some ⟨A, value⟩) :
    derivation.termSection model realization stable beta eta Γ A contextRead typeRead = value :=
  Option.some.inj
    ((derivation.termSection_checked model realization stable beta eta Γ A contextRead typeRead).symm.trans
      ((ModelData.check?_eq_some_iff _ _ _).mpr sectionRead))

theorem termSection_derivation_independent
    (first second : Derivation D (.term context term type))
    (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    first.termSection model realization stable beta eta Γ A contextRead typeRead =
      second.termSection model realization stable beta eta Γ A contextRead typeRead :=
  first.termSection_unique model realization stable beta eta Γ A contextRead typeRead _
    (second.termSection_readout model realization stable beta eta Γ A contextRead typeRead)

theorem termSection_annotation_independent {otherType : TypeExpr S n}
    (first : Derivation D (.term context term type))
    (second : Derivation D (.term context term otherType))
    (Γ : Context C n) (A B : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A)
    (otherTypeRead : model.evaluateType Γ otherType = some B) :
    A = B ∧ HEq (first.termSection model realization stable beta eta Γ A contextRead typeRead)
      (second.termSection model realization stable beta eta Γ B contextRead otherTypeRead) :=
  ModelData.checked_readout_unique
    (first.termSection_checked model realization stable beta eta Γ A contextRead typeRead)
    (second.termSection_checked model realization stable beta eta Γ B contextRead otherTypeRead)

theorem termSection_equation {other : TermExpr S n}
    (first : Derivation D (.term context term type))
    (second : Derivation D (.term context other type))
    (equation : Derivation D (.termEq context term other type))
    (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    first.termSection model realization stable beta eta Γ A contextRead typeRead =
      second.termSection model realization stable beta eta Γ A contextRead typeRead := by
  rcases (equation.sound model realization stable beta eta).termEqAt
    Γ A contextRead typeRead with ⟨value, firstRead, secondRead⟩
  exact (first.termSection_unique model realization stable beta eta Γ A contextRead typeRead _ firstRead).trans
    (second.termSection_unique model realization stable beta eta Γ A contextRead typeRead _ secondRead).symm

variable {k : Nat} {source : ContextExpr S n} {target : ContextExpr S k}
  {substitution : Substitution S k n}

theorem substitutionArrow_isSome
    (derivation : Derivation D (.substitution source target substitution))
    (Γ : Context C n) (Δ : Context C k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    (model.evaluateSubstitution Γ Δ substitution).isSome :=
  Option.isSome_iff_exists.mpr
    ((derivation.sound model realization stable beta eta).substitutionAt Γ Δ sourceRead targetRead)

noncomputable def substitutionArrow
    (derivation : Derivation D (.substitution source target substitution))
    (Γ : Context C n) (Δ : Context C k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) : C.toCwf.Sub Γ.1 Δ.1 :=
  (model.evaluateSubstitution Γ Δ substitution).get
    (derivation.substitutionArrow_isSome model realization stable beta eta Γ Δ sourceRead targetRead)

theorem substitutionArrow_readout
    (derivation : Derivation D (.substitution source target substitution))
    (Γ : Context C n) (Δ : Context C k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    model.evaluateSubstitution Γ Δ substitution =
      some (derivation.substitutionArrow model realization stable beta eta Γ Δ sourceRead targetRead) :=
  (Option.some_get _).symm

theorem substitutionArrow_unique
    (derivation : Derivation D (.substitution source target substitution))
    (Γ : Context C n) (Δ : Context C k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) (arrow : C.toCwf.Sub Γ.1 Δ.1)
    (arrowRead : model.evaluateSubstitution Γ Δ substitution = some arrow) :
    derivation.substitutionArrow model realization stable beta eta Γ Δ sourceRead targetRead = arrow :=
  Option.some.inj
    ((derivation.substitutionArrow_readout model realization stable beta eta Γ Δ sourceRead targetRead).symm.trans arrowRead)

theorem substitutionArrow_derivation_independent
    (first second : Derivation D (.substitution source target substitution))
    (Γ : Context C n) (Δ : Context C k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    first.substitutionArrow model realization stable beta eta Γ Δ sourceRead targetRead =
      second.substitutionArrow model realization stable beta eta Γ Δ sourceRead targetRead :=
  first.substitutionArrow_unique model realization stable beta eta Γ Δ sourceRead targetRead _
    (second.substitutionArrow_readout model realization stable beta eta Γ Δ sourceRead targetRead)

theorem substitutionArrow_equation {other : Substitution S k n}
    (first : Derivation D (.substitution source target substitution))
    (second : Derivation D (.substitution source target other))
    (equation : Derivation D (.substitutionEq source target substitution other))
    (Γ : Context C n) (Δ : Context C k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    first.substitutionArrow model realization stable beta eta Γ Δ sourceRead targetRead =
      second.substitutionArrow model realization stable beta eta Γ Δ sourceRead targetRead := by
  rcases (equation.sound model realization stable beta eta).substitutionEqAt Γ Δ sourceRead targetRead
    with ⟨arrow, firstRead, secondRead⟩
  exact (first.substitutionArrow_unique model realization stable beta eta Γ Δ sourceRead targetRead _ firstRead).trans
    (second.substitutionArrow_unique model realization stable beta eta Γ Δ sourceRead targetRead _ secondRead).symm

theorem termSection_substitution {body : TermExpr S k} {annotation : TypeExpr S k}
    (original : Derivation D (.term target body annotation))
    (substituted : Derivation D (.term source (body.substitute substitution)
      (annotation.substitute substitution)))
    (Γ : Context C n) (Δ : Context C k) (modelMap : ModelSubstitution model Γ Δ substitution)
    (A : C.toCwf.Ty Δ.1)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ)
    (typeRead : model.evaluateType Δ annotation = some A) :
    substituted.termSection model realization stable beta eta Γ (C.toCwf.tySub A modelMap.arrow)
        sourceRead (model.evaluateType_substitute stable annotation Γ Δ substitution modelMap A typeRead) =
      C.toCwf.tmSub (original.termSection model realization stable beta eta Δ A targetRead typeRead)
        modelMap.arrow :=
  substituted.termSection_unique model realization stable beta eta Γ _ sourceRead
    (model.evaluateType_substitute stable annotation Γ Δ substitution modelMap A typeRead) _
    (model.evaluateTerm_substitute stable body Γ Δ substitution modelMap
      ⟨A, original.termSection model realization stable beta eta Δ A targetRead typeRead⟩
      (original.termSection_readout model realization stable beta eta Δ A targetRead typeRead))

theorem typeValue_substitution {annotation : TypeExpr S k}
    (original : Derivation D (.type target annotation))
    (substituted : Derivation D (.type source (annotation.substitute substitution)))
    (Γ : Context C n) (Δ : Context C k) (modelMap : ModelSubstitution model Γ Δ substitution)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    substituted.typeValue model realization stable beta eta Γ sourceRead =
      C.toCwf.tySub (original.typeValue model realization stable beta eta Δ targetRead) modelMap.arrow :=
  substituted.typeValue_unique model realization stable beta eta Γ sourceRead _
    (model.evaluateType_substitute stable annotation Γ Δ substitution modelMap _
      (original.typeValue_readout model realization stable beta eta Δ targetRead))

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
