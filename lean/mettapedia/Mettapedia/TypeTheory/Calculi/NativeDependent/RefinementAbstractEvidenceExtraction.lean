import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundness

/-!
# Canonical semantic sections of generated certificates

Successful interpretation of a generated term judgment proves that its actual
authored expression evaluator has a value at the supplied context and type.
The value is obtained from that evaluator. Its readout determines it uniquely,
independently of the supplied derivation and converted annotation proof.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe a c s t m p

variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C}
  {D : Signature S} {n : Nat}

namespace ModelData

set_option backward.isDefEq.respectTransparency false in
theorem checked_readout_unique {Γ : C.toCwf.Ctx}
    {result : Option (Value C.toCwf Γ)}
    {A B : C.toCwf.Ty Γ}
    {first : C.toCwf.Tm Γ A} {second : C.toCwf.Tm Γ B}
    (firstChecked : check? result A = some first) (secondChecked : check? result B = some second) :
    A = B ∧ HEq first second := by
  have values : (⟨A, first⟩ : Value C.toCwf Γ) = ⟨B, second⟩ :=
    Option.some.inj (((check?_eq_some_iff _ _ _).mp firstChecked).symm.trans
      ((check?_eq_some_iff _ _ _).mp secondChecked))
  exact ⟨congrArg Sigma.fst values, ContextualSumComprehension.sigma_second_heq values⟩

end ModelData

namespace Interprets

theorem termChecked_isSome {model : ModelData S C localModel} {context : ContextExpr S n}
    {term : TermExpr S n} {type : TypeExpr S n}
    (interpreted : Interprets model (.term context term type)) (Γ : ModelScope C localModel n)
    (A : C.toCwf.Ty Γ.1) (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    (ModelData.check? (model.evaluateTerm Γ term) A).isSome := by
  rcases interpreted.termAt Γ A contextRead typeRead with ⟨value, sectionRead⟩
  exact Option.isSome_iff_exists.mpr ⟨value,
    (ModelData.check?_eq_some_iff _ _ _).mpr sectionRead⟩

end Interprets

namespace Derivation

variable (model : ModelData S C localModel) (realization : SignatureRealization model D)
  (stable : StrictPiSubstitution localModel.products) (beta : PiBeta localModel.products)
  (eta : PiEta localModel.products stable.1)
  {context : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}

include model realization stable beta eta

theorem contextValue_isSome (derivation : Derivation D (.context context)) :
    (model.evaluateContext context).isSome :=
  Option.isSome_iff_exists.mpr (sound model realization stable beta eta derivation)

noncomputable def contextValue (derivation : Derivation D (.context context)) : ModelScope C localModel n :=
  (model.evaluateContext context).get (contextValue_isSome model realization stable beta eta derivation)

theorem contextValue_readout (derivation : Derivation D (.context context)) :
    model.evaluateContext context = some (contextValue model realization stable beta eta derivation) :=
  (Option.some_get _).symm

theorem contextValue_unique (derivation : Derivation D (.context context))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    contextValue model realization stable beta eta derivation = Γ :=
  Option.some.inj ((contextValue_readout model realization stable beta eta derivation).symm.trans contextRead)

theorem contextValue_derivation_independent
    (first second : Derivation D (.context context)) :
    contextValue model realization stable beta eta first = contextValue model realization stable beta eta second :=
  contextValue_unique model realization stable beta eta first _
    (contextValue_readout model realization stable beta eta second)

theorem contextValue_equation {other : ContextExpr S n}
    (first : Derivation D (.context context)) (second : Derivation D (.context other))
    (equation : Derivation D (.contextEq context other)) :
    contextValue model realization stable beta eta first = contextValue model realization stable beta eta second := by
  have read := (sound model realization stable beta eta equation).contextEqAt _
    (contextValue_readout model realization stable beta eta first)
  exact (contextValue_unique model realization stable beta eta second _ read).symm

theorem typeValue_isSome (derivation : Derivation D (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    (model.evaluateType Γ type).isSome :=
  Option.isSome_iff_exists.mpr
    ((sound model realization stable beta eta derivation).typeAt Γ contextRead)

noncomputable def typeValue (derivation : Derivation D (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) : C.toCwf.Ty Γ.1 :=
  (model.evaluateType Γ type).get
    (typeValue_isSome model realization stable beta eta derivation Γ contextRead)

theorem typeValue_readout (derivation : Derivation D (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    model.evaluateType Γ type = some (typeValue model realization stable beta eta derivation Γ contextRead) :=
  (Option.some_get _).symm

theorem typeValue_unique (derivation : Derivation D (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ)
    (A : C.toCwf.Ty Γ.1) (typeRead : model.evaluateType Γ type = some A) :
    typeValue model realization stable beta eta derivation Γ contextRead = A :=
  Option.some.inj ((typeValue_readout model realization stable beta eta derivation Γ contextRead).symm.trans typeRead)

theorem typeValue_derivation_independent (first second : Derivation D (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    typeValue model realization stable beta eta first Γ contextRead =
      typeValue model realization stable beta eta second Γ contextRead :=
  typeValue_unique model realization stable beta eta first Γ contextRead _
    (typeValue_readout model realization stable beta eta second Γ contextRead)

theorem typeValue_equation {other : TypeExpr S n}
    (first : Derivation D (.type context type)) (second : Derivation D (.type context other))
    (equation : Derivation D (.typeEq context type other))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    typeValue model realization stable beta eta first Γ contextRead =
      typeValue model realization stable beta eta second Γ contextRead := by
  have read := (sound model realization stable beta eta equation).typeEqAt Γ _ contextRead
    (typeValue_readout model realization stable beta eta first Γ contextRead)
  exact (typeValue_unique model realization stable beta eta second Γ contextRead _ read).symm

/-- The generated judgment supplies the successful-check proof; the returned
value is read from the authored raw expression evaluator. -/
noncomputable def termSection (derivation : Derivation D (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) : C.toCwf.Tm Γ.1 A :=
  (ModelData.check? (model.evaluateTerm Γ term) A).get
    ((sound model realization stable beta eta derivation).termChecked_isSome
      Γ A contextRead typeRead)

theorem termSection_checked (derivation : Derivation D (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    ModelData.check? (model.evaluateTerm Γ term) A =
      some (termSection model realization stable beta eta derivation Γ A contextRead typeRead) :=
  (Option.some_get _).symm

theorem termSection_readout (derivation : Derivation D (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    model.evaluateTerm Γ term = some ⟨A,
      termSection model realization stable beta eta derivation Γ A contextRead typeRead⟩ :=
  (ModelData.check?_eq_some_iff _ _ _).mp
    (termSection_checked model realization stable beta eta derivation Γ A contextRead typeRead)

theorem termSection_unique (derivation : Derivation D (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) (value : C.toCwf.Tm Γ.1 A)
    (sectionRead : model.evaluateTerm Γ term = some ⟨A, value⟩) :
    termSection model realization stable beta eta derivation Γ A contextRead typeRead = value :=
  Option.some.inj
    ((termSection_checked model realization stable beta eta derivation Γ A contextRead typeRead).symm.trans
      ((ModelData.check?_eq_some_iff _ _ _).mpr sectionRead))

theorem termSection_derivation_independent
    (first second : Derivation D (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    termSection model realization stable beta eta first Γ A contextRead typeRead =
      termSection model realization stable beta eta second Γ A contextRead typeRead :=
  termSection_unique model realization stable beta eta first Γ A contextRead typeRead _
    (termSection_readout model realization stable beta eta second Γ A contextRead typeRead)

theorem termSection_annotation_independent {otherType : TypeExpr S n}
    (first : Derivation D (.term context term type))
    (second : Derivation D (.term context term otherType))
    (Γ : ModelScope C localModel n) (A B : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A)
    (otherTypeRead : model.evaluateType Γ otherType = some B) :
    A = B ∧ HEq (termSection model realization stable beta eta first Γ A contextRead typeRead)
      (termSection model realization stable beta eta second Γ B contextRead otherTypeRead) :=
  ModelData.checked_readout_unique
    (termSection_checked model realization stable beta eta first Γ A contextRead typeRead)
    (termSection_checked model realization stable beta eta second Γ B contextRead otherTypeRead)

theorem termSection_equation {other : TermExpr S n}
    (first : Derivation D (.term context term type))
    (second : Derivation D (.term context other type))
    (equation : Derivation D (.termEq context term other type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    termSection model realization stable beta eta first Γ A contextRead typeRead =
      termSection model realization stable beta eta second Γ A contextRead typeRead := by
  rcases (sound model realization stable beta eta equation).termEqAt
    Γ A contextRead typeRead with ⟨value, firstRead, secondRead⟩
  exact (termSection_unique model realization stable beta eta first Γ A contextRead typeRead _ firstRead).trans
    (termSection_unique model realization stable beta eta second Γ A contextRead typeRead _ secondRead).symm

variable {predicate : PropExpr S n}

theorem predicateValue_isSome (derivation : Derivation D (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    (model.evaluatePredicate Γ predicate).isSome :=
  Option.isSome_iff_exists.mpr
    ((sound model realization stable beta eta derivation).predicateAt Γ contextRead)

noncomputable def predicateValue (derivation : Derivation D (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) : localModel.doctrine.Predicate Γ.1 :=
  (model.evaluatePredicate Γ predicate).get
    (predicateValue_isSome model realization stable beta eta derivation Γ contextRead)

theorem predicateValue_readout (derivation : Derivation D (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    model.evaluatePredicate Γ predicate =
      some (predicateValue model realization stable beta eta derivation Γ contextRead) :=
  (Option.some_get _).symm

theorem predicateValue_unique (derivation : Derivation D (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ)
    (φ : localModel.doctrine.Predicate Γ.1) (predicateRead : model.evaluatePredicate Γ predicate = some φ) :
    predicateValue model realization stable beta eta derivation Γ contextRead = φ :=
  Option.some.inj
    ((predicateValue_readout model realization stable beta eta derivation Γ contextRead).symm.trans predicateRead)

theorem predicateValue_derivation_independent
    (first second : Derivation D (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    predicateValue model realization stable beta eta first Γ contextRead =
      predicateValue model realization stable beta eta second Γ contextRead :=
  predicateValue_unique model realization stable beta eta first Γ contextRead _
    (predicateValue_readout model realization stable beta eta second Γ contextRead)

theorem predicateValue_equation {other : PropExpr S n}
    (first : Derivation D (.predicate context predicate))
    (second : Derivation D (.predicate context other))
    (equation : Derivation D (.predicateEq context predicate other))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    predicateValue model realization stable beta eta first Γ contextRead =
      predicateValue model realization stable beta eta second Γ contextRead := by
  have read := (sound model realization stable beta eta equation).predicateEqAt Γ _ contextRead
    (predicateValue_readout model realization stable beta eta first Γ contextRead)
  exact (predicateValue_unique model realization stable beta eta second Γ contextRead _ read).symm

theorem predicateValue_entailment (formed : Derivation D (.predicate context predicate))
    (derivation : Derivation D (.entails context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    predicateValue model realization stable beta eta formed Γ contextRead = ⊤ :=
  predicateValue_unique model realization stable beta eta formed Γ contextRead _
    ((sound model realization stable beta eta derivation).entailsAt Γ contextRead)

variable {k : Nat} {source : ContextExpr S n} {target : ContextExpr S k}
  {substitution : Substitution S k n}

theorem substitutionArrow_isSome
    (derivation : Derivation D (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    (model.evaluateSubstitution Γ Δ substitution).isSome :=
  Option.isSome_iff_exists.mpr
    ((sound model realization stable beta eta derivation).substitutionAt Γ Δ sourceRead targetRead)

noncomputable def substitutionArrow
    (derivation : Derivation D (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) : C.toCwf.Sub Γ.1 Δ.1 :=
  (model.evaluateSubstitution Γ Δ substitution).get
    (substitutionArrow_isSome model realization stable beta eta derivation Γ Δ sourceRead targetRead)

theorem substitutionArrow_readout
    (derivation : Derivation D (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    model.evaluateSubstitution Γ Δ substitution =
      some (substitutionArrow model realization stable beta eta derivation Γ Δ sourceRead targetRead) :=
  (Option.some_get _).symm

theorem substitutionArrow_unique
    (derivation : Derivation D (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) (arrow : C.toCwf.Sub Γ.1 Δ.1)
    (arrowRead : model.evaluateSubstitution Γ Δ substitution = some arrow) :
    substitutionArrow model realization stable beta eta derivation Γ Δ sourceRead targetRead = arrow :=
  Option.some.inj
    ((substitutionArrow_readout model realization stable beta eta derivation Γ Δ sourceRead targetRead).symm.trans arrowRead)

theorem substitutionArrow_derivation_independent
    (first second : Derivation D (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    substitutionArrow model realization stable beta eta first Γ Δ sourceRead targetRead =
      substitutionArrow model realization stable beta eta second Γ Δ sourceRead targetRead :=
  substitutionArrow_unique model realization stable beta eta first Γ Δ sourceRead targetRead _
    (substitutionArrow_readout model realization stable beta eta second Γ Δ sourceRead targetRead)

theorem substitutionArrow_equation {other : Substitution S k n}
    (first : Derivation D (.substitution source target substitution))
    (second : Derivation D (.substitution source target other))
    (equation : Derivation D (.substitutionEq source target substitution other))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    substitutionArrow model realization stable beta eta first Γ Δ sourceRead targetRead =
      substitutionArrow model realization stable beta eta second Γ Δ sourceRead targetRead := by
  rcases (sound model realization stable beta eta equation).substitutionEqAt Γ Δ sourceRead targetRead
    with ⟨arrow, firstRead, secondRead⟩
  exact (substitutionArrow_unique model realization stable beta eta first Γ Δ sourceRead targetRead _ firstRead).trans
    (substitutionArrow_unique model realization stable beta eta second Γ Δ sourceRead targetRead _ secondRead).symm

theorem termSection_substitution {body : TermExpr S k} {annotation : TypeExpr S k}
    (original : Derivation D (.term target body annotation))
    (substituted : Derivation D (.term source (body.substitute substitution)
      (annotation.substitute substitution)))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k) (modelMap : ModelSubstitution model Γ Δ substitution)
    (A : C.toCwf.Ty Δ.1)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ)
    (typeRead : model.evaluateType Δ annotation = some A) :
    termSection model realization stable beta eta substituted Γ (C.toCwf.tySub A modelMap.arrow)
        sourceRead (model.evaluateType_substitute stable annotation Γ Δ substitution modelMap A typeRead) =
      C.toCwf.tmSub (termSection model realization stable beta eta original Δ A targetRead typeRead)
        modelMap.arrow :=
  termSection_unique model realization stable beta eta substituted Γ _ sourceRead
    (model.evaluateType_substitute stable annotation Γ Δ substitution modelMap A typeRead) _
    (model.evaluateTerm_substitute stable body Γ Δ substitution modelMap
      ⟨A, termSection model realization stable beta eta original Δ A targetRead typeRead⟩
      (termSection_readout model realization stable beta eta original Δ A targetRead typeRead))

theorem typeValue_substitution {annotation : TypeExpr S k}
    (original : Derivation D (.type target annotation))
    (substituted : Derivation D (.type source (annotation.substitute substitution)))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k) (modelMap : ModelSubstitution model Γ Δ substitution)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    typeValue model realization stable beta eta substituted Γ sourceRead =
      C.toCwf.tySub (typeValue model realization stable beta eta original Δ targetRead) modelMap.arrow :=
  typeValue_unique model realization stable beta eta substituted Γ sourceRead _
    (model.evaluateType_substitute stable annotation Γ Δ substitution modelMap _
      (typeValue_readout model realization stable beta eta original Δ targetRead))

theorem predicateValue_substitution {formula : PropExpr S k}
    (original : Derivation D (.predicate target formula))
    (substituted : Derivation D (.predicate source (formula.substitute substitution)))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k) (modelMap : ModelSubstitution model Γ Δ substitution)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    predicateValue model realization stable beta eta substituted Γ sourceRead =
      localModel.doctrine.reindex modelMap.arrow
        (predicateValue model realization stable beta eta original Δ targetRead) :=
  predicateValue_unique model realization stable beta eta substituted Γ sourceRead _
    (model.evaluatePredicate_substitute stable formula Γ Δ substitution modelMap _
      (predicateValue_readout model realization stable beta eta original Δ targetRead))

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
