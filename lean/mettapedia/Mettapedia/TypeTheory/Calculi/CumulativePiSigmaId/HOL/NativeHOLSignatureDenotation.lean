import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLInterface

/-!
# Signature-generic denotation of represented HOL terms

This module interprets the actual cumulative-tower terms selected by a
`LogicalSignature` in an arbitrary Henkin model of the same HOL signature.
The semantic judgment is defined constructorwise on native variables, the
declared closed operations, native application, and native abstraction.
It does not invoke a proof compiler and it does not decode a native term back
to HOL syntax.

The representation theorem is consequently a commuting-square result: the
independently defined source denotation and native denotation agree on every
successfully represented term.  Renaming and substitution act through the
native operations already supplied by the presentation layer.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLSignatureDenotation

open Presentation Presentation.FormationSensitive
open FormationSensitiveHOLInterface
open Mettapedia.Logic

universe u v w

variable {Base : Type u} {Const : HOL.Ty Base → Type v}
/-- A semantic judgment on actual represented native terms.  The logical
declarations receive their Henkin meanings, while application and abstraction
are the literal meta-level operations of the Henkin carrier. -/
inductive Denotes (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, w} Base Const) :
    {gamma : HOL.Ctx Base} → {type : HOL.Ty Base} →
    Tower.Tm gamma.length →
      (model.Valuation gamma → HOL.Ty.denote model.Carrier type) → Prop where
  | index {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
      (index : HOL.Var gamma type) :
      Denotes signature model (.var (variableIndex index))
        (fun valuation => valuation index)
  | constant {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
      (symbol : Const type) :
      Denotes signature model (gamma := gamma)
        (liftClosed (signature.constant symbol))
        (fun _ => model.constDen symbol)
  | implication {gamma : HOL.Ctx Base} :
      Denotes signature model (gamma := gamma)
        (type := .arr .prop (.arr .prop .prop))
        (liftClosed signature.implication)
        (fun _ p q => ULift.up (p.down → q.down))
  | universal {gamma : HOL.Ctx Base} (type : HOL.Ty Base) :
      Denotes signature model (gamma := gamma)
        (type := .arr (.arr type .prop) .prop)
        (liftClosed (signature.universal type))
        (fun _ predicate =>
          ULift.up (∀ x, model.adm type x → (predicate x).down))
  | equality {gamma : HOL.Ctx Base} (type : HOL.Ty Base) :
      Denotes signature model (gamma := gamma)
        (type := .arr type (.arr type .prop))
        (liftClosed (signature.equality type))
        (fun _ left right => ULift.up (model.Eqv type left right))
  | application {gamma : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {function argument : Tower.Tm gamma.length}
      {functionMeaning : model.Valuation gamma →
        HOL.Ty.denote model.Carrier (.arr domain codomain)}
      {argumentMeaning : model.Valuation gamma →
        HOL.Ty.denote model.Carrier domain} :
      Denotes signature model function functionMeaning →
        Denotes signature model argument argumentMeaning →
        Denotes signature model (.app function argument)
          (fun valuation => functionMeaning valuation (argumentMeaning valuation))
  | abstraction {gamma : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {body : Tower.Tm (gamma.length + 1)}
      {bodyMeaning : model.Valuation (domain :: gamma) →
        HOL.Ty.denote model.Carrier codomain} :
      Denotes signature model (gamma := domain :: gamma) body bodyMeaning →
        Denotes signature model (type := .arr domain codomain) (.lam body)
          (fun valuation x => bodyMeaning (model.extend valuation x))

variable {signature : LogicalSignature Base Const}
  {model : HOL.HenkinModel.{u, v, w} Base Const}

/-- Semantic construction entails formation-sensitive typing in the same
declared signature; no semantic clause admits an undeclared native term. -/
theorem Denotes.typed {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes signature model raw value) :
    Typing signature.rules (context signature.types gamma) raw
      (typeAt signature.types gamma.length type) := by
  induction meaning with
  | index index =>
      simpa only [context_lookup] using
        Typing.var (R := signature.rules) (Γ := context signature.types _)
          (variableIndex index)
  | constant symbol =>
      simpa only [LogicalSignature.rules, liftClosed, typeAt_rename] using
        closed_typed (signature.constant_typed symbol) (context signature.types _)
  | implication =>
      simpa only [LogicalSignature.rules, liftClosed, typeAt_rename] using
        closed_typed signature.implication_typed (context signature.types _)
  | universal type =>
      simpa only [LogicalSignature.rules, liftClosed, typeAt_rename] using
        closed_typed (signature.universal_typed type) (context signature.types _)
  | equality type =>
      simpa only [LogicalSignature.rules, liftClosed, typeAt_rename] using
        closed_typed (signature.equality_typed type) (context signature.types _)
  | application _ _ functionTyped argumentTyped =>
      simpa only [inst0, typeAt_subst] using Typing.appElim functionTyped argumentTyped
  | @abstraction gamma domain codomain body bodyMeaning _ bodyTyped =>
      exact .lamIntro (typeAt_formed signature (.arr domain codomain) _)
        (.sort Tower.zero) bodyTyped

/-- Every constructed native value is the denotation of an intrinsic HOL
term.  This is derived from the native judgment rather than used to define it. -/
theorem Denotes.source_denotation {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes signature model raw value) :
    ∃ term : HOL.Term Const gamma type,
      ∀ valuation, value valuation = model.denote term valuation := by
  induction meaning with
  | index index => exact ⟨.var index, fun _ => rfl⟩
  | constant symbol => exact ⟨.const symbol, fun _ => rfl⟩
  | implication =>
      exact ⟨.lam (.lam (.imp (.var (.vs .vz)) (.var .vz))), fun _ => rfl⟩
  | universal type =>
      exact ⟨.lam (.all (.app (.var (.vs .vz)) (.var .vz))), fun _ => rfl⟩
  | equality type =>
      exact ⟨.lam (.lam (.eq (.var (.vs .vz)) (.var .vz))), fun _ => rfl⟩
  | application _ _ functionInduction argumentInduction =>
      obtain ⟨function, functionMeaning⟩ := functionInduction
      obtain ⟨argument, argumentMeaning⟩ := argumentInduction
      refine ⟨.app function argument, ?_⟩
      intro valuation
      simp only [HOL.HenkinModel.denote, HOL.PreModel.denote,
        functionMeaning valuation, argumentMeaning valuation]
  | abstraction _ bodyInduction =>
      obtain ⟨body, bodyMeaning⟩ := bodyInduction
      refine ⟨.lam body, ?_⟩
      intro valuation
      funext x
      exact bodyMeaning (model.extend valuation x)

/-- Henkin closure makes every interpreted native value admissible whenever
its ambient valuation is admissible. -/
theorem Denotes.admissible {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes signature model raw value)
    {valuation : model.Valuation gamma}
    (admissible : model.ValuationAdmissible valuation) :
    model.adm type (value valuation) := by
  obtain ⟨term, equation⟩ := meaning.source_denotation
  rw [equation valuation]
  exact model.denote_admissible admissible term

/-- Actual native renaming precomposes the interpretation with the matching
source valuation map. -/
theorem Denotes.rename {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes signature model raw value) {delta : HOL.Ctx Base}
    (rho : HOL.Rename Base gamma delta) (rawRenaming : Ren gamma.length delta.length)
    (compatible : ∀ {a} (index : HOL.Var gamma a),
      variableIndex (rho index) = rawRenaming (variableIndex index)) :
    Denotes signature model (Presentation.rename rawRenaming raw)
      (fun valuation => value (HOL.Soundness.renameVal model rho valuation)) := by
  induction meaning generalizing delta with
  | index index =>
      simpa only [Presentation.rename, ← compatible index,
        HOL.Soundness.renameVal] using
        (Denotes.index (signature := signature) (model := model) (rho index))
  | constant symbol =>
      simpa only [Presentation.rename, rename_liftClosed] using
        (Denotes.constant (signature := signature) (model := model)
          (gamma := delta) symbol)
  | implication =>
      simpa only [Presentation.rename, rename_liftClosed] using
        (Denotes.implication (signature := signature) (model := model)
          (gamma := delta))
  | universal type =>
      simpa only [Presentation.rename, rename_liftClosed] using
        (Denotes.universal (signature := signature) (model := model)
          (gamma := delta) type)
  | equality type =>
      simpa only [Presentation.rename, rename_liftClosed] using
        (Denotes.equality (signature := signature) (model := model)
          (gamma := delta) type)
  | application _ _ functionInduction argumentInduction =>
      exact .application (functionInduction rho rawRenaming compatible)
        (argumentInduction rho rawRenaming compatible)
  | @abstraction gamma domain codomain body bodyMeaning _ inductionHypothesis =>
      have lifted : ∀ {a} (index : HOL.Var (domain :: gamma) a),
          variableIndex (HOL.Rename.lift rho index) =
            liftRen rawRenaming (variableIndex index) := by
        intro a index
        cases index with
        | vz => rfl
        | vs prior => exact congrArg Fin.succ (compatible prior)
      have interpreted := Denotes.abstraction
        (inductionHypothesis (HOL.Rename.lift rho) (liftRen rawRenaming) lifted)
      simpa only [Presentation.rename, HOL.Soundness.renameVal_lift] using interpreted

/-- Extend a semantic environment substitution while retaining the newest
bound object. -/
def liftEnvironment {gamma delta : HOL.Ctx Base} {type : HOL.Ty Base}
    (environment : model.Valuation delta → model.Valuation gamma)
    (valuation : model.Valuation (type :: delta)) :
    model.Valuation (type :: gamma) :=
  model.extend
    (environment (HOL.Soundness.renameVal model HOL.Rename.weaken valuation))
    (valuation .vz)

theorem liftEnvironment_extend {gamma delta : HOL.Ctx Base} {type : HOL.Ty Base}
    (environment : model.Valuation delta → model.Valuation gamma)
    (valuation : model.Valuation delta) (x : HOL.Ty.denote model.Carrier type) :
    (liftEnvironment environment (model.extend valuation x) :
      model.Valuation (type :: gamma)) =
      (model.extend (environment valuation) x : model.Valuation (type :: gamma)) := by
  simp only [liftEnvironment, HOL.Soundness.renameVal_weaken_extend,
    HOL.HenkinModel.extend, HOL.PreModel.extend]

/-- Native simultaneous substitution is semantic environment substitution. -/
theorem Denotes.substitute {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes signature model raw value) {delta : HOL.Ctx Base}
    (sigma : Sub Tower.Head gamma.length delta.length)
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {a} (index : HOL.Var gamma a),
      Denotes signature model (sigma (variableIndex index))
        (fun valuation => environment valuation index)) :
    Denotes signature model (Presentation.subst sigma raw)
      (fun valuation => value (environment valuation)) := by
  induction meaning generalizing delta with
  | index index => exact components index
  | constant symbol =>
      simpa only [Presentation.subst, subst_liftClosed] using
        (Denotes.constant (signature := signature) (model := model)
          (gamma := delta) symbol)
  | implication =>
      simpa only [Presentation.subst, subst_liftClosed] using
        (Denotes.implication (signature := signature) (model := model)
          (gamma := delta))
  | universal type =>
      simpa only [Presentation.subst, subst_liftClosed] using
        (Denotes.universal (signature := signature) (model := model)
          (gamma := delta) type)
  | equality type =>
      simpa only [Presentation.subst, subst_liftClosed] using
        (Denotes.equality (signature := signature) (model := model)
          (gamma := delta) type)
  | application _ _ functionInduction argumentInduction =>
      exact .application
        (functionInduction sigma environment components)
        (argumentInduction sigma environment components)
  | @abstraction gamma domain codomain body bodyMeaning _ inductionHypothesis =>
      have liftedComponents : ∀ {a} (index : HOL.Var (domain :: gamma) a),
          Denotes signature model (gamma := domain :: delta)
            (liftSub sigma (variableIndex index))
            (fun valuation => liftEnvironment environment valuation index) := by
        intro a index
        cases index with
        | vz => exact .index .vz
        | vs prior =>
            simpa only [variableIndex, liftSub, Fin.cases_succ, liftEnvironment,
              HOL.HenkinModel.extend, HOL.PreModel.extend] using
              (components prior).rename HOL.Rename.weaken wk (fun _ => rfl)
      have interpreted := Denotes.abstraction
        (inductionHypothesis (delta := domain :: delta) (liftSub sigma)
          (liftEnvironment environment) liftedComponents)
      simpa only [Presentation.subst, liftEnvironment_extend] using interpreted

private theorem application_result {n : Nat} {function argument : Option (Tower.Tm n)}
    {result : Tower.Tm n} :
    (do let f ← function; let a ← argument; pure (.app f a)) = some result ↔
      ∃ f a, function = some f ∧ argument = some a ∧ result = .app f a := by
  cases function <;> cases argument <;> simp [eq_comm]

/-- Representation and native denotation commute for every supported source
term, with no declaration-name or datatype-specific cases. -/
theorem representation_square {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (term : HOL.Term Const gamma type) {raw : Tower.Tm gamma.length}
    (represented : represent signature term = some raw) :
    Denotes signature model raw (fun valuation => model.denote term valuation) := by
  induction term with
  | var index =>
      cases Option.some.inj represented
      exact .index index
  | const symbol =>
      cases Option.some.inj represented
      exact Denotes.constant (signature := signature) (model := model)
        symbol
  | app function argument functionInduction argumentInduction =>
      obtain ⟨f, a, hf, ha, rfl⟩ := application_result.mp represented
      exact .application (functionInduction hf) (argumentInduction ha)
  | lam body inductionHypothesis =>
      obtain ⟨bodyCode, bodyRepresented, rfl⟩ := Option.map_eq_some_iff.mp represented
      exact .abstraction (inductionHypothesis bodyRepresented)
  | imp premise conclusion premiseInduction conclusionInduction =>
      obtain ⟨function, conclusionCode, functionRepresented, conclusionRepresented, rfl⟩ :=
        application_result.mp represented
      obtain ⟨head, premiseCode, headRepresented, premiseRepresented, rfl⟩ :=
        application_result.mp functionRepresented
      cases Option.some.inj headRepresented
      exact Denotes.application (domain := .prop) (codomain := .prop)
        (Denotes.application (domain := .prop)
          (codomain := .arr .prop .prop)
          (Denotes.implication (signature := signature) (model := model)
            )
          (premiseInduction premiseRepresented))
        (conclusionInduction conclusionRepresented)
  | @all type gamma body inductionHypothesis =>
      obtain ⟨head, argument, headRepresented, argumentRepresented, rfl⟩ :=
        application_result.mp represented
      cases Option.some.inj headRepresented
      obtain ⟨bodyCode, bodyRepresented, rfl⟩ :=
        Option.map_eq_some_iff.mp argumentRepresented
      exact Denotes.application (domain := .arr type .prop) (codomain := .prop)
        (Denotes.universal (signature := signature) (model := model)
          type)
        (.abstraction (inductionHypothesis bodyRepresented))
  | @eq gamma type left right leftInduction rightInduction =>
      obtain ⟨function, rightCode, functionRepresented, rightRepresented, rfl⟩ :=
        application_result.mp represented
      obtain ⟨head, leftCode, headRepresented, leftRepresented, rfl⟩ :=
        application_result.mp functionRepresented
      cases Option.some.inj headRepresented
      exact Denotes.application (domain := type) (codomain := .prop)
        (Denotes.application (domain := type) (codomain := .arr type .prop)
          (Denotes.equality (signature := signature) (model := model)
            type)
          (leftInduction leftRepresented))
        (rightInduction rightRepresented)
  | top | bot | and | or | not | ex => cases represented

/-- The same square commutes after a represented source substitution and the
matching actual native substitution. -/
theorem representation_substitution_square {gamma delta : HOL.Ctx Base}
    {type : HOL.Ty Base} (term : HOL.Term Const gamma type)
    {raw : Tower.Tm gamma.length} (represented : represent signature term = some raw)
    (sourceSubstitution : HOL.Subst Const gamma delta)
    (nativeSubstitution : Sub Tower.Head gamma.length delta.length)
    (compatible : ∀ {a} (index : HOL.Var gamma a),
      represent signature (sourceSubstitution index) =
        some (nativeSubstitution (variableIndex index))) :
    Denotes signature model (Presentation.subst nativeSubstitution raw)
      (fun valuation =>
        model.denote term (HOL.Soundness.substVal model sourceSubstitution valuation)) := by
  exact (representation_square term represented).substitute nativeSubstitution
    (HOL.Soundness.substVal model sourceSubstitution)
    (fun index => representation_square (sourceSubstitution index) (compatible index))

#print axioms Denotes.typed
#print axioms Denotes.source_denotation
#print axioms Denotes.admissible
#print axioms Denotes.rename
#print axioms Denotes.substitute
#print axioms representation_square
#print axioms representation_substitution_square

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLSignatureDenotation
