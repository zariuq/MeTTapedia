import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLDefinitionReductDenotation
import Mettapedia.Logic.HOL.DefinitionExtensionSemantics
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationInsertionCoherence

/-!
# A definition-respecting HOL/native declaration model

An admitted fresh native declaration extends both sides of the existing
HOL representation: the source constant signature gains one typed symbol,
and the native declaration signature gains its checked body. The Henkin
model for the source extension is constructed by closed-term substitution,
so the new symbol denotes its defining body without an extra assumption.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDefinitionModelExtension

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface HOLImpredicativeRepresentation
open NativeHOLSignatureDenotation

universe u v w
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Freshness in the installed rules implies that the prior declaration
inventory does not already own the name. -/
theorem prior_name_absent (signature : LogicalSignature Base Const)
    (name : DeclName) (fresh : signature.rules.constantType name = none) :
    signature.declarations.entries name = none := by
  unfold LogicalSignature.rules extendRules combinedType at fresh
  cases base : Tower.rules.constantType name with
  | some type => simp [base] at fresh
  | none =>
      cases prior : signature.declarations.entries name with
      | none => rfl
      | some entry => simp [base, Signature.typeOf?, prior] at fresh

private theorem tower_name_absent (signature : LogicalSignature Base Const)
    (name : DeclName) (fresh : signature.rules.constantType name = none) :
    Tower.rules.constantType name = none := by
  unfold LogicalSignature.rules extendRules combinedType at fresh
  cases base : Tower.rules.constantType name with
  | none => exact base
  | some type => simp [base] at fresh

private def extendedConstant (signature : LogicalSignature Base Const)
    (name : DeclName) {target : HOL.Ty Base} :
    ∀ {type : HOL.Ty Base}, HOL.DefinedConst Const target type → Tower.Tm 0
  | _, .old symbol => signature.constant symbol
  | _, .defined => .const name

/-- A checked fresh definition induces a law-bearing logical signature.
Old symbols retain their exact native terms; the one new symbol selects the
native declaration name admitted by the existing checker. -/
def extendedSignature (signature : LogicalSignature Base Const)
    (name : DeclName) {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) :
    LogicalSignature Base (HOL.DefinedConst Const type) := by
  let declarations := signature.declarations.insert name
    (HOLDefinitionAdmission.entry signature body)
  have extension : signature.declarations.Extends declarations :=
    Signature.extends_insert_of_absent signature.declarations name
      (HOLDefinitionAdmission.entry signature body)
      (prior_name_absent signature name fresh)
  have freshBase := tower_name_absent signature name fresh
  refine {
    declarations := declarations
    types := signature.types
    proposition_formed := signature.proposition_formed.monoSignature extension
    base_formed := fun b => (signature.base_formed b).monoSignature extension
    constant := extendedConstant signature name
    constant_typed := ?_
    implication := signature.implication
    implication_typed := signature.implication_typed.monoSignature extension
    universal := signature.universal
    universal_typed := fun t => (signature.universal_typed t).monoSignature extension
    equality := signature.equality
    equality_typed := fun t => (signature.equality_typed t).monoSignature extension
  }
  · intro t symbol
    cases symbol with
    | old old =>
        simpa only [extendedConstant] using
          (signature.constant_typed old).monoSignature extension
    | defined =>
        have typed : Typing (extendRules Tower.rules declarations) .nil (.const name)
            (liftClosed (typeAt signature.types 0 type)) := by
          apply Typing.const (type := typeAt signature.types 0 type)
          · apply combinedType_of_signature Tower.rules declarations freshBase
            simp [declarations, HOLDefinitionAdmission.entry]
          · exact (typeAt_formed signature type (.nil : Tower.Ctx 0)).monoSignature extension
          · exact .sort Tower.zero
        simpa only [extendedConstant, TelescopeAbstraction.liftClosed_zero] using typed

@[simp] theorem extendedSignature_old_constant
    (signature : LogicalSignature Base Const) (name : DeclName)
    {target type : HOL.Ty Base} (body : HOL.Term Const [] target)
    (fresh : signature.rules.constantType name = none) (symbol : Const type) :
    (extendedSignature signature name body fresh).constant (HOL.DefinedConst.old symbol) =
      signature.constant symbol := rfl

/-- The existing partial representation is unchanged on every old term,
including the logical operators and their binders. -/
theorem represent_embedded (signature : LogicalSignature Base Const)
    (name : DeclName) {target : HOL.Ty Base} (body : HOL.Term Const [] target)
    (fresh : signature.rules.constantType name = none)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base} (term : HOL.Term Const gamma type) :
    represent (extendedSignature signature name body fresh)
      (HOL.DefinedConst.embed (target := target) term) = represent signature term := by
  induction term <;>
    simp_all [HOL.DefinedConst.embed, HOL.mapConst, represent,
      extendedSignature, extendedConstant]

/-- Total translation of an old term is stable when the fresh definition is
added to both signatures. -/
theorem translate_embedded (signature : LogicalSignature Base Const)
    (name : DeclName) {target : HOL.Ty Base} (body : HOL.Term Const [] target)
    (fresh : signature.rules.constantType name = none)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base} (term : HOL.Term Const gamma type) :
    translate (extendedSignature signature name body fresh)
      (HOL.DefinedConst.embed (target := target) term) = translate signature term := by
  apply Option.some.inj
  rw [← translate_eq, ← translate_eq, HOL.DefinedConst.expand_embed, represent_embedded]

/-- Every old source term keeps its native denotation after the new checked
definition is installed. Because the statement quantifies over the entire
prior signature, it applies equally to names introduced by earlier steps. -/
theorem prior_term_denotes_after_definition
    (signature : LogicalSignature Base Const)
    (M : HOL.HenkinModel.{u, v, w} Base Const) (name : DeclName)
    {target : HOL.Ty Base} (body : HOL.Term Const [] target)
    (fresh : signature.rules.constantType name = none)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (term : HOL.Term Const gamma type) :
    Denotes (extendedSignature signature name body fresh)
      (M.definitionExtension body) (translate signature term)
      (fun valuation => M.denote term valuation) := by
  have meaning := NativeHOLImpredicativeDenotation.translate_denotes
    (extendedSignature signature name body fresh) (M.definitionExtension body)
    (HOL.DefinedConst.embed (target := target) term)
  rw [translate_embedded signature name body fresh term] at meaning
  have sameValue :
      (fun valuation : (M.definitionExtension body).Valuation gamma =>
        (M.definitionExtension body).denote
          (HOL.DefinedConst.embed (target := target) term) valuation) =
      (fun valuation => M.denote term valuation) := by
    funext valuation
    exact M.definitionExtension_embed body term valuation
  exact sameValue ▸ meaning

/-- The new source symbol is represented by the very native name admitted as
the definition. No alternate encoding is introduced by the total translator. -/
theorem translate_defined (signature : LogicalSignature Base Const)
    (name : DeclName) {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) (gamma : HOL.Ctx Base) :
    translate (extendedSignature signature name body fresh)
        (Γ := gamma) (HOL.Term.const (HOL.DefinedConst.defined :
          HOL.DefinedConst Const type type)) =
      (liftClosed (.const name) : Tower.Tm gamma.length) := by
  apply Option.some.inj
  rw [← translate_eq]
  rfl

@[simp] theorem extendedSignature_defined_constant
    (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) :
    (extendedSignature signature name body fresh).constant
      (HOL.DefinedConst.defined : HOL.DefinedConst Const type type) = .const name := by
  rfl

/-- The actual declaration name denotes the source definition body in the
definition-respecting model. This is obtained from the constructed model's
fresh-symbol interpretation, not from a postulated declaration equation. -/
theorem defined_name_denotes (signature : LogicalSignature Base Const)
    (M : HOL.HenkinModel.{u, v, w} Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) (gamma : HOL.Ctx Base) :
    Denotes (extendedSignature signature name body fresh)
      (M.definitionExtension body) (gamma := gamma) (type := type)
      (liftClosed (.const name))
      (fun _ => M.denote body (fun index => nomatch index)) := by
  have meaning := Denotes.constant
    (signature := extendedSignature signature name body fresh)
    (model := M.definitionExtension body) (gamma := gamma)
    (HOL.DefinedConst.defined : HOL.DefinedConst Const type type)
  rw [extendedSignature_defined_constant,
    HOL.HenkinModel.definitionExtension_defined] at meaning
  exact meaning

/-- The extended native rules license the exact δ reduct of the definition. -/
theorem extended_delta (signature : LogicalSignature Base Const)
    (name : DeclName) {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) (gamma : HOL.Ctx Base) :
    Step (extendedSignature signature name body fresh).rules.headEq
      (.const name : Tower.Tm gamma.length)
      (liftClosed (translate signature body))
      (extendedSignature signature name body fresh).rules.computation := by
  apply Step.root
  apply RootStep.delta
  simp [extendedSignature, HOLDefinitionAdmission.entry]

/-- The rules used by checked sequential admission and by the extended
semantic signature are literally equal. The generic fresh-insertion theorem
compares every type lookup and every licensed root reduction. -/
theorem declaration_rules_package_eq
    (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) :
    HOLDefinitionAdmission.rules signature name body =
      (extendedSignature signature name body fresh).rules := by
  change extendRules (extendRules Tower.rules signature.declarations)
      (Signature.ofList [(name, HOLDefinitionAdmission.entry signature body)]) =
    extendRules Tower.rules
      (signature.declarations.insert name (HOLDefinitionAdmission.entry signature body))
  exact extendRules_sequential_eq_insert Tower.rules signature.declarations name
    (HOLDefinitionAdmission.entry signature body) fresh

/-- Both presentations select the same type for every global name. -/
theorem declaration_type_package_agreement
    (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) (candidate : DeclName) :
    (HOLDefinitionAdmission.rules signature name body).constantType candidate =
      (extendedSignature signature name body fresh).rules.constantType candidate := by
  rw [declaration_rules_package_eq signature name body fresh]

/-- Sequential admission and the inserted logical signature license exactly
the same root computations, not merely the same new δ example. This compares
all prior and new declared steps in both directions. -/
theorem declaration_root_package_agreement
    (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none)
    {n : Nat} {left right : Tower.Tm n} :
    (HOLDefinitionAdmission.rules signature name body).computation.step left right ↔
      (extendedSignature signature name body fresh).rules.computation.step left right := by
  rw [declaration_rules_package_eq signature name body fresh]

/-- The actual δ target is denoted in the *same* extended model as the new
native name. This uses exact translation stability and conservative source
semantics, not a second ad-hoc interpretation of the reduct. -/
theorem definition_target_denotes (signature : LogicalSignature Base Const)
    (M : HOL.HenkinModel.{u, v, w} Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) (gamma : HOL.Ctx Base) :
    Denotes (extendedSignature signature name body fresh)
      (M.definitionExtension body) (gamma := gamma) (type := type)
      (liftClosed (translate signature body))
      (fun _ => M.denote body (fun index => nomatch index)) := by
  have meaning := NativeHOLImpredicativeDenotation.translate_closed_denotes
    (extendedSignature signature name body fresh) (M.definitionExtension body)
    (HOL.DefinedConst.embed (target := type) body) gamma
  rw [translate_embedded signature name body fresh body] at meaning
  have value := M.definitionExtension_embed body body
    (fun index => nomatch index)
  have sameValue :
      (fun _ : (M.definitionExtension body).Valuation gamma =>
        (M.definitionExtension body).denote
          (HOL.DefinedConst.embed (target := type) body)
          (fun index => nomatch index)) =
      (fun _ => M.denote body (fun index => nomatch index)) := by
    funext _
    exact value
  exact sameValue ▸ meaning

/-- Checked admission and native δ agree with the same constructed Henkin
value on both ends. This is semantic preservation for one genuinely admitted
closed definition, not a claim about all arbitrary declaration models. -/
theorem admitted_definition_delta_preserves_value
    (signature : LogicalSignature Base Const)
    (M : HOL.HenkinModel.{u, v, w} Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) (gamma : HOL.Ctx Base) :
    DeclarationAdmissionReplay.Admitted signature.rules []
      (HOLDefinitionAdmission.declarations signature name body) ∧
    Step (HOLDefinitionAdmission.rules signature name body).headEq
      (.const name : Tower.Tm gamma.length)
      (liftClosed (translate signature body))
      (HOLDefinitionAdmission.rules signature name body).computation ∧
    Denotes (extendedSignature signature name body fresh)
      (M.definitionExtension body) (gamma := gamma) (type := type)
      (.const name)
      (fun _ => M.denote body (fun index => nomatch index)) ∧
    Denotes (extendedSignature signature name body fresh)
      (M.definitionExtension body) (gamma := gamma) (type := type)
      (liftClosed (translate signature body))
      (fun _ => M.denote body (fun index => nomatch index)) := by
  refine ⟨HOLDefinitionAdmission.admitted signature name body fresh,
    HOLDefinitionAdmission.delta signature name body, ?_,
    definition_target_denotes signature M name body fresh gamma⟩
  simpa only [liftClosed, Presentation.rename] using
    defined_name_denotes signature M name body fresh gamma

/-- Two ordered definitions demonstrate that the successor law retains the
first declaration's source meaning when the second body is allowed to refer
to the first symbol. Both prefix entries are checked by the same admission
judgment; neither one's meaning is inferred from the other's proof. -/
theorem two_definition_prefix_preserves_first
    (signature : LogicalSignature Base Const)
    (M : HOL.HenkinModel.{u, v, w} Base Const)
    (firstName : DeclName) {firstType : HOL.Ty Base}
    (firstBody : HOL.Term Const [] firstType)
    (firstFresh : signature.rules.constantType firstName = none)
    (secondName : DeclName) {secondType : HOL.Ty Base}
    (secondBody : HOL.Term (HOL.DefinedConst Const firstType) [] secondType)
    (secondFresh :
      (extendedSignature signature firstName firstBody firstFresh).rules.constantType
        secondName = none)
    (gamma : HOL.Ctx Base) :
    let firstSignature := extendedSignature signature firstName firstBody firstFresh
    let firstModel := M.definitionExtension firstBody
    let secondSignature := extendedSignature firstSignature secondName secondBody secondFresh
    let secondModel := firstModel.definitionExtension secondBody
    DeclarationAdmissionReplay.Admitted signature.rules []
      (HOLDefinitionAdmission.declarations signature firstName firstBody) ∧
    DeclarationAdmissionReplay.Admitted firstSignature.rules []
      (HOLDefinitionAdmission.declarations firstSignature secondName secondBody) ∧
    Denotes secondSignature secondModel (gamma := gamma) (type := firstType)
      (liftClosed (.const firstName))
      (fun _ => M.denote firstBody (fun index => nomatch index)) ∧
    Denotes secondSignature secondModel (gamma := gamma) (type := secondType)
      (liftClosed (.const secondName))
      (fun _ => firstModel.denote secondBody (fun index => nomatch index)) := by
  dsimp
  let firstSignature := extendedSignature signature firstName firstBody firstFresh
  let firstModel := M.definitionExtension firstBody
  let priorSymbol : HOL.Term (HOL.DefinedConst Const firstType) gamma firstType :=
    .const HOL.DefinedConst.defined
  have retained := prior_term_denotes_after_definition firstSignature firstModel
    secondName secondBody secondFresh priorSymbol
  have code : translate firstSignature priorSymbol =
      (liftClosed (.const firstName) : Tower.Tm gamma.length) := by
    exact translate_defined signature firstName firstBody firstFresh gamma
  rw [code] at retained
  have sameValue :
      (fun valuation : (firstModel.definitionExtension secondBody).Valuation gamma =>
        firstModel.denote priorSymbol valuation) =
      (fun _ => M.denote firstBody (fun index => nomatch index)) := by
    funext valuation
    rfl
  have firstMeaning := sameValue ▸ retained
  refine ⟨HOLDefinitionAdmission.admitted signature firstName firstBody firstFresh,
    HOLDefinitionAdmission.admitted firstSignature secondName secondBody secondFresh,
    firstMeaning, ?_⟩
  exact defined_name_denotes firstSignature firstModel secondName secondBody secondFresh gamma

namespace Controls

/-- A second, genuinely computed definition applies the identity function to
the symbol introduced by the first declaration. -/
def computedFromPrior {target : HOL.Ty Base} :
    HOL.Term (HOL.DefinedConst Const target) [] target :=
  .app (.lam (.var .vz)) (.const HOL.DefinedConst.defined)

theorem computedFromPrior_not_bare_constant {target : HOL.Ty Base} :
    (computedFromPrior (Const := Const) (target := target)) ≠
      HOL.Term.const HOL.DefinedConst.defined := by
  intro same
  cases same

/-- The second declaration's computed body obtains precisely the value of
the first definition, after one source β computation. -/
theorem computed_second_denotes_first_body
    (signature : LogicalSignature Base Const)
    (M : HOL.HenkinModel.{u, v, w} Base Const)
    (firstName secondName : DeclName) {target : HOL.Ty Base}
    (firstBody : HOL.Term Const [] target)
    (firstFresh : signature.rules.constantType firstName = none)
    (secondFresh :
      (extendedSignature signature firstName firstBody firstFresh).rules.constantType
        secondName = none)
    (gamma : HOL.Ctx Base) :
    let firstSignature := extendedSignature signature firstName firstBody firstFresh
    let firstModel := M.definitionExtension firstBody
    let secondBody := computedFromPrior (Const := Const) (target := target)
    Denotes (extendedSignature firstSignature secondName secondBody secondFresh)
      (firstModel.definitionExtension secondBody) (gamma := gamma) (type := target)
      (liftClosed (.const secondName))
      (fun _ => M.denote firstBody (fun index => nomatch index)) := by
  dsimp
  let firstSignature := extendedSignature signature firstName firstBody firstFresh
  let firstModel := M.definitionExtension firstBody
  let secondBody := computedFromPrior (Const := Const) (target := target)
  have meaning := defined_name_denotes firstSignature firstModel secondName secondBody
    secondFresh gamma
  have sameValue :
      (fun _ : (firstModel.definitionExtension secondBody).Valuation gamma =>
        firstModel.denote secondBody (fun index => nomatch index)) =
      (fun _ => M.denote firstBody (fun index => nomatch index)) := by
    funext _
    rfl
  exact sameValue ▸ meaning

end Controls

#print axioms extendedSignature
#print axioms translate_defined
#print axioms prior_term_denotes_after_definition
#print axioms defined_name_denotes
#print axioms extended_delta
#print axioms declaration_rules_package_eq
#print axioms declaration_type_package_agreement
#print axioms declaration_root_package_agreement
#print axioms definition_target_denotes
#print axioms admitted_definition_delta_preserves_value
#print axioms two_definition_prefix_preserves_first
#print axioms Controls.computedFromPrior_not_bare_constant
#print axioms Controls.computed_second_denotes_first_body

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDefinitionModelExtension
