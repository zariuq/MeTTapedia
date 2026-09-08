import Mettapedia.Languages.Megalodon.HenkinDeltaSemantics
import Mettapedia.Languages.Megalodon.HenkinDeltaTyping

/-!
# A native definition environment and its satisfying Henkin models

The mixed plain/prefix environment of `DeltaTypingExamples` declares the identity
function, a proposition `q := id p`, a proposition parameter `p`, and an unrelated
prefix-polymorphic identity. Its checked native bodies are identified by exact
erasure, independently of their model meanings.

The models below interpret `id` by the identity function and independently choose
the denotations of `p` and `q`. Assigning them the same proposition satisfies every
eligible definition equation. Assigning `p` true and `q` false preserves all native
typing checks but refutes the definition equations and unfolding preservation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeDefinitionModel

open MathdataKernel
open Mettapedia.Logic.HOL
open HenkinTermInterpretation
open HenkinTermInterpretation.DeltaTypingExamples

abbrev NativeConstant := Constant environment

def identityConstant : NativeConstant (.prop ⇒ .prop) :=
  .named "id" identityDeclaration (by decide) rfl

def propositionConstant : NativeConstant .prop :=
  .named "q" propositionDeclaration (by decide) rfl

def parameterConstant : NativeConstant .prop :=
  .named "p" parameterDeclaration (by decide) rfl

def identityBody : ClosedTerm NativeConstant (.prop ⇒ .prop) := .lam (.var .vz)

def propositionBody : ClosedFormula NativeConstant :=
  .app (.const identityConstant) (.const parameterConstant)

/-- Exact erasure of a variable at the innermost binder determines that variable. -/
private theorem eq_var_of_erase_zero {context : Ctx Base} {type : Ty Base}
    (term : Term NativeConstant (type :: context) type)
    (erased : erase term = some (.db 0)) : term = .var .vz := by
  cases term with
  | var index =>
      cases index with
      | vz => rfl
      | vs index => simp [erase, variableIndex] at erased
  | const constant => cases constant <;> simp [erase, Constant.erase] at erased
  | _ => simp [erase, Option.bind_eq_some_iff] at erased

/-- Names and their lookup provenance survive intrinsic interpretation. -/
private theorem eq_const_of_erase_named {context : Ctx Base} {type : Ty Base}
    (name : Name) (declaration : TermDecl)
    (lookup : environment.lookupTerm? name = some declaration)
    (typed : declaration.type = reifyType type)
    (term : Term NativeConstant context type) (erased : erase term = some (.named name)) :
    term = .const (.named name declaration lookup typed) := by
  cases term with
  | const constant =>
      cases constant with
      | primitive index lookup => simp [erase, Constant.erase] at erased
      | named other otherDeclaration otherLookup otherTyped =>
          simp only [erase, Constant.erase, Option.some.injEq, Tm.named.injEq] at erased
          subst other
          have same : otherDeclaration = declaration := Option.some.inj (otherLookup.symm.trans lookup)
          subst otherDeclaration
          rfl
  | _ => simp [erase, Option.bind_eq_some_iff] at erased

/-- The chosen checked interpretation is forced by the actual native lambda body. -/
private theorem eq_identity_of_erase (term : ClosedTerm NativeConstant (.prop ⇒ .prop))
    (erased : erase term = some (.lam .prop (.db 0))) : term = identityBody := by
  cases term with
  | var index => nomatch index
  | const constant => cases constant <;> simp [erase, Constant.erase] at erased
  | lam body =>
      have inner : erase body = some (.db 0) := by
        simpa [erase, reifyType, Option.bind_eq_some_iff] using erased
      rw [eq_var_of_erase_zero body inner]
      rfl
  | app function argument => simp [erase, Option.bind_eq_some_iff] at erased

/-- The intermediate application type is recovered from the actual `id` lookup,
not guessed from the final proposition type. -/
private theorem eq_proposition_of_erase (term : ClosedFormula NativeConstant)
    (erased : erase term = some (.app (.named "id") (.named "p"))) :
    term = propositionBody := by
  cases term with
  | var index => nomatch index
  | const constant => cases constant <;> simp [erase, Constant.erase] at erased
  | app function argument =>
      obtain ⟨rawFunction, functionErased, rawArgument, argumentErased, shape⟩ :=
        (by simpa [erase, Option.bind_eq_some_iff] using erased :
          ∃ f, erase function = some f ∧ ∃ a, erase argument = some a ∧
            f = .named "id" ∧ a = .named "p")
      rcases shape with ⟨rfl, rfl⟩
      have inferred := infer_of_erase function functionErased (depth := 0) (by trivial)
      simp only [inferTerm, environment, Environment.lookupTerm?, lookupTermList?,
        identityDeclaration] at inferred
      have domain : _ = (Ty.prop : Ty Base) :=
        reifyType_injective (Tp.arr.inj (Option.some.inj inferred)).1.symm
      subst domain
      rw [eq_const_of_erase_named "id" identityDeclaration (by decide) rfl function functionErased,
        eq_const_of_erase_named "p" parameterDeclaration (by decide) rfl argument argumentErased]
      rfl
  | _ => simp [erase, Option.bind_eq_some_iff] at erased

theorem checked_identity_body :
    checkedDefinitions.interpretBody "id" identityDeclaration (by decide) rfl
      (.lam .prop (.db 0)) rfl = identityBody :=
  eq_identity_of_erase _ (checkedDefinitions.erase_interpretBody _ _ _ _ _ _)

theorem checked_proposition_body :
    checkedDefinitions.interpretBody "q" propositionDeclaration (by decide) rfl
      (.app (.named "id") (.named "p")) rfl = propositionBody :=
  eq_proposition_of_erase _ (checkedDefinitions.erase_interpretBody _ _ _ _ _ _)

def carrier : Base → Type 1 := fun _ => ULift.{1} Unit

/-- Interpret the actual native constants. The two proposition meanings are
independent parameters; no definition equation is built into this assignment. -/
def constantDenotation (parameter proposition : Prop) {type : Ty Base}
    (constant : NativeConstant type) : Ty.denote.{0, 0} carrier type := by
  cases constant with
  | primitive index lookup => simp [environment] at lookup
  | named name declaration lookup typed =>
      simp only [environment, Environment.lookupTerm?, lookupTermList?, identityDeclaration,
        propositionDeclaration, parameterDeclaration, prefixDeclaration] at lookup
      split at lookup
      · cases lookup
        have typeEq : type = (.prop ⇒ .prop) := reifyType_injective typed.symm
        subst type
        exact fun value => value
      · split at lookup
        · cases lookup
          have typeEq : type = .prop := reifyType_injective typed.symm
          subst type
          exact .up proposition
        · split at lookup
          · cases lookup
            have typeEq : type = .prop := reifyType_injective typed.symm
            subst type
            exact .up parameter
          · split at lookup
            · cases lookup
              cases type with
              | prop | arr => cases typed
              | base index => cases index <;> cases typed
            · cases lookup

def model (parameter proposition : Prop) : HenkinModel.{0, 0, 0} Base NativeConstant :=
  HenkinModel.standard carrier (constantDenotation parameter proposition)

@[simp] theorem denote_identityConstant (parameter proposition : Prop) :
    (model parameter proposition).constDen identityConstant = fun value => value := rfl

@[simp] theorem denote_propositionConstant (parameter proposition : Prop) :
    (model parameter proposition).constDen propositionConstant = ULift.up proposition := rfl

@[simp] theorem denote_parameterConstant (parameter proposition : Prop) :
    (model parameter proposition).constDen parameterConstant = ULift.up parameter := rfl

@[simp] theorem denote_identityBody (parameter proposition : Prop)
    (valuation : (model parameter proposition).Valuation []) :
    (model parameter proposition).denote identityBody valuation = fun value => value := rfl

@[simp] theorem denote_propositionBody (parameter proposition : Prop)
    (valuation : (model parameter proposition).Valuation []) :
    (model parameter proposition).denote propositionBody valuation = ULift.up parameter := rfl

/-- Equal parameter and defined-proposition meanings satisfy the two actual
native definitions; the unrelated prefix declaration remains in the environment. -/
theorem definitionEquations (parameter : Prop) :
    DefinitionEquations checkedDefinitions (model parameter parameter) where
  equation := by
    intro type name declaration lookup typed body defined
    simp only [environment, Environment.lookupTerm?, lookupTermList?, identityDeclaration,
      propositionDeclaration, parameterDeclaration, prefixDeclaration] at lookup
    split at lookup
    · rename_i nameIsId
      have nameEq : name = "id" := (beq_iff_eq.mp nameIsId).symm
      subst name
      cases lookup
      cases defined
      have typeEq : type = (.prop ⇒ .prop) := reifyType_injective typed.symm
      subst type
      rw [checked_identity_body]
      rfl
    · split at lookup
      · rename_i nameIsQ
        have nameEq : name = "q" := (beq_iff_eq.mp nameIsQ).symm
        subst name
        cases lookup
        cases defined
        have typeEq : type = .prop := reifyType_injective typed.symm
        subst type
        rw [checked_proposition_body]
        rfl
      · split at lookup
        · cases lookup
          cases defined
        · split at lookup
          · cases lookup
            cases type with
            | prop | arr => cases typed
            | base index => cases index <;> cases typed
          · cases lookup

/-- These actual native definitions constrain exactly the chosen meaning of
`q`: it must agree with `p`. The parameter itself remains arbitrary. -/
theorem definitionEquations_iff (parameter proposition : Prop) :
    DefinitionEquations checkedDefinitions (model parameter proposition) ↔
      (proposition ↔ parameter) := by
  constructor
  · intro equations
    have equation := equations.equation (type := .prop) "q" propositionDeclaration
      (by decide) rfl (.app (.named "id") (.named "p")) rfl
    rw [checked_proposition_body] at equation
    exact (congrArg ULift.down equation).to_iff
  · intro meanings
    have same := propext meanings
    subst proposition
    exact definitionEquations parameter

def sourceTerm : ClosedTerm NativeConstant (.base (.inl 0) ⇒ .prop) :=
  .lam (.const propositionConstant)

def resultTerm : ClosedTerm NativeConstant (.base (.inl 0) ⇒ .prop) :=
  .lam (.app (weaken identityBody) (.const parameterConstant))

theorem erase_sourceTerm : erase sourceTerm = some source := rfl

theorem erase_resultTerm : erase resultTerm = some result := rfl

/-- The intrinsic operation unfolds the same two definitions as native delta
normalization, retaining the resulting beta redex underneath the outer binder. -/
theorem interpreted_two_definitions :
    deltaInterpretation checkedDefinitions 2 sourceTerm = some resultTerm := by
  have identityExpansion : deltaConstants checkedDefinitions 1 identityConstant =
      some identityBody := by
    change substConst? (deltaConstants checkedDefinitions 0)
      (checkedDefinitions.interpretBody "id" identityDeclaration (by decide) rfl
        (.lam .prop (.db 0)) rfl) = _
    rw [checked_identity_body]
    rfl
  have propositionExpansion : deltaConstants checkedDefinitions 2 propositionConstant =
      some (.app identityBody (.const parameterConstant)) := by
    change substConst? (deltaConstants checkedDefinitions 1)
      (checkedDefinitions.interpretBody "q" propositionDeclaration (by decide) rfl
        (.app (.named "id") (.named "p")) rfl) = _
    rw [checked_proposition_body]
    simp only [propositionBody, substConst?, identityExpansion]
    rfl
  simp only [deltaInterpretation, sourceTerm, substConst?, propositionExpansion]
  rfl

/-- The generic same-model theorem applies to a checked native computation,
not merely to a separately chosen HOL replacement table. -/
theorem native_unfolding_preserves_meaning (parameter : Prop) :
    deltaNormalize environment 2 source = some result ∧
      (model parameter parameter).denote resultTerm (fun v => nomatch v) =
        (model parameter parameter).denote sourceTerm (fun v => nomatch v) := by
  refine ⟨two_definition_depth, ?_⟩
  exact denote_deltaInterpretation checkedDefinitions (model parameter parameter)
    (definitionEquations parameter) 2 sourceTerm resultTerm interpreted_two_definitions
      (fun v => nomatch v)

/-- Altering only the meaning of `q` violates its equation, despite unchanged
native body checks and unchanged source typing. -/
theorem altered_meaning_refutes_equations :
    ¬ DefinitionEquations checkedDefinitions (model True False) := by
  intro equations
  have equation := equations.equation (type := .prop) "q" propositionDeclaration (by decide) rfl
    (.app (.named "id") (.named "p")) rfl
  rw [checked_proposition_body] at equation
  have false_eq_true : False = True := congrArg ULift.down equation
  exact false_eq_true.mpr trivial

/-- The successful native expansion changes meaning in the altered model.
Well-typedness therefore cannot replace the model's declaration equations. -/
theorem altered_meaning_breaks_preservation :
    (model True False).denote resultTerm (fun v => nomatch v) ≠
      (model True False).denote sourceTerm (fun v => nomatch v) := by
  intro equal
  have true_eq_false : True = False :=
    congrArg (fun function => (function (ULift.up ())).down) equal
  exact true_eq_false.mp trivial

theorem typing_does_not_imply_definition_equations :
    CheckedPlainDefinitions environment ∧
      inferTerm environment 1 [] source = some (.arr (.var 0) .prop) ∧
      ¬ DefinitionEquations checkedDefinitions (model True False) :=
  ⟨checkedDefinitions, source_inferred, altered_meaning_refutes_equations⟩

#print axioms checked_identity_body
#print axioms checked_proposition_body
#print axioms definitionEquations
#print axioms definitionEquations_iff
#print axioms interpreted_two_definitions
#print axioms native_unfolding_preserves_meaning
#print axioms altered_meaning_refutes_equations
#print axioms altered_meaning_breaks_preservation

end Mettapedia.Languages.Megalodon.NativeDefinitionModel
