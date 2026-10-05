import Mettapedia.Languages.MM0.Presentation.DefinitionAdmissionExecution

/-! # MM0 definition-body execution agrees with independent admission -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitionAdmission

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalDeclaration
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => bodyProgram
local notation "A" => bodyEquations
local notation "H" => dataEqualityHost

private theorem typed_body_computes (checked : Bool) (table : SignatureTable) (context : Context)
    (dependencies : Finset Nat) (expression : Preterm) :
    Applies P H "mm0:body-typed"
      [boolean checked, encodeTable table, encodeContext context, encodeDependencies dependencies, encode expression]
      (boolean (checked && (match Preterm.freeVariables? (signatureOf table) context expression with
        | none => false | some free => decide (free ⊆ dependencies)))) := by
  cases checked with
  | false => exact ⟨1, by rw [body_apply _ (by decide)]; rfl⟩
  | true =>
      refine body_equation (equation := A[12]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
        (body_free_checked table context expression dependencies)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (free_variables_reused table context expression)

theorem body_context_computes (table : SignatureTable) (context : Context) (sort : Nat)
    (dependencies : Finset Nat) (expression : Preterm) :
    Applies P H "mm0:body-context"
      [encodeTable table, encodeContext context, natural sort, encodeDependencies dependencies, encode expression]
      (boolean (decide (Preterm.infer (signatureOf table) context expression = some ([], sort)) &&
        (match Preterm.freeVariables? (signatureOf table) context expression with
        | none => false | some free => decide (free ⊆ dependencies)))) := by
  refine body_equation (equation := A[10]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
    (typed_body_computes _ table context dependencies expression)
  refine Evaluates.call
    (values := [encodeType (Preterm.infer (signatureOf table) context expression), encodeType (some ([], sort))])
    (by simp [Special]) (.cons ?_ (.cons ?_ .nil))
    (.primitive (by rfl) (dataEqualityHost_encoded encodeType encodeType_injective _ _))
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
      (body_infer_computes table context expression)
  · exact Evaluates.call (by simp [Special])
      (.cons (Evaluates.list .nil) (.cons (.variable (by rfl)) .nil)) (.constructor (by rfl) (by rfl))

private theorem dummies_body_computes (checked : Bool) (table : SignatureTable)
    (declaration : TermDecl) (body : Definition.Body) :
    Applies P H "mm0:body-dummies"
      [boolean checked, encodeTable table, encodeContext declaration.arguments, natural declaration.resultSort,
        encodeDependencies declaration.dependencies, encodeNaturals body.dummies, encode body.expression]
      (boolean (checked &&
        (decide (Preterm.infer (signatureOf table) (body.context declaration) body.expression = some ([], declaration.resultSort)) &&
        (match Preterm.freeVariables? (signatureOf table) (body.context declaration) body.expression with
        | none => false | some free => decide (free ⊆ declaration.dependencies))))) := by
  cases checked with
  | false => exact ⟨1, by rw [body_apply _ (by decide)]; rfl⟩
  | true =>
      refine body_equation (equation := A[9]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
        (body_context_computes table (body.context declaration) declaration.resultSort declaration.dependencies body.expression)
      refine Evaluates.call
        (values := [encodeContext declaration.arguments, encodeContext (body.dummies.map Kernel.Binder.bound)])
        (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (dummy_context_computes body.dummies)
      · simpa only [Definition.Body.context, encodeContext, List.map_append] using
          body_append_computes (declaration.arguments.map encodeBinder) ((body.dummies.map Kernel.Binder.bound).map encodeBinder)

theorem body_computes (sorts : SortTable) (table : SignatureTable)
    (declaration : TermDecl) (body : Definition.Body) :
    Applies P H "mm0:form-body" [encodeSorts sorts, encodeTable table, encodeDeclaration declaration, encodeBody body]
      (boolean (Definition.checkBody (sortsOf sorts) (signatureOf table) declaration body)) := by
  rw [Definition.checkBody, Bool.and_assoc]
  refine body_equation (equation := A[7]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))
    (dummies_body_computes _ table declaration body)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (declaration_suffix_reused _ (by decide) _ _ (dummies_computes sorts body.dummies))

theorem body_result_exact (sorts : SortTable) (table : SignatureTable)
    (declaration : TermDecl) (body : Definition.Body) (result : Term) :
    Applies P H "mm0:form-body" [encodeSorts sorts, encodeTable table, encodeDeclaration declaration, encodeBody body] result ↔
      result = boolean (Definition.checkBody (sortsOf sorts) (signatureOf table) declaration body) := by
  constructor
  · exact fun run => run.deterministic (body_computes sorts table declaration body)
  · rintro rfl; exact body_computes sorts table declaration body

theorem body_accepts_iff (sorts : SortTable) (table : SignatureTable)
    (declaration : TermDecl) (body : Definition.Body) :
    Applies P H "mm0:form-body" [encodeSorts sorts, encodeTable table, encodeDeclaration declaration, encodeBody body] (.sym "True") ↔
      Definition.AdmissibleBody (sortsOf sorts) (signatureOf table) declaration body := by
  rw [body_result_exact, ← Definition.checkBody_iff]
  cases Definition.checkBody (sortsOf sorts) (signatureOf table) declaration body <;> simp [boolean]

theorem body_refuses_iff (sorts : SortTable) (table : SignatureTable)
    (declaration : TermDecl) (body : Definition.Body) :
    Applies P H "mm0:form-body" [encodeSorts sorts, encodeTable table, encodeDeclaration declaration, encodeBody body] (.sym "False") ↔
      ¬ Definition.AdmissibleBody (sortsOf sorts) (signatureOf table) declaration body := by
  rw [body_result_exact, ← Definition.checkBody_iff]
  cases Definition.checkBody (sortsOf sorts) (signatureOf table) declaration body <;> simp [boolean]

theorem admitted_body_has_declared_type (sorts : SortTable) (table : SignatureTable)
    (declaration : TermDecl) (body : Definition.Body)
    (accepted : Applies P H "mm0:form-body"
      [encodeSorts sorts, encodeTable table, encodeDeclaration declaration, encodeBody body] (.sym "True")) :
    Preterm.HasType (signatureOf table) (body.context declaration) body.expression [] declaration.resultSort :=
  ((body_accepts_iff sorts table declaration body).mp accepted).typed

theorem admitted_body_has_no_undeclared_free_variables (sorts : SortTable) (table : SignatureTable)
    (declaration : TermDecl) (body : Definition.Body)
    (accepted : Applies P H "mm0:form-body"
      [encodeSorts sorts, encodeTable table, encodeDeclaration declaration, encodeBody body] (.sym "True")) :
    ∃ free, Preterm.FreeVars (signatureOf table) (body.context declaration) body.expression free ∧
      free ⊆ declaration.dependencies :=
  ((body_accepts_iff sorts table declaration body).mp accepted).free

theorem body_completed_result (sorts : SortTable) (table : SignatureTable)
    (declaration : TermDecl) (body : Definition.Body) (fuel : Nat)
    (finished : apply P H fuel "mm0:form-body"
      [encodeSorts sorts, encodeTable table, encodeDeclaration declaration, encodeBody body] ≠ .exhausted) :
    apply P H fuel "mm0:form-body"
      [encodeSorts sorts, encodeTable table, encodeDeclaration declaration, encodeBody body] =
      .value (boolean (Definition.checkBody (sortsOf sorts) (signatureOf table) declaration body)) :=
  (body_computes sorts table declaration body).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitionAdmission
