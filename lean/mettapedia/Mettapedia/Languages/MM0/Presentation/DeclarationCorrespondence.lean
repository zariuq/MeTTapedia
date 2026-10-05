import Mettapedia.Languages.MM0.Presentation.ContextFormation

/-!
# Exact authored MM0 declaration payload validation

The independent declaration predicates remain the reference. Successful
payload formation is separate from proving and publishing a theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalProof
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => declarationProgram
local notation "A" => declarationEquations
local notation "H" => dataEqualityHost

private theorem term_result_computes (checked : Bool) (context : Context) (dependencies : Finset Nat) :
    Applies P H "mm0:form-term-result" [boolean checked, encodeContext context, encodeDependencies dependencies]
      (boolean (checked && decide (∀ index ∈ dependencies, Context.isBound context index = true))) := by
  cases checked with
  | false => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | true =>
      refine declaration_equation (equation := A[34]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (bound_dependencies_computes context dependencies)

private theorem term_context_computes (checked : Bool) (sorts : SortTable) (declaration : TermDecl) :
    Applies P H "mm0:form-term-context"
      [boolean checked, encodeSorts sorts, encodeContext declaration.arguments,
        natural declaration.resultSort, encodeDependencies declaration.dependencies]
      (boolean (checked && ((sortsOf sorts declaration.resultSort).any SortUse.result.allows &&
        decide (∀ index ∈ declaration.dependencies, Context.isBound declaration.arguments index = true)))) := by
  cases checked with
  | false => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | true =>
      refine declaration_equation (equation := A[32]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (term_result_computes _ declaration.arguments declaration.dependencies)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.symbol _ _ _ _) .nil)))
        (sort_computes sorts declaration.resultSort .result)

theorem term_computes (sorts : SortTable) (declaration : TermDecl) :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration declaration]
      (boolean (TermDecl.check (sortsOf sorts) declaration)) := by
  have run : Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration declaration]
      (boolean (Context.check (sortsOf sorts) declaration.arguments &&
        ((sortsOf sorts declaration.resultSort).any SortUse.result.allows &&
          decide (∀ index ∈ declaration.dependencies, Context.isBound declaration.arguments index = true)))) := by
    refine declaration_equation (equation := A[30]) (by decide) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
      (term_context_computes _ sorts declaration)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
      (context_computes sorts declaration.arguments)
  cases known : sortsOf sorts declaration.resultSort <;>
    simpa [TermDecl.check, known, SortUse.allows, Bool.and_assoc] using run

theorem dummy_sort_computes (sorts : SortTable) (sort : Nat) :
    Applies P H "mm0:form-sort" [encodeSorts sorts, natural sort, .sym "Dummy"]
      (boolean (Definition.dummySortAllowed (sortsOf sorts) sort)) := by
  have run := sort_computes sorts sort .dummy
  cases known : sortsOf sorts sort <;>
    simpa [Definition.dummySortAllowed, known, SortUse.name, SortUse.allows] using run

private theorem dummies_next_computes (checked : Bool) (sorts : SortTable) (rest : List Nat)
    (tail : Applies P H "mm0:form-dummies" [encodeSorts sorts, encodeNaturals rest]
      (boolean (Definition.checkDummySorts (sortsOf sorts) rest))) :
    Applies P H "mm0:form-dummies-next" [boolean checked, encodeSorts sorts, encodeNaturals rest]
      (boolean (checked && Definition.checkDummySorts (sortsOf sorts) rest)) := by
  cases checked with
  | false => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | true =>
      refine declaration_equation (equation := A[39]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) tail

theorem dummies_computes (sorts : SortTable) (dummies : List Nat) :
    Applies P H "mm0:form-dummies" [encodeSorts sorts, encodeNaturals dummies]
      (boolean (Definition.checkDummySorts (sortsOf sorts) dummies)) := by
  induction dummies with
  | nil => exact ⟨3, by rw [declaration_apply _ (by decide)]; rfl⟩
  | cons first rest ih =>
      refine declaration_equation (equation := A[35]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [listView ((first :: rest).map natural), encodeSorts sorts])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_computes _)
      · refine declaration_equation (equation := A[37]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call (by simp [Special])
          (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
          (dummies_next_computes _ sorts rest ih)
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.symbol _ _ _ _) .nil)))
          (dummy_sort_computes sorts first)

private theorem statement_saturated_computes (sorts : SortTable) (remaining : Context) (sort : Nat) :
    Applies P H "mm0:form-statement-saturated"
      [listView (remaining.map encodeBinder), encodeSorts sorts, natural sort]
      (boolean (match remaining with | [] => (sortsOf sorts sort).any SortInfo.provable | _ => false)) := by
  cases remaining with
  | cons binder rest => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | nil =>
      refine declaration_equation (equation := A[43]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.symbol _ _ _ _) .nil)))
        (sort_computes sorts sort .statement)

private theorem statement_type_computes (sorts : SortTable) (type : Option ExpressionType) :
    Applies P H "mm0:form-statement-type" [encodeType type, encodeSorts sorts]
      (boolean (match type with | some ([], sort) => (sortsOf sorts sort).any SortInfo.provable | _ => false)) := by
  cases type with
  | none => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | some type =>
      obtain ⟨remaining, sort⟩ := type
      have run : Applies P H "mm0:form-statement-type"
          [encodeType (some (remaining, sort)), encodeSorts sorts]
          (boolean (match remaining with | [] => (sortsOf sorts sort).any SortInfo.provable | _ => false)) := by
        refine declaration_equation (equation := A[42]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call (by simp [Special])
          (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
          (statement_saturated_computes sorts remaining sort)
        exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_computes _)
      cases remaining <;> exact run

theorem statement_computes (sorts : SortTable) (table : SignatureTable) (context : Context) (expression : Preterm) :
    Applies P H "mm0:form-statement" [encodeSorts sorts, encodeTable table, encodeContext context, encode expression]
      (boolean (Preterm.checkStatement (sortsOf sorts) (signatureOf table) context expression)) := by
  refine declaration_equation (equation := A[40]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (statement_type_computes sorts (Preterm.infer (signatureOf table) context expression))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (typing_reused _ (by decide) _ _ (infer_computes table context expression))

private theorem statements_next_computes (checked : Bool) (sorts : SortTable) (table : SignatureTable)
    (context : Context) (rest : List Preterm)
    (tail : Applies P H "mm0:form-statements" [encodeSorts sorts, encodeTable table, encodeContext context, encodeExpressions rest]
      (boolean (rest.all (Preterm.checkStatement (sortsOf sorts) (signatureOf table) context)))) :
    Applies P H "mm0:form-statements-next"
      [boolean checked, encodeSorts sorts, encodeTable table, encodeContext context, encodeExpressions rest]
      (boolean (checked && rest.all (Preterm.checkStatement (sortsOf sorts) (signatureOf table) context))) := by
  cases checked with
  | false => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | true =>
      refine declaration_equation (equation := A[49]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) tail

theorem statements_computes (sorts : SortTable) (table : SignatureTable) (context : Context) (expressions : List Preterm) :
    Applies P H "mm0:form-statements" [encodeSorts sorts, encodeTable table, encodeContext context, encodeExpressions expressions]
      (boolean (expressions.all (Preterm.checkStatement (sortsOf sorts) (signatureOf table) context))) := by
  induction expressions with
  | nil => exact ⟨3, by rw [declaration_apply _ (by decide)]; rfl⟩
  | cons first rest ih =>
      refine declaration_equation (equation := A[45]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [listView ((first :: rest).map encode), encodeSorts sorts, encodeTable table, encodeContext context])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_computes _)
      · refine declaration_equation (equation := A[47]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call (by simp [Special])
          (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
          (statements_next_computes _ sorts table context rest ih)
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
          (statement_computes sorts table context first)

private theorem theorem_context_computes (checked : Bool) (sorts : SortTable) (table : SignatureTable) (declaration : TheoremDecl) :
    Applies P H "mm0:form-theorem-context"
      [boolean checked, encodeSorts sorts, encodeTable table, encodeContext declaration.arguments,
        encodeExpressions declaration.hypotheses, encode declaration.conclusion]
      (boolean (checked && (declaration.hypotheses.all
        (Preterm.checkStatement (sortsOf sorts) (signatureOf table) declaration.arguments) &&
        Preterm.checkStatement (sortsOf sorts) (signatureOf table) declaration.arguments declaration.conclusion))) := by
  cases checked with
  | false => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | true =>
      refine declaration_equation (equation := A[52]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil))
        (and_computes (declaration.hypotheses.all
          (Preterm.checkStatement (sortsOf sorts) (signatureOf table) declaration.arguments))
          (Preterm.checkStatement (sortsOf sorts) (signatureOf table) declaration.arguments declaration.conclusion))
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
          (statements_computes sorts table declaration.arguments declaration.hypotheses)
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
          (statement_computes sorts table declaration.arguments declaration.conclusion)

theorem theorem_computes (sorts : SortTable) (table : SignatureTable) (declaration : TheoremDecl) :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem declaration]
      (boolean (TheoremDecl.check (sortsOf sorts) (signatureOf table) declaration)) := by
  rw [TheoremDecl.check, Bool.and_assoc]
  refine declaration_equation (equation := A[50]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))
    (theorem_context_computes _ sorts table declaration)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (context_computes sorts declaration.arguments)

theorem term_result_exact (sorts : SortTable) (declaration : TermDecl) (result : Term) :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration declaration] result ↔
      result = boolean (TermDecl.check (sortsOf sorts) declaration) := by
  constructor
  · exact fun run => run.deterministic (term_computes sorts declaration)
  · rintro rfl; exact term_computes sorts declaration

theorem term_accepts_iff (sorts : SortTable) (declaration : TermDecl) :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration declaration] (.sym "True") ↔
      TermDecl.Admissible (sortsOf sorts) declaration := by
  rw [term_result_exact, ← TermDecl.check_iff]
  cases TermDecl.check (sortsOf sorts) declaration <;> simp [boolean]

theorem term_refuses_iff (sorts : SortTable) (declaration : TermDecl) :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration declaration] (.sym "False") ↔
      ¬ TermDecl.Admissible (sortsOf sorts) declaration := by
  rw [term_result_exact, ← TermDecl.check_iff]
  cases TermDecl.check (sortsOf sorts) declaration <;> simp [boolean]

theorem theorem_result_exact (sorts : SortTable) (table : SignatureTable) (declaration : TheoremDecl) (result : Term) :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem declaration] result ↔
      result = boolean (TheoremDecl.check (sortsOf sorts) (signatureOf table) declaration) := by
  constructor
  · exact fun run => run.deterministic (theorem_computes sorts table declaration)
  · rintro rfl; exact theorem_computes sorts table declaration

theorem theorem_accepts_iff (sorts : SortTable) (table : SignatureTable) (declaration : TheoremDecl) :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem declaration] (.sym "True") ↔
      TheoremDecl.Admissible (sortsOf sorts) (signatureOf table) declaration := by
  rw [theorem_result_exact, ← TheoremDecl.check_iff]
  cases TheoremDecl.check (sortsOf sorts) (signatureOf table) declaration <;> simp [boolean]

theorem theorem_refuses_iff (sorts : SortTable) (table : SignatureTable) (declaration : TheoremDecl) :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem declaration] (.sym "False") ↔
      ¬ TheoremDecl.Admissible (sortsOf sorts) (signatureOf table) declaration := by
  rw [theorem_result_exact, ← TheoremDecl.check_iff]
  cases TheoremDecl.check (sortsOf sorts) (signatureOf table) declaration <;> simp [boolean]

theorem theorem_completed_result (sorts : SortTable) (table : SignatureTable) (declaration : TheoremDecl) (fuel : Nat)
    (finished : apply P H fuel "mm0:form-theorem"
      [encodeSorts sorts, encodeTable table, encodeTheorem declaration] ≠ .exhausted) :
    apply P H fuel "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem declaration] =
      .value (boolean (TheoremDecl.check (sortsOf sorts) (signatureOf table) declaration)) :=
  (theorem_computes sorts table declaration).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration
