import Mettapedia.Logic.HOL.ProofSyntax
import Mettapedia.Logic.HOL.Soundness

/-!
# Computing HOL expressions with retained invariant proofs

Each operation supplies an actual retained proof of closure. Running a finite
list builds both the object expression and its proof, using universal and
implication elimination. It does not search for proofs or assume closure of
an arbitrary operation. Assumptions and the surrounding object context remain
explicit. The dependent host can consume the resulting source proof unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ProofCarryingPipeline

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}
  {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}

def closureFormula (predicate : Term Const Γ (σ ⇒ .prop))
    (operation : Term Const Γ (σ ⇒ σ)) : Formula Const Γ :=
  .all (.imp (.app (weaken predicate) (.var .vz))
    (.app (weaken predicate) (.app (weaken operation) (.var .vz))))

structure Value (predicate : Term Const Γ (σ ⇒ .prop))
    (assumptions : List (Formula Const Γ)) where
  term : Term Const Γ σ
  evidence : ProofSyntax Const assumptions (.app predicate term)

structure Operation (predicate : Term Const Γ (σ ⇒ .prop))
    (assumptions : List (Formula Const Γ)) where
  term : Term Const Γ (σ ⇒ σ)
  evidence : ProofSyntax Const assumptions (closureFormula predicate term)

private theorem substitute_weaken (argument : Term Const Γ σ)
    {τ : Ty Base} (body : Term Const Γ τ) :
    subst (Subst.single argument) (weaken body) = body :=
  instantiate_weaken argument body

/-- The next proof is built from the selected closure proof and current proof. -/
def Operation.apply {predicate : Term Const Γ (σ ⇒ .prop)}
    (operation : Operation predicate Δ) (value : Value predicate Δ) : Value predicate Δ where
  term := .app operation.term value.term
  evidence := .impE (by
    simpa only [closureFormula, instantiate, subst, Subst.single, substitute_weaken] using
      (ProofSyntax.allE value.term operation.evidence)) value.evidence

def run {predicate : Term Const Γ (σ ⇒ .prop)}
    (operations : List (Operation predicate Δ)) (initial : Value predicate Δ) : Value predicate Δ :=
  operations.foldl (fun value operation => operation.apply value) initial

/-- Segment composition preserves the proof data as well as the expression. -/
theorem run_append {predicate : Term Const Γ (σ ⇒ .prop)}
    (first second : List (Operation predicate Δ)) (initial : Value predicate Δ) :
    run (first ++ second) initial = run second (run first initial) := by
  exact List.foldl_append

/-- Forgetting proofs leaves exactly ordinary left-to-right expression building. -/
theorem run_term {predicate : Term Const Γ (σ ⇒ .prop)}
    (operations : List (Operation predicate Δ)) (initial : Value predicate Δ) :
    (run operations initial).term =
      operations.foldl (fun value operation => .app operation.term value) initial.term := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih => exact ih (operation.apply initial)

/-- Interpreting the constructed expression agrees with applying the
interpreted operations in order. No proof validity or extensionality premise
is needed for this computation equation. -/
theorem run_denote {predicate : Term Const Γ (σ ⇒ .prop)}
    (operations : List (Operation predicate Δ)) (initial : Value predicate Δ)
    (model : HenkinModel.{u, v, w} Base Const) (valuation : HenkinModel.Valuation model Γ) :
    model.denote (run operations initial).term valuation =
      operations.foldl (fun value (operation : Operation predicate Δ) =>
        model.denote operation.term valuation value)
        (model.denote initial.term valuation) := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih => exact ih (operation.apply initial)

/-- Semantic validity uses the existing HOL soundness theorem and explicitly
requires validity of the source assumptions in the selected Henkin model. -/
theorem run_sound {predicate : Term Const Γ (σ ⇒ .prop)}
    (operations : List (Operation predicate Δ)) (initial : Value predicate Δ)
    (model : HenkinModel.{u, v, w} Base Const) (valuation : HenkinModel.Valuation model Γ)
    (extensional : HenkinModel.FunctionsRespectEqv model)
    (admissible : HenkinModel.ValuationAdmissible model valuation)
    (assumptions : Soundness.SatisfiesHyps model valuation Δ) :
    (model.denote (.app predicate (run operations initial).term) valuation).down :=
  Soundness.extDerivation_sound (run operations initial).evidence.erase
    extensional admissible assumptions

#print axioms run_append
#print axioms run_term
#print axioms run_denote
#print axioms run_sound

end Mettapedia.Logic.HOL.ProofCarryingPipeline
