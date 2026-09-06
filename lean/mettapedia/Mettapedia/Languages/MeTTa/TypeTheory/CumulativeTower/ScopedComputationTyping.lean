import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRegularity

/-!
# Formation-sensitive typing of scoped computation bodies

The computation syntax carries raw native terms, rather than host functions
or pre-admitted answer subtypes. These independent rules type its returned
terms, operation calls, choices and bound continuations. Ordinary sequencing
requires a result type independent of the selected value; dependent sequencing
retains that value in the native Sigma result.

Operation signatures contain a closed argument type and a one-variable result
family. Their formation is checked separately from execution. The structural
theorems use the existing capture-avoiding native substitutions and refined
context morphisms. They neither make arbitrary operations sound nor select a
full CBPV calculus, a sharing implementation, or an evaluation strategy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedComputation

variable {Head Operation : Type} {n m : Nat}

/-- An operation's result may depend on its actual argument. Signatures have
no semantic or proof fields. Multiple parameters can use a native Sigma input. -/
structure OperationSignature (Head Operation : Type) where
  input : Operation → Tm Head 0
  output : Operation → Tm Head 1

namespace OperationSignature

/-- Instantiate the independently authored one-variable result family. -/
def result (signature : OperationSignature Head Operation)
    (operation : Operation) (argument : Tm Head n) : Tm Head n :=
  subst (fun _ => argument) (signature.output operation)

@[simp] theorem substitute_result (signature : OperationSignature Head Operation)
    (operation : Operation) (argument : Tm Head n) (σ : Sub Head n m) :
    subst σ (signature.result operation argument) =
      signature.result operation (subst σ argument) := by
  exact subst_comp σ (fun _ => argument) (signature.output operation)

@[simp] theorem rename_result (signature : OperationSignature Head Operation)
    (operation : Operation) (argument : Tm Head n) (ρ : Ren n m) :
    rename ρ (signature.result operation argument) =
      signature.result operation (rename ρ argument) := by
  exact rename_subst ρ (fun _ => argument) (signature.output operation)

end OperationSignature

/-- Formation is a property of the authored operation declaration, not a
claim that its implementation returns values of the declared family. -/
structure OperationFormation (R : Rules Head)
    (signature : OperationSignature Head Operation) (operation : Operation) : Prop where
  input_formed : ∃ u, R.isUniverse u ∧
    FormationSensitive.Typing R .nil (signature.input operation) (.head u)
  output_formed : ∃ v, R.isUniverse v ∧
    FormationSensitive.Typing R (.snoc .nil (signature.input operation))
      (signature.output operation) (.head v)

/-- Independent computation typing on the raw scoped code. In particular,
sequence bodies are syntax under a real binder, not Lean continuations. -/
inductive Typing (R : Rules Head) (signature : OperationSignature Head Operation) :
    {n : Nat} → Ctx Head n → Code Head Operation n → Tm Head n → Prop where
  | returnValue {n : Nat} {Γ : Ctx Head n} {value A : Tm Head n} :
      FormationSensitive.Typing R Γ value A →
      Typing R signature Γ (.returnValue value) A
  | sequence {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u v : Head}
      {first : Code Head Operation n} {body : Code Head Operation (n + 1)} :
      FormationSensitive.Typing R Γ A (.head u) → R.isUniverse u →
      FormationSensitive.Typing R Γ B (.head v) → R.isUniverse v →
      Typing R signature Γ first A →
      Typing R signature (.snoc Γ A) body (rename wk B) →
      Typing R signature Γ (.sequence first body) B
  | sequenceSigma {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head}
      {first : Code Head Operation n} {body : Code Head Operation (n + 1)} :
      FormationSensitive.Typing R Γ (.sigma A B) (.head u) → R.isUniverse u →
      Typing R signature Γ first A → Typing R signature (.snoc Γ A) body B →
      Typing R signature Γ (.sequenceSigma first body) (.sigma A B)
  | choose {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
      {left right : Code Head Operation n} :
      Typing R signature Γ left A → Typing R signature Γ right A →
      Typing R signature Γ (.choose left right) A
  | call {n : Nat} {Γ : Ctx Head n} {operation : Operation} {argument : Tm Head n} :
      OperationFormation R signature operation →
      FormationSensitive.Typing R Γ argument (liftClosed (signature.input operation)) →
      Typing R signature Γ (.call operation argument) (signature.result operation argument)
  | conv {n : Nat} {Γ : Ctx Head n} {code : Code Head Operation n}
      {A B : Tm Head n} {u : Head} :
      Typing R signature Γ code A →
      FormationSensitive.Typing R Γ B (.head u) → R.isUniverse u →
      Conv R.headEq A B R.computation → Typing R signature Γ code B

variable {R : Rules Head} {signature : OperationSignature Head Operation}
  {Γ : Ctx Head n} {Δ : Ctx Head m}

/-- Extend a refined native environment with an actually admitted result. -/
theorem extendEnvironment {σ : Sub Head n m} {A : Tm Head n} {value : Tm Head m}
    (typed : FormationSensitive.CtxMor R Γ Δ σ)
    (admitted : FormationSensitive.Typing R Δ value (subst σ A)) :
    FormationSensitive.CtxMor R (.snoc Γ A) Δ (consSub value σ) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa only [consSub_zero, Ctx.lookup_snoc_zero, subst_consSub_rename_wk] using admitted
  · intro prior
    simpa only [consSub_succ, Ctx.lookup_snoc_succ, subst_consSub_rename_wk] using typed prior

/-- Substitution preserves every computation constructor and the selected
dependent family, including native declaration-formation premises. -/
theorem Typing.substitute {code : Code Head Operation n} {A : Tm Head n}
    (typing : Typing R signature Γ code A) :
    ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m},
      FormationSensitive.CtxMor R Γ Δ σ →
      Typing R signature Δ (code.substitute σ) (subst σ A) := by
  induction typing with
  | returnValue admitted =>
      intro m Δ σ typed
      exact .returnValue (admitted.substitute typed)
  | sequence formedA universeA formedB universeB _ _ ihFirst ihBody =>
      intro m Δ σ typed
      apply Typing.sequence (formedA.substitute typed) universeA
        (formedB.substitute typed) universeB (ihFirst typed)
      simpa only [subst_liftSub_wk] using ihBody (typed.lift _)
  | sequenceSigma formed universeWitness _ _ ihFirst ihBody =>
      intro m Δ σ typed
      exact .sequenceSigma (formed.substitute typed) universeWitness
        (ihFirst typed) (ihBody (typed.lift _))
  | choose _ _ ihLeft ihRight =>
      intro m Δ σ typed
      exact .choose (ihLeft typed) (ihRight typed)
  | call declared admitted =>
      intro m Δ σ typed
      have argument := admitted.substitute typed
      rw [subst_liftClosed] at argument
      simpa only [Code.substitute, OperationSignature.substitute_result] using
        (Typing.call declared argument)
  | conv _ formed universeWitness conversion ih =>
      intro m Δ σ typed
      exact .conv (ih typed) (formed.substitute typed) universeWitness (conversion.substitute σ)

/-- Renaming is the variable-only instance of the same typed substitution law. -/
theorem Typing.rename {code : Code Head Operation n} {A : Tm Head n}
    (typing : Typing R signature Γ code A) {ρ : Ren n m}
    (compatible : CtxRen Γ Δ ρ) :
    Typing R signature Δ (code.rename ρ) (rename ρ A) := by
  have typed : FormationSensitive.CtxMor R Γ Δ (renSub ρ) := by
    intro index
    simpa only [renSub, subst_renSub, compatible index] using
      (FormationSensitive.Typing.var (R := R) (Γ := Δ) (ρ index))
  simpa only [Code.substitute_renSub, subst_renSub] using typing.substitute typed

/-- Opening a computation binder uses an admitted native term, never an
effectful computation substituted into mathematical types. This does not
classify the term as a syntactic CBPV value or normalize its payload. -/
theorem Typing.instantiate {A : Tm Head n} {B : Tm Head (n + 1)}
    {body : Code Head Operation (n + 1)} {value : Tm Head n}
    (typing : Typing R signature (.snoc Γ A) body B)
    (admitted : FormationSensitive.Typing R Γ value A) :
    Typing R signature Γ (Code.instantiate value body) (inst0 value B) := by
  apply typing.substitute
  intro index
  refine Fin.cases ?_ ?_ index
  · change FormationSensitive.Typing R Γ value (inst0 value (Presentation.rename wk A))
    rw [inst0_rename_wk]
    exact admitted
  · intro prior
    change FormationSensitive.Typing R Γ (.var prior)
      (inst0 value (Presentation.rename wk (Ctx.lookup Γ prior)))
    rw [inst0_rename_wk]
    exact .var prior

/-- A computation admitted in a formed native telescope. -/
structure Judgment (R : Rules Head) (signature : OperationSignature Head Operation)
    (Γ : Ctx Head n) (code : Code Head Operation n) (A : Tm Head n) : Prop where
  context : FormationSensitive.ContextFormation R Γ
  typing : Typing R signature Γ code A

theorem Judgment.substitute {code : Code Head Operation n} {A : Tm Head n}
    (judgment : Judgment R signature Γ code A) {σ : Sub Head n m}
    (target : FormationSensitive.ContextFormation R Δ)
    (typed : FormationSensitive.CtxMor R Γ Δ σ) :
    Judgment R signature Δ (code.substitute σ) (subst σ A) :=
  ⟨target, judgment.typing.substitute typed⟩

end ScopedComputation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
