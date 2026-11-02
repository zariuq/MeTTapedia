import Mettapedia.Logic.HOL.FiniteConstructorSeparation

/-!
# Constructor programs respect encoded payload equality

Equal encodings have the same constructor occurrence and equal original
fields. Applying any occurrence-indexed typed program to those fields gives
equal results. Distinct occurrences are refuted by the actual encoder's
handler observations, and field recovery uses its retained beta proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
open CurriedPredicates Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {assumptions : List (Formula Const Γ)} {result : Ty Base}

def applyFields_congr (fields : List (Ty Base))
    (first second : Term Const Γ (FunctionType fields result))
    (firstArguments secondArguments : Arguments Const Γ fields)
    (functions : ProofSyntax Const assumptions (.eq first second))
    (arguments : ∀ {type : Ty Base} (index : Var fields type),
      ProofSyntax Const assumptions (.eq (argumentAt index firstArguments) (argumentAt index secondArguments))) :
    ProofSyntax Const assumptions (.eq (applyFields fields first firstArguments) (applyFields fields second secondArguments)) := by
  induction fields with
  | nil => exact functions
  | cons type rest previous =>
    exact previous (.app first firstArguments.1) (.app second secondArguments.1)
      firstArguments.2 secondArguments.2
      (.eqTrans (.eqApp firstArguments.1 functions) (.eqAppArg second (arguments .vz)))
      (fun index => arguments (.vs index))

theorem applyFields_congr_free (fields : List (Ty Base))
    (first second : Term Const Γ (FunctionType fields result))
    (firstArguments secondArguments : Arguments Const Γ fields)
    (functions : ProofSyntax Const assumptions (.eq first second))
    (arguments : ∀ {type : Ty Base} (index : Var fields type),
      ProofSyntax Const assumptions (.eq (argumentAt index firstArguments) (argumentAt index secondArguments)))
    (functionsFree : functions.FunctionExtensionalityFree)
    (argumentsFree : ∀ {type : Ty Base} (index : Var fields type), (arguments index).FunctionExtensionalityFree) :
    (applyFields_congr fields first second firstArguments secondArguments functions arguments).FunctionExtensionalityFree := by
  induction fields with
  | nil => exact functionsFree
  | cons type rest previous =>
    exact previous (.app first firstArguments.1) (.app second secondArguments.1)
      firstArguments.2 secondArguments.2
      (.eqTrans (.eqApp firstArguments.1 functions) (.eqAppArg second (arguments .vz)))
      (fun index => arguments (.vs index)) ⟨functionsFree, argumentsFree .vz⟩
      (fun index => argumentsFree (.vs index))

def program_equal_of_payload (signature : List (List (Ty Base)))
    (programs : (occurrence : Fin signature.length) → Term Const Γ (FunctionType (signature.get occurrence) result))
    (first second : Fin signature.length)
    (firstArguments : Arguments Const Γ (signature.get first))
    (secondArguments : Arguments Const Γ (signature.get second))
    (same : ProofSyntax Const assumptions (.eq (encode signature first firstArguments) (encode signature second secondArguments))) :
    ProofSyntax Const assumptions (.eq
      (applyFields (signature.get first) (programs first) firstArguments)
      (applyFields (signature.get second) (programs second) secondArguments)) := by
  by_cases occurrences : first = second
  · subst second
    exact applyFields_congr _ _ _ firstArguments secondArguments (.eqRefl (programs first))
      (fun index => recover_field signature first index firstArguments secondArguments same)
  · exact .botE (separate_occurrences signature first second occurrences firstArguments secondArguments same)

theorem program_equal_of_payload_free (signature : List (List (Ty Base)))
    (programs : (occurrence : Fin signature.length) → Term Const Γ (FunctionType (signature.get occurrence) result))
    (first second : Fin signature.length)
    (firstArguments : Arguments Const Γ (signature.get first))
    (secondArguments : Arguments Const Γ (signature.get second))
    (same : ProofSyntax Const assumptions (.eq (encode signature first firstArguments) (encode signature second secondArguments)))
    (sameFree : same.FunctionExtensionalityFree) :
    (program_equal_of_payload signature programs first second firstArguments secondArguments same).FunctionExtensionalityFree := by
  unfold program_equal_of_payload
  split
  next occurrences =>
    cases occurrences
    apply applyFields_congr_free
    · trivial
    · intro type index
      exact recover_field_free signature first index firstArguments secondArguments same sameFree
  · exact separate_occurrences_free signature first second _ firstArguments secondArguments same sameFree

#print axioms program_equal_of_payload
#print axioms program_equal_of_payload_free

end Mettapedia.Logic.HOL.FiniteConstructorEncoding
