import Mettapedia.Logic.HOL.FiniteConstructorReadout
import Mettapedia.Logic.HOL.CurriedPredicateProofs

/-!
# Retained separation of encoded constructor occurrences

One handler returns truth at the selected occurrence and falsity elsewhere.
An equality between distinct encoded occurrences would identify these two
propositions. The construction uses the actual handler encoder and retained
beta/application proofs; no constructor separation axiom is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
open CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {assumptions : List (Formula Const Γ)}

theorem select_falseHandlers (signature : List (List (Ty Base))) (occurrence : Fin signature.length) :
    selectHandler signature occurrence (falseHandlers (Const := Const) (Γ := Γ) signature) =
      constant (signature.get occurrence) (.bot : Formula Const Γ) := by
  induction signature with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest previous =>
    rcases occurrence with ⟨index, bound⟩
    cases index with
    | zero => rfl
    | succ index => exact previous ⟨index, Nat.lt_of_succ_lt_succ bound⟩

theorem select_otherHandler (signature : List (List (Ty Base))) (first second : Fin signature.length)
    (different : first ≠ second) (handler : Term Const Γ (handlerType (signature.get first))) :
    selectHandler signature second (withHandler signature first handler) =
      constant (signature.get second) (.bot : Formula Const Γ) := by
  induction signature with
  | nil => exact Fin.elim0 first
  | cons fields rest previous =>
    rcases first with ⟨firstIndex, firstBound⟩
    rcases second with ⟨secondIndex, secondBound⟩
    cases firstIndex with
    | zero =>
      cases secondIndex with
      | zero => exact False.elim (different rfl)
      | succ secondIndex => exact select_falseHandlers rest ⟨secondIndex, Nat.lt_of_succ_lt_succ secondBound⟩
    | succ firstIndex =>
      cases secondIndex with
      | zero => rfl
      | succ secondIndex =>
        apply previous ⟨firstIndex, Nat.lt_of_succ_lt_succ firstBound⟩
          ⟨secondIndex, Nat.lt_of_succ_lt_succ secondBound⟩ _ handler
        intro same
        apply different
        exact Fin.ext (congrArg (fun index => index.val + 1) same)

def observe_selected_constant (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) (formula : Formula Const Γ) :
    ProofSyntax Const assumptions (.eq (observe signature (encode signature occurrence arguments)
      (withHandler signature occurrence (constant (signature.get occurrence) formula))) formula) := by
  have readout := encode_beta (Δ := assumptions) signature occurrence arguments
    (withHandler signature occurrence (constant (signature.get occurrence) formula))
  have selected := ProofSyntax.castIndices rfl
    (by rw [select_withHandler]) readout
  exact .eqTrans selected (constant_beta _ formula arguments)

def observe_other_false (signature : List (List (Ty Base))) (first second : Fin signature.length)
    (different : first ≠ second) (handler : Term Const Γ (handlerType (signature.get first)))
    (arguments : Arguments Const Γ (signature.get second)) :
    ProofSyntax Const assumptions (.eq
      (observe signature (encode signature second arguments) (withHandler signature first handler)) .bot) := by
  have readout := encode_beta (Δ := assumptions) signature second arguments (withHandler signature first handler)
  have selected := ProofSyntax.castIndices rfl
    (by rw [select_otherHandler signature first second different handler]) readout
  exact .eqTrans selected (constant_beta _ .bot arguments)

def separate_occurrences (signature : List (List (Ty Base))) (first second : Fin signature.length)
    (different : first ≠ second) (firstArguments : Arguments Const Γ (signature.get first))
    (secondArguments : Arguments Const Γ (signature.get second))
    (same : ProofSyntax Const assumptions (.eq (encode signature first firstArguments) (encode signature second secondArguments))) :
    ProofSyntax Const assumptions .bot :=
  .impE (.eqPropEL (.eqTrans
    (.eqSymm (observe_selected_constant signature first firstArguments .top))
    (.eqTrans (observe_congr signature _ _ (withHandler signature first (constant _ .top)) same)
      (observe_other_false signature first second different (constant _ .top) secondArguments)))) .topI

theorem observe_selected_constant_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) (formula : Formula Const Γ) :
    (observe_selected_constant (assumptions := assumptions) signature occurrence arguments formula).FunctionExtensionalityFree := by
  unfold observe_selected_constant
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact encode_beta_free _ _ _ _
  · exact constant_beta_free _ _ _

theorem observe_other_false_free (signature : List (List (Ty Base))) (first second : Fin signature.length)
    (different : first ≠ second) (handler : Term Const Γ (handlerType (signature.get first)))
    (arguments : Arguments Const Γ (signature.get second)) :
    (observe_other_false (assumptions := assumptions) signature first second different handler arguments).FunctionExtensionalityFree := by
  unfold observe_other_false
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact encode_beta_free _ _ _ _
  · exact constant_beta_free _ _ _

theorem separate_occurrences_free (signature : List (List (Ty Base))) (first second : Fin signature.length)
    (different : first ≠ second) (firstArguments : Arguments Const Γ (signature.get first))
    (secondArguments : Arguments Const Γ (signature.get second))
    (same : ProofSyntax Const assumptions (.eq (encode signature first firstArguments) (encode signature second secondArguments)))
    (free : same.FunctionExtensionalityFree) :
    (separate_occurrences signature first second different firstArguments secondArguments same).FunctionExtensionalityFree := by
  exact ⟨⟨observe_selected_constant_free _ _ _ _,
    ⟨observe_congr_free _ _ _ _ same free, observe_other_false_free _ _ _ _ _ _⟩⟩, True.intro⟩

#print axioms separate_occurrences
#print axioms separate_occurrences_free
end Mettapedia.Logic.HOL.FiniteConstructorEncoding
