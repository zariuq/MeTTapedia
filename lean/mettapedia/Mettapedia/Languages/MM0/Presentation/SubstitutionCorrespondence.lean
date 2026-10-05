import Mettapedia.Languages.MM0.Presentation.SubstitutionProgram
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# Authored substitution computes the independent MM0 substitution

The equations perform the traversal, lookup and short-circuit control flow.
The only primitive contracts used are natural zero testing and predecessor.
The correspondence includes missing-variable refusal, arbitrary finite terms
and substitution lists, and indices without a machine-word restriction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation

open Kernel
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => substitutionProgram
local notation "H" => naturalHost

private theorem zero_applies (index : Nat) :
    Applies P H "nik:nat-zero" [natural index]
      (.sym (if index = 0 then "True" else "False")) :=
  .primitive (by rfl) (naturalHost_zero index)

private theorem pred_applies (index : Nat) :
    Applies P H "nik:nat-pred" [natural index] (natural index.pred) :=
  .primitive (by rfl) (naturalHost_pred index)

private theorem lookup_zero_applies (head tail : Term) (index : Nat) :
    Applies P H "mm0:lookup-zero" [.sym "True", head, tail, natural index]
      (.expr [.sym "Some", head]) := ⟨2, rfl⟩

private theorem lookup_successor_applies (head tail result : Term) (index : Nat)
    (next : Applies P H "mm0:lookup" [tail, natural index] result) :
    Applies P H "mm0:lookup-zero" [.sym "False", head, tail, natural (index + 1)] result := by
  refine Applies.equation (equation := P[10])
    (environment := [("h", head), ("t", tail), ("i", natural (index + 1))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) next
  · exact .variable (by rfl)
  · refine Evaluates.call (values := [natural (index + 1)]) (by simp [Special])
      (.cons ?_ .nil) (pred_applies (index + 1))
    exact .variable (by rfl)

private theorem lookup_cons_applies (head tail result : Term) (index : Nat)
    (next : Applies P H "mm0:lookup-zero"
      [.sym (if index = 0 then "True" else "False"), head, tail, natural index] result) :
    Applies P H "mm0:lookup" [.expr [.sym "LCons", head, tail], natural index] result := by
  refine Applies.equation (equation := P[8])
    (environment := [("h", head), ("t", tail), ("i", natural index)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))) next
  · refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (zero_applies index)
    exact .variable (by rfl)
  · exact .variable (by rfl)
  · exact .variable (by rfl)
  · exact .variable (by rfl)

theorem lookup_computes (values : List Preterm) (index : Nat) :
    Applies P H "mm0:lookup" [encodeValues values, natural index]
      (encodeResult values[index]?) := by
  induction values generalizing index with
  | nil => exact ⟨1, rfl⟩
  | cons head tail ih =>
      apply lookup_cons_applies
      cases index with
      | zero => exact lookup_zero_applies _ _ _
      | succ index =>
          simpa only [Nat.add_one_ne_zero, ↓reduceIte, List.getElem?_cons_succ] using
            lookup_successor_applies (encode head) (encodeValues tail)
              (encodeResult tail[index]?) index (ih index)

private theorem substitute_variable_applies (values : List Preterm) (index : Nat) :
    Applies P H "mm0:subst" [encode (.var index), encodeValues values]
      (encodeResult values[index]?) := by
  refine Applies.equation (equation := P[0])
    (environment := [("i", natural index), ("values", encodeValues values)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) (lookup_computes values index)
  · exact .variable (by rfl)
  · exact .variable (by rfl)

private theorem substitute_function_none (argument values : Term) :
    Applies P H "mm0:subst-function" [.sym "None", argument, values] (.sym "None") := ⟨1, rfl⟩

private theorem substitute_argument_none (function : Term) :
    Applies P H "mm0:subst-argument" [function, .sym "None"] (.sym "None") := ⟨1, rfl⟩

private theorem substitute_argument_some (function argument : Term) :
    Applies P H "mm0:subst-argument" [function, .expr [.sym "Some", argument]]
      (.expr [.sym "Some", .expr [.sym "MM0:App", function, argument]]) := ⟨3, rfl⟩

private theorem substitute_function_some (function argument values middle result : Term)
    (child : Applies P H "mm0:subst" [argument, values] middle)
    (finish : Applies P H "mm0:subst-argument" [function, middle] result) :
    Applies P H "mm0:subst-function" [.expr [.sym "Some", function], argument, values] result := by
  refine Applies.equation (equation := P[4])
    (environment := [("f", function), ("x", argument), ("values", values)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) finish
  · exact .variable (by rfl)
  · refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) child
    · exact .variable (by rfl)
    · exact .variable (by rfl)

private theorem substitute_application_applies (function argument values middle result : Term)
    (child : Applies P H "mm0:subst" [function, values] middle)
    (finish : Applies P H "mm0:subst-function" [middle, argument, values] result) :
    Applies P H "mm0:subst" [.expr [.sym "MM0:App", function, argument], values] result := by
  refine Applies.equation (equation := P[2])
    (environment := [("f", function), ("x", argument), ("values", values)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ (.cons ?_ .nil))) finish
  · refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) child
    · exact .variable (by rfl)
    · exact .variable (by rfl)
  · exact .variable (by rfl)
  · exact .variable (by rfl)

/-- Every finite substitution input is computed by the authored equations,
including an explicit `None` when a required variable has no image. -/
theorem substitution_computes (source : Preterm) (values : List Preterm) :
    Applies P H "mm0:subst" [encode source, encodeValues values]
      (encodeResult (source.substitute (Substitution.ofList values))) := by
  induction source with
  | var index => exact substitute_variable_applies values index
  | term symbol => exact ⟨4, rfl⟩
  | app function argument ihFunction ihArgument =>
      refine substitute_application_applies _ _ _ _ _ ihFunction ?_
      cases hf : function.substitute (Substitution.ofList values) with
      | none =>
          simpa [Preterm.substitute, hf, encodeResult] using
            substitute_function_none (encode argument) (encodeValues values)
      | some function' =>
          cases ha : argument.substitute (Substitution.ofList values) with
          | none =>
              have child : Applies P H "mm0:subst" [encode argument, encodeValues values]
                  (.sym "None") := by simpa [ha, encodeResult] using ihArgument
              simpa [Preterm.substitute, hf, ha, encodeResult] using
                substitute_function_some (encode function') (encode argument) (encodeValues values)
                  (.sym "None") (.sym "None") child (substitute_argument_none _)
          | some argument' =>
              have child : Applies P H "mm0:subst" [encode argument, encodeValues values]
                  (.expr [.sym "Some", encode argument']) := by simpa [ha, encodeResult] using ihArgument
              simpa [Preterm.substitute, hf, ha, encodeResult, encode] using
                substitute_function_some (encode function') (encode argument) (encodeValues values)
                  (.expr [.sym "Some", encode argument'])
                  (.expr [.sym "Some", .expr [.sym "MM0:App", encode function', encode argument']])
                  child (substitute_argument_some _ _)

/-- The shared engine cannot return a different outcome for these inputs. -/
theorem substitution_result_exact (source : Preterm) (values : List Preterm) (result : Term) :
    Applies P H "mm0:subst" [encode source, encodeValues values] result ↔
      result = encodeResult (source.substitute (Substitution.ofList values)) := by
  constructor
  · intro computation
    exact computation.deterministic (substitution_computes source values)
  · intro same
    subst result
    exact substitution_computes source values

theorem encodeResult_injective : Function.Injective encodeResult := by
  intro first second same
  cases first with
  | none => cases second <;> first | rfl | cases same
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have encoded : encode first = encode second := by
            simpa only [encodeResult, Term.expr.injEq, List.cons.injEq, and_true, true_and] using same
          exact congrArg some (encode_injective encoded)

/-- Soundness and completeness against independent structural substitution. -/
theorem substitution_accepts_iff (source result : Preterm) (values : List Preterm) :
    Applies P H "mm0:subst" [encode source, encodeValues values] (encodeResult (some result)) ↔
      Preterm.Substitutes (Substitution.ofList values) source result := by
  rw [substitution_result_exact]
  constructor
  · intro same
    exact Preterm.substitute_sound (encodeResult_injective same).symm
  · intro derivation
    rw [derivation.eval]

theorem substitution_refuses_iff (source : Preterm) (values : List Preterm) :
    Applies P H "mm0:subst" [encode source, encodeValues values] (encodeResult none) ↔
      ¬ ∃ result, Preterm.Substitutes (Substitution.ofList values) source result := by
  rw [substitution_result_exact]
  constructor
  · intro same
    exact (Preterm.substitute_none_iff _ _).mp (encodeResult_injective same).symm
  · intro refused
    rw [(Preterm.substitute_none_iff _ _).mpr refused]

end Mettapedia.Languages.MM0.Presentation
