import Mettapedia.Languages.MeTTa.PeTTa.ExplicitEvaluation

/-!
# Captured argument readout and guarded code specialization

The existing value-occurrence semantics supplies both readout modes. A held
argument is syntax in its caller's environment; adding a callee's bindings
does not extend that captured environment. Reading it as data uses simultaneous
substitution, whereas explicit code evaluation may interpret its expressions.

The code specialization law below requires inertness only for substitutions
on the source's actual footprint. Unrelated bindings need not be inert. Its
answer-list equality retains order and multiplicity. These laws concern the
finite first-order occurrence fragment; they do not verify a C compiler or
license erasing effects, escaping unification, or callable head patterns.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.HeldArgumentSpecialization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SubstitutionAlgebra (Subst subst vars restrict)
open ValueOccurrences (Program evalIn evalCode evalPlanned planOf Inert)

/-- Code substitution needs inertness at the captured source's variables,
not at every variable of a larger caller environment. -/
theorem code_substitution_of_inert_captures (P : Program) (environment : Subst)
    (source : Atom)
    (inert : ∀ name ∈ vars source, ∀ value,
      environment name = some value → Inert P value) :
    evalCode P (subst environment source) = evalIn P environment source := by
  have restricted : ∀ name value,
      restrict environment (vars source) name = some value → Inert P value := by
    intro name value bound
    by_cases present : name ∈ vars source
    · exact inert name present value (by simpa [restrict, present] using bound)
    · simp [restrict, present] at bound
  have readout := ValueOccurrences.evalCode_subst_of_inert P
    (restrict environment (vars source)) restricted source
  rw [SubstitutionAlgebra.subst_restrict_vars] at readout
  rw [ValueOccurrences.evalIn_congr_on_vars P
    (restrict environment (vars source)) environment source
    (fun name present => by simp [restrict, present])] at readout
  exact readout

/-- Reading a captured argument retains precisely the caller prefix even
when a callee introduces the same source spelling. -/
theorem captured_syntax_ignores_callee (caller callee : List (String × Atom))
    (source : Atom) :
    subst (fun name => List.lookup name ((caller ++ callee).take caller.length)) source =
      subst (fun name => List.lookup name caller) source := by
  simp

/-- The same prefix boundary preserves the whole evaluated answer list. -/
theorem captured_evaluation_ignores_callee (P : Program)
    (caller callee : List (String × Atom)) (source : Atom) :
    evalIn P (fun name => List.lookup name ((caller ++ callee).take caller.length)) source =
      evalIn P (fun name => List.lookup name caller) source := by
  simp

/-- The retained occurrence plan agrees with captured-environment execution
without imposing inertness on values which remain data. -/
theorem captured_plan_readout (P : Program)
    (caller callee : List (String × Atom)) (source : Atom) :
    evalPlanned P (planOf source)
        (subst (fun name => List.lookup name ((caller ++ callee).take caller.length)) source) =
      evalIn P (fun name => List.lookup name caller) source := by
  rw [ValueOccurrences.evalPlanned_planOf_subst]
  exact captured_evaluation_ignores_callee P caller callee source

/-- An explicitly forced captured source may be specialized using ordinary
value slots when its captured values are inert on the source footprint. -/
theorem captured_code_readout (P : Program)
    (caller callee : List (String × Atom)) (source : Atom)
    (inert : ∀ name ∈ vars source, ∀ value,
      List.lookup name caller = some value → Inert P value) :
    evalCode P (subst (fun name => List.lookup name ((caller ++ callee).take caller.length)) source) =
      evalIn P (fun name => List.lookup name caller) source := by
  rw [captured_syntax_ignores_callee]
  exact code_substitution_of_inert_captures P (fun name => List.lookup name caller) source inert

namespace Controls

def duplicateCall : Program where
  isCall items := items == [.symbol "choose"]
  answers _ := [.symbol "answer", .symbol "answer"]

def caller : Subst := ValueOccurrences.bindAt SubstitutionAlgebra.empty "code"
  (.expression [.symbol "choose"])

theorem held_call_stays_data :
    evalPlanned duplicateCall (planOf (.var "code"))
      (subst caller (.var "code")) =
        [.expression [.symbol "choose"]] := by decide

theorem explicit_force_keeps_duplicate_answers :
    evalCode duplicateCall (subst caller (.var "code")) =
      [.symbol "answer", .symbol "answer"] := by decide

theorem erasing_the_value_boundary_changes_answers :
    evalCode duplicateCall (subst caller (.var "code")) ≠
      evalIn duplicateCall caller (.var "code") := by decide

theorem held_cons_preserves_written_syntax :
    subst (ValueOccurrences.bindAt SubstitutionAlgebra.empty "n" (.grounded (.int 5)))
      (.expression [.symbol "cons", .var "n", .expression []]) =
        .expression [.symbol "cons", .grounded (.int 5), .expression []] := by decide

theorem callee_binding_cannot_replace_a_capture :
    subst (fun name => List.lookup name
      (([("n", Atom.grounded (.int 5))] ++ [("n", Atom.grounded (.int 9))]).take 1))
      (.var "n") = .grounded (.int 5) := by decide

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.HeldArgumentSpecialization
