import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedControlFlow

/-! Ordered source clauses distinguish first success, failure fallthrough
and exhaustive failure. The successful prepared cursor path retains a
nonempty captured environment and outer continuation.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.SelectionControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def number (value : Int) : OCaml.Value := .literal (.integer value)
def clauses : List OCaml.Clause := [⟨.literal (.integer 0), 1⟩, ⟨.bind, 2⟩, ⟨.wildcard, 1⟩]
def program : OCaml.Program where
  code := #[.literal (.integer 42), .literal (.integer 0), .variable 0, .matchValue 0 clauses]
  entry := 3

def table : GeneralPremise.ProviderSnapshot :=
  GeneralPremise.ProviderAppend.appendRows provider [failureRow 0 (number 42)]
def captured : OCaml.Environment := [number 99]
def rest : OCaml.Continuation := [.consHead (.literal .nil)]
def encodedRest : Pattern := node "MlKConsHead" [value (.literal .nil), node "MlKDone"]
def encodedClauses : Pattern := node "MlClauseCons" [patternId 0, code 1,
  node "MlClauseCons" [patternId 1, code 2, node "MlClauseCons" [patternId 2, code 1, node "MlClauseNil"]]]

#guard program.checkScope
#guard (prepare program).toOption.isSome
#guard OCaml.run program 100 (OCaml.begin program) == .complete (.ok (number 42))
#guard !(OCaml.run program 100 (OCaml.begin program) == .complete (.ok (number 0)))
#guard OCaml.selectClause clauses (number 42) == some (2, [number 42])
#guard OCaml.selectClause clauses (number 0) == some (1, [])
#guard !(OCaml.selectClause clauses (number 0) == some (2, [number 0]))
#guard OCaml.selectClause [⟨.literal (.integer 0), 1⟩] (number 42) == none
#guard (OCaml.Primitive.divide.eval [number 42, number 0]).toOption == some (.error .divisionByZero)

theorem ordered_fallthrough_has_actual_path (prepared : Prepared) (built : prepare program = .ok prepared) :
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value (number 42), node "MlKMatch" [encodedClauses, environment captured, encodedRest]])
      (node "MlEvaluate" [code 2, environment [number 42, number 99], encodedRest]) := by
  have cached : ∀ clause ∈ clauses, ∀ index,
      patternReference? (patterns program) clause.pattern = some (patternId index) →
      OCaml.matchPattern clause.pattern (number 42) = none → failureRow index (number 42) ∈ table.rows := by
    intro clause member index referenced failed
    simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · have actual : patternReference? (patterns program) (.literal (.integer 0)) = some (patternId 0) := by decide +kernel
      rw [actual] at referenced
      have same := patternId_injective (Option.some.inj referenced)
      subst index
      simp [table, GeneralPremise.ProviderAppend.appendRows]
    · simp [OCaml.matchPattern] at failed
    · simp [OCaml.matchPattern] at failed
  have actual := prepared_ordered_match_success_path program prepared table clauses encodedClauses (number 42) 2 [number 42]
    captured rest encodedRest built rfl (by decide +kernel) (by rfl) cached (by rfl)
  exact actual.2

theorem successful_clause_cannot_be_cached_as_failure (snapshot : GeneralPremise.ProviderSnapshot)
    (meaning : ProviderMeaning (patterns program) snapshot) : failureRow 1 (number 42) ∉ snapshot.rows := by
  intro cached
  have failed := meaning.2 1 .bind (number 42) (by rfl) cached
  cases failed

#print axioms ordered_fallthrough_has_actual_path
#print axioms successful_clause_cannot_be_cached_as_failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.SelectionControls
