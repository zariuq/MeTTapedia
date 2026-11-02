import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClassPatternFailure
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueReading
import Mettapedia.OSLF.MeTTaIL.ProviderAppend

/-! Failure-cache rows carry source meaning independently of provider row
typing. Appending a row for an actually failed pattern preserves that
meaning, including when another request later reuses the cached answer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def failureRow (index : Nat) (argument : OCaml.Value) : GeneralPremise.ProviderRow :=
  ⟨"ml-pattern-failure", [patternId index, value argument]⟩

def FailureRowsSound (pool : List OCaml.MatchPattern) (snapshot : GeneralPremise.ProviderSnapshot) : Prop :=
  ∀ index parameter argument, pool[index]? = some parameter →
    failureRow index argument ∈ snapshot.rows → OCaml.matchPattern parameter argument = none

theorem patternId_injective : Function.Injective patternId := by
  intro first second same
  have equal := (List.cons.inj (Pattern.apply.inj same).2).1
  exact digits_injective equal

theorem failureRow_injective {first second : Nat} {left right : OCaml.Value}
    (same : failureRow first left = failureRow second right) : first = second ∧ left = right := by
  have valuesSame := congrArg GeneralPremise.ProviderRow.values same
  have parts := List.cons.inj valuesSame
  exact ⟨patternId_injective parts.1, value_injective (List.cons.inj parts.2).1⟩

theorem initial_failure_rows_sound (pool : List OCaml.MatchPattern) : FailureRowsSound pool provider := by
  intro index parameter argument indexed present
  cases present

theorem append_failure_sound (pool : List OCaml.MatchPattern) (snapshot : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (sound : FailureRowsSound pool snapshot) (indexed : pool[index]? = some parameter)
    (failed : OCaml.matchPattern parameter argument = none) :
    FailureRowsSound pool (GeneralPremise.ProviderAppend.appendRows snapshot [failureRow index argument]) := by
  intro other otherParameter otherArgument selected present
  rcases (GeneralPremise.ProviderAppend.row_membership snapshot [failureRow index argument] (failureRow other otherArgument)).mp present
      with old | fresh
  · exact sound other otherParameter otherArgument selected old
  · have same := List.mem_singleton.mp fresh
    obtain ⟨rfl, rfl⟩ := failureRow_injective same
    have parameterSame := Option.some.inj (selected.symm.trans indexed)
    subst otherParameter
    exact failed

theorem cached_failure_authorized (pool : List OCaml.MatchPattern) (snapshot : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation)
    (sound : FailureRowsSound pool snapshot) (indexed : pool[index]? = some parameter)
    (cached : failureRow index argument ∈ snapshot.rows) :
    OCaml.enterBody parameter argument body capturedEnvironment rest = .halted (.error .matchFailure) := by
  simp only [OCaml.enterBody, sound index parameter argument indexed cached]

#print axioms failureRow_injective
#print axioms initial_failure_rows_sound
#print axioms append_failure_sound
#print axioms cached_failure_authorized

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
