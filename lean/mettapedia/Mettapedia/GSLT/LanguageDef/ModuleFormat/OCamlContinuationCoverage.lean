import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternPool
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlStateClosed

/-! A continuation carries patterns declared by the prepared program pool.
That syntactic coverage is sufficient for total compact state encoding; it
does not assume a successful target run or an evaluation result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def FrameCovered (pool : List OCaml.MatchPattern) : OCaml.Frame → Prop
  | .letValue parameter _ _ => parameter ∈ pool
  | .matchValue clauses _ => ∀ clause ∈ clauses, clause.pattern ∈ pool
  | _ => True

def ContinuationCovered (pool : List OCaml.MatchPattern) (rest : OCaml.Continuation) : Prop :=
  ∀ frame ∈ rest, FrameCovered pool frame

def StateCovered (pool : List OCaml.MatchPattern) : OCaml.MachineState → Prop
  | .evaluate _ _ rest | .returned _ rest => ContinuationCovered pool rest
  | .halted _ => True

theorem frame?_exists (pool : List OCaml.MatchPattern) (frame : OCaml.Frame) (rest : Pattern)
    (covered : FrameCovered pool frame) : ∃ encoded, frame? pool frame rest = some encoded := by
  cases frame with
  | letValue parameter body captured =>
      obtain ⟨patternCode, referenced⟩ := patternReference?_exists covered
      exact ⟨node "MlKLet" [patternCode, code body, environment captured, rest],
        by simp only [frame?, referenced, Option.bind_eq_bind, Option.bind_some, Option.pure_def]⟩
  | matchValue clauses captured =>
      obtain ⟨clauseCode, referenced⟩ := clauseList?_exists clauses covered
      exact ⟨node "MlKMatch" [clauseCode, environment captured, rest],
        by simp only [frame?, referenced, Option.bind_eq_bind, Option.bind_some, Option.pure_def]⟩
  | _ => exact ⟨_, rfl⟩

theorem continuation?_exists (pool : List OCaml.MatchPattern) (rest : OCaml.Continuation)
    (covered : ContinuationCovered pool rest) : ∃ encoded, continuation? pool rest = some encoded := by
  induction rest with
  | nil => exact ⟨_, rfl⟩
  | cons frame rest ih =>
      obtain ⟨tail, tailResolved⟩ := ih (fun child present => covered child (List.mem_cons_of_mem frame present))
      obtain ⟨encoded, frameResolved⟩ := frame?_exists pool frame tail (covered frame List.mem_cons_self)
      exact ⟨encoded, by simp only [continuation?, tailResolved, Option.bind_eq_bind, Option.bind_some, frameResolved]⟩

theorem state?_exists (pool : List OCaml.MatchPattern) (state : OCaml.MachineState)
    (covered : StateCovered pool state) : ∃ encoded, state? pool state = some encoded := by
  cases state with
  | evaluate reference captured rest =>
      obtain ⟨tail, resolved⟩ := continuation?_exists pool rest covered
      exact ⟨node "MlEvaluate" [code reference, environment captured, tail],
        by simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]⟩
  | returned actual rest =>
      obtain ⟨tail, resolved⟩ := continuation?_exists pool rest covered
      exact ⟨node "MlReturn" [value actual, tail],
        by simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]⟩
  | halted result => cases result <;> exact ⟨_, rfl⟩

theorem initial_covered (program : OCaml.Program) : StateCovered (patterns program) (OCaml.begin program) := by
  intro frame member
  cases member

#print axioms state?_exists

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
