import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunAdmissionJoin

/-!
# Selected scalar-source paths and the loaded HOL run predicate

Source paths retain their parses, routing and authored execution evidence.
Their erasures execute through the loaded admission and path predicates in
one received model. Reflection requires the fixed parse policy's canonical
coverage; it does not impose determinism on the grammar or erase source data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.HOLRuns

open Interface Source Payloads OccurrenceProfile
open Mettapedia.Languages.OpenTheory
open HOLPreparedRunEncoding HOLRunSpecialization

variable (label : Nat → Term) (decision : Decisions (effect label) (admission label))
  (input : HOLRunAdmissionJoin.Input) (other : TypeFamilySemantics.OperatorFamilies.{0})
  (prior : TypeFamilySemantics.Assignment.{0})

noncomputable def accepts (events : List (RawEvent (effect label))) (source target : State) : Prop :=
  (input.operations.signature.pathValue (input.model (effect label) other prior)
    (input.admittedValue (effect label) other prior (admission label))
    (wordValue (effect label) _ _ (input.runCoding (effect label) other prior)
      (input.runAgreement (effect label) other prior) events)
    ((input.runCoding (effect label) other prior).states.symm (some source))
    ((input.runCoding (effect label) other prior).states.symm (some target))).down

theorem preserves {keep : ParsePolicy} {source target : Source.Object label decision keep}
    (path : Quiver.Path source target) :
    accepts label input other prior
      (word (effect label) (admission label) ((erase label decision keep).mapPath path))
      source.state target.state :=
  (input.admitted_path_iff (effect label) other prior (admission label) _ source.state target.state).mpr
    ⟨(erase label decision keep).mapPath path, rfl⟩

theorem reflects {keep : ParsePolicy} (coverage : CanonicalCoverage label keep)
    (source : Source.Object label decision keep) (target : State)
    (events : List (RawEvent (effect label)))
    (accepted : accepts label input other prior events source.state target) :
    ∃ lifted : (destination : Source.Object label decision keep) × Quiver.Path source destination,
      ((erase label decision keep).pathStar source lifted).1 = target ∧
      word (effect label) (admission label) ((erase label decision keep).pathStar source lifted).2 = events := by
  obtain ⟨path, words⟩ :=
    (input.admitted_path_iff (effect label) other prior (admission label) events source.state target).mp accepted
  obtain ⟨lifted, same⟩ := erase_paths_surjective label decision coverage source ⟨target, path⟩
  refine ⟨lifted, ?_, ?_⟩
  · exact congrArg Sigma.fst same
  · have mapped := congrArg
      (fun run : (destination : EffectCore.EventObject (effect label) (admission label)) ×
          @Quiver.Path (EffectCore.EventObject (effect label) (admission label)) _ source.state destination =>
            word (effect label) (admission label) run.2) same
    exact mapped.trans words

theorem all_parses_reflects (source : Source.Object label decision allParses) (target : State)
    (events : List (RawEvent (effect label)))
    (accepted : accepts label input other prior events source.state target) :
    ∃ lifted : (destination : Source.Object label decision allParses) × Quiver.Path source destination,
      ((erase label decision allParses).pathStar source lifted).1 = target ∧
      word (effect label) (admission label) ((erase label decision allParses).pathStar source lifted).2 = events :=
  reflects label decision input other prior (allParses_coverage label) source target events accepted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.HOLRuns
