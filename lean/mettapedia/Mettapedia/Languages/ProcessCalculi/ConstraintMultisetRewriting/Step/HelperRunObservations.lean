import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorInterchange

/-!
# Declaration-shape observations of actual helper executions

Frame transport can change a term's declaration names and physical occurrence
names. It preserves the ordered input/output sorts of every helper. This
observation therefore compares histories without assuming any identity
normalization of the native result isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

def helperWord {source : State S O} (run : helperStep.Run source) : List (MetaArity S) :=
  run.word.map (fun entry => entry.2.helper)

theorem helperWord_append {source : State S O} (run : helperStep.Run source) (later : helperStep.Run run.last) :
    helperWord (run.append later) = helperWord run ++ helperWord later := by
  simp only [helperWord, Step.Run.word_append, List.map_append]

theorem similar_helperWord : ∀ {source target : State S O} {first : helperStep.Run source} {second : helperStep.Run target},
    helperTransport.Similar first second → helperWord first = helperWord second
  | _, _, .nil _, .nil _, _ => rfl
  | _, _, .nil _, .cons _ _ _, impossible => False.elim impossible
  | _, _, .cons _ _ _, .nil _, impossible => False.elim impossible
  | _, _, .cons f _ rest, .cons g _ later, related => by
      obtain ⟨_iso, same, related⟩ := related
      have head := congrArg Firing.helper same
      change f.helper = g.helper at head
      change f.helper :: helperWord rest = g.helper :: helperWord later
      rw [head, similar_helperWord related]

theorem helperWord_moveRun {source target : State S O} (iso : helperTransport.Iso source target)
    (run : helperStep.Run source) : helperWord (helperTransport.moveRun iso run) = helperWord run :=
  (similar_helperWord (Transport.Similar.moveRun iso run)).symm

theorem RebasePlan.helperWord_eq : ∀ {left right : State S O} (place : ContextPlacement left right)
    (run : helperStep.Run left) (plan : RebasePlan S O place run),
    helperWord (RebasePlan.realize place run plan).execution = helperWord run
  | _, _, _, .nil _, .nil _ => rfl
  | _, _, place, .cons f allowed rest, .cons _ _ tail => by
      change f.helper :: helperWord (helperTransport.moveRun (helperTransport.symm (place.left_result_iso f))
        (RebasePlan.realize (place.afterLeft f) rest tail).execution) = f.helper :: helperWord rest
      rw [helperWord_moveRun, RebasePlan.helperWord_eq]

theorem TensorPlan.helperWord_eq {left right : State S O} {place : ContextPlacement left right}
    {first : helperStep.Run left} {second : helperStep.Run right} (plan : TensorPlan place first second) :
    helperWord (TensorPlan.realize plan).execution = helperWord first ++ helperWord second := by
  change helperWord ((RebasePlan.realize place first plan.leftPlan).execution.append _) = _
  rw [helperWord_append, helperWord_moveRun]
  exact congrArg₂ List.append (RebasePlan.helperWord_eq place first plan.leftPlan)
    (RebasePlan.helperWord_eq (RebasePlan.realize place first plan.leftPlan).target.swap second plan.rightPlan)

theorem TensorPlan.sequential_helperWord {left right : State S O} {place : ContextPlacement left right}
    {first : helperStep.Run left} {second : helperStep.Run right}
    {afterFirst : helperStep.Run first.last} {afterSecond : helperStep.Run second.last}
    (before : TensorPlan place first second)
    (after : TensorPlan (TensorPlan.realize before).target afterFirst afterSecond) :
    helperWord (before.sequentialExecution after) =
      (helperWord first ++ helperWord second) ++ (helperWord afterFirst ++ helperWord afterSecond) := by
  rw [TensorPlan.sequentialExecution, helperWord_append, helperWord_moveRun,
    TensorPlan.helperWord_eq, TensorPlan.helperWord_eq]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
