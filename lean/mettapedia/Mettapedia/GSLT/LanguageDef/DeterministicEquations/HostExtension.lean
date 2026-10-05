import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramExtension

/-!
# Primitive-catalogue agreement on a program's calls

A larger primitive catalogue preserves an existing computation when it agrees
on every primitive or constructor call reachable from the authored program.
The comparison preserves every outcome at every fuel, including faults and
exhaustion. Bound values are not recursively executed when they are read.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

def Host.AgreesOn (source target : Host) (heads : List String) : Prop :=
  ∀ head ∈ heads, ∀ arguments, source.primitive head arguments = target.primitive head arguments

private theorem items_eq_on {ev ev' : Env → Term → Outcome} {environment : Env} (items : List Term)
    (equal : ∀ item ∈ items, ev environment item = ev' environment item) :
    evalItemsWith ev environment items = evalItemsWith ev' environment items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp only [evalItemsWith, equal first (List.mem_cons_self ..)]
      rw [ih (fun item member => equal item (List.mem_cons_of_mem _ member))]

theorem eval_host_eq (program : Program) {source target : Host} {heads : List String}
    (hosts : source.AgreesOn target heads)
    (closed : ∀ equation ∈ program, CallsWithin heads equation.body)
    (fuel : Nat) (environment : Env) (term : Term) (confined : CallsWithin heads term) :
    eval program source fuel environment term = eval program target fuel environment term := by
  induction fuel generalizing environment term with
  | zero => rfl
  | succ fuel ih =>
      have callEqual (head : String) (used : head ∈ heads) (arguments : List Term) :
          apply program source fuel head arguments = apply program target fuel head arguments := by
        unfold apply applyWith
        split
        · cases selected : program.select head arguments with
          | none => rfl
          | some pair => exact ih pair.2 pair.1.body (closed pair.1 (Program.selected_mem selected))
        · rw [hosts head used arguments]
      rw [eval, eval]
      cases term with
      | var _ => rfl
      | sym _ => rfl
      | lit _ => rfl
      | list items =>
          have same := items_eq_on items (fun item member => ih environment item (confined.list_child member))
          simp only [evalStep, same]
      | expr items =>
          unfold evalStep
          split
          · rename_i _ _ impossible
            cases impossible
          · rename_i _ _ impossible
            cases impossible
          · rename_i _ _ impossible
            cases impossible
          · rename_i _ _ impossible
            cases impossible
          · rfl
          · rename_i _ name value body same
            have equalItems := Term.expr.inj same
            subst items
            rw [ih environment value (confined.expr_child (by simp))]
            split
            · exact ih _ body (confined.expr_child (by simp))
            · rfl
          · rfl
          · rfl
          · rfl
          · rename_i _ head arguments _ _ _ _ same
            have equalItems := Term.expr.inj same
            subst items
            rw [items_eq_on arguments (fun item member =>
              ih environment item (confined.expr_child (List.mem_cons_of_mem _ member)))]
            split
            · exact callEqual head confined.head _
            · rfl
          · rename_i _ terms _ _ _ _ _ _ same
            have equalItems := Term.expr.inj same
            subst items
            rw [items_eq_on terms (fun item member => ih environment item (confined.expr_child member))]

theorem apply_host_eq (program : Program) {source target : Host}
    (hosts : source.AgreesOn target program.calledHeads)
    (fuel : Nat) (head : String) (used : head ∈ program.calledHeads) (arguments : List Term) :
    apply program source fuel head arguments = apply program target fuel head arguments := by
  unfold apply applyWith
  split
  · cases selected : program.select head arguments with
    | none => rfl
    | some pair =>
      exact eval_host_eq program hosts (fun _ member => Program.calledHeads_body member)
        fuel pair.2 pair.1.body (Program.calledHeads_body (Program.selected_mem selected))
  · rw [hosts head used arguments]

theorem Applies.host_iff (program : Program) {source target : Host}
    (hosts : source.AgreesOn target program.calledHeads)
    (head : String) (used : head ∈ program.calledHeads) (arguments : List Term) (result : Term) :
    Applies program source head arguments result ↔ Applies program target head arguments result := by
  unfold Applies
  simp only [apply_host_eq program hosts _ head used arguments]

namespace HostExtensionControls

private def sourceHost : Host := ⟨fun _ _ => .unhandled⟩
private def extraHost : Host := ⟨fun head _ => if head = "new" then .value (.sym "new-result") else .unhandled⟩
private def capturedHost : Host := ⟨fun head _ => if head = "old-data" then .fault else .unhandled⟩
private def program : Program := [⟨"old", "old", [], .expr [.sym "old-data"]⟩]

theorem unrelated_primitive_preserves_call (fuel : Nat) :
    apply program sourceHost fuel "old" [] = apply program extraHost fuel "old" [] := by
  apply apply_host_eq program (head := "old")
  · intro head used arguments
    have cases' : head = "old" ∨ head = "old-data" := by
      simpa [Program.calledHeads, program, calledHeads, calledHeadsList] using used
    rcases cases' with rfl | rfl <;> rfl
  · decide

theorem claiming_a_constructor_changes_the_result :
    apply program sourceHost 2 "old" [] = .value (.expr [.sym "old-data"]) ∧
      apply program capturedHost 2 "old" [] = .failure := by constructor <;> rfl

theorem capturing_host_does_not_agree : ¬ sourceHost.AgreesOn capturedHost program.calledHeads := by
  intro agreement
  have impossible := agreement "old-data" (by decide) []
  cases impossible

end HostExtensionControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
