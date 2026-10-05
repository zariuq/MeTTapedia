import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramExtension

/-!
# Dispatching new equations in an extended program

The new component's equations are selected locally, while their bodies execute
in the whole composed program. They may therefore call the preceding component.
Disjointness protects the new heads from earlier definitions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

theorem DispatchAgreement.suffix (preceding addition : Program)
    (disjoint : ∀ equation ∈ addition, equation.head ∉ preceding.calledHeads) :
    DispatchAgreement addition (preceding ++ addition) (addition.map Equation.head) := by
  have undefined (head : String) (used : head ∈ addition.map Equation.head) :
      preceding.defines head = false := by
    obtain ⟨new, member, rfl⟩ := List.mem_map.mp used
    simp only [Program.defines, List.any_eq_false]
    intro old oldMember
    have different : old.head ≠ new.head := fun same =>
      disjoint new member (same ▸ Program.calledHeads_head oldMember)
    simp [different]
  constructor
  · intro head used arity
    simp only [Program.definesAt, List.any_append]
    change addition.definesAt head arity = (preceding.definesAt head arity || addition.definesAt head arity)
    rw [Program.definesAt_false_of_defines_false (undefined head used) arity, Bool.false_or]
  · intro head used
    simp only [Program.defines, List.any_append]
    change addition.defines head = (preceding.defines head || addition.defines head)
    rw [undefined head used, Bool.false_or]
  · intro head used arguments
    simp only [Program.select, List.findSome?_append]
    change addition.select head arguments = (preceding.select head arguments).or (addition.select head arguments)
    rw [Program.select_none_of_undefined (undefined head used) arguments, Option.none_or]

theorem Applies.suffix_equation {preceding addition : Program} {host : Host}
    (disjoint : ∀ equation ∈ addition, equation.head ∉ preceding.calledHeads)
    {head : String} {arguments : List Term} {equation : Equation} {environment : Env} {result : Term}
    (used : head ∈ addition.map Equation.head)
    (defined : addition.definesAt head arguments.length = true)
    (selected : addition.select head arguments = some (equation, environment))
    (body : Evaluates (preceding ++ addition) host environment equation.body result) :
    Applies (preceding ++ addition) host head arguments result := by
  have dispatch := DispatchAgreement.suffix preceding addition disjoint
  exact Applies.equation ((dispatch.definesAt head used _).symm.trans defined)
    ((dispatch.select head used _).symm.trans selected) body

theorem apply_suffix_eq (preceding addition : Program) (host : Host)
    (disjoint : ∀ equation ∈ addition, equation.head ∉ preceding.calledHeads)
    (head : String) (used : head ∈ addition.map Equation.head) (fuel : Nat) (arguments : List Term) :
    apply (preceding ++ addition) host fuel head arguments =
      applyWith addition host (eval (preceding ++ addition) host fuel) head arguments := by
  have dispatch := DispatchAgreement.suffix preceding addition disjoint
  change applyWith (preceding ++ addition) host _ _ _ = _
  simp only [applyWith, ← dispatch.definesAt head used arguments.length,
    ← dispatch.defines head used, ← dispatch.select head used arguments]

namespace ProgramSuffixControls

private def base : Program := [⟨"old", "old", [], .sym "answer"⟩]
private def addition : Program := [⟨"new", "new", [], .expr [.sym "old"]⟩]
private def host : Host := ⟨fun _ _ => .unhandled⟩

theorem new_body_can_call_the_old_component :
    apply (base ++ addition) host 2 "new" [] = .value (.sym "answer") := rfl

theorem isolated_new_component_does_not_perform_that_call :
    apply addition host 2 "new" [] = .value (.expr [.sym "old"]) := rfl

end ProgramSuffixControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
