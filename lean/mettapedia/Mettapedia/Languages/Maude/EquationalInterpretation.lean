import Mettapedia.Languages.Maude.HookedEquivalence

/-! Many-sorted interpretations for ordinary and imported Maude equations.
Soundness is proved by mutual induction over equality and its conditional
premises; it does not assume that the premise producer is already sound. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude

structure EquationalInterpretation (signature : Signature) where
  Value : Type
  finish : String → List (Option Value) → Option Value
  Fits : Option Value → String → Prop
  operation_sorted : ∀ declaration ∈ signature.operators, ∀ arguments,
    List.Forall₂ Fits arguments declaration.arguments → Fits (finish declaration.id arguments) declaration.result

namespace EquationalInterpretation

variable {signature : Signature}

def evaluate (model : EquationalInterpretation signature) (assignment : String → Option model.Value) :
    Term → Option model.Value
  | .var name => assignment name
  | .app label arguments => model.finish label (arguments.map (model.evaluate assignment))

def SortedAssignment (model : EquationalInterpretation signature) (context : VariableContext)
    (assignment : String → Option model.Value) : Prop :=
  ∀ name sort, context.lookup name = some sort → model.Fits (assignment name) sort

theorem evaluate_sorted (model : EquationalInterpretation signature)
    {context : VariableContext} {assignment : String → Option model.Value}
    (assigned : model.SortedAssignment context assignment) {source : Term} {sort : String}
    (typed : HasSort signature context source sort) : model.Fits (model.evaluate assignment source) sort := by
  refine HasSort.rec
    (motive_1 := fun source sort _ => model.Fits (model.evaluate assignment source) sort)
    (motive_2 := fun sources sorts _ => List.Forall₂ model.Fits
      (sources.map (model.evaluate assignment)) sorts)
    ?_ ?_ ?_ ?_ typed
  · intro name sort found
    simpa only [evaluate] using assigned name sort found
  · intro declaration arguments member _ ih
    simpa only [evaluate] using model.operation_sorted declaration member _ ih
  · exact .nil
  · intro first sort rest sorts _ _ firstIH restIH
    exact .cons firstIH restIH

theorem evaluate_substitute (model : EquationalInterpretation signature)
    (assignment : String → Option model.Value) (replacement : Valuation) (source : Term) :
    model.evaluate assignment (source.substitute replacement) =
      model.evaluate (fun name => model.evaluate assignment (replacement name)) source := by
  refine Term.rec
    (motive_1 := fun source => model.evaluate assignment (source.substitute replacement) =
      model.evaluate (fun name => model.evaluate assignment (replacement name)) source)
    (motive_2 := fun sources => sources.map (fun source => model.evaluate assignment (source.substitute replacement)) =
      sources.map (model.evaluate (fun name => model.evaluate assignment (replacement name))))
    ?_ ?_ ?_ ?_ source
  · intro name
    simp only [Term.substitute, evaluate]
  · intro label arguments ih
    simpa only [Term.substitute, evaluate, List.map_map, Function.comp_def] using congrArg (model.finish label) ih
  · rfl
  · intro first rest firstIH restIH
    simp only [List.map_cons, firstIH, restIH]

theorem evaluate_frame (model : EquationalInterpretation signature)
    {context : VariableContext} {hole result : String}
    (frame : ArgumentContext signature context hole result)
    (assignment : String → Option model.Value) {source target : Term}
    (same : model.evaluate assignment source = model.evaluate assignment target) :
    model.evaluate assignment (frame.plug source) = model.evaluate assignment (frame.plug target) := by
  simp only [ArgumentContext.plug, evaluate, List.map_append, List.map_cons, same]

end EquationalInterpretation

structure EquationModel (theory : Theory) (hook : EquationHook)
    extends EquationalInterpretation theory.signature where
  algebra_sound : ∀ {context sort source target}, AlgebraStep theory.signature context sort source target →
    ∀ assignment, toEquationalInterpretation.SortedAssignment context assignment →
    toEquationalInterpretation.evaluate assignment source = toEquationalInterpretation.evaluate assignment target
  equation_sound : ∀ row ∈ theory.equations, ∀ assignment,
    toEquationalInterpretation.SortedAssignment row.usedContext assignment →
    (∀ condition ∈ row.conditions,
      toEquationalInterpretation.evaluate assignment condition.left =
        toEquationalInterpretation.evaluate assignment condition.right) →
    toEquationalInterpretation.evaluate assignment row.left = toEquationalInterpretation.evaluate assignment row.right
  hook_sound : ∀ {context sort source target}, hook context sort source target →
    ∀ assignment, toEquationalInterpretation.SortedAssignment context assignment →
    toEquationalInterpretation.evaluate assignment source = toEquationalInterpretation.evaluate assignment target

theorem EquationModel.sound {theory : Theory} {hook : EquationHook}
    (model : EquationModel theory hook) {context : VariableContext} {sort : String} {source target : Term}
    (equivalent : HookedEquivalent theory hook context sort source target)
    (assignment : String → Option model.Value)
    (assigned : model.toEquationalInterpretation.SortedAssignment context assignment) :
    model.toEquationalInterpretation.evaluate assignment source =
      model.toEquationalInterpretation.evaluate assignment target := by
  let interpretation := model.toEquationalInterpretation
  refine HookedEquivalent.rec
    (motive_1 := fun _ source target _ =>
      interpretation.evaluate assignment source = interpretation.evaluate assignment target)
    (motive_2 := fun replacement conditions _ => ∀ condition ∈ conditions,
      interpretation.evaluate assignment (condition.left.substitute replacement) =
        interpretation.evaluate assignment (condition.right.substitute replacement))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intro _ _ _
    rfl
  · intro _ _ _ _ ih
    exact ih.symm
  · intro _ _ _ _ _ _ first last
    exact first.trans last
  · intro _ _ frame _ _ _ ih
    exact interpretation.evaluate_frame frame assignment ih
  · intro _ _ _ step
    exact model.algebra_sound step assignment assigned
  · intro row _ replacement member _ _ _ typed _ conditions
    rw [interpretation.evaluate_substitute, interpretation.evaluate_substitute]
    apply model.equation_sound row member
    · intro name sort found
      exact interpretation.evaluate_sorted assigned (typed name sort found)
    · intro condition inside
      simpa only [interpretation.evaluate_substitute] using conditions condition inside
  · intro _ _ _ _ _ step
    exact model.hook_sound step assignment assigned
  · intro replacement condition impossible
    cases impossible
  · intro replacement condition rest sort _ _ first restIH actual member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact restIH actual member

end Mettapedia.Languages.Maude
