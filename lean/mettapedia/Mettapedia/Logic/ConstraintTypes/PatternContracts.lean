import Mettapedia.Logic.ConstraintTypes.CheckingPatterns
import Mettapedia.Logic.ConstraintTypes.CallTyping

/-!
# Predicate boundaries with checking patterns

Evaluation policy belongs to inputs. Results have a checking pattern and no
staging switch. One proper-type assignment is shared by the entire signature;
explicit wildcards do not enlarge that assignment's universe. The compiler and
ordered execution use the existing scoped constraints and boundary trace model.
Weakening statements fix the body, source arity and prepared argument values;
they preserve argument modes. They do not compare hold with evaluate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.PatternContracts

open SymbolicTypes ScopedConstraints CheckingPatterns

variable {Kind : Type} {sig : CheckingPatterns.Signature Kind} {Carrier : Kind → Type}
  {Context P Q C : Type} {typeArity : C → Nat} {valueKind : Kind} {n : Nat}

structure Input (sig : CheckingPatterns.Signature Kind) (P Q C : Type) (typeArity : C → Nat)
    (valueKind : Kind) where
  evaluation : CallTyping.Evaluation
  check : Pattern sig P Q C typeArity valueKind

abbrev Declaration (sig : CheckingPatterns.Signature Kind) (P Q C : Type) (typeArity : C → Nat)
    (valueKind : Kind) (arity : Nat) :=
  CallTyping.Signature (Input sig P Q C typeArity valueKind) (Pattern sig P Q C typeArity valueKind) arity

def argumentPlan (inputs : List (Input sig P Q C typeArity valueKind)) : CallTyping.Evaluation :=
  if inputs.isEmpty then .evaluate
  else if inputs.all (fun input => input.evaluation == .hold) then .hold else .evaluate

def Input.substitute {X : Type} (substitution : P → Expr X Q C typeArity)
    (input : Input sig P Q C typeArity valueKind) : Input sig X Q C typeArity valueKind :=
  ⟨input.evaluation, input.check.substitute substitution⟩

theorem substitution_preserves_argument_plan {X : Type} (substitution : P → Expr X Q C typeArity)
    (inputs : List (Input sig P Q C typeArity valueKind)) :
    argumentPlan (inputs.map (Input.substitute substitution)) = argumentPlan inputs := by
  simp [argumentPlan, Input.substitute, List.all_map, Function.comp_def]

def inputProblems [DecidableEq P] (model : Model sig Carrier Context Q C typeArity)
    (compiler : Compiler model) (context : Context) (arguments : Fin n → Carrier valueKind)
    (declaration : Declaration sig P Q C typeArity valueKind n) : List (Problem P Q C typeArity) :=
  combinations ((List.finRange n).map fun i => compile model compiler (declaration.input i).check context (arguments i))

theorem inputProblems_correct [DecidableEq P] (model : Model sig Carrier Context Q C typeArity)
    (compiler : Compiler model) (context : Context) (arguments : Fin n → Carrier valueKind)
    (declaration : Declaration sig P Q C typeArity valueKind n) (parameters : P → Closed Q C typeArity) :
    alternativesSatisfy (inputProblems model compiler context arguments declaration) parameters ↔
      ∀ i, Matches model parameters (declaration.input i).check context (arguments i) := by
  rw [inputProblems, satisfies_combinations]
  constructor
  · intro all i
    exact (compile_correct _ _ _ _ _ _).1 (all _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
  · intro all choice present
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 present
    exact (compile_correct _ _ _ _ _ _).2 (all i)

abbrev Frame (sig : CheckingPatterns.Signature Kind) (P Q C : Type) (typeArity : C → Nat)
    (valueKind : Kind) (arity : Nat) :=
  List (Declaration sig P Q C typeArity valueKind arity × Problem P Q C typeArity)

def prepare [DecidableEq P] (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (context : Context) (arguments : Fin n → Carrier valueKind)
    (declarations : List (Declaration sig P Q C typeArity valueKind n)) : Frame sig P Q C typeArity valueKind n :=
  declarations.flatMap fun declaration =>
    (inputProblems model compiler context arguments declaration).map fun evidence => (declaration, evidence)

def finishProblems [DecidableEq P] (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (context : Context) (value : Carrier valueKind) (frame : Frame sig P Q C typeArity valueKind n) :
    List (Problem Empty Q C typeArity) :=
  frame.flatMap fun candidate => (compile model compiler candidate.1.output context value).map fun result =>
    close (conjunction candidate.2 result)

def AdmitsInput (model : Model sig Carrier Context Q C typeArity) (context : Context)
    (arguments : Fin n → Carrier valueKind) (declarations : List (Declaration sig P Q C typeArity valueKind n)) : Prop :=
  ∃ declaration ∈ declarations, ∃ parameters : P → Closed Q C typeArity,
    ∀ i, Matches model parameters (declaration.input i).check context (arguments i)

def Allowed (model : Model sig Carrier Context Q C typeArity) (before after : Context)
    (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (declarations : List (Declaration sig P Q C typeArity valueKind n)) : Prop :=
  ∃ declaration ∈ declarations, ∃ parameters : P → Closed Q C typeArity,
    (∀ i, Matches model parameters (declaration.input i).check before (arguments i)) ∧
      Matches model parameters declaration.output after value

theorem frame_exact [DecidableEq P] (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (before after : Context) (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (declarations : List (Declaration sig P Q C typeArity valueKind n)) :
    alternativesSatisfy (finishProblems model compiler after value (prepare model compiler before arguments declarations))
      Empty.elim ↔ Allowed model before after arguments value declarations := by
  constructor
  · rintro ⟨problem, present, solved⟩
    obtain ⟨⟨declaration, evidence⟩, member, selected⟩ := List.mem_flatMap.1 present
    obtain ⟨actual, declared, prepared⟩ := List.mem_flatMap.1 member
    obtain ⟨input, inputMember, same⟩ := List.mem_map.1 prepared
    cases same
    obtain ⟨result, resultMember, same⟩ := List.mem_map.1 selected
    subst problem
    obtain ⟨parameters, joint⟩ := (satisfies_close _).1 solved
    obtain ⟨inputs, output⟩ := (satisfies_conjunction _ _ _).1 joint
    exact ⟨declaration, declared, parameters, (inputProblems_correct _ _ _ _ _ _).1 ⟨evidence, inputMember, inputs⟩,
      (compile_correct _ _ _ _ _ _).1 ⟨result, resultMember, output⟩⟩
  · rintro ⟨declaration, declared, parameters, inputs, output⟩
    obtain ⟨input, inputMember, checkedInputs⟩ := (inputProblems_correct _ _ _ _ _ _).2 inputs
    obtain ⟨result, resultMember, checkedOutput⟩ := (compile_correct _ _ _ _ _ _).2 output
    refine ⟨close (conjunction input result), List.mem_flatMap.2 ⟨(declaration,input), ?_, ?_⟩, ?_⟩
    · exact List.mem_flatMap.2 ⟨declaration, declared, List.mem_map.2 ⟨input,inputMember,rfl⟩⟩
    · exact List.mem_map.2 ⟨result,resultMember,rfl⟩
    · exact (satisfies_close _).2 ⟨parameters,(satisfies_conjunction _ _ _).2 ⟨checkedInputs,checkedOutput⟩⟩

def entryAccepted [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (frame : Frame sig P Q C typeArity valueKind n) : Bool := accept (frame.map fun candidate => close candidate.2)

def resultAccepted [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (context : Context) (value : Carrier valueKind) (frame : Frame sig P Q C typeArity valueKind n) : Bool :=
  accept (finishProblems model compiler context value frame)

theorem entryAccepted_iff [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity) (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (context : Context) (arguments : Fin n → Carrier valueKind)
    (declarations : List (Declaration sig P Q C typeArity valueKind n)) :
    entryAccepted (prepare model compiler context arguments declarations) = true ↔
      AdmitsInput model context arguments declarations := by
  rw [entryAccepted,accept_closed_iff seed]
  constructor
  · rintro ⟨problem, present, solved⟩
    obtain ⟨⟨declaration,evidence⟩,member,same⟩ := List.mem_map.1 present
    subst problem
    obtain ⟨actual,declared,selected⟩ := List.mem_flatMap.1 member
    obtain ⟨input,inputMember,same⟩ := List.mem_map.1 selected
    cases same
    obtain ⟨parameters,checked⟩ := (satisfies_close _).1 solved
    exact ⟨declaration,declared,parameters,(inputProblems_correct _ _ _ _ _ _).1 ⟨evidence,inputMember,checked⟩⟩
  · rintro ⟨declaration,declared,parameters,all⟩
    obtain ⟨input,inputMember,checked⟩ := (inputProblems_correct _ _ _ _ _ _).2 all
    refine ⟨close input,List.mem_map.2 ⟨(declaration,input),?_,rfl⟩,?_⟩
    · exact List.mem_flatMap.2 ⟨declaration,declared,List.mem_map.2 ⟨input,inputMember,rfl⟩⟩
    · exact (satisfies_close _).2 ⟨parameters,checked⟩

theorem resultAccepted_iff [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity) (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (before after : Context) (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (declarations : List (Declaration sig P Q C typeArity valueKind n)) :
    resultAccepted model compiler after value (prepare model compiler before arguments declarations) = true ↔
      Allowed model before after arguments value declarations := by
  rw [resultAccepted,accept_closed_iff seed]
  exact frame_exact _ _ _ _ _ _ _

def Relaxed (strong weak : Declaration sig P Q C typeArity valueKind n) : Prop :=
  (∀ i, (strong.input i).evaluation = (weak.input i).evaluation) ∧
  (∀ i, Weakens (strong.input i).check (weak.input i).check) ∧ Weakens strong.output weak.output

theorem weakening_preserves_same_call_witness (model : Model sig Carrier Context Q C typeArity)
    (before after : Context) (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (strong weak : Declaration sig P Q C typeArity valueKind n) (relaxed : Relaxed strong weak)
    (parameters : P → Closed Q C typeArity)
    (inputs : ∀ i, Matches model parameters (strong.input i).check before (arguments i))
    (output : Matches model parameters strong.output after value) :
    (∀ i, Matches model parameters (weak.input i).check before (arguments i)) ∧
      Matches model parameters weak.output after value :=
  ⟨fun i => weakening_preserves_witness model parameters (relaxed.2.1 i) before (arguments i) (inputs i),
    weakening_preserves_witness model parameters relaxed.2.2 after value output⟩

theorem weakening_preserves_admitted_answers (model : Model sig Carrier Context Q C typeArity)
    (before after : Context) (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (strong weak : List (Declaration sig P Q C typeArity valueKind n))
    (relaxed : ∀ declaration ∈ strong, ∃ replacement ∈ weak, Relaxed declaration replacement) :
    Allowed model before after arguments value strong → Allowed model before after arguments value weak := by
  rintro ⟨declaration,present,parameters,inputs,output⟩
  obtain ⟨replacement,member,weakens⟩ := relaxed declaration present
  exact ⟨replacement,member,parameters,weakening_preserves_same_call_witness
    model before after arguments value declaration replacement weakens parameters inputs output⟩

theorem declaration_membership_preserves_allowed (model : Model sig Carrier Context Q C typeArity)
    (before after : Context) (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (left right : List (Declaration sig P Q C typeArity valueKind n))
    (same : ∀ declaration, declaration ∈ left ↔ declaration ∈ right) :
    Allowed model before after arguments value left ↔ Allowed model before after arguments value right := by
  constructor
  · rintro ⟨declaration,present,parameters,checked⟩
    exact ⟨declaration,(same declaration).1 present,parameters,checked⟩
  · rintro ⟨declaration,present,parameters,checked⟩
    exact ⟨declaration,(same declaration).2 present,parameters,checked⟩

theorem unrestricted_result_iff_input (model : Model sig Carrier Context Q C typeArity)
    (before after : Context) (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (declarations : List (Declaration sig P Q C typeArity valueKind n))
    (unrestricted : ∀ declaration ∈ declarations, declaration.output = .any) :
    Allowed model before after arguments value declarations ↔ AdmitsInput model before arguments declarations := by
  constructor
  · rintro ⟨declaration,present,parameters,inputs,_⟩; exact ⟨declaration,present,parameters,inputs⟩
  · rintro ⟨declaration,present,parameters,inputs⟩
    exact ⟨declaration,present,parameters,inputs,by rw [unrestricted declaration present]; exact .any _ _⟩

def runFrame [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (frame : Frame sig P Q C typeArity valueKind n)
    (body : Boundary.Body Context (Fin n → Carrier valueKind) (Carrier valueKind) Fault Effect)
    (context : Context) (arguments : Fin n → Carrier valueKind) : Trace (Carrier valueKind × Context) Fault Effect :=
  Boundary.call ⟨fun _ _ => entryAccepted frame,
    fun after _ value => resultAccepted model compiler after value frame⟩ body context arguments

def invoke [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (declarations : List (Declaration sig P Q C typeArity valueKind n))
    (body : Boundary.Body Context (Fin n → Carrier valueKind) (Carrier valueKind) Fault Effect)
    (context : Context) (arguments : Fin n → Carrier valueKind) : Trace (Carrier valueKind × Context) Fault Effect :=
  match declarations with
  | [] => body context arguments
  | _ :: _ => runFrame model compiler (prepare model compiler context arguments declarations) body context arguments

theorem undeclared_body_identity [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (body : Boundary.Body Context (Fin n → Carrier valueKind) (Carrier valueKind) Fault Effect)
    (context : Context) (arguments : Fin n → Carrier valueKind) :
    invoke model compiler ([] : List (Declaration sig P Q C typeArity valueKind n)) body context arguments =
      body context arguments := rfl

theorem admitted_call_filters_once [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (seed : Closed Q C typeArity) (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (declarations : List (Declaration sig P Q C typeArity valueKind n))
    (body : Boundary.Body Context (Fin n → Carrier valueKind) (Carrier valueKind) Fault Effect)
    (context : Context) (arguments : Fin n → Carrier valueKind)
    (admitted : AdmitsInput model context arguments declarations) :
    invoke model compiler declarations body context arguments =
      (body context arguments).filter (fun result => resultAccepted model compiler result.2 result.1
        (prepare model compiler context arguments declarations)) := by
  have entry := (entryAccepted_iff seed model compiler context arguments declarations).2 admitted
  cases declarations with
  | nil => obtain ⟨_,present,_⟩ := admitted; cases present
  | cons first rest => simp only [invoke,runFrame,Boundary.call,entry,if_true]

theorem unrestricted_result_preserves_computation [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (seed : Closed Q C typeArity) (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (declarations : List (Declaration sig P Q C typeArity valueKind n))
    (body : Boundary.Body Context (Fin n → Carrier valueKind) (Carrier valueKind) Fault Effect)
    (context : Context) (arguments : Fin n → Carrier valueKind)
    (admitted : AdmitsInput model context arguments declarations)
    (unrestricted : ∀ declaration ∈ declarations, declaration.output = .any) :
    invoke model compiler declarations body context arguments = body context arguments := by
  rw [admitted_call_filters_once seed model compiler declarations body context arguments admitted]
  have same : (fun result : Carrier valueKind × Context => resultAccepted model compiler result.2 result.1
      (prepare model compiler context arguments declarations)) = fun _ => true := by
    funext result
    exact (resultAccepted_iff seed model compiler context result.2 arguments result.1 declarations).2
      ((unrestricted_result_iff_input model context result.2 arguments result.1 declarations unrestricted).2 admitted)
  rw [same,Trace.no_check]

theorem admitted_effects_preserved [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (seed : Closed Q C typeArity) (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (declarations : List (Declaration sig P Q C typeArity valueKind n))
    (body : Boundary.Body Context (Fin n → Carrier valueKind) (Carrier valueKind) Fault Effect)
    (context : Context) (arguments : Fin n → Carrier valueKind)
    (admitted : AdmitsInput model context arguments declarations) :
    (invoke model compiler declarations body context arguments).effects = (body context arguments).effects := by
  rw [admitted_call_filters_once seed model compiler declarations body context arguments admitted]
  exact Trace.effects_filter _ _

theorem admitted_faults_preserved [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (seed : Closed Q C typeArity) (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (declarations : List (Declaration sig P Q C typeArity valueKind n))
    (body : Boundary.Body Context (Fin n → Carrier valueKind) (Carrier valueKind) Fault Effect)
    (context : Context) (arguments : Fin n → Carrier valueKind)
    (admitted : AdmitsInput model context arguments declarations) :
    (invoke model compiler declarations body context arguments).terminalFault = (body context arguments).terminalFault := by
  rw [admitted_call_filters_once seed model compiler declarations body context arguments admitted]
  exact Trace.fault_filter _ _

theorem body_equivalence_preserved [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (model : Model sig Carrier Context Q C typeArity) (compiler : Compiler model)
    (declarations : List (Declaration sig P Q C typeArity valueKind n))
    (left right : Boundary.Body Context (Fin n → Carrier valueKind) (Carrier valueKind) Fault Effect)
    (same : ∀ context arguments, left context arguments = right context arguments)
    (context : Context) (arguments : Fin n → Carrier valueKind) :
    invoke model compiler declarations left context arguments = invoke model compiler declarations right context arguments := by
  cases declarations <;> simp only [invoke,runFrame,Boundary.call,same]

theorem shared_parameter_iff_common_type (model : Model sig Carrier Context Q C typeArity)
    (parameter : P) (context : Context) (left right : Carrier valueKind) :
    (∃ parameters : P → Closed Q C typeArity,
      Matches model parameters (.proper (.parameter parameter)) context left ∧
      Matches model parameters (.proper (.parameter parameter)) context right) ↔
      ∃ type : Closed Q C typeArity, model.member context left type ∧ model.member context right type := by
  simp only [matches_proper_iff,TypeExpr.substitute]
  constructor
  · rintro ⟨parameters,left,right⟩; exact ⟨parameters parameter,left,right⟩
  · rintro ⟨type,left,right⟩; exact ⟨(fun _ => type),left,right⟩

end Mettapedia.Logic.ConstraintTypes.PatternContracts
