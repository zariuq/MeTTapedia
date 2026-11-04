import Mettapedia.Logic.ConstraintTypes.ConstructorTyping
import Mettapedia.Logic.ConstraintTypes.Execution

/-!
# Staged call contracts with shared symbolic witnesses

Evaluation modes are syntactic observations, separate from proper type schemes.
Arguments are held only under a unanimous literal raw-mode request. Entry
constraints are compiled once and retained as equations; no declaration context
is stored in the frame. Results are checked in their new context, sharing the
same scheme parameters with the inputs. The body is run once, independently of
the number of declarations or type witnesses.

The executable checker here is the closed-value specialization. Open values
retain residual predicates, whose normalization is covered by SymbolicTypes.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.CallTyping

open SymbolicTypes ScopedConstraints ConstructorTyping

variable {P Q C S Context Mode : Type} {typeArity : C → Nat} {valueArity : S → Nat} {n : Nat}

inductive Evaluation where
  | evaluate
  | hold
  deriving DecidableEq, Repr

abbrev Domain (P Q C Mode : Type) (arity : C → Nat) := Mode ⊕ Expr P Q C arity

structure Signature (Input Output : Type) (inputs : Nat) where
  input : Fin inputs → Input
  output : Output

abbrev Declaration (P Q C Mode : Type) (arity : C → Nat) (inputs : Nat) :=
  Signature (Domain P Q C Mode arity) (Domain P Q C Mode arity) inputs

def requestsRaw [DecidableEq Mode] (raw : Mode) : Domain P Q C Mode typeArity → Bool
  | .inl mode => decide (mode = raw)
  | .inr _ => false

/-- A mixed request evaluates once. A type parameter cannot become a raw-mode
request by being instantiated while the proper type equations are solved. -/
def evaluationPlan [DecidableEq Mode] (raw : Mode) (domains : List (Domain P Q C Mode typeArity)) : Evaluation :=
  if domains.isEmpty then .evaluate
  else if domains.all (requestsRaw raw) then .hold else .evaluate

theorem singleton_plan [DecidableEq Mode] (raw : Mode) (domain : Domain P Q C Mode typeArity) :
    evaluationPlan raw [domain] = if requestsRaw raw domain then .hold else .evaluate := by
  simp [evaluationPlan]

theorem proper_parameter_evaluates [DecidableEq Mode] (raw : Mode) (p : P) :
    evaluationPlan raw [(Sum.inr (TypeExpr.parameter p) : Domain P Q C Mode typeArity)] = .evaluate := rfl

def Fits (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (context : Context) (value : Tree S valueArity) (parameters : P → Closed Q C typeArity) :
    Domain P Q C Mode typeArity → Prop
  | .inl mode => observe context mode value = true
  | .inr type => HasType system context value (type.substitute parameters)

def compileDomain [DecidableEq P] (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (context : Context) (value : Tree S valueArity) : Domain P Q C Mode typeArity → List (Problem P Q C typeArity)
  | .inl mode => if observe context mode value then [truth] else []
  | .inr type => ConstructorTyping.compile system context value type

theorem compileDomain_correct [DecidableEq P] (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (context : Context) (value : Tree S valueArity) (parameters : P → Closed Q C typeArity)
    (domain : Domain P Q C Mode typeArity) :
    alternativesSatisfy (compileDomain system observe context value domain) parameters ↔
      Fits system observe context value parameters domain := by
  cases domain with
  | inl mode =>
      by_cases h : observe context mode value = true
      · simp [compileDomain, h, alternativesSatisfy, Fits, satisfies_truth]
      · simp [compileDomain, h, alternativesSatisfy, Fits]
  | inr type => exact ConstructorTyping.compile_correct _ _ _ _ _

def inputProblems [DecidableEq P] (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (context : Context)
    (arguments : Fin n → Tree S valueArity) (declaration : Declaration P Q C Mode typeArity n) :
    List (Problem P Q C typeArity) :=
  combinations ((List.finRange n).map fun i =>
    compileDomain system observe context (arguments i) (declaration.input i))

theorem inputProblems_correct [DecidableEq P] (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (context : Context)
    (arguments : Fin n → Tree S valueArity) (declaration : Declaration P Q C Mode typeArity n)
    (parameters : P → Closed Q C typeArity) :
    alternativesSatisfy (inputProblems system observe context arguments declaration) parameters ↔
      ∀ i, Fits system observe context (arguments i) parameters (declaration.input i) := by
  simp only [inputProblems, satisfies_combinations, List.mem_map]
  constructor
  · intro all i
    exact (compileDomain_correct _ _ _ _ _ _).1 (all _ ⟨i, List.mem_finRange i, rfl⟩)
  · rintro all _ ⟨i, _, rfl⟩
    exact (compileDomain_correct _ _ _ _ _ _).2 (all i)

structure Candidate (P Q C Mode : Type) (arity : C → Nat) (inputs : Nat) where
  declaration : Declaration P Q C Mode arity inputs
  evidence : Problem P Q C arity

def prepare [DecidableEq P] (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (context : Context)
    (arguments : Fin n → Tree S valueArity) (declarations : List (Declaration P Q C Mode typeArity n)) :
    List (Candidate P Q C Mode typeArity n) :=
  declarations.flatMap fun declaration =>
    (inputProblems system observe context arguments declaration).map fun evidence => ⟨declaration, evidence⟩

def finishProblems [DecidableEq P] (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (context : Context)
    (value : Tree S valueArity) (frame : List (Candidate P Q C Mode typeArity n)) :
    List (Problem Empty Q C typeArity) :=
  frame.flatMap fun candidate =>
    (compileDomain system observe context value candidate.declaration.output).map fun output =>
      close (conjunction candidate.evidence output)

def Allowed (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (before after : Context)
    (arguments : Fin n → Tree S valueArity) (value : Tree S valueArity)
    (declarations : List (Declaration P Q C Mode typeArity n)) : Prop :=
  ∃ declaration ∈ declarations, ∃ parameters : P → Closed Q C typeArity,
    (∀ i, Fits system observe before (arguments i) parameters (declaration.input i)) ∧
      Fits system observe after value parameters declaration.output

/-- Compilation preserves the call relation across distinct input and result
contexts. Input evidence, not a historical context, is kept in the frame. -/
theorem frame_exact [DecidableEq P] (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (before after : Context)
    (arguments : Fin n → Tree S valueArity) (value : Tree S valueArity)
    (declarations : List (Declaration P Q C Mode typeArity n)) :
    alternativesSatisfy
      (finishProblems system observe after value (prepare system observe before arguments declarations))
      Empty.elim ↔ Allowed system observe before after arguments value declarations := by
  constructor
  · rintro ⟨problem, member, solved⟩
    obtain ⟨candidate, member, mapped⟩ := List.mem_flatMap.1 member
    obtain ⟨declaration, present, mappedInput⟩ := List.mem_flatMap.1 member
    obtain ⟨input, inputMember, rfl⟩ := List.mem_map.1 mappedInput
    obtain ⟨output, outputMember, rfl⟩ := List.mem_map.1 mapped
    obtain ⟨parameters, joint⟩ := satisfies_close _ |>.1 solved
    obtain ⟨si, so⟩ := (satisfies_conjunction _ _ _).1 joint
    exact ⟨declaration, present, parameters,
      (inputProblems_correct _ _ _ _ _ _).1 ⟨input, inputMember, si⟩,
      (compileDomain_correct _ _ _ _ _ _).1 ⟨output, outputMember, so⟩⟩
  · rintro ⟨declaration, present, parameters, inputs, result⟩
    obtain ⟨input, inputMember, si⟩ := (inputProblems_correct _ _ _ _ _ _).2 inputs
    obtain ⟨output, outputMember, so⟩ := (compileDomain_correct _ _ _ _ _ _).2 result
    refine ⟨_, List.mem_flatMap.2 ⟨⟨declaration, input⟩,
      List.mem_flatMap.2 ⟨declaration, present, List.mem_map.2 ⟨input, inputMember, rfl⟩⟩,
      List.mem_map.2 ⟨output, outputMember, rfl⟩⟩, ?_⟩
    exact (satisfies_close _).2 ⟨parameters, (satisfies_conjunction _ _ _).2 ⟨si, so⟩⟩


def entryAccepted [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (frame : List (Candidate P Q C Mode typeArity n)) : Bool :=
  accept (frame.map fun candidate => close candidate.evidence)

def resultAccepted [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (context : Context)
    (value : Tree S valueArity) (frame : List (Candidate P Q C Mode typeArity n)) : Bool :=
  accept (finishProblems system observe context value frame)

def AdmitsInput (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (context : Context)
    (arguments : Fin n → Tree S valueArity) (declarations : List (Declaration P Q C Mode typeArity n)) : Prop :=
  ∃ declaration ∈ declarations, ∃ parameters : P → Closed Q C typeArity,
    ∀ i, Fits system observe context (arguments i) parameters (declaration.input i)

theorem entryAccepted_iff [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity) (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (context : Context)
    (arguments : Fin n → Tree S valueArity) (declarations : List (Declaration P Q C Mode typeArity n)) :
    entryAccepted (prepare system observe context arguments declarations) = true ↔
      AdmitsInput system observe context arguments declarations := by
  rw [entryAccepted, accept_closed_iff seed]
  constructor
  · rintro ⟨problem, present, solved⟩
    obtain ⟨candidate, candidatePresent, equal⟩ := List.mem_map.1 present
    subst problem
    obtain ⟨declaration, declared, inputMap⟩ := List.mem_flatMap.1 candidatePresent
    obtain ⟨input, inputPresent, equal⟩ := List.mem_map.1 inputMap
    subst candidate
    obtain ⟨parameters, solved⟩ := (satisfies_close _).1 solved
    exact ⟨declaration, declared, parameters,
      (inputProblems_correct _ _ _ _ _ _).1 ⟨input, inputPresent, solved⟩⟩
  · rintro ⟨declaration, declared, parameters, inputs⟩
    obtain ⟨input, present, solved⟩ := (inputProblems_correct _ _ _ _ _ _).2 inputs
    refine ⟨_, List.mem_map.2 ⟨⟨declaration, input⟩,
      List.mem_flatMap.2 ⟨declaration, declared, List.mem_map.2 ⟨input, present, rfl⟩⟩, rfl⟩, ?_⟩
    exact (satisfies_close _).2 ⟨parameters, solved⟩

theorem resultAccepted_iff [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity) (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (before after : Context)
    (arguments : Fin n → Tree S valueArity) (value : Tree S valueArity)
    (declarations : List (Declaration P Q C Mode typeArity n)) :
    resultAccepted system observe after value (prepare system observe before arguments declarations) = true ↔
      Allowed system observe before after arguments value declarations := by
  rw [resultAccepted, accept_closed_iff seed]
  exact frame_exact _ _ _ _ _ _ _


theorem admitsInput_declaration_congr
    (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (context : Context)
    (arguments : Fin n → Tree S valueArity)
    (left right : List (Declaration P Q C Mode typeArity n))
    (same : ∀ declaration, declaration ∈ left ↔ declaration ∈ right) :
    AdmitsInput system observe context arguments left ↔ AdmitsInput system observe context arguments right := by
  constructor
  · rintro ⟨declaration, present, witness, fits⟩
    exact ⟨declaration, (same declaration).1 present, witness, fits⟩
  · rintro ⟨declaration, present, witness, fits⟩
    exact ⟨declaration, (same declaration).2 present, witness, fits⟩


theorem entryAccepted_declaration_congr [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity) (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (context : Context)
    (arguments : Fin n → Tree S valueArity)
    (left right : List (Declaration P Q C Mode typeArity n))
    (same : ∀ declaration, declaration ∈ left ↔ declaration ∈ right) :
    entryAccepted (prepare system observe context arguments left) =
      entryAccepted (prepare system observe context arguments right) := by
  apply Bool.eq_iff_iff.mpr
  rw [entryAccepted_iff seed, entryAccepted_iff seed]
  exact admitsInput_declaration_congr _ _ _ _ _ _ same

theorem allowed_declaration_congr
    (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (before after : Context)
    (arguments : Fin n → Tree S valueArity) (value : Tree S valueArity)
    (left right : List (Declaration P Q C Mode typeArity n))
    (same : ∀ declaration, declaration ∈ left ↔ declaration ∈ right) :
    Allowed system observe before after arguments value left ↔
      Allowed system observe before after arguments value right := by
  constructor
  · rintro ⟨declaration, present, witness, fits⟩
    exact ⟨declaration, (same declaration).1 present, witness, fits⟩
  · rintro ⟨declaration, present, witness, fits⟩
    exact ⟨declaration, (same declaration).2 present, witness, fits⟩

/-- This applies to reordering and duplicate declarations, including all
joint-witness constraints. The compiler need not emit identical problem lists. -/
theorem resultAccepted_declaration_congr [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (seed : Closed Q C typeArity) (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool) (before after : Context)
    (arguments : Fin n → Tree S valueArity) (value : Tree S valueArity)
    (left right : List (Declaration P Q C Mode typeArity n))
    (same : ∀ declaration, declaration ∈ left ↔ declaration ∈ right) :
    resultAccepted system observe after value (prepare system observe before arguments left) =
      resultAccepted system observe after value (prepare system observe before arguments right) := by
  apply Bool.eq_iff_iff.mpr
  rw [resultAccepted_iff seed, resultAccepted_iff seed]
  exact allowed_declaration_congr _ _ _ _ _ _ _ _ same

/-- A prepared frame holds input equations and source schemes. The return check
receives the result context; it does not recover a world captured at entry. -/
def runFrame [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (frame : List (Candidate P Q C Mode typeArity n))
    (body : Boundary.Body Context (Fin n → Tree S valueArity) (Tree S valueArity) Fault Effect)
    (context : Context) (arguments : Fin n → Tree S valueArity) :
    Trace (Tree S valueArity × Context) Fault Effect :=
  Boundary.call ⟨fun _ _ => entryAccepted frame,
    fun after _ value => resultAccepted system observe after value frame⟩ body context arguments

def invoke [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (declarations : List (Declaration P Q C Mode typeArity n))
    (body : Boundary.Body Context (Fin n → Tree S valueArity) (Tree S valueArity) Fault Effect)
    (context : Context) (arguments : Fin n → Tree S valueArity) :
    Trace (Tree S valueArity × Context) Fault Effect :=
  match declarations with
  | [] => body context arguments
  | first :: rest => runFrame system observe (prepare system observe context arguments (first :: rest))
      body context arguments

theorem undeclared_body_identity [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (body : Boundary.Body Context (Fin n → Tree S valueArity) (Tree S valueArity) Fault Effect) :
    invoke system observe [] body = body := rfl

/-- Declaration evidence filters the one ordered body trace. Neither alternative
signatures nor multiple type witnesses cause another evaluation of the body. -/
theorem admitted_call_filters_once [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (seed : Closed Q C typeArity) (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (declarations : List (Declaration P Q C Mode typeArity n))
    (body : Boundary.Body Context (Fin n → Tree S valueArity) (Tree S valueArity) Fault Effect)
    (context : Context) (arguments : Fin n → Tree S valueArity)
    (admitted : AdmitsInput system observe context arguments declarations) :
    invoke system observe declarations body context arguments =
      (body context arguments).filter fun result => resultAccepted system observe result.2 result.1
        (prepare system observe context arguments declarations) := by
  have accepted := (entryAccepted_iff seed system observe context arguments declarations).2 admitted
  cases declarations with
  | nil => obtain ⟨_, impossible, _⟩ := admitted; cases impossible
  | cons first rest => simp only [invoke, runFrame, Boundary.call, accepted, if_true]

theorem admitted_effects_preserved [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (seed : Closed Q C typeArity) (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (declarations : List (Declaration P Q C Mode typeArity n))
    (body : Boundary.Body Context (Fin n → Tree S valueArity) (Tree S valueArity) Fault Effect)
    (context : Context) (arguments : Fin n → Tree S valueArity)
    (admitted : AdmitsInput system observe context arguments declarations) :
    (invoke system observe declarations body context arguments).effects = (body context arguments).effects := by
  rw [admitted_call_filters_once seed system observe declarations body context arguments admitted]
  exact Trace.effects_filter _ _

theorem admitted_faults_preserved [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (seed : Closed Q C typeArity) (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (declarations : List (Declaration P Q C Mode typeArity n))
    (body : Boundary.Body Context (Fin n → Tree S valueArity) (Tree S valueArity) Fault Effect)
    (context : Context) (arguments : Fin n → Tree S valueArity)
    (admitted : AdmitsInput system observe context arguments declarations) :
    (invoke system observe declarations body context arguments).terminalFault =
      (body context arguments).terminalFault := by
  rw [admitted_call_filters_once seed system observe declarations body context arguments admitted]
  exact Trace.fault_filter _ _


theorem invoke_declaration_congr [DecidableEq P] [DecidableEq Q] [DecidableEq C] {Fault Effect : Type}
    (seed : Closed Q C typeArity) (system : System Context P Q C S typeArity valueArity)
    (observe : Context → Mode → Tree S valueArity → Bool)
    (left right : List (Declaration P Q C Mode typeArity n))
    (same : ∀ declaration, declaration ∈ left ↔ declaration ∈ right)
    (body : Boundary.Body Context (Fin n → Tree S valueArity) (Tree S valueArity) Fault Effect)
    (context : Context) (arguments : Fin n → Tree S valueArity) :
    invoke system observe left body context arguments = invoke system observe right body context arguments := by
  have entrySame := entryAccepted_declaration_congr seed system observe context arguments left right same
  have resultsSame :
      (fun result : Tree S valueArity × Context => resultAccepted system observe result.2 result.1
        (prepare system observe context arguments left)) =
      (fun result : Tree S valueArity × Context => resultAccepted system observe result.2 result.1
        (prepare system observe context arguments right)) := by
    funext result
    exact resultAccepted_declaration_congr seed system observe context result.2 arguments result.1 left right same
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons first rest => have impossible := (same first).2 List.mem_cons_self; cases impossible
  | cons first rest =>
      cases right with
      | nil => have impossible := (same first).1 List.mem_cons_self; cases impossible
      | cons second remaining =>
          simp only [invoke, runFrame, Boundary.call, entrySame]
          rw [resultsSame]

end Mettapedia.Logic.ConstraintTypes.CallTyping
