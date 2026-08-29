import Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
import Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
import Mettapedia.OSLF.Framework.DerivedTyping

/-!
# Observed operational realizations: surface evaluation versus machine execution

A serialized presentation may rewrite explicit *request* terms in a
machine-state sort while the language it presents evaluates *atoms*.  The
two are compatible exactly when a declared observation of the machine's run
agrees with the same observation of the surface evaluation.  This module
fixes that as a structure with two-sided, observation-indexed adequacy, and
instantiates it on the strongest existing evidence:

* MeTTaZero, whose atom-level semantics `evaluateOne : Pattern → Multiset
  Pattern` is joined to the generic executor's rewriting of `Process`-sorted
  request terms by the proved bag equations
  `query_rewrite_bag_adequate` / `evaluation_rewrite_bag_adequate`;
* the PeTTa `CoreDecl` fragment, whose request-to-completion edge is exactly
  the declarative command semantics (`request_step_completed_iff_pettaCmd`),
  as a relational realization.

The decisive corollary, `process_rewriting_realizes_atom_evaluation`, states
in one theorem that a machine whose reduction sort is `Process` realizes a
surface semantics in which atoms evaluate.  "The reduction sort is
`Process`, therefore atoms do not reduce" is thereby refuted on the tree's
own strongest instance.

Scope caveat carried from the underlying theorems: MeTTaZero's premise
relation is supplied from its own semantic bag, so the adequacy is executor
adequacy (matching, substitution, occurrence counting) rather than an
independent declarative semantics of atom evaluation.  The observation
covered is the *bag*; no theorem here speaks about the order of the machine's
stream, and the structure keeps the stream (`List`) and the bag (`Multiset`)
distinct so that this remains visible.
-/

namespace Mettapedia.GSLT.LanguageDef.ObservedOperationalRealization

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping

/-- The sort of a pattern's head constructor, read from the presentation. -/
def headSort (language : LanguageDef) : Pattern → Option String
  | .apply constructor _ =>
      (language.terms.find? (·.label = constructor)).map (·.category)
  | _ => none

/-- A bag-exact realization: supported surface inputs are encoded into a
machine, the machine takes one step to an ordered list of successors, and a
declared observation of that list equals the same observation of the surface
occurrence bag.  The stream and the bag are kept distinct on purpose. -/
structure BagExact (Surface Machine Answer Observation : Type) where
  language : LanguageDef
  reductionSort : String
  reductionSort_declared : reductionSort ∈ language.typeNames
  Supported : Surface → Prop
  surfaceEval : Surface → Multiset Answer
  encode : Surface → Machine
  machineStep : Machine → List Machine
  WellSorted : Machine → Prop
  encode_wellSorted : ∀ x, Supported x → WellSorted (encode x)
  step_wellSorted : ∀ x, Supported x → ∀ m ∈ machineStep (encode x), WellSorted m
  observeMachine : List Machine → Observation
  observeSurface : Multiset Answer → Observation
  adequate : ∀ x, Supported x →
    observeMachine (machineStep (encode x)) = observeSurface (surfaceEval x)

/-- A relational realization: the machine's request-to-completion edge holds
exactly when the surface relation does.  Used where the surface semantics is
a relation rather than a bag-valued function. -/
structure Relational (Surface Machine Answer : Type) where
  Supported : Surface → Prop
  SurfaceEval : Surface → Answer → Prop
  encode : Surface → Machine
  complete : Surface → Answer → Machine
  MachineStep : Machine → Machine → Prop
  adequate : ∀ x a, Supported x →
    (MachineStep (encode x) (complete x a) ↔ SurfaceEval x a)

/-! ## MeTTaZero: atoms evaluate on the surface, requests rewrite in the machine -/

section MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy

theorem zero_process_declared : "Process" ∈ language.typeNames := by
  decide

theorem queryRequest_headSort (space pattern template : Pattern) :
    headSort language (queryRequestPattern space pattern template) = some "Process" := by
  rfl

theorem queryAnswer_headSort (answer : Pattern) :
    headSort language (queryAnswerPattern answer) = some "Process" := by
  rfl

theorem evaluationRequest_headSort (space subject : Pattern) :
    headSort language (evaluationRequestPattern space subject) = some "Process" := by
  rfl

theorem evaluationAnswer_headSort (answer : Pattern) :
    headSort language (evaluationAnswerPattern answer) = some "Process" := by
  rfl

/-- The query realization: surface input is a (pattern, template) pair
evaluated by the atom-level `query`; the machine rewrites the `Process`-sorted
request term; the observation is the occurrence bag. -/
noncomputable def zeroQuery (model : Model) (space : model.Space) (spaceTerm : Pattern) :
    BagExact (Pattern × Pattern) Pattern Pattern (Multiset Pattern) where
  language := language
  reductionSort := "Process"
  reductionSort_declared := zero_process_declared
  Supported := fun _ => True
  surfaceEval := fun x => query model space x.1 x.2
  encode := fun x => queryRequestPattern spaceTerm x.1 x.2
  machineStep := rewriteStepWithPremisesUsing (relationEnv model space spaceTerm) language
  WellSorted := fun m => headSort language m = some "Process"
  encode_wellSorted := fun x _ => queryRequest_headSort spaceTerm x.1 x.2
  step_wellSorted := by
    intro x _ m member
    have bag : (rewriteStepWithPremisesUsing (relationEnv model space spaceTerm) language
        (queryRequestPattern spaceTerm x.1 x.2) : Multiset Pattern) =
        (query model space x.1 x.2).map queryAnswerPattern :=
      query_rewrite_bag_adequate model space spaceTerm x.1 x.2
    have memberBag : m ∈ ((query model space x.1 x.2).map queryAnswerPattern) := by
      rw [← bag]; exact Multiset.mem_coe.mpr member
    obtain ⟨answer, _, rfl⟩ := Multiset.mem_map.mp memberBag
    exact queryAnswer_headSort answer
  observeMachine := fun successors => (successors : Multiset Pattern)
  observeSurface := fun bag => bag.map queryAnswerPattern
  adequate := fun x _ => query_rewrite_bag_adequate model space spaceTerm x.1 x.2

/-- The evaluation realization: the surface input is one atom, evaluated by
`evaluateOne`. -/
noncomputable def zeroEvaluate (model : Model) (space : model.Space) (spaceTerm : Pattern) :
    BagExact Pattern Pattern Pattern (Multiset Pattern) where
  language := language
  reductionSort := "Process"
  reductionSort_declared := zero_process_declared
  Supported := fun _ => True
  surfaceEval := fun subject => evaluateOne model space subject
  encode := fun subject => evaluationRequestPattern spaceTerm subject
  machineStep := rewriteStepWithPremisesUsing (relationEnv model space spaceTerm) language
  WellSorted := fun m => headSort language m = some "Process"
  encode_wellSorted := fun subject _ => evaluationRequest_headSort spaceTerm subject
  step_wellSorted := by
    intro subject _ m member
    have bag : (rewriteStepWithPremisesUsing (relationEnv model space spaceTerm) language
        (evaluationRequestPattern spaceTerm subject) : Multiset Pattern) =
        (evaluateOne model space subject).map evaluationAnswerPattern :=
      evaluation_rewrite_bag_adequate model space spaceTerm subject
    have memberBag : m ∈ ((evaluateOne model space subject).map evaluationAnswerPattern) := by
      rw [← bag]; exact Multiset.mem_coe.mpr member
    obtain ⟨answer, _, rfl⟩ := Multiset.mem_map.mp memberBag
    exact evaluationAnswer_headSort answer
  observeMachine := fun successors => (successors : Multiset Pattern)
  observeSurface := fun bag => bag.map evaluationAnswerPattern
  adequate := fun subject _ => evaluation_rewrite_bag_adequate model space spaceTerm subject

/-- **A `Process`-reducing machine realizes atom evaluation.**  The encoded
request has head sort `Process`, and its one-step successor bag is exactly the
image of the atom-level evaluation of the subject.  The inference "the
reduction sort is `Process`, so atoms do not reduce" is false for this
presentation. -/
theorem process_rewriting_realizes_atom_evaluation (model : Model) (space : model.Space)
    (spaceTerm subject : Pattern) :
    headSort language (evaluationRequestPattern spaceTerm subject) = some "Process" ∧
      ((zeroEvaluate model space spaceTerm).machineStep
          ((zeroEvaluate model space spaceTerm).encode subject) : Multiset Pattern) =
        (evaluateOne model space subject).map evaluationAnswerPattern :=
  ⟨evaluationRequest_headSort spaceTerm subject,
    evaluation_rewrite_bag_adequate model space spaceTerm subject⟩

/-- The derivation classifies the answer constructor as reflecting into the
reduction sort; read together with the theorem above, the `□` arrow is the
machine reflecting an atom's evaluation, not a claim that atoms are inert. -/
def atomSort : LangSort language := ⟨"Atom", by decide⟩
def processSort : LangSort language := ⟨"Process", by decide⟩

theorem evaluationAnswer_crossing :
    ("zero-evaluate-answer", "Atom", "Process") ∈ unaryCrossings language := by
  decide

def evaluationAnswerArrow : SortArrow language atomSort processSort :=
  ⟨"zero-evaluate-answer", evaluationAnswer_crossing⟩

theorem evaluationAnswer_is_reflecting :
    classifyArrow language "Process" evaluationAnswerArrow = .reflecting := by
  decide

end MeTTaZero

/-! ## PeTTa `CoreDecl`: a relational realization, explicitly fragmentary -/

section PeTTa
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT

/-- The PeTTa core fragment: surface inputs are (state, request) pairs, the
surface relation is the declarative `PeTTaCmd`, the machine is the generated
operational theory.  `Supported` is deliberately `True` only for the core
fragment the theory covers; library and profile features of the running
dialect are outside it. -/
def pettaCore : Relational (EvalState × Pattern) CoreOperationalTerm (EvalState × Answers) where
  Supported := fun _ => True
  SurfaceEval := fun x a => PeTTaCmd x.1 x.2 a.1 a.2
  encode := fun x => .request x.1 x.2
  complete := fun x a => .completed x.1 x.2 a.1 a.2
  MachineStep := CoreOperationalGSLT.Step
  adequate := fun x a _ => request_step_completed_iff_pettaCmd x.1 x.2 a.1 a.2

end PeTTa

#print axioms process_rewriting_realizes_atom_evaluation
#print axioms evaluationAnswer_is_reflecting

end Mettapedia.GSLT.LanguageDef.ObservedOperationalRealization
