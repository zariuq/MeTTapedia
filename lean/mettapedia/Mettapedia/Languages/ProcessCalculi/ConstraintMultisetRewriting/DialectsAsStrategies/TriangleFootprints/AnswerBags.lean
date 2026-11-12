import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.CompleteRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.RegionsWithVariables
import Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec

/-!
# Answer bags over the fragment: HE and PeTTa agree on settling calls

`CompleteRun.double_complete_run` followed one call, `(double 4)`, from HE's entry configuration
to its published answer and compared it with PeTTa's streaming run. Here the same comparison is
made for every flat ground call of the fragment, with several matching equations and with call
bodies that are themselves calls.

**The two machines are the tree's.** HE runs `RecursiveMachine.Contextual.Step` from `load`, with
any cast lookup meeting `EntryToQuery.AnswersUndefined` (both of HE's lookups do) and any policy.
PeTTa runs `Streaming.advance` from `Streaming.enter` on its translation of the same rows: the
program its own loader collects (`translate`, `SpaceSemantics.collect`) over the store that loading
builds (`store`, `Effects.loaded`). PeTTa's steps are taken by its own rules
(`Streaming.Transition`, `Unifying.Transition`).

**The fragment** (`Ordinary`, `Settles`): calls `(f a₁ … aₙ)` of data atoms whose head is
undeclared, no host operation, no instruction, no PeTTa primitive or control form; programs of
symbol-headed, `cons`-free equations (`RegionsWithVariables.ConsFreeHeads`). A term settles when it
is a data atom other than `NotReducible`, a call of a head with no equation (a constructor), or a
call with a nonempty region whose bodies all settle. `Settles` is the termination and coverage
hypothesis, stated on the program: it mentions rows, patterns and bodies, never an answer or a run.

## Results

* `settles_agree`: one induction on the settling derivation gives, for every settling term, an
  answer list `L` that HE's machine returns from pending work on the term under any live list,
  scope, activation and stack (`HEEvaluates`), and that PeTTa's streaming machine delivers, in
  order, under any frames (`PeTTaEvaluates`, in continuation form through `Delivers`).
* `answers_agree`, `answer_bags_agree`, `answer_bags_agree_with_he_lookups`: **HE's complete run
  from its entry configuration publishes exactly the atoms that PeTTa's streaming run of the
  translation yields from some fuel on, in the same order and with the same multiplicities**; so
  the bags agree.
* `uncovered_calls_differ`: a call whose head has an equation of its arity but no matching row:
  HE answers the call, PeTTa answers nothing (more in `FragmentDifferences`).

## Controls

* `Controls.toss_agrees` (several equations, a call body, recursion): `heads`, `tails`, `edge` in
  both; `Controls.pick_agrees` (a literal and a variable pattern both match): `one`, `any`.
* `Controls.five_differs`: `(f 5)` on `{(= (f 4) 8)}`: HE `(f 5)`, PeTTa nothing.
* `Controls.loop_does_not_settle`: `(loop)` on `{(= (loop) (loop))}` does not settle, so the
  termination hypothesis is not vacuous.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace AnswerBags

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationRowResultsRel
  EquationWork AlphaVariantRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load observe)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open ServiceFootprints EntryToQuery

/-! ## PeTTa's translation of a program -/

theorem collect_ok : ∀ atoms : List Atom, ∃ program, SpaceSemantics.collect atoms = .ok program
  | [] => ⟨_, rfl⟩
  | form :: rest => by
      obtain ⟨program, collected⟩ := collect_ok rest
      simp only [SpaceSemantics.collect, collected, bind, Except.bind]
      split <;> exact ⟨_, rfl⟩

/-- **PeTTa's translation of an HE program**: the program PeTTa's own loader collects from the same
rows (`SpaceSemantics.collect` classifies every form and rejects none). -/
def translate (atoms : List Atom) : SpaceSemantics.Program :=
  match SpaceSemantics.collect atoms with
  | .ok program => program
  | .error _ => { equations := [], declarations := [] }

/-- The store PeTTa runs the translation on: `&self` holds the loaded rows. -/
def store (atoms : List Atom) : Effects.State := Effects.loaded (translate atoms)

theorem collect_translate (atoms : List Atom) :
    SpaceSemantics.collect atoms = .ok (translate atoms) := by
  obtain ⟨program, collected⟩ := collect_ok atoms
  simp only [translate, collected]

theorem translate_equations (atoms : List Atom) :
    (translate atoms).equations = atoms.filterMap LiveEquations.equationOfRow :=
  (LiveEquations.collect_equations (collect_translate atoms)).symm

theorem store_core (atoms : List Atom) : (store atoms).core = atoms :=
  SpaceSemantics.loadedAtoms_collect (collect_translate atoms)

theorem collect_declarations : ∀ (atoms : List Atom) (program : SpaceSemantics.Program),
    SpaceSemantics.collect atoms = .ok program → ∀ d ∈ program.declarations, d ∈ atoms
  | [], program, collected => by
      simp only [SpaceSemantics.collect, Except.ok.injEq] at collected
      subst collected
      intro d member
      cases member
  | form :: rest, program, collected => by
      simp only [SpaceSemantics.collect, bind, Except.bind] at collected
      cases restCollected : SpaceSemantics.collect rest with
      | error message => simp [restCollected] at collected
      | ok restProgram =>
      simp only [restCollected] at collected
      have later := collect_declarations rest restProgram restCollected
      split at collected <;> (simp only [Except.ok.injEq] at collected; subst collected)
      · intro d member
        exact List.mem_cons_of_mem _ (later d member)
      · intro d member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (later d inRest)
      · intro d member
        exact List.mem_cons_of_mem _ (later d member)

/-- A head with no declaration row demands no raw argument in the translation. -/
theorem argumentIsRaw_false {atoms : List Atom} {f : String} (notNative : StdLib.known f = false)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = []) (index : Nat) :
    Mettapedia.Languages.MeTTa.PeTTa.Eval.argumentIsRaw (translate atoms) f index = false := by
  unfold Mettapedia.Languages.MeTTa.PeTTa.Eval.argumentIsRaw
  rw [if_neg (by simp [notNative])]
  apply List.any_eq_false.mpr
  intro d member
  have inAtoms := collect_declarations atoms _ (collect_translate atoms) d member
  split
  · rename_i name types
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro same
    subst same
    have outside := List.filter_eq_nil_iff.mp untyped _ inAtoms
    rw [WholeRunWords.declaration_typeRegion] at outside
    exact absurd rfl outside
  · simp

/-! ## The fragment -/

/-- **An ordinary call** `(f a₁ … aₙ)` of data atoms. HE runs it through the type-directed tuple
entry and then its equation query: `f` has no declaration, is no host operation, and the call is no
minimal instruction. PeTTa runs it as a call of an authored function or as a constructor: `f` is no
I/O head and no primitive, and the call is no source control form and opens no streaming scope. -/
structure Ordinary (dispatch : GroundedDispatch) (atoms : List Atom) (f : String)
    (args : List Atom) : Prop where
  head : DataAtom (.symbol f)
  arguments : ∀ a ∈ args, DataAtom a
  untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = []
  notHost : ¬ dispatch.executable (.symbol f)
  notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: args)) = false
  notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false
  notNative : StdLib.known f = false
  notControl : Unifying.sourceControlForm (.expression (.symbol f :: args)) = false
  notCollapse : f ≠ "collapse"
  notOnce : f ≠ "once"

/-- The bodies of the rows in a call's region, in row order. -/
def regionBodies (atoms : List Atom) (f : String) (args : List Atom) : List Atom :=
  (atoms.filter (pettaCallRegion f args)).filterMap fun row =>
    (LiveEquations.equationOfRow row).map (·.body)

/-- **The fragment's terms, with termination and coverage stated on the program.** A term settles
when it is a data atom other than `NotReducible`; or an ordinary call whose head has no equation
(a constructor); or an ordinary call with at least one row in its region whose bodies all settle.
This is an accessibility predicate on the program's call graph: it mentions only rows, patterns and
bodies, never an answer or a run. -/
inductive Settles (dispatch : GroundedDispatch) (atoms : List Atom) : Atom → Prop
  | data {a : Atom} : DataAtom a → a ≠ Atom.notReducible → Settles dispatch atoms a
  | constructor {f : String} {args : List Atom} : Ordinary dispatch atoms f args →
      (atoms.filterMap LiveEquations.equationOfRow).all (fun equation => equation.head != f) = true →
      Settles dispatch atoms (.expression (.symbol f :: args))
  | call {f : String} {args : List Atom} : Ordinary dispatch atoms f args →
      regionBodies atoms f args ≠ [] →
      (∀ body ∈ regionBodies atoms f args, Settles dispatch atoms body) →
      Settles dispatch atoms (.expression (.symbol f :: args))

/-- What an answer of the fragment is: closed, no error, ground, neither `Empty` nor an error, and
not the symbol `Error` (so no tuple it heads is an error). -/
structure Answerable (a : Atom) : Prop where
  closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs a name
  notError : isErrorAtom a = false
  ground : isGroundAtom a = true
  notStopped : ¬ IsEmptyOrErrorRel a
  notErrorSymbol : a ≠ .symbol "Error"

theorem answerable_of_data {a : Atom} (data : DataAtom a) : Answerable a := by
  refine ⟨fun name occurs => ?_, ?_, ?_, data.not_stopped, ?_⟩
  · cases data <;> cases occurs
  · cases data <;> rfl
  · cases data <;> rfl
  · cases data with
    | symbol _ notError => exact fun same => notError (by cases same; rfl)
    | grounded value => exact fun same => by cases same

theorem args_ground {args : List Atom} (data : ∀ a ∈ args, DataAtom a) :
    isGroundAtom.isGroundList args = true := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      simp only [isGroundAtom.isGroundList, Bool.and_eq_true]
      exact ⟨(answerable_of_data (data a List.mem_cons_self)).ground,
        ih fun b member => data b (List.mem_cons_of_mem _ member)⟩

/-- A call atom with an ordinary head and answerable arguments is answerable. -/
theorem app_answerable {f : String} {vals : List Atom} (head : DataAtom (.symbol f))
    (each : ∀ a ∈ vals, Answerable a) : Answerable (.expression (.symbol f :: vals)) := by
  have groundList : isGroundAtom.isGroundList vals = true := by
    induction vals with
    | nil => rfl
    | cons a rest ih =>
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true]
        exact ⟨(each a List.mem_cons_self).ground,
          ih fun b member => each b (List.mem_cons_of_mem _ member)⟩
  refine ⟨fun name occurs => ?_, ?_, ?_, ?_, fun same => by cases same⟩
  · cases occurs with
    | expression member inner =>
        rcases List.mem_cons.mp member with rfl | inArgs
        · cases inner
        · exact (each _ inArgs).closed name inner
  · cases head with
    | symbol _ notError => simp [isErrorAtom, notError]
  · simp [isGroundAtom, isGroundAtom.isGroundList, groundList]
  · rintro (same | ⟨tail, same⟩)
    · simp [Atom.empty] at same
    · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      cases head with
      | symbol _ notError => exact notError same.1

theorem call_answerable {f : String} {args : List Atom} (head : DataAtom (.symbol f))
    (data : ∀ a ∈ args, DataAtom a) : Answerable (.expression (.symbol f :: args)) :=
  app_answerable head fun a member => answerable_of_data (data a member)

/-! ## PeTTa's streaming machine, step by step -/

namespace PeTTaRuns

open Unifying (Answer)

/-- Runs of PeTTa's streaming machine, by its own rules (`Streaming.Transition`). -/
abbrev PSteps (registry : SpaceSemantics.Program) : Streaming.State → Streaming.State → Prop :=
  Relation.ReflTransGen (Streaming.Transition registry)

variable {registry : SpaceSemantics.Program}

theorem evaluate_data (world : Streaming.World) (σ : Subst) {d : Atom} (data : DataAtom d)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    Streaming.Transition registry ⟨world, .execute ⟨.evaluate σ d, frames⟩ :: older, answers, next⟩
      ⟨world, .execute ⟨.returned [⟨d, σ⟩], frames⟩ :: older, answers, next⟩ := by
  cases data with
  | symbol _ _ => exact .phase rfl rfl (.symbol rfl) (.plain rfl)
  | grounded value => exact .phase rfl rfl (.grounded rfl) (.plain rfl)

theorem return_root (world : Streaming.World) (answer : Answer) (older : List Streaming.Job)
    (answers : List Answer) (next : Nat) :
    Streaming.Transition registry ⟨world, .execute ⟨.returned [answer], []⟩ :: older, answers, next⟩
      ⟨world, older, answers ++ [answer], next⟩ :=
  .answer rfl (.root _)

theorem return_argument (world : Streaming.World) (answer : Answer)
    (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target) (rest held : List Atom) (index : Nat)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.returned [answer], .source (.argument target rest held index) :: frames⟩ ::
        older, answers, next⟩
      ⟨world, .execute ⟨.sequence [.arguments answer.bindings target rest (held ++ [answer.value])
        (index + 1)] [], frames⟩ :: older, answers, next⟩ :=
  .answer rfl (.source (.argument_return rfl rfl) (.plain rfl))

theorem alternatives (world : Streaming.World) (controls : List Unifying.Control)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    Streaming.Transition registry ⟨world, .execute ⟨.sequence controls [], frames⟩ :: older, answers,
        next⟩
      ⟨world, (controls.map fun control => .execute ⟨control, frames⟩) ++ older, answers, next⟩ :=
  Streaming.Transition.alternatives (controls := controls) (answers := []) (frames := frames)
    (older := older) rfl

/-- Whether a target demands its argument at `index` unevaluated. -/
def rawDemand (registry : SpaceSemantics.Program) :
    Mettapedia.Languages.MeTTa.PeTTa.Eval.Target → Nat → Bool
  | .function head, index => Mettapedia.Languages.MeTTa.PeTTa.Eval.argumentIsRaw registry head index
  | .data, _ => false

theorem evaluate_argument (world : Streaming.World) (σ : Subst)
    (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target) (first : Atom) (rest held : List Atom)
    (index : Nat) (demanded : rawDemand registry target index = false)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.arguments σ target (first :: rest) held index, frames⟩ :: older, answers,
        next⟩
      ⟨world, .execute ⟨.evaluate σ first, .source (.argument target rest held index) :: frames⟩ ::
        older, answers, next⟩ := by
  cases target with
  | function head => exact .phase rfl rfl (.evaluated_argument rfl demanded) (.waiting rfl rfl)
  | data => exact .phase rfl rfl (.evaluated_argument rfl rfl) (.waiting rfl rfl)

/-- One data argument: evaluated, returned to its frame, and the traversal continued. -/
theorem argument_data (world : Streaming.World) (σ : Subst)
    (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target) {first : Atom} (data : DataAtom first)
    (rest held : List Atom) (index : Nat) (demanded : rawDemand registry target index = false)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    PSteps registry
      ⟨world, .execute ⟨.arguments σ target (first :: rest) held index, frames⟩ :: older, answers,
        next⟩
      ⟨world, .execute ⟨.arguments σ target rest (held ++ [first]) (index + 1), frames⟩ :: older,
        answers, next⟩ := by
  refine .head (evaluate_argument world σ target first rest held index demanded frames older answers
    next) ?_
  refine .head (evaluate_data world σ data _ older answers next) ?_
  refine .head (return_argument world ⟨first, σ⟩ target rest held index frames older answers next) ?_
  exact .single (alternatives world _ frames older answers next)

/-- **The argument traversal of data atoms.** -/
theorem arguments_data (world : Streaming.World) (σ : Subst)
    (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target)
    (demanded : ∀ index, rawDemand registry target index = false)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    ∀ (values held : List Atom) (index : Nat), (∀ v ∈ values, DataAtom v) →
      PSteps registry
        ⟨world, .execute ⟨.arguments σ target values held index, frames⟩ :: older, answers, next⟩
        ⟨world, .execute ⟨.arguments σ target [] (held ++ values) (index + values.length), frames⟩ ::
          older, answers, next⟩
  | [], held, index, _ => by
      simp only [List.append_nil, List.length_nil, Nat.add_zero]
      exact .refl
  | first :: rest, held, index, data => by
      refine .trans (argument_data world σ target (data first List.mem_cons_self) rest held index
        (demanded index) frames older answers next) ?_
      have later := arguments_data world σ target demanded frames older answers next rest
        (held ++ [first]) (index + 1) (fun v member => data v (List.mem_cons_of_mem _ member))
      rw [List.length_cons, show index + (rest.length + 1) = index + 1 + rest.length by omega]
      simpa only [List.append_assoc, List.singleton_append] using later

theorem phase_call (σ : Subst) {f : String} (args : List Atom) (notCollapse : f ≠ "collapse")
    (notOnce : f ≠ "once") :
    Streaming.phaseControl (.evaluate σ (.expression (.symbol f :: args))) = true := by
  unfold Streaming.phaseControl
  split <;> simp_all

theorem call_enter (world : Streaming.World) (σ : Subst) {f : String} {args : List Atom}
    (notCollapse : f ≠ "collapse") (notOnce : f ≠ "once")
    (notControl : Unifying.sourceControlForm (.expression (.symbol f :: args)) = false)
    (callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry registry world.privateCode).equations.any (·.head == f)) = true)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.evaluate σ (.expression (.symbol f :: args)), frames⟩ :: older, answers,
        next⟩
      ⟨world, .execute ⟨.arguments σ (.function f) args [] 0, frames⟩ :: older, answers, next⟩ :=
  .phase rfl (phase_call σ args notCollapse notOnce) (.call_enter rfl notControl callable) (.plain rfl)

theorem data_enter (world : Streaming.World) (σ : Subst) {f : String} {args : List Atom}
    (notCollapse : f ≠ "collapse") (notOnce : f ≠ "once")
    (notControl : Unifying.sourceControlForm (.expression (.symbol f :: args)) = false)
    (notCallable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry registry world.privateCode).equations.any (·.head == f)) = false)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.evaluate σ (.expression (.symbol f :: args)), frames⟩ :: older, answers,
        next⟩
      ⟨world, .execute ⟨.arguments σ .data (.symbol f :: args) [] 0, frames⟩ :: older, answers,
        next⟩ :=
  .phase rfl (phase_call σ args notCollapse notOnce) (.data_enter rfl notControl notCallable)
    (.plain rfl)

theorem construct (world : Streaming.World) (σ : Subst) (held : List Atom) (index : Nat)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.arguments σ .data [] held index, frames⟩ :: older, answers, next⟩
      ⟨world, .execute ⟨.returned [⟨.expression (held.map (Unifying.resolve σ)), σ⟩], frames⟩ ::
        older, answers, next⟩ :=
  .phase rfl rfl (.construct rfl) (.plain rfl)

theorem apply_equations (world : Streaming.World) (σ : Subst) {f : String} (held : List Atom)
    (index : Nat) {selected : Unifying.Control} {used : Nat}
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false)
    (chosen : Unifying.application (Unifying.codeRegistry registry world.privateCode)
      (Unifying.codeEquations world.state world.privateCode) f (held.map (Unifying.resolve σ)) σ
      world.uses = some (selected, used))
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.arguments σ (.function f) [] held index, frames⟩ :: older, answers, next⟩
      ⟨{world with uses := world.uses + used}, .execute ⟨selected, frames⟩ :: older, answers,
        next⟩ :=
  .phase rfl rfl (.equations rfl notIO (by rintro rfl; simp [StdLib.known] at notNative) notNative
    chosen) (.plain rfl)

/-! ### Bindings: ground, and fresh for every later use -/

theorem freshFor_renamed {use next : Nat} {bound σ : Subst} (before : use < next)
    (fresh : ∀ k, Unifying.FreshFor (next + k) σ) :
    ∀ k, Unifying.FreshFor (next + k) (Unifying.renameKeys use bound ++ σ) := by
  intro k name
  unfold Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup
  rw [List.find?_append]
  have missing : (Unifying.renameKeys use bound).find?
      (fun p => p.1 == Unifying.freshName (next + k) name) = none := by
    rw [List.find?_eq_none]
    intro p member
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp member
    simp only [beq_iff_eq]
    intro same
    have := (ScopedSource.freshName_equal_iff use (next + k) q.1 name).mp same
    omega
  have outer := fresh k name
  unfold Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup at outer
  rw [missing, Option.none_or]
  exact outer

theorem groundRange_renamed {use : Nat} {bound σ : Subst} (boundRange : Unifying.GroundRange bound)
    (range : Unifying.GroundRange σ) : Unifying.GroundRange (Unifying.renameKeys use bound ++ σ) := by
  intro p member
  rcases List.mem_append.mp member with inRenamed | inOuter
  · obtain ⟨q, inBound, rfl⟩ := List.mem_map.mp inRenamed
    exact boundRange q inBound
  · exact range p inOuter

theorem matchValues_groundRange : ∀ (patterns values : List Atom) (current bound : Subst),
    Unifying.GroundRange current → (∀ v ∈ values, isGroundAtom v = true) →
    SpaceSemantics.matchValue.matchValues current patterns values = some bound →
    Unifying.GroundRange bound
  | [], [], current, bound, range, _, matched => by
      simp only [SpaceSemantics.matchValue.matchValues, Option.some.injEq] at matched
      subst matched
      exact range
  | [], _ :: _, _, _, _, _, matched => by simp [SpaceSemantics.matchValue.matchValues] at matched
  | _ :: _, [], _, _, _, _, matched => by simp [SpaceSemantics.matchValue.matchValues] at matched
  | pattern :: patterns, value :: values, current, bound, range, ground, matched => by
      simp only [SpaceSemantics.matchValue.matchValues, Option.bind_eq_bind] at matched
      cases first : SpaceSemantics.matchValue current pattern value with
      | none => simp [first] at matched
      | some middle =>
          rw [first, Option.bind_some] at matched
          have middleRange := (Unifying.unifyPattern_ground
            (Unifying.atomSize pattern + Unifying.atomSize value + 1) current pattern value range
            (ground value List.mem_cons_self) (by omega)).2 middle first
          exact matchValues_groundRange patterns values middle bound middleRange
            (fun v member => ground v (List.mem_cons_of_mem _ member)) matched

theorem resolve_ground (σ : Subst) {a : Atom} (ground : isGroundAtom a = true) :
    Unifying.resolve σ a = a :=
  Unifying.applySubst_ground σ a ground

theorem map_resolve_ground (σ : Subst) {values : List Atom}
    (ground : ∀ v ∈ values, isGroundAtom v = true) : values.map (Unifying.resolve σ) = values := by
  induction values with
  | nil => rfl
  | cons v rest ih =>
      rw [List.map_cons, resolve_ground σ (ground v List.mem_cons_self),
        ih fun w member => ground w (List.mem_cons_of_mem _ member)]

end PeTTaRuns

/-! ## The call's region, as PeTTa selects it -/

/-- The bodies of the candidate equations whose argument patterns match the values, in order. -/
def matchingBodies (values : List Atom) (chosen : List SpaceSemantics.Equation) : List Atom :=
  chosen.filterMap fun e =>
    (SpaceSemantics.matchValue.matchValues [] e.arguments values).map fun _ => e.body

theorem regionBodies_eq (atoms : List Atom) (f : String) (args : List Atom) :
    regionBodies atoms f args = matchingBodies args
      (Unifying.candidates (atoms.filterMap LiveEquations.equationOfRow) f args.length) := by
  induction atoms with
  | nil => rfl
  | cons row rows ih =>
      simp only [regionBodies, matchingBodies, Unifying.candidates] at ih ⊢
      cases found : LiveEquations.equationOfRow row with
      | none =>
          have outside : pettaCallRegion f args row = false := pettaCallRegion_not_equation found
          simp [outside, found, ih]
      | some e =>
          cases matched : SpaceSemantics.matchValue.matchValues [] e.arguments args with
          | none =>
              by_cases selected : (e.head == f && e.arguments.length == args.length) = true
              · simp [pettaCallRegion, found, matched, selected, ih]
              · simp [pettaCallRegion, found, matched, selected, ih]
          | some bound =>
              by_cases selected : (e.head == f && e.arguments.length == args.length) = true
              · simp [pettaCallRegion, found, matched, selected, ih]
              · simp [pettaCallRegion, found, matched, selected, ih]

theorem regionBodies_cons (row : Atom) (rows : List Atom) (f : String) (args : List Atom) :
    regionBodies (row :: rows) f args =
      (if pettaCallRegion f args row = true then
        ((LiveEquations.equationOfRow row).map (·.body)).toList else []) ++ regionBodies rows f args := by
  unfold regionBodies
  by_cases inside : pettaCallRegion f args row = true
  · cases found : LiveEquations.equationOfRow row <;> simp [inside, found]
  · simp [inside]

theorem mem_regionBodies {atoms : List Atom} {f : String} {args : List Atom} {b : Atom}
    (member : b ∈ regionBodies atoms f args) :
    ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = args.length ∧ e.body = b := by
  rw [regionBodies_eq] at member
  obtain ⟨e, chosen, found⟩ := List.mem_filterMap.mp member
  obtain ⟨live, selected⟩ := List.mem_filter.mp chosen
  simp only [Bool.and_eq_true, beq_iff_eq] at selected
  cases matched : SpaceSemantics.matchValue.matchValues [] e.arguments args with
  | none => simp [matched] at found
  | some _ =>
      simp only [matched, Option.map_some, Option.some.injEq] at found
      exact ⟨e, live, selected.1, selected.2, found⟩

theorem regionBodies_nil_of_no_equation {atoms : List Atom} {f : String} (args : List Atom)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true) :
    regionBodies atoms f args = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro b member
  obtain ⟨e, live, head, _, _⟩ := mem_regionBodies member
  have different := List.all_eq_true.mp noEquation e live
  simp [head] at different

/-! ## PeTTa evaluates the fragment -/

open PeTTaRuns in
/-- **The frames deliver the value `v` as `K v`**: from any reached world over the translation's
store, with bindings that are ground and leave every later use fresh, the job returning `v` to the
frames runs to its end, appends answers whose values are `K v`, and leaves the older jobs. -/
def Delivers (atoms : List Atom) (frames : List Streaming.Frame) (K : Atom → List Atom)
    (v : Atom) : Prop :=
  ∀ (world : Streaming.World) (σ : Subst), world.state = store atoms → world.privateCode = [] →
    Unifying.GroundRange σ → (∀ k, Unifying.FreshFor (world.uses + k) σ) →
    ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = K v ∧
        PSteps (translate atoms)
          ⟨world, .execute ⟨.returned [⟨v, σ⟩], frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

open PeTTaRuns in
/-- **PeTTa's streaming machine evaluates `t` to the answers `L`**, under any frames that deliver
each of them: from any reached world over the translation's store, with bindings that are ground
and leave every later use fresh, the job of `t` runs to its end and appends, in order, what the
frames make of each answer. At the root (no frame) that is the answers themselves. -/
def PeTTaEvaluates (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ (frames : List Streaming.Frame) (K : Atom → List Atom), (∀ v ∈ L, Delivers atoms frames K v) →
  ∀ (world : Streaming.World) (σ : Subst), world.state = store atoms → world.privateCode = [] →
    Unifying.GroundRange σ → (∀ k, Unifying.FreshFor (world.uses + k) σ) →
    ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = L.flatMap K ∧
        PSteps (translate atoms)
          ⟨world, .execute ⟨.evaluate σ t, frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

theorem flatMap_root (L : List Atom) : L.flatMap (fun v => [v]) = L := by
  induction L with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

namespace PeTTaRuns

/-- **The root delivers an answer by recording it.** -/
theorem delivers_root (atoms : List Atom) {v : Atom} (answerable : Answerable v) :
    Delivers atoms [] (fun v => [v]) v := by
  intro world σ _ _ _ _ older answers next
  exact ⟨world.uses, [⟨v, σ⟩], le_rfl, by simp [resolve_ground σ answerable.ground],
    .single (return_root world ⟨v, σ⟩ older answers next)⟩

theorem petta_data (atoms : List Atom) {d : Atom} (data : DataAtom d) :
    PeTTaEvaluates atoms d [d] := by
  intro frames K deliver world σ state privateCode range fresh older answers next
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver d List.mem_cons_self world σ state
    privateCode range fresh older answers next
  exact ⟨uses, out, grown, by simp [valuesOut],
    .head (evaluate_data world σ data frames older answers next) path⟩

/-- The clauses a call selects run one after another, each body to its end. -/
theorem run_clauses {atoms : List Atom} {σ : Subst} {values : List Atom}
    (ground : ∀ v ∈ values, isGroundAtom v = true) (range : Unifying.GroundRange σ)
    (frames : List Streaming.Frame) (K : Atom → List Atom) :
    ∀ (chosen : List SpaceSemantics.Equation) (use : Nat) (Ls : List (List Atom)),
      List.Forall₂ (fun b L => PeTTaEvaluates atoms b L ∧ isGroundAtom b = true)
        (matchingBodies values chosen) Ls →
      (∀ v ∈ Ls.flatten, Delivers atoms frames K v) →
      ∀ (world : Streaming.World), world.state = store atoms → world.privateCode = [] →
        use + chosen.length ≤ world.uses → (∀ k, Unifying.FreshFor (use + k) σ) →
        ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
          ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
            out.map (fun answer => Unifying.resolve answer.bindings answer.value) =
              Ls.flatten.flatMap K ∧
            PSteps (translate atoms)
              ⟨world, ((Unifying.renamedClauses σ values use chosen).map fun control =>
                .execute ⟨control, frames⟩) ++ older, answers, next⟩
              ⟨{world with uses := uses}, older, answers ++ out, next⟩
  | [], _, Ls, related, _, world, _, _, _, _, older, answers, next => by
      cases related
      refine ⟨world.uses, [], le_rfl, rfl, ?_⟩
      simp only [Unifying.renamedClauses, List.map_nil, List.nil_append, List.append_nil]
      exact .refl
  | e :: rest, use, Ls, related, deliver, world, state, privateCode, enough, fresh, older, answers,
      next => by
      have enough' : use + 1 + rest.length ≤ world.uses := by
        simp only [List.length_cons] at enough
        omega
      cases matched : SpaceSemantics.matchValue.matchValues [] e.arguments values with
      | none =>
          have skip : matchingBodies values (e :: rest) = matchingBodies values rest := by
            simp [matchingBodies, matched]
          rw [skip] at related
          have clauses : Unifying.renamedClauses σ values use (e :: rest) =
              Unifying.renamedClauses σ values (use + 1) rest := by
            simp [Unifying.renamedClauses, matched]
          rw [clauses]
          exact run_clauses ground range frames K rest (use + 1) Ls related deliver world state
            privateCode enough' (fun k => by
              have shifted := fresh (1 + k)
              rwa [← Nat.add_assoc] at shifted) older answers next
      | some bound =>
          have take : matchingBodies values (e :: rest) = e.body :: matchingBodies values rest := by
            simp [matchingBodies, matched]
          rw [take] at related
          cases related with
          | cons here later =>
              rename_i L Ls'
              have clauses : Unifying.renamedClauses σ values use (e :: rest) =
                  .evaluate (Unifying.renameKeys use bound ++ σ) (Unifying.rename use e.body) ::
                    Unifying.renamedClauses σ values (use + 1) rest := by
                simp [Unifying.renamedClauses, matched]
              rw [clauses, Unifying.rename_ground use e.body here.2]
              have boundRange := matchValues_groundRange e.arguments values [] bound
                (fun _ member => by cases member) ground matched
              have below : use < world.uses := by omega
              have outerFresh : ∀ k, Unifying.FreshFor (world.uses + k) σ := fun k => by
                have shifted := fresh (world.uses - use + k)
                rwa [show use + (world.uses - use + k) = world.uses + k by omega] at shifted
              obtain ⟨uses₁, out₁, grown₁, values₁, path₁⟩ := here.1 frames K
                (fun v member => deliver v (by
                  rw [List.flatten_cons]
                  exact List.mem_append_left _ member)) world
                (Unifying.renameKeys use bound ++ σ) state privateCode
                (groundRange_renamed boundRange range) (freshFor_renamed below outerFresh)
                (((Unifying.renamedClauses σ values (use + 1) rest).map fun control =>
                  .execute ⟨control, frames⟩) ++ older) answers next
              obtain ⟨uses₂, out₂, grown₂, values₂, path₂⟩ := run_clauses ground range frames K rest
                (use + 1) Ls' later
                (fun v member => deliver v (by
                  rw [List.flatten_cons]
                  exact List.mem_append_right _ member))
                {world with uses := uses₁} state privateCode (by simp only; omega)
                (fun k => by
                  have shifted := fresh (1 + k)
                  rwa [← Nat.add_assoc] at shifted) older (answers ++ out₁) next
              refine ⟨uses₂, out₁ ++ out₂, grown₁.trans grown₂, ?_, ?_⟩
              · rw [List.map_append, values₁, values₂, List.flatten_cons, List.flatMap_append]
              · simp only [List.map_cons, List.cons_append]
                rw [← List.append_assoc]
                exact path₁.trans path₂

/-- **A constructor application**: PeTTa builds the expression of the held values and delivers
it. -/
theorem petta_construct {atoms : List Atom} {vals : List Atom}
    (groundVals : ∀ v ∈ vals, isGroundAtom v = true) (frames : List Streaming.Frame)
    (K : Atom → List Atom) (deliver : Delivers atoms frames K (.expression vals))
    (world : Streaming.World) (σ : Subst) (state : world.state = store atoms)
    (privateCode : world.privateCode = []) (range : Unifying.GroundRange σ)
    (fresh : ∀ k, Unifying.FreshFor (world.uses + k) σ) (index : Nat)
    (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat) :
    ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
      out.map (fun answer => Unifying.resolve answer.bindings answer.value) = K (.expression vals) ∧
      PSteps (translate atoms)
        ⟨world, .execute ⟨.arguments σ .data [] vals index, frames⟩ :: older, answers, next⟩
        ⟨{world with uses := uses}, older, answers ++ out, next⟩ := by
  have step := construct (registry := translate atoms) world σ vals index frames older answers next
  rw [map_resolve_ground σ groundVals] at step
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver world σ state privateCode range fresh older
    answers next
  exact ⟨uses, out, grown, valuesOut, .head step path⟩

/-- **An application of a defined head to held values**: PeTTa selects the matching equations of
the translation in row order and runs each body to its end, under the same frames. With an empty
region it selects nothing and has no answer. -/
theorem petta_apply {atoms : List Atom} {f : String} {vals : List Atom}
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = vals.length)
    (groundVals : ∀ v ∈ vals, isGroundAtom v = true) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => PeTTaEvaluates atoms b L ∧ isGroundAtom b = true)
      (regionBodies atoms f vals) Ls)
    (frames : List Streaming.Frame) (K : Atom → List Atom)
    (deliver : ∀ v ∈ Ls.flatten, Delivers atoms frames K v)
    (world : Streaming.World) (σ : Subst) (state : world.state = store atoms)
    (privateCode : world.privateCode = []) (range : Unifying.GroundRange σ)
    (fresh : ∀ k, Unifying.FreshFor (world.uses + k) σ) (index : Nat)
    (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat) :
    ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
      out.map (fun answer => Unifying.resolve answer.bindings answer.value) = Ls.flatten.flatMap K ∧
      PSteps (translate atoms)
        ⟨world, .execute ⟨.arguments σ (.function f) [] vals index, frames⟩ :: older, answers, next⟩
        ⟨{world with uses := uses}, older, answers ++ out, next⟩ := by
  obtain ⟨e, live, head, arity⟩ := defined
  have liveEquations : Unifying.codeEquations world.state world.privateCode =
      atoms.filterMap LiveEquations.equationOfRow := by
    rw [state, privateCode]
    simp only [Unifying.codeEquations, List.nil_append, LiveEquations.liveEquations, store_core]
  set chosen := Unifying.candidates (atoms.filterMap LiveEquations.equationOfRow) f vals.length
    with chosenEq
  have arityKnown : vals.length ∈ Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
      (Unifying.codeRegistry (translate atoms) world.privateCode) f := by
    rw [privateCode]
    simp only [Mettapedia.Languages.MeTTa.PeTTa.Eval.arities, Unifying.codeRegistry, List.nil_append,
      translate_equations]
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨live, by simp [head]⟩, arity⟩
  have applied : Unifying.application (Unifying.codeRegistry (translate atoms) world.privateCode)
      (Unifying.codeEquations world.state world.privateCode) f
      (vals.map (Unifying.resolve σ)) σ world.uses =
      some (.sequence (Unifying.renamedClauses σ vals world.uses chosen) [], chosen.length) := by
    rw [map_resolve_ground σ groundVals, liveEquations]
    unfold Unifying.application
    rw [if_pos arityKnown]
    simp only
    rw [Unifying.selections_eq_renamedClauses range groundVals world.uses _ fresh]
    rfl
  have related : List.Forall₂ (fun b L => PeTTaEvaluates atoms b L ∧ isGroundAtom b = true)
      (matchingBodies vals chosen) Ls := by
    rw [chosenEq, ← regionBodies_eq]
    exact bodies
  obtain ⟨uses, out, grown, valuesOut, path⟩ := run_clauses groundVals range frames K chosen
    world.uses Ls related deliver {world with uses := world.uses + chosen.length} state privateCode
    (by simp only; omega) fresh older answers next
  refine ⟨uses, out, by simp only at grown; omega, valuesOut, ?_⟩
  refine .head (apply_equations world σ vals index notIO notNative applied frames older answers
    next) ?_
  refine .head (alternatives _ _ frames older answers next) ?_
  exact path

/-- **A constructor call**: PeTTa builds the expression from its evaluated items. -/
theorem petta_constructor {dispatch : GroundedDispatch} {atoms : List Atom} {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true) :
    PeTTaEvaluates atoms (.expression (.symbol f :: args)) [.expression (.symbol f :: args)] := by
  intro frames K deliver world σ state privateCode range fresh older answers next
  have notCallable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      false := by
    rw [privateCode, ordinary.notIO, ordinary.notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    apply List.any_eq_false.mpr
    intro e member
    have different := List.all_eq_true.mp noEquation e member
    simpa using different
  have items : ∀ v ∈ Atom.symbol f :: args, DataAtom v := by
    intro v member
    rcases List.mem_cons.mp member with rfl | inArgs
    · exact ordinary.head
    · exact ordinary.arguments v inArgs
  have groundItems : ∀ v ∈ Atom.symbol f :: args, isGroundAtom v = true :=
    fun v member => (answerable_of_data (items v member)).ground
  obtain ⟨uses, out, grown, valuesOut, path⟩ := petta_construct groundItems frames K
    (deliver _ List.mem_cons_self) world σ state privateCode range fresh
    (0 + (Atom.symbol f :: args).length) older answers next
  refine ⟨uses, out, grown, by simp [valuesOut], ?_⟩
  refine .head (data_enter world σ ordinary.notCollapse ordinary.notOnce ordinary.notControl
    notCallable frames older answers next) ?_
  have items := arguments_data (registry := translate atoms) world σ .data (fun _ => rfl) frames
    older answers next (Atom.symbol f :: args) [] 0 items
  rw [List.nil_append] at items
  exact items.trans path

/-- **A call of a defined head**: PeTTa evaluates its arguments, selects the matching equations of
the translation in row order, and runs each body to its end. With an empty region it selects
nothing and has no answer. -/
theorem petta_call {dispatch : GroundedDispatch} {atoms : List Atom} {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = args.length)
    {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => PeTTaEvaluates atoms b L ∧ isGroundAtom b = true)
      (regionBodies atoms f args) Ls) :
    PeTTaEvaluates atoms (.expression (.symbol f :: args)) Ls.flatten := by
  intro frames K deliver world σ state privateCode range fresh older answers next
  have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      true := by
    obtain ⟨e, live, head, _⟩ := defined
    rw [privateCode, ordinary.notIO, ordinary.notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    exact List.any_eq_true.mpr ⟨e, live, by simp [head]⟩
  have groundArgs : ∀ v ∈ args, isGroundAtom v = true :=
    fun v member => (answerable_of_data (ordinary.arguments v member)).ground
  obtain ⟨uses, out, grown, valuesOut, path⟩ := petta_apply ordinary.notIO ordinary.notNative
    defined groundArgs bodies frames K deliver world σ state privateCode range fresh
    (0 + args.length) older answers next
  refine ⟨uses, out, grown, valuesOut, ?_⟩
  refine .head (call_enter world σ ordinary.notCollapse ordinary.notOnce ordinary.notControl
    callable frames older answers next) ?_
  have entered := arguments_data (registry := translate atoms) world σ (.function f)
    (fun index => argumentIsRaw_false ordinary.notNative ordinary.untyped index) frames older
    answers next args [] 0 ordinary.arguments
  rw [List.nil_append] at entered
  exact entered.trans path

end PeTTaRuns

/-! ## Lists -/

theorem forall₂_of_forall_exists {α β : Type} {R : α → β → Prop} :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, R a b) → ∃ m, List.Forall₂ R l m
  | [], _ => ⟨[], .nil⟩
  | a :: l, each => by
      obtain ⟨b, here⟩ := each a List.mem_cons_self
      obtain ⟨m, rest⟩ := forall₂_of_forall_exists l fun x member =>
        each x (List.mem_cons_of_mem _ member)
      exact ⟨b :: m, .cons here rest⟩

theorem forall₂_left_exists {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (related : List.Forall₂ R l m) : ∀ a ∈ l, ∃ b, R a b := by
  induction related with
  | nil => intro a member; cases member
  | cons here _ ih =>
      intro a member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨_, here⟩
      · exact ih a inRest

theorem forall₂_right_exists {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (related : List.Forall₂ R l m) : ∀ b ∈ m, ∃ a, R a b := by
  induction related with
  | nil => intro b member; cases member
  | cons here _ ih =>
      intro b member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨_, here⟩
      · exact ih b inRest

theorem map_fixed {α : Type} {g : α → α} : ∀ {l : List α}, (∀ a ∈ l, g a = a) → l.map g = l
  | [], _ => rfl
  | a :: l, fixed => by
      rw [List.map_cons, fixed a List.mem_cons_self,
        map_fixed fun b member => fixed b (List.mem_cons_of_mem _ member)]

/-! ## What HE needs of a body -/

/-- What HE's run needs of an equation body of the fragment: it has no variable, is no `function`
form, is not `NotReducible` (which would make HE refuse the reduction), is neither `Empty` nor an
error, is fixed by every renaming of variables, and is ground. -/
structure BodyFacts (t : Atom) : Prop where
  closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs t name
  notFunction : ∀ policy : Policy, ¬ Completed.FunctionPending policy (Entry.Value.ofAtom t)
  notRefused : t ≠ Atom.notReducible
  notStopped : ¬ IsEmptyOrErrorRel t
  fixed : ∀ rename : String → String,
    Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename t = t
  ground : isGroundAtom t = true

theorem call_facts {dispatch : GroundedDispatch} {atoms : List Atom} {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args) : BodyFacts (.expression (.symbol f :: args)) := by
  have answerable := call_answerable ordinary.head ordinary.arguments
  refine ⟨answerable.closed, fun policy pending => ?_, (fun same => by cases same), ?_,
    fun rename => ?_, answerable.ground⟩
  · obtain ⟨⟨body, same⟩, _⟩ := pending
    rw [Entry.Value.erase_ofAtom] at same
    simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    have instruction := ordinary.notInstruction
    rw [same.1] at instruction
    simp [Minimal.embeddedInstruction] at instruction
  · rintro (same | ⟨tail, same⟩)
    · simp [Atom.empty] at same
    · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      cases ordinary.head with
      | symbol _ notError => exact notError same.1
  · simp only [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars,
      List.map_cons]
    rw [map_fixed fun a member => by
      cases ordinary.arguments a member <;>
        simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]]

theorem settles_facts {dispatch : GroundedDispatch} {atoms : List Atom} {t : Atom}
    (settles : Settles dispatch atoms t) : BodyFacts t := by
  cases settles with
  | data data notRefused =>
      refine ⟨(answerable_of_data data).closed, fun policy pending => ?_, notRefused, data.not_stopped,
        fun rename => by
          cases data <;> simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars],
        (answerable_of_data data).ground⟩
      obtain ⟨⟨body, same⟩, _⟩ := pending
      rw [Entry.Value.erase_ofAtom] at same
      cases data <;> cases same
  | constructor ordinary _ => exact call_facts ordinary
  | call ordinary _ _ => exact call_facts ordinary

/-! ## HE's machine, step by step -/

/-- **HE's machine evaluates `t` to the answers `L`**: from pending work on `t` under `%Undefined%`,
with any live list, scope, activation, continuation stack and publication prefix, HE's machine
returns a batch whose atoms are `L`, under the same stack. -/
def HEEvaluates (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result),
    ∃ results : List Result, results.map (fun result => result.1.erase) = L ∧
      Relation.ReflTransGen (HEStep dispatch lookup policy)
        ⟨Space.ofList atoms, .work (.atom live scope (Entry.Value.ofAtom t) Atom.undefinedType
          activation), stack, emitted⟩
        ⟨Space.ofList atoms, .returning results, stack, emitted⟩

namespace HERuns

open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeOccurrencesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel equalityGroundedSemantic)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (LogicalMergeRel)

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- Runs of HE's machine. -/
abbrev HESteps (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) :
    HEConfig → HEConfig → Prop :=
  Relation.ReflTransGen (HEStep dispatch lookup policy)

theorem read_closed (policy : Policy) (frame : Frame) {t : Atom}
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs t name) :
    frame.read policy (Entry.Value.ofAtom t) = Entry.Value.ofAtom t := by
  unfold Completed.Frame.read
  apply Entry.Value.substitute_variable_free
  intro name occurs
  rw [Entry.Value.erase_ofAtom] at occurs
  exact closed name occurs

theorem he_data (answers : AnswersUndefined lookup) (atoms : List Atom) {d : Atom}
    (data : DataAtom d) : HEEvaluates dispatch lookup policy atoms d [d] := by
  intro live scope activation stack emitted
  exact ⟨[(Entry.Value.ofAtom d, activation)], by simp,
    .single (CompleteRun.cast_step_frame answers _ data activation live scope stack emitted)⟩

/-- **The tuple traversal of data atoms under any activation.** -/
theorem tuple_steps (answers : AnswersUndefined lookup) (space : Space) :
    ∀ (values : List Atom), values ≠ [] → (∀ v ∈ values, DataAtom v) →
      ∀ (live : List Atom) (scope : List String) (frame : Frame) (stack : List Continuation)
        (emitted : List Result),
        HESteps dispatch lookup policy
          ⟨space, .work (.tuple live scope (values.map Entry.Value.ofAtom) frame), stack, emitted⟩
          ⟨space, .returning [(.expression .active (values.map Entry.Value.ofAtom), frame)], stack,
            emitted⟩
  | [], nonempty, _ => absurd rfl nonempty
  | [atom], _, data => by
      intro live scope frame stack emitted
      have here := data atom List.mem_cons_self
      refine .head (.internal .tupleSingleton) ?_
      refine .head (CompleteRun.cast_step_frame answers space here frame _ _ _ _) ?_
      refine .head (.internal .singleton) ?_
      rw [List.map_singleton (f := Completed.tupleSingleton), tupleSingleton_data here]
      exact .refl
  | atom :: next :: rest, _, data => by
      intro live scope frame stack emitted
      have here := data atom List.mem_cons_self
      have later : ∀ v ∈ next :: rest, DataAtom v := fun v member =>
        data v (List.mem_cons_of_mem _ member)
      have nextData := later next List.mem_cons_self
      refine .head (.internal .tupleCons) ?_
      refine .head (CompleteRun.cast_step_frame answers space here frame _ _ _ _) ?_
      refine .head (.internal .branches) ?_
      refine .head (.internal (.branchesContinue ?_)) ?_
      · simpa using here.not_stopped
      refine .trans (tuple_steps answers space (next :: rest) (List.cons_ne_nil _ _) later
        _ _ _ _ _) ?_
      refine .head (.internal .tupleTail) ?_
      rw [List.map_singleton (f := Completed.tuplePrepend _), tuplePrepend_data nextData rest]
      refine .head (.internal .append) ?_
      refine .head (.internal .branchesNil) ?_
      exact .single (.internal .prepend)

/-- **From pending work on an ordinary call to its equation query**, under any activation and
stack: the type-directed entry, the tuple traversal, the calls continuation. -/
theorem call_entry_steps (answers : AnswersUndefined lookup) {atoms : List Atom} {f : String}
    {args : List Atom} (data : ∀ a ∈ Atom.symbol f :: args, DataAtom a)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result) :
    HESteps dispatch lookup policy
      ⟨Space.ofList atoms, .work (.atom live scope
        (Entry.Value.ofAtom (.expression (.symbol f :: args))) Atom.undefinedType activation), stack,
        emitted⟩
      ⟨Space.ofList atoms, .work (.call live scope (callValue f args) Atom.undefinedType activation),
        .append (.calls live scope Atom.undefinedType []) ::
          .publish (.expression (.symbol f :: args)) :: stack, emitted⟩ := by
  have headData := data _ List.mem_cons_self
  have closed := (call_answerable headData fun a member =>
    data a (List.mem_cons_of_mem _ member)).closed
  have readCall := read_closed policy activation closed
  have entry : Entry.Rel policy.reentry
      (activation.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).status
      (activation.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase
      Atom.undefinedType .interpret := by
    have base := call_entry policy headData args
    rw [Completed.Frame.read_empty] at base
    rw [readCall]
    exact base
  have shape : activation.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args))) =
      .expression .active (Entry.Value.ofAtom (.symbol f) :: args.map Entry.Value.ofAtom) := by
    rw [readCall]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have occurrences : TypeOccurrencesRel ((Space.ofList atoms).atoms : Multiset Atom)
      (Entry.Value.ofAtom (.symbol f)).erase {Atom.undefinedType} := by
    rw [Entry.Value.erase_ofAtom]
    exact untyped_occurrences untyped
  have step := LocalStepWith.atomTuple (admission := .historical) (space := Space.ofList atoms)
    (dispatch := dispatch) (lookup := lookup) (live := live) (scope := scope) (stack := stack)
    entry shape occurrences
  have published : (activation.read policy
      (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase =
      .expression (.symbol f :: args) := by
    rw [readCall, Entry.Value.erase_ofAtom]
  rw [published] at step
  refine .head (.internal step) ?_
  refine .trans (tuple_steps answers _ (Atom.symbol f :: args) (List.cons_ne_nil _ _) data
    _ _ _ _ _) ?_
  refine .head (.internal .calls) ?_
  exact .single (.internal .callsCons)

theorem nonGrounded_call {atoms : List Atom} {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args) :
    NonGroundedCallRel dispatch (callValue f args).erase := by
  rw [callValue_erase]
  refine And.intro ?_ ordinary.notInstruction
  intro host
  obtain ⟨operator, arguments, same, executable⟩ := host
  simp only [Atom.expression.injEq, List.cons.injEq] at same
  rw [← same.1] at executable
  exact ordinary.notHost executable

/-- A row's block of an equation query: empty outside the region, one work inside it. -/
theorem block_of_region {live : List Atom} {query : Atom} {incoming : Bindings} {position : Nat}
    {row : Atom} {block : List EquationWork}
    (derived : EquationRowResultsRel live query incoming position row block) :
    (eqRegion live query incoming row = false → block = []) ∧
      (eqRegion live query incoming row = true → ∃ left right pattern body output,
        row = .expression [.symbol "=", left, right] ∧
          block = [⟨position, left, right, pattern, body, output⟩] ∧
          AlphaVariantRel live query incoming left right pattern body) := by
  constructor
  · intro outside
    exact (inert_of_eqRegion (by simp [outside]) position block).mp derived
  · intro inside
    cases derived with
    | irrelevant _ notEquation =>
        rw [eqRegion_not_equation notEquation] at inside
        cases inside
    | miss left right pattern body alpha noViable =>
        exfalso
        have inert : Inert live query incoming (.expression [.symbol "=", left, right]) := by
          intro position' block'
          constructor
          · intro derived'
            cases derived' with
            | irrelevant =>
                rename_i notEquation
                exact absurd rfl (notEquation _ _)
            | miss => rfl
            | hit =>
                exact absurd ⟨‹MatchRel _ _ _ _›, ‹LogicalMergeRel _ _ _›⟩
                  (noViable _ _ ‹AlphaVariantRel _ _ _ _ _ _ _› _ _)
          · rintro rfl
            exact .miss position' left right pattern body alpha noViable
        simp [eqRegion, inert] at inside
    | hit left right pattern body matched output alpha _ _ =>
        exact ⟨left, right, pattern, body, output, rfl, rfl, alpha⟩

/-- **HE's frontier of an ordinary call carries the bodies of the call's region, in row order**,
on programs of symbol-headed, `cons`-free equations, at every satisfiable incoming record. -/
theorem frontier_bodies {atoms live : List Atom} {f : String} {args : List Atom}
    {incoming : Bindings}
    (ground : ∀ value ∈ args,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars value = [])
    (satisfiable : ∃ model : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied model incoming)
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    (fixed : ∀ b ∈ regionBodies atoms f args, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (.expression (.symbol f :: args))
      incoming works) :
    works.map EquationWork.body = regionBodies atoms f args := by
  suffices key : ∀ (rows : List Atom) (k : Nat) (blocks : List (List EquationWork)),
      (∀ row ∈ rows, RegionsWithVariables.ConsFreeHeads row) →
      (∀ b ∈ regionBodies rows f args, ∀ rename : String → String,
        Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b) →
      List.Forall₂ (fun row block => EquationRowResultsRel live (.expression (.symbol f :: args))
        incoming row.2 row.1 block) (rows.zipIdx k) blocks →
      blocks.flatten.map EquationWork.body = regionBodies rows f args by
    cases frontier with
    | completed covered => exact key atoms 0 _ program fixed covered
  intro rows
  induction rows with
  | nil =>
      intro k blocks _ _ covered
      cases covered
      rfl
  | cons row rows ih =>
      intro k blocks program fixed covered
      rw [List.zipIdx_cons] at covered
      cases covered with
      | cons here rest =>
          rename_i block blocks'
          have agree := RegionsWithVariables.regions_agree_consFree (head := f) live ground
            satisfiable (program row List.mem_cons_self)
          rw [regionBodies_cons] at fixed ⊢
          have restEq := ih (k + 1) blocks' (fun r member => program r (List.mem_cons_of_mem _ member))
            (fun b member => fixed b (List.mem_append_right _ member)) rest
          rw [List.flatten_cons, List.map_append, restEq]
          cases inRegion : pettaCallRegion f args row with
          | false =>
              rw [(block_of_region here).1 (agree.trans inRegion)]
              simp
          | true =>
              obtain ⟨left, right, pattern, body, output, rfl, rfl, alpha⟩ :=
                (block_of_region here).2 (agree.trans inRegion)
              cases found : LiveEquations.equationOfRow (.expression [.symbol "=", left, right]) with
              | none =>
                  rw [pettaCallRegion_not_equation found] at inRegion
                  cases inRegion
              | some e =>
                  have shape := LiveEquations.equationOfRow_eq_some found
                  simp only [SpaceSemantics.Equation.toAtom, Atom.expression.injEq, List.cons.injEq]
                    at shape
                  obtain ⟨rename, _, _, renamedRight, _⟩ := alpha
                  have bodyEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq
                    renamedRight
                  have member : right ∈ (if pettaCallRegion f args
                      (.expression [.symbol "=", left, right]) = true then
                        ((LiveEquations.equationOfRow (.expression [.symbol "=", left, right])).map
                          (·.body)).toList else []) ++ regionBodies rows f args := by
                    rw [if_pos inRegion, found]
                    simp [shape.2.2.1]
                  have bodyIs : body = e.body := by
                    rw [bodyEq, fixed right member rename, shape.2.2.1]
                  rw [bodyIs]
                  simp

/-- **The equation loop**: each work's body is evaluated under its unifier's activation, and the
batches are concatenated in work order. -/
theorem equations_steps {atoms : List Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => HEEvaluates dispatch lookup policy atoms work.body L ∧
        BodyFacts work.body) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        ∃ results : List Result, results.map (fun result => result.1.erase) = Ls.flatten ∧
          HESteps dispatch lookup policy
            ⟨Space.ofList atoms, .work (.equations live scope original Atom.undefinedType activation
              works), stack, emitted⟩
            ⟨Space.ofList atoms, .returning results, stack, emitted⟩
  | [], Ls, _, related, stack, emitted => by
      cases related
      exact ⟨[], rfl, .single (.internal .equationsNil)⟩
  | work :: works, Ls, unifiers, related, stack, emitted => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨output, sameBindings, unified⟩ := unifiers work List.mem_cons_self
          obtain ⟨evaluates, facts⟩ := here
          have readBody := read_closed policy output facts.closed
          obtain ⟨R, eraseR, pathR⟩ := evaluates live scope output
            (.append (.boundaryBatch live scope none (.returned original Atom.undefinedType) []) ::
              .append (.equations live scope original Atom.undefinedType activation works) :: stack)
            emitted
          obtain ⟨R', eraseR', pathR'⟩ := equations_steps works Ls'
            (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
            (.prepend (R ++ []) :: stack) emitted
          refine ⟨(R ++ []) ++ R', ?_, ?_⟩
          · rw [List.append_nil, List.map_append, eraseR, eraseR', List.flatten_cons]
          · refine .head (.internal (.equationsCons sameBindings unified)) ?_
            rw [readBody]
            refine .head (.internal (.boundaryProducerRaw (facts.notFunction policy))) ?_
            refine .head (.internal .boundaryBatch) ?_
            refine .head (.internal .boundaryBatchCons) ?_
            refine .head (.internal .boundaryReturned) ?_
            refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
            · rw [Entry.Value.erase_ofAtom]
              exact facts.notRefused
            · rw [Entry.Value.erase_ofAtom]
              exact facts.notStopped
            refine .trans pathR ?_
            refine .head (.internal .append) ?_
            refine .head (.internal .boundaryBatchNil) ?_
            refine .head (.internal .prepend) ?_
            refine .head (.internal .append) ?_
            refine .trans pathR' ?_
            exact .single (.internal .prepend)

theorem success_all {α : Type} {isError : α → Bool} (raw : List α)
    (fine : ∀ item ∈ raw, isError item = false) :
    Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel isError raw raw := by
  cases raw with
  | nil => exact .allErrors fun _ member => by cases member
  | cons item rest =>
      have chosen := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := isError) (raw := item :: rest)
        ⟨item, List.mem_cons_self, fine item List.mem_cons_self⟩
      have same : (item :: rest).filter (fun x => !isError x) = item :: rest :=
        List.filter_eq_self.mpr fun x member => by simp [fine x member]
      rwa [same] at chosen

theorem readResult_closed (policy : Policy) (result : Result)
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs result.1.erase name) :
    Completed.readResult policy result = result := by
  unfold Completed.readResult Completed.Frame.read
  rw [Entry.Value.substitute_variable_free _ _ _ closed]

/-- **The call's batch is published**: the calls continuation closes, and the publication keeps
every answer, since none is an error. -/
theorem finish_steps {atoms : List Atom} {live : List Atom} {scope : List String} (c : Atom)
    (results : List Result) (clean : ∀ r ∈ results, Answerable r.1.erase)
    (stack : List Continuation) (emitted : List Result) :
    ∃ published : List Result,
      published.map (fun r => r.1.erase) = results.map (fun r => r.1.erase) ∧
      HESteps dispatch lookup policy
        ⟨Space.ofList atoms, .returning results,
          .append (.calls live scope Atom.undefinedType []) :: .publish c :: stack, emitted⟩
        ⟨Space.ofList atoms, .returning published, stack, emitted⟩ := by
  have unchanged : (results ++ []).map (Completed.readResult policy) = results := by
    rw [List.append_nil]
    exact map_fixed fun r member => readResult_closed policy r (clean r member).closed
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ((results ++ []).map (Completed.readResult policy)) results := by
    rw [unchanged]
    exact success_all results fun r member => (clean r member).notError
  refine ⟨results.map (Completed.publishResult policy c), ?_, ?_⟩
  · simp [Completed.publishResult]
  · refine .head (.internal .append) ?_
    refine .head (.internal .callsNil) ?_
    refine .head (.internal .prepend) ?_
    exact .single (.internal (.publish selected))

theorem ordinary_data {dispatch : GroundedDispatch} {atoms : List Atom} {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args) :
    ∀ a ∈ Atom.symbol f :: args, DataAtom a := by
  intro a member
  rcases List.mem_cons.mp member with rfl | inArgs
  · exact ordinary.head
  · exact ordinary.arguments a inArgs

theorem value_not_error {f : String} {vals : List Atom} {value : Entry.Value}
    (head : DataAtom (.symbol f)) (erased : value.erase = .expression (.symbol f :: vals)) :
    ¬ IsErrorRel value.erase := by
  rw [erased]
  rintro ⟨tail, same⟩
  simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
  cases head with
  | symbol _ notError => exact notError same.1

theorem value_nonGrounded {f : String} {vals : List Atom} {value : Entry.Value}
    (notHost : ¬ dispatch.executable (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (erased : value.erase = .expression (.symbol f :: vals)) :
    NonGroundedCallRel dispatch value.erase := by
  rw [erased]
  refine And.intro ?_ notInstruction
  intro host
  obtain ⟨operator, arguments, same, executable⟩ := host
  simp only [Atom.expression.injEq, List.cons.injEq] at same
  rw [← same.1] at executable
  exact notHost executable

/-- **HE's equation query on a call value with an empty region**: no work, and the call value is
returned as it is (`callAbsent`). Any call value whose atom is `(f v₁ … vₙ)` with ground `vᵢ`. -/
theorem he_query_absent {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : DataAtom (.symbol f)) (notHost : ¬ dispatch.executable (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (ground : ∀ v ∈ vals,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars v = [])
    (empty : regionBodies atoms f vals = []) (live : List Atom) (scope : List String)
    (activation : Frame) (value : Entry.Value) (erased : value.erase = .expression (.symbol f :: vals))
    (stack : List Continuation) (emitted : List Result) :
    HESteps dispatch lookup policy
      ⟨Space.ofList atoms, .work (.call live scope value Atom.undefinedType activation), stack,
        emitted⟩
      ⟨Space.ofList atoms, .returning [(value, activation)], stack, emitted⟩ := by
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: vals)) activation.bindings
  have bodies := frontier_bodies ground activation.certified.satisfiable program
    (by rw [empty]; intro b member; cases member) frontier
  rw [empty] at bodies
  have none : works = [] := List.map_eq_nil_iff.mp bodies
  subst none
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      value.erase activation.bindings [] := by
    rw [erased]
    exact frontier
  exact .single (.internal (.callAbsent (value_not_error head erased)
    (value_nonGrounded notHost notInstruction erased) frontier'))

/-- **HE's equation query on a call value with a nonempty region**: the query fires, each work's
body is evaluated under its unifier's activation, and the batches come back in row order. -/
theorem he_query_equations {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : DataAtom (.symbol f)) (notHost : ¬ dispatch.executable (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (ground : ∀ v ∈ vals,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars v = [])
    (nonempty : regionBodies atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => HEEvaluates dispatch lookup policy atoms b L ∧ BodyFacts b ∧
      ∀ a ∈ L, Answerable a) (regionBodies atoms f vals) Ls)
    (live : List Atom) (scope : List String) (activation : Frame) (value : Entry.Value)
    (erased : value.erase = .expression (.symbol f :: vals)) (stack : List Continuation)
    (emitted : List Result) :
    ∃ results : List Result, results.map (fun result => result.1.erase) = Ls.flatten ∧
      HESteps dispatch lookup policy
        ⟨Space.ofList atoms, .work (.call live scope value Atom.undefinedType activation), stack,
          emitted⟩
        ⟨Space.ofList atoms, .returning results, stack, emitted⟩ := by
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: vals)) activation.bindings
  have fixed : ∀ b ∈ regionBodies atoms f vals, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    intro b member
    obtain ⟨L, related⟩ := forall₂_left_exists bodies b member
    exact related.2.1.fixed
  have bodiesEq := frontier_bodies ground activation.certified.satisfiable program fixed frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    exact nonempty bodiesEq.symm
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      value.erase activation.bindings works := by
    rw [erased]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding activation.environment value
        (Entry.Value.ofAtom w.pattern) output.environment := by
    intro w member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
    exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
  have related : List.Forall₂ (fun w L => HEEvaluates dispatch lookup policy atoms w.body L ∧
      BodyFacts w.body) works Ls := by
    have onWorks := bodies
    rw [← bodiesEq] at onWorks
    exact (List.forall₂_map_left_iff.mp onWorks).imp fun _ _ both => ⟨both.1, both.2.1⟩
  obtain ⟨R, eraseR, pathR⟩ := equations_steps works Ls unifiers related stack emitted
  exact ⟨R, eraseR, .head (.internal (.callEquations (value_not_error head erased)
    (value_nonGrounded notHost notInstruction erased) frontier' worksNonempty)) pathR⟩

theorem results_answerable {results : List Result} {Ls : List (List Atom)} {bodies : List Atom}
    {R : Atom → List Atom → Prop}
    (related : List.Forall₂ (fun b L => R b L ∧ ∀ a ∈ L, Answerable a) bodies Ls)
    (erased : results.map (fun result => result.1.erase) = Ls.flatten) :
    ∀ r ∈ results, Answerable r.1.erase := by
  intro r member
  have inFlat : r.1.erase ∈ Ls.flatten := by
    rw [← erased]
    exact List.mem_map.mpr ⟨r, member, rfl⟩
  obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp inFlat
  obtain ⟨b, both⟩ := forall₂_right_exists related L inLs
  exact both.2 _ inner

theorem ground_typeVars {a : Atom} (answerable : Answerable a) :
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars a = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  exact answerable.closed name
    ((Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars a name).mpr member)

/-- **A call with an empty region**: HE's query finds no work, and the call answers itself. -/
theorem he_absent (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (empty : regionBodies atoms f args = []) :
    HEEvaluates dispatch lookup policy atoms (.expression (.symbol f :: args))
      [.expression (.symbol f :: args)] := by
  intro live scope activation stack emitted
  have clean : ∀ r ∈ [(callValue f args, activation)], Answerable r.1.erase := by
    intro r member
    rw [List.mem_singleton] at member
    subst member
    rw [callValue_erase]
    exact call_answerable ordinary.head ordinary.arguments
  obtain ⟨published, erased, finish⟩ := finish_steps (dispatch := dispatch) (lookup := lookup)
    (policy := policy) (atoms := atoms) (live := live) (scope := scope)
    (.expression (.symbol f :: args)) [(callValue f args, activation)] clean stack emitted
  refine ⟨published, by rw [erased]; simp [callValue_erase], ?_⟩
  refine .trans (call_entry_steps answers (ordinary_data ordinary) ordinary.untyped live scope
    activation stack emitted) ?_
  refine .trans (he_query_absent program ordinary.head ordinary.notHost ordinary.notInstruction
    (fun v member => ground_typeVars (answerable_of_data (ordinary.arguments v member))) empty
    live scope activation _ (callValue_erase f args) _ emitted) ?_
  exact finish

/-- **A call with a nonempty region**: HE's query fires, each work's body is evaluated, and the
batches are published in row order. -/
theorem he_call (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (nonempty : regionBodies atoms f args ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => HEEvaluates dispatch lookup policy atoms b L ∧ BodyFacts b ∧
      ∀ a ∈ L, Answerable a) (regionBodies atoms f args) Ls) :
    HEEvaluates dispatch lookup policy atoms (.expression (.symbol f :: args)) Ls.flatten := by
  intro live scope activation stack emitted
  obtain ⟨R, eraseR, pathR⟩ := he_query_equations program ordinary.head ordinary.notHost
    ordinary.notInstruction
    (fun v member => ground_typeVars (answerable_of_data (ordinary.arguments v member))) nonempty
    bodies live scope activation _ (callValue_erase f args)
    (.append (.calls live scope Atom.undefinedType []) ::
      .publish (.expression (.symbol f :: args)) :: stack) emitted
  have clean := results_answerable (bodies.imp fun _ _ both => ⟨both.1, both.2.2⟩) eraseR
  obtain ⟨published, erased, finish⟩ := finish_steps (dispatch := dispatch) (lookup := lookup)
    (policy := policy) (atoms := atoms) (live := live) (scope := scope)
    (.expression (.symbol f :: args)) R clean stack emitted
  refine ⟨published, by rw [erased, eraseR], ?_⟩
  refine .trans (call_entry_steps answers (ordinary_data ordinary) ordinary.untyped live scope
    activation stack emitted) ?_
  exact pathR.trans finish

/-- HE's top-level publication moves a returned batch to the emitted answers, in order. -/
theorem publish_all (space : Space) : ∀ (results emitted : List Result),
    HESteps dispatch lookup policy ⟨space, .returning results, [], emitted⟩
      ⟨space, .returning [], [], emitted ++ results⟩
  | [], emitted => by
      rw [List.append_nil]
  | r :: rs, emitted => by
      refine .head .publish ?_
      have later := publish_all space rs (emitted ++ [r])
      rwa [List.append_assoc, List.singleton_append] at later

end HERuns

/-! ## Both machines on the whole fragment -/

section Joint

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **Both machines evaluate every settling term to the same answer list**: one induction on the
program's settling derivation, with the list shared by the two machines. -/
theorem settles_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {t : Atom}
    (settles : Settles dispatch atoms t) :
    ∃ L : List Atom, (∀ a ∈ L, Answerable a) ∧ HEEvaluates dispatch lookup policy atoms t L ∧
      PeTTaEvaluates atoms t L := by
  induction settles with
  | @data d data _ =>
      refine ⟨[d], fun a member => ?_, HERuns.he_data answers atoms data,
        PeTTaRuns.petta_data atoms data⟩
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data data
  | @constructor f args ordinary noEquation =>
      refine ⟨[.expression (.symbol f :: args)], fun a member => ?_,
        HERuns.he_absent answers program ordinary (regionBodies_nil_of_no_equation args noEquation),
        PeTTaRuns.petta_constructor ordinary noEquation⟩
      rw [List.mem_singleton] at member
      subst member
      exact call_answerable ordinary.head ordinary.arguments
  | @call f args ordinary nonempty settled ih =>
      have each : ∀ b ∈ regionBodies atoms f args, ∃ L, Settles dispatch atoms b ∧
          (∀ a ∈ L, Answerable a) ∧ HEEvaluates dispatch lookup policy atoms b L ∧
          PeTTaEvaluates atoms b L := by
        intro b member
        obtain ⟨L, rest⟩ := ih b member
        exact ⟨L, settled b member, rest⟩
      obtain ⟨Ls, related⟩ := forall₂_of_forall_exists _ each
      have defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
          e.arguments.length = args.length := by
        obtain ⟨b, inRegion⟩ := List.exists_mem_of_ne_nil _ nonempty
        obtain ⟨e, live, head, arity, _⟩ := mem_regionBodies inRegion
        exact ⟨e, live, head, arity⟩
      refine ⟨Ls.flatten, ?_, HERuns.he_call answers program ordinary nonempty
          (related.imp fun _ _ both => ⟨both.2.2.1, settles_facts both.1, both.2.1⟩),
        PeTTaRuns.petta_call ordinary defined
          (related.imp fun _ _ both => ⟨both.2.2.2, (settles_facts both.1).ground⟩)⟩
      intro a member
      obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
      obtain ⟨b, both⟩ := forall₂_right_exists related L inLs
      exact both.2.1 a inner

/-- A finished streaming state stays as it is. -/
theorem advance_finished (registry : SpaceSemantics.Program) (world : Streaming.World)
    (answers : List Unifying.Answer) (next fuel : Nat) :
    Streaming.advance registry fuel ⟨world, [], answers, next⟩ = ⟨world, [], answers, next⟩ :=
  Mettapedia.Machines.BoundedDeterministicRun.run_of_none _ _ rfl fuel

/-- Once PeTTa's run has no pending job, more fuel changes nothing. -/
theorem advance_stable {registry : SpaceSemantics.Program} {state : Streaming.State} {m : Nat}
    (done : (Streaming.advance registry m state).agenda = []) :
    ∀ n, m ≤ n → Streaming.advance registry n state = Streaming.advance registry m state := by
  intro n bigger
  rw [show n = m + (n - m) by omega, Streaming.advance_add]
  generalize Streaming.advance registry m state = reached at done ⊢
  cases reached with
  | mk world agenda answers next =>
      simp only at done
      subst done
      exact advance_finished registry world answers next _

/-- **PeTTa's complete run** of a settling ground term from its entry: from some fuel on, its
values are the term's answers. -/
theorem petta_complete {atoms : List Atom} {c : Atom} {L : List Atom}
    (ground : isGroundAtom c = true) (clean : ∀ a ∈ L, Answerable a)
    (evaluates : PeTTaEvaluates atoms c L) :
    ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
      (Streaming.enter { state := store atoms } c)) = L := by
  have entered : Streaming.enter { state := store atoms } c =
      ⟨{ state := store atoms, uses := 1 }, [.execute ⟨.evaluate [] c, []⟩], [], 0⟩ := by
    simp only [Streaming.enter, Unifying.rename_ground 0 c ground]
  obtain ⟨uses, out, _, valuesOut, path⟩ := evaluates [] (fun v => [v])
    (fun v member => PeTTaRuns.delivers_root atoms (clean v member))
    { state := store atoms, uses := 1 } [] rfl rfl (fun _ member => by cases member)
    (fun _ _ => rfl) [] [] 0
  rw [flatMap_root] at valuesOut
  obtain ⟨N, reached⟩ := (Streaming.path_iff_advance _ _ _).mp path
  refine ⟨N, fun n bigger => ?_⟩
  rw [entered, show n = N + (n - N) by omega, Streaming.advance_add, reached, advance_finished]
  simpa [Streaming.values] using valuesOut

/-- **HE's complete run** of a term from its entry configuration: the published answers are the
term's answers, and the final configuration is observed complete. -/
theorem he_complete {atoms : List Atom} {c : Atom} {L : List Atom}
    (evaluates : HEEvaluates dispatch lookup policy atoms c L) :
    ∃ heAnswers : List Result, heAnswers.map (fun r => r.1.erase) = L ∧
      Relation.ReflTransGen (HEStep dispatch lookup policy)
        (load (Space.ofList atoms) c Atom.undefinedType)
        ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
      observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers := by
  obtain ⟨R, eraseR, path⟩ := evaluates [] [] Completed.Frame.empty [] []
  exact ⟨R, eraseR, path.trans (HERuns.publish_all _ R []), rfl⟩

/-- **The answers agree over the fragment** (the generalization of
`CompleteRun.double_complete_run`). For a program of symbol-headed, `cons`-free equations and a
term that settles in it (a flat ground call of data atoms whose head is undeclared, no host
operation and no instruction, with termination and coverage stated on the program): HE's machine,
with any cast lookup meeting `AnswersUndefined` and any policy, runs from its entry configuration to
a completed phase, and from some fuel on PeTTa's streaming run of the translation yields exactly the
atoms HE published, in the same order and with the same multiplicities. -/
theorem answers_agree (dispatch : GroundedDispatch) {lookup : CastLookup}
    (answers : AnswersUndefined lookup) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {c : Atom}
    (settles : Settles dispatch atoms c) :
    ∃ (heAnswers : List Result) (N : Nat),
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers ∧
        ∀ n, N ≤ n →
          Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = heAnswers.map (fun r => r.1.erase) := by
  obtain ⟨L, clean, he, petta⟩ := settles_agree (policy := policy) answers program settles
  obtain ⟨R, eraseR, path, observed⟩ := he_complete he
  obtain ⟨N, stable⟩ := petta_complete (settles_facts settles).ground clean petta
  exact ⟨R, N, path, observed, fun n bigger => by rw [stable n bigger, eraseR]⟩

/-- **The answer bags agree over the fragment**: the same statement read as bags. Order is not an
observation in either dialect; multiplicity is, and it is kept. -/
theorem answer_bags_agree (dispatch : GroundedDispatch) {lookup : CastLookup}
    (answers : AnswersUndefined lookup) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {c : Atom}
    (settles : Settles dispatch atoms c) :
    ∃ (heAnswers : List Result) (N : Nat),
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers ∧
        ∀ n, N ≤ n →
          ((heAnswers.map fun r => r.1.erase : List Atom) : Multiset Atom) =
            (Streaming.values (Streaming.advance (translate atoms) n
              (Streaming.enter { state := store atoms } c)) : Multiset Atom) := by
  obtain ⟨R, N, path, observed, agree⟩ := answers_agree dispatch answers policy program settles
  exact ⟨R, N, path, observed, fun n bigger => by rw [agree n bigger]⟩

/-- **With either of HE's own cast lookups** (the historical list storage and the scoped fresh
variants), the answer bags agree on every settling term. -/
theorem answer_bags_agree_with_he_lookups (dispatch : GroundedDispatch) (policy : Policy)
    {atoms : List Atom} (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    {c : Atom} (settles : Settles dispatch atoms c) :
    ∀ lookup ∈ [Completed.rawLookup, Completed.scopedLookup],
      ∃ (heAnswers : List Result) (N : Nat),
        Relation.ReflTransGen (HEStep dispatch lookup policy)
            (load (Space.ofList atoms) c Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
          observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers ∧
          ∀ n, N ≤ n →
            ((heAnswers.map fun r => r.1.erase : List Atom) : Multiset Atom) =
              (Streaming.values (Streaming.advance (translate atoms) n
                (Streaming.enter { state := store atoms } c)) : Multiset Atom) := by
  intro lookup member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact answer_bags_agree dispatch raw_answers policy program settles
  · exact answer_bags_agree dispatch scoped_answers policy program settles

/-! ## Where the answers differ inside the fragment -/

/-- **An uncovered call: HE answers the call itself, PeTTa answers nothing.** For an ordinary call
whose head has an equation of the call's arity but no row whose patterns match it (an empty
region), HE's equation query finds no work and HE publishes the call itself as its one answer
(`callAbsent`), while PeTTa's call selects no clause and yields no value (a failed goal). The bags
are `{c}` and `{}`. This is the one difference inside the fragment of flat ground calls on
symbol-headed, `cons`-free programs; `Settles` excludes it by asking for coverage. -/
theorem uncovered_calls_differ (dispatch : GroundedDispatch) {lookup : CastLookup}
    (answers : AnswersUndefined lookup) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (empty : regionBodies atoms f args = [])
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = args.length) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers ∧
        heAnswers.map (fun r => r.1.erase) = [.expression (.symbol f :: args)]) ∧
    ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
      (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))) = [] := by
  constructor
  · obtain ⟨R, eraseR, path, observed⟩ := he_complete (dispatch := dispatch) (lookup := lookup)
      (policy := policy) (HERuns.he_absent answers program ordinary empty)
    exact ⟨R, path, observed, eraseR⟩
  · have nothing : PeTTaEvaluates atoms (.expression (.symbol f :: args))
        ([] : List (List Atom)).flatten :=
      PeTTaRuns.petta_call ordinary defined (by rw [empty]; exact .nil)
    exact petta_complete (call_answerable ordinary.head ordinary.arguments).ground
      (fun _ member => by cases member) nothing

end Joint

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)

/-- A symbol. -/
abbrev sym (name : String) : Atom := .symbol name
/-- An application `(head args…)`. -/
abbrev app (head : String) (args : List Atom) : Atom := .expression (.symbol head :: args)
/-- An equation row `(= lhs rhs)`. -/
abbrev rule (lhs rhs : Atom) : Atom := .expression [.symbol "=", lhs, rhs]

theorem rule_consFree {f : String} {args : List Atom} {rhs : Atom}
    (free : ∀ a ∈ args, RegionsWithVariables.ConsFree a) :
    RegionsWithVariables.ConsFreeHeads (rule (app f args) rhs) := by
  intro lhs rhs' same
  cases same
  exact ⟨f, args, rfl, free⟩

/-- `coin` has two equations; `toss` calls `coin` and also has a data body; `pick` has a literal
and a variable pattern; `(p a)` is no equation. -/
def coinRows : List Atom :=
  [rule (app "coin" []) (sym "heads"), rule (app "coin" []) (sym "tails"),
   rule (app "toss" []) (app "coin" []), rule (app "toss" []) (sym "edge"),
   rule (app "pick" [.grounded (.int 1)]) (sym "one"), rule (app "pick" [.var "x"]) (sym "any"),
   .expression [sym "p", sym "a"]]

theorem coin_program : ∀ row ∈ coinRows, RegionsWithVariables.ConsFreeHeads row := by
  intro row member
  simp only [coinRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rule_consFree (by simp)
  · exact rule_consFree (by simp)
  · exact rule_consFree (by simp)
  · exact rule_consFree (by simp)
  · exact rule_consFree fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .grounded _
  · exact rule_consFree fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .var _
  · intro lhs rhs same
    simp at same

theorem ordinary_nullary (name : String) (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    (untyped : (Space.ofList coinRows).atoms.filter (typeRegion (.symbol name)) = [])
    (notInstruction : Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead name = false)
    (notNative : StdLib.known name = false)
    (notControl : Unifying.sourceControlForm (.expression [.symbol name]) = false)
    (notCollapse : name ≠ "collapse") (notOnce : name ≠ "once") :
    Ordinary noHost coinRows name [] :=
  ⟨.symbol notEmpty notError, by simp, untyped, fun impossible => impossible, notInstruction, notIO,
    notNative, notControl, notCollapse, notOnce⟩

theorem ordinary_coin : Ordinary noHost coinRows "coin" [] :=
  ordinary_nullary "coin" (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide +kernel) (by decide) (by decide)

theorem ordinary_toss : Ordinary noHost coinRows "toss" [] :=
  ordinary_nullary "toss" (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide +kernel) (by decide) (by decide)

theorem coin_bodies : regionBodies coinRows "coin" [] = [sym "heads", sym "tails"] := by
  decide +kernel

theorem toss_bodies : regionBodies coinRows "toss" [] = [app "coin" [], sym "edge"] := by
  decide +kernel

theorem settles_symbol (name : String) (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    (notRefused : name ≠ "NotReducible") : Settles noHost coinRows (sym name) :=
  .data (.symbol notEmpty notError) fun same => notRefused (by cases same; rfl)

theorem coin_settles : Settles noHost coinRows (app "coin" []) := by
  refine .call ordinary_coin (by rw [coin_bodies]; simp) ?_
  rw [coin_bodies]
  intro b member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact settles_symbol "heads" (by decide) (by decide) (by decide)
  · exact settles_symbol "tails" (by decide) (by decide) (by decide)

/-- **`(toss)` settles**: its region holds `(coin)` and `edge`; `(coin)` has two rows. -/
theorem toss_settles : Settles noHost coinRows (app "toss" []) := by
  refine .call ordinary_toss (by rw [toss_bodies]; simp) ?_
  rw [toss_bodies]
  intro b member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact coin_settles
  · exact settles_symbol "edge" (by decide) (by decide) (by decide)

/-- **Positive control: several equations, a call body, multiplicity.** `(toss)` on the coin
program: HE's complete run publishes `heads`, `tails`, `edge`, and PeTTa's streaming run of the
translation yields the same three values. -/
theorem toss_agrees {lookup : CastLookup} (answers : AnswersUndefined lookup) (policy : Policy) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost lookup policy)
          (load (Space.ofList coinRows) (app "toss" []) Atom.undefinedType)
          ⟨Space.ofList coinRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [sym "heads", sym "tails", sym "edge"] ∧
        Streaming.values (Streaming.advance (translate coinRows) 80
          (Streaming.enter { state := store coinRows } (app "toss" []))) =
          [sym "heads", sym "tails", sym "edge"] := by
  have computed : Streaming.values (Streaming.advance (translate coinRows) 80
      (Streaming.enter { state := store coinRows } (app "toss" []))) =
      [sym "heads", sym "tails", sym "edge"] := by
    decide +kernel
  have finished : (Streaming.advance (translate coinRows) 80
      (Streaming.enter { state := store coinRows } (app "toss" []))).agenda.length = 0 := by
    decide +kernel
  obtain ⟨R, N, path, _, agree⟩ := answers_agree noHost answers policy coin_program toss_settles
  refine ⟨R, path, ?_, computed⟩
  have later := agree (max N 80) (le_max_left _ _)
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) _ (le_max_right _ _), computed] at later
  exact later.symm

/-- `(pick 1)`: a literal pattern and a variable pattern both match. -/
theorem pick_bodies : regionBodies coinRows "pick" [.grounded (.int 1)] = [sym "one", sym "any"] := by
  decide +kernel

theorem pick_settles : Settles noHost coinRows (app "pick" [.grounded (.int 1)]) := by
  have ordinary : Ordinary noHost coinRows "pick" [.grounded (.int 1)] :=
    ⟨.symbol (by decide) (by decide), fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .grounded _, by decide +kernel, fun impossible => impossible, by decide +kernel,
      by decide, by decide, by decide +kernel, by decide, by decide⟩
  refine .call ordinary (by rw [pick_bodies]; simp) ?_
  rw [pick_bodies]
  intro b member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact settles_symbol "one" (by decide) (by decide) (by decide)
  · exact settles_symbol "any" (by decide) (by decide) (by decide)

/-- **Positive control: two matching equations, one with a variable pattern.** -/
theorem pick_agrees {lookup : CastLookup} (answers : AnswersUndefined lookup) (policy : Policy) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost lookup policy)
          (load (Space.ofList coinRows) (app "pick" [.grounded (.int 1)]) Atom.undefinedType)
          ⟨Space.ofList coinRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [sym "one", sym "any"] := by
  have computed : Streaming.values (Streaming.advance (translate coinRows) 60
      (Streaming.enter { state := store coinRows } (app "pick" [.grounded (.int 1)]))) =
      [sym "one", sym "any"] := by
    decide +kernel
  have finished : (Streaming.advance (translate coinRows) 60
      (Streaming.enter { state := store coinRows }
        (app "pick" [.grounded (.int 1)]))).agenda.length = 0 := by
    decide +kernel
  obtain ⟨R, N, path, _, agree⟩ := answers_agree noHost answers policy coin_program pick_settles
  refine ⟨R, path, ?_⟩
  have later := agree (max N 60) (le_max_left _ _)
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) _ (le_max_right _ _), computed] at later
  exact later.symm

/-- `{(= (f 4) 8)}`. -/
def fourRows : List Atom := [rule (app "f" [.grounded (.int 4)]) (.grounded (.int 8))]

/-- **Negative control: the uncovered call `(f 5)`.** HE answers `(f 5)`; PeTTa answers nothing. -/
theorem five_differs {lookup : CastLookup} (answers : AnswersUndefined lookup) (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost lookup policy)
          (load (Space.ofList fourRows) (app "f" [.grounded (.int 5)]) Atom.undefinedType)
          ⟨Space.ofList fourRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [app "f" [.grounded (.int 5)]]) ∧
      Streaming.values (Streaming.advance (translate fourRows) 30
        (Streaming.enter { state := store fourRows } (app "f" [.grounded (.int 5)]))) = [] ∧
      (Streaming.advance (translate fourRows) 30
        (Streaming.enter { state := store fourRows } (app "f" [.grounded (.int 5)]))).agenda.length =
        0 := by
  have program : ∀ row ∈ fourRows, RegionsWithVariables.ConsFreeHeads row := by
    intro row member
    simp only [fourRows, List.mem_singleton] at member
    subst member
    exact rule_consFree fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .grounded _
  have ordinary : Ordinary noHost fourRows "f" [.grounded (.int 5)] :=
    ⟨.symbol (by decide) (by decide), fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .grounded _, by decide +kernel, fun impossible => impossible, by decide +kernel,
      by decide, by decide, by decide +kernel, by decide, by decide⟩
  have empty : regionBodies fourRows "f" [.grounded (.int 5)] = [] := by decide +kernel
  have defined : ∃ e ∈ fourRows.filterMap LiveEquations.equationOfRow, e.head = "f" ∧
      e.arguments.length = [Atom.grounded (.int 5)].length :=
    ⟨⟨"f", [.grounded (.int 4)], .grounded (.int 8)⟩,
      List.mem_filterMap.mpr ⟨_, List.mem_singleton_self _, rfl⟩, rfl, rfl⟩
  obtain ⟨⟨R, path, _, erased⟩, _⟩ :=
    uncovered_calls_differ noHost answers policy program ordinary empty defined
  exact ⟨⟨R, path, erased⟩, by decide +kernel, by decide +kernel⟩

/-- `{(= (loop) (loop))}`. -/
def loopRows : List Atom := [rule (app "loop" []) (app "loop" [])]

/-- **Negative control: the termination hypothesis is not vacuous.** `(loop)` does not settle in
`{(= (loop) (loop))}`. -/
theorem loop_does_not_settle (dispatch : GroundedDispatch) :
    ¬ Settles dispatch loopRows (app "loop" []) := by
  have bodies : regionBodies loopRows "loop" [] = [app "loop" []] := by decide +kernel
  have defined : (loopRows.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != "loop") = false := by
    decide +kernel
  suffices key : ∀ t, Settles dispatch loopRows t → t ≠ app "loop" [] from
    fun settles => key _ settles rfl
  intro t settles
  induction settles with
  | @data a data _ =>
      intro same
      subst same
      cases data
  | @constructor f args _ noEquation =>
      intro same
      simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rw [defined] at noEquation
      cases noEquation
  | @call f args _ _ _ ih =>
      intro same
      simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ih (app "loop" []) (by rw [bodies]; exact List.mem_singleton_self _) rfl

end Controls

#print axioms argumentIsRaw_false
#print axioms regionBodies_eq
#print axioms PeTTaRuns.arguments_data
#print axioms PeTTaRuns.run_clauses
#print axioms PeTTaRuns.petta_constructor
#print axioms PeTTaRuns.petta_call
#print axioms HERuns.tuple_steps
#print axioms HERuns.call_entry_steps
#print axioms HERuns.block_of_region
#print axioms HERuns.frontier_bodies
#print axioms HERuns.equations_steps
#print axioms HERuns.finish_steps
#print axioms HERuns.he_absent
#print axioms HERuns.he_call
#print axioms settles_agree
#print axioms petta_complete
#print axioms he_complete
#print axioms answers_agree
#print axioms answer_bags_agree
#print axioms answer_bags_agree_with_he_lookups
#print axioms uncovered_calls_differ
#print axioms Controls.toss_agrees
#print axioms Controls.pick_agrees
#print axioms Controls.five_differs
#print axioms Controls.loop_does_not_settle

end AnswerBags

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
