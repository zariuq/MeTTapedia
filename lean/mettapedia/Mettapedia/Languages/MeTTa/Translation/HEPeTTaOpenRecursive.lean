import Mettapedia.Languages.MeTTa.Translation.HEPeTTaSound
import Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming
import Mettapedia.Machines.OrderedProtocol

/-!
# Open recursive HE--PeTTa comparison

This owner completes the first-order E2 comparison under the passive-environment
admission established in `HEPeTTaSound`. The branch-tree and scoped depth-first
linearization theorems preserve open caller correlations and ordered physical
occurrences. They describe a shared fragment of the existing dialects; they do
not define MeTTa or constrain HO MeTTa Prime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Translation.OpenRecursive

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
open Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
open Mettapedia.Languages.MeTTa.Translation.PureConstructor
open Mettapedia.Languages.MeTTa.Translation.PureConstructor.RecursiveTransport

/-- Resolving invocation slots does not change the complete joint observer.
The same later model still reads every slot and every pending caller atom. -/
theorem solutionTuples_call_read_arguments {source : Equations} {environment : Environment}
    (resolved : resolve source = some environment) (head : String)
    (arguments pending : List Atom) :
    solutionTuples source
        (.expression (.symbol head :: arguments.map (read environment)) :: pending) =
      solutionTuples source (.expression (.symbol head :: arguments) :: pending) := by
  apply solutionTuples_congr_models
  intro candidate solved
  have argumentsEq :
      List.map
          ((HE.Spec.Type.RuntimeRefinement.applyTypeValuation fun name => decode (candidate name)) ∘
            read environment) arguments =
        List.map
          (HE.Spec.Type.RuntimeRefinement.applyTypeValuation fun name => decode (candidate name))
          arguments := by
    calc
      _ = List.map ((read candidate) ∘ read environment) arguments := by
        apply List.map_congr_left
        intro argument _member
        exact (read_eq_applyTypeValuation candidate (read environment argument)).symm
      _ = List.map (read candidate) arguments := by
        simpa only [List.map_map] using resolve_packet_preserves resolved candidate solved arguments
      _ = _ := by
        apply List.map_congr_left
        intro argument _member
        exact read_eq_applyTypeValuation candidate argument
  simp only [List.map_cons, read_eq_applyTypeValuation,
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation, List.map_map]
  rw [argumentsEq]

def evaluationGoals (rows : List (Atom × Atom)) : List Goal :=
  rows.map fun row => .evaluate row.1 row.2

/-- A source destination is fresh for the reached equation store and the
expression it receives.  The saved continuation intentionally mentions that
destination: it is the channel by which the child returns.  Freshness from the
live caller packet is stated by `Evaluation.Allocated`, whose indices expose
the exact prefix and pending syntax at each recursive cut. -/
structure PrivateDestination (control : Control) (expression destination : Atom)
    (older : List Goal) : Type where
  name : String
  destination_eq : destination = .var name
  storeFresh : ∀ pair ∈ control.bindings,
    name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
      name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2
  sourceFresh : name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars expression

/-- The part of source support which survives goal-stack reduction.  This is
the reserved boundary, root destination and reached equation store; pending
goals are deliberately excluded. -/
def PersistentSupport (control : Control) : Finset String :=
  control.reserved ∪
    ((control.destination ::
      control.bindings.flatMap (fun pair => [pair.1, pair.2])).foldl
        (fun names atom => names ∪ (encode atom).freeVars) ∅)

private theorem foldAtomSupport (atoms : List Atom) (initial : Finset String) :
    atoms.foldl (fun found atom => found ∪ (encode atom).freeVars) initial =
      initial ∪ atoms.foldl (fun found atom => found ∪ (encode atom).freeVars) ∅ := by
  induction atoms generalizing initial with
  | nil => simp
  | cons atom atoms ih =>
      rw [List.foldl_cons,ih]
      conv_rhs => rw [List.foldl_cons,Finset.empty_union,ih]
      exact Finset.union_assoc _ _ _

private theorem foldAtomSupport_extends (atoms : List Atom) (initial : Finset String) :
    initial ⊆ atoms.foldl (fun found atom => found ∪ (encode atom).freeVars) initial := by
  rw [foldAtomSupport]
  exact Finset.subset_union_left

/-- Persistent support is a lower bound of the allocator's complete support. -/
theorem persistentSupport_subset_support (control : Control) :
    PersistentSupport control ⊆ control.support := by
  unfold PersistentSupport Control.support
  simp only [List.foldl_append]
  rw [foldAtomSupport (control.goals.flatMap Goal.atoms)]
  intro name member
  simp only [Finset.mem_union] at member ⊢
  tauto

/-- The source allocator and HE presentation use the same variable support,
despite representing it respectively as a finite set and an occurrence list. -/
theorem typeVars_mem_encode_freeVars (atom : Atom) (name : String)
    (member : name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars atom) :
    name ∈ (encode atom).freeVars := by
  revert member
  induction atom using Atom.rec
      (motive_2 := fun atoms =>
        name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList atoms →
          ∃ index : Fin atoms.length, name ∈ (encode atoms[index]).freeVars) with
  | symbol symbol => simp [HE.Spec.Type.Presentation.TypeSubst.typeVars]
  | var varName => simp [HE.Spec.Type.Presentation.TypeSubst.typeVars,encode,
      Mettapedia.Logic.LP.Term.freeVars]
  | grounded value => simp [HE.Spec.Type.Presentation.TypeSubst.typeVars]
  | expression children inductionHypothesis =>
      intro occurrence
      simp only [encode,
        Mettapedia.Logic.LP.Term.freeVars,Finset.mem_biUnion,Finset.mem_univ,true_and]
      exact inductionHypothesis occurrence
  | nil =>
      rename_i impossible
      simp [HE.Spec.Type.Presentation.TypeSubst.typeVarsList] at impossible
  | cons head tail headProof tailProof =>
      rename_i occurrence
      simp only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append] at occurrence
      rcases occurrence with first | rest
      · refine ⟨⟨0,Nat.zero_lt_succ _⟩,?_⟩
        change name ∈ (encode head).freeVars
        exact headProof first
      · obtain ⟨index,present⟩ := tailProof rest
        refine ⟨index.succ,?_⟩
        change name ∈ (encode tail[index]).freeVars
        exact present

private theorem typeVarsList_mem_foldAtomSupport (atoms : List Atom) (name : String)
    (member : name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList atoms) :
    name ∈ atoms.foldl (fun found atom => found ∪ (encode atom).freeVars) ∅ := by
  induction atoms with
  | nil => simp [HE.Spec.Type.Presentation.TypeSubst.typeVarsList] at member
  | cons atom atoms inductionHypothesis =>
      rw [List.foldl_cons,foldAtomSupport]
      simp only [Finset.empty_union,Finset.mem_union]
      simp only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append] at member
      exact member.imp (typeVars_mem_encode_freeVars atom name)
        inductionHypothesis

theorem typeVars_mem_persistent_destination (control : Control) (name : String)
    (member : name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars control.destination) :
    name ∈ PersistentSupport control := by
  unfold PersistentSupport
  apply Finset.mem_union_right
  apply typeVarsList_mem_foldAtomSupport
  exact HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
    List.mem_cons_self name member

theorem typeVars_mem_persistent_binding (control : Control) (pair : Atom × Atom)
    (present : pair ∈ control.bindings) (name : String)
    (member : name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ++
      HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2) :
    name ∈ PersistentSupport control := by
  unfold PersistentSupport
  apply Finset.mem_union_right
  apply typeVarsList_mem_foldAtomSupport
  rcases List.mem_append.mp member with left | right
  · exact HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
      (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨pair,present,by simp⟩)) name left
  · exact HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
      (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨pair,present,by simp⟩)) name right

/-- Accepting one equation retains every name in the old persistent store. -/
theorem persistentSupport_append_equation (control : Control) (value destination : Atom)
    (older : List Goal) :
    PersistentSupport control ⊆
      PersistentSupport {control with
        bindings := control.bindings ++ [(value,destination)],goals := older} := by
  intro name member
  unfold PersistentSupport at member ⊢
  rcases Finset.mem_union.mp member with reserved | stored
  · exact Finset.mem_union_left _ reserved
  · apply Finset.mem_union_right
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] at stored ⊢
    rw [show control.destination ::
        (control.bindings.flatMap (fun pair => [pair.1,pair.2]) ++ [value,destination]) =
        (control.destination :: control.bindings.flatMap (fun pair => [pair.1,pair.2])) ++
          [value,destination] by simp]
    rw [List.foldl_append]
    exact foldAtomSupport_extends [value,destination] _ stored

theorem persistentSupport_protectControl (control : Control) (extra : Finset String) :
    PersistentSupport (protectControl control extra) = PersistentSupport control ∪ extra := by
  simp only [PersistentSupport,protectControl]
  ac_rfl

mutual
/-- A finite open source evaluation tree.  This is independent source syntax:
it contains source preparation, logical refinement and clause-frontier
evidence, but no HE completion and no executable-machine run. -/
inductive Evaluation (program : Program) :
    Control → Atom → Atom → List Goal → List Control → Type where
  | variable {control : Control} {sourceName slotName : String} {older : List Goal}
      {after : Equations}
      (privateDestination : PrivateDestination control (.var sourceName) (.var slotName) older)
      (atGoal : control.goals = .evaluate (.var sourceName) (.var slotName) :: older)
      (accepted : Refinement control.bindings (.var sourceName) (.var slotName) (some after)) :
      Evaluation program control (.var sourceName) (.var slotName) older
        [{control with bindings := after, goals := older}]
  | symbol {control : Control} {name : String} {destination : Atom} {older : List Goal}
      {after : Equations}
      (privateDestination : PrivateDestination control (.symbol name) destination older)
      (atGoal : control.goals = .evaluate (.symbol name) destination :: older)
      (accepted : Refinement control.bindings (.symbol name) destination (some after)) :
      Evaluation program control (.symbol name) destination older
        [{control with bindings := after, goals := older}]
  | grounded {control : Control} {value : GroundedValue} {destination : Atom}
      {older : List Goal} {after : Equations}
      (privateDestination : PrivateDestination control (.grounded value) destination older)
      (atGoal : control.goals = .evaluate (.grounded value) destination :: older)
      (accepted : Refinement control.bindings (.grounded value) destination (some after)) :
      Evaluation program control (.grounded value) destination older
        [{control with bindings := after, goals := older}]
  | unit {control : Control} {destination : Atom} {older : List Goal} {after : Equations}
      (privateDestination : PrivateDestination control (.expression []) destination older)
      (atGoal : control.goals = .evaluate (.expression []) destination :: older)
      (accepted : Refinement control.bindings (.expression []) destination (some after)) :
      Evaluation program control (.expression []) destination older
        [{control with bindings := after, goals := older}]
  | constructor {control opened : Control} {head : String} {arguments : List Atom}
      {destination : Atom} {older : List Goal} {outcomes : List Control}
      (passive : ConstructorHead program head)
      (privateDestination : PrivateDestination control
        (.expression (.symbol head :: arguments)) destination older)
      (atGoal : control.goals =
        .evaluate (.expression (.symbol head :: arguments)) destination :: older)
      (prepared : Prepared .eagerValue program control destination older
        (.expression (.symbol head :: arguments)) opened)
      (argumentsRun : Arguments program opened
        (arguments.zip (freshSlots control arguments.length))
        (.expression (.symbol head :: freshSlots control arguments.length)) destination
        (.equate (.expression (.symbol head :: freshSlots control arguments.length)) destination)
        older outcomes) :
      Evaluation program control (.expression (.symbol head :: arguments)) destination older outcomes
  | call {control opened : Control} {head : String} {arguments : List Atom}
      {destination : Atom} {older : List Goal} {outcomes : List Control}
      (defined : DefinedHead program head)
      (privateDestination : PrivateDestination control
        (.expression (.symbol head :: arguments)) destination older)
      (atGoal : control.goals =
        .evaluate (.expression (.symbol head :: arguments)) destination :: older)
      (prepared : Prepared .eagerValue program control destination older
        (.expression (.symbol head :: arguments)) opened)
      (argumentsRun : Arguments program opened
        (arguments.zip (freshSlots control arguments.length))
        (.expression (.symbol head :: freshSlots control arguments.length)) destination
        (.invoke head (freshSlots control arguments.length) destination) older outcomes) :
      Evaluation program control (.expression (.symbol head :: arguments)) destination older outcomes

/-- Left-to-right argument evaluation.  Every reached head branch receives
its own tail derivation, so shared constraints flow into later siblings. -/
inductive Arguments (program : Program) :
    Control → List (Atom × Atom) → Atom → Atom → Goal → List Goal → List Control → Type where
  | nil {control : Control} {assembled destination : Atom} {final : Goal} {older : List Goal}
      {outcomes : List Control}
      (atGoal : control.goals = final :: older)
      (continued : Invocation program control assembled destination final older outcomes) :
      Arguments program control [] assembled destination final older outcomes
  | cons {control : Control} {source slot : Atom} {rows : List (Atom × Atom)}
      {assembled destination : Atom} {final : Goal} {older : List Goal} {heads outcomes : List Control}
      (atGoal : control.goals = .evaluate source slot :: evaluationGoals rows ++ final :: older)
      (first : Evaluation program control source slot (evaluationGoals rows ++ final :: older) heads)
      (branches : ArgumentBranches program heads rows assembled destination final older outcomes) :
      Arguments program control ((source,slot) :: rows) assembled destination final older outcomes

/-- A complete occurrence fold over the alternatives returned by one
argument.  Multiplicity and order are retained structurally. -/
inductive ArgumentBranches (program : Program) :
    List Control → List (Atom × Atom) → Atom → Atom → Goal → List Goal → List Control → Type where
  | nil {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
      {older : List Goal} :
      ArgumentBranches program [] rows assembled destination final older []
  | cons {head : Control} {heads : List Control} {rows : List (Atom × Atom)}
      {assembled destination : Atom} {final : Goal} {older : List Goal} {children rest : List Control}
      (first : Arguments program head rows assembled destination final older children)
      (remaining : ArgumentBranches program heads rows assembled destination final older rest) :
      ArgumentBranches program (head :: heads) rows assembled destination final older (children ++ rest)

/-- The terminal argument continuation is either passive data assembly or a
complete ordered equation frontier.  Frontier rows are source decisions, not
machine callbacks. -/
inductive Invocation (program : Program) :
    Control → Atom → Atom → Goal → List Goal → List Control → Type where
  | constructor {control : Control} {head : String} {arguments : List Atom}
      {destination : Atom} {older : List Goal}
      {after : Equations}
      (passive : ConstructorHead program head)
      (privateDestination : PrivateDestination control
        (.expression (.symbol head :: arguments)) destination older)
      (atGoal : control.goals =
        .equate (.expression (.symbol head :: arguments)) destination :: older)
      (accepted : Refinement control.bindings
        (.expression (.symbol head :: arguments)) destination (some after)) :
      Invocation program control (.expression (.symbol head :: arguments)) destination
        (.equate (.expression (.symbol head :: arguments)) destination) older
        [{control with bindings := after, goals := older}]
  | equations {control : Control} {extra : Finset String} {head : String}
      {arguments : List Atom} {destination : Atom} {older : List Goal}
      {environment : Environment} {selected : List (Nat × Control)} {outcomes : List Control}
      (defined : DefinedHead program head)
      (privateDestination : PrivateDestination control
        (.expression (.symbol head :: arguments)) destination older)
      (atGoal : control.goals = .invoke head arguments destination :: older)
      (resolved : resolve control.bindings = some environment)
      (resolvedSupported : ∀ name ∈
        HE.Spec.Type.Presentation.TypeSubst.typeVarsList (arguments.map (read environment)),
        name ∈ (protectControl control extra).support)
      (frontier : ClauseChoice.Frontier program (protectControl control extra) head
        (arguments.map (read environment)) destination older
        (List.range program.equations.length) selected)
      (nonempty : selected ≠ [])
      (bodies : Bodies program destination older selected outcomes) :
      Invocation program control (.expression (.symbol head :: arguments))
        destination (.invoke head arguments destination) older outcomes

/-- Recursive clause bodies are evaluated independently from the same
complete frontier.  Their result lists concatenate in stored occurrence
order; deterministic DFS linearization is proved separately. -/
inductive Bodies (program : Program) :
    Atom → List Goal → List (Nat × Control) → List Control → Type where
  | nil {destination : Atom} {older : List Goal} : Bodies program destination older [] []
  | cons {destination : Atom} {older : List Goal} {position : Nat} {selected : Control}
      {remaining : List (Nat × Control)} {body : Atom} {children rest : List Control}
      (atGoal : selected.goals = .evaluate body destination :: older)
      (first : Evaluation program selected body destination older children)
      (later : Bodies program destination older remaining rest) :
      Bodies program destination older ((position,selected) :: remaining) (children ++ rest)
end

/-- Source preparation changes only the active goal list, so the persistent
allocator boundary is exactly unchanged. -/
theorem Prepared.persistentSupport_eq
    {policy : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Policy}
    {program : Program} {control next : Control} {destination : Atom}
    {older : List Goal} {expression : Atom}
    (prepared : Prepared policy program control destination older expression next) :
    PersistentSupport next = PersistentSupport control := by
  cases prepared <;> rfl

/-- One edge of the branching source tree.  Local syntax expansion and
equation acceptance are ordinary source steps.  Invocation selection is a
complete-frontier edge; its DFS queue realization is intentionally separate. -/
inductive BranchStep (program : Program) : Control → Control → Prop where
  | expanded {control next : Control} {expression destination : Atom} {older : List Goal}
      (atGoal : control.goals = .evaluate expression destination :: older)
      (ordinary : scopedForm expression = false)
      (prepared : Prepared .eagerValue program control destination older expression next) :
      BranchStep program control next
  | accepted {control : Control} {value destination : Atom} {older : List Goal}
      {after : Equations}
      (atGoal : control.goals = .equate value destination :: older)
      (refined : Refinement control.bindings value destination (some after)) :
      BranchStep program control {control with bindings := after, goals := older}
  | selected {control : Control} {extra : Finset String} {head : String}
      {arguments : List Atom} {destination : Atom} {older : List Goal}
      {environment : Environment} {choices : List (Nat × Control)} {position : Nat}
      {next : Control}
      (atGoal : control.goals = .invoke head arguments destination :: older)
      (resolved : resolve control.bindings = some environment)
      (frontier : ClauseChoice.Frontier program (protectControl control extra) head
        (arguments.map (read environment)) destination older
        (List.range program.equations.length) choices)
      (member : (position,next) ∈ choices) : BranchStep program control next

abbrev BranchPath (program : Program) := Relation.ReflTransGen (BranchStep program)

mutual
theorem Evaluation.paths {program : Program} {control : Control} {expression destination : Atom}
    {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination older outcomes) :
    ∀ outcome ∈ outcomes, BranchPath program control outcome := by
  match source with
  | @Evaluation.variable _ control sourceName slotName older after _private atGoal accepted =>
      intro outcome member
      obtain rfl := List.mem_singleton.mp member
      let middle := {control with goals := .equate (.var sourceName) (.var slotName) :: older}
      have opened : BranchStep program control middle := .expanded atGoal rfl (.variableValue sourceName)
      have closed : BranchStep program middle {control with bindings := after, goals := older} := by
        apply BranchStep.accepted (value := .var sourceName) (destination := .var slotName)
        · rfl
        · simpa only [middle] using accepted
      exact (Relation.ReflTransGen.single opened).trans (Relation.ReflTransGen.single closed)
  | @Evaluation.symbol _ control name destination older after _private atGoal accepted =>
      intro outcome member
      obtain rfl := List.mem_singleton.mp member
      let middle := {control with goals := .equate (.symbol name) destination :: older}
      have opened : BranchStep program control middle := .expanded atGoal rfl (.symbol name)
      have closed : BranchStep program middle {control with bindings := after, goals := older} := by
        apply BranchStep.accepted (value := .symbol name) (destination := destination)
        · rfl
        · simpa only [middle] using accepted
      exact (Relation.ReflTransGen.single opened).trans (Relation.ReflTransGen.single closed)
  | @Evaluation.grounded _ control value destination older after _private atGoal accepted =>
      intro outcome member
      obtain rfl := List.mem_singleton.mp member
      let middle := {control with goals := .equate (.grounded value) destination :: older}
      have opened : BranchStep program control middle := .expanded atGoal rfl (.grounded value)
      have closed : BranchStep program middle {control with bindings := after, goals := older} := by
        apply BranchStep.accepted (value := .grounded value) (destination := destination)
        · rfl
        · simpa only [middle] using accepted
      exact (Relation.ReflTransGen.single opened).trans (Relation.ReflTransGen.single closed)
  | @Evaluation.unit _ control destination older after _private atGoal accepted =>
      intro outcome member
      obtain rfl := List.mem_singleton.mp member
      let middle := {control with goals := .equate (.expression []) destination :: older}
      have opened : BranchStep program control middle := .expanded atGoal rfl (.tuple [] (by simp))
      have closed : BranchStep program middle {control with bindings := after, goals := older} := by
        apply BranchStep.accepted (value := .expression []) (destination := destination)
        · rfl
        · simpa only [middle] using accepted
      exact (Relation.ReflTransGen.single opened).trans (Relation.ReflTransGen.single closed)
  | @Evaluation.constructor _ control opened head arguments destination older outcomes
      passive _private atGoal prepared argumentsRun =>
      intro outcome member
      have ordinary : scopedForm (.expression (.symbol head :: arguments)) = false := by
        rcases passive.1 with ⟨_io,_known,excluded⟩
        simp only [scopedForm]
        split <;> simp_all
      exact (Relation.ReflTransGen.single (BranchStep.expanded atGoal ordinary prepared)).trans
        (argumentsRun.paths outcome member)
  | @Evaluation.call _ control opened head arguments destination older outcomes
      defined _private atGoal prepared argumentsRun =>
      intro outcome member
      have ordinary : scopedForm (.expression (.symbol head :: arguments)) = false := by
        rcases defined.1 with ⟨_io,_known,excluded⟩
        simp only [scopedForm]
        split <;> simp_all
      exact (Relation.ReflTransGen.single (BranchStep.expanded atGoal ordinary prepared)).trans
        (argumentsRun.paths outcome member)
termination_by structural source

theorem Arguments.paths {program : Program} {control : Control} {rows : List (Atom × Atom)}
    {assembled destination : Atom} {final : Goal} {older : List Goal} {outcomes : List Control}
    (source : Arguments program control rows assembled destination final older outcomes) :
    ∀ outcome ∈ outcomes, BranchPath program control outcome := by
  match source with
  | .nil _atGoal continued => exact continued.paths
  | .cons _atGoal first branches =>
      intro outcome member
      obtain ⟨head,headMember,path⟩ := branches.paths outcome member
      exact (first.paths head headMember).trans path
termination_by structural source

theorem ArgumentBranches.paths {program : Program} {heads : List Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal} {older : List Goal}
    {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes) :
    ∀ outcome ∈ outcomes, ∃ head ∈ heads, BranchPath program head outcome := by
  match source with
  | .nil => simp
  | .cons first remaining =>
      intro outcome member
      rcases List.mem_append.mp member with member | member
      · exact ⟨_,List.mem_cons_self,first.paths outcome member⟩
      · obtain ⟨head,present,path⟩ := remaining.paths outcome member
        exact ⟨head,List.mem_cons_of_mem _ present,path⟩
termination_by structural source

theorem Invocation.paths {program : Program} {control : Control} {assembled destination : Atom}
    {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : Invocation program control assembled destination final older outcomes) :
    ∀ outcome ∈ outcomes, BranchPath program control outcome := by
  match source with
  | .constructor _passive _private atGoal accepted =>
      intro outcome member
      obtain rfl := List.mem_singleton.mp member
      exact Relation.ReflTransGen.single (.accepted atGoal accepted)
  | @Invocation.equations _ control extra head arguments destination older environment selected outcomes
      _defined _private atGoal resolved _resolvedSupported frontier nonempty bodies =>
      intro outcome member
      obtain ⟨row,rowMember,path⟩ := bodies.paths outcome member
      exact (Relation.ReflTransGen.single
        (BranchStep.selected atGoal resolved frontier rowMember)).trans path
termination_by structural source

theorem Bodies.paths {program : Program} {destination : Atom} {older : List Goal}
    {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes) :
    ∀ outcome ∈ outcomes,
      ∃ row ∈ selected, BranchPath program row.2 outcome := by
  match source with
  | .nil => simp
  | .cons _atGoal first later =>
      intro outcome member
      rcases List.mem_append.mp member with member | member
      · exact ⟨_,List.mem_cons_self,first.paths outcome member⟩
      · obtain ⟨row,present,path⟩ := later.paths outcome member
        exact ⟨row,List.mem_cons_of_mem _ present,path⟩
termination_by structural source
end

/-! ## Ordered source-origin traces

`BranchPath` records reachability but deliberately forgets which physical
equation occurrence was selected at each branching edge.  The scoped DFS
machine stores exactly that list in each `CollectionWork`.  The following
relation strengthens the source path with those portable occurrence indices,
without mentioning a scheduler or a collection queue. -/

inductive BranchTrace (program : Program) : Control → List Nat → Control → Prop where
  | refl (control : Control) : BranchTrace program control [] control
  | expanded {control next outcome : Control} {expression destination : Atom}
      {older : List Goal} {occurrences : List Nat}
      (atGoal : control.goals = .evaluate expression destination :: older)
      (ordinary : scopedForm expression = false)
      (prepared : Prepared .eagerValue program control destination older expression next)
      (later : BranchTrace program next occurrences outcome) :
      BranchTrace program control occurrences outcome
  | accepted {control outcome : Control} {value destination : Atom} {older : List Goal}
      {after : Equations} {occurrences : List Nat}
      (atGoal : control.goals = .equate value destination :: older)
      (refined : Refinement control.bindings value destination (some after))
      (later : BranchTrace program {control with bindings := after, goals := older}
        occurrences outcome) :
      BranchTrace program control occurrences outcome
  | selected {control next outcome : Control} {extra : Finset String} {head : String}
      {arguments : List Atom} {destination : Atom} {older : List Goal}
      {environment : Environment} {choices : List (Nat × Control)} {position : Nat}
      {occurrences : List Nat}
      (atGoal : control.goals = .invoke head arguments destination :: older)
      (resolved : resolve control.bindings = some environment)
      (frontier : ClauseChoice.Frontier program (protectControl control extra) head
        (arguments.map (read environment)) destination older
        (List.range program.equations.length) choices)
      (member : (position,next) ∈ choices)
      (later : BranchTrace program next occurrences outcome) :
      BranchTrace program control (position :: occurrences) outcome

theorem BranchTrace.toPath {program : Program} {before after : Control}
    {occurrences : List Nat} (source : BranchTrace program before occurrences after) :
    BranchPath program before after := by
  induction source with
  | refl => exact .refl
  | expanded atGoal ordinary prepared _ inductionHypothesis =>
      exact (Relation.ReflTransGen.single (.expanded atGoal ordinary prepared)).trans
        inductionHypothesis
  | accepted atGoal refined _ inductionHypothesis =>
      exact (Relation.ReflTransGen.single (.accepted atGoal refined)).trans
        inductionHypothesis
  | selected atGoal resolved frontier member _ inductionHypothesis =>
      exact (Relation.ReflTransGen.single (.selected atGoal resolved frontier member)).trans
        inductionHypothesis

theorem BranchTrace.trans {program : Program} {first middle last : Control}
    {firstOccurrences secondOccurrences : List Nat}
    (before : BranchTrace program first firstOccurrences middle)
    (suffix : BranchTrace program middle secondOccurrences last) :
    BranchTrace program first (firstOccurrences ++ secondOccurrences) last := by
  induction before with
  | refl => simpa using suffix
  | expanded atGoal ordinary prepared _ inductionHypothesis =>
      exact .expanded atGoal ordinary prepared (inductionHypothesis suffix)
  | accepted atGoal refined _ inductionHypothesis =>
      exact .accepted atGoal refined (inductionHypothesis suffix)
  | selected atGoal resolved frontier member _ inductionHypothesis =>
      exact .selected atGoal resolved frontier member (inductionHypothesis suffix)

private theorem BranchTrace.prefix_forall₂
    {program : Program} {first middle : Control} {beforeTrace : List Nat}
    {traces : List (List Nat)} {outcomes : List Control}
    (before : BranchTrace program first beforeTrace middle)
    (after : List.Forall₂ (BranchTrace program middle) traces outcomes) :
    ∃ prefixed, List.Forall₂ (BranchTrace program first) prefixed outcomes := by
  refine ⟨traces.map (beforeTrace ++ ·),?_⟩
  induction after with
  | nil => exact .nil
  | cons path _ inductionHypothesis =>
      exact .cons (before.trans path) inductionHypothesis

private theorem BranchTrace.selected_forall₂
    {program : Program} {control : Control} {extra : Finset String} {head : String}
    {arguments : List Atom} {destination : Atom} {older : List Goal}
    {environment : Environment} {choices rows : List (Nat × Control)}
    (atGoal : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (frontier : ClauseChoice.Frontier program (protectControl control extra) head
      (arguments.map (read environment)) destination older
      (List.range program.equations.length) choices)
    (included : ∀ row ∈ rows, row ∈ choices) :
    List.Forall₂ (BranchTrace program control)
      (rows.map fun row => [row.1]) (rows.map Prod.snd) := by
  induction rows with
  | nil => exact .nil
  | cons row rows inductionHypothesis =>
      rcases row with ⟨position,next⟩
      exact .cons
        (.selected atGoal resolved frontier (included _ List.mem_cons_self) (.refl next))
        (inductionHypothesis fun candidate member =>
          included candidate (List.mem_cons_of_mem _ member))

mutual
theorem Evaluation.traces {program : Program} {control : Control}
    {expression destination : Atom} {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination older outcomes) :
    ∃ traces, List.Forall₂ (BranchTrace program control) traces outcomes := by
  match source with
  | @Evaluation.variable _ control sourceName slotName older after _private atGoal accepted =>
      let middle := {control with goals := .equate (.var sourceName) (.var slotName) :: older}
      have refined : Refinement middle.bindings (.var sourceName) (.var slotName) (some after) := by
        simpa only [middle] using accepted
      exact ⟨[[]],.cons
        (.expanded atGoal rfl (.variableValue sourceName)
          (.accepted rfl refined (.refl _))) .nil⟩
  | @Evaluation.symbol _ control name destination older after _private atGoal accepted =>
      let middle := {control with goals := .equate (.symbol name) destination :: older}
      have refined : Refinement middle.bindings (.symbol name) destination (some after) := by
        simpa only [middle] using accepted
      exact ⟨[[]],.cons
        (.expanded atGoal rfl (.symbol name)
          (.accepted rfl refined (.refl _))) .nil⟩
  | @Evaluation.grounded _ control value destination older after _private atGoal accepted =>
      let middle := {control with goals := .equate (.grounded value) destination :: older}
      have refined : Refinement middle.bindings (.grounded value) destination (some after) := by
        simpa only [middle] using accepted
      exact ⟨[[]],.cons
        (.expanded atGoal rfl (.grounded value)
          (.accepted rfl refined (.refl _))) .nil⟩
  | @Evaluation.unit _ control destination older after _private atGoal accepted =>
      let middle := {control with goals := .equate (.expression []) destination :: older}
      have refined : Refinement middle.bindings (.expression []) destination (some after) := by
        simpa only [middle] using accepted
      exact ⟨[[]],.cons
        (.expanded atGoal rfl (.tuple [] (by simp))
          (.accepted rfl refined (.refl _))) .nil⟩
  | @Evaluation.constructor _ _ _ head arguments _ _ _ passive _private atGoal prepared argumentsRun =>
      obtain ⟨traces,related⟩ := argumentsRun.traces
      have ordinary : scopedForm (.expression (.symbol head :: arguments)) = false := by
        rcases passive.1 with ⟨_io,_known,excluded⟩
        simp only [scopedForm]
        split <;> simp_all
      exact ⟨traces,related.imp fun _ _ path => .expanded atGoal ordinary prepared path⟩
  | @Evaluation.call _ _ _ head arguments _ _ _ defined _private atGoal prepared argumentsRun =>
      obtain ⟨traces,related⟩ := argumentsRun.traces
      have ordinary : scopedForm (.expression (.symbol head :: arguments)) = false := by
        rcases defined.1 with ⟨_io,_known,excluded⟩
        simp only [scopedForm]
        split <;> simp_all
      exact ⟨traces,related.imp fun _ _ path => .expanded atGoal ordinary prepared path⟩
termination_by structural source

theorem Arguments.traces {program : Program} {control : Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : Arguments program control rows assembled destination final older outcomes) :
    ∃ traces, List.Forall₂ (BranchTrace program control) traces outcomes := by
  match source with
  | .nil _atGoal continued => exact continued.traces
  | .cons _atGoal first branches =>
      obtain ⟨headTraces,headsRelated⟩ := first.traces
      exact branches.traces headsRelated
termination_by structural source

theorem ArgumentBranches.traces {program : Program} {heads : List Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes)
    {root : Control} {headTraces : List (List Nat)}
    (headsRelated : List.Forall₂ (BranchTrace program root) headTraces heads) :
    ∃ traces, List.Forall₂ (BranchTrace program root) traces outcomes := by
  match source with
  | .nil =>
      cases headsRelated
      exact ⟨[],.nil⟩
  | .cons first remaining =>
      cases headsRelated with
      | cons headPath restPaths =>
          obtain ⟨childTraces,childrenRelated⟩ := first.traces
          obtain ⟨prefixedTraces,prefixed⟩ :=
            BranchTrace.prefix_forall₂ headPath childrenRelated
          obtain ⟨restTraces,restRelated⟩ := remaining.traces restPaths
          exact ⟨prefixedTraces ++ restTraces,List.rel_append prefixed restRelated⟩
termination_by structural source

theorem Invocation.traces {program : Program} {control : Control}
    {assembled destination : Atom} {final : Goal} {older : List Goal}
    {outcomes : List Control}
    (source : Invocation program control assembled destination final older outcomes) :
    ∃ traces, List.Forall₂ (BranchTrace program control) traces outcomes := by
  match source with
  | .constructor _passive _private atGoal accepted =>
      exact ⟨[[]],.cons (.accepted atGoal accepted (.refl _)) .nil⟩
  | @Invocation.equations _ control extra head arguments destination older environment selected _
      _defined _private atGoal resolved _resolvedSupported frontier _nonempty bodies =>
      have selectedRelated := BranchTrace.selected_forall₂ atGoal resolved frontier
        (rows := selected) (fun _ member => member)
      exact bodies.traces selectedRelated
termination_by structural source

theorem Bodies.traces {program : Program} {destination : Atom} {older : List Goal}
    {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes)
    {root : Control} {selectedTraces : List (List Nat)}
    (selectedRelated : List.Forall₂ (BranchTrace program root) selectedTraces
      (selected.map Prod.snd)) :
    ∃ traces, List.Forall₂ (BranchTrace program root) traces outcomes := by
  match source with
  | .nil =>
      cases selectedRelated
      exact ⟨[],.nil⟩
  | .cons _atGoal first later =>
      cases selectedRelated with
      | cons selectedPath restPaths =>
          obtain ⟨childTraces,childrenRelated⟩ := first.traces
          obtain ⟨prefixedTraces,prefixed⟩ :=
            BranchTrace.prefix_forall₂ selectedPath childrenRelated
          obtain ⟨restTraces,restRelated⟩ := later.traces restPaths
          exact ⟨prefixedTraces ++ restTraces,List.rel_append prefixed restRelated⟩
termination_by structural source
end

/-- Every accepted refinement has a resolvable reached equation store. -/
theorem refinement_resolves_after {before : Equations} {value destination : Atom}
    {after : Equations} (source : Refinement before value destination (some after)) :
    ∃ environment, resolve after = some environment := by
  cases source with
  | accepted environment old new =>
      apply resolve_complete
      refine ⟨environment,?_⟩
      intro pair member
      rcases List.mem_append.mp member with previous | latest
      · exact old pair previous
      · obtain rfl := List.mem_singleton.mp latest
        exact new

mutual
/-- Every result occurrence produced by the finite source tree is at its
declared continuation and carries a resolvable reached constraint store. -/
theorem Evaluation.outcomes_ready {program : Program} {control : Control}
    {expression destination : Atom} {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination older outcomes) :
    ∀ outcome ∈ outcomes,
      outcome.goals = older ∧ ∃ environment, resolve outcome.bindings = some environment := by
  match source with
  | .variable _private _atGoal accepted | .symbol _private _atGoal accepted |
    .grounded _private _atGoal accepted | .unit _private _atGoal accepted =>
      intro outcome member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨rfl,refinement_resolves_after accepted⟩
  | .constructor _passive _private _atGoal _prepared argumentsRun |
    .call _defined _private _atGoal _prepared argumentsRun =>
      exact argumentsRun.outcomes_ready
termination_by structural source

theorem Arguments.outcomes_ready {program : Program} {control : Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : Arguments program control rows assembled destination final older outcomes) :
    ∀ outcome ∈ outcomes,
      outcome.goals = older ∧ ∃ environment, resolve outcome.bindings = some environment := by
  match source with
  | .nil _atGoal continued => exact continued.outcomes_ready
  | .cons _atGoal _first branches => exact branches.outcomes_ready
termination_by structural source

theorem ArgumentBranches.outcomes_ready {program : Program} {heads : List Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes) :
    ∀ outcome ∈ outcomes,
      outcome.goals = older ∧ ∃ environment, resolve outcome.bindings = some environment := by
  match source with
  | .nil => simp
  | .cons first remaining =>
      intro outcome member
      rcases List.mem_append.mp member with firstMember | laterMember
      · exact first.outcomes_ready outcome firstMember
      · exact remaining.outcomes_ready outcome laterMember
termination_by structural source

theorem Invocation.outcomes_ready {program : Program} {control : Control}
    {assembled destination : Atom} {final : Goal} {older : List Goal}
    {outcomes : List Control}
    (source : Invocation program control assembled destination final older outcomes) :
    ∀ outcome ∈ outcomes,
      outcome.goals = older ∧ ∃ environment, resolve outcome.bindings = some environment := by
  match source with
  | .constructor _passive _private _atGoal accepted =>
      intro outcome member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨rfl,refinement_resolves_after accepted⟩
  | .equations _defined _private _atGoal _resolved _supported _frontier _nonempty bodies =>
      exact bodies.outcomes_ready
termination_by structural source

theorem Bodies.outcomes_ready {program : Program} {destination : Atom} {older : List Goal}
    {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes) :
    ∀ outcome ∈ outcomes,
      outcome.goals = older ∧ ∃ environment, resolve outcome.bindings = some environment := by
  match source with
  | .nil => simp
  | .cons _atGoal first later =>
      intro outcome member
      rcases List.mem_append.mp member with firstMember | laterMember
      · exact first.outcomes_ready outcome firstMember
      · exact later.outcomes_ready outcome laterMember
termination_by structural source
end

namespace CollectionLinearization

open Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped
open Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.ProtectedContinuation
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Machines.OrderedProtocol.Completion

/-- A concrete scoped-machine control represents a raw open-recursive control
with a finite stack of predicate-return delimiters before its concrete
continuation.  Source and concrete continuations may differ structurally when
an outer delimiter follows pending siblings, but expose the same atom support. -/
structure DelimitedControl (sourceOlder actualOlder : List Goal)
    (raw actual : Control) : Type where
  bindings : actual.bindings = raw.bindings
  destination : actual.destination = raw.destination
  reserved : actual.reserved = raw.reserved
  older_atoms : actualOlder.flatMap Goal.atoms = sourceOlder.flatMap Goal.atoms
  restores : List Nat
  activePrefix : List Goal
  raw_goals : raw.goals = activePrefix ++ sourceOlder
  actual_goals : actual.goals =
    activePrefix ++ restores.map Goal.restoreCommit ++ actualOlder

private theorem restoreCommit_atoms (restores : List Nat) :
    (restores.map Goal.restoreCommit).flatMap Goal.atoms = [] := by
  induction restores with
  | nil => rfl
  | cons boundary restores inductionHypothesis =>
      simp only [List.map_cons,List.flatMap_cons,Goal.atoms,List.nil_append,
        inductionHypothesis]

/-- Inserting logical choice delimiters changes no variable support. -/
theorem DelimitedControl.support_eq {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual) :
    actual.support = raw.support := by
  rcases related with
    ⟨bindings,destination,reserved,olderAtoms,restores,activePrefix,rawGoals,actualGoals⟩
  simp only [Control.support,bindings,destination,reserved,actualGoals,rawGoals,
    List.flatMap_append,restoreCommit_atoms,List.append_nil,olderAtoms]

theorem DelimitedControl.freshName_eq {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual) (index : Nat) :
    freshName actual index = freshName raw index := by
  simp only [freshName,related.support_eq]

theorem DelimitedControl.freshSlots_eq {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual) (count : Nat) :
    freshSlots actual count = freshSlots raw count := by
  simp only [freshSlots,related.freshName_eq]

/-- Extending both controls by the same allocator boundary preserves their
exact delimited relation.  This is the boundary used by the retained DFS
machine before scanning an equation frontier. -/
def DelimitedControl.protect {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (boundary : Finset String) :
    DelimitedControl sourceOlder actualOlder (protectControl raw boundary)
      (protectControl actual boundary) := by
  exact ⟨by simpa only [protectControl] using related.bindings,
    by simpa only [protectControl] using related.destination,
    by simp only [protectControl,related.reserved],related.older_atoms,
    related.restores,related.activePrefix,
    by simpa only [protectControl] using related.raw_goals,
    by simpa only [protectControl] using related.actual_goals⟩

/-- Install the concrete clause delimiter while retaining the source-selected
bindings, body and public continuation. -/
def delimitedClauseChoice (cutBoundary : Nat) (restores : List Nat)
    (older : List Goal) (choice : Control) : Control :=
  { choice with
    cutBoundary := cutBoundary
    goals := match choice.goals with
      | body :: _ => body :: restores.map Goal.restoreCommit ++ older
      | [] => restores.map Goal.restoreCommit ++ older }

/-- Equal protected reserves are the exact synchronization condition needed
for two delimited controls to allocate the same fresh clause instance. -/
theorem DelimitedControl.protected_support_eq {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (extra boundary : Finset String)
    (sameReserved : (protectControl actual boundary).reserved =
      (protectControl raw extra).reserved) :
    (protectControl actual boundary).support =
      (protectControl raw extra).support := by
  have reserves : actual.reserved ∪ boundary = raw.reserved ∪ extra := by
    simpa only [protectControl] using sameReserved
  rcases related with
    ⟨bindings,destination,_reserved,olderAtoms,restores,activePrefix,rawGoals,actualGoals⟩
  simp only [Control.support,protectControl,bindings,destination,
    actualGoals,rawGoals,List.flatMap_append,restoreCommit_atoms,List.append_nil,olderAtoms]
  rw [reserves]

theorem DelimitedControl.protected_freshPattern_eq {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (extra boundary : Finset String)
    (sameReserved : (protectControl actual boundary).reserved =
      (protectControl raw extra).reserved)
    (occurrence : Nat) (equation : Equation) :
    ClauseChoice.freshPattern (protectControl actual boundary) occurrence equation =
      ClauseChoice.freshPattern (protectControl raw extra) occurrence equation := by
  have namesEqual : ClauseChoice.rename (protectControl actual boundary) occurrence
      (ClauseChoice.clauseAtoms equation) =
      ClauseChoice.rename (protectControl raw extra) occurrence
        (ClauseChoice.clauseAtoms equation) := by
    funext name
    simp only [ClauseChoice.rename,freshName,
      related.protected_support_eq extra boundary sameReserved]
  exact congrArg (fun rename =>
    HE.Spec.Type.RuntimeRefinement.renameTypeVars rename (ClauseChoice.pattern equation))
    namesEqual

theorem DelimitedControl.protected_freshBody_eq {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (extra boundary : Finset String)
    (sameReserved : (protectControl actual boundary).reserved =
      (protectControl raw extra).reserved)
    (occurrence : Nat) (equation : Equation) :
    ClauseChoice.freshBody (protectControl actual boundary) occurrence equation =
      ClauseChoice.freshBody (protectControl raw extra) occurrence equation := by
  have namesEqual : ClauseChoice.rename (protectControl actual boundary) occurrence
      (ClauseChoice.clauseAtoms equation) =
      ClauseChoice.rename (protectControl raw extra) occurrence
        (ClauseChoice.clauseAtoms equation) := by
    funext name
    simp only [ClauseChoice.rename,freshName,
      related.protected_support_eq extra boundary sameReserved]
  exact congrArg (fun rename =>
    HE.Spec.Type.RuntimeRefinement.renameTypeVars rename equation.body) namesEqual

/-- A complete source row decision transports across a delimiter stack once
the source and retained-machine protection sets synchronize their reserves. -/
theorem DelimitedControl.decision_lift {program : Program}
    {sourceOlder actualOlder : List Goal}
    {raw actual : Control} {extra boundary : Finset String} {head : String}
    {arguments : List Atom} {destination : Atom} {occurrence : Nat}
    {result : Option Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (sameReserved : (protectControl actual boundary).reserved =
      (protectControl raw extra).reserved)
    (source : ClauseChoice.Decision program (protectControl raw extra) head
      arguments destination sourceOlder occurrence result) :
    ClauseChoice.Decision program (protectControl actual boundary) head arguments
      destination (related.restores.map Goal.restoreCommit ++ actualOlder) occurrence
      (result.map
        (delimitedClauseChoice actual.cutBoundary related.restores actualOlder)) := by
  cases source with
  | other equation row different => exact .other equation row different
  | refused equation row sameHead incompatible =>
      apply ClauseChoice.Decision.refused equation row sameHead
      rw [related.protected_freshPattern_eq extra boundary sameReserved occurrence equation]
      simpa only [protectControl,related.bindings] using incompatible
  | selected equation bindings row sameHead compatible =>
      have accepted : Refinement (protectControl actual boundary).bindings
          (.expression (.symbol head :: arguments))
          (ClauseChoice.freshPattern (protectControl actual boundary) occurrence equation)
          (some bindings) := by
        rw [related.protected_freshPattern_eq extra boundary sameReserved occurrence equation]
        simpa only [protectControl,related.bindings] using compatible
      have chosen := ClauseChoice.Decision.selected
        (program := program) (control := protectControl actual boundary)
        (head := head) (arguments := arguments) (destination := destination)
        (older := related.restores.map Goal.restoreCommit ++ actualOlder)
        equation bindings row sameHead accepted
      let rawChoice : Control :=
        { bindings := bindings
          goals := .evaluate
            (ClauseChoice.freshBody (protectControl raw extra) occurrence equation)
              destination :: sourceOlder
          destination := (protectControl raw extra).destination
          reserved := (protectControl raw extra).reserved
          cutBoundary := (protectControl raw extra).cutBoundary }
      let actualChoice : Control :=
        { bindings := bindings
          goals := .evaluate
            (ClauseChoice.freshBody (protectControl actual boundary) occurrence equation)
              destination :: related.restores.map Goal.restoreCommit ++ actualOlder
          destination := (protectControl actual boundary).destination
          reserved := (protectControl actual boundary).reserved
          cutBoundary := (protectControl actual boundary).cutBoundary }
      have bodyEq :=
        related.protected_freshBody_eq extra boundary sameReserved occurrence equation
      have destinationEq : (protectControl actual boundary).destination =
          (protectControl raw extra).destination := by
        simpa only [protectControl] using related.destination
      have choiceEq : delimitedClauseChoice actual.cutBoundary related.restores actualOlder
          rawChoice = actualChoice := by
        simp only [delimitedClauseChoice,rawChoice,actualChoice]
        rw [bodyEq,destinationEq,sameReserved]
        simp only [protectControl]
      simpa only [rawChoice,actualChoice,Option.map_some,choiceEq,
        List.cons_append] using chosen

/-- Complete frontiers transport position-for-position.  Accepted duplicate
occurrences remain duplicate entries in the same order. -/
theorem DelimitedControl.frontier_lift {program : Program}
    {sourceOlder actualOlder : List Goal}
    {raw actual : Control} {extra boundary : Finset String} {head : String}
    {arguments : List Atom} {destination : Atom} {positions : List Nat}
    {choices : List (Nat × Control)}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (sameReserved : (protectControl actual boundary).reserved =
      (protectControl raw extra).reserved)
    (source : ClauseChoice.Frontier program (protectControl raw extra) head
      arguments destination sourceOlder positions choices) :
    ClauseChoice.Frontier program (protectControl actual boundary) head arguments
      destination (related.restores.map Goal.restoreCommit ++ actualOlder) positions
      (choices.map fun row =>
        (row.1,delimitedClauseChoice actual.cutBoundary related.restores actualOlder row.2)) := by
  induction source with
  | nil => exact .nil
  | skip decision _rest inductionHypothesis =>
      exact .skip (related.decision_lift sameReserved decision) inductionHypothesis
  | keep decision _rest inductionHypothesis =>
      exact .keep (related.decision_lift sameReserved decision) inductionHypothesis

/-- Entering a selected predicate installs its current cut delimiter in front
of the older delimiter stack while leaving the raw clause body unchanged. -/
def DelimitedControl.of_predicateEntry {sourceOlder actualOlder : List Goal}
    {raw actual selected : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    {body destination : Atom}
    (atGoal : selected.goals = .evaluate body destination :: sourceOlder)
    (retained : Nat) :
    DelimitedControl sourceOlder actualOlder selected
      (predicateEntry retained
        (delimitedClauseChoice actual.cutBoundary related.restores actualOlder selected)) := by
  refine ⟨rfl,rfl,rfl,related.older_atoms,actual.cutBoundary :: related.restores,
    [.evaluate body destination],?_,?_⟩
  · simpa only [List.singleton_append] using atGoal
  · simp only [predicateEntry,delimitedClauseChoice,atGoal,List.map_cons,
      List.cons_append,List.nil_append]

/-- Support retained behind the current work item in its DFS queue. -/
def pendingSupport {Context : Type} (pending : List (CollectionWork Context)) :
    Finset String :=
  pending.foldr (fun work names => work.1.support ∪ names) ∅

/-- Support already published in the current root scope together with every
outer retained scope.  The active work item and its queue tail are accounted
for separately. -/
def collectedSupport {Context : Type} (parents : List (CollectionScope Context))
    (scope : CollectionScope Context) : Finset String :=
  scope.collected.foldr (fun answer names => answer.support ∪ names) ∅ ∪
    parents.foldr (fun parent names => CollectionScope.support parent ∪ names) ∅

/-- The retained work installed for one selected source occurrence. -/
def enteredEquationWork {Context : Type} (cutBoundary : Nat) (restores : List Nat)
    (actualOlder : List Goal) (retained : Nat) (context : Context) (origins : List Nat)
    (row : Nat × Control) : CollectionWork Context :=
  (predicateEntry retained
      (delimitedClauseChoice cutBoundary restores actualOlder row.2),
    context,origins ++ [row.1])

/-- Every selected clause supplied to `Bodies` begins with its fresh body at
the declared destination and exact older continuation. -/
theorem Bodies.selected_ready {program : Program} {destination : Atom}
    {older : List Goal} {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes) :
    ∀ row ∈ selected,
      ∃ body, row.2.goals = .evaluate body destination :: older := by
  match source with
  | .nil => simp
  | @Bodies.cons _ _ _ position selected remaining body children rest atGoal first later =>
      intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨body,atGoal⟩
      · exact Bodies.selected_ready later row member
termination_by structural source

/-- The support of entered equation alternatives is exactly the support of
their raw selected controls followed by the pre-existing queue tail. -/
theorem DelimitedControl.pendingSupport_enteredEquationWork {Context : Type}
    {sourceOlder actualOlder : List Goal} {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual) {destination : Atom}
    (choices : List (Nat × Control)) (retained : Nat) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (ready : ∀ row ∈ choices,
      ∃ body, row.2.goals = .evaluate body destination :: sourceOlder) :
    pendingSupport
        (choices.map (enteredEquationWork actual.cutBoundary related.restores actualOlder
          retained context origins) ++ pending) =
      choices.foldr (fun row names => row.2.support ∪ names)
        (pendingSupport pending) := by
  induction choices with
  | nil => rfl
  | cons row choices inductionHypothesis =>
      obtain ⟨body,atGoal⟩ := ready row List.mem_cons_self
      have supportEq :=
        (related.of_predicateEntry (selected := row.2) atGoal retained).support_eq
      simp only [List.map_cons,List.cons_append,pendingSupport,List.foldr_cons,
        enteredEquationWork,supportEq]
      exact congrArg (fun names => row.2.support ∪ names)
        (inductionHypothesis
          (fun candidate member => ready candidate (List.mem_cons_of_mem row member)))

/-- Concrete queued work realizes raw continuation roots in order.  Each item
records its source trace, physical origin path and exact support of the work
remaining behind it. -/
inductive QueuedWorkRel {Context : Type} (program : Program)
    (sourceOlder actualOlder : List Goal) (root : Control)
    (baseOrigins : List Nat) (basePending : List (CollectionWork Context)) :
    List (Control × Finset String) → List (CollectionWork Context) → Prop where
  | nil : QueuedWorkRel program sourceOlder actualOlder root baseOrigins basePending [] []
  | cons {raw actual : Control} {pSupp : Finset String} {context : Context}
      {origins trace : List Nat} {queued : List (Control × Finset String)}
      {work : List (CollectionWork Context)}
      (related : Nonempty (DelimitedControl sourceOlder actualOlder raw actual))
      (path : BranchTrace program root trace raw)
      (originsEq : origins = baseOrigins ++ trace)
      (supportEq : pSupp = pendingSupport (work ++ basePending))
      (rest : QueuedWorkRel program sourceOlder actualOlder root baseOrigins
        basePending queued work) :
      QueuedWorkRel program sourceOlder actualOlder root baseOrigins basePending
        ((raw,pSupp) :: queued) ((actual,context,origins) :: work)

/-- Queue-support assignment for a complete selected equation frontier. -/
def queuedSelections (base : Finset String) :
    List (Nat × Control) → List (Control × Finset String)
  | [] => []
  | row :: remaining =>
      (row.2,remaining.foldr (fun next names => next.2.support ∪ names) base) ::
        queuedSelections base remaining

/-- A complete source body list supplies the exact concrete predicate-entry
queue used by the retained DFS machine, including occurrence paths and the
support of every remaining suffix. -/
theorem Bodies.queuedWorkRel {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {root actual : Control}
    {head : String} {arguments : List Atom} {destination : Atom}
    {environment : Environment} {allChoices selected : List (Nat × Control)}
    {outcomes : List Control}
    (bodies : Bodies program destination sourceOlder selected outcomes)
    (related : DelimitedControl sourceOlder actualOlder root actual)
    (atCall : root.goals = .invoke head arguments destination :: sourceOlder)
    (resolved : resolve root.bindings = some environment)
    {extra : Finset String}
    (coverage : ClauseChoice.Frontier program (protectControl root extra) head
      (arguments.map (read environment)) destination sourceOlder
      (List.range program.equations.length) allChoices)
    (included : ∀ row ∈ selected, row ∈ allChoices)
    (baseOrigins : List Nat) (basePending : List (CollectionWork Context))
    (context : Context) :
    QueuedWorkRel program sourceOlder actualOlder root baseOrigins basePending
      (queuedSelections (pendingSupport basePending) selected)
      (selected.map (enteredEquationWork actual.cutBoundary related.restores actualOlder
        basePending.length context baseOrigins)) := by
  match bodies with
  | .nil => exact .nil
  | @Bodies.cons _ _ _ position selected remaining body children rest atBody first later =>
      have enteredRelated :=
        related.of_predicateEntry (selected := selected) atBody basePending.length
      have selectedPath : BranchTrace program root [position] selected :=
        .selected atCall resolved coverage
          (included (position,selected) List.mem_cons_self) (.refl selected)
      have remainingSupport := related.pendingSupport_enteredEquationWork
        (destination := destination) remaining basePending.length context baseOrigins
        basePending (Bodies.selected_ready later)
      refine .cons ⟨enteredRelated⟩ selectedPath rfl ?_ ?_
      · exact remainingSupport.symm
      · exact Bodies.queuedWorkRel later related atCall resolved coverage
          (fun row member => included row (List.mem_cons_of_mem _ member))
          baseOrigins basePending context
termination_by structural bodies

/-- At a root collection scope, total allocator support factors into the raw
active control, the exact queue tail, and previously retained observations.
Delimiter goals and occurrence paths contribute no names. -/
theorem DelimitedControl.collectionSupport_eq {Context : Type}
    {sourceOlder actualOlder : List Goal} {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World)
    (parents : List (CollectionScope Context)) (scope : CollectionScope Context)
    (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (frontier : scope.frontier = (actual,context,origins) :: pending)
    (root : scope.caller = none) :
    collectionSupport
        (⟨world,scope :: parents⟩ : CollectionConfiguration Context) =
      raw.support ∪ pendingSupport pending ∪ collectedSupport parents scope := by
  simp only [collectionSupport,List.foldr_cons,CollectionScope.support,frontier,
    root,Option.map_none,Option.getD_none,pendingSupport,collectedSupport,
    related.support_eq,Finset.union_empty]
  ac_rfl

/-- At the return boundary of the active subcomputation, the delimiter stack
is the whole difference between the concrete and raw goal lists. -/
theorem DelimitedControl.at_continuation {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (atEnd : raw.goals = sourceOlder) :
    actual.goals = related.restores.map Goal.restoreCommit ++ actualOlder := by
  have prefixLength : related.activePrefix.length = 0 := by
    have same := congrArg List.length (related.raw_goals.symm.trans atEnd)
    simp only [List.length_append] at same
    omega
  have prefixNil := List.eq_nil_of_length_eq_zero prefixLength
  simpa only [prefixNil,List.nil_append] using related.actual_goals

/-- Any active source prefix remains before the delimiter stack.  This is the
two-continuation law used when unevaluated siblings precede an outer caller. -/
theorem DelimitedControl.prefix_goals {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual) (active : List Goal)
    (atPrefix : raw.goals = active ++ sourceOlder) :
    actual.goals = active ++ related.restores.map Goal.restoreCommit ++ actualOlder := by
  have same : related.activePrefix ++ sourceOlder = active ++ sourceOlder :=
    related.raw_goals.symm.trans atPrefix
  have prefixEq : related.activePrefix = active := List.append_cancel_right same
  simpa only [prefixEq] using related.actual_goals

theorem DelimitedControl.entry_goals {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual) (goal : Goal)
    (atGoal : raw.goals = goal :: sourceOlder) :
    actual.goals = goal :: related.restores.map Goal.restoreCommit ++ actualOlder := by
  have atPrefix : raw.goals = [goal] ++ sourceOlder := by
    simpa only [List.singleton_append] using atGoal
  simpa only [List.singleton_append,List.cons_append,List.nil_append] using
    related.prefix_goals [goal] atPrefix

def DelimitedControl.replace_prefix {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual) (active : List Goal) :
    DelimitedControl sourceOlder actualOlder (replace raw (active ++ sourceOlder))
      (replace actual
        (active ++ related.restores.map Goal.restoreCommit ++ actualOlder)) := by
  exact ⟨by simpa only [replace] using related.bindings,
    by simpa only [replace] using related.destination,
    by simpa only [replace] using related.reserved,related.older_atoms,
    related.restores,active,rfl,rfl⟩

/-- One ordinary evaluation expansion commutes with an already installed
delimiter stack when its syntax-directed work prefix is the same. -/
theorem DelimitedControl.expanded_replace {Context : Type} {program : Program}
    {raw actual : Control} {expression destination : Atom}
    {sourceOlder actualOlder active : List Goal}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (atGoal : raw.goals = .evaluate expression destination :: sourceOlder)
    (ordinary : scopedForm expression = false)
    (prepared : Prepared .eagerValue program actual destination
      (related.restores.map Goal.restoreCommit ++ actualOlder) expression
      (replace actual
        (active ++ related.restores.map Goal.restoreCommit ++ actualOlder)))
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World) (context : Context) :
    ∃ _ : DelimitedControl sourceOlder actualOlder
        (replace raw (active ++ sourceOlder))
        (replace actual
          (active ++ related.restores.map Goal.restoreCommit ++ actualOlder)),
      Source.Step .eagerValue program (⟨world,actual,context⟩ : Cursor Context)
        (.silent (⟨world,
          replace actual
            (active ++ related.restores.map Goal.restoreCommit ++ actualOlder),context⟩ :
          Cursor Context)) := by
  exact ⟨related.replace_prefix active,
    .expanded expression destination
      (related.restores.map Goal.restoreCommit ++ actualOlder) _
      (related.entry_goals (.evaluate expression destination) atGoal) ordinary prepared⟩

/-- Accepted logical refinement commutes with the delimiter stack and exposes
the same reached binding store at the raw continuation. -/
theorem DelimitedControl.accepted_step {Context : Type} {program : Program}
    {raw actual : Control} {value destination : Atom}
    {sourceOlder actualOlder : List Goal} {after : Equations}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (atGoal : raw.goals = .equate value destination :: sourceOlder)
    (accepted : Refinement raw.bindings value destination (some after))
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World) (context : Context) :
    let reached : Control :=
      { bindings := after
        goals := related.restores.map Goal.restoreCommit ++ actualOlder
        destination := actual.destination
        reserved := actual.reserved
        cutBoundary := actual.cutBoundary }
    ∃ _ : DelimitedControl sourceOlder actualOlder
        {raw with bindings := after,goals := sourceOlder} reached,
      Source.Step .eagerValue program (⟨world,actual,context⟩ : Cursor Context)
        (.silent (⟨world,reached,context⟩ : Cursor Context)) := by
  dsimp only
  have actualAccepted : Refinement actual.bindings value destination (some after) := by
    simpa only [related.bindings] using accepted
  refine ⟨⟨rfl,related.destination,related.reserved,related.older_atoms,
    related.restores,[],rfl,rfl⟩,
    .accepted value destination
    (related.restores.map Goal.restoreCommit ++ actualOlder) after
    (related.entry_goals (.equate value destination) atGoal) actualAccepted⟩

/-- Enter one argument evaluation by moving its remaining sibling and final
goals into the source and concrete continuations.  Outer delimiters stay after
those siblings; the child starts with an empty inner delimiter stack. -/
def DelimitedControl.enter_argument {sourceOlder actualOlder : List Goal}
    {raw actual : Control}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    {source slot : Atom} {rows : List (Atom × Atom)} {final : Goal}
    (atGoal : raw.goals =
      .evaluate source slot :: (evaluationGoals rows ++ final :: sourceOlder)) :
    DelimitedControl
      (evaluationGoals rows ++ final :: sourceOlder)
      (evaluationGoals rows ++ final ::
        (related.restores.map Goal.restoreCommit ++ actualOlder))
      raw actual := by
  have prefixEq : related.activePrefix =
      .evaluate source slot :: (evaluationGoals rows ++ [final]) := by
    have same : related.activePrefix ++ sourceOlder =
        (.evaluate source slot :: (evaluationGoals rows ++ [final])) ++ sourceOlder := by
      simpa only [List.cons_append,List.append_assoc,List.singleton_append,
        List.nil_append] using
        related.raw_goals.symm.trans atGoal
    exact List.append_cancel_right same
  refine ⟨related.bindings,related.destination,related.reserved,?_,[],
    [.evaluate source slot],?_,?_⟩
  · simp only [List.flatMap_append,List.flatMap_cons,restoreCommit_atoms,
      List.nil_append,related.older_atoms]
  · simpa only [List.singleton_append,List.cons_append,List.append_assoc,
      List.nil_append] using atGoal
  · simpa only [prefixEq,List.map_nil,List.nil_append,List.singleton_append,
      List.cons_append,List.append_assoc] using related.actual_goals

/-- After a child has popped its inner delimiters, its sibling continuation
reconstitutes the enclosing delimiter relation. -/
def DelimitedControl.exit_argument {sourceOlder actualOlder : List Goal}
    (olderAtoms : actualOlder.flatMap Goal.atoms = sourceOlder.flatMap Goal.atoms)
    (outerRestores : List Nat) {rows : List (Atom × Atom)} {final : Goal}
    {head reached : Control}
    (bindings : reached.bindings = head.bindings)
    (destination : reached.destination = head.destination)
    (reserved : reached.reserved = head.reserved)
    (headGoals : head.goals = evaluationGoals rows ++ final :: sourceOlder)
    (reachedGoals : reached.goals = evaluationGoals rows ++ final ::
      (outerRestores.map Goal.restoreCommit ++ actualOlder)) :
    DelimitedControl sourceOlder actualOlder head reached := by
  refine ⟨bindings,destination,reserved,olderAtoms,outerRestores,
    evaluationGoals rows ++ [final],?_,?_⟩
  · simpa only [List.append_assoc,List.singleton_append] using headGoals
  · simpa only [List.append_assoc,List.singleton_append,List.cons_append,
      List.nil_append] using reachedGoals

/-- A source preparation is representation-independent across every concrete
continuation with the same atom support.  Control forms which inspect the
current cut boundary are discharged by their own component law. -/
def PreparedDelimitedRel {program : Program} {raw next : Control}
    {expression destination : Atom} {sourceOlder : List Goal}
    (_source : Prepared .eagerValue program raw destination sourceOlder expression next) : Prop :=
  ∀ (actualOlder : List Goal) (actual : Control),
    ∀ (related : DelimitedControl sourceOlder actualOlder raw actual),
      ∃ actualNext,
        Nonempty (DelimitedControl sourceOlder actualOlder next actualNext) ∧
        Prepared .eagerValue program actual destination
          (related.restores.map Goal.restoreCommit ++ actualOlder) expression actualNext

theorem PreparedDelimitedRel.of_source {program : Program} {raw firstNext secondNext : Control}
    {expression destination : Atom} {sourceOlder : List Goal}
    (first : Prepared .eagerValue program raw destination sourceOlder expression firstNext)
    (second : Prepared .eagerValue program raw destination sourceOlder expression secondNext)
    (valid : PreparedDelimitedRel second) : PreparedDelimitedRel first := by
  have same : firstNext = secondNext := first.execution.symm.trans second.execution
  subst secondNext
  exact valid

theorem PreparedDelimitedRel.application {program : Program} {raw : Control}
    {destination : Atom} {sourceOlder : List Goal} (head : String)
    (arguments : List Atom)
    (ordinary : lexicalForm (.expression (.symbol head :: arguments)) = false)
    (declared : callable program head = true) :
    PreparedDelimitedRel
      (Prepared.application (policy := Policy.eagerValue) (control := raw)
        (destination := destination) (older := sourceOlder)
        head arguments ordinary declared) := by
  intro actualOlder actual related
  let active :=
    (callArguments program head arguments (freshSlots raw arguments.length)).1 ++
      [.invoke head
        (callArguments program head arguments (freshSlots raw arguments.length)).2 destination]
  have slots := related.freshSlots_eq arguments.length
  refine ⟨replace actual
      (active ++ related.restores.map Goal.restoreCommit ++ actualOlder),
    ⟨by simpa only [active,List.append_assoc] using related.replace_prefix active⟩,?_⟩
  simpa only [active,slots,List.append_assoc] using
    (Prepared.application (policy := Policy.eagerValue) (program := program)
      (control := actual) (destination := destination)
      (older := related.restores.map Goal.restoreCommit ++ actualOlder)
      head arguments ordinary declared)

theorem PreparedDelimitedRel.construction {program : Program} {raw : Control}
    {destination : Atom} {sourceOlder : List Goal} (head : String)
    (arguments : List Atom)
    (ordinary : lexicalForm (.expression (.symbol head :: arguments)) = false)
    (data : callable program head = false) :
    PreparedDelimitedRel
      (Prepared.construction (policy := Policy.eagerValue) (control := raw)
        (destination := destination) (older := sourceOlder)
        head arguments ordinary data) := by
  intro actualOlder actual related
  let active : List Goal :=
    (arguments.zip (freshSlots raw arguments.length)).map
        (fun row => Goal.evaluate row.1 row.2) ++
      [Goal.equate (.expression (.symbol head :: freshSlots raw arguments.length)) destination]
  have slots := related.freshSlots_eq arguments.length
  refine ⟨replace actual
      (active ++ related.restores.map Goal.restoreCommit ++ actualOlder),
    ⟨by simpa only [active,List.append_assoc] using related.replace_prefix active⟩,?_⟩
  simpa only [active,slots,List.append_assoc] using
    (Prepared.construction (policy := Policy.eagerValue) (program := program)
      (control := actual) (destination := destination)
      (older := related.restores.map Goal.restoreCommit ++ actualOlder)
      head arguments ordinary data)

/-- Reflexive-transitive silent execution in the maintained pre-return source
profile.  This is a path in the existing scoped source rules, not a second
stepper. -/
def PreReturnPath {Context : Type} (policy : Policy) (program : Program)
    (before after : ScopedCursor Context) : Prop :=
  ∃ fuel, Derivation (preReturnRule policy program) fuel before [] (.exhausted after)

theorem PreReturnPath.refl {Context : Type} (policy : Policy) (program : Program)
    (state : ScopedCursor Context) : PreReturnPath policy program state state :=
  ⟨0,.pause state⟩

theorem PreReturnPath.single {Context : Type} {policy : Policy} {program : Program}
    {before after : ScopedCursor Context} (source : PreReturnStep policy program before after) :
    PreReturnPath policy program before after := by
  refine ⟨1,?_⟩
  simpa only [zero_add] using
    (Derivation.silent (rule := preReturnRule policy program)
      ⟨after,rfl,source⟩ (.pause after))

theorem PreReturnPath.trans {Context : Type} {policy : Policy} {program : Program}
    {first middle last : ScopedCursor Context}
    (beforePath : PreReturnPath policy program first middle)
    (suffix : PreReturnPath policy program middle last) :
    PreReturnPath policy program first last := by
  obtain ⟨firstFuel,firstPath⟩ := beforePath
  obtain ⟨secondFuel,secondPath⟩ := suffix
  exact ⟨firstFuel + secondFuel,by
    simpa only [List.nil_append] using firstPath.resume secondPath⟩

/-- A synchronized source frontier is installed by one actual retained-scope
step.  Every selected occurrence receives the current predicate delimiter;
the queue order and physical occurrence path are unchanged. -/
theorem DelimitedControl.equations_step {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {raw actual : Control} {extra : Finset String}
    {head : String} {arguments : List Atom} {destination : Atom}
    {environment : Environment} {choices : List (Nat × Control)}
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (atGoal : raw.goals = .invoke head arguments destination :: sourceOlder)
    (resolved : resolve raw.bindings = some environment)
    (ordinary : head ≠ "parse")
    (unknown : Mettapedia.Languages.MeTTa.PeTTa.StdLib.known head = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead head = false)
    (declared : program.equations.any (·.head == head) = true)
    (coverage : ClauseChoice.Frontier program (protectControl raw extra) head
      (arguments.map (read environment)) destination sourceOlder
      (List.range program.equations.length) choices)
    (supply : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World)
    (parents : List (CollectionScope Context)) (scope : CollectionScope Context)
    (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (frontier : scope.frontier = (actual,context,origins) :: pending)
    (synchronized :
      (protectControl actual (collectionSupport
        (⟨world,scope :: parents⟩ : CollectionConfiguration Context))).reserved =
        (protectControl raw extra).reserved) :
    let actualChoices := choices.map fun row =>
      (row.1,delimitedClauseChoice actual.cutBoundary related.restores actualOlder row.2)
    PreReturnPath .eagerValue program
      (supply,⟨world,scope :: parents⟩)
      (supply,⟨world,{scope with frontier :=
        (actualChoices.map (fun row =>
          (predicateEntry pending.length row.2,context,origins ++ [row.1]))) ++ pending} ::
        parents⟩) := by
  dsimp only
  let boundary := collectionSupport
    (⟨world,scope :: parents⟩ : CollectionConfiguration Context)
  have sameReserved : (protectControl actual boundary).reserved =
      (protectControl raw extra).reserved := by
    simpa only [boundary] using synchronized
  have targetCoverage := related.frontier_lift sameReserved coverage
  have actualAtGoal : actual.goals = .invoke head arguments destination ::
      related.restores.map Goal.restoreCommit ++ actualOlder :=
    related.entry_goals (.invoke head arguments destination) atGoal
  have actualResolved : resolve actual.bindings = some environment := by
    simpa only [related.bindings] using resolved
  let actualChoices := choices.map fun row =>
    (row.1,delimitedClauseChoice actual.cutBoundary related.restores actualOlder row.2)
  have localStep : PreReturnStep .eagerValue program
      (supply,⟨world,scope :: parents⟩)
      (supply,⟨world,{scope with frontier :=
        (actualChoices.map (fun row =>
          (predicateEntry pending.length row.2,context,origins ++ [row.1]))) ++ pending} ::
        parents⟩) := by
    exact PreReturnStep.equations supply world scope parents actual context origins pending
      head arguments destination (related.restores.map Goal.restoreCommit ++ actualOlder)
      environment actualChoices frontier actualAtGoal actualResolved ordinary unknown notIO
      declared (by simpa only [boundary,actualChoices] using targetCoverage)
  simpa only [actualChoices] using PreReturnPath.single localStep

private theorem drain_restoreCommits_aux {Context : Type} (program : Program)
    (supply : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World)
    (parents : List (CollectionScope Context)) (scope : CollectionScope Context)
    (raw actual : Control) (actualOlder : List Goal) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (restores : List Nat)
    (bindings : actual.bindings = raw.bindings)
    (destination : actual.destination = raw.destination)
    (reserved : actual.reserved = raw.reserved)
    (actualGoals : actual.goals = restores.map Goal.restoreCommit ++ actualOlder)
    (frontier : scope.frontier = (actual,context,origins) :: pending) :
    ∃ reached,
      reached.bindings = raw.bindings ∧
      reached.destination = raw.destination ∧
      reached.reserved = raw.reserved ∧
      reached.goals = actualOlder ∧
      PreReturnPath .eagerValue program
        (supply,⟨world,scope :: parents⟩)
        (supply,⟨world,{scope with frontier := (reached,context,origins) :: pending} :: parents⟩) := by
  induction restores generalizing actual scope with
  | nil =>
      refine ⟨actual,bindings,destination,reserved,?_,?_⟩
      · simpa only [List.map_nil,List.nil_append] using actualGoals
      · have sameScope :
            {scope with frontier := (actual,context,origins) :: pending} = scope := by
          cases scope
          simp_all
        simpa only [sameScope] using
          (PreReturnPath.refl .eagerValue program (supply,⟨world,scope :: parents⟩))
  | cons boundary restores inductionHypothesis =>
      let reachedControl : Control :=
        {actual with goals := restores.map Goal.restoreCommit ++ actualOlder, cutBoundary := boundary}
      let reachedScope : CollectionScope Context :=
        {scope with frontier := (reachedControl,context,origins) :: pending}
      have localStep : Source.Step .eagerValue program
          (⟨world,actual,context⟩ : Cursor Context)
          (.silent (⟨world,reachedControl,context⟩ : Cursor Context)) := by
        apply Source.Step.restoring boundary (restores.map Goal.restoreCommit ++ actualOlder)
        simpa only [List.map_cons,List.cons_append] using actualGoals
      have scopedStep : PreReturnStep .eagerValue program
          (supply,⟨world,scope :: parents⟩)
          (supply,⟨world,reachedScope :: parents⟩) := by
        simpa only [reachedScope,retainChild] using
          (PreReturnStep.continuing supply world scope parents actual context origins pending
            (⟨world,reachedControl,context⟩ : Cursor Context) frontier localStep)
      obtain ⟨final,finalBindings,finalDestination,finalReserved,finalGoals,restPath⟩ :=
        inductionHypothesis reachedScope reachedControl
          (by simpa only [reachedControl] using bindings)
          (by simpa only [reachedControl] using destination)
          (by simpa only [reachedControl] using reserved)
          rfl rfl
      refine ⟨final,finalBindings,finalDestination,finalReserved,finalGoals,?_⟩
      have joined := (PreReturnPath.single scopedStep).trans restPath
      simpa only [reachedScope] using joined

/-- Once the active raw computation has reached its continuation, the concrete
machine pops every saved predicate boundary before exposing that continuation.
Bindings, destination, reserved support, world, context, origins and the queue
tail are unchanged. -/
theorem drain_restoreCommits {Context : Type} (program : Program)
    (supply : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World)
    (parents : List (CollectionScope Context)) (scope : CollectionScope Context)
    (raw actual : Control) (sourceOlder actualOlder : List Goal)
    (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (related : DelimitedControl sourceOlder actualOlder raw actual)
    (atEnd : raw.goals = sourceOlder)
    (frontier : scope.frontier = (actual,context,origins) :: pending) :
    ∃ reached,
      reached.bindings = raw.bindings ∧
      reached.destination = raw.destination ∧
      reached.reserved = raw.reserved ∧
      reached.goals = actualOlder ∧
      PreReturnPath .eagerValue program
        (supply,⟨world,scope :: parents⟩)
        (supply,⟨world,{scope with frontier := (reached,context,origins) :: pending} :: parents⟩) :=
  drain_restoreCommits_aux program supply world parents scope raw actual actualOlder context origins pending
    related.restores related.bindings related.destination related.reserved
    (related.at_continuation atEnd) frontier

/-- A finite path in the complete scoped source rules, retaining its exact
ordered publication list and reached configuration. -/
def ScopedSourcePath {Context : Type} (policy : Policy) (program : Program)
    (before : ScopedCursor Context) (events : List CollectedAnswer)
    (after : ScopedCursor Context) : Prop :=
  ∃ fuel, Derivation (sourceRule policy program) fuel
    before events (.exhausted after)

theorem ScopedSourcePath.trans {Context : Type} {policy : Policy} {program : Program}
    {first middle last : ScopedCursor Context} {earlier later : List CollectedAnswer}
    (beforePath : ScopedSourcePath policy program first earlier middle)
    (afterPath : ScopedSourcePath policy program middle later last) :
    ScopedSourcePath policy program first (earlier ++ later) last := by
  obtain ⟨firstFuel,firstSource⟩ := beforePath
  obtain ⟨secondFuel,secondSource⟩ := afterPath
  exact ⟨firstFuel + secondFuel,firstSource.resume secondSource⟩

theorem PreReturnPath.toScoped {Context : Type} {policy : Policy} {program : Program}
    {before after : ScopedCursor Context}
    (source : PreReturnPath policy program before after) :
    ScopedSourcePath policy program before [] after := by
  obtain ⟨fuel,path⟩ := source
  exact ⟨fuel,preReturn_derivation_source path⟩

/-- The public answer represented by a terminal raw control and its complete
physical source-origin path. -/
def ResolvedAnswer (origins : List Nat) (control : Control)
    (answer : CollectedAnswer) : Prop :=
  ∃ environment, resolve control.bindings = some environment ∧
    answer = ⟨read environment control.destination,control.bindings,origins,[]⟩

/-- A terminal raw occurrence, represented by any finite delimiter stack at
the head of a root collection scope, pops those delimiters and publishes
exactly one answer.  The older queue, prior collected answers and occurrence
path are retained verbatim. -/
theorem root_terminal_drain {Context : Type} (program : Program)
    (supply : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World)
    (parents : List (CollectionScope Context)) (scope : CollectionScope Context)
    (raw actual : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (environment : Environment)
    (related : DelimitedControl [] [] raw actual) (atEnd : raw.goals = [])
    (frontier : scope.frontier = (actual,context,origins) :: pending)
    (root : scope.caller = none) (resolved : resolve raw.bindings = some environment) :
    let answer : CollectedAnswer :=
      ⟨read environment raw.destination,raw.bindings,origins,[]⟩
    ResolvedAnswer origins raw answer ∧
      ScopedSourcePath .eagerValue program
        (supply,⟨world,scope :: parents⟩) [answer]
        (supply,⟨world,
          Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Scope.record
            scope pending answer :: parents⟩) := by
  dsimp only
  obtain ⟨reached,reachedBindings,reachedDestination,reachedReserved,reachedGoals,
      restorePath⟩ :=
    drain_restoreCommits program supply world parents scope raw actual [] [] context origins
      pending related atEnd frontier
  let restoredScope : CollectionScope Context :=
    {scope with frontier := (reached,context,origins) :: pending}
  let answer : CollectedAnswer :=
    ⟨read environment raw.destination,raw.bindings,origins,[]⟩
  have reachedResolved : resolve reached.bindings = some environment := by
    simpa only [reachedBindings] using resolved
  have localReturn : Source.Step .eagerValue program
      (⟨world,reached,context⟩ : Cursor Context)
      (.finish (.value (read environment reached.destination) reached.bindings,
        (⟨world,reached,context⟩ : Cursor Context))) :=
    .returned environment reachedGoals reachedResolved
  have scopedReturn : Source.ScopedStep Source.FreshOperations.owned .eagerValue program
      (supply,⟨world,restoredScope :: parents⟩)
      (.publish [answer]
        (supply,⟨world,
          Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Scope.record
            scope pending answer :: parents⟩)) := by
    have active := Source.ScopedStep.active (fresh := Source.FreshOperations.owned)
      (policy := Policy.eagerValue) supply world restoredScope parents reached context origins
      pending _ rfl
      (Source.ActiveStep.answered (fresh := Source.FreshOperations.owned)
        (policy := Policy.eagerValue) (program := program)
        (read environment reached.destination) reached.bindings
        (⟨world,reached,context⟩ : Cursor Context) localReturn)
    simpa only [restoredScope,root,Option.isNone_none,if_true,answer,
      reachedBindings,reachedDestination,
      Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Scope.record] using active
  have finalStep : ScopedSourcePath .eagerValue program
      (supply,⟨world,restoredScope :: parents⟩) [answer]
      (supply,⟨world,
        Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Scope.record
          scope pending answer :: parents⟩) := by
    refine ⟨1,?_⟩
    simpa only [zero_add,List.append_nil] using
      (Derivation.published
        (rule := sourceRule .eagerValue program)
        ⟨_,rfl,scopedReturn⟩ (.pause _))
  refine ⟨⟨environment,resolved,rfl⟩,?_⟩
  have restoredPath : ScopedSourcePath .eagerValue program
      (supply,⟨world,scope :: parents⟩) []
      (supply,⟨world,restoredScope :: parents⟩) := by
    simpa only [restoredScope] using restorePath.toScoped
  simpa only [List.nil_append] using restoredPath.trans finalStep

/-- A terminal source occurrence and the answer emitted for it retain the
complete relative clause-origin trace. -/
def OriginAnswerRel (program : Program) (root : Control) (baseOrigins : List Nat)
    (terminal : Control) (answer : CollectedAnswer) : Prop :=
  ∃ trace, BranchTrace program root trace terminal ∧
    ResolvedAnswer (baseOrigins ++ trace) terminal answer

/-- Support contributed by the answer of one resolvable terminal control.
Occurrence origins are intentionally absent because they contain no names. -/
def rawAnswerSupport (raw : Control) : Finset String :=
  match resolve raw.bindings with
  | some environment =>
      operandSupport
        (read environment raw.destination ::
          raw.bindings.flatMap (fun pair => [pair.1,pair.2]))
  | none => ∅

theorem resolvedAnswer_support (raw : Control) (origins : List Nat)
    (environment : Environment) (resolved : resolve raw.bindings = some environment) :
    (⟨read environment raw.destination,raw.bindings,origins,[]⟩ : CollectedAnswer).support =
      rawAnswerSupport raw := by
  simp only [CollectedAnswer.support,rawAnswerSupport,resolved,List.append_nil]

private theorem foldCollectedSupport (answers : List CollectedAnswer)
    (initial : Finset String) :
    answers.foldr (fun answer names => answer.support ∪ names) initial =
      answers.foldr (fun answer names => answer.support ∪ names) ∅ ∪ initial := by
  induction answers with
  | nil => simp
  | cons answer answers inductionHypothesis =>
      simp only [List.foldr_cons,inductionHypothesis]
      ac_rfl

theorem collectedSupport_append_answer {Context : Type}
    (parents : List (CollectionScope Context)) (scope : CollectionScope Context)
    (pending : List (CollectionWork Context)) (answer : CollectedAnswer) :
    collectedSupport parents
        {scope with frontier := pending,collected := scope.collected ++ [answer]} =
      collectedSupport parents scope ∪ answer.support := by
  unfold collectedSupport
  rw [List.foldr_append,foldCollectedSupport]
  simp only [List.foldr_cons,List.foldr_nil,Finset.union_empty]
  ac_rfl

/-- Continuation-passing root contract for one raw source control.  It is
parametric in the concrete delimiter representation.  Its explicit support
indices make the source freshening boundary independent of the concrete queue
representation while preserving the exact ordered answer block. -/
def RootContinuationContract {Context : Type} (program : Program)
    (sourceOlder actualOlder : List Goal)
    (raw : Control) (pSupp cSupp : Finset String)
    (terminals : List Control) (cSuppAfter : Finset String) : Prop :=
  ∀ (supply : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World)
    (parents : List (CollectionScope Context)) (scope : CollectionScope Context)
    (actual : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)),
    DelimitedControl sourceOlder actualOlder raw actual →
    scope.frontier = (actual,context,origins) :: pending →
    scope.caller = none →
    pendingSupport pending = pSupp →
    collectedSupport parents scope = cSupp →
    ∃ answers,
      List.Forall₂ (OriginAnswerRel program raw origins) terminals answers ∧
      collectedSupport parents
          {scope with frontier := pending,collected := scope.collected ++ answers} =
        cSuppAfter ∧
      ScopedSourcePath .eagerValue program
        (supply,⟨world,scope :: parents⟩) answers
        (supply,⟨world,
          { scope with frontier := pending, collected := scope.collected ++ answers } :: parents⟩)

/-- One or more silent pre-return source steps transport every concrete
delimiter representation of `raw` to a representation of `next`, without
touching the queue tail or occurrence path. -/
def DelimitedTransition {Context : Type} (program : Program)
    (sourceOlder actualOlder : List Goal)
    (raw next : Control) : Prop :=
  ∀ (supply : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World)
    (parents : List (CollectionScope Context)) (scope : CollectionScope Context)
    (actual : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)),
    DelimitedControl sourceOlder actualOlder raw actual →
    scope.frontier = (actual,context,origins) :: pending →
    ∃ actualNext,
      Nonempty (DelimitedControl sourceOlder actualOlder next actualNext) ∧
      PreReturnPath .eagerValue program
        (supply,⟨world,scope :: parents⟩)
        (supply,⟨world,
          { scope with frontier := (actualNext,context,origins) :: pending } :: parents⟩)

theorem DelimitedTransition.of_local {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {raw next : Control}
    (lift : ∀ (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World)
      (context : Context) (actual : Control),
      DelimitedControl sourceOlder actualOlder raw actual →
      ∃ actualNext,
        Nonempty (DelimitedControl sourceOlder actualOlder next actualNext) ∧
        Source.Step .eagerValue program (⟨world,actual,context⟩ : Cursor Context)
          (.silent (⟨world,actualNext,context⟩ : Cursor Context))) :
    DelimitedTransition (Context := Context) program sourceOlder actualOlder raw next := by
  intro supply world parents scope actual context origins pending related frontier
  obtain ⟨actualNext,nextRelated,localStep⟩ := lift world context actual related
  let nextScope : CollectionScope Context :=
    { scope with frontier := (actualNext,context,origins) :: pending }
  have scopedStep : PreReturnStep .eagerValue program
      (supply,⟨world,scope :: parents⟩)
      (supply,⟨world,nextScope :: parents⟩) := by
    simpa only [nextScope,retainChild] using
      (PreReturnStep.continuing supply world scope parents actual context origins pending
        (⟨world,actualNext,context⟩ : Cursor Context) frontier localStep)
  exact ⟨actualNext,nextRelated,by
    simpa only [nextScope] using PreReturnPath.single scopedStep⟩

theorem DelimitedTransition.of_prepared {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {raw next : Control}
    {expression destination : Atom}
    (atGoal : raw.goals = .evaluate expression destination :: sourceOlder)
    (ordinary : scopedForm expression = false)
    (prepared : Prepared .eagerValue program raw destination sourceOlder expression next)
    (compatible : PreparedDelimitedRel prepared) :
    DelimitedTransition (Context := Context) program sourceOlder actualOlder raw next ∧
      BranchTrace program raw [] next := by
  constructor
  · apply DelimitedTransition.of_local
    intro world context actual related
    obtain ⟨actualNext,nextRelated,actualPrepared⟩ :=
      compatible actualOlder actual related
    have actualAtGoal : actual.goals = .evaluate expression destination ::
        related.restores.map Goal.restoreCommit ++ actualOlder :=
      related.entry_goals (.evaluate expression destination) atGoal
    exact ⟨actualNext,nextRelated,
      .expanded expression destination
        (related.restores.map Goal.restoreCommit ++ actualOlder)
        actualNext actualAtGoal ordinary actualPrepared⟩
  · exact .expanded atGoal ordinary prepared (.refl next)

theorem DelimitedTransition.trans {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {first middle last : Control}
    (beforeTransition : DelimitedTransition (Context := Context) program
      sourceOlder actualOlder first middle)
    (afterTransition : DelimitedTransition (Context := Context) program
      sourceOlder actualOlder middle last) :
    DelimitedTransition (Context := Context) program
      sourceOlder actualOlder first last := by
  intro supply world parents scope actual context origins pending related frontier
  obtain ⟨actualMiddle,⟨middleRelated⟩,firstPath⟩ :=
    beforeTransition supply world parents scope actual context origins pending related frontier
  let middleScope : CollectionScope Context :=
    { scope with frontier := (actualMiddle,context,origins) :: pending }
  obtain ⟨actualLast,lastRelated,secondPath⟩ :=
    afterTransition supply world parents middleScope actualMiddle context origins pending
      middleRelated rfl
  refine ⟨actualLast,lastRelated,?_⟩
  have joined := firstPath.trans secondPath
  simpa only [middleScope] using joined

theorem DelimitedTransition.expanded_replace {Context : Type} {program : Program}
    {raw actualNext : Control} {expression destination : Atom}
    {sourceOlder actualOlder active : List Goal}
    (atGoal : raw.goals = .evaluate expression destination :: sourceOlder)
    (ordinary : scopedForm expression = false)
    (nextEq : actualNext = replace raw (active ++ sourceOlder))
    (prepared : ∀ (actual : Control)
      (related : DelimitedControl sourceOlder actualOlder raw actual),
      Prepared .eagerValue program actual destination
        (related.restores.map Goal.restoreCommit ++ actualOlder) expression
        (replace actual
          (active ++ related.restores.map Goal.restoreCommit ++ actualOlder))) :
    DelimitedTransition (Context := Context) program
      sourceOlder actualOlder raw actualNext := by
  subst actualNext
  apply DelimitedTransition.of_local
  intro world context actual related
  obtain ⟨nextRelated,localStep⟩ := related.expanded_replace atGoal ordinary
    (prepared actual related) world context
  exact ⟨_,⟨nextRelated⟩,localStep⟩

theorem DelimitedTransition.accepted {Context : Type} {program : Program}
    {raw : Control} {value destination : Atom} {sourceOlder actualOlder : List Goal}
    {after : Equations} (atGoal : raw.goals = .equate value destination :: sourceOlder)
    (accepted : Refinement raw.bindings value destination (some after)) :
    DelimitedTransition (Context := Context) program sourceOlder actualOlder raw
      {raw with bindings := after,goals := sourceOlder} := by
  apply DelimitedTransition.of_local
  intro world context actual related
  obtain ⟨nextRelated,localStep⟩ := related.accepted_step atGoal accepted world context
  exact ⟨_,⟨nextRelated⟩,localStep⟩

/-- The common two-step leaf pattern—syntax expansion followed by accepted
equation refinement—lifts once for variables, symbols, grounded atoms and the
empty tuple. -/
theorem direct_evaluation_transition {Context : Type} {program : Program}
    {raw : Control} {expression value destination : Atom}
    {sourceOlder actualOlder : List Goal}
    {after : Equations}
    (atGoal : raw.goals = .evaluate expression destination :: sourceOlder)
    (ordinary : scopedForm expression = false)
    (preparedRaw : Prepared .eagerValue program raw destination sourceOlder expression
      (replace raw ([.equate value destination] ++ sourceOlder)))
    (preparedActual : ∀ (actual : Control)
      (related : DelimitedControl sourceOlder actualOlder raw actual),
      Prepared .eagerValue program actual destination
        (related.restores.map Goal.restoreCommit ++ actualOlder) expression
        (replace actual ([.equate value destination] ++
          related.restores.map Goal.restoreCommit ++ actualOlder)))
    (accepted : Refinement raw.bindings value destination (some after)) :
    DelimitedTransition (Context := Context) program sourceOlder actualOlder raw
        {raw with bindings := after,goals := sourceOlder} ∧
      BranchTrace program raw []
        {raw with bindings := after,goals := sourceOlder} := by
  let middle : Control := replace raw ([.equate value destination] ++ sourceOlder)
  have expanded : DelimitedTransition (Context := Context) program
      sourceOlder actualOlder raw middle := by
    apply DelimitedTransition.expanded_replace atGoal ordinary rfl
    exact preparedActual
  have middleAccepted : Refinement middle.bindings value destination (some after) := by
    simpa only [middle,replace] using accepted
  have refined : DelimitedTransition (Context := Context) program
      sourceOlder actualOlder middle
      {middle with bindings := after,goals := sourceOlder} :=
    DelimitedTransition.accepted rfl middleAccepted
  have combined := expanded.trans refined
  have trace : BranchTrace program raw []
      {middle with bindings := after,goals := sourceOlder} :=
    .expanded atGoal ordinary preparedRaw (.accepted rfl middleAccepted (.refl _))
  simpa only [middle,replace] using And.intro combined trace

/-- A silent delimited prefix composes in front of any root continuation
contract. -/
theorem RootContinuationContract.prepend {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {raw next : Control}
    {pSupp cSupp cSuppAfter : Finset String}
    {terminals : List Control}
    (sourceTrace : BranchTrace program raw [] next)
    (beforeTransition : DelimitedTransition (Context := Context) program
      sourceOlder actualOlder raw next)
    (suffix : RootContinuationContract (Context := Context) program
      sourceOlder actualOlder next
      pSupp cSupp terminals cSuppAfter) :
    RootContinuationContract (Context := Context) program sourceOlder actualOlder raw
      pSupp cSupp terminals cSuppAfter := by
  intro supply world parents scope actual context origins pending related frontier root
    pendingEq collectedEq
  obtain ⟨actualNext,⟨nextRelated⟩,beforePath⟩ :=
    beforeTransition supply world parents scope actual context origins pending related frontier
  let nextScope : CollectionScope Context :=
    { scope with frontier := (actualNext,context,origins) :: pending }
  obtain ⟨answers,answersRelated,supportAfter,afterPath⟩ :=
    suffix supply world parents nextScope actualNext context origins pending nextRelated rfl
      (by simpa only [nextScope] using root) pendingEq
      (by
        change collectedSupport parents scope = cSupp
        exact collectedEq)
  have rebased : List.Forall₂ (OriginAnswerRel program raw origins) terminals answers :=
    answersRelated.imp fun terminal answer related => by
      obtain ⟨trace,path,resolved⟩ := related
      exact ⟨trace,by simpa only [List.nil_append] using sourceTrace.trans path,resolved⟩
  refine ⟨answers,rebased,by simpa only [nextScope] using supportAfter,?_⟩
  have joined := beforePath.toScoped.trans afterPath
  simpa only [nextScope,List.nil_append] using joined

/-- A continuation for argument heads lifts across the sibling goals of the
current argument.  Inner predicate delimiters are popped first; the enclosing
delimiter stack is then reconstructed behind the siblings. -/
theorem RootContinuationContract.lift_argument {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal}
    (olderAtoms : actualOlder.flatMap Goal.atoms = sourceOlder.flatMap Goal.atoms)
    (outerRestores : List Nat) {rows : List (Atom × Atom)} {final : Goal}
    {head : Control} {pSupp cSupp cSuppAfter : Finset String}
    {terminals : List Control}
    (headGoals : head.goals = evaluationGoals rows ++ final :: sourceOlder)
    (outer : RootContinuationContract (Context := Context) program
      sourceOlder actualOlder head pSupp cSupp terminals cSuppAfter) :
    RootContinuationContract (Context := Context) program
      (evaluationGoals rows ++ final :: sourceOlder)
      (evaluationGoals rows ++ final ::
        (outerRestores.map Goal.restoreCommit ++ actualOlder))
      head pSupp cSupp terminals cSuppAfter := by
  intro supply world parents scope actualHead context origins pending related frontier root
    pendingEq collectedEq
  obtain ⟨reached,reachedBindings,reachedDestination,reachedReserved,reachedGoals,
      restorePath⟩ :=
    drain_restoreCommits program supply world parents scope head actualHead
      (evaluationGoals rows ++ final :: sourceOlder)
      (evaluationGoals rows ++ final ::
        (outerRestores.map Goal.restoreCommit ++ actualOlder))
      context origins pending related headGoals frontier
  have outerRelated : DelimitedControl sourceOlder actualOlder head reached :=
    DelimitedControl.exit_argument olderAtoms outerRestores reachedBindings
      reachedDestination reachedReserved headGoals reachedGoals
  let reachedScope : CollectionScope Context :=
    {scope with frontier := (reached,context,origins) :: pending}
  obtain ⟨answers,answersRelated,supportAfter,afterPath⟩ :=
    outer supply world parents reachedScope reached context origins pending outerRelated rfl
      (by simpa only [reachedScope] using root) pendingEq
      (by
        change collectedSupport parents scope = cSupp
        exact collectedEq)
  refine ⟨answers,answersRelated,by simpa only [reachedScope] using supportAfter,?_⟩
  have joined := restorePath.toScoped.trans afterPath
  simpa only [reachedScope,List.nil_append] using joined

/-- Total support added by a consecutive block of outcome continuations. -/
def supportIncrement (increments : List (Finset String)) : Finset String :=
  increments.foldr (· ∪ ·) ∅

def zipSupportIncrements (queued : List (Control × Finset String))
    (increments : List (Finset String)) :
    List ((Control × Finset String) × Finset String) :=
  queued.zip increments

/-- One ordered occurrence consumes the accumulated support state and returns
the exact state obtained by adjoining its declared continuation increment. -/
def RootContinuationStep {Context : Type} (program : Program)
    (sourceOlder actualOlder : List Goal) :
    ((Control × Finset String) × Finset String) →
      Finset String → List Control → Finset String → Prop :=
  fun item before block after =>
    after = before ∪ item.2 ∧
      RootContinuationContract (Context := Context) program sourceOlder actualOlder item.1.1
        item.1.2 before block (before ∪ item.2)

/-- Existing ordered state-flat-map composition is the continuation chain for
successive DFS occurrences.  No second list-fold or scheduler is introduced. -/
abbrev RootContinuationChain {Context : Type} (program : Program)
    (sourceOlder actualOlder : List Goal)
    (queued : List (Control × Finset String))
    (increments : List (Finset String)) (cSupp : Finset String)
    (terminals : List Control) (cSuppAfter : Finset String) : Prop :=
  queued.length = increments.length ∧
    OrderedStateFlatMapRel
      (RootContinuationStep (Context := Context) program sourceOlder actualOlder)
      (zipSupportIncrements queued increments) cSupp terminals cSuppAfter

private theorem rootContinuationRun_cSuppAfter_eq {Context : Type}
    {program : Program} {sourceOlder actualOlder : List Goal}
    {items : List ((Control × Finset String) × Finset String)}
    {cSupp cSuppAfter : Finset String} {terminals : List Control}
    (source : OrderedStateFlatMapRel
      (RootContinuationStep (Context := Context) program sourceOlder actualOlder)
      items cSupp terminals cSuppAfter) :
    cSuppAfter = cSupp ∪ supportIncrement (items.map Prod.snd) := by
  induction source with
  | nil => simp [supportIncrement]
  | cons head _tail inductionHypothesis =>
      rcases head with ⟨rfl,_contract⟩
      rw [inductionHypothesis]
      simp only [List.map_cons,supportIncrement,List.foldr_cons]
      ac_rfl

theorem RootContinuationChain.cSuppAfter_eq {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {queued : List (Control × Finset String)}
    {increments : List (Finset String)} {cSupp cSuppAfter : Finset String}
    {terminals : List Control}
    (source : RootContinuationChain (Context := Context) program sourceOlder actualOlder
      queued increments cSupp terminals cSuppAfter) :
    cSuppAfter = cSupp ∪ supportIncrement increments := by
  rw [rootContinuationRun_cSuppAfter_eq source.2]
  unfold zipSupportIncrements
  rw [List.map_snd_zip (le_of_eq source.1.symm)]

/-- Split an ordered continuation chain at a structural source boundary.  The
middle support is the state actually reached after the left answer block. -/
theorem RootContinuationChain.split_append {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {left right : List (Control × Finset String)}
    {leftIncrements rightIncrements : List (Finset String)}
    {cSupp cSuppAfter : Finset String} {terminals : List Control}
    (source : RootContinuationChain (Context := Context) program sourceOlder actualOlder
      (left ++ right) (leftIncrements ++ rightIncrements)
      cSupp terminals cSuppAfter)
    (leftLength : left.length = leftIncrements.length) :
    ∃ middle leftTerminals rightTerminals,
      terminals = leftTerminals ++ rightTerminals ∧
      RootContinuationChain (Context := Context) program sourceOlder actualOlder
        left leftIncrements cSupp leftTerminals middle ∧
      RootContinuationChain (Context := Context) program sourceOlder actualOlder
        right rightIncrements middle rightTerminals cSuppAfter := by
  have rightLength : right.length = rightIncrements.length := by
    have totalLength := source.1
    simp only [List.length_append] at totalLength
    omega
  have run : OrderedStateFlatMapRel
      (RootContinuationStep (Context := Context) program sourceOlder actualOlder)
      (zipSupportIncrements left leftIncrements ++
        zipSupportIncrements right rightIncrements)
      cSupp terminals cSuppAfter := by
    simpa only [zipSupportIncrements,List.zip_append leftLength] using source.2
  obtain ⟨middle,leftTerminals,rightTerminals,terminalsEq,leftRun,rightRun⟩ :=
    OrderedStateFlatMapRel.split
      (zipSupportIncrements left leftIncrements)
      (zipSupportIncrements right rightIncrements) run
  exact ⟨middle,leftTerminals,rightTerminals,terminalsEq,
    ⟨leftLength,leftRun⟩,⟨rightLength,rightRun⟩⟩

/-- Execute an ordered continuation chain against its concrete retained queue.
The resulting answers are rebased to the common source root and base origin
path, preserving every occurrence and its order. -/
theorem RootContinuationChain.run_queue {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {rootControl : Control}
    {baseOrigins : List Nat} {basePending : List (CollectionWork Context)}
    {queued : List (Control × Finset String)} {work : List (CollectionWork Context)}
    {increments : List (Finset String)} {cSupp cSuppAfter : Finset String}
    {terminals : List Control}
    (source : RootContinuationChain (Context := Context) program
      sourceOlder actualOlder queued increments cSupp terminals cSuppAfter)
    (related : QueuedWorkRel program sourceOlder actualOlder rootControl
      baseOrigins basePending queued work)
    (supply : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (world : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.World)
    (parents : List (CollectionScope Context)) (scope : CollectionScope Context)
    (frontier : scope.frontier = work ++ basePending)
    (root : scope.caller = none)
    (collectedEq : collectedSupport parents scope = cSupp) :
    ∃ answers,
      List.Forall₂ (OriginAnswerRel program rootControl baseOrigins) terminals answers ∧
      collectedSupport parents
          {scope with frontier := basePending,collected := scope.collected ++ answers} =
        cSuppAfter ∧
      ScopedSourcePath .eagerValue program
        (supply,⟨world,scope :: parents⟩) answers
        (supply,⟨world,
          {scope with frontier := basePending,collected := scope.collected ++ answers} ::
          parents⟩) := by
  induction related generalizing increments cSupp terminals scope with
  | nil =>
      have incrementsNil : increments = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa only [List.length_nil] using source.1.symm
      subst increments
      cases source.2
      have sameScope :
          {scope with frontier := basePending,collected := scope.collected} = scope := by
        cases scope
        simp_all
      refine ⟨[],.nil,?_,?_⟩
      · simpa only [List.append_nil,sameScope] using collectedEq
      · have path := (PreReturnPath.refl .eagerValue program
          (supply,⟨world,scope :: parents⟩)).toScoped
        simpa only [List.append_nil,sameScope] using path
  | @cons raw actual pSupp context origins trace queued work related path originsEq
      supportEq rest inductionHypothesis =>
      cases increments with
      | nil =>
          have impossible := source.1
          simp at impossible
      | cons increment increments =>
          rcases source with ⟨lengthEq,run⟩
          cases run with
          | @cons _ _ _ middle _ headTerminals tailTerminals headStep tailRun =>
              rcases headStep with ⟨rfl,headContract⟩
              obtain ⟨relatedProof⟩ := related
              have headFrontier : scope.frontier =
                  (actual,context,origins) :: (work ++ basePending) := by
                simpa only [List.cons_append] using frontier
              obtain ⟨headAnswers,headRelated,headSupport,headPath⟩ :=
                headContract supply world parents scope actual context origins
                  (work ++ basePending) relatedProof headFrontier root
                  supportEq.symm collectedEq
              let middleScope : CollectionScope Context :=
                { frontier := work ++ basePending
                  collected := scope.collected ++ headAnswers
                  caller := scope.caller }
              have tailLength : queued.length = increments.length := by
                simpa only [List.length_cons,Nat.succ.injEq] using lengthEq
              obtain ⟨tailAnswers,tailRelated,tailSupport,tailPath⟩ :=
                inductionHypothesis
                  (source := ⟨tailLength,tailRun⟩)
                  (scope := middleScope) (frontier := rfl)
                  (root := by simpa only [middleScope] using root)
                  (collectedEq := by simpa only [middleScope] using headSupport)
              have rebasedHead : List.Forall₂
                  (OriginAnswerRel program rootControl baseOrigins)
                  headTerminals headAnswers :=
                headRelated.imp fun terminal answer answerRelated => by
                  obtain ⟨suffix,suffixPath,resolved⟩ := answerRelated
                  exact ⟨trace ++ suffix,path.trans suffixPath,by
                    simpa only [originsEq,List.append_assoc] using resolved⟩
              refine ⟨headAnswers ++ tailAnswers,
                List.rel_append rebasedHead tailRelated,?_,?_⟩
              · simpa only [middleScope,List.append_assoc] using tailSupport
              · have joined := headPath.trans tailPath
                simpa only [middleScope,List.append_assoc] using joined

/-- Lift every argument-head continuation across the same remaining sibling
goals and enclosing delimiter stack. -/
theorem RootContinuationChain.lift_argument {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal}
    (olderAtoms : actualOlder.flatMap Goal.atoms = sourceOlder.flatMap Goal.atoms)
    (outerRestores : List Nat) {rows : List (Atom × Atom)} {final : Goal}
    {queued : List (Control × Finset String)}
    {increments : List (Finset String)} {cSupp cSuppAfter : Finset String}
    {terminals : List Control}
    (ready : ∀ item ∈ queued,
      item.1.goals = evaluationGoals rows ++ final :: sourceOlder)
    (source : RootContinuationChain (Context := Context) program
      sourceOlder actualOlder queued increments cSupp terminals cSuppAfter) :
    RootContinuationChain (Context := Context) program
      (evaluationGoals rows ++ final :: sourceOlder)
      (evaluationGoals rows ++ final ::
        (outerRestores.map Goal.restoreCommit ++ actualOlder))
      queued increments cSupp terminals cSuppAfter := by
  induction queued generalizing increments cSupp terminals with
  | nil =>
      have incrementsNil : increments = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa only [List.length_nil] using source.1.symm
      subst increments
      cases source.2
      exact ⟨rfl,.nil _⟩
  | cons item queued inductionHypothesis =>
      cases increments with
      | nil =>
          have impossible := source.1
          simp at impossible
      | cons increment increments =>
          rcases source with ⟨lengthEq,run⟩
          cases run with
          | cons first rest =>
              have tailLength : queued.length = increments.length := by
                simpa only [List.length_cons,Nat.succ.injEq] using lengthEq
              have liftedFirst : RootContinuationStep (Context := Context) program
                  (evaluationGoals rows ++ final :: sourceOlder)
                  (evaluationGoals rows ++ final ::
                    (outerRestores.map Goal.restoreCommit ++ actualOlder))
                  (item,increment) _ _ _ := ⟨first.1,
                first.2.lift_argument olderAtoms outerRestores
                  (ready item List.mem_cons_self)⟩
              have liftedRest := inductionHypothesis
                (increments := increments)
                (ready := fun candidate member =>
                  ready candidate (List.mem_cons_of_mem item member))
                (source := ⟨tailLength,rest⟩)
              exact ⟨lengthEq,.cons liftedFirst liftedRest.2⟩

theorem RootContinuationChain.singleton_inv {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {control : Control}
    {pSupp cSupp cSuppAfter : Finset String}
    {increment : Finset String} {terminals : List Control}
    (source : RootContinuationChain (Context := Context) program sourceOlder actualOlder
      [(control,pSupp)] [increment] cSupp terminals cSuppAfter) :
    cSuppAfter = cSupp ∪ increment ∧
      RootContinuationContract (Context := Context) program sourceOlder actualOlder control
        pSupp cSupp terminals (cSupp ∪ increment) := by
  rcases source with ⟨_length,run⟩
  cases run with
  | cons head tail =>
      cases tail
      simpa only [zipSupportIncrements,List.zip_cons_cons,List.zip_nil_left,
        List.append_nil,RootContinuationStep] using head

theorem RootContinuationChain.singleton_contract {Context : Type} {program : Program}
    {sourceOlder actualOlder : List Goal} {control : Control}
    {pSupp cSupp cSuppAfter : Finset String} {increments : List (Finset String)}
    {terminals : List Control}
    (source : RootContinuationChain (Context := Context) program sourceOlder actualOlder
      [(control,pSupp)] increments cSupp terminals cSuppAfter) :
    RootContinuationContract (Context := Context) program sourceOlder actualOlder
      control pSupp cSupp terminals cSuppAfter := by
  cases increments with
  | nil =>
      have impossible := source.1
      simp at impossible
  | cons increment increments =>
      have tailNil : increments = [] := by
        apply List.eq_nil_of_length_eq_zero
        have lengthEq : 1 = Nat.succ increments.length := by
          simpa only [List.length_cons,List.length_nil] using source.1
        omega
      subst increments
      obtain ⟨rfl,contract⟩ := RootContinuationChain.singleton_inv source
      exact contract

theorem direct_evaluation_contract {Context : Type} {program : Program}
    {raw after : Control} {sourceOlder actualOlder : List Goal}
    {pSupp cSupp cSuppAfter : Finset String}
    {increments : List (Finset String)} {terminals : List Control}
    (transition : DelimitedTransition (Context := Context) program
      sourceOlder actualOlder raw after)
    (trace : BranchTrace program raw [] after)
    (continuation : RootContinuationChain (Context := Context) program sourceOlder actualOlder
      [(after,pSupp)] increments cSupp terminals cSuppAfter) :
    RootContinuationContract (Context := Context) program sourceOlder actualOlder raw
      pSupp cSupp terminals cSuppAfter := by
  exact continuation.singleton_contract.prepend trace transition

theorem root_terminal_contract {Context : Type} (program : Program) (raw : Control)
    (pSupp cSupp : Finset String) (atEnd : raw.goals = [])
    (resolvable : ∃ environment, resolve raw.bindings = some environment) :
    RootContinuationContract (Context := Context) program [] [] raw pSupp cSupp [raw]
      (cSupp ∪ rawAnswerSupport raw) := by
  intro supply world parents scope actual context origins pending related frontier root
    _pendingEq collectedEq
  obtain ⟨environment,resolved⟩ := resolvable
  let answer : CollectedAnswer :=
    ⟨read environment raw.destination,raw.bindings,origins,[]⟩
  have drained := root_terminal_drain program supply world parents scope raw actual context origins
    pending environment related atEnd frontier root resolved
  refine ⟨[answer],?_,?_,?_⟩
  · exact .cons ⟨[],.refl raw,by simpa only [List.append_nil,answer] using drained.1⟩ .nil
  · calc
      collectedSupport parents
          {scope with frontier := pending,collected := scope.collected ++ [answer]} =
          collectedSupport parents scope ∪ answer.support :=
        collectedSupport_append_answer parents scope pending answer
      _ = cSupp ∪ rawAnswerSupport raw := by
        rw [collectedEq,resolvedAnswer_support raw origins environment resolved]
  · simpa only [Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Scope.record,answer]
      using drained.2

/-- Every ordered list of terminal outcomes supplies its own singleton block;
the queue-support assignments are supplied by the source tree, so pending
intermediate alternatives are retained exactly. -/
theorem root_terminal_chain {Context : Type} (program : Program)
    (outcomes : List Control) (queued : List (Control × Finset String))
    (cSupp : Finset String) (aligned : queued.map Prod.fst = outcomes)
    (ready : ∀ outcome ∈ outcomes,
      outcome.goals = [] ∧ ∃ environment, resolve outcome.bindings = some environment) :
      RootContinuationChain (Context := Context) program [] []
      queued (outcomes.map rawAnswerSupport)
      cSupp outcomes (cSupp ∪ supportIncrement (outcomes.map rawAnswerSupport)) := by
  induction outcomes generalizing queued cSupp with
  | nil =>
      have queuedNil : queued = [] := by
        cases queued with
        | nil => rfl
        | cons item queued => simp at aligned
      subst queued
      exact ⟨rfl,by
        simpa only [List.map_nil,zipSupportIncrements,List.zip_nil_left,
          supportIncrement,List.foldr_nil,Finset.union_empty] using
          (OrderedStateFlatMapRel.nil
            (step := RootContinuationStep (Context := Context) program [] []) cSupp)⟩
  | cons outcome outcomes inductionHypothesis =>
      cases queued with
      | nil => simp at aligned
      | cons item queued =>
        rcases item with ⟨actualOutcome,pSupp⟩
        simp only [List.map_cons,List.cons.injEq] at aligned
        rcases aligned with ⟨actualEq,tailAligned⟩
        subst actualOutcome
        have head := root_terminal_contract (Context := Context) program outcome
          pSupp cSupp
          (ready outcome List.mem_cons_self).1 (ready outcome List.mem_cons_self).2
        have tail := inductionHypothesis
          queued (cSupp := cSupp ∪ rawAnswerSupport outcome) tailAligned
          (fun candidate member => ready candidate (List.mem_cons_of_mem _ member))
        have headStep :
            RootContinuationStep (Context := Context) program [] []
              ((outcome,pSupp),rawAnswerSupport outcome)
              cSupp [outcome] (cSupp ∪ rawAnswerSupport outcome) := ⟨rfl,head⟩
        refine ⟨?_,?_⟩
        · simpa only [List.length_cons,List.length_map] using
            congrArg Nat.succ tail.1
        simpa only [List.map_cons,zipSupportIncrements,List.zip_cons_cons,
          List.singleton_append,supportIncrement,List.foldr_cons,Finset.union_assoc] using
            (OrderedStateFlatMapRel.cons
              (step := RootContinuationStep (Context := Context) program [] []) headStep tail.2)

mutual
/-- Static queue-tail support carried by every outcome of a source subtree.
The assignment follows DFS order and does not mention a machine execution. -/
def Evaluation.queuedOutcomes {program : Program} {control : Control}
    {expression destination : Atom} {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination older outcomes)
    (pSupp : Finset String) : List (Control × Finset String) :=
  match source with
  | @Evaluation.variable _ control _ _ older after _ _ _ |
    @Evaluation.symbol _ control _ _ older after _ _ _ |
    @Evaluation.grounded _ control _ _ older after _ _ _ |
    @Evaluation.unit _ control _ older after _ _ _ =>
      [({control with bindings := after,goals := older},pSupp)]
  | .constructor _ _ _ _ argumentsRun | .call _ _ _ _ argumentsRun =>
      Arguments.queuedOutcomes argumentsRun pSupp
termination_by structural source

def Arguments.queuedOutcomes {program : Program} {control : Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : Arguments program control rows assembled destination final older outcomes)
    (pSupp : Finset String) : List (Control × Finset String) :=
  match source with
  | .nil _ continued => Invocation.queuedOutcomes continued pSupp
  | .cons _ first branches =>
      ArgumentBranches.queuedOutcomes branches (Evaluation.queuedOutcomes first pSupp)
termination_by structural source

def ArgumentBranches.queuedOutcomes {program : Program} {heads : List Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes)
    (headsQueued : List (Control × Finset String)) : List (Control × Finset String) :=
  match source,headsQueued with
  | .nil,_ => []
  | .cons first remaining,(_,headPSupp) :: restQueued =>
      Arguments.queuedOutcomes first headPSupp ++
        ArgumentBranches.queuedOutcomes remaining restQueued
  | .cons _ _,[] => []
termination_by structural source

def Invocation.queuedOutcomes {program : Program} {control : Control}
    {assembled destination : Atom} {final : Goal} {older : List Goal}
    {outcomes : List Control}
    (source : Invocation program control assembled destination final older outcomes)
    (pSupp : Finset String) : List (Control × Finset String) :=
  match source with
  | @Invocation.constructor _ control _ _ _ older after _ _ _ _ =>
      [({control with bindings := after,goals := older},pSupp)]
  | .equations _ _ _ _ _ _ _ bodies => Bodies.queuedOutcomes bodies pSupp
termination_by structural source

def Bodies.queuedOutcomes {program : Program} {destination : Atom} {older : List Goal}
    {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes)
    (pSupp : Finset String) : List (Control × Finset String) :=
  match source with
  | .nil => []
  | @Bodies.cons _ _ _ _ _ remaining _ _ _ _ first later =>
      let pSuppHead := remaining.foldr (fun row names => row.2.support ∪ names) pSupp
      Evaluation.queuedOutcomes first pSuppHead ++ Bodies.queuedOutcomes later pSupp
termination_by structural source
end

/-- Collapse the continuation-support slices of each head occurrence into the
single increment seen while producing that head. -/
def ArgumentBranches.headContSupports {program : Program} {heads : List Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes)
    (contSupports : List (Finset String)) : List (Finset String) :=
  match source with
  | .nil => []
  | @ArgumentBranches.cons _ _ _ _ _ _ _ _ children _ first remaining =>
      supportIncrement (contSupports.take children.length) ::
        ArgumentBranches.headContSupports remaining (contSupports.drop children.length)
termination_by structural source

/-- Collapse each selected clause body's final continuation-support slice into
the single increment of that selected work item. -/
def Bodies.headContSupports {program : Program} {destination : Atom}
    {older : List Goal} {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes)
    (contSupports : List (Finset String)) : List (Finset String) :=
  match source with
  | .nil => []
  | @Bodies.cons _ _ _ _ _ _ _ children _ _ first later =>
      supportIncrement (contSupports.take children.length) ::
        Bodies.headContSupports later (contSupports.drop children.length)
termination_by structural source

mutual
/-- Pure synchronization of equation-freshening boundaries with the static
DFS queue support and the support accumulated by outer continuations. -/
def Evaluation.ExtraSynchronized {program : Program} {control : Control}
    {expression destination : Atom} {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination older outcomes)
    (pSupp cSupp : Finset String) (contSupports : List (Finset String)) : Prop :=
  match source with
  | .variable _ _ _ | .symbol _ _ _ | .grounded _ _ _ | .unit _ _ _ => True
  | .constructor _ _ _ prepared argumentsRun | .call _ _ _ prepared argumentsRun =>
      PreparedDelimitedRel prepared ∧
        Arguments.ExtraSynchronized argumentsRun pSupp cSupp contSupports
termination_by structural source

def Arguments.ExtraSynchronized {program : Program} {control : Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : Arguments program control rows assembled destination final older outcomes)
    (pSupp cSupp : Finset String) (contSupports : List (Finset String)) : Prop :=
  match source with
  | .nil _ continued => Invocation.ExtraSynchronized continued pSupp cSupp contSupports
  | .cons _ first branches =>
      Evaluation.ExtraSynchronized first pSupp cSupp
          (ArgumentBranches.headContSupports branches contSupports) ∧
        ArgumentBranches.ExtraSynchronized branches
          (Evaluation.queuedOutcomes first pSupp) cSupp contSupports
termination_by structural source

def ArgumentBranches.ExtraSynchronized {program : Program} {heads : List Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes)
    (headsQueued : List (Control × Finset String)) (cSupp : Finset String)
    (contSupports : List (Finset String)) : Prop :=
  match source,headsQueued with
  | .nil,_ => True
  | @ArgumentBranches.cons _ _ _ _ _ _ _ _ children _ first remaining,
      (_,headPSupp) :: restQueued =>
      Arguments.ExtraSynchronized first headPSupp cSupp
          (contSupports.take children.length) ∧
        ArgumentBranches.ExtraSynchronized remaining restQueued
          (cSupp ∪ supportIncrement (contSupports.take children.length))
          (contSupports.drop children.length)
  | .cons _ _,[] => False
termination_by structural source

def Invocation.ExtraSynchronized {program : Program} {control : Control}
    {assembled destination : Atom} {final : Goal} {older : List Goal}
    {outcomes : List Control}
    (source : Invocation program control assembled destination final older outcomes)
    (pSupp cSupp : Finset String) (contSupports : List (Finset String)) : Prop :=
  match source with
  | .constructor _ _ _ _ => True
  | @Invocation.equations _ control extra _ _ _ _ _ _ _ _ _ _ _ _ _ _ bodies =>
      (protectControl control (control.support ∪ pSupp ∪ cSupp)).reserved =
          (protectControl control extra).reserved ∧
        Bodies.ExtraSynchronized bodies pSupp cSupp contSupports
termination_by structural source

def Bodies.ExtraSynchronized {program : Program} {destination : Atom} {older : List Goal}
    {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes)
    (pSupp cSupp : Finset String) (contSupports : List (Finset String)) : Prop :=
  match source with
  | .nil => True
  | @Bodies.cons _ _ _ _ _ remaining _ children _ _ first later =>
      Evaluation.ExtraSynchronized first
          (remaining.foldr (fun row names => row.2.support ∪ names) pSupp)
          cSupp (contSupports.take children.length) ∧
        Bodies.ExtraSynchronized later pSupp
          (cSupp ∪ supportIncrement (contSupports.take children.length))
          (contSupports.drop children.length)
termination_by structural source
end

mutual
/-- Structural height shared by proofs which recurse across the five mutually
inductive open-source judgments. -/
def Evaluation.height {program : Program} {control : Control}
    {expression destination : Atom} {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination older outcomes) : Nat :=
  match source with
  | .variable _ _ _ | .symbol _ _ _ | .grounded _ _ _ | .unit _ _ _ => 1
  | .constructor _ _ _ _ argumentsRun | .call _ _ _ _ argumentsRun =>
      Arguments.height argumentsRun + 1
termination_by structural source

def Arguments.height {program : Program} {control : Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : Arguments program control rows assembled destination final older outcomes) : Nat :=
  match source with
  | .nil _ continued => Invocation.height continued + 1
  | .cons _ first branches =>
      Nat.max (Evaluation.height first) (ArgumentBranches.height branches) + 1
termination_by structural source

def ArgumentBranches.height {program : Program} {heads : List Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes) : Nat :=
  match source with
  | .nil => 1
  | .cons first remaining =>
      Nat.max (Arguments.height first) (ArgumentBranches.height remaining) + 1
termination_by structural source

def Invocation.height {program : Program} {control : Control}
    {assembled destination : Atom} {final : Goal} {older : List Goal}
    {outcomes : List Control}
    (source : Invocation program control assembled destination final older outcomes) : Nat :=
  match source with
  | .constructor _ _ _ _ => 1
  | .equations _ _ _ _ _ _ _ bodies => Bodies.height bodies + 1
termination_by structural source

def Bodies.height {program : Program} {destination : Atom} {older : List Goal}
    {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes) : Nat :=
  match source with
  | .nil => 1
  | .cons _ first later =>
      Nat.max (Evaluation.height first) (Bodies.height later) + 1
termination_by structural source
end

mutual
theorem Evaluation.queuedOutcomes_fst {program : Program} {control : Control}
    {expression destination : Atom} {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination older outcomes)
    (pSupp : Finset String) :
    (Evaluation.queuedOutcomes source pSupp).map Prod.fst = outcomes := by
  match source with
  | .variable _ _ _ | .symbol _ _ _ | .grounded _ _ _ | .unit _ _ _ => rfl
  | .constructor _ _ _ _ argumentsRun | .call _ _ _ _ argumentsRun =>
      exact Arguments.queuedOutcomes_fst argumentsRun pSupp
termination_by Evaluation.height source
decreasing_by all_goals simp [Evaluation.height]

theorem Arguments.queuedOutcomes_fst {program : Program} {control : Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : Arguments program control rows assembled destination final older outcomes)
    (pSupp : Finset String) :
    (Arguments.queuedOutcomes source pSupp).map Prod.fst = outcomes := by
  match source with
  | .nil _ continued => exact Invocation.queuedOutcomes_fst continued pSupp
  | .cons _ first branches =>
      exact ArgumentBranches.queuedOutcomes_fst branches
        (Evaluation.queuedOutcomes first pSupp)
        (Evaluation.queuedOutcomes_fst first pSupp)
termination_by Arguments.height source
decreasing_by all_goals simp [Arguments.height]

theorem ArgumentBranches.queuedOutcomes_fst {program : Program} {heads : List Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes)
    (headsQueued : List (Control × Finset String))
    (aligned : headsQueued.map Prod.fst = heads) :
    (ArgumentBranches.queuedOutcomes source headsQueued).map Prod.fst = outcomes := by
  match source with
  | .nil =>
      cases headsQueued with
      | nil => rfl
      | cons head tail => simp at aligned
  | .cons first remaining =>
      cases headsQueued with
      | nil => simp at aligned
      | cons queuedHead restQueued =>
          rcases queuedHead with ⟨actualHead,headPSupp⟩
          simp only [List.map_cons,List.cons.injEq] at aligned
          rcases aligned with ⟨_headAligned,restAligned⟩
          simp only [ArgumentBranches.queuedOutcomes,List.map_append,
            Arguments.queuedOutcomes_fst first headPSupp,
            ArgumentBranches.queuedOutcomes_fst remaining restQueued restAligned]
termination_by ArgumentBranches.height source
decreasing_by all_goals simp [ArgumentBranches.height]

theorem Invocation.queuedOutcomes_fst {program : Program} {control : Control}
    {assembled destination : Atom} {final : Goal} {older : List Goal}
    {outcomes : List Control}
    (source : Invocation program control assembled destination final older outcomes)
    (pSupp : Finset String) :
    (Invocation.queuedOutcomes source pSupp).map Prod.fst = outcomes := by
  match source with
  | .constructor _ _ _ _ => rfl
  | .equations _ _ _ _ _ _ _ bodies => exact Bodies.queuedOutcomes_fst bodies pSupp
termination_by Invocation.height source
decreasing_by all_goals simp [Invocation.height]

theorem Bodies.queuedOutcomes_fst {program : Program} {destination : Atom}
    {older : List Goal} {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes)
    (pSupp : Finset String) :
    (Bodies.queuedOutcomes source pSupp).map Prod.fst = outcomes := by
  match source with
  | .nil => rfl
  | @Bodies.cons _ _ _ _ _ remaining _ _ _ _ first later =>
      simp only [Bodies.queuedOutcomes,List.map_append,
        Evaluation.queuedOutcomes_fst first
          (remaining.foldr (fun row names => row.2.support ∪ names) pSupp),
        Bodies.queuedOutcomes_fst later pSupp]
termination_by Bodies.height source
decreasing_by all_goals simp [Bodies.height]
end

theorem Evaluation.queuedOutcomes_length {program : Program} {control : Control}
    {expression destination : Atom} {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination older outcomes)
    (pSupp : Finset String) :
    (Evaluation.queuedOutcomes source pSupp).length = outcomes.length := by
  have same := congrArg List.length (Evaluation.queuedOutcomes_fst source pSupp)
  simpa only [List.length_map] using same

theorem ArgumentBranches.headContSupports_length {program : Program}
    {heads : List Control} {rows : List (Atom × Atom)} {assembled destination : Atom}
    {final : Goal} {older : List Goal} {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes)
    (contSupports : List (Finset String))
    (sameLength : contSupports.length = outcomes.length) :
    (ArgumentBranches.headContSupports source contSupports).length = heads.length := by
  match source with
  | .nil => rfl
  | @ArgumentBranches.cons _ _ _ _ _ _ _ _ children rest first remaining =>
      have restLength : (contSupports.drop children.length).length = rest.length := by
        simp only [List.length_drop,List.length_append] at sameLength ⊢
        omega
      simp only [ArgumentBranches.headContSupports,List.length_cons,
        ArgumentBranches.headContSupports_length remaining
          (contSupports.drop children.length) restLength]
termination_by structural source

theorem Bodies.headContSupports_length {program : Program} {destination : Atom}
    {older : List Goal} {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes)
    (contSupports : List (Finset String))
    (sameLength : contSupports.length = outcomes.length) :
    (Bodies.headContSupports source contSupports).length = selected.length := by
  match source with
  | .nil => rfl
  | @Bodies.cons _ _ _ _ _ _ _ children rest _ first later =>
      have restLength : (contSupports.drop children.length).length = rest.length := by
        simp only [List.length_drop,List.length_append] at sameLength ⊢
        omega
      simp only [Bodies.headContSupports,List.length_cons,
        Bodies.headContSupports_length later (contSupports.drop children.length) restLength]
termination_by structural source

theorem queuedSelections_length (base : Finset String)
    (selected : List (Nat × Control)) :
    (queuedSelections base selected).length = selected.length := by
  induction selected with
  | nil => rfl
  | cons row selected inductionHypothesis =>
      simp only [queuedSelections,List.length_cons,inductionHypothesis]

theorem queuedSelections_fst (base : Finset String)
    (selected : List (Nat × Control)) :
    (queuedSelections base selected).map Prod.fst = selected.map Prod.snd := by
  induction selected with
  | nil => rfl
  | cons row selected inductionHypothesis =>
      simp only [queuedSelections,List.map_cons,inductionHypothesis]

mutual
theorem Evaluation.drain {Context : Type} {program : Program} {control : Control}
    {expression destination : Atom} {sourceOlder : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination sourceOlder outcomes)
    {actualOlder : List Goal} {pSupp cSupp cSuppAfter : Finset String}
    {contSupports : List (Finset String)} {terminals : List Control}
    (sync : Evaluation.ExtraSynchronized source pSupp cSupp contSupports)
    (continuation : RootContinuationChain (Context := Context) program
      sourceOlder actualOlder (Evaluation.queuedOutcomes source pSupp)
      contSupports cSupp terminals cSuppAfter) :
    RootContinuationContract (Context := Context) program sourceOlder actualOlder
      control pSupp cSupp terminals cSuppAfter := by
  match source with
  | @Evaluation.variable _ control sourceName slotName sourceOlder after
      _private atGoal accepted =>
      have transition := direct_evaluation_transition (Context := Context) (program := program)
        (sourceOlder := sourceOlder) (actualOlder := actualOlder)
        atGoal rfl (.variableValue (program := program) sourceName)
        (fun _actual _related => .variableValue (program := program) sourceName) accepted
      exact direct_evaluation_contract transition.1 transition.2 continuation
  | @Evaluation.symbol _ control name destination sourceOlder after
      _private atGoal accepted =>
      have transition := direct_evaluation_transition (Context := Context) (program := program)
        (sourceOlder := sourceOlder) (actualOlder := actualOlder)
        atGoal rfl (.symbol (program := program) name)
        (fun _actual _related => .symbol (program := program) name) accepted
      exact direct_evaluation_contract transition.1 transition.2 continuation
  | @Evaluation.grounded _ control value destination sourceOlder after
      _private atGoal accepted =>
      have transition := direct_evaluation_transition (Context := Context) (program := program)
        (sourceOlder := sourceOlder) (actualOlder := actualOlder)
        atGoal rfl (.grounded (program := program) value)
        (fun _actual _related => .grounded (program := program) value) accepted
      exact direct_evaluation_contract transition.1 transition.2 continuation
  | @Evaluation.unit _ control destination sourceOlder after _private atGoal accepted =>
      have transition := direct_evaluation_transition (Context := Context) (program := program)
        (sourceOlder := sourceOlder) (actualOlder := actualOlder)
        atGoal rfl (.tuple (program := program) [] (by simp))
        (fun _actual _related => .tuple (program := program) [] (by simp)) accepted
      exact direct_evaluation_contract transition.1 transition.2 continuation
  | @Evaluation.constructor _ control opened head arguments destination sourceOlder outcomes
      passive _private atGoal prepared argumentsRun =>
      have syncParts : PreparedDelimitedRel prepared ∧
          Arguments.ExtraSynchronized argumentsRun pSupp cSupp contSupports := by
        simpa only [Evaluation.ExtraSynchronized] using sync
      have suffix := Arguments.drain (Context := Context) argumentsRun syncParts.2 continuation
      have ordinary : scopedForm (.expression (.symbol head :: arguments)) = false := by
        rcases passive.1 with ⟨_io,_known,excluded⟩
        simp only [scopedForm]
        split <;> simp_all
      have transition := DelimitedTransition.of_prepared (Context := Context)
        (actualOlder := actualOlder) atGoal ordinary prepared syncParts.1
      exact suffix.prepend transition.2 transition.1
  | @Evaluation.call _ control opened head arguments destination sourceOlder outcomes
      defined _private atGoal prepared argumentsRun =>
      have syncParts : PreparedDelimitedRel prepared ∧
          Arguments.ExtraSynchronized argumentsRun pSupp cSupp contSupports := by
        simpa only [Evaluation.ExtraSynchronized] using sync
      have suffix := Arguments.drain (Context := Context) argumentsRun syncParts.2 continuation
      have ordinary : scopedForm (.expression (.symbol head :: arguments)) = false := by
        rcases defined.1 with ⟨_io,_known,excluded⟩
        simp only [scopedForm]
        split <;> simp_all
      have transition := DelimitedTransition.of_prepared (Context := Context)
        (actualOlder := actualOlder) atGoal ordinary prepared syncParts.1
      exact suffix.prepend transition.2 transition.1
termination_by Evaluation.height source
decreasing_by all_goals simp [Evaluation.height]

theorem Arguments.drain {Context : Type} {program : Program} {control : Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {sourceOlder : List Goal} {outcomes : List Control}
    (source : Arguments program control rows assembled destination final sourceOlder outcomes)
    {actualOlder : List Goal} {pSupp cSupp cSuppAfter : Finset String}
    {contSupports : List (Finset String)} {terminals : List Control}
    (sync : Arguments.ExtraSynchronized source pSupp cSupp contSupports)
    (continuation : RootContinuationChain (Context := Context) program
      sourceOlder actualOlder (Arguments.queuedOutcomes source pSupp)
      contSupports cSupp terminals cSuppAfter) :
    RootContinuationContract (Context := Context) program sourceOlder actualOlder
      control pSupp cSupp terminals cSuppAfter := by
  match source with
  | .nil _atGoal continued =>
      exact Invocation.drain (Context := Context) continued
        (by simpa only [Arguments.ExtraSynchronized] using sync) continuation
  | @Arguments.cons _ control sourceAtom slot rows assembled destination final sourceOlder
      heads outcomes atGoal first branches =>
      have syncParts :
          Evaluation.ExtraSynchronized first pSupp cSupp
              (ArgumentBranches.headContSupports branches contSupports) ∧
            ArgumentBranches.ExtraSynchronized branches
              (Evaluation.queuedOutcomes first pSupp) cSupp contSupports := by
        simpa only [Arguments.ExtraSynchronized] using sync
      let headsQueued := Evaluation.queuedOutcomes first pSupp
      have headsAligned : headsQueued.map Prod.fst = heads :=
        Evaluation.queuedOutcomes_fst first pSupp
      have branchesContinuation : RootContinuationChain (Context := Context) program
          sourceOlder actualOlder
          (ArgumentBranches.queuedOutcomes branches headsQueued)
          contSupports cSupp terminals cSuppAfter := by
        simpa only [Arguments.queuedOutcomes,headsQueued] using continuation
      have headsOuter := ArgumentBranches.drain (Context := Context) branches headsQueued
        headsAligned syncParts.2 branchesContinuation
      intro supply world parents scope actual context origins pending related frontier root
        pendingEq collectedEq
      have readyQueued : ∀ item ∈ headsQueued,
          item.1.goals = evaluationGoals rows ++ final :: sourceOlder := by
        intro item member
        have rawMember : item.1 ∈ heads := by
          rw [← headsAligned]
          exact List.mem_map_of_mem member
        exact (first.outcomes_ready item.1 rawMember).1
      have headsChild := headsOuter.lift_argument related.older_atoms related.restores
        readyQueued
      have firstContract := Evaluation.drain (Context := Context) first syncParts.1 headsChild
      exact firstContract supply world parents scope actual context origins pending
        (related.enter_argument atGoal) frontier root pendingEq collectedEq
termination_by Arguments.height source
decreasing_by all_goals simp [Arguments.height]

theorem ArgumentBranches.drain {Context : Type} {program : Program}
    {heads : List Control} {rows : List (Atom × Atom)} {assembled destination : Atom}
    {final : Goal} {sourceOlder : List Goal} {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final sourceOlder outcomes)
    (headsQueued : List (Control × Finset String))
    (aligned : headsQueued.map Prod.fst = heads)
    {actualOlder : List Goal} {cSupp cSuppAfter : Finset String}
    {contSupports : List (Finset String)} {terminals : List Control}
    (sync : ArgumentBranches.ExtraSynchronized source headsQueued cSupp contSupports)
    (continuation : RootContinuationChain (Context := Context) program
      sourceOlder actualOlder (ArgumentBranches.queuedOutcomes source headsQueued)
      contSupports cSupp terminals cSuppAfter) :
    RootContinuationChain (Context := Context) program sourceOlder actualOlder
      headsQueued (ArgumentBranches.headContSupports source contSupports)
      cSupp terminals cSuppAfter := by
  match source with
  | .nil =>
      have headsQueuedNil : headsQueued = [] := by
        cases headsQueued with
        | nil => rfl
        | cons item rest => simp at aligned
      subst headsQueued
      have contSupportsNil : contSupports = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa only [ArgumentBranches.queuedOutcomes,List.length_nil] using continuation.1.symm
      subst contSupports
      simpa only [ArgumentBranches.queuedOutcomes,
        ArgumentBranches.headContSupports] using continuation
  | @ArgumentBranches.cons _ head heads rows assembled destination final sourceOlder
      children rest first remaining =>
      cases headsQueued with
      | nil => simp at aligned
      | cons queuedHead restQueued =>
          rcases queuedHead with ⟨actualHead,headPSupp⟩
          simp only [List.map_cons,List.cons.injEq] at aligned
          rcases aligned with ⟨headEq,restAligned⟩
          let firstCont := contSupports.take children.length
          let restCont := contSupports.drop children.length
          have contLength : contSupports.length = (children ++ rest).length := by
            have queuedLength := congrArg List.length
              (ArgumentBranches.queuedOutcomes_fst
                (.cons first remaining) ((actualHead,headPSupp) :: restQueued)
                (by simp only [List.map_cons,headEq,restAligned]))
            simp only [List.length_map] at queuedLength
            exact continuation.1.symm.trans queuedLength
          have contEq : firstCont ++ restCont = contSupports := by
            exact List.take_append_drop children.length contSupports
          have firstContLength : firstCont.length = children.length := by
            simp only [firstCont,List.length_take,List.length_append] at contLength ⊢
            omega
          have firstQueuedLength :
              (Arguments.queuedOutcomes first headPSupp).length = firstCont.length := by
            have firstLength := congrArg List.length
              (Arguments.queuedOutcomes_fst first headPSupp)
            simpa only [List.length_map,firstContLength] using firstLength
          have repacked : RootContinuationChain (Context := Context) program
              sourceOlder actualOlder
              (Arguments.queuedOutcomes first headPSupp ++
                ArgumentBranches.queuedOutcomes remaining restQueued)
              (firstCont ++ restCont) cSupp terminals cSuppAfter := by
            simpa only [ArgumentBranches.queuedOutcomes,contEq] using continuation
          obtain ⟨middle,firstTerminals,restTerminals,rfl,firstChain,restChain⟩ :=
            repacked.split_append firstQueuedLength
          have middleEq := firstChain.cSuppAfter_eq
          subst middle
          have syncParts :
              Arguments.ExtraSynchronized first headPSupp cSupp firstCont ∧
                ArgumentBranches.ExtraSynchronized remaining restQueued
                  (cSupp ∪ supportIncrement firstCont) restCont := by
            simpa only [ArgumentBranches.ExtraSynchronized,firstCont,restCont] using sync
          have firstContract := Arguments.drain (Context := Context) first syncParts.1 firstChain
          have restResult := ArgumentBranches.drain (Context := Context) remaining
            restQueued restAligned syncParts.2 restChain
          subst actualHead
          have headStep : RootContinuationStep (Context := Context) program
              sourceOlder actualOlder
              ((head,headPSupp),supportIncrement firstCont) cSupp firstTerminals
              (cSupp ∪ supportIncrement firstCont) := ⟨rfl,firstContract⟩
          refine ⟨?_,?_⟩
          · simpa only [ArgumentBranches.headContSupports,List.length_cons] using
              congrArg Nat.succ restResult.1
          · simpa only [ArgumentBranches.headContSupports,firstCont,restCont,
              zipSupportIncrements,List.zip_cons_cons,List.singleton_append] using
              (OrderedStateFlatMapRel.cons
                (step := RootContinuationStep (Context := Context) program
                  sourceOlder actualOlder) headStep restResult.2)
termination_by ArgumentBranches.height source
decreasing_by all_goals simp [ArgumentBranches.height]

theorem Invocation.drain {Context : Type} {program : Program} {control : Control}
    {assembled destination : Atom} {final : Goal} {sourceOlder : List Goal}
    {outcomes : List Control}
    (source : Invocation program control assembled destination final sourceOlder outcomes)
    {actualOlder : List Goal} {pSupp cSupp cSuppAfter : Finset String}
    {contSupports : List (Finset String)} {terminals : List Control}
    (sync : Invocation.ExtraSynchronized source pSupp cSupp contSupports)
    (continuation : RootContinuationChain (Context := Context) program
      sourceOlder actualOlder (Invocation.queuedOutcomes source pSupp)
      contSupports cSupp terminals cSuppAfter) :
    RootContinuationContract (Context := Context) program sourceOlder actualOlder
      control pSupp cSupp terminals cSuppAfter := by
  match source with
  | @Invocation.constructor _ control head arguments destination sourceOlder after
      _passive _private atGoal accepted =>
      have transition : DelimitedTransition (Context := Context) program
          sourceOlder actualOlder control
          {control with bindings := after,goals := sourceOlder} :=
        DelimitedTransition.accepted atGoal accepted
      have trace : BranchTrace program control []
          {control with bindings := after,goals := sourceOlder} :=
        .accepted atGoal accepted (.refl _)
      exact direct_evaluation_contract transition trace continuation
  | @Invocation.equations _ control extra head arguments destination sourceOlder
      environment selected outcomes defined _private atGoal resolved _supported coverage
      _nonempty bodies =>
      have syncParts :
          (protectControl control (control.support ∪ pSupp ∪ cSupp)).reserved =
              (protectControl control extra).reserved ∧
            Bodies.ExtraSynchronized bodies pSupp cSupp contSupports := by
        simpa only [Invocation.ExtraSynchronized] using sync
      have bodiesChain := Bodies.drain (Context := Context) bodies syncParts.2 continuation
      intro supply world parents scope actual context origins pending related frontier root
        pendingEq collectedEq
      have supportEq := related.collectionSupport_eq world parents scope context origins
        pending frontier root
      rw [pendingEq,collectedEq] at supportEq
      have synchronized :
          (protectControl actual (collectionSupport
            (⟨world,scope :: parents⟩ : CollectionConfiguration Context))).reserved =
            (protectControl control extra).reserved := by
        calc
          _ = (protectControl control
                (control.support ∪ pSupp ∪ cSupp)).reserved := by
              simp only [protectControl,related.reserved,supportEq]
          _ = _ := syncParts.1
      have ordinary : head ≠ "parse" := by
        intro same
        subst head
        have unknown := defined.1.2.1
        simp [Mettapedia.Languages.MeTTa.PeTTa.StdLib.known] at unknown
      have declared : program.equations.any (·.head == head) = true := by
        obtain ⟨equation,member,same⟩ := defined.2
        exact List.any_eq_true.mpr ⟨equation,member,by simp [same]⟩
      have equationPath := related.equations_step atGoal resolved ordinary
        defined.1.2.1 defined.1.1 declared coverage supply world parents scope context
        origins pending frontier synchronized
      let actualChoices := selected.map fun row =>
        (row.1,delimitedClauseChoice actual.cutBoundary related.restores actualOlder row.2)
      let enteredWork := selected.map
        (enteredEquationWork actual.cutBoundary related.restores actualOlder
          pending.length context origins)
      let enteredScope : CollectionScope Context :=
        { frontier := enteredWork ++ pending
          collected := scope.collected
          caller := scope.caller }
      have workRelated : QueuedWorkRel program sourceOlder actualOlder control origins pending
          (queuedSelections pSupp selected) enteredWork := by
        simpa only [pendingEq,enteredWork] using
          (Bodies.queuedWorkRel bodies related atGoal resolved coverage
            (fun _ member => member) origins pending context)
      obtain ⟨answers,answersRelated,supportAfter,afterPath⟩ :=
        bodiesChain.run_queue workRelated supply world parents enteredScope rfl
          (by simpa only [enteredScope] using root)
          (by
            change collectedSupport parents scope = cSupp
            exact collectedEq)
      refine ⟨answers,answersRelated,by simpa only [enteredScope] using supportAfter,?_⟩
      have beforePath : ScopedSourcePath .eagerValue program
          (supply,⟨world,scope :: parents⟩) []
          (supply,⟨world,enteredScope :: parents⟩) := by
        have sameWork :
            actualChoices.map (fun row =>
              (predicateEntry pending.length row.2,context,origins ++ [row.1])) =
              enteredWork := by
          dsimp only [actualChoices,enteredWork,enteredEquationWork]
          rw [List.map_map]
          apply List.map_congr_left
          intro row _member
          rcases row with ⟨position,selectedControl⟩
          rfl
        dsimp only at equationPath
        rw [sameWork] at equationPath
        simpa only [enteredScope] using equationPath.toScoped
      have joined := beforePath.trans afterPath
      simpa only [List.nil_append,enteredScope] using joined
termination_by Invocation.height source
decreasing_by all_goals simp [Invocation.height]

theorem Bodies.drain {Context : Type} {program : Program} {destination : Atom}
    {sourceOlder : List Goal} {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination sourceOlder selected outcomes)
    {actualOlder : List Goal} {pSupp cSupp cSuppAfter : Finset String}
    {contSupports : List (Finset String)} {terminals : List Control}
    (sync : Bodies.ExtraSynchronized source pSupp cSupp contSupports)
    (continuation : RootContinuationChain (Context := Context) program
      sourceOlder actualOlder (Bodies.queuedOutcomes source pSupp)
      contSupports cSupp terminals cSuppAfter) :
    RootContinuationChain (Context := Context) program sourceOlder actualOlder
      (queuedSelections pSupp selected) (Bodies.headContSupports source contSupports)
      cSupp terminals cSuppAfter := by
  match source with
  | .nil =>
      have contSupportsNil : contSupports = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa only [Bodies.queuedOutcomes,List.length_nil] using continuation.1.symm
      subst contSupports
      simpa only [Bodies.queuedOutcomes,queuedSelections,Bodies.headContSupports]
        using continuation
  | @Bodies.cons _ destination sourceOlder position selected remaining body children rest
      atGoal first later =>
      let pSuppHead := remaining.foldr (fun row names => row.2.support ∪ names) pSupp
      let firstCont := contSupports.take children.length
      let restCont := contSupports.drop children.length
      have contLength : contSupports.length = (children ++ rest).length := by
        have queuedLength := congrArg List.length (Bodies.queuedOutcomes_fst
          (.cons (position := position) atGoal first later) pSupp)
        simp only [List.length_map] at queuedLength
        exact continuation.1.symm.trans queuedLength
      have contEq : firstCont ++ restCont = contSupports :=
        List.take_append_drop children.length contSupports
      have firstContLength : firstCont.length = children.length := by
        simp only [firstCont,List.length_take,List.length_append] at contLength ⊢
        omega
      have firstQueuedLength :
          (Evaluation.queuedOutcomes first pSuppHead).length = firstCont.length := by
        have firstLength := Evaluation.queuedOutcomes_length first pSuppHead
        exact firstLength.trans firstContLength.symm
      have repacked : RootContinuationChain (Context := Context) program
          sourceOlder actualOlder
          (Evaluation.queuedOutcomes first pSuppHead ++ Bodies.queuedOutcomes later pSupp)
          (firstCont ++ restCont) cSupp terminals cSuppAfter := by
        simpa only [Bodies.queuedOutcomes,pSuppHead,contEq] using continuation
      obtain ⟨middle,firstTerminals,restTerminals,rfl,firstChain,restChain⟩ :=
        repacked.split_append firstQueuedLength
      have middleEq := firstChain.cSuppAfter_eq
      subst middle
      have syncParts :
          Evaluation.ExtraSynchronized first pSuppHead cSupp firstCont ∧
            Bodies.ExtraSynchronized later pSupp
              (cSupp ∪ supportIncrement firstCont) restCont := by
        simpa only [Bodies.ExtraSynchronized,pSuppHead,firstCont,restCont] using sync
      have firstContract := Evaluation.drain (Context := Context) first syncParts.1 firstChain
      have restResult := Bodies.drain (Context := Context) later syncParts.2 restChain
      have headStep : RootContinuationStep (Context := Context) program
          sourceOlder actualOlder
          ((selected,pSuppHead),supportIncrement firstCont) cSupp firstTerminals
          (cSupp ∪ supportIncrement firstCont) := ⟨rfl,firstContract⟩
      refine ⟨?_,?_⟩
      · simpa only [queuedSelections,Bodies.headContSupports,List.length_cons] using
          congrArg Nat.succ restResult.1
      · simpa only [queuedSelections,Bodies.headContSupports,pSuppHead,firstCont,restCont,
          zipSupportIncrements,List.zip_cons_cons,List.singleton_append] using
          (OrderedStateFlatMapRel.cons
            (step := RootContinuationStep (Context := Context) program
              sourceOlder actualOlder) headStep restResult.2)
termination_by Bodies.height source
decreasing_by all_goals simp [Bodies.height]
end

/-- A synchronized root source tree drains through the actual retained DFS
queue to the same ordered terminal occurrences. -/
theorem Evaluation.root_drain {Context : Type} {program : Program}
    {control : Control} {expression destination : Atom} {outcomes : List Control}
    (source : Evaluation program control expression destination [] outcomes)
    (pSupp cSupp : Finset String)
    (sync : Evaluation.ExtraSynchronized source pSupp cSupp
      (outcomes.map rawAnswerSupport)) :
    RootContinuationContract (Context := Context) program [] [] control pSupp cSupp
      outcomes (cSupp ∪ supportIncrement (outcomes.map rawAnswerSupport)) := by
  have terminalChain := root_terminal_chain (Context := Context) program outcomes
    (Evaluation.queuedOutcomes source pSupp) cSupp
    (Evaluation.queuedOutcomes_fst source pSupp) source.outcomes_ready
  exact Evaluation.drain source sync terminalChain

#print axioms Evaluation.traces
#print axioms Evaluation.outcomes_ready
#print axioms DelimitedControl.support_eq
#print axioms DelimitedControl.enter_argument
#print axioms drain_restoreCommits
#print axioms root_terminal_drain
#print axioms root_terminal_chain
#print axioms RootContinuationChain.run_queue
#print axioms Evaluation.drain
#print axioms Bodies.drain
#print axioms Evaluation.root_drain

end CollectionLinearization

mutual
/-- Local freshness for every destination allocated by a finite source tree.
The prefix and pending packet are the exact observations live at that node;
no future evaluator behavior occurs in this admission. -/
def Evaluation.Allocated {program : Program} {control : Control} {expression destination : Atom}
    {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control expression destination older outcomes)
    (sourcePrefix sourcePending : List Atom) : Prop :=
  match source with
  | .variable privateDestination _atGoal _accepted =>
      privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
        (sourcePrefix ++ expression :: sourcePending)
  | .symbol privateDestination _atGoal _accepted =>
      privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
        (sourcePrefix ++ expression :: sourcePending)
  | .grounded privateDestination _atGoal _accepted =>
      privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
        (sourcePrefix ++ expression :: sourcePending)
  | .unit privateDestination _atGoal _accepted =>
      privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
        (sourcePrefix ++ expression :: sourcePending)
  | @Evaluation.constructor _ _ _ head _ _ _ _ _ privateDestination _atGoal _prepared
      argumentsRun =>
      privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
          (sourcePrefix ++ expression :: sourcePending) ∧
        argumentsRun.Allocated sourcePrefix [.symbol head] sourcePending
  | @Evaluation.call _ _ _ head _ _ _ _ _ privateDestination _atGoal _prepared
      argumentsRun =>
      privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
          (sourcePrefix ++ expression :: sourcePending) ∧
        argumentsRun.Allocated sourcePrefix [.symbol head] sourcePending

def Arguments.Allocated {program : Program} {control : Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal} {older : List Goal}
    {outcomes : List Control}
    (source : Arguments program control rows assembled destination final older outcomes)
    (sourcePrefix sourceEvaluated sourcePending : List Atom) : Prop :=
  match source with
  | .nil _atGoal continued => continued.Allocated sourcePrefix sourcePending
  | @Arguments.cons _ _ source slot rows _ _ _ _ _ _ _atGoal first branches =>
      first.Allocated (sourcePrefix ++ sourceEvaluated) (rows.map Prod.fst ++ sourcePending) ∧
        branches.Allocated sourcePrefix (sourceEvaluated ++ [slot]) sourcePending

def ArgumentBranches.Allocated {program : Program} {heads : List Control}
    {rows : List (Atom × Atom)} {assembled destination : Atom} {final : Goal}
    {older : List Goal}
    {outcomes : List Control}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes)
    (sourcePrefix sourceEvaluated sourcePending : List Atom) : Prop :=
  match source with
  | .nil => True
  | .cons first remaining =>
      first.Allocated sourcePrefix sourceEvaluated sourcePending ∧
        remaining.Allocated sourcePrefix sourceEvaluated sourcePending

def Invocation.Allocated {program : Program} {control : Control} {assembled destination : Atom}
    {final : Goal}
    {older : List Goal} {outcomes : List Control}
    (source : Invocation program control assembled destination final older outcomes)
    (sourcePrefix sourcePending : List Atom) : Prop :=
  match source with
  | .constructor _passive privateDestination _atGoal _accepted =>
      privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
        (sourcePrefix ++ assembled :: sourcePending)
  | .equations _defined privateDestination _atGoal _resolved _resolvedSupported _frontier
      _nonempty bodies =>
      privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
          (sourcePrefix ++ assembled :: sourcePending) ∧
        bodies.Allocated sourcePrefix sourcePending

def Bodies.Allocated {program : Program} {destination : Atom} {older : List Goal}
    {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes)
    (sourcePrefix sourcePending : List Atom) : Prop :=
  match source with
  | .nil => True
  | .cons _atGoal first later =>
      first.Allocated sourcePrefix sourcePending ∧ later.Allocated sourcePrefix sourcePending
end

end Mettapedia.Languages.MeTTa.Translation.OpenRecursive



namespace Mettapedia.Languages.MeTTa.Translation.OpenRecursive

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
open Mettapedia.Languages.MeTTa.Translation.PureConstructor
open Mettapedia.Languages.MeTTa.Translation.PureConstructor.RecursiveTransport
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (Program)
open Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
open Mettapedia.Languages.MeTTa.Translation.ConstructorMatch

/-- An admitted source term together with one passive materialization of its
free variables.  The materializer is explicit so a later frame can compose
with it; no equality between old and new variable representatives is needed. -/
def InputInstance (program : Program) (scope : List String)
    (source : Atom) (input : Entry.Value) : Prop :=
  ∃ materializer : String → Entry.Value,
    CodeRel program scope (Entry.Value.ofAtom source) ∧
    (∀ name ∈ scope,
      Value program (materializer name).erase scope ∧ NoErrorSymbol (materializer name).erase) ∧
    input = Entry.Value.substitute .preserve materializer (Entry.Value.ofAtom source)

private theorem substitute_congr_of_typeVars
    (policy : Entry.RebuildPolicy) (first second : String → Entry.Value)
    (value : Entry.Value)
    (same : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars value.erase,
      first name = second name) :
    Entry.Value.substitute policy first value = Entry.Value.substitute policy second value := by
  induction value using Entry.Value.rec
      (motive_2 := fun values =>
        (∀ value ∈ values, ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars value.erase,
          first name = second name) →
        values.map (Entry.Value.substitute policy first) =
          values.map (Entry.Value.substitute policy second)) with
  | symbol => simp only [Entry.Value.substitute]
  | grounded => simp only [Entry.Value.substitute]
  | var name =>
      simp only [Entry.Value.substitute]
      apply same
      simp [Entry.Value.erase,HE.Spec.Type.Presentation.TypeSubst.typeVars]
  | expression previous children ih =>
      have childrenSame := ih (fun child member name used => same name (by
        simpa only [Entry.Value.erase,HE.Spec.Type.Presentation.TypeSubst.typeVars] using
          (HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
            (List.mem_map.mpr ⟨child,member,rfl⟩) name used)))
      cases policy <;>
        simp [Entry.Value.substitute,childrenSame,Entry.Value.rebuildStatus]
  | nil _ => rfl
  | cons head tail firstProof restProof allSame =>
      exact congrArg₂ List.cons (firstProof (allSame head List.mem_cons_self))
        (restProof (fun value member => allSame value (List.mem_cons_of_mem _ member)))

theorem InputInstance.raw {program : Program} {scope : List String} {source : Atom}
    (code : CodeRel program scope (Entry.Value.ofAtom source)) :
    InputInstance program scope source (Entry.Value.ofAtom source) := by
  refine ⟨Entry.Value.var,code,?_,?_⟩
  · intro name member
    exact ⟨by simpa only [Entry.Value.erase] using
      (Value.variable (program := program) member),
      by simpa only [Entry.Value.erase] using NoErrorSymbol.variable name⟩
  · exact (Entry.Value.substitute_identity .preserve _).symm

theorem InputInstance.weaken {program : Program} {scope targetScope : List String}
    {source : Atom} {input : Entry.Value}
    (sourceInstance : InputInstance program scope source input)
    (included : ∀ name ∈ scope, name ∈ targetScope) :
    InputInstance program targetScope source input := by
  obtain ⟨oldMaterializer,code,oldPassive,inputEq⟩ := sourceInstance
  let materializer : String → Entry.Value := fun name =>
    if name ∈ scope then oldMaterializer name else .var name
  refine ⟨materializer,code.weaken included,?_,?_⟩
  · intro name member
    by_cases old : name ∈ scope
    · simpa only [materializer,if_pos old] using
        And.intro ((oldPassive name old).1.weaken included) (oldPassive name old).2
    · simp only [materializer,if_neg old,Entry.Value.erase]
      exact ⟨Value.variable member,NoErrorSymbol.variable name⟩
  · rw [inputEq]
    apply substitute_congr_of_typeVars
    intro name used
    have old : name ∈ scope := code.vars_covered name (by
      simpa only [Entry.Value.erase_ofAtom] using used)
    simp only [materializer,if_pos old]

theorem inputInstances_weaken
    {program : Program} {scope targetScope : List String}
    {sources : List Atom} {inputs : List Entry.Value}
    (instances : List.Forall₂ (InputInstance program scope) sources inputs)
    (included : ∀ name ∈ scope, name ∈ targetScope) :
    List.Forall₂ (InputInstance program targetScope) sources inputs := by
  induction instances with
  | nil => exact .nil
  | cons one _rest ih => exact .cons (one.weaken included) ih

/-- Reading an already materialized term in a later passive frame is
composition of passive materializers under the stable-data rebuild policy. -/
theorem InputInstance.read {program : Program} {scope : List String}
    {source : Atom} {input : Entry.Value}
    (sourceInstance : InputInstance program scope source input)
    (frame : Frame) (passive : PassiveEnvironment program scope frame.environment) :
    InputInstance program scope source
      (frame.read HE.Spec.Eval.Completed.Policy.unmarked input) := by
  obtain ⟨oldMaterializer,code,oldPassive,inputEq⟩ := sourceInstance
  let materializer := Entry.Value.compose .preserve oldMaterializer
    (Entry.Value.resolve frame.environment)
  refine ⟨materializer,code,?_,?_⟩
  · intro name member
    exact passive.substitute .preserve (oldMaterializer name)
      (oldPassive name member).1 (oldPassive name member).2
  · rw [Frame.read,inputEq]
    change Entry.Value.substitute .preserve (Entry.Value.resolve frame.environment)
        (Entry.Value.substitute .preserve oldMaterializer (Entry.Value.ofAtom source)) = _
    rw [Entry.Value.preserve_compose]

/-- Reading admitted raw code through a passive frame is its explicit passive
materialization instance. -/
theorem InputInstance.of_read {program : Program} {scope : List String}
    {source : Atom} (code : CodeRel program scope (Entry.Value.ofAtom source))
    (frame : Frame) (passive : PassiveEnvironment program scope frame.environment) :
    InputInstance program scope source
      (frame.read HE.Spec.Eval.Completed.Policy.unmarked (Entry.Value.ofAtom source)) := by
  refine ⟨Entry.Value.resolve frame.environment,code,?_,rfl⟩
  intro name member
  exact ⟨passive.resolve.1 name member,passive.resolve.2 name⟩

theorem InputInstance.value_of_source_variable {program : Program} {scope : List String}
    {sourceName : String} {input : Entry.Value}
    (sourceInstance : InputInstance program scope (.var sourceName) input) :
    Value program input.erase scope ∧ NoErrorSymbol input.erase := by
  obtain ⟨materializer,code,passive,inputEq⟩ := sourceInstance
  have member : sourceName ∈ scope := by
    apply code.vars_covered sourceName
    simp [Entry.Value.erase_ofAtom,HE.Spec.Type.Presentation.TypeSubst.typeVars]
  rw [inputEq]
  simpa [Entry.Value.ofAtom,Entry.Value.substitute,Entry.Value.erase] using
    passive sourceName member

theorem InputInstance.code_input {program : Program} {scope : List String}
    {source : Atom} {input : Entry.Value}
    (sourceInstance : InputInstance program scope source input) : CodeRel program scope input := by
  obtain ⟨materializer,code,passive,inputEq⟩ := sourceInstance
  rw [inputEq]
  exact code.substitute .preserve materializer passive

theorem InputInstance.source_data {program : Program} {scope : List String}
    {source : Atom} {input : Entry.Value}
    (sourceInstance : InputInstance program scope source input)
    (notActive : ∀ head arguments,
      Entry.Value.ofAtom source ≠ .expression .active (.symbol head :: arguments)) :
    Value program source scope ∧ NoErrorSymbol source := by
  obtain ⟨_materializer,code,_passive,_inputEq⟩ := sourceInstance
  generalize equality : Entry.Value.ofAtom source = value at code
  cases code with
  | @«variable» variableName member =>
      have sourceEq : source = .var variableName := by
        simpa only [Entry.Value.erase_ofAtom,Entry.Value.erase] using congrArg Entry.Value.erase equality
      subst source
      exact ⟨Value.variable member,NoErrorSymbol.variable variableName⟩
  | data valid safe =>
      rw [← equality,Entry.Value.erase_ofAtom] at valid safe
      exact ⟨valid,safe⟩
  | active ordinary each => exact (notActive _ _ equality).elim

theorem CodeRel.not_refusal {program : Program} {scope : List String}
    {value : Entry.Value} (code : CodeRel program scope value) :
    value.erase ≠ Atom.notReducible := by
  cases code with
  | «variable» => simp [Entry.Value.erase,Atom.notReducible]
  | data valid _safe => exact valid.not_refusal
  | active ordinary each =>
      simp [Entry.Value.erase,Atom.notReducible]

theorem CodeRel.not_stopped {program : Program} {scope : List String}
    {value : Entry.Value} (code : CodeRel program scope value) :
    ¬HE.Spec.Eval.IsEmptyOrErrorRel value.erase := by
  cases code with
  | «variable» => simp [Entry.Value.erase,HE.Spec.Eval.IsEmptyOrErrorRel,
      HE.Spec.Eval.IsErrorRel,Atom.empty]
  | data valid _safe => exact valid.not_stopped
  | @active head arguments ordinary each =>
      have clean : head ≠ "Error" := fun same => ordinary.2.2 (by simp [same])
      simp [Entry.Value.erase,HE.Spec.Eval.IsEmptyOrErrorRel,
        HE.Spec.Eval.IsErrorRel,Atom.empty,clean]

theorem CodeRel.not_function_pending {program : Program} {scope : List String}
    {value : Entry.Value} (code : CodeRel program scope value)
    (policy : HE.Spec.Eval.Completed.Policy) :
    ¬HE.Spec.Eval.Completed.FunctionPending policy value := by
  cases code with
  | @«variable» name member =>
      have valid : Value program (Entry.Value.var name).erase scope := by
        simpa only [Entry.Value.erase] using (Value.variable (program := program) member)
      exact valid.not_function_pending policy
  | data valid _safe => exact valid.not_function_pending policy
  | @active head arguments ordinary each =>
      rintro ⟨⟨body,shape⟩,_ready⟩
      simp only [Entry.Value.erase,List.map_cons] at shape
      have headEq : head = "function" := Atom.symbol.inj (List.cons.inj
        (Atom.expression.inj shape)).1
      exact ordinary.2.2 (by simp [headEq])

/-- Passive source syntax remains passive after the explicit materializer is
applied.  This is the leaf case used by symbols, scalars, units and constructor
data; executable applications are handled by the recursive cases. -/
theorem InputInstance.passive {program : Program} {scope : List String}
    {source : Atom} {input : Entry.Value}
    (sourceInstance : InputInstance program scope source input)
    (valid : Value program source scope) (safe : NoErrorSymbol source) :
    Value program input.erase scope ∧ NoErrorSymbol input.erase := by
  obtain ⟨materializer,_code,materializes,inputEq⟩ := sourceInstance
  rw [inputEq,Entry.Value.erase_substitute,Entry.Value.erase_ofAtom]
  have covered : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars source,
      name ∈ scope := by
    intro name member
    exact valid.variables name ((HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr member)
  exact ⟨valid.substitute _ (fun name member => (materializes name member).1),
    safe.substitute _ (fun name member => (materializes name (covered name member)).2)⟩

/-- A materialized fixed-head source application retains that literal head;
its children are materialized by the same passive environment. -/
theorem InputInstance.application {program : Program} {scope : List String}
    {head : String} {arguments : List Atom} {input : Entry.Value}
    (sourceInstance : InputInstance program scope
      (.expression (.symbol head :: arguments)) input) :
    ∃ children,
      input = .expression .active (.symbol head :: children) ∧
      List.Forall₂ (InputInstance program scope) arguments children := by
  obtain ⟨materializer,code,passive,inputEq⟩ := sourceInstance
  let materialize : Atom → Entry.Value := fun atom =>
    Entry.Value.substitute .preserve materializer (Entry.Value.ofAtom atom)
  have childCode : ∀ argument ∈ arguments,
      CodeRel program scope (Entry.Value.ofAtom argument) := by
    intro argument member
    have parent : CodeRel program scope
        (.expression .active (.symbol head :: arguments.map Entry.Value.ofAtom)) := by
      simpa only [Entry.Value.ofAtom,List.map_cons] using code
    apply parent.children
    simpa only [Entry.Value.ofAtom,List.map_cons] using
      (List.mem_cons_of_mem (Entry.Value.symbol head) (List.mem_map_of_mem member))
  have paired : List.Forall₂ (InputInstance program scope) arguments
      (arguments.map materialize) := by
    suffices ∀ items : List Atom,
        (∀ argument ∈ items, CodeRel program scope (Entry.Value.ofAtom argument)) →
        List.Forall₂ (InputInstance program scope) items (items.map materialize) by
      exact this arguments childCode
    intro items
    induction items with
    | nil => intro _; exact .nil
    | cons argument rest ih =>
        intro each
        exact .cons ⟨materializer,each argument List.mem_cons_self,passive,rfl⟩
          (ih (fun child member => each child (List.mem_cons_of_mem _ member)))
  refine ⟨arguments.map materialize,?_,paired⟩
  rw [inputEq]
  simp [materialize,Entry.Value.ofAtom,Entry.Value.substitute,Entry.Value.rebuildStatus]

/-- The cross-language names needed by the next recursive cut already belong
to the source store component which survives reduction of the current goal. -/
structure SupportRel (scope : List String) (live : List Atom) (incoming : HE.Bindings)
    (hePacket sourcePacket : List Atom) (control : Control) : Prop where
  scope : ∀ name ∈ scope, name ∈ PersistentSupport control
  live : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList live,
    name ∈ PersistentSupport control
  incoming : ∀ name ∈ HE.Spec.Bindings.ScopeObservation.specBindingVars incoming,
    name ∈ PersistentSupport control
  hePacket : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList hePacket,
    name ∈ PersistentSupport control
  sourcePacket : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList sourcePacket,
    name ∈ PersistentSupport control

theorem SupportRel.mono
    {scope : List String} {live : List Atom} {incoming : HE.Bindings}
    {hePacket sourcePacket : List Atom} {before after : Control}
    (supported : SupportRel scope live incoming hePacket sourcePacket before)
    (monotone : PersistentSupport before ⊆ PersistentSupport after) :
    SupportRel scope live incoming hePacket sourcePacket after :=
  ⟨fun name member => monotone (supported.scope name member),
   fun name member => monotone (supported.live name member),
   fun name member => monotone (supported.incoming name member),
   fun name member => monotone (supported.hePacket name member),
   fun name member => monotone (supported.sourcePacket name member)⟩

theorem Value.typeVars_mem_scope
    {program : Program} {scope : List String} {atom : Atom}
    (valid : Value program atom scope) {name : String}
    (member : name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars atom) :
    name ∈ scope :=
  valid.variables name ((HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars atom name).mpr member)

theorem SupportRel.of_prepared
    {scope : List String} {live : List Atom} {incoming : HE.Bindings}
    {hePacket sourcePacket : List Atom} {control opened : Control}
    {policy : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Policy}
    {program : Program} {destination : Atom} {older : List Goal} {expression : Atom}
    (supported : SupportRel scope live incoming hePacket sourcePacket control)
    (prepared : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source.Prepared
      policy program control destination older expression opened) :
    SupportRel scope live incoming hePacket sourcePacket opened := by
  have same := Mettapedia.Languages.MeTTa.Translation.OpenRecursive.Prepared.persistentSupport_eq
    prepared
  refine ⟨?_,?_,?_,?_,?_⟩ <;> intro name member <;> rw [same]
  · exact supported.scope name member
  · exact supported.live name member
  · exact supported.incoming name member
  · exact supported.hePacket name member
  · exact supported.sourcePacket name member

/-- Replacing one expression coordinate by its child vector does not change
the finite support required by the comparison. -/
theorem SupportRel.decompose
    {scope : List String} {live : List Atom} {incoming : HE.Bindings}
    {heFront heChildren hePending sourceFront sourceChildren sourcePending : List Atom}
    {control : Control}
    (supported : SupportRel scope live incoming
      (heFront ++ .expression heChildren :: hePending)
      (sourceFront ++ .expression sourceChildren :: sourcePending) control) :
    SupportRel scope live incoming
      (heFront ++ heChildren ++ hePending)
      (sourceFront ++ sourceChildren ++ sourcePending) control := by
  refine ⟨supported.scope,supported.live,supported.incoming,?_,?_⟩
  · intro name member
    apply supported.hePacket
    simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      HE.Spec.Type.Presentation.TypeSubst.typeVars,List.mem_append,List.mem_cons,
      List.append_assoc] using member
  · intro name member
    apply supported.sourcePacket
    simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      HE.Spec.Type.Presentation.TypeSubst.typeVars,List.mem_append,List.mem_cons,
      List.append_assoc] using member

theorem SupportRel.assemble
    {scope : List String} {live : List Atom} {incoming : HE.Bindings}
    {heFront heChildren hePending sourceFront sourceChildren sourcePending : List Atom}
    {control : Control}
    (supported : SupportRel scope live incoming
      (heFront ++ heChildren ++ hePending)
      (sourceFront ++ sourceChildren ++ sourcePending) control) :
    SupportRel scope live incoming
      (heFront ++ .expression heChildren :: hePending)
      (sourceFront ++ .expression sourceChildren :: sourcePending) control := by
  refine ⟨supported.scope,supported.live,supported.incoming,?_,?_⟩
  · intro name member
    apply supported.hePacket
    simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      HE.Spec.Type.Presentation.TypeSubst.typeVars,List.mem_append,List.mem_cons,
      List.append_assoc] using member
  · intro name member
    apply supported.sourcePacket
    simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      HE.Spec.Type.Presentation.TypeSubst.typeVars,List.mem_append,List.mem_cons,
      List.append_assoc] using member

theorem SupportRel.readCoordinate
    {program : Program} {scope : List String} {live : List Atom} {incoming : HE.Bindings}
    {heFront hePending sourcePacket : List Atom} {control : Control}
    {frame : Frame} {input : Entry.Value}
    (supported : SupportRel scope live incoming
      (heFront ++ input.erase :: hePending) sourcePacket control)
    (code : CodeRel program scope
      (frame.read HE.Spec.Eval.Completed.Policy.unmarked input)) :
    SupportRel scope live incoming
      (heFront ++ (frame.read HE.Spec.Eval.Completed.Policy.unmarked input).erase :: hePending)
      sourcePacket control := by
  refine ⟨supported.scope,supported.live,supported.incoming,?_,supported.sourcePacket⟩
  intro name member
  simp only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
    HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append] at member
  rcases member with frontMember | tailMember
  · apply supported.hePacket
    simp only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append]
    exact Or.inl frontMember
  · rcases tailMember with valueMember | pendingMember
    · exact supported.scope name (code.vars_covered name valueMember)
    · apply supported.hePacket
      simp only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
        HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append]
      exact Or.inr (Or.inr pendingMember)

theorem SupportRel.unfocus
    {scope : List String} {live : List Atom} {incoming : HE.Bindings}
    {heFront sourceFront : List Atom} {query sourceQuery : Atom}
    {hePending sourcePending : List Atom} {control : Control}
    (supported : SupportRel scope live incoming
      (query :: heFront ++ hePending) (sourceQuery :: sourceFront ++ sourcePending) control) :
    SupportRel scope live incoming
      (heFront ++ query :: hePending) (sourceFront ++ sourceQuery :: sourcePending) control := by
  refine ⟨supported.scope,supported.live,supported.incoming,?_,?_⟩
  · intro name member
    apply supported.hePacket
    simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append,
      or_comm,or_left_comm,or_assoc] using member
  · intro name member
    apply supported.sourcePacket
    simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append,
      or_comm,or_left_comm,or_assoc] using member

/-- One completed occurrence retains a single joint model for its evaluated
prefix, returned value and caller packet.  It also carries only the persistent
support needed to enter the next sibling or recursive clause. -/
def OutcomeRel (program : Program) (scope : List String)
    (hePrefix sourcePrefix hePending sourcePending : List Atom) (destination : Atom)
    (older : List Goal) (before : Control)
    (result : HE.Spec.Eval.Completed.Result) (source : Control) : Prop :=
  ∃ outScope : List String,
    (∀ name ∈ scope, name ∈ outScope) ∧
    source.goals = older ∧
    PersistentSupport before ⊆ PersistentSupport source ∧
    (∀ name ∈ outScope, name ∈ PersistentSupport source) ∧
    (∀ name ∈ HE.Spec.Bindings.ScopeObservation.specBindingVars result.2.bindings,
      name ∈ PersistentSupport source) ∧
    (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars destination,
      name ∈ PersistentSupport source) ∧
    Value program result.1.erase outScope ∧
    NoErrorSymbol result.1.erase ∧
    PassiveEnvironment program outScope result.2.environment ∧
    HE.Spec.Bindings.ScopeObservation.observedTuples result.2.bindings
      (hePrefix ++ result.1.erase :: hePending) =
    solutionTuples source.bindings (sourcePrefix ++ destination :: sourcePending)

private theorem observed_read_coordinate
    (policy : HE.Spec.Eval.Completed.Policy) (frame : Frame)
    (front pending : List Atom) (value : Entry.Value) :
    HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (front ++ (frame.read policy value).erase :: pending) =
      HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (front ++ value.erase :: pending) := by
  apply HE.Spec.Bindings.ScopeObservation.observedTuples_congr_models
  intro model satisfied
  have same : HE.Spec.Type.RuntimeRefinement.applyTypeValuation model
      (frame.read policy value).erase =
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation model value.erase := by
    rw [Frame.read,Entry.Value.erase_substitute_environment]
    exact frame.certified.preserves_model model satisfied value.erase
  simp only [List.map_append,List.map_cons,same]

theorem OutcomeRel.weaken
    {program : Program} {scope targetScope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom} {destination : Atom}
    {older : List Goal} {before : Control}
    {result : HE.Spec.Eval.Completed.Result} {source : Control}
    (related : OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending
      destination older before result source)
    (included : ∀ name ∈ targetScope, name ∈ scope) :
    OutcomeRel program targetScope hePrefix sourcePrefix hePending sourcePending
      destination older before result source := by
  obtain ⟨outScope,scopeOut,goals,monotone,scopeSupported,bindingsSupported,
    destinationSupported,valid,safe,passive,packet⟩ := related
  exact ⟨outScope,fun name member => scopeOut name (included name member),goals,monotone,
    scopeSupported,bindingsSupported,destinationSupported,valid,safe,passive,packet⟩

/-- Final result materialization changes representatives but preserves the
joint packet and the reached frame. -/
theorem OutcomeRel.readResult
    {program : Program} {scope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom} {destination : Atom}
    {older : List Goal} {before : Control}
    {result : HE.Spec.Eval.Completed.Result} {source : Control}
    (related : OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending
      destination older before result source) :
    OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending destination older before
      (HE.Spec.Eval.Completed.readResult HE.Spec.Eval.Completed.Policy.unmarked result) source := by
  obtain ⟨outScope,scopeOut,goals,monotone,scopeSupported,bindingsSupported,
    destinationSupported,valid,safe,passive,packet⟩ := related
  refine ⟨outScope,scopeOut,goals,monotone,scopeSupported,bindingsSupported,
    destinationSupported,?_,?_,passive,?_⟩
  · exact (passive.substitute .preserve result.1 valid safe).1
  · exact (passive.substitute .preserve result.1 valid safe).2
  · exact (observed_read_coordinate HE.Spec.Eval.Completed.Policy.unmarked
      result.2 hePrefix hePending result.1).trans packet

/-- Publication under the unmarked profile changes only readiness metadata,
which is outside the joint erased observation. -/
theorem OutcomeRel.publishResult
    {program : Program} {scope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom} {destination original : Atom}
    {older : List Goal} {before : Control}
    {result : HE.Spec.Eval.Completed.Result} {source : Control}
    (related : OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending
      destination older before result source) :
    OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending destination older before
      (HE.Spec.Eval.Completed.publishResult HE.Spec.Eval.Completed.Policy.unmarked original result)
      source := by
  obtain ⟨outScope,scopeOut,goals,monotone,scopeSupported,bindingsSupported,
    destinationSupported,valid,safe,passive,packet⟩ := related
  refine ⟨outScope,scopeOut,goals,monotone,scopeSupported,bindingsSupported,
    destinationSupported,?_,?_,passive,?_⟩
  · simpa only [HE.Spec.Eval.Completed.publishResult_erase] using valid
  · simpa only [HE.Spec.Eval.Completed.publishResult_erase] using safe
  · simpa [HE.Spec.Eval.Completed.publishResult,
      HE.Spec.Eval.Completed.publishResult_erase] using packet

/-- Sequential child completion composes growing passive scopes and persistent
source support without changing the final packet. -/
theorem OutcomeRel.rebase
    {program : Program} {scope middleScope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom}
    {destination : Atom} {older : List Goal} {before middle : Control}
    {result : HE.Spec.Eval.Completed.Result} {source : Control}
    (scopeIncluded : ∀ name ∈ scope, name ∈ middleScope)
    (firstMonotone : PersistentSupport before ⊆ PersistentSupport middle)
    (related : OutcomeRel program middleScope hePrefix sourcePrefix hePending sourcePending
      destination older middle result source) :
    OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending
      destination older before result source := by
  obtain ⟨outScope,middleIncluded,goals,secondMonotone,scopeSupported,
    bindingsSupported,destinationSupported,valid,safe,passive,packet⟩ := related
  exact ⟨outScope,fun name member => middleIncluded name (scopeIncluded name member),goals,
    fun name member => secondMonotone (firstMonotone member),scopeSupported,
    bindingsSupported,destinationSupported,valid,safe,passive,packet⟩

theorem outcomes_rebase
    {program : Program} {scope middleScope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom}
    {destination : Atom} {older : List Goal} {before middle : Control}
    {results : List HE.Spec.Eval.Completed.Result} {sources : List Control}
    (scopeIncluded : ∀ name ∈ scope, name ∈ middleScope)
    (monotone : PersistentSupport before ⊆ PersistentSupport middle)
    (related : List.Forall₂ (OutcomeRel program middleScope hePrefix sourcePrefix
      hePending sourcePending destination older middle) results sources) :
    List.Forall₂ (OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending
      destination older before) results sources := by
  induction related with
  | nil => exact .nil
  | cons one _rest ih => exact .cons (one.rebase scopeIncluded monotone) ih

theorem outcomes_not_stopped
    {program : Program} {scope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom}
    {destination : Atom} {older : List Goal} {before : Control}
    {results : List HE.Spec.Eval.Completed.Result} {sources : List Control}
    (related : List.Forall₂ (OutcomeRel program scope hePrefix sourcePrefix
      hePending sourcePending destination older before) results sources) :
    ∀ result ∈ results, ¬HE.Spec.Eval.IsEmptyOrErrorRel result.1.erase := by
  induction related with
  | nil => simp
  | @cons result source results sources one _rest inductionHypothesis =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨_outScope,_included,_goals,_monotone,_scopeSupported,
          _bindingsSupported,_destinationSupported,valid,_safe,_passive,_packet⟩ := one
        exact valid.not_stopped
      · exact inductionHypothesis candidate member

theorem typeVarsList_cons_supported
    {support : String → Prop} {value : Atom} {tail : List Atom}
    (valueSupported : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars value, support name)
    (tailSupported : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList tail, support name) :
    ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList (value :: tail), support name := by
  intro name member
  rcases List.mem_append.mp member with valueMember | tailMember
  · exact valueSupported name valueMember
  · exact tailSupported name tailMember

theorem typeVarsList_insert_supported
    {support : String → Prop} {front suffix : List Atom} {value : Atom}
    (oldSupported : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (front ++ suffix), support name)
    (valueSupported : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars value,
      support name) :
    ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      ((front ++ [value]) ++ suffix), support name := by
  intro name member
  rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
    HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append] at member
  rcases List.mem_append.mp member with frontOrValue | suffixMember
  · rcases List.mem_append.mp frontOrValue with frontMember | valueMember
    · apply oldSupported
      rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append]
      exact List.mem_append_left _ frontMember
    · apply valueSupported name
      simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.append_nil] using valueMember
  · apply oldSupported
    rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append]
    exact List.mem_append_right _ suffixMember

theorem typeVarsList_remove_supported
    {support : String → Prop} {front suffix : List Atom} {value : Atom}
    (oldSupported : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (front ++ value :: suffix), support name) :
    ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (front ++ suffix), support name := by
  intro name member
  rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append] at member
  rcases List.mem_append.mp member with frontMember | suffixMember
  · apply oldSupported
    rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append]
    exact List.mem_append_left _ frontMember
  · apply oldSupported
    rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append]
    exact List.mem_append_right _ (List.mem_append_right _ suffixMember)

theorem assemblePrefix_empty_open {program : Program} {scope : List String}
    (values : List Entry.Value)
    (safe : ∀ value ∈ values, Value program value.erase scope ∧ NoErrorSymbol value.erase)
    (frame : Frame) :
    assemblePrefix values (.expression .active [],frame) = (.expression .active values,frame) := by
  induction values with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have later := inductionHypothesis (fun value member => safe value (List.mem_cons_of_mem _ member))
      change tuplePrepend first (assemblePrefix rest (.expression .active [],frame)) = _
      rw [later]
      have clean : HE.isEmptyOrError (Entry.Value.expression .active rest).erase = false := by
        have safeAtoms : ∀ atom ∈ rest.map Entry.Value.erase, NoErrorSymbol atom := by
          intro atom member
          obtain ⟨value,present,rfl⟩ := List.mem_map.mp member
          exact (safe value (List.mem_cons_of_mem _ present)).2
        simpa only [Entry.Value.erase] using NoErrorSymbol.tuple_clean safeAtoms
      simp only [tuplePrepend,clean,Bool.false_eq_true,↓reduceIte]

/-- Expanding one expression coordinate back into its children preserves the
same joint model.  Both the already evaluated prefix and the child vector may
use different private names, so their lengths are recorded independently. -/
theorem joint_packet_decompose
    {incoming : HE.Bindings} {before : Equations}
    {heFront heChildren hePending sourceFront sourceChildren sourcePending : List Atom}
    (frontLength : heFront.length = sourceFront.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (heFront ++ .expression heChildren :: hePending) =
      solutionTuples before (sourceFront ++ .expression sourceChildren :: sourcePending)) :
    HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (heFront ++ heChildren ++ hePending) =
      solutionTuples before (sourceFront ++ sourceChildren ++ sourcePending) := by
  have expressionRead (environment : Environment) (atoms : List Atom) :
      read environment (.expression atoms) = .expression (atoms.map (read environment)) := by
    simp only [read_eq_applyTypeValuation,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
    exact congrArg Atom.expression (List.map_congr_left fun atom _ =>
      (read_eq_applyTypeValuation environment atom).symm)
  ext values
  constructor
  · rintro ⟨valuation,model,returned⟩
    have assembled : (heFront ++ .expression heChildren :: hePending).map
        (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) ∈
        solutionTuples before (sourceFront ++ .expression sourceChildren :: sourcePending) := by
      rw [← related]
      exact ⟨valuation,model,rfl⟩
    obtain ⟨environment,solved,same⟩ := assembled
    simp only [List.map_append,List.map_cons,expressionRead,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at same
    obtain ⟨frontSame,restSame⟩ := List.append_inj same (by
      simpa only [List.length_map] using frontLength.symm)
    have expressionSame := (List.cons.inj restSame).1
    have childrenSame : heChildren.map
        (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) =
        sourceChildren.map (read environment) := Atom.expression.inj expressionSame.symm
    have pendingSame := (List.cons.inj restSame).2
    refine ⟨environment,solved,?_⟩
    simpa only [List.map_append,frontSame,childrenSame,pendingSame] using returned
  · rintro ⟨environment,model,returned⟩
    have assembled : (sourceFront ++ .expression sourceChildren :: sourcePending).map
        (read environment) ∈
        HE.Spec.Bindings.ScopeObservation.observedTuples incoming
          (heFront ++ .expression heChildren :: hePending) := by
      rw [related]
      exact ⟨environment,model,rfl⟩
    obtain ⟨valuation,solved,same⟩ := assembled
    simp only [List.map_append,List.map_cons,expressionRead,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at same
    obtain ⟨frontSame,restSame⟩ := List.append_inj same (by
      simpa only [List.length_map] using frontLength)
    have expressionSame := (List.cons.inj restSame).1
    have childrenSame : sourceChildren.map (read environment) =
        heChildren.map (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) :=
      Atom.expression.inj expressionSame.symm
    have pendingSame := (List.cons.inj restSame).2
    refine ⟨valuation,solved,?_⟩
    simpa only [List.map_append,frontSame,childrenSame,pendingSame] using returned

/-- Reassembling one coordinate after an already evaluated prefix preserves
the same joint model. -/
theorem joint_packet_assemble_coordinate
    {incoming : HE.Bindings} {before : Equations}
    {heFront heChildren hePending sourceFront sourceChildren sourcePending : List Atom}
    (frontLength : heFront.length = sourceFront.length)
    (childrenLength : heChildren.length = sourceChildren.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (heFront ++ heChildren ++ hePending) =
      solutionTuples before (sourceFront ++ sourceChildren ++ sourcePending)) :
    HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (heFront ++ .expression heChildren :: hePending) =
      solutionTuples before (sourceFront ++ .expression sourceChildren :: sourcePending) := by
  have expressionRead (environment : Environment) (atoms : List Atom) :
      read environment (.expression atoms) = .expression (atoms.map (read environment)) := by
    simp only [read_eq_applyTypeValuation,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
    exact congrArg Atom.expression (List.map_congr_left fun atom _ =>
      (read_eq_applyTypeValuation environment atom).symm)
  ext values
  constructor
  · rintro ⟨valuation,model,returned⟩
    have flat : (heFront ++ heChildren ++ hePending).map
        (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) ∈
        solutionTuples before (sourceFront ++ sourceChildren ++ sourcePending) := by
      rw [← related]
      exact ⟨valuation,model,rfl⟩
    obtain ⟨environment,solved,same⟩ := flat
    simp only [List.map_append] at same
    rw [List.append_assoc,List.append_assoc] at same
    obtain ⟨frontSame,restSame⟩ := List.append_inj same (by
      simpa only [List.length_map] using frontLength.symm)
    obtain ⟨childrenSame,pendingSame⟩ := List.append_inj restSame (by
      simpa only [List.length_map] using childrenLength.symm)
    refine ⟨environment,solved,?_⟩
    simp only [List.map_append,List.map_cons,expressionRead]
    simpa only [frontSame,childrenSame,pendingSame,List.map_append,List.map_cons,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,expressionRead] using returned
  · rintro ⟨environment,solved,returned⟩
    have flat : (sourceFront ++ sourceChildren ++ sourcePending).map (read environment) ∈
        HE.Spec.Bindings.ScopeObservation.observedTuples incoming
          (heFront ++ heChildren ++ hePending) := by
      rw [related]
      exact ⟨environment,solved,rfl⟩
    obtain ⟨valuation,model,same⟩ := flat
    simp only [List.map_append] at same
    rw [List.append_assoc,List.append_assoc] at same
    obtain ⟨frontSame,restSame⟩ := List.append_inj same (by
      simpa only [List.length_map] using frontLength)
    obtain ⟨childrenSame,pendingSame⟩ := List.append_inj restSame (by
      simpa only [List.length_map] using childrenLength)
    refine ⟨valuation,model,?_⟩
    simp only [List.map_append,List.map_cons]
    simpa only [frontSame,childrenSame,pendingSame,List.map_append,List.map_cons,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,expressionRead] using returned

/-- Focusing the current coordinate before an equally long evaluated prefix
is a shared observer permutation.  It changes neither solution theory nor
occurrence multiplicity. -/
theorem joint_packet_focus_coordinate
    {incoming : HE.Bindings} {before : Equations}
    {heFront sourceFront : List Atom} {query sourceQuery : Atom}
    {hePending sourcePending : List Atom}
    (frontLength : heFront.length = sourceFront.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (heFront ++ query :: hePending) =
      solutionTuples before (sourceFront ++ sourceQuery :: sourcePending)) :
    HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (query :: heFront ++ hePending) =
      solutionTuples before (sourceQuery :: sourceFront ++ sourcePending) := by
  ext values
  constructor
  · rintro ⟨valuation,model,returned⟩
    have original : (heFront ++ query :: hePending).map
        (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) ∈
        solutionTuples before (sourceFront ++ sourceQuery :: sourcePending) := by
      rw [← related]
      exact ⟨valuation,model,rfl⟩
    obtain ⟨environment,solved,same⟩ := original
    simp only [List.map_append,List.map_cons] at same
    obtain ⟨frontSame,restSame⟩ := List.append_inj same (by
      simpa only [List.length_map] using frontLength.symm)
    have querySame := (List.cons.inj restSame).1
    have pendingSame := (List.cons.inj restSame).2
    refine ⟨environment,solved,?_⟩
    simpa only [List.map_cons,List.map_append,frontSame,querySame,pendingSame] using returned
  · rintro ⟨environment,solved,returned⟩
    have original : (sourceFront ++ sourceQuery :: sourcePending).map (read environment) ∈
        HE.Spec.Bindings.ScopeObservation.observedTuples incoming
          (heFront ++ query :: hePending) := by
      rw [related]
      exact ⟨environment,solved,rfl⟩
    obtain ⟨valuation,model,same⟩ := original
    simp only [List.map_append,List.map_cons] at same
    obtain ⟨frontSame,restSame⟩ := List.append_inj same (by
      simpa only [List.length_map] using frontLength)
    have querySame := (List.cons.inj restSame).1
    have pendingSame := (List.cons.inj restSame).2
    refine ⟨valuation,model,?_⟩
    simpa only [List.map_cons,List.map_append,frontSame,querySame,pendingSame] using returned

theorem joint_packet_unfocus_coordinate
    {incoming : HE.Bindings} {before : Equations}
    {heFront sourceFront : List Atom} {query sourceQuery : Atom}
    {hePending sourcePending : List Atom}
    (frontLength : heFront.length = sourceFront.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (query :: heFront ++ hePending) =
      solutionTuples before (sourceQuery :: sourceFront ++ sourcePending)) :
    HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (heFront ++ query :: hePending) =
      solutionTuples before (sourceFront ++ sourceQuery :: sourcePending) := by
  ext values
  constructor
  · rintro ⟨valuation,model,returned⟩
    have focused : (query :: heFront ++ hePending).map
        (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) ∈
        solutionTuples before (sourceQuery :: sourceFront ++ sourcePending) := by
      rw [← related]
      exact ⟨valuation,model,rfl⟩
    obtain ⟨environment,solved,same⟩ := focused
    simp only [List.map_append,List.map_cons] at same
    have querySame := (List.cons.inj same).1
    have restSame := (List.cons.inj same).2
    obtain ⟨frontSame,pendingSame⟩ := List.append_inj restSame (by
      simpa only [List.length_map] using frontLength.symm)
    refine ⟨environment,solved,?_⟩
    simpa only [List.map_cons,List.map_append,frontSame,querySame,pendingSame] using returned
  · rintro ⟨environment,solved,returned⟩
    have focused : (sourceQuery :: sourceFront ++ sourcePending).map (read environment) ∈
        HE.Spec.Bindings.ScopeObservation.observedTuples incoming
          (query :: heFront ++ hePending) := by
      rw [related]
      exact ⟨environment,solved,rfl⟩
    obtain ⟨valuation,model,same⟩ := focused
    simp only [List.map_append,List.map_cons] at same
    have querySame := (List.cons.inj same).1
    have restSame := (List.cons.inj same).2
    obtain ⟨frontSame,pendingSame⟩ := List.append_inj restSame (by
      simpa only [List.length_map] using frontLength)
    refine ⟨valuation,model,?_⟩
    simpa only [List.map_cons,List.map_append,frontSame,querySame,pendingSame] using returned

/-- A passive HE value and a correlated source value complete the same fresh
destination occurrence.  The source may reach this final equation through a
larger structural derivation; this lemma only discharges the boundary. -/
theorem passive_forward
    (program : Program) (allowed machineScope : List String) (live : List Atom)
    (frame : Frame) (control : Control) (input : Entry.Value) (sourceValue : Atom)
    (slotName : String) (older : List Goal)
    (valid : Value program input.erase allowed) (safe : NoErrorSymbol input.erase)
    (passive : PassiveEnvironment program allowed frame.environment)
    (hePrefix sourcePrefix hePending sourcePending : List Atom)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (hePrefix ++ input.erase :: hePending) =
      solutionTuples control.bindings (sourcePrefix ++ sourceValue :: sourcePending))
    (support : SupportRel allowed live frame.bindings
      (hePrefix ++ input.erase :: hePending)
      (sourcePrefix ++ sourceValue :: sourcePending) control)
    (storeFresh : ∀ pair ∈ control.bindings,
      slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
        slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2)
    (packetFresh : slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (sourcePrefix ++ sourceValue :: sourcePending))
    (accepted : Refinement control.bindings sourceValue (.var slotName)
      (some (control.bindings ++ [(sourceValue,.var slotName)]))) :
    ∃ output,
      AtomRel (equationSpace program) noForeign rawLookup
        live machineScope input Atom.undefinedType frame [(output,frame)]
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      OutcomeRel program allowed hePrefix sourcePrefix hePending sourcePending (.var slotName)
        older control (output,frame)
        ({control with bindings := control.bindings ++ [(sourceValue,.var slotName)],goals := older} : Control) := by
  cases accepted
  obtain ⟨output,completed,outputErase⟩ :=
    passive.he_completes frame input valid safe live machineScope HE.Spec.Eval.Completed.Policy.unmarked
  have readAdmitted := passive.substitute .preserve input valid safe
  have relatedOutput : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
      (hePrefix ++ output.erase :: hePending) =
      solutionTuples control.bindings (sourcePrefix ++ sourceValue :: sourcePending) := by
    rw [outputErase]
    exact (observed_read_coordinate HE.Spec.Eval.Completed.Policy.unmarked
      frame hePrefix hePending input).trans related
  have packet := private_destination_joint_prefix relatedOutput slotName storeFresh packetFresh
  let afterControl : Control :=
    {control with bindings := control.bindings ++ [(sourceValue,.var slotName)],goals := older}
  have monotone : PersistentSupport control ⊆ PersistentSupport afterControl :=
    persistentSupport_append_equation control sourceValue (.var slotName) older
  refine ⟨output,completed,⟨allowed,fun _ member => member,rfl,monotone,?_,?_,?_,?_,?_,passive,?_⟩⟩
  · intro name member
    exact monotone (support.scope name member)
  · intro name member
    exact monotone (support.incoming name member)
  · intro name member
    apply typeVars_mem_persistent_binding afterControl (sourceValue,.var slotName)
    · simp [afterControl]
    · exact List.mem_append_right _ member
  · rw [outputErase]
    exact readAdmitted.1
  · rw [outputErase]
    exact readAdmitted.2
  · simpa only using packet

/-- The open variable rule is already a complete paired child: HE reads a
passive capture, while the source binds its fresh destination. -/
theorem variable_forward
    (program : Program) (allowed machineScope : List String) (live : List Atom)
    (frame : Frame) (control : Control)
    (input : Entry.Value) (sourceName slotName : String) (older : List Goal)
    (sourceInstance : InputInstance program allowed (.var sourceName) input)
    (passive : PassiveEnvironment program allowed frame.environment)
    (hePrefix sourcePrefix hePending sourcePending : List Atom)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (hePrefix ++ input.erase :: hePending) =
      solutionTuples control.bindings (sourcePrefix ++ .var sourceName :: sourcePending))
    (support : SupportRel allowed live frame.bindings
      (hePrefix ++ input.erase :: hePending)
      (sourcePrefix ++ .var sourceName :: sourcePending) control)
    (storeFresh : ∀ pair ∈ control.bindings,
      slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
        slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2)
    (packetFresh : slotName ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (sourcePrefix ++ .var sourceName :: sourcePending))
    (accepted : Refinement control.bindings (.var sourceName) (.var slotName)
      (some (control.bindings ++ [(.var sourceName,.var slotName)]))) :
    ∃ output,
      AtomRel (equationSpace program) noForeign rawLookup
        live machineScope input Atom.undefinedType frame [(output,frame)]
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      OutcomeRel program allowed hePrefix sourcePrefix hePending sourcePending (.var slotName)
        older control (output,frame)
        ({control with bindings := control.bindings ++ [(.var sourceName,.var slotName)],goals := older} : Control) := by
  have admitted := sourceInstance.value_of_source_variable
  exact passive_forward program allowed machineScope live frame control input (.var sourceName) slotName older
    admitted.1 admitted.2 passive hePrefix sourcePrefix hePending sourcePending related
    support storeFresh packetFresh accepted

/-- Every passive source leaf uses the same two logical operations: HE
materializes the admitted value, and the source equates that value with its
private destination.  The result is stated for the actual refinement output,
not only for a hand-written append expression. -/
theorem direct_forward
    (program : Program) (allowed machineScope : List String) (live : List Atom)
    (frame : Frame) (control : Control) (input : Entry.Value) (sourceValue destination : Atom)
    (older : List Goal) (sourceInstance : InputInstance program allowed sourceValue input)
    (sourceValid : Value program sourceValue allowed) (sourceSafe : NoErrorSymbol sourceValue)
    (passive : PassiveEnvironment program allowed frame.environment)
    (hePrefix sourcePrefix hePending sourcePending : List Atom)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (hePrefix ++ input.erase :: hePending) =
      solutionTuples control.bindings (sourcePrefix ++ sourceValue :: sourcePending))
    (support : SupportRel allowed live frame.bindings
      (hePrefix ++ input.erase :: hePending)
      (sourcePrefix ++ sourceValue :: sourcePending) control)
    (privateDestination : PrivateDestination control sourceValue destination older)
    (packetFresh : privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (sourcePrefix ++ sourceValue :: sourcePending))
    {after : Equations}
    (accepted : Refinement control.bindings sourceValue destination (some after)) :
    ∃ output,
      AtomRel (equationSpace program) noForeign rawLookup live machineScope input
        Atom.undefinedType frame [(output,frame)]
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      OutcomeRel program allowed hePrefix sourcePrefix hePending sourcePending destination
        older control (output,frame) ({control with bindings := after,goals := older} : Control) := by
  obtain ⟨inputValid,inputSafe⟩ := sourceInstance.passive sourceValid sourceSafe
  rw [privateDestination.destination_eq] at accepted ⊢
  cases accepted with
  | accepted environment old same =>
      exact passive_forward program allowed machineScope live frame control input sourceValue
        privateDestination.name older inputValid inputSafe passive hePrefix sourcePrefix
        hePending sourcePending related support privateDestination.storeFresh packetFresh
        (.accepted environment old same)

theorem direct_forward_batch
    (program : Program) (allowed machineScope : List String) (live : List Atom)
    (frame : Frame) (control : Control) (input : Entry.Value) (sourceValue destination : Atom)
    (older : List Goal) (sourceInstance : InputInstance program allowed sourceValue input)
    (sourceValid : Value program sourceValue allowed) (sourceSafe : NoErrorSymbol sourceValue)
    (passive : PassiveEnvironment program allowed frame.environment)
    (hePrefix sourcePrefix hePending sourcePending : List Atom)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (hePrefix ++ input.erase :: hePending) =
      solutionTuples control.bindings (sourcePrefix ++ sourceValue :: sourcePending))
    (support : SupportRel allowed live frame.bindings
      (hePrefix ++ input.erase :: hePending)
      (sourcePrefix ++ sourceValue :: sourcePending) control)
    (privateDestination : PrivateDestination control sourceValue destination older)
    (packetFresh : privateDestination.name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (sourcePrefix ++ sourceValue :: sourcePending))
    {after : Equations}
    (accepted : Refinement control.bindings sourceValue destination (some after)) :
    ∃ results,
      AtomRel (equationSpace program) noForeign rawLookup live machineScope input
        Atom.undefinedType frame results (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program allowed hePrefix sourcePrefix hePending sourcePending
        destination older control)
        results [({control with bindings := after,goals := older} : Control)] := by
  obtain ⟨output,completed,relatedOutput⟩ := direct_forward program allowed machineScope live
    frame control input sourceValue destination older sourceInstance sourceValid sourceSafe passive
    hePrefix sourcePrefix hePending sourcePending related support privateDestination packetFresh accepted
  exact ⟨[(output,frame)],completed,.cons relatedOutput .nil⟩

private theorem outcomes_read
    {program : Program} {scope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom} {destination : Atom}
    {older : List Goal} {before : Control}
    {results : List HE.Spec.Eval.Completed.Result} {sources : List Control}
    (related : List.Forall₂
      (OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending destination older before)
      results sources) :
    List.Forall₂
      (OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending destination older before)
      (results.map (HE.Spec.Eval.Completed.readResult HE.Spec.Eval.Completed.Policy.unmarked))
      sources := by
  induction related with
  | nil => exact .nil
  | cons one _rest ih => exact .cons one.readResult ih

private theorem outcomes_publish
    {program : Program} {scope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom} {destination original : Atom}
    {older : List Goal} {before : Control}
    {results : List HE.Spec.Eval.Completed.Result} {sources : List Control}
    (related : List.Forall₂
      (OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending destination older before)
      results sources) :
    List.Forall₂
      (OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending destination older before)
      (results.map (HE.Spec.Eval.Completed.publishResult
        HE.Spec.Eval.Completed.Policy.unmarked original)) sources := by
  induction related with
  | nil => exact .nil
  | cons one _rest ih => exact .cons one.publishResult ih

private theorem outcomes_no_error
    {program : Program} {scope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom} {destination : Atom}
    {older : List Goal} {before : Control}
    {results : List HE.Spec.Eval.Completed.Result} {sources : List Control}
    (related : List.Forall₂
      (OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending destination older before)
      results sources) :
    ∀ result ∈ results, HE.isErrorAtom result.1.erase = false := by
  induction related with
  | nil => simp
  | @cons result source results sources one _rest ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨_outScope,_included,_goals,_monotone,_scopeSupported,
          _bindingsSupported,_destinationSupported,valid,_safe,_passive,_packet⟩ := one
        have clean := valid.boolean_clean
        simp only [HE.isEmptyOrError,Bool.or_eq_false_iff] at clean
        exact clean.2
      · exact ih candidate member

/-- Open materialized applications use the same tuple/call machine rule as
closed ones.  The only extra work is to read each reached result before
publication; `OutcomeRel` proves that this preserves its joint packet. -/
theorem expression_complete_open
    (program : Program) (allowed machineScope : List String) (live : List Atom)
    (head : String) (ordinary : OrdinaryHead head)
    (arguments : List Entry.Value) (frame : Frame) (input : Entry.Value)
    (readShape : frame.read HE.Spec.Eval.Completed.Policy.unmarked input =
      .expression .active (.symbol head :: arguments))
    {rows raw : List HE.Spec.Eval.Completed.Result}
    (tuple : TupleRel (equationSpace program) noForeign rawLookup
      (Atom.undefinedType :: live) machineScope (.symbol head :: arguments) frame rows
      (policy := HE.Spec.Eval.Completed.Policy.unmarked))
    (calls : CallsRel (equationSpace program) noForeign rawLookup live machineScope
      Atom.undefinedType rows raw (policy := HE.Spec.Eval.Completed.Policy.unmarked))
    {hePrefix sourcePrefix hePending sourcePending : List Atom} {destination : Atom}
    {older : List Goal} {before : Control}
    {sources : List Control}
    (related : List.Forall₂
      (OutcomeRel program allowed hePrefix sourcePrefix hePending sourcePending
        destination older before)
      raw sources) :
    ∃ results,
      AtomRel (equationSpace program) noForeign rawLookup live machineScope input
        Atom.undefinedType frame results
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂
        (OutcomeRel program allowed hePrefix sourcePrefix hePending sourcePending
          destination older before)
        results sources := by
  let readRaw := raw.map
    (HE.Spec.Eval.Completed.readResult HE.Spec.Eval.Completed.Policy.unmarked)
  have readRelated : List.Forall₂
      (OutcomeRel program allowed hePrefix sourcePrefix hePending sourcePending
        destination older before)
      readRaw sources := outcomes_read related
  have noError : ∀ result ∈ readRaw, HE.isErrorAtom result.1.erase = false :=
    outcomes_no_error readRelated
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : HE.Spec.Eval.Completed.Result => HE.isErrorAtom result.1.erase)
      readRaw readRaw := by
    cases readEq : readRaw with
    | nil =>
        exact .allErrors (by simp)
    | cons first rest =>
        have noError' : ∀ result ∈ first :: rest,
            HE.isErrorAtom result.1.erase = false := by
          intro result member
          exact noError result (by rw [readEq]; exact member)
        have filter : (first :: rest).filter
            (fun result => !HE.isErrorAtom result.1.erase) = first :: rest := by
          apply List.filter_eq_self.mpr
          intro result member
          simp only [noError' result member,Bool.not_false]
        simpa only [filter] using
          (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
            (isError := fun result : HE.Spec.Eval.Completed.Result => HE.isErrorAtom result.1.erase)
            (raw := first :: rest) ⟨first,List.mem_cons_self,noError' first List.mem_cons_self⟩)
  have headClean : head ≠ "Error" := fun same => ordinary.2.2 (by simp [same])
  have entered : Entry.Rel HE.Spec.Eval.Completed.Policy.unmarked.reentry
      (frame.read HE.Spec.Eval.Completed.Policy.unmarked input).status
      (frame.read HE.Spec.Eval.Completed.Policy.unmarked input).erase
      Atom.undefinedType .interpret := by
    rw [readShape]
    simp only [Entry.Value.status,Entry.Value.erase,List.map_cons]
    apply Entry.Rel.expression
    · simp [HE.Spec.Eval.IsEmptyOrErrorRel,HE.Spec.Eval.IsErrorRel,
        Atom.empty,headClean]
    · simp [Atom.undefinedType,Atom.atomType,Atom.expressionType,Atom.variableType]
    · exact Or.inr rfl
  let published := readRaw.map (HE.Spec.Eval.Completed.publishResult
    HE.Spec.Eval.Completed.Policy.unmarked
      (frame.read HE.Spec.Eval.Completed.Policy.unmarked input).erase)
  have completed : AtomRel (equationSpace program) noForeign rawLookup live machineScope input
      Atom.undefinedType frame published (policy := HE.Spec.Eval.Completed.Policy.unmarked) := by
    apply AtomRel.tuple entered readShape
    · simpa only [Entry.Value.erase,Multiset.coe_singleton] using
        (HE.Spec.Type.StorageTypesRel.symbolUndefined
          (equationSpace.no_annotations program (.symbol head))).occurrences
    · exact tuple
    · exact calls
    · exact priority
  exact ⟨published,completed,outcomes_publish readRelated⟩

/-- Passive constructor assembly is one source equation and one HE absent-call
occurrence.  The fresh destination is observed jointly with the caller packet. -/
theorem constructor_invocation_forward
    (program : Program) (allowed machineScope : List String) (live : List Atom)
    (head : String) (sourceArguments : List Atom) (arguments : List Entry.Value)
    (constructor : ConstructorHead program head)
    (argumentValues : ∀ argument ∈ arguments,
      Value program argument.erase allowed ∧ NoErrorSymbol argument.erase)
    (frame : Frame) (passive : PassiveEnvironment program allowed frame.environment)
    (control : Control) (destination : Atom) (older : List Goal)
    (privateDestination : PrivateDestination control
      (.expression (.symbol head :: sourceArguments)) destination older)
    (hePrefix sourcePrefix hePending sourcePending : List Atom)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (hePrefix ++
          (Entry.Value.expression .active (Entry.Value.symbol head :: arguments)).erase :: hePending) =
      solutionTuples control.bindings
        (sourcePrefix ++ .expression (.symbol head :: sourceArguments) :: sourcePending))
    (support : SupportRel allowed live frame.bindings
      (hePrefix ++
        (Entry.Value.expression .active (Entry.Value.symbol head :: arguments)).erase :: hePending)
      (sourcePrefix ++ .expression (.symbol head :: sourceArguments) :: sourcePending) control)
    (packetFresh : privateDestination.name ∉
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList
        (sourcePrefix ++ .expression (.symbol head :: sourceArguments) :: sourcePending))
    {after : Equations}
    (accepted : Refinement control.bindings
      (.expression (.symbol head :: sourceArguments)) destination (some after)) :
    ∃ results,
      CallRel (equationSpace program) noForeign rawLookup live machineScope
        (.expression .active (.symbol head :: arguments)) Atom.undefinedType frame results
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂
        (OutcomeRel program allowed hePrefix sourcePrefix hePending sourcePending
          destination older control)
        results [({control with bindings := after,goals := older} : Control)] := by
  let original : Entry.Value := .expression .active (.symbol head :: arguments)
  have value : Value program original.erase allowed := by
    simp only [original,Entry.Value.erase,List.map_cons]
    apply Value.constructor constructor
    intro atom member
    obtain ⟨argument,present,rfl⟩ := List.mem_map.mp member
    exact (argumentValues argument present).1
  have safe : NoErrorSymbol original.erase := by
    simp only [original,Entry.Value.erase,List.map_cons]
    apply NoErrorSymbol.expression
    intro atom member
    obtain rfl | member := List.mem_cons.mp member
    · exact NoErrorSymbol.symbol (fun same => constructor.1.2.2 (by simp [same]))
    · obtain ⟨argument,present,rfl⟩ := List.mem_map.mp member
      exact (argumentValues argument present).2
  have call : CallRel (equationSpace program) noForeign rawLookup live machineScope
      original Atom.undefinedType frame [(original,frame)]
      (policy := HE.Spec.Eval.Completed.Policy.unmarked) := by
    apply CallRel.absent (fun failed => value.not_stopped (Or.inr failed))
    · simpa only [original,Entry.Value.erase,List.map_cons] using
        constructor.1.he_non_grounded (arguments.map Entry.Value.erase)
    · simpa only [original,Entry.Value.erase,List.map_cons] using
        constructor.he_frontier_empty (arguments.map Entry.Value.erase)
          (Atom.undefinedType :: live) frame.bindings
  rw [privateDestination.destination_eq] at accepted ⊢
  cases accepted with
  | accepted environment old same =>
      have packet := private_destination_joint_prefix related privateDestination.name
        privateDestination.storeFresh packetFresh
      let afterControl : Control :=
        {bindings := control.bindings ++
            [(.expression (.symbol head :: sourceArguments),.var privateDestination.name)]
         goals := older
         destination := control.destination
         reserved := control.reserved
         cutBoundary := control.cutBoundary}
      have monotone : PersistentSupport control ⊆ PersistentSupport afterControl :=
        persistentSupport_append_equation control
          (.expression (.symbol head :: sourceArguments)) (.var privateDestination.name) older
      refine ⟨[(original,frame)],call,.cons ?_ .nil⟩
      refine ⟨allowed,fun _ member => member,rfl,monotone,?_,?_,?_,value,safe,passive,?_⟩
      · intro name member
        exact monotone (support.scope name member)
      · intro name member
        exact monotone (support.incoming name member)
      · intro name member
        apply typeVars_mem_persistent_binding afterControl
          (.expression (.symbol head :: sourceArguments),.var privateDestination.name)
        · simp [afterControl]
        · exact List.mem_append_right _ member
      · simpa only using packet

/-- The semantic names which a clause allocator must protect at an open call.
The contract mentions only observable HE and source support; it does not fix
how a realization chooses fresh spellings. -/
structure FrontierCoverage (control : Control) (live : List Atom)
    (query : Atom) (incoming : HE.Bindings)
    (hePacket sourcePacket : List Atom) : Prop where
  heVisible : ∀ name,
    HE.Spec.Eval.Steps.QueryVisibleName live query incoming name → name ∈ control.support
  heBindings : ∀ name ∈ HE.Spec.Bindings.ScopeObservation.specBindingVars incoming,
    name ∈ control.support
  hePacket : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList hePacket,
    name ∈ control.support
  sourceBindings : ∀ pair ∈ control.bindings,
    ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ++
        HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2,
      name ∈ control.support
  sourcePacket : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList sourcePacket,
    name ∈ control.support

/-- Persistent cross-language support entails the allocator contract at the
current invocation.  Pending goal syntax does not enter this argument. -/
theorem SupportRel.frontierCoverage
    {scope : List String} {live : List Atom} {incoming : HE.Bindings}
    {query : Atom} {pending sourcePacket : List Atom} {control : Control}
    (supported : SupportRel scope live incoming (query :: pending) sourcePacket control) :
    FrontierCoverage control live query incoming (query :: pending) sourcePacket := by
  have lift {name : String} (member : name ∈ PersistentSupport control) :
      name ∈ control.support := persistentSupport_subset_support control member
  constructor
  · intro name visible
    rcases visible with queryVisible | liveVisible | assignmentKey |
        assignmentValue | equalityEndpoint
    · apply lift
      apply supported.hePacket
      exact HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
        List.mem_cons_self name
        ((HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars query name).mp queryVisible)
    · obtain ⟨atom,member,occurs⟩ := liveVisible
      apply lift
      apply supported.live
      exact HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
        member name ((HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars atom name).mp occurs)
    · obtain ⟨value,member⟩ := assignmentKey
      apply lift
      apply supported.incoming
      simp only [HE.Spec.Bindings.ScopeObservation.specBindingVars,List.mem_append,List.mem_flatMap]
      exact Or.inl ⟨(name,value),member,by simp⟩
    · obtain ⟨key,value,member,occurs⟩ := assignmentValue
      apply lift
      apply supported.incoming
      simp only [HE.Spec.Bindings.ScopeObservation.specBindingVars,List.mem_append,List.mem_flatMap]
      exact Or.inl ⟨(key,value),member,by
        exact List.mem_cons_of_mem _
          ((HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars value name).mp occurs)⟩
    · obtain ⟨left,right,member,endpoint⟩ := equalityEndpoint
      rcases endpoint with same | same
      · subst name
        apply lift
        apply supported.incoming
        simp only [HE.Spec.Bindings.ScopeObservation.specBindingVars,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨(left,right),member,by simp⟩
      · subst name
        apply lift
        apply supported.incoming
        simp only [HE.Spec.Bindings.ScopeObservation.specBindingVars,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨(left,right),member,by simp⟩
  · intro name member
    exact lift (supported.incoming name member)
  · intro name member
    exact lift (supported.hePacket name member)
  · intro pair member name occurrence
    exact lift (typeVars_mem_persistent_binding control pair member name occurrence)
  · intro name member
    exact lift (supported.sourcePacket name member)

/-- At a focused invocation, source resolution may change the syntax of the
argument vector.  Its variables are licensed by the source allocator; every
other name comes from the persistent joint packet. -/
theorem SupportRel.resolvedInvocationCoverage
    {scope : List String} {live : List Atom} {incoming : HE.Bindings}
    {heFront sourceFront hePending sourcePending : List Atom}
    {query : Atom} {control : Control} (extra : Finset String)
    (head : String) (arguments resolvedArguments : List Atom)
    (supported : SupportRel scope live incoming
      (heFront ++ query :: hePending)
      (sourceFront ++ .expression (.symbol head :: arguments) :: sourcePending) control)
    (resolvedSupported : ∀ name ∈
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList resolvedArguments,
      name ∈ (protectControl control extra).support) :
    FrontierCoverage (protectControl control extra) live query incoming
      (query :: heFront ++ hePending)
      (.expression (.symbol head :: resolvedArguments) :: sourceFront ++ sourcePending) := by
  have focused : SupportRel scope live incoming
      (query :: heFront ++ hePending)
      (.expression (.symbol head :: arguments) :: sourceFront ++ sourcePending) control := by
    refine ⟨supported.scope,supported.live,supported.incoming,?_,?_⟩
    · intro name member
      apply supported.hePacket
      simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
        HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append,List.mem_cons,
        or_comm,or_left_comm,or_assoc] using member
    · intro name member
      apply supported.sourcePacket
      simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
        HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append,List.mem_cons,
        or_comm,or_left_comm,or_assoc] using member
  have protectedMono : PersistentSupport control ⊆
      PersistentSupport (protectControl control extra) := by
    rw [persistentSupport_protectControl]
    exact Finset.subset_union_left
  have raw := (focused.mono protectedMono).frontierCoverage
  refine ⟨raw.heVisible,raw.heBindings,raw.hePacket,raw.sourceBindings,?_⟩
  intro name member
  rcases List.mem_append.mp member with resolved | rest
  · exact resolvedSupported name (by simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      HE.Spec.Type.Presentation.TypeSubst.typeVars,List.append_nil,List.nil_append] using resolved)
  · apply raw.sourcePacket
    exact List.mem_append_right _ rest

/-- Any allocator satisfying `FrontierCoverage` produces a clause instance
fresh for both open observations.  This is the nominal interface used by E2;
`protectControl` is only one implementation of the interface. -/
theorem FrontierCoverage.fresh_clause
    {control : Control} {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {hePacket sourcePacket : List Atom}
    (covered : FrontierCoverage control live query incoming hePacket sourcePacket)
    (position : Nat) (equation : PeTTa.SpaceSemantics.Equation) :
    let pattern := ClauseChoice.freshPattern control position equation
    let body := ClauseChoice.freshBody control position equation
    (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList [pattern,body],
      name ∉ HE.Spec.Bindings.ScopeObservation.specBindingVars incoming ∧
        name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList hePacket) ∧
    (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList [pattern,body],
      (∀ pair ∈ control.bindings,
        name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
          name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2) ∧
        name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList sourcePacket) := by
  intro pattern body
  have avoids : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList [pattern,body],
      name ∉ control.support := by
    intro name occurs
    obtain ⟨atom,member,inside⟩ :=
      HE.Spec.Type.Presentation.Freshness.exists_mem_of_mem_typeVarsList occurs
    have paired : ClauseChoice.freshen control position (ClauseChoice.clauseAtoms equation) =
        [pattern,body] := rfl
    exact ClauseChoice.freshen_vars_avoid control position (ClauseChoice.clauseAtoms equation)
      atom (paired ▸ member) name inside
  constructor
  · intro name occurs
    exact ⟨fun member => avoids name occurs (covered.heBindings name member),
      fun member => avoids name occurs (covered.hePacket name member)⟩
  · intro name occurs
    constructor
    · intro pair member
      have both := covered.sourceBindings pair member
      exact ⟨fun inside => avoids name occurs (both name (List.mem_append_left _ inside)),
        fun inside => avoids name occurs (both name (List.mem_append_right _ inside))⟩
    · intro member
      exact avoids name occurs (covered.sourcePacket name member)

/-- A complete clause scan under an arbitrary support-respecting allocator
constructs the corresponding HE frontier.  It preserves physical occurrence
multiplicity and the complete correlated pending packet. -/
theorem guarded_joint_frontier
    (program : Program) (control : Control)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (live : List Atom) (query : Atom) (incoming : HE.Bindings)
    (pending sourcePending : List Atom)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming (query :: pending) =
      solutionTuples control.bindings
        (.expression (.symbol head :: arguments) :: sourcePending))
    (covered : FrontierCoverage control live query incoming (query :: pending)
      (.expression (.symbol head :: arguments) :: sourcePending))
    {choices : List (Nat × Control)}
    (frontier : ClauseChoice.Frontier program control head arguments destination older
      (List.range program.equations.length) choices) :
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live
        query incoming works ∧
      List.Forall₂ (ClausePendingAgreement control
        (.expression (.symbol head :: arguments)) destination older pending sourcePending)
        choices works := by
  have rowLaw : ∀ {position : Nat} {result : Option Control},
      ClauseChoice.Decision program control head arguments destination older position result →
      ∃ equation works, program.equations[position]? = some equation ∧
        HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming position
          (PeTTa.SpaceSemantics.Equation.toAtom equation) works ∧
        List.Forall₂ (fun next work =>
          ClausePendingAgreement control (.expression (.symbol head :: arguments))
            destination older pending sourcePending (position,next) work)
          result.toList works := by
    intro position result decision
    have miss (equation : PeTTa.SpaceSemantics.Equation)
        (refused : Refinement control.bindings (.expression (.symbol head :: arguments))
          (ClauseChoice.freshPattern control position equation) none) :
        HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming position
          (PeTTa.SpaceSemantics.Equation.toAtom equation) [] := by
      have fresh := covered.fresh_clause position equation
      have variant := petta_fresh_instance_he_alpha
        (ClauseChoice.fresh_clause_instance control position equation) covered.heVisible
      apply HE.Spec.Eval.Steps.EquationRowResultsRel.miss position _ _ _ _ variant
      intro otherPattern otherBody otherVariant matched output compatible
      apply (petta_fresh_clause_joint_refused_iff related fresh.1 fresh.2).mp refused
      exact (HE.EquationFreshening.alphaVariants_candidate_exists_iff otherVariant variant).mp
        ⟨output,matched,compatible⟩
    cases decision with
    | other equation row different =>
        exact ⟨equation,[],row,miss equation
          (different_head_refused control.bindings control position equation head arguments different),
          .nil⟩
    | refused equation row _same incompatible =>
        exact ⟨equation,[],row,miss equation incompatible,.nil⟩
    | selected equation bindings row _same compatible =>
        have fresh := covered.fresh_clause position equation
        have bindingsEq : bindings = control.bindings ++
            [(.expression (.symbol head :: arguments),
              ClauseChoice.freshPattern control position equation)] := by
          cases compatible
          rfl
        obtain ⟨output,candidate,observations⟩ :=
          petta_fresh_clause_joint_refinement related fresh.1 fresh.2 compatible
        obtain ⟨matched,matching,merged⟩ := candidate
        refine ⟨equation,[⟨position,ClauseChoice.pattern equation,equation.body,
          ClauseChoice.freshPattern control position equation,
          ClauseChoice.freshBody control position equation,output⟩],row,?_,?_⟩
        · exact .hit _ _ _ _ _ _ _
            (petta_fresh_instance_he_alpha
              (ClauseChoice.fresh_clause_instance control position equation) covered.heVisible)
            matching merged
        · exact .cons ⟨rfl,bindingsEq,rfl,rfl,rfl,rfl,observations⟩ .nil
  exact petta_frontier_he_frontier_of_decision
    (ClausePendingAgreement control (.expression (.symbol head :: arguments))
      destination older pending sourcePending) rowLaw frontier

/-- The invocation boundary focuses the assembled call, resolves its source
slots, and constructs the complete correlated HE frontier. -/
theorem equation_invocation_frontier
    (program : Program) (control : Control) (extra : Finset String)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) (resolved : resolve control.bindings = some environment)
    (live : List Atom) (query : Atom) (incoming : HE.Bindings)
    (heFront sourceFront hePending sourcePending : List Atom)
    (frontLength : heFront.length = sourceFront.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (heFront ++ query :: hePending) =
      solutionTuples control.bindings
        (sourceFront ++ .expression (.symbol head :: arguments) :: sourcePending))
    {scope : List String}
    (supported : SupportRel scope live incoming
      (heFront ++ query :: hePending)
      (sourceFront ++ .expression (.symbol head :: arguments) :: sourcePending) control)
    (resolvedSupported : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (arguments.map (read environment)), name ∈ (protectControl control extra).support)
    {choices : List (Nat × Control)}
    (sourceFrontier : ClauseChoice.Frontier program (protectControl control extra) head
      (arguments.map (read environment)) destination older
      (List.range program.equations.length) choices) :
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live
        query incoming works ∧
      List.Forall₂ (ClausePendingAgreement (protectControl control extra)
        (.expression (.symbol head :: arguments.map (read environment))) destination older
        (heFront ++ hePending) (sourceFront ++ sourcePending)) choices works := by
  have focused := joint_packet_focus_coordinate frontLength related
  have resolvedPacket : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
      (query :: heFront ++ hePending) =
      solutionTuples (protectControl control extra).bindings
        (.expression (.symbol head :: arguments.map (read environment)) ::
          sourceFront ++ sourcePending) := by
    change _ = solutionTuples control.bindings _
    exact focused.trans
      (solutionTuples_call_read_arguments resolved head arguments
        (sourceFront ++ sourcePending)).symm
  have coverage := supported.resolvedInvocationCoverage extra head arguments
    (arguments.map (read environment)) resolvedSupported
  exact guarded_joint_frontier program (protectControl control extra) head
    (arguments.map (read environment)) destination older live query incoming
    (heFront ++ hePending) (sourceFront ++ sourcePending) resolvedPacket coverage sourceFrontier

/-- Every retained frontier occurrence has the successful row decision which
created that exact control. -/
theorem ClauseChoice.Frontier.decision_of_mem
    {program : Program} {control : Control} {head : String} {arguments : List Atom}
    {destination : Atom} {older : List Goal} {positions : List Nat}
    {answers : List (Nat × Control)}
    (frontier : ClauseChoice.Frontier program control head arguments destination older
      positions answers) {position : Nat} {selected : Control}
    (member : (position,selected) ∈ answers) :
    ClauseChoice.Decision program control head arguments destination older position
      (some selected) := by
  induction frontier with
  | nil => cases member
  | skip _ rest inductionHypothesis => exact inductionHypothesis member
  | @keep occurrence remaining next answers decision rest inductionHypothesis =>
      rcases List.mem_cons.mp member with same | later
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
        exact decision
      · exact inductionHypothesis later

/-- Syntactic support of a contextual unification output is precisely old
support plus the two matched operands. -/
theorem unifyCandidate_support
    {target pattern : Atom} {incoming output : HE.Bindings}
    (candidate : HE.Spec.Eval.Steps.UnifyCandidateRel target pattern incoming output)
    (name : String) :
    name ∈ HE.Spec.Bindings.ScopeObservation.specBindingVars output ↔
      name ∈ HE.Spec.Bindings.ScopeObservation.specBindingVars incoming ∨
        name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars target ∨
        name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars pattern := by
  obtain ⟨_matched,matching,merged⟩ := candidate
  rw [merged.support name,
    HE.QueryBindingProjection.SourceSupport.match_support matching name]
  tauto

theorem ClausePendingAgreement.persistent_mono
    {caller : Control} {sourceQuery destination : Atom} {older : List Goal}
    {pending sourcePending : List Atom} {selected : Nat × Control}
    {work : HE.Spec.Eval.Steps.EquationWork}
    (agreement : ClausePendingAgreement caller sourceQuery destination older pending sourcePending
      selected work) :
    PersistentSupport caller ⊆ PersistentSupport selected.2 := by
  have appended := persistentSupport_append_equation caller sourceQuery work.pattern selected.2.goals
  intro name member
  have reached := appended member
  unfold PersistentSupport at reached ⊢
  rw [agreement.bindings,agreement.destination,agreement.reserved]
  exact reached

theorem ClausePendingAgreement.pattern_supported
    {caller : Control} {sourceQuery destination : Atom} {older : List Goal}
    {pending sourcePending : List Atom} {selected : Nat × Control}
    {work : HE.Spec.Eval.Steps.EquationWork}
    (agreement : ClausePendingAgreement caller sourceQuery destination older pending sourcePending
      selected work) {name : String}
    (member : name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars work.pattern) :
    name ∈ PersistentSupport selected.2 := by
  apply typeVars_mem_persistent_binding selected.2 (sourceQuery,work.pattern)
  · rw [agreement.bindings]
    exact List.mem_append_right _ List.mem_cons_self
  · exact List.mem_append_right _ member

/-- Both constructor applications and defined calls first materialize the same
ordered argument packet. The argument derivation supplies the continuation
chosen at the source node. -/
private theorem prepared_application_forward
    {program : Program} {control opened : Control} {head : String} {sourceArguments : List Atom}
    {destination : Atom}
    {older : List Goal} {outcomes : List Control}
    (ordinary : OrdinaryHead head)
    (prepared : Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source.Prepared
      .eagerValue program control destination older (.expression (.symbol head :: sourceArguments)) opened)
    {machineScope : List String} {live : List Atom} {scope : List String}
    {frame : Frame} {input : Entry.Value}
    (sourceInstance : InputInstance program scope (.expression (.symbol head :: sourceArguments)) input)
    (passive : PassiveEnvironment program scope frame.environment)
    {heFront sourceFront hePending sourcePending : List Atom}
    (frontLength : heFront.length = sourceFront.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (heFront ++ input.erase :: hePending) =
      solutionTuples control.bindings (sourceFront ++ .expression (.symbol head :: sourceArguments) :: sourcePending))
    (supported : SupportRel scope live frame.bindings
      (heFront ++ input.erase :: hePending)
      (sourceFront ++ .expression (.symbol head :: sourceArguments) :: sourcePending) control)
    (runArguments : ∀ arguments : List Entry.Value,
      List.Forall₂ (InputInstance program scope)
        ((sourceArguments.zip (freshSlots control sourceArguments.length)).map Prod.fst)
        arguments →
      (.expression (.symbol head :: freshSlots control sourceArguments.length) : Atom) =
        .expression (.symbol head :: (sourceArguments.zip
          (freshSlots control sourceArguments.length)).map Prod.snd) →
      HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (heFront ++ [Entry.Value.symbol head].map Entry.Value.erase ++ arguments.map Entry.Value.erase ++ hePending) =
        solutionTuples opened.bindings
          (sourceFront ++ [Atom.symbol head] ++ (sourceArguments.zip
            (freshSlots control sourceArguments.length)).map Prod.fst ++ sourcePending) →
      SupportRel scope live frame.bindings
        (heFront ++ [Entry.Value.symbol head].map Entry.Value.erase ++ arguments.map Entry.Value.erase ++ hePending)
        (sourceFront ++ [Atom.symbol head] ++ (sourceArguments.zip
          (freshSlots control sourceArguments.length)).map Prod.fst ++ sourcePending) opened →
      (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
          (.symbol head :: Atom.undefinedType :: live), name ∈ PersistentSupport opened) →
      ∃ tupleRows raw,
        TupleRel (equationSpace program) noForeign rawLookup
          (.symbol head :: Atom.undefinedType :: live) machineScope arguments frame tupleRows
          (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
        CallsRel (equationSpace program) noForeign rawLookup live machineScope Atom.undefinedType
          (tupleRows.map (assemblePrefix [.symbol head])) raw
          (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
        List.Forall₂ (OutcomeRel program scope heFront sourceFront hePending sourcePending
          destination older opened) raw outcomes) :
    ∃ results,
      AtomRel (equationSpace program) noForeign rawLookup live machineScope input
        Atom.undefinedType frame results (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program scope heFront sourceFront hePending sourcePending
        destination older control) results outcomes := by
  let readInput := frame.read HE.Spec.Eval.Completed.Policy.unmarked input
  have readInstance : InputInstance program scope
      (.expression (.symbol head :: sourceArguments)) readInput :=
    sourceInstance.read frame passive
  have readCode := readInstance.code_input
  obtain ⟨arguments,readShape,instances⟩ := readInstance.application
  have readRelated : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
      (heFront ++ readInput.erase :: hePending) =
    solutionTuples control.bindings
      (sourceFront ++ .expression (.symbol head :: sourceArguments) :: sourcePending) :=
    (observed_read_coordinate HE.Spec.Eval.Completed.Policy.unmarked frame
      heFront hePending input).trans related
  have readSupport := supported.readCoordinate readCode
  have flatRelated := joint_packet_decompose frontLength (by
    simpa only [readInput,readShape,Entry.Value.erase,List.map_cons] using readRelated)
  have readSupportExpr : SupportRel scope live frame.bindings
      (heFront ++ (.expression (.symbol head :: arguments.map Entry.Value.erase)) :: hePending)
      (sourceFront ++ .expression (.symbol head :: sourceArguments) :: sourcePending) control := by
    simpa only [readInput,readShape,Entry.Value.erase,List.map_cons] using readSupport
  have flatSupport := readSupportExpr.decompose |>.of_prepared prepared
  have rowInstances : List.Forall₂ (InputInstance program scope)
      ((sourceArguments.zip (freshSlots control sourceArguments.length)).map Prod.fst)
      arguments := by
    rw [List.map_fst_zip (by simp)]
    exact instances
  have rowSources :
      (sourceArguments.zip (freshSlots control sourceArguments.length)).map Prod.fst =
        sourceArguments := List.map_fst_zip (by simp)
  have assembledShape :
      (.expression (.symbol head :: freshSlots control sourceArguments.length) : Atom) =
        .expression (.symbol head ::
          (sourceArguments.zip (freshSlots control sourceArguments.length)).map Prod.snd) := by
    rw [List.map_snd_zip (by simp)]
  have argumentRelated : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
      (heFront ++ [Entry.Value.symbol head].map Entry.Value.erase ++
        arguments.map Entry.Value.erase ++ hePending) =
    solutionTuples opened.bindings
      (sourceFront ++ [Atom.symbol head] ++
        (sourceArguments.zip (freshSlots control sourceArguments.length)).map Prod.fst ++
          sourcePending) := by
    rw [prepared.retains_frame.1,rowSources]
    simpa only [Entry.Value.erase,List.map_cons,List.map_nil,List.nil_append,
      List.singleton_append,List.cons_append,List.append_assoc] using flatRelated
  have argumentSupport : SupportRel scope live frame.bindings
      (heFront ++ [Entry.Value.symbol head].map Entry.Value.erase ++
        arguments.map Entry.Value.erase ++ hePending)
      (sourceFront ++ [Atom.symbol head] ++
        (sourceArguments.zip (freshSlots control sourceArguments.length)).map Prod.fst ++
          sourcePending) opened := by
    rw [rowSources]
    simpa only [Entry.Value.erase,List.map_cons,List.map_nil,List.nil_append,
      List.singleton_append,List.cons_append,List.append_assoc] using flatSupport
  obtain ⟨tupleRows, raw, tuple, calls, rawRelated⟩ := runArguments arguments
    rowInstances assembledShape argumentRelated argumentSupport (by
      intro name member
      apply flatSupport.live name
      simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
        HE.Spec.Type.Presentation.TypeSubst.typeVars, Atom.undefinedType, List.nil_append,
        List.mem_append] using member)
  have whole := prepend_symbol_tuple (program := program) ordinary arguments
    HE.Spec.Eval.Completed.Policy.unmarked (Atom.undefinedType :: live) machineScope frame tuple
  have preparedMono : PersistentSupport control ⊆ PersistentSupport opened := by
    have same := Mettapedia.Languages.MeTTa.Translation.OpenRecursive.Prepared.persistentSupport_eq prepared
    intro name member
    rw [same]
    exact member
  have rebased := outcomes_rebase (program := program) (scope := scope)
    (middleScope := scope) (fun _ member => member) preparedMono rawRelated
  obtain ⟨results,completed,resultsRelated⟩ := expression_complete_open program scope machineScope live
    head ordinary arguments frame input readShape
    whole calls rebased
  exact ⟨results,completed,resultsRelated⟩

mutual
/-- Every admitted open source evaluation constructs the matching contextual
HE derivation and all correlated source outcomes. -/
theorem Evaluation.forward
    {program : Program} {control : Control} {sourceValue destination : Atom}
    {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control sourceValue destination older outcomes)
    (patterns : ConstructorPatterns program) (programCode : CodeProgram program)
    (machineScope : List String) (live : List Atom) (scope : List String)
    (frame : Frame) (input : Entry.Value)
    (sourceInstance : InputInstance program scope sourceValue input)
    (passive : PassiveEnvironment program scope frame.environment)
    (heFront sourceFront hePending sourcePending : List Atom)
    (frontLength : heFront.length = sourceFront.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (heFront ++ input.erase :: hePending) =
      solutionTuples control.bindings (sourceFront ++ sourceValue :: sourcePending))
    (supported : SupportRel scope live frame.bindings
      (heFront ++ input.erase :: hePending)
      (sourceFront ++ sourceValue :: sourcePending) control)
    (allocated : source.Allocated sourceFront sourcePending) :
    ∃ results,
      AtomRel (equationSpace program) noForeign rawLookup live machineScope input
        Atom.undefinedType frame results (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program scope heFront sourceFront hePending sourcePending
        destination older control) results outcomes := by
  match source with
  | @Evaluation.variable _ control sourceName slotName older after privateDestination atGoal accepted =>
      have admitted := sourceInstance.source_data (by
        intro head arguments impossible
        simp [Entry.Value.ofAtom] at impossible)
      exact direct_forward_batch program scope machineScope live frame control input (.var sourceName)
        (.var slotName) older sourceInstance admitted.1 admitted.2 passive heFront sourceFront
        hePending sourcePending related supported privateDestination allocated accepted
  | @Evaluation.symbol _ control name destination older after privateDestination atGoal accepted =>
      have admitted := sourceInstance.source_data (by
        intro head arguments impossible
        simp [Entry.Value.ofAtom] at impossible)
      exact direct_forward_batch program scope machineScope live frame control input (.symbol name)
        destination older sourceInstance admitted.1 admitted.2 passive heFront sourceFront
        hePending sourcePending related supported privateDestination allocated accepted
  | @Evaluation.grounded _ control value destination older after privateDestination atGoal accepted =>
      have admitted := sourceInstance.source_data (by
        intro head arguments impossible
        simp [Entry.Value.ofAtom] at impossible)
      exact direct_forward_batch program scope machineScope live frame control input (.grounded value)
        destination older sourceInstance admitted.1 admitted.2 passive heFront sourceFront
        hePending sourcePending related supported privateDestination allocated accepted
  | @Evaluation.unit _ control destination older after privateDestination atGoal accepted =>
      have admitted := sourceInstance.source_data (by
        intro head arguments impossible
        simp [Entry.Value.ofAtom] at impossible)
      exact direct_forward_batch program scope machineScope live frame control input (.expression [])
        destination older sourceInstance admitted.1 admitted.2 passive heFront sourceFront
        hePending sourcePending related supported privateDestination allocated accepted
  | @Evaluation.constructor _ control opened head sourceArguments destination older outcomes
      constructor privateDestination atGoal prepared argumentsRun =>
      apply prepared_application_forward constructor.1 prepared sourceInstance passive
        frontLength related supported
      intro arguments instances shape packet support liveSupported
      exact Arguments.forward argumentsRun patterns programCode machineScope
        (.symbol head :: Atom.undefinedType :: live) live scope frame head constructor.1 arguments [] []
        instances (by simp) shape heFront sourceFront hePending sourcePending frontLength rfl packet
        passive support allocated.2 liveSupported
  | @Evaluation.call _ control opened head sourceArguments destination older outcomes
      defined privateDestination atGoal prepared argumentsRun =>
      apply prepared_application_forward defined.1 prepared sourceInstance passive
        frontLength related supported
      intro arguments instances shape packet support liveSupported
      exact Arguments.forward argumentsRun patterns programCode machineScope
        (.symbol head :: Atom.undefinedType :: live) live scope frame head defined.1 arguments [] []
        instances (by simp) shape heFront sourceFront hePending sourcePending frontLength rfl packet
        passive support allocated.2 liveSupported
termination_by structural source

theorem Arguments.forward
    {program : Program} {control : Control} {rows : List (Atom × Atom)}
    {assembled destination : Atom} {final : Goal} {older : List Goal}
    {outcomes : List Control}
    (source : Arguments program control rows assembled destination final older outcomes)
    (patterns : ConstructorPatterns program) (programCode : CodeProgram program)
    (machineScope : List String) (tupleLive callLive : List Atom) (scope : List String) (frame : Frame)
    (head : String) (ordinary : OrdinaryHead head) (annotated evaluated : List Entry.Value)
    (sourceEvaluated : List Atom)
    (instances : List.Forall₂ (InputInstance program scope) (rows.map Prod.fst) annotated)
    (evaluatedValues : ∀ value ∈ evaluated,
      Value program value.erase scope ∧ NoErrorSymbol value.erase)
    (assembledShape : assembled = .expression
      (.symbol head :: (sourceEvaluated ++ rows.map Prod.snd)))
    (heFront sourceFront hePending sourcePending : List Atom)
    (frontLength : heFront.length = sourceFront.length)
    (evaluatedLength : evaluated.length = sourceEvaluated.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
      (heFront ++ (.symbol head :: evaluated).map Entry.Value.erase ++
        annotated.map Entry.Value.erase ++ hePending) =
      solutionTuples control.bindings
        (sourceFront ++ (.symbol head :: sourceEvaluated) ++ rows.map Prod.fst ++ sourcePending))
    (passive : PassiveEnvironment program scope frame.environment)
    (supported : SupportRel scope callLive frame.bindings
      (heFront ++ (.symbol head :: evaluated).map Entry.Value.erase ++
        annotated.map Entry.Value.erase ++ hePending)
      (sourceFront ++ (.symbol head :: sourceEvaluated) ++ rows.map Prod.fst ++ sourcePending)
      control)
    (allocated : source.Allocated sourceFront (.symbol head :: sourceEvaluated) sourcePending)
    (tupleLiveSupported : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList tupleLive,
      name ∈ PersistentSupport control) :
    ∃ tupleRows raw,
      TupleRel (equationSpace program) noForeign rawLookup tupleLive machineScope
        annotated frame tupleRows (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      CallsRel (equationSpace program) noForeign rawLookup callLive machineScope
        Atom.undefinedType (tupleRows.map (assemblePrefix (.symbol head :: evaluated))) raw
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program scope heFront sourceFront hePending sourcePending
        destination older control) raw outcomes := by
  match source with
  | .nil atGoal continued =>
      cases instances
      have invocationRelated := joint_packet_assemble_coordinate
        (heFront := heFront) (sourceFront := sourceFront)
        (heChildren := (.symbol head :: evaluated).map Entry.Value.erase)
        (sourceChildren := .symbol head :: sourceEvaluated)
        (hePending := hePending) (sourcePending := sourcePending) frontLength
        (by simpa only [List.length_map,List.length_cons] using congrArg Nat.succ evaluatedLength)
        (by simpa only [List.map_nil,List.append_nil,assembledShape,List.nil_append]
          using related)
      have invocationSupport := (by
        have normalized : SupportRel scope callLive frame.bindings
            (heFront ++ (.symbol head :: evaluated).map Entry.Value.erase ++ hePending)
            (sourceFront ++ (.symbol head :: sourceEvaluated) ++ sourcePending) control := by
          simpa only [List.map_nil,List.append_nil,List.nil_append] using supported
        have base := SupportRel.assemble
          (heFront := heFront) (sourceFront := sourceFront)
          (heChildren := (.symbol head :: evaluated).map Entry.Value.erase)
          (sourceChildren := .symbol head :: sourceEvaluated)
          (hePending := hePending) (sourcePending := sourcePending) normalized
        simpa only [List.map_nil,List.append_nil,assembledShape,List.nil_append] using base)
      have prefixValues : ∀ value ∈ (.symbol head :: evaluated),
          Value program value.erase scope ∧ NoErrorSymbol value.erase := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨by simpa only [Entry.Value.erase] using
              (ordinary.symbol_value (program := program) (scope := scope)),
            by simpa only [Entry.Value.erase] using
              (NoErrorSymbol.symbol (fun same => ordinary.2.2 (by simp [same])))⟩
        · exact evaluatedValues value member
      have invocationShape : assembled = .expression (.symbol head :: sourceEvaluated) := by
        simpa only [List.map_nil,List.append_nil] using assembledShape
      obtain ⟨raw,call,rawRelated⟩ := Invocation.forward continued patterns programCode machineScope
        callLive scope frame head evaluated sourceEvaluated evaluatedValues invocationShape
        heFront sourceFront hePending sourcePending frontLength
        (by simpa only [Entry.Value.erase,List.map_cons] using invocationRelated) passive
        (by simpa only [Entry.Value.erase,List.map_cons] using invocationSupport) allocated
      have calls : CallsRel (equationSpace program) noForeign rawLookup callLive machineScope
          Atom.undefinedType
          ([(.expression .active [],frame)].map (assemblePrefix (.symbol head :: evaluated))) raw
          (policy := HE.Spec.Eval.Completed.Policy.unmarked) := by
        have assembledEmpty := assemblePrefix_empty_open (program := program) (scope := scope)
          (.symbol head :: evaluated) prefixValues frame
        rw [show [(.expression .active [],frame)].map
          (assemblePrefix (.symbol head :: evaluated)) =
          [(.expression .active (.symbol head :: evaluated),frame)] by
            simp only [List.map_cons,List.map_nil,assembledEmpty]]
        have emptyCalls : CallsRel (equationSpace program) noForeign rawLookup callLive
            machineScope Atom.undefinedType [] []
            (policy := HE.Spec.Eval.Completed.Policy.unmarked) := CallsRel.nil
        simpa only [List.append_nil] using CallsRel.cons call emptyCalls
      exact ⟨[(.expression .active [],frame)],raw,TupleRel.nil,calls,rawRelated⟩
  | @Arguments.cons _ control sourceValue slot rows assembled destination final older heads outcomes
      atGoal first branches =>
      have annotatedNonempty : annotated ≠ [] := by
        intro empty
        subst annotated
        cases instances
      obtain ⟨input,tail,rfl⟩ := List.exists_cons_of_ne_nil annotatedNonempty
      cases instances with
      | cons headInstance tailInstances =>
          obtain ⟨firstAllocated,branchesAllocated⟩ := allocated
          let headLive := if tail = [] then tupleLive else
            .expression (tail.map Entry.Value.erase) :: tupleLive
          have headRelated : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
              ((heFront ++ (.symbol head :: evaluated).map Entry.Value.erase) ++
                input.erase :: (tail.map Entry.Value.erase ++ hePending)) =
            solutionTuples control.bindings
              ((sourceFront ++ (.symbol head :: sourceEvaluated)) ++ sourceValue ::
                (rows.map Prod.fst ++ sourcePending)) := by
            simpa only [List.map_cons,List.cons_append,List.append_assoc] using related
          have headSupport : SupportRel scope headLive frame.bindings
              ((heFront ++ (.symbol head :: evaluated).map Entry.Value.erase) ++
                input.erase :: (tail.map Entry.Value.erase ++ hePending))
              ((sourceFront ++ (.symbol head :: sourceEvaluated)) ++ sourceValue ::
                (rows.map Prod.fst ++ sourcePending)) control := by
            refine ⟨supported.scope,?_,supported.incoming,?_,?_⟩
            · intro name member
              unfold headLive at member
              split at member
              · exact tupleLiveSupported name member
              · change name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars
                    (.expression (tail.map Entry.Value.erase)) ++
                    HE.Spec.Type.Presentation.TypeSubst.typeVarsList tupleLive at member
                rcases List.mem_append.mp member with tailMember | liveMember
                · change name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
                    (tail.map Entry.Value.erase) at tailMember
                  obtain ⟨atom,atomMember,atomVar⟩ :=
                    HE.Spec.Type.Presentation.Freshness.exists_mem_of_mem_typeVarsList tailMember
                  apply supported.hePacket
                  apply HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
                    (atom := atom)
                  · exact List.mem_append_left hePending
                      (List.mem_append_right
                        (heFront ++ (.symbol head :: evaluated).map Entry.Value.erase)
                        (by simpa only [List.map_cons] using
                          (List.mem_cons_of_mem input.erase atomMember)))
                  · exact atomVar
                · exact tupleLiveSupported name liveMember
            · intro name member
              apply supported.hePacket
              simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
                HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append,List.mem_cons,
                List.map_cons,List.cons_append,List.append_assoc] using member
            · intro name member
              apply supported.sourcePacket
              simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append,
                HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append,List.mem_cons,
                List.map_cons,List.cons_append,List.append_assoc] using member
          obtain ⟨headResults,headCompleted,headOutcomes⟩ := Evaluation.forward first patterns programCode
            machineScope headLive scope frame input headInstance passive
            (heFront ++ (.symbol head :: evaluated).map Entry.Value.erase)
            (sourceFront ++ (.symbol head :: sourceEvaluated))
            (tail.map Entry.Value.erase ++ hePending)
            (rows.map Prod.fst ++ sourcePending)
            (by simp only [List.length_append,List.length_map,List.length_cons]; omega)
            headRelated headSupport firstAllocated
          have heBefore : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
              ((heFront ++ (.symbol head :: evaluated).map Entry.Value.erase) ++
                input.erase :: (tail.map Entry.Value.erase ++ hePending)),
              name ∈ PersistentSupport control := by
            intro name member
            apply supported.hePacket
            simpa only [List.map_cons,List.cons_append,List.append_assoc] using member
          have sourceBefore : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
              ((sourceFront ++ .symbol head :: sourceEvaluated) ++
                sourceValue :: (rows.map Prod.fst ++ sourcePending)),
              name ∈ PersistentSupport control := by
            intro name member
            apply supported.sourcePacket
            simpa only [List.map_cons,List.cons_append,List.append_assoc] using member
          have branchPacketSupported := And.intro
            (typeVarsList_remove_supported heBefore)
            (typeVarsList_remove_supported sourceBefore)
          obtain ⟨tupleRows,raw,branchRel,calls,rawRelated⟩ := ArgumentBranches.forward branches patterns programCode
            machineScope tupleLive callLive scope control head ordinary evaluated tail slot
            heFront sourceFront sourceEvaluated hePending sourcePending frontLength evaluatedLength
            (by simpa only [List.map_cons,List.nil_append,List.cons_append,List.append_assoc]
              using assembledShape)
            evaluatedValues tailInstances branchesAllocated supported.live tupleLiveSupported
            (by
              constructor
              · intro name member
                apply branchPacketSupported.1 name
                simpa only [Entry.Value.erase,List.map_cons,List.cons_append,List.append_assoc]
                  using member
              · intro name member
                apply branchPacketSupported.2 name
                simpa only [List.cons_append,List.append_assoc] using member)
            (by simpa only [Entry.Value.erase,List.map_cons] using headOutcomes)
          have tuple : TupleRel (equationSpace program) noForeign rawLookup tupleLive machineScope
              (input :: tail) frame tupleRows (policy := HE.Spec.Eval.Completed.Policy.unmarked) := by
            cases tail with
            | nil =>
                rw [empty_tuple_branches branchRel (outcomes_not_stopped headOutcomes)]
                exact .singleton (by simpa only [headLive,↓reduceIte] using headCompleted)
            | cons next rest =>
                exact .cons (by simpa only [headLive,List.cons_ne_nil,↓reduceIte] using headCompleted)
                  branchRel
          exact ⟨tupleRows,raw,tuple,calls,rawRelated⟩
termination_by structural source

theorem ArgumentBranches.forward
    {program : Program} {heads outcomes : List Control} {rows : List (Atom × Atom)}
    {assembled destination : Atom} {final : Goal} {older : List Goal}
    (source : ArgumentBranches program heads rows assembled destination final older outcomes)
    (patterns : ConstructorPatterns program) (programCode : CodeProgram program)
    (machineScope : List String) (tupleLive callLive : List Atom) (scope : List String)
    (before : Control) (head : String) (ordinary : OrdinaryHead head)
    (evaluated annotated : List Entry.Value) (slot : Atom)
    (heFront sourceFront sourceEvaluated hePending sourcePending : List Atom)
    (frontLength : heFront.length = sourceFront.length)
    (evaluatedLength : evaluated.length = sourceEvaluated.length)
    (assembledShape : assembled = .expression
      (.symbol head :: ((sourceEvaluated ++ [slot]) ++ rows.map Prod.snd)))
    (evaluatedValues : ∀ value ∈ evaluated,
      Value program value.erase scope ∧ NoErrorSymbol value.erase)
    (instances : List.Forall₂ (InputInstance program scope) (rows.map Prod.fst) annotated)
    (allocated : source.Allocated sourceFront
      (.symbol head :: (sourceEvaluated ++ [slot])) sourcePending)
    (callLiveSupported : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList callLive,
      name ∈ PersistentSupport before)
    (tupleLiveSupported : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList tupleLive,
      name ∈ PersistentSupport before)
    (packetSupported :
      (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
          ((heFront ++ .symbol head :: evaluated.map Entry.Value.erase) ++
            annotated.map Entry.Value.erase ++ hePending),
        name ∈ PersistentSupport before) ∧
      (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
          ((sourceFront ++ .symbol head :: sourceEvaluated) ++
            rows.map Prod.fst ++ sourcePending),
        name ∈ PersistentSupport before))
    {headResults : List HE.Spec.Eval.Completed.Result}
    (headRelated : List.Forall₂
      (OutcomeRel program scope
        (heFront ++ .symbol head :: evaluated.map Entry.Value.erase)
        (sourceFront ++ .symbol head :: sourceEvaluated)
        (annotated.map Entry.Value.erase ++ hePending)
        (rows.map Prod.fst ++ sourcePending) slot
        (evaluationGoals rows ++ final :: older) before)
      headResults heads)
    :
    ∃ tupleRows raw,
      TupleBranchesRel (equationSpace program) noForeign rawLookup tupleLive machineScope
        annotated headResults tupleRows (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      CallsRel (equationSpace program) noForeign rawLookup callLive machineScope
        Atom.undefinedType (tupleRows.map (assemblePrefix (.symbol head :: evaluated))) raw
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program scope heFront sourceFront hePending sourcePending
        destination older before) raw outcomes := by
  match source with
  | .nil =>
      cases headRelated
      exact ⟨[],[],.nil,.nil,.nil⟩
  | @ArgumentBranches.cons _ headControl headControls rows assembled destination final older
      children restControls first remaining =>
      cases headRelated with
      | @cons headResult _ tailResults _ one rest =>
          obtain ⟨headScope,scopeIncluded,headGoals,headMonotone,headScopeSupported,
            headBindingsSupported,headDestinationSupported,headValid,headSafe,headPassive,
            headPacket⟩ := one
          have weakenedInstances : List.Forall₂ (InputInstance program headScope)
              (rows.map Prod.fst) annotated := inputInstances_weaken instances scopeIncluded
          have weakenedValues : ∀ value ∈ evaluated,
              Value program value.erase headScope ∧ NoErrorSymbol value.erase := by
            intro value member
            exact ⟨(evaluatedValues value member).1.weaken scopeIncluded,
              (evaluatedValues value member).2⟩
          have extendedValues : ∀ value ∈ evaluated ++ [headResult.1],
              Value program value.erase headScope ∧ NoErrorSymbol value.erase := by
            intro value member
            rcases List.mem_append.mp member with old | latest
            · exact weakenedValues value old
            · obtain rfl := List.mem_singleton.mp latest
              exact ⟨headValid,headSafe⟩
          have tailSupport : SupportRel headScope callLive
              headResult.2.bindings
              (heFront ++ (.symbol head :: (evaluated ++ [headResult.1])).map Entry.Value.erase ++
                annotated.map Entry.Value.erase ++ hePending)
              (sourceFront ++ (.symbol head :: (sourceEvaluated ++ [slot])) ++
                rows.map Prod.fst ++ sourcePending) headControl := by
            refine ⟨headScopeSupported,?_,headBindingsSupported,?_,?_⟩
            · intro name member
              exact headMonotone (callLiveSupported name member)
            · intro name member
              have inserted := typeVarsList_insert_supported
                (front := heFront ++ .symbol head :: evaluated.map Entry.Value.erase)
                (suffix := annotated.map Entry.Value.erase ++ hePending)
                (value := headResult.1.erase)
                (fun candidate oldMember => headMonotone
                  (packetSupported.1 candidate (by
                    simpa only [List.append_assoc] using oldMember)))
                (fun candidate valueMember => headScopeSupported candidate
                  (Mettapedia.Languages.MeTTa.Translation.OpenRecursive.Value.typeVars_mem_scope
                    headValid valueMember))
              apply inserted name
              simpa only [Entry.Value.erase,List.map_append,List.map_cons,List.map_nil,
                List.singleton_append,List.cons_append,List.append_assoc] using member
            · intro name member
              have inserted := typeVarsList_insert_supported
                (front := sourceFront ++ .symbol head :: sourceEvaluated)
                (suffix := rows.map Prod.fst ++ sourcePending) (value := slot)
                (fun candidate oldMember => headMonotone
                  (packetSupported.2 candidate (by
                    simpa only [List.append_assoc] using oldMember)))
                (fun candidate slotMember => headDestinationSupported candidate slotMember)
              apply inserted name
              simpa only [List.singleton_append,List.cons_append,List.append_assoc] using member
          have tailRelated : HE.Spec.Bindings.ScopeObservation.observedTuples headResult.2.bindings
              (heFront ++ (.symbol head :: (evaluated ++ [headResult.1])).map Entry.Value.erase ++
                annotated.map Entry.Value.erase ++ hePending) =
            solutionTuples headControl.bindings
              (sourceFront ++ (.symbol head :: (sourceEvaluated ++ [slot])) ++
                rows.map Prod.fst ++ sourcePending) := by
            simpa only [Entry.Value.erase,List.map_append,List.map_cons,List.map_nil,
              List.nil_append,List.singleton_append,List.cons_append,List.append_assoc] using headPacket
          obtain ⟨children,firstRaw,tailTuple,firstCalls,firstRelated⟩ := Arguments.forward first
            patterns programCode machineScope (headResult.1.erase :: tupleLive) callLive headScope
            headResult.2 head ordinary annotated (evaluated ++ [headResult.1])
            (sourceEvaluated ++ [slot]) weakenedInstances extendedValues assembledShape
            heFront sourceFront hePending sourcePending frontLength
            (by simp [evaluatedLength]) tailRelated headPassive tailSupport
            allocated.1 (by
              intro name member
              simp only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList,List.mem_append] at member
              rcases member with valueMember | liveMember
              · exact headScopeSupported name
                  (Mettapedia.Languages.MeTTa.Translation.OpenRecursive.Value.typeVars_mem_scope
                    headValid valueMember)
              · exact headMonotone (tupleLiveSupported name liveMember))
          obtain ⟨restRows,restRaw,restTuple,restCalls,restRelated⟩ := ArgumentBranches.forward remaining
            patterns programCode machineScope tupleLive callLive scope before head ordinary evaluated
            annotated slot heFront sourceFront sourceEvaluated hePending sourcePending frontLength
            evaluatedLength assembledShape evaluatedValues instances allocated.2 callLiveSupported
            tupleLiveSupported packetSupported rest
          have rebased := outcomes_rebase (program := program) (scope := scope)
            (middleScope := headScope) scopeIncluded headMonotone firstRelated
          refine ⟨children.map (tuplePrepend headResult.1) ++ restRows,firstRaw ++ restRaw,
            .continuing headValid.not_stopped tailTuple restTuple,?_,?_⟩
          · simpa only [List.map_append,List.map_map,Function.comp_def,
              List.cons_append,←assemblePrefix_snoc] using firstCalls.append restCalls
          · exact List.rel_append rebased restRelated
termination_by structural source

theorem Invocation.forward
    {program : Program} {control : Control} {assembled destination : Atom}
    {final : Goal} {older : List Goal} {outcomes : List Control}
    (source : Invocation program control assembled destination final older outcomes)
    (patterns : ConstructorPatterns program) (programCode : CodeProgram program)
    (machineScope : List String) (live : List Atom) (scope : List String) (frame : Frame)
    (head : String) (evaluated : List Entry.Value) (sourceArguments : List Atom)
    (argumentValues : ∀ value ∈ evaluated,
      Value program value.erase scope ∧ NoErrorSymbol value.erase)
    (assembledShape : assembled = .expression (.symbol head :: sourceArguments))
    (heFront sourceFront hePending sourcePending : List Atom)
    (frontLength : heFront.length = sourceFront.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
      (heFront ++ (Entry.Value.expression .active (.symbol head :: evaluated)).erase :: hePending) =
      solutionTuples control.bindings
        (sourceFront ++ .expression (.symbol head :: sourceArguments) :: sourcePending))
    (passive : PassiveEnvironment program scope frame.environment)
    (supported : SupportRel scope live frame.bindings
      (heFront ++ (Entry.Value.expression .active (.symbol head :: evaluated)).erase :: hePending)
      (sourceFront ++ .expression (.symbol head :: sourceArguments) :: sourcePending) control)
    (allocated : source.Allocated sourceFront sourcePending) :
    ∃ raw,
      CallRel (equationSpace program) noForeign rawLookup live machineScope
        (.expression .active (.symbol head :: evaluated)) Atom.undefinedType frame raw
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program scope heFront sourceFront hePending sourcePending
        destination older control) raw outcomes := by
  match source with
  | @Invocation.constructor _ control selectedHead selectedArguments destination older after
      constructor privateDestination atGoal accepted =>
      have assembledChildren : .symbol selectedHead :: selectedArguments =
          .symbol head :: sourceArguments := Atom.expression.inj assembledShape
      have selectedHeadEq : selectedHead = head :=
        Atom.symbol.inj (List.cons.inj assembledChildren).1
      have selectedArgumentsEq : selectedArguments = sourceArguments :=
        (List.cons.inj assembledChildren).2
      subst head
      subst sourceArguments
      exact constructor_invocation_forward program scope machineScope live selectedHead selectedArguments evaluated
        constructor argumentValues frame passive control destination older privateDestination heFront sourceFront
        hePending sourcePending related supported allocated accepted
  | @Invocation.equations _ control extra selectedHead selectedArguments destination older environment selected outcomes
      defined privateDestination atGoal resolved resolvedSupported sourceFrontier nonempty bodies =>
      have assembledChildren : .symbol selectedHead :: selectedArguments =
          .symbol head :: sourceArguments := Atom.expression.inj assembledShape
      have selectedHeadEq : selectedHead = head :=
        Atom.symbol.inj (List.cons.inj assembledChildren).1
      have selectedArgumentsEq : selectedArguments = sourceArguments :=
        (List.cons.inj assembledChildren).2
      subst head
      subst sourceArguments
      obtain ⟨packetFresh,bodiesAllocated⟩ := allocated
      let query : Atom := (Entry.Value.expression .active (.symbol selectedHead :: evaluated)).erase
      have frontierSupport : SupportRel scope (Atom.undefinedType :: live) frame.bindings
          (heFront ++ query :: hePending)
          (sourceFront ++ .expression (.symbol selectedHead :: selectedArguments) :: sourcePending) control := by
        refine ⟨supported.scope,?_,supported.incoming,?_,supported.sourcePacket⟩
        · intro name member
          apply supported.live name
          simpa only [HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
            HE.Spec.Type.Presentation.TypeSubst.typeVars,Atom.undefinedType,List.nil_append,
            List.mem_append] using member
        · simpa only [query] using supported.hePacket
      obtain ⟨works,frontier,paired⟩ := equation_invocation_frontier program control extra selectedHead
        selectedArguments destination older environment resolved (Atom.undefinedType :: live) query
        frame.bindings heFront sourceFront hePending sourcePending frontLength
        (by simpa only [query] using related) frontierSupport
        resolvedSupported sourceFrontier
      have allValues : ∀ child ∈ (.symbol selectedHead :: evaluated),
          Value program child.erase scope ∧ NoErrorSymbol child.erase := by
        intro child member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨by simpa only [Entry.Value.erase] using
              (defined.1.symbol_value (program := program) (scope := scope)),
            by simpa only [Entry.Value.erase] using
              (NoErrorSymbol.symbol (fun same => defined.1.2.2 (by simp [same])))⟩
        · exact argumentValues child member
      have protectMono : PersistentSupport control ⊆
          PersistentSupport (protectControl control extra) := by
        rw [persistentSupport_protectControl]
        exact Finset.subset_union_left
      have guardedSupport := supported.mono protectMono
      have callerFacts :
          (∀ name ∈ scope, name ∈ PersistentSupport (protectControl control extra)) ∧
          (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList live,
            name ∈ PersistentSupport (protectControl control extra)) ∧
          (∀ name ∈ HE.Spec.Bindings.ScopeObservation.specBindingVars frame.bindings,
            name ∈ PersistentSupport (protectControl control extra)) ∧
          (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList (heFront ++ hePending),
            name ∈ PersistentSupport (protectControl control extra)) ∧
          (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
              (sourceFront ++ sourcePending),
            name ∈ PersistentSupport (protectControl control extra)) := by
        refine ⟨guardedSupport.scope,guardedSupport.live,guardedSupport.incoming,?_,?_⟩
        · intro name member
          apply guardedSupport.hePacket
          rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append] at member
          rcases List.mem_append.mp member with frontMember | pendingMember
          · rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append]
            exact List.mem_append_left _ frontMember
          · rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append]
            exact List.mem_append_right _ (List.mem_append_right _ pendingMember)
        · intro name member
          apply guardedSupport.sourcePacket
          rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append] at member
          rcases List.mem_append.mp member with frontMember | pendingMember
          · rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append]
            exact List.mem_append_left _ frontMember
          · rw [HE.Spec.Type.Presentation.TypeSubst.typeVarsList_append]
            exact List.mem_append_right _ (List.mem_append_right _ pendingMember)
      obtain ⟨raw,completed,guardedRelated⟩ := Bodies.forward bodies patterns programCode scope
        machineScope live (protectControl control extra) frame selectedHead defined.1 evaluated
        (.expression (.symbol selectedHead :: selectedArguments.map (read environment)))
        heFront sourceFront hePending sourcePending frontLength argumentValues passive bodiesAllocated
        callerFacts frontier (fun _ member => member) paired
      have rawRelated := outcomes_rebase (program := program) (scope := scope)
        (middleScope := scope) (fun _ member => member) protectMono guardedRelated
      have worksNonempty : works ≠ [] := by
        intro empty
        rw [empty] at paired
        exact nonempty (List.forall₂_nil_right_iff.mp paired)
      refine ⟨raw,.equations ?_ ?_ frontier worksNonempty completed,rawRelated⟩
      · have clean : selectedHead ≠ "Error" := fun same => defined.1.2.2 (by simp [same])
        simp [Entry.Value.erase,HE.Spec.Eval.IsErrorRel,clean]
      · simpa only [Entry.Value.erase,List.map_cons] using
          (defined.1.he_non_grounded (evaluated.map Entry.Value.erase))
termination_by structural source

theorem Bodies.forward
    {program : Program} {destination : Atom} {older : List Goal}
    {selected : List (Nat × Control)} {outcomes : List Control}
    (source : Bodies program destination older selected outcomes)
    (patterns : ConstructorPatterns program) (programCode : CodeProgram program)
    (scope machineScope : List String) (live : List Atom) (before : Control) (frame : Frame)
    (head : String) (ordinary : OrdinaryHead head) (evaluated : List Entry.Value)
    (sourceQuery : Atom) (heFront sourceFront hePending sourcePending : List Atom)
    (frontLength : heFront.length = sourceFront.length)
    (evaluatedValues : ∀ value ∈ evaluated,
      Value program value.erase scope ∧ NoErrorSymbol value.erase)
    (passive : PassiveEnvironment program scope frame.environment)
    (allocated : source.Allocated sourceFront sourcePending)
    (callerSupport :
      (∀ name ∈ scope, name ∈ PersistentSupport before) ∧
      (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList live,
        name ∈ PersistentSupport before) ∧
      (∀ name ∈ HE.Spec.Bindings.ScopeObservation.specBindingVars frame.bindings,
        name ∈ PersistentSupport before) ∧
      (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList (heFront ++ hePending),
        name ∈ PersistentSupport before) ∧
      (∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
          (sourceFront ++ sourcePending), name ∈ PersistentSupport before))
    {allWorks works : List HE.Spec.Eval.Steps.EquationWork}
    (frontier : HE.Spec.Eval.Steps.EquationFrontierRel (equationSpace program)
      (Atom.undefinedType :: live) (Entry.Value.expression .active (.symbol head :: evaluated)).erase
      frame.bindings allWorks)
    (included : ∀ work ∈ works, work ∈ allWorks)
    (paired : List.Forall₂ (ClausePendingAgreement before sourceQuery destination older
      (heFront ++ hePending) (sourceFront ++ sourcePending)) selected works) :
    ∃ raw,
      EquationBodiesRel (equationSpace program) noForeign rawLookup live machineScope
        (.expression .active (.symbol head :: evaluated)) Atom.undefinedType frame works raw
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program scope heFront sourceFront hePending sourcePending
        destination older before) raw outcomes := by
  match source with
  | .nil =>
      cases paired
      exact ⟨[],.nil,.nil⟩
  | @Bodies.cons _ destination older position selected remaining body children rest atGoal first later =>
      cases paired with
      | @cons selectedPair work selectedTail workTail agreement agreements =>
          have present : work ∈ allWorks := included work List.mem_cons_self
          obtain ⟨matched,occurrence⟩ := frontier.occurrence present
          have candidate : HE.Spec.Eval.Steps.UnifyCandidateRel
              (Entry.Value.expression .active (.symbol head :: evaluated)).erase work.pattern
              frame.bindings work.bindings := ⟨matched,occurrence.selected.2,occurrence.result.1⟩
          obtain ⟨valueEnvironment,unified,certified⟩ :=
            Entry.Value.UnifyRel.of_source_candidate
              (policy := HE.Spec.Eval.Completed.Policy.unmarked.rebuilding)
              (left := Entry.Value.expression .active (.symbol head :: evaluated))
              (right := Entry.Value.ofAtom work.pattern)
              frame.certified (by simpa only [Entry.Value.erase_ofAtom] using candidate)
          let after : Frame := ⟨work.bindings,valueEnvironment,certified⟩
          have childValues : ∀ child ∈ (.symbol head :: evaluated),
              Value program child.erase scope ∧ NoErrorSymbol child.erase := by
            intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨by simpa only [Entry.Value.erase] using
                  (ordinary.symbol_value (program := program) (scope := scope)),
                by simpa only [Entry.Value.erase] using
                  (NoErrorSymbol.symbol (fun same => ordinary.2.2 (by simp [same])))⟩
            · exact evaluatedValues child member
          have entered := patterns.clause_entry programCode frontier present
            HE.Spec.Eval.Completed.Policy.unmarked after passive childValues unified
          let clauseScope := scope ++ HE.Spec.Type.Presentation.TypeSubst.typeVars work.pattern
          have rawBodyCode : CodeRel program clauseScope (Entry.Value.ofAtom work.body) :=
            (programCode.work_body_code frontier present).weaken
              (fun _ member => List.mem_append_right _ member)
          have bodyInstance : InputInstance program clauseScope work.body
              (after.read HE.Spec.Eval.Completed.Policy.unmarked (Entry.Value.ofAtom work.body)) :=
            InputInstance.of_read rawBodyCode after entered.1
          have beforeToSelected : PersistentSupport before ⊆ PersistentSupport selected :=
            Mettapedia.Languages.MeTTa.Translation.OpenRecursive.ClausePendingAgreement.persistent_mono
              agreement
          have clauseNameSupported : ∀ name ∈ clauseScope,
              name ∈ PersistentSupport selected := by
            intro name member
            rcases List.mem_append.mp member with old | fresh
            · exact beforeToSelected (callerSupport.1 name old)
            · exact Mettapedia.Languages.MeTTa.Translation.OpenRecursive.ClausePendingAgreement.pattern_supported
                agreement fresh
          have clauseSupport : SupportRel clauseScope live work.bindings
              ((after.read HE.Spec.Eval.Completed.Policy.unmarked
                (Entry.Value.ofAtom work.body)).erase :: heFront ++ hePending)
              (work.body :: sourceFront ++ sourcePending) selected := by
            refine ⟨?_,?_,?_,?_,?_⟩
            · exact clauseNameSupported
            · intro name member
              exact beforeToSelected (callerSupport.2.1 name member)
            · intro name member
              rw [unifyCandidate_support candidate name] at member
              rcases member with old | queryVar | patternVar
              · exact beforeToSelected (callerSupport.2.2.1 name old)
              · have queryChildren : name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
                    (.symbol head :: evaluated.map Entry.Value.erase) := by
                  simpa only [Entry.Value.erase,List.map_cons,
                    HE.Spec.Type.Presentation.TypeSubst.typeVars] using queryVar
                obtain ⟨child,childMember,childVar⟩ :=
                  HE.Spec.Type.Presentation.Freshness.exists_mem_of_mem_typeVarsList queryChildren
                rcases List.mem_cons.mp childMember with rfl | argumentMember
                · simp [HE.Spec.Type.Presentation.TypeSubst.typeVars] at childVar
                · obtain ⟨value,present,rfl⟩ := List.mem_map.mp argumentMember
                  exact beforeToSelected (callerSupport.1 name
                    (Mettapedia.Languages.MeTTa.Translation.OpenRecursive.Value.typeVars_mem_scope
                      (evaluatedValues value present).1 childVar))
              · exact Mettapedia.Languages.MeTTa.Translation.OpenRecursive.ClausePendingAgreement.pattern_supported
                  agreement patternVar
            · intro name member
              exact typeVarsList_cons_supported
                (fun candidate bodyVar => clauseNameSupported candidate
                  (entered.2.vars_covered candidate bodyVar))
                (fun candidate pendingVar => beforeToSelected
                  (callerSupport.2.2.2.1 candidate pendingVar)) name member
            · intro name member
              exact typeVarsList_cons_supported
                (fun candidate bodyVar => clauseNameSupported candidate
                  (rawBodyCode.vars_covered candidate (by
                    simpa only [Entry.Value.erase_ofAtom] using bodyVar)))
                (fun candidate pendingVar => beforeToSelected
                  (callerSupport.2.2.2.2 candidate pendingVar)) name member
          have bodyRelated : HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings
              ((after.read HE.Spec.Eval.Completed.Policy.unmarked
                (Entry.Value.ofAtom work.body)).erase :: heFront ++ hePending) =
            solutionTuples selected.bindings (work.body :: sourceFront ++ sourcePending) := by
            have rawObserved : HE.Spec.Bindings.ScopeObservation.observedTuples after.bindings
                ((Entry.Value.ofAtom work.body).erase :: heFront ++ hePending) =
              solutionTuples selected.bindings (work.body :: sourceFront ++ sourcePending) := by
              simpa only [after,Entry.Value.erase_ofAtom,List.cons_append] using agreement.observations
            exact (observed_read_coordinate HE.Spec.Eval.Completed.Policy.unmarked after []
              (heFront ++ hePending) (Entry.Value.ofAtom work.body)).trans rawObserved
          have bodyRelatedAt := joint_packet_unfocus_coordinate frontLength bodyRelated
          have bodySupportAt := clauseSupport.unfocus
          have bodyEq : body = work.body := by
            have same := atGoal.symm.trans agreement.goals
            exact (Goal.evaluate.inj (List.cons.inj same).1).1
          have actualBodyInstance : InputInstance program clauseScope body
              (after.read HE.Spec.Eval.Completed.Policy.unmarked (Entry.Value.ofAtom work.body)) := by
            simpa only [bodyEq] using bodyInstance
          have actualBodyRelated : HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings
              (heFront ++ (after.read HE.Spec.Eval.Completed.Policy.unmarked
                (Entry.Value.ofAtom work.body)).erase :: hePending) =
            solutionTuples selected.bindings (sourceFront ++ body :: sourcePending) := by
            simpa only [bodyEq] using bodyRelatedAt
          have actualBodySupport : SupportRel clauseScope live work.bindings
              (heFront ++ (after.read HE.Spec.Eval.Completed.Policy.unmarked
                (Entry.Value.ofAtom work.body)).erase :: hePending)
              (sourceFront ++ body :: sourcePending) selected := by
            simpa only [bodyEq] using bodySupportAt
          obtain ⟨firstRaw,bodyCompleted,firstRelated⟩ := Evaluation.forward first patterns programCode
            machineScope live clauseScope after
            (after.read HE.Spec.Eval.Completed.Policy.unmarked (Entry.Value.ofAtom work.body))
            actualBodyInstance entered.1 heFront sourceFront hePending sourcePending frontLength
            actualBodyRelated actualBodySupport allocated.1
          have returned : ReturnRel (equationSpace program) noForeign rawLookup live machineScope
              (.expression .active (.symbol head :: evaluated)) Atom.undefinedType
              (after.read HE.Spec.Eval.Completed.Policy.unmarked (Entry.Value.ofAtom work.body))
              after firstRaw (policy := HE.Spec.Eval.Completed.Policy.unmarked) :=
            .evaluate
              (Mettapedia.Languages.MeTTa.Translation.OpenRecursive.CodeRel.not_refusal entered.2)
              (Mettapedia.Languages.MeTTa.Translation.OpenRecursive.CodeRel.not_stopped entered.2)
              bodyCompleted
          obtain ⟨restRaw,tail,restRelated⟩ := Bodies.forward later patterns programCode scope machineScope
            live before frame head ordinary evaluated sourceQuery heFront sourceFront hePending sourcePending
            frontLength evaluatedValues passive allocated.2 callerSupport frontier
            (fun work member => included work (List.mem_cons_of_mem _ member)) agreements
          have rebased := outcomes_rebase (program := program) (scope := scope)
            (middleScope := clauseScope)
            (fun name member => List.mem_append_left _ member) beforeToSelected firstRelated
          exact ⟨firstRaw ++ restRaw,
            .ordinary_cons rfl unified
              (Mettapedia.Languages.MeTTa.Translation.OpenRecursive.CodeRel.not_function_pending
                entered.2 HE.Spec.Eval.Completed.Policy.unmarked) returned tail,
            List.rel_append rebased restRelated⟩
termination_by structural source
end

/-- The reached joint observations of contextual results, in result-occurrence
order.  Each element is the complete model set for the returned value together
with the caller packet. -/
def observedOutcomePackets (hePrefix hePending : List Atom)
    (results : List HE.Spec.Eval.Completed.Result) : List (Set (List Atom)) :=
  results.map fun result =>
    HE.Spec.Bindings.ScopeObservation.observedTuples result.2.bindings
      (hePrefix ++ result.1.erase :: hePending)

/-- The corresponding reached observations at the source controls, retaining
the same occurrence order. -/
def solutionOutcomePackets (sourcePrefix sourcePending : List Atom) (destination : Atom)
    (outcomes : List Control) : List (Set (List Atom)) :=
  outcomes.map fun source =>
    solutionTuples source.bindings (sourcePrefix ++ destination :: sourcePending)

/-- Pointwise outcome correspondence preserves the complete ordered list of
joint observations.  In particular, equal observations at distinct source
occurrences remain distinct list entries. -/
theorem OutcomeRel.packet_list_eq
    {program : Program} {scope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom} {destination : Atom}
    {older : List Goal} {before : Control}
    {results : List HE.Spec.Eval.Completed.Result} {outcomes : List Control}
    (related : List.Forall₂
      (OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending
        destination older before) results outcomes) :
    observedOutcomePackets hePrefix hePending results =
      solutionOutcomePackets sourcePrefix sourcePending destination outcomes := by
  induction related with
  | nil => rfl
  | cons row _rows inductionHypothesis =>
      obtain ⟨_outScope,_scopeOut,_goals,_monotone,_scopeSupported,
        _bindingsSupported,_destinationSupported,_valid,_safe,_passive,packet⟩ := row
      unfold observedOutcomePackets solutionOutcomePackets
      simp only [List.map_cons]
      exact congrArg₂ List.cons packet inductionHypothesis

/-- Forgetting order from the preceding theorem preserves occurrence
multiplicity rather than deduplicating equal observations. -/
theorem OutcomeRel.packet_bag_eq
    {program : Program} {scope : List String}
    {hePrefix sourcePrefix hePending sourcePending : List Atom} {destination : Atom}
    {older : List Goal} {before : Control}
    {results : List HE.Spec.Eval.Completed.Result} {outcomes : List Control}
    (related : List.Forall₂
      (OutcomeRel program scope hePrefix sourcePrefix hePending sourcePending
        destination older before) results outcomes) :
    (observedOutcomePackets hePrefix hePending results : Multiset (Set (List Atom))) =
      (solutionOutcomePackets sourcePrefix sourcePending destination outcomes :
        Multiset (Set (List Atom))) :=
  congrArg (fun packets : List (Set (List Atom)) =>
    (packets : Multiset (Set (List Atom)))) (OutcomeRel.packet_list_eq related)

/-- Principal E2 transport theorem.  An admitted finite open source tree earns
the contextual HE derivation, an ordered occurrence correspondence, and a
source branch path to every reached outcome.  Executable DFS queue
linearization is deliberately a separate theorem. -/
theorem Evaluation.transport
    {program : Program} {control : Control} {sourceValue destination : Atom}
    {older : List Goal} {outcomes : List Control}
    (source : Evaluation program control sourceValue destination older outcomes)
    (patterns : ConstructorPatterns program) (programCode : CodeProgram program)
    (machineScope : List String) (live : List Atom) (scope : List String)
    (frame : Frame) (input : Entry.Value)
    (sourceInstance : InputInstance program scope sourceValue input)
    (passive : PassiveEnvironment program scope frame.environment)
    (heFront sourceFront hePending sourcePending : List Atom)
    (frontLength : heFront.length = sourceFront.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (heFront ++ input.erase :: hePending) =
      solutionTuples control.bindings (sourceFront ++ sourceValue :: sourcePending))
    (supported : SupportRel scope live frame.bindings
      (heFront ++ input.erase :: hePending)
      (sourceFront ++ sourceValue :: sourcePending) control)
    (allocated : source.Allocated sourceFront sourcePending) :
    ∃ results,
      AtomRel (equationSpace program) noForeign rawLookup live machineScope input
        Atom.undefinedType frame results
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program scope heFront sourceFront hePending sourcePending
        destination older control) results outcomes ∧
      (∀ outcome ∈ outcomes, BranchPath program control outcome) ∧
      observedOutcomePackets heFront hePending results =
        solutionOutcomePackets sourceFront sourcePending destination outcomes := by
  obtain ⟨results,completed,outcomesRelated⟩ := source.forward patterns programCode
    machineScope live scope frame input sourceInstance passive heFront sourceFront
    hePending sourcePending frontLength related supported allocated
  exact ⟨results,completed,outcomesRelated,source.paths,
    OutcomeRel.packet_list_eq outcomesRelated⟩

namespace CollectionLinearization

/-- Principal E2/E3 composition theorem.  One admitted open recursive source
tree earns both its contextual HE derivation and its exact retained DFS queue
drain.  The only scheduling premise is the structural freshening synchronization
computed from the source tree and queue-support indices. -/
theorem Evaluation.realize_root
    {Context : Type} {program : Program} {control : Control}
    {sourceValue destination : Atom}
    {outcomes : List Control}
    (source : OpenRecursive.Evaluation program control sourceValue destination [] outcomes)
    (patterns : ConstructorPatterns program) (programCode : CodeProgram program)
    (machineScope : List String) (live : List Atom) (scope : List String)
    (frame : Frame) (input : Entry.Value)
    (sourceInstance : InputInstance program scope sourceValue input)
    (passive : PassiveEnvironment program scope frame.environment)
    (heFront sourceFront hePending sourcePending : List Atom)
    (frontLength : heFront.length = sourceFront.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples frame.bindings
        (heFront ++ input.erase :: hePending) =
      solutionTuples control.bindings (sourceFront ++ sourceValue :: sourcePending))
    (supported : SupportRel scope live frame.bindings
      (heFront ++ input.erase :: hePending)
      (sourceFront ++ sourceValue :: sourcePending) control)
    (allocated : source.Allocated sourceFront sourcePending)
    (pSupp cSupp : Finset String)
    (sync : Evaluation.ExtraSynchronized source pSupp cSupp
      (outcomes.map rawAnswerSupport)) :
    ∃ results,
      AtomRel (equationSpace program) noForeign rawLookup live machineScope input
        Atom.undefinedType frame results
        (policy := HE.Spec.Eval.Completed.Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program scope heFront sourceFront hePending sourcePending
        destination [] control) results outcomes ∧
      (∀ outcome ∈ outcomes, BranchPath program control outcome) ∧
      observedOutcomePackets heFront hePending results =
        solutionOutcomePackets sourceFront sourcePending destination outcomes ∧
      RootContinuationContract (Context := Context) program [] [] control pSupp cSupp outcomes
        (cSupp ∪ supportIncrement (outcomes.map rawAnswerSupport)) := by
  obtain ⟨results,completed,outcomesRelated,paths,packets⟩ :=
    OpenRecursive.Evaluation.transport source patterns programCode machineScope live scope
      frame input sourceInstance passive heFront sourceFront hePending sourcePending
      frontLength related supported allocated
  exact ⟨results,completed,outcomesRelated,paths,packets,
    Evaluation.root_drain source pSupp cSupp sync⟩

#print axioms Evaluation.realize_root

end CollectionLinearization

#print axioms Evaluation.paths
#print axioms Evaluation.forward
#print axioms Arguments.forward
#print axioms ArgumentBranches.forward
#print axioms Invocation.forward
#print axioms Bodies.forward
#print axioms OutcomeRel.packet_list_eq
#print axioms OutcomeRel.packet_bag_eq
#print axioms Evaluation.transport

end Mettapedia.Languages.MeTTa.Translation.OpenRecursive

namespace Mettapedia.Languages.MeTTa.Translation.OpenRecursive.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
open Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
open Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.Source
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
open Mettapedia.Languages.MeTTa.Translation.PureConstructor
open Mettapedia.Languages.MeTTa.Translation.ConstructorMatch
open Mettapedia.Languages.MeTTa.Translation.OpenRecursive.CollectionLinearization

/-!
The positive control below exercises open argument materialization, duplicate
physical clause occurrences, recursive bodies and constructor assembly in one
finite source tree. Its negative packet assertion complements the admission
separators PureConstructor.RecursiveControls.active_clause_pattern_rejected
and OpenContinuation.ActiveBindingControls.active_binding_separates_dispatch.
-/

open PureConstructor.RecursiveControls

private def query : Atom := .expression [.symbol "fork",.var "x"]

private def rootControl : Control :=
  { bindings := [(.var "x", .symbol "Z")]
    goals := [.evaluate query (.var "out")]
    destination := .var "out"
    reserved := {"x"} }

private def rootSlot : Atom := .var (freshName rootControl 0)

private def rootOpened : Control :=
  prepare .eagerValue program rootControl query (.var "out") []

private theorem rootPrepared :
    Prepared .eagerValue program rootControl (.var "out") [] query rootOpened :=
  prepare_has_source _ _ _ _ _ _

private theorem rootPrepared_delimited : PreparedDelimitedRel rootPrepared := by
  let canonical := Prepared.application (policy := Policy.eagerValue)
    (program := program) (control := rootControl) (destination := (.var "out" : Atom))
    (older := []) "fork" [.var "x"] (by rfl) (by rfl)
  exact PreparedDelimitedRel.of_source rootPrepared canonical
    (PreparedDelimitedRel.application "fork" [.var "x"] (by rfl) (by rfl))

private theorem rootOpened_bindings :
    rootOpened.bindings = [(.var "x",.symbol "Z")] := by
  exact rootPrepared.retains_frame.1.trans rfl

private def rootArgumentAfter : Control :=
  { rootOpened with
    bindings := rootOpened.bindings ++ [(.var "x",rootSlot)]
    goals := [.invoke "fork" [rootSlot] (.var "out")] }

private def rootPrivate :
    PrivateDestination rootControl query (.var "out") [] := by
  refine ⟨"out",rfl,?_,?_⟩ <;> decide +kernel

private def rootArgumentPrivate :
    PrivateDestination rootOpened (.var "x") rootSlot
      [.invoke "fork" [rootSlot] (.var "out")] := by
  refine ⟨freshName rootControl 0,rfl,?_,?_⟩ <;> decide +kernel

private def zeroEnvironment : Environment :=
  fun _ => encode (.symbol "Z")

private theorem read_zero_var (name : String) :
    read zeroEnvironment (.var name) = .symbol "Z" := by
  rw [read_eq_applyTypeValuation]
  simp [HE.Spec.Type.RuntimeRefinement.applyTypeValuation,zeroEnvironment]

private theorem read_zero_symbol (name : String) :
    read zeroEnvironment (.symbol name) = .symbol name := by
  rw [read_eq_applyTypeValuation]
  simp [HE.Spec.Type.RuntimeRefinement.applyTypeValuation]

private theorem rootArgumentAccepted :
    Refinement rootOpened.bindings (.var "x") rootSlot
      (some rootArgumentAfter.bindings) := by
  apply Refinement.accepted zeroEnvironment
  · intro pair member
    rw [rootOpened_bindings] at member
    obtain rfl := List.mem_singleton.mp member
    exact (read_zero_var "x").trans (read_zero_symbol "Z").symm
  · simp [rootSlot,read_zero_var]

private def rootArgument :
    Evaluation program rootOpened (.var "x") rootSlot
      [.invoke "fork" [rootSlot] (.var "out")] [rootArgumentAfter] := by
  apply Evaluation.variable rootArgumentPrivate
  · rfl
  · simpa only [rootArgumentAfter,rootSlot] using rootArgumentAccepted

private theorem rootSolvable :
    ∃ environment, resolve rootArgumentAfter.bindings = some environment := by
  apply resolve_complete
  refine ⟨zeroEnvironment,?_⟩
  intro pair member
  simp only [rootArgumentAfter,rootOpened_bindings,List.mem_append,List.mem_singleton] at member
  rcases member with rfl | rfl
  · exact (read_zero_var "x").trans (read_zero_symbol "Z").symm
  · simp [rootSlot,read_zero_var]

/-- Source-level freshening choices for the recursive control fixture.  E2 is
parametric in this profile; E3 chooses the live retained-scope supports. -/
class FresheningProfile where
  rootExtra : Finset String
  stripExtra : Nat → Finset String

abbrev FresheningProfile.empty : FresheningProfile :=
  ⟨∅,fun _ => ∅⟩

section
variable [profile : FresheningProfile]
include profile

private def guardedRoot : Control :=
  protectControl rootArgumentAfter profile.rootExtra

private theorem guardedRoot_bindings :
    guardedRoot.bindings = [(.var "x",.symbol "Z"),(.var "x",rootSlot)] := by
  simp [guardedRoot,protectControl,rootArgumentAfter,rootOpened_bindings]

private def forkQuery : Atom := .expression [.symbol "fork",.symbol "Z"]

private def forkBindings (occurrence : Nat) : Equations :=
  guardedRoot.bindings ++
    [(forkQuery,ClauseChoice.freshPattern guardedRoot occurrence forkRule)]

private def forkChoice (occurrence : Nat) : Control :=
  { guardedRoot with
    bindings := forkBindings occurrence
    goals := [.evaluate (ClauseChoice.freshBody guardedRoot occurrence forkRule)
      (.var "out")] }

private theorem forkAccepted (occurrence : Nat) :
    Refinement guardedRoot.bindings forkQuery
      (ClauseChoice.freshPattern guardedRoot occurrence forkRule)
      (some (forkBindings occurrence)) := by
  apply Refinement.accepted zeroEnvironment
  · intro pair member
    rw [guardedRoot_bindings] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact (read_zero_var "x").trans (read_zero_symbol "Z").symm
    · simp [rootSlot,read_zero_var]
  · rw [read_eq_applyTypeValuation,read_eq_applyTypeValuation]
    simp [forkQuery,forkRule,ClauseChoice.freshPattern,ClauseChoice.pattern,
      HE.Spec.Type.RuntimeRefinement.renameTypeVars,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,zeroEnvironment]

private theorem forkFrontier :
    ClauseChoice.Frontier program guardedRoot "fork" [.symbol "Z"] (.var "out") []
      (List.range program.equations.length) [(2,forkChoice 2),(3,forkChoice 3)] := by
  apply ClauseChoice.Frontier.skip
  · exact .other base (by rfl) (by decide +kernel)
  apply ClauseChoice.Frontier.skip
  · exact .other stepRule (by rfl) (by decide +kernel)
  apply ClauseChoice.Frontier.keep
  · exact .selected forkRule (forkBindings 2) (by rfl) rfl (forkAccepted 2)
  apply ClauseChoice.Frontier.keep
  · exact .selected forkRule (forkBindings 3) (by rfl) rfl (forkAccepted 3)
  exact .nil

private theorem zero_solves_forkBindings (occurrence : Nat) :
    Solves zeroEnvironment (forkBindings occurrence) := by
  intro pair member
  simp only [forkBindings,List.mem_append,List.mem_singleton] at member
  rcases member with old | rfl
  · rw [guardedRoot_bindings] at old
    simp only [List.mem_cons,List.not_mem_nil,or_false] at old
    rcases old with rfl | rfl
    · exact (read_zero_var "x").trans (read_zero_symbol "Z").symm
    · simp [rootSlot,read_zero_var]
  · rw [read_eq_applyTypeValuation,read_eq_applyTypeValuation]
    simp [forkQuery,forkRule,ClauseChoice.freshPattern,ClauseChoice.pattern,
      HE.Spec.Type.RuntimeRefinement.renameTypeVars,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,zeroEnvironment]

private def forkVariable (occurrence : Nat) : String :=
  ClauseChoice.rename guardedRoot occurrence
    (ClauseChoice.clauseAtoms forkRule) "x"

private def forkBody (occurrence : Nat) : Atom :=
  .expression [.symbol "strip",.var (forkVariable occurrence)]

private theorem forkBody_eq (occurrence : Nat) :
    ClauseChoice.freshBody guardedRoot occurrence forkRule = forkBody occurrence := by
  simp [forkBody,forkVariable,forkRule,tailCall,ClauseChoice.freshBody,
    HE.Spec.Type.RuntimeRefinement.renameTypeVars]

private def stripOpened (occurrence : Nat) : Control :=
  prepare .eagerValue program (forkChoice occurrence) (forkBody occurrence)
    (.var "out") []

private theorem stripPrepared (occurrence : Nat) :
    Prepared .eagerValue program (forkChoice occurrence) (.var "out") []
      (forkBody occurrence) (stripOpened occurrence) :=
  prepare_has_source _ _ _ _ _ _

private theorem stripPrepared_delimited (occurrence : Nat) :
    PreparedDelimitedRel (stripPrepared occurrence) := by
  let canonical := Prepared.application (policy := Policy.eagerValue)
    (program := program) (control := forkChoice occurrence)
    (destination := (.var "out" : Atom)) (older := [])
    "strip" [.var (forkVariable occurrence)] (by rfl) (by rfl)
  exact PreparedDelimitedRel.of_source (stripPrepared occurrence) canonical
    (PreparedDelimitedRel.application "strip" [.var (forkVariable occurrence)]
      (by rfl) (by rfl))

private theorem stripOpened_bindings (occurrence : Nat) :
    (stripOpened occurrence).bindings = forkBindings occurrence := by
  exact (stripPrepared occurrence).retains_frame.1.trans rfl

private def stripSlot (occurrence : Nat) : Atom :=
  .var (freshName (forkChoice occurrence) 0)

private def stripArgumentAfter (occurrence : Nat) : Control :=
  { stripOpened occurrence with
    bindings := (stripOpened occurrence).bindings ++
      [(.var (forkVariable occurrence),stripSlot occurrence)]
    goals := [.invoke "strip" [stripSlot occurrence] (.var "out")] }

omit profile in
private theorem freshName_storeFresh (control : Control) (index : Nat) :
    ∀ pair ∈ control.bindings,
      freshName control index ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
        freshName control index ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2 := by
  intro pair present
  constructor <;> intro member
  · exact freshName_not_mem control index
      (persistentSupport_subset_support control
        (typeVars_mem_persistent_binding control pair present _ (List.mem_append_left _ member)))
  · exact freshName_not_mem control index
      (persistentSupport_subset_support control
        (typeVars_mem_persistent_binding control pair present _ (List.mem_append_right _ member)))

private theorem out_mem_guardedRoot_support : "out" ∈ guardedRoot.support := by
  apply persistentSupport_subset_support guardedRoot
  apply typeVars_mem_persistent_destination guardedRoot "out"
  have destination : guardedRoot.destination = .var "out" := by
    simp [guardedRoot,protectControl,rootArgumentAfter,
      rootPrepared.retains_frame.2.1,rootControl]
  rw [destination]
  simp [HE.Spec.Type.Presentation.TypeSubst.typeVars]

private theorem forkVariable_ne_out (occurrence : Nat) :
    forkVariable occurrence ≠ "out" := by
  intro same
  have fresh := ClauseChoice.rename_fresh guardedRoot occurrence
    (ClauseChoice.clauseAtoms forkRule) "x"
  apply fresh
  change forkVariable occurrence ∈ guardedRoot.support
  rw [same]
  exact out_mem_guardedRoot_support

omit profile in
private theorem rootSlot_ne_out : freshName rootControl 0 ≠ "out" := by
  intro same
  apply freshName_not_mem rootControl 0
  rw [same]
  apply persistentSupport_subset_support rootControl
  apply typeVars_mem_persistent_destination rootControl "out"
  simp [rootControl,HE.Spec.Type.Presentation.TypeSubst.typeVars]

private theorem forkVariable_mem_pattern (occurrence : Nat) :
    forkVariable occurrence ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars
      (ClauseChoice.freshPattern guardedRoot occurrence forkRule) := by
  simp [forkVariable,forkRule,ClauseChoice.freshPattern,ClauseChoice.pattern,
    HE.Spec.Type.RuntimeRefinement.renameTypeVars,
    HE.Spec.Type.Presentation.TypeSubst.typeVars,
    HE.Spec.Type.Presentation.TypeSubst.typeVarsList]

private theorem forkVariable_mem_choice_support (occurrence : Nat) :
    forkVariable occurrence ∈ (forkChoice occurrence).support := by
  apply persistentSupport_subset_support (forkChoice occurrence)
  apply typeVars_mem_persistent_binding (forkChoice occurrence)
    (forkQuery,ClauseChoice.freshPattern guardedRoot occurrence forkRule)
  · simp [forkChoice,forkBindings]
  · exact List.mem_append_right _ (forkVariable_mem_pattern occurrence)

private def stripPrivate (occurrence : Nat) :
    PrivateDestination (forkChoice occurrence) (forkBody occurrence) (.var "out") [] := by
  refine ⟨"out",rfl,?_,?_⟩
  · intro pair member
    simp only [forkChoice,forkBindings,List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · rw [guardedRoot_bindings] at old
      simp only [List.mem_cons,List.not_mem_nil,or_false] at old
      rcases old with rfl | rfl
      · simp [HE.Spec.Type.Presentation.TypeSubst.typeVars]
      · simp [rootSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
          rootSlot_ne_out.symm]
    · constructor
      · simp [forkQuery,HE.Spec.Type.Presentation.TypeSubst.typeVars,
          HE.Spec.Type.Presentation.TypeSubst.typeVarsList]
      · simpa [forkVariable,forkRule,ClauseChoice.freshPattern,ClauseChoice.pattern,
          HE.Spec.Type.RuntimeRefinement.renameTypeVars,
          HE.Spec.Type.Presentation.TypeSubst.typeVars,
          HE.Spec.Type.Presentation.TypeSubst.typeVarsList] using
          (forkVariable_ne_out occurrence).symm
  · simp [forkBody,HE.Spec.Type.Presentation.TypeSubst.typeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      (forkVariable_ne_out occurrence).symm]

private def stripArgumentPrivate (occurrence : Nat) :
    PrivateDestination (stripOpened occurrence) (.var (forkVariable occurrence))
      (stripSlot occurrence)
      [.invoke "strip" [stripSlot occurrence] (.var "out")] := by
  refine ⟨freshName (forkChoice occurrence) 0,rfl,?_,?_⟩
  · rw [stripOpened_bindings]
    exact freshName_storeFresh (forkChoice occurrence) 0
  · simp only [HE.Spec.Type.Presentation.TypeSubst.typeVars,List.mem_singleton]
    exact fun same => freshName_not_mem (forkChoice occurrence) 0
      (same ▸ forkVariable_mem_choice_support occurrence)

private theorem stripArgumentAccepted (occurrence : Nat) :
    Refinement (stripOpened occurrence).bindings (.var (forkVariable occurrence))
      (stripSlot occurrence) (some (stripArgumentAfter occurrence).bindings) := by
  apply Refinement.accepted zeroEnvironment
  · rw [stripOpened_bindings]
    exact zero_solves_forkBindings occurrence
  · simp [stripSlot,read_zero_var]

private def stripArgument (occurrence : Nat) :
    Evaluation program (stripOpened occurrence) (.var (forkVariable occurrence))
      (stripSlot occurrence)
      [.invoke "strip" [stripSlot occurrence] (.var "out")]
      [stripArgumentAfter occurrence] := by
  apply Evaluation.variable (stripArgumentPrivate occurrence)
  · rfl
  · simpa only [stripArgumentAfter,stripSlot] using stripArgumentAccepted occurrence

private theorem stripArgumentAfter_solvable (occurrence : Nat) :
    ∃ environment, resolve (stripArgumentAfter occurrence).bindings = some environment := by
  apply resolve_complete
  refine ⟨zeroEnvironment,?_⟩
  intro pair member
  simp only [stripArgumentAfter,List.mem_append,List.mem_singleton] at member
  rcases member with old | rfl
  · rw [stripOpened_bindings] at old
    exact zero_solves_forkBindings occurrence pair old
  · simp [stripSlot,read_zero_var]

private noncomputable def stripEnvironment (occurrence : Nat) : Environment :=
  Classical.choose (stripArgumentAfter_solvable occurrence)

private theorem stripResolved (occurrence : Nat) :
    resolve (stripArgumentAfter occurrence).bindings = some (stripEnvironment occurrence) :=
  Classical.choose_spec (stripArgumentAfter_solvable occurrence)

private theorem solved_forkBindings_reads_variable
    (occurrence : Nat) (environment : Environment)
    (solved : Solves environment (forkBindings occurrence)) :
    read environment (.var (forkVariable occurrence)) = .symbol "Z" := by
  have same := solved
    (forkQuery,ClauseChoice.freshPattern guardedRoot occurrence forkRule)
    (by simp [forkBindings])
  rw [read_eq_applyTypeValuation,read_eq_applyTypeValuation] at same
  simp [forkQuery,forkRule,ClauseChoice.freshPattern,
    ClauseChoice.pattern,HE.Spec.Type.RuntimeRefinement.renameTypeVars,
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at same
  simpa [read_eq_applyTypeValuation,HE.Spec.Type.RuntimeRefinement.applyTypeValuation,
    forkVariable,forkRule] using same.symm

private theorem solved_stripArgument_reads_slot
    (occurrence : Nat) (environment : Environment)
    (solved : Solves environment (stripArgumentAfter occurrence).bindings) :
    read environment (stripSlot occurrence) = .symbol "Z" := by
  have old : Solves environment (forkBindings occurrence) := by
    intro pair member
    apply solved pair
    simp [stripArgumentAfter,stripOpened_bindings,List.mem_append,member]
  have linked := solved
    (.var (forkVariable occurrence),stripSlot occurrence)
    (by simp [stripArgumentAfter])
  exact linked.symm.trans (solved_forkBindings_reads_variable occurrence environment old)

private def stripGuard (occurrence : Nat) : Control :=
  protectControl (stripArgumentAfter occurrence) (profile.stripExtra occurrence)

private def stripQuery : Atom := .expression [.symbol "strip",.symbol "Z"]

private def baseBindings (occurrence : Nat) : Equations :=
  (stripGuard occurrence).bindings ++
    [(stripQuery,ClauseChoice.freshPattern (stripGuard occurrence) 0 base)]

private def baseChoice (occurrence : Nat) : Control :=
  { stripGuard occurrence with
    bindings := baseBindings occurrence
    goals := [.evaluate (ClauseChoice.freshBody (stripGuard occurrence) 0 base)
      (.var "out")] }

private theorem baseAccepted (occurrence : Nat) :
    Refinement (stripGuard occurrence).bindings stripQuery
      (ClauseChoice.freshPattern (stripGuard occurrence) 0 base)
      (some (baseBindings occurrence)) := by
  apply Refinement.accepted zeroEnvironment
  · intro pair member
    change pair ∈ (stripArgumentAfter occurrence).bindings at member
    simp only [stripArgumentAfter,List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · rw [stripOpened_bindings] at old
      exact zero_solves_forkBindings occurrence pair old
    · simp [stripSlot,read_zero_var]
  · simp [stripQuery,base,boxed,ClauseChoice.freshPattern,ClauseChoice.pattern,
      HE.Spec.Type.RuntimeRefinement.renameTypeVars]

private theorem stepRefused (occurrence : Nat) :
    Refinement (stripGuard occurrence).bindings stripQuery
      (ClauseChoice.freshPattern (stripGuard occurrence) 1 stepRule) none := by
  apply Refinement.refused
  rintro ⟨environment,_solved,same⟩
  rw [read_eq_applyTypeValuation,read_eq_applyTypeValuation] at same
  simp [stripQuery,stepRule,ClauseChoice.freshPattern,ClauseChoice.pattern,
    HE.Spec.Type.RuntimeRefinement.renameTypeVars,
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at same

private theorem stripFrontier (occurrence : Nat) :
    ClauseChoice.Frontier program (stripGuard occurrence) "strip" [.symbol "Z"]
      (.var "out") [] (List.range program.equations.length)
      [(0,baseChoice occurrence)] := by
  apply ClauseChoice.Frontier.keep
  · exact .selected base (baseBindings occurrence) (by rfl) rfl (baseAccepted occurrence)
  apply ClauseChoice.Frontier.skip
  · exact .refused stepRule (by rfl) rfl (stepRefused occurrence)
  apply ClauseChoice.Frontier.skip
  · exact .other forkRule (by rfl) (by decide +kernel)
  apply ClauseChoice.Frontier.skip
  · exact .other forkRule (by rfl) (by decide +kernel)
  exact .nil

private theorem zero_solves_stripArgumentAfter (occurrence : Nat) :
    Solves zeroEnvironment (stripArgumentAfter occurrence).bindings := by
  intro pair member
  simp only [stripArgumentAfter,List.mem_append,List.mem_singleton] at member
  rcases member with old | rfl
  · rw [stripOpened_bindings] at old
    exact zero_solves_forkBindings occurrence pair old
  · simp [stripSlot,read_zero_var]

private theorem zero_solves_baseBindings (occurrence : Nat) :
    Solves zeroEnvironment (baseBindings occurrence) := by
  intro pair member
  simp only [baseBindings,List.mem_append,List.mem_singleton] at member
  rcases member with old | rfl
  · exact zero_solves_stripArgumentAfter occurrence pair old
  · simp [stripQuery,base,boxed,ClauseChoice.freshPattern,ClauseChoice.pattern,
      HE.Spec.Type.RuntimeRefinement.renameTypeVars]

private theorem out_mem_forkChoice_support (occurrence : Nat) :
    "out" ∈ (forkChoice occurrence).support := by
  apply persistentSupport_subset_support (forkChoice occurrence)
  apply typeVars_mem_persistent_destination (forkChoice occurrence) "out"
  have destination : (forkChoice occurrence).destination = .var "out" := by
    simp [forkChoice,guardedRoot,protectControl,rootArgumentAfter,
      rootPrepared.retains_frame.2.1,rootControl]
  rw [destination]
  simp [HE.Spec.Type.Presentation.TypeSubst.typeVars]

private theorem stripSlot_ne_out (occurrence : Nat) :
    freshName (forkChoice occurrence) 0 ≠ "out" := by
  intro same
  apply freshName_not_mem (forkChoice occurrence) 0
  rw [same]
  exact out_mem_forkChoice_support occurrence

private def boxOpened (occurrence : Nat) : Control :=
  prepare .eagerValue program (baseChoice occurrence) boxed (.var "out") []

private theorem boxPrepared (occurrence : Nat) :
    Prepared .eagerValue program (baseChoice occurrence) (.var "out") []
      boxed (boxOpened occurrence) :=
  prepare_has_source _ _ _ _ _ _

private theorem boxPrepared_delimited (occurrence : Nat) :
    PreparedDelimitedRel (boxPrepared occurrence) := by
  let canonical := Prepared.construction (policy := Policy.eagerValue)
    (program := program) (control := baseChoice occurrence)
    (destination := (.var "out" : Atom)) (older := [])
    "Box" [.symbol "Z"] (by rfl) (by rfl)
  exact PreparedDelimitedRel.of_source (boxPrepared occurrence) canonical
    (PreparedDelimitedRel.construction "Box" [.symbol "Z"] (by rfl) (by rfl))

private theorem boxOpened_bindings (occurrence : Nat) :
    (boxOpened occurrence).bindings = baseBindings occurrence := by
  exact (boxPrepared occurrence).retains_frame.1.trans rfl

private def boxSlot (occurrence : Nat) : Atom :=
  .var (freshName (baseChoice occurrence) 0)

private def boxArgumentAfter (occurrence : Nat) : Control :=
  { boxOpened occurrence with
    bindings := (boxOpened occurrence).bindings ++ [(.symbol "Z",boxSlot occurrence)]
    goals := [.equate (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")] }

private theorem outFresh_baseChoice (occurrence : Nat) :
    ∀ pair ∈ (baseChoice occurrence).bindings,
      "out" ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
        "out" ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2 := by
  intro pair member
  simp only [baseChoice,baseBindings,List.mem_append,List.mem_singleton] at member
  rcases member with old | rfl
  · change pair ∈ (stripArgumentAfter occurrence).bindings at old
    simp only [stripArgumentAfter,List.mem_append,List.mem_singleton] at old
    rcases old with earlier | rfl
    · rw [stripOpened_bindings] at earlier
      exact (stripPrivate occurrence).storeFresh pair earlier
    · simp [stripSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
        (forkVariable_ne_out occurrence).symm,(stripSlot_ne_out occurrence).symm]
  · simp [stripQuery,base,boxed,ClauseChoice.freshPattern,ClauseChoice.pattern,
      HE.Spec.Type.RuntimeRefinement.renameTypeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList]

private def boxPrivate (occurrence : Nat) :
    PrivateDestination (baseChoice occurrence) boxed (.var "out") [] := by
  refine ⟨"out",rfl,outFresh_baseChoice occurrence,?_⟩
  simp [boxed,HE.Spec.Type.Presentation.TypeSubst.typeVars,
    HE.Spec.Type.Presentation.TypeSubst.typeVarsList]

private def boxArgumentPrivate (occurrence : Nat) :
    PrivateDestination (boxOpened occurrence) (.symbol "Z") (boxSlot occurrence)
      [.equate (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")] := by
  refine ⟨freshName (baseChoice occurrence) 0,rfl,?_,?_⟩
  · rw [boxOpened_bindings]
    exact freshName_storeFresh (baseChoice occurrence) 0
  · simp [HE.Spec.Type.Presentation.TypeSubst.typeVars]

private theorem boxArgumentAccepted (occurrence : Nat) :
    Refinement (boxOpened occurrence).bindings (.symbol "Z") (boxSlot occurrence)
      (some (boxArgumentAfter occurrence).bindings) := by
  apply Refinement.accepted zeroEnvironment
  · rw [boxOpened_bindings]
    exact zero_solves_baseBindings occurrence
  · simp [boxSlot,read_zero_var,read_zero_symbol]

private def boxArgument (occurrence : Nat) :
    Evaluation program (boxOpened occurrence) (.symbol "Z") (boxSlot occurrence)
      [.equate (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")]
      [boxArgumentAfter occurrence] := by
  apply Evaluation.symbol (boxArgumentPrivate occurrence)
  · rfl
  · simpa only [boxArgumentAfter,boxSlot] using boxArgumentAccepted occurrence

private theorem out_mem_baseChoice_support (occurrence : Nat) :
    "out" ∈ (baseChoice occurrence).support := by
  apply persistentSupport_subset_support (baseChoice occurrence)
  apply typeVars_mem_persistent_destination (baseChoice occurrence) "out"
  have destination : (baseChoice occurrence).destination = .var "out" := by
    have guardedDestination : guardedRoot.destination = .var "out" := by
      simp [guardedRoot,protectControl,rootArgumentAfter,
        rootPrepared.retains_frame.2.1,rootControl]
    have forkDestination : (forkChoice occurrence).destination = .var "out" := by
      simp [forkChoice,guardedDestination]
    have openedDestination := (stripPrepared occurrence).retains_frame.2.1
    simp [baseChoice,stripGuard,protectControl,stripArgumentAfter,
      openedDestination,forkDestination]
  rw [destination]
  simp [HE.Spec.Type.Presentation.TypeSubst.typeVars]

private theorem boxSlot_ne_out (occurrence : Nat) :
    freshName (baseChoice occurrence) 0 ≠ "out" := by
  intro same
  apply freshName_not_mem (baseChoice occurrence) 0
  rw [same]
  exact out_mem_baseChoice_support occurrence

private def boxReturnPrivate (occurrence : Nat) :
    PrivateDestination (boxArgumentAfter occurrence)
      (.expression [.symbol "Box",boxSlot occurrence]) (.var "out") [] := by
  refine ⟨"out",rfl,?_,?_⟩
  · intro pair member
    simp only [boxArgumentAfter,List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · rw [boxOpened_bindings] at old
      exact outFresh_baseChoice occurrence pair old
    · simp [boxSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
        (boxSlot_ne_out occurrence).symm]
  · simp [boxSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      (boxSlot_ne_out occurrence).symm]

private def boxEnvironment : Environment :=
  fun name => if name = "out" then encode boxed else encode (.symbol "Z")

omit profile in
private theorem boxEnvironment_read_out :
    read boxEnvironment (.var "out") = boxed := by
  rw [read_eq_applyTypeValuation]
  simp [boxEnvironment,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]

omit profile in
private theorem boxEnvironment_read_other (name : String) (different : name ≠ "out") :
    read boxEnvironment (.var name) = .symbol "Z" := by
  rw [read_eq_applyTypeValuation]
  simp [boxEnvironment,HE.Spec.Type.RuntimeRefinement.applyTypeValuation,different]

omit profile in
private theorem boxEnvironment_agrees_without_out (atom : Atom)
    (fresh : "out" ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars atom) :
    read boxEnvironment atom = read zeroEnvironment atom := by
  rw [read_eq_applyTypeValuation,read_eq_applyTypeValuation]
  apply HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
  intro name member
  have different : name ≠ "out" := by
    intro same
    exact fresh (same ▸ member)
  simp [boxEnvironment,zeroEnvironment,different]

private theorem boxEnvironment_solves_baseBindings (occurrence : Nat) :
    Solves boxEnvironment (baseBindings occurrence) := by
  intro pair member
  have fresh := outFresh_baseChoice occurrence pair (by
    simpa only [baseChoice] using member)
  calc
    read boxEnvironment pair.1 = read zeroEnvironment pair.1 :=
      boxEnvironment_agrees_without_out pair.1 fresh.1
    _ = read zeroEnvironment pair.2 := zero_solves_baseBindings occurrence pair member
    _ = read boxEnvironment pair.2 :=
      (boxEnvironment_agrees_without_out pair.2 fresh.2).symm

private theorem boxReturnAccepted (occurrence : Nat) :
    Refinement (boxArgumentAfter occurrence).bindings
      (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")
      (some ((boxArgumentAfter occurrence).bindings ++
        [(.expression [.symbol "Box",boxSlot occurrence],.var "out")])) := by
  apply Refinement.accepted boxEnvironment
  · intro pair member
    simp only [boxArgumentAfter,List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · rw [boxOpened_bindings] at old
      exact boxEnvironment_solves_baseBindings occurrence pair old
    · calc
        read boxEnvironment (.symbol "Z") = read zeroEnvironment (.symbol "Z") :=
          boxEnvironment_agrees_without_out _ (by
            simp [HE.Spec.Type.Presentation.TypeSubst.typeVars])
        _ = read zeroEnvironment (boxSlot occurrence) := by
          simp [boxSlot,read_zero_var,read_zero_symbol]
        _ = read boxEnvironment (boxSlot occurrence) :=
          (boxEnvironment_agrees_without_out _ (by
            simp [boxSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
              (boxSlot_ne_out occurrence).symm])).symm
  · rw [boxEnvironment_read_out]
    rw [read_eq_applyTypeValuation]
    simp [boxSlot,boxEnvironment,boxed,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,boxSlot_ne_out]

private def boxResult (occurrence : Nat) : Control :=
  { boxArgumentAfter occurrence with
    bindings := (boxArgumentAfter occurrence).bindings ++
      [(.expression [.symbol "Box",boxSlot occurrence],.var "out")]
    goals := [] }

private def boxInvocation (occurrence : Nat) :
    Invocation program (boxArgumentAfter occurrence)
      (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")
      (.equate (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")) []
      [boxResult occurrence] := by
  apply Invocation.constructor passive_box (boxReturnPrivate occurrence) rfl
  simpa only [boxResult] using boxReturnAccepted occurrence

private theorem baseBody_eq (occurrence : Nat) :
    ClauseChoice.freshBody (stripGuard occurrence) 0 base = boxed := by
  simp [base,boxed,ClauseChoice.freshBody,
    HE.Spec.Type.RuntimeRefinement.renameTypeVars]

private def boxedEvaluation (occurrence : Nat) :
    Evaluation program (baseChoice occurrence) boxed (.var "out") []
      [boxResult occurrence] := by
  change Evaluation program (baseChoice occurrence)
    (.expression [.symbol "Box",.symbol "Z"]) (.var "out") []
      [boxResult occurrence]
  apply Evaluation.constructor passive_box (boxPrivate occurrence)
    (by simp [baseChoice,baseBody_eq,boxed])
    (boxPrepared occurrence)
  apply Arguments.cons
  · rfl
  · exact boxArgument occurrence
  · have terminal : Arguments program (boxArgumentAfter occurrence) []
        (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")
        (.equate (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")) []
        [boxResult occurrence] := .nil rfl (boxInvocation occurrence)
    have branches : ArgumentBranches program [boxArgumentAfter occurrence] []
        (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")
        (.equate (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")) []
        [boxResult occurrence] := .cons terminal .nil
    change ArgumentBranches program [boxArgumentAfter occurrence] []
      (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")
      (.equate (.expression [.symbol "Box",boxSlot occurrence]) (.var "out")) []
      [boxResult occurrence]
    exact branches

private def stripReturnPrivate (occurrence : Nat) :
    PrivateDestination (stripArgumentAfter occurrence)
      (.expression [.symbol "strip",stripSlot occurrence]) (.var "out") [] := by
  refine ⟨"out",rfl,?_,?_⟩
  · intro pair member
    simp only [stripArgumentAfter,List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · rw [stripOpened_bindings] at old
      exact (stripPrivate occurrence).storeFresh pair old
    · simp [stripSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
        (forkVariable_ne_out occurrence).symm,(stripSlot_ne_out occurrence).symm]
  · simp [stripSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      (stripSlot_ne_out occurrence).symm]

private noncomputable def stripInvocation (occurrence : Nat) :
    Invocation program (stripArgumentAfter occurrence)
      (.expression [.symbol "strip",stripSlot occurrence]) (.var "out")
      (.invoke "strip" [stripSlot occurrence] (.var "out")) []
      [boxResult occurrence] := by
  have solved := resolve_sound (stripResolved occurrence)
  have readSlot := solved_stripArgument_reads_slot occurrence
    (stripEnvironment occurrence) solved
  have frontier : ClauseChoice.Frontier program
      (protectControl (stripArgumentAfter occurrence) (profile.stripExtra occurrence)) "strip"
      ([stripSlot occurrence].map (read (stripEnvironment occurrence))) (.var "out") []
      (List.range program.equations.length) [(0,baseChoice occurrence)] := by
    simpa only [stripGuard,List.map_cons,List.map_nil,readSlot] using stripFrontier occurrence
  have bodies : Bodies program (.var "out") [] [(0,baseChoice occurrence)]
      [boxResult occurrence] :=
    .cons (by simp [baseChoice,baseBody_eq,boxed]) (boxedEvaluation occurrence) .nil
  apply Invocation.equations (extra := profile.stripExtra occurrence)
    defined_strip (stripReturnPrivate occurrence) rfl
    (stripResolved occurrence)
  · intro name member
    simp only [List.map_cons,List.map_nil,readSlot,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      HE.Spec.Type.Presentation.TypeSubst.typeVars] at member
    simp at member
  · exact frontier
  · simp
  · exact bodies

private noncomputable def stripEvaluation (occurrence : Nat) :
    Evaluation program (forkChoice occurrence) (forkBody occurrence) (.var "out") []
      [boxResult occurrence] := by
  apply Evaluation.call defined_strip (stripPrivate occurrence)
    (by simp [forkChoice,forkBody_eq,forkBody]) (stripPrepared occurrence)
  apply Arguments.cons
  · rfl
  · exact stripArgument occurrence
  · have terminal : Arguments program (stripArgumentAfter occurrence) []
        (.expression [.symbol "strip",stripSlot occurrence]) (.var "out")
        (.invoke "strip" [stripSlot occurrence] (.var "out")) []
        [boxResult occurrence] := .nil rfl (stripInvocation occurrence)
    have branches : ArgumentBranches program [stripArgumentAfter occurrence] []
        (.expression [.symbol "strip",stripSlot occurrence]) (.var "out")
        (.invoke "strip" [stripSlot occurrence] (.var "out")) []
        [boxResult occurrence] := .cons terminal .nil
    change ArgumentBranches program [stripArgumentAfter occurrence] []
      (.expression [.symbol "strip",stripSlot occurrence]) (.var "out")
      (.invoke "strip" [stripSlot occurrence] (.var "out")) []
      [boxResult occurrence]
    exact branches

private noncomputable def rootEnvironment : Environment :=
  Classical.choose rootSolvable

omit profile in
private theorem rootResolved :
    resolve rootArgumentAfter.bindings = some rootEnvironment :=
  Classical.choose_spec rootSolvable

omit profile in
private theorem solved_root_reads_slot
    (environment : Environment) (solved : Solves environment rootArgumentAfter.bindings) :
    read environment rootSlot = .symbol "Z" := by
  have first := solved (.var "x",.symbol "Z") (by
    simp [rootArgumentAfter,rootOpened_bindings])
  have second := solved (.var "x",rootSlot) (by
    simp [rootArgumentAfter])
  exact second.symm.trans (first.trans (by
    rw [read_eq_applyTypeValuation]
    simp [HE.Spec.Type.RuntimeRefinement.applyTypeValuation]))

private def rootReturnPrivate :
    PrivateDestination rootArgumentAfter
      (.expression [.symbol "fork",rootSlot]) (.var "out") [] := by
  refine ⟨"out",rfl,?_,?_⟩
  · intro pair member
    simp only [rootArgumentAfter,List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · rw [rootOpened_bindings] at old
      exact rootPrivate.storeFresh pair old
    · simp [rootSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
        (rootSlot_ne_out).symm]
  · simp [rootSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,(rootSlot_ne_out).symm]

private noncomputable def rootInvocation :
    Invocation program rootArgumentAfter (.expression [.symbol "fork",rootSlot])
      (.var "out") (.invoke "fork" [rootSlot] (.var "out")) []
      [boxResult 2,boxResult 3] := by
  have solved := resolve_sound rootResolved
  have readSlot := solved_root_reads_slot rootEnvironment solved
  have frontier : ClauseChoice.Frontier program
      (protectControl rootArgumentAfter profile.rootExtra) "fork"
      ([rootSlot].map (read rootEnvironment)) (.var "out") []
      (List.range program.equations.length) [(2,forkChoice 2),(3,forkChoice 3)] := by
    simpa only [guardedRoot,List.map_cons,List.map_nil,readSlot] using forkFrontier
  have bodies : Bodies program (.var "out") []
      [(2,forkChoice 2),(3,forkChoice 3)] [boxResult 2,boxResult 3] := by
    simpa only [List.singleton_append] using
      (Bodies.cons (by simp [forkChoice,forkBody_eq,forkBody]) (stripEvaluation 2)
        (Bodies.cons (by simp [forkChoice,forkBody_eq,forkBody])
          (stripEvaluation 3) Bodies.nil))
  apply Invocation.equations (extra := profile.rootExtra)
    defined_fork rootReturnPrivate rfl rootResolved
  · intro name member
    simp only [List.map_cons,List.map_nil,readSlot,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      HE.Spec.Type.Presentation.TypeSubst.typeVars] at member
    simp at member
  · exact frontier
  · simp
  · exact bodies

private noncomputable def openRecursiveSource :
    Evaluation program rootControl query (.var "out") []
      [boxResult 2,boxResult 3] := by
  apply Evaluation.call defined_fork rootPrivate rfl rootPrepared
  apply Arguments.cons
  · rfl
  · exact rootArgument
  · have terminal : Arguments program rootArgumentAfter []
        (.expression [.symbol "fork",rootSlot]) (.var "out")
        (.invoke "fork" [rootSlot] (.var "out")) []
        [boxResult 2,boxResult 3] := .nil rfl rootInvocation
    have branches : ArgumentBranches program [rootArgumentAfter] []
        (.expression [.symbol "fork",rootSlot]) (.var "out")
        (.invoke "fork" [rootSlot] (.var "out")) []
        [boxResult 2,boxResult 3] := .cons terminal .nil
    change ArgumentBranches program [rootArgumentAfter] []
      (.expression [.symbol "fork",rootSlot]) (.var "out")
      (.invoke "fork" [rootSlot] (.var "out")) []
      [boxResult 2,boxResult 3]
    exact branches

private def openBindings : HE.Bindings := ⟨[("x",.symbol "Z")],[]⟩

private def openEnvironment : Entry.Value.Environment := [("x",.symbol "Z")]

omit profile in
private theorem openCertified :
    HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate openBindings
      (Entry.Value.eraseEnvironment openEnvironment) := by
  apply HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate.of_normal_theory
  · simp [openEnvironment,Entry.Value.eraseEnvironment,Entry.Value.erase,
      HE.Spec.Type.Presentation.TypeSubst.Normal,
      HE.Spec.Type.Presentation.TypeSubst.keys,
      HE.Spec.Type.Presentation.TypeSubst.typeVars]
  · intro valuation
    simp [openBindings,openEnvironment,Entry.Value.eraseEnvironment,Entry.Value.erase,
      HE.Spec.Type.Presentation.Theory.TypeSubstSatisfied,
      HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied]

private def openFrame : Frame := ⟨openBindings,openEnvironment,openCertified⟩

omit profile in
private theorem openPassive : PassiveEnvironment program ["x"] openFrame.environment := by
  intro pair member
  obtain rfl := List.mem_singleton.mp member
  exact ⟨by simpa only [Entry.Value.erase] using
      (Value.symbol (program := program) "Z" (by decide +kernel) (by decide +kernel)),
    by simpa only [Entry.Value.erase] using
      (NoErrorSymbol.symbol (by decide +kernel : "Z" ≠ "Error"))⟩

omit profile in
private theorem queryInstance :
    InputInstance program ["x"] query (Entry.Value.ofAtom query) := by
  apply InputInstance.raw
  have admitted : CodeRel program ["x"]
      (.expression .active [.symbol "fork",.var "x"]) := by
    apply CodeRel.active ordinary_fork
    intro argument member
    obtain rfl := List.mem_singleton.mp member
    exact .variable (by simp)
  simpa [query,Entry.Value.ofAtom] using admitted

omit profile in
private theorem initialPacket :
    observedTuples openFrame.bindings [query,.var "x"] =
      solutionTuples rootControl.bindings [query,.var "x"] := by
  apply reached_pending_observations
  intro environment
  simpa [openFrame,openBindings,rootControl,
    HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations] using
      (solves_binding_equations environment openBindings).symm

omit profile in
private theorem rootSupport :
    SupportRel ["x"] [] openFrame.bindings [query,.var "x"]
      [query,.var "x"] rootControl := by
  constructor <;> intro name member
  · simp only [List.mem_singleton] at member
    subst name
    simp [PersistentSupport,rootControl]
  · simp [HE.Spec.Type.Presentation.TypeSubst.typeVarsList] at member
  · simp [openFrame,openBindings,
      HE.Spec.Bindings.ScopeObservation.specBindingVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVars] at member
    subst name
    simp [PersistentSupport,rootControl]
  · simp [query,HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      HE.Spec.Type.Presentation.TypeSubst.typeVars] at member
    subst name
    simp [PersistentSupport,rootControl]
  · simp [query,HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
      HE.Spec.Type.Presentation.TypeSubst.typeVars] at member
    subst name
    simp [PersistentSupport,rootControl]

omit profile in
private theorem freshName_ne_supported (control : Control) (index : Nat)
    (name : String) (supported : name ∈ control.support) :
    freshName control index ≠ name := by
  intro same
  exact freshName_not_mem control index (same ▸ supported)

omit profile in
private theorem root_x_supported : "x" ∈ rootControl.support := by
  simp [Control.support,rootControl]

private theorem forkChoice_x_supported (occurrence : Nat) :
    "x" ∈ (forkChoice occurrence).support := by
  apply persistentSupport_subset_support (forkChoice occurrence)
  apply typeVars_mem_persistent_binding (forkChoice occurrence)
    (.var "x",.symbol "Z")
  · simp [forkChoice,forkBindings,guardedRoot_bindings]
  · simp [HE.Spec.Type.Presentation.TypeSubst.typeVars]

private theorem baseChoice_x_supported (occurrence : Nat) :
    "x" ∈ (baseChoice occurrence).support := by
  apply persistentSupport_subset_support (baseChoice occurrence)
  apply typeVars_mem_persistent_binding (baseChoice occurrence)
    (.var "x",.symbol "Z")
  · change (.var "x",.symbol "Z") ∈ baseBindings occurrence
    apply List.mem_append_left
    change (.var "x",.symbol "Z") ∈ (stripArgumentAfter occurrence).bindings
    apply List.mem_append_left
    rw [stripOpened_bindings]
    apply List.mem_append_left
    rw [guardedRoot_bindings]
    exact List.mem_cons_self
  · simp [HE.Spec.Type.Presentation.TypeSubst.typeVars]

omit profile in
private theorem name_avoids_one_freshSlot (control : Control) (name : String)
    (different : freshName control 0 ≠ name) :
    name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList (freshSlots control 1) := by
  simp [freshSlots,HE.Spec.Type.Presentation.TypeSubst.typeVarsList,
    HE.Spec.Type.Presentation.TypeSubst.typeVars,different.symm]

private def BranchFreshness (occurrence : Nat) : Prop :=
  "out" ≠ forkVariable occurrence ∧
    (freshName (forkChoice occurrence) 0 ≠ forkVariable occurrence ∧
      freshName (forkChoice occurrence) 0 ≠ "x") ∧
    "out" ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (freshSlots (forkChoice occurrence) 1) ∧
    freshName (baseChoice occurrence) 0 ≠ "x" ∧
    "out" ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (freshSlots (baseChoice occurrence) 1)

private theorem branchFreshness (occurrence : Nat) : BranchFreshness occurrence := by
  refine ⟨(forkVariable_ne_out occurrence).symm,⟨?_,?_⟩,?_,?_,?_⟩
  · exact freshName_ne_supported (forkChoice occurrence) 0 _
      (forkVariable_mem_choice_support occurrence)
  · exact freshName_ne_supported (forkChoice occurrence) 0 _
      (forkChoice_x_supported occurrence)
  · exact name_avoids_one_freshSlot (forkChoice occurrence) "out"
      (stripSlot_ne_out occurrence)
  · exact freshName_ne_supported (baseChoice occurrence) 0 _
      (baseChoice_x_supported occurrence)
  · exact name_avoids_one_freshSlot (baseChoice occurrence) "out"
      (boxSlot_ne_out occurrence)

private def BranchPacketFreshness (occurrence : Nat) : Prop :=
  ("out" ≠ forkVariable occurrence ∧ "out" ≠ "x") ∧
    (freshName (forkChoice occurrence) 0 ≠ forkVariable occurrence ∧
      freshName (forkChoice occurrence) 0 ≠ "x") ∧
    ("out" ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (freshSlots (forkChoice occurrence) 1) ∧ "out" ≠ "x") ∧
    "out" ≠ "x" ∧
    freshName (baseChoice occurrence) 0 ≠ "x" ∧
    "out" ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (freshSlots (baseChoice occurrence) 1) ∧
    "out" ≠ "x"

private theorem branchPacketFreshness (occurrence : Nat) :
    BranchPacketFreshness occurrence := by
  obtain ⟨callFresh,⟨argumentFresh,argumentCaller⟩,returnFresh,
    boxCaller,boxReturnFresh⟩ := branchFreshness occurrence
  have outCaller : "out" ≠ "x" := by decide +kernel
  exact ⟨⟨callFresh,outCaller⟩,⟨argumentFresh,argumentCaller⟩,
    ⟨returnFresh,outCaller⟩,outCaller,boxCaller,boxReturnFresh,outCaller⟩

private theorem openAllocated :
    openRecursiveSource.Allocated [] [.var "x"] := by
  simp only [openRecursiveSource,rootInvocation,stripEvaluation,stripInvocation,
    boxedEvaluation,boxInvocation,rootArgument,stripArgument,boxArgument,id,
    Evaluation.Allocated,Arguments.Allocated,ArgumentBranches.Allocated,
    Invocation.Allocated,Bodies.Allocated,List.nil_append,List.map_nil,
    List.singleton_append]
  simp only [rootPrivate,rootArgumentPrivate,rootReturnPrivate,
    stripPrivate,stripArgumentPrivate,stripReturnPrivate,
    boxPrivate,boxArgumentPrivate,boxReturnPrivate,
    query,forkBody,boxed,List.zipWith_nil_left,List.map_nil,List.append_nil,
    List.nil_append,List.mem_append,List.mem_singleton,
    List.length_cons,List.length_nil,
    Nat.zero_add,not_or,
    HE.Spec.Type.Presentation.TypeSubst.typeVars,
    HE.Spec.Type.Presentation.TypeSubst.typeVarsList,and_true]
  have outCaller : "out" ≠ "x" := by decide +kernel
  have rootCaller := freshName_ne_supported rootControl 0 "x" root_x_supported
  have rootReturn := name_avoids_one_freshSlot rootControl "out" rootSlot_ne_out
  exact ⟨⟨outCaller,outCaller⟩,⟨rootCaller,rootCaller⟩,
    ⟨rootReturn,outCaller⟩,branchPacketFreshness 2,branchPacketFreshness 3⟩

private theorem boxEnvironment_solves_boxArgumentAfter (occurrence : Nat) :
    Solves boxEnvironment (boxArgumentAfter occurrence).bindings := by
  intro pair member
  simp only [boxArgumentAfter,List.mem_append,List.mem_singleton] at member
  rcases member with old | rfl
  · rw [boxOpened_bindings] at old
    exact boxEnvironment_solves_baseBindings occurrence pair old
  · calc
      read boxEnvironment (.symbol "Z") = read zeroEnvironment (.symbol "Z") :=
        boxEnvironment_agrees_without_out _ (by
          simp [HE.Spec.Type.Presentation.TypeSubst.typeVars])
      _ = read zeroEnvironment (boxSlot occurrence) := by
        simp [boxSlot,read_zero_var,read_zero_symbol]
      _ = read boxEnvironment (boxSlot occurrence) :=
        (boxEnvironment_agrees_without_out _ (by
          simp [boxSlot,HE.Spec.Type.Presentation.TypeSubst.typeVars,
            (boxSlot_ne_out occurrence).symm])).symm

private theorem boxEnvironment_solves_result (occurrence : Nat) :
    Solves boxEnvironment (boxResult occurrence).bindings := by
  intro pair member
  simp only [boxResult,List.mem_append,List.mem_singleton] at member
  rcases member with old | rfl
  · exact boxEnvironment_solves_boxArgumentAfter occurrence pair old
  · rw [boxEnvironment_read_out]
    rw [read_eq_applyTypeValuation]
    simp [boxSlot,boxEnvironment,boxed,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,boxSlot_ne_out]

private theorem x_binding_mem_result (occurrence : Nat) :
    (.var "x",.symbol "Z") ∈ (boxResult occurrence).bindings := by
  simp only [boxResult,List.mem_append,List.mem_singleton]
  apply Or.inl
  simp only [boxArgumentAfter,List.mem_append,List.mem_singleton]
  apply Or.inl
  rw [boxOpened_bindings]
  simp only [baseBindings,List.mem_append,List.mem_singleton]
  apply Or.inl
  change (.var "x",.symbol "Z") ∈ (stripArgumentAfter occurrence).bindings
  simp only [stripArgumentAfter,List.mem_append,List.mem_singleton]
  apply Or.inl
  rw [stripOpened_bindings]
  simp only [forkBindings,List.mem_append,List.mem_singleton]
  apply Or.inl
  rw [guardedRoot_bindings]
  exact List.mem_cons_self

private theorem outcome_positive (occurrence : Nat) :
    [boxed,.symbol "Z"] ∈
      solutionTuples (boxResult occurrence).bindings [.var "out",.var "x"] := by
  refine ⟨boxEnvironment,boxEnvironment_solves_result occurrence,?_⟩
  simp [boxEnvironment_read_out,boxEnvironment_read_other,boxed]

private theorem outcome_negative (occurrence : Nat) :
    [boxed,.expression [.symbol "S",.symbol "Z"]] ∉
      solutionTuples (boxResult occurrence).bindings [.var "out",.var "x"] := by
  rintro ⟨environment,solved,returned⟩
  have xBound := solved (.var "x",.symbol "Z") (x_binding_mem_result occurrence)
  have returnedX : read environment (.var "x") =
      .expression [.symbol "S",.symbol "Z"] := by
    exact (List.cons.inj (List.cons.inj returned).2).1
  have readZ : read environment (.symbol "Z") = .symbol "Z" := by
    rw [read_eq_applyTypeValuation]
    simp [HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
  have impossible : (.symbol "Z" : Atom) = .expression [.symbol "S",.symbol "Z"] :=
    (xBound.trans readZ).symm.trans returnedX
  cases impossible

private theorem openRecursiveSource_synchronized_of (pSupp cSupp : Finset String)
    (rootSync :
      (protectControl rootArgumentAfter
        (rootArgumentAfter.support ∪ (pSupp ∪ cSupp))).reserved =
        (protectControl rootArgumentAfter profile.rootExtra).reserved)
    (strip2Sync :
      (protectControl (stripArgumentAfter 2)
        ((stripArgumentAfter 2).support ∪
          ((forkChoice 3).support ∪ (pSupp ∪ cSupp)))).reserved =
        (protectControl (stripArgumentAfter 2) (profile.stripExtra 2)).reserved)
    (strip3Sync :
      (protectControl (stripArgumentAfter 3)
        ((stripArgumentAfter 3).support ∪
          (pSupp ∪ (cSupp ∪ rawAnswerSupport (boxResult 2))))).reserved =
        (protectControl (stripArgumentAfter 3) (profile.stripExtra 3)).reserved) :
    Evaluation.ExtraSynchronized openRecursiveSource pSupp cSupp
      ([boxResult 2,boxResult 3].map rawAnswerSupport) := by
  simp only [openRecursiveSource,rootInvocation,stripEvaluation,stripInvocation,
    boxedEvaluation,boxInvocation,rootArgument,stripArgument,boxArgument,id,
    Evaluation.ExtraSynchronized,Arguments.ExtraSynchronized,
    ArgumentBranches.ExtraSynchronized,Invocation.ExtraSynchronized,
    Bodies.ExtraSynchronized,Evaluation.queuedOutcomes,supportIncrement]
  simp [rootSync,strip2Sync,strip3Sync,Finset.union_assoc]
  exact ⟨rootPrepared_delimited,
    ⟨⟨stripPrepared_delimited 2,boxPrepared_delimited 2⟩,
      ⟨stripPrepared_delimited 3,boxPrepared_delimited 3⟩⟩⟩

end

/-- The root call is freshened against exactly the active control, queued work,
and already collected answers visible at its collection cut. -/
private abbrev rootFresheningStage (pSupp cSupp : Finset String) : FresheningProfile :=
  ⟨rootArgumentAfter.support ∪ (pSupp ∪ cSupp),fun _ => ∅⟩

/-- After choosing the first duplicate clause, the second clause is already in
the DFS queue.  Its support therefore contributes to the first recursive call's
freshening boundary. -/
private def strip2Extra (pSupp cSupp : Finset String) : Finset String :=
  let stage := rootFresheningStage pSupp cSupp
  (stripArgumentAfter (profile := stage) 2).support ∪
    ((forkChoice (profile := stage) 3).support ∪ (pSupp ∪ cSupp))

/-- The profile after entering the first selected clause. -/
private abbrev firstBranchFresheningStage
    (pSupp cSupp : Finset String) : FresheningProfile :=
  ⟨rootArgumentAfter.support ∪ (pSupp ∪ cSupp),
    fun occurrence => if occurrence = 2 then strip2Extra pSupp cSupp else ∅⟩

/-- The second recursive call sees the first answer in the retained collection
and no selected clause behind it. -/
private def strip3Extra (pSupp cSupp : Finset String) : Finset String :=
  let stage := firstBranchFresheningStage pSupp cSupp
  (stripArgumentAfter (profile := stage) 3).support ∪
    (pSupp ∪
      (cSupp ∪ rawAnswerSupport (boxResult (profile := stage) 2)))

/-- Concrete freshening choices induced by the retained DFS collection state.
The definition follows the queue order: root, first duplicate, then second
duplicate after the first answer has been collected. -/
abbrev collectionFresheningProfile
    (pSupp cSupp : Finset String) : FresheningProfile :=
  ⟨rootArgumentAfter.support ∪ (pSupp ∪ cSupp),
    fun occurrence =>
      if occurrence = 2 then strip2Extra pSupp cSupp
      else if occurrence = 3 then strip3Extra pSupp cSupp
      else ∅⟩

/-- The recursive duplicate-clause source tree uses exactly the protection
sets computed by the concrete collection queue at every equation dispatch. -/
theorem open_recursive_duplicate_synchronized (pSupp cSupp : Finset String) :
    Evaluation.ExtraSynchronized
      (openRecursiveSource (profile := collectionFresheningProfile pSupp cSupp))
      pSupp cSupp
      ([boxResult (profile := collectionFresheningProfile pSupp cSupp) 2,
          boxResult (profile := collectionFresheningProfile pSupp cSupp) 3].map
        rawAnswerSupport) := by
  let profile : FresheningProfile := collectionFresheningProfile pSupp cSupp
  change Evaluation.ExtraSynchronized
    (openRecursiveSource (profile := profile)) pSupp cSupp
    ([boxResult (profile := profile) 2,boxResult (profile := profile) 3].map
      rawAnswerSupport)
  exact openRecursiveSource_synchronized_of (profile := profile) pSupp cSupp
    rfl rfl rfl

/-- Positive E3 control: the retained DFS collection machine drains the same
two recursive duplicate-clause occurrences, in source order, with the exact
live support used for every freshening decision. -/
theorem open_recursive_duplicate_root_drain {Context : Type}
    (pSupp cSupp : Finset String) :
    RootContinuationContract (Context := Context) program [] [] rootControl
      pSupp cSupp
      [boxResult (profile := collectionFresheningProfile pSupp cSupp) 2,
        boxResult (profile := collectionFresheningProfile pSupp cSupp) 3]
      (cSupp ∪ supportIncrement
        ([boxResult (profile := collectionFresheningProfile pSupp cSupp) 2,
            boxResult (profile := collectionFresheningProfile pSupp cSupp) 3].map
          rawAnswerSupport)) := by
  exact Evaluation.root_drain
    (openRecursiveSource (profile := collectionFresheningProfile pSupp cSupp))
    pSupp cSupp (open_recursive_duplicate_synchronized pSupp cSupp)

#print axioms open_recursive_duplicate_synchronized
#print axioms open_recursive_duplicate_root_drain

/-- End-to-end E2/E3 control.  The same open recursive source tree realizes
the contextual HE relation and the retained PeTTa DFS queue, preserving the
two physical clause occurrences, their order and their shared caller binding. -/
theorem open_recursive_duplicate_realization {Context : Type}
    (pSupp cSupp : Finset String) :
    let profile := collectionFresheningProfile pSupp cSupp
    ∃ results,
      AtomRel (equationSpace program) noForeign rawLookup [] ["x"]
        (Entry.Value.ofAtom query) Atom.undefinedType openFrame results
        (policy := Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program ["x"] [] [] [.var "x"] [.var "x"]
        (.var "out") [] rootControl) results
        [boxResult (profile := profile) 2,boxResult (profile := profile) 3] ∧
      (∀ outcome ∈ [boxResult (profile := profile) 2,boxResult (profile := profile) 3],
        BranchPath program rootControl outcome) ∧
      observedOutcomePackets [] [.var "x"] results =
        solutionOutcomePackets [] [.var "x"] (.var "out")
          [boxResult (profile := profile) 2,boxResult (profile := profile) 3] ∧
      RootContinuationContract (Context := Context) program [] [] rootControl
        pSupp cSupp
        [boxResult (profile := profile) 2,boxResult (profile := profile) 3]
        (cSupp ∪ supportIncrement
          ([boxResult (profile := profile) 2,boxResult (profile := profile) 3].map
            rawAnswerSupport)) ∧
      results.length = 2 ∧
      ∀ outcome ∈ [boxResult (profile := profile) 2,boxResult (profile := profile) 3],
        [boxed,.symbol "Z"] ∈ solutionTuples outcome.bindings [.var "out",.var "x"] ∧
        [boxed,.expression [.symbol "S",.symbol "Z"]] ∉
          solutionTuples outcome.bindings [.var "out",.var "x"] := by
  dsimp only
  let profile : FresheningProfile := collectionFresheningProfile pSupp cSupp
  obtain ⟨results,completed,outcomesRelated,paths,packets,drain⟩ :=
    CollectionLinearization.Evaluation.realize_root (Context := Context)
      (openRecursiveSource (profile := profile)) constructor_patterns program_code
      ["x"] [] ["x"] openFrame (Entry.Value.ofAtom query) queryInstance openPassive
      [] [] [.var "x"] [.var "x"] rfl
      (by simpa only [List.nil_append,Entry.Value.erase_ofAtom] using initialPacket)
      (by simpa only [List.nil_append,Entry.Value.erase_ofAtom] using rootSupport)
      openAllocated pSupp cSupp
      (open_recursive_duplicate_synchronized pSupp cSupp)
  refine ⟨results,completed,outcomesRelated,paths,packets,drain,?_,?_⟩
  · simpa using outcomesRelated.length_eq
  · intro outcome member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨outcome_positive 2,outcome_negative 2⟩
    · rcases member with rfl | impossible
      · exact ⟨outcome_positive 3,outcome_negative 3⟩
      · cases impossible

#print axioms open_recursive_duplicate_realization

/-- Positive E2 control: an open caller binding flows through argument
evaluation, two duplicate clause occurrences, recursive calls and constructor
assembly.  The paired negative observation shows that the caller correlation
was retained rather than independently resampled. -/
theorem open_recursive_duplicate_transport [profile : FresheningProfile] :
    ∃ results,
      AtomRel (equationSpace program) noForeign rawLookup [] ["x"]
        (Entry.Value.ofAtom query) Atom.undefinedType openFrame results
        (policy := Policy.unmarked) ∧
      List.Forall₂ (OutcomeRel program ["x"] [] [] [.var "x"] [.var "x"]
        (.var "out") [] rootControl) results
        [boxResult (profile := profile) 2,boxResult (profile := profile) 3] ∧
      (∀ outcome ∈ [boxResult (profile := profile) 2,boxResult (profile := profile) 3],
        BranchPath program rootControl outcome) ∧
      observedOutcomePackets [] [.var "x"] results =
        solutionOutcomePackets [] [.var "x"] (.var "out")
          [boxResult (profile := profile) 2,boxResult (profile := profile) 3] ∧
      results.length = 2 ∧
      ∀ outcome ∈ [boxResult (profile := profile) 2,boxResult (profile := profile) 3],
        [boxed,.symbol "Z"] ∈ solutionTuples outcome.bindings [.var "out",.var "x"] ∧
        [boxed,.expression [.symbol "S",.symbol "Z"]] ∉
          solutionTuples outcome.bindings [.var "out",.var "x"] := by
  obtain ⟨results,completed,outcomesRelated,paths,packets⟩ :=
    openRecursiveSource.transport constructor_patterns program_code ["x"] [] ["x"]
      openFrame (Entry.Value.ofAtom query) queryInstance openPassive
      [] [] [.var "x"] [.var "x"] rfl
      (by simpa only [List.nil_append,Entry.Value.erase_ofAtom] using initialPacket)
      (by simpa only [List.nil_append,Entry.Value.erase_ofAtom] using rootSupport)
      openAllocated
  refine ⟨results,completed,outcomesRelated,paths,packets,?_,?_⟩
  · simpa using outcomesRelated.length_eq
  · intro outcome member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨outcome_positive 2,outcome_negative 2⟩
    · rcases member with rfl | impossible
      · exact ⟨outcome_positive 3,outcome_negative 3⟩
      · cases impossible

#print axioms open_recursive_duplicate_transport

end Mettapedia.Languages.MeTTa.Translation.OpenRecursive.Controls
