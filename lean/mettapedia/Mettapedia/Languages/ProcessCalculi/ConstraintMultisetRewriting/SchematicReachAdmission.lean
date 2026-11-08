import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachInformation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpacesReachWrite
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep

/-!+# One admission for schematic rows, reachable spaces and atomic writes

The rule is an already scoped instance. Each selected input opens its own
schema view, even when two reads select one physical occurrence. Addresses
retain their shared capture identities. The single joint equation problem
resolves ports without imposing a written source order. Guards use schema
matching on the original occurrence world, counting a physical row once.

The full owner profile has every name. A boundary may instead retain a set
of write-only names: production is allowed there without granting reads.
This relation does not choose source spelling or infer capture policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {point : S.Srt} {Name Local Shared O : Type}
    [DecidableEq Name] [DecidableEq O]
    (locals : Local → MetaArity (base S point Name))
    (captures : Shared → MetaArity (base S point Name))

abbrev Active := ContextualSelectionViews.target locals captures
abbrev ActiveTerm := Closed (Active locals captures)

def lowerCheck : NamedSpaces.LocatedCheck (ActiveTerm locals captures) → Check (ActiveTerm locals captures)
  | .equal left right => .equal left right
  | .absent address payload => .absent (place address payload)
  | .count address payload number => .count (place address payload) number

def lowerRule (rule : NamedSpaces.LocatedRule (ActiveTerm locals captures)) : RuleInstance (ActiveTerm locals captures) :=
  ⟨rule.take.map (fun p => place p.1 p.2), rule.read.map (fun p => place p.1 p.2),
    rule.tell,rule.checks.map (lowerCheck locals captures),rule.produce.map (fun p => place p.1 p.2)⟩

def placedRows (addresses : O → Closed captures)
    (rows : O → ContextualStoredRows.Row locals captures [] point) :=
  fun occurrence => locatedRow locals captures (addresses occurrence) (rows occurrence)

def inputViews (occupied : Finset Nat) (selection : Selection O)
    (addresses : O → Closed captures) (rows : O → ContextualStoredRows.Row locals captures [] point) :
    List (ActiveTerm locals captures) × List (ActiveTerm locals captures) :=
  (List.ofFn fun port : Fin selection.taken.length => ContextualStoredRows.viewAt locals captures
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port))
      (placedRows locals captures addresses rows (selection.taken.get port)),
   List.ofFn fun port : Fin selection.read.length => ContextualStoredRows.viewAt locals captures
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port))
      (placedRows locals captures addresses rows (selection.read.get port)))

def eventEquations (occupied : Finset Nat) (selection : Selection O)
    (addresses : O → Closed captures) (rows : O → ContextualStoredRows.Row locals captures [] point)
    (rule : NamedSpaces.LocatedRule (ActiveTerm locals captures)) : EquationStore (ActiveTerm locals captures) :=
  ContextualActivatedStep.useEquations (lowerRule locals captures rule).take
      (inputViews locals captures occupied selection addresses rows).1 ++
    ContextualActivatedStep.useEquations (lowerRule locals captures rule).read
      (inputViews locals captures occupied selection addresses rows).2 ++ rule.tell

def storedViews (occupied : Finset Nat) (selection : Selection O)
    (addresses : O → Closed captures) (rows : O → ContextualStoredRows.Row locals captures [] point)
    (before : Configuration (Closed captures) O) : Name → Set (ActiveTerm locals captures) :=
  fun n => {term | ∃ occurrence ∈ before.present,
    ResolvesTo (ContextualActivatedStep.frame locals captures before).equations
      (instantiate (ContextualSelectionViews.capturedTarget locals captures) (addresses occurrence)) n ∧
    ∃ scope, scope ∉ occupied ∧
      scope ≠ ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection) ∧
      term = ContextualStoredRows.viewAt locals captures scope
        (placedRows locals captures addresses rows occurrence)}

def eventProblem (occupied : Finset Nat) (selection : Selection O)
    (addresses : O → Closed captures) (rows : O → ContextualStoredRows.Row locals captures [] point)
    (before : Configuration (Closed captures) O)
    (rule : NamedSpaces.LocatedRule (ActiveTerm locals captures)) : EquationStore (ActiveTerm locals captures) :=
  (ContextualActivatedStep.frame locals captures before).equations ++
    eventEquations locals captures occupied selection addresses rows rule

def Reached (occupied : Finset Nat) (selection : Selection O) (known : Set (ActiveTerm locals captures))
    (addresses : O → Closed captures) (rows : O → ContextualStoredRows.Row locals captures [] point)
    (before : Configuration (Closed captures) O) : Name → Prop :=
  Reach (ContextualActivatedStep.frame locals captures before).equations known
    (storedViews locals captures occupied selection addresses rows before)

structure Held (known : Set (ActiveTerm locals captures)) (written : Set Name)
    (rule : NamedSpaces.LocatedRule (ActiveTerm locals captures)) : Prop where
  ports : ∀ term ∈ (lowerRule locals captures rule).take ++ (lowerRule locals captures rule).read, term ∈ known
  tells : KnowsEquations known rule.tell
  readSpaces : ∀ address ∈ rule.take.map Prod.fst ++ rule.read.map Prod.fst ++
      rule.checks.filterMap NamedSpaces.LocatedCheck.space?, address ∈ known
  produce : ∀ port ∈ rule.produce,
    (port.1 ∈ known ∧ place port.1 port.2 ∈ known) ∨
      (∃ n ∈ written, port.1 = name n ∧ port.2 ∈ known)

structure Admits (occupied : Finset Nat) (selection : Selection O)
    (known : Set (ActiveTerm locals captures)) (written : Set Name)
    (addresses : O → Closed captures) (rows : O → ContextualStoredRows.Row locals captures [] point)
    (before : Configuration (Closed captures) O)
    (rule : NamedSpaces.LocatedRule (ActiveTerm locals captures))
    (outputs : O → ActiveTerm locals captures) : Prop where
  held : Held locals captures known written rule
  resources : ContextualInteractionFactors.Resources selection before.present
  take_length : rule.take.length = selection.taken.length
  read_length : rule.read.length = selection.read.length
  outputs : selection.made.map outputs = (lowerRule locals captures rule).produce
  consistent : ContextualFrameUnifier.Solvable
    (eventProblem locals captures occupied selection addresses rows before rule)
  selected : ∀ occurrence ∈ selection.taken ++ selection.read, ∃ n,
    Reached locals captures occupied selection known addresses rows before n ∧
    ResolvesTo (ContextualActivatedStep.frame locals captures before).equations
      (instantiate (ContextualSelectionViews.capturedTarget locals captures) (addresses occurrence)) n
  resolved : ∀ address ∈ rule.spaces, ∃ n,
    ResolvesTo (eventProblem locals captures occupied selection addresses rows before rule) address n
  checks : ∀ check ∈ (lowerRule locals captures rule).checks,
    ContextualGuardSemantics.Ask locals
      (eventProblem locals captures occupied selection addresses rows before rule)
      (ContextualGuardedStep.guardRows locals captures (placedRows locals captures addresses rows)) before.present check

variable {locals captures}
    {occupied : Finset Nat} {selection : Selection O} {known : Set (ActiveTerm locals captures)}
    {written : Set Name} {addresses : O → Closed captures}
    {rows : O → ContextualStoredRows.Row locals captures [] point}
    {before : Configuration (Closed captures) O}
    {rule : NamedSpaces.LocatedRule (ActiveTerm locals captures)} {outputs : O → ActiveTerm locals captures}

theorem Admits.enabled (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs) :
    Enabled outputs before.present selection.commit :=
  ((ContextualInteractionFactors.resources_iff outputs selection before.present).mp admitted.resources).2.2

theorem Admits.present (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs)
    {occurrence : O} (selected : occurrence ∈ selection.taken ++ selection.read) : occurrence ∈ before.present := by
  rcases List.mem_append.mp selected with taken | read
  · exact admitted.enabled.taken_subset (by simpa [Selection.commit] using taken)
  · exact admitted.enabled.kept_subset (by simpa [Selection.commit] using read)

omit [DecidableEq Name] in
private theorem knows_uses {V : Type} {decl : V → MetaArity (base S point Name)}
    {known : Set (Closed decl)} {patterns values : List (Closed decl)}
    (patternsKnown : ∀ p ∈ patterns, p ∈ known) (valuesKnown : ∀ v ∈ values, v ∈ known) :
    KnowsEquations known (ContextualActivatedStep.useEquations patterns values) := by
  induction patterns generalizing values with
  | nil => simp [ContextualActivatedStep.useEquations,Selection.equations,KnowsEquations]
  | cons pattern rest ih =>
      cases values with
      | nil => simp [ContextualActivatedStep.useEquations,Selection.equations,KnowsEquations]
      | cons value tail =>
          intro equation member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨patternsKnown _ List.mem_cons_self,valuesKnown _ List.mem_cons_self⟩
          · exact ih (fun p pm => patternsKnown p (List.mem_cons_of_mem _ pm))
              (fun v vm => valuesKnown v (List.mem_cons_of_mem _ vm)) equation member

theorem Admits.input_knowledge
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs) :
    let views := storedViews locals captures occupied selection addresses rows before
    let allKnown := Knowledge known views (Reached locals captures occupied selection known addresses rows before)
    (∀ term ∈ (inputViews locals captures occupied selection addresses rows).1, term ∈ allKnown) ∧
    (∀ term ∈ (inputViews locals captures occupied selection addresses rows).2, term ∈ allKnown) := by
  constructor
  · intro term member
    obtain ⟨port,rfl⟩ := List.mem_ofFn.mp member
    obtain ⟨n,reached,atName⟩ := admitted.selected _ (List.mem_append_left _ (List.get_mem _ _))
    refine Or.inr ⟨n,reached,selection.taken.get port,
      admitted.present (List.mem_append_left _ (List.get_mem _ _)),atName,_,
      ContextualActivationScopes.at_fresh occupied _,?_,rfl⟩
    exact Ne.symm (ContextualActivationScopes.different_ports_have_different_scopes occupied
      (ContextualActivationScopes.rulePort_ne_takePort selection port))
  · intro term member
    obtain ⟨port,rfl⟩ := List.mem_ofFn.mp member
    obtain ⟨n,reached,atName⟩ := admitted.selected _ (List.mem_append_right _ (List.get_mem _ _))
    refine Or.inr ⟨n,reached,selection.read.get port,
      admitted.present (List.mem_append_right _ (List.get_mem _ _)),atName,_,
      ContextualActivationScopes.at_fresh occupied _,?_,rfl⟩
    exact Ne.symm (ContextualActivationScopes.different_ports_have_different_scopes occupied
      (ContextualActivationScopes.rulePort_ne_readPort selection port))

theorem Admits.equations_known
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs) :
    KnowsEquations (Knowledge known (storedViews locals captures occupied selection addresses rows before)
      (Reached locals captures occupied selection known addresses rows before))
      (eventEquations locals captures occupied selection addresses rows rule) := by
  intro equation member
  rcases List.mem_append.mp member with uses | tell
  · rcases List.mem_append.mp uses with taken | read
    · exact knows_uses (fun p pm => Or.inl (admitted.held.ports p (List.mem_append_left _ pm)))
        admitted.input_knowledge.1 equation taken
    · exact knows_uses (fun p pm => Or.inl (admitted.held.ports p (List.mem_append_right _ pm)))
        admitted.input_knowledge.2 equation read
  · exact ⟨Or.inl (admitted.held.tells equation tell).1,Or.inl (admitted.held.tells equation tell).2⟩

theorem Admits.resolved_in_firing_reached
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs)
    {term : ActiveTerm locals captures} (member : term ∈ known) {n : Name}
    (resolved : ResolvesTo (eventProblem locals captures occupied selection addresses rows before rule) term n) :
    Reached locals captures occupied selection known addresses rows before n :=
  SchematicReach.resolved_in_firing_reached admitted.consistent admitted.equations_known member resolved

theorem Admits.produced_lands
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs)
    {port : ActiveTerm locals captures × ActiveTerm locals captures} (member : port ∈ rule.produce) :
    ∃ n, ResolvesTo (eventProblem locals captures occupied selection addresses rows before rule) port.1 n ∧
      (Reached locals captures occupied selection known addresses rows before n ∨ n ∈ written) := by
  rcases admitted.held.produce port member with full | ⟨n,writtenN,atN,_⟩
  · obtain ⟨n,resolved⟩ := admitted.resolved port.1 (NamedSpaces.produce_space_mem member)
    exact ⟨n,resolved,Or.inl (admitted.resolved_in_firing_reached full.1 resolved)⟩
  · exact ⟨n,atN ▸ resolves_name _ n,Or.inr writtenN⟩

theorem Admits.read_space_reached
    (admitted : Admits locals captures occupied selection known written addresses rows before rule outputs)
    {address : ActiveTerm locals captures}
    (member : address ∈ rule.take.map Prod.fst ++ rule.read.map Prod.fst ++
      rule.checks.filterMap NamedSpaces.LocatedCheck.space?) {n : Name}
    (resolved : ResolvesTo (eventProblem locals captures occupied selection addresses rows before rule) address n) :
    Reached locals captures occupied selection known addresses rows before n :=
  admitted.resolved_in_firing_reached (admitted.held.readSpaces address member) resolved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach
