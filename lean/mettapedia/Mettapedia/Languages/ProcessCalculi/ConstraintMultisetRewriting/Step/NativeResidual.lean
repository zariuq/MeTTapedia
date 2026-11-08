import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeDiamond

/-!
# The native residual: a live firing read at another execution's published result

An execution `G` at a native state publishes the state `rawTarget G`: its frame adds the opened rule
locals of `G` and the solver's helper family, its knowledge is `G`'s information carried along the
inclusion of the old frame, and every occurrence `G` does not make keeps its row, carried along the
same inclusion with the private family extended (`retained`, `rows_of_not_made`).

## Carrying a firing to the published result

* **The information frame is carried** (`carry`): a firing's opened rule locals move to the scopes a
  later activation at the published result opens, `shift G` beyond their own, and the state's names
  move to their old copies. Rule locals and state names move by `sourceCarry`.
* **Preparation commutes with the carrying** (`prepared_rule_carried`, `prepared_take_carried`,
  `prepared_read_carried`, `addedEquations_carried`, `latent_carried`): the rule, take and read views,
  the equations the selection adds and the latent equations of the rows it reads, prepared at the
  published result, are the carried ones. Scopes are relocated, never shared: the rule locals of the
  later activation open beyond every scope the execution reserved (`scopeAt_shift`).

## The residual of a live firing

A **live firing** (`LiveFiring`) has its predicate queries given by patterns, no publication recipes,
and every output published as a live shared row. Its **residual** after `G` (`LiveFiring.residualAt`)
is the same firing read at `G`'s published result: the rule, outputs and query patterns carried.

* **Its information is `G`'s knowledge with the firing's own information carried**
  (`information_residualAt`), when the firing selects nothing `G` makes.
* **Its solutions are joint solutions** (`Joint`): a solution of the residual's information restricts
  to a solution of the firing's information and one of `G`'s, agreeing on the state's frame
  (`Joint.ofResidual`), and every joint solution amalgamates into a solution of the residual's
  information (`models_amalgam`).
* **Its guards and queries are the firing's, read at the restriction**, over the published rows
  (`region_residual`, `guard_residual`), when they see none of `G`'s takes and none of `G`'s live
  outputs at any joint solution.

**Each stays admitted after the other** (`LiveFiring.residual_admitted`, `LiveFiring.after`,
`LiveFiring.each_after`): a live firing that `G` leaves clear (`Clear`: disjoint takes and ports,
`G` takes nothing it reads, joint consistency, blindness to `G`'s takes and live outputs) is still
admitted at `G`'s published result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP (ScopedVar)
open ContextualPredicateQueryAdmission (nativeLabels matchingQuery)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- Models survive a later instantiation. -/
theorem models_compose_left {V W X : Type} {source : V → MetaArity S} {middle : W → MetaArity S}
    {target : X → MetaArity S} (later : Assignment middle target) {σ : Assignment source middle}
    {problem : ContextualResidual.Problem source} (solved : ContextualResidual.Models σ problem) :
    ContextualResidual.Models (Assignment.compose later σ) problem := by
  apply (ContextualResidual.models_mapProblem σ later problem).mp
  intro equation member
  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
  exact congrArg (instantiateObservation later) (solved original inside)

namespace NativeResidual

section Carry

variable {s : NativeState S O Γ sort} (G : ContextualConditionalExecution.Firing s.locals s.state)

/-- How far the scopes of an activation at the published result lie beyond those of one at the
state. -/
def shift : ℕ :=
  ContextualActivationScopes.start G.target.occupied -
    ContextualActivationScopes.start s.state.occupied

theorem start_le : ContextualActivationScopes.start s.state.occupied ≤
    ContextualActivationScopes.start G.target.occupied := by
  have inside : s.state.occupied ⊆ G.target.occupied :=
    (Finset.subset_union_left (s₂ := ContextualActivationScopes.reserved s.state.occupied G.selection)).trans
      (ContextualFreshFrameScopeLedger.old_scopes_retained _)
  have bound : s.state.occupied.sup id ≤ G.target.occupied.sup id := Finset.sup_mono inside
  unfold ContextualActivationScopes.start
  omega

/-- **Scopes are relocated, never shared**: every port of an activation at the published result
opens `shift G` beyond the same port at the state. -/
theorem scopeAt_shift {size : ℕ} (port : Fin size) :
    ContextualActivationScopes.scopeAt G.target.occupied port =
      ContextualActivationScopes.scopeAt s.state.occupied port + shift G := by
  have := start_le G
  unfold ContextualActivationScopes.scopeAt shift
  omega

/-- **The carrying of a firing's information frame** to the frame of a firing at the published
result: an opened rule local moves `shift G` scopes on, a state name to its old copy. -/
def carry : Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
    (ContextualActivatedStep.target (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations)
  | .inl name => generator (ContextualActivatedStep.target (ContextualPublication.privateFamily s.locals G.update.declaration)
      G.target.declarations) (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name)))
  | .inr name => generator (ContextualActivatedStep.target (ContextualPublication.privateFamily s.locals G.update.declaration)
      G.target.declarations) (.inr (.inl (.inr name)))

/-- Rule locals and state names, carried to the published result. -/
def sourceCarry : Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
    (ContextualActivatedStep.source (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations)
  | .inl name => generator (ContextualActivatedStep.source (ContextualPublication.privateFamily s.locals G.update.declaration)
      G.target.declarations) (.inl (.inl name))
  | .inr name => generator (ContextualActivatedStep.source (ContextualPublication.privateFamily s.locals G.update.declaration)
      G.target.declarations) (.inr (.inl (.inr name)))

/-- The state's names, carried to their old copies in the published frame. -/
def change : Assignment s.state.declarations G.target.declarations :=
  Assignment.compose (ContextualComputedFreshFrame.includeSource G.update)
    (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)

theorem includeSource_apply (name : ScopedVar s.Local ⊕ s.state.Names) :
    ContextualComputedFreshFrame.includeSource G.update name =
      generator G.target.declarations (.inl name) :=
  instantiate_generator (ContextualFreshFrame.includeOld (ContextualActivatedStep.target s.locals s.state.declarations)
    G.update.declaration ContextualComputedFreshFrame.noDeclarations) (.inl name)

theorem change_apply (name : s.state.Names) :
    change G name = generator G.target.declarations (.inl (.inr name)) := by
  show instantiate (ContextualComputedFreshFrame.includeSource G.update) (generator _ (.inr name)) = _
  rw [instantiate_generator, includeSource_apply]

/-- **The freshening square**: opening at a scope and then carrying is carrying and then opening
`shift G` scopes on. -/
theorem carry_freshening (scope : ℕ) :
    Assignment.compose (carry G) (ContextualFreshening.assignment s.locals s.state.declarations scope) =
      Assignment.compose
        (ContextualFreshening.assignment (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations (scope + shift G))
        (sourceCarry G) := by
  funext name
  cases name with
  | inl name =>
      exact (instantiate_generator (carry G) (.inl (ScopedVar.at scope name))).trans
        (instantiate_generator (ContextualFreshening.assignment (ContextualPublication.privateFamily s.locals
          G.update.declaration) G.target.declarations (scope + shift G)) (.inl (.inl name))).symm
  | inr name =>
      exact (instantiate_generator (carry G) (.inr name)).trans
        (instantiate_generator (ContextualFreshening.assignment (ContextualPublication.privateFamily s.locals
          G.update.declaration) G.target.declarations (scope + shift G)) (.inr (.inl (.inr name)))).symm

/-- **The capture square**: the state's names, carried as information or as knowledge, agree. -/
theorem carry_captured :
    Assignment.compose (carry G) (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
      Assignment.compose
        (ContextualSelectionViews.capturedTarget (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations)
        (change G) := by
  funext name
  exact (instantiate_generator (carry G) (.inr name)).trans
    ((congrArg (instantiate (ContextualSelectionViews.capturedTarget (ContextualPublication.privateFamily s.locals
      G.update.declaration) G.target.declarations)) (change_apply G name)).trans
      (instantiate_generator (ContextualSelectionViews.capturedTarget (ContextualPublication.privateFamily s.locals
        G.update.declaration) G.target.declarations) (.inl (.inr name)))).symm

/-- Extending the private family after carrying the captures is `sourceCarry`. -/
theorem sourceCarry_eq :
    Assignment.compose
        (ContextualPublication.includePrivate s.locals G.update.declaration
          (captures := G.target.declarations))
        (ContextualStoredRows.liftCaptures s.locals (change G)) = sourceCarry G := by
  funext name
  cases name with
  | inl name =>
      exact instantiate_generator (ContextualPublication.includePrivate s.locals G.update.declaration
        (captures := G.target.declarations)) (.inl name)
  | inr name =>
      exact (congrArg (fun term => instantiate (ContextualPublication.includePrivate s.locals G.update.declaration
          (captures := G.target.declarations))
          (instantiate (ContextualSelectionViews.capturedSource s.locals G.target.declarations) term))
          (change_apply G name)).trans
        ((congrArg (instantiate (ContextualPublication.includePrivate s.locals G.update.declaration
          (captures := G.target.declarations)))
          (instantiate_generator (ContextualSelectionViews.capturedSource s.locals G.target.declarations)
            (.inl (.inr name)))).trans
          (instantiate_generator (ContextualPublication.includePrivate s.locals G.update.declaration
            (captures := G.target.declarations)) (.inr (.inl (.inr name)))))

/-- **The row a retained occurrence holds** at the published result: its row carried along the
inclusion of the old frame, with the private family extended. -/
def retained (o : O) :
    ContextualConditionalRows.Row (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations Γ sort :=
  ContextualConditionalPublication.extendPrivate s.locals G.update.declaration _
    ((s.state.rows o).map s.locals s.state.declarations (change G))

/-- **An occurrence the execution does not make keeps its row**, carried. -/
theorem rows_of_not_made {o : O} (notMade : o ∉ G.selection.made) :
    G.target.rows o = retained G o := by
  show (if o ∈ G.selection.made then _ else _) = _
  rw [if_neg notMade]
  rfl

theorem retained_template (o : O) :
    ContextualStoredRows.asTemplate (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations (retained G o).value =
      instantiate (sourceCarry G)
        (ContextualStoredRows.asTemplate s.locals s.state.declarations (s.state.rows o).value) := by
  rw [retained, ContextualConditionalPublication.extended_template]
  show instantiate _ (ContextualStoredRows.asTemplate s.locals _
    ((s.state.rows o).value.map s.locals (change G))) = _
  rw [ContextualStoredRows.asTemplate_map, ← Assignment.instantiate_compose, sourceCarry_eq]

theorem retained_obligations (o : O) :
    (retained G o).obligations =
      ContextualResidual.mapProblem (sourceCarry G) (s.state.rows o).obligations := by
  show ContextualResidual.mapProblem (ContextualPublication.includePrivate _ _)
    (ContextualResidual.mapProblem (ContextualStoredRows.liftCaptures s.locals (change G))
      (s.state.rows o).obligations) = _
  rw [ContextualConditionalNaturality.map_problem_compose, sourceCarry_eq]

theorem carry_termAt (scope : ℕ) {Δ : Ctx S} {kind : S.Srt}
    (term : Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Δ kind) :
    instantiate (carry G) (ContextualFreshening.termAt s.locals s.state.declarations scope term) =
      ContextualFreshening.termAt (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations (scope + shift G)
        (instantiate (sourceCarry G) term) := by
  unfold ContextualFreshening.termAt
  rw [← Assignment.instantiate_compose, carry_freshening, Assignment.instantiate_compose]

theorem carry_obligationsAt (scope : ℕ) (o : O) :
    ContextualResidual.mapProblem (carry G)
        ((s.state.rows o).obligationsAt s.locals s.state.declarations scope) =
      (retained G o).obligationsAt _ _ (scope + shift G) := by
  unfold ContextualConditionalRows.Row.obligationsAt
  rw [ContextualConditionalNaturality.map_problem_compose, carry_freshening,
    ← ContextualConditionalNaturality.map_problem_compose, retained_obligations]

/-! ## Preparation commutes with the carrying -/

variable (selection : Selection O)
  (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort))

/-- **The rule views are carried**, whatever rows the two preparations read. -/
theorem prepared_rule_carried (rows : O → ContextualStoredRows.Row s.locals s.state.declarations Γ sort)
    (later : O → ContextualStoredRows.Row (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations Γ sort) :
    (ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied selection rule rows).rule.map
        (instantiate (carry G)) =
      (ContextualActivatedStep.prepared (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations
        G.target.occupied selection (rule.map (instantiate (sourceCarry G))) later).rule := by
  change (rule.map (ContextualFreshening.termAt s.locals s.state.declarations
      (ContextualActivationScopes.scopeAt s.state.occupied (ContextualActivationScopes.rulePort selection)))).map _ =
    (rule.map (instantiate (sourceCarry G))).map (ContextualFreshening.termAt _ _
      (ContextualActivationScopes.scopeAt G.target.occupied (ContextualActivationScopes.rulePort selection)))
  rw [OccurrenceRelabeling.rule_map_comp, OccurrenceRelabeling.rule_map_comp]
  apply congrArg (fun mapping => rule.map mapping)
  funext term
  show instantiate (carry G) (ContextualFreshening.termAt s.locals s.state.declarations _ term) =
    ContextualFreshening.termAt _ _ _ (instantiate (sourceCarry G) term)
  rw [carry_termAt, scopeAt_shift]

theorem prepared_take_carried (port : Fin selection.taken.length) :
    instantiate (carry G)
        ((ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied selection rule
          (fun o => (s.state.rows o).value)).taken port) =
      (ContextualActivatedStep.prepared (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations
        G.target.occupied selection (rule.map (instantiate (sourceCarry G)))
        (fun o => (retained G o).value)).taken port := by
  change instantiate (carry G) (ContextualFreshening.termAt s.locals s.state.declarations
      (ContextualActivationScopes.scopeAt s.state.occupied (ContextualActivationScopes.takePort selection port))
      (ContextualStoredRows.asTemplate s.locals s.state.declarations (s.state.rows (selection.taken.get port)).value)) =
    ContextualFreshening.termAt _ _
      (ContextualActivationScopes.scopeAt G.target.occupied (ContextualActivationScopes.takePort selection port))
      (ContextualStoredRows.asTemplate _ _ (retained G (selection.taken.get port)).value)
  rw [carry_termAt, retained_template, scopeAt_shift]

theorem prepared_read_carried (port : Fin selection.read.length) :
    instantiate (carry G)
        ((ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied selection rule
          (fun o => (s.state.rows o).value)).read port) =
      (ContextualActivatedStep.prepared (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations
        G.target.occupied selection (rule.map (instantiate (sourceCarry G)))
        (fun o => (retained G o).value)).read port := by
  change instantiate (carry G) (ContextualFreshening.termAt s.locals s.state.declarations
      (ContextualActivationScopes.scopeAt s.state.occupied (ContextualActivationScopes.readPort selection port))
      (ContextualStoredRows.asTemplate s.locals s.state.declarations (s.state.rows (selection.read.get port)).value)) =
    ContextualFreshening.termAt _ _
      (ContextualActivationScopes.scopeAt G.target.occupied (ContextualActivationScopes.readPort selection port))
      (ContextualStoredRows.asTemplate _ _ (retained G (selection.read.get port)).value)
  rw [carry_termAt, retained_template, scopeAt_shift]

/-- **The equations a selection adds are carried.** -/
theorem addedEquations_carried :
    ContextualFrameUnifier.mapProblem (carry G)
        (ContextualActivatedStep.addedEquations s.locals s.state.declarations s.state.occupied selection rule
          (fun o => (s.state.rows o).value)) =
      ContextualActivatedStep.addedEquations (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations
        G.target.occupied selection (rule.map (instantiate (sourceCarry G)))
        (fun o => (retained G o).value) := by
  have mapped := prepared_rule_carried G selection rule (fun o => (s.state.rows o).value)
    (fun o => (retained G o).value)
  have takes : List.map (instantiate (carry G))
      (ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied selection rule
        (fun o => (s.state.rows o).value)).rule.take =
      (ContextualActivatedStep.prepared (ContextualPublication.privateFamily s.locals G.update.declaration)
        G.target.declarations G.target.occupied selection (rule.map (instantiate (sourceCarry G)))
        (fun o => (retained G o).value)).rule.take := congrArg RuleInstance.take mapped
  have reads : List.map (instantiate (carry G))
      (ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied selection rule
        (fun o => (s.state.rows o).value)).rule.read =
      (ContextualActivatedStep.prepared (ContextualPublication.privateFamily s.locals G.update.declaration)
        G.target.declarations G.target.occupied selection (rule.map (instantiate (sourceCarry G)))
        (fun o => (retained G o).value)).rule.read := congrArg RuleInstance.read mapped
  have tells : ContextualFrameUnifier.mapProblem (carry G)
      (ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied selection rule
        (fun o => (s.state.rows o).value)).rule.tell =
      (ContextualActivatedStep.prepared (ContextualPublication.privateFamily s.locals G.update.declaration)
        G.target.declarations G.target.occupied selection (rule.map (instantiate (sourceCarry G)))
        (fun o => (retained G o).value)).rule.tell := congrArg RuleInstance.tell mapped
  have takenViews :
      (List.ofFn (ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied selection rule
          (fun o => (s.state.rows o).value)).taken).map (instantiate (carry G)) =
        List.ofFn (ContextualActivatedStep.prepared (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations
          G.target.occupied selection (rule.map (instantiate (sourceCarry G)))
          (fun o => (retained G o).value)).taken := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext (prepared_take_carried G selection rule))
  have readViews :
      (List.ofFn (ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied selection rule
          (fun o => (s.state.rows o).value)).read).map (instantiate (carry G)) =
        List.ofFn (ContextualActivatedStep.prepared (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations
          G.target.occupied selection (rule.map (instantiate (sourceCarry G)))
          (fun o => (retained G o).value)).read := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext (prepared_read_carried G selection rule))
  simp only [ContextualActivatedStep.addedEquations, ContextualTransportedActivation.map_append,
    ContextualTransportedActivation.map_useEquations, takes, reads, tells, takenViews, readViews]

/-- **The latent equations of the rows a selection reads are carried.** -/
theorem latent_carried :
    ContextualResidual.mapProblem (carry G)
        (ContextualConditionalExecution.latent s.locals s.state.declarations s.state.occupied selection
          s.state.rows) =
      ContextualConditionalExecution.latent (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations
        G.target.occupied selection (retained G) := by
  have append (first second : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)) :
      ContextualResidual.mapProblem (carry G) (first ++ second) =
        ContextualResidual.mapProblem (carry G) first ++ ContextualResidual.mapProblem (carry G) second :=
    List.map_append ..
  have flatten (parts : List (ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations))) :
      ContextualResidual.mapProblem (carry G) parts.flatten =
        (parts.map (ContextualResidual.mapProblem (carry G))).flatten :=
    List.map_flatten ..
  have takes : (fun port : Fin selection.taken.length => ContextualResidual.mapProblem (carry G)
      ((s.state.rows (selection.taken.get port)).obligationsAt s.locals s.state.declarations
        (ContextualActivationScopes.scopeAt s.state.occupied (ContextualActivationScopes.takePort selection port)))) =
      fun port => (retained G (selection.taken.get port)).obligationsAt _ _
        (ContextualActivationScopes.scopeAt G.target.occupied (ContextualActivationScopes.takePort selection port)) :=
    funext fun port => (carry_obligationsAt G _ _).trans (by rw [scopeAt_shift])
  have reads : (fun port : Fin selection.read.length => ContextualResidual.mapProblem (carry G)
      ((s.state.rows (selection.read.get port)).obligationsAt s.locals s.state.declarations
        (ContextualActivationScopes.scopeAt s.state.occupied (ContextualActivationScopes.readPort selection port)))) =
      fun port => (retained G (selection.read.get port)).obligationsAt _ _
        (ContextualActivationScopes.scopeAt G.target.occupied (ContextualActivationScopes.readPort selection port)) :=
    funext fun port => (carry_obligationsAt G _ _).trans (by rw [scopeAt_shift])
  unfold ContextualConditionalExecution.latent
  rw [append, flatten, flatten, List.map_ofFn, List.map_ofFn]
  exact congrArg₂ (fun first second => (List.ofFn first).flatten ++ (List.ofFn second).flatten) takes reads

end Carry

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- The latent equations read only the selected rows. -/
theorem latent_rows_congr {Local Names : Type} (locals : Local → MetaArity S) (declarations : Names → MetaArity S)
    (occupied : Finset ℕ) (selection : Selection O)
    {first second : O → ContextualConditionalRows.Row locals declarations Γ sort}
    (same : ∀ o ∈ selection.taken ++ selection.read, first o = second o) :
    ContextualConditionalExecution.latent locals declarations occupied selection first =
      ContextualConditionalExecution.latent locals declarations occupied selection second := by
  have takes : (fun port : Fin selection.taken.length =>
      (first (selection.taken.get port)).obligationsAt locals declarations
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port))) =
      fun port => (second (selection.taken.get port)).obligationsAt locals declarations
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port)) :=
    funext fun port => by rw [same _ (List.mem_append_left _ (List.get_mem _ _))]
  have reads : (fun port : Fin selection.read.length =>
      (first (selection.read.get port)).obligationsAt locals declarations
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port))) =
      fun port => (second (selection.read.get port)).obligationsAt locals declarations
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port)) :=
    funext fun port => by rw [same _ (List.mem_append_right _ (List.get_mem _ _))]
  unfold ContextualConditionalExecution.latent
  rw [takes, reads]

end NativeResidual

open NativeResidual

/-! ## Live firings and their residuals -/

/-- **A live native firing**: its predicate queries are given by patterns (with the occurrences each
must see), it has no publication recipes, and every output is published as a live shared row. -/
structure LiveFiring (s : NativeState S O Γ sort) : Type 1 where
  rule : RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort)
  selection : Selection O
  outputs : O → Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort
  patterns : List (Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort × Finset O)
  fuel : ℕ

namespace LiveFiring

variable {s : NativeState S O Γ sort}

/-- The native firing of a live firing. -/
noncomputable def toNative (f : LiveFiring s) : NativeFiring s where
  rule := f.rule
  selection := f.selection
  outputs := f.outputs
  reusable _ := false
  queries := f.patterns.map fun pattern => matchingQuery s.locals pattern.1 pattern.2
  fuel := f.fuel
  recipes _ := none
  recipes_made _ _ := rfl

/-- **The residual of a live firing after an execution**: the same firing read at the execution's
published result, with its rule, outputs and query patterns carried. -/
def residualAt (G : ContextualConditionalExecution.Firing s.locals s.state) (f : LiveFiring s) :
    LiveFiring (rawTarget G) where
  rule := f.rule.map (instantiate (sourceCarry G))
  selection := f.selection
  outputs o := instantiate (carry G) (f.outputs o)
  patterns := f.patterns.map fun pattern => (instantiate (carry G) pattern.1, pattern.2)
  fuel := f.fuel


end LiveFiring

namespace NativeResidual

variable {s : NativeState S O Γ sort}

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem mapProblem_append {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    (assignment : Assignment source target) (first second : ContextualResidual.Problem source) :
    ContextualResidual.mapProblem assignment (first ++ second) =
      ContextualResidual.mapProblem assignment first ++ ContextualResidual.mapProblem assignment second :=
  List.map_append ..

/-- The information of an execution's data at the state. -/
abbrev problemOf (s : NativeState S O Γ sort) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort)) :=
  ContextualConditionalExecution.information s.locals s.state.declarations s.state.occupied selection rule
    s.state.rows s.state.equations

/-- The firing's own part of its information: the equations its selection adds and the latent
equations of the rows it reads. -/
abbrev ownPart (s : NativeState S O Γ sort) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort)) :=
  ContextualResidual.observeProblem (ContextualActivatedStep.addedEquations s.locals s.state.declarations
      s.state.occupied selection rule (fun o => (s.state.rows o).value)) ++
    ContextualConditionalExecution.latent s.locals s.state.declarations s.state.occupied selection s.state.rows

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- The information of a firing: the knowledge, then the firing's own part. -/
theorem information_eq {Local Names : Type} (locals : Local → MetaArity S) (declarations : Names → MetaArity S)
    (occupied : Finset ℕ) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals declarations)) Γ sort))
    (rows : O → ContextualConditionalRows.Row locals declarations Γ sort)
    (before : ContextualResidual.Problem declarations) :
    ContextualConditionalExecution.information locals declarations occupied selection rule rows before =
      ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget locals declarations) before ++
        (ContextualResidual.observeProblem (ContextualActivatedStep.addedEquations locals declarations occupied
          selection rule (fun o => (rows o).value)) ++
          ContextualConditionalExecution.latent locals declarations occupied selection rows) :=
  List.append_assoc ..

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- A solution of a firing's information solves the knowledge and the firing's own part. -/
theorem models_problemOf_iff (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort))
    {W : Type} {next : W → MetaArity S}
    (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) next) :
    ContextualResidual.Models σ (problemOf s selection rule) ↔
      ContextualResidual.Models
          (Assignment.compose σ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations))
          s.state.equations ∧
        ContextualResidual.Models σ (ownPart s selection rule) := by
  rw [problemOf, information_eq, ContextualResidual.models_append, ContextualResidual.models_mapProblem]

section Residual

variable (G : ContextualConditionalExecution.Firing s.locals s.state)

/-- The information frame of a firing at the published result. -/
abbrev laterTarget :=
  ContextualActivatedStep.target (ContextualPublication.privateFamily s.locals G.update.declaration)
    G.target.declarations

/-- The knowledge of the published result, read at a later information frame. -/
abbrev laterCaptured :=
  ContextualSelectionViews.capturedTarget (ContextualPublication.privateFamily s.locals G.update.declaration)
    G.target.declarations

/-- **The information of a residual** is the published knowledge with the firing's own part
carried, when the firing selects nothing the execution makes. -/
theorem information_residualAt (f : LiveFiring s)
    (unmade : ∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ G.selection.made) :
    (f.residualAt G).toNative.information =
      ContextualResidual.mapProblem (laterCaptured G) G.target.equations ++
        ContextualResidual.mapProblem (carry G) (ownPart s f.selection f.rule) := by
  have values : ∀ o ∈ f.selection.taken ++ f.selection.read, (G.target.rows o).value = (retained G o).value :=
    fun o member => by rw [rows_of_not_made G (unmade o member)]
  have rows : ∀ o ∈ f.selection.taken ++ f.selection.read, G.target.rows o = retained G o :=
    fun o member => rows_of_not_made G (unmade o member)
  show ContextualConditionalExecution.information (ContextualPublication.privateFamily s.locals G.update.declaration)
      G.target.declarations G.target.occupied f.selection (f.rule.map (instantiate (sourceCarry G)))
      G.target.rows G.target.equations = _
  rw [information_eq (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations
      G.target.occupied f.selection (f.rule.map (instantiate (sourceCarry G))) G.target.rows G.target.equations,
    ContextualActivatedStep.addedEquations_rows_congr _ _ _ _ _ (first := fun o => (G.target.rows o).value) values,
    latent_rows_congr _ _ _ _ rows, ← addedEquations_carried, ← latent_carried,
    ContextualResidual.observeProblem_mapProblem, mapProblem_append]

/-- The solutions of a residual's information, through their two restrictions. -/
theorem residual_models_iff (f : LiveFiring s)
    (unmade : ∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ G.selection.made)
    {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next) :
    ContextualResidual.Models ρ (f.residualAt G).toNative.information ↔
      ContextualResidual.Models (Assignment.compose (Assignment.compose ρ (laterCaptured G))
          (ContextualComputedFreshFrame.includeSource G.update)) (problemOf s G.selection G.rule) ∧
        ContextualResidual.Models (Assignment.compose ρ (carry G)) (ownPart s f.selection f.rule) := by
  rw [information_residualAt G f unmade]
  refine (ContextualResidual.models_append _ _ _).trans (and_congr ?_ ?_)
  · exact (ContextualResidual.models_mapProblem _ _ _).trans
      (ContextualResidual.models_mapProblem (ContextualComputedFreshFrame.includeSource G.update) _ _)
  · exact ContextualResidual.models_mapProblem _ _ _

/-- The two restrictions of a later solution agree on the state's frame. -/
theorem restrictions_agree {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next) :
    Assignment.compose (Assignment.compose ρ (carry G))
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
      Assignment.compose (Assignment.compose (Assignment.compose ρ (laterCaptured G))
          (ContextualComputedFreshFrame.includeSource G.update))
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) := by
  funext name
  exact ((instantiate_generator (Assignment.compose ρ (carry G)) (.inr name)).trans
      (instantiate_generator ρ (.inr (.inl (.inr name))))).trans
    (((instantiate_generator (Assignment.compose (Assignment.compose ρ (laterCaptured G))
        (ContextualComputedFreshFrame.includeSource G.update)) (.inr name)).trans
      ((congrArg (instantiate (Assignment.compose ρ (laterCaptured G))) (includeSource_apply G (.inr name))).trans
        ((instantiate_generator (Assignment.compose ρ (laterCaptured G)) (.inl (.inr name))).trans
          (instantiate_generator ρ (.inr (.inl (.inr name)))))))).symm

end Residual

/-- **A joint solution**: solutions of two informations at one state, into one frame, agreeing on
the state's frame. -/
structure Joint (s : NativeState S O Γ sort)
    (first second : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations))
    (b : Frames.Frame S) : Type where
  left : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity
  right : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity
  left_models : ContextualResidual.Models left first
  right_models : ContextualResidual.Models right second
  agree : Assignment.compose left (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
    Assignment.compose right (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)

namespace Joint

variable {first second : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)}
  {b : Frames.Frame S}

/-- The joint solution read the other way round. -/
def swap (J : Joint s first second b) : Joint s second first b :=
  ⟨J.right, J.left, J.right_models, J.left_models, J.agree.symm⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem agree_at (J : Joint s first second b) (name : s.state.Names) : J.left (.inr name) = J.right (.inr name) :=
  (instantiate_generator J.left (.inr name)).symm.trans
    ((congrFun J.agree name).trans (instantiate_generator J.right (.inr name)))

/-- **A solution of a residual's information is a joint solution**: its two restrictions. -/
def ofResidual (G : ContextualConditionalExecution.Firing s.locals s.state) (f : LiveFiring s)
    (unmade : ∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ G.selection.made)
    {b : Frames.Frame S} (ρ : Assignment (laterTarget G) b.arity)
    (solved : ContextualResidual.Models ρ (f.residualAt G).toNative.information) :
    Joint s f.toNative.information (problemOf s G.selection G.rule) b where
  left := Assignment.compose ρ (carry G)
  right := Assignment.compose (Assignment.compose ρ (laterCaptured G)) (ContextualComputedFreshFrame.includeSource G.update)
  left_models := (models_problemOf_iff f.selection f.rule _).mpr
    ⟨(restrictions_agree G ρ).symm ▸
      ((models_problemOf_iff G.selection G.rule _).mp ((residual_models_iff G f unmade ρ).mp solved).1).1,
      ((residual_models_iff G f unmade ρ).mp solved).2⟩
  right_models := ((residual_models_iff G f unmade ρ).mp solved).1
  agree := restrictions_agree G ρ

end Joint

section Amalgam

variable (G : ContextualConditionalExecution.Firing s.locals s.state)
  {first second : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)}
  {b : Frames.Frame S}

/-- **The amalgamation of a joint solution** into a solution at a later information frame: the
carried rule locals read the first solution, the published frame the second, and the names neither
reaches (scoped private helpers, solver helpers) go to the first-order frame. -/
def amalgam (J : Joint s first second b) : Assignment (laterTarget G) (Frames.firstOrderFrame S).arity
  | .inl ⟨scope, .inl name⟩ =>
      instantiate (Frames.toFirstOrder b) (J.left (.inl ⟨scope - shift G, name⟩))
  | .inl ⟨scope, .inr helper⟩ => Frames.toFirstOrder ⟨_, laterTarget G⟩ (.inl ⟨scope, .inr helper⟩)
  | .inr (.inl name) => instantiate (Frames.toFirstOrder b) (J.right name)
  | .inr (.inr helper) => Frames.toFirstOrder ⟨_, laterTarget G⟩ (.inr (.inr helper))

theorem amalgam_left (J : Joint s first second b) :
    Assignment.compose (amalgam G J) (carry G) = Assignment.compose (Frames.toFirstOrder b) J.left := by
  funext name
  cases name with
  | inl name =>
      refine (instantiate_generator (amalgam G J) (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name)))).trans ?_
      show instantiate (Frames.toFirstOrder b) (J.left (.inl ⟨name.scope + shift G - shift G, name.name⟩)) =
        instantiate (Frames.toFirstOrder b) (J.left (.inl name))
      rw [Nat.add_sub_cancel]
  | inr name =>
      exact (instantiate_generator (amalgam G J) (.inr (.inl (.inr name)))).trans
        (congrArg (instantiate (Frames.toFirstOrder b)) (J.agree_at name).symm)

theorem amalgam_right (J : Joint s first second b) :
    Assignment.compose (Assignment.compose (amalgam G J) (laterCaptured G))
        (ContextualComputedFreshFrame.includeSource G.update) =
      Assignment.compose (Frames.toFirstOrder b) J.right := by
  funext name
  exact (congrArg (instantiate (Assignment.compose (amalgam G J) (laterCaptured G))) (includeSource_apply G name)).trans
    ((instantiate_generator (Assignment.compose (amalgam G J) (laterCaptured G)) (.inl name)).trans
      (instantiate_generator (amalgam G J) (.inr (.inl name))))

/-- **Every joint solution amalgamates into a solution of the residual's information.** -/
theorem models_amalgam (f : LiveFiring s)
    (unmade : ∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ G.selection.made)
    (J : Joint s f.toNative.information (problemOf s G.selection G.rule) b) :
    ContextualResidual.Models (amalgam G J) (f.residualAt G).toNative.information := by
  refine (residual_models_iff G f unmade (amalgam G J)).mpr ⟨?_, ?_⟩
  · rw [amalgam_right]
    exact models_compose_left _ J.right_models
  · rw [amalgam_left]
    exact models_compose_left _ ((models_problemOf_iff f.selection f.rule J.left).mp J.left_models).2

end Amalgam

/-! ## Guards and queries at the published result -/

section Guards

variable (G : ContextualConditionalExecution.Firing s.locals s.state)

theorem retained_candidate {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next) :
    Assignment.compose (Assignment.compose ρ (laterCaptured G)) (change G) =
      Assignment.compose (Assignment.compose ρ (carry G))
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) := by
  funext name
  exact ((congrArg (instantiate (Assignment.compose ρ (laterCaptured G))) (change_apply G name)).trans
      ((instantiate_generator (Assignment.compose ρ (laterCaptured G)) (.inl (.inr name))).trans
        (instantiate_generator ρ (.inr (.inl (.inr name)))))).trans
    ((instantiate_generator (Assignment.compose ρ (carry G)) (.inr name)).trans
      (instantiate_generator ρ (.inr (.inl (.inr name))))).symm

/-- **A retained occurrence is seen at the published result exactly when it is seen at the state**,
by the restriction of the solution. -/
theorem matches_retained {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next) {o : O}
    (notMade : o ∉ G.selection.made) (pattern : Term (signature S next) Γ sort) :
    ContextualConditionalRows.Matches (ContextualPublication.privateFamily s.locals G.update.declaration)
        (laterTarget G) ρ pattern
        (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
          G.target.declarations G.target.rows o) ↔
      ContextualConditionalRows.Matches s.locals (ContextualActivatedStep.target s.locals s.state.declarations)
        (Assignment.compose ρ (carry G)) pattern
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows o) := by
  show ContextualConditionalRows.Matches _ _ ρ pattern ((G.target.rows o).map _ _ (laterCaptured G)) ↔
    ContextualConditionalRows.Matches _ _ (Assignment.compose ρ (carry G)) pattern
      ((s.state.rows o).map _ _ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations))
  rw [rows_of_not_made G notMade, ContextualConditionalRows.matches_map_iff, ContextualConditionalRows.matches_map_iff,
    retained, ContextualConditionalPublication.extendPrivate_matches_iff, ContextualConditionalRows.matches_map_iff,
    retained_candidate]

/-- **A live output is seen at the published result exactly when the pattern is the output**, read
at the restriction to the published frame. -/
theorem matches_made {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next) {o : O}
    (made : o ∈ G.selection.made) (live : G.reusable o = false) (pattern : Term (signature S next) Γ sort) :
    ContextualConditionalRows.Matches (ContextualPublication.privateFamily s.locals G.update.declaration)
        (laterTarget G) ρ pattern
        (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
          G.target.declarations G.target.rows o) ↔
      pattern = instantiate (Assignment.compose (Assignment.compose ρ (laterCaptured G))
        (ContextualComputedFreshFrame.includeSource G.update)) (G.outputs o) := by
  show ContextualConditionalRows.Matches _ _ ρ pattern ((G.target.rows o).map _ _ (laterCaptured G)) ↔ _
  rw [G.shared_row o made live, ContextualConditionalRows.ofStored_map, ContextualConditionalRows.ofStored_matches_iff]
  show pattern = instantiate ρ (instantiate (laterCaptured G)
    (instantiate (ContextualComputedFreshFrame.includeSource G.update) (G.outputs o))) ↔ _
  rw [Assignment.instantiate_compose, Assignment.instantiate_compose]

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem absent_iff_region {Local Shared W : Type} {locals : Local → MetaArity S} {captures : Shared → MetaArity S}
    {next : W → MetaArity S} (candidate : Assignment captures next)
    (rows : O → ContextualConditionalRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) :
    ContextualConditionalGuards.Holds locals candidate rows world (.absent pattern) ↔
      ContextualConditionalGuards.region locals candidate rows world pattern = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [ContextualConditionalGuards.Holds, ContextualConditionalGuards.mem_region, not_and]

/-- **The region of a carried pattern at the published result is the region of the pattern at the
state**, read at the restriction, when the pattern sees none of the execution's takes and none of
its outputs. -/
theorem region_residual {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next)
    (pattern : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)
    (blindTaken : ∀ o ∈ G.selection.taken, ¬ ContextualConditionalRows.Matches s.locals
      (ContextualActivatedStep.target s.locals s.state.declarations) (Assignment.compose ρ (carry G))
      (instantiate (Assignment.compose ρ (carry G)) pattern)
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows o))
    (blindMade : ∀ o ∈ G.selection.made, ¬ ContextualConditionalRows.Matches
      (ContextualPublication.privateFamily s.locals G.update.declaration) (laterTarget G) ρ
      (instantiate ρ (instantiate (carry G) pattern))
      (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
        G.target.declarations G.target.rows o)) :
    ContextualConditionalGuards.region (ContextualPublication.privateFamily s.locals G.update.declaration) ρ
        (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
          G.target.declarations G.target.rows) G.target.present (instantiate (carry G) pattern) =
      ContextualConditionalGuards.region s.locals (Assignment.compose ρ (carry G))
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
        pattern := by
  have notMadeOf : ∀ {o : O}, o ∈ s.state.present → o ∉ G.selection.made := fun inP made =>
    Finset.disjoint_left.mp G.admitted.fresh (List.mem_toFinset.mpr made) inP
  have samePattern : instantiate ρ (instantiate (carry G) pattern) =
      instantiate (Assignment.compose ρ (carry G)) pattern := (Assignment.instantiate_compose _ _ _).symm
  ext o
  rw [ContextualConditionalGuards.mem_region, ContextualConditionalGuards.mem_region, samePattern]
  constructor
  · rintro ⟨inFire, seen⟩
    rcases mem_fire.mp inFire with ⟨inP, _⟩ | made
    · exact ⟨inP, (matches_retained G ρ (notMadeOf inP) _).mp seen⟩
    · exact absurd (samePattern ▸ seen) (blindMade o (List.mem_toFinset.mp made))
  · rintro ⟨inP, seen⟩
    have notTaken : o ∉ G.selection.taken := fun taken => blindTaken o taken seen
    exact ⟨mem_fire.mpr (Or.inl ⟨inP, fun taken => notTaken (List.mem_toFinset.mp taken)⟩),
      (matches_retained G ρ (notMadeOf inP) _).mpr seen⟩

/-- **A carried guard holds at the published result exactly when the guard holds at the state**,
read at the restriction, when it sees none of the execution's takes and none of its outputs. -/
theorem guard_residual {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next)
    (check : Check (Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort))
    (blindTaken : ∀ o ∈ G.selection.taken, ¬ GuardSees s.locals (Assignment.compose ρ (carry G))
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) check o)
    (blindMade : ∀ o ∈ G.selection.made, ¬ GuardSees (ContextualPublication.privateFamily s.locals G.update.declaration) ρ
      (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
        G.target.declarations G.target.rows) (check.map (instantiate (carry G))) o) :
    ContextualConditionalGuards.Holds (ContextualPublication.privateFamily s.locals G.update.declaration) ρ
        (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
          G.target.declarations G.target.rows) G.target.present (check.map (instantiate (carry G))) ↔
      ContextualConditionalGuards.Holds s.locals (Assignment.compose ρ (carry G))
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present check := by
  cases check with
  | equal first second =>
      show instantiate ρ (instantiate (carry G) first) = instantiate ρ (instantiate (carry G) second) ↔ _
      rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
      rfl
  | absent pattern =>
      dsimp only [Check.map]
      rw [absent_iff_region, absent_iff_region, region_residual G ρ pattern blindTaken blindMade]
  | count pattern cardinality =>
      show (ContextualConditionalGuards.region _ ρ _ _ (instantiate (carry G) pattern)).card = cardinality ↔
        (ContextualConditionalGuards.region _ _ _ _ pattern).card = cardinality
      rw [region_residual G ρ pattern blindTaken blindMade]

/-- **A carried pattern query holds at the published result exactly when the query holds at the
state**, read at the restriction, under the same blindness. -/
theorem query_residual {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next)
    (pattern : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)
    (seen : Finset O)
    (blindTaken : ∀ o ∈ G.selection.taken, ¬ ContextualConditionalRows.Matches s.locals
      (ContextualActivatedStep.target s.locals s.state.declarations) (Assignment.compose ρ (carry G))
      (instantiate (Assignment.compose ρ (carry G)) pattern)
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows o))
    (blindMade : ∀ o ∈ G.selection.made, ¬ ContextualConditionalRows.Matches
      (ContextualPublication.privateFamily s.locals G.update.declaration) (laterTarget G) ρ
      (instantiate ρ (instantiate (carry G) pattern))
      (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
        G.target.declarations G.target.rows o)) :
    ((matchingQuery (ContextualPublication.privateFamily s.locals G.update.declaration)
        (instantiate (carry G) pattern) seen).atSolution ⟨W, next, ρ⟩).Holds
        (nativeLabels (ContextualPublication.privateFamily s.locals G.update.declaration) G.target) G.target.present ↔
      ((matchingQuery s.locals pattern seen).atSolution ⟨W, next, Assignment.compose ρ (carry G)⟩).Holds
        (nativeLabels s.locals s.state) s.state.present := by
  refine (ContextualPredicateQueryAdmission.matching_holds_iff
    (ContextualPublication.privateFamily s.locals G.update.declaration) (instantiate (carry G) pattern) seen
    (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
      G.target.declarations G.target.rows) G.target.present ⟨W, next, ρ⟩).trans ?_
  refine Iff.trans ?_ (ContextualPredicateQueryAdmission.matching_holds_iff s.locals pattern seen
    (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
    ⟨W, next, Assignment.compose ρ (carry G)⟩).symm
  show ContextualConditionalGuards.region _ ρ _ _ _ = seen ↔
    ContextualConditionalGuards.region _ (Assignment.compose ρ (carry G)) _ _ _ = seen
  rw [region_residual G ρ pattern blindTaken blindMade]

end Guards

section Admission

/-- **What a guard sees among live outputs**: its pattern, read at one solution, is an output,
read at another. An equality guard sees nothing. -/
def SeesOutput {V W : Type} {declaration : V → MetaArity S} {next : W → MetaArity S}
    (left right : Assignment declaration next) (output : Term (signature S declaration) Γ sort) :
    Check (Term (signature S declaration) Γ sort) → Prop
  | .equal _ _ => False
  | .absent pattern => instantiate left pattern = instantiate right output
  | .count pattern _ => instantiate left pattern = instantiate right output

variable (G : ContextualConditionalExecution.Firing s.locals s.state)

/-- A carried guard sees an execution's live output at the published result exactly when it sees it
at the restrictions. -/
theorem guardSees_made_iff {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next) {o : O}
    (made : o ∈ G.selection.made) (live : G.reusable o = false)
    (check : Check (Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)) :
    GuardSees (ContextualPublication.privateFamily s.locals G.update.declaration) ρ
        (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
          G.target.declarations G.target.rows) (check.map (instantiate (carry G))) o ↔
      SeesOutput (Assignment.compose ρ (carry G))
        (Assignment.compose (Assignment.compose ρ (laterCaptured G)) (ContextualComputedFreshFrame.includeSource G.update))
        (G.outputs o) check := by
  cases check with
  | equal first second => exact Iff.rfl
  | absent pattern =>
      refine (matches_made G ρ made live _).trans ?_
      show _ ↔ instantiate (Assignment.compose ρ (carry G)) pattern = _
      rw [Assignment.instantiate_compose ρ (carry G) pattern]
  | count pattern cardinality =>
      refine (matches_made G ρ made live _).trans ?_
      show _ ↔ instantiate (Assignment.compose ρ (carry G)) pattern = _
      rw [Assignment.instantiate_compose ρ (carry G) pattern]

end Admission

end NativeResidual

open NativeResidual

/-- **An execution leaves a live firing clear**, stated with the execution's data at the state:
disjoint takes and produced ports; the execution takes nothing the firing reads; some joint solution
of the two informations exists; and at every joint solution the firing's guards and query patterns
see none of the execution's takes (with the state's rows) and none of its live outputs. -/
structure Clear {s : NativeState S O Γ sort} (f : LiveFiring s) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort))
    (outputs : O → Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort) : Prop where
  takes : Disjoint f.selection.taken.toFinset selection.taken.toFinset
  ports : Disjoint f.selection.made.toFinset selection.made.toFinset
  keeps : Disjoint selection.taken.toFinset f.selection.read.toFinset
  consistent : ∃ b : Frames.Frame S, Nonempty (Joint s f.toNative.information (problemOf s selection rule) b)
  blindTakes : ∀ (b : Frames.Frame S) (J : Joint s f.toNative.information (problemOf s selection rule) b),
    ∀ o ∈ selection.taken,
      (∀ check ∈ f.toNative.prepared.rule.checks, ¬ GuardSees s.locals J.left
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) check o) ∧
      ∀ pattern ∈ f.patterns, ¬ ContextualConditionalRows.Matches s.locals
        (ContextualActivatedStep.target s.locals s.state.declarations) J.left (instantiate J.left pattern.1)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows o)
  blindOutputs : ∀ (b : Frames.Frame S) (J : Joint s f.toNative.information (problemOf s selection rule) b),
    ∀ o ∈ selection.made,
      (∀ check ∈ f.toNative.prepared.rule.checks, ¬ SeesOutput J.left J.right (outputs o) check) ∧
      ∀ pattern ∈ f.patterns, instantiate J.left pattern.1 ≠ instantiate J.right (outputs o)

namespace LiveFiring

variable {s : NativeState S O Γ sort}

/-- **A live firing stays admitted after an execution that leaves it clear**: its residual is
admitted at the execution's published result. -/
theorem residual_admitted (G : ContextualConditionalExecution.Firing s.locals s.state) (f : LiveFiring s)
    (live : ∀ o ∈ G.selection.made, G.reusable o = false) (admitted : f.toNative.Realized)
    (clear : Clear f G.selection G.rule G.outputs) : (f.residualAt G).toNative.Realized := by
  obtain ⟨⟨takeNodup, madeNodup, takeLength, readLength, produce⟩, enabled, _, asks⟩ :=
    (native_admits_iff f.toNative).mp admitted
  have unmade : ∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ G.selection.made := by
    intro o member made
    have inP : o ∈ s.state.present := by
      rcases List.mem_append.mp member with taken | read
      · exact enabled.taken_subset (List.mem_toFinset.mpr taken)
      · exact enabled.kept_subset (List.mem_toFinset.mpr read)
    exact Finset.disjoint_left.mp G.admitted.fresh (List.mem_toFinset.mpr made) inP
  have mapped := prepared_rule_carried G f.selection f.rule (fun o => (s.state.rows o).value)
    (fun o => (G.target.rows o).value)
  apply (native_admits_iff _).mpr
  refine ⟨⟨takeNodup, madeNodup, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (List.length_map _).trans takeLength
  · exact (List.length_map _).trans readLength
  · exact (List.map_map (g := instantiate (carry G)) (f := f.outputs) (l := f.selection.made)).symm.trans
      ((congrArg (List.map (instantiate (carry G))) produce).trans (congrArg RuleInstance.produce mapped))
  · show Enabled (fun _ : O => ()) (fire s.state.present (G.selection.commit (T := Unit)))
      (f.selection.commit (T := Unit))
    refine ⟨fun o member => ?_, fun o member => ?_, enabled.apart, ?_, fun read member => by
      simp [Selection.commit] at member⟩
    · exact mem_fire.mpr (Or.inl ⟨enabled.taken_subset member,
        fun takenG => Finset.disjoint_left.mp clear.takes member takenG⟩)
    · exact mem_fire.mpr (Or.inl ⟨enabled.kept_subset member,
        fun takenG => Finset.disjoint_left.mp clear.keeps takenG member⟩)
    · rw [Finset.disjoint_left]
      intro o made inFire
      rcases mem_fire.mp inFire with ⟨inP, _⟩ | madeG
      · exact Finset.disjoint_left.mp enabled.fresh made inP
      · exact Finset.disjoint_left.mp clear.ports made madeG
  · obtain ⟨b, ⟨J⟩⟩ := clear.consistent
    exact ⟨Frames.firstOrderFrame S, amalgam G J, models_amalgam G f unmade J⟩
  · intro b ρ solved
    obtain ⟨checksHold, queriesHold⟩ := asks b (Joint.ofResidual G f unmade ρ solved).left
      (Joint.ofResidual G f unmade ρ solved).left_models
    have blindT := clear.blindTakes b (Joint.ofResidual G f unmade ρ solved)
    have blindO := clear.blindOutputs b (Joint.ofResidual G f unmade ρ solved)
    refine ⟨fun check member => ?_, fun query member => ?_⟩
    · have member' : check ∈ (RuleInstance.map (instantiate (carry G))
          (ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied f.selection f.rule
            (fun o => (s.state.rows o).value)).rule).checks :=
        (congrArg (fun checks => check ∈ checks) (congrArg RuleInstance.checks mapped)).mpr member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member'
      exact (guard_residual G ρ original (fun o taken => (blindT o taken).1 original inside)
        (fun o made sees => (blindO o made).1 original inside
          ((guardSees_made_iff G ρ made (live o made) original).mp sees))).mpr (checksHold original inside)
    · obtain ⟨carried, inCarried, rfl⟩ := List.mem_map.mp member
      obtain ⟨pattern, inPatterns, rfl⟩ := List.mem_map.mp inCarried
      exact (query_residual G ρ pattern.1 pattern.2 (fun o taken => (blindT o taken).2 pattern inPatterns)
        (fun o made seen => (blindO o made).2 pattern inPatterns
          ((Assignment.instantiate_compose ρ (carry G) pattern.1).trans
            ((matches_made G ρ made (live o made) _).mp seen)))).mpr
        (queriesHold _ (List.mem_map_of_mem inPatterns))

/-- **The native residual** of a live firing after another's step: the firing read at the published
result of the other's step. -/
noncomputable def residual {g : LiveFiring s} (second : g.toNative.Realized) (f : LiveFiring s) :
    NativeFiring (native.result g.toNative second) :=
  (f.residualAt (g.toNative.pinned second).firing).toNative

/-- **A live firing stays admitted after another live firing's step**, when the other leaves it
clear. -/
theorem after {f g : LiveFiring s} (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clear : Clear f g.selection g.rule g.outputs) : (residual second f).Realized := by
  have authored : (g.toNative.pinned second).firing.rule = g.rule := (g.toNative.pinned second).authored
  have selected : (g.toNative.pinned second).firing.selection = g.selection :=
    (g.toNative.pinned second).selected
  have values : (g.toNative.pinned second).firing.outputs = g.outputs := (g.toNative.pinned second).values
  have intents : (g.toNative.pinned second).firing.reusable = fun _ => false :=
    (g.toNative.pinned second).intents
  refine residual_admitted _ f (fun o _ => by rw [intents]) first ?_
  rw [authored, selected, values]
  exact clear

/-- **Each stays admitted after the other**: two live firings that leave each other clear are each
admitted at the other's published result. -/
theorem each_after {f g : LiveFiring s} (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    (residual second f).Realized ∧ (residual first g).Realized :=
  ⟨after first second clearF, after second first clearG⟩

end LiveFiring

#print axioms NativeResidual.scopeAt_shift
#print axioms NativeResidual.carry_freshening
#print axioms NativeResidual.carry_captured
#print axioms NativeResidual.rows_of_not_made
#print axioms NativeResidual.prepared_rule_carried
#print axioms NativeResidual.addedEquations_carried
#print axioms NativeResidual.latent_carried
#print axioms NativeResidual.information_residualAt
#print axioms NativeResidual.residual_models_iff
#print axioms NativeResidual.Joint.ofResidual
#print axioms NativeResidual.models_amalgam
#print axioms NativeResidual.matches_retained
#print axioms NativeResidual.matches_made
#print axioms NativeResidual.region_residual
#print axioms NativeResidual.guard_residual
#print axioms NativeResidual.query_residual
#print axioms NativeResidual.guardSees_made_iff
#print axioms LiveFiring.residual_admitted
#print axioms LiveFiring.after
#print axioms LiveFiring.each_after

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
