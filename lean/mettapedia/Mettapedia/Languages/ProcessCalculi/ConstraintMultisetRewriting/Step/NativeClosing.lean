import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidual

/-!
# The closing leg of the native diamond: one joint state, extended by dead names

Two live firings `f` and `g` that leave each other clear fire in either order (`Step/NativeResidual`):
`g` and then `f` read at `g`'s published result, or `f` and then `g` read at `f`'s. The two composite
published states have different frames: each order adds its own solver helpers, its own scoped
private helpers, and opens the second firing's rule locals at relocated scopes, so they need not be
equal, nor isomorphic as frames. They are **one state seen through two inclusions**.

## The joint state

The **joint frame** (`jointFrame`) has the opened rule locals of each firing in its own copy and the
state's names once (`leftCopy`, `rightCopy`, `sharedCopy`); exchanging the copies is `swapCopies`.
The **joint state** of the two firings is solver-free: its rows (`jointRows`) are each firing's
outputs as live rows in its own copy and every other row along the shared names; its knowledge
(`jointEquations`) is the first firing's information in its copy and the second's own part in the
other. Reading the copies the other way round exchanges the rows (`jointRows_swap`) and permutes the
knowledge (`jointEquations_swap_perm`).

## The closing leg

For every execution of the first firing and every execution of the residual (any solver return, any
budget), the composite published state is the joint state carried along an **inclusion**
(`inclusion`, by an injective map of names, `inclusionNames_injective`) and with the private family
extended twice (`lift`):

* **knowledge** (`equations_second`): the composite knowledge is the joint knowledge carried;
* **rows** (`rows_second`): every occurrence's row is the joint row carried;
* **present occurrences** (`present_second`): the composite physical result.

**The closing leg** (`LiveFiring.closing`): the two orders of two live firings that leave each other
clear reach states with the same present occurrences, with every row the carried joint row along each
order's inclusion, and with knowledge the carried joint knowledge, up to the order of its equations.

No property of the solver is used: its return enters the composite states only through helper names
that no row, equation or occurrence mentions. Every row, equation and occurrence of a composite state
is carried from the joint state, so the names an inclusion misses are dead. The interface's
isomorphisms of states (`Step.StateIso`) are isomorphisms of frames; an injective inclusion that
misses names is not one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire fire_comm)
open Mettapedia.Logic.LP (ScopedVar)
open NativeResidual

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeClosing

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Extending the private family commutes with carrying the captures.** -/
theorem extendPrivate_map {Local Added Shared Next : Type} (locals : Local → MetaArity S)
    (added : Added → MetaArity S) {captures : Shared → MetaArity S} {next : Next → MetaArity S}
    (change : Assignment captures next) (row : ContextualConditionalRows.Row locals captures Γ sort) :
    (ContextualConditionalPublication.extendPrivate locals added captures row).map
        (ContextualPublication.privateFamily locals added) captures change =
      ContextualConditionalPublication.extendPrivate locals added next (row.map locals captures change) := by
  have captured : Assignment.compose (ContextualPublication.includePrivate locals added (captures := next))
      (ContextualSelectionViews.capturedSource locals next) =
      ContextualSelectionViews.capturedSource (ContextualPublication.privateFamily locals added) next := by
    funext name
    exact instantiate_generator (ContextualPublication.includePrivate locals added (captures := next)) (.inr name)
  have square : Assignment.compose
      (ContextualStoredRows.liftCaptures (ContextualPublication.privateFamily locals added) change)
      (ContextualPublication.includePrivate locals added (captures := captures)) =
    Assignment.compose (ContextualPublication.includePrivate locals added (captures := next))
      (ContextualStoredRows.liftCaptures locals change) := by
    funext name
    cases name with
    | inl name =>
        exact (instantiate_generator
          (ContextualStoredRows.liftCaptures (ContextualPublication.privateFamily locals added) change)
            (.inl (.inl name))).trans
          (instantiate_generator (ContextualPublication.includePrivate locals added (captures := next))
            (.inl name)).symm
    | inr name =>
        exact (instantiate_generator
          (ContextualStoredRows.liftCaptures (ContextualPublication.privateFamily locals added) change)
            (.inr name)).trans
          ((congrArg (fun assignment => instantiate assignment (change name)) captured.symm).trans
            (Assignment.instantiate_compose _ _ _))
  cases row with
  | mk value obligations =>
      apply congrArg₂ ContextualConditionalRows.Row.mk
      · cases value with
        | schema body =>
            show ContextualStoredRows.Row.schema (instantiate _ (instantiate _ body)) =
              ContextualStoredRows.Row.schema (instantiate _ (instantiate _ body))
            rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, square]
        | shared value => rfl
      · show ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ obligations) =
          ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ obligations)
        rw [ContextualConditionalNaturality.map_problem_compose, ContextualConditionalNaturality.map_problem_compose,
          square]

/-! ## The joint frame -/

section JointFrame

variable (s : NativeState S O Γ sort)

/-- The names of the joint frame: the opened rule locals of the left firing, then those of the right
firing beside the state's names. -/
abbrev jointNames := ScopedVar s.Local ⊕ (ScopedVar s.Local ⊕ s.state.Names)

/-- **The joint frame** of two firings at one state. -/
abbrev jointFrame : jointNames s → MetaArity S :=
  Sum.elim (fun name => s.locals name.name) (ContextualActivatedStep.target s.locals s.state.declarations)

/-- The left firing's information frame in the joint frame. -/
def leftCopy : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) (jointFrame s)
  | .inl name => generator (jointFrame s) (.inl name)
  | .inr name => generator (jointFrame s) (.inr (.inr name))

/-- The right firing's information frame in the joint frame. -/
def rightCopy : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) (jointFrame s) :=
  fun name => generator (jointFrame s) (.inr name)

/-- The state's names in the joint frame. -/
def sharedCopy : Assignment s.state.declarations (jointFrame s) :=
  fun name => generator (jointFrame s) (.inr (.inr name))

/-- Exchanging the two copies. -/
def swapCopies : Assignment (jointFrame s) (jointFrame s)
  | .inl name => generator (jointFrame s) (.inr (.inl name))
  | .inr (.inl name) => generator (jointFrame s) (.inl name)
  | .inr (.inr name) => generator (jointFrame s) (.inr (.inr name))

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem leftCopy_captured :
    Assignment.compose (leftCopy s) (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
      sharedCopy s := by
  funext name
  exact instantiate_generator (leftCopy s) (.inr name)

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem rightCopy_captured :
    Assignment.compose (rightCopy s) (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
      sharedCopy s := by
  funext name
  exact instantiate_generator (rightCopy s) (.inr name)

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem swap_left : Assignment.compose (swapCopies s) (leftCopy s) = rightCopy s := by
  funext name
  cases name with
  | inl name => exact instantiate_generator (swapCopies s) (.inl name)
  | inr name => exact instantiate_generator (swapCopies s) (.inr (.inr name))

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem swap_right : Assignment.compose (swapCopies s) (rightCopy s) = leftCopy s := by
  funext name
  cases name with
  | inl name => exact instantiate_generator (swapCopies s) (.inr (.inl name))
  | inr name => exact instantiate_generator (swapCopies s) (.inr (.inr name))

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem swap_shared : Assignment.compose (swapCopies s) (sharedCopy s) = sharedCopy s := by
  funext name
  exact instantiate_generator (swapCopies s) (.inr (.inr name))

end JointFrame

/-! ## The joint state -/

section JointState

variable {s : NativeState S O Γ sort}

/-- **The rows of the joint state**: the left firing's outputs as live rows in its copy, the right
firing's in its copy, and every other occurrence's row along the state's names. -/
def jointRows (left : LiveFiring s) (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)
    (o : O) : ContextualConditionalRows.Row s.locals (jointFrame s) Γ sort :=
  if o ∈ left.selection.made then
    ContextualConditionalRows.ofStored _ _ (.shared (instantiate (leftCopy s) (left.outputs o)))
  else if o ∈ selection.made then
    ContextualConditionalRows.ofStored _ _ (.shared (instantiate (rightCopy s) (outputs o)))
  else (s.state.rows o).map s.locals s.state.declarations (sharedCopy s)

/-- **The knowledge of the joint state**: the right firing's information in its copy, and the left
firing's own part in the other. -/
def jointEquations (left : LiveFiring s) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort)) :
    ContextualResidual.Problem (jointFrame s) :=
  ContextualResidual.mapProblem (rightCopy s) (problemOf s selection rule) ++
    ContextualResidual.mapProblem (leftCopy s) (ownPart s left.selection left.rule)

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Reading the copies the other way round exchanges the rows.** -/
theorem jointRows_swap (f g : LiveFiring s)
    (ports : Disjoint f.selection.made.toFinset g.selection.made.toFinset) (o : O) :
    jointRows g f.selection f.outputs o =
      (jointRows f g.selection g.outputs o).map s.locals (jointFrame s) (swapCopies s) := by
  by_cases inF : o ∈ f.selection.made
  · have notG : o ∉ g.selection.made := fun inG =>
      Finset.disjoint_left.mp ports (List.mem_toFinset.mpr inF) (List.mem_toFinset.mpr inG)
    simp only [jointRows, inF, notG, ↓reduceIte]
    show _ = ContextualConditionalRows.ofStored _ _
      (.shared (instantiate (swapCopies s) (instantiate (leftCopy s) (f.outputs o))))
    rw [← Assignment.instantiate_compose, swap_left]
  · by_cases inG : o ∈ g.selection.made
    · simp only [jointRows, inF, inG, ↓reduceIte]
      show _ = ContextualConditionalRows.ofStored _ _
        (.shared (instantiate (swapCopies s) (instantiate (rightCopy s) (g.outputs o))))
      rw [← Assignment.instantiate_compose, swap_right]
    · simp only [jointRows, inF, inG, ↓reduceIte]
      rw [ContextualConditionalNaturality.row_map_compose, swap_shared]

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Reading the copies the other way round permutes the knowledge.** -/
theorem jointEquations_swap_perm (f g : LiveFiring s) :
    (jointEquations g f.selection f.rule).Perm
      (ContextualResidual.mapProblem (swapCopies s) (jointEquations f g.selection g.rule)) := by
  have rightKnowledge : ContextualResidual.mapProblem (rightCopy s)
      (ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)
        s.state.equations) =
      ContextualResidual.mapProblem (sharedCopy s) s.state.equations := by
    rw [ContextualConditionalNaturality.map_problem_compose, rightCopy_captured]
  have leftKnowledge : ContextualResidual.mapProblem (leftCopy s)
      (ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)
        s.state.equations) =
      ContextualResidual.mapProblem (sharedCopy s) s.state.equations := by
    rw [ContextualConditionalNaturality.map_problem_compose, leftCopy_captured]
  have lhs : jointEquations g f.selection f.rule =
      ContextualResidual.mapProblem (sharedCopy s) s.state.equations ++
        (ContextualResidual.mapProblem (rightCopy s) (ownPart s f.selection f.rule) ++
          ContextualResidual.mapProblem (leftCopy s) (ownPart s g.selection g.rule)) := by
    rw [jointEquations, problemOf, information_eq,
      mapProblem_append (rightCopy s) (ContextualResidual.mapProblem
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) s.state.equations),
      rightKnowledge, List.append_assoc]
  have rhs : ContextualResidual.mapProblem (swapCopies s) (jointEquations f g.selection g.rule) =
      ContextualResidual.mapProblem (sharedCopy s) s.state.equations ++
        (ContextualResidual.mapProblem (leftCopy s) (ownPart s g.selection g.rule) ++
          ContextualResidual.mapProblem (rightCopy s) (ownPart s f.selection f.rule)) := by
    rw [jointEquations, mapProblem_append (swapCopies s),
      ContextualConditionalNaturality.map_problem_compose (rightCopy s) (swapCopies s),
      ContextualConditionalNaturality.map_problem_compose (leftCopy s) (swapCopies s), swap_right, swap_left,
      problemOf, information_eq,
      mapProblem_append (leftCopy s) (ContextualResidual.mapProblem
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) s.state.equations),
      leftKnowledge, List.append_assoc]
  rw [lhs, rhs]
  exact List.Perm.append_left _ List.perm_append_comm

end JointState

/-! ## The inclusion of the joint state into a composite published state -/

section Inclusion

variable {s : NativeState S O Γ sort} (G : ContextualConditionalExecution.Firing s.locals s.state)
  (H : ContextualConditionalExecution.Firing (rawTarget G).locals (rawTarget G).state)

/-- The names of the joint frame in the composite published state: the left copy as the second
firing's relocated rule locals, the right copy as the first firing's, and the state's names. -/
def inclusionNames : jointNames s → H.target.Names
  | .inl name => .inl (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name)))
  | .inr (.inl name) => .inl (.inr (.inl (.inl name)))
  | .inr (.inr name) => .inl (.inr (.inl (.inr name)))

/-- Reading the composite published state's names back into the joint frame, where they come from
it. -/
def retract : H.target.Names → Option (jointNames s)
  | .inl (.inl ⟨scope, .inl name⟩) => some (.inl ⟨scope - shift G, name⟩)
  | .inl (.inr (.inl (.inl name))) => some (.inr (.inl name))
  | .inl (.inr (.inl (.inr name))) => some (.inr (.inr name))
  | _ => none

theorem retract_inclusionNames (name : jointNames s) :
    retract G H (inclusionNames G H name) = some name := by
  rcases name with ⟨scope, name⟩ | name | name
  · show some (Sum.inl ⟨scope + shift G - shift G, name⟩ : jointNames s) = _
    rw [Nat.add_sub_cancel]
  · rfl
  · rfl

/-- **The inclusion is injective**: the names it misses are dead. -/
theorem inclusionNames_injective : Function.Injective (inclusionNames G H) := by
  intro first second same
  have back := congrArg (retract G H) same
  rwa [retract_inclusionNames, retract_inclusionNames, Option.some_inj] at back

/-- **The inclusion of the joint frame** into the composite published state, name by name as
`inclusionNames`. -/
def inclusion : Assignment (jointFrame s) H.target.declarations
  | .inl name => generator H.target.declarations (.inl (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name))))
  | .inr (.inl name) => generator H.target.declarations (.inl (.inr (.inl (.inl name))))
  | .inr (.inr name) => generator H.target.declarations (.inl (.inr (.inl (.inr name))))

/-- A row of the joint state, carried to the composite published state with the private family
extended by both helper families. -/
def lift (ι : Assignment (jointFrame s) H.target.declarations)
    (row : ContextualConditionalRows.Row s.locals (jointFrame s) Γ sort) :
    ContextualConditionalRows.Row (ContextualPublication.privateFamily
      (ContextualPublication.privateFamily s.locals G.update.declaration) H.update.declaration)
      H.target.declarations Γ sort :=
  ContextualConditionalPublication.extendPrivate (ContextualPublication.privateFamily s.locals G.update.declaration)
    H.update.declaration H.target.declarations
    (ContextualConditionalPublication.extendPrivate s.locals G.update.declaration H.target.declarations
      (row.map s.locals (jointFrame s) ι))

theorem lift_shared (ι : Assignment (jointFrame s) H.target.declarations)
    (value : Term (signature S (jointFrame s)) Γ sort) :
    lift G H ι (ContextualConditionalRows.ofStored _ _ (.shared value)) =
      ContextualConditionalRows.ofStored _ _ (.shared (instantiate ι value)) :=
  rfl

theorem lift_map (ι : Assignment (jointFrame s) H.target.declarations)
    (change : Assignment (jointFrame s) (jointFrame s))
    (row : ContextualConditionalRows.Row s.locals (jointFrame s) Γ sort) :
    lift G H ι (row.map s.locals (jointFrame s) change) = lift G H (Assignment.compose ι change) row := by
  unfold lift
  rw [ContextualConditionalNaturality.row_map_compose]

/-- The first firing's information frame enters through its knowledge. -/
theorem inclusion_right :
    Assignment.compose (inclusion G H) (rightCopy s) =
      Assignment.compose (ContextualComputedFreshFrame.includeSource H.update)
        (Assignment.compose (laterCaptured G) (ContextualComputedFreshFrame.includeSource G.update)) := by
  funext name
  have chain : Assignment.compose (ContextualComputedFreshFrame.includeSource H.update)
      (Assignment.compose (laterCaptured G) (ContextualComputedFreshFrame.includeSource G.update)) name =
      generator H.target.declarations (.inl (.inr (.inl name))) :=
    (congrArg (fun term => instantiate (ContextualComputedFreshFrame.includeSource H.update)
        (instantiate (laterCaptured G) term)) (includeSource_apply G name)).trans
      ((congrArg (instantiate (ContextualComputedFreshFrame.includeSource H.update))
        (instantiate_generator (laterCaptured G) (.inl name))).trans
        ((instantiate_generator (ContextualComputedFreshFrame.includeSource H.update) (.inr (.inl name))).trans
          (includeSource_apply (s := rawTarget G) H (.inr (.inl name)))))
  refine Eq.trans ?_ chain.symm
  cases name with
  | inl name => exact instantiate_generator (inclusion G H) (.inr (.inl name))
  | inr name => exact instantiate_generator (inclusion G H) (.inr (.inr name))

/-- The first firing's outputs enter through the second firing's carrying of its old frame. -/
theorem inclusion_right_outputs :
    Assignment.compose (inclusion G H) (rightCopy s) =
      Assignment.compose (change (s := rawTarget G) H) (ContextualComputedFreshFrame.includeSource G.update) := by
  funext name
  have chain : Assignment.compose (change (s := rawTarget G) H)
      (ContextualComputedFreshFrame.includeSource G.update) name =
      generator H.target.declarations (.inl (.inr (.inl name))) :=
    (congrArg (instantiate (change (s := rawTarget G) H)) (includeSource_apply G name)).trans
      ((instantiate_generator (change (s := rawTarget G) H) (.inl name)).trans
        (change_apply (s := rawTarget G) H (.inl name)))
  refine Eq.trans ?_ chain.symm
  cases name with
  | inl name => exact instantiate_generator (inclusion G H) (.inr (.inl name))
  | inr name => exact instantiate_generator (inclusion G H) (.inr (.inr name))

/-- The second firing's information frame enters through its carrying. -/
theorem inclusion_left :
    Assignment.compose (inclusion G H) (leftCopy s) =
      Assignment.compose (ContextualComputedFreshFrame.includeSource H.update) (carry G) := by
  funext name
  cases name with
  | inl name =>
      exact (instantiate_generator (inclusion G H) (.inl name)).trans
        ((instantiate_generator (ContextualComputedFreshFrame.includeSource H.update)
          (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name)))).trans
          (includeSource_apply (s := rawTarget G) H (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name))))).symm
  | inr name =>
      exact (instantiate_generator (inclusion G H) (.inr (.inr name))).trans
        ((instantiate_generator (ContextualComputedFreshFrame.includeSource H.update) (.inr (.inl (.inr name)))).trans
          (includeSource_apply (s := rawTarget G) H (.inr (.inl (.inr name))))).symm

/-- The state's names enter through both carryings. -/
theorem inclusion_shared :
    Assignment.compose (inclusion G H) (sharedCopy s) =
      Assignment.compose (change (s := rawTarget G) H) (change G) := by
  funext name
  exact (instantiate_generator (inclusion G H) (.inr (.inr name))).trans
    ((congrArg (instantiate (change (s := rawTarget G) H)) (change_apply G name)).trans
      ((instantiate_generator (change (s := rawTarget G) H) (.inl (.inr name))).trans
        (change_apply (s := rawTarget G) H (.inl (.inr name))))).symm

end Inclusion

/-! ## A composite published state is the joint state carried -/

section Composite

variable {s : NativeState S O Γ sort} (G : ContextualConditionalExecution.Firing s.locals s.state)
  (H : ContextualConditionalExecution.Firing (rawTarget G).locals (rawTarget G).state)

/-- **An execution of a residual**: an execution at the published result with the residual's data. -/
structure Executes (f : LiveFiring s) : Prop where
  rule : H.rule = (f.residualAt G).rule
  selection : H.selection = f.selection
  outputs : H.outputs = (f.residualAt G).outputs
  live : ∀ o ∈ H.selection.made, H.reusable o = false

variable {G H}

/-- **The composite knowledge is the joint knowledge carried.** -/
theorem equations_second {f : LiveFiring s} (executes : Executes G H f)
    (unmade : ∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ G.selection.made) :
    H.target.equations = ContextualResidual.mapProblem (inclusion G H) (jointEquations f G.selection G.rule) := by
  have key : ContextualConditionalExecution.information
      (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations G.target.occupied
      H.selection H.rule G.target.rows G.target.equations = (f.residualAt G).toNative.information := by
    rw [executes.selection, executes.rule]
    rfl
  calc H.target.equations
      = ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource H.update)
          (ContextualResidual.mapProblem (laterCaptured G) G.target.equations ++
            ContextualResidual.mapProblem (carry G) (ownPart s f.selection f.rule)) :=
        congrArg (ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource H.update))
          (key.trans (information_residualAt G f unmade))
    _ = ContextualResidual.mapProblem (Assignment.compose (inclusion G H) (rightCopy s))
            (problemOf s G.selection G.rule) ++
          ContextualResidual.mapProblem (Assignment.compose (inclusion G H) (leftCopy s))
            (ownPart s f.selection f.rule) := by
        rw [inclusion_right, inclusion_left]
        exact (mapProblem_append _ _ _).trans (congrArg₂ (· ++ ·)
          ((congrArg (ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource H.update))
            (ContextualConditionalNaturality.map_problem_compose (ContextualComputedFreshFrame.includeSource G.update)
              (laterCaptured G) (problemOf s G.selection G.rule))).trans
            (ContextualConditionalNaturality.map_problem_compose _ _ _))
          (ContextualConditionalNaturality.map_problem_compose _ _ _))
    _ = ContextualResidual.mapProblem (inclusion G H) (jointEquations f G.selection G.rule) := by
        rw [jointEquations, mapProblem_append (inclusion G H),
          ContextualConditionalNaturality.map_problem_compose (rightCopy s) (inclusion G H),
          ContextualConditionalNaturality.map_problem_compose (leftCopy s) (inclusion G H)]

/-- **Every composite row is the joint row carried.** -/
theorem rows_second {f : LiveFiring s} (executes : Executes G H f)
    (live : ∀ o ∈ G.selection.made, G.reusable o = false) (o : O) :
    H.target.rows o = lift G H (inclusion G H) (jointRows f G.selection G.outputs o) := by
  by_cases inF : o ∈ f.selection.made
  · have inH : o ∈ H.selection.made := by rw [executes.selection]; exact inF
    have joint : jointRows f G.selection G.outputs o =
        ContextualConditionalRows.ofStored _ _ (.shared (instantiate (leftCopy s) (f.outputs o))) := if_pos inF
    rw [joint, lift_shared, H.shared_row o inH (executes.live o inH), executes.outputs]
    exact congrArg (fun term => ContextualConditionalRows.ofStored _ _ (.shared term))
      ((Assignment.instantiate_compose _ _ _).symm.trans
        ((congrArg (fun assignment => instantiate assignment (f.outputs o)) (inclusion_left G H).symm).trans
          (Assignment.instantiate_compose _ _ _)))
  · have notH : o ∉ H.selection.made := by rw [executes.selection]; exact inF
    rw [rows_of_not_made (s := rawTarget G) H notH]
    by_cases inG : o ∈ G.selection.made
    · have joint : jointRows f G.selection G.outputs o =
          ContextualConditionalRows.ofStored _ _ (.shared (instantiate (rightCopy s) (G.outputs o))) := by
        unfold jointRows
        rw [if_neg inF, if_pos inG]
      rw [joint, lift_shared]
      show ContextualConditionalPublication.extendPrivate _ _ _
          ((G.target.rows o).map _ _ (change (s := rawTarget G) H)) = _
      rw [G.shared_row o inG (live o inG)]
      exact congrArg (fun term => ContextualConditionalRows.ofStored _ _ (.shared term))
        ((Assignment.instantiate_compose _ _ _).symm.trans
          ((congrArg (fun assignment => instantiate assignment (G.outputs o)) (inclusion_right_outputs G H).symm).trans
            (Assignment.instantiate_compose _ _ _)))
    · have joint : jointRows f G.selection G.outputs o =
          (s.state.rows o).map s.locals s.state.declarations (sharedCopy s) := by
        unfold jointRows
        rw [if_neg inF, if_neg inG]
      rw [joint]
      show ContextualConditionalPublication.extendPrivate _ _ _
          ((G.target.rows o).map _ _ (change (s := rawTarget G) H)) = _
      rw [rows_of_not_made G inG]
      exact (congrArg (ContextualConditionalPublication.extendPrivate
          (ContextualPublication.privateFamily s.locals G.update.declaration) H.update.declaration
          H.target.declarations)
          (extendPrivate_map s.locals G.update.declaration (change (s := rawTarget G) H)
            ((s.state.rows o).map s.locals s.state.declarations (change G)))).trans
        (congrArg (fun row => ContextualConditionalPublication.extendPrivate
            (ContextualPublication.privateFamily s.locals G.update.declaration) H.update.declaration
            H.target.declarations
            (ContextualConditionalPublication.extendPrivate s.locals G.update.declaration H.target.declarations row))
          ((ContextualConditionalNaturality.row_map_compose s.locals (change G) (change (s := rawTarget G) H)
              (s.state.rows o)).trans
            ((congrArg (fun assignment => (s.state.rows o).map s.locals s.state.declarations assignment)
              (inclusion_shared G H).symm).trans
              (ContextualConditionalNaturality.row_map_compose s.locals (sharedCopy s) (inclusion G H)
                (s.state.rows o)).symm)))

/-- **The composite present occurrences** are the composite physical result. -/
theorem present_second {f : LiveFiring s} (executes : Executes G H f) :
    H.target.present = fire (fire s.state.present (G.selection.commit (T := Unit))) (f.selection.commit (T := Unit)) := by
  show fire (fire s.state.present (G.selection.commit (T := Unit))) (H.selection.commit (T := Unit)) = _
  rw [executes.selection]

end Composite

end NativeClosing

open NativeClosing

namespace LiveFiring

variable {s : NativeState S O Γ sort}

/-- The execution pinned by a live firing's step. -/
noncomputable abbrev execution {f : LiveFiring s} (first : f.toNative.Realized) :
    ContextualConditionalExecution.Firing s.locals s.state :=
  (f.toNative.pinned first).firing

/-- The execution pinned by the step of a residual. -/
noncomputable abbrev residualExecution {f g : LiveFiring s} (first : f.toNative.Realized)
    (second : g.toNative.Realized) (clear : Clear f g.selection g.rule g.outputs) :
    ContextualConditionalExecution.Firing (rawTarget (execution second)).locals (rawTarget (execution second)).state :=
  ((residual second f).pinned (after first second clear)).firing

theorem execution_data {f : LiveFiring s} (first : f.toNative.Realized) :
    (execution first).rule = f.rule ∧ (execution first).selection = f.selection ∧
      (execution first).outputs = f.outputs ∧ (execution first).reusable = fun _ => false :=
  ⟨(f.toNative.pinned first).authored, (f.toNative.pinned first).selected, (f.toNative.pinned first).values,
    (f.toNative.pinned first).intents⟩

theorem residualExecution_executes {f g : LiveFiring s} (first : f.toNative.Realized)
    (second : g.toNative.Realized) (clear : Clear f g.selection g.rule g.outputs) :
    Executes (execution second) (residualExecution first second clear) f where
  rule := ((residual second f).pinned (after first second clear)).authored
  selection := ((residual second f).pinned (after first second clear)).selected
  outputs := ((residual second f).pinned (after first second clear)).values
  live o _ := by
    have intents : (residualExecution first second clear).reusable = fun _ => false :=
      ((residual second f).pinned (after first second clear)).intents
    rw [intents]

/-- The step of the residual publishes the state of its pinned execution. -/
theorem result_residual {f g : LiveFiring s} (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clear : Clear f g.selection g.rule g.outputs) :
    native.result (residual second f) (after first second clear) = rawTarget (residualExecution first second clear) :=
  rfl

/-- **The closing leg of the native diamond.** Two live firings that leave each other clear fire in
either order, `g` then `f` (state `rawTarget H`) or `f` then `g` (state `rawTarget H'`). Both are the
one joint state, carried along each order's inclusion: their present occurrences agree, every row is
the carried joint row, and the knowledge is the carried joint knowledge, up to the order of its
equations. Every solver return is allowed. -/
theorem closing {f g : LiveFiring s} (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    (rawTarget (residualExecution first second clearF)).state.present =
        (rawTarget (residualExecution second first clearG)).state.present ∧
      (∀ o, (rawTarget (residualExecution first second clearF)).state.rows o =
          lift (execution second) (residualExecution first second clearF)
            (inclusion (execution second) (residualExecution first second clearF))
            (jointRows f g.selection g.outputs o) ∧
        (rawTarget (residualExecution second first clearG)).state.rows o =
          lift (execution first) (residualExecution second first clearG)
            (Assignment.compose (inclusion (execution first) (residualExecution second first clearG))
              (swapCopies s))
            (jointRows f g.selection g.outputs o)) ∧
      (rawTarget (residualExecution first second clearF)).state.equations =
          ContextualResidual.mapProblem (inclusion (execution second) (residualExecution first second clearF))
            (jointEquations f g.selection g.rule) ∧
      ((rawTarget (residualExecution second first clearG)).state.equations).Perm
        (ContextualResidual.mapProblem
          (Assignment.compose (inclusion (execution first) (residualExecution second first clearG)) (swapCopies s))
          (jointEquations f g.selection g.rule)) := by
  obtain ⟨_, selectedF, valuesF, intentsF⟩ := execution_data first
  obtain ⟨authoredG, selectedG, valuesG, intentsG⟩ := execution_data second
  have ruleF : (execution first).rule = f.rule := (execution_data first).1
  obtain ⟨_, enabledF, _, _⟩ := (native_admits_iff f.toNative).mp first
  obtain ⟨_, enabledG, _, _⟩ := (native_admits_iff g.toNative).mp second
  have unmadeOf : ∀ {x y : LiveFiring s} (admittedX : x.toNative.Realized) (admittedY : y.toNative.Realized),
      ∀ o ∈ x.selection.taken ++ x.selection.read, o ∉ (execution admittedY).selection.made := by
    intro x y admittedX admittedY o member made
    obtain ⟨_, enabledX, _, _⟩ := (native_admits_iff x.toNative).mp admittedX
    have inP : o ∈ s.state.present := by
      rcases List.mem_append.mp member with taken | read
      · exact enabledX.taken_subset (List.mem_toFinset.mpr taken)
      · exact enabledX.kept_subset (List.mem_toFinset.mpr read)
    exact Finset.disjoint_left.mp (execution admittedY).admitted.fresh (List.mem_toFinset.mpr made) inP
  have executesF := residualExecution_executes first second clearF
  have executesG := residualExecution_executes second first clearG
  have liveG : ∀ o ∈ (execution second).selection.made, (execution second).reusable o = false :=
    fun o _ => by rw [intentsG]
  have liveF : ∀ o ∈ (execution first).selection.made, (execution first).reusable o = false :=
    fun o _ => by rw [intentsF]
  have physical : fire (fire s.state.present ((execution second).selection.commit (T := Unit)))
      (f.selection.commit (T := Unit)) =
      fire (fire s.state.present ((execution first).selection.commit (T := Unit))) (g.selection.commit (T := Unit)) := by
    rw [selectedG, selectedF]
    exact fire_comm enabledG enabledF
  have rowsF : ∀ o, jointRows f (execution second).selection (execution second).outputs o =
      jointRows f g.selection g.outputs o := fun o => by rw [selectedG, valuesG]
  have rowsG : ∀ o, jointRows g (execution first).selection (execution first).outputs o =
      jointRows g f.selection f.outputs o := fun o => by rw [selectedF, valuesF]
  have equationsF : jointEquations f (execution second).selection (execution second).rule =
      jointEquations f g.selection g.rule := by rw [selectedG, authoredG]
  have equationsG : jointEquations g (execution first).selection (execution first).rule =
      jointEquations g f.selection f.rule := by rw [selectedF, ruleF]
  refine ⟨(present_second executesF).trans (physical.trans (present_second executesG).symm), fun o => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (rows_second executesF liveG o).trans (congrArg _ (rowsF o))
  · exact (rows_second executesG liveF o).trans ((congrArg _ ((rowsG o).trans
      (jointRows_swap f g clearF.ports o))).trans (lift_map _ _ _ _ _))
  · exact (equations_second executesF (unmadeOf first second)).trans (congrArg _ equationsF)
  · refine (List.Perm.of_eq ((equations_second executesG (unmadeOf second first)).trans
      (congrArg _ equationsG))).trans ?_
    exact ((jointEquations_swap_perm f g).map _).trans (List.Perm.of_eq
      (ContextualConditionalNaturality.map_problem_compose _ _ _))

end LiveFiring

#print axioms NativeClosing.extendPrivate_map
#print axioms NativeClosing.jointRows_swap
#print axioms NativeClosing.jointEquations_swap_perm
#print axioms NativeClosing.inclusionNames_injective
#print axioms NativeClosing.inclusion_right
#print axioms NativeClosing.inclusion_left
#print axioms NativeClosing.inclusion_shared
#print axioms NativeClosing.equations_second
#print axioms NativeClosing.rows_second
#print axioms NativeClosing.present_second
#print axioms LiveFiring.result_residual
#print axioms LiveFiring.closing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
