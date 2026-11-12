import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfTypedCondition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.DeclaredErrors
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.EveryRunFinishesW

/-!
# HE's two type lookups give the same machine on programs with closed declarations

HE's contextual machine takes its type lookup as a parameter. The historical lookup
(`Completed.rawLookup`) answers the stored types of a subject verbatim; the scoped lookup
(`Completed.scopedLookup`) answers fresh alpha-variants of them, as HE's space index does when it
renames a stored atom's variables at every query. They differ exactly where a stored type has a type
variable: there the raw lookup shares one variable between all invocations of a polymorphic
declaration.

**Transfer.** On a space whose stored types are all closed (`ClosedTypes`; every program whose type
declarations are closed, `closedTypes_of_declarations`, in particular every program without
declarations), the two lookups are equal (`raw_eq_scoped`). The machine consults its lookup only at
the space of the step or of a context it entered (`local_transfer`), so the two machines have the same
steps (`step_transfer`), the same runs (`runs_iff`), the same well-foundedness (`acc_iff`) and the
same final configurations, for every grounded dispatch without minimal services (such a dispatch never
enters a context, `local_contexts`).

Every-run statements are bundled once (`Publishes`: a complete run exists and every complete run
publishes the given atoms; `Finishes`: no infinite run, and every reachable configuration steps or is
final with the given atoms) and transferred once (`publishes_iff`, `finishes_iff`). The earlier
every-run theorems then hold on the scoped lookup at once:

* `every_complete_run_c_scoped`, `every_complete_run_n_scoped`, `every_complete_run_k_scoped`:
  nested calls, nested values, variables bound to compound values;
* `every_run_finishes_k_scoped`: every run finishes;
* `typed_every_run_scoped`, `declared_every_run_scoped`, `error_every_run_complete_scoped`: the
  declared paths (their declarations are closed).

The world machine with integer operations needs no transfer: its theorems are already stated for
both lookups (`EveryRunFinishesW.every_run_finishes_kg_with_he_lookups`).

## Controls

* `Controls.plain_closed` (positive): a program without declarations has closed types.
* `Controls.if_not_closed` (negative): HE's `if` program does not; its arrow has the variable `t`.
* `Controls.lookups_differ` (negative, the transfer has content): on HE's `if` program the scoped
  lookup answers `(-> Bool Atom Atom $u)` for `if`, which the raw lookup does not; the scoped lookup
  is not the raw one there. So the `if` theorems of `IfEveryRun` to `IfTypedCondition` are not
  covered by the transfer; `ScopedIf` restates `if` on the scoped lookup.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace ScopedTransfer

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (StorageTypesRel AnnotationTypesRel
  IntrinsicGroundedTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact (ArgumentAlphaVariantsRel
  TypeCandidateAlphaVariantRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open EntryToQuery EveryRun EveryRunFinishes

/-! ## Closed stored types -/

/-- **Every stored type of the space is closed**: no type variable occurs in any type the
list-storage enumeration answers, for any subject. -/
def ClosedTypes (space : Space) : Prop :=
  ∀ (subject : Atom) (types : List Atom), StorageTypesRel space subject types →
    ∀ T ∈ types, TypeSubst.typeVars T = []

/-- **Every type declaration of the program has a closed type.** -/
def ClosedDeclarations (atoms : List Atom) : Prop :=
  ∀ a ∈ atoms, ∀ subject T : Atom, a = .expression [.symbol ":", subject, T] →
    TypeSubst.typeVars T = []

theorem annotation_member {target : Atom} {atoms types : List Atom}
    (extracted : AnnotationTypesRel target atoms types) {T : Atom} (member : T ∈ types) :
    .expression [.symbol ":", target, T] ∈ atoms := by
  induction extracted with
  | nil => cases member
  | hit _ ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih later)
  | skip _ _ ih => exact List.mem_cons_of_mem _ (ih member)

theorem intrinsic_closed {value : GroundedValue} {T : Atom} (intrinsic : IntrinsicGroundedTypeRel value T) :
    TypeSubst.typeVars T = [] := by
  cases intrinsic <;> rfl

theorem undefined_closed : TypeSubst.typeVars Atom.undefinedType = [] := rfl

/-- **Closed declarations give closed stored types.** The fallback `%Undefined%` and the intrinsic
types of grounded values are closed. -/
theorem closedTypes_of_declarations {atoms : List Atom} (closed : ClosedDeclarations atoms) :
    ClosedTypes (Space.ofList atoms) := by
  intro subject types stored T member
  cases stored with
  | «variable» => rw [List.mem_singleton.mp member]; rfl
  | groundedKnown intrinsic _ => rw [List.mem_singleton.mp member]; exact intrinsic_closed intrinsic
  | groundedUndefined _ => rw [List.mem_singleton.mp member]; rfl
  | symbolKnown annotations _ =>
      exact closed _ (annotation_member annotations member) _ T rfl
  | symbolUndefined _ => rw [List.mem_singleton.mp member]; rfl
  | unit => rw [List.mem_singleton.mp member]; rfl
  | expressionKnown annotations _ =>
      exact closed _ (annotation_member annotations member) _ T rfl
  | expressionUndefined _ => rw [List.mem_singleton.mp member]; rfl

/-! ## On closed stored types the two lookups are equal -/

/-- A closed atom is fixed by every renaming of type variables. -/
theorem rename_closed (rename : String → String) (atom : Atom) (closed : TypeSubst.typeVars atom = []) :
    renameTypeVars rename atom = atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      TypeSubst.typeVarsList atoms = [] → atoms.map (renameTypeVars rename) = atoms) with
  | symbol name => simp [renameTypeVars]
  | var name => simp [TypeSubst.typeVars] at closed
  | grounded value => simp [renameTypeVars]
  | expression atoms ih =>
      simp only [TypeSubst.typeVars] at closed
      simp [renameTypeVars, ih closed]
  | nil => rfl
  | cons head tail headIH tailIH =>
      rename_i closedList
      simp only [TypeSubst.typeVarsList, List.append_eq_nil_iff] at closedList
      simp [headIH closedList.1, tailIH closedList.2]

/-- **Fresh variants of closed types are the types themselves.** -/
theorem variants_closed_iff {avoid : List String} {sources targets : List Atom}
    (closed : ∀ T ∈ sources, TypeSubst.typeVars T = []) :
    ArgumentAlphaVariantsRel avoid sources targets ↔ targets = sources := by
  constructor
  · intro variants
    induction variants with
    | nil => rfl
    | cons variant _ ih =>
        obtain ⟨rename, _, renamed, _⟩ := variant
        rw [ih (fun T member => closed T (List.mem_cons_of_mem _ member)), renamed,
          rename_closed rename _ (closed _ List.mem_cons_self)]
  · intro same
    rw [same]
    clear same
    induction sources generalizing avoid with
    | nil => exact .nil avoid
    | cons source rest ih =>
        have sourceClosed := closed source List.mem_cons_self
        refine .cons ⟨id, Function.injective_id, (rename_closed id source sourceClosed).symm, ?_⟩
          (ih (fun T member => closed T (List.mem_cons_of_mem _ member)))
        intro name member
        rw [sourceClosed] at member
        cases member

/-- **On a space with closed stored types, the raw and the scoped lookups are equal**, for every
protected scope. -/
theorem raw_eq_scoped {space : Space} (closed : ClosedTypes space) (scope : List String) :
    Completed.rawLookup scope space = Completed.scopedLookup scope space := by
  funext bindings subject expected candidates
  apply propext
  change StorageTypesRel space subject candidates ↔
    ∃ raw, StorageTypesRel space subject raw ∧
      ArgumentAlphaVariantsRel (invocationTypeScope scope [] subject expected bindings) raw candidates
  constructor
  · intro stored
    exact ⟨candidates, stored, (variants_closed_iff (closed subject candidates stored)).mpr rfl⟩
  · rintro ⟨raw, stored, variants⟩
    rw [(variants_closed_iff (closed subject raw stored)).mp variants]
    exact stored

/-! ## The machine consults its lookup only at the spaces it runs in -/

/-- **The contexts a control has entered** all satisfy `P`. -/
def ContextsIn (P : Space → Prop) : Control → Prop
  | .work _ => True
  | .returning _ => True
  | .context label child _ => P label ∧ ContextsIn P child

theorem selection_congr {admission : Completed.ArgumentService} {space : Space}
    {l₁ l₂ : CastLookup} (agree : ∀ scope, l₁ scope space = l₂ scope space) {policy : Policy}
    {live : List Atom} {scope : List String} {expression operator expected : Atom} {before : Frame}
    {outcome : Completed.InvocationSelection} :
    admission.selection space l₁ policy live scope expression operator expected before outcome ↔
      admission.selection space l₂ policy live scope expression operator expected before outcome := by
  cases admission <;>
    simp only [Completed.ArgumentService.selection, Completed.InvocationSelectionRel, agree]

/-- **One local step transfers between lookups that agree on the spaces it runs in**: the step's
space and every context its control has entered. -/
theorem local_transfer {P : Space → Prop} {admission : Completed.ArgumentService}
    {l₁ l₂ : CastLookup} {space : Space} {dispatch : GroundedDispatch} {policy : Policy}
    {before after : Control × List Continuation}
    (step : LocalStepWith admission space dispatch l₁ policy before after) :
    (∀ space', P space' → ∀ scope, l₁ scope space' = l₂ scope space') → P space →
      ContextsIn P before.1 → LocalStepWith admission space dispatch l₂ policy before after := by
  induction step
  case cast entered batch paired =>
    intro agree here _
    simp only [agree _ here] at batch paired
    exact .cast entered batch paired
  case atomFunction entered shaped selected =>
    intro agree here _
    exact .atomFunction entered shaped ((selection_congr (agree _ here)).mp selected)
  case atomFallback entered shaped selected =>
    intro agree here _
    exact .atomFallback entered shaped ((selection_congr (agree _ here)).mp selected)
  case atomSelectionFailed entered shaped selected =>
    intro agree here _
    exact .atomSelectionFailed entered shaped ((selection_congr (agree _ here)).mp selected)
  case boundaryNativeCompletedReturn returned =>
    intro agree here _
    simp only [agree _ here] at returned
    exact .boundaryNativeCompletedReturn returned
  case callAbsent notError nonGrounded frontier =>
    intro _ _ _
    exact .callAbsent notError nonGrounded frontier
  case contextStep inner ih =>
    intro agree _ contexts
    obtain ⟨entered, child⟩ := contexts
    exact .contextStep (ih agree entered child)
  all_goals
    intro _ _ _
    constructor <;> assumption

/-- **Without minimal services the machine never enters a context**: every control reached keeps its
contexts in `P`. -/
theorem local_contexts {P : Space → Prop} {admission : Completed.ArgumentService} {lookup : CastLookup}
    {space : Space} {dispatch : GroundedDispatch} {policy : Policy}
    {before after : Control × List Continuation}
    (step : LocalStepWith admission space dispatch lookup policy before after) :
    dispatch.minimal = none → ContextsIn P before.1 → ContextsIn P after.1 := by
  induction step
  case contextStep _ ih =>
    intro none contexts
    exact ⟨contexts.1, ih none contexts.2⟩
  case minimalEvalc provided =>
    intro none _
    rw [none] at provided
    cases provided
  case minimalMetta provided =>
    intro none _
    rw [none] at provided
    cases provided
  all_goals
    intro _ _
    exact True.intro

variable {dispatch : GroundedDispatch} {policy : Policy}

theorem step_transfer {P : Space → Prop} {l₁ l₂ : CastLookup}
    (agree : ∀ space, P space → ∀ scope, l₁ scope space = l₂ scope space) {x y : HEConfig}
    (step : HEStep dispatch l₁ policy x y) (here : P x.space) (contexts : ContextsIn P x.control) :
    HEStep dispatch l₂ policy x y := by
  cases step with
  | internal inner => exact .internal (local_transfer inner agree here contexts)
  | publish => exact .publish

theorem step_space {lookup : CastLookup} {x y : HEConfig} (step : HEStep dispatch lookup policy x y) :
    y.space = x.space := by
  cases step <;> rfl

theorem step_contexts {P : Space → Prop} {lookup : CastLookup} (none : dispatch.minimal = none)
    {x y : HEConfig} (step : HEStep dispatch lookup policy x y) (contexts : ContextsIn P x.control) :
    ContextsIn P y.control := by
  cases step with
  | internal inner => exact local_contexts inner none contexts
  | publish => exact True.intro

/-- The invariant along a run: the space keeps `P` and the contexts stay in `P`. -/
theorem reach_invariant {P : Space → Prop} {lookup : CastLookup} (none : dispatch.minimal = none)
    {x y : HEConfig} (run : Relation.ReflTransGen (HEStep dispatch lookup policy) x y)
    (here : P x.space) (contexts : ContextsIn P x.control) : P y.space ∧ ContextsIn P y.control := by
  induction run with
  | refl => exact ⟨here, contexts⟩
  | tail _ step ih => exact ⟨step_space step ▸ ih.1, step_contexts none step ih.2⟩

/-- **Runs transfer between lookups that agree on `P`**, from a configuration whose space and
contexts satisfy `P`, for a dispatch without minimal services. -/
theorem steps_transfer {P : Space → Prop} {l₁ l₂ : CastLookup}
    (agree : ∀ space, P space → ∀ scope, l₁ scope space = l₂ scope space)
    (none : dispatch.minimal = none) {x y : HEConfig}
    (run : Relation.ReflTransGen (HEStep dispatch l₁ policy) x y)
    (here : P x.space) (contexts : ContextsIn P x.control) :
    Relation.ReflTransGen (HEStep dispatch l₂ policy) x y := by
  induction run with
  | refl => exact .refl
  | tail path step ih =>
      have reached := reach_invariant none path here contexts
      exact .tail ih (step_transfer agree step reached.1 reached.2)

/-- **Well-foundedness transfers.** -/
theorem acc_transfer {P : Space → Prop} {l₁ l₂ : CastLookup}
    (agree : ∀ space, P space → ∀ scope, l₁ scope space = l₂ scope space)
    (none : dispatch.minimal = none) {x : HEConfig}
    (acc : Acc (fun b a => HEStep dispatch l₁ policy a b) x) :
    P x.space → ContextsIn P x.control → Acc (fun b a => HEStep dispatch l₂ policy a b) x := by
  induction acc with
  | intro x _ ih =>
      intro here contexts
      refine Acc.intro x fun y step => ?_
      have back := step_transfer (fun space h scope => (agree space h scope).symm) step here contexts
      exact ih y back (step_space back ▸ here) (step_contexts none back contexts)

/-! ## The specialization to closed spaces -/

/-- The agreement of the two lookups on closed spaces. -/
theorem closed_agree : ∀ space : Space, ClosedTypes space →
    ∀ scope, Completed.rawLookup scope space = Completed.scopedLookup scope space :=
  fun _ closed scope => raw_eq_scoped closed scope

theorem closed_agree_symm : ∀ space : Space, ClosedTypes space →
    ∀ scope, Completed.scopedLookup scope space = Completed.rawLookup scope space :=
  fun _ closed scope => (raw_eq_scoped closed scope).symm

theorem load_contexts (P : Space → Prop) (space : Space) (c E : Atom) :
    ContextsIn P (load space c E).control := True.intro

/-- **Runs from the entry are the same under both lookups**, on a closed space, for a dispatch
without minimal services. -/
theorem runs_iff (none : dispatch.minimal = none) {space : Space} (closed : ClosedTypes space)
    (c E : Atom) (y : HEConfig) :
    Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy) (load space c E) y ↔
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy) (load space c E) y :=
  ⟨fun run => steps_transfer closed_agree none run closed (load_contexts _ space c E),
    fun run => steps_transfer closed_agree_symm none run closed (load_contexts _ space c E)⟩

/-- **Steps at every reachable configuration are the same under both lookups.** -/
theorem reached_step_iff (none : dispatch.minimal = none) {space : Space} (closed : ClosedTypes space)
    {c E : Atom} {y : HEConfig}
    (run : Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy) (load space c E) y)
    (z : HEConfig) :
    HEStep dispatch Completed.rawLookup policy y z ↔ HEStep dispatch Completed.scopedLookup policy y z := by
  have reached := reach_invariant (P := ClosedTypes) none run closed (load_contexts _ space c E)
  exact ⟨fun step => step_transfer closed_agree step reached.1 reached.2,
    fun step => step_transfer closed_agree_symm step reached.1 reached.2⟩

theorem acc_iff (none : dispatch.minimal = none) {space : Space} (closed : ClosedTypes space)
    (c E : Atom) :
    Acc (fun b a => HEStep dispatch Completed.rawLookup policy a b) (load space c E) ↔
      Acc (fun b a => HEStep dispatch Completed.scopedLookup policy a b) (load space c E) :=
  ⟨fun acc => acc_transfer closed_agree none acc closed (load_contexts _ space c E),
    fun acc => acc_transfer closed_agree_symm none acc closed (load_contexts _ space c E)⟩

/-! ## Every-run statements, bundled and transferred once -/

/-- The final configuration publishing `emitted`. -/
abbrev final (space : Space) (emitted : List Result) : HEConfig := ⟨space, .returning [], [], emitted⟩

/-- **Every complete run publishes `L`, and one exists**, from the entry of `c` under
`%Undefined%`. -/
def Publishes (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) (space : Space)
    (c : Atom) (L : List Atom) : Prop :=
  (∃ heAnswers : List Result,
    Relation.ReflTransGen (HEStep dispatch lookup policy) (load space c Atom.undefinedType)
      (final space heAnswers)) ∧
  ∀ emitted : List Result,
    Relation.ReflTransGen (HEStep dispatch lookup policy) (load space c Atom.undefinedType)
      (final space emitted) →
    emitted.map (fun r => r.1.erase) = L

/-- **Every run finishes with `L`**: no infinite run from the entry of `c`, and every reachable
configuration steps or is final with `L`. -/
def Finishes (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) (space : Space)
    (c : Atom) (L : List Atom) : Prop :=
  Acc (fun b a => HEStep dispatch lookup policy a b) (load space c Atom.undefinedType) ∧
  ∀ y, Relation.ReflTransGen (HEStep dispatch lookup policy) (load space c Atom.undefinedType) y →
    (∃ z, HEStep dispatch lookup policy y z) ∨
      ∃ emitted : List Result, y = final space emitted ∧ emitted.map (fun r => r.1.erase) = L

/-- **The every-run bundle transfers to the scoped lookup**, on a closed space, for a dispatch
without minimal services. -/
theorem publishes_iff (none : dispatch.minimal = none) {space : Space} (closed : ClosedTypes space)
    (c : Atom) (L : List Atom) :
    Publishes dispatch Completed.rawLookup policy space c L ↔
      Publishes dispatch Completed.scopedLookup policy space c L := by
  simp only [Publishes, runs_iff none closed]

/-- **The finishing bundle transfers to the scoped lookup.** -/
theorem finishes_iff (none : dispatch.minimal = none) {space : Space} (closed : ClosedTypes space)
    (c : Atom) (L : List Atom) :
    Finishes dispatch Completed.rawLookup policy space c L ↔
      Finishes dispatch Completed.scopedLookup policy space c L := by
  unfold Finishes
  rw [acc_iff none closed]
  constructor
  · rintro ⟨acc, every⟩
    refine ⟨acc, fun y run => ?_⟩
    have back := (runs_iff none closed c Atom.undefinedType y).mpr run
    rcases every y back with ⟨z, step⟩ | done
    · exact Or.inl ⟨z, (reached_step_iff none closed back z).mp step⟩
    · exact Or.inr done
  · rintro ⟨acc, every⟩
    refine ⟨acc, fun y run => ?_⟩
    rcases every y ((runs_iff none closed c Atom.undefinedType y).mp run) with ⟨z, step⟩ | done
    · exact Or.inl ⟨z, (reached_step_iff none closed run z).mpr step⟩
    · exact Or.inr done

/-- `Finishes` gives `Publishes`: a final configuration is reached, and a final configuration does
not step. -/
theorem Finishes.publishes {lookup : CastLookup} {space : Space} {c : Atom} {L : List Atom}
    (finishes : Finishes dispatch lookup policy space c L) : Publishes dispatch lookup policy space c L := by
  obtain ⟨acc, every⟩ := finishes
  refine ⟨?_, fun emitted run => ?_⟩
  · have reach : ∀ x, Acc (fun b a => HEStep dispatch lookup policy a b) x →
        Relation.ReflTransGen (HEStep dispatch lookup policy) (load space c Atom.undefinedType) x →
        ∃ heAnswers, Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load space c Atom.undefinedType) (final space heAnswers) := by
      intro x accX
      induction accX with
      | intro x _ ih =>
          intro path
          rcases every x path with ⟨z, step⟩ | ⟨emitted, rfl, _⟩
          · exact ih z step (path.tail step)
          · exact ⟨emitted, path⟩
    exact reach _ acc .refl
  · rcases every _ run with ⟨z, step⟩ | ⟨emitted', same, erased⟩
    · exact absurd step final_no_step
    · simp only [final, Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.mk.injEq,
        true_and] at same
      rw [same]
      exact erased

/-! ## Checking closed declarations -/

/-- The type variables of a declaration's type, and none for any other atom. -/
def declarationVars : Atom → List String
  | .expression [.symbol ":", _, T] => TypeSubst.typeVars T
  | _ => []

/-- **A finite check of closed declarations.** -/
theorem closedDeclarations_of_check {atoms : List Atom}
    (check : atoms.all (fun a => (declarationVars a).isEmpty) = true) : ClosedDeclarations atoms := by
  intro a member subject T same
  have each := List.all_eq_true.mp check a member
  subst same
  simpa [declarationVars, List.isEmpty_iff] using each

/-! ## The earlier every-run theorems on the scoped lookup -/

section Lifted

open Mettapedia.Languages.MeTTa.PeTTa
open AnswerBags (translate store)
open Mettapedia.Languages.MeTTa.HE (mkError)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (FunctionTypeRel)
open AnswerBags.Controls (sym app rule)

/-- **Nested calls in bodies, on the scoped lookup** (`NestedCalls.every_complete_run_c`): for a
program with closed declarations and a dispatch without minimal services, a complete run exists; from
some fuel on PeTTa's streaming run yields `L`; every complete run publishes `L`. -/
theorem every_complete_run_c_scoped (policy : Policy) (none : dispatch.minimal = none)
    {atoms : List Atom} (closed : ClosedDeclarations atoms) (program : NestedCalls.CallProgram atoms)
    {c : Atom} {L : List Atom} (settles : NestedCalls.SettlesC dispatch atoms c L) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      ∃ N : Nat, ∀ n, N ≤ n →
        Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = L ∧
          ∀ emitted : List Result,
            Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
                (load (Space.ofList atoms) c Atom.undefinedType)
                ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
              emitted.map (fun r => r.1.erase) = L := by
  have raw := NestedCalls.every_complete_run_c policy program settles
  simpa only [runs_iff none (closedTypes_of_declarations closed)] using raw

/-- **Variables at any depth inside built values, on the scoped lookup**
(`NestedValues.every_complete_run_n`). -/
theorem every_complete_run_n_scoped (policy : Policy) (none : dispatch.minimal = none)
    {atoms : List Atom} (closed : ClosedDeclarations atoms)
    (program : NestedValues.NestedProgram dispatch atoms) {c : Atom}
    (settles : NestedValues.SettlesN dispatch atoms c) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
            (load (Space.ofList atoms) c Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = emitted.map (fun r => r.1.erase) := by
  have raw := NestedValues.every_complete_run_n policy program settles
  simpa only [runs_iff none (closedTypes_of_declarations closed)] using raw

/-- **Variables bound to compound values, on the scoped lookup**
(`CompoundBindings.every_complete_run_k`). -/
theorem every_complete_run_k_scoped (policy : Policy) (none : dispatch.minimal = none)
    {atoms : List Atom} (closed : ClosedDeclarations atoms) (program : NestedCalls.CallProgram atoms)
    {c : Atom} {L : List Atom} (settles : CompoundBindings.SettlesK dispatch atoms c L) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      ∃ N : Nat, ∀ n, N ≤ n →
        Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = L ∧
          ∀ emitted : List Result,
            Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
                (load (Space.ofList atoms) c Atom.undefinedType)
                ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
              emitted.map (fun r => r.1.erase) = L := by
  have raw := CompoundBindings.every_complete_run_k policy program settles
  simpa only [runs_iff none (closedTypes_of_declarations closed)] using raw

/-- **Every run finishes, on the scoped lookup** (`EveryRunFinishes.every_run_finishes_k`): no
infinite run, every reachable configuration steps or is final with `L`, and PeTTa yields `L`. -/
theorem every_run_finishes_k_scoped (policy : Policy) (none : dispatch.minimal = none)
    {atoms : List Atom} (closed : ClosedDeclarations atoms) (program : NestedCalls.CallProgram atoms)
    {c : Atom} {L : List Atom} (settles : CompoundBindings.SettlesK dispatch atoms c L) :
    Finishes dispatch Completed.scopedLookup policy (Space.ofList atoms) c L ∧
      Publishes dispatch Completed.scopedLookup policy (Space.ofList atoms) c L ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } c)) = L := by
  obtain ⟨acc, every, N, petta⟩ := every_run_finishes_k policy program settles
  have raw : Finishes dispatch Completed.rawLookup policy (Space.ofList atoms) c L := ⟨acc, every⟩
  have onScoped := (finishes_iff none (closedTypes_of_declarations closed) c L).mp raw
  exact ⟨onScoped, onScoped.publishes, N, petta⟩

/-- The declarations of `{(: f (-> Number Number)), (: b Bool), (= (f $x) yes)}` are closed. -/
theorem declaredRows_closed : ClosedDeclarations DeclaredHeads.declaredRows :=
  closedDeclarations_of_check (by decide)

/-- **The well-typed declared path, on the scoped lookup** (`TypedEveryRun.typed_every_run`):
`(f 4)` with `(: f (-> Number Number))` publishes `yes` on every complete run. -/
theorem typed_every_run_scoped (dispatch : GroundedDispatch) (none : dispatch.minimal = none)
    (notHost : ¬ dispatch.executable (.symbol "f")) (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
          (load (Space.ofList DeclaredHeads.declaredRows) DeclaredHeads.typedCall Atom.undefinedType)
          ⟨Space.ofList DeclaredHeads.declaredRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
            (load (Space.ofList DeclaredHeads.declaredRows) DeclaredHeads.typedCall Atom.undefinedType)
            ⟨Space.ofList DeclaredHeads.declaredRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [sym "yes"]) ∧
      ∀ n, 40 ≤ n → Streaming.values (Streaming.advance (translate DeclaredHeads.declaredRows) n
        (Streaming.enter { state := store DeclaredHeads.declaredRows } DeclaredHeads.typedCall)) =
          [sym "yes"] := by
  have raw := TypedEveryRun.typed_every_run dispatch notHost policy
  simpa only [runs_iff none (closedTypes_of_declarations declaredRows_closed)] using raw

/-- **The declared guard, on the scoped lookup** (`DeclaredEveryRun.declared_every_run`): `(f b)`
publishes the `BadArgType` error on every complete run, while PeTTa answers `yes`. -/
theorem declared_every_run_scoped (dispatch : GroundedDispatch) (none : dispatch.minimal = none)
    (policy : Policy) :
    (∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
          (load (Space.ofList DeclaredHeads.declaredRows) DeclaredHeads.declaredCall
            Atom.undefinedType)
          ⟨Space.ofList DeclaredHeads.declaredRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [DeclaredHeads.badArgument]) ∧
      Mettapedia.Languages.MeTTa.HE.isErrorAtom DeclaredHeads.badArgument = true ∧
      ∀ n, 40 ≤ n → Streaming.values (Streaming.advance (translate DeclaredHeads.declaredRows) n
        (Streaming.enter { state := store DeclaredHeads.declaredRows } DeclaredHeads.declaredCall)) =
          [sym "yes"] := by
  have raw := DeclaredEveryRun.declared_every_run dispatch policy
  simpa only [runs_iff none (closedTypes_of_declarations declaredRows_closed)] using raw

/-- **The error path at any arity, on the scoped lookup** (`DeclaredErrors.error_every_run_complete`),
for a program with closed declarations. -/
theorem error_every_run_complete_scoped (dispatch : GroundedDispatch) (none : dispatch.minimal = none)
    (policy : Policy) {atoms : List Atom} (closed : ClosedDeclarations atoms)
    {g : String} {arrow returnType : Atom} {pre preT preA post postT : List Atom}
    {bad badType badActual : Atom} (gData : DataAtom (.symbol g))
    (notUndefined : arrow ≠ Atom.undefinedType)
    (gTypes : StorageTypesRel (Space.ofList atoms) (.symbol g) [arrow])
    (arrowShape : FunctionTypeRel arrow (preT ++ badType :: postT) returnType)
    (lengths : post.length = postT.length)
    (stored : List.Forall₂ (fun a A => StorageTypesRel (Space.ofList atoms) a [A]) pre preA)
    (keeps : List.Forall₂ (fun T A => DeclaredErrors.AcceptsKeeping policy T A) preT preA)
    (badStored : StorageTypesRel (Space.ofList atoms) bad [badActual])
    (rejects : DeclaredErrors.Rejects policy badType badActual) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
          (load (Space.ofList atoms) (.expression (.symbol g :: (pre ++ bad :: post)))
            Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
            (load (Space.ofList atoms) (.expression (.symbol g :: (pre ++ bad :: post)))
              Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) =
            [mkError (.expression (.symbol g :: (pre ++ bad :: post)))
              (.badArgType (1 + pre.length) badType badActual)] := by
  have raw := DeclaredErrors.error_every_run_complete dispatch policy gData notUndefined gTypes
    arrowShape lengths stored keeps badStored rejects
  simpa only [runs_iff none (closedTypes_of_declarations closed)] using raw

end Lifted

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule)
open IfEveryRun (ifArrow ifProgram if_types)

/-- **Positive control**: a program without declarations has closed types. -/
theorem plain_closed : ClosedTypes (Space.ofList [rule (app "f" [.var "x"]) (.var "x")]) :=
  closedTypes_of_declarations (closedDeclarations_of_check (by decide))

/-- **Negative control**: HE's `if` program does not have closed types; its arrow has `t`. -/
theorem if_not_closed : ¬ ClosedTypes (Space.ofList ifProgram) := by
  intro closed
  have vars := closed _ _ if_types ifArrow List.mem_cons_self
  simp [TypeSubst.typeVars, TypeSubst.typeVarsList] at vars

/-- `(-> Bool Atom Atom $u)`. -/
abbrev ifArrowU : Atom :=
  .expression [.symbol "->", sym "Bool", Atom.atomType, Atom.atomType, .var "u"]

/-- **Negative control, the transfer has content**: on HE's `if` program the scoped lookup answers
`(-> Bool Atom Atom $u)` for `if`, and the raw lookup does not. -/
theorem lookups_differ :
    Completed.scopedLookup [] (Space.ofList ifProgram) Bindings.empty (.symbol "if")
        Atom.undefinedType [ifArrowU] ∧
      ¬ Completed.rawLookup [] (Space.ofList ifProgram) Bindings.empty (.symbol "if")
        Atom.undefinedType [ifArrowU] := by
  constructor
  · refine ⟨[ifArrow], if_types, .cons ⟨Equiv.swap "t" "u", (Equiv.swap "t" "u").injective, ?_, ?_⟩
      (.nil _)⟩
    · simp [ifArrow, ifArrowU, Equiv.swap_apply_left, Atom.atomType]
    · intro name member
      simp [TypeSubst.typeVars, TypeSubst.typeVarsList, Atom.atomType] at member
      subst member
      rw [Equiv.swap_apply_left]
      decide
  · intro queried
    have same := StorageTypesRel.unique
      (show StorageTypesRel (Space.ofList ifProgram) (.symbol "if") [ifArrowU] from queried) if_types
    simp [ifArrowU, ifArrow] at same

end Controls

#print axioms closedTypes_of_declarations
#print axioms raw_eq_scoped
#print axioms local_transfer
#print axioms local_contexts
#print axioms steps_transfer
#print axioms acc_transfer
#print axioms runs_iff
#print axioms acc_iff
#print axioms publishes_iff
#print axioms finishes_iff
#print axioms Finishes.publishes
#print axioms closedDeclarations_of_check
#print axioms every_complete_run_c_scoped
#print axioms every_complete_run_n_scoped
#print axioms every_complete_run_k_scoped
#print axioms every_run_finishes_k_scoped
#print axioms typed_every_run_scoped
#print axioms declared_every_run_scoped
#print axioms error_every_run_complete_scoped
#print axioms Controls.plain_closed
#print axioms Controls.if_not_closed
#print axioms Controls.lookups_differ

end ScopedTransfer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
