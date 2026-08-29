import Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection

/-!
# First-order plans for the mainline PeTTa call guard

This module compiles the closed, resolved fragment of the authored mainline
call guard into a small ordered plan family.  Compilation is all-or-decline:
if any declaration relevant to the requested head and arity is outside the
closed fragment, the whole family is returned as `outsideFragment`.

Plan acceptance is defined independently from `InputGuard` and `OutputGuard`.
The central theorem proves exact list equality with `successfulDeclarations`,
retaining declaration occurrence identity, multiplicity, and authored order.

Shared owner, revision, head, and arity coordinates live on a compiled family,
so even an empty family retains its authority key.  Execution distinguishes a
current empty result from explicit fallback, and cold-path validity requires
exact compiler production rather than coordinate consistency alone.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan

open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection

set_option autoImplicit false

/-! ## Admitted closed type expressions -/

/- Whether a resolved type expression contains no unresolved PeTTa variable. -/
mutual
  def termIsClosed : Term → Bool
    | .variable _ => false
    | .number _ | .string _ | .atom _ => true
    | .list elements => termListIsClosed elements

  def termListIsClosed : List Term → Bool
    | [] => true
    | term :: terms => termIsClosed term && termListIsClosed terms
end

@[simp] theorem termIsClosed_variable (name : String) :
    termIsClosed (.variable name) = false := rfl

/-! ## First-order guard plan language -/

inductive ArgMode where
  | rawAtom
  | evalUnchecked
  | evalSoftcutType (expected : Term)
deriving DecidableEq, Repr

inductive ResultMode where
  | resultUnchecked
  | resultSoftcutType (expected : Term)
deriving DecidableEq, Repr

/-- Independent operational meaning of one compiled input mode. -/
def ArgMode.Accepts (mode : ArgMode) (snapshot : Snapshot)
    (source value : Term) : Prop :=
  match mode with
  | .rawAtom => value = source
  | .evalUnchecked => True
  | .evalSoftcutType expected =>
      GetType snapshot value expected ∨
        (¬ GetType snapshot value expected ∧
          GetMetatype snapshot value expected)

instance (mode : ArgMode) (snapshot : Snapshot) (source value : Term) :
    Decidable (mode.Accepts snapshot source value) := by
  cases mode <;> unfold ArgMode.Accepts <;> infer_instance

/-- Independent operational meaning of one compiled result mode. -/
def ResultMode.Accepts (mode : ResultMode) (snapshot : Snapshot)
    (value : Term) : Prop :=
  match mode with
  | .resultUnchecked => True
  | .resultSoftcutType expected =>
      GetType snapshot value expected ∨
        (¬ GetType snapshot value expected ∧
          GetMetatype snapshot value expected)

instance (mode : ResultMode) (snapshot : Snapshot) (value : Term) :
    Decidable (mode.Accepts snapshot value) := by
  cases mode <;> unfold ResultMode.Accepts <;> infer_instance

def ArgumentsAccept
    (snapshot : Snapshot) : List ArgMode → List Term → List Term → Prop
  | [], [], [] => True
  | mode :: modes, source :: sources, value :: values =>
      mode.Accepts snapshot source value ∧
        ArgumentsAccept snapshot modes sources values
  | _, _, _ => False

private def decidableArgumentsAccept (snapshot : Snapshot) :
    (modes : List ArgMode) → (sources values : List Term) →
      Decidable (ArgumentsAccept snapshot modes sources values)
  | [], [], [] => isTrue trivial
  | mode :: modes, source :: sources, value :: values =>
      match inferInstanceAs (Decidable (mode.Accepts snapshot source value)),
          decidableArgumentsAccept snapshot modes sources values with
      | isTrue head, isTrue tail => isTrue ⟨head, tail⟩
      | isFalse head, _ => isFalse (fun proof => head proof.1)
      | _, isFalse tail => isFalse (fun proof => tail proof.2)
  | [], [], _ :: _ => isFalse (by simp [ArgumentsAccept])
  | [], _ :: _, [] => isFalse (by simp [ArgumentsAccept])
  | [], _ :: _, _ :: _ => isFalse (by simp [ArgumentsAccept])
  | _ :: _, [], [] => isFalse (by simp [ArgumentsAccept])
  | _ :: _, [], _ :: _ => isFalse (by simp [ArgumentsAccept])
  | _ :: _, _ :: _, [] => isFalse (by simp [ArgumentsAccept])

instance (snapshot : Snapshot) (modes : List ArgMode)
    (sources values : List Term) :
    Decidable (ArgumentsAccept snapshot modes sources values) :=
  decidableArgumentsAccept snapshot modes sources values

/-- Declaration-local first-order instructions.  Authority and request
coordinates belong to `CompiledGuardFamily`, including for an empty family. -/
structure GuardPlan where
  declarationOccurrence : Nat
  argumentModes : List ArgMode
  resultMode : ResultMode
  declaration : ArrowDeclaration
deriving DecidableEq, Repr

namespace GuardPlan

/- Coordinate consistency is intentionally weaker than semantic validity. -/
def CoordinateConsistent (plan : GuardPlan) : Prop :=
  plan.declarationOccurrence = plan.declaration.occurrence ∧
    plan.argumentModes.length = plan.declaration.inputTypes.length

instance (plan : GuardPlan) : Decidable plan.CoordinateConsistent := by
  unfold CoordinateConsistent
  infer_instance

/-- Direct plan acceptance, without reference to `GuardedBy`. -/
def Accepts (plan : GuardPlan) (snapshot : Snapshot) (call : Call) : Prop :=
  plan.declaration.function = call.function ∧
    ArgumentsAccept snapshot plan.argumentModes
      call.sourceArguments call.evaluatedArguments ∧
      plan.resultMode.Accepts snapshot call.result

instance (plan : GuardPlan) (snapshot : Snapshot) (call : Call) :
    Decidable (plan.Accepts snapshot call) := by
  unfold Accepts
  infer_instance

end GuardPlan

/- Shared authority and request coordinates for one compiled overload family. -/
structure CompiledGuardFamily where
  owner : SpaceOwner
  revision : Nat
  head : String
  arity : Nat
  plans : List GuardPlan
deriving DecidableEq, Repr

namespace CompiledGuardFamily

def CurrentAt (family : CompiledGuardFamily) (current : OwnedSnapshot) : Prop :=
  family.owner = current.owner ∧
    family.revision = current.snapshot.revision

instance (family : CompiledGuardFamily) (current : OwnedSnapshot) :
    Decidable (family.CurrentAt current) := by
  unfold CurrentAt
  infer_instance

def MatchesCall (family : CompiledGuardFamily) (call : Call) : Prop :=
  family.head = call.function ∧
    family.arity = call.sourceArguments.length

instance (family : CompiledGuardFamily) (call : Call) :
    Decidable (family.MatchesCall call) := by
  unfold MatchesCall
  infer_instance

end CompiledGuardFamily

inductive CompilationResult where
  | compiled (family : CompiledGuardFamily)
  | outsideFragment
deriving DecidableEq, Repr

inductive GuardFallbackReason where
  | outsideFragment
  | foreignOwner
  | staleRevision
  | wrongHead
  | wrongArity
deriving DecidableEq, Repr

inductive GuardExecution where
  | executed (declarations : List ArrowDeclaration)
  | fallback (reason : GuardFallbackReason)
deriving DecidableEq, Repr

theorem GuardExecution.fallback_ne_executed
    (reason : GuardFallbackReason) (declarations : List ArrowDeclaration) :
    GuardExecution.fallback reason ≠ .executed declarations := by
  simp

/-! ## Closed-fragment compiler -/

def compileArgMode (expected : Term) : Option ArgMode :=
  if expected = atomType then
    some .rawAtom
  else if expected = undefinedType then
    some .evalUnchecked
  else if expected = holeType then
    some .evalUnchecked
  else if termIsClosed expected then
    some (.evalSoftcutType expected)
  else
    none

def compileResultMode (expected : Term) : Option ResultMode :=
  if expected = undefinedType then
    some .resultUnchecked
  else if expected = holeType then
    some .resultUnchecked
  else if expected = atomType then
    some .resultUnchecked
  else if termIsClosed expected then
    some (.resultSoftcutType expected)
  else
    none

def compileArgumentModes : List Term → Option (List ArgMode)
  | [] => some []
  | expected :: expectedTypes => do
      let mode ← compileArgMode expected
      let modes ← compileArgumentModes expectedTypes
      pure (mode :: modes)

theorem compileArgumentModes_length
    {expectedTypes : List Term} {modes : List ArgMode}
    (compiled : compileArgumentModes expectedTypes = some modes) :
    modes.length = expectedTypes.length := by
  induction expectedTypes generalizing modes with
  | nil => simpa [compileArgumentModes] using compiled
  | cons expected expectedTypes ih =>
      simp only [compileArgumentModes] at compiled
      cases modeResult : compileArgMode expected with
      | none => simp [modeResult] at compiled
      | some mode =>
          cases modesResult : compileArgumentModes expectedTypes with
          | none => simp [modeResult, modesResult] at compiled
          | some tailModes =>
              simp [modeResult, modesResult] at compiled
              subst modes
              simp [ih modesResult]

def compileGuard (declaration : ArrowDeclaration) : Option GuardPlan := do
  let argumentModes ← compileArgumentModes declaration.inputTypes
  let resultMode ← compileResultMode declaration.outputType
  pure
    { declarationOccurrence := declaration.occurrence
      argumentModes := argumentModes
      resultMode := resultMode
      declaration := declaration }

namespace GuardPlan

/- Mechanical production from a declaration in the resolved snapshot. -/
def ProducedIn (plan : GuardPlan) (snapshot : Snapshot) : Prop :=
  plan.declaration ∈ snapshot.declarations ∧
    compileGuard plan.declaration = some plan

instance (plan : GuardPlan) (snapshot : Snapshot) :
    Decidable (plan.ProducedIn snapshot) := by
  unfold ProducedIn
  infer_instance

/- Semantic plan validity adds the authored environment invariant. -/
def ValidIn (plan : GuardPlan) (snapshot : Snapshot) : Prop :=
  snapshot.WellFormed ∧ plan.ProducedIn snapshot

instance (plan : GuardPlan) (snapshot : Snapshot) :
    Decidable (plan.ValidIn snapshot) := by
  unfold ValidIn
  infer_instance

end GuardPlan

def Relevant (declaration : ArrowDeclaration)
    (head : String) (arity : Nat) : Prop :=
  declaration.function = head ∧ declaration.inputTypes.length = arity

instance (declaration : ArrowDeclaration) (head : String) (arity : Nat) :
    Decidable (Relevant declaration head arity) := by
  unfold Relevant
  infer_instance

def compileRelevantGuards (owner : SpaceOwner) (revision : Nat)
    (head : String) (arity : Nat) :
    List ArrowDeclaration → CompilationResult
  | [] => .compiled ⟨owner, revision, head, arity, []⟩
  | declaration :: declarations =>
      if Relevant declaration head arity then
        match compileGuard declaration with
        | none => .outsideFragment
        | some plan =>
            match compileRelevantGuards owner revision head arity declarations with
            | .outsideFragment => .outsideFragment
            | .compiled family =>
                .compiled { family with plans := plan :: family.plans }
      else
        compileRelevantGuards owner revision head arity declarations

/-- Compile every relevant declaration exactly once, or decline the whole
family if any relevant declaration is outside the closed fragment. -/
def compileGuards (owned : OwnedSnapshot)
    (head : String) (arity : Nat) : CompilationResult :=
  compileRelevantGuards owned.owner owned.snapshot.revision head arity
    owned.snapshot.declarations

/- Execute independently defined declaration-local predicates in plan order. -/
def executePlanList (snapshot : Snapshot) (call : Call) :
    List GuardPlan → List ArrowDeclaration
  | [] => []
  | plan :: plans =>
      if plan.Accepts snapshot call then
        plan.declaration :: executePlanList snapshot call plans
      else
        executePlanList snapshot call plans

/- Execute a family only when its complete authority and request key is
current.  Fallback is an authority/control observation, never a type result. -/
def executeGuardFamily (current : OwnedSnapshot) (call : Call)
    (family : CompiledGuardFamily) : GuardExecution :=
  if family.owner = current.owner then
    if family.revision = current.snapshot.revision then
      if family.head = call.function then
        if family.arity = call.sourceArguments.length then
          .executed (executePlanList current.snapshot call family.plans)
        else
          .fallback .wrongArity
      else
        .fallback .wrongHead
    else
      .fallback .staleRevision
  else
    .fallback .foreignOwner

/- Execute compilation without collapsing an unsupported fragment into an
empty current result. -/
def executeCompilation (current : OwnedSnapshot) (call : Call) :
    CompilationResult → GuardExecution
  | .outsideFragment => .fallback .outsideFragment
  | .compiled family => executeGuardFamily current call family

theorem executeGuardFamily_foreign_owner
    (current : OwnedSnapshot) (call : Call) (family : CompiledGuardFamily)
    (foreign : family.owner ≠ current.owner) :
    executeGuardFamily current call family = .fallback .foreignOwner := by
  simp [executeGuardFamily, foreign]

theorem executeGuardFamily_stale_revision
    (current : OwnedSnapshot) (call : Call) (family : CompiledGuardFamily)
    (ownerCurrent : family.owner = current.owner)
    (stale : family.revision ≠ current.snapshot.revision) :
    executeGuardFamily current call family = .fallback .staleRevision := by
  simp [executeGuardFamily, ownerCurrent, stale]

theorem executeCompilation_outsideFragment
    (current : OwnedSnapshot) (call : Call) :
    executeCompilation current call .outsideFragment =
      .fallback .outsideFragment :=
  rfl

/-! ## Local compiler correctness -/

theorem plan_softcut_exact (snapshot : Snapshot)
    (source value expected : Term) :
    (ArgMode.evalSoftcutType expected).Accepts snapshot source value ↔
      GetType snapshot value expected ∨
        (¬ GetType snapshot value expected ∧
          GetMetatype snapshot value expected) :=
  Iff.rfl

theorem plan_atom_raw_exact (snapshot : Snapshot) (source value : Term) :
    ArgMode.rawAtom.Accepts snapshot source value ↔ value = source :=
  Iff.rfl

theorem plan_unchecked_inputs_exact
    (snapshot : Snapshot) (source value : Term) :
    ArgMode.evalUnchecked.Accepts snapshot source value :=
  trivial

theorem plan_result_softcut_exact (snapshot : Snapshot)
    (value expected : Term) :
    (ResultMode.resultSoftcutType expected).Accepts snapshot value ↔
      GetType snapshot value expected ∨
        (¬ GetType snapshot value expected ∧
          GetMetatype snapshot value expected) :=
  Iff.rfl

theorem compileArgMode_accepts
    {expected : Term} {mode : ArgMode}
    (compiled : compileArgMode expected = some mode)
    (snapshot : Snapshot) (source value : Term) :
    mode.Accepts snapshot source value ↔
      InputGuard snapshot source value expected := by
  by_cases atom : expected = atomType
  · subst expected
    simp [compileArgMode, atomType] at compiled
    subst mode
    simp [InputGuard, atomType, ArgMode.Accepts]
  · by_cases undefined : expected = undefinedType
    · subst expected
      simp [compileArgMode, atomType, undefinedType] at compiled
      subst mode
      simp [InputGuard, atomType, undefinedType, ArgMode.Accepts]
    · by_cases hole : expected = holeType
      · subst expected
        simp [compileArgMode, atomType, undefinedType, holeType] at compiled
        subst mode
        simp [InputGuard, atomType, undefinedType, holeType,
          ArgMode.Accepts]
      · by_cases closed : termIsClosed expected = true
        · simp [compileArgMode, atom, undefined, hole, closed] at compiled
          subst mode
          simp [InputGuard, atom, undefined, hole, ArgMode.Accepts]
        · simp [compileArgMode, atom, undefined, hole, closed] at compiled

theorem compileResultMode_accepts
    {expected : Term} {mode : ResultMode}
    (compiled : compileResultMode expected = some mode)
    (snapshot : Snapshot) (value : Term) :
    mode.Accepts snapshot value ↔ OutputGuard snapshot value expected := by
  by_cases undefined : expected = undefinedType
  · simp [compileResultMode, undefined] at compiled
    subst mode
    simp [OutputGuard, undefined, ResultMode.Accepts]
  · by_cases hole : expected = holeType
    · simp [compileResultMode, hole] at compiled
      subst mode
      simp [OutputGuard, hole, ResultMode.Accepts]
    · by_cases atom : expected = atomType
      · simp [compileResultMode, atom] at compiled
        subst mode
        simp [OutputGuard, atom, ResultMode.Accepts]
      · by_cases closed : termIsClosed expected = true
        · simp [compileResultMode, undefined, hole, atom, closed] at compiled
          subst mode
          simp [OutputGuard, undefined, hole, atom, ResultMode.Accepts]
        · simp [compileResultMode, undefined, hole, atom, closed] at compiled

theorem compileArgumentModes_accepts
    {expectedTypes : List Term} {modes : List ArgMode}
    (compiled : compileArgumentModes expectedTypes = some modes)
    (snapshot : Snapshot) (sources values : List Term) :
    ArgumentsAccept snapshot modes sources values ↔
      ArgumentsGuard snapshot sources values expectedTypes := by
  induction expectedTypes generalizing modes sources values with
  | nil =>
      simp only [compileArgumentModes] at compiled
      cases compiled
      cases sources <;> cases values <;>
        simp [ArgumentsAccept, ArgumentsGuard]
  | cons expected expectedTypes ih =>
      simp only [compileArgumentModes] at compiled
      cases modeResult : compileArgMode expected with
      | none => simp [modeResult] at compiled
      | some mode =>
          cases modesResult : compileArgumentModes expectedTypes with
          | none => simp [modeResult, modesResult] at compiled
          | some tailModes =>
              simp [modeResult, modesResult] at compiled
              subst modes
              cases sources <;> cases values <;>
                simp [ArgumentsAccept, ArgumentsGuard,
                  compileArgMode_accepts modeResult,
                  ih modesResult]

theorem compileGuard_coordinateConsistent
    {declaration : ArrowDeclaration} {plan : GuardPlan}
    (compiled : compileGuard declaration = some plan) :
    plan.CoordinateConsistent := by
  unfold compileGuard at compiled
  cases modesResult : compileArgumentModes declaration.inputTypes with
  | none => simp [modesResult] at compiled
  | some modes =>
      cases resultModeResult : compileResultMode declaration.outputType with
      | none => simp [modesResult, resultModeResult] at compiled
      | some resultMode =>
          simp [modesResult, resultModeResult] at compiled
          subst plan
          exact ⟨rfl, compileArgumentModes_length modesResult⟩

theorem compileGuard_declaration_exact
    {declaration : ArrowDeclaration} {plan : GuardPlan}
    (compiled : compileGuard declaration = some plan) :
    plan.declaration = declaration := by
  unfold compileGuard at compiled
  cases modesResult : compileArgumentModes declaration.inputTypes with
  | none => simp [modesResult] at compiled
  | some modes =>
      cases resultModeResult : compileResultMode declaration.outputType with
      | none => simp [modesResult, resultModeResult] at compiled
      | some resultMode =>
          simp [modesResult, resultModeResult] at compiled
          subst plan
          rfl

theorem compileGuard_accepts
    {snapshot : Snapshot}
    {declaration : ArrowDeclaration} {plan : GuardPlan}
    (compiled : compileGuard declaration = some plan)
    (call : Call) :
    plan.Accepts snapshot call ↔
      declaration.function = call.function ∧
        ArgumentsGuard snapshot call.sourceArguments
          call.evaluatedArguments declaration.inputTypes ∧
        OutputGuard snapshot call.result declaration.outputType := by
  unfold compileGuard at compiled
  cases modesResult : compileArgumentModes declaration.inputTypes with
  | none => simp [modesResult] at compiled
  | some modes =>
      cases resultModeResult : compileResultMode declaration.outputType with
      | none => simp [modesResult, resultModeResult] at compiled
      | some resultMode =>
          simp [modesResult, resultModeResult] at compiled
          subst plan
          simp only [GuardPlan.Accepts]
          rw [compileArgumentModes_accepts modesResult,
            compileResultMode_accepts resultModeResult]

theorem plan_result_guard_exact
    {expected : Term} {mode : ResultMode}
    (compiled : compileResultMode expected = some mode)
    (snapshot : Snapshot) (value : Term) :
    mode.Accepts snapshot value ↔ OutputGuard snapshot value expected :=
  compileResultMode_accepts compiled snapshot value

theorem family_foreign_owner_inactive
    (family : CompiledGuardFamily) (current : OwnedSnapshot)
    (foreign : family.owner ≠ current.owner) :
    ¬ family.CurrentAt current := by
  intro current
  exact foreign current.1

theorem family_stale_revision_inactive
    (family : CompiledGuardFamily) (current : OwnedSnapshot)
    (stale : family.revision ≠ current.snapshot.revision) :
    ¬ family.CurrentAt current := by
  intro current
  exact stale current.2

private theorem argumentsGuard_lengths
    {snapshot : Snapshot} {sources values expectedTypes : List Term}
    (guarded : ArgumentsGuard snapshot sources values expectedTypes) :
    sources.length = expectedTypes.length ∧
      values.length = expectedTypes.length := by
  induction sources generalizing values expectedTypes with
  | nil =>
      cases values <;> cases expectedTypes <;>
        simp_all [ArgumentsGuard]
  | cons source sources ih =>
      cases values with
      | nil => cases expectedTypes <;> simp_all [ArgumentsGuard]
      | cons value values =>
          cases expectedTypes with
          | nil => simp_all [ArgumentsGuard]
          | cons expected expectedTypes =>
              have tailLengths := ih guarded.2
              simp [tailLengths]

private theorem guardedBy_iff_guard_core
    {snapshot : Snapshot} {call : Call} {declaration : ArrowDeclaration}
    (wellFormed : snapshot.WellFormed)
    (member : declaration ∈ snapshot.declarations) :
    GuardedBy declaration ⟨snapshot, call⟩ ↔
      declaration.function = call.function ∧
        ArgumentsGuard snapshot call.sourceArguments
          call.evaluatedArguments declaration.inputTypes ∧
        OutputGuard snapshot call.result declaration.outputType := by
  simp [GuardedBy, wellFormed, member]

private theorem not_relevant_not_guarded
    {snapshot : Snapshot} {call : Call} {declaration : ArrowDeclaration}
    {head : String} {arity : Nat}
    (wellFormed : snapshot.WellFormed)
    (member : declaration ∈ snapshot.declarations)
    (callHead : call.function = head)
    (callArity : call.sourceArguments.length = arity)
    (notRelevant : ¬ Relevant declaration head arity) :
    ¬ GuardedBy declaration ⟨snapshot, call⟩ := by
  intro guarded
  have core :=
    (guardedBy_iff_guard_core wellFormed member).1 guarded
  have lengths := argumentsGuard_lengths core.2.1
  apply notRelevant
  constructor
  · exact core.1.trans callHead
  · exact lengths.1.symm.trans callArity

namespace CompiledGuardFamily

/- Cold-path semantic validity is exact compiler production at the current
authority.  Exactness matters for order, completeness, and empty families. -/
def ValidFor (family : CompiledGuardFamily) (owned : OwnedSnapshot) : Prop :=
  owned.snapshot.WellFormed ∧
    family.CurrentAt owned ∧
      compileGuards owned family.head family.arity = .compiled family

instance (family : CompiledGuardFamily) (owned : OwnedSnapshot) :
    Decidable (family.ValidFor owned) := by
  unfold ValidFor
  infer_instance

end CompiledGuardFamily

private theorem compileRelevantGuards_coordinates
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat) :
    ∀ (declarations : List ArrowDeclaration) (family : CompiledGuardFamily),
      compileRelevantGuards owner revision head arity declarations =
        .compiled family →
      family.owner = owner ∧ family.revision = revision ∧
        family.head = head ∧ family.arity = arity := by
  intro declarations
  induction declarations with
  | nil =>
      intro family compiled
      simp [compileRelevantGuards] at compiled
      subst family
      simp
  | cons declaration declarations ih =>
      intro family compiled
      by_cases relevant : Relevant declaration head arity
      · simp only [compileRelevantGuards, if_pos relevant] at compiled
        cases planResult : compileGuard declaration with
        | none => simp [planResult] at compiled
        | some plan =>
            cases tailResult :
                compileRelevantGuards owner revision head arity declarations with
            | outsideFragment => simp [planResult, tailResult] at compiled
            | compiled tailFamily =>
                simp [planResult, tailResult] at compiled
                subst family
                exact ih tailFamily tailResult
      · simp only [compileRelevantGuards, if_neg relevant] at compiled
        exact ih family compiled

/- Exact family coordinates produced for one compilation request. -/
theorem compileGuards_coordinates
    {owned : OwnedSnapshot} {head : String} {arity : Nat}
    {family : CompiledGuardFamily}
    (compiled : compileGuards owned head arity = .compiled family) :
    family.owner = owned.owner ∧
      family.revision = owned.snapshot.revision ∧
        family.head = head ∧ family.arity = arity := by
  unfold compileGuards at compiled
  exact compileRelevantGuards_coordinates
    owned.owner owned.snapshot.revision head arity
    owned.snapshot.declarations family compiled

private theorem compileRelevantGuards_plans_valid
    (snapshot : Snapshot) (owner : SpaceOwner) (revision : Nat)
    (head : String) (arity : Nat) :
    ∀ (declarations : List ArrowDeclaration) (family : CompiledGuardFamily),
      (∀ declaration, declaration ∈ declarations →
        declaration ∈ snapshot.declarations) →
      compileRelevantGuards owner revision head arity declarations =
        .compiled family →
      ∀ plan ∈ family.plans,
        plan.ProducedIn snapshot ∧
          Relevant plan.declaration head arity := by
  intro declarations
  induction declarations with
  | nil =>
      intro family _ compiled
      simp [compileRelevantGuards] at compiled
      subst family
      simp
  | cons declaration declarations ih =>
      intro family allMembers compiled
      have declarationMember : declaration ∈ snapshot.declarations :=
        allMembers declaration (by simp)
      have tailMembers : ∀ candidate, candidate ∈ declarations →
          candidate ∈ snapshot.declarations := by
        intro candidate member
        exact allMembers candidate (by simp [member])
      by_cases relevant : Relevant declaration head arity
      · simp only [compileRelevantGuards, if_pos relevant] at compiled
        cases planResult : compileGuard declaration with
        | none => simp [planResult] at compiled
        | some plan =>
            cases tailResult :
                compileRelevantGuards owner revision head arity declarations with
            | outsideFragment => simp [planResult, tailResult] at compiled
            | compiled tailFamily =>
                simp [planResult, tailResult] at compiled
                subst family
                intro candidate member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · have planDeclaration :=
                    compileGuard_declaration_exact planResult
                  constructor
                  · constructor
                    · simpa [planDeclaration] using declarationMember
                    · simpa [planDeclaration] using planResult
                  · simpa [planDeclaration] using relevant
                · exact ih tailFamily tailMembers tailResult candidate member
      · simp only [compileRelevantGuards, if_neg relevant] at compiled
        exact ih family tailMembers compiled

theorem compileGuards_family_valid
    (owned : OwnedSnapshot) (head : String) (arity : Nat)
    (family : CompiledGuardFamily)
    (wellFormed : owned.snapshot.WellFormed)
    (compiled : compileGuards owned head arity = .compiled family) :
    family.ValidFor owned := by
  have coordinates := compileGuards_coordinates compiled
  constructor
  · exact wellFormed
  · constructor
    · exact ⟨coordinates.1, coordinates.2.1⟩
    · simpa [coordinates.2.2.1, coordinates.2.2.2] using compiled

theorem CompiledGuardFamily.validFor_plan_valid
    {owned : OwnedSnapshot} {family : CompiledGuardFamily}
    {plan : GuardPlan}
    (valid : family.ValidFor owned) (member : plan ∈ family.plans) :
    plan.ValidIn owned.snapshot ∧
      Relevant plan.declaration family.head family.arity := by
  rcases valid with ⟨wellFormed, _, produced⟩
  unfold compileGuards at produced
  have planProduced := compileRelevantGuards_plans_valid
    owned.snapshot owned.owner owned.snapshot.revision family.head family.arity
    owned.snapshot.declarations family (by simp) produced plan member
  exact ⟨⟨wellFormed, planProduced.1⟩, planProduced.2⟩

theorem validIn_accepts_iff_guardedBy
    {plan : GuardPlan} {snapshot : Snapshot} {call : Call}
    (valid : plan.ValidIn snapshot) :
    plan.Accepts snapshot call ↔
      GuardedBy plan.declaration ⟨snapshot, call⟩ :=
  (compileGuard_accepts valid.2.2 call).trans
    (guardedBy_iff_guard_core valid.1 valid.2.1).symm

private theorem compileRelevantGuards_execute_exact
    (owner : SpaceOwner) (snapshot : Snapshot) (call : Call)
    (head : String) (arity : Nat)
    (wellFormed : snapshot.WellFormed)
    (callHead : call.function = head)
    (callArity : call.sourceArguments.length = arity) :
    ∀ (declarations : List ArrowDeclaration) (family : CompiledGuardFamily),
      (∀ declaration, declaration ∈ declarations →
        declaration ∈ snapshot.declarations) →
      compileRelevantGuards owner snapshot.revision head arity declarations =
        .compiled family →
      executePlanList snapshot call family.plans =
        declarations.filter fun declaration =>
          decide (GuardedBy declaration (⟨snapshot, call⟩ : Claim)) := by
  intro declarations
  induction declarations with
  | nil =>
      intro family _ compiled
      simp [compileRelevantGuards] at compiled
      subst family
      rfl
  | cons declaration declarations ih =>
      intro family allMembers compiled
      have declarationMember : declaration ∈ snapshot.declarations :=
        allMembers declaration (by simp)
      have tailMembers : ∀ candidate, candidate ∈ declarations →
          candidate ∈ snapshot.declarations := by
        intro candidate member
        exact allMembers candidate (by simp [member])
      by_cases relevant : Relevant declaration head arity
      · simp only [compileRelevantGuards, if_pos relevant] at compiled
        cases planResult : compileGuard declaration with
        | none => simp [planResult] at compiled
        | some plan =>
            cases tailResult :
                compileRelevantGuards owner snapshot.revision head arity declarations with
            | outsideFragment => simp [planResult, tailResult] at compiled
            | compiled tailFamily =>
                simp [planResult, tailResult] at compiled
                subst family
                have tailExact :=
                  ih tailFamily tailMembers tailResult
                have planDeclaration := compileGuard_declaration_exact planResult
                have acceptsIff := compileGuard_accepts
                  (snapshot := snapshot) planResult call
                have guardedIff :=
                  guardedBy_iff_guard_core (call := call)
                    wellFormed declarationMember
                have acceptGuardIff :
                    plan.Accepts snapshot call ↔
                      GuardedBy declaration ⟨snapshot, call⟩ :=
                  acceptsIff.trans guardedIff.symm
                by_cases guarded :
                    GuardedBy declaration ⟨snapshot, call⟩
                · have accepted := acceptGuardIff.2 guarded
                  simp [executePlanList, accepted, guarded, planDeclaration,
                    tailExact]
                · have rejected : ¬ plan.Accepts snapshot call :=
                    fun accepted => guarded (acceptGuardIff.1 accepted)
                  simp [executePlanList, rejected, guarded, tailExact]
      · simp only [compileRelevantGuards, if_neg relevant] at compiled
        have tailExact := ih family tailMembers compiled
        have notGuarded := not_relevant_not_guarded wellFormed
          declarationMember callHead callArity relevant
        simp [notGuarded, tailExact]

/-! ## Exact ordered-list theorem and consequences -/

/-- The strongest G2 result: successful generated plans are exactly the
existing authored-order declaration fibre, as a list rather than a Boolean or
set projection. -/
theorem executePlanList_eq_successfulDeclarations
    (owned : OwnedSnapshot) (call : Call)
    (family : CompiledGuardFamily)
    (wellFormed : owned.snapshot.WellFormed)
    (compiled :
      compileGuards owned call.function call.sourceArguments.length =
        .compiled family) :
    executePlanList owned.snapshot call family.plans =
      successfulDeclarations ⟨owned.snapshot, call⟩ := by
  unfold compileGuards at compiled
  exact compileRelevantGuards_execute_exact owned.owner owned.snapshot call
    call.function call.sourceArguments.length wellFormed rfl rfl
    owned.snapshot.declarations family (by simp) compiled

/- The strongest G2 observation theorem: current compiled-family execution is
exactly the authored successful-declaration list. -/
theorem executeGuardFamily_eq_successfulDeclarations
    (owned : OwnedSnapshot) (call : Call)
    (family : CompiledGuardFamily)
    (valid : family.ValidFor owned)
    (requestMatches : family.MatchesCall call) :
    executeGuardFamily owned call family =
      .executed (successfulDeclarations ⟨owned.snapshot, call⟩) := by
  have compiled := valid.2.2
  rw [requestMatches.1, requestMatches.2] at compiled
  have exact := executePlanList_eq_successfulDeclarations
    owned call family valid.1 compiled
  simp [executeGuardFamily, valid.2.1.1, valid.2.1.2,
    requestMatches.1, requestMatches.2, exact]

theorem executeCompilation_eq_successfulDeclarations
    (owned : OwnedSnapshot) (call : Call)
    (family : CompiledGuardFamily)
    (valid : family.ValidFor owned)
    (requestMatches : family.MatchesCall call) :
    executeCompilation owned call (.compiled family) =
      .executed (successfulDeclarations ⟨owned.snapshot, call⟩) := by
  unfold executeCompilation
  exact executeGuardFamily_eq_successfulDeclarations
    owned call family valid requestMatches

theorem compileGuards_sound
    {owned : OwnedSnapshot} {call : Call}
    {family : CompiledGuardFamily} {observed : List ArrowDeclaration}
    {declaration : ArrowDeclaration}
    (valid : family.ValidFor owned)
    (requestMatches : family.MatchesCall call)
    (execution : executeGuardFamily owned call family = .executed observed)
    (member : declaration ∈ observed) :
    declaration ∈ successfulDeclarations ⟨owned.snapshot, call⟩ := by
  have exact := executeGuardFamily_eq_successfulDeclarations
    owned call family valid requestMatches
  rw [exact] at execution
  cases execution
  exact member

theorem compileGuards_complete
    {owned : OwnedSnapshot} {call : Call}
    {family : CompiledGuardFamily} {observed : List ArrowDeclaration}
    {declaration : ArrowDeclaration}
    (valid : family.ValidFor owned)
    (requestMatches : family.MatchesCall call)
    (execution : executeGuardFamily owned call family = .executed observed)
    (member : declaration ∈ successfulDeclarations ⟨owned.snapshot, call⟩) :
    declaration ∈ observed := by
  have exact := executeGuardFamily_eq_successfulDeclarations
    owned call family valid requestMatches
  rw [exact] at execution
  cases execution
  exact member

theorem compileGuards_order_exact
    {owned : OwnedSnapshot} {call : Call}
    {family : CompiledGuardFamily} {observed : List ArrowDeclaration}
    (valid : family.ValidFor owned)
    (requestMatches : family.MatchesCall call)
    (execution : executeGuardFamily owned call family = .executed observed) :
    List.Sublist observed owned.snapshot.declarations := by
  have exact := executeGuardFamily_eq_successfulDeclarations
    owned call family valid requestMatches
  rw [exact] at execution
  cases execution
  exact List.filter_sublist

theorem compileGuards_no_invention
    {owned : OwnedSnapshot} {call : Call}
    {family : CompiledGuardFamily} {observed : List ArrowDeclaration}
    {declaration : ArrowDeclaration}
    (valid : family.ValidFor owned)
    (requestMatches : family.MatchesCall call)
    (execution : executeGuardFamily owned call family = .executed observed)
    (member : declaration ∈ observed) :
    declaration ∈ owned.snapshot.declarations :=
  (compileGuards_order_exact valid requestMatches execution).subset member

private theorem compileRelevantGuards_declines_of_unsupported_member
    {owner : SpaceOwner} {revision : Nat}
    {head : String} {arity : Nat} {declaration : ArrowDeclaration}
    (relevant : Relevant declaration head arity)
    (unsupported : compileGuard declaration = none) :
    ∀ declarations : List ArrowDeclaration,
      declaration ∈ declarations →
      compileRelevantGuards owner revision head arity declarations =
        .outsideFragment := by
  intro declarations
  induction declarations with
  | nil => simp
  | cons candidate declarations ih =>
      intro member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [compileRelevantGuards, relevant, unsupported]
      · by_cases candidateRelevant : Relevant candidate head arity
        · simp only [compileRelevantGuards, if_pos candidateRelevant]
          cases candidatePlan : compileGuard candidate with
          | none => simp
          | some plan => simp [ih member]
        · simp [compileRelevantGuards, candidateRelevant, ih member]

theorem unsupported_relevant_declaration_declines_family
    {owned : OwnedSnapshot}
    {head : String} {arity : Nat} {declaration : ArrowDeclaration}
    (member : declaration ∈ owned.snapshot.declarations)
    (relevant : Relevant declaration head arity)
    (unsupported : compileGuard declaration = none) :
    compileGuards owned head arity = .outsideFragment := by
  unfold compileGuards
  exact compileRelevantGuards_declines_of_unsupported_member
    relevant unsupported owned.snapshot.declarations member

/-! ## Positive and negative executable canaries -/

namespace Canary

def owner : SpaceOwner := ⟨91⟩
def foreignOwner : SpaceOwner := ⟨92⟩

def owned (snapshot : Snapshot) : OwnedSnapshot := ⟨owner, snapshot⟩

def rawPlan : GuardPlan :=
  { declarationOccurrence :=
      CallGuardNativeKernel.Canary.declaration.occurrence
    argumentModes := [.rawAtom]
    resultMode := .resultSoftcutType numberType
    declaration := CallGuardNativeKernel.Canary.declaration }

def rawFamily : CompiledGuardFamily :=
  ⟨owner, CallGuardNativeKernel.Canary.snapshot.revision,
    "f", 1, [rawPlan]⟩

def emptyFamily : CompiledGuardFamily :=
  ⟨owner, CallGuardNativeKernel.Canary.snapshot.revision,
    "absent", 3, []⟩

theorem raw_atom_plan_compiles :
    compileGuards (owned CallGuardNativeKernel.Canary.snapshot) "f" 1 =
      .compiled rawFamily := by
  decide

theorem no_applicable_declaration_compiles_empty_family :
    compileGuards (owned CallGuardNativeKernel.Canary.snapshot) "absent" 3 =
      .compiled emptyFamily := by
  decide

theorem raw_atom_plan_accepts :
    executeGuardFamily (owned CallGuardNativeKernel.Canary.snapshot)
      CallGuardNativeKernel.Canary.claim.call rawFamily =
        .executed [CallGuardNativeKernel.Canary.declaration] := by
  decide

theorem changed_raw_atom_plan_rejected :
    executeGuardFamily (owned CallGuardNativeKernel.Canary.snapshot)
      CallGuardNativeKernel.Canary.changedRawClaim.call rawFamily =
        .executed [] := by
  decide

theorem current_empty_family_executes_empty :
    executeGuardFamily (owned CallGuardNativeKernel.Canary.snapshot)
      ⟨"absent", [.number "1", .number "2", .number "3"],
        [.number "1", .number "2", .number "3"], .number "4"⟩
      emptyFamily = .executed [] := by
  decide

def uncheckedInputDeclaration : ArrowDeclaration :=
  ⟨20, "u", [undefinedType, holeType], numberType⟩

def uncheckedInputSnapshot : Snapshot :=
  ⟨8, [uncheckedInputDeclaration], [], ["u"]⟩

def uncheckedInputCall : Call :=
  ⟨"u", [.atom "x", .atom "y"], [.number "1", .string "two"],
    .number "3"⟩

theorem undefined_and_hole_inputs_evaluate_unchecked :
    ∃ family,
      compileGuards (owned uncheckedInputSnapshot) "u" 2 =
        .compiled family ∧
      executeGuardFamily (owned uncheckedInputSnapshot)
        uncheckedInputCall family = .executed [uncheckedInputDeclaration] := by
  refine ⟨_, rfl, ?_⟩
  decide

def exactTypeDeclaration : ArrowDeclaration :=
  ⟨21, "n", [numberType], numberType⟩

def exactTypeSnapshot : Snapshot :=
  ⟨9, [exactTypeDeclaration], [], ["n"]⟩

def exactTypeCall : Call :=
  ⟨"n", [.number "1"], [.number "1"], .number "2"⟩

theorem exact_getType_input_and_result_accept :
    ∃ family,
      compileGuards (owned exactTypeSnapshot) "n" 1 = .compiled family ∧
      executeGuardFamily (owned exactTypeSnapshot) exactTypeCall family =
        .executed [exactTypeDeclaration] := by
  refine ⟨_, rfl, ?_⟩
  decide

theorem metatype_fallback_accepts :
    ∃ family,
      compileGuards
        (owned CallGuardNativeKernel.Canary.fallbackClaim.snapshot)
        "g" 1 = .compiled family ∧
      executeGuardFamily
        (owned CallGuardNativeKernel.Canary.fallbackClaim.snapshot)
        CallGuardNativeKernel.Canary.fallbackClaim.call family =
        .executed [CallGuardNativeKernel.Canary.fallbackDeclaration] := by
  refine ⟨_, rfl, ?_⟩
  decide

theorem getType_success_excludes_extra_metatype_requirement :
    (ArgMode.evalSoftcutType numberType).Accepts exactTypeSnapshot
      (.number "1") (.number "1") ∧
    ¬ GetMetatype exactTypeSnapshot (.number "1") numberType := by
  decide

def unrestrictedResultDeclarations : List ArrowDeclaration :=
  [⟨30, "a", [], atomType⟩,
   ⟨31, "u", [], undefinedType⟩,
   ⟨32, "h", [], holeType⟩]

theorem unrestricted_result_modes_compile :
    unrestrictedResultDeclarations.map
        (fun declaration =>
          compileResultMode declaration.outputType) =
      [some .resultUnchecked, some .resultUnchecked,
        some .resultUnchecked] := by
  decide

theorem two_overloads_retain_exact_source_order :
    ∃ family,
      compileGuards
        (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot) "f" 1 =
          .compiled family ∧
      family.plans.map GuardPlan.declaration =
        [CallGuardNativeKernel.Canary.declaration,
          CallGuardNativeKernel.Canary.alternativeDeclaration] ∧
      executeGuardFamily
        (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot)
        CallGuardNativeKernel.Canary.overloadedClaim.call family =
        .executed [CallGuardNativeKernel.Canary.declaration,
          CallGuardNativeKernel.Canary.alternativeDeclaration] := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> decide

def duplicateSource : SourceSnapshot :=
  ⟨owner, 10,
    [CallGuardNativeKernel.Canary.declaration,
      { CallGuardNativeKernel.Canary.declaration with occurrence := 99 }],
    [], ["f"]⟩

theorem resolved_duplicate_yields_one_first_occurrence_plan :
    ∃ family,
      compileGuards duplicateSource.resolve "f" 1 = .compiled family ∧
      family.plans.map GuardPlan.declarationOccurrence = [10] := by
  refine ⟨_, rfl, ?_⟩
  decide

def wrongOrdinaryInputCall : Call :=
  ⟨"n", [.string "bad"], [.string "bad"], .number "2"⟩

def wrongOrdinaryResultCall : Call :=
  ⟨"n", [.number "1"], [.number "1"], .string "bad"⟩

theorem wrong_ordinary_input_and_result_fail :
    ∃ family,
      compileGuards (owned exactTypeSnapshot) "n" 1 = .compiled family ∧
      executeGuardFamily (owned exactTypeSnapshot)
        wrongOrdinaryInputCall family = .executed [] ∧
      executeGuardFamily (owned exactTypeSnapshot)
        wrongOrdinaryResultCall family = .executed [] := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> decide

def foreignCurrent : OwnedSnapshot :=
  ⟨foreignOwner, CallGuardNativeKernel.Canary.snapshot⟩

def staleCurrent : OwnedSnapshot :=
  ⟨owner, { CallGuardNativeKernel.Canary.snapshot with revision := 8 }⟩

theorem foreign_owner_and_stale_revision_fallback :
    executeGuardFamily foreignCurrent
        CallGuardNativeKernel.Canary.claim.call rawFamily =
          .fallback .foreignOwner ∧
      executeGuardFamily staleCurrent
        CallGuardNativeKernel.Canary.claim.call rawFamily =
          .fallback .staleRevision := by
  decide

theorem rejection_is_distinct_from_authority_fallback :
    GuardExecution.executed [] ≠ .fallback .foreignOwner ∧
      GuardExecution.executed [] ≠ .fallback .staleRevision := by
  decide

def wrongHeadCall : Call :=
  { CallGuardNativeKernel.Canary.claim.call with function := "other" }

def wrongArityCall : Call :=
  { CallGuardNativeKernel.Canary.claim.call with
    sourceArguments := []
    evaluatedArguments := [] }

theorem wrong_head_and_arity_do_not_activate :
    executeGuardFamily (owned CallGuardNativeKernel.Canary.snapshot)
        wrongHeadCall rawFamily = .fallback .wrongHead ∧
      executeGuardFamily (owned CallGuardNativeKernel.Canary.snapshot)
        wrongArityCall rawFamily = .fallback .wrongArity := by
  decide

def polymorphicDeclaration : ArrowDeclaration :=
  ⟨40, "f", [.variable "T"], .variable "T"⟩

def mixedSupportedAndOpenSnapshot : Snapshot :=
  ⟨11,
    [CallGuardNativeKernel.Canary.declaration, polymorphicDeclaration],
    [], ["f"]⟩

theorem one_open_relevant_overload_declines_whole_family :
    compileGuards (owned mixedSupportedAndOpenSnapshot) "f" 1 =
      .outsideFragment := by
  decide

theorem outside_fragment_requests_fallback :
    executeCompilation (owned mixedSupportedAndOpenSnapshot)
      CallGuardNativeKernel.Canary.claim.call .outsideFragment =
        .fallback .outsideFragment := by
  rfl

def reversedOverloadSnapshot : Snapshot :=
  { CallGuardNativeKernel.Canary.overloadedClaim.snapshot with
    declarations :=
      [CallGuardNativeKernel.Canary.alternativeDeclaration,
        CallGuardNativeKernel.Canary.declaration] }

theorem changing_declaration_order_changes_plan_order :
    ∃ forward reverse,
      compileGuards
          (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot) "f" 1 =
        .compiled forward ∧
      compileGuards (owned reversedOverloadSnapshot) "f" 1 =
        .compiled reverse ∧
      forward.plans.map GuardPlan.declaration =
        [CallGuardNativeKernel.Canary.declaration,
          CallGuardNativeKernel.Canary.alternativeDeclaration] ∧
      reverse.plans.map GuardPlan.declaration =
        [CallGuardNativeKernel.Canary.alternativeDeclaration,
          CallGuardNativeKernel.Canary.declaration] ∧
      List.Perm
        (successfulDeclarations
          CallGuardNativeKernel.Canary.overloadedClaim)
        (successfulDeclarations
          ⟨reversedOverloadSnapshot,
            CallGuardNativeKernel.Canary.overloadedClaim.call⟩) := by
  refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

def forgedPlan : GuardPlan :=
  { declarationOccurrence := exactTypeDeclaration.occurrence
    argumentModes := [.evalUnchecked]
    resultMode := .resultUnchecked
    declaration := exactTypeDeclaration }

def forgedCall : Call :=
  ⟨"n", [.string "bad"], [.string "bad"], .string "bad"⟩

theorem forged_plan_is_coordinate_consistent :
    forgedPlan.CoordinateConsistent := by
  decide

theorem forged_plan_accepts_but_is_not_valid :
    forgedPlan.Accepts exactTypeSnapshot forgedCall ∧
      ¬ forgedPlan.ValidIn exactTypeSnapshot ∧
      ¬ GuardedBy exactTypeDeclaration
        (⟨exactTypeSnapshot, forgedCall⟩ : Claim) := by
  decide

def forgedFamily : CompiledGuardFamily :=
  ⟨owner, exactTypeSnapshot.revision, "n", 1, [forgedPlan]⟩

def forgedEmptyFamily : CompiledGuardFamily :=
  ⟨owner, CallGuardNativeKernel.Canary.snapshot.revision, "f", 1, []⟩

theorem forged_plan_and_empty_families_are_not_valid :
    ¬ forgedFamily.ValidFor (owned exactTypeSnapshot) ∧
      ¬ forgedEmptyFamily.ValidFor
        (owned CallGuardNativeKernel.Canary.snapshot) := by
  decide

theorem compiled_family_is_semantically_valid :
    ∃ family,
      compileGuards (owned exactTypeSnapshot) "n" 1 = .compiled family ∧
        family.ValidFor (owned exactTypeSnapshot) := by
  rcases exact_getType_input_and_result_accept with
    ⟨family, compiled, _⟩
  exact ⟨family, compiled,
    compileGuards_family_valid (owned exactTypeSnapshot) "n" 1
      family (by decide) compiled⟩

def illFormedSnapshot : Snapshot :=
  { exactTypeSnapshot with registeredFunctions := ["n", "n"] }

theorem ill_formed_snapshot_compiles_but_is_not_valid :
    ∃ family,
      compileGuards (owned illFormedSnapshot) "n" 1 = .compiled family ∧
      executeGuardFamily (owned illFormedSnapshot) exactTypeCall family =
        .executed [exactTypeDeclaration] ∧
      successfulDeclarations (⟨illFormedSnapshot, exactTypeCall⟩ : Claim) = [] ∧
      ¬ family.ValidFor (owned illFormedSnapshot) := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩ <;> decide

end Canary

#print axioms compileArgumentModes_length
#print axioms plan_softcut_exact
#print axioms plan_atom_raw_exact
#print axioms plan_unchecked_inputs_exact
#print axioms compileArgMode_accepts
#print axioms compileResultMode_accepts
#print axioms compileArgumentModes_accepts
#print axioms GuardExecution.fallback_ne_executed
#print axioms executeGuardFamily_foreign_owner
#print axioms executeGuardFamily_stale_revision
#print axioms executeCompilation_outsideFragment
#print axioms compileGuard_coordinateConsistent
#print axioms compileGuard_declaration_exact
#print axioms compileGuard_accepts
#print axioms plan_result_guard_exact
#print axioms family_foreign_owner_inactive
#print axioms family_stale_revision_inactive
#print axioms compileGuards_coordinates
#print axioms compileGuards_family_valid
#print axioms CompiledGuardFamily.validFor_plan_valid
#print axioms validIn_accepts_iff_guardedBy
#print axioms executePlanList_eq_successfulDeclarations
#print axioms executeGuardFamily_eq_successfulDeclarations
#print axioms executeCompilation_eq_successfulDeclarations
#print axioms compileGuards_sound
#print axioms compileGuards_complete
#print axioms compileGuards_order_exact
#print axioms compileGuards_no_invention
#print axioms unsupported_relevant_declaration_declines_family
#print axioms Canary.raw_atom_plan_accepts
#print axioms Canary.no_applicable_declaration_compiles_empty_family
#print axioms Canary.changed_raw_atom_plan_rejected
#print axioms Canary.current_empty_family_executes_empty
#print axioms Canary.undefined_and_hole_inputs_evaluate_unchecked
#print axioms Canary.metatype_fallback_accepts
#print axioms Canary.foreign_owner_and_stale_revision_fallback
#print axioms Canary.rejection_is_distinct_from_authority_fallback
#print axioms Canary.one_open_relevant_overload_declines_whole_family
#print axioms Canary.outside_fragment_requests_fallback
#print axioms Canary.changing_declaration_order_changes_plan_order
#print axioms Canary.forged_plan_is_coordinate_consistent
#print axioms Canary.forged_plan_accepts_but_is_not_valid
#print axioms Canary.forged_plan_and_empty_families_are_not_valid
#print axioms Canary.compiled_family_is_semantically_valid
#print axioms Canary.ill_formed_snapshot_compiles_but_is_not_valid

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
