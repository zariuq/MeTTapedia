import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidual

/-!
# Native states up to dead names: inclusions, and live firings carried along them

A **dead name** of a native state is a frame name or private-family name that no row, equation,
guard, query or scope mentions. A state with dead names is another state seen through an
**inclusion** (`Inclusion`): injective, arity-preserving maps of the private family and of the
frame's names. A **dead-name extension** (`DeadExtension`) is an inclusion along which every row is
the carried row, the knowledge is the carried knowledge up to the order of its equations, and the
present occurrences and the scope ledger are the same. The names the inclusion misses are dead.

## Carrying

Every frame map here is a reindexing: of the frame (`Inclusion.frame`), of the rule frame
(`Inclusion.source`), and of the information frame (`Inclusion.target`, an extension in the sense
of `ContextualGuardMatching.Extension`). They commute with capturing and with opening at a scope
(`target_captured`, `target_freshening`). A row is carried by moving its captures and then its
private names (`Inclusion.row`); carrying composes (`row_comp`).

## Matching along an injective private reindexing

`matches_reindexPrivate_iff`: a row whose private names are moved injectively matches exactly what
the row matched. The off-image private names receive fresh generators in a larger witness frame;
no inhabitant of any sort is assumed. Guards and regions follow (`holds_reindexPrivate_iff`,
`region_reindexPrivate`).

## Live firings along a dead-name extension

A live firing is carried by carrying its rule, outputs and query patterns (`Inclusion.firing`).

* **Preparation is carried** (`prepared_rule_carried`, `prepared_take_carried`,
  `prepared_read_carried`, `addedEquations_carried`, `latent_carried`), and so is the information,
  up to the order of its equations (`information_carried`).
* **Guards and queries are carried**, read at the restriction of a solution
  (`guardRows_carried`, `holds_carried_iff`, `query_carried_iff`).
* **Admission is invariant** (`DeadExtension.admits_iff`): a live firing is admitted exactly when
  its carrying is. The direction from the larger state uses the fresh-generator lift of solutions
  (`ContextualGuardMatching.Extension.liftModel`), so a solution of the smaller state's information
  never needs a term for a dead name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP (ScopedVar)
open ContextualPredicateQueryAdmission (nativeLabels matchingQuery)
open ContextualGuardMatching (Extension instanceAssignment)
open ContextualPrefixModels (inclusion extended)

namespace NativeDead

/-! ## Reindexing -/

section Reindex

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}

/-- A reindexing depends on its map of identities only. -/
theorem reindex_congr {first second : V → W} (same : first = second)
    (firstPreserves : ∀ identity, target (first identity) = source identity)
    (secondPreserves : ∀ identity, target (second identity) = source identity) :
    reindex first firstPreserves = reindex second secondPreserves := by
  subst same
  rfl

end Reindex

/-! ## Matching along an injective private reindexing -/

section Private

variable {S : Signature} {Local Added Shared Next Future Extra : Type}
  (locals : Local → MetaArity S) (added : Added → MetaArity S) (captures : Shared → MetaArity S)
  {next : Next → MetaArity S} {future : Future → MetaArity S}

/-- Composing a local instance with a fresh inclusion. -/
theorem instance_inclusion (unused : Extra → MetaArity S) (images : Assignment locals future)
    (embedding : Assignment next future) (candidate : Assignment captures next) :
    instanceAssignment locals (Assignment.compose (inclusion unused future) images)
        (Assignment.compose (inclusion unused future) embedding) candidate =
      Assignment.compose (inclusion unused future) (instanceAssignment locals images embedding candidate) := by
  funext name
  cases name with
  | inl name => rfl
  | inr name => exact Assignment.instantiate_compose _ _ _

/-- The private family, moved injectively, as an extension. -/
abbrev privateExtension (names : Local → Added) (injective : Function.Injective names)
    (preserves : ∀ name, added (names name) = locals name) : Extension locals :=
  ⟨Added, added, names, injective, preserves⟩

/-- A witness frame grown by the off-image private names. -/
abbrev grownWitness (names : Local → Added) (injective : Function.Injective names)
    (preserves : ∀ name, added (names name) = locals name) (extension : Extension next) : Extension next :=
  ⟨(privateExtension locals added names injective preserves).Complement ⊕ extension.Names,
    extended (privateExtension locals added names injective preserves).complementDeclarations extension.declarations,
    fun name => Sum.inr (extension.name name), fun _ _ same => extension.injective (Sum.inr.inj same),
    fun name => extension.preserves name⟩

theorem grownWitness_assignment (names : Local → Added) (injective : Function.Injective names)
    (preserves : ∀ name, added (names name) = locals name) (extension : Extension next) :
    (grownWitness locals added names injective preserves extension).assignment =
      Assignment.compose (inclusion (privateExtension locals added names injective preserves).complementDeclarations
        extension.declarations) extension.assignment := by
  funext name
  show castMetaBody _ (generator _ (Sum.inr (extension.name name))) =
    instantiate (inclusion _ _) (castMetaBody _ (generator extension.declarations (extension.name name)))
  rw [instantiate_castMetaBody, instantiate_generator]
  rfl

/-- **The square of the grown witness**: the lifted local images, read through the private
reindexing, are the old instance followed by the fresh inclusion. -/
theorem grown_square (names : Local → Added) (injective : Function.Injective names)
    (preserves : ∀ name, added (names name) = locals name) (candidate : Assignment captures next)
    (extension : Extension next) (images : Assignment locals extension.declarations) :
    Assignment.compose
        (instanceAssignment added ((privateExtension locals added names injective preserves).liftModel images)
          (grownWitness locals added names injective preserves extension).assignment candidate)
        (ContextualConditionalPublication.privateReindex locals added captures names preserves) =
      Assignment.compose (inclusion (privateExtension locals added names injective preserves).complementDeclarations
        extension.declarations) (instanceAssignment locals images extension.assignment candidate) := by
  rw [ContextualConditionalPublication.instance_privateReindex, grownWitness_assignment]
  have square := (privateExtension locals added names injective preserves).liftModel_square images
  change Assignment.compose ((privateExtension locals added names injective preserves).liftModel images)
      (reindex names preserves) = _ at square
  rw [square]
  exact instance_inclusion locals captures _ images extension.assignment candidate

/-- **A row whose private names move injectively matches exactly what the row matched.** -/
theorem matches_reindexPrivate_iff (names : Local → Added) (injective : Function.Injective names)
    (preserves : ∀ name, added (names name) = locals name) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (row : ContextualConditionalRows.Row locals captures Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    ContextualConditionalRows.Matches added captures candidate pattern
        (ContextualConditionalPublication.reindexPrivate locals added captures names preserves row) ↔
      ContextualConditionalRows.Matches locals captures candidate pattern row := by
  constructor
  · exact ContextualConditionalPublication.matches_of_reindexPrivate locals added captures names preserves
      candidate row pattern
  · rintro ⟨extension, images, obligations, same⟩
    have square := grown_square locals added captures names injective preserves candidate extension images
    refine ⟨grownWitness locals added names injective preserves extension,
      (privateExtension locals added names injective preserves).liftModel images, ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      rw [square]
      exact ContextualResidual.models_compose obligations _
    · rw [ContextualConditionalPublication.reindexed_template, ← Assignment.instantiate_compose, square,
        Assignment.instantiate_compose, same, grownWitness_assignment, Assignment.instantiate_compose]

variable {O : Type}

theorem region_reindexPrivate (names : Local → Added) (injective : Function.Injective names)
    (preserves : ∀ name, added (names name) = locals name) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → ContextualConditionalRows.Row locals captures Γ sort)
    (world : Finset O) (pattern : Term (signature S captures) Γ sort) :
    ContextualConditionalGuards.region added candidate
        (fun o => ContextualConditionalPublication.reindexPrivate locals added captures names preserves (rows o))
        world pattern =
      ContextualConditionalGuards.region locals candidate rows world pattern := by
  classical
  ext o
  simp only [ContextualConditionalGuards.mem_region,
    matches_reindexPrivate_iff locals added captures names injective preserves]

theorem holds_reindexPrivate_iff (names : Local → Added) (injective : Function.Injective names)
    (preserves : ∀ name, added (names name) = locals name) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → ContextualConditionalRows.Row locals captures Γ sort)
    (world : Finset O) (check : Check (Term (signature S captures) Γ sort)) :
    ContextualConditionalGuards.Holds added candidate
        (fun o => ContextualConditionalPublication.reindexPrivate locals added captures names preserves (rows o))
        world check ↔
      ContextualConditionalGuards.Holds locals candidate rows world check := by
  cases check with
  | equal first second => exact Iff.rfl
  | absent pattern =>
      simp only [ContextualConditionalGuards.Holds,
        matches_reindexPrivate_iff locals added captures names injective preserves]
  | count pattern cardinality =>
      change (ContextualConditionalGuards.region added candidate _ world pattern).card = cardinality ↔
        (ContextualConditionalGuards.region locals candidate rows world pattern).card = cardinality
      rw [region_reindexPrivate locals added captures names injective preserves]

/-- Moving private names twice is moving them once. -/
theorem reindexPrivate_comp {Third : Type} (third : Third → MetaArity S) (first : Local → Added)
    (second : Added → Third) (firstPreserves : ∀ name, added (first name) = locals name)
    (secondPreserves : ∀ name, third (second name) = added name)
    {Γ : Ctx S} {sort : S.Srt} (row : ContextualConditionalRows.Row locals captures Γ sort) :
    ContextualConditionalPublication.reindexPrivate added third captures second secondPreserves
        (ContextualConditionalPublication.reindexPrivate locals added captures first firstPreserves row) =
      ContextualConditionalPublication.reindexPrivate locals third captures (fun name => second (first name))
        (fun name => (secondPreserves (first name)).trans (firstPreserves name)) row := by
  have square : Assignment.compose
      (ContextualConditionalPublication.privateReindex added third captures second secondPreserves)
      (ContextualConditionalPublication.privateReindex locals added captures first firstPreserves) =
    ContextualConditionalPublication.privateReindex locals third captures (fun name => second (first name))
      (fun name => (secondPreserves (first name)).trans (firstPreserves name)) := by
    unfold ContextualConditionalPublication.privateReindex
    rw [reindex_compose]
    exact reindex_congr (funext fun name => by cases name <;> rfl) _ _
  rcases row with ⟨value, obligations⟩
  apply congrArg₂ ContextualConditionalRows.Row.mk
  · cases value with
    | schema body =>
        change ContextualStoredRows.Row.schema (instantiate _ (instantiate _ body)) =
          ContextualStoredRows.Row.schema (instantiate _ body)
        rw [← Assignment.instantiate_compose, square]
    | shared value => rfl
  · change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ obligations) =
      ContextualResidual.mapProblem _ obligations
    rw [ContextualConditionalNaturality.map_problem_compose, square]

/-- **Extending the private family is an injective private reindexing.** -/
theorem extendPrivate_eq_reindexPrivate {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualConditionalRows.Row locals captures Γ sort) :
    ContextualConditionalPublication.extendPrivate locals added captures row =
      ContextualConditionalPublication.reindexPrivate locals (ContextualPublication.privateFamily locals added)
        captures Sum.inl (fun _ => rfl) row := by
  have same : ContextualPublication.includePrivate locals added (captures := captures) =
      ContextualConditionalPublication.privateReindex locals (ContextualPublication.privateFamily locals added)
        captures Sum.inl (fun _ => rfl) := by
    funext name
    cases name <;> rfl
  rcases row with ⟨value, obligations⟩
  apply congrArg₂ ContextualConditionalRows.Row.mk
  · cases value with
    | schema body =>
        change ContextualStoredRows.Row.schema (instantiate _ body) = ContextualStoredRows.Row.schema (instantiate _ body)
        rw [same]
    | shared value => rfl
  · change ContextualResidual.mapProblem _ obligations = ContextualResidual.mapProblem _ obligations
    rw [same]

end Private

/-! ## Inclusions of native states -/

section Inclusions

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

/-- **An inclusion of native states**: injective, arity-preserving maps of the private family and
of the frame's names. -/
structure Inclusion (s u : NativeState S O Γ sort) where
  locals : s.Local → u.Local
  locals_injective : Function.Injective locals
  locals_preserves : ∀ name, u.locals (locals name) = s.locals name
  names : s.state.Names → u.state.Names
  names_injective : Function.Injective names
  names_preserves : ∀ name, u.state.declarations (names name) = s.state.declarations name

namespace Inclusion

variable {s u w : NativeState S O Γ sort}

/-- The identity inclusion. -/
def refl (s : NativeState S O Γ sort) : Inclusion s s :=
  ⟨id, Function.injective_id, fun _ => rfl, id, Function.injective_id, fun _ => rfl⟩

/-- Inclusions compose. -/
def comp (e : Inclusion s u) (e' : Inclusion u w) : Inclusion s w :=
  ⟨fun name => e'.locals (e.locals name), e'.locals_injective.comp e.locals_injective,
    fun name => (e'.locals_preserves (e.locals name)).trans (e.locals_preserves name),
    fun name => e'.names (e.names name), e'.names_injective.comp e.names_injective,
    fun name => (e'.names_preserves (e.names name)).trans (e.names_preserves name)⟩

/-- An opened rule local, carried. -/
def scopedName (e : Inclusion s u) (name : ScopedVar s.Local) : ScopedVar u.Local :=
  ⟨name.scope, e.locals name.name⟩

theorem scopedName_injective (e : Inclusion s u) : Function.Injective e.scopedName := by
  rintro ⟨scope, name⟩ ⟨scope', name'⟩ same
  simp only [scopedName, ScopedVar.mk.injEq] at same
  obtain ⟨rfl, named⟩ := same
  rw [e.locals_injective named]

/-- The frame's names, carried. -/
def frame (e : Inclusion s u) : Assignment s.state.declarations u.state.declarations :=
  reindex e.names e.names_preserves

theorem source_preserves (e : Inclusion s u) :
    ∀ name, ContextualActivatedStep.source u.locals u.state.declarations (Sum.map e.locals e.names name) =
      ContextualActivatedStep.source s.locals s.state.declarations name
  | .inl name => e.locals_preserves name
  | .inr name => e.names_preserves name

/-- The rule frame, carried. -/
def source (e : Inclusion s u) :
    Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
      (ContextualActivatedStep.source u.locals u.state.declarations) :=
  reindex (Sum.map e.locals e.names) e.source_preserves

theorem target_preserves (e : Inclusion s u) :
    ∀ name, ContextualActivatedStep.target u.locals u.state.declarations (Sum.map e.scopedName e.names name) =
      ContextualActivatedStep.target s.locals s.state.declarations name
  | .inl name => e.locals_preserves name.name
  | .inr name => e.names_preserves name

/-- The information frame, carried. -/
def target (e : Inclusion s u) :
    Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
      (ContextualActivatedStep.target u.locals u.state.declarations) :=
  reindex (Sum.map e.scopedName e.names) e.target_preserves

/-- The information frame's inclusion, as an extension. -/
abbrev targetExtension (e : Inclusion s u) : Extension (ContextualActivatedStep.target s.locals s.state.declarations) :=
  ⟨ScopedVar u.Local ⊕ u.state.Names, ContextualActivatedStep.target u.locals u.state.declarations,
    Sum.map e.scopedName e.names, e.scopedName_injective.sumMap e.names_injective, e.target_preserves⟩

theorem targetExtension_assignment (e : Inclusion s u) : e.targetExtension.assignment = e.target := rfl

theorem capturedTarget_eq (s : NativeState S O Γ sort) :
    ContextualSelectionViews.capturedTarget s.locals s.state.declarations =
      reindex (source := s.state.declarations) Sum.inr (fun _ => rfl) := rfl

theorem capturedSource_eq {Local Names : Type} (locals : Local → MetaArity S) (declarations : Names → MetaArity S) :
    ContextualSelectionViews.capturedSource locals declarations =
      reindex (source := declarations) Sum.inr (fun _ => rfl) := rfl

theorem freshening_eq {Local Names : Type} (locals : Local → MetaArity S) (declarations : Names → MetaArity S)
    (scope : ℕ) :
    ContextualFreshening.assignment locals declarations scope =
      reindex (Sum.map (ScopedVar.at scope) id) (fun name => by cases name <;> rfl) := by
  funext name
  cases name <;> rfl

theorem liftCaptures_reindex {Local Names Next : Type} (locals : Local → MetaArity S)
    {declarations : Names → MetaArity S} {next : Next → MetaArity S} (names : Names → Next)
    (preserves : ∀ name, next (names name) = declarations name) :
    ContextualStoredRows.liftCaptures locals (reindex names preserves) =
      reindex (Sum.map id names) (fun name => by
        cases name with
        | inl name => rfl
        | inr name => exact preserves name) := by
  funext name
  cases name with
  | inl name => rfl
  | inr name =>
      show instantiate (ContextualSelectionViews.capturedSource locals next) (reindex names preserves name) = _
      rw [instantiate_reindex]
      rfl

/-- **The capture square**: captured names carried as information or as knowledge agree. -/
theorem target_captured (e : Inclusion s u) :
    Assignment.compose e.target (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
      Assignment.compose (ContextualSelectionViews.capturedTarget u.locals u.state.declarations) e.frame := by
  funext name
  show instantiate e.target (generator (ContextualActivatedStep.target s.locals s.state.declarations) (.inr name)) =
    instantiate (ContextualSelectionViews.capturedTarget u.locals u.state.declarations)
      (reindex e.names e.names_preserves name)
  rw [instantiate_generator, instantiate_reindex]
  rfl

/-- **The freshening square**: opening at a scope and then carrying is carrying and then opening. -/
theorem target_freshening (e : Inclusion s u) (scope : ℕ) :
    Assignment.compose e.target (ContextualFreshening.assignment s.locals s.state.declarations scope) =
      Assignment.compose (ContextualFreshening.assignment u.locals u.state.declarations scope) e.source := by
  funext name
  cases name with
  | inl name =>
      show instantiate e.target
          (generator (ContextualActivatedStep.target s.locals s.state.declarations) (.inl (ScopedVar.at scope name))) =
        instantiate (ContextualFreshening.assignment u.locals u.state.declarations scope)
          (reindex (Sum.map e.locals e.names) e.source_preserves (.inl name))
      rw [instantiate_generator, instantiate_reindex]
      rfl
  | inr name =>
      show instantiate e.target (generator (ContextualActivatedStep.target s.locals s.state.declarations) (.inr name)) =
        instantiate (ContextualFreshening.assignment u.locals u.state.declarations scope)
          (reindex (Sum.map e.locals e.names) e.source_preserves (.inr name))
      rw [instantiate_generator, instantiate_reindex]
      rfl

/-- The rule frame's carrying moves captures, then private names. -/
theorem source_eq (e : Inclusion s u) :
    e.source = Assignment.compose
      (ContextualConditionalPublication.privateReindex s.locals u.locals u.state.declarations e.locals
        e.locals_preserves)
      (ContextualStoredRows.liftCaptures s.locals e.frame) := by
  funext name
  cases name with
  | inl name =>
      show reindex (Sum.map e.locals e.names) e.source_preserves (.inl name) =
        instantiate (ContextualConditionalPublication.privateReindex s.locals u.locals u.state.declarations e.locals
          e.locals_preserves) (generator (ContextualActivatedStep.source s.locals u.state.declarations) (.inl name))
      rw [instantiate_generator]
      rfl
  | inr name =>
      show reindex (Sum.map e.locals e.names) e.source_preserves (.inr name) =
        instantiate (ContextualConditionalPublication.privateReindex s.locals u.locals u.state.declarations e.locals
          e.locals_preserves)
          (instantiate (ContextualSelectionViews.capturedSource s.locals u.state.declarations)
            (reindex e.names e.names_preserves name))
      rw [instantiate_reindex, instantiate_castMetaBody]
      erw [instantiate_generator]
      rfl

theorem frame_comp (e : Inclusion s u) (e' : Inclusion u w) :
    Assignment.compose e'.frame e.frame = (e.comp e').frame := by
  rw [frame, frame, reindex_compose]
  rfl

theorem frame_refl (s : NativeState S O Γ sort) : (refl s).frame = generator s.state.declarations := rfl

/-- **A row, carried**: its captures move along the frame, then its private names. -/
def row (e : Inclusion s u) (r : ContextualConditionalRows.Row s.locals s.state.declarations Γ sort) :
    ContextualConditionalRows.Row u.locals u.state.declarations Γ sort :=
  ContextualConditionalPublication.reindexPrivate s.locals u.locals u.state.declarations e.locals e.locals_preserves
    (r.map s.locals s.state.declarations e.frame)

theorem row_template (e : Inclusion s u) (r : ContextualConditionalRows.Row s.locals s.state.declarations Γ sort) :
    ContextualStoredRows.asTemplate u.locals u.state.declarations (e.row r).value =
      instantiate e.source (ContextualStoredRows.asTemplate s.locals s.state.declarations r.value) := by
  rw [row, ContextualConditionalPublication.reindexed_template]
  show instantiate _ (ContextualStoredRows.asTemplate s.locals u.state.declarations (r.value.map s.locals e.frame)) = _
  rw [ContextualStoredRows.asTemplate_map, ← Assignment.instantiate_compose, ← source_eq]

theorem row_obligations (e : Inclusion s u) (r : ContextualConditionalRows.Row s.locals s.state.declarations Γ sort) :
    (e.row r).obligations = ContextualResidual.mapProblem e.source r.obligations := by
  show ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ r.obligations) = _
  rw [ContextualConditionalNaturality.map_problem_compose, ← source_eq]

theorem row_obligationsAt (e : Inclusion s u) (scope : ℕ)
    (r : ContextualConditionalRows.Row s.locals s.state.declarations Γ sort) :
    (e.row r).obligationsAt u.locals u.state.declarations scope =
      ContextualResidual.mapProblem e.target (r.obligationsAt s.locals s.state.declarations scope) := by
  unfold ContextualConditionalRows.Row.obligationsAt
  rw [row_obligations, ContextualConditionalNaturality.map_problem_compose,
    ContextualConditionalNaturality.map_problem_compose, target_freshening]

/-- **Carrying rows composes.** -/
theorem row_comp (e : Inclusion s u) (e' : Inclusion u w)
    (r : ContextualConditionalRows.Row s.locals s.state.declarations Γ sort) :
    e'.row (e.row r) = (e.comp e').row r := by
  unfold row
  rw [ContextualConditionalPublication.reindexPrivate_map, ContextualConditionalNaturality.row_map_compose,
    reindexPrivate_comp, frame_comp]
  rfl

theorem row_refl (r : ContextualConditionalRows.Row s.locals s.state.declarations Γ sort) :
    (refl s).row r = r := by
  have privateId : ContextualConditionalPublication.privateReindex s.locals s.locals s.state.declarations
      (refl s).locals (refl s).locals_preserves = generator (ContextualActivatedStep.source s.locals s.state.declarations) := by
    funext name
    cases name <;> rfl
  unfold row
  rw [frame_refl, ContextualConditionalNaturality.row_map_identity]
  rcases r with ⟨value, obligations⟩
  apply congrArg₂ ContextualConditionalRows.Row.mk
  · cases value with
    | schema body =>
        change ContextualStoredRows.Row.schema (instantiate _ body) = .schema body
        rw [privateId, instantiate_identity]
    | shared value => rfl
  · change ContextualResidual.mapProblem _ obligations = obligations
    rw [privateId]
    simp only [ContextualResidual.mapProblem, instantiateObservation_identity, List.map_id']

/-- **A captured guard row, carried**: the state's row carried, read at the information frame, is the
row read at the information frame and then carried. -/
theorem row_guard (e : Inclusion s u) (r : ContextualConditionalRows.Row s.locals s.state.declarations Γ sort) :
    (e.row r).map u.locals u.state.declarations
        (ContextualSelectionViews.capturedTarget u.locals u.state.declarations) =
      ContextualConditionalPublication.reindexPrivate s.locals u.locals
        (ContextualActivatedStep.target u.locals u.state.declarations) e.locals e.locals_preserves
        ((r.map s.locals s.state.declarations
          (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)).map s.locals _ e.target) := by
  unfold row
  rw [ContextualConditionalPublication.reindexPrivate_map, ContextualConditionalNaturality.row_map_compose,
    ContextualConditionalNaturality.row_map_compose, target_captured]

/-- **A live firing, carried**: its rule, outputs and query patterns. -/
def firing (e : Inclusion s u) (f : LiveFiring s) : LiveFiring u where
  rule := f.rule.map (instantiate e.source)
  selection := f.selection
  outputs o := instantiate e.target (f.outputs o)
  patterns := f.patterns.map fun pattern => (instantiate e.target pattern.1, pattern.2)
  fuel := f.fuel

end Inclusion

/-- **A dead-name extension**: an inclusion along which every row is the carried row, the knowledge
is the carried knowledge up to the order of its equations, and the present occurrences and the scope
ledger are the same. Every name it misses is dead: nothing mentions it. -/
structure DeadExtension (s u : NativeState S O Γ sort) extends Inclusion s u where
  rows : ∀ o, u.state.rows o = toInclusion.row (s.state.rows o)
  equations : u.state.equations.Perm (ContextualResidual.mapProblem toInclusion.frame s.state.equations)
  present : u.state.present = s.state.present
  occupied : u.state.occupied = s.state.occupied

namespace DeadExtension

variable {s u w : NativeState S O Γ sort}

/-- Every state is a dead-name extension of itself. -/
def refl (s : NativeState S O Γ sort) : DeadExtension s s where
  toInclusion := Inclusion.refl s
  rows o := (Inclusion.row_refl (s.state.rows o)).symm
  equations := by
    rw [Inclusion.frame_refl]
    simp only [ContextualResidual.mapProblem, instantiateObservation_identity, List.map_id']
    exact List.Perm.refl _
  present := rfl
  occupied := rfl

/-- **Dead-name extensions compose.** -/
def comp (e : DeadExtension s u) (e' : DeadExtension u w) : DeadExtension s w where
  toInclusion := e.toInclusion.comp e'.toInclusion
  rows o := (e'.rows o).trans ((congrArg e'.toInclusion.row (e.rows o)).trans (Inclusion.row_comp _ _ _))
  equations := by
    refine e'.equations.trans ((e.equations.map _).trans (List.Perm.of_eq ?_))
    show ContextualResidual.mapProblem e'.frame (ContextualResidual.mapProblem e.frame s.state.equations) = _
    rw [ContextualConditionalNaturality.map_problem_compose, Inclusion.frame_comp]
  present := e'.present.trans e.present
  occupied := e'.occupied.trans e.occupied

end DeadExtension

end Inclusions

/-! ## Preparation, information and guards, carried -/

section Carried

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

/-- Models read their problem as a set. -/
theorem models_perm {V W : Type} {declaration : V → MetaArity S} {next : W → MetaArity S}
    (σ : Assignment declaration next) {first second : ContextualResidual.Problem declaration}
    (same : first.Perm second) : ContextualResidual.Models σ first ↔ ContextualResidual.Models σ second :=
  ⟨fun solved equation member => solved equation (same.mem_iff.mpr member),
    fun solved equation member => solved equation (same.mem_iff.mp member)⟩

namespace Inclusion

variable {s u : NativeState S O Γ sort} (e : Inclusion s u)

theorem termAt_carried (scope : ℕ) {Δ : Ctx S} {kind : S.Srt}
    (term : Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Δ kind) :
    instantiate e.target (ContextualFreshening.termAt s.locals s.state.declarations scope term) =
      ContextualFreshening.termAt u.locals u.state.declarations scope (instantiate e.source term) := by
  unfold ContextualFreshening.termAt
  rw [← Assignment.instantiate_compose, target_freshening, Assignment.instantiate_compose]

variable (occupied : Finset ℕ) (selection : Selection O)
  (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort))

/-- **The rule views are carried**, whatever rows the two preparations read. -/
theorem prepared_rule_carried (rows : O → ContextualStoredRows.Row s.locals s.state.declarations Γ sort)
    (later : O → ContextualStoredRows.Row u.locals u.state.declarations Γ sort) :
    (ContextualActivatedStep.prepared s.locals s.state.declarations occupied selection rule rows).rule.map
        (instantiate e.target) =
      (ContextualActivatedStep.prepared u.locals u.state.declarations occupied selection
        (rule.map (instantiate e.source)) later).rule := by
  change (rule.map (ContextualFreshening.termAt s.locals s.state.declarations
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)))).map _ =
    (rule.map (instantiate e.source)).map (ContextualFreshening.termAt _ _
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)))
  rw [OccurrenceRelabeling.rule_map_comp, OccurrenceRelabeling.rule_map_comp]
  apply congrArg (fun mapping => rule.map mapping)
  funext term
  exact e.termAt_carried _ term

variable (rows : O → ContextualConditionalRows.Row s.locals s.state.declarations Γ sort)
  (later : O → ContextualConditionalRows.Row u.locals u.state.declarations Γ sort)
  (carried : ∀ o, later o = e.row (rows o))

include carried in
theorem prepared_take_carried (port : Fin selection.taken.length) :
    instantiate e.target
        ((ContextualActivatedStep.prepared s.locals s.state.declarations occupied selection rule
          (fun o => (rows o).value)).taken port) =
      (ContextualActivatedStep.prepared u.locals u.state.declarations occupied selection
        (rule.map (instantiate e.source)) (fun o => (later o).value)).taken port := by
  change instantiate e.target (ContextualFreshening.termAt s.locals s.state.declarations
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port))
      (ContextualStoredRows.asTemplate s.locals s.state.declarations (rows (selection.taken.get port)).value)) =
    ContextualFreshening.termAt _ _
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port))
      (ContextualStoredRows.asTemplate _ _ (later (selection.taken.get port)).value)
  rw [e.termAt_carried, carried, e.row_template]

include carried in
theorem prepared_read_carried (port : Fin selection.read.length) :
    instantiate e.target
        ((ContextualActivatedStep.prepared s.locals s.state.declarations occupied selection rule
          (fun o => (rows o).value)).read port) =
      (ContextualActivatedStep.prepared u.locals u.state.declarations occupied selection
        (rule.map (instantiate e.source)) (fun o => (later o).value)).read port := by
  change instantiate e.target (ContextualFreshening.termAt s.locals s.state.declarations
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port))
      (ContextualStoredRows.asTemplate s.locals s.state.declarations (rows (selection.read.get port)).value)) =
    ContextualFreshening.termAt _ _
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port))
      (ContextualStoredRows.asTemplate _ _ (later (selection.read.get port)).value)
  rw [e.termAt_carried, carried, e.row_template]

include carried in
/-- **The equations a selection adds are carried.** -/
theorem addedEquations_carried :
    ContextualFrameUnifier.mapProblem e.target
        (ContextualActivatedStep.addedEquations s.locals s.state.declarations occupied selection rule
          (fun o => (rows o).value)) =
      ContextualActivatedStep.addedEquations u.locals u.state.declarations occupied selection
        (rule.map (instantiate e.source)) (fun o => (later o).value) := by
  have mapped := e.prepared_rule_carried occupied selection rule (fun o => (rows o).value) (fun o => (later o).value)
  have takes : List.map (instantiate e.target)
      (ContextualActivatedStep.prepared s.locals s.state.declarations occupied selection rule
        (fun o => (rows o).value)).rule.take =
      (ContextualActivatedStep.prepared u.locals u.state.declarations occupied selection
        (rule.map (instantiate e.source)) (fun o => (later o).value)).rule.take := congrArg RuleInstance.take mapped
  have reads : List.map (instantiate e.target)
      (ContextualActivatedStep.prepared s.locals s.state.declarations occupied selection rule
        (fun o => (rows o).value)).rule.read =
      (ContextualActivatedStep.prepared u.locals u.state.declarations occupied selection
        (rule.map (instantiate e.source)) (fun o => (later o).value)).rule.read := congrArg RuleInstance.read mapped
  have tells : ContextualFrameUnifier.mapProblem e.target
      (ContextualActivatedStep.prepared s.locals s.state.declarations occupied selection rule
        (fun o => (rows o).value)).rule.tell =
      (ContextualActivatedStep.prepared u.locals u.state.declarations occupied selection
        (rule.map (instantiate e.source)) (fun o => (later o).value)).rule.tell := congrArg RuleInstance.tell mapped
  have takenViews :
      (List.ofFn (ContextualActivatedStep.prepared s.locals s.state.declarations occupied selection rule
          (fun o => (rows o).value)).taken).map (instantiate e.target) =
        List.ofFn (ContextualActivatedStep.prepared u.locals u.state.declarations occupied selection
          (rule.map (instantiate e.source)) (fun o => (later o).value)).taken := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext (e.prepared_take_carried occupied selection rule rows later carried))
  have readViews :
      (List.ofFn (ContextualActivatedStep.prepared s.locals s.state.declarations occupied selection rule
          (fun o => (rows o).value)).read).map (instantiate e.target) =
        List.ofFn (ContextualActivatedStep.prepared u.locals u.state.declarations occupied selection
          (rule.map (instantiate e.source)) (fun o => (later o).value)).read := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext (e.prepared_read_carried occupied selection rule rows later carried))
  simp only [ContextualActivatedStep.addedEquations, ContextualTransportedActivation.map_append,
    ContextualTransportedActivation.map_useEquations, takes, reads, tells, takenViews, readViews]

include carried in
/-- **The latent equations of the selected rows are carried.** -/
theorem latent_carried :
    ContextualResidual.mapProblem e.target
        (ContextualConditionalExecution.latent s.locals s.state.declarations occupied selection rows) =
      ContextualConditionalExecution.latent u.locals u.state.declarations occupied selection later := by
  have append (first second : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)) :
      ContextualResidual.mapProblem e.target (first ++ second) =
        ContextualResidual.mapProblem e.target first ++ ContextualResidual.mapProblem e.target second :=
    List.map_append ..
  have flatten (parts : List (ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations))) :
      ContextualResidual.mapProblem e.target parts.flatten =
        (parts.map (ContextualResidual.mapProblem e.target)).flatten :=
    List.map_flatten ..
  have takes : (fun port : Fin selection.taken.length => ContextualResidual.mapProblem e.target
      ((rows (selection.taken.get port)).obligationsAt s.locals s.state.declarations
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port)))) =
      fun port => (later (selection.taken.get port)).obligationsAt _ _
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port)) :=
    funext fun port => by rw [carried, e.row_obligationsAt]
  have reads : (fun port : Fin selection.read.length => ContextualResidual.mapProblem e.target
      ((rows (selection.read.get port)).obligationsAt s.locals s.state.declarations
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port)))) =
      fun port => (later (selection.read.get port)).obligationsAt _ _
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port)) :=
    funext fun port => by rw [carried, e.row_obligationsAt]
  unfold ContextualConditionalExecution.latent
  rw [append, flatten, flatten, List.map_ofFn, List.map_ofFn]
  exact congrArg₂ (fun first second => (List.ofFn first).flatten ++ (List.ofFn second).flatten) takes reads

include carried in
/-- **The information is carried**, up to the order of the knowledge's equations. -/
theorem information_carried (before : ContextualResidual.Problem s.state.declarations)
    (after : ContextualResidual.Problem u.state.declarations)
    (equations : after.Perm (ContextualResidual.mapProblem e.frame before)) :
    (ContextualConditionalExecution.information u.locals u.state.declarations occupied selection
        (rule.map (instantiate e.source)) later after).Perm
      (ContextualResidual.mapProblem e.target
        (ContextualConditionalExecution.information s.locals s.state.declarations occupied selection rule rows
          before)) := by
  have knowledge : (ContextualResidual.mapProblem
      (ContextualSelectionViews.capturedTarget u.locals u.state.declarations) after).Perm
      (ContextualResidual.mapProblem e.target (ContextualResidual.mapProblem
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) before)) := by
    rw [ContextualConditionalNaturality.map_problem_compose, target_captured,
      ← ContextualConditionalNaturality.map_problem_compose]
    exact equations.map _
  unfold ContextualConditionalExecution.information
  rw [NativeResidual.mapProblem_append, NativeResidual.mapProblem_append,
    ← ContextualResidual.observeProblem_mapProblem, e.addedEquations_carried occupied selection rule rows later carried,
    e.latent_carried occupied selection rows later carried]
  exact (knowledge.append_right _).append_right _

include carried in
/-- **The guard rows are carried**: read at the information frame, carried, with the private names
moved. -/
theorem guardRows_carried :
    ContextualConditionalExecution.guardRows u.locals u.state.declarations later =
      fun o => ContextualConditionalPublication.reindexPrivate s.locals u.locals
        (ContextualActivatedStep.target u.locals u.state.declarations) e.locals e.locals_preserves
        ((ContextualConditionalExecution.guardRows s.locals s.state.declarations rows o).map s.locals _ e.target) := by
  funext o
  show (later o).map _ _ _ = _
  rw [carried, e.row_guard]
  rfl

include carried in
/-- **A carried guard holds exactly when the guard holds at the restriction.** -/
theorem holds_carried_iff (world : Finset O) {W : Type} {next : W → MetaArity S}
    (ρ : Assignment (ContextualActivatedStep.target u.locals u.state.declarations) next)
    (check : Check (Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)) :
    ContextualConditionalGuards.Holds u.locals ρ
        (ContextualConditionalExecution.guardRows u.locals u.state.declarations later) world
        (check.map (instantiate e.target)) ↔
      ContextualConditionalGuards.Holds s.locals (Assignment.compose ρ e.target)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations rows) world check := by
  rw [e.guardRows_carried rows later carried,
    holds_reindexPrivate_iff s.locals u.locals _ e.locals e.locals_injective e.locals_preserves]
  exact ContextualConditionalGuards.holds_transport s.locals e.target ρ _ world check

include carried in
/-- **The region of a carried pattern is the region of the pattern at the restriction.** -/
theorem region_carried (world : Finset O) {W : Type} {next : W → MetaArity S}
    (ρ : Assignment (ContextualActivatedStep.target u.locals u.state.declarations) next)
    (pattern : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort) :
    ContextualConditionalGuards.region u.locals ρ
        (ContextualConditionalExecution.guardRows u.locals u.state.declarations later) world
        (instantiate e.target pattern) =
      ContextualConditionalGuards.region s.locals (Assignment.compose ρ e.target)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations rows) world pattern := by
  rw [e.guardRows_carried rows later carried,
    region_reindexPrivate s.locals u.locals _ e.locals e.locals_injective e.locals_preserves]
  exact ContextualConditionalGuards.region_transport s.locals e.target ρ _ world pattern

end Inclusion

end Carried

/-! ## Admission along a dead-name extension -/

section Admission

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **Guards and queries are blind to fresh names in the solution frame.** -/
theorem holds_inclusion_iff {s : NativeState S O Γ sort} {Extra : Type} (unused : Extra → MetaArity S)
    (f : LiveFiring s) (b : Frames.Frame S)
    (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity) :
    native.Holds f.toNative ⟨Extra ⊕ b.Names, extended unused b.arity⟩
        (Assignment.compose (inclusion unused b.arity) σ) ↔ native.Holds f.toNative b σ := by
  show ((∀ check ∈ f.toNative.prepared.rule.checks, ContextualConditionalGuards.Holds s.locals
        (Assignment.compose (inclusion unused b.arity) σ)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present check) ∧
      ∀ query ∈ f.toNative.queries,
        (query.atSolution ⟨Extra ⊕ b.Names, extended unused b.arity, Assignment.compose (inclusion unused b.arity) σ⟩).Holds
          (nativeLabels s.locals s.state) s.state.present) ↔
    ((∀ check ∈ f.toNative.prepared.rule.checks, ContextualConditionalGuards.Holds s.locals σ
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present check) ∧
      ∀ query ∈ f.toNative.queries,
        (query.atSolution ⟨b.Names, b.arity, σ⟩).Holds (nativeLabels s.locals s.state) s.state.present)
  refine and_congr (forall₂_congr fun check _ =>
    ContextualConditionalNaturality.holds_inclusion_iff s.locals unused σ _ _ check) ?_
  show (∀ query ∈ f.patterns.map (fun pattern => matchingQuery s.locals pattern.1 pattern.2), _) ↔
    ∀ query ∈ f.patterns.map (fun pattern => matchingQuery s.locals pattern.1 pattern.2), _
  rw [List.forall_mem_map, List.forall_mem_map]
  refine forall₂_congr fun pattern _ => ?_
  refine (ContextualPredicateQueryAdmission.matching_holds_iff s.locals pattern.1 pattern.2
    (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
    ⟨Extra ⊕ b.Names, extended unused b.arity, Assignment.compose (inclusion unused b.arity) σ⟩).trans
    (Iff.trans ?_ (ContextualPredicateQueryAdmission.matching_holds_iff s.locals pattern.1 pattern.2
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
      ⟨b.Names, b.arity, σ⟩).symm)
  show ContextualConditionalGuards.region s.locals (Assignment.compose (inclusion unused b.arity) σ) _ _ _ = _ ↔
    ContextualConditionalGuards.region s.locals σ _ _ _ = _
  rw [ContextualConditionalNaturality.region_inclusion]

namespace DeadExtension

variable {s u : NativeState S O Γ sort} (e : DeadExtension s u)

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **The information of a carried firing is the carried information**, up to order. -/
theorem information_firing (f : LiveFiring s) :
    (e.firing f).toNative.information.Perm (ContextualResidual.mapProblem e.target f.toNative.information) := by
  show (ContextualConditionalExecution.information u.locals u.state.declarations u.state.occupied f.selection
      (f.rule.map (instantiate e.source)) u.state.rows u.state.equations).Perm _
  rw [e.occupied]
  exact e.information_carried s.state.occupied f.selection f.rule s.state.rows u.state.rows e.rows
    s.state.equations u.state.equations e.equations

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **The rule views of a carried firing are the carried views.** -/
theorem prepared_firing (f : LiveFiring s) :
    (e.firing f).toNative.prepared.rule = f.toNative.prepared.rule.map (instantiate e.target) := by
  show (ContextualActivatedStep.prepared u.locals u.state.declarations u.state.occupied f.selection
      (f.rule.map (instantiate e.source)) (fun o => (u.state.rows o).value)).rule = _
  rw [e.occupied]
  exact (e.prepared_rule_carried s.state.occupied f.selection f.rule _ _).symm

/-- **A carried firing's guards and queries hold at a solution exactly when the firing's hold at its
restriction.** -/
theorem holds_firing_iff (f : LiveFiring s) (b : Frames.Frame S)
    (ρ : Assignment (ContextualActivatedStep.target u.locals u.state.declarations) b.arity) :
    native.Holds (e.firing f).toNative b ρ ↔ native.Holds f.toNative b (Assignment.compose ρ e.target) := by
  show ((∀ check ∈ (e.firing f).toNative.prepared.rule.checks, ContextualConditionalGuards.Holds u.locals ρ
        (ContextualConditionalExecution.guardRows u.locals u.state.declarations u.state.rows) u.state.present check) ∧
      ∀ query ∈ (e.firing f).toNative.queries,
        (query.atSolution ⟨b.Names, b.arity, ρ⟩).Holds (nativeLabels u.locals u.state) u.state.present) ↔
    ((∀ check ∈ f.toNative.prepared.rule.checks, ContextualConditionalGuards.Holds s.locals
        (Assignment.compose ρ e.target)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present check) ∧
      ∀ query ∈ f.toNative.queries,
        (query.atSolution ⟨b.Names, b.arity, Assignment.compose ρ e.target⟩).Holds
          (nativeLabels s.locals s.state) s.state.present)
  rw [e.prepared_firing, e.present]
  refine and_congr ?_ ?_
  · show (∀ check ∈ List.map (Check.map (instantiate e.target)) f.toNative.prepared.rule.checks, _) ↔ _
    rw [List.forall_mem_map]
    exact forall₂_congr fun check _ => e.holds_carried_iff s.state.rows u.state.rows e.rows s.state.present ρ check
  · show (∀ query ∈ (f.patterns.map fun pattern => (instantiate e.target pattern.1, pattern.2)).map
        (fun pattern => matchingQuery u.locals pattern.1 pattern.2), _) ↔
      ∀ query ∈ f.patterns.map (fun pattern => matchingQuery s.locals pattern.1 pattern.2), _
    rw [List.forall_mem_map, List.forall_mem_map, List.forall_mem_map]
    refine forall₂_congr fun pattern _ => ?_
    refine (ContextualPredicateQueryAdmission.matching_holds_iff u.locals (instantiate e.target pattern.1) pattern.2
      (ContextualConditionalExecution.guardRows u.locals u.state.declarations u.state.rows) s.state.present
      ⟨b.Names, b.arity, ρ⟩).trans
      (Iff.trans ?_ (ContextualPredicateQueryAdmission.matching_holds_iff s.locals pattern.1 pattern.2
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
        ⟨b.Names, b.arity, Assignment.compose ρ e.target⟩).symm)
    show ContextualConditionalGuards.region u.locals ρ _ _ (instantiate e.target pattern.1) = _ ↔ _
    rw [e.region_carried s.state.rows u.state.rows e.rows s.state.present ρ pattern.1]

/-- **Admission is invariant along a dead-name extension**: a live firing is admitted exactly when
its carrying is. Every solution of the smaller state's information lifts, with fresh generators for
the dead names, to a solution of the carried information, and guards and queries are blind to the
fresh generators. -/
theorem admits_iff (f : LiveFiring s) : f.toNative.Realized ↔ (e.firing f).toNative.Realized := by
  rw [native_admits_iff, native_admits_iff]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · show (f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧ f.rule.take.length = f.selection.taken.length ∧
        f.rule.read.length = f.selection.read.length ∧
        f.selection.made.map f.outputs = f.toNative.prepared.rule.produce) ↔
      (f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
        (f.rule.map (instantiate e.source)).take.length = f.selection.taken.length ∧
        (f.rule.map (instantiate e.source)).read.length = f.selection.read.length ∧
        f.selection.made.map (fun o => instantiate e.target (f.outputs o)) =
          (e.firing f).toNative.prepared.rule.produce)
    rw [e.prepared_firing]
    have outputs : f.selection.made.map (fun o => instantiate e.target (f.outputs o)) =
        (f.selection.made.map f.outputs).map (instantiate e.target) := (List.map_map ..).symm
    rw [outputs]
    show _ ↔ (_ ∧ _ ∧ (f.rule.take.map _).length = _ ∧ (f.rule.read.map _).length = _ ∧
      _ = f.toNative.prepared.rule.produce.map _)
    rw [List.length_map, List.length_map]
    exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (List.map_injective_iff.mpr e.targetExtension.instantiate_injective).eq_iff.symm)))
  · show Enabled _ s.state.present _ ↔ Enabled _ u.state.present _
    rw [e.present]
    exact Iff.rfl
  · refine (Frames.contextual_solvable_iff (V := ScopedVar s.Local ⊕ s.state.Names) _).trans
      (Iff.trans ?_ (Frames.contextual_solvable_iff (V := ScopedVar u.Local ⊕ u.state.Names) _).symm)
    refine (ContextualConditionalNaturality.solvable_extension_iff e.targetExtension f.toNative.information).symm.trans ?_
    exact exists_congr fun Future => exists_congr fun future => exists_congr fun candidate =>
      (models_perm candidate (e.information_firing f)).symm
  · constructor
    · intro asked b ρ solved
      have restricted : ContextualResidual.Models (Assignment.compose ρ e.target) f.toNative.information :=
        (ContextualResidual.models_mapProblem _ _ _).mp ((models_perm ρ (e.information_firing f)).mp solved)
      exact (e.holds_firing_iff f b ρ).mpr (asked b _ restricted)
    · intro asked b σ solved
      have lifted : ContextualResidual.Models (e.targetExtension.liftModel σ) (e.firing f).toNative.information :=
        (models_perm _ (e.information_firing f)).mpr
          ((ContextualConditionalNaturality.models_liftModel_iff e.targetExtension σ _).mpr solved)
      have held := (e.holds_firing_iff f ⟨_, _⟩ _).mp
        (asked ⟨e.targetExtension.Complement ⊕ b.Names, extended e.targetExtension.complementDeclarations b.arity⟩
          (e.targetExtension.liftModel σ) lifted)
      have square : Assignment.compose (e.targetExtension.liftModel σ) e.target =
          Assignment.compose (inclusion e.targetExtension.complementDeclarations b.arity) σ :=
        e.targetExtension.liftModel_square σ
      have key := congrArg (native.Holds f.toNative
        ⟨e.targetExtension.Complement ⊕ b.Names, extended e.targetExtension.complementDeclarations b.arity⟩) square
      exact (holds_inclusion_iff e.targetExtension.complementDeclarations f b σ).mp (Eq.mp key held)

end DeadExtension

end Admission

end NativeDead

#print axioms NativeDead.matches_reindexPrivate_iff
#print axioms NativeDead.holds_reindexPrivate_iff
#print axioms NativeDead.reindexPrivate_comp
#print axioms NativeDead.extendPrivate_eq_reindexPrivate
#print axioms NativeDead.Inclusion.target_captured
#print axioms NativeDead.Inclusion.target_freshening
#print axioms NativeDead.Inclusion.source_eq
#print axioms NativeDead.Inclusion.row_comp
#print axioms NativeDead.Inclusion.row_refl
#print axioms NativeDead.DeadExtension.comp
#print axioms NativeDead.Inclusion.prepared_rule_carried
#print axioms NativeDead.Inclusion.addedEquations_carried
#print axioms NativeDead.Inclusion.latent_carried
#print axioms NativeDead.Inclusion.information_carried
#print axioms NativeDead.Inclusion.holds_carried_iff
#print axioms NativeDead.Inclusion.region_carried
#print axioms NativeDead.holds_inclusion_iff
#print axioms NativeDead.DeadExtension.holds_firing_iff
#print axioms NativeDead.DeadExtension.admits_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
