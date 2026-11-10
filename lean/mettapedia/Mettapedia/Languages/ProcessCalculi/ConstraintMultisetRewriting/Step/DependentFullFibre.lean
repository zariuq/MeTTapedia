import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreConservativity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# The fibre join: the conflict-bearing second-order step inside the dependent full step

**Admission through any map of frame instances** (`frameMap_admission_transfer`). R53's argument for
`Translation.admission_transfer` holds for every map of frame instances that reflects the
equivalence: at a firing whose guards and predicate queries are equation guards, and whose
information has a principal answer that the map keeps principal on its image, admission is the
target's admission condition on the translated data.

**Through the η-long fibre** (`fibre_admission_transfer`). For the map `fibre` of the second-order
frames into the dependent unifier's typed βη frames, under a closed realization, the factorization
hypothesis is discharged: when the dependent unifier decides the translated information, by a
principal answer landing in a translated frame or by a refutation, admission is preserved and
reflected. Fullness and principal reflection (`fibre_answer_in_fibre`) turn the unifier's answer
into a second-order principal answer whose translation is principal.

**The chosen instance** (`translateState`, `translateFiring`). The first-order step
`AnnotatedRuns.firstOrder` of the second-order action at a list frame `M` (terms are
observations at `M`, solutions are its endomorphic assignments) has takes, reads, tells, equation
guards and absence and counting queries. Its states and firings map into the dependent full step
at the translated telescope, with no helpers:

* the information of a translated firing is the translation of its problem (`translate_information`);
* **admission is preserved and reflected** (`admits_translate_iff`) at every firing without census
  queries and counting checks, whenever the dependent unifier decides the translated information and
  each translated absence extension by an endomorphic principal answer or a refutation; the only
  condition left on the first-order side is that the produced labels are the made occurrences'
  labels, a shape the first-order step's fixed labelling imposes;
* **results correspond** (`result_translate`): the dependent result of a translated firing is the
  translated first-order result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentFibre Translation
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

/-! ## Admission through a map of frame instances -/

section Generic

universe uO uT uH uO' uT' uH' uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {Obj' : Type uO'} {Tm' : Obj' → Type uT'} {Hom' : Obj' → Obj' → Type uH'}
  {X : Frames Tm Hom} {Y : Frames Tm' Hom'}

/-- **Admission is preserved and reflected by a map of frame instances** that reflects the
equivalence, at a firing whose information has a principal answer kept principal on the image. -/
theorem frameMap_admission_transfer (Φ : FrameMap X Y) (reflects : Φ.Reflects)
    {O : Type} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
    (P : Step X O State Firing) [P.Guarded] (guards : ∀ {s : State} (f : Firing s), EquationStore (Tm (P.target f)))
    (holds : ∀ {s : State} (f : Firing s) (b : Obj) (g : Hom (P.target f) b),
      P.Holds f b g ↔ X.Models g (guards f))
    {s : State} (f : Firing s) {m : Obj} {answer : Hom (P.target f) m}
    (principal : X.Principal (P.information f) answer)
    (factors : Φ.FactorsOnImage (P.information f) (Φ.hom answer)) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      Y.Solvable (Φ.store (P.information f)) ∧
      Y.Entails (Φ.store (P.information f)) (fun _ g => Y.Models g (Φ.store (guards f))) := by
  have asks : X.Entails (P.information f) (P.Holds f) ↔
      X.Entails (P.information f) (fun _ g => X.Models g (guards f)) :=
    ⟨fun asked b g solved => (holds f b g).mp (asked b g solved),
      fun asked b g solved => (holds f b g).mpr (asked b g solved)⟩
  rw [P.admits_iff f, asks, ← Φ.entails_iff_of_factorsOnImage reflects principal factors]
  have solvable : X.Solvable (P.information f) ↔ Y.Solvable (Φ.store (P.information f)) :=
    ⟨Φ.solvable, fun _ => principal.solvable⟩
  rw [solvable]

end Generic

/-! ## Through the η-long fibre -/

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
  (rigid : ∀ name, S.roles name = .rigid) (church : ConversionCoherence.ChurchRosser S.R)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)
  (sortInjective : Function.Injective names.sort)
  (closed : ClosedRealization (S := S) names)
  (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))

/-- **The dependent unifier decides a translated store** at a list frame `M`, with answers in the
fibre over `N`-frames: a principal answer landing in a translated frame, or a refutation. -/
def DecidedInFibre {M : List (Binding.MetaArity sig)}
    (K : EquationStore (Binding.ContextualFamily.Observation sig M.get)) : Prop :=
  (∃ (N : List (Binding.MetaArity sig))
      (τ : (fibre facts roots heads church names realization).obj N ⟶
        (fibre facts roots heads church names realization).obj M),
      (frames S.levels).Principal ((fibre facts roots heads church names realization).store K) τ) ∨
    ¬ (frames S.levels).Solvable ((fibre facts roots heads church names realization).store K)

include algebra complete rigid sortInjective closed operatorInjective in
/-- **Admission through the η-long fibre.** For every candidate step over the second-order frames
whose guards and predicate queries are equation guards, at a firing whose translated information the
dependent unifier decides in the fibre, admission is the dependent admission condition on the
translated data. -/
theorem fibre_admission_transfer {O : Type} [DecidableEq O] {State : Type} {Firing : State → Type}
    (P : Step (listFrames sig) O State Firing) [P.Guarded]
    (guards : ∀ {s : State} (f : Firing s),
      EquationStore (Binding.ContextualFamily.Observation sig (P.target f).get))
    (holds : ∀ {s : State} (f : Firing s) (N : List (Binding.MetaArity sig))
      (g : Binding.ContextualFamily.Assignment (S := sig) (P.target f).get N.get),
      P.Holds f N g ↔ (listFrames sig).Models g (guards f))
    {s : State} (f : Firing s)
    (decided : DecidedInFibre facts roots heads church names realization (P.information f)) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
        (P.information f)) ∧
      (frames S.levels).Entails ((fibre facts roots heads church names realization).store
          (P.information f))
        (fun _ g => (frames S.levels).Models g
          ((fibre facts roots heads church names realization).store (guards f))) := by
  rcases decided with ⟨N, τ, principal⟩ | refuted
  · obtain ⟨σ, _, dependent, second⟩ := fibre_answer_in_fibre facts roots heads algebra complete rigid
      church names realization sortInjective closed @operatorInjective principal
    refine frameMap_admission_transfer (fibre facts roots heads church names realization)
      (fibre_reflects facts roots heads algebra complete rigid church names realization sortInjective
        @operatorInjective) P guards holds f second ?_
    intro b ρ solved
    obtain ⟨residual, through⟩ := dependent.factors b ρ solved
    exact ⟨residual, fun t => through _⟩
  · constructor
    · intro admitted
      exact absurd ((fibre facts roots heads church names realization).solvable
        (P.solvable_information admitted)) refuted
    · rintro ⟨-, -, solvable, -⟩
      exact absurd solvable refuted

/-! ## The chosen instance: the first-order step of the second-order action -/

section Instance

variable {O : Type} [DecidableEq O] (M : List (Binding.MetaArity sig))

/-- The terms of the first-order step: observations at `M`. -/
abbrev Obs := Binding.ContextualFamily.Observation sig M.get

/-- The second-order action at `M`: observations, acted on by its endomorphic assignments. -/
abbrev action := (listFrames sig).endo M

variable {M} (label : O → Obs M)

/-- The translated state: the translated telescope, the translated knowledge, the same
occurrences, and the translated labels. -/
def translateState (C : Configuration (Obs M) O) : State S.R O :=
  ⟨(fibre facts roots heads church names realization).obj M,
    (fibre facts roots heads church names realization).store C.equations, C.present,
    fun o => (fibre facts roots heads church names realization).tm (label o)⟩

/-- The equation guards of a check. -/
def checkGuards : Check (Obs M) → EquationStore (Obs M)
  | .equal left right => [(left, right)]
  | _ => []

variable (O) in
/-- The predicate queries of a check: absence and counting of the translated pattern. -/
def checkQueries : Check (Obs M) →
    List (Query S.levels O ((fibre facts roots heads church names realization).obj M))
  | .absent pattern => [Query.absent S.levels O ((fibre facts roots heads church names realization).tm pattern)]
  | .count pattern number =>
      [Query.count S.levels O ((fibre facts roots heads church names realization).tm pattern) number]
  | .equal _ _ => []

/-- **The translated firing**: no helpers; the same selection; translated take and read patterns,
made rows, tells and equation guards; absence and counting queries of the translated patterns. -/
def translateFiring (C : Configuration (Obs M) O)
    (f : AnnotatedRuns.Firing (Obs M) (Binding.ContextualFamily.Assignment (S := sig) M.get M.get) O) :
    Firing S.levels (translateState facts roots heads church names realization label C) where
  helpers := .nil _
  taken := f.selection.taken
  read := f.selection.read
  takes := f.rule.take.map (fibre facts roots heads church names realization).tm
  reads := f.rule.read.map (fibre facts roots heads church names realization).tm
  makes := f.selection.made.map fun o =>
    (o, Make.ofRow ((fibre facts roots heads church names realization).tm (label o)))
  tells := (fibre facts roots heads church names realization).store f.rule.tell
  guards := (fibre facts roots heads church names realization).store (f.rule.checks.flatMap checkGuards)
  queries := f.rule.checks.flatMap (checkQueries facts roots heads church names realization O)

variable (C : Configuration (Obs M) O)
  (f : AnnotatedRuns.Firing (Obs M) (Binding.ContextualFamily.Assignment (S := sig) M.get M.get) O)

omit [DecidableEq O] in
theorem translate_row (o : O) :
    (translateFiring facts roots heads church names realization label C f).row o =
      (fibre facts roots heads church names realization).tm (label o) :=
  (frames S.levels).act_id _

omit [DecidableEq O] in
theorem translate_row_eq :
    (translateFiring facts roots heads church names realization label C f).row =
      fun o => (fibre facts roots heads church names realization).tm (label o) :=
  funext (translate_row facts roots heads church names realization label C f)

omit [DecidableEq O] in
theorem map_fst_pair {α β : Type} (g : α → β) :
    ∀ l : List α, (l.map fun o => (o, g o)).map Prod.fst = l
  | [] => rfl
  | o :: rest => congrArg (o :: ·) (map_fst_pair g rest)

omit [DecidableEq O] in
theorem translate_made :
    (translateFiring facts roots heads church names realization label C f).made = f.selection.made :=
  map_fst_pair _ _

omit [DecidableEq O] in
theorem translate_selection :
    (translateFiring facts roots heads church names realization label C f).selection = f.selection := by
  show (⟨f.selection.taken, f.selection.read, _⟩ : Selection O) = f.selection
  rw [translate_made]

omit [DecidableEq O] in
theorem zip_map_equations {T T' : Type*} (g : T → T') (lab : O → T) :
    ∀ (ps : List T) (sel : List O),
      ((ps.map g).zip sel).map (fun x => (x.1, g (lab x.2))) =
        (ps.zipWith (fun p o => (p, lab o)) sel).map (fun e => (g e.1, g e.2))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: ps, _ :: sel => congrArg (_ :: ·) (zip_map_equations g lab ps sel)

omit [DecidableEq O] in
theorem translate_matching (patterns : List (Obs M)) (selected : List O) :
    (translateFiring facts roots heads church names realization label C f).matching
        (patterns.map (fibre facts roots heads church names realization).tm) selected =
      (fibre facts roots heads church names realization).store
        (Selection.equations label patterns selected) := by
  unfold Firing.matching
  rw [translate_row_eq]
  exact zip_map_equations _ label patterns selected

omit [DecidableEq O] in
/-- **The information of a translated firing is the translation of its problem.** -/
theorem translate_information :
    (translateFiring facts roots heads church names realization label C f).information =
      (fibre facts roots heads church names realization).store
        (f.selection.problem label f.rule C) := by
  have takes : (translateFiring facts roots heads church names realization label C f).matching
      (translateFiring facts roots heads church names realization label C f).takes
      (translateFiring facts roots heads church names realization label C f).taken =
      (fibre facts roots heads church names realization).store
        (Selection.equations label f.rule.take f.selection.taken) :=
    translate_matching facts roots heads church names realization label C f f.rule.take f.selection.taken
  have reads : (translateFiring facts roots heads church names realization label C f).matching
      (translateFiring facts roots heads church names realization label C f).reads
      (translateFiring facts roots heads church names realization label C f).read =
      (fibre facts roots heads church names realization).store
        (Selection.equations label f.rule.read f.selection.read) :=
    translate_matching facts roots heads church names realization label C f f.rule.read f.selection.read
  have knowledge : (frames S.levels).applyStore
      (translateFiring facts roots heads church names realization label C f).helpers.weaken
      (translateState facts roots heads church names realization label C).knowledge =
      (fibre facts roots heads church names realization).store C.equations :=
    Frames.applyStore_id (X := frames S.levels) _
  unfold Firing.information
  rw [takes, reads, knowledge]
  simp only [Selection.problem, FrameMap.store, List.map_append]
  rfl

/-! ### Solvability, guards and absence through the fibre -/

omit [DecidableEq O] in
/-- An absence ask is the refutation of each extension. -/
theorem entails_absent_iff {Obj : Type*} {Tm : Obj → Type*} {Hom : Obj → Obj → Type*}
    (X : Frames Tm Hom) {a : Obj} (K : EquationStore (Tm a)) (p : Tm a) (present : Finset O)
    (row : O → Tm a) :
    X.Entails K (fun _ τ => ∀ o ∈ present, ¬ X.E (X.act τ p) (X.act τ (row o))) ↔
      ∀ o ∈ present, ¬ X.Solvable (K ++ [(p, row o)]) := by
  constructor
  · rintro asked o inside ⟨b, τ, solved⟩
    obtain ⟨old, new⟩ := (Frames.models_append τ K _).mp solved
    exact asked b τ old o inside (new _ (List.mem_singleton_self _))
  · intro refuted b τ solved o inside equated
    refine refuted o inside ⟨b, τ, (Frames.models_append τ K _).mpr ⟨solved, ?_⟩⟩
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact equated

omit [DecidableEq O] in
/-- The same for a substitution action. -/
theorem action_entails_absent_iff {T U : Type*} (A : SubstitutionAction T U) (K : EquationStore T)
    (p : T) (present : Finset O) (row : O → T) :
    A.Entails K (fun σ => ∀ o ∈ present, ¬ A.E (A.apply σ p) (A.apply σ (row o))) ↔
      ∀ o ∈ present, ¬ A.Consistent (K ++ [(p, row o)]) := by
  constructor
  · rintro asked o inside ⟨σ, solved⟩
    obtain ⟨old, new⟩ := (A.models_append σ K _).mp solved
    exact asked σ old o inside (new _ (List.mem_singleton_self _))
  · intro refuted σ solved o inside equated
    refine refuted o inside ⟨σ, (A.models_append σ K _).mpr ⟨solved, ?_⟩⟩
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact equated

/-- A principal answer of a substitution action decides equation guards. -/
theorem action_principal_entails_iff {T U : Type*} {A : SubstitutionAction T U}
    {K : EquationStore T} {answer : U} (principal : A.Principal K answer) (G : EquationStore T) :
    A.Entails K (fun σ => A.Models σ G) ↔ A.Models answer G := by
  constructor
  · intro asked
    exact asked answer principal.sound
  · intro holds δ solved e member
    obtain ⟨residual, through⟩ := principal.factors δ solved
    have later := A.models_compose holds residual e member
    exact A.equivalence.trans (through e.1)
      (A.equivalence.trans later (A.equivalence.symm (through e.2)))

include algebra complete rigid sortInjective closed operatorInjective in
/-- **Solvability through the fibre**: on a store the dependent unifier decides by an endomorphic
principal answer or a refutation, dependent solvability is consistency of the first-order step. -/
theorem solvable_iff_consistent {K : EquationStore (Obs M)}
    (decided : (∃ τ : (fibre facts roots heads church names realization).obj M ⟶
        (fibre facts roots heads church names realization).obj M,
        (frames S.levels).Principal ((fibre facts roots heads church names realization).store K) τ) ∨
      ¬ (frames S.levels).Solvable ((fibre facts roots heads church names realization).store K)) :
    (frames S.levels).Solvable ((fibre facts roots heads church names realization).store K) ↔
      (action M).Consistent K := by
  constructor
  · intro solvable
    rcases decided with ⟨τ, principal⟩ | refuted
    · obtain ⟨σ, _, _, second⟩ := fibre_answer_in_fibre facts roots heads algebra complete rigid
        church names realization sortInjective closed @operatorInjective principal
      exact ⟨σ, second.sound⟩
    · exact absurd solvable refuted
  · rintro ⟨σ, solved⟩
    exact ⟨_, (fibre facts roots heads church names realization).hom σ,
      (fibre facts roots heads church names realization).models solved⟩

include algebra complete rigid sortInjective closed operatorInjective in
/-- **Equation guards through the fibre**, at an endomorphic principal answer of the unifier. -/
theorem entails_guards_iff {K G : EquationStore (Obs M)}
    {τ : (fibre facts roots heads church names realization).obj M ⟶
      (fibre facts roots heads church names realization).obj M}
    (principal : (frames S.levels).Principal ((fibre facts roots heads church names realization).store K) τ) :
    (frames S.levels).Entails ((fibre facts roots heads church names realization).store K)
        (fun _ g => (frames S.levels).Models g ((fibre facts roots heads church names realization).store G)) ↔
      (action M).Entails K (fun σ => (action M).Models σ G) := by
  obtain ⟨σ, _, dependent, second⟩ := fibre_answer_in_fibre facts roots heads algebra complete rigid
    church names realization sortInjective closed @operatorInjective principal
  rw [dependent.entails_models_iff, action_principal_entails_iff second.endo]
  exact fibre_models_iff facts roots heads algebra complete rigid church names realization
    sortInjective @operatorInjective σ G


/-! ### Admission and results of translated firings -/

omit [DecidableEq O] in
/-- The unifier decides a translated store at `M` by an endomorphic principal answer or a
refutation. -/
def EndoDecided (K : EquationStore (Obs M)) : Prop :=
  (∃ τ : (fibre facts roots heads church names realization).obj M ⟶
      (fibre facts roots heads church names realization).obj M,
      (frames S.levels).Principal ((fibre facts roots heads church names realization).store K) τ) ∨
    ¬ (frames S.levels).Solvable ((fibre facts roots heads church names realization).store K)

/-- The physical enabling of a selection, read off its lists, for any labels. -/
theorem selection_enabled_iff {R : Type*} (lab : O → R) (sel : Selection O) (present : Finset O) :
    Enabled lab present (sel.commit (T := R)) ↔
      (∀ o ∈ sel.taken, o ∈ present) ∧ (∀ o ∈ sel.read, o ∈ present) ∧
        (∀ o ∈ sel.taken, o ∉ sel.read) ∧ ∀ o ∈ sel.made, o ∉ present := by
  constructor
  · intro enabled
    refine ⟨fun o member => enabled.taken_subset (by simpa [Selection.commit] using member),
      fun o member => enabled.kept_subset (by simpa [Selection.commit] using member),
      fun o member readToo => Finset.disjoint_left.mp enabled.apart
        (by simpa [Selection.commit] using member) (by simpa [Selection.commit] using readToo),
      fun o member present' => Finset.disjoint_left.mp enabled.fresh
        (by simpa [Selection.commit] using member) present'⟩
  · rintro ⟨taken, read, apart, fresh⟩
    refine ⟨fun o member => taken o (by simpa [Selection.commit] using member),
      fun o member => read o (by simpa [Selection.commit] using member),
      Finset.disjoint_left.mpr fun {o} member readToo => apart o
        (by simpa [Selection.commit] using member) (by simpa [Selection.commit] using readToo),
      Finset.disjoint_left.mpr fun {o} member present' => fresh o
        (by simpa [Selection.commit] using member) present',
      fun q member => by simp [Selection.commit] at member⟩

omit [DecidableEq O] in
/-- **The checks of a first-order firing without counting checks**: its equation guards, and the
refutation of every absence extension. -/
theorem checks_entails_iff (noCount : ∀ p n, Check.count p n ∉ f.rule.checks) :
    (∀ c ∈ f.rule.checks, (action M).Entails (f.selection.problem label f.rule C)
        (fun σ => c.Holds (action M) σ label C.present)) ↔
      (action M).Entails (f.selection.problem label f.rule C)
          (fun σ => (action M).Models σ (f.rule.checks.flatMap checkGuards)) ∧
        ∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
          ¬ (action M).Consistent (f.selection.problem label f.rule C ++ [(p, label o)]) := by
  constructor
  · intro checks
    refine ⟨fun σ solved e member => ?_, fun p inside => ?_⟩
    · obtain ⟨c, present, guard⟩ := List.mem_flatMap.mp member
      cases c with
      | equal left right =>
          obtain rfl := List.mem_singleton.mp guard
          exact checks _ present σ solved
      | absent _ => cases guard
      | count _ _ => cases guard
    · exact (action_entails_absent_iff (action M) _ p C.present label).mp (checks _ inside)
  · rintro ⟨guards, absences⟩ c present
    cases c with
    | equal left right =>
        intro σ solved
        exact guards σ solved _ (List.mem_flatMap.mpr ⟨_, present, List.mem_singleton_self _⟩)
    | absent p => exact (action_entails_absent_iff (action M) _ p C.present label).mpr (absences p present)
    | count p n => exact absurd present (noCount p n)

/-- **First-order admission**, without census queries and counting checks. -/
theorem firstOrder_admits_iff (noQueries : f.queries = [])
    (noCount : ∀ p n, Check.count p n ∉ f.rule.checks) :
    (AnnotatedRuns.firstOrder (action M) label).Admits (s := C) f ↔
      (f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
        f.rule.take.length = f.selection.taken.length ∧ f.rule.read.length = f.selection.read.length ∧
        f.selection.made.map label = f.rule.produce) ∧
      ((∀ o ∈ f.selection.taken, o ∈ C.present) ∧ (∀ o ∈ f.selection.read, o ∈ C.present) ∧
        (∀ o ∈ f.selection.taken, o ∉ f.selection.read) ∧ ∀ o ∈ f.selection.made, o ∉ C.present) ∧
      (action M).Consistent (f.selection.problem label f.rule C) ∧
      (action M).Entails (f.selection.problem label f.rule C)
          (fun σ => (action M).Models σ (f.rule.checks.flatMap checkGuards)) ∧
        ∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
          ¬ (action M).Consistent (f.selection.problem label f.rule C ++ [(p, label o)]) := by
  show f.Valid (action M) label C ↔ _
  constructor
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences, consistent,
      checks⟩, -⟩
    obtain ⟨guards, absences⟩ := (checks_entails_iff label C f noCount).mp checks
    exact ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs⟩,
      (selection_enabled_iff label f.selection C.present).mp occurrences, consistent, guards, absences⟩
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs⟩, enabled, consistent,
      guards, absences⟩
    refine ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs,
      (selection_enabled_iff label f.selection C.present).mpr enabled, consistent,
      (checks_entails_iff label C f noCount).mpr ⟨guards, absences⟩⟩, ?_⟩
    intro q member
    rw [noQueries] at member
    cases member

omit [DecidableEq O] in
/-- **The queries of a translated firing**: absence of each translated pattern is the refutation of
each translated absence extension. -/
theorem translate_queries_iff (noCount : ∀ p n, Check.count p n ∉ f.rule.checks) :
    (∀ q ∈ (translateFiring facts roots heads church names realization label C f).queries,
        (frames S.levels).Entails
          (translateFiring facts roots heads church names realization label C f).information
          (fun _ τ => q.Holds C.present
            (translateFiring facts roots heads church names realization label C f).row τ)) ↔
      ∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
        ¬ (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
          (f.selection.problem label f.rule C ++ [(p, label o)])) := by
  have absentAsk : ∀ p : Obs M,
      (frames S.levels).Entails
          (translateFiring facts roots heads church names realization label C f).information
          (fun _ τ => (Query.absent S.levels O ((fibre facts roots heads church names realization).tm p)).Holds
            C.present (translateFiring facts roots heads church names realization label C f).row τ) ↔
        ∀ o ∈ C.present, ¬ (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
          (f.selection.problem label f.rule C ++ [(p, label o)])) := by
    intro p
    have pointwise : (frames S.levels).Entails
          (translateFiring facts roots heads church names realization label C f).information
          (fun _ τ => (Query.absent S.levels O ((fibre facts roots heads church names realization).tm p)).Holds
            C.present (translateFiring facts roots heads church names realization label C f).row τ) ↔
        (frames S.levels).Entails
          (translateFiring facts roots heads church names realization label C f).information
          (fun _ τ => ∀ o ∈ C.present, ¬ (frames S.levels).E
            ((frames S.levels).act τ ((fibre facts roots heads church names realization).tm p))
            ((frames S.levels).act τ
              ((translateFiring facts roots heads church names realization label C f).row o))) :=
      ⟨fun asked b τ solved => (Query.absent_holds_iff _ _ _ τ).mp (asked b τ solved),
        fun asked b τ solved => (Query.absent_holds_iff _ _ _ τ).mpr (asked b τ solved)⟩
    rw [pointwise]
    refine (entails_absent_iff (frames S.levels) _ _ C.present _).trans ?_
    rw [translate_information, translate_row_eq]
    simp only [FrameMap.store, List.map_append, List.map_cons, List.map_nil]
    exact Iff.rfl
  constructor
  · intro asked p inside
    exact (absentAsk p).mp (asked _ (List.mem_flatMap.mpr ⟨_, inside, List.mem_singleton_self _⟩))
  · intro absences q member
    obtain ⟨c, present, query⟩ := List.mem_flatMap.mp member
    cases c with
    | equal _ _ => cases query
    | absent p =>
        obtain rfl := List.mem_singleton.mp query
        exact (absentAsk p).mpr (absences p present)
    | count p n => exact absurd present (noCount p n)

/-- **Dependent admission of a translated firing**, without counting checks. -/
theorem translate_admits_iff (noCount : ∀ p n, Check.count p n ∉ f.rule.checks) :
    (step S.levels O).Admits (s := translateState facts roots heads church names realization label C)
        (translateFiring facts roots heads church names realization label C f) ↔
      (f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
        f.rule.take.length = f.selection.taken.length ∧ f.rule.read.length = f.selection.read.length) ∧
      ((∀ o ∈ f.selection.taken, o ∈ C.present) ∧ (∀ o ∈ f.selection.read, o ∈ C.present) ∧
        (∀ o ∈ f.selection.taken, o ∉ f.selection.read) ∧ ∀ o ∈ f.selection.made, o ∉ C.present) ∧
      (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
        (f.selection.problem label f.rule C)) ∧
      (frames S.levels).Entails ((fibre facts roots heads church names realization).store
          (f.selection.problem label f.rule C))
        (fun _ g => (frames S.levels).Models g ((fibre facts roots heads church names realization).store
          (f.rule.checks.flatMap checkGuards))) ∧
      ∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
        ¬ (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
          (f.selection.problem label f.rule C ++ [(p, label o)])) := by
  rw [admits_iff]
  have queries := translate_queries_iff facts roots heads church names realization label C f noCount
  have information := translate_information facts roots heads church names realization label C f
  have made := translate_made facts roots heads church names realization label C f
  have shapes : (translateFiring facts roots heads church names realization label C f).Shapes ↔
      f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
        f.rule.take.length = f.selection.taken.length ∧ f.rule.read.length = f.selection.read.length := by
    unfold Firing.Shapes
    rw [made]
    constructor
    · rintro ⟨takeDistinct, outputDistinct, takeLength, readLength, -⟩
      exact ⟨takeDistinct, outputDistinct, (List.length_map _).symm.trans takeLength,
        (List.length_map _).symm.trans readLength⟩
    · rintro ⟨takeDistinct, outputDistinct, takeLength, readLength⟩
      refine ⟨takeDistinct, outputDistinct, (List.length_map _).trans takeLength,
        (List.length_map _).trans readLength, fun m member => ?_⟩
      obtain ⟨o, -, rfl⟩ := List.mem_map.mp member
      exact Make.ofRow_wellTyped _
  constructor
  · rintro ⟨shaped, ⟨taken, read, apart, fresh⟩, solvable, guards, asked⟩
    refine ⟨shapes.mp shaped, ⟨taken, read, apart, by rw [← made]; exact fresh⟩,
      by rw [← information]; exact solvable, by rw [← information]; exact guards, queries.mp asked⟩
  · rintro ⟨shaped, ⟨taken, read, apart, fresh⟩, solvable, guards, asked⟩
    refine ⟨shapes.mpr shaped, ⟨taken, read, apart, by rw [made]; exact fresh⟩,
      by rw [information]; exact solvable, by rw [information]; exact guards, queries.mpr asked⟩

include algebra complete rigid sortInjective closed operatorInjective in
/-- **Admission is preserved and reflected by the join.** At a first-order firing without census
queries and counting checks, whose problem and absence extensions the dependent unifier decides in
the fibre at `M`, the firing is admitted exactly when its produced labels are its made occurrences'
labels and its translation is admitted by the dependent full step. -/
theorem admits_translate_iff (noQueries : f.queries = [])
    (noCount : ∀ p n, Check.count p n ∉ f.rule.checks)
    (decided : EndoDecided facts roots heads church names realization (f.selection.problem label f.rule C))
    (decidedAbsent : ∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
      EndoDecided facts roots heads church names realization
        (f.selection.problem label f.rule C ++ [(p, label o)])) :
    (AnnotatedRuns.firstOrder (action M) label).Admits (s := C) f ↔
      f.selection.made.map label = f.rule.produce ∧
        (step S.levels O).Admits (s := translateState facts roots heads church names realization label C)
          (translateFiring facts roots heads church names realization label C f) := by
  have absences : (∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
        ¬ (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
          (f.selection.problem label f.rule C ++ [(p, label o)]))) ↔
      ∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
        ¬ (action M).Consistent (f.selection.problem label f.rule C ++ [(p, label o)]) :=
    forall_congr' fun p => imp_congr_right fun inside => forall₂_congr fun o present =>
      not_congr (solvable_iff_consistent facts roots heads algebra complete rigid church names
        realization sortInjective closed @operatorInjective (decidedAbsent p inside o present))
  rw [firstOrder_admits_iff label C f noQueries noCount,
    translate_admits_iff facts roots heads church names realization label C f noCount, absences]
  rcases decided with ⟨τ, principal⟩ | refuted
  · rw [entails_guards_iff facts roots heads algebra complete rigid church names realization
        sortInjective closed @operatorInjective principal,
      solvable_iff_consistent facts roots heads algebra complete rigid church names realization
        sortInjective closed @operatorInjective (.inl ⟨τ, principal⟩)]
    constructor
    · rintro ⟨⟨a, b, c, d, outputs⟩, rest⟩
      exact ⟨outputs, ⟨a, b, c, d⟩, rest⟩
    · rintro ⟨outputs, ⟨a, b, c, d⟩, rest⟩
      exact ⟨⟨a, b, c, d, outputs⟩, rest⟩
  · constructor
    · rintro ⟨-, -, consistent, -⟩
      exact absurd ((solvable_iff_consistent facts roots heads algebra complete rigid church names
        realization sortInjective closed @operatorInjective (.inr refuted)).mpr consistent) refuted
    · rintro ⟨-, -, -, solvable, -⟩
      exact absurd solvable refuted

/-- The made rows of a translated firing relabel to the translated labels. -/
theorem relabel_translate
    (typed : ∀ m ∈ (translateFiring facts roots heads church names realization label C f).makes,
      m.2.WellTyped) :
    relabel (translateFiring facts roots heads church names realization label C f).row
        (translateFiring facts roots heads church names realization label C f).makes typed =
      fun o => (fibre facts roots heads church names realization).tm (label o) := by
  funext o
  by_cases inside : o ∈ (translateFiring facts roots heads church names realization label C f).made
  · obtain ⟨m, member, named, eq⟩ := relabel_of_mem _ _ typed inside
    rw [eq]
    obtain ⟨o', -, rfl⟩ := List.mem_map.mp member
    have same : o' = o := named
    subst same
    rfl
  · rw [relabel_of_not_mem _ _ typed inside, translate_row]

/-- **Results correspond**: the dependent result of a translated firing is the translated
first-order result. The translated firing makes no helpers, so the frames' isomorphism is the
identity. -/
theorem result_translate
    (admitted : (step S.levels O).Admits (s := translateState facts roots heads church names realization label C)
      (translateFiring facts roots heads church names realization label C f)) :
    (step S.levels O).result (translateFiring facts roots heads church names realization label C f) admitted =
      translateState facts roots heads church names realization label (f.result label C) := by
  show State.mk _ (translateFiring facts roots heads church names realization label C f).information
      (fire C.present ((translateFiring facts roots heads church names realization label C f).selection.commit
        (T := Unit)))
      (relabel _ _ admitted.1.2.2.2.2) = _
  rw [relabel_translate, translate_information, translate_selection]
  rfl

end Instance

end DependentFull

#print axioms DependentFull.frameMap_admission_transfer
#print axioms DependentFull.fibre_admission_transfer
#print axioms DependentFull.translate_information
#print axioms DependentFull.entails_absent_iff
#print axioms DependentFull.action_entails_absent_iff
#print axioms DependentFull.action_principal_entails_iff
#print axioms DependentFull.solvable_iff_consistent
#print axioms DependentFull.entails_guards_iff
#print axioms DependentFull.selection_enabled_iff
#print axioms DependentFull.checks_entails_iff
#print axioms DependentFull.firstOrder_admits_iff
#print axioms DependentFull.translate_queries_iff
#print axioms DependentFull.translate_admits_iff
#print axioms DependentFull.admits_translate_iff
#print axioms DependentFull.relabel_translate
#print axioms DependentFull.result_translate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
