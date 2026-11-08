import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullFibre

/-!
# Counting queries through the fibre join

R91's join (`admits_translate_iff`) excludes counting checks. This module removes that exclusion.

**Counting at a principal answer** (`Frames.Principal.entails_count_iff`,
`SubstitutionAction.Principal.entails_count_iff`). An exact count of the present rows equated with a
pattern, asked at every solution of a store with a principal answer, holds exactly when:
* the count at the principal answer is the number;
* and every present row the principal answer does not equate with the pattern is refuted by the
  store, that is, the store extended by `pattern ≐ row` has no solution.

Solutions factor through the principal answer, so the rows it equates are equated at every solution;
a row it leaves apart would raise the count at some solution unless that extension is refuted.

**Through the fibre** (`count_transfer`). For the first-order step of the second-order action, a
counting check is asked at every endomorphic solution. Its translation, R91's counting query of the
translated pattern, is asked at every dependent solution. The two asks agree when the dependent
unifier decides the problem and each extension by an endomorphic principal answer or a refutation,
the condition R91 uses for absence (`EndoDecided`):
* the matched rows correspond, because the fibre reflects the equivalence;
* each extension is refuted on one side exactly when on the other.

**Admission with counting checks** (`admits_translate_iff_count`). At every first-order firing without
census queries, under those decisions, first-order admission is the shape condition on produced
labels together with dependent admission of the translation. No exclusion of counting checks
remains.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

/-! ## Counting at a principal answer -/

section Generic

universe uO uT uH

open Classical in
/-- The present rows a solution equates with a pattern. -/
noncomputable def Frames.matchedAt {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    (X : Frames Tm Hom) {O : Type} {a b : Obj} (τ : Hom a b) (pattern : Tm a) (present : Finset O)
    (row : O → Tm a) : Finset O :=
  present.filter fun o => X.E (X.act τ pattern) (X.act τ (row o))

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom} {O : Type}

theorem mem_matchedAt {a b : Obj} (τ : Hom a b) (pattern : Tm a) (present : Finset O) (row : O → Tm a)
    (o : O) :
    o ∈ X.matchedAt τ pattern present row ↔ o ∈ present ∧ X.E (X.act τ pattern) (X.act τ (row o)) := by
  classical
  unfold matchedAt
  rw [Finset.mem_filter]

/-- Equations of a principal answer hold at every solution. -/
theorem Principal.equated {a m : Obj} {K : EquationStore (Tm a)} {answer : Hom a m}
    (principal : X.Principal K answer) {b : Obj} {τ : Hom a b} (solved : X.Models τ K) {s t : Tm a}
    (same : X.E (X.act answer s) (X.act answer t)) : X.E (X.act τ s) (X.act τ t) := by
  obtain ⟨residual, through⟩ := principal.factors b τ solved
  have later := X.preserves residual same
  rw [← X.act_comp, ← X.act_comp] at later
  exact (X.equivalence b).trans (through s) ((X.equivalence b).trans later ((X.equivalence b).symm (through t)))

/-- **An exact count at every solution, through a principal answer.** -/
theorem Principal.entails_count_iff {a m : Obj} {K : EquationStore (Tm a)} {answer : Hom a m}
    (principal : X.Principal K answer) (pattern : Tm a) (present : Finset O) (row : O → Tm a)
    (number : Nat) :
    X.Entails K (fun _ τ => (X.matchedAt τ pattern present row).card = number) ↔
      (X.matchedAt answer pattern present row).card = number ∧
        ∀ o ∈ present, o ∉ X.matchedAt answer pattern present row →
          ¬ X.Solvable (K ++ [(pattern, row o)]) := by
  have grows : ∀ {b : Obj} {τ : Hom a b}, X.Models τ K →
      X.matchedAt answer pattern present row ⊆ X.matchedAt τ pattern present row := by
    intro b τ solved o inside
    obtain ⟨present', same⟩ := (mem_matchedAt answer pattern present row o).mp inside
    exact (mem_matchedAt τ pattern present row o).mpr ⟨present', principal.equated solved same⟩
  constructor
  · intro asked
    refine ⟨asked m answer principal.sound, fun o present' outside => ?_⟩
    rintro ⟨b, τ, solved⟩
    obtain ⟨old, new⟩ := (models_append τ K _).mp solved
    have inside : o ∈ X.matchedAt τ pattern present row :=
      (mem_matchedAt τ pattern present row o).mpr ⟨present', new _ (List.mem_singleton_self _)⟩
    have strict : X.matchedAt answer pattern present row ⊂ X.matchedAt τ pattern present row :=
      Finset.ssubset_iff_subset_ne.mpr ⟨grows old, fun same => outside (same ▸ inside)⟩
    have smaller := Finset.card_lt_card strict
    rw [asked m answer principal.sound, asked b τ old] at smaller
    exact lt_irrefl _ smaller
  · rintro ⟨atAnswer, refuted⟩ b τ solved
    have same : X.matchedAt τ pattern present row = X.matchedAt answer pattern present row := by
      refine Finset.Subset.antisymm (fun o inside => ?_) (grows solved)
      obtain ⟨present', equated⟩ := (mem_matchedAt τ pattern present row o).mp inside
      by_contra outside
      refine refuted o present' outside ⟨b, τ, (models_append τ K _).mpr ⟨solved, ?_⟩⟩
      intro e member
      obtain rfl := List.mem_singleton.mp member
      exact equated
    rw [same]
    exact atAnswer

end Frames

namespace SubstitutionAction

variable {T S : Type*} {A : SubstitutionAction T S} {O : Type}

theorem mem_matches (σ : S) (label : O → T) (present : Finset O) (pattern : T) (o : O) :
    o ∈ Check.matches A σ label present pattern ↔ o ∈ present ∧ A.E (A.apply σ pattern) (A.apply σ (label o)) := by
  classical
  unfold Check.matches
  rw [Finset.mem_filter]

theorem Principal.equated {K : EquationStore T} {answer : S} (principal : A.Principal K answer) {δ : S}
    (solved : A.Models δ K) {s t : T} (same : A.E (A.apply answer s) (A.apply answer t)) :
    A.E (A.apply δ s) (A.apply δ t) := by
  obtain ⟨residual, through⟩ := principal.factors δ solved
  have later := A.preserves residual same
  rw [← A.apply_compose, ← A.apply_compose] at later
  exact A.equivalence.trans (through s) (A.equivalence.trans later (A.equivalence.symm (through t)))

/-- **An exact count at every solution, through a principal answer**, for a substitution action. -/
theorem Principal.entails_count_iff {K : EquationStore T} {answer : S} (principal : A.Principal K answer)
    (pattern : T) (present : Finset O) (label : O → T) (number : Nat) :
    A.Entails K (fun σ => (Check.matches A σ label present pattern).card = number) ↔
      (Check.matches A answer label present pattern).card = number ∧
        ∀ o ∈ present, o ∉ Check.matches A answer label present pattern →
          ¬ A.Consistent (K ++ [(pattern, label o)]) := by
  have grows : ∀ {δ : S}, A.Models δ K →
      Check.matches A answer label present pattern ⊆ Check.matches A δ label present pattern := by
    intro δ solved o inside
    obtain ⟨present', same⟩ := (mem_matches answer label present pattern o).mp inside
    exact (mem_matches δ label present pattern o).mpr
      ⟨present', SubstitutionAction.Principal.equated principal solved same⟩
  constructor
  · intro asked
    refine ⟨asked answer principal.sound, fun o present' outside => ?_⟩
    rintro ⟨δ, solved⟩
    obtain ⟨old, new⟩ := (A.models_append δ K _).mp solved
    have inside : o ∈ Check.matches A δ label present pattern :=
      (mem_matches δ label present pattern o).mpr ⟨present', new _ (List.mem_singleton_self _)⟩
    have strict : Check.matches A answer label present pattern ⊂ Check.matches A δ label present pattern :=
      Finset.ssubset_iff_subset_ne.mpr ⟨grows old, fun same => outside (same ▸ inside)⟩
    have smaller := Finset.card_lt_card strict
    rw [asked answer principal.sound, asked δ old] at smaller
    exact lt_irrefl _ smaller
  · rintro ⟨atAnswer, refuted⟩ δ solved
    have same : Check.matches A δ label present pattern = Check.matches A answer label present pattern := by
      refine Finset.Subset.antisymm (fun o inside => ?_) (grows solved)
      obtain ⟨present', equated⟩ := (mem_matches δ label present pattern o).mp inside
      by_contra outside
      refine refuted o present' outside ⟨δ, (A.models_append δ K _).mpr ⟨solved, ?_⟩⟩
      intro e member
      obtain rfl := List.mem_singleton.mp member
      exact equated
    rw [same]
    exact atAnswer

end SubstitutionAction

end Generic

namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentFibre Translation

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The counting query holds exactly when the matched present rows number as asked.** -/
theorem Query.count_holds_iff {O : Type} {Δ : Context S.R} (pattern : TotalTerm Δ) (number : Nat)
    (present : Finset O) (row : O → TotalTerm Δ) {Θ : Context S.R} (τ : Θ ⟶ Δ) :
    (Query.count S.levels O pattern number).Holds present row τ ↔
      ((frames S.levels).matchedAt τ pattern present row).card = number := by
  constructor
  · rintro ⟨seen, members, card⟩
    have same : seen = (frames S.levels).matchedAt τ pattern present row := by
      ext o
      rw [members o, Frames.mem_matchedAt]
      rfl
    rw [← same]
    exact card
  · intro card
    refine ⟨(frames S.levels).matchedAt τ pattern present row, fun o => ?_, card⟩
    rw [Frames.mem_matchedAt]
    rfl

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
  (rigid : ∀ name, S.roles name = .rigid) (church : ConversionCoherence.ChurchRosser S.R)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)
  (sortInjective : Function.Injective names.sort)
  (closed : ClosedRealization (S := S) names)
  (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))

section Instance

variable {O : Type} [DecidableEq O] {M : List (Binding.MetaArity sig)} (label : O → Obs M)

omit [DecidableEq O] in
include algebra complete rigid sortInjective closed operatorInjective in
/-- **Counting through the fibre.** When the dependent unifier decides the problem and each of its
extensions by a present row, by an endomorphic principal answer or a refutation, the translated
counting query is asked at every dependent solution exactly when the counting check is asked at every
endomorphic solution. -/
theorem count_transfer (K : EquationStore (Obs M)) (pattern : Obs M) (number : Nat) (present : Finset O)
    (decided : EndoDecided facts roots heads church names realization K)
    (decidedExtensions : ∀ o ∈ present,
      EndoDecided facts roots heads church names realization (K ++ [(pattern, label o)])) :
    (frames S.levels).Entails ((fibre facts roots heads church names realization).store K)
        (fun _ τ => (Query.count S.levels O ((fibre facts roots heads church names realization).tm pattern)
          number).Holds present (fun o => (fibre facts roots heads church names realization).tm (label o)) τ) ↔
      (action M).Entails K (fun σ => (Check.matches (action M) σ label present pattern).card = number) := by
  have counted : (frames S.levels).Entails ((fibre facts roots heads church names realization).store K)
        (fun _ τ => (Query.count S.levels O ((fibre facts roots heads church names realization).tm pattern)
          number).Holds present (fun o => (fibre facts roots heads church names realization).tm (label o)) τ) ↔
      (frames S.levels).Entails ((fibre facts roots heads church names realization).store K)
        (fun _ τ => ((frames S.levels).matchedAt τ ((fibre facts roots heads church names realization).tm pattern)
          present (fun o => (fibre facts roots heads church names realization).tm (label o))).card = number) :=
    ⟨fun asked b τ solved => (Query.count_holds_iff _ _ _ _ τ).mp (asked b τ solved),
      fun asked b τ solved => (Query.count_holds_iff _ _ _ _ τ).mpr (asked b τ solved)⟩
  rw [counted]
  rcases decided with ⟨τ, principal⟩ | refuted
  · obtain ⟨σ, _, dependent, second⟩ := fibre_answer_in_fibre facts roots heads algebra complete rigid
      church names realization sortInjective closed @operatorInjective principal
    rw [dependent.entails_count_iff, SubstitutionAction.Principal.entails_count_iff second.endo]
    have matched : (frames S.levels).matchedAt ((fibre facts roots heads church names realization).hom σ)
          ((fibre facts roots heads church names realization).tm pattern) present
          (fun o => (fibre facts roots heads church names realization).tm (label o)) =
        Check.matches (action M) σ label present pattern := by
      ext o
      rw [Frames.mem_matchedAt, SubstitutionAction.mem_matches]
      refine and_congr Iff.rfl ⟨fun same => ?_, fun same => ?_⟩
      · have back := ((frames S.levels).equivalence _).trans
          ((fibre facts roots heads church names realization).act σ pattern)
          (((frames S.levels).equivalence _).trans same
            (((frames S.levels).equivalence _).symm ((fibre facts roots heads church names realization).act σ (label o))))
        exact fibre_reflects facts roots heads algebra complete rigid church names realization sortInjective
          @operatorInjective back
      · have forth := (fibre facts roots heads church names realization).preserves (a := M) same
        exact ((frames S.levels).equivalence _).trans
          (((frames S.levels).equivalence _).symm ((fibre facts roots heads church names realization).act σ pattern))
          (((frames S.levels).equivalence _).trans forth
            ((fibre facts roots heads church names realization).act σ (label o)))
    rw [matched]
    refine and_congr Iff.rfl (forall₂_congr fun o present' => imp_congr_right fun _ => not_congr ?_)
    have extension := solvable_iff_consistent facts roots heads algebra complete rigid church names realization
      sortInjective closed @operatorInjective (decidedExtensions o present')
    simp only [FrameMap.store, List.map_append, List.map_cons, List.map_nil] at extension
    exact extension
  · have inconsistent : ¬ (action M).Consistent K := fun consistent =>
      refuted ((solvable_iff_consistent facts roots heads algebra complete rigid church names realization
        sortInjective closed @operatorInjective (.inr refuted)).mpr consistent)
    constructor
    · intro _ δ solved
      exact absurd ⟨δ, solved⟩ inconsistent
    · intro _ b τ solved
      exact absurd ⟨b, τ, solved⟩ refuted

variable (C : Configuration (Obs M) O)
  (f : AnnotatedRuns.Firing (Obs M) (Binding.ContextualFamily.Assignment (S := sig) M.get M.get) O)

omit [DecidableEq O] in
/-- **The checks of a first-order firing**: equation guards, the refutation of every absence
extension, and every exact count. -/
theorem checks_entails_iff_count :
    (∀ c ∈ f.rule.checks, (action M).Entails (f.selection.problem label f.rule C)
        (fun σ => c.Holds (action M) σ label C.present)) ↔
      (action M).Entails (f.selection.problem label f.rule C)
          (fun σ => (action M).Models σ (f.rule.checks.flatMap checkGuards)) ∧
        (∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
          ¬ (action M).Consistent (f.selection.problem label f.rule C ++ [(p, label o)])) ∧
        ∀ p n, Check.count p n ∈ f.rule.checks →
          (action M).Entails (f.selection.problem label f.rule C)
            (fun σ => (Check.matches (action M) σ label C.present p).card = n) := by
  constructor
  · intro checks
    refine ⟨fun σ solved e member => ?_, fun p inside => ?_, fun p n inside σ solved => checks _ inside σ solved⟩
    · obtain ⟨c, present, guard⟩ := List.mem_flatMap.mp member
      cases c with
      | equal left right =>
          obtain rfl := List.mem_singleton.mp guard
          exact checks _ present σ solved
      | absent _ => cases guard
      | count _ _ => cases guard
    · exact (action_entails_absent_iff (action M) _ p C.present label).mp (checks _ inside)
  · rintro ⟨guards, absences, counts⟩ c present
    cases c with
    | equal left right =>
        intro σ solved
        exact guards σ solved _ (List.mem_flatMap.mpr ⟨_, present, List.mem_singleton_self _⟩)
    | absent p => exact (action_entails_absent_iff (action M) _ p C.present label).mpr (absences p present)
    | count p n => exact counts p n present

/-- **First-order admission with every kind of check**, without census queries. -/
theorem firstOrder_admits_iff_count (noQueries : f.queries = []) :
    (AnnotatedRuns.firstOrder (action M) label).Admits (s := C) f ↔
      (f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
        f.rule.take.length = f.selection.taken.length ∧ f.rule.read.length = f.selection.read.length ∧
        f.selection.made.map label = f.rule.produce) ∧
      ((∀ o ∈ f.selection.taken, o ∈ C.present) ∧ (∀ o ∈ f.selection.read, o ∈ C.present) ∧
        (∀ o ∈ f.selection.taken, o ∉ f.selection.read) ∧ ∀ o ∈ f.selection.made, o ∉ C.present) ∧
      (action M).Consistent (f.selection.problem label f.rule C) ∧
      ∀ c ∈ f.rule.checks, (action M).Entails (f.selection.problem label f.rule C)
        (fun σ => c.Holds (action M) σ label C.present) := by
  show f.Valid (action M) label C ↔ _
  constructor
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences, consistent,
      checks⟩, -⟩
    exact ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs⟩,
      (selection_enabled_iff label f.selection C.present).mp occurrences, consistent, checks⟩
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs⟩, enabled, consistent, checks⟩
    refine ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs,
      (selection_enabled_iff label f.selection C.present).mpr enabled, consistent, checks⟩, ?_⟩
    intro q member
    rw [noQueries] at member
    cases member

omit [DecidableEq O] in
/-- **The queries of a translated firing**, counting included: absence of each translated pattern is
the refutation of each translated absence extension, and each counting query is asked of the
translated problem. -/
theorem translate_queries_iff_count :
    (∀ q ∈ (translateFiring facts roots heads church names realization label C f).queries,
        (frames S.levels).Entails
          (translateFiring facts roots heads church names realization label C f).information
          (fun _ τ => q.Holds C.present
            (translateFiring facts roots heads church names realization label C f).row τ)) ↔
      (∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
        ¬ (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
          (f.selection.problem label f.rule C ++ [(p, label o)]))) ∧
      ∀ p n, Check.count p n ∈ f.rule.checks →
        (frames S.levels).Entails ((fibre facts roots heads church names realization).store
            (f.selection.problem label f.rule C))
          (fun _ τ => (Query.count S.levels O ((fibre facts roots heads church names realization).tm p)
            n).Holds C.present (fun o => (fibre facts roots heads church names realization).tm (label o)) τ) := by
  have information := translate_information facts roots heads church names realization label C f
  have row := translate_row_eq facts roots heads church names realization label C f
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
    rw [information, row]
    simp only [FrameMap.store, List.map_append, List.map_cons, List.map_nil]
    exact Iff.rfl
  have countAsk : ∀ (p : Obs M) (n : Nat),
      (frames S.levels).Entails
          (translateFiring facts roots heads church names realization label C f).information
          (fun _ τ => (Query.count S.levels O ((fibre facts roots heads church names realization).tm p) n).Holds
            C.present (translateFiring facts roots heads church names realization label C f).row τ) ↔
        (frames S.levels).Entails ((fibre facts roots heads church names realization).store
            (f.selection.problem label f.rule C))
          (fun _ τ => (Query.count S.levels O ((fibre facts roots heads church names realization).tm p)
            n).Holds C.present (fun o => (fibre facts roots heads church names realization).tm (label o)) τ) := by
    intro p n
    rw [information, row]
    exact Iff.rfl
  constructor
  · intro asked
    refine ⟨fun p inside => (absentAsk p).mp (asked _ (List.mem_flatMap.mpr ⟨_, inside, List.mem_singleton_self _⟩)),
      fun p n inside => (countAsk p n).mp (asked _ (List.mem_flatMap.mpr ⟨_, inside, List.mem_singleton_self _⟩))⟩
  · rintro ⟨absences, counts⟩ q member
    obtain ⟨c, present, query⟩ := List.mem_flatMap.mp member
    cases c with
    | equal _ _ => cases query
    | absent p =>
        obtain rfl := List.mem_singleton.mp query
        exact (absentAsk p).mpr (absences p present)
    | count p n =>
        obtain rfl := List.mem_singleton.mp query
        exact (countAsk p n).mpr (counts p n present)

/-- **Dependent admission of a translated firing, counting checks included.** -/
theorem translate_admits_iff_count :
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
      (∀ p, Check.absent p ∈ f.rule.checks → ∀ o ∈ C.present,
        ¬ (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
          (f.selection.problem label f.rule C ++ [(p, label o)]))) ∧
      ∀ p n, Check.count p n ∈ f.rule.checks →
        (frames S.levels).Entails ((fibre facts roots heads church names realization).store
            (f.selection.problem label f.rule C))
          (fun _ τ => (Query.count S.levels O ((fibre facts roots heads church names realization).tm p)
            n).Holds C.present (fun o => (fibre facts roots heads church names realization).tm (label o)) τ) := by
  rw [admits_iff]
  have queries := translate_queries_iff_count facts roots heads church names realization label C f
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
    obtain ⟨absent, count⟩ := queries.mp asked
    exact ⟨shapes.mp shaped, ⟨taken, read, apart, by rw [← made]; exact fresh⟩,
      by rw [← information]; exact solvable, by rw [← information]; exact guards, absent, count⟩
  · rintro ⟨shaped, ⟨taken, read, apart, fresh⟩, solvable, guards, absent, count⟩
    exact ⟨shapes.mpr shaped, ⟨taken, read, apart, by rw [made]; exact fresh⟩,
      by rw [information]; exact solvable, by rw [information]; exact guards, queries.mpr ⟨absent, count⟩⟩

include algebra complete rigid sortInjective closed operatorInjective in
/-- **Admission is preserved and reflected by the join, counting checks included.** At a first-order
firing without census queries, whose problem and whose extensions by each check's pattern and each
present row the dependent unifier decides at `M`, the firing is admitted exactly when its produced
labels are its made occurrences' labels and its translation is admitted by the dependent full step. -/
theorem admits_translate_iff_count (noQueries : f.queries = [])
    (decided : EndoDecided facts roots heads church names realization (f.selection.problem label f.rule C))
    (decidedExtensions : ∀ c ∈ f.rule.checks, ∀ o ∈ C.present,
      EndoDecided facts roots heads church names realization
        (f.selection.problem label f.rule C ++ [(c.pattern, label o)])) :
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
        realization sortInjective closed @operatorInjective (decidedExtensions _ inside o present))
  have counts : (∀ p n, Check.count p n ∈ f.rule.checks →
        (frames S.levels).Entails ((fibre facts roots heads church names realization).store
            (f.selection.problem label f.rule C))
          (fun _ τ => (Query.count S.levels O ((fibre facts roots heads church names realization).tm p)
            n).Holds C.present (fun o => (fibre facts roots heads church names realization).tm (label o)) τ)) ↔
      ∀ p n, Check.count p n ∈ f.rule.checks →
        (action M).Entails (f.selection.problem label f.rule C)
          (fun σ => (Check.matches (action M) σ label C.present p).card = n) :=
    forall₂_congr fun p n => imp_congr_right fun inside =>
      count_transfer facts roots heads algebra complete rigid church names realization sortInjective closed
        @operatorInjective label _ p n C.present decided (decidedExtensions _ inside)
  rw [firstOrder_admits_iff_count label C f noQueries, checks_entails_iff_count label C f,
    translate_admits_iff_count facts roots heads church names realization label C f, absences, counts]
  rcases decided with ⟨τ, principal⟩ | refuted
  · rw [entails_guards_iff facts roots heads algebra complete rigid church names realization sortInjective closed
        @operatorInjective principal,
      solvable_iff_consistent facts roots heads algebra complete rigid church names realization sortInjective closed
        @operatorInjective (.inl ⟨τ, principal⟩)]
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

end Instance

end DependentFull

#print axioms Frames.Principal.entails_count_iff
#print axioms SubstitutionAction.Principal.entails_count_iff
#print axioms DependentFull.Query.count_holds_iff
#print axioms DependentFull.count_transfer
#print axioms DependentFull.checks_entails_iff_count
#print axioms DependentFull.firstOrder_admits_iff_count
#print axioms DependentFull.translate_queries_iff_count
#print axioms DependentFull.translate_admits_iff_count
#print axioms DependentFull.admits_translate_iff_count

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
