import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullNonVacuity

/-!
# A multi-frame second-order instance of the fibre join, without the endomorphism condition

R91's chosen instance is the first-order step of the second-order action at one list frame `M`: its
solutions are endomorphisms of `M`, so its join needs the unifier's answers to land back at `M`
(`EndoDecided`), which the solvers do not give: their answers land at smaller telescopes.

The frame-local equation step over the list frames (`EquationStep.step (listFrames sig)`) has
solutions into every list frame. Its states and firings translate into the dependent full step at
translated telescopes, with no helpers (`translateLocal`, `translateEquationFiring`):

* the translated information is the translation of the information (`translateEquation_information`);
* **admission is preserved and reflected** wherever the unifier decides the information in the fibre
  (`translateEquation_admits_iff`), with answers at any translated telescope, so with no endomorphism
  condition; in particular wherever the full solver decides it (`translateEquation_admits_iff_of_full`);
* **results correspond** (`translateEquation_result`): the dependent result of a translated firing is the
  translated result.

**Controls** in the point package (`DependentFullNonVacuityInstanceControls`): the take firing `m(x)` on the row `n(x)` is admitted by the
dependent full step, with the decision read off the solver's run (`take_translated_admitted`); the
take `F(x)` on the row `y` is refused by it (`outside_translated_refused`).
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

section Instance

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (church : ConversionCoherence.ChurchRosser S.R)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)
variable {O : Type} [DecidableEq O]

/-- Observations at list frames. -/
abbrev ListObs (sig : Binding.Signature) : List (Binding.MetaArity sig) → Type :=
  fun M => Binding.ContextualFamily.Observation sig M.get

/-- **The translated state**: the translated telescope, knowledge and labels, the same occurrences. -/
def translateLocal (s : EquationStep.State (ListObs sig) O) : State S.R O :=
  ⟨(fibre facts roots heads church names realization).obj s.frame,
    (fibre facts roots heads church names realization).store s.knowledge, s.present,
    fun o => (fibre facts roots heads church names realization).tm (s.label o)⟩

/-- **The translated firing**: no helpers, the same selection, the translated patterns, made rows,
tells and guards, and no predicate queries. -/
def translateEquationFiring {s : EquationStep.State (ListObs sig) O} (f : EquationStep.Firing (ListObs sig) s) :
    Firing S.levels (translateLocal facts roots heads church names realization s) where
  helpers := .nil _
  taken := f.taken
  read := f.read
  takes := f.takes.map (fibre facts roots heads church names realization).tm
  reads := f.reads.map (fibre facts roots heads church names realization).tm
  makes := f.makes.map fun m => (m.1, Make.ofRow ((fibre facts roots heads church names realization).tm m.2))
  tells := (fibre facts roots heads church names realization).store f.tells
  guards := (fibre facts roots heads church names realization).store f.guards
  queries := []

variable {s : EquationStep.State (ListObs sig) O} (f : EquationStep.Firing (ListObs sig) s)

omit [DecidableEq O] in
theorem translateEquation_row (o : O) :
    (translateEquationFiring facts roots heads church names realization f).row o =
      (fibre facts roots heads church names realization).tm (s.label o) :=
  (frames S.levels).act_id _

omit [DecidableEq O] in
theorem map_fst_second {α β γ : Type*} (g : β → γ) :
    ∀ l : List (α × β), (l.map fun m => (m.1, g m.2)).map Prod.fst = l.map Prod.fst
  | [] => rfl
  | m :: rest => congrArg (m.1 :: ·) (map_fst_second g rest)

omit [DecidableEq O] in
theorem translateEquation_made :
    (translateEquationFiring facts roots heads church names realization f).made = f.made :=
  map_fst_second (fun t => Make.ofRow ((fibre facts roots heads church names realization).tm t)) f.makes

omit [DecidableEq O] in
theorem translateEquation_selection :
    (translateEquationFiring facts roots heads church names realization f).selection = f.selection := by
  show (⟨f.taken, f.read, _⟩ : Selection O) = ⟨f.taken, f.read, f.made⟩
  rw [translateEquation_made]

omit [DecidableEq O] in
theorem zip_map_store {T T' : Type*} (g : T → T') (lab : O → T) :
    ∀ (ps : List T) (sel : List O),
      ((ps.map g).zip sel).map (fun x => (x.1, g (lab x.2))) =
        ((ps.zip sel).map fun x => (x.1, lab x.2)).map (fun e => (g e.1, g e.2))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: ps, _ :: sel => congrArg (_ :: ·) (zip_map_store g lab ps sel)

omit [DecidableEq O] in
theorem translateEquation_matching (patterns : List (ListObs sig s.frame)) (selected : List O) :
    (translateEquationFiring facts roots heads church names realization f).matching
        (patterns.map (fibre facts roots heads church names realization).tm) selected =
      (fibre facts roots heads church names realization).store (s.matching patterns selected) := by
  unfold Firing.matching
  rw [show (translateEquationFiring facts roots heads church names realization f).row =
      fun o => (fibre facts roots heads church names realization).tm (s.label o) from
    funext (translateEquation_row facts roots heads church names realization f)]
  exact zip_map_store _ s.label patterns selected

omit [DecidableEq O] in
/-- **The information of a translated firing is the translation of its information.** -/
theorem translateEquation_information :
    (translateEquationFiring facts roots heads church names realization f).information =
      (fibre facts roots heads church names realization).store (f.information (listFrames sig)) := by
  have takes : (translateEquationFiring facts roots heads church names realization f).matching
      (translateEquationFiring facts roots heads church names realization f).takes
      (translateEquationFiring facts roots heads church names realization f).taken =
      (fibre facts roots heads church names realization).store (s.matching f.takes f.taken) :=
    translateEquation_matching facts roots heads church names realization f f.takes f.taken
  have reads : (translateEquationFiring facts roots heads church names realization f).matching
      (translateEquationFiring facts roots heads church names realization f).reads
      (translateEquationFiring facts roots heads church names realization f).read =
      (fibre facts roots heads church names realization).store (s.matching f.reads f.read) :=
    translateEquation_matching facts roots heads church names realization f f.reads f.read
  have knowledge : (frames S.levels).applyStore
      (translateEquationFiring facts roots heads church names realization f).helpers.weaken
      (translateLocal facts roots heads church names realization s).knowledge =
      (fibre facts roots heads church names realization).store s.knowledge :=
    Frames.applyStore_id (X := frames S.levels) _
  have source : (listFrames sig).applyStore ((listFrames sig).id s.frame) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := listFrames sig) _
  unfold Firing.information EquationStep.Firing.information
  rw [takes, reads, knowledge, source]
  simp only [FrameMap.store, List.map_append]
  rfl

/-- **Admission is preserved and reflected**, wherever the unifier decides the information in the
fibre: answers may land at any translated telescope. -/
theorem translateEquation_admits_iff
    (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
    (rigid : ∀ name, S.roles name = .rigid) (sortInjective : Function.Injective names.sort)
    (closed : ClosedRealization (S := S) names)
    (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))
    (decided : DecidedInFibre facts roots heads church names realization
      ((EquationStep.step (listFrames sig) O).information f)) :
    (EquationStep.step (listFrames sig) O).Admits f ↔
      (step S.levels O).Admits (translateEquationFiring facts roots heads church names realization f) := by
  rw [fibre_admission_transfer facts roots heads algebra complete rigid church names realization sortInjective
    closed @operatorInjective (EquationStep.step (listFrames sig) O).toStep (fun f => f.guards) (fun _ _ _ => Iff.rfl)
    f decided, admits_iff, translateEquation_information, translateEquation_made]
  show f.Shapes ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧ _ ↔ _
  rw [EquationStep.enabled_iff]
  constructor
  · rintro ⟨⟨taken, made, takes, reads⟩, enabled, solvable, guards⟩
    refine ⟨⟨taken, (translateEquation_made facts roots heads church names realization f).symm ▸ made,
      (List.length_map _).trans takes, (List.length_map _).trans reads, fun m member => ?_⟩,
      enabled, solvable, guards, fun q member => absurd member List.not_mem_nil⟩
    obtain ⟨m', -, rfl⟩ := List.mem_map.mp member
    exact Make.ofRow_wellTyped _
  · rintro ⟨⟨taken, made, takes, reads, -⟩, enabled, solvable, guards, -⟩
    exact ⟨⟨taken, (translateEquation_made facts roots heads church names realization f) ▸ made,
      (List.length_map _).symm.trans takes, (List.length_map _).symm.trans reads⟩, enabled, solvable, guards⟩

theorem relabel_translate_rows (label : O → ListObs sig s.frame) :
    ∀ (makes : List (O × ListObs sig s.frame))
      (typed : ∀ m ∈ makes.map (fun m => (m.1, Make.ofRow ((fibre facts roots heads church names realization).tm m.2))),
        m.2.WellTyped) (o : O),
      relabel (fun o => (fibre facts roots heads church names realization).tm (label o))
          (makes.map fun m => (m.1, Make.ofRow ((fibre facts roots heads church names realization).tm m.2))) typed o =
        (fibre facts roots heads church names realization).tm (EquationStep.relabelRows label makes o)
  | [], _, _ => rfl
  | m :: rest, typed, o => by
      by_cases same : o = m.1
      · simp only [List.map_cons, relabel, EquationStep.relabelRows, if_pos same]
        rfl
      · simp only [List.map_cons, relabel, EquationStep.relabelRows, if_neg same]
        exact relabel_translate_rows label rest _ o

/-- **Results correspond**: the dependent result of a translated firing is the translated result. -/
theorem translateEquation_result (admitted : (EquationStep.step (listFrames sig) O).Admits f)
    (admitted' : (step S.levels O).Admits (translateEquationFiring facts roots heads church names realization f)) :
    (step S.levels O).result (translateEquationFiring facts roots heads church names realization f) admitted' =
      translateLocal facts roots heads church names realization
        ((EquationStep.step (listFrames sig) O).result f admitted) := by
  show State.mk _ (translateEquationFiring facts roots heads church names realization f).information
      (fire s.present ((translateEquationFiring facts roots heads church names realization f).selection.commit
        (T := Unit)))
      (relabel _ _ admitted'.1.2.2.2.2) =
    State.mk _ ((fibre facts roots heads church names realization).store
        ((listFrames sig).applyStore ((listFrames sig).id s.frame) (f.information (listFrames sig))))
      (fire s.present (f.selection.commit (T := Unit)))
      (fun o => (fibre facts roots heads church names realization).tm (EquationStep.relabelRows s.label f.makes o))
  have labels : relabel (translateEquationFiring facts roots heads church names realization f).row
      (translateEquationFiring facts roots heads church names realization f).makes admitted'.1.2.2.2.2 =
      fun o => (fibre facts roots heads church names realization).tm (EquationStep.relabelRows s.label f.makes o) := by
    funext o
    rw [show (translateEquationFiring facts roots heads church names realization f).row =
        fun o => (fibre facts roots heads church names realization).tm (s.label o) from
      funext (translateEquation_row facts roots heads church names realization f)]
    exact relabel_translate_rows facts roots heads church names realization s.label f.makes _ o
  rw [labels, Frames.applyStore_id (X := listFrames sig), translateEquation_information,
    translateEquation_selection]
  rfl

section Full

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **Where the full solver decides, the translation preserves and reflects admission.** -/
theorem translateEquation_admits_iff_of_full
    (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
    (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
    (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
    (root : ExecutableReduction.RootEvaluator S.R)
    (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
      ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
        Equal S.R Θ.raw term.code code type.code)
    (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
      Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
    (headTypingUnique : ∀ {head first second : Head},
      S.R.headTyping head first → S.R.headTyping head second → first = second)
    (sortInjective : Function.Injective names.sort) (closed : ClosedRealization (S := S) names)
    (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))
    (rounds fuel : Nat)
    (decided : (ContextualDependentWorklist.run (ContextualDependentPatternSolver.fullSolver rigid facts complete roots
      heads algebra declared choices reducer root normalizes certifyNormal headTypingUnique rounds)
      ((fibre facts roots heads church names realization).store
        ((EquationStep.step (listFrames sig) O).information f)) fuel).Decided) :
    (EquationStep.step (listFrames sig) O).Admits f ↔
      (step S.levels O).Admits (translateEquationFiring facts roots heads church names realization f) :=
  translateEquation_admits_iff facts roots heads church names realization f algebra complete rigid sortInjective
    closed @operatorInjective
    (decidedInFibre_of_full facts roots heads church names realization rigid complete algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique _ rounds fuel decided)

end Full

end Instance

end DependentFull

#print axioms DependentFull.translateEquation_information
#print axioms DependentFull.translateEquation_admits_iff
#print axioms DependentFull.relabel_translate_rows
#print axioms DependentFull.translateEquation_result
#print axioms DependentFull.translateEquation_admits_iff_of_full

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
