import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Dispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullJoinFull

/-!
# The second-order fibre is licensed where the dependent unifier is decisive

The map `fibre` carries the second-order frames into the dependent unifier's typed βη frames. The
joins proved for it run downward: the dependent unifier decides, and its answer is read in the
fibre. This file turns that downward reading into the upward license, **under an explicit
decisiveness hypothesis**: the dependent unifier decides the translated store in the fibre
(`DecidedInFibre`), either given directly or obtained from a run of the full solver
(`decidedInFibre_of_full`). Decisiveness of the dependent unifier on translated stores is open; it
is assumed here as a hypothesis of each theorem and nowhere else.

* **The top's decision covers** (`fibre_coversAt_of_decidedInFibre`): a principal answer of the
  unifier landing in a translated frame is, up to typed equality, the translation of a second-order
  solution, and that translation is principal (`fibre_answer_in_fibre`, which uses that principal
  answers are determined by their action up to the equivalence); a refutation covers vacuously.
* **`licensed_of_top_decisive`**: on every class of stores where the unifier decides the
  translations, the fibre is licensed; `licensed_of_full_decisive` takes the decisions from runs of
  the full solver.
* **Dispatch at the step** (`dispatch_admits_iff_of_top_decisive`): for any step over the unifier's
  frames, at a firing dispatched along the fibre whose translated problem the unifier decides,
  admission is the second-order solvability and ask. The expensive decisiveness is the proof
  device; the second-order answer is the runtime path.
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
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
  (rigid : ∀ name, S.roles name = .rigid) (church : ConversionCoherence.ChurchRosser S.R)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)
  (sortInjective : Function.Injective names.sort)
  (closed : ClosedRealization (S := S) names)
  (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))

include algebra complete rigid sortInjective closed operatorInjective in
/-- **The top's decision covers.** -/
theorem fibre_coversAt_of_decidedInFibre {M : List (Binding.MetaArity sig)}
    {K : EquationStore (Binding.ContextualFamily.Observation sig M.get)}
    (decided : DecidedInFibre facts roots heads church names realization K) :
    (fibre facts roots heads church names realization).CoversAt K := by
  rcases decided with ⟨N, τ, principal⟩ | refuted
  · obtain ⟨σ, -, dependent, second⟩ := fibre_answer_in_fibre facts roots heads algebra complete rigid
      church names realization sortInjective closed @operatorInjective principal
    exact FrameMap.coversAt_of_principal second.sound dependent
  · exact FrameMap.coversAt_of_refuted refuted

include algebra complete rigid sortInjective closed operatorInjective in
/-- **The top's decision licenses.** -/
theorem fibre_licensedAt_of_decidedInFibre {M : List (Binding.MetaArity sig)}
    {K : EquationStore (Binding.ContextualFamily.Observation sig M.get)}
    (decided : DecidedInFibre facts roots heads church names realization K) :
    (fibre facts roots heads church names realization).LicensedAt K :=
  (fibre_coversAt_of_decidedInFibre facts roots heads algebra complete rigid church names realization
    sortInjective closed @operatorInjective decided).licensedAt

include algebra complete rigid sortInjective closed operatorInjective in
/-- **`licensed_of_top_decisive`**: the fibre is licensed on every class of stores whose
translations the dependent unifier decides in the fibre. The decisiveness is the hypothesis. -/
theorem licensed_of_top_decisive
    {D : (M : List (Binding.MetaArity sig)) →
      EquationStore (Binding.ContextualFamily.Observation sig M.get) → Prop}
    (decisive : ∀ M K, D M K → DecidedInFibre facts roots heads church names realization K) :
    (fibre facts roots heads church names realization).LicensedOn D :=
  fun M K inside => fibre_licensedAt_of_decidedInFibre facts roots heads algebra complete rigid church
    names realization sortInjective closed @operatorInjective (decisive M K inside)

include algebra complete rigid sortInjective closed operatorInjective in
/-- **Dispatch to the second-order fibre where the unifier is decisive.** For any step over the
unifier's frames, at a firing dispatched along the fibre whose translated problem the unifier
decides in the fibre, admission is the second-order solvability and ask of the guards. -/
theorem dispatch_admits_iff_of_top_decisive {O : Type} [DecidableEq O] {State : Type}
    {Firing : State → Type} (P : Step (ContextualDependentEta.frames S.levels) O State Firing) [P.Guarded]
    {s : State} {f : Firing s} (d : (fibre facts roots heads church names realization).Dispatched P f)
    (decided : DecidedInFibre facts roots heads church names realization d.problem) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      (listFrames sig).Solvable d.problem ∧
      (listFrames sig).Entails d.problem (fun _ g => (listFrames sig).Models g d.guards) :=
  FrameMap.dispatch_admits_iff_of_coversAt
    (fibre_reflects facts roots heads algebra complete rigid church names realization sortInjective
      @operatorInjective) P d
    (fibre_coversAt_of_decidedInFibre facts roots heads algebra complete rigid church names realization
      sortInjective closed @operatorInjective decided)

section Full

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include algebra complete rigid sortInjective closed operatorInjective in
/-- **The license from runs of the full solver**: on every class of stores whose translations some
run of the full solver decides, the fibre is licensed. The decisiveness is the hypothesis. -/
theorem licensed_of_full_decisive
    {D : (M : List (Binding.MetaArity sig)) →
      EquationStore (Binding.ContextualFamily.Observation sig M.get) → Prop}
    (decisive : ∀ M K, D M K → ∃ rounds fuel : Nat,
      (ContextualDependentWorklist.run (ContextualDependentPatternSolver.fullSolver rigid facts complete roots
        heads algebra declared choices reducer root normalizes certifyNormal headTypingUnique rounds)
        ((fibre facts roots heads church names realization).store K) fuel).Decided) :
    (fibre facts roots heads church names realization).LicensedOn D := by
  refine licensed_of_top_decisive facts roots heads algebra complete rigid church names realization
    sortInjective closed @operatorInjective fun M K inside => ?_
  obtain ⟨rounds, fuel, decided⟩ := decisive M K inside
  exact decidedInFibre_of_full (facts := facts) (roots := roots) (heads := heads) (church := church)
    (names := names) (realization := realization) (rigid := rigid) (complete := complete)
    (algebra := algebra) (declared := declared) (choices := choices) (reducer := reducer) (root := root)
    (normalizes := normalizes) (certifyNormal := certifyNormal) (headTypingUnique := headTypingUnique)
    K rounds fuel decided

end Full

end DependentFull

#print axioms DependentFull.fibre_coversAt_of_decidedInFibre
#print axioms DependentFull.fibre_licensedAt_of_decidedInFibre
#print axioms DependentFull.licensed_of_top_decisive
#print axioms DependentFull.dispatch_admits_iff_of_top_decisive
#print axioms DependentFull.licensed_of_full_decisive

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
