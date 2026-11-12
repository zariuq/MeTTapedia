import Mettapedia.TypeTheory.ContextualTypedPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeUniverseFrames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PrincipalAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.ExactTransitions
import Mathlib.Data.Fintype.Card

/-!
# Publication in the actual set-family model

The source contains a size n and an index i : Fin n. Learning n = k licenses
the same index at Fin k. The answer retains all k possible indices rather
than choosing one. At k = zero the solution context is empty: symbolic
solvability still exists, while closed realization does not.

This is an extensional model interpretation, not a conversion rule added to
the intensional syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SetControls

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypedPublication

abbrev model := familiesCwf.{0}
abbrev frame := NativeUniverse.cwfFrames model
abbrev Context := Σ size : Nat, Fin size

/-- This actual model observes points through a context-valued term.
Consequently values-only agreement here determines the whole substitution. -/
theorem substitutions_eq_of_agree {source target : Type} {first second : source → target}
    (agree : UnificationWithLevels.Agree frame first second) : first = second := by
  let pointRow : NativeUniverse.Judged model target := ⟨fun _ => target, id⟩
  exact eq_of_heq (Sigma.mk.inj (agree pointRow)).2

theorem view_at_agreement {source target : Type} (output : View model target)
    {first second : source → target} (agree : UnificationWithLevels.Agree frame first second) :
    output.At first ↔ output.At second := by
  cases substitutions_eq_of_agree agree
  rfl

/-- The same principal-answer contract as the syntactic publication route,
with the model-specific observation law actually discharged. -/
theorem view_at_principal_iff {source target : Type} (output : View model source)
    {problem : EquationStore (NativeUniverse.Judged model source)} {answer : target → source}
    (principal : frame.Principal problem answer) :
    frame.Entails problem (fun _ substitution => output.At substitution) ↔ output.At answer :=
  principal.entails_iff (fun _ _ _ agree => view_at_agreement output agree)
    (fun _ further licensed => output.at_precompose licensed further)

theorem view_uniform_iff_residual {source target : Type} (output : View model source)
    {problem : EquationStore (NativeUniverse.Judged model source)} {answer : target → source}
    {remaining : EquationStore (NativeUniverse.Judged model target)}
    (exact : UnificationWithLevels.Exact frame problem answer remaining) :
    frame.Entails problem (fun _ substitution => output.At substitution) ↔
      frame.Entails remaining (fun _ further => (output.reindex answer).At further) := by
  constructor
  · intro original observer further solved
    exact (output.at_reindex_iff answer further).mpr
      (original observer (fun point => answer (further point))
        ((exact observer _).mpr ⟨further, UnificationWithLevels.Agree.refl _, solved⟩))
  · intro residual observer substitution solved
    obtain ⟨further, agree, valid⟩ := (exact observer substitution).mp solved
    exact (view_at_agreement output agree).mpr
      ((output.at_reindex_iff answer further).mp (residual observer further valid))

def sizeRow : NativeUniverse.Judged model Context := ⟨fun _ => Nat, fun point => point.1⟩

def sizeConstant (size : Nat) : NativeUniverse.Judged model Context := ⟨fun _ => Nat, fun _ => size⟩

def information (size : Nat) : EquationStore (NativeUniverse.Judged model Context) :=
  [(sizeRow, sizeConstant size)]

def view (size : Nat) : View model Context :=
  ⟨(fun point => Fin point.1), (fun point => point.2), (fun _ => Fin size)⟩

theorem models_iff {observer : Type} (size : Nat) (substitution : observer → Context) :
    frame.Models substitution (information size) ↔ ∀ point, (substitution point).1 = size := by
  constructor
  · intro models point
    have same := models (sizeRow, sizeConstant size) (List.mem_singleton_self _)
    have functions : (fun x => (substitution x).1) = (fun _ => size) :=
      eq_of_heq (Sigma.mk.inj same).2
    exact congrFun functions point
  · intro sizes equation member
    obtain rfl := List.mem_singleton.mp member
    change (⟨fun _ : observer => Nat, fun point => (substitution point).1⟩ : NativeUniverse.Judged model observer) =
      ⟨fun _ => Nat, fun _ => size⟩
    exact congrArg (fun value : observer → Nat =>
      (⟨fun _ => Nat, value⟩ : NativeUniverse.Judged model observer)) (funext sizes)

theorem source_license {observer : Type} (size : Nat) (substitution : observer → Context)
    (models : frame.Models substitution (information size)) : (view size).At substitution := by
  funext point
  change Fin (substitution point).1 = Fin size
  rw [(models_iff size substitution).mp models point]

def answer (size : Nat) : Fin size → Context := fun index => ⟨size, index⟩

theorem answer_solves (size : Nat) : frame.Models (answer size) (information size) :=
  (models_iff size _).mpr (fun _ => rfl)

def factor {observer : Type} (size : Nat) (substitution : observer → Context)
    (models : frame.Models substitution (information size)) : observer → Fin size :=
  fun point => Fin.cast ((models_iff size substitution).mp models point) (substitution point).2

theorem factor_point (size : Nat) (point : Context) (same : point.1 = size) :
    answer size (Fin.cast same point.2) = point := by
  rcases point with ⟨n, index⟩
  change n = size at same
  subst n
  rfl

theorem factor_exact {observer : Type} (size : Nat) (substitution : observer → Context)
    (models : frame.Models substitution (information size)) :
    (fun point => answer size (factor size substitution models point)) = substitution := by
  funext point
  exact factor_point size _ _

/-- A genuine principal family: the answer frame is Fin size, not a single
chosen witness, and every source assignment factors through it. -/
theorem principal (size : Nat) : frame.Principal (information size) (answer size) := by
  refine ⟨answer_solves size, ?_⟩
  intro observer substitution models
  refine ⟨factor size substitution models, ?_⟩
  have exact := factor_exact size substitution models
  intro term
  change frame.act substitution term = frame.act (fun point => answer size (factor size substitution models point)) term
  rw [exact]

theorem uniform_size_view_from_answer (size : Nat) :
    frame.Entails (information size) (fun _ substitution => (view size).At substitution) :=
  (view_at_principal_iff (view size) (principal size)).mpr
    (source_license size (answer size) (answer_solves size))

theorem all_indices_retained (size : Nat) (index : Fin size) :
    (view size).realize (answer size) (source_license size _ (answer_solves size)) index = index := rfl

theorem three_indices_not_collapsed :
    answer 3 ⟨0, by decide⟩ ≠ answer 3 ⟨2, by decide⟩ := by
  intro same
  have indices := congrArg (fun point : Context => point.2.val) same
  cases indices

theorem not_licensed_before_matching : ¬ (view 3).At (fun point : Context => point) := by
  intro licensed
  have types : Fin 1 = Fin 3 := congrFun licensed (⟨1, ⟨0, by decide⟩⟩ : Context)
  have cards := Fintype.card_congr (Equiv.cast types)
  simp only [Fintype.card_fin] at cards
  cases cards

theorem zero_is_symbolically_solvable : frame.Solvable (information 0) :=
  ⟨Fin 0, answer 0, answer_solves 0⟩

theorem zero_has_no_closed_realization :
    ¬ ∃ substitution : Unit → Context, frame.Models substitution (information 0) := by
  rintro ⟨substitution, models⟩
  exact Fin.elim0 (factor 0 substitution models ())

theorem repeated_readout {observer : Type} (size : Nat) (indices : observer → Fin size) :
    ((view size).reindex (answer size)).readout indices
        (((view size).at_reindex_iff (answer size) indices).mpr
          ((view size).at_precompose (source_license size _ (answer_solves size)) indices)) =
      (view size).readout (fun point => answer size (indices point))
        ((view size).at_precompose (source_license size _ (answer_solves size)) indices) :=
  (view size).readout_reindex (answer size) indices _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SetControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SetControls.principal
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SetControls.zero_has_no_closed_realization
