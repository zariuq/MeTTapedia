import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingActiveOrigins

/-!
# Separating controls for scoped prefix-origin tracing

Private-name extrusion cannot turn a private sender into a listener on an
ambient channel. A matching private pair does execute. Replication contraction
can discard a distinct duplicate mark, while both actual syntax endpoints
remain related by the original equation. Input-body marks remain suspended.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkingControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames

abbrev ambient : Ctx sig := [Srt.nm]

def splitChannels : Proc ambient :=
  par (nu (out1 (.var .zero) (.var (.succ .zero))))
    (inp1 (.var .zero) nil)

def splitMarks : ActiveMarking.Tree Nat :=
  .par (.nu 9 (.out1 1)) (.inp1 2 .nil)

def ambientKeys : ActiveMarkedNames.Environment Nat ambient := fun _ => 3

theorem split_marks_fit : Fits splitMarks splitChannels :=
  .par (.nu 9 (.out1 1 _ _)) (.inp1 2 _ .nil)

/-- Even arbitrary static rearrangement and replication do not turn these
physically distinct private/ambient channels into an enabled rendezvous. -/
theorem split_channels_no_step (target : Proc ambient) : ¬ StepModulo splitChannels target := by
  intro firing
  rcases step_has_observed_pair (fun key : Nat => key) 0 split_marks_fit ambientKeys firing with
    ⟨input, output, inputMember, outputMember, sameChannel, arities⟩
  simp only [splitMarks, splitChannels, observe, par, nu, inp1, out1, nameKey,
    ActiveMarkedNames.extend, ambientKeys, Set.mem_union, Set.mem_singleton_iff] at inputMember outputMember
  rcases inputMember with rfl | rfl <;> rcases outputMember with rfl | rfl
  all_goals simp_all

/-- A pair under the same actual private binder does communicate. -/
def joinedChannels : Proc ambient :=
  nu (par (out1 (.var .zero) (.var (.succ .zero))) (inp1 (.var .zero) nil))

theorem joined_channels_step : StepModulo joinedChannels (nu nil) := by
  refine ⟨joinedChannels, nu nil, .refl _, ?_, .refl _⟩
  exact .nu (.comm1 _ _ _)

/-- The extrusion proof transports the actual binder mark and ambient keys. -/
theorem extrusion_keeps_distinct_keys :
    Transport splitMarks splitChannels (.nu 9 (.par (.out1 1) (.inp1 2 .nil)))
      (nu (par (out1 (.var .zero) (.var (.succ .zero))) (weaken (inp1 (.var .zero) nil)))) :=
  .nuPar 9 _ _ _ _

def repeatedListener : Proc ambient := inp1 (.var .zero) nil

def distinctCopies : ActiveMarking.Tree Nat := .par (.inp1 11 .nil) (.rep (.inp1 22 .nil))

theorem distinct_copies_fit : Fits distinctCopies (par repeatedListener (rep repeatedListener)) :=
  .par (.inp1 11 _ .nil) (.rep (.inp1 22 _ .nil))

/-- Static contraction may forget the origin of the separately supplied
one-shot listener; the persistent server's origin remains available. -/
theorem different_origins_contract :
    Transport distinctCopies (par repeatedListener (rep repeatedListener))
      (.rep (.inp1 22 .nil)) (rep repeatedListener) := .repFold _ _ _

def oneShotSelection : Selection .input1 11 distinctCopies := .left _ (.inp1 11 .nil)

theorem contracted_origin_is_absent : ¬ Nonempty (Selection .input1 11 (.rep (.inp1 22 (.nil : ActiveMarking.Tree Nat)))) := by
  rintro ⟨selected⟩
  cases selected with
  | rep selected => cases selected

theorem no_bijective_active_origin_transport :
    Nonempty (Selection .input1 11 distinctCopies) ∧
      ¬ Nonempty (Selection .input1 11 (.rep (.inp1 22 (.nil : ActiveMarking.Tree Nat)))) :=
  ⟨⟨oneShotSelection⟩, contracted_origin_is_absent⟩

/-- A mark beneath an input is suspended, despite belonging to its actual body. -/
theorem guarded_output_is_not_active :
    ¬ Nonempty (Selection .output1 7 (.inp1 3 (.out1 7 : ActiveMarking.Tree Nat))) := by
  rintro ⟨selected⟩
  cases selected

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkingControls
