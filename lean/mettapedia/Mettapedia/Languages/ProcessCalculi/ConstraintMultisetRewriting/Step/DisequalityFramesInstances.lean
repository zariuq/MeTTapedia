import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullIndependence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualDiamond

/-!
# Disequations at dependent frames and at declaration frames

**The dependent full step is a prestep** (`Dependent.prestep`): its result keeps the information at
the extended frame and relabels the made occurrences by their checked rows, which needs only the
shapes. Its step is `DependentFull.step`, with the same admission (`Dependent.prestep_admits_iff`)
and the same result (`Dependent.prestep_result`). Its settlement is the identity
(`Dependent.reflects`), so it carries disequations: `Dependent.withDisequations` is the dependent
full step over disequation frames of `ContextualDependentEta.frames`. A firing there tells
disequations of typed terms at its extended frame, and is admitted when some solution of its
information separates them.

**The helper step at declaration frames is a prestep** (`Contextual.prestep`): `Helpers.helperStep`
of `ContextualDiamond`, with the same admission and result (`Contextual.prestep_admits_iff`,
`Contextual.prestep_result`). `Contextual.withDisequations` is the helper step over disequation frames
of `Frames.contextual S`.

**A firing that tells nothing** along an extension that reflects the equivalence is a firing with
disequations at every state (`Interface.Step.DFiring.silent`). A dependent firing without helpers moves
along the identity, which does (`Dependent.toFiring_reflects`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames

open Interface (Frames)
open Disequality (DisequationStore)

/-! ## The dependent full step -/

namespace Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open Interface.DependentFull
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  (levels : LevelModel rules L) (O : Type) [DecidableEq O]

/-- **The dependent full step as a prestep**: its result is computed from the firing's data and its
shapes. -/
def prestep : Prestep (ContextualDependentEta.frames levels) O (State rules O) (Firing levels) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := f.helpers.frame
  extension f := f.helpers.weaken
  information f := f.information
  transported {s} f e member := (step levels O).transported (s := s) f e member
  Shapes f := f.Shapes
  Holds f _ τ := f.Holds τ
  result {s} f shapes := ⟨f.helpers.frame, f.information, fire s.present (f.selection.commit (T := Unit)),
    relabel f.row f.makes shapes.2.2.2.2⟩
  present_result _ _ := rfl
  settle f _ := (ContextualDependentEta.frames levels).id f.helpers.frame
  knowledge_result f _ := (Frames.applyStore_id (X := ContextualDependentEta.frames levels) f.information).symm

/-- **Its step is the dependent full step**: the same admission. -/
theorem prestep_admits_iff {s : State rules O} (f : Firing levels s) :
    (prestep levels O).step.Admits f ↔ (step levels O).Admits f :=
  Iff.rfl

/-- And the same result. -/
theorem prestep_result {s : State rules O} (f : Firing levels s) (admitted : (prestep levels O).step.Admits f) :
    (prestep levels O).step.result f admitted = (step levels O).result f admitted :=
  rfl

/-- Its settlement is the identity. -/
theorem reflects : (prestep levels O).step.Reflects :=
  fun _ _ _ _ same => id_reflects (X := ContextualDependentEta.frames levels) same

/-- **The dependent full step with disequations.** -/
abbrev withDisequations := (prestep levels O).step.withDisequations (reflects levels O)

variable {levels O}

/-- A firing without helpers moves along the identity, which reflects the equivalence. -/
theorem toFiring_reflects {s : State rules O} (f : Plain levels O s.frame) {u v : TotalTerm s.frame}
    (same : (ContextualDependentEta.frames levels).E
      ((ContextualDependentEta.frames levels).act ((prestep levels O).extension (Plain.toFiring f)) u)
      ((ContextualDependentEta.frames levels).act ((prestep levels O).extension (Plain.toFiring f)) v)) :
    (ContextualDependentEta.frames levels).E u v :=
  id_reflects (X := ContextualDependentEta.frames levels) same

end Dependent

/-! ## The helper step at declaration frames -/

namespace Contextual

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Helpers (helperStep)

variable {S : Signature} {O : Type} [DecidableEq O]

variable (S O) in
/-- **The helper step as a prestep**: its result is computed from the firing's data. -/
def prestep : Prestep (Frames.contextual S) O (Interface.Helpers.State S O) Interface.Helpers.Firing where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := Interface.Helpers.extend _ f.helper
  extension f := Interface.Helpers.incl _ f.helper
  information f := f.information
  transported {s} f e member := helperStep.transported (s := s) f e member
  Shapes f := f.selection.made.Nodup
  Holds {s} f b σ := helperStep.Holds (s := s) f b σ
  result f _ := f.after
  present_result _ _ := rfl
  settle f _ := (Frames.contextual S).id (Interface.Helpers.extend _ f.helper)
  knowledge_result f _ := (Frames.applyStore_id (X := Frames.contextual S) f.information).symm

/-- **Its step is the helper step**: the same admission. -/
theorem prestep_admits_iff {s : Interface.Helpers.State S O} (f : Interface.Helpers.Firing s) :
    (prestep S O).step.Admits f ↔ helperStep.Admits f :=
  Iff.rfl

/-- And the same result. -/
theorem prestep_result {s : Interface.Helpers.State S O} (f : Interface.Helpers.Firing s)
    (admitted : (prestep S O).step.Admits f) :
    (prestep S O).step.result f admitted = helperStep.result f admitted :=
  rfl

variable (S O) in
/-- Its settlement is the identity. -/
theorem reflects : (prestep S O).step.Reflects :=
  fun _ _ _ _ same => id_reflects (X := Frames.contextual S) same

variable (S O) in
/-- **The helper step with disequations**, over disequation frames of declaration frames. -/
abbrev withDisequations := (prestep S O).step.withDisequations (reflects S O)

end Contextual

#print axioms Dependent.prestep_admits_iff
#print axioms Dependent.prestep_result
#print axioms Dependent.reflects
#print axioms Dependent.toFiring_reflects
#print axioms Contextual.prestep_admits_iff
#print axioms Contextual.prestep_result
#print axioms Contextual.reflects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames
