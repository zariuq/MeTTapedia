import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeInstance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionSplitting

/-!
# Telling disequations on any instance, for firings without guards

`Prestep.withDisequations` needs a result determined by the firing's shapes. An instance whose
result needs its own admission, such as the native step, whose result is pinned by an execution that
asks its checks at every solution, has no result for a firing admitted only at separating solutions.

**The bridge for such instances** (`Unguarded.withDisequations`): restrict to firings whose guards
and predicate queries hold at every solution (`DFiring.unguarded`). For those, admission with
disequations implies the instance's own admission (`DFiring.admits_base`), so the instance's result
exists; it carries the disequations along the settlement, which must reflect the equivalence
(`SettleReflects`). This is an instance of `Interface.Step` over disequation frames
(`admits_iff_separating`, `refused_of_identified`, `conservative`).

**The native step qualifies** (`native_settle_reflects`): its settlement is the inclusion of the
information frame into the solver's active frame, an injective extension of declarations, so
instantiation along it is injective (`ContextualGuardMatching.Extension.instantiate_injective`).
A native firing whose rule has no checks and which asks no predicate queries is unguarded
(`native_unguarded`). So native firings without guards can tell disequations
(`nativeWithDisequations`). Guarded native firings with disequations need an execution that asks its
checks at separating solutions only; that is open.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames.Unguarded

open Interface (Frames)
open Disequality (DisequationStore)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)

/-- A state with disequations at its frame, separated by the identity. -/
structure DState where
  state : State
  disequations : DisequationStore (Tm (P.frame state))
  separated : Separates X (X.id (P.frame state)) disequations

variable {P}

def DState.frame (s : DState P) : Frame X := ⟨P.frame s.state, s.disequations, s.separated⟩

variable (P) in
/-- The state's disequations at a firing's target. -/
def carried (s : DState P) (f : Firing s.state) : DisequationStore (Tm (P.target f)) :=
  X.applyStore (P.extension f) s.disequations

variable (P) in
/-- **A firing without guards with disequations**: its guards and predicate queries hold at every
solution, and its told disequations form a frame with the carried ones. -/
structure DFiring (s : DState P) where
  base : Firing s.state
  tells : DisequationStore (Tm (P.target base))
  formed : Separates X (X.id (P.target base)) (carried P s base ++ tells)
  unguarded : ∀ (b : Obj) (g : Hom (P.target base) b), P.Holds base b g

namespace DFiring

variable {s : DState P} (f : DFiring P s)

def target : Frame X := ⟨P.target f.base, carried P s f.base ++ f.tells, f.formed⟩

def extension : Morphism X s.frame f.target :=
  ⟨P.extension f.base, fun _ τ separated =>
    (separates_applyStore (P.extension f.base) τ s.disequations).mp (separates_append.mp separated).1⟩

/-- Admission with disequations. -/
def Admits : Prop :=
  P.Shapes f.base ∧ Enabled (fun _ : O => ()) (P.present s.state) ((P.selection f.base).commit (T := Unit)) ∧
    (frames X).Solvable (a := f.target) (P.information f.base) ∧
    (frames X).Entails (a := f.target) (P.information f.base) (fun B g => P.Holds f.base B.obj g.1)

/-- **Admission with disequations implies the instance's admission**, for a firing without guards. -/
theorem admits_base {f : DFiring P s} (admitted : f.Admits) : P.Admits f.base :=
  (P.admits_iff f.base).mpr ⟨admitted.1, admitted.2.1, solvable_base admitted.2.2.1,
    fun b g _ => f.unguarded b g⟩

end DFiring

variable (P) in
/-- **The settlement of admitted firings reflects the equivalence.** -/
def SettleReflects : Prop :=
  ∀ {s : State} (f : Firing s) (admitted : P.Admits f) {u v : Tm (P.target f)},
    X.E (X.act (P.settle f admitted) u) (X.act (P.settle f admitted) v) → X.E u v

/-- The state after a firing without guards with disequations. -/
def DFiring.after (reflects : SettleReflects P) {s : DState P} (f : DFiring P s) (admitted : f.Admits) :
    DState P :=
  ⟨P.result f.base (DFiring.admits_base admitted),
    X.applyStore (P.settle f.base (DFiring.admits_base admitted)) (carried P s f.base ++ f.tells),
    (separates_applyStore _ _ _).mpr ((separates_congr (fun t => by rw [X.act_comp, X.act_id]) _).mpr
      (separates_of_reflects (reflects f.base (DFiring.admits_base admitted)) f.formed))⟩

variable (P) in
/-- **The instance with disequations, on firings without guards.** -/
def withDisequations (reflects : SettleReflects P) : Interface.Step (frames X) O (DState P) (DFiring P) where
  frame s := s.frame
  knowledge s := P.knowledge s.state
  present s := P.present s.state
  selection f := P.selection f.base
  target f := f.target
  extension f := f.extension
  information f := P.information f.base
  transported f e member := P.transported f.base e member
  Shapes f := P.Shapes f.base
  Holds f B g := P.Holds f.base B.obj g.1
  Admits f := f.Admits
  admits_iff _ := Iff.rfl
  result f admitted := f.after reflects admitted
  present_result f admitted := P.present_result f.base (DFiring.admits_base admitted)
  settle f admitted := ⟨P.settle f.base (DFiring.admits_base admitted), fun _ τ separated =>
    (separates_applyStore (P.settle f.base (DFiring.admits_base admitted)) τ _).mp separated⟩
  knowledge_result f admitted := P.knowledge_result f.base (DFiring.admits_base admitted)

variable (reflects : SettleReflects P)

/-- **Admission, unfolded**: some solution of the information separates the disequations. -/
theorem admits_iff_separating {s : DState P} (f : DFiring P s) :
    (withDisequations P reflects).Admits f ↔ P.Shapes f.base ∧
      Enabled (fun _ : O => ()) (P.present s.state) ((P.selection f.base).commit (T := Unit)) ∧
      ∃ (b : Obj) (g : Hom (P.target f.base) b),
        X.Models g (P.information f.base) ∧ Separates X g (carried P s f.base ++ f.tells) := by
  show f.Admits ↔ _
  constructor
  · rintro ⟨shapes, enabled, solvable, -⟩
    exact ⟨shapes, enabled, (solvable_iff (D := f.target) _).mp solvable⟩
  · rintro ⟨shapes, enabled, solvable⟩
    exact ⟨shapes, enabled, (solvable_iff (D := f.target) _).mpr solvable,
      (entails_iff (D := f.target) _ (P.Holds f.base)).mpr fun b g _ _ => f.unguarded b g⟩

/-- **A disequation refuses an identifying firing.** -/
theorem refused_of_identified {s : DState P} (f : DFiring P s) {d : Equation (Tm (P.target f.base))}
    (member : d ∈ carried P s f.base ++ f.tells)
    (identified : X.Entails (P.information f.base) (fun _ g => X.E (X.act g d.1) (X.act g d.2))) :
    ¬ (withDisequations P reflects).Admits f := by
  intro admitted
  obtain ⟨-, -, b, g, solved, separated⟩ := (admits_iff_separating reflects f).mp admitted
  exact separated d member (identified b g solved)

/-- **Conservative**: at a state without disequations, a silent firing is admitted exactly when its
firing of the instance is. -/
theorem conservative {s : DState P} (f : DFiring P s) (empty : s.disequations = []) (silent : f.tells = []) :
    (withDisequations P reflects).Admits f ↔ P.Admits f.base := by
  rw [admits_iff_separating, P.admits_iff f.base]
  have separated : ∀ {b : Obj} (g : Hom (P.target f.base) b), Separates X g (carried P s f.base ++ f.tells) := by
    intro b g
    show Separates X g (X.applyStore (P.extension f.base) s.disequations ++ f.tells)
    rw [empty, silent]
    exact separates_nil _
  constructor
  · rintro ⟨shapes, enabled, b, g, solved, -⟩
    exact ⟨shapes, enabled, ⟨b, g, solved⟩, fun b g _ => f.unguarded b g⟩
  · rintro ⟨shapes, enabled, ⟨b, g, solved⟩, -⟩
    exact ⟨shapes, enabled, b, g, solved, separated g⟩

end Generic

/-! ## The native step -/

section Native

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature}

/-- The inclusion of a source family into an active family, as an injective extension. -/
def inclusionExtension {V W : Type} (source : V → MetaArity S) (returned : W → MetaArity S) :
    ContextualGuardMatching.Extension source :=
  ⟨V ⊕ (W ⊕ Empty), ContextualComputedFreshFrame.active source returned, Sum.inl, Sum.inl_injective,
    fun _ => rfl⟩

/-- **The inclusion of the information frame is that extension's assignment.** -/
theorem includeSource_eq {V : Type} {source : V → MetaArity S} {problem : ContextualResidual.Problem source}
    (update : ContextualFrameUpdate.Update problem) :
    ContextualComputedFreshFrame.includeSource update = (inclusionExtension source update.declaration).assignment := by
  funext v
  show instantiate (ContextualFreshFrame.includeOld source update.declaration
      ContextualComputedFreshFrame.noDeclarations)
      (generator (ContextualComputedFreshFrame.old source) (.inl v)) = _
  rw [instantiate_generator]
  rfl

/-- **Instantiation along the inclusion is injective on observations.** -/
theorem includeSource_injective {V : Type} {source : V → MetaArity S}
    {problem : ContextualResidual.Problem source} (update : ContextualFrameUpdate.Update problem)
    {u v : Observation S source}
    (same : instantiateObservation (ContextualComputedFreshFrame.includeSource update) u =
      instantiateObservation (ContextualComputedFreshFrame.includeSource update) v) : u = v := by
  rw [includeSource_eq] at same
  obtain ⟨Γ, sort, t⟩ := u
  obtain ⟨Γ', sort', t'⟩ := v
  change (⟨Γ, sort, instantiate (inclusionExtension source update.declaration).assignment t⟩ :
      Observation S (inclusionExtension source update.declaration).declarations) =
    ⟨Γ', sort', instantiate (inclusionExtension source update.declaration).assignment t'⟩ at same
  have contexts : Γ = Γ' := congrArg Sigma.fst same
  subst contexts
  have inner := eq_of_heq (Sigma.mk.inj same).2
  have sorts : sort = sort' := congrArg Sigma.fst inner
  subst sorts
  have terms := eq_of_heq (Sigma.mk.inj inner).2
  have equal := ContextualGuardMatching.Extension.instantiate_injective _ terms
  subst equal
  rfl

variable {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **The native settlement reflects the equivalence.** -/
theorem native_settle_reflects : SettleReflects (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)) :=
  fun f realized _ _ same => includeSource_injective (f.pinned realized).firing.update same

/-- **A native firing without checks and predicate queries is unguarded.** -/
theorem native_unguarded {s : Interface.NativeState S O Γ sort} (f : Interface.NativeFiring s)
    (noChecks : f.prepared.rule.checks = []) (noQueries : f.queries = []) (b : Interface.Frames.Frame S)
    (g : Assignment s.infoFrame.arity b.arity) : Interface.native.Holds f b g :=
  ⟨fun _ member => absurd (noChecks ▸ member) List.not_mem_nil,
    fun _ member => absurd (noQueries ▸ member) List.not_mem_nil⟩

/-- **The native step with disequations, on firings without guards.** -/
noncomputable abbrev nativeWithDisequations :=
  withDisequations (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)) native_settle_reflects

end Native

#print axioms DFiring.admits_base
#print axioms admits_iff_separating
#print axioms refused_of_identified
#print axioms conservative
#print axioms includeSource_eq
#print axioms includeSource_injective
#print axioms native_settle_reflects
#print axioms native_unguarded

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames.Unguarded
