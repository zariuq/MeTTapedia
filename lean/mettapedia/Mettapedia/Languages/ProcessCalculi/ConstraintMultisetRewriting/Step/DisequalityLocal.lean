import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesStep

/-!
# Disequations preserved by the actual prepared settlement

Global reflection is a sufficient certificate. `LocalCompatible` asks only
that the inequalities carried or told by this firing survive its settlement.
The result carries their images, so later substitutions still respect them.

The local condition is a structural condition on a lifted firing. It never
requires the base guard to hold. `withLocalDisequations` is a genuine `Step`;
the existing global construction is recovered with identical admitted results.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step

open DisequalityFrames (frames Separates separates_applyStore separates_congr
  separates_of_reflects separates_nil solvable_base solvable_iff entails_iff)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)

/-- Preserve the inequalities actually present at the firing's target.
Preparation evidence is proposition-valued in this interface. -/
def LocalCompatible {s : P.DState} (f : P.DFiring s) : Prop :=
  ∀ p : P.Prepares f.base,
    Separates X (P.preparedSettle f.base p) (P.carried s f.base ++ f.tells)

theorem localCompatible_iff {s : P.DState} (f : P.DFiring s) (p : P.Prepares f.base) :
    P.LocalCompatible f ↔
      Separates X (P.preparedSettle f.base p) (P.carried s f.base ++ f.tells) :=
  ⟨fun compatible => compatible p, fun compatible _ => compatible⟩

/-- The local obligation is exactly validity of the transported result context. -/
theorem localCompatible_iff_result_separates {s : P.DState} (f : P.DFiring s)
    (p : P.Prepares f.base) :
    P.LocalCompatible f ↔
      Separates X (X.id (P.frame (P.preparedResult f.base p)))
        (X.applyStore (P.preparedSettle f.base p) (P.carried s f.base ++ f.tells)) := by
  rw [P.localCompatible_iff f p, separates_applyStore]
  exact (separates_congr (fun t => by rw [X.act_comp, X.act_id]) _).symm

theorem localCompatible_of_reflects (reflects : P.Reflects) {s : P.DState}
    (f : P.DFiring s) : P.LocalCompatible f := by
  intro p
  exact separates_of_reflects (reflects f.base p) f.formed

/-- Global reflection is exactly uniform preservation of every valid
disequation store. A singleton witnesses any failure of reflection. -/
theorem reflects_iff_preserves_all_disequations :
    P.Reflects ↔ ∀ {s : State} (f : Firing s) (p : P.Prepares f)
      (disequations : Disequality.DisequationStore (Tm (P.target f))),
      Separates X (X.id (P.target f)) disequations →
        Separates X (P.preparedSettle f p) disequations := by
  classical
  constructor
  · intro reflects s f p disequations separated
    exact separates_of_reflects (reflects f p) separated
  · intro preserves s f p u v same
    by_contra different
    have separated : Separates X (X.id (P.target f)) [(u, v)] := by
      intro d member identified
      obtain rfl := List.mem_singleton.mp member
      exact different (by simpa only [X.act_id] using identified)
    exact preserves f p [(u, v)] separated (u, v) (List.mem_singleton_self _) same

/-- Disequations for any base step, with only local settlement compatibility.
The old base admission is never used to prepare the result. -/
def withLocalDisequations [P.Guarded] : Step (frames X) O P.DState P.DFiring where
  frame s := s.frame
  knowledge s := P.knowledge s.state
  present s := P.present s.state
  selection f := P.selection f.base
  target f := f.target
  extension f := f.extension
  information f := P.information f.base
  information_refines f := by
    intro b σ solved
    exact P.information_refines f.base σ.1 solved
  Shapes f := P.Shapes f.base ∧ P.LocalCompatible f
  Admits f := f.Admits ∧ P.LocalCompatible f
  admitted_prepares _ admitted :=
    ⟨⟨admitted.1.1, admitted.2⟩, admitted.1.2.1, admitted.1.2.2.1⟩
  preparedResult {s} f p :=
    ⟨P.preparedResult f.base ⟨p.1.1, p.2.1, solvable_base p.2.2⟩,
      X.applyStore (P.preparedSettle f.base ⟨p.1.1, p.2.1, solvable_base p.2.2⟩)
        (P.carried s f.base ++ f.tells),
      (separates_applyStore _ _ _).mpr
        ((separates_congr (fun t => by rw [X.act_comp, X.act_id]) _).mpr (p.1.2 _))⟩
  present_preparedResult f _ := P.present_preparedResult f.base _
  preparedSettle f p :=
    ⟨P.preparedSettle f.base ⟨p.1.1, p.2.1, solvable_base p.2.2⟩,
      fun _ τ separated => (separates_applyStore _ _ _).mp separated⟩
  result_refines f p := by
    intro b σ solved
    exact P.result_refines f.base ⟨p.1.1, p.2.1, solvable_base p.2.2⟩ σ.1 solved

variable [P.Guarded]

instance withLocalDisequations_guarded : P.withLocalDisequations.Guarded where
  holds f B g := P.Holds f.base B.obj g.1
  admission f := by
    constructor
    · rintro ⟨⟨shapes, enabled, solvable, asked⟩, compatible⟩
      exact ⟨⟨⟨shapes, compatible⟩, enabled, solvable⟩, asked⟩
    · rintro ⟨⟨⟨shapes, compatible⟩, enabled, solvable⟩, asked⟩
      exact ⟨⟨shapes, enabled, solvable, asked⟩, compatible⟩

instance withLocalDisequations_literalInformation [P.LiteralInformation] :
    P.withLocalDisequations.LiteralInformation := ⟨fun f => P.transported f.base⟩

instance withLocalDisequations_literalKnowledge [P.LiteralKnowledge] :
    P.withLocalDisequations.LiteralKnowledge :=
  ⟨fun f p => P.knowledge_preparedResult f.base ⟨p.1.1, p.2.1, solvable_base p.2.2⟩⟩

instance withLocalDisequations_exact [P.Exact] : P.withLocalDisequations.Exact :=
  ⟨fun f p _ σ solved => Exact.exactness (P := P) f.base
    ⟨p.1.1, p.2.1, solvable_base p.2.2⟩ σ.1 solved⟩

theorem withLocalDisequations_admits_iff {s : P.DState} (f : P.DFiring s) :
    P.withLocalDisequations.Admits f ↔ f.Admits ∧ P.LocalCompatible f :=
  Iff.rfl

theorem withLocalDisequations_admits_iff_separating {s : P.DState} (f : P.DFiring s) :
    P.withLocalDisequations.Admits f ↔
      (P.Shapes f.base ∧
        Enabled (fun _ : O => ()) (P.present s.state) ((P.selection f.base).commit (T := Unit)) ∧
        (∃ (b : Obj) (g : Hom (P.target f.base) b),
          X.Models g (P.information f.base) ∧ Separates X g (P.carried s f.base ++ f.tells)) ∧
        ∀ (b : Obj) (g : Hom (P.target f.base) b), X.Models g (P.information f.base) →
          Separates X g (P.carried s f.base ++ f.tells) → P.Holds f.base b g) ∧
      P.LocalCompatible f := by
  show (f.Admits ∧ P.LocalCompatible f) ↔ _
  unfold DFiring.Admits
  exact and_congr (and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (solvable_iff (D := f.target) (P.information f.base))
      (entails_iff (D := f.target) (P.information f.base) (P.Holds f.base))))) Iff.rfl

theorem withLocalDisequations_global_admits (reflects : P.Reflects) {s : P.DState}
    (f : P.DFiring s) :
    P.withLocalDisequations.Admits f ↔ (P.withDisequations reflects).Admits f := by
  change (f.Admits ∧ P.LocalCompatible f) ↔ f.Admits
  exact and_iff_left (P.localCompatible_of_reflects reflects f)

theorem withLocalDisequations_global_result (reflects : P.Reflects) {s : P.DState}
    (f : P.DFiring s) (admitted : P.withLocalDisequations.Admits f) :
    P.withLocalDisequations.result f admitted =
      (P.withDisequations reflects).result f ((P.withLocalDisequations_global_admits reflects f).mp admitted) :=
  rfl

theorem withLocalDisequations_global_settle (reflects : P.Reflects) {s : P.DState}
    (f : P.DFiring s) (admitted : P.withLocalDisequations.Admits f) :
    P.withLocalDisequations.settle f admitted =
      (P.withDisequations reflects).settle f ((P.withLocalDisequations_global_admits reflects f).mp admitted) :=
  rfl

/-- Recover every old execution, preserving its actual firing data. -/
def localRunToGlobal (reflects : P.Reflects) :
    {s : P.DState} → P.withLocalDisequations.Run s → (P.withDisequations reflects).Run s
  | _, .nil s => .nil s
  | _, .cons f admitted rest =>
      .cons f ((P.withLocalDisequations_global_admits reflects f).mp admitted)
        (localRunToGlobal reflects rest)

def globalRunToLocal (reflects : P.Reflects) :
    {s : P.DState} → (P.withDisequations reflects).Run s → P.withLocalDisequations.Run s
  | _, .nil s => .nil s
  | _, .cons f admitted rest =>
      .cons f ((P.withLocalDisequations_global_admits reflects f).mpr admitted)
        (globalRunToLocal reflects rest)

theorem localRunToGlobal_word (reflects : P.Reflects) {s : P.DState}
    (r : P.withLocalDisequations.Run s) : (P.localRunToGlobal reflects r).word = r.word := by
  induction r with
  | nil => rfl
  | cons f admitted rest ih => exact congrArg (List.cons _) ih

theorem localRunToGlobal_last (reflects : P.Reflects) {s : P.DState}
    (r : P.withLocalDisequations.Run s) : (P.localRunToGlobal reflects r).last = r.last := by
  induction r with
  | nil => rfl
  | cons f admitted rest ih => exact ih

theorem globalRunToLocal_word (reflects : P.Reflects) {s : P.DState}
    (r : (P.withDisequations reflects).Run s) : (P.globalRunToLocal reflects r).word = r.word := by
  induction r with
  | nil => rfl
  | cons f admitted rest ih => exact congrArg (List.cons _) ih

theorem globalRunToLocal_last (reflects : P.Reflects) {s : P.DState}
    (r : (P.withDisequations reflects).Run s) : (P.globalRunToLocal reflects r).last = r.last := by
  induction r with
  | nil => rfl
  | cons f admitted rest ih => exact ih

theorem globalRunToLocal_localRunToGlobal (reflects : P.Reflects) {s : P.DState}
    (r : P.withLocalDisequations.Run s) :
    P.globalRunToLocal reflects (P.localRunToGlobal reflects r) = r := by
  induction r with
  | nil => rfl
  | cons f admitted rest ih => exact congrArg (Run.cons f admitted) ih

theorem localRunToGlobal_globalRunToLocal (reflects : P.Reflects) {s : P.DState}
    (r : (P.withDisequations reflects).Run s) :
    P.localRunToGlobal reflects (P.globalRunToLocal reflects r) = r := by
  induction r with
  | nil => rfl
  | cons f admitted rest ih => exact congrArg (Run.cons f admitted) ih

/-- A selected commitment that collapses a listed inequality is refused. -/
theorem withLocalDisequations_refused_of_collapsed {s : P.DState} (f : P.DFiring s)
    (p : P.Prepares f.base) {d : Equation (Tm (P.target f.base))}
    (member : d ∈ P.carried s f.base ++ f.tells)
    (same : X.E (X.act (P.preparedSettle f.base p) d.1)
      (X.act (P.preparedSettle f.base p) d.2)) :
    ¬ P.withLocalDisequations.Admits f := by
  intro admitted
  exact admitted.2 p d member same

omit [P.Guarded] in
theorem localCompatible_empty {s : P.DState} (f : P.DFiring s)
    (empty : s.disequations = []) (silent : f.tells = []) : P.LocalCompatible f := by
  intro p
  show Separates X _ (X.applyStore (P.extension f.base) s.disequations ++ f.tells)
  rw [empty, silent]
  exact separates_nil _

/-- No extra restriction on an equation-only firing, even for a committing step. -/
theorem withLocalDisequations_conservative {s : P.DState} (f : P.DFiring s)
    (empty : s.disequations = []) (silent : f.tells = []) :
    P.withLocalDisequations.Admits f ↔ P.Admits f.base := by
  rw [P.withLocalDisequations_admits_iff_separating f, P.admits_iff f.base]
  have separated : ∀ {b : Obj} (g : Hom (P.target f.base) b),
      Separates X g (P.carried s f.base ++ f.tells) := by
    intro b g
    show Separates X g (X.applyStore (P.extension f.base) s.disequations ++ f.tells)
    rw [empty, silent]
    exact separates_nil _
  constructor
  · rintro ⟨⟨shapes, enabled, ⟨b, g, solved, _⟩, asked⟩, _⟩
    exact ⟨shapes, enabled, ⟨b, g, solved⟩, fun b g solved => asked b g solved (separated g)⟩
  · rintro ⟨shapes, enabled, ⟨b, g, solved⟩, asked⟩
    exact ⟨⟨shapes, enabled, ⟨b, g, solved, separated g⟩, fun b g solved _ => asked b g solved⟩,
      P.localCompatible_empty f empty silent⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step
