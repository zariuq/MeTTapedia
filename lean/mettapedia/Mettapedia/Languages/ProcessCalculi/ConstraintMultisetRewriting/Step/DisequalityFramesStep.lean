import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFrames

/-!
# Telling disequations on any instance of the step

## Presteps (`Prestep`)

A **prestep** is every part of an instance of `Interface.Step` except admission: states and their
frames, knowledge and present occurrences; firings with their selection, target frame, extension,
information, shapes, guards and predicate queries (`Holds`); and a result, settlement and resulting
knowledge determined by the firing's **shapes** alone. Its step (`Prestep.step`) admits by the
interface's characterization, `admits_iff` holding by definition.

The first-order step of the run layer (`firstOrderPrestep`), the dependent full step and the helper
step at declaration frames (`DisequalityFramesInstances`) are presteps: each result is computed from
the firing's data and its shapes, never from a solution.

## The step with disequations, for every step (`Interface.Step.withDisequations`)

Over a step `P` whose prepared settlement reflects the equivalence (`Interface.Step.Reflects`):
* a state is a state of `P` and a disequation store at its frame that the identity separates
  (`DState`), so its frame is a disequation frame;
* a firing is a firing of `P` and the disequations it tells at its target frame, which together with
  the state's disequations carried along the extension form a disequation frame (`DFiring`);
* admission is the interface's, over `DisequalityFrames.frames X`: the shapes, the physical enabling,
  a solution of the information that **separates every disequation**, and the guards and predicate
  queries at every such solution (`admits_iff_separating`);
* the result is `P`'s prepared result at the preparation that separating solvability implies, with
  the disequations carried along the prepared settlement (`result_state`): `P`'s own admission is
  never asked, so guarded firings keep their guards.

It is an instance of `Interface.Step` over disequation frames, so every interface-level theorem
applies to it. A prestep's step is such a `P`: its prepared settlement is its settlement at the shapes.

* **A told disequation refuses an identifying firing** (`refused_of_identified`,
  `refused_of_carried`): a firing whose information identifies, at every solution, the two sides of a
  disequation of its target frame, in particular one the state was told earlier, is refused.
* **Conservative over equation-only stores** (`conservative`, `conservative_result`, `result_plain`,
  `lift`, `lift_last`, `lift_word`): at a state without disequations, a firing that tells none is
  admitted exactly when its firing of `P` is, with `P`'s result, and every run of `P` is a run of the
  step with disequations.

## The first-order step with disequations is the one-frame instance

`Disequality.step A label` is the step with disequations over `(firstOrderPrestep A label).step`
(`firstOrderWith`): states, firings and
admission correspond (`ofOldState`, `ofOldFiring`, `oneFrame_admits_iff`), and so do results
(`oneFrame_result_state`, `oneFrame_result_disequations`). `Disequality.conservative` is a corollary
(`old_conservative`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames

open Interface (Frames)
open Disequality (DisequationStore)
open AnnotatedRuns (firstOrder)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF

/-! ## Presteps -/

/-- **The data of an instance of the step before its asks**, with a result determined by the
firing's shapes. -/
structure Prestep {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (State : Type uS)
    (Firing : State → Type uF) where
  frame : State → Obj
  knowledge : (s : State) → EquationStore (Tm (frame s))
  present : State → Finset O
  selection : {s : State} → Firing s → Selection O
  target : {s : State} → Firing s → Obj
  extension : {s : State} → (f : Firing s) → Hom (frame s) (target f)
  information : {s : State} → (f : Firing s) → EquationStore (Tm (target f))
  transported : ∀ {s : State} (f : Firing s) (e : Equation (Tm (frame s))), e ∈ knowledge s →
    (X.act (extension f) e.1, X.act (extension f) e.2) ∈ information f
  Shapes : {s : State} → Firing s → Prop
  Holds : {s : State} → (f : Firing s) → (b : Obj) → Hom (target f) b → Prop
  result : {s : State} → (f : Firing s) → Shapes f → State
  present_result : ∀ {s : State} (f : Firing s) (shapes : Shapes f),
    present (result f shapes) = fire (present s) ((selection f).commit (T := Unit))
  settle : {s : State} → (f : Firing s) → (shapes : Shapes f) → Hom (target f) (frame (result f shapes))
  knowledge_result : ∀ {s : State} (f : Firing s) (shapes : Shapes f),
    knowledge (result f shapes) = X.applyStore (settle f shapes) (information f)

namespace Prestep

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (Q : Prestep X O State Firing)

/-- **The step of a prestep**: admission is the interface's characterization. -/
def step : Interface.Step.Standard X O State Firing where
  frame := Q.frame
  knowledge := Q.knowledge
  present := Q.present
  selection := Q.selection
  target := Q.target
  extension := Q.extension
  information := Q.information
  transported := Q.transported
  Shapes := Q.Shapes
  Holds := Q.Holds
  Admits {s} f := Q.Shapes f ∧ Enabled (fun _ : O => ()) (Q.present s) ((Q.selection f).commit (T := Unit)) ∧
    X.Solvable (Q.information f) ∧ X.Entails (Q.information f) (Q.Holds f)
  admits_iff _ := Iff.rfl
  preparedResult f p := Q.result f p.1
  present_preparedResult f p := Q.present_result f p.1
  preparedSettle f p := Q.settle f p.1
  knowledge_preparedResult f p := Q.knowledge_result f p.1

end Prestep

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames

/-! ## Disequations on every step -/

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step

open Disequality (DisequationStore)
open DisequalityFrames (Frame Morphism frames Separates separates_applyStore separates_append
  separates_congr separates_of_reflects separates_nil solvable_base solvable_iff entails_iff)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)

/-- A state with disequations: a state of the step and a disequation store at its frame that the
identity separates. -/
structure DState where
  state : State
  disequations : DisequationStore (Tm (P.frame state))
  separated : Separates X (X.id (P.frame state)) disequations

variable {P}

/-- The disequation frame of a state. -/
def DState.frame (s : P.DState) : Frame X := ⟨P.frame s.state, s.disequations, s.separated⟩

variable (P) in
/-- The state's disequations, read at a firing's target frame along its extension. -/
def carried (s : P.DState) (f : Firing s.state) : DisequationStore (Tm (P.target f)) :=
  X.applyStore (P.extension f) s.disequations

variable (P) in
/-- A firing with disequations: a firing of the step and the disequations it tells, which with the
state's carried ones form a disequation frame. Its guards are kept. -/
structure DFiring (s : P.DState) where
  base : Firing s.state
  tells : DisequationStore (Tm (P.target base))
  formed : Separates X (X.id (P.target base)) (P.carried s base ++ tells)

namespace DFiring

variable {s : P.DState} (f : P.DFiring s)

/-- Its target disequation frame. -/
def target : Frame X := ⟨P.target f.base, P.carried s f.base ++ f.tells, f.formed⟩

/-- Its extension, a morphism of disequation frames. -/
def extension : Morphism X s.frame f.target :=
  ⟨P.extension f.base, fun _ τ separated =>
    (separates_applyStore (P.extension f.base) τ s.disequations).mp (separates_append.mp separated).1⟩

/-- **Admission with disequations**: the shapes, the physical enabling, a solution of the
information that separates every disequation, and the guards and predicate queries at every such
solution. It asks nothing of the settlement. -/
def Admits [P.Guarded] : Prop :=
  P.Shapes f.base ∧ Enabled (fun _ : O => ()) (P.present s.state) ((P.selection f.base).commit (T := Unit)) ∧
    (frames X).Solvable (a := f.target) (P.information f.base) ∧
    (frames X).Entails (a := f.target) (P.information f.base) (fun B g => P.Holds f.base B.obj g.1)

end DFiring

/-- **A firing that tells nothing**, along an extension that reflects the equivalence: the state's
disequations stay separated at its target. -/
def DFiring.silent (s : P.DState) (f : Firing s.state)
    (reflects : ∀ {u v : Tm (P.frame s.state)}, X.E (X.act (P.extension f) u) (X.act (P.extension f) v) → X.E u v) :
    P.DFiring s :=
  ⟨f, [], separates_append.mpr ⟨(separates_applyStore _ _ _).mpr
    ((separates_congr (fun t => by rw [X.act_comp, X.act_id]) _).mpr (separates_of_reflects reflects s.separated)),
    separates_nil _⟩⟩

variable (P) in
/-- **Prepared settlement reflects the equivalence**: it identifies no two terms that were apart.
Every settlement by an identity does (`DisequalityFrames.id_reflects`). -/
def Reflects : Prop :=
  ∀ {s : State} (f : Firing s) (p : P.Prepares f) {u v : Tm (P.target f)},
    X.E (X.act (P.preparedSettle f p) u) (X.act (P.preparedSettle f p) v) → X.E u v

variable (P) in
/-- **The step with disequations, for every step**, an instance of the interface over disequation
frames. Its effect is the step's prepared effect at the preparation that separating solvability
implies, with the disequations carried along the prepared settlement: the step's own admission is
never asked, and guarded firings keep their guards. -/
def withDisequations [P.Guarded] (reflects : P.Reflects) : Step (frames X) O P.DState P.DFiring where
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
  Shapes f := P.Shapes f.base
  Admits f := f.Admits
  admitted_prepares _ admitted := ⟨admitted.1, admitted.2.1, admitted.2.2.1⟩
  preparedResult {s} f p :=
    ⟨P.preparedResult f.base ⟨p.1, p.2.1, solvable_base p.2.2⟩,
      X.applyStore (P.preparedSettle f.base ⟨p.1, p.2.1, solvable_base p.2.2⟩) (P.carried s f.base ++ f.tells),
      (separates_applyStore _ _ _).mpr ((separates_congr (fun t => by rw [X.act_comp, X.act_id]) _).mpr
        (separates_of_reflects (reflects f.base _) f.formed))⟩
  present_preparedResult f _ := P.present_preparedResult f.base _
  preparedSettle f p := ⟨P.preparedSettle f.base ⟨p.1, p.2.1, solvable_base p.2.2⟩, fun _ τ separated =>
    (separates_applyStore (P.preparedSettle f.base ⟨p.1, p.2.1, solvable_base p.2.2⟩) τ _).mp separated⟩
  result_refines f p := by
    intro b σ solved
    exact P.result_refines f.base ⟨p.1, p.2.1, solvable_base p.2.2⟩ σ.1 solved

variable [P.Guarded] (reflects : P.Reflects)

instance withDisequations_guarded : (P.withDisequations reflects).Guarded where
  holds f B g := P.Holds f.base B.obj g.1
  admission f := by
    change f.Admits ↔ _
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b, c⟩, d⟩,
      fun ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩⟩

instance withDisequations_literalInformation [P.LiteralInformation] :
    (P.withDisequations reflects).LiteralInformation := ⟨fun f => P.transported f.base⟩

instance withDisequations_literalKnowledge [P.LiteralKnowledge] :
    (P.withDisequations reflects).LiteralKnowledge :=
  ⟨fun f p => P.knowledge_preparedResult f.base ⟨p.1, p.2.1, solvable_base p.2.2⟩⟩

instance withDisequations_exact [P.Exact] : (P.withDisequations reflects).Exact :=
  ⟨fun f p _ σ solved => Exact.exactness (P := P) f.base
    ⟨p.1, p.2.1, solvable_base p.2.2⟩ σ.1 solved⟩

/-- **Admission with disequations, unfolded**: some solution of the information, into some later
frame of the base, separates the disequations; the guards and queries hold at every such solution. -/
theorem admits_iff_separating {s : P.DState} (f : P.DFiring s) :
    (P.withDisequations reflects).Admits f ↔ P.Shapes f.base ∧
      Enabled (fun _ : O => ()) (P.present s.state) ((P.selection f.base).commit (T := Unit)) ∧
      (∃ (b : Obj) (g : Hom (P.target f.base) b),
        X.Models g (P.information f.base) ∧ Separates X g (P.carried s f.base ++ f.tells)) ∧
      ∀ (b : Obj) (g : Hom (P.target f.base) b), X.Models g (P.information f.base) →
        Separates X g (P.carried s f.base ++ f.tells) → P.Holds f.base b g := by
  show f.Admits ↔ _
  unfold DFiring.Admits
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr (solvable_iff (D := f.target) (P.information f.base))
    (entails_iff (D := f.target) (P.information f.base) (P.Holds f.base))))

/-- **A disequation refuses an identifying firing**: a firing whose information identifies, at every
solution, the two sides of a disequation of its target frame is refused. -/
theorem refused_of_identified {s : P.DState} (f : P.DFiring s) {d : Equation (Tm (P.target f.base))}
    (member : d ∈ P.carried s f.base ++ f.tells)
    (identified : X.Entails (P.information f.base) (fun _ g => X.E (X.act g d.1) (X.act g d.2))) :
    ¬ (P.withDisequations reflects).Admits f := by
  intro admitted
  obtain ⟨-, -, ⟨b, g, solved, separated⟩, -⟩ := (admits_iff_separating reflects f).mp admitted
  exact separated d member (identified b g solved)

/-- **A disequation told earlier refuses a later identifying firing**: if the state holds the
disequation `d` and every solution of a firing's information, read back along its extension,
identifies the two sides of `d`, the firing is refused. -/
theorem refused_of_carried {s : P.DState} (f : P.DFiring s) {d : Equation (Tm (P.frame s.state))}
    (member : d ∈ s.disequations)
    (identified : X.Entails (P.information f.base)
      (fun _ g => X.E (X.act (X.comp g (P.extension f.base)) d.1) (X.act (X.comp g (P.extension f.base)) d.2))) :
    ¬ (P.withDisequations reflects).Admits f := by
  refine refused_of_identified reflects f (d := (X.act (P.extension f.base) d.1, X.act (P.extension f.base) d.2))
    (List.mem_append_left _ (List.mem_map.mpr ⟨d, member, rfl⟩)) ?_
  intro b g solved
  have h : X.E (X.act (X.comp g (P.extension f.base)) d.1) (X.act (X.comp g (P.extension f.base)) d.2) :=
    identified b g solved
  show X.E (X.act g (X.act (P.extension f.base) d.1)) (X.act g (X.act (P.extension f.base) d.2))
  rw [← X.act_comp, ← X.act_comp]
  exact h

/-! ### Conservativity over equation-only stores -/

variable (P) in
/-- The equation-only state of a state of the step. -/
def plain (s : State) : P.DState := ⟨s, [], separates_nil _⟩

/-- A firing that tells no disequation. -/
def DFiring.ofBase (s : P.DState) (f : Firing s.state) (empty : s.disequations = []) : P.DFiring s :=
  ⟨f, [], by
    show Separates X _ (X.applyStore (P.extension f) s.disequations ++ [])
    rw [empty]
    exact separates_nil _⟩

/-- **Conservative over equation-only stores**: at a state without disequations, a firing that tells
none is admitted exactly when its firing of the step is. -/
theorem conservative {s : P.DState} (f : P.DFiring s) (empty : s.disequations = []) (silent : f.tells = []) :
    (P.withDisequations reflects).Admits f ↔ P.Admits f.base := by
  rw [admits_iff_separating, P.admits_iff f.base]
  have separated : ∀ {b : Obj} (g : Hom (P.target f.base) b), Separates X g (P.carried s f.base ++ f.tells) := by
    intro _ g
    show Separates X g (X.applyStore (P.extension f.base) s.disequations ++ f.tells)
    rw [empty, silent]
    exact separates_nil _
  constructor
  · rintro ⟨shapes, enabled, ⟨b, g, solved, -⟩, asked⟩
    exact ⟨shapes, enabled, ⟨b, g, solved⟩, fun b g solved => asked b g solved (separated g)⟩
  · rintro ⟨shapes, enabled, ⟨b, g, solved⟩, asked⟩
    exact ⟨shapes, enabled, ⟨b, g, solved, separated g⟩, fun b g solved _ => asked b g solved⟩

/-- **The result is the prepared result at the base**, whether or not the base firing is admitted. -/
theorem result_state {s : P.DState} (f : P.DFiring s) (admitted : (P.withDisequations reflects).Admits f) :
    ((P.withDisequations reflects).result f admitted).state =
      P.preparedResult f.base ⟨admitted.1, admitted.2.1, solvable_base admitted.2.2.1⟩ :=
  rfl

/-- **With the same result**: when the base firing is admitted too, the result with disequations is
at the base result. -/
theorem conservative_result {s : P.DState} (f : P.DFiring s) (admitted : (P.withDisequations reflects).Admits f)
    (base : P.Admits f.base) : ((P.withDisequations reflects).result f admitted).state = P.result f.base base :=
  rfl

/-- The result of a silent firing at an equation-only state is the equation-only state of the
step's result. -/
theorem result_plain (s : State) (f : Firing s)
    (admitted : (P.withDisequations reflects).Admits (DFiring.ofBase (P.plain s) f rfl)) :
    (P.withDisequations reflects).result (DFiring.ofBase (P.plain s) f rfl) admitted =
      P.plain (P.result f ((conservative reflects _ rfl rfl).mp admitted)) :=
  rfl

/-- **Every run of the step is a run of the step with disequations**, from the equation-only
state, firing by firing. -/
def lift : {s : State} → P.Run s → (P.withDisequations reflects).Run (P.plain s)
  | _, .nil s => .nil (P.plain s)
  | s, .cons f admitted rest =>
      .cons (DFiring.ofBase (P.plain s) f rfl)
        ((conservative reflects (DFiring.ofBase (P.plain s) f rfl) rfl rfl).mpr admitted) (lift rest)

theorem lift_last : ∀ {s : State} (r : P.Run s), (lift reflects r).last = P.plain r.last
  | _, .nil _ => rfl
  | _, .cons _ _ rest => lift_last rest

theorem lift_word : ∀ {s : State} (r : P.Run s),
    (lift reflects r).word.map (fun x => ⟨x.1.state, x.2.base⟩) = r.word
  | _, .nil _ => rfl
  | _, .cons f admitted rest => by
      show ⟨_, f⟩ :: (lift reflects rest).word.map (fun x => ⟨x.1.state, x.2.base⟩) = ⟨_, f⟩ :: rest.word
      rw [lift_word rest]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames

open Interface (Frames)
open Disequality (DisequationStore)
open AnnotatedRuns (firstOrder)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

/-! ## The first-order step is a prestep -/

section FirstOrder

universe uA uB uC

variable {T : Type uA} {S : Type uB} {O : Type uC} [DecidableEq O] (A : SubstitutionAction T S)
  (label : O → T)

/-- **The first-order step as a prestep**: its result is computed from the firing's data. -/
def firstOrderPrestep :
    Prestep (Frames.ofSubstitution A) O (Configuration T O) (fun _ => AnnotatedRuns.Firing T S O) where
  frame _ := PUnit.unit
  knowledge C := C.equations
  present C := C.present
  selection f := f.selection
  target _ := PUnit.unit
  extension _ := A.identity
  information {C} f := f.selection.problem label f.rule C
  transported {C} f e member := (firstOrder A label).transported (s := C) f e member
  Shapes {C} f := (firstOrder A label).Shapes (s := C) f
  Holds {C} f b σ := (firstOrder A label).Holds (s := C) f b σ
  result {C} f _ := f.result label C
  present_result _ _ := rfl
  settle _ _ := A.identity
  knowledge_result {C} f _ := (Frames.applyStore_id (X := Frames.ofSubstitution A)
    (f.selection.problem label f.rule C)).symm

/-- **The prestep's step is the first-order step**: the same admission. -/
theorem firstOrderPrestep_admits_iff (C : Configuration T O) (f : AnnotatedRuns.Firing T S O) :
    (firstOrderPrestep A label).step.Admits (s := C) f ↔ (firstOrder A label).Admits (s := C) f :=
  ((firstOrder A label).admits_iff f).symm

/-- And the same result. -/
theorem firstOrderPrestep_result (C : Configuration T O) (f : AnnotatedRuns.Firing T S O)
    (admitted : (firstOrderPrestep A label).step.Admits (s := C) f) :
    (firstOrderPrestep A label).step.result f admitted =
      (firstOrder A label).result f ((firstOrderPrestep_admits_iff A label C f).mp admitted) :=
  rfl

/-- Its settlement is the identity, which reflects the equivalence. -/
theorem firstOrder_reflects : (firstOrderPrestep A label).step.Reflects :=
  fun _ _ _ _ same => id_reflects (X := Frames.ofSubstitution A) (a := PUnit.unit) same

/-- **The first-order step with disequations over the generic construction.** -/
abbrev firstOrderWith :=
  (firstOrderPrestep A label).step.withDisequations (firstOrder_reflects A label)

theorem applyStore_identity (D : DisequationStore T) :
    (Frames.ofSubstitution A).applyStore (a := PUnit.unit) (b := PUnit.unit) A.identity D = D :=
  Frames.applyStore_id (X := Frames.ofSubstitution A) (a := PUnit.unit) D

variable {A label}

/-- A state of `Disequality.step`, as a state of the generic construction. -/
def ofOldState (s : Disequality.State A O) : (firstOrderPrestep A label).step.DState :=
  ⟨s.configuration, s.disequations.1, s.disequations.2⟩

/-- A firing of `Disequality.step`, as a firing of the generic construction. -/
def ofOldFiring {s : Disequality.State A O} (f : Disequality.Firing A O s) :
    (firstOrderPrestep A label).step.DFiring (ofOldState s) :=
  ⟨f.base, f.tells, by
    show Separates (Frames.ofSubstitution A) _
      ((Frames.ofSubstitution A).applyStore A.identity s.disequations.1 ++ f.tells)
    rw [applyStore_identity]
    exact f.formed⟩

theorem separates_ofOld {s : Disequality.State A O} (f : Disequality.Firing A O s) (σ : S) :
    Separates (Frames.ofSubstitution A) (a := PUnit.unit) (b := PUnit.unit) σ
        ((firstOrderPrestep A label).step.carried (ofOldState s) f.base ++ f.tells) ↔
      Disequality.Separates A σ f.target.1 := by
  show Separates (Frames.ofSubstitution A) σ
      ((Frames.ofSubstitution A).applyStore A.identity s.disequations.1 ++ f.tells) ↔ _
  rw [applyStore_identity]
  rfl

/-- **`Disequality.step` is the one-frame instance of the construction**: the same admission. -/
theorem oneFrame_admits_iff {s : Disequality.State A O} (f : Disequality.Firing A O s) :
    (Disequality.step A label).Admits f ↔ (firstOrderWith A label).Admits (ofOldFiring f) := by
  have solvable := OneFrame.old_solvable_iff A (D := f.target)
    (f.base.selection.problem label f.base.rule s.configuration)
  have entails := OneFrame.old_entails_iff A (D := f.target)
    (f.base.selection.problem label f.base.rule s.configuration) (Disequality.holdsAt A label f)
  refine ((Disequality.step A label).admits_iff f).trans ?_
  rw [Interface.Step.admits_iff_separating]
  constructor
  · rintro ⟨shapes, enabled, solv, asks⟩
    obtain ⟨σ, solved, separated⟩ := solvable.mp solv
    have asked := entails.mp asks
    exact ⟨shapes, enabled, ⟨PUnit.unit, σ, solved, (separates_ofOld f σ).mpr separated⟩,
      fun _ σ solved separated => asked σ solved ((separates_ofOld f σ).mp separated)⟩
  · rintro ⟨shapes, enabled, ⟨_, σ, solved, separated⟩, asks⟩
    exact ⟨shapes, enabled, solvable.mpr ⟨σ, solved, (separates_ofOld f σ).mp separated⟩,
      entails.mpr fun σ solved separated => asks PUnit.unit σ solved ((separates_ofOld f σ).mpr separated)⟩

/-- **The results correspond**: the same configuration. -/
theorem oneFrame_result_state {s : Disequality.State A O} (f : Disequality.Firing A O s)
    (admitted : (Disequality.step A label).Admits f) :
    ((firstOrderWith A label).result (ofOldFiring f) ((oneFrame_admits_iff f).mp admitted)).state =
      ((Disequality.step A label).result f admitted).configuration :=
  rfl

/-- **And the same disequations.** -/
theorem oneFrame_result_disequations {s : Disequality.State A O} (f : Disequality.Firing A O s)
    (admitted : (Disequality.step A label).Admits f) :
    ((firstOrderWith A label).result (ofOldFiring f) ((oneFrame_admits_iff f).mp admitted)).disequations =
      ((Disequality.step A label).result f admitted).disequations.1 := by
  show (Frames.ofSubstitution A).applyStore A.identity
      ((Frames.ofSubstitution A).applyStore A.identity s.disequations.1 ++ f.tells) = s.disequations.1 ++ f.tells
  rw [applyStore_identity, applyStore_identity]

/-- `Disequality.conservative`, from `conservative`. -/
theorem old_conservative {s : Disequality.State A O} (f : Disequality.Firing A O s)
    (empty : s.disequations.1 = []) (silent : f.tells = []) :
    (Disequality.step A label).Admits f ↔ (firstOrder A label).Admits (s := s.configuration) f.base := by
  rw [oneFrame_admits_iff, Interface.Step.conservative (firstOrder_reflects A label) (ofOldFiring f) empty silent]
  exact firstOrderPrestep_admits_iff A label s.configuration f.base

end FirstOrder

#print axioms firstOrderPrestep_admits_iff
#print axioms firstOrderPrestep_result
#print axioms firstOrder_reflects
#print axioms oneFrame_admits_iff
#print axioms oneFrame_result_state
#print axioms oneFrame_result_disequations
#print axioms old_conservative
#print axioms Interface.Step.admits_iff_separating
#print axioms Interface.Step.refused_of_identified
#print axioms Interface.Step.refused_of_carried
#print axioms Interface.Step.conservative
#print axioms Interface.Step.result_state
#print axioms Interface.Step.conservative_result
#print axioms Interface.Step.result_plain
#print axioms Interface.Step.lift_last
#print axioms Interface.Step.lift_word

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames
