import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Disequality

/-!
# Disequation frames over any category of frames

`Disequality` builds disequation frames over a substitution action, the one-frame case. This module
builds them over any `Interface.Frames X`.

## The construction (`Frame`, `Morphism`, `frames`)

* A solution `f : a ⟶ b` **separates** a disequation store at `a` when it identifies the two sides of
  none of its disequations (`Separates`).
* A **disequation frame** is a frame `a` of `X` with a disequation store there that the identity of
  `a` separates. Equivalently, some solution into some later frame separates it (`separates_id_iff`).
* A **morphism** of disequation frames is a morphism of `X` that carries every separating solution
  of the later frame, into every frame, back to a separating solution of the earlier one.

They form a category of frames in the sense of `Interface.Frames` (`frames`), acting on terms as `X`
does. So the interface's solvability, asks and principality apply unchanged:
* **solvability is solvability with separation** (`solvable_iff`): some solution into some later
  frame of `X` solves the equations and separates the frame's disequations;
* **an ask is asked at every separating solution** (`entails_iff`);
* **principal answers survive as answers into a frame** (`principal`, `solvable_iff_separates`): a
  principal answer of the equations in `X` that separates the disequations is principal at the
  frame, with the transported disequations as its target frame; if it does not separate them, the
  store is not solvable there;
* **no single solution presents a disequation store** unless every solution separates it
  (`presents_iff`).

## The one-frame instance (`OneFrame`)

Over `Frames.ofSubstitution A` the construction is the one of `Disequality`: frames and morphisms
correspond (`OneFrame.ofOld`, `toOld`, `homOfOld`, `homToOld`), and so do solvability and asks
(`OneFrame.solvable_iff_old`, `OneFrame.entails_iff_old`) and principal answers
(`OneFrame.principal_toOld`). The theorems of `Disequality` are corollaries of the ones here
(`OneFrame.old_solvable_iff`, `old_entails_iff`, `old_principal`, `old_solvable_iff_separates`,
`old_presents_iff`), each proved from its general form.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames

open Interface (Frames)
open Disequality (DisequationStore)

universe uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## Separation -/

section Separation

variable (X : Frames Tm Hom)

/-- A solution **separates** a disequation store when it identifies the two sides of none of its
disequations. -/
def Separates {a b : Obj} (f : Hom a b) (store : DisequationStore (Tm a)) : Prop :=
  ∀ d ∈ store, ¬ X.E (X.act f d.1) (X.act f d.2)

variable {X}

@[simp] theorem separates_nil {a b : Obj} (f : Hom a b) : Separates X f [] := by
  simp [Separates]

theorem separates_append {a b : Obj} {f : Hom a b} {one two : DisequationStore (Tm a)} :
    Separates X f (one ++ two) ↔ Separates X f one ∧ Separates X f two := by
  constructor
  · intro separated
    exact ⟨fun d member => separated d (List.mem_append_left _ member),
      fun d member => separated d (List.mem_append_right _ member)⟩
  · rintro ⟨first, second⟩ d member
    rcases List.mem_append.mp member with member | member
    · exact first d member
    · exact second d member

/-- Separation depends on a solution only through its action. -/
theorem separates_congr {a b : Obj} {f g : Hom a b} (same : ∀ t, X.act f t = X.act g t)
    (store : DisequationStore (Tm a)) : Separates X f store ↔ Separates X g store := by
  simp only [Separates, same]

/-- **Separation is reflected along later instantiation**: what a composite separates, its first
factor separated. -/
theorem separates_of_comp {a b c : Obj} {f : Hom a b} {g : Hom b c} {store : DisequationStore (Tm a)}
    (later : Separates X (X.comp g f) store) : Separates X f store := by
  intro d member same
  apply later d member
  rw [X.act_comp, X.act_comp]
  exact X.preserves g same

/-- A transported store is separated exactly by the composites. -/
theorem separates_applyStore {a b c : Obj} (f : Hom a b) (g : Hom b c) (store : DisequationStore (Tm a)) :
    Separates X g (X.applyStore f store) ↔ Separates X (X.comp g f) store := by
  constructor
  · intro separated d member
    have kept := separated _ (List.mem_map.mpr ⟨d, member, rfl⟩)
    rw [X.act_comp, X.act_comp]
    exact kept
  · intro separated d member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have kept := separated original present
    rw [X.act_comp, X.act_comp] at kept
    exact kept

/-- **A disequation store has a separating solution exactly when the identity separates it.** -/
theorem separates_id_iff {a : Obj} (store : DisequationStore (Tm a)) :
    Separates X (X.id a) store ↔ ∃ (b : Obj) (f : Hom a b), Separates X f store := by
  constructor
  · intro separated
    exact ⟨a, X.id a, separated⟩
  · rintro ⟨b, f, separated⟩
    apply separates_of_comp (g := f)
    exact (separates_congr (fun t => by rw [X.act_comp, X.act_id]) store).mpr separated

/-- The identity separates a store exactly when no disequation has equivalent sides. -/
theorem separates_id_iff_apart {a : Obj} (store : DisequationStore (Tm a)) :
    Separates X (X.id a) store ↔ ∀ d ∈ store, ¬ X.E d.1 d.2 := by
  simp only [Separates, X.act_id]

/-- **A morphism that reflects the equivalence separates every store the identity separates.** -/
theorem separates_of_reflects {a b : Obj} {f : Hom a b}
    (reflects : ∀ {u v : Tm a}, X.E (X.act f u) (X.act f v) → X.E u v)
    {store : DisequationStore (Tm a)} (separated : Separates X (X.id a) store) : Separates X f store :=
  fun d member same => (separates_id_iff_apart store).mp separated d member (reflects same)

/-- The identity reflects the equivalence. -/
theorem id_reflects {a : Obj} {u v : Tm a} (same : X.E (X.act (X.id a) u) (X.act (X.id a) v)) :
    X.E u v := by
  rwa [X.act_id, X.act_id] at same

end Separation

/-! ## Disequation frames -/

section Construction

variable (X : Frames Tm Hom)

/-- A **disequation frame** over `X`: a frame of `X` and a disequation store there that its identity
separates. -/
structure Frame where
  obj : Obj
  store : DisequationStore (Tm obj)
  separated : Separates X (X.id obj) store

/-- A **morphism of disequation frames**: a morphism of `X` that carries every separating solution of
the later frame, into every frame, back to a separating solution of the earlier one. -/
abbrev Morphism (D D' : Frame X) : Type uH :=
  {f : Hom D.obj D'.obj // ∀ (c : Obj) (τ : Hom D'.obj c), Separates X τ D'.store →
    Separates X (X.comp τ f) D.store}

/-- **The category of disequation frames over `X`**, acting on terms as `X` does. -/
def frames : Frames (fun D : Frame X => Tm D.obj) (Morphism X) where
  E := X.E
  equivalence D := X.equivalence D.obj
  act f t := X.act f.1 t
  id D := ⟨X.id D.obj, fun _ τ separated =>
    (separates_congr (fun t => by rw [X.act_comp, X.act_id]) D.store).mpr separated⟩
  comp g f := ⟨X.comp g.1 f.1, fun c τ separated =>
    (separates_congr (fun t => (Frames.act_comp_assoc f.1 g.1 τ t).symm) _).mpr
      (f.2 c _ (g.2 c τ separated))⟩
  act_id t := X.act_id t
  act_comp g f t := X.act_comp g.1 f.1 t
  preserves f _ _ same := X.preserves f.1 same

end Construction

section Theory

variable {X : Frames Tm Hom}

theorem models_iff {D D' : Frame X} (f : Morphism X D D') (store : EquationStore (Tm D.obj)) :
    (frames X).Models f store ↔ X.Models f.1 store :=
  Iff.rfl

theorem applyStore_eq {D D' : Frame X} (f : Morphism X D D') (store : EquationStore (Tm D.obj)) :
    (frames X).applyStore f store = X.applyStore f.1 store :=
  rfl

/-- **A morphism separates its source frame.** -/
theorem separates_morphism {D D' : Frame X} (f : Morphism X D D') : Separates X f.1 D.store :=
  separates_of_comp (g := X.id D'.obj) (f.2 _ (X.id D'.obj) D'.separated)

/-- The frame of the disequations a separating solution leaves. -/
def image {a b : Obj} (f : Hom a b) (store : DisequationStore (Tm a)) (separated : Separates X f store) :
    Frame X :=
  ⟨b, X.applyStore f store, (separates_applyStore f (X.id b) store).mpr
    ((separates_congr (fun t => by rw [X.act_comp, X.act_id]) store).mpr separated)⟩

/-- A separating solution as a morphism into the frame it leaves. -/
def toImage (D : Frame X) {b : Obj} (f : Hom D.obj b) (separated : Separates X f D.store) :
    Morphism X D (image f D.store separated) :=
  ⟨f, fun _ τ later => (separates_applyStore f τ D.store).mp later⟩

/-- **Solvability at a disequation frame is solvability with separation.** -/
theorem solvable_iff {D : Frame X} (store : EquationStore (Tm D.obj)) :
    (frames X).Solvable (a := D) store ↔
      ∃ (b : Obj) (f : Hom D.obj b), X.Models f store ∧ Separates X f D.store := by
  constructor
  · rintro ⟨D', f, solved⟩
    exact ⟨D'.obj, f.1, solved, separates_morphism f⟩
  · rintro ⟨b, f, solved, separated⟩
    exact ⟨_, toImage D f separated, solved⟩

/-- Solvability at a disequation frame implies solvability in `X`. -/
theorem solvable_base {D : Frame X} {store : EquationStore (Tm D.obj)}
    (solvable : (frames X).Solvable (a := D) store) : X.Solvable store := by
  obtain ⟨b, f, solved, -⟩ := (solvable_iff store).mp solvable
  exact ⟨b, f, solved⟩

/-- **An ask at a disequation frame is asked at every separating solution.** -/
theorem entails_iff {D : Frame X} (store : EquationStore (Tm D.obj))
    (observation : (b : Obj) → Hom D.obj b → Prop) :
    (frames X).Entails (a := D) store (fun B f => observation B.obj f.1) ↔
      ∀ (b : Obj) (f : Hom D.obj b), X.Models f store → Separates X f D.store → observation b f := by
  constructor
  · intro asked b f solved separated
    exact asked _ (toImage D f separated) solved
  · intro asked D' f solved
    exact asked D'.obj f.1 solved (separates_morphism f)

/-- An ask in `X` is an ask at every disequation frame. -/
theorem entails_of_base {D : Frame X} {store : EquationStore (Tm D.obj)}
    {observation : (b : Obj) → Hom D.obj b → Prop} (asked : X.Entails store observation) :
    (frames X).Entails (a := D) store (fun B f => observation B.obj f.1) :=
  (entails_iff store observation).mpr fun b f solved _ => asked b f solved

/-- **Principal answers survive, as answers into a frame**: a principal answer of the equations in
`X` that separates the disequations is principal at the disequation frame, its target frame being the
transported disequations. -/
theorem principal {D : Frame X} {store : EquationStore (Tm D.obj)} {m : Obj} {answer : Hom D.obj m}
    (principalAnswer : X.Principal store answer) (separated : Separates X answer D.store) :
    (frames X).Principal (a := D) store (toImage D answer separated) where
  sound := principalAnswer.sound
  factors := by
    intro D' f solved
    obtain ⟨residual, through⟩ := principalAnswer.factors D'.obj f.1 solved
    refine ⟨⟨residual, fun c τ later d member => ?_⟩, fun t => through t⟩
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    intro same
    apply f.2 c τ later original present
    have first : X.E (X.act (X.comp τ f.1) original.1)
        (X.act (X.comp τ residual) (X.act answer original.1)) := by
      rw [X.act_comp τ f.1, X.act_comp τ residual, ← X.act_comp residual answer]
      exact X.preserves τ (through original.1)
    have second : X.E (X.act (X.comp τ f.1) original.2)
        (X.act (X.comp τ residual) (X.act answer original.2)) := by
      rw [X.act_comp τ f.1, X.act_comp τ residual, ← X.act_comp residual answer]
      exact X.preserves τ (through original.2)
    exact (X.equivalence c).trans first ((X.equivalence c).trans same ((X.equivalence c).symm second))

/-- **Solvability with disequations is decided by a principal answer of the equations**: the store is
solvable at the frame exactly when that answer separates the frame's disequations. -/
theorem solvable_iff_separates {D : Frame X} {store : EquationStore (Tm D.obj)} {m : Obj}
    {answer : Hom D.obj m} (principalAnswer : X.Principal store answer) :
    (frames X).Solvable (a := D) store ↔ Separates X answer D.store := by
  constructor
  · intro solvable d member same
    obtain ⟨b, f, solved, separated⟩ := (solvable_iff store).mp solvable
    obtain ⟨residual, through⟩ := principalAnswer.factors b f solved
    apply separated d member
    have moved : X.E (X.act (X.comp residual answer) d.1) (X.act (X.comp residual answer) d.2) := by
      rw [X.act_comp, X.act_comp]
      exact X.preserves residual same
    exact (X.equivalence b).trans (through d.1)
      ((X.equivalence b).trans moved ((X.equivalence b).symm (through d.2)))
  · intro separated
    exact (solvable_iff store).mpr ⟨m, answer, principalAnswer.sound, separated⟩

variable (X) in
/-- A solution **presents** a disequation store when the store's separating solutions are exactly
the solutions that factor through it. -/
def Presents {a : Obj} (store : DisequationStore (Tm a)) {m : Obj} (answer : Hom a m) : Prop :=
  ∀ (b : Obj) (f : Hom a b), Separates X f store ↔
    ∃ residual : Hom m b, ∀ t, X.E (X.act f t) (X.act (X.comp residual answer) t)

variable (X) in
/-- **Disunification has no single principal answer in general**: a disequation store is presented by
one solution exactly when every solution separates it. -/
theorem presents_iff {a : Obj} (store : DisequationStore (Tm a)) :
    (∃ (m : Obj) (answer : Hom a m), Presents X store answer) ↔
      ∀ (b : Obj) (f : Hom a b), Separates X f store := by
  constructor
  · rintro ⟨m, answer, presents⟩ b σ
    have answerSeparates : Separates X answer store :=
      (presents m answer).mpr ⟨X.id m, fun t => by
        rw [X.act_comp, X.act_id]
        exact (X.equivalence m).refl _⟩
    have identitySeparates : Separates X (X.id a) store :=
      (separates_id_iff store).mpr ⟨m, answer, answerSeparates⟩
    obtain ⟨back, through⟩ := (presents a (X.id a)).mp identitySeparates
    apply (presents b σ).mpr
    refine ⟨X.comp σ back, fun t => ?_⟩
    have moved := X.preserves σ (through t)
    simp only [X.act_comp, X.act_id] at moved ⊢
    exact moved
  · intro every
    refine ⟨a, X.id a, fun b σ => ⟨fun _ => ⟨σ, fun t => ?_⟩, fun _ => every b σ⟩⟩
    rw [X.act_comp, X.act_id]
    exact (X.equivalence b).refl _

end Theory

/-! ## The one-frame instance is the construction of `Disequality` -/

namespace OneFrame

universe uA uB

variable {T : Type uA} {S : Type uB} (A : SubstitutionAction T S)

/-- The one-frame category of `A`. -/
abbrev Y := Frames.ofSubstitution A

theorem separates_iff (σ : S) (store : DisequationStore T) :
    Separates (Y A) (a := PUnit.unit) (b := PUnit.unit) σ store ↔ Disequality.Separates A σ store :=
  Iff.rfl

variable {A}

/-- A disequation frame of `Disequality`, as one over the one-frame category. -/
def ofOld (D : Disequality.Frame A) : Frame (Y A) := ⟨PUnit.unit, D.1, D.2⟩

/-- A disequation frame over the one-frame category, as one of `Disequality`. -/
def toOld (D : Frame (Y A)) : Disequality.Frame A := ⟨D.store, D.separated⟩

theorem toOld_ofOld (D : Disequality.Frame A) : toOld (ofOld D) = D := rfl

theorem ofOld_toOld (D : Frame (Y A)) : ofOld (toOld D) = D := rfl

/-- A morphism of `Disequality`, over the one-frame category. -/
def homOfOld {D D' : Disequality.Frame A} (f : Disequality.Hom A D D') :
    Morphism (Y A) (ofOld D) (ofOld D') :=
  ⟨f.1, fun _ τ separated => f.2 τ separated⟩

/-- A morphism over the one-frame category, as one of `Disequality`. -/
def homToOld {D D' : Frame (Y A)} (f : Morphism (Y A) D D') : Disequality.Hom A (toOld D) (toOld D') :=
  ⟨f.1, fun τ separated => f.2 PUnit.unit τ separated⟩

/-- **Solvability corresponds.** -/
theorem solvable_iff_old (D : Disequality.Frame A) (store : EquationStore T) :
    (frames (Y A)).Solvable (a := ofOld D) store ↔ (Disequality.frames A).Solvable (a := D) store := by
  constructor
  · rintro ⟨D', f, solved⟩
    exact ⟨toOld D', homToOld f, solved⟩
  · rintro ⟨D', f, solved⟩
    exact ⟨ofOld D', homOfOld f, solved⟩

/-- **Asks correspond.** -/
theorem entails_iff_old (D : Disequality.Frame A) (store : EquationStore T) (observation : S → Prop) :
    (frames (Y A)).Entails (a := ofOld D) store (fun _ f => observation f.1) ↔
      (Disequality.frames A).Entails (a := D) store (fun _ f => observation f.1) := by
  constructor
  · intro asked D' f solved
    exact asked (ofOld D') (homOfOld f) solved
  · intro asked D' f solved
    exact asked (toOld D') (homToOld f) solved

/-- **Principal answers correspond.** -/
theorem principal_toOld {D : Disequality.Frame A} {M : Frame (Y A)} {store : EquationStore T}
    {answer : Morphism (Y A) (ofOld D) M} (principal : (frames (Y A)).Principal store answer) :
    (Disequality.frames A).Principal (a := D) (m := toOld M) store (homToOld answer) where
  sound := principal.sound
  factors := by
    intro D' f solved
    obtain ⟨residual, through⟩ := principal.factors (ofOld D') (homOfOld f) solved
    exact ⟨homToOld residual, through⟩

/-! ### The theorems of `Disequality`, as corollaries -/

variable (A) in
/-- `Disequality.solvable_iff`, from `solvable_iff`. -/
theorem old_solvable_iff {D : Disequality.Frame A} (store : EquationStore T) :
    (Disequality.frames A).Solvable (a := D) store ↔
      ∃ σ, A.Models σ store ∧ Disequality.Separates A σ D.1 := by
  rw [← solvable_iff_old, solvable_iff]
  constructor
  · rintro ⟨_, σ, solved, separated⟩
    exact ⟨σ, solved, separated⟩
  · rintro ⟨σ, solved, separated⟩
    exact ⟨PUnit.unit, σ, solved, separated⟩

variable (A) in
/-- `Disequality.entails_iff`, from `entails_iff`. -/
theorem old_entails_iff {D : Disequality.Frame A} (store : EquationStore T) (observation : S → Prop) :
    (Disequality.frames A).Entails (a := D) store (fun _ f => observation f.1) ↔
      ∀ σ, A.Models σ store → Disequality.Separates A σ D.1 → observation σ := by
  rw [← entails_iff_old]
  rw [entails_iff (D := ofOld D) store (fun _ σ => observation σ)]
  constructor
  · intro asked σ solved separated
    exact asked PUnit.unit σ solved separated
  · intro asked _ σ solved separated
    exact asked σ solved separated

/-- `Disequality.principal`, from `principal`. -/
theorem old_principal {D : Disequality.Frame A} {store : EquationStore T} {answer : S}
    (principalAnswer : A.Principal store answer) (separated : Disequality.Separates A answer D.1) :
    (Disequality.frames A).Principal (a := D) store (Disequality.toImage D answer separated) :=
  principal_toOld (principal (X := Y A) (D := ofOld D) (m := PUnit.unit)
    ((Frames.ofSubstitution_principal_iff A store answer).mpr principalAnswer) separated)

/-- `Disequality.solvable_iff_separates`, from `solvable_iff_separates`. -/
theorem old_solvable_iff_separates {D : Disequality.Frame A} {store : EquationStore T} {answer : S}
    (principalAnswer : A.Principal store answer) :
    (Disequality.frames A).Solvable (a := D) store ↔ Disequality.Separates A answer D.1 := by
  rw [← solvable_iff_old]
  exact solvable_iff_separates (X := Y A) (D := ofOld D) (m := PUnit.unit)
    ((Frames.ofSubstitution_principal_iff A store answer).mpr principalAnswer)

variable (A) in
/-- `Disequality.presents_iff`, from `presents_iff`. -/
theorem old_presents_iff (store : DisequationStore T) :
    (∃ answer, Disequality.Presents A store answer) ↔ ∀ σ, Disequality.Separates A σ store := by
  have general := presents_iff (Y A) (a := PUnit.unit) store
  constructor
  · rintro ⟨answer, presents⟩
    have every := general.mp ⟨PUnit.unit, answer, fun _ σ => presents σ⟩
    exact fun σ => every PUnit.unit σ
  · intro every
    obtain ⟨_, answer, presents⟩ := general.mpr fun _ σ => every σ
    exact ⟨answer, fun σ => presents PUnit.unit σ⟩

end OneFrame

#print axioms separates_id_iff
#print axioms separates_applyStore
#print axioms separates_of_reflects
#print axioms frames
#print axioms separates_morphism
#print axioms solvable_iff
#print axioms entails_iff
#print axioms principal
#print axioms solvable_iff_separates
#print axioms presents_iff
#print axioms OneFrame.solvable_iff_old
#print axioms OneFrame.entails_iff_old
#print axioms OneFrame.principal_toOld
#print axioms OneFrame.old_solvable_iff
#print axioms OneFrame.old_entails_iff
#print axioms OneFrame.old_principal
#print axioms OneFrame.old_solvable_iff_separates
#print axioms OneFrame.old_presents_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames
