import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Independence

/-!
# Lawful transport: the laws that make independence intrinsic

`Transport.residual` carries only its selection and naturality laws, `Step.settle` may be any
morphism, and `Step.Holds` any predicate. Independence is defined through the residual, so without
further laws it depends on which residual an instance happens to choose. This module adds the laws,
over an existing `Transport`, and proves that under them independence is a property of the step.

## Locality of guards (`Step.Guards`)

The interface has no labels, so the region is explicit data. A firing's guards at one solution are a
predicate of present occurrences (`Guard`); the interface's `Holds` is that predicate read at the
state's present occurrences (`holds_iff`); it respects the frame equivalence (`respects`); and it
reads the present occurrences only inside its `region` (`inside`). A firing that writes nothing in the
region keeps the guards (`Guards.guard_fire`).

## Residual coherence (`Transport.Coherent`)

The residual of `f` after an admitted `g` comes with a morphism `carry` from `f`'s target into the
residual's target, under `g`'s morphism of frames (`square`). Its target is the amalgamation of `f`'s
target with `g`'s result over the state's frame, for solutions: every pair of solutions that agree on
the state's frame comes from one solution (`amalgamate`), and a solution is determined by its two
restrictions (`separated`). Its information is `f`'s information carried, together with `g`'s result
knowledge (`information`); its shapes are `f`'s (`shapes`); and its guards are `f`'s pulled back along
`carry` (`guard`). Admission of a residual is then a condition that mentions no residual
(`Coherent.admits_iff`, `Step.AdmitsAfter`), and two coherent residuals are isomorphic firings
(`Coherent.firingIso`). When `g` writes outside `f`'s region, the residual's `Holds` is `f`'s guard
read at the state `f` started from (`Coherent.holds_residual_iff`).

## Conservative settlement (`Step.ConservativeSettlement`)

Every solution of a firing's information factors through `settle`. Under it the result asks exactly
what the information asks (`Step.entails_result_iff`) and is solvable exactly when the information is
(`Step.solvable_result_iff`): settlement chooses no solution.

## Lawful transport and the content theorem

A **lawful transport** (`Transport.Lawful`) has coherent residuals, conservative settlement, and
results that respect isomorphism of firings (`canonical`). **Two lawful transports with the same
state classes have the same independence** (`Transport.Lawful.independent_iff`); in particular,
replacing the residual of a lawful transport by another lawful one changes nothing
(`Transport.Lawful.independent_withResidual_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

universe uO uT uH uOcc uS uF uI

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **Two morphisms that act the same**, up to the equivalence of terms. -/
def Agree (X : Frames Tm Hom) {a b : Obj} (f g : Hom a b) : Prop :=
  ∀ t : Tm a, X.E (X.act f t) (X.act g t)

variable {X : Frames Tm Hom}

namespace Agree

theorem refl {a b : Obj} (f : Hom a b) : X.Agree f f := fun _ => (X.equivalence b).refl _

theorem symm {a b : Obj} {f g : Hom a b} (same : X.Agree f g) : X.Agree g f :=
  fun t => (X.equivalence b).symm (same t)

theorem trans {a b : Obj} {f g h : Hom a b} (first : X.Agree f g) (second : X.Agree g h) :
    X.Agree f h :=
  fun t => (X.equivalence b).trans (first t) (second t)

theorem of_eq {a b : Obj} {f g : Hom a b} (same : f = g) : X.Agree f g := same ▸ refl f

/-- Agreement survives a later morphism. -/
theorem comp_left {a b c : Obj} (h : Hom b c) {f g : Hom a b} (same : X.Agree f g) :
    X.Agree (X.comp h f) (X.comp h g) := fun t => by
  rw [X.act_comp, X.act_comp]
  exact X.preserves h (same t)

/-- Agreement survives an earlier morphism. -/
theorem comp_right {a b c : Obj} {f g : Hom b c} (same : X.Agree f g) (h : Hom a b) :
    X.Agree (X.comp f h) (X.comp g h) := fun t => by
  rw [X.act_comp, X.act_comp]
  exact same (X.act h t)

theorem models_iff {a b : Obj} {f g : Hom a b} (same : X.Agree f g) (store : EquationStore (Tm a)) :
    X.Models f store ↔ X.Models g store :=
  models_congrE same store

/-- Agreeing morphisms carry a store to stores with the same solutions. -/
theorem equivalent {a b : Obj} {f g : Hom a b} (same : X.Agree f g) (store : EquationStore (Tm a)) :
    X.Equivalent (X.applyStore f store) (X.applyStore g store) := fun _ h =>
  (models_applyStore f h store).trans
    (((comp_left h same).models_iff store).trans (models_applyStore g h store).symm)

end Agree

theorem agree_assoc {a b c d : Obj} (h : Hom a b) (f : Hom b c) (g : Hom c d) :
    X.Agree (X.comp (X.comp g f) h) (X.comp g (X.comp f h)) := fun t => by
  rw [act_comp_assoc]
  exact (X.equivalence d).refl _

theorem agree_id_left {a b : Obj} (f : Hom a b) : X.Agree (X.comp (X.id b) f) f := fun t => by
  rw [X.act_comp, X.act_id]
  exact (X.equivalence b).refl _

theorem agree_id_right {a b : Obj} (f : Hom a b) : X.Agree (X.comp f (X.id a)) f := fun t => by
  rw [X.act_comp, X.act_id]
  exact (X.equivalence b).refl _

theorem Iso.agree_inv_hom {a b : Obj} (φ : X.Iso a b) : X.Agree (X.comp φ.inv φ.hom) (X.id a) :=
  fun t => by
    rw [X.act_comp, X.act_id]
    exact φ.inv_hom t

theorem Iso.agree_hom_inv {a b : Obj} (φ : X.Iso a b) : X.Agree (X.comp φ.hom φ.inv) (X.id b) :=
  fun t => by
    rw [X.act_comp, X.act_id]
    exact φ.hom_inv t

end Frames

namespace Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)

/-- The identities a selection writes: those it takes and those it makes. -/
def Writes (selection : Selection O) (o : O) : Prop := o ∈ selection.taken ∨ o ∈ selection.made

/-- **Guards that are local to an explicit region.** A firing's guards at one solution are a
predicate of present occurrences; the interface's `Holds` is that predicate at the state's present
occurrences; it respects the frame equivalence; and it reads present occurrences only inside its
region. -/
structure Guards [P.Guarded] where
  Guard : {s : State} → (f : Firing s) → (b : Obj) → Hom (P.target f) b → Finset O → Prop
  region : {s : State} → (f : Firing s) → (b : Obj) → Hom (P.target f) b → Set O
  holds_iff : ∀ {s : State} (f : Firing s) (b : Obj) (σ : Hom (P.target f) b),
    P.Holds f b σ ↔ Guard f b σ (P.present s)
  respects : ∀ {s : State} (f : Firing s) (b : Obj) {σ τ : Hom (P.target f) b}, X.Agree σ τ →
    ∀ W : Finset O, (Guard f b σ W ↔ Guard f b τ W)
  inside : ∀ {s : State} (f : Firing s) (b : Obj) (σ : Hom (P.target f) b) {W W' : Finset O},
    (∀ o ∈ region f b σ, (o ∈ W ↔ o ∈ W')) → (Guard f b σ W ↔ Guard f b σ W')

/-- **Conservative settlement**: every solution of an admitted firing's information factors through
its settling morphism. -/
def ConservativeSettlement : Prop :=
  ∀ {s : State} (f : Firing s) (admitted : P.Admits f) (b : Obj) (σ : Hom (P.target f) b),
    X.Models σ (P.information f) →
      ∃ ρ : Hom (P.frame (P.result f admitted)) b, X.Agree σ (X.comp ρ (P.settle f admitted))

variable {P}

namespace Guards

variable [P.Guarded]
variable (G : P.Guards)
include G

/-- `Holds` respects the frame equivalence. -/
theorem holds_respects {s : State} (f : Firing s) (b : Obj) {σ τ : Hom (P.target f) b}
    (same : X.Agree σ τ) : P.Holds f b σ ↔ P.Holds f b τ := by
  rw [G.holds_iff, G.holds_iff]
  exact G.respects f b same _

/-- **The guards survive every firing that writes outside their region.** -/
theorem guard_fire {s : State} (f : Firing s) (b : Obj) (σ : Hom (P.target f) b) (W : Finset O)
    (writer : Selection O) (outside : ∀ o ∈ G.region f b σ, ¬ Writes writer o) :
    G.Guard f b σ (fire W (writer.commit (T := Unit))) ↔ G.Guard f b σ W := by
  apply G.inside
  intro o member
  have untouched := outside o member
  simp only [Writes, not_or] at untouched
  rw [mem_fire]
  simp [Selection.commit, untouched.1, untouched.2]

end Guards

/-- **An isomorphism of firings at one state**: an isomorphism of their targets under the state's
frame, carrying the information to information with the same solutions and the guards to the
guards, with the same selection and shapes. -/
structure FiringIso [P.Guarded] (G : P.Guards) {s : State} (f₁ f₂ : Firing s) where
  frame : X.Iso (P.target f₁) (P.target f₂)
  extension : X.Agree (X.comp frame.hom (P.extension f₁)) (P.extension f₂)
  selection : P.selection f₁ = P.selection f₂
  shapes : P.Shapes f₁ ↔ P.Shapes f₂
  information : X.Equivalent (X.applyStore frame.hom (P.information f₁)) (P.information f₂)
  guard : ∀ (b : Obj) (ρ : Hom (P.target f₂) b) (W : Finset O),
    G.Guard f₂ b ρ W ↔ G.Guard f₁ b (X.comp ρ frame.hom) W

/-- **Isomorphic firings are admitted together.** -/
theorem FiringIso.admits_iff [P.Guarded] {G : P.Guards} {s : State} {f₁ f₂ : Firing s} (i : FiringIso G f₁ f₂) :
    P.Admits f₁ ↔ P.Admits f₂ := by
  rw [P.admits_iff, P.admits_iff, i.selection]
  refine and_congr i.shapes (and_congr Iff.rfl (and_congr ?_ ?_))
  · exact (i.frame.solvable_applyStore_iff _).symm.trans (Frames.Equivalent.solvable_iff i.information)
  · constructor
    · intro asked b ρ solved
      have back : X.Models (X.comp ρ i.frame.hom) (P.information f₁) :=
        (Frames.models_applyStore i.frame.hom ρ _).mp ((i.information b ρ).mpr solved)
      exact (G.holds_iff f₂ b ρ).mpr ((i.guard b ρ _).mpr ((G.holds_iff f₁ b _).mp (asked b _ back)))
    · intro asked b σ solved
      have agree : X.Agree (X.comp (X.comp σ i.frame.inv) i.frame.hom) σ :=
        (Frames.agree_assoc i.frame.hom i.frame.inv σ).trans
          ((Frames.Agree.comp_left σ i.frame.agree_inv_hom).trans (Frames.agree_id_right σ))
      have here : X.Models (X.comp σ i.frame.inv) (P.information f₂) :=
        (i.information b _).mp ((Frames.models_applyStore i.frame.hom _ _).mpr
          ((agree.models_iff _).mpr solved))
      have holds := (i.guard b _ _).mp ((G.holds_iff f₂ b _).mp (asked b _ here))
      exact (G.holds_iff f₁ b σ).mpr ((G.respects f₁ b agree _).mp holds)

/-- **Admission of `f` after `g`, stated without a residual**: `f`'s shapes; its selection enabled at
`g`'s result; a solution of `f`'s information that agrees on the state's frame with a solution of
`g`'s result knowledge; and `f`'s guards, read at the occurrences present after `g`, at every such
pair. -/
def AdmitsAfter [P.Guarded] (G : P.Guards) {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) :
    Prop :=
  P.Shapes f ∧
    Enabled (fun _ : O => ()) (P.present (P.result g admitted)) ((P.selection f).commit (T := Unit)) ∧
    (∃ (b : Obj) (σ : Hom (P.target f) b) (τ : Hom (P.frame (P.result g admitted)) b),
      X.Models σ (P.information f) ∧ X.Models τ (P.knowledge (P.result g admitted)) ∧
        X.Agree (X.comp σ (P.extension f)) (X.comp τ (P.along g admitted))) ∧
    ∀ (b : Obj) (σ : Hom (P.target f) b) (τ : Hom (P.frame (P.result g admitted)) b),
      X.Models σ (P.information f) → X.Models τ (P.knowledge (P.result g admitted)) →
        X.Agree (X.comp σ (P.extension f)) (X.comp τ (P.along g admitted)) →
          G.Guard f b σ (P.present (P.result g admitted))

/-- **Settlement chooses no solution**: under conservative settlement, the result asks exactly what
the information asks. -/
theorem entails_result_iff [P.Exact] (conservative : P.ConservativeSettlement) {s : State} (f : Firing s)
    (admitted : P.Admits f) (Q : (b : Obj) → Hom (P.target f) b → Prop)
    (respects : ∀ (b : Obj) (σ τ : Hom (P.target f) b), X.Agree σ τ → (Q b σ ↔ Q b τ)) :
    X.Entails (P.knowledge (P.result f admitted)) (fun b ρ => Q b (X.comp ρ (P.settle f admitted))) ↔
      X.Entails (P.information f) Q := by
  constructor
  · intro asked b σ solved
    obtain ⟨ρ, agree⟩ := conservative f admitted b σ solved
    have result : X.Models ρ (P.knowledge (P.result f admitted)) := by
      exact Exact.exactness (P := P) f (P.prepares admitted) ρ ((agree.models_iff _).mp solved)
    exact (respects b _ _ agree).mpr (asked b ρ result)
  · intro asked b ρ solved
    exact asked b _ (P.result_refines f (P.prepares admitted) ρ solved)

/-- Under conservative settlement, the result is solvable exactly when the information is. -/
theorem solvable_result_iff [P.Exact] (conservative : P.ConservativeSettlement) {s : State} (f : Firing s)
    (admitted : P.Admits f) :
    X.Solvable (P.knowledge (P.result f admitted)) ↔ X.Solvable (P.information f) := by
  constructor
  · rintro ⟨b, ρ, solved⟩
    exact ⟨b, _, P.result_refines f (P.prepares admitted) ρ solved⟩
  · rintro ⟨b, σ, solved⟩
    obtain ⟨ρ, agree⟩ := conservative f admitted b σ solved
    refine ⟨b, ρ, ?_⟩
    exact Exact.exactness (P := P) f (P.prepares admitted) ρ ((agree.models_iff _).mp solved)

end Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing}

namespace Transport

/-- **Residual coherence**: the residual of `f` after an admitted `g` is `f` carried along `g`. Its
target amalgamates `f`'s target with `g`'s result over the state's frame, for solutions; its
information is `f`'s carried, together with `g`'s result knowledge; its shapes are `f`'s; its guards
are `f`'s pulled back. -/
structure Coherent [P.Guarded] (T : Transport P) (G : P.Guards) where
  carry : {s : State} → (g : Firing s) → (admitted : P.Admits g) → (f : Firing s) →
    Hom (P.target f) (P.target (T.residual g admitted f))
  square : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s),
    X.Agree (X.comp (carry g admitted f) (P.extension f))
      (X.comp (P.extension (T.residual g admitted f)) (P.along g admitted))
  amalgamate : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) (b : Obj)
      (σ : Hom (P.target f) b) (τ : Hom (P.frame (P.result g admitted)) b),
      X.Agree (X.comp σ (P.extension f)) (X.comp τ (P.along g admitted)) →
      ∃ ρ : Hom (P.target (T.residual g admitted f)) b,
        X.Agree (X.comp ρ (carry g admitted f)) σ ∧
          X.Agree (X.comp ρ (P.extension (T.residual g admitted f))) τ
  separated : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) (b : Obj)
      (ρ ρ' : Hom (P.target (T.residual g admitted f)) b),
      X.Agree (X.comp ρ (carry g admitted f)) (X.comp ρ' (carry g admitted f)) →
      X.Agree (X.comp ρ (P.extension (T.residual g admitted f)))
        (X.comp ρ' (P.extension (T.residual g admitted f))) →
      X.Agree ρ ρ'
  information : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s),
    X.Equivalent (P.information (T.residual g admitted f))
      (X.applyStore (carry g admitted f) (P.information f) ++
        X.applyStore (P.extension (T.residual g admitted f)) (P.knowledge (P.result g admitted)))
  shapes : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s),
    P.Shapes (T.residual g admitted f) ↔ P.Shapes f
  guard : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) (b : Obj)
    (ρ : Hom (P.target (T.residual g admitted f)) b) (W : Finset O),
    G.Guard (T.residual g admitted f) b ρ W ↔ G.Guard f b (X.comp ρ (carry g admitted f)) W

/-- **A lawful transport**: coherent residuals, conservative settlement, and results that respect
isomorphism of firings. -/
structure Lawful [P.Guarded] (T : Transport P) (G : P.Guards) where
  coherent : T.Coherent G
  conservative : P.ConservativeSettlement
  canonical : ∀ {s : State} {f₁ f₂ : Firing s}, Step.FiringIso G f₁ f₂ →
    ∀ (first : P.Admits f₁) (second : P.Admits f₂), T.Same (P.result f₁ first) (P.result f₂ second)

variable [P.Guarded] {T T' : Transport P} {G : P.Guards}

namespace Coherent

variable (C : T.Coherent G)
include C

/-- A solution of a residual's information is a solution of `f`'s information and of `g`'s result
knowledge, read through the two restrictions. -/
theorem models_iff {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) {b : Obj}
    (ρ : Hom (P.target (T.residual g admitted f)) b) :
    X.Models ρ (P.information (T.residual g admitted f)) ↔
      X.Models (X.comp ρ (C.carry g admitted f)) (P.information f) ∧
        X.Models (X.comp ρ (P.extension (T.residual g admitted f))) (P.knowledge (P.result g admitted)) := by
  rw [C.information g admitted f b ρ, Frames.models_append, Frames.models_applyStore,
    Frames.models_applyStore]

/-- The two restrictions of a solution agree on the state's frame. -/
theorem restrictions_agree {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) {b : Obj}
    (ρ : Hom (P.target (T.residual g admitted f)) b) :
    X.Agree (X.comp (X.comp ρ (C.carry g admitted f)) (P.extension f))
      (X.comp (X.comp ρ (P.extension (T.residual g admitted f))) (P.along g admitted)) :=
  (Frames.agree_assoc _ _ ρ).trans
    ((Frames.Agree.comp_left ρ (C.square g admitted f)).trans (Frames.agree_assoc _ _ ρ).symm)

/-- **Admission of a coherent residual mentions no residual.** -/
theorem admits_iff {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) :
    P.Admits (T.residual g admitted f) ↔ Step.AdmitsAfter G g admitted f := by
  rw [P.admits_iff, C.shapes, T.selection_residual]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · constructor
    · rintro ⟨b, ρ, solved⟩
      obtain ⟨first, second⟩ := (C.models_iff g admitted f ρ).mp solved
      exact ⟨b, _, _, first, second, C.restrictions_agree g admitted f ρ⟩
    · rintro ⟨b, σ, τ, first, second, agree⟩
      obtain ⟨ρ, throughCarry, throughExtension⟩ := C.amalgamate g admitted f b σ τ agree
      exact ⟨b, ρ, (C.models_iff g admitted f ρ).mpr
        ⟨(throughCarry.models_iff _).mpr first, (throughExtension.models_iff _).mpr second⟩⟩
  · constructor
    · intro asked b σ τ first second agree
      obtain ⟨ρ, throughCarry, throughExtension⟩ := C.amalgamate g admitted f b σ τ agree
      have solved := (C.models_iff g admitted f ρ).mpr
        ⟨(throughCarry.models_iff _).mpr first, (throughExtension.models_iff _).mpr second⟩
      have holds := (C.guard g admitted f b ρ _).mp ((G.holds_iff _ b ρ).mp (asked b ρ solved))
      exact (G.respects f b throughCarry _).mp holds
    · intro asked b ρ solved
      obtain ⟨first, second⟩ := (C.models_iff g admitted f ρ).mp solved
      exact (G.holds_iff _ b ρ).mpr ((C.guard g admitted f b ρ _).mpr
        (asked b _ _ first second (C.restrictions_agree g admitted f ρ)))

/-- **Locality, read on the residual**: when `g` writes outside `f`'s region, the residual's `Holds`
is `f`'s guard read at the occurrences present before `g`. -/
theorem holds_residual_iff {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) {b : Obj}
    (ρ : Hom (P.target (T.residual g admitted f)) b)
    (outside : ∀ o ∈ G.region f b (X.comp ρ (C.carry g admitted f)), ¬ Step.Writes (P.selection g) o) :
    P.Holds (T.residual g admitted f) b ρ ↔ G.Guard f b (X.comp ρ (C.carry g admitted f)) (P.present s) := by
  rw [G.holds_iff, C.guard, P.present_result]
  exact G.guard_fire f b _ (P.present s) (P.selection g) outside

/-- **Two coherent residuals are isomorphic firings**: the amalgamation property gives the
morphisms both ways, and separation makes them inverse. -/
theorem firingIso (C' : T'.Coherent G) {s : State} (g : Firing s) (admitted : P.Admits g)
    (f : Firing s) :
    Nonempty (Step.FiringIso G (T.residual g admitted f) (T'.residual g admitted f)) := by
  obtain ⟨θ, θCarry, θExtension⟩ := C.amalgamate g admitted f _ (C'.carry g admitted f)
    (P.extension (T'.residual g admitted f)) (C'.square g admitted f)
  obtain ⟨θ', θ'Carry, θ'Extension⟩ := C'.amalgamate g admitted f _ (C.carry g admitted f)
    (P.extension (T.residual g admitted f)) (C.square g admitted f)
  have back : X.Agree (X.comp θ' θ) (X.id _) := by
    apply C.separated g admitted f _ _ _
    · exact (Frames.agree_assoc _ _ _).trans ((Frames.Agree.comp_left θ' θCarry).trans
        (θ'Carry.trans (Frames.agree_id_left _).symm))
    · exact (Frames.agree_assoc _ _ _).trans ((Frames.Agree.comp_left θ' θExtension).trans
        (θ'Extension.trans (Frames.agree_id_left _).symm))
  have forth : X.Agree (X.comp θ θ') (X.id _) := by
    apply C'.separated g admitted f _ _ _
    · exact (Frames.agree_assoc _ _ _).trans ((Frames.Agree.comp_left θ θ'Carry).trans
        (θCarry.trans (Frames.agree_id_left _).symm))
    · exact (Frames.agree_assoc _ _ _).trans ((Frames.Agree.comp_left θ θ'Extension).trans
        (θExtension.trans (Frames.agree_id_left _).symm))
  refine ⟨⟨⟨θ, θ', fun t => ?_, fun t => ?_⟩, θExtension,
    (T.selection_residual g admitted f).trans (T'.selection_residual g admitted f).symm,
    (C.shapes g admitted f).trans (C'.shapes g admitted f).symm, ?_, ?_⟩⟩
  · have law := back t
    rw [X.act_comp, X.act_id] at law
    exact law
  · have law := forth t
    rw [X.act_comp, X.act_id] at law
    exact law
  · intro b ρ
    have throughCarry : X.Agree (X.comp (X.comp ρ θ) (C.carry g admitted f))
        (X.comp ρ (C'.carry g admitted f)) :=
      (Frames.agree_assoc _ _ _).trans (Frames.Agree.comp_left ρ θCarry)
    have throughExtension : X.Agree (X.comp (X.comp ρ θ) (P.extension (T.residual g admitted f)))
        (X.comp ρ (P.extension (T'.residual g admitted f))) :=
      (Frames.agree_assoc _ _ _).trans (Frames.Agree.comp_left ρ θExtension)
    rw [Frames.models_applyStore, C.models_iff g admitted f, C'.models_iff g admitted f,
      throughCarry.models_iff, throughExtension.models_iff]
  · intro b ρ W
    refine (C'.guard g admitted f b ρ W).trans ((G.respects f b ?_ W).trans
      (C.guard g admitted f b (X.comp ρ θ) W).symm)
    exact (Frames.Agree.comp_left ρ θCarry.symm).trans (Frames.agree_assoc _ _ _).symm

end Coherent

/-- One direction of the content theorem. -/
theorem Lawful.independent_of (L : T.Lawful G) (L' : T'.Lawful G)
    (classes : ∀ s t : State, T.Same s t → T'.Same s t) {s : State} {f g : Firing s}
    (independent : T.Independent s f g) : T'.Independent s f g := by
  obtain ⟨first, second, afterFirst, afterSecond, close⟩ := independent
  obtain ⟨i⟩ := L.coherent.firingIso L'.coherent f first g
  obtain ⟨j⟩ := L.coherent.firingIso L'.coherent g second f
  have afterFirst' := i.admits_iff.mp afterFirst
  have afterSecond' := j.admits_iff.mp afterSecond
  exact ⟨first, second, afterFirst', afterSecond',
    (L'.canonical i afterFirst afterFirst').symm.trans
      ((classes _ _ close).trans (L'.canonical j afterSecond afterSecond'))⟩

/-- **The content theorem: under the laws, independence does not depend on the choice of
residual.** Two lawful transports with the same state classes have the same independence. -/
theorem Lawful.independent_iff (L : T.Lawful G) (L' : T'.Lawful G)
    (classes : ∀ s t : State, T.Same s t ↔ T'.Same s t) {s : State} {f g : Firing s} :
    T.Independent s f g ↔ T'.Independent s f g :=
  ⟨L.independent_of L' fun s t => (classes s t).mp, L'.independent_of L fun s t => (classes s t).mpr⟩

/-- Under the laws, admission of a residual is the same for every lawful choice. -/
theorem Lawful.admits_residual_iff (L : T.Lawful G) (L' : T'.Lawful G) {s : State} (g : Firing s)
    (admitted : P.Admits g) (f : Firing s) :
    P.Admits (T.residual g admitted f) ↔ P.Admits (T'.residual g admitted f) :=
  (L.coherent.admits_iff g admitted f).trans (L'.coherent.admits_iff g admitted f).symm

omit [P.Guarded] in
/-- **The same transport with another residual.** -/
def withResidual (T : Transport P)
    (residual : {s : State} → (g : Firing s) → (admitted : P.Admits g) → Firing s →
      Firing (P.result g admitted))
    (selection_residual : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s),
      P.selection (residual g admitted f) = P.selection f)
    (move_residual : ∀ {s t : State} (i : T.Iso s t) (g : Firing s) (admitted : P.Admits g)
      (f : Firing s), T.Alike (T.move (T.result_move i g admitted) (residual g admitted f))
        (residual (T.move i g) ((T.admits_move i g).mpr admitted) (T.move i f))) :
    Transport P :=
  { T with
    residual := residual
    selection_residual := selection_residual
    move_residual := move_residual }

/-- **Replacing the residual of a lawful transport by another lawful one keeps independence.** -/
theorem Lawful.independent_withResidual_iff
    {residual : {s : State} → (g : Firing s) → (admitted : P.Admits g) → Firing s →
      Firing (P.result g admitted)}
    {selection_residual : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s),
      P.selection (residual g admitted f) = P.selection f}
    {move_residual : ∀ {s t : State} (i : T.Iso s t) (g : Firing s) (admitted : P.Admits g)
      (f : Firing s), T.Alike (T.move (T.result_move i g admitted) (residual g admitted f))
        (residual (T.move i g) ((T.admits_move i g).mpr admitted) (T.move i f))}
    (L : T.Lawful G) (L' : (T.withResidual residual selection_residual move_residual).Lawful G)
    {s : State} {f g : Firing s} :
    (T.withResidual residual selection_residual move_residual).Independent s f g ↔ T.Independent s f g :=
  L'.independent_iff L fun _ _ => Iff.rfl

end Transport

#print axioms Frames.Agree.equivalent
#print axioms Step.Guards.guard_fire
#print axioms Step.FiringIso.admits_iff
#print axioms Step.entails_result_iff
#print axioms Step.solvable_result_iff
#print axioms Transport.Coherent.admits_iff
#print axioms Transport.Coherent.holds_residual_iff
#print axioms Transport.Coherent.firingIso
#print axioms Transport.Lawful.independent_iff
#print axioms Transport.Lawful.admits_residual_iff
#print axioms Transport.Lawful.independent_withResidual_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
