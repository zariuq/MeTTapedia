import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull
import Mettapedia.OSLF.PresheafNativeType.InternalLanguage
import Mathlib.CategoryTheory.Subfunctor.Equalizer

/-!
# A firing's information as a comprehension, and typing after the match

The frames of the dependent full step are the contexts of the typed contextual category, and a
morphism of frames from `Δ` to `Θ` is a substitution `τ : Θ ⟶ Δ`. So the solutions of a store at
`Δ` are elements of the representable presheaf `y Δ`, and they form a predicate on it in the
presheaf topos of native type theory.

* **The comprehension of a store** (`solutions`): at `Θ`, the substitutions `τ : Θ ⟶ Δ` solving
  every equation. It is a subfunctor of `y Δ` because solutions survive further substitution.
* **It is the joint equalizer of the names of the equations** (`factors_iff`, `solutions_cons`): a
  judged term of `Δ` names, by Yoneda, a natural transformation from `y Δ` to the presheaf of judged
  terms up to typed equality (`name`). A natural transformation into `y Δ` factors through the
  solutions exactly when it equalizes the names of both sides of every equation, and the solutions of
  one more equation are Mathlib's subfunctor equalizer inside the solutions of the rest.
* **Made rows form a presheaf** (`rows`): a formed type and a raw code over each frame. The rows
  whose code is typed at their type are a subfunctor (`typedRows`), and a made row of `Δ` names a
  natural transformation `y Δ ⟶ rows` (`rowName`).
* **Typed in the frame** (`TypedInFrame`): the row's name factors through the typed rows. This is
  exactly the step's present rule, `Make.WellTyped` (`typedInFrame_iff`).
* **Typed after the match** (`TypedAfterMatch`): the row's name, restricted to the comprehension of
  the information, factors through the typed rows. By the image-comprehension adjunction of native
  type theory this is the inclusion of the comprehension in the row's typing predicate
  (`typedAfterMatch_iff_le`), and it is exactly "typed at every solution" (`typedAfterMatch_iff`).

**Conservativity and controls.** A row typed in the frame is typed after every match
(`typedAfterMatch_of_wellTyped`); after the empty match the two notions coincide
(`typedAfterMatch_nil_iff`); more information types more rows (`TypedAfterMatch.mono`). A store with
no solution types every row (`typedAfterMatch_of_not_solvable`): the comprehension is empty, so
admission must keep asking solvability, as the step does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-! ## The comprehension of a store -/

section Solutions

/-- **The comprehension of a store** at the frame `Δ`: at each later frame `Θ`, the substitutions
`τ : Θ ⟶ Δ` that solve every equation of the store. A predicate on the representable presheaf. -/
def solutions {Δ : Context rules} (I : EquationStore (TotalTerm Δ)) : Subfunctor (yoneda.obj Δ) where
  obj _ := {τ | (frames levels).Models τ I}
  map g _ solved := Frames.models_comp solved g.unop

theorem mem_solutions {Δ Θ : Context rules} (I : EquationStore (TotalTerm Δ)) (τ : Θ ⟶ Δ) :
    τ ∈ (solutions levels I).obj (op Θ) ↔ (frames levels).Models τ I := Iff.rfl

/-- **The name of a judged term** of `Δ`: by Yoneda, the natural transformation from `y Δ` to the
presheaf of judged terms up to typed equality that sends `τ` to the class of the substituted term. -/
def name {Δ : Context rules} (t : TotalTerm Δ) : yoneda.obj Δ ⟶ QTerm.rawPresheaf levels :=
  yonedaEquiv.symm (QTerm.mk levels t.2)

theorem name_app {Δ Θ : Context rules} (t : TotalTerm Δ) (τ : Θ ⟶ Δ) :
    (name levels t).app (op Θ) τ = QTerm.mk levels (t.reindex τ).2 := rfl

/-- **A substitution solves an equation exactly when it equalizes the names of its two sides.** -/
theorem solves_iff {Δ Θ : Context rules} (τ : Θ ⟶ Δ) (e : Equation (TotalTerm Δ)) :
    (frames levels).Solves τ e ↔ (name levels e.1).app (op Θ) τ = (name levels e.2).app (op Θ) τ := by
  rw [name_app, name_app]
  exact equivalent_iff_classes levels _ _

/-- **The comprehension is the joint equalizer of the names**: a natural transformation into `y Δ`
factors through the solutions of a store exactly when it equalizes the names of the two sides of
every equation. The factorization is unique, the inclusion being a monomorphism. -/
theorem factors_iff {Δ : Context rules} (I : EquationStore (TotalTerm Δ))
    {G : (Context rules)ᵒᵖ ⥤ Type} (g : G ⟶ yoneda.obj Δ) :
    (∃ lift : G ⟶ (solutions levels I).toFunctor, lift ≫ (solutions levels I).ι = g) ↔
      ∀ e ∈ I, g ≫ name levels e.1 = g ≫ name levels e.2 := by
  refine (Mettapedia.OSLF.PresheafNativeType.imageComprehension_iff g (solutions levels I)).symm.trans ?_
  constructor
  · intro inside e member
    ext Θ x
    exact (solves_iff levels (g.app Θ x) e).mp
      (inside Θ (Set.mem_range_self (f := g.app Θ) x) e member)
  · intro equal Θ τ inRange
    obtain ⟨x, rfl⟩ := inRange
    intro e member
    exact (solves_iff levels (g.app Θ x) e).mpr
      (ConcreteCategory.congr_hom (congr_app (equal e member) Θ) x)

/-- **One more equation is one more equalizer**: the solutions of `e :: I` are Mathlib's equalizer
subfunctor, inside the solutions of `I`, of the names of the two sides of `e`. -/
theorem solutions_cons {Δ : Context rules} (e : Equation (TotalTerm Δ))
    (I : EquationStore (TotalTerm Δ)) :
    solutions levels (e :: I) = Subfunctor.equalizer ((solutions levels I).ι ≫ name levels e.1)
      ((solutions levels I).ι ≫ name levels e.2) := by
  ext Θ τ
  constructor
  · intro solved
    have rest : τ ∈ (solutions levels I).obj Θ := fun e' member => solved e' (List.mem_cons_of_mem _ member)
    exact Exists.intro rest ((solves_iff levels τ e).mp (solved e List.mem_cons_self))
  · intro inside
    obtain ⟨rest, first⟩ := inside
    intro e' member
    rcases List.mem_cons.mp member with same | later
    · rw [same]
      exact (solves_iff levels τ e).mpr first
    · exact rest e' later

/-- The empty store is solved everywhere: its comprehension is the whole representable. -/
theorem solutions_nil (Δ : Context rules) : solutions levels ([] : EquationStore (TotalTerm Δ)) = ⊤ := by
  ext Θ τ
  exact ⟨fun _ => trivial, fun _ => Frames.models_nil _⟩

/-- More information, fewer solutions. -/
theorem solutions_anti {Δ : Context rules} {I J : EquationStore (TotalTerm Δ)}
    (inside : ∀ e ∈ I, e ∈ J) : solutions levels J ≤ solutions levels I :=
  fun _ _ solved => Frames.models_of_subset inside solved

/-- **Stores side by side meet**: the comprehension of `I ++ J` is the meet of the two. -/
theorem solutions_append {Δ : Context rules} (I J : EquationStore (TotalTerm Δ)) :
    solutions levels (I ++ J) = solutions levels I ⊓ solutions levels J := by
  ext Θ τ
  exact Frames.models_append (X := frames levels) τ I J

/-- **Reindexing a store pulls back its comprehension**: the solutions of `K` transported along
`w : Δ ⟶ Γ` are the substitutions whose composite with `w` solves `K`. -/
theorem solutions_applyStore {Γ Δ : Context rules} (w : Δ ⟶ Γ) (K : EquationStore (TotalTerm Γ)) :
    solutions levels ((frames levels).applyStore w K) = (solutions levels K).preimage (yoneda.map w) := by
  ext Θ τ
  exact Frames.models_applyStore (X := frames levels) w τ K

/-- A store is solvable exactly when its comprehension is not empty. -/
theorem solvable_iff_ne_bot {Δ : Context rules} (I : EquationStore (TotalTerm Δ)) :
    (frames levels).Solvable I ↔ solutions levels I ≠ ⊥ := by
  constructor
  · rintro ⟨Θ, τ, solved⟩ empty
    have inside : τ ∈ (solutions levels I).obj (op Θ) := solved
    rw [empty] at inside
    exact inside
  · intro nonempty
    by_contra none
    apply nonempty
    ext Θ τ
    exact ⟨fun solved => none ⟨Θ.unop, τ, solved⟩, fun absurd => absurd.elim⟩

end Solutions

/-! ## Made rows and their typing -/

section Rows

omit [UniverseLevel.LevelOrder L] in
theorem make_ext {Δ : Context rules} {m m' : Make Δ} (sameType : m.type = m'.type)
    (sameCode : m.code = m'.code) : m = m' := by
  cases m
  cases m'
  cases sameType
  cases sameCode
  rfl

variable (rules) in
/-- **The presheaf of made rows**: a formed type and a raw code over each frame, both substituted. -/
def rows : (Context rules)ᵒᵖ ⥤ Type where
  obj Θ := Make Θ.unop
  map g := TypeCat.ofHom fun m => ⟨m.type.reindex g.unop, subst g.unop.substitution m.code⟩
  map_id _ := by
    ext m
    exact make_ext (TypeOver.reindex_id m.type) (subst_ids m.code)
  map_comp f g := by
    ext m
    exact make_ext (TypeOver.reindex_comp m.type g.unop f.unop)
      (subst_subComp g.unop.substitution f.unop.substitution m.code).symm

variable (rules) in
/-- **The typed rows**: those whose code is typed at their type, `Make.WellTyped`. Typing survives
substitution, so they form a subfunctor. -/
def typedRows : Subfunctor (rows rules) where
  obj _ := {m | m.WellTyped}
  map g _ typed := typed.substitute g.unop.typed

/-- **The name of a made row** of `Δ`: by Yoneda, `y Δ ⟶ rows`, the row substituted along `τ`. -/
def rowName {Δ : Context rules} (m : Make Δ) : yoneda.obj Δ ⟶ rows rules :=
  yonedaEquiv.symm m

theorem rowName_app {Δ Θ : Context rules} (m : Make Δ) (τ : Θ ⟶ Δ) :
    (rowName m).app (op Θ) τ = (⟨m.type.reindex τ, subst τ.substitution m.code⟩ : Make Θ) := rfl

/-- **The typing predicate of a made row**: the substitutions along which it is a typed row. It is
the pullback of the typed rows along the row's name (the change of base of native type theory). -/
def typing {Δ : Context rules} (m : Make Δ) : Subfunctor (yoneda.obj Δ) :=
  (typedRows rules).preimage (rowName m)

theorem mem_typing {Δ Θ : Context rules} (m : Make Δ) (τ : Θ ⟶ Δ) :
    τ ∈ (typing m).obj (op Θ) ↔
      Typed rules Θ.raw (subst τ.substitution m.code) (m.type.reindex τ).code := Iff.rfl

/-- **Typed in the frame**: the row's name factors through the typed rows. -/
def TypedInFrame {Δ : Context rules} (m : Make Δ) : Prop :=
  ∃ lift : yoneda.obj Δ ⟶ (typedRows rules).toFunctor, lift ≫ (typedRows rules).ι = rowName m

/-- **Typed after the match**: the row's name, restricted to the comprehension of the information,
factors through the typed rows. -/
def TypedAfterMatch {Δ : Context rules} (I : EquationStore (TotalTerm Δ)) (m : Make Δ) : Prop :=
  ∃ lift : (solutions levels I).toFunctor ⟶ (typedRows rules).toFunctor,
    lift ≫ (typedRows rules).ι = (solutions levels I).ι ≫ rowName m

omit [UniverseLevel.LevelOrder L] in
/-- **Typed in the frame is the step's present rule**: the name factors exactly when the made code is
typed at its type in the frame. -/
theorem typedInFrame_iff {Δ : Context rules} (m : Make Δ) : TypedInFrame m ↔ m.WellTyped := by
  refine (Mettapedia.OSLF.PresheafNativeType.imageComprehension_iff (rowName m) (typedRows rules)).symm.trans ?_
  constructor
  · intro le
    have atIdentity : Typed rules Δ.raw (subst ids m.code) (m.type.reindex (𝟙 Δ)).code :=
      le (op Δ) (Set.mem_range_self (f := (rowName m).app (op Δ)) (𝟙 Δ))
    rw [subst_ids, TypeOver.reindex_id] at atIdentity
    exact atIdentity
  · intro typed Θ x inRange
    obtain ⟨τ, rfl⟩ := inRange
    exact typed.substitute τ.typed

/-- **Typed after the match is inclusion of the comprehension in the typing predicate**, by the
image-comprehension adjunction of native type theory. -/
theorem typedAfterMatch_iff_le {Δ : Context rules} (I : EquationStore (TotalTerm Δ)) (m : Make Δ) :
    TypedAfterMatch levels I m ↔ solutions levels I ≤ typing m := by
  refine (Mettapedia.OSLF.PresheafNativeType.imageComprehension_iff
    ((solutions levels I).ι ≫ rowName m) (typedRows rules)).symm.trans ?_
  show Subfunctor.range ((solutions levels I).ι ≫ rowName m) ≤ typedRows rules ↔ _
  rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff]
  rfl

/-- **Typed after the match is typed at every solution**: the made code, substituted along any
solution of the information, is typed at the substituted type. -/
theorem typedAfterMatch_iff {Δ : Context rules} (I : EquationStore (TotalTerm Δ)) (m : Make Δ) :
    TypedAfterMatch levels I m ↔ ∀ (Θ : Context rules) (τ : Θ ⟶ Δ), (frames levels).Models τ I →
      Typed rules Θ.raw (subst τ.substitution m.code) (m.type.reindex τ).code := by
  rw [typedAfterMatch_iff_le]
  constructor
  · intro le Θ τ solved
    exact le (op Θ) solved
  · intro typed Θ τ solved
    exact typed Θ.unop τ solved

/-- **Conservativity**: a row typed in the frame is typed after every match. -/
theorem typedAfterMatch_of_wellTyped {Δ : Context rules} (I : EquationStore (TotalTerm Δ))
    {m : Make Δ} (typed : m.WellTyped) : TypedAfterMatch levels I m :=
  (typedAfterMatch_iff levels I m).mpr fun _ τ _ => typed.substitute τ.typed

/-- **After the empty match, typed after the match is typed in the frame**: the identity solves the
empty store. -/
theorem typedAfterMatch_nil_iff {Δ : Context rules} (m : Make Δ) :
    TypedAfterMatch levels ([] : EquationStore (TotalTerm Δ)) m ↔ m.WellTyped := by
  constructor
  · intro typed
    have atIdentity : Typed rules Δ.raw (subst ids m.code) (m.type.reindex (𝟙 Δ)).code :=
      (typedAfterMatch_iff levels [] m).mp typed Δ (𝟙 Δ) (Frames.models_nil _)
    rw [subst_ids, TypeOver.reindex_id] at atIdentity
    exact atIdentity
  · exact typedAfterMatch_of_wellTyped levels []

/-- **More information types more rows.** -/
theorem TypedAfterMatch.mono {Δ : Context rules} {I J : EquationStore (TotalTerm Δ)}
    (inside : ∀ e ∈ I, e ∈ J) {m : Make Δ} (typed : TypedAfterMatch levels I m) :
    TypedAfterMatch levels J m :=
  (typedAfterMatch_iff levels J m).mpr fun Θ τ solved =>
    (typedAfterMatch_iff levels I m).mp typed Θ τ (Frames.models_of_subset inside solved)

/-- **Control: a store with no solution types every row.** Its comprehension is empty, so the
inclusion holds vacuously; admission must keep asking for solvability. -/
theorem typedAfterMatch_of_not_solvable {Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    (none : ¬ (frames levels).Solvable I) (m : Make Δ) : TypedAfterMatch levels I m :=
  (typedAfterMatch_iff levels I m).mpr fun Θ τ solved => (none ⟨Θ, τ, solved⟩).elim

end Rows

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.solutions
#print axioms NativeTypesOnTheStep.solves_iff
#print axioms NativeTypesOnTheStep.factors_iff
#print axioms NativeTypesOnTheStep.solutions_cons
#print axioms NativeTypesOnTheStep.solutions_nil
#print axioms NativeTypesOnTheStep.solvable_iff_ne_bot
#print axioms NativeTypesOnTheStep.rows
#print axioms NativeTypesOnTheStep.typedRows
#print axioms NativeTypesOnTheStep.typedInFrame_iff
#print axioms NativeTypesOnTheStep.typedAfterMatch_iff_le
#print axioms NativeTypesOnTheStep.typedAfterMatch_iff
#print axioms NativeTypesOnTheStep.typedAfterMatch_of_wellTyped
#print axioms NativeTypesOnTheStep.typedAfterMatch_nil_iff
#print axioms NativeTypesOnTheStep.TypedAfterMatch.mono
#print axioms NativeTypesOnTheStep.typedAfterMatch_of_not_solvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
