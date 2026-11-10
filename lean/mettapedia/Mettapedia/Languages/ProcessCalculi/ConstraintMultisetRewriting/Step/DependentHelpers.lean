import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFrames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualDiamond

/-!
# The candidate step at dependently typed frames: firings that make fresh helpers

A **helper firing** at a state whose frame is the telescope `Γ` makes one occurrence and one fresh
helper `x : A`, where `A` is a formed type over `Γ`, and tells the helper's value `v : A`: its
information is the old knowledge read in `Γ.A` together with the definition `x ≐ v`
(`helperStep`). This is the dependent counterpart of `Helpers.helperStep`.

* **Admission** (`admits_iff`): solvable knowledge, a fresh occurrence, and guards asked by the
  knowledge. The helper never constrains the old frame, because every solution of the knowledge
  extends by the value (`extendSolution_models`).
* **Transport** (`helperTransport`) along strict isomorphisms of telescopes (`Strict`): a firing moves
  by reindexing its type, value and guards; its result moves along the isomorphism lifted under the
  new variable (`liftIso`). The transport groupoid uses isomorphisms whose inverse laws hold on the
  nose, so the functor laws of moving firings hold on the nose. Transport along every isomorphism of
  states, up to conversion and with occurrences renamed, is `conversionTransport` (`DependentConversion`).
* **The swap** (`swapIso`): `Γ.A.B ≅ Γ.B.A` for two types `A`, `B` over `Γ`, fixing every old
  variable (`swap_fixes`). Diamonds close up to this swap (`helper_closes`), and independence is
  solvable knowledge, fresh distinct occurrences and both guards asked (`independent_iff`).
* **When the swap exists.** In a run `f ; g₁`, the second firing lives at the frame `f` made, so its
  type may mention `f`'s helper. For every transport, a two-firing run swaps exactly when its second
  firing is alike to the residual of a firing at the start with which the first is independent
  (`swap_exists_iff`). For helper firings, `g₁` is a residual exactly when substituting `f`'s value for
  `f`'s helper fixes it (`residual_exists_iff`), so the run swaps exactly when that substitution fixes
  `g₁` and `f` is independent of `g₁` read at the start (`swap_exists_iff_fixed`). A residual's type is
  a weakening; when the type of `g₁` is not, no swap exists (`no_swap_of_not_weakened`).

Controls (`Consumer`, over a two-head rule package): two independent firings at the empty frame
whose composite states differ and are isomorphic (`composites_differ`). The dependent negative
control, `y : Id A x x` for the first helper `x`, is in `DependentControls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head : Type} {rules : Rules Head}

/-! ## Morphisms into an extended frame -/

/-- A morphism into an extended frame is determined by its projection and its newest component. -/
theorem hom_ext_extend {X Γ : Context rules} {A : TypeOver Γ} {f g : X ⟶ extend Γ A}
    (base : f ≫ projectionHom Γ A = g ≫ projectionHom Γ A)
    (newestSame : f.substitution 0 = g.substitution 0) : f = g := by
  apply FormationSensitiveContextual.Hom.ext
  funext i
  refine Fin.cases newestSame (fun j => ?_) i
  exact congrFun (congrArg FormationSensitiveContextual.Hom.substitution base) j

/-- A substitution lifted under one more variable, whose type is the reindexed type. -/
def lift {Γ Δ : Context rules} (σ : Δ ⟶ Γ) {A : TypeOver Γ} {B : TypeOver Δ}
    (same : B = A.reindex σ) : extend Δ B ⟶ extend Γ A :=
  pair (projectionHom Δ B ≫ σ) ((newest Δ B).cast (by subst same; exact (A.reindex_comp _ σ).symm))

theorem lift_projection {Γ Δ : Context rules} (σ : Δ ⟶ Γ) {A : TypeOver Γ} {B : TypeOver Δ}
    (same : B = A.reindex σ) : lift σ same ≫ projectionHom Γ A = projectionHom Δ B ≫ σ :=
  pair_projection _ _

theorem lift_zero {Γ Δ : Context rules} (σ : Δ ⟶ Γ) {A : TypeOver Γ} {B : TypeOver Δ}
    (same : B = A.reindex σ) : (lift σ same).substitution 0 = .var 0 :=
  Term.cast_code _ _

/-- **The definition `x ≐ v` is natural along lifted substitutions.** -/
theorem definition_lift {Γ Δ : Context rules} (σ : Δ ⟶ Γ) {A : TypeOver Γ} (v : Term Γ A) :
    (frames rules).applyStore (lift σ rfl) [definition Γ v] = [definition Δ (v.reindex σ)] := by
  have first : (Entry.last Γ A).reindex (lift σ rfl) = Entry.last Δ (A.reindex σ) := by
    rw [lift, Entry.last_reindex_pair]
    exact Entry.ext (A.reindex_comp _ σ) (Term.cast_code _ _)
  have second : ((⟨A, v⟩ : Entry Γ).reindex (projectionHom Γ A)).reindex (lift σ rfl) =
      (⟨A, v⟩ : Entry Γ).reindex (projectionHom Δ (A.reindex σ) ≫ σ) := by
    rw [← Entry.reindex_comp, lift_projection]
  have third : (⟨A, v⟩ : Entry Γ).reindex (projectionHom Δ (A.reindex σ) ≫ σ) =
      (⟨A.reindex σ, v.reindex σ⟩ : Entry Δ).reindex (projectionHom Δ (A.reindex σ)) :=
    Entry.reindex_comp _ _ _
  show [((Entry.last Γ A).reindex (lift σ rfl),
      ((⟨A, v⟩ : Entry Γ).reindex (projectionHom Γ A)).reindex (lift σ rfl))] =
    [definition Δ (v.reindex σ)]
  rw [first, second, third]
  rfl

/-! ## Isomorphisms of telescopes -/

/-- The isomorphism of dependent frames given by an isomorphism of telescopes. -/
def framesIso {Γ Δ : Context rules} (e : Δ ≅ Γ) : (frames rules).Iso Γ Δ where
  hom := e.hom
  inv := e.inv
  inv_hom t := by
    show Entry.Convertible ((t.reindex e.hom).reindex e.inv) t
    rw [← Entry.reindex_comp, e.inv_hom_id, Entry.reindex_id]
    exact Entry.Convertible.refl t
  hom_inv t := by
    show Entry.Convertible ((t.reindex e.inv).reindex e.hom) t
    rw [← Entry.reindex_comp, e.hom_inv_id, Entry.reindex_id]
    exact Entry.Convertible.refl t

theorem liftIso_type {Γ Δ : Context rules} (e : Δ ≅ Γ) (A : TypeOver Γ) :
    A = (A.reindex e.hom).reindex e.inv := by
  rw [← TypeOver.reindex_comp, e.inv_hom_id, TypeOver.reindex_id]

theorem lift_hom_inv {Γ Δ : Context rules} (e : Δ ≅ Γ) (A : TypeOver Γ) :
    lift e.hom rfl ≫ lift e.inv (liftIso_type e A) = 𝟙 (extend Δ (A.reindex e.hom)) := by
  apply hom_ext_extend
  · rw [Category.assoc, lift_projection, ← Category.assoc, lift_projection, Category.assoc,
      e.hom_inv_id, Category.comp_id, Category.id_comp]
  · show subst (lift e.hom rfl).substitution ((lift e.inv (liftIso_type e A)).substitution 0) = .var 0
    rw [lift_zero]
    exact lift_zero _ _

theorem lift_inv_hom {Γ Δ : Context rules} (e : Δ ≅ Γ) (A : TypeOver Γ) :
    lift e.inv (liftIso_type e A) ≫ lift e.hom rfl = 𝟙 (extend Γ A) := by
  apply hom_ext_extend
  · rw [Category.assoc, lift_projection, ← Category.assoc, lift_projection, Category.assoc,
      e.inv_hom_id, Category.comp_id, Category.id_comp]
  · show subst (lift e.inv (liftIso_type e A)).substitution ((lift e.hom rfl).substitution 0) = .var 0
    rw [lift_zero]
    exact lift_zero _ _

/-- **An isomorphism of telescopes lifts under one more variable.** -/
def liftIso {Γ Δ : Context rules} (e : Δ ≅ Γ) (A : TypeOver Γ) :
    extend Δ (A.reindex e.hom) ≅ extend Γ A where
  hom := lift e.hom rfl
  inv := lift e.inv (liftIso_type e A)
  hom_inv_id := lift_hom_inv e A
  inv_hom_id := lift_inv_hom e A

/-! ## Swapping two helpers -/

/-- Two variables made in one order, read in the other. -/
def swap (Γ : Context rules) (A B : TypeOver Γ) :
    extend (extend Γ B) (A.reindex (projectionHom Γ B)) ⟶
      extend (extend Γ A) (B.reindex (projectionHom Γ A)) :=
  pair (lift (projectionHom Γ B) rfl)
    (((newest Γ B).reindex (projectionHom (extend Γ B) (A.reindex (projectionHom Γ B)))).cast
      (by rw [← TypeOver.reindex_comp, ← TypeOver.reindex_comp, lift_projection]))

theorem swap_projection (Γ : Context rules) (A B : TypeOver Γ) :
    swap Γ A B ≫ projectionHom (extend Γ A) (B.reindex (projectionHom Γ A)) =
      lift (projectionHom Γ B) rfl :=
  pair_projection _ _

theorem swap_zero (Γ : Context rules) (A B : TypeOver Γ) :
    (swap Γ A B).substitution 0 = .var (Fin.succ 0) :=
  Term.cast_code _ _

theorem swap_one (Γ : Context rules) (A B : TypeOver Γ) :
    (swap Γ A B).substitution (Fin.succ 0) = .var 0 := by
  show (lift (projectionHom Γ B) (A := A) rfl).substitution 0 = .var 0
  exact lift_zero _ _

theorem swap_swap (Γ : Context rules) (A B : TypeOver Γ) :
    swap Γ A B ≫ swap Γ B A = 𝟙 _ := by
  apply hom_ext_extend
  · rw [Category.assoc, swap_projection, Category.id_comp]
    apply hom_ext_extend
    · rw [Category.assoc, lift_projection, ← Category.assoc, swap_projection, lift_projection]
    · show subst (swap Γ A B).substitution ((lift (projectionHom Γ A) rfl).substitution 0) =
        projection 0
      rw [lift_zero]
      exact swap_zero Γ A B
  · show subst (swap Γ A B).substitution ((swap Γ B A).substitution 0) = .var 0
    rw [swap_zero]
    exact swap_one Γ A B

/-- **Swapping two helpers is an isomorphism of telescopes.** -/
def swapIso (Γ : Context rules) (A B : TypeOver Γ) :
    extend (extend Γ B) (A.reindex (projectionHom Γ B)) ≅
      extend (extend Γ A) (B.reindex (projectionHom Γ A)) where
  hom := swap Γ A B
  inv := swap Γ B A
  hom_inv_id := swap_swap Γ A B
  inv_hom_id := swap_swap Γ B A

/-- **The swap fixes every old variable.** -/
theorem swap_fixes (Γ : Context rules) (A B : TypeOver Γ) :
    swap Γ A B ≫ projectionHom (extend Γ A) (B.reindex (projectionHom Γ A)) ≫ projectionHom Γ A =
      projectionHom (extend Γ B) (A.reindex (projectionHom Γ B)) ≫ projectionHom Γ B := by
  rw [← Category.assoc, swap_projection, lift_projection]

/-- The definition of the second helper, read through the swap, is the definition read through
the projection. -/
theorem definition_swap (Γ : Context rules) (A : TypeOver Γ) {B : TypeOver Γ} (v : Term Γ B) :
    (frames rules).applyStore (swap Γ A B)
        [definition (extend Γ A) (v.reindex (projectionHom Γ A))] =
      (frames rules).applyStore (projectionHom (extend Γ B) (A.reindex (projectionHom Γ B)))
        [definition Γ v] := by
  have first : (Entry.last (extend Γ A) (B.reindex (projectionHom Γ A))).reindex (swap Γ A B) =
      (Entry.last Γ B).reindex (projectionHom (extend Γ B) (A.reindex (projectionHom Γ B))) := by
    rw [swap, Entry.last_reindex_pair]
    refine Entry.ext ?_ (Term.cast_code _ _)
    show (B.reindex (projectionHom Γ A)).reindex (lift (projectionHom Γ B) rfl) =
      (B.reindex (projectionHom Γ B)).reindex (projectionHom (extend Γ B) (A.reindex (projectionHom Γ B)))
    rw [← TypeOver.reindex_comp, ← TypeOver.reindex_comp, lift_projection]
  have second : ((⟨B.reindex (projectionHom Γ A), v.reindex (projectionHom Γ A)⟩ :
        Entry (extend Γ A)).reindex (projectionHom (extend Γ A) (B.reindex (projectionHom Γ A)))).reindex
          (swap Γ A B) =
      ((⟨B, v⟩ : Entry Γ).reindex (projectionHom Γ B)).reindex
        (projectionHom (extend Γ B) (A.reindex (projectionHom Γ B))) := by
    have moved : (⟨B.reindex (projectionHom Γ A), v.reindex (projectionHom Γ A)⟩ : Entry (extend Γ A)) =
        (⟨B, v⟩ : Entry Γ).reindex (projectionHom Γ A) := rfl
    rw [moved, ← Entry.reindex_comp, ← Entry.reindex_comp, swap_projection, lift_projection,
      Entry.reindex_comp]
  show [((Entry.last (extend Γ A) (B.reindex (projectionHom Γ A))).reindex (swap Γ A B),
      ((⟨B.reindex (projectionHom Γ A), v.reindex (projectionHom Γ A)⟩ :
        Entry (extend Γ A)).reindex (projectionHom (extend Γ A) (B.reindex (projectionHom Γ A)))).reindex
          (swap Γ A B))] =
    [((Entry.last Γ B).reindex (projectionHom (extend Γ B) (A.reindex (projectionHom Γ B))),
      ((⟨B, v⟩ : Entry Γ).reindex (projectionHom Γ B)).reindex
        (projectionHom (extend Γ B) (A.reindex (projectionHom Γ B))))]
  rw [first, second]

/-! ## The helper step -/

variable (rules) (O : Type)

/-- A state of the dependent helper step: a frame, its knowledge and its present occurrences. -/
structure State where
  frame : Context rules
  knowledge : EquationStore (Entry frame)
  present : Finset O

variable {rules O}

/-- **A dependent helper firing**: it makes one occurrence and one fresh helper of a formed type
over the frame it fires at, and tells the helper's value. Its guards are equations on that frame,
asked at every solution. -/
structure Firing (s : State rules O) where
  made : O
  helper : TypeOver s.frame
  value : Term s.frame helper
  guards : EquationStore (Entry s.frame)

theorem Firing.ext {s : State rules O} {f g : Firing s} (made : f.made = g.made)
    (helper : f.helper = g.helper) (value : f.value.code = g.value.code)
    (guards : f.guards = g.guards) : f = g := by
  cases f with
  | mk fMade fHelper fValue fGuards =>
    cases g with
    | mk gMade gHelper gValue gGuards =>
      dsimp only at made helper value guards
      subst made helper guards
      obtain rfl := Term.ext value
      rfl

namespace Firing

variable {s : State rules O} (f : Firing s)

/-- The occurrence it makes. -/
def selection : Selection O := ⟨[], [], [f.made]⟩

/-- The helper's equation at the extended frame: the definition of the helper by its value. -/
def tell : Equation (Entry (extend s.frame f.helper)) := definition s.frame f.value

/-- Its information: the knowledge read in the extended frame, and the helper's definition. -/
def information : EquationStore (Entry (extend s.frame f.helper)) :=
  (frames rules).applyStore (projectionHom s.frame f.helper) s.knowledge ++ [f.tell]

/-- The state after it. -/
abbrev after [DecidableEq O] : State rules O :=
  ⟨extend s.frame f.helper, f.information, fire s.present (f.selection.commit (T := Unit))⟩

/-- The firing read at another state along a substitution of frames. -/
abbrev move {t : State rules O} (φ : t.frame ⟶ s.frame) : Firing t :=
  ⟨f.made, f.helper.reindex φ, f.value.reindex φ, (frames rules).applyStore φ f.guards⟩

/-- The firing read at another state along a substitution of frames, its occurrence renamed. -/
abbrev carry {t : State rules O} (π : O ≃ O) (φ : t.frame ⟶ s.frame) : Firing t :=
  ⟨π f.made, f.helper.reindex φ, f.value.reindex φ, (frames rules).applyStore φ f.guards⟩

end Firing

variable [DecidableEq O]

/-- **The dependent helper step**: firings that make fresh helpers of formed types, guarded by
equations on the old frame; it has no predicate queries. -/
abbrev helperStep : Interface.Step.Standard (frames rules) O (State rules O) Firing where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := extend _ f.helper
  extension f := projectionHom _ f.helper
  information f := f.information
  transported := by
    intro s f e member
    exact List.mem_append_left _ (List.mem_map.mpr ⟨e, member, rfl⟩)
  Shapes f := f.selection.made.Nodup
  Holds {s} f _ σ := (frames rules).Models ((frames rules).comp σ (projectionHom s.frame f.helper)) f.guards
  Admits {s} f := f.selection.made.Nodup ∧
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (frames rules).Solvable f.information ∧
    (frames rules).Entails f.information fun _ σ =>
      (frames rules).Models ((frames rules).comp σ (projectionHom s.frame f.helper)) f.guards
  admits_iff _ := Iff.rfl
  preparedResult f _ := f.after
  present_preparedResult _ _ := rfl
  preparedSettle f _ := (frames rules).id (extend _ f.helper)
  knowledge_preparedResult f _ := (Frames.applyStore_id (X := frames rules) f.information).symm

instance helperStep_guarded : (helperStep (rules := rules) (O := O)).toStep.Guarded :=
  Interface.Step.standard_guarded _

/-- The morphism a helper firing moves along is the projection off its helper. -/
theorem along_eq {s : State rules O} (f : Firing s) (admitted : (helperStep (rules := rules)).Admits f) :
    (helperStep (rules := rules)).along f admitted = projectionHom s.frame f.helper :=
  Category.id_comp _

omit [DecidableEq O] in
/-- Extend a solution by the helper's value. -/
def extendSolution {s : State rules O} (f : Firing s) {Δ : Context rules} (σ : Δ ⟶ s.frame) :
    Δ ⟶ extend s.frame f.helper :=
  pair σ (f.value.reindex σ)

omit [DecidableEq O] in
theorem extendSolution_restrict {s : State rules O} (f : Firing s) {Δ : Context rules}
    (σ : Δ ⟶ s.frame) : extendSolution f σ ≫ projectionHom s.frame f.helper = σ :=
  pair_projection _ _

omit [DecidableEq O] in
/-- **The helper is fresh**: every solution of the knowledge extends to the information. -/
theorem extendSolution_models {s : State rules O} (f : Firing s) {Δ : Context rules}
    (σ : Δ ⟶ s.frame) (solved : (frames rules).Models σ s.knowledge) :
    (frames rules).Models (extendSolution f σ) f.information := by
  refine (Frames.models_append _ _ _).mpr ⟨?_, ?_⟩
  · refine (Frames.models_applyStore (X := frames rules) (projectionHom _ f.helper)
      (extendSolution f σ) _).mpr ?_
    show (frames rules).Models (extendSolution f σ ≫ projectionHom _ f.helper) s.knowledge
    rw [extendSolution_restrict]
    exact solved
  · intro e member
    obtain rfl := List.mem_singleton.mp member
    show Entry.Convertible ((Entry.last s.frame f.helper).reindex (extendSolution f σ))
      (((⟨f.helper, f.value⟩ : Entry s.frame).reindex (projectionHom _ f.helper)).reindex
        (extendSolution f σ))
    rw [← Entry.reindex_comp, extendSolution_restrict, extendSolution, Entry.last_reindex_pair]
    exact Entry.Convertible.refl _

omit [DecidableEq O] in
theorem information_solvable {s : State rules O} (f : Firing s)
    (solvable : (frames rules).Solvable s.knowledge) : (frames rules).Solvable f.information := by
  obtain ⟨Δ, σ, solved⟩ := solvable
  exact ⟨Δ, extendSolution f σ, extendSolution_models f σ solved⟩

omit [DecidableEq O] in
theorem restrict_models {s : State rules O} (f : Firing s) {Δ : Context rules}
    (σ : Δ ⟶ extend s.frame f.helper) (solved : (frames rules).Models σ f.information) :
    (frames rules).Models (σ ≫ projectionHom s.frame f.helper) s.knowledge :=
  (Frames.models_applyStore (X := frames rules) (projectionHom s.frame f.helper) σ s.knowledge).mp
    (Frames.models_of_subset (fun _ member => List.mem_append_left _ member) solved)

omit [DecidableEq O] in
/-- **The information asks exactly what the knowledge asks about the old frame.** -/
theorem entails_information_iff {s : State rules O} (f : Firing s)
    (guards : EquationStore (Entry s.frame)) :
    (frames rules).Entails f.information
        (fun _ σ => (frames rules).Models ((frames rules).comp σ (projectionHom s.frame f.helper)) guards) ↔
      (frames rules).Entails s.knowledge (fun _ σ => (frames rules).Models σ guards) := by
  constructor
  · intro asked Δ σ solved
    have holds : (frames rules).Models (extendSolution f σ ≫ projectionHom s.frame f.helper) guards :=
      asked Δ (extendSolution f σ) (extendSolution_models f σ solved)
    rwa [extendSolution_restrict] at holds
  · intro asked Δ σ solved
    exact asked Δ _ (restrict_models f σ solved)

omit [DecidableEq O] in
theorem knowledge_solvable {s : State rules O} (f : Firing s)
    (solvable : (frames rules).Solvable f.information) : (frames rules).Solvable s.knowledge :=
  Frames.solvable_of_applyStore (X := frames rules) (projectionHom s.frame f.helper)
    (Frames.solvable_of_subset (fun _ member => List.mem_append_left _ member) solvable)

theorem enabled_iff {s : State rules O} (f : Firing s) :
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ↔ f.made ∉ s.present := by
  constructor
  · intro enabled present
    exact Finset.disjoint_left.mp enabled.fresh (by simp [Firing.selection, Selection.commit]) present
  · intro absent
    refine ⟨by simp [Firing.selection, Selection.commit], by simp [Firing.selection, Selection.commit],
      by simp [Firing.selection, Selection.commit], ?_, by simp [Firing.selection, Selection.commit]⟩
    simpa [Firing.selection, Selection.commit] using absent

/-- **Admission of a dependent helper firing**: solvable knowledge, a fresh occurrence, and guards
that the knowledge asks. -/
theorem admits_iff {s : State rules O} (f : Firing s) :
    (helperStep (rules := rules)).Admits f ↔ (frames rules).Solvable s.knowledge ∧ f.made ∉ s.present ∧
      (frames rules).Entails s.knowledge (fun _ σ => (frames rules).Models σ f.guards) := by
  constructor
  · rintro ⟨-, enabled, solvable, asked⟩
    exact ⟨knowledge_solvable f solvable, (enabled_iff f).mp enabled,
      (entails_information_iff f f.guards).mp asked⟩
  · rintro ⟨solvable, absent, asked⟩
    exact ⟨List.nodup_singleton _, (enabled_iff f).mpr absent, information_solvable f solvable,
      (entails_information_iff f f.guards).mpr asked⟩

/-! ## Transport along strict isomorphisms -/

omit [DecidableEq O] in
/-- **A strict isomorphism of states**: an isomorphism of telescopes whose inverse laws hold on the
nose, carrying the knowledge to knowledge with the same solutions, with the same occurrences. -/
structure Strict (s t : State rules O) where
  frame : t.frame ≅ s.frame
  knowledge : (frames rules).Equivalent ((frames rules).applyStore frame.hom s.knowledge) t.knowledge
  present : s.present = t.present

/-- A strict isomorphism, as the interface sees it. -/
def Strict.toStateIso {s t : State rules O} (i : Strict s t) :
    (helperStep (rules := rules) (O := O)).StateIso s t :=
  ⟨framesIso i.frame, i.knowledge, Equiv.refl O, by
    rw [Equiv.refl_toEmbedding, Finset.map_refl]
    exact i.present⟩

omit [DecidableEq O] in
/-- The information of a firing moved along a substitution that carries the knowledge is its
information carried along the lifted substitution. -/
theorem information_move_along {s t : State rules O} (σ : t.frame ⟶ s.frame)
    (knowledge : (frames rules).Equivalent ((frames rules).applyStore σ s.knowledge) t.knowledge)
    (f : Firing s) :
    (frames rules).Equivalent ((frames rules).applyStore (lift σ rfl) f.information)
      (f.move (t := t) σ).information := by
  have carried : (frames rules).applyStore (lift σ rfl) f.information =
      (frames rules).applyStore (projectionHom t.frame (f.helper.reindex σ))
          ((frames rules).applyStore σ s.knowledge) ++
        [definition t.frame (f.value.reindex σ)] := by
    unfold Firing.information Firing.tell
    rw [Frames.applyStore_append, Frames.applyStore_applyStore, Frames.applyStore_applyStore]
    congr 1
    exact definition_lift σ f.value
  rw [carried]
  exact Frames.Equivalent.append_right (Frames.Equivalent.applyStore _ knowledge) _

omit [DecidableEq O] in
/-- The information of a moved firing is the information carried along the lifted isomorphism. -/
theorem information_move {s t : State rules O} (i : Strict s t) (f : Firing s) :
    (frames rules).Equivalent
      ((frames rules).applyStore (liftIso i.frame f.helper).hom f.information)
      (f.move (t := t) i.frame.hom).information :=
  information_move_along i.frame.hom i.knowledge f

/-- **Residuals are natural along lifted substitutions**: reading a residual along the lifted
substitution, with its occurrence renamed, is the residual of the carried firings. -/
theorem move_along_lift {s t : State rules O} (π : O ≃ O) (σ : t.frame ⟶ s.frame) (g : Firing s)
    (admitted : (helperStep (rules := rules)).Admits g) (f : Firing s)
    (moved : (helperStep (rules := rules)).Admits (g.carry (t := t) π σ)) :
    (f.move (t := g.after) ((helperStep (rules := rules)).along g admitted)).carry
        (t := (g.carry (t := t) π σ).after) π (lift σ rfl) =
      (f.carry (t := t) π σ).move (t := (g.carry (t := t) π σ).after)
        ((helperStep (rules := rules)).along (g.carry (t := t) π σ) moved) := by
  refine Firing.ext rfl ?_ ?_ ?_
  · show (f.helper.reindex ((helperStep (rules := rules)).along g admitted)).reindex (lift σ rfl) =
      (f.helper.reindex σ).reindex ((helperStep (rules := rules)).along (g.carry (t := t) π σ) moved)
    rw [along_eq, along_eq, ← TypeOver.reindex_comp, ← TypeOver.reindex_comp, lift_projection]
  · show subst (lift σ rfl).substitution
        (subst ((helperStep (rules := rules)).along g admitted).substitution f.value.code) =
      subst ((helperStep (rules := rules)).along (g.carry (t := t) π σ) moved).substitution
        (subst σ.substitution f.value.code)
    rw [along_eq, along_eq, subst_subComp, subst_subComp]
    exact congrArg (fun τ : extend t.frame (g.helper.reindex σ) ⟶ s.frame =>
      subst τ.substitution f.value.code) (lift_projection σ (A := g.helper) rfl)
  · show (frames rules).applyStore (lift σ rfl)
        ((frames rules).applyStore ((helperStep (rules := rules)).along g admitted) f.guards) =
      (frames rules).applyStore ((helperStep (rules := rules)).along (g.carry (t := t) π σ) moved)
        ((frames rules).applyStore σ f.guards)
    rw [along_eq, along_eq, Frames.applyStore_applyStore, Frames.applyStore_applyStore]
    show (frames rules).applyStore (lift σ rfl ≫ projectionHom s.frame g.helper) f.guards =
      (frames rules).applyStore (projectionHom t.frame (g.helper.reindex σ) ≫ σ) f.guards
    rw [lift_projection]

/-- **Transport of dependent helper firings** along strict isomorphisms of states. -/
def helperTransport : Transport (helperStep (rules := rules) (O := O)).toStep where
  Iso s t := Strict s t
  toStateIso i := i.toStateIso
  refl s := ⟨Iso.refl s.frame, Frames.Iso.equivalent_refl (X := frames rules) s.knowledge, rfl⟩
  symm i := ⟨i.frame.symm, (framesIso i.frame).equivalent_symm i.knowledge, i.present.symm⟩
  trans i j := ⟨j.frame ≪≫ i.frame,
    Frames.Iso.equivalent_trans (framesIso i.frame) (framesIso j.frame) i.knowledge j.knowledge,
    i.present.trans j.present⟩
  Alike f f' := f = f'
  alike_equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  selection_alike same := congrArg _ same
  admits_alike same := same ▸ Iff.rfl
  result_alike {s} {f} _ same _ _ := by
    subst same
    exact ⟨Iso.refl _, Frames.Iso.equivalent_refl (X := frames rules) _, rfl⟩
  move i f := f.move i.frame.hom
  move_alike _ _ _ same := by
    subst same
    rfl
  move_refl f := Firing.ext rfl f.helper.reindex_id (subst_ids f.value.code)
    (Frames.applyStore_id (X := frames rules) f.guards)
  move_trans i j f := Firing.ext rfl (f.helper.reindex_comp j.frame.hom i.frame.hom)
    (subst_subComp j.frame.hom.substitution i.frame.hom.substitution f.value.code).symm
    (Frames.applyStore_applyStore (X := frames rules) i.frame.hom j.frame.hom f.guards).symm
  move_symm i f := by
    have inverse : subComp i.frame.inv.substitution i.frame.hom.substitution = ids :=
      congrArg FormationSensitiveContextual.Hom.substitution i.frame.inv_hom_id
    refine Firing.ext rfl ?_ ?_ ?_
    · show (f.helper.reindex i.frame.hom).reindex i.frame.inv = f.helper
      rw [← TypeOver.reindex_comp, i.frame.inv_hom_id, TypeOver.reindex_id]
    · show subst i.frame.inv.substitution (subst i.frame.hom.substitution f.value.code) = f.value.code
      rw [subst_subComp, inverse, subst_ids]
    · show (frames rules).applyStore i.frame.inv ((frames rules).applyStore i.frame.hom f.guards) = f.guards
      rw [Frames.applyStore_applyStore]
      show (frames rules).applyStore (i.frame.inv ≫ i.frame.hom) f.guards = f.guards
      rw [i.frame.inv_hom_id]
      exact Frames.applyStore_id (X := frames rules) f.guards
  selection_move _ _ := rfl
  admits_move {s t} i f := by
    have present : s.present = t.present := i.present
    rw [admits_iff, admits_iff, present]
    exact and_congr i.toStateIso.solvable_iff.symm (and_congr Iff.rfl
      ((Frames.Equivalent.entails_iff i.knowledge _).symm.trans
        (Frames.Iso.entails_applyStore_iff (framesIso i.frame) s.knowledge f.guards)))
  result_move i f _ :=
    ⟨liftIso i.frame f.helper, information_move i f,
      congrArg (fun present : Finset O => fire present (f.selection.commit (T := Unit))) i.present⟩
  residual g admitted f := f.move ((helperStep (rules := rules)).along g admitted)
  selection_residual _ _ _ := rfl
  move_residual i g admitted f := move_along_lift (Equiv.refl O) i.frame.hom g admitted f _

/-! ## The diamond closes up to the swap -/

/-- **The diamond of two dependent helper firings closes up to swapping the helpers.** -/
theorem helper_closes : (helperTransport (rules := rules) (O := O)).Closes := by
  intro s f g first second _ _
  refine ⟨⟨swapIso s.frame f.helper g.helper, ?_, ?_⟩⟩
  · show (frames rules).Equivalent
        ((frames rules).applyStore (swap s.frame f.helper g.helper)
          ((frames rules).applyStore
              (projectionHom (extend s.frame f.helper) (g.helper.reindex (projectionHom s.frame f.helper)))
              ((frames rules).applyStore (projectionHom s.frame f.helper) s.knowledge ++
                [definition s.frame f.value]) ++
            [definition (extend s.frame f.helper) (g.value.reindex (projectionHom s.frame f.helper))]))
        ((frames rules).applyStore
            (projectionHom (extend s.frame g.helper) (f.helper.reindex (projectionHom s.frame g.helper)))
            ((frames rules).applyStore (projectionHom s.frame g.helper) s.knowledge ++
              [definition s.frame g.value]) ++
          [definition (extend s.frame g.helper) (f.value.reindex (projectionHom s.frame g.helper))])
    have knowledgePart : (frames rules).applyStore (swap s.frame f.helper g.helper)
          ((frames rules).applyStore
            (projectionHom (extend s.frame f.helper) (g.helper.reindex (projectionHom s.frame f.helper)))
            ((frames rules).applyStore (projectionHom s.frame f.helper) s.knowledge)) =
        (frames rules).applyStore
          (projectionHom (extend s.frame g.helper) (f.helper.reindex (projectionHom s.frame g.helper)))
          ((frames rules).applyStore (projectionHom s.frame g.helper) s.knowledge) := by
      rw [Frames.applyStore_applyStore, Frames.applyStore_applyStore, Frames.applyStore_applyStore]
      show (frames rules).applyStore ((swap s.frame f.helper g.helper ≫
          projectionHom (extend s.frame f.helper) (g.helper.reindex (projectionHom s.frame f.helper))) ≫
            projectionHom s.frame f.helper) s.knowledge = _
      rw [Category.assoc, swap_fixes]
      rfl
    have firstTell : (frames rules).applyStore (swap s.frame f.helper g.helper)
          ((frames rules).applyStore
            (projectionHom (extend s.frame f.helper) (g.helper.reindex (projectionHom s.frame f.helper)))
            [definition s.frame f.value]) =
        [definition (extend s.frame g.helper) (f.value.reindex (projectionHom s.frame g.helper))] := by
      rw [Frames.applyStore_applyStore]
      show (frames rules).applyStore (swap s.frame f.helper g.helper ≫
          projectionHom (extend s.frame f.helper) (g.helper.reindex (projectionHom s.frame f.helper)))
          [definition s.frame f.value] = _
      rw [swap_projection]
      exact definition_lift (projectionHom s.frame g.helper) f.value
    have secondTell := definition_swap s.frame f.helper g.value
    rw [Frames.applyStore_append, Frames.applyStore_append, Frames.applyStore_append, knowledgePart,
      firstTell, secondTell, Frames.applyStore_append]
    exact Frames.equivalent_of_mem_iff fun e => by
      simp only [List.mem_append]
      tauto
  · show fire (fire s.present (f.selection.commit (T := Unit))) (g.selection.commit (T := Unit)) =
      fire (fire s.present (g.selection.commit (T := Unit))) (f.selection.commit (T := Unit))
    ext o
    simp only [Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.mem_fire]
    simp [Firing.selection, Selection.commit]
    tauto

/-- The residual's guards are asked after the other firing exactly when the knowledge asks them. -/
theorem residual_asks_iff {s : State rules O} (f : Firing s) (first : (helperStep (rules := rules)).Admits f)
    (guards : EquationStore (Entry s.frame)) :
    (frames rules).Entails f.information (fun _ σ =>
        (frames rules).Models σ ((frames rules).applyStore ((helperStep (rules := rules)).along f first) guards)) ↔
      (frames rules).Entails s.knowledge (fun _ σ => (frames rules).Models σ guards) := by
  rw [along_eq]
  refine Iff.trans ?_ (entails_information_iff f guards)
  constructor
  · intro asked Δ σ solved
    exact (Frames.models_applyStore (X := frames rules) (projectionHom s.frame f.helper) σ guards).mp
      (asked Δ σ solved)
  · intro asked Δ σ solved
    exact (Frames.models_applyStore (X := frames rules) (projectionHom s.frame f.helper) σ guards).mpr
      (asked Δ σ solved)

/-- **Independence of dependent helper firings**: solvable knowledge, fresh and distinct
occurrences, and the guards of both firings asked by the knowledge. -/
theorem independent_iff {s : State rules O} {f g : Firing s} :
    (helperTransport (rules := rules) (O := O)).Independent s f g ↔
      (frames rules).Solvable s.knowledge ∧ f.made ∉ s.present ∧ g.made ∉ s.present ∧
        f.made ≠ g.made ∧
        (frames rules).Entails s.knowledge (fun _ σ => (frames rules).Models σ f.guards) ∧
        (frames rules).Entails s.knowledge (fun _ σ => (frames rules).Models σ g.guards) := by
  rw [Transport.independent_iff_admits helper_closes]
  constructor
  · rintro ⟨first, second, afterFirst, -⟩
    obtain ⟨solvable, fFresh, fAsked⟩ := (admits_iff f).mp first
    obtain ⟨-, gFresh, gAsked⟩ := (admits_iff g).mp second
    obtain ⟨-, gAfter, -⟩ := (admits_iff _).mp afterFirst
    refine ⟨solvable, fFresh, gFresh, fun same => gAfter ?_, fAsked, gAsked⟩
    show g.made ∈ fire s.present (f.selection.commit (T := Unit))
    rw [← same]
    simp [fire, Firing.selection, Selection.commit]
  · rintro ⟨solvable, fFresh, gFresh, distinct, fAsked, gAsked⟩
    have first := (admits_iff f).mpr ⟨solvable, fFresh, fAsked⟩
    have second := (admits_iff g).mpr ⟨solvable, gFresh, gAsked⟩
    refine ⟨first, second,
      (admits_iff _).mpr ⟨information_solvable f solvable, ?_, (residual_asks_iff f first g.guards).mpr gAsked⟩,
      (admits_iff _).mpr ⟨information_solvable g solvable, ?_, (residual_asks_iff g second f.guards).mpr fAsked⟩⟩
    · show g.made ∉ fire s.present (f.selection.commit (T := Unit))
      simp [fire, Firing.selection, Selection.commit, gFresh, Ne.symm distinct]
    · show f.made ∉ fire s.present (g.selection.commit (T := Unit))
      simp [fire, Firing.selection, Selection.commit, fFresh, distinct]

/-! ## When the swap exists -/

section Swaps

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}
  {O' : Type uOcc} [DecidableEq O'] {State' : Type uS} {Firing' : State' → Type uF}
  {P : Interface.Step X O' State' Firing'} {T : Transport.{uO, uT, uH, uOcc, uS, uF, uI} P}

/-- A run of one firing admits no swap. -/
theorem not_swapStep_single {s : State'} {f : Firing' s} {a : P.Admits f} {r : P.Run s} :
    ¬ T.SwapStep (.cons f a (.nil _)) r := by
  intro step
  cases step with
  | later _ _ inner => cases inner

/-- **A two-firing run swaps exactly when its second firing is alike to the residual of a firing at
the start with which the first is independent.** -/
theorem swap_exists_iff {s : State'} {f : Firing' s} {a : P.Admits f}
    {g₁ : Firing' (P.result f a)} {a₁ : P.Admits g₁} :
    (∃ r, T.SwapStep (.cons f a (.cons g₁ a₁ (.nil _))) r) ↔
      ∃ g : Firing' s, T.Alike (T.residual f a g) g₁ ∧ T.Independent s f g := by
  constructor
  · rintro ⟨r, step⟩
    cases step with
    | here first second residualG afterFirst residualF afterSecond similar =>
        exact ⟨_, residualG, Transport.swap_independent first second residualG afterFirst residualF
          afterSecond similar⟩
    | later _ _ inner => exact (not_swapStep_single inner).elim
  · rintro ⟨g, residual, independent⟩
    obtain ⟨first, second, afterFirst, afterSecond, ⟨close⟩⟩ := independent
    exact ⟨_, .here first second residual a₁ (Transport.Alike.refl _) afterSecond
      (Transport.similar_nil_nil.mpr
        ⟨T.trans (T.symm (T.result_alike residual afterFirst a₁)) close⟩)⟩

end Swaps

/-- **A firing whose helper type is not a weakening has no swap**: a residual after a helper firing
reads its type through the projection, so its type is a weakening. -/
theorem no_swap_of_not_weakened {s : State rules O} {f : Firing s}
    {a : (helperStep (rules := rules)).Admits f} {g₁ : Firing f.after}
    {a₁ : (helperStep (rules := rules)).Admits g₁}
    (notWeakened : ∀ T : Tm Head s.frame.arity, rename wk T ≠ g₁.helper.code) :
    ∀ r, ¬ (helperTransport (rules := rules) (O := O)).SwapStep (.cons f a (.cons g₁ a₁ (.nil _))) r := by
  intro r step
  obtain ⟨g, residual, -⟩ := swap_exists_iff.mp ⟨r, step⟩
  have residual : _ = g₁ := residual
  apply notWeakened g.helper.code
  rw [← residual]
  show rename wk g.helper.code = subst ((helperStep (rules := rules)).along f a).substitution g.helper.code
  rw [along_eq]
  exact (subst_projection g.helper.code).symm

omit [DecidableEq O] in
/-- Moving a firing twice is moving it along the composite. -/
theorem Firing.move_move {s t u : State rules O} (f : Firing s) (σ : t.frame ⟶ s.frame)
    (τ : u.frame ⟶ t.frame) : (f.move (t := t) σ).move (t := u) τ = f.move (t := u) (τ ≫ σ) :=
  Firing.ext rfl (f.helper.reindex_comp τ σ).symm
    (subst_subComp τ.substitution σ.substitution f.value.code)
    (Frames.applyStore_applyStore (X := frames rules) σ τ f.guards)

omit [DecidableEq O] in
theorem Firing.move_id {s : State rules O} (f : Firing s) : f.move (t := s) (𝟙 s.frame) = f :=
  Firing.ext rfl f.helper.reindex_id (subst_ids f.value.code)
    (Frames.applyStore_id (X := frames rules) f.guards)

/-- **A second firing is a residual exactly when it is fixed by the first helper's definition**:
substituting the first helper's value for the first helper leaves its type, value and guards
unchanged. -/
theorem residual_exists_iff {s : State rules O} (f : Firing s)
    (a : (helperStep (rules := rules)).Admits f) (g₁ : Firing f.after) :
    (∃ g : Firing s, (helperTransport (rules := rules) (O := O)).residual f a g = g₁) ↔
      g₁.move (t := f.after) (projectionHom s.frame f.helper ≫ instantiate s.frame f.value) = g₁ := by
  constructor
  · rintro ⟨g, rfl⟩
    show (g.move (t := f.after) ((helperStep (rules := rules)).along f a)).move (t := f.after)
        (projectionHom s.frame f.helper ≫ instantiate s.frame f.value) =
      g.move (t := f.after) ((helperStep (rules := rules)).along f a)
    rw [along_eq, Firing.move_move, Category.assoc, instantiate_projection, Category.comp_id]
  · intro fixed
    refine ⟨g₁.move (t := s) (instantiate s.frame f.value), ?_⟩
    show (g₁.move (t := s) (instantiate s.frame f.value)).move (t := f.after)
        ((helperStep (rules := rules)).along f a) = g₁
    rw [along_eq, Firing.move_move]
    exact fixed

/-- **When the swap exists, exactly.** A run `f ; g₁` of dependent helper firings swaps exactly when
the definition of `f`'s helper fixes `g₁`, and `f` is independent of the firing that `g₁` is at the
start (`g₁` with `f`'s value substituted for `f`'s helper). -/
theorem swap_exists_iff_fixed {s : State rules O} {f : Firing s}
    {a : (helperStep (rules := rules)).Admits f} {g₁ : Firing f.after}
    {a₁ : (helperStep (rules := rules)).Admits g₁} :
    (∃ r, (helperTransport (rules := rules) (O := O)).SwapStep (.cons f a (.cons g₁ a₁ (.nil _))) r) ↔
      g₁.move (t := f.after) (projectionHom s.frame f.helper ≫ instantiate s.frame f.value) = g₁ ∧
        (helperTransport (rules := rules) (O := O)).Independent s f
          (g₁.move (t := s) (instantiate s.frame f.value)) := by
  rw [swap_exists_iff]
  constructor
  · rintro ⟨g, residual, independent⟩
    have residual : _ = g₁ := residual
    refine ⟨(residual_exists_iff f a g₁).mp ⟨g, residual⟩, ?_⟩
    have same : g₁.move (t := s) (instantiate s.frame f.value) = g := by
      rw [← residual]
      show (g.move (t := f.after) ((helperStep (rules := rules)).along f a)).move (t := s)
          (instantiate s.frame f.value) = g
      rw [along_eq, Firing.move_move, instantiate_projection, Firing.move_id]
    rw [same]
    exact independent
  · rintro ⟨fixed, independent⟩
    refine ⟨_, ?_, independent⟩
    change _ = g₁
    show (g₁.move (t := s) (instantiate s.frame f.value)).move (t := f.after)
        ((helperStep (rules := rules)).along f a) = g₁
    rw [along_eq, Firing.move_move]
    exact fixed

/-! ## Controls -/

namespace Consumer

/-- Two heads: a universe and a ground type in it. -/
inductive TinyHead where
  | universe
  | ground
  deriving DecidableEq

/-- The ground type lives in the universe; Π-types and identity types of small types are small. -/
def tiny : Rules TinyHead where
  headTyping h u := h = .ground ∧ u = .universe
  isUniverse u := u = .universe
  join u v w := u = .universe ∧ v = .universe ∧ w = .universe
  cumulative _ _ := False
  headEq u v := u = v

/-- Which telescope entries are Π-types, newest first. -/
def piFlags : {n : Nat} → Ctx TinyHead n → List Bool
  | _, .nil => []
  | _, .snoc Γ A => (match A with | .pi _ _ => true | _ => false) :: piFlags Γ

/-- The empty frame. -/
abbrev start : State tiny Nat := ⟨empty tiny, [], ∅⟩

theorem ground_formed {n : Nat} (Γ : Ctx TinyHead n) :
    FormationSensitive.Typing tiny Γ (.head .ground) (.head .universe) :=
  .headType ⟨rfl, rfl⟩

/-- `g → g` over a telescope. -/
def arrow {n : Nat} : Tm TinyHead n := .pi (.head .ground) (.head .ground)

theorem arrow_formed {n : Nat} (Γ : Ctx TinyHead n) :
    FormationSensitive.Typing tiny Γ arrow (.head .universe) :=
  .piForm (ground_formed Γ) rfl (ground_formed _) rfl ⟨rfl, rfl, rfl⟩

/-- `λ x. x : g → g`. -/
theorem identity_typed {n : Nat} (Γ : Ctx TinyHead n) :
    FormationSensitive.Typing tiny Γ (.lam (.var 0)) arrow :=
  .lamIntro (arrow_formed Γ) rfl (.var 0)

/-- The helper type `g → g`, over the empty frame. -/
def arrowType : TypeOver (empty tiny) := ⟨arrow, .universe, rfl, arrow_formed _⟩

/-- The helper type `Id (g → g) (λx.x) (λx.x)`, over the empty frame. -/
def reflType : TypeOver (empty tiny) :=
  ⟨.id arrow (.lam (.var 0)) (.lam (.var 0)), .universe, rfl,
    .idForm (arrow_formed _) rfl (identity_typed _) (identity_typed _)⟩

/-- Makes occurrence `1` and a helper `x : g → g`, valued `λx.x`. -/
def first : Firing start := ⟨1, arrowType, ⟨.lam (.var 0), identity_typed _⟩, []⟩

/-- Makes occurrence `2` and a helper `y : Id (g → g) (λx.x) (λx.x)`, valued `refl (λx.x)`. -/
def second : Firing start := ⟨2, reflType, ⟨.refl (.lam (.var 0)), .reflIntro (identity_typed _)⟩, []⟩

theorem start_solvable : (frames tiny).Solvable start.knowledge :=
  ⟨empty tiny, 𝟙 _, Frames.models_nil _⟩

/-- **The consumer diamond: the two firings are independent.** -/
theorem independent : (helperTransport (rules := tiny) (O := Nat)).Independent start first second :=
  independent_iff.mpr ⟨start_solvable, by decide, by decide, by decide,
    fun _ _ _ => Frames.models_nil _, fun _ _ _ => Frames.models_nil _⟩

/-- **The diamond commutes only up to the swap**: the two composite states are different, and they
are isomorphic. -/
theorem composites_differ :
    ∃ (a : (helperStep (rules := tiny)).Admits first) (b : (helperStep (rules := tiny)).Admits second)
      (a₁ : (helperStep (rules := tiny)).Admits (helperTransport.residual first a second))
      (b₁ : (helperStep (rules := tiny)).Admits (helperTransport.residual second b first)),
      (helperStep (rules := tiny)).result _ a₁ ≠ (helperStep (rules := tiny)).result _ b₁ ∧
        helperTransport.Same ((helperStep (rules := tiny)).result _ a₁)
          ((helperStep (rules := tiny)).result _ b₁) := by
  obtain ⟨a, b, a₁, b₁, close⟩ := independent
  refine ⟨a, b, a₁, b₁, fun same => ?_, close⟩
  have flags : piFlags (Ctx.snoc (Ctx.snoc Ctx.nil arrow) (subst projection reflType.code)) =
      piFlags (Ctx.snoc (Ctx.snoc Ctx.nil reflType.code) (subst projection arrowType.code)) :=
    congrArg (fun state : State tiny Nat => piFlags state.frame.raw) same
  exact absurd flags (by decide)

end Consumer

end Dependent

#print axioms Dependent.hom_ext_extend
#print axioms Dependent.definition_lift
#print axioms Dependent.liftIso
#print axioms Dependent.swapIso
#print axioms Dependent.swap_fixes
#print axioms Dependent.definition_swap
#print axioms Dependent.admits_iff
#print axioms Dependent.information_move
#print axioms Dependent.helperTransport
#print axioms Dependent.helper_closes
#print axioms Dependent.independent_iff
#print axioms Dependent.not_swapStep_single
#print axioms Dependent.swap_exists_iff
#print axioms Dependent.no_swap_of_not_weakened
#print axioms Dependent.residual_exists_iff
#print axioms Dependent.swap_exists_iff_fixed
#print axioms Dependent.Consumer.independent
#print axioms Dependent.Consumer.composites_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
