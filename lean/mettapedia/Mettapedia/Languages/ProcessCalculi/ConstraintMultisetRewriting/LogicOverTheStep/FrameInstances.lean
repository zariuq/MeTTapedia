import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.SolutionFibration
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFrames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull

/-!
# The solution fibration at real frames: first-order and dependent

## Knowledge is a forcing relation

A predicate is **persistent** when later instantiation keeps it (`Persistent`); the models of a
store are (`persistent_models`). The step reads its guards by entailment, a universal statement
over the solutions of the knowledge, and **what the knowledge entails, the result of every firing
entails along the firing** (`entails_along`): adding knowledge never invalidates an entailed
observation. Absence read at one solution is not persistent
(`FirstOrder.absentAt_not_persistent`: the pattern `x` misses the constant `c` at the identity and
meets it once `x` is instantiated by `c`); the step does not read it there. Adding knowledge loses
no entailed observation; absence of a stored pattern is lost to stores, put beside
(`ContextGrades`) or made by firings.

## First-order frames (`FirstOrder`)

The first-order term action is faithful (`AnnotatedRuns.firstOrder_faithful`), so on its frames
every predicate is observational and reindexing is functorial on all of them
(`firstOrder_reindex_id`, `firstOrder_reindex_comp`). On the real first-order step the result is
the information reindexed along the settlement (`firstOrder_result_eq`).

## Dependent frames (`Dependent`, `Full`)

* The formation-sensitive dependent frames are a category on the nose, so reindexing is functorial
  on every predicate, not only the observational ones (`Dependent.reindex_id_raw`,
  `Dependent.reindex_comp_raw`).
* **The lifting property, discharged by the tree's principal answer**: substituting its value covers
  the definition `x ≐ v` of the newest variable (`Dependent.definition_covers`, from
  `Dependent.definition_principal`), so the asks of the definition are exactly the asks after the
  substitution (`Dependent.definition_entails_iff`) and solvability is preserved and reflected
  (`Dependent.definition_solvable_iff`).
* **The dependent full step changes frames**: its firings extend the state's frame by a telescope of
  fresh helpers. Knowledge only refines along that weakening and the settlement, in the fibre over
  the result frame (`Full.knowledge_along`), and along every run (`Full.run_refines`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.FrameInstances

open Interface
open SolutionFibration

universe uO uT uH uOcc uS uF

/-! ## Knowledge is a forcing relation -/

section Persistence

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

/-- **Persistent predicates** survive later instantiation. -/
def Persistent {a : Obj} (φ : Pred Hom a) : Prop :=
  ∀ (b c : Obj) (f : Hom a b) (g : Hom b c), φ ⟨b, f⟩ → φ ⟨c, X.comp g f⟩

/-- **The models of a store are persistent.** -/
theorem persistent_models {a : Obj} (store : EquationStore (Tm a)) :
    Persistent X (models X store) :=
  fun _ _ _ g solved => Frames.models_comp solved g

variable {X} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **What the knowledge entails, the result of every firing entails along the firing.** -/
theorem entails_along (P : Interface.Step X O State Firing) {s : State} {f : Firing s}
    (admitted : P.Admits f) {Q : (b : Obj) → Hom (P.frame s) b → Prop}
    (asked : X.Entails (P.knowledge s) Q) :
    X.Entails (P.knowledge (P.result f admitted)) (fun b σ => Q b (X.comp σ (P.along f admitted))) := by
  intro b σ solved
  exact (entails_iff_le X _ _).mp asked _ (knowledge_along_le P admitted ⟨b, σ⟩ solved)

end Persistence

/-! ## First-order frames -/

namespace FirstOrder

open Mettapedia.Logic.LP

/-- The first-order frames over an LP signature: one frame, substitutions as morphisms. -/
abbrev frames (signature : LPSignature) := Frames.ofSubstitution (ConstraintMultisetRewriting.FirstOrder.action signature)

/-- The first-order frames are faithful. -/
theorem frames_faithful (signature : LPSignature) : Faithful (frames signature) :=
  fun _ _ f g same => AnnotatedRuns.firstOrder_faithful signature f g same

/-- **On first-order frames reindexing along the identity is the identity, on every predicate.** -/
theorem firstOrder_reindex_id (signature : LPSignature)
    (φ : Pred (fun _ _ : PUnit.{1} => Subst signature) PUnit.unit) :
    reindex (frames signature) ((frames signature).id PUnit.unit) φ = φ :=
  reindex_id _ (observational_of_faithful _ (frames_faithful signature) φ)

/-- **On first-order frames reindexing along a composite is the composite, on every predicate.** -/
theorem firstOrder_reindex_comp (signature : LPSignature) (h g : Subst signature)
    (φ : Pred (fun _ _ : PUnit.{1} => Subst signature) PUnit.unit) :
    reindex (frames signature)
        ((frames signature).comp (a := PUnit.unit) (b := PUnit.unit) (c := PUnit.unit) g h) φ =
      reindex (frames signature) (a := PUnit.unit) (a' := PUnit.unit) g
        (reindex (frames signature) (a := PUnit.unit) (a' := PUnit.unit) h φ) :=
  reindex_comp _ h g (observational_of_faithful _ (frames_faithful signature) φ)

/-- The real first-order step over the first-order term action. -/
abbrev step (signature : LPSignature) {O : Type} [DecidableEq O] (label : O → Term signature) :=
  (AnnotatedRuns.firstOrder (ConstraintMultisetRewriting.FirstOrder.action signature) label).toStep

/-- **On the real first-order step the result is the information reindexed along the
settlement.** -/
theorem firstOrder_result_eq (signature : LPSignature) {O : Type} [DecidableEq O]
    (label : O → Term signature) {C : Configuration (Term signature) O}
    {f : AnnotatedRuns.Firing (Term signature) (Subst signature) O}
    (admitted : (step signature label).Admits (s := C) f) :
    models (frames signature) (a := PUnit.unit)
        ((step signature label).knowledge ((step signature label).result f admitted)) =
      reindex (frames signature) (a := PUnit.unit) (a' := PUnit.unit)
        ((step signature label).settle f admitted)
        (models (frames signature) (a := PUnit.unit) ((step signature label).information (s := C) f)) :=
  result_eq (step signature label) admitted

/-- One variable and one constant. -/
def tiny : LPSignature where
  constants := Unit
  vars := Unit
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

/-- The variable `x`. -/
def x : Term tiny := .var ()

/-- The constant `c`. -/
def c : Term tiny := .const ()

/-- The pattern `x` misses the one occurrence, labelled `c`, at a solution. -/
def absentAt : Pred (fun _ _ : PUnit.{1} => Subst tiny) PUnit.unit :=
  fun σ => (Check.absent x).Holds (ConstraintMultisetRewriting.FirstOrder.action tiny) σ.2
    (fun _ : Unit => c) {()}

/-- **Control: absence at a solution is not persistent.** At the identity `x` misses `c`; after
instantiating `x` by `c` it meets it. -/
theorem absentAt_not_persistent :
    absentAt ⟨PUnit.unit, Subst.id tiny⟩ ∧
      ¬ absentAt ⟨PUnit.unit, Subst.comp (fun _ => c) (Subst.id tiny)⟩ ∧
      ¬ Persistent (frames tiny) absentAt := by
  have atIdentity : absentAt ⟨PUnit.unit, Subst.id tiny⟩ := by
    intro o _ same
    cases same
  have afterInstantiation : ¬ absentAt ⟨PUnit.unit, Subst.comp (fun _ => c) (Subst.id tiny)⟩ :=
    fun clear => clear () (Finset.mem_singleton_self ()) rfl
  exact ⟨atIdentity, afterInstantiation, fun persistent =>
    afterInstantiation (persistent PUnit.unit PUnit.unit (Subst.id tiny) (fun _ => c) atIdentity)⟩

end FirstOrder

/-! ## Formation-sensitive dependent frames -/

namespace Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type} {rules : Rules Head}

/-- **The dependent frames are a category on the nose**: reindexing along the identity is the
identity on every predicate. -/
theorem reindex_id_raw {Γ : Context rules} (φ : Pred (fun Γ Δ : Context rules => Δ ⟶ Γ) Γ) :
    reindex (Interface.Dependent.frames rules) ((Interface.Dependent.frames rules).id Γ) φ = φ := by
  funext σ
  obtain ⟨Δ, f⟩ := σ
  show φ ⟨Δ, f ≫ 𝟙 Γ⟩ = φ ⟨Δ, f⟩
  rw [Category.comp_id]

/-- **Reindexing along a composite is the composite on every predicate.** -/
theorem reindex_comp_raw {Γ Γ' Γ'' : Context rules} (h : Γ' ⟶ Γ) (g : Γ'' ⟶ Γ')
    (φ : Pred (fun Γ Δ : Context rules => Δ ⟶ Γ) Γ) :
    reindex (Interface.Dependent.frames rules) ((Interface.Dependent.frames rules).comp g h) φ =
      reindex (Interface.Dependent.frames rules) g (reindex (Interface.Dependent.frames rules) h φ) := by
  funext σ
  obtain ⟨Δ, f⟩ := σ
  show φ ⟨Δ, f ≫ (g ≫ h)⟩ = φ ⟨Δ, (f ≫ g) ≫ h⟩
  rw [Category.assoc]

/-- **Substituting its value covers the definition of the newest variable.** -/
theorem definition_covers (Γ : Context rules) {A : TypeOver Γ} (v : Term Γ A) :
    Covers (Interface.Dependent.frames rules) (Interface.Dependent.instantiate Γ v)
      [Interface.Dependent.definition Γ v] :=
  covers_of_principal _ (Interface.Dependent.definition_principal Γ v)

/-- **The asks of a definition are exactly the asks after substituting its value**, for
observational asks. -/
theorem definition_entails_iff (Γ : Context rules) {A : TypeOver Γ} (v : Term Γ A)
    {observation : (Δ : Context rules) → (Δ ⟶ extend Γ A) → Prop}
    (observational : Observational (Interface.Dependent.frames rules) (ask observation)) :
    (Interface.Dependent.frames rules).Entails
        ((Interface.Dependent.frames rules).applyStore (Interface.Dependent.instantiate Γ v)
          [Interface.Dependent.definition Γ v])
        (fun Δ σ => observation Δ
          ((Interface.Dependent.frames rules).comp σ (Interface.Dependent.instantiate Γ v))) ↔
      (Interface.Dependent.frames rules).Entails [Interface.Dependent.definition Γ v] observation :=
  entails_reindex_iff _ (definition_covers Γ v) observational

/-- **Solvability of a definition is preserved and reflected by substituting its value.** -/
theorem definition_solvable_iff (Γ : Context rules) {A : TypeOver Γ} (v : Term Γ A) :
    (Interface.Dependent.frames rules).Solvable
        ((Interface.Dependent.frames rules).applyStore (Interface.Dependent.instantiate Γ v)
          [Interface.Dependent.definition Γ v]) ↔
      (Interface.Dependent.frames rules).Solvable [Interface.Dependent.definition Γ v] :=
  solvable_reindex_iff _ (definition_covers Γ v)

end Dependent

/-! ## The dependent full step -/

namespace Full

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head : Type} {rules : Rules Head} {L : Type} [UniverseLevel.LevelOrder L]
  (levels : LevelModel rules L) (O : Type) [DecidableEq O]

/-- The dependent full step, as a step. -/
abbrev step := (DependentFull.step levels O).toStep

variable {levels O}

/-- **Knowledge only refines along the helper weakening and the settlement**, in the fibre over
the result frame. -/
theorem knowledge_along {s : DependentFull.State rules O} {f : DependentFull.Firing levels s}
    (admitted : (step levels O).Admits f) :
    models (ContextualDependentEta.frames levels) ((step levels O).knowledge ((step levels O).result f admitted)) ≤
      reindex (ContextualDependentEta.frames levels) ((step levels O).along f admitted)
        (models (ContextualDependentEta.frames levels) ((step levels O).knowledge s)) :=
  knowledge_along_le (step levels O) admitted

/-- **Along every run of the dependent full step, knowledge only refines.** -/
theorem run_refines {s : DependentFull.State rules O} (r : (step levels O).Run s) :
    models (ContextualDependentEta.frames levels) ((step levels O).knowledge r.last) ≤
      reindex (ContextualDependentEta.frames levels) r.toLast
        (models (ContextualDependentEta.frames levels) ((step levels O).knowledge s)) :=
  run_le (step levels O) r

end Full

#print axioms persistent_models
#print axioms entails_along
#print axioms FirstOrder.frames_faithful
#print axioms FirstOrder.firstOrder_reindex_id
#print axioms FirstOrder.firstOrder_reindex_comp
#print axioms FirstOrder.firstOrder_result_eq
#print axioms FirstOrder.absentAt_not_persistent
#print axioms Dependent.reindex_id_raw
#print axioms Dependent.reindex_comp_raw
#print axioms Dependent.definition_covers
#print axioms Dependent.definition_entails_iff
#print axioms Dependent.definition_solvable_iff
#print axioms Full.knowledge_along
#print axioms Full.run_refines

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.FrameInstances
