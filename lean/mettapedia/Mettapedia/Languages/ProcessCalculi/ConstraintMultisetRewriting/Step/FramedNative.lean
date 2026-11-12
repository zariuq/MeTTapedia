import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FramedConfiguration
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceSystems

/-!
# Conservative native snapshots and the coexistence-family interpretation

A native configuration embeds at its original frame. Family-frame solutions
preserve and reflect its native solutions. Native-state families have a unique
spatial interpretation preserving atoms, the unit and concatenation: the store
of a concatenated family is the union of the two stores.
The interpretation is a view; complete native control data remains in the family.

Former names (until 2026-11-11): `spatial_append` was `spatial_par`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF

namespace Coexistence.FramedConfiguration

variable {Obj : Type uO} {Tm : Obj → Type uT} {O : Type uOcc}

def nativeTerm (a : Obj) (term : Tm a) : Frames.Families.Term Tm [a] :=
  ⟨⟨a, term⟩, List.mem_singleton_self _⟩

def nativeEquation (a : Obj) (equation : Equation (Tm a)) : Equation (Frames.Families.Term Tm [a]) :=
  (nativeTerm a equation.1, nativeTerm a equation.2)

def ofNative (a : Obj) (state : Configuration (Tm a) O) : FramedConfiguration Tm O :=
  ⟨[a], ⟨state.equations.map (nativeEquation a), state.present⟩⟩

variable {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

def singletonMap {a b : Obj} (mapping : Hom a b) : Frames.Families.Map Hom [a] [b] := by
  intro source member
  have same : source = a := List.mem_singleton.mp member
  subst source
  exact ⟨⟨b, List.mem_singleton_self _⟩, mapping⟩

theorem models_ofNative (a : Obj) (state : Configuration (Tm a) O) {target : List Obj}
    (mapping : Frames.Families.Map Hom [a] target) :
    X.families.Models mapping (ofNative a state).content.equations ↔
      X.Models (mapping a (List.mem_singleton_self _)).snd state.equations := by
  constructor
  · intro solved equation member
    have family := solved (nativeEquation a equation) (List.mem_map.mpr ⟨equation, member, rfl⟩)
    exact (Frames.Families.related_same_frame_iff X).mp family
  · intro solved equation member
    obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp member
    exact Frames.Families.Related.sameFrame (solved original inStore)

theorem solvable_ofNative_iff (a : Obj) (state : Configuration (Tm a) O) :
    X.families.Solvable (ofNative a state).content.equations ↔ X.Solvable state.equations := by
  constructor
  · rintro ⟨target, mapping, solved⟩
    exact ⟨(mapping a (List.mem_singleton_self _)).fst.val,
      (mapping a (List.mem_singleton_self _)).snd, (models_ofNative X a state mapping).mp solved⟩
  · rintro ⟨target, mapping, solved⟩
    refine ⟨[target], singletonMap mapping, (models_ofNative X a state _).mpr ?_⟩
    exact solved

variable [DecidableEq O]

theorem tensor_ofNative (a : Obj) (left right : Configuration (Tm a) O) :
    Similar X (tensor (ofNative a left) (ofNative a right))
      (ofNative a (Coexistence.tensor left right)) := by
  have support : ∀ frame, frame ∈ [a] ++ [a] ↔ frame ∈ [a] := by simp
  let combined : Configuration (Frames.Families.Term Tm ([a] ++ [a])) O :=
    (tensor (ofNative a left) (ofNative a right)).content
  let result : Configuration (Frames.Families.Term Tm [a]) O :=
    (ofNative a (Coexistence.tensor left right)).content
  refine ⟨support, ?_⟩
  change Coexistence.Same X.families (a := [a])
    (widen (fun frame member => (support frame).mp member) combined) result
  have same : widen (fun frame member => (support frame).mp member) combined = result := by
    apply eraseConfiguration_injective
    rw [erase_widen]
    change erase (tensor (ofNative a left) (ofNative a right)) =
      erase (ofNative a (Coexistence.tensor left right))
    rw [erase_tensor]
    simp only [erase, ofNative, eraseConfiguration, Coexistence.tensor, List.map_append]
  rw [same]
  exact Coexistence.Same.refl X.families _

theorem joint_native_solvable_iff (a : Obj) (left right : Configuration (Tm a) O) :
    X.families.Solvable (tensor (ofNative a left) (ofNative a right)).content.equations ↔
      X.Solvable (Coexistence.tensor left right).equations :=
  (Similar.solvable_iff X (tensor_ofNative X a left right)).trans
    (solvable_ofNative_iff X a (Coexistence.tensor left right))

end Coexistence.FramedConfiguration

namespace EffectCore.Systems

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (effect : EffectCore X O State Firing)

def spatialAtom (state : State) : Coexistence.FramedConfiguration Tm O :=
  Coexistence.FramedConfiguration.ofNative (effect.frame state) (effect.configuration state)

def spatial : effect.Systems → Coexistence.FramedConfiguration Tm O :=
  fold effect (spatialAtom effect)

@[simp] theorem spatial_unit : spatial effect (unit effect) = Coexistence.FramedConfiguration.unit := rfl

@[simp] theorem spatial_atom (state : State) : spatial effect (atom effect state) = spatialAtom effect state :=
  fold_atom effect _ state

theorem spatial_append (left right : effect.Systems) :
    spatial effect (append effect left right) = Coexistence.FramedConfiguration.tensor
      (spatial effect left) (spatial effect right) := fold_append effect _ left right

theorem spatial_frames (systems : effect.Systems) :
    (spatial effect systems).frames = systems.map effect.frame := by
  induction systems with
  | nil => rfl
  | cons state rest ih =>
      change [effect.frame state] ++ (spatial effect rest).frames = effect.frame state :: rest.map effect.frame
      rw [ih]
      rfl

theorem spatial_present (systems : effect.Systems) :
    (spatial effect systems).content.present = present effect systems := by
  induction systems with
  | nil => rfl
  | cons state rest ih =>
      change effect.present state ∪ (spatial effect rest).content.present =
        effect.present state ∪ present effect rest
      rw [ih]

theorem spatial_unique (interpret : effect.Systems → Coexistence.FramedConfiguration Tm O)
    (unitLaw : interpret (unit effect) = Coexistence.FramedConfiguration.unit)
    (atomLaw : ∀ state, interpret (atom effect state) = spatialAtom effect state)
    (appendLaw : ∀ left right, interpret (append effect left right) =
      Coexistence.FramedConfiguration.tensor (interpret left) (interpret right)) :
    interpret = spatial effect := fold_unique effect _ interpret unitLaw atomLaw appendLaw

end EffectCore.Systems
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
