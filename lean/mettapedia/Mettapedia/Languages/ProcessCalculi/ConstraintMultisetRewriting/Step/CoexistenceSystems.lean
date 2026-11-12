import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Coexistence

/-!
# Finite coexistence of complete native states

The free finite family keeps the original states, including control data not
visible in their configurations. It exists without a native empty state,
closure under union, a common future frame or any independence condition.
Its common-frame interpretations use one morphism per represented frame, so
components sharing a declaration frame also share its substitution.

The universal property here is the free word monoid on native states: its
product `append` is concatenation of families. Symmetry is a permutation of
the family, respected by the stated solution and resource observations. This
is not a claim that arbitrary admitted executions commute, and it is not a
process constructor of the calculus: the joint store of a family is the union
of its members' stores (`FramedNative.spatial`).

Former names (until 2026-11-11): `append` was `par`; `append_assoc`,
`unit_append`, `append_unit`, `perm_append_comm`, `models_append`,
`present_append` and `fold_append` were `par_assoc`, `unit_par`, `par_unit`,
`par_symmetry`, `models_par`, `present_par` and `fold_par`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uM

namespace EffectCore

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

abbrev Systems (_effect : EffectCore X O State Firing) := List State

namespace Systems

variable (effect : EffectCore X O State Firing)

def atom (state : State) : effect.Systems := [state]
def unit : effect.Systems := []
/-- Concatenation of two finite families of native states. -/
def append (left right : effect.Systems) : effect.Systems := left ++ right

theorem append_assoc (left middle right : effect.Systems) :
    append effect (append effect left middle) right = append effect left (append effect middle right) :=
  List.append_assoc _ _ _

@[simp] theorem unit_append (systems : effect.Systems) : append effect (unit effect) systems = systems := rfl

@[simp] theorem append_unit (systems : effect.Systems) : append effect systems (unit effect) = systems :=
  List.append_nil _

theorem perm_append_comm (left right : effect.Systems) :
    (append effect left right).Perm (append effect right left) := List.perm_append_comm

theorem atom_injective : Function.Injective (atom effect) := by
  intro left right same
  exact List.singleton_injective same

abbrev Placement (systems : effect.Systems) (target : Obj) :=
  (source : Obj) → source ∈ systems.map effect.frame → Hom source target

def Placement.at {systems : effect.Systems} {target : Obj}
    (placement : Placement effect systems target) (state : State) (member : state ∈ systems) :
    Hom (effect.frame state) target :=
  placement (effect.frame state) (List.mem_map.mpr ⟨state, member, rfl⟩)

def Placement.left {left right : effect.Systems} {target : Obj}
    (placement : Placement effect (append effect left right) target) : Placement effect left target :=
  fun source member => placement source (by
    change source ∈ (left ++ right).map effect.frame
    rw [List.map_append]
    exact List.mem_append_left _ member)

def Placement.right {left right : effect.Systems} {target : Obj}
    (placement : Placement effect (append effect left right) target) : Placement effect right target :=
  fun source member => placement source (by
    change source ∈ (left ++ right).map effect.frame
    rw [List.map_append]
    exact List.mem_append_right _ member)

def Placement.reindex {left right : effect.Systems} {target : Obj}
    (permutation : left.Perm right) (placement : Placement effect right target) :
    Placement effect left target :=
  fun source member => placement source ((permutation.map effect.frame).mem_iff.mp member)

def Placement.post {systems : effect.Systems} {target later : Obj} (next : Hom target later)
    (placement : Placement effect systems target) : Placement effect systems later :=
  fun source member => X.comp next (placement source member)

def Models (systems : effect.Systems) (target : Obj) (placement : Placement effect systems target) :
    Prop := ∀ (state : State) (member : state ∈ systems),
      X.Models (Placement.at effect placement state member) (effect.knowledge state)

def NativeSolvable (systems : effect.Systems) : Prop :=
  ∃ (target : Obj) (placement : Placement effect systems target), Models effect systems target placement

theorem models_append {left right : effect.Systems} {target : Obj}
    (placement : Placement effect (append effect left right) target) :
    Models effect (append effect left right) target placement ↔
      Models effect left target (Placement.left effect placement) ∧
        Models effect right target (Placement.right effect placement) := by
  constructor
  · intro solved
    exact ⟨fun state member => solved state (List.mem_append_left _ member),
      fun state member => solved state (List.mem_append_right _ member)⟩
  · rintro ⟨leftSolved, rightSolved⟩ state member
    rcases List.mem_append.mp member with inLeft | inRight
    · exact leftSolved state inLeft
    · exact rightSolved state inRight

theorem models_reindex {left right : effect.Systems} {target : Obj}
    (permutation : left.Perm right) (placement : Placement effect right target) :
    Models effect left target (Placement.reindex effect permutation placement) ↔
      Models effect right target placement := by
  constructor
  · intro solved state member
    exact solved state (permutation.mem_iff.mpr member)
  · intro solved state member
    exact solved state (permutation.mem_iff.mp member)

theorem models_post {systems : effect.Systems} {target later : Obj}
    (next : Hom target later) (placement : Placement effect systems target)
    (solved : Models effect systems target placement) :
    Models effect systems later (Placement.post effect next placement) := by
  intro state member
  exact Frames.models_comp (solved state member) next

def present : effect.Systems → Finset O
  | [] => ∅
  | state :: rest => effect.present state ∪ present rest

theorem present_append (left right : effect.Systems) :
    present effect (append effect left right) = present effect left ∪ present effect right := by
  induction left with
  | nil => simp [append, present]
  | cons state rest ih =>
      change present effect (rest ++ right) = present effect rest ∪ present effect right at ih
      simp only [append, List.cons_append, present]
      rw [ih]
      exact (Finset.union_assoc _ _ _).symm

theorem mem_present (occurrence : O) (systems : effect.Systems) :
    occurrence ∈ present effect systems ↔ ∃ state ∈ systems, occurrence ∈ effect.present state := by
  induction systems with
  | nil => simp [present]
  | cons state rest ih =>
      simp only [present, Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro (inState | ⟨other, member, inOther⟩)
        · exact ⟨state, Or.inl rfl, inState⟩
        · exact ⟨other, Or.inr member, inOther⟩
      · rintro ⟨other, same | member, inOther⟩
        · subst other
          exact Or.inl inOther
        · exact Or.inr ⟨other, member, inOther⟩

theorem present_perm {left right : effect.Systems} (permutation : left.Perm right) :
    present effect left = present effect right := by
  ext occurrence
  rw [mem_present, mem_present]
  exact ⟨fun ⟨state, member, present⟩ => ⟨state, permutation.mem_iff.mp member, present⟩,
    fun ⟨state, member, present⟩ => ⟨state, permutation.mem_iff.mpr member, present⟩⟩

section FreeInterpretation

variable {M : Type uM} [Monoid M]

def fold (read : State → M) : effect.Systems → M
  | [] => 1
  | state :: rest => read state * fold read rest

@[simp] theorem fold_unit (read : State → M) : fold effect read (unit effect) = 1 := rfl

@[simp] theorem fold_atom (read : State → M) (state : State) :
    fold effect read (atom effect state) = read state := mul_one _

theorem fold_append (read : State → M) (left right : effect.Systems) :
    fold effect read (append effect left right) = fold effect read left * fold effect read right := by
  induction left with
  | nil => exact (one_mul _).symm
  | cons state rest ih =>
      exact (congrArg (read state * ·) ih).trans (mul_assoc _ _ _).symm

theorem fold_unique (read : State → M) (interpret : effect.Systems → M)
    (unitLaw : interpret (unit effect) = 1)
    (atomLaw : ∀ state, interpret (atom effect state) = read state)
    (appendLaw : ∀ left right, interpret (append effect left right) = interpret left * interpret right) :
    interpret = fold effect read := by
  funext systems
  induction systems with
  | nil => exact unitLaw
  | cons state rest ih =>
      change interpret (append effect (atom effect state) rest) = read state * fold effect read rest
      rw [appendLaw, atomLaw, ih]

theorem interpretation_exists_unique (read : State → M) : ∃! interpret : effect.Systems → M,
    interpret (unit effect) = 1 ∧ (∀ state, interpret (atom effect state) = read state) ∧
      ∀ left right, interpret (append effect left right) = interpret left * interpret right := by
  refine ⟨fold effect read, ⟨fold_unit effect read, fold_atom effect read, fold_append effect read⟩, ?_⟩
  intro interpret laws
  exact fold_unique effect read interpret laws.1 laws.2.1 laws.2.2

end FreeInterpretation
end Systems
end EffectCore
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
