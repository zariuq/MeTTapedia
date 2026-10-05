import Mettapedia.Languages.MM0.Kernel.SubstitutionTyping

/-!
# Fresh dummy images for MM0 definition unfolding

An unfolding substitutes the definition's parameters and its dummy variables.
Each dummy image must be a bound variable of the declared sort, fresh for all
parameter images and all earlier dummy images. Checking parameters alone
would incorrectly permit two dummy variables to collapse to one.

This module checks images in an existing target context. Admission of the
definition itself is responsible for its allowed dummy sorts and body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

namespace Preterm

def FreshFor (target : Context) (index : Nat) (expression : Preterm) : Prop :=
  (∃ support, Supports target expression support) ∧ ¬ HasVar target index expression

def checkFreshFor (target : Context) (index : Nat) (expression : Preterm) : Bool :=
  match support? target expression with
  | none => false
  | some support => decide (index ∉ support)

theorem checkFreshFor_iff (target : Context) (index : Nat) (expression : Preterm) :
    checkFreshFor target index expression = true ↔ FreshFor target index expression := by
  cases result : support? target expression with
  | none =>
      have undefined := (support_none_iff target expression).mp result
      simp [checkFreshFor, result, FreshFor, undefined]
  | some support =>
      have supported := support_sound result
      have defined : ∃ support, Supports target expression support := ⟨_, supported⟩
      simp [checkFreshFor, result, FreshFor, defined, ← supported.mem_iff_hasVar]

end Preterm

namespace Definition

inductive FreshDummies (target : Context) : List Preterm → List Nat → List Nat → Prop where
  | nil (arguments : List Preterm) : FreshDummies target arguments [] []
  | cons {arguments : List Preterm} {sort image : Nat} {sorts images : List Nat} :
      target[image]? = some (.bound sort) →
      (∀ expression ∈ arguments, Preterm.FreshFor target image expression) →
      FreshDummies target (arguments ++ [.var image]) sorts images →
      FreshDummies target arguments (sort :: sorts) (image :: images)

def checkDummies (target : Context) : List Preterm → List Nat → List Nat → Bool
  | _, [], [] => true
  | arguments, sort :: sorts, image :: images =>
      decide (target[image]? = some (.bound sort)) &&
        arguments.all (Preterm.checkFreshFor target image) &&
        checkDummies target (arguments ++ [.var image]) sorts images
  | _, _, _ => false

theorem checkDummies_iff (target : Context) (arguments : List Preterm) (sorts images : List Nat) :
    checkDummies target arguments sorts images = true ↔ FreshDummies target arguments sorts images := by
  induction sorts generalizing arguments images with
  | nil =>
      cases images with
      | nil => exact ⟨fun _ => .nil _, fun _ => rfl⟩
      | cons image images => constructor <;> intro impossible <;> cases impossible
  | cons sort sorts ih =>
      cases images with
      | nil => constructor <;> intro impossible <;> cases impossible
      | cons image images =>
          simp only [checkDummies, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
            Preterm.checkFreshFor_iff, ih]
          constructor
          · rintro ⟨⟨lookup, fresh⟩, rest⟩; exact .cons lookup fresh rest
          · intro admitted; cases admitted with
            | cons lookup fresh rest => exact ⟨⟨lookup, fresh⟩, rest⟩

theorem FreshDummies.length_eq {target : Context} {arguments : List Preterm} {sorts images : List Nat}
    (admitted : FreshDummies target arguments sorts images) : sorts.length = images.length := by
  induction admitted with
  | nil => rfl
  | cons _ _ _ ih => simpa using ih

theorem FreshDummies.typed {target : Context} {arguments : List Preterm} {sorts images : List Nat}
    (admitted : FreshDummies target arguments sorts images) (signature : TermSignature) :
    List.Forall₂ (Preterm.FitsBinder signature target) (images.map Preterm.var)
      (sorts.map Binder.bound) := by
  induction admitted with
  | nil => exact .nil
  | cons lookup _ _ ih => exact .cons (.bound lookup) ih

theorem FreshDummies.excludes_arguments {target : Context} {arguments : List Preterm}
    {sorts images : List Nat} (admitted : FreshDummies target arguments sorts images) :
    ∀ image ∈ images, ∀ expression ∈ arguments, ¬ Preterm.HasVar target image expression := by
  induction admitted with
  | nil => simp
  | cons lookup fresh tail ih =>
      intro image member expression argument
      rcases List.mem_cons.mp member with rfl | later
      · exact (fresh expression argument).2
      · exact ih image later expression (List.mem_append_left _ argument)

theorem FreshDummies.distinct {target : Context} {arguments : List Preterm}
    {sorts images : List Nat} (admitted : FreshDummies target arguments sorts images) :
    images.Nodup := by
  induction admitted with
  | nil => exact List.nodup_nil
  | @cons arguments sort image sorts images lookup _ tail ih =>
      rw [List.nodup_cons]
      refine ⟨?_, ih⟩
      intro repeated
      have absent := tail.excludes_arguments image repeated (.var image) (by simp)
      exact absent (.bound lookup)

end Definition

end Mettapedia.Languages.MM0.Kernel
