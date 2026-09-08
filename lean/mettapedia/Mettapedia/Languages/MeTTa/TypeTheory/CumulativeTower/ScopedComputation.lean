import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypedSubstitution

/-!
# Scoped return, sequencing and effect-call syntax

This reified computation fragment contains native terms and scoped binding
bodies, not host-language continuations. Ordinary sequencing and sequencing
that retains its selected value are distinct constructors. Both bind one
native term variable in the body.

Its structural algebra reuses the cumulative presentation's capture-avoiding
renaming and substitution, including the same lifted environments under
binders. These are syntax laws, independent of a typing profile, effect
handler, or evaluation strategy. The fragment is not a full CBPV calculus:
thunk/force and a choice of Prime calculus are not supplied here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedComputation

/-- Independently authored computation syntax with one new native variable
under either sequencing body. Operation names themselves contain no binders. -/
inductive Code (Head Operation : Type) : Nat → Type where
  | returnValue {n : Nat} (term : Tm Head n) : Code Head Operation n
  | sequence {n : Nat} (first : Code Head Operation n)
      (body : Code Head Operation (n + 1)) : Code Head Operation n
  | sequenceSigma {n : Nat} (first : Code Head Operation n)
      (body : Code Head Operation (n + 1)) : Code Head Operation n
  | choose {n : Nat} (left right : Code Head Operation n) : Code Head Operation n
  | call {n : Nat} (operation : Operation) (argument : Tm Head n) : Code Head Operation n
  deriving DecidableEq, Repr

namespace Code

variable {Head Operation : Type} {n m k : Nat}

/-- Capture-avoiding renaming of every native term and sequencing body. -/
def rename {n m : Nat} (ρ : Ren n m) : Code Head Operation n → Code Head Operation m
  | .returnValue term => .returnValue (Presentation.rename ρ term)
  | .sequence first body => .sequence (rename ρ first) (rename (liftRen ρ) body)
  | .sequenceSigma first body => .sequenceSigma (rename ρ first) (rename (liftRen ρ) body)
  | .choose left right => .choose (rename ρ left) (rename ρ right)
  | .call operation argument => .call operation (Presentation.rename ρ argument)

/-- Native simultaneous substitution, lifted once under each sequencing body. -/
def substitute {n m : Nat} (σ : Sub Head n m) : Code Head Operation n → Code Head Operation m
  | .returnValue term => .returnValue (subst σ term)
  | .sequence first body => .sequence (substitute σ first) (substitute (liftSub σ) body)
  | .sequenceSigma first body =>
      .sequenceSigma (substitute σ first) (substitute (liftSub σ) body)
  | .choose left right => .choose (substitute σ left) (substitute σ right)
  | .call operation argument => .call operation (subst σ argument)

/-- Open the newest computation binder with a native term. -/
def instantiate (argument : Tm Head n) (body : Code Head Operation (n + 1)) :
    Code Head Operation n := substitute (subst0 argument) body

theorem rename_ext {ρ ξ : Ren n m} (equal : ∀ index, ρ index = ξ index)
    (code : Code Head Operation n) : rename ρ code = rename ξ code := by
  have same : ρ = ξ := funext equal
  rw [same]

theorem substitute_ext {σ τ : Sub Head n m} (equal : ∀ index, σ index = τ index)
    (code : Code Head Operation n) : substitute σ code = substitute τ code := by
  have same : σ = τ := funext equal
  rw [same]

@[simp] theorem rename_id (code : Code Head Operation n) : rename idRen code = code := by
  induction code with
  | returnValue term => simp only [rename, Presentation.rename_id]
  | sequence first body ihFirst ihBody =>
      simp only [rename, liftRen_id, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody =>
      simp only [rename, liftRen_id, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [rename, ihLeft, ihRight]
  | call operation argument => simp only [rename, Presentation.rename_id]

@[simp] theorem rename_comp (ρ : Ren m k) (ξ : Ren n m) (code : Code Head Operation n) :
    rename ρ (rename ξ code) = rename (fun index => ρ (ξ index)) code := by
  induction code generalizing m k ρ with
  | returnValue term => simp only [rename, Presentation.rename_comp]
  | sequence first body ihFirst ihBody =>
      simp only [rename, ihFirst, ihBody]
      congr 1
      exact rename_ext (fun index => liftRen_comp_apply ρ ξ index) body
  | sequenceSigma first body ihFirst ihBody =>
      simp only [rename, ihFirst, ihBody]
      congr 1
      exact rename_ext (fun index => liftRen_comp_apply ρ ξ index) body
  | choose left right ihLeft ihRight => simp only [rename, ihLeft, ihRight]
  | call operation argument => simp only [rename, Presentation.rename_comp]

@[simp] theorem substitute_ids (code : Code Head Operation n) :
    substitute ids code = code := by
  induction code with
  | returnValue term => simp only [substitute, subst_ids]
  | sequence first body ihFirst ihBody =>
      simp only [substitute, liftSub_ids, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody =>
      simp only [substitute, liftSub_ids, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [substitute, ihLeft, ihRight]
  | call operation argument => simp only [substitute, subst_ids]

@[simp] theorem substitute_renSub (ρ : Ren n m) (code : Code Head Operation n) :
    substitute (renSub ρ) code = rename ρ code := by
  induction code generalizing m with
  | returnValue term => simp only [substitute, rename, subst_renSub]
  | sequence first body ihFirst ihBody =>
      simp only [substitute, rename, liftSub_renSub, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody =>
      simp only [substitute, rename, liftSub_renSub, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [substitute, rename, ihLeft, ihRight]
  | call operation argument => simp only [substitute, rename, subst_renSub]

theorem rename_substitute (ρ : Ren m k) (σ : Sub Head n m) (code : Code Head Operation n) :
    rename ρ (substitute σ code) =
      substitute (fun index => Presentation.rename ρ (σ index)) code := by
  induction code generalizing m k ρ with
  | returnValue term => simp only [rename, substitute, rename_subst]
  | sequence first body ihFirst ihBody =>
      simp only [rename, substitute, ihFirst, ihBody]
      congr 1
      exact substitute_ext (fun index => rename_liftSub ρ σ index) body
  | sequenceSigma first body ihFirst ihBody =>
      simp only [rename, substitute, ihFirst, ihBody]
      congr 1
      exact substitute_ext (fun index => rename_liftSub ρ σ index) body
  | choose left right ihLeft ihRight => simp only [rename, substitute, ihLeft, ihRight]
  | call operation argument => simp only [rename, substitute, rename_subst]

theorem substitute_rename (σ : Sub Head m k) (ρ : Ren n m) (code : Code Head Operation n) :
    substitute σ (rename ρ code) = substitute (fun index => σ (ρ index)) code := by
  induction code generalizing m k σ with
  | returnValue term => simp only [substitute, rename, subst_rename]
  | sequence first body ihFirst ihBody =>
      simp only [substitute, rename, ihFirst, ihBody]
      congr 1
      exact substitute_ext (fun index => liftSub_liftRen_apply σ ρ index) body
  | sequenceSigma first body ihFirst ihBody =>
      simp only [substitute, rename, ihFirst, ihBody]
      congr 1
      exact substitute_ext (fun index => liftSub_liftRen_apply σ ρ index) body
  | choose left right ihLeft ihRight => simp only [substitute, rename, ihLeft, ihRight]
  | call operation argument => simp only [substitute, rename, subst_rename]

@[simp] theorem substitute_comp (τ : Sub Head m k) (σ : Sub Head n m)
    (code : Code Head Operation n) :
    substitute τ (substitute σ code) = substitute (subComp τ σ) code := by
  induction code generalizing m k τ with
  | returnValue term => simp only [substitute, subst_subComp]
  | sequence first body ihFirst ihBody =>
      simp only [substitute, ihFirst, ihBody]
      congr 1
      exact substitute_ext (fun index => liftSub_comp_apply τ σ index) body
  | sequenceSigma first body ihFirst ihBody =>
      simp only [substitute, ihFirst, ihBody]
      congr 1
      exact substitute_ext (fun index => liftSub_comp_apply τ σ index) body
  | choose left right ihLeft ihRight => simp only [substitute, ihLeft, ihRight]
  | call operation argument => simp only [substitute, subst_subComp]

/-- Opening commutes with ambient renaming, with the body renaming lifted. -/
theorem rename_instantiate (ρ : Ren n m) (argument : Tm Head n)
    (body : Code Head Operation (n + 1)) :
    rename ρ (instantiate argument body) =
      instantiate (Presentation.rename ρ argument) (rename (liftRen ρ) body) := by
  simp only [instantiate, rename_substitute, substitute_rename]
  apply substitute_ext
  intro index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    rfl

/-- Substitution commutes with opening, retaining capture avoidance in both
sequencing forms and in every embedded native term. -/
theorem substitute_instantiate (σ : Sub Head n m) (argument : Tm Head n)
    (body : Code Head Operation (n + 1)) :
    substitute σ (instantiate argument body) =
      instantiate (subst σ argument) (substitute (liftSub σ) body) := by
  simp only [instantiate, substitute_comp]
  apply substitute_ext
  intro index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    exact (inst0_rename_wk (subst σ argument) (σ prior)).symm

/-- Substituting a paired environment is the same as substituting the older
environment under the binder and then opening it with the newest value. -/
theorem substitute_consSub (argument : Tm Head m) (σ : Sub Head n m)
    (body : Code Head Operation (n + 1)) :
    substitute (consSub argument σ) body =
      instantiate argument (substitute (liftSub σ) body) := by
  simp only [instantiate, substitute_comp]
  apply substitute_ext
  intro index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    exact (inst0_rename_wk argument (σ prior)).symm

@[simp] theorem substitute_consSub_rename_wk (argument : Tm Head m)
    (σ : Sub Head n m) (code : Code Head Operation n) :
    substitute (consSub argument σ) (rename wk code) = substitute σ code := by
  rw [substitute_rename]
  rfl

@[simp] theorem instantiate_rename_wk (argument : Tm Head n) (code : Code Head Operation n) :
    instantiate argument (rename wk code) = code := by
  rw [instantiate, substitute_rename]
  exact substitute_ids code

/-- Composing substitution with an extended environment preserves the newest
value and composes the older coordinates by the native environment law. -/
theorem substitute_consSub_comp (τ : Sub Head m k) (argument : Tm Head m)
    (σ : Sub Head n m) (body : Code Head Operation (n + 1)) :
    substitute τ (substitute (consSub argument σ) body) =
      substitute (consSub (subst τ argument) (subComp τ σ)) body := by
  rw [substitute_comp, subComp_consSub]

end Code

namespace Examples

/-- The outer selected value is used underneath another sequencing binder. -/
def binderBody : Code Bool Bool 2 :=
  .sequence (.call true (.var 0)) (.returnValue (.pair (.var 1) (.var 0)))

/-- A free variable supplied to the outer binder remains free under the next
binder; the next binder's local variable remains at index zero. -/
theorem opening_preserves_free_variable :
    Code.instantiate (.var 0) binderBody =
      (.sequence (.call true (.var 0))
        (.returnValue (.pair (.var 1) (.var 0))) : Code Bool Bool 1) := rfl

theorem opening_rejects_capture :
    Code.instantiate (.var 0) binderBody ≠
      (.sequence (.call true (.var 0))
        (.returnValue (.pair (.var 0) (.var 0))) : Code Bool Bool 1) := by decide

/-- The witness-retaining form has the same binder discipline. -/
def sigmaBinderBody : Code Bool Bool 2 :=
  .sequenceSigma (.returnValue (.var 0))
    (.choose (.returnValue (.pair (.var 1) (.var 0))) (.call false (.var 1)))

theorem sigma_opening_preserves_free_variable :
    Code.instantiate (.var 0) sigmaBinderBody =
      (.sequenceSigma (.returnValue (.var 0))
        (.choose (.returnValue (.pair (.var 1) (.var 0)))
          (.call false (.var 1))) : Code Bool Bool 1) := rfl

theorem sigma_opening_rejects_capture :
    Code.instantiate (.var 0) sigmaBinderBody ≠
      (.sequenceSigma (.returnValue (.var 0))
        (.choose (.returnValue (.pair (.var 0) (.var 0)))
          (.call false (.var 0))) : Code Bool Bool 1) := by decide

/-- Sequencing that retains its selected witness is not identified with
ordinary sequencing by the structural algebra. -/
theorem sequencing_forms_distinct :
    (.sequence (.returnValue (.head true)) (.returnValue (.var 0)) : Code Bool Bool 0) ≠
      .sequenceSigma (.returnValue (.head true)) (.returnValue (.var 0)) := by decide

end Examples

#print axioms Code.rename_id
#print axioms Code.rename_comp
#print axioms Code.substitute_ids
#print axioms Code.substitute_renSub
#print axioms Code.rename_substitute
#print axioms Code.substitute_rename
#print axioms Code.substitute_comp
#print axioms Code.rename_instantiate
#print axioms Code.substitute_instantiate
#print axioms Code.substitute_consSub
#print axioms Code.substitute_consSub_comp
#print axioms Examples.opening_preserves_free_variable
#print axioms Examples.opening_rejects_capture
#print axioms Examples.sigma_opening_preserves_free_variable
#print axioms Examples.sigma_opening_rejects_capture
#print axioms Examples.sequencing_forms_distinct

end ScopedComputation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
