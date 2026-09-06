import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputation

/-!
# Scoped native computations with separate suspension references

Native mathematical variables and suspension references have independent
scopes. Sequence binds a native value; `letNeed` binds a suspension reference
only in its body, so the suspended source is nonrecursive. Native payloads
remain the existing presentation terms and effects are opaque closed data.

The structural laws do not execute suspended code, allocate cells, or establish
memoization. They support a scoped suspension/need fragment, not full
first-class CBPV value/computation types or a surface evaluation default.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedComputation

/-- Native scope first, suspension-reference scope second. Neither handles nor
computation bodies are encoded as native mathematical terms. -/
inductive Code (Head Operation Effect : Type) : Nat → Nat → Type where
  | returnValue {n k : Nat} (term : Tm Head n) : Code Head Operation Effect n k
  | sequence {n k : Nat} (first : Code Head Operation Effect n k)
      (body : Code Head Operation Effect (n + 1) k) : Code Head Operation Effect n k
  | sequenceSigma {n k : Nat} (first : Code Head Operation Effect n k)
      (body : Code Head Operation Effect (n + 1) k) : Code Head Operation Effect n k
  | choose {n k : Nat} (left right : Code Head Operation Effect n k) :
      Code Head Operation Effect n k
  | call {n k : Nat} (operation : Operation) (argument : Tm Head n) :
      Code Head Operation Effect n k
  | emit {n k : Nat} (effect : Effect) (next : Code Head Operation Effect n k) :
      Code Head Operation Effect n k
  | letNeed {n k : Nat} (suspended : Code Head Operation Effect n k)
      (body : Code Head Operation Effect n (k + 1)) : Code Head Operation Effect n k
  | force {n k : Nat} (reference : Fin k) : Code Head Operation Effect n k
  deriving DecidableEq, Repr

namespace Code

variable {Head Operation Effect : Type} {n m p k l q : Nat}

/-- Rename native variables, lifting only beneath native-value binders. -/
def rename {n m k : Nat} (ρ : Ren n m) :
    Code Head Operation Effect n k → Code Head Operation Effect m k
  | .returnValue term => .returnValue (Presentation.rename ρ term)
  | .sequence first body => .sequence (rename ρ first) (rename (liftRen ρ) body)
  | .sequenceSigma first body => .sequenceSigma (rename ρ first) (rename (liftRen ρ) body)
  | .choose left right => .choose (rename ρ left) (rename ρ right)
  | .call operation argument => .call operation (Presentation.rename ρ argument)
  | .emit effect next => .emit effect (rename ρ next)
  | .letNeed suspended body => .letNeed (rename ρ suspended) (rename ρ body)
  | .force reference => .force reference

/-- Substitute actual native terms. A new suspension reference does not bind
a native variable and therefore does not lift this substitution. -/
def substitute {n m k : Nat} (σ : Sub Head n m) :
    Code Head Operation Effect n k → Code Head Operation Effect m k
  | .returnValue term => .returnValue (subst σ term)
  | .sequence first body => .sequence (substitute σ first) (substitute (liftSub σ) body)
  | .sequenceSigma first body =>
      .sequenceSigma (substitute σ first) (substitute (liftSub σ) body)
  | .choose left right => .choose (substitute σ left) (substitute σ right)
  | .call operation argument => .call operation (subst σ argument)
  | .emit effect next => .emit effect (substitute σ next)
  | .letNeed suspended body => .letNeed (substitute σ suspended) (substitute σ body)
  | .force reference => .force reference

/-- Rename suspension references. Only the `letNeed` body introduces a new
reference; its suspended source cannot refer to that new reference. -/
def renameHandles {n k l : Nat} (θ : Fin k → Fin l) :
    Code Head Operation Effect n k → Code Head Operation Effect n l
  | .returnValue term => .returnValue term
  | .sequence first body => .sequence (renameHandles θ first) (renameHandles θ body)
  | .sequenceSigma first body =>
      .sequenceSigma (renameHandles θ first) (renameHandles θ body)
  | .choose left right => .choose (renameHandles θ left) (renameHandles θ right)
  | .call operation argument => .call operation argument
  | .emit effect next => .emit effect (renameHandles θ next)
  | .letNeed suspended body =>
      .letNeed (renameHandles θ suspended) (renameHandles (liftRen θ) body)
  | .force reference => .force (θ reference)

/-- Open a native-value binder using the native top substitution. -/
def instantiate (argument : Tm Head n) (body : Code Head Operation Effect (n + 1) k) :
    Code Head Operation Effect n k := substitute (subst0 argument) body

/-- Open a suspension-reference binder with an existing outer reference.
This changes reference names, not suspended code or runtime cell ownership. -/
def instantiateHandle (reference : Fin k) (body : Code Head Operation Effect n (k + 1)) :
    Code Head Operation Effect n k := renameHandles (Fin.cases reference id) body

theorem rename_ext {ρ ξ : Ren n m} (equal : ∀ index, ρ index = ξ index)
    (code : Code Head Operation Effect n k) : rename ρ code = rename ξ code := by
  rw [funext equal]

theorem substitute_ext {σ τ : Sub Head n m} (equal : ∀ index, σ index = τ index)
    (code : Code Head Operation Effect n k) : substitute σ code = substitute τ code := by
  rw [funext equal]

theorem renameHandles_ext {θ φ : Fin k → Fin l} (equal : ∀ index, θ index = φ index)
    (code : Code Head Operation Effect n k) : renameHandles θ code = renameHandles φ code := by
  rw [funext equal]

@[simp] theorem rename_id (code : Code Head Operation Effect n k) :
    rename idRen code = code := by
  induction code with
  | returnValue term => simp only [rename, Presentation.rename_id]
  | sequence first body ihFirst ihBody => simp only [rename, liftRen_id, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody => simp only [rename, liftRen_id, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [rename, ihLeft, ihRight]
  | call operation argument => simp only [rename, Presentation.rename_id]
  | emit effect next ih => simp only [rename, ih]
  | letNeed suspended body ihSuspended ihBody => simp only [rename, ihSuspended, ihBody]
  | force reference => rfl

@[simp] theorem rename_comp (ρ : Ren m p) (ξ : Ren n m)
    (code : Code Head Operation Effect n k) :
    rename ρ (rename ξ code) = rename (fun index => ρ (ξ index)) code := by
  induction code generalizing m p ρ with
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
  | emit effect next ih => simp only [rename, ih]
  | letNeed suspended body ihSuspended ihBody => simp only [rename, ihSuspended, ihBody]
  | force reference => rfl

@[simp] theorem substitute_ids (code : Code Head Operation Effect n k) :
    substitute ids code = code := by
  induction code with
  | returnValue term => simp only [substitute, subst_ids]
  | sequence first body ihFirst ihBody => simp only [substitute, liftSub_ids, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody => simp only [substitute, liftSub_ids, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [substitute, ihLeft, ihRight]
  | call operation argument => simp only [substitute, subst_ids]
  | emit effect next ih => simp only [substitute, ih]
  | letNeed suspended body ihSuspended ihBody => simp only [substitute, ihSuspended, ihBody]
  | force reference => rfl

@[simp] theorem substitute_renSub (ρ : Ren n m) (code : Code Head Operation Effect n k) :
    substitute (renSub ρ) code = rename ρ code := by
  induction code generalizing m with
  | returnValue term => simp only [substitute, rename, subst_renSub]
  | sequence first body ihFirst ihBody =>
      simp only [substitute, rename, liftSub_renSub, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody =>
      simp only [substitute, rename, liftSub_renSub, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [substitute, rename, ihLeft, ihRight]
  | call operation argument => simp only [substitute, rename, subst_renSub]
  | emit effect next ih => simp only [substitute, rename, ih]
  | letNeed suspended body ihSuspended ihBody => simp only [substitute, rename, ihSuspended, ihBody]
  | force reference => rfl

theorem rename_substitute (ρ : Ren m p) (σ : Sub Head n m)
    (code : Code Head Operation Effect n k) :
    rename ρ (substitute σ code) =
      substitute (fun index => Presentation.rename ρ (σ index)) code := by
  induction code generalizing m p ρ with
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
  | emit effect next ih => simp only [rename, substitute, ih]
  | letNeed suspended body ihSuspended ihBody => simp only [rename, substitute, ihSuspended, ihBody]
  | force reference => rfl

theorem substitute_rename (σ : Sub Head m p) (ρ : Ren n m)
    (code : Code Head Operation Effect n k) :
    substitute σ (rename ρ code) = substitute (fun index => σ (ρ index)) code := by
  induction code generalizing m p σ with
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
  | emit effect next ih => simp only [substitute, rename, ih]
  | letNeed suspended body ihSuspended ihBody => simp only [substitute, rename, ihSuspended, ihBody]
  | force reference => rfl

@[simp] theorem substitute_comp (τ : Sub Head m p) (σ : Sub Head n m)
    (code : Code Head Operation Effect n k) :
    substitute τ (substitute σ code) = substitute (subComp τ σ) code := by
  induction code generalizing m p τ with
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
  | emit effect next ih => simp only [substitute, ih]
  | letNeed suspended body ihSuspended ihBody => simp only [substitute, ihSuspended, ihBody]
  | force reference => rfl

theorem substitute_instantiate (σ : Sub Head n m) (argument : Tm Head n)
    (body : Code Head Operation Effect (n + 1) k) :
    substitute σ (instantiate argument body) =
      instantiate (subst σ argument) (substitute (liftSub σ) body) := by
  simp only [instantiate, substitute_comp]
  apply substitute_ext
  intro index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    exact (inst0_rename_wk (subst σ argument) (σ prior)).symm

theorem rename_instantiate (ρ : Ren n m) (argument : Tm Head n)
    (body : Code Head Operation Effect (n + 1) k) :
    rename ρ (instantiate argument body) =
      instantiate (Presentation.rename ρ argument) (rename (liftRen ρ) body) := by
  simp only [instantiate, rename_substitute, substitute_rename]
  apply substitute_ext
  intro index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    rfl

theorem substitute_consSub (argument : Tm Head m) (σ : Sub Head n m)
    (body : Code Head Operation Effect (n + 1) k) :
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
    (σ : Sub Head n m) (code : Code Head Operation Effect n k) :
    substitute (consSub argument σ) (rename wk code) = substitute σ code := by
  rw [substitute_rename]
  rfl

@[simp] theorem instantiate_rename_wk (argument : Tm Head n)
    (code : Code Head Operation Effect n k) :
    instantiate argument (rename wk code) = code := by
  rw [instantiate, substitute_rename]
  exact substitute_ids code

@[simp] theorem renameHandles_id (code : Code Head Operation Effect n k) :
    renameHandles idRen code = code := by
  induction code with
  | returnValue term => rfl
  | sequence first body ihFirst ihBody => simp only [renameHandles, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody => simp only [renameHandles, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [renameHandles, ihLeft, ihRight]
  | call operation argument => rfl
  | emit effect next ih => simp only [renameHandles, ih]
  | letNeed suspended body ihSuspended ihBody =>
      simp only [renameHandles, liftRen_id, ihSuspended, ihBody]
  | force reference => rfl

@[simp] theorem renameHandles_comp (θ : Fin l → Fin q) (φ : Fin k → Fin l)
    (code : Code Head Operation Effect n k) :
    renameHandles θ (renameHandles φ code) =
      renameHandles (fun index => θ (φ index)) code := by
  induction code generalizing l q θ with
  | returnValue term => rfl
  | sequence first body ihFirst ihBody => simp only [renameHandles, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody => simp only [renameHandles, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [renameHandles, ihLeft, ihRight]
  | call operation argument => rfl
  | emit effect next ih => simp only [renameHandles, ih]
  | letNeed suspended body ihSuspended ihBody =>
      simp only [renameHandles, ihSuspended, ihBody]
      congr 1
      exact renameHandles_ext (fun index => liftRen_comp_apply θ φ index) body
  | force reference => rfl

/-- The two substitutions commute because their variables inhabit distinct
scopes, including in a term containing both kinds of binders. -/
theorem renameHandles_substitute (θ : Fin k → Fin l) (σ : Sub Head n m)
    (code : Code Head Operation Effect n k) :
    renameHandles θ (substitute σ code) = substitute σ (renameHandles θ code) := by
  induction code generalizing m l with
  | returnValue term => rfl
  | sequence first body ihFirst ihBody => simp only [renameHandles, substitute, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody => simp only [renameHandles, substitute, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [renameHandles, substitute, ihLeft, ihRight]
  | call operation argument => rfl
  | emit effect next ih => simp only [renameHandles, substitute, ih]
  | letNeed suspended body ihSuspended ihBody =>
      simp only [renameHandles, substitute, ihSuspended, ihBody]
  | force reference => rfl

theorem renameHandles_rename (θ : Fin k → Fin l) (ρ : Ren n m)
    (code : Code Head Operation Effect n k) :
    renameHandles θ (rename ρ code) = rename ρ (renameHandles θ code) := by
  rw [← substitute_renSub, renameHandles_substitute, substitute_renSub]

theorem renameHandles_instantiate (θ : Fin k → Fin l) (argument : Tm Head n)
    (body : Code Head Operation Effect (n + 1) k) :
    renameHandles θ (instantiate argument body) =
      instantiate argument (renameHandles θ body) :=
  renameHandles_substitute θ (subst0 argument) body

theorem substitute_instantiateHandle (σ : Sub Head n m) (reference : Fin k)
    (body : Code Head Operation Effect n (k + 1)) :
    substitute σ (instantiateHandle reference body) =
      instantiateHandle reference (substitute σ body) := by
  unfold instantiateHandle
  rw [renameHandles_substitute]

/-- Include the previous suspension-free computation syntax at any handle
scope, without changing a native payload or either native-value binder. -/
def embed {n k : Nat} : ScopedComputation.Code Head Operation n → Code Head Operation Effect n k
  | .returnValue term => .returnValue term
  | .sequence first body => .sequence (embed first) (embed body)
  | .sequenceSigma first body => .sequenceSigma (embed first) (embed body)
  | .choose left right => .choose (embed left) (embed right)
  | .call operation argument => .call operation argument

theorem embed_substitute (σ : Sub Head n m) (code : ScopedComputation.Code Head Operation n) :
    embed (Effect := Effect) (k := k) (code.substitute σ) = substitute σ (embed code) := by
  induction code generalizing m with
  | returnValue term => rfl
  | sequence first body ihFirst ihBody =>
      simp only [ScopedComputation.Code.substitute, embed, substitute, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody =>
      simp only [ScopedComputation.Code.substitute, embed, substitute, ihFirst, ihBody]
  | choose left right ihLeft ihRight =>
      simp only [ScopedComputation.Code.substitute, embed, substitute, ihLeft, ihRight]
  | call operation argument => rfl

theorem embed_renameHandles (θ : Fin k → Fin l) (code : ScopedComputation.Code Head Operation n) :
    renameHandles θ (embed (Effect := Effect) code) = embed code := by
  induction code with
  | returnValue term => rfl
  | sequence first body ihFirst ihBody => simp only [embed, renameHandles, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody => simp only [embed, renameHandles, ihFirst, ihBody]
  | choose left right ihLeft ihRight => simp only [embed, renameHandles, ihLeft, ihRight]
  | call operation argument => rfl

/-- Inclusion retains the entire old source syntax, not only its answers. -/
theorem embed_injective :
    Function.Injective (embed (Head := Head) (Operation := Operation)
      (Effect := Effect) (n := n) (k := k)) := by
  intro first second equal
  induction first with
  | returnValue term => cases second <;> simp_all [embed]
  | sequence first body ihFirst ihBody =>
      cases second <;> simp_all [embed]
      exact ⟨ihFirst rfl, ihBody rfl⟩
  | sequenceSigma first body ihFirst ihBody =>
      cases second <;> simp_all [embed]
      exact ⟨ihFirst rfl, ihBody rfl⟩
  | choose left right ihLeft ihRight =>
      cases second <;> simp_all [embed]
      exact ⟨ihLeft rfl, ihRight rfl⟩
  | call operation argument => cases second <;> simp_all [embed]

end Code

namespace Examples

/-- A native variable is captured inside suspended code, then referred to
under a native value binder; the suspension reference has its own position. -/
def nativeBody : Code Nat Unit Unit 2 1 :=
  .letNeed (.call () (.var 0))
    (.sequence (.force 0) (.returnValue (.pair (.var 1) (.var 0))))

theorem native_opening_preserves_free_variable :
    Code.instantiate (.var 0 : Tm Nat 1) nativeBody =
      (.letNeed (.call () (.var 0))
        (.sequence (.force 0) (.returnValue (.pair (.var 1) (.var 0)))) :
          Code Nat Unit Unit 1 1) := by
  rfl

theorem native_opening_rejects_capture :
    Code.instantiate (.var 0 : Tm Nat 1) nativeBody ≠
      (.letNeed (.call () (.var 0))
        (.sequence (.force 0) (.returnValue (.pair (.var 0) (.var 0)))) :
          Code Nat Unit Unit 1 1) := by
  decide

/-- The suspended expression uses an older handle. Only its body receives
the newest handle, which must remain zero under ambient handle weakening. -/
def handleBody : Code Nat Unit Unit 1 1 :=
  .letNeed (.force 0)
    (.sequence (.force 0) (.choose (.force 1) (.returnValue (.var 0))))

theorem handle_weakening_separates_binders :
    Code.renameHandles wk handleBody =
      (.letNeed (.force 1)
        (.sequence (.force 0) (.choose (.force 2) (.returnValue (.var 0)))) :
          Code Nat Unit Unit 1 2) := by
  rfl

theorem handle_weakening_rejects_capture :
    Code.renameHandles wk handleBody ≠
      (.letNeed (.force 1)
        (.sequence (.force 1) (.choose (.force 2) (.returnValue (.var 0)))) :
          Code Nat Unit Unit 1 2) := by
  decide

end Examples

#print axioms Code.rename_comp
#print axioms Code.substitute_comp
#print axioms Code.substitute_instantiate
#print axioms Code.substitute_consSub
#print axioms Code.renameHandles_comp
#print axioms Code.renameHandles_substitute
#print axioms Code.embed_substitute
#print axioms Code.embed_injective
#print axioms Examples.native_opening_preserves_free_variable
#print axioms Examples.native_opening_rejects_capture
#print axioms Examples.handle_weakening_separates_binders
#print axioms Examples.handle_weakening_rejects_capture

end ScopedNeedComputation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
