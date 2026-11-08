import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mettapedia.TypeTheory.DisplayedPresheafCwf

/-!
# The candidate step's frames over the native universe

**Every category with families is a frame instance** (`cwfFrames`). Frames are contexts; a
morphism from `Γ` to `Δ` instantiates the variables of `Γ` by terms over `Δ`, that is a substitution
`Δ → Γ`; a judged term is a type with a term of it; the action is substitution; the equivalence is
equality. The action laws are exactly the CwF's substitution laws, so they hold on the nose whenever
the CwF is strict.

**The native universe** (`nativeFrames`) is the instance at the displayed-presheaf CwF: contexts are
presheaves on a syntax category, types are proof-relevant functors on the category of elements,
terms are natural sections, and substitution is precomposition with the induced functor of
categories of elements. That precomposition is strictly functorial, so the action laws hold
definitionally (`nativeFrames_act_comp`, `nativeFrames_act_id`). The caveat of the native
development, that formation of dependent products is stable only up to canonical isomorphism,
concerns type formers, not substitution, and does not reach these laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace NativeUniverse

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

/-- A judged term of a context: a type with a term of it. -/
abbrev Judged (C : Cwf.{u, v, w, w'}) (Γ : C.Ctx) : Type (max w w') := Σ A : C.Ty Γ, C.Tm Γ A

/-- **Every category with families is a frame instance**: contexts, substitutions acting on typed
terms, and equality. -/
def cwfFrames (C : Cwf.{u, v, w, w'}) : Frames (Judged C) (fun Γ Δ : C.Ctx => C.Sub Δ Γ) where
  E := fun s t => s = t
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act σ t := ⟨C.tySub t.1 σ, C.tmSub t.2 σ⟩
  id Γ := C.idS Γ
  comp g f := C.compS f g
  act_id t := Sigma.ext (C.tySub_id t.1) (by rw [C.tmSub_id]; exact cast_heq _ _)
  act_comp g f t := Sigma.ext (C.tySub_comp t.1 f g) (by rw [C.tmSub_comp]; exact cast_heq _ _)
  preserves := fun {_ _} σ {_ _} same =>
    congrArg (fun t : Judged C _ => (⟨C.tySub t.1 σ, C.tmSub t.2 σ⟩ : Judged C _)) same

/-- Solvability at CwF frames: a substitution into some later context equalizing every equation. -/
theorem cwfFrames_solvable_iff (C : Cwf.{u, v, w, w'}) {Γ : C.Ctx}
    (store : EquationStore (Judged C Γ)) :
    (cwfFrames C).Solvable store ↔ ∃ (Δ : C.Ctx) (σ : C.Sub Δ Γ), ∀ e ∈ store,
      (⟨C.tySub e.1.1 σ, C.tmSub e.1.2 σ⟩ : Judged C Δ) = ⟨C.tySub e.2.1 σ, C.tmSub e.2.2 σ⟩ :=
  Iff.rfl

section Native

open CategoryTheory Mettapedia.TypeTheory.DisplayedPresheafCwf

variable (Context : Type u) [Category.{v} Context]

/-- **The native universe as frames**: presheaf contexts on one syntax category, natural
substitutions, proof-relevant displayed families and their natural sections. -/
abbrev nativeFrames := cwfFrames (presheafCwf.{u, v, w} Context)

/-- **Native substitution is strictly functorial**: the composition law of the action holds by
definition, with no coherence isomorphism. -/
theorem nativeFrames_act_comp {Γ Δ Θ : (presheafCwf.{u, v, w} Context).Ctx}
    (g : (presheafCwf.{u, v, w} Context).Sub Θ Δ) (f : (presheafCwf.{u, v, w} Context).Sub Δ Γ)
    (t : Judged (presheafCwf.{u, v, w} Context) Γ) :
    (nativeFrames.{u, v, w} Context).act ((nativeFrames.{u, v, w} Context).comp g f) t =
      (nativeFrames.{u, v, w} Context).act g ((nativeFrames.{u, v, w} Context).act f t) :=
  rfl

/-- The identity law of the native action also holds by definition. -/
theorem nativeFrames_act_id {Γ : (presheafCwf.{u, v, w} Context).Ctx}
    (t : Judged (presheafCwf.{u, v, w} Context) Γ) :
    (nativeFrames.{u, v, w} Context).act ((nativeFrames.{u, v, w} Context).id Γ) t = t :=
  rfl

end Native

end NativeUniverse

#print axioms NativeUniverse.cwfFrames
#print axioms NativeUniverse.cwfFrames_solvable_iff
#print axioms NativeUniverse.nativeFrames_act_comp
#print axioms NativeUniverse.nativeFrames_act_id

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
