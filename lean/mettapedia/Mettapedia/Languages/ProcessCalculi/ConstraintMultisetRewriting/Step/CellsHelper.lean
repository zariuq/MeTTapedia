import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Cells
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualDiamond

/-!
# Cells of the helper instance: residual faces commute along the closing swaps

The square of two helper firings `f` and `g` closes by swapping their two helpers
(`Helpers.helper_closes`, with `Helpers.swapIso`). Here:

* **The residual faces commute along the swap** (`Helpers.helper_cube`): a third firing read after
  `f` and then `g`, and carried along the swap, is the same firing read after `g` and then `f`. Hence
  the cube law holds for every closing choice whose frame isomorphisms are the swaps and whose
  occurrence renamings are the identity (`Helpers.helperCubeLaw`).
  The concrete operation `Helpers.helperClosing` retains these swap witnesses;
  `Helpers.helperClosing_cube` instantiates the cube law for that operation.
* **The closing swaps cohere** (`Helpers.swap_swap`, `Helpers.swap_braid`): a swap is its own inverse,
  and the two ways of reversing three helpers by swaps of neighbours agree. These are the relations
  of the symmetric group on the helpers; they hold because fresh helpers are allocated by coproduct
  and the swaps are coproduct symmetries (Mac Lane coherence for the symmetric monoidal structure of
  coproducts). They are the face identities a 3-cell's closing isomorphisms need.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Frames (Frame)

namespace Helpers

variable {S : Signature} {O : Type} [DecidableEq O]

omit [DecidableEq O] in
theorem cube_value {F : Frame S} (first second : MetaArity S) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S F.arity) Γ sort)
    {φ : Assignment F.arity (extend F first).arity}
    {φ' : Assignment (extend F first).arity (extend (extend F first) second).arity}
    {ψ : Assignment F.arity (extend F second).arity}
    {ψ' : Assignment (extend F second).arity (extend (extend F second) first).arity}
    (hφ : φ = incl F first) (hφ' : φ' = incl (extend F first) second)
    (hψ : ψ = incl F second) (hψ' : ψ' = incl (extend F second) first) :
    instantiate (swap F first second) (instantiate φ' (instantiate φ value)) =
      instantiate ψ' (instantiate ψ value) := by
  subst hφ hφ' hψ hψ'
  exact swap_value F first second value

omit [DecidableEq O] in
theorem cube_guards {F : Frame S} (first second : MetaArity S)
    (guards : EquationStore (Observation S F.arity))
    {φ : Assignment F.arity (extend F first).arity}
    {φ' : Assignment (extend F first).arity (extend (extend F first) second).arity}
    {ψ : Assignment F.arity (extend F second).arity}
    {ψ' : Assignment (extend F second).arity (extend (extend F second) first).arity}
    (hφ : φ = incl F first) (hφ' : φ' = incl (extend F first) second)
    (hψ : ψ = incl F second) (hψ' : ψ' = incl (extend F second) first) :
    (Frames.contextual S).applyStore (swap F first second)
        ((Frames.contextual S).applyStore φ' ((Frames.contextual S).applyStore φ guards)) =
      (Frames.contextual S).applyStore ψ' ((Frames.contextual S).applyStore ψ guards) := by
  subst hφ hφ' hψ hψ'
  exact (congrArg ((Frames.contextual S).applyStore (swap F first second))
      (Frames.applyStore_applyStore (X := Frames.contextual S) (incl F first)
        (incl (extend F first) second) guards)).trans
    ((Frames.applyStore_applyStore (X := Frames.contextual S) _ _ guards).trans
      ((congrArg (fun assignment => (Frames.contextual S).applyStore assignment guards)
        (swap_incl_incl F first second)).trans
        (Frames.applyStore_applyStore (X := Frames.contextual S) (incl F second)
          (incl (extend F second) first) guards).symm))

/-- **The residual faces of helper firings commute along the closing swap.** -/
theorem helper_cube {s : State S O} {f g : Firing s} (h : Firing s) (first : helperStep.Admits f)
    (second : helperStep.Admits g) (afterFirst : helperStep.Admits (helperTransport.residual f first g))
    (afterSecond : helperStep.Admits (helperTransport.residual g second f)) :
    (helperTransport.residual (helperTransport.residual f first g) afterFirst
        (helperTransport.residual f first h)).move
        (t := helperStep.result (helperTransport.residual g second f) afterSecond)
        (swap s.frame f.helper g.helper) =
      helperTransport.residual (helperTransport.residual g second f) afterSecond
        (helperTransport.residual g second h) :=
  Firing.mk_congr _ _
    (cube_value f.helper g.helper h.value (along_eq f first) (along_eq _ afterFirst)
      (along_eq g second) (along_eq _ afterSecond))
    (cube_guards f.helper g.helper h.guards (along_eq f first) (along_eq _ afterFirst)
      (along_eq g second) (along_eq _ afterSecond))

/-- **The cube law of the helper transport**, for every closing choice whose frame isomorphisms are
the swaps of the two helpers and whose occurrence renamings are the identity. -/
theorem helperCubeLaw (close : (helperTransport (S := S) (O := O)).Closing)
    (swaps : ∀ {s : State S O} {f g : Firing s} (first : helperStep.Admits f)
      (second : helperStep.Admits g) (afterFirst : helperStep.Admits (helperTransport.residual f first g))
      (afterSecond : helperStep.Admits (helperTransport.residual g second f)),
      (close first second afterFirst afterSecond).frame.hom = swap s.frame f.helper g.helper)
    (fixed : ∀ {s : State S O} {f g : Firing s} (first : helperStep.Admits f)
      (second : helperStep.Admits g) (afterFirst : helperStep.Admits (helperTransport.residual f first g))
      (afterSecond : helperStep.Admits (helperTransport.residual g second f)),
      (close first second afterFirst afterSecond).rename = Equiv.refl O) :
    helperTransport.CubeLaw close := by
  intro s f g h first second afterFirst afterSecond
  have cube := helper_cube h first second afterFirst afterSecond
  have framed := swaps first second afterFirst afterSecond
  have renamed := fixed first second afterFirst afterSecond
  show helperTransport.move (close first second afterFirst afterSecond) _ = _
  generalize close first second afterFirst afterSecond = c at framed renamed ⊢
  obtain ⟨⟨hom, inv, inv_hom, hom_inv⟩, knowledge, π, present⟩ := c
  dsimp only at framed renamed
  subst framed renamed
  exact cube

/-- A concrete closing operation, retaining the declaration-swap witness. -/
def helperClosing : (helperTransport (S := S) (O := O)).Closing :=
  fun first second _afterFirst _afterSecond => helperSquareIso first second

theorem helperClosing_cube : (helperTransport (S := S) (O := O)).CubeLaw helperClosing :=
  helperCubeLaw helperClosing (by intros; rfl) (by intros; rfl)

/-- **The two ways of reversing three helpers by swaps of neighbours agree.** -/
theorem swap_braid (F : Frame S) (a b c : MetaArity S) :
    Assignment.compose (lift (swap F b c) a)
        (Assignment.compose (swap (extend F b) a c) (lift (swap F a b) c)) =
      Assignment.compose (swap (extend F c) a b)
        (Assignment.compose (lift (swap F a c) b) (swap (extend F a) b c)) := by
  funext name
  rcases name with ((name | ⟨⟩) | ⟨⟩) | ⟨⟩
  · show instantiate (lift (swap F b c) a) (instantiate (swap (extend F b) a c)
        (instantiate (incl (extend (extend F b) a) c)
          (generator (extend (extend F b) a).arity (.inl (.inl name))))) =
      instantiate (swap (extend F c) a b) (instantiate (lift (swap F a c) b)
        (generator (extend (extend (extend F a) c) b).arity (.inl (.inl (.inl name)))))
    rw [instantiate_generator, instantiate_generator]
    show instantiate (lift (swap F b c) a) (instantiate (swap (extend F b) a c)
        (generator (extend (extend (extend F b) a) c).arity (.inl (.inl (.inl name))))) =
      instantiate (swap (extend F c) a b) (instantiate (incl (extend (extend F c) a) b)
        (generator (extend (extend F c) a).arity (.inl (.inl name))))
    rw [instantiate_generator, instantiate_generator]
    show instantiate (lift (swap F b c) a)
        (generator (extend (extend (extend F b) c) a).arity (.inl (.inl (.inl name)))) =
      instantiate (swap (extend F c) a b)
        (generator (extend (extend (extend F c) a) b).arity (.inl (.inl (.inl name))))
    rw [instantiate_generator, instantiate_generator]
    show instantiate (incl (extend (extend F c) b) a)
        (generator (extend (extend F c) b).arity (.inl (.inl name))) =
      generator (extend (extend (extend F c) b) a).arity (.inl (.inl (.inl name)))
    rw [instantiate_generator]
    rfl
  · show instantiate (lift (swap F b c) a) (instantiate (swap (extend F b) a c)
        (instantiate (incl (extend (extend F b) a) c)
          (generator (extend (extend F b) a).arity (.inr ())))) =
      instantiate (swap (extend F c) a b) (instantiate (lift (swap F a c) b)
        (generator (extend (extend (extend F a) c) b).arity (.inl (.inl (.inr ())))))
    rw [instantiate_generator, instantiate_generator]
    show instantiate (lift (swap F b c) a) (instantiate (swap (extend F b) a c)
        (generator (extend (extend (extend F b) a) c).arity (.inl (.inr ())))) =
      instantiate (swap (extend F c) a b) (instantiate (incl (extend (extend F c) a) b)
        (generator (extend (extend F c) a).arity (.inr ())))
    rw [instantiate_generator, instantiate_generator]
    show instantiate (lift (swap F b c) a)
        (generator (extend (extend (extend F b) c) a).arity (.inr ())) =
      instantiate (swap (extend F c) a b)
        (generator (extend (extend (extend F c) a) b).arity (.inl (.inr ())))
    rw [instantiate_generator, instantiate_generator]
    rfl
  · show instantiate (lift (swap F b c) a) (instantiate (swap (extend F b) a c)
        (instantiate (incl (extend (extend F b) a) c)
          (generator (extend (extend F b) a).arity (.inl (.inr ()))))) =
      instantiate (swap (extend F c) a b) (instantiate (lift (swap F a c) b)
        (generator (extend (extend (extend F a) c) b).arity (.inr ())))
    rw [instantiate_generator, instantiate_generator]
    show instantiate (lift (swap F b c) a) (instantiate (swap (extend F b) a c)
        (generator (extend (extend (extend F b) a) c).arity (.inl (.inl (.inr ()))))) =
      instantiate (swap (extend F c) a b)
        (generator (extend (extend (extend F c) a) b).arity (.inr ()))
    rw [instantiate_generator, instantiate_generator]
    show instantiate (lift (swap F b c) a)
        (generator (extend (extend (extend F b) c) a).arity (.inl (.inl (.inr ())))) =
      generator (extend (extend (extend F c) b) a).arity (.inl (.inr ()))
    rw [instantiate_generator]
    show instantiate (incl (extend (extend F c) b) a)
        (generator (extend (extend F c) b).arity (.inr ())) =
      generator (extend (extend (extend F c) b) a).arity (.inl (.inr ()))
    rw [instantiate_generator]
    rfl
  · show instantiate (lift (swap F b c) a) (instantiate (swap (extend F b) a c)
        (generator (extend (extend (extend F b) a) c).arity (.inr ()))) =
      instantiate (swap (extend F c) a b) (instantiate (lift (swap F a c) b)
        (generator (extend (extend (extend F a) c) b).arity (.inl (.inr ()))))
    rw [instantiate_generator, instantiate_generator]
    show instantiate (lift (swap F b c) a)
        (generator (extend (extend (extend F b) c) a).arity (.inl (.inr ()))) =
      instantiate (swap (extend F c) a b) (instantiate (incl (extend (extend F c) a) b)
        (generator (extend (extend F c) a).arity (.inl (.inr ()))))
    rw [instantiate_generator, instantiate_generator]
    show instantiate (incl (extend (extend F c) b) a)
        (generator (extend (extend F c) b).arity (.inl (.inr ()))) =
      instantiate (swap (extend F c) a b)
        (generator (extend (extend (extend F c) a) b).arity (.inl (.inl (.inr ()))))
    rw [instantiate_generator, instantiate_generator]
    rfl

end Helpers

#print axioms Helpers.cube_value
#print axioms Helpers.cube_guards
#print axioms Helpers.helper_cube
#print axioms Helpers.helperCubeLaw
#print axioms Helpers.swap_braid

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
