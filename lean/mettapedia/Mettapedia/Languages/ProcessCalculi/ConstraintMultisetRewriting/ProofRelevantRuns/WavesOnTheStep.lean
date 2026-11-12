import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CellsFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeIteratedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Waves

/-!
# Waves on the step: the cells are not flag, and Helly gives every order

Two readings of joint waves on the step itself.

* **Cells.** `CellsFlag`: the cells of a transport are flag when every round whose members form
  2-cells two by two is a cell. `firstOrder_cells_not_flag`: the first-order step's cells are not
  flag; the hollow cube of `CellControls.hollow_cube` is the witness.
* **Native waves.** A family of live firings is jointly solvable (`NativeIterated.Jointly`) when the
  shadows of their informations on the state's names meet (`jointly_iff_shadows`; `shadow` is the
  set of assignments of the state's names that extend to a solution of the firing's information).
  `jointly_of_convex_shadows`: where the shadows at one frame meet two by two and are convex for
  one ternary operation, the family is jointly solvable. `every_order_admitted_of_convex`:
  **pairwise clear firings with pairwise meeting convex shadows are admitted in every order.**
* `tellers_shadows_not_convex`, `tellers_shadows_meet`, `tellers_not_convex`: for the three native
  tellers of `NativeIteratedControls`, which are pairwise clear and admit no order, the shadows meet
  two by two at the state's information frame, and no ternary operation makes all three convex.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns

open Interface

/-! ## Cells of a transport -/

section Cells

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS}
  {Firing : State → Type uF} {P : Interface.Step X O State Firing}

/-- Every two members of a round, in their order, form a 2-cell. -/
def PairwiseCells (T : Interface.Transport.{uO,uT,uH,uOcc,uS,uF,uI} P) (s : State)
    (round : List (Firing s)) : Prop :=
  ∀ i j : Fin round.length, i < j → T.Cell s [round[i], round[j]]

/-- **The cells of a transport are flag** when pairwise 2-cells give a cell. -/
def CellsFlag (T : Interface.Transport.{uO,uT,uH,uOcc,uS,uF,uI} P) : Prop :=
  ∀ (s : State) (round : List (Firing s)), PairwiseCells T s round → T.Cell s round

end Cells

open AnnotatedRuns in
/-- **The first-order step's cells are not flag**: the three tells of the hollow cube form 2-cells
two by two and no 3-cell. -/
theorem firstOrder_cells_not_flag :
    ¬ CellsFlag (firstOrderTransport ConstraintMultisetRewriting.Controls.A AnnotatedRuns.Controls.label) := by
  intro flag
  obtain ⟨⟨_, sameOne⟩, ⟨_, sameTwo⟩, ⟨_, oneTwo⟩, none⟩ := CellControls.hollow_cube
  apply none
  apply flag
  intro i j less
  fin_cases i <;> fin_cases j <;> first | exact absurd less (by decide) | assumption

/-! ## Native waves -/

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual

section Native

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **The shadow of a firing** at a frame: the assignments of the state's names that extend to a
solution of its information. -/
def shadow (s : NativeState S O Γ sort) (f : LiveFiring s) (b : Frames.Frame S) :
    Set (Assignment s.state.declarations b.arity) :=
  {shared | ∃ σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity,
    ContextualResidual.Models σ f.toNative.information ∧
      Assignment.compose σ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) = shared}

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Joint solvability is a common point of the shadows.** -/
theorem jointly_iff_shadows (s : NativeState S O Γ sort) (fs : List (LiveFiring s)) :
    NativeIterated.Jointly s fs ↔
      ∃ (b : Frames.Frame S) (shared : Assignment s.state.declarations b.arity),
        ∀ f ∈ fs, shared ∈ shadow s f b :=
  Iff.rfl

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- Two firings have a joint solution at a frame exactly when their shadows there meet. -/
theorem shadows_meet_iff (s : NativeState S O Γ sort) (f g : LiveFiring s) (b : Frames.Frame S) :
    (shadow s f b ∩ shadow s g b).Nonempty ↔
      Nonempty (Joint s f.toNative.information g.toNative.information b) := by
  constructor
  · rintro ⟨shared, ⟨σ, modelsF, agreeF⟩, ⟨τ, modelsG, agreeG⟩⟩
    exact ⟨⟨σ, τ, modelsF, modelsG, agreeF.trans agreeG.symm⟩⟩
  · rintro ⟨joint⟩
    exact ⟨_, ⟨joint.left, joint.left_models, rfl⟩, ⟨joint.right, joint.right_models, joint.agree.symm⟩⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Convex shadows that meet two by two at one frame are jointly solvable.** -/
theorem jointly_of_convex_shadows {s : NativeState S O Γ sort} {fs : List (LiveFiring s)}
    (b : Frames.Frame S)
    (m : Assignment s.state.declarations b.arity → Assignment s.state.declarations b.arity →
      Assignment s.state.declarations b.arity → Assignment s.state.declarations b.arity)
    (nonempty : fs ≠ []) (convex : ∀ f ∈ fs, MedianConvex m (shadow s f b))
    (pairwise : ∀ f ∈ fs, ∀ g ∈ fs, (shadow s f b ∩ shadow s g b).Nonempty) :
    NativeIterated.Jointly s fs := by
  obtain ⟨shared, every⟩ := helly (m := m) (fs.map fun f => shadow s f b) (by simpa using nonempty)
    (by
      intro C member
      obtain ⟨f, inside, rfl⟩ := List.mem_map.mp member
      exact convex f inside)
    (by
      intro C memberC E memberE
      obtain ⟨f, insideF, rfl⟩ := List.mem_map.mp memberC
      obtain ⟨g, insideG, rfl⟩ := List.mem_map.mp memberE
      exact pairwise f insideF g insideG)
  exact ⟨b, shared, fun f member => every _ (List.mem_map.mpr ⟨f, member, rfl⟩)⟩

/-- **Pairwise clear firings whose convex shadows meet two by two are admitted in every order.** -/
theorem every_order_admitted_of_convex {s : NativeState S O Γ sort} {fs : List (LiveFiring s)}
    (admitted : ∀ f ∈ fs, f.toNative.Realized) (clears : fs.Pairwise NativeIterated.Clears)
    (b : Frames.Frame S)
    (m : Assignment s.state.declarations b.arity → Assignment s.state.declarations b.arity →
      Assignment s.state.declarations b.arity → Assignment s.state.declarations b.arity)
    (nonempty : fs ≠ []) (convex : ∀ f ∈ fs, MedianConvex m (shadow s f b))
    (pairwise : ∀ f ∈ fs, ∀ g ∈ fs, (shadow s f b ∩ shadow s g b).Nonempty)
    {order : List (LiveFiring s)} (perm : order.Perm fs) :
    ∃ t, NativeIterated.Sequential s order t :=
  NativeIterated.every_order_admitted
    ⟨admitted, clears, jointly_of_convex_shadows b m nonempty convex pairwise⟩ perm

end Native

open NativeIteratedControls in
/-- **The native hollow cube is a failure of convexity**: wherever the shadows of the three
pairwise clear tellers meet two by two at one frame, no ternary operation makes all three convex. -/
theorem tellers_shadows_not_convex (b : Frames.Frame NativeResidualExample.tiny)
    (pairwise : ∀ f ∈ tellers, ∀ g ∈ tellers, (shadow pair f b ∩ shadow pair g b).Nonempty)
    (m : Assignment pair.state.declarations b.arity → Assignment pair.state.declarations b.arity →
      Assignment pair.state.declarations b.arity → Assignment pair.state.declarations b.arity) :
    ¬ ∀ f ∈ tellers, MedianConvex m (shadow pair f b) :=
  fun convex => tellers_not_jointly
    (jointly_of_convex_shadows b m (List.cons_ne_nil _ _) convex pairwise)

open NativeIteratedControls in
/-- The shared assignment of a valuation of `X` and `Y`. -/
def tellersPoint (valueX valueY : Bool) : Assignment twoNames (ContextualActivatedStep.target
    NativeResidualExample.noLocals twoNames) :=
  Assignment.compose (valuation valueX valueY)
    (ContextualSelectionViews.capturedTarget NativeResidualExample.noLocals twoNames)

open NativeIteratedControls in
/-- **The shadows of the three native tellers meet two by two** at the state's information frame. -/
theorem tellers_shadows_meet :
    ∀ f ∈ tellers, ∀ g ∈ tellers,
      (shadow pair f pair.infoFrame ∩ shadow pair g pair.infoFrame).Nonempty := by
  have inX : ∀ valueY, tellersPoint true valueY ∈ shadow pair tellX pair.infoFrame :=
    fun valueY => ⟨valuation true valueY, (models_tellX _).mpr rfl, rfl⟩
  have inY : ∀ valueX, tellersPoint valueX false ∈ shadow pair tellY pair.infoFrame :=
    fun valueX => ⟨valuation valueX false, (models_tellY _).mpr rfl, rfl⟩
  have inSame : ∀ value,
      tellersPoint value value ∈ shadow pair NativeIteratedControls.tellSame pair.infoFrame :=
    fun value => ⟨valuation value value, (models_tellSame _).mpr rfl, rfl⟩
  intro f inF g inG
  simp only [tellers, List.mem_cons, List.not_mem_nil, or_false] at inF inG
  rcases inF with rfl | rfl | rfl <;> rcases inG with rfl | rfl | rfl
  · exact ⟨_, inX false, inX false⟩
  · exact ⟨_, inX false, inY true⟩
  · exact ⟨_, inX true, inSame true⟩
  · exact ⟨_, inY true, inX false⟩
  · exact ⟨_, inY true, inY true⟩
  · exact ⟨_, inY false, inSame false⟩
  · exact ⟨_, inSame true, inX true⟩
  · exact ⟨_, inSame false, inY false⟩
  · exact ⟨_, inSame true, inSame true⟩

open NativeIteratedControls in
/-- **No ternary operation makes the three native tellers' shadows convex**, unconditionally. -/
theorem tellers_not_convex
    (m : Assignment pair.state.declarations pair.infoFrame.arity →
      Assignment pair.state.declarations pair.infoFrame.arity →
      Assignment pair.state.declarations pair.infoFrame.arity →
      Assignment pair.state.declarations pair.infoFrame.arity) :
    ¬ ∀ f ∈ tellers, MedianConvex m (shadow pair f pair.infoFrame) :=
  tellers_shadows_not_convex pair.infoFrame tellers_shadows_meet m

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns
