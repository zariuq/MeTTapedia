import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulTransport

/-!
# Coherent residuals represent compatible solution pairs

At each future frame, restriction gives a bijection between residual solutions
and compatible pairs of solutions, after quotienting maps by their action on
terms. This is a solution-level amalgamation property. It does not assert
pushouts of raw frame morphisms or uniqueness of principal answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} [P.Guarded]
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P} {G : P.Guards}

namespace Step

structure JointSolution {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) (b : Obj) where
  first : Hom (P.target f) b
  second : Hom (P.frame (P.result g admitted)) b
  first_models : X.Models first (P.information f)
  second_models : X.Models second (P.knowledge (P.result g admitted))
  agree : X.Agree (X.comp first (P.extension f)) (X.comp second (P.along g admitted))

def jointSolutionSetoid {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s) (b : Obj) :
    Setoid (JointSolution g admitted f b) where
  r left right := X.Agree left.first right.first ∧ X.Agree left.second right.second
  iseqv := ⟨fun _ => ⟨Frames.Agree.refl _, Frames.Agree.refl _⟩,
    fun same => ⟨same.1.symm, same.2.symm⟩,
    fun first second => ⟨first.1.trans second.1, first.2.trans second.2⟩⟩

end Step

namespace Frames

def solutionSetoid {a : Obj} (store : EquationStore (Tm a)) (b : Obj) :
    Setoid {mapping : Hom a b // X.Models mapping store} where
  r left right := X.Agree left.val right.val
  iseqv := ⟨fun _ => Agree.refl _, fun same => same.symm, fun first second => first.trans second⟩

end Frames

namespace Transport.Coherent

variable (coherent : T.Coherent G) {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s)

def restrictSolution (b : Obj)
    (solution : {ρ : Hom (P.target (T.residual g admitted f)) b //
      X.Models ρ (P.information (T.residual g admitted f))}) : Step.JointSolution g admitted f b where
  first := X.comp solution.val (coherent.carry g admitted f)
  second := X.comp solution.val (P.extension (T.residual g admitted f))
  first_models := ((coherent.models_iff g admitted f solution.val).mp solution.property).1
  second_models := ((coherent.models_iff g admitted f solution.val).mp solution.property).2
  agree := coherent.restrictions_agree g admitted f solution.val

def solutionRestriction (b : Obj) :
    Quotient (Frames.solutionSetoid (X := X) (P.information (T.residual g admitted f)) b) →
      Quotient (Step.jointSolutionSetoid g admitted f b) :=
  Quotient.map (coherent.restrictSolution g admitted f b)
    (fun _ _ same => ⟨same.comp_right _, same.comp_right _⟩)

theorem solutionRestriction_injective (b : Obj) :
    Function.Injective (coherent.solutionRestriction g admitted f b) := by
  intro first second
  induction first using Quotient.inductionOn with
  | h first =>
      induction second using Quotient.inductionOn with
      | h second =>
          intro same
          obtain ⟨onFirst, onSecond⟩ := Quotient.exact same
          exact Quotient.sound (coherent.separated g admitted f b first.val second.val onFirst onSecond)

theorem solutionRestriction_surjective (b : Obj) :
    Function.Surjective (coherent.solutionRestriction g admitted f b) := by
  intro pair
  induction pair using Quotient.inductionOn with
  | h pair =>
      obtain ⟨ρ, onFirst, onSecond⟩ := coherent.amalgamate g admitted f b pair.first pair.second pair.agree
      let solved : {ρ : Hom (P.target (T.residual g admitted f)) b //
          X.Models ρ (P.information (T.residual g admitted f))} :=
        ⟨ρ, (coherent.models_iff g admitted f ρ).mpr
          ⟨(onFirst.models_iff _).mpr pair.first_models,
            (onSecond.models_iff _).mpr pair.second_models⟩⟩
      exact ⟨Quotient.mk _ solved, Quotient.sound ⟨onFirst, onSecond⟩⟩

noncomputable def solutionJoin (b : Obj) :
    Quotient (Frames.solutionSetoid (X := X) (P.information (T.residual g admitted f)) b) ≃
      Quotient (Step.jointSolutionSetoid g admitted f b) :=
  Equiv.ofBijective (coherent.solutionRestriction g admitted f b)
    ⟨coherent.solutionRestriction_injective g admitted f b,
      coherent.solutionRestriction_surjective g admitted f b⟩

include coherent in
theorem residual_solvable_iff_joint_solution :
    X.Solvable (P.information (T.residual g admitted f)) ↔
      ∃ b, Nonempty (Step.JointSolution g admitted f b) := by
  constructor
  · rintro ⟨b, ρ, solved⟩
    exact ⟨b, ⟨coherent.restrictSolution g admitted f b ⟨ρ, solved⟩⟩⟩
  · rintro ⟨b, ⟨pair⟩⟩
    obtain ⟨ρ, onFirst, onSecond⟩ := coherent.amalgamate g admitted f b pair.first pair.second pair.agree
    exact ⟨b, ρ, (coherent.models_iff g admitted f ρ).mpr
      ⟨(onFirst.models_iff _).mpr pair.first_models,
        (onSecond.models_iff _).mpr pair.second_models⟩⟩

end Transport.Coherent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
