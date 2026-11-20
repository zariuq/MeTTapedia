import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Definitions

/-!
# Synthesizing a row's typing in its own frame

`vecAdmits?` asks for each made row a type `B` formed in the row's frame at which the body is typed
there (`FrameTypedAt`). Here a function produces it, from the tree's executable checking:

* **the candidate** (`candidate`): the tree's executable synthesis (`ExecutableChecking.synth`), which
  types variables, constants, heads, type formers, reflexivity, eliminations of synthesized terms
  (applications whose function type reduces to a dependent function type, the projections) and
  abstractions applied to synthesized arguments; extended by one rule, **the non-dependent pair**:
  a pair of synthesized terms gets `Σ A (wk B)`;
* **the certificate** (`synthesize`): the candidate's universe by the tree's synthesis and universe
  recognition, and the body checked against the candidate by the tree's executable check; soundness
  by `CheckingAlgorithm.sound`. The result is exactly the proof object `vecAdmits?` needs
  (`frameTypeOf`).

**The class handled** (`Shape`): pairs of bodies of the class, and bodies that are neither
abstractions nor pairs, which the tree's synthesis is asked for: variables, constants, the recursive
call (an application of the function variable), applications of declared constants, projections,
type formers. A candidate exists only inside the class (`candidate_shape`); inside it the budget may
still run out, and the tree's synthesis may decline (an application whose function type does not
reduce to a dependent function type). **Just outside**: an abstraction, which carries no domain, has
no candidate at any budget (`candidate_lam`); its row may well be typed after its match, so a failure
here is "not decided", never a refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D numType)

/-- **The candidate type**: the tree's synthesis, with the non-dependent pair rule. -/
def candidate (fuel : Nat) {n : Nat} (Γ : Ctx Tower.Head n) : Tower.Tm n → Option (Tower.Tm n)
  | .pair a b =>
      (candidate fuel Γ a).bind fun A => (candidate fuel Γ b).bind fun B => some (.sigma A (rename wk B))
  | t => (ExecutableChecking.synth vecS.R vecChoices (vecReducer level1) fuel Γ t).map (·.1)

/-- **Just outside the class**: an abstraction has no candidate, at any budget. -/
theorem candidate_lam (fuel : Nat) {n : Nat} (Γ : Ctx Tower.Head n) (body : Tower.Tm (n + 1)) :
    candidate fuel Γ (.lam body) = none := by
  cases fuel <;> rfl

/-- **The class of bodies synthesis handles**: pairs of bodies of the class, and bodies that are
neither abstractions nor pairs. -/
inductive Shape : {n : Nat} → Tower.Tm n → Prop
  | pair {n : Nat} {a b : Tower.Tm n} : Shape a → Shape b → Shape (.pair a b)
  | synthesized {n : Nat} {t : Tower.Tm n} : (∀ body, t ≠ .lam body) → (∀ a b, t ≠ .pair a b) → Shape t

/-- **A candidate exists only inside the class.** -/
theorem candidate_shape {fuel : Nat} : ∀ {n : Nat} {Γ : Ctx Tower.Head n} {t T : Tower.Tm n},
    candidate fuel Γ t = some T → Shape t
  | _, Γ, .pair a b, _, found => by
      rw [candidate] at found
      obtain ⟨A, hA, rest⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨B, hB, -⟩ := Option.bind_eq_some_iff.mp rest
      exact .pair (candidate_shape hA) (candidate_shape hB)
  | _, Γ, .lam body, _, found => by
      rw [candidate_lam] at found
      cases found
  | _, _, .var _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)
  | _, _, .const _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)
  | _, _, .head _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)
  | _, _, .pi _ _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)
  | _, _, .sigma _ _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)
  | _, _, .id _ _ _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)
  | _, _, .app _ _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)
  | _, _, .fst _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)
  | _, _, .snd _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)
  | _, _, .refl _, _, _ => .synthesized (fun _ h => nomatch h) (fun _ _ h => nomatch h)

/-- **The row's typing, synthesized**: a type formed in the frame, and the body typed at it there. -/
def synthesize (fuel : Nat) (Γ : Context pkg) (t : Tower.Tm Γ.arity) :
    Option (Σ' B : TypeOver Γ, Typed pkg Γ.raw t B.code) :=
  (candidate fuel Γ.raw t).bind fun T =>
    (level? fuel Γ T).bind fun l =>
      (ExecutableChecking.check vecS.R vecChoices (vecReducer level1) fuel Γ.raw t T).bind fun c =>
        some ⟨⟨T, l.val, l.property.1, l.property.2⟩,
          CheckingAlgorithm.sound (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
            (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1) (vecDeclared level1) c.down
            Γ.formed ⟨l.val, l.property.1, l.property.2⟩⟩

/-- **The proof object `vecAdmits?` needs**, for the one made row of an elaborated row. -/
def frameTypeOf {n : Nat} (e : Elaborated n) (s : Σ' B : TypeOver e.frame, Typed pkg e.frame.raw e.made.code B.code) :
    ∀ m ∈ e.firing.makes, Σ' B : TypeOver e.firing.helpers.frame, FrameTypedAt m.2 B :=
  fun m member => ⟨s.1, by
    obtain rfl := List.mem_singleton.mp member
    exact s.2⟩

/-- **What synthesis returns is a typing in the frame.** -/
theorem synthesize_sound {fuel : Nat} {Γ : Context pkg} {t : Tower.Tm Γ.arity}
    {s : Σ' B : TypeOver Γ, Typed pkg Γ.raw t B.code} (_found : synthesize fuel Γ t = some s) :
    Typed pkg Γ.raw t s.1.code :=
  s.2

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.candidate
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.candidate_lam
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.candidate_shape
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.synthesize
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.frameTypeOf
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.synthesize_sound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
