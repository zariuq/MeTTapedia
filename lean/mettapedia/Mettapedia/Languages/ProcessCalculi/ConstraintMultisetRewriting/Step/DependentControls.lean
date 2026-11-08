import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentHelpers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.EmptyRootConversion

/-!
# The candidate step at dependently typed frames: adversarial controls

Over the two-head package `Consumer.tiny` (a universe and a ground type in it, with Π- and identity
types and no declared computation):

* **A dependent pair has no swap.** After the firing that makes `x : g → g`, a firing that makes
  `y : Id (g → g) x x` is admitted, and the run of the two admits no swap at all
  (`dependent_run_has_no_swap`): its type mentions `x`, so it is not the residual of any firing at
  the start; the exact criterion fails too, since substituting `x := λx.x` changes its type
  (`dependent_not_fixed`). The independent pair of `Consumer` does swap (`independent_run_swaps`).
* **Formation up to conversion.** With `P t := Id (g → g) (λx.x) t`, `A := (λf.f)(λx.x)` and
  `B := λx.x`, the type `P A` is formed and `refl (λx.x)` has it only through conversion, since `refl`
  produces `P B`. A helper of type `P A` with that value is admitted (`converted_admitted`); the
  judged terms `refl : P A` and `refl : P B` are different and convertible, and the equation between
  them is solvable (`converted_entries`).
* **An ill-typed equation.** At the frame `y : g`, the equation between `y : g` and `λx.x : g → g`
  relates terms of different types. No solution exists in any later frame, because a solution must
  convert the types too and a Π-type never converts to a head (`illTyped_unsolvable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Dependent

namespace Consumer

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

/-! ## A dependent pair has no swap -/

theorem first_admitted : (helperStep (rules := tiny)).Admits first :=
  (admits_iff first).mpr ⟨start_solvable, by decide, fun _ _ _ => Frames.models_nil _⟩

/-- At the state the first firing made, a helper `y : Id (g → g) x x` about the first helper `x`,
valued `refl x`. -/
def dependent : Firing first.after :=
  ⟨3, ⟨.id arrow (.var 0) (.var 0), .universe, rfl, .idForm (arrow_formed _) rfl (.var 0) (.var 0)⟩,
    ⟨.refl (.var 0), .reflIntro (.var 0)⟩, []⟩

theorem dependent_admitted : (helperStep (rules := tiny)).Admits dependent :=
  (admits_iff dependent).mpr ⟨information_solvable first start_solvable,
    by simp [fire, Firing.selection, Selection.commit, first, dependent],
    fun _ _ _ => Frames.models_nil _⟩

/-- The type of `y` is not a weakening: it mentions `x`, since instantiating `x` by two different
terms gives two different types, while a weakening ignores `x`. -/
theorem dependent_not_weakened :
    ∀ T : Tm TinyHead start.frame.arity, rename wk T ≠ dependent.helper.code := by
  intro T same
  have atGround := congrArg (subst (consSub (.head .ground) ids)) same
  have atUniverse := congrArg (subst (consSub (.head .universe) ids)) same
  rw [subst_consSub_rename_wk, subst_ids] at atGround atUniverse
  have heads : (Tm.head TinyHead.ground : Tm TinyHead 0) = .head .universe :=
    (Tm.id.inj (atGround.symm.trans atUniverse)).2.1
  cases heads

/-- **The dependent pair has no swap**: the run `x : g → g` then `y : Id (g → g) x x` admits no swap
at all. -/
theorem dependent_run_has_no_swap :
    ∀ r, ¬ (helperTransport (rules := tiny) (O := Nat)).SwapStep
      (.cons first first_admitted (.cons dependent dependent_admitted (.nil _))) r :=
  no_swap_of_not_weakened dependent_not_weakened

/-- **The exact criterion fails for the dependent pair**: substituting `x := λx.x` does not fix the
firing that makes `y : Id (g → g) x x`. -/
theorem dependent_not_fixed :
    dependent.move (t := first.after)
        (projectionHom start.frame first.helper ≫ instantiate start.frame first.value) ≠ dependent := by
  intro fixed
  obtain ⟨g, residual⟩ := (residual_exists_iff first first_admitted dependent).mpr fixed
  apply dependent_not_weakened g.helper.code
  rw [← residual]
  show rename wk g.helper.code =
    subst ((helperStep (rules := tiny)).along first first_admitted).substitution g.helper.code
  rw [along_eq]
  exact (subst_projection g.helper.code).symm

/-- The independent pair swaps in front of the empty continuation. -/
theorem independent_run_swaps (a : (helperStep (rules := tiny)).Admits first)
    (a₁ : (helperStep (rules := tiny)).Admits (helperTransport.residual first a second)) :
    ∃ r, (helperTransport (rules := tiny) (O := Nat)).SwapStep
      (.cons first a (.cons (helperTransport.residual first a second) a₁ (.nil _))) r :=
  swap_exists_iff.mpr ⟨second, rfl, independent⟩

/-! ## Formation up to conversion -/

/-- `(λf.f)(λx.x)`. -/
def redex {n : Nat} : Tm TinyHead n := .app (.lam (.var 0)) (.lam (.var 0))

theorem redex_typed {n : Nat} (Γ : Ctx TinyHead n) :
    FormationSensitive.Typing tiny Γ redex arrow :=
  .appElim (.lamIntro (.piForm (arrow_formed Γ) rfl (arrow_formed _) rfl ⟨rfl, rfl, rfl⟩) rfl (.var 0))
    (identity_typed Γ)

/-- `P B ≡ P A`, by one β-step inside the identity type. -/
theorem redex_conv {n : Nat} :
    Conv tiny.headEq (.id arrow (.lam (.var 0)) (.lam (.var 0)) : Tm TinyHead n)
      (.id arrow (.lam (.var 0)) redex) tiny.computation :=
  .symm _ _ (.rel _ _ (.congIdRight (.betaPi _ _)))

/-- The formed type `P A = Id (g → g) (λx.x) ((λf.f)(λx.x))`. -/
def redexType : TypeOver (empty tiny) :=
  ⟨.id arrow (.lam (.var 0)) redex, .universe, rfl,
    .idForm (arrow_formed _) rfl (identity_typed _) (redex_typed _)⟩

/-- `refl (λx.x) : P A`, typed only through conversion. -/
def redexValue : Term (empty tiny) redexType :=
  ⟨.refl (.lam (.var 0)), .conv (.reflIntro (identity_typed _)) redexType.formed rfl redex_conv⟩

/-- `refl (λx.x) : P B`, typed directly. -/
def reflValue : Term (empty tiny) reflType :=
  ⟨.refl (.lam (.var 0)), .reflIntro (identity_typed _)⟩

/-- A helper of type `P A`, valued by a term that only conversion types. -/
def converted : Firing start := ⟨4, redexType, redexValue, []⟩

theorem converted_admitted : (helperStep (rules := tiny)).Admits converted :=
  (admits_iff converted).mpr ⟨start_solvable, by decide, fun _ _ _ => Frames.models_nil _⟩

/-- **Formation up to conversion**: `refl : P A` and `refl : P B` are different judged terms, the
frames identify them, and the equation between them is solvable. -/
theorem converted_entries :
    (⟨redexType, redexValue⟩ : Entry (empty tiny)) ≠ ⟨reflType, reflValue⟩ ∧
      (frames tiny).E (⟨redexType, redexValue⟩ : Entry (empty tiny)) ⟨reflType, reflValue⟩ ∧
      (frames tiny).Solvable (a := empty tiny)
        [((⟨redexType, redexValue⟩ : Entry (empty tiny)), ⟨reflType, reflValue⟩)] := by
  have convertible : Entry.Convertible (⟨redexType, redexValue⟩ : Entry (empty tiny)) ⟨reflType, reflValue⟩ :=
    ⟨.symm _ _ redex_conv, .refl _⟩
  refine ⟨fun same => ?_, convertible, (solvable_empty_iff _).mpr fun e member => ?_⟩
  · have codes := congrArg (fun e : Entry (empty tiny) => e.type.code) same
    cases codes
  · obtain rfl := List.mem_singleton.mp member
    exact convertible

/-! ## An ill-typed equation -/

/-- The ground type, over the empty frame. -/
def groundType : TypeOver (empty tiny) := ⟨.head .ground, .universe, rfl, ground_formed _⟩

/-- `λx.x : g → g`, as a judged term at the empty frame. -/
def identityEntry : Entry (empty tiny) := ⟨arrowType, ⟨.lam (.var 0), identity_typed _⟩⟩

theorem tiny_symm : Std.Symm tiny.headEq := ⟨fun _ _ same => same.symm⟩

/-- **An ill-typed equation is never solvable**: at the frame `y : g`, the equation `y ≐ λx.x`
between a term of `g` and a term of `g → g` has no solution in any later frame. -/
theorem illTyped_unsolvable :
    ¬ (frames tiny).Solvable (a := extend (empty tiny) groundType)
      [(Entry.last (empty tiny) groundType, identityEntry.reindex (projectionHom _ groundType))] := by
  rintro ⟨Δ, σ, solved⟩
  have types := (solved _ (List.mem_singleton_self _)).1
  exact (EmptyRootConversion.piConversionBoundary tiny rfl tiny_symm).headDisjoint (.symm _ _ types)

end Consumer

end Dependent

#print axioms Dependent.Consumer.dependent_admitted
#print axioms Dependent.Consumer.dependent_not_weakened
#print axioms Dependent.Consumer.dependent_run_has_no_swap
#print axioms Dependent.Consumer.dependent_not_fixed
#print axioms Dependent.Consumer.independent_run_swaps
#print axioms Dependent.Consumer.converted_admitted
#print axioms Dependent.Consumer.converted_entries
#print axioms Dependent.Consumer.illTyped_unsolvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
