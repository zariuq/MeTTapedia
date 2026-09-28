import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Comparison

/-!
# Runs of the executable package

Runs of the package from a term typed in the typed equality that stop, stop at
one term, and the term they stop at is equal to the start in the typed
equality. The statement concerns runs that stop; it does not say that runs
stop.

The draft's identity elimination fires only when the reflexivity witness, the
point and the endpoint are one term. For the typed equality that is not
enough: with `f : num → num`, the elimination at `refl (λ n. f n)` with point
and endpoint `f` is typed, because `λ n. f n` and `f` are equal functions, and
the linear rule reduces it, but its witness is not its point.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.ConversionCoherence
open Presentation.ConstructorSystem (Normal)
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Package (jName U0 numT)

/-! ## Runs that stop -/

/-- Runs of the package from a typed term that stop, stop at one term, equal to
the start in the typed equality. -/
theorem stopped_unique {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed rules Γ)
    {term T first second : Tower.Tm n} (typing : Typed rules Γ term T)
    (firstRuns : Reduces rules term first) (firstStopped : Normal rules first)
    (secondRuns : Reduces rules term second) (secondStopped : Normal rules second) :
    first = second ∧ Equal rules Γ term first T :=
  ⟨constructors.eq_of_normal firstStopped secondStopped
      (.trans _ _ _ (.symm _ _ (stepStar_implies_conv firstRuns))
        (stepStar_implies_conv secondRuns)),
    (reduces_preserve formed firstRuns typing).2⟩

/-! ## A witness that is not the point -/

/-- The context `f : num → num`. -/
abbrev funCtx : Tower.Ctx 1 := .snoc .nil (.pi numT numT)

/-- `λ n. f n`. -/
def etaExpanded : Tower.Tm 1 := .lam (.app (.var 1) (.var 0))

/-- `id:eliminate (num → num) f (λ y p. num) zero f (refl (λ n. f n))`. -/
def etaElimination : Tower.Tm 1 :=
  appSpine (.const jName)
    [.pi numT numT, .var 0, .lam (.lam numT), .const zeroN, .var 0, .refl etaExpanded]

/-- The names the elimination uses. -/
abbrev etaStage : Rules Tower.Head := stage (allowedIn [numN, zeroN, jName])

theorem etaElimination_typed : Typed rules funCtx etaElimination numT := by
  have numMem : numN ∈ [numN, zeroN, jName] := List.mem_cons_self ..
  have zeroMem : zeroN ∈ [numN, zeroN, jName] := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have jMem : jName ∈ [numN, zeroN, jName] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  -- the carrier `num → num` and the function `f`
  have carrier : ∀ {m : Nat} {Δ : Tower.Ctx m}, Typed etaStage Δ (.pi numT numT) U0 :=
    piT (numT_typed numMem) (numT_typed numMem)
  have fT : Typed etaStage funCtx (.var 0) (.pi numT numT) := .var 0
  -- `λ n. f n` is `f`
  have expandedT : Typed etaStage funCtx etaExpanded (.pi numT numT) :=
    .lamIntro carrier (.sort _) (.appElim (B := numT) (Derivable.var 1) (Derivable.var 0))
  have etaEq : Equal etaStage funCtx etaExpanded (.var 0) (.pi numT numT) :=
    .etaPi expandedT fT (.betaPi carrier (.sort _)
      (.appElim (B := numT) (Derivable.var 2) (Derivable.var 0)) (Derivable.var 0))
  -- the motive `λ y p. num`
  have formed₂ : Typed etaStage (.snoc funCtx (.pi numT numT))
      (.pi (.id (.pi numT numT) (.var 1) (.var 0)) U0) U1 :=
    piT (raiseT (idT carrier (.var 1) (.var 0))) U0_typed
  have formed : Typed etaStage funCtx
      (.pi (.pi numT numT) (.pi (.id (.pi numT numT) (.var 1) (.var 0)) U0)) U1 :=
    piT (raiseT carrier) formed₂
  have bodyM : Typed etaStage
      (.snoc (.snoc funCtx (.pi numT numT)) (.id (.pi numT numT) (.var 1) (.var 0))) numT U0 :=
    numT_typed numMem
  have motiveTyped : Typed etaStage funCtx (.lam (.lam numT))
      (.pi (.pi numT numT) (.pi (.id (.pi numT numT) (.var 1) (.var 0)) U0)) :=
    .lamIntro formed (.sort _) (.lamIntro formed₂ (.sort _) bodyM)
  -- the method `zero`, at the motive's value at reflexivity of `f`
  have method : Typed etaStage funCtx (.const zeroN)
      (.app (.app (.lam (.lam numT)) (.var 0)) (.refl (.var 0))) :=
    .conv (zero_typed numMem zeroMem)
      (.symm (betaTwoT formed (.sort _) formed₂ bodyM fT (.reflIntro fT))) (.sort Tower.zero)
  -- the path `refl (λ n. f n)`, at `f = f`
  have path : Typed etaStage funCtx (.refl etaExpanded) (.id (.pi numT numT) (.var 0) (.var 0)) :=
    .conv (.reflIntro expandedT) (.idCong (.refl carrier) (.sort _) etaEq etaEq)
      (.sort Tower.zero)
  -- the eliminator
  obtain ⟨w, hw, tj⟩ := jType_typed
  have declJ : etaStage.constantType jName = some Package.jType :=
    (stage_declared jMem).trans rfl
  have j0 : Typed etaStage funCtx (.const jName) (liftClosed Package.jType) :=
    .const declJ (Derivable.mono (RulesSub.constantFree _) tj) hw
  rw [jType_eq] at j0
  have j1 := Derivable.appElim j0 carrier
  have j2 := Derivable.appElim j1 fT
  have j3 := Derivable.appElim j2 motiveTyped
  have j4 := Derivable.appElim j3 method
  have j5 := Derivable.appElim j4 fT
  have j6 := Derivable.appElim j5 path
  have typed : Typed etaStage funCtx etaElimination numT :=
    .conv j6 (betaTwoT formed (.sort _) formed₂ bodyM fT path) (.sort Tower.zero)
  exact Derivable.mono (stage_sub_rules _) typed

/-- The linear rule reduces the elimination to its method. -/
theorem etaElimination_step : rules.computation.step etaElimination (.const zeroN) :=
  rules_step (listed 3 (by decide)) ⟨_, _, _, _, _, _, rfl, rfl⟩

/-- Its witness is not its point. -/
theorem etaExpanded_ne_point : etaExpanded ≠ .var 0 := by
  intro same
  cases same

#print axioms stopped_unique
#print axioms etaElimination_typed
#print axioms etaElimination_step

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
