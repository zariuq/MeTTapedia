import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullFibre
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreConservativityControls

/-!
# The fibre join in a concrete package: controls

The package is the cumulative tower with one rigid sort constant `point : U0`, where every
hypothesis of the fibre join is discharged (`ContextualDependentFibre.Controls`).

**Positive control: a take that crosses a binder** (`binder_take_admitted`). At the list frame of two
unary metavariables `m, n`, a first-order firing takes the row labelled `n(x)` with the pattern
`m(x)`: the take equation is `λx. m x ≐ λx. n x`. The dependent unifier answers it with the
endomorphism `m, n ↦ λx. m x`, principal with η (`endo_principal`). The firing is admitted by the
first-order step and its translation by the dependent full step, and the two results correspond.

**Negative control: a firing outside the image** (`pairFiring`). At the same translated state, the
dependent full step admits a firing with one fresh helper `p : Σ point. point` (`pair_admitted`).
No first-order firing translates to it (`pair_not_translated`): translated firings make no helpers.
Its result frame has a variable of dependent pair type (`pair_result_has_sigma`), which no translated
telescope has (`translated_no_sigma`), so its result lies outside the fibre
(`pair_result_not_translated`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.FibreControls

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentEtaLong Translation
open ContextualDependentFibre ContextualDependentFibre.Controls

/-! ## The endomorphic answer of the pattern equation -/

/-- The endomorphism `m, n ↦ m(x)` of the two-metavariable frame. -/
def endoCollapse :
    Binding.ContextualFamily.Assignment (S := pointSig) (pairFrame star).get (pairFrame star).get
  | ⟨0, _⟩ => Binding.ContextualFamily.generator (pairFrame star).get (mIdx star)
  | ⟨1, _⟩ => Binding.ContextualFamily.generator (pairFrame star).get (mIdx star)
  | ⟨_ + 2, h⟩ => absurd h (by simp)

theorem endoCollapse_solves :
    (listFrames pointSig).Models (a := pairFrame star) (b := pairFrame star) endoCollapse
      (patternStore star) :=
  (pattern_listModels_iff star endoCollapse).mpr rfl

/-- **With η, the pattern equation has an endomorphic principal answer** in the unifier's frame:
the translation of `m, n ↦ m(x)`. -/
theorem endo_principal :
    (frames setting.levels).Principal (a := Ψ.obj (pairFrame star)) (m := Ψ.obj (pairFrame star))
      (Ψ.store (patternStore star)) (Ψ.hom endoCollapse) where
  sound := Ψ.models endoCollapse_solves
  factors := by
    intro b τ solved
    have equation := (solved _ (List.mem_singleton_self _)).2
    change Equal setting.R b.raw (etaOf (τ.substitution (mIdx star))) (etaOf (τ.substitution (nIdx star)))
      (subst τ.substitution (liftClosed (unaryType names star))) at equation
    rw [subst_liftClosed] at equation
    have typedAt : ∀ i : Fin (pairFrame star).length,
        Typed setting.R b.raw (τ.substitution i) (liftClosed (unaryType names star)) := by
      intro i
      have typed := τ.typed i
      change Typed setting.R b.raw (τ.substitution i)
        (subst τ.substitution (Ctx.lookup (metaCtx names (pairFrame star)) i)) at typed
      exact pair_lookup_subst names star τ.substitution i ▸ typed
    refine ⟨τ, fun t => act_equal_of_substEq ⟨τ.typed, fun i => ?_⟩ t⟩
    rcases i with ⟨_ | _ | k, bound⟩
    · change Equal setting.R b.raw (τ.substitution (mIdx star)) (etaOf (τ.substitution (mIdx star)))
        (subst τ.substitution (Ctx.lookup (metaCtx names (pairFrame star)) (mIdx star)))
      exact (pair_lookup_subst names star τ.substitution (mIdx star)).symm ▸
        EtaFrames.eta_equal names realization star (typedAt (mIdx star))
    · change Equal setting.R b.raw (τ.substitution (nIdx star)) (etaOf (τ.substitution (mIdx star)))
        (subst τ.substitution (Ctx.lookup (metaCtx names (pairFrame star)) (nIdx star)))
      exact (pair_lookup_subst names star τ.substitution (nIdx star)).symm ▸
        Derivable.trans (EtaFrames.eta_equal names realization star (typedAt (nIdx star))) (.symm equation)
    · exact absurd bound (show ¬ (k + 1 + 1 < 2) by omega)

/-! ## The positive control: a take that crosses a binder -/

/-- Labels: the row `1` is `n(x)`; every other row is `m(x)`. -/
def label (o : Nat) : Obs (pairFrame star) :=
  if o = 1 then occurrence (pairFrame star) (nIdx star) else occurrence (pairFrame star) (mIdx star)

/-- One present row, `1 : n(x)`, and empty knowledge. -/
def start : Configuration (Obs (pairFrame star)) Nat := ⟨[], {1}⟩

/-- Take the row `1` with the pattern `m(x)`. -/
def takeFiring :
    AnnotatedRuns.Firing (Obs (pairFrame star))
      (Binding.ContextualFamily.Assignment (S := pointSig) (pairFrame star).get (pairFrame star).get) Nat :=
  ⟨⟨[occurrence (pairFrame star) (mIdx star)], [], [], [], []⟩, [], ⟨[1], [], []⟩⟩

/-- Its problem is the pattern equation `m(x) ≐ n(x)`. -/
theorem takeFiring_problem :
    takeFiring.selection.problem label takeFiring.rule start = patternStore star := rfl

theorem takeFiring_decided :
    EndoDecided (S := setting) facts roots heads church names realization
      (takeFiring.selection.problem label takeFiring.rule start) := by
  rw [takeFiring_problem]
  exact .inl ⟨_, endo_principal⟩

theorem takeFiring_firstOrder :
    (AnnotatedRuns.firstOrder (action (pairFrame star)) label).Admits (s := start) takeFiring := by
  refine (firstOrder_admits_iff label start takeFiring rfl (fun _ _ member => by cases member)).mpr
    ⟨⟨by decide, by decide, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro o member
    simp only [takeFiring, List.mem_singleton] at member
    subst member
    simp [start]
  · intro o member
    cases member
  · intro o _ readToo
    cases readToo
  · intro o member
    cases member
  · rw [takeFiring_problem]
    exact ⟨endoCollapse, endoCollapse_solves⟩
  · intro σ _ e member
    cases member
  · intro p member
    cases member

/-- **A take that crosses a binder is admitted on both sides**: by the first-order step of the
second-order action, and, translated, by the dependent full step. -/
theorem binder_take_admitted :
    (AnnotatedRuns.firstOrder (action (pairFrame star)) label).Admits (s := start) takeFiring ∧
      (step setting.levels Nat).Admits
        (s := translateState (S := setting) facts roots heads church names realization label start)
        (translateFiring (S := setting) facts roots heads church names realization label start takeFiring) :=
  ⟨takeFiring_firstOrder,
    ((admits_translate_iff (S := setting) facts roots heads algebra complete rigid church names realization
      sortInjective point_closed @operatorInjective label start takeFiring rfl
      (fun _ _ member => by cases member) takeFiring_decided
      (fun _ member => by cases member)).mp takeFiring_firstOrder).2⟩

/-- **The take constrains**: every dependent solution of the translated information equates the
translated pattern `λx. m x` with the row `λx. n x`. -/
theorem binder_take_constrains {Θ : Context setting.R}
    {τ : Θ ⟶ (translateFiring (S := setting) facts roots heads church names realization label start
      takeFiring).helpers.frame}
    (solved : (frames setting.levels).Models τ
      (translateFiring (S := setting) facts roots heads church names realization label start takeFiring).information) :
    (frames setting.levels).E
      ((frames setting.levels).act τ (Ψ.tm (occurrence (pairFrame star) (mIdx star))))
      ((frames setting.levels).act τ (Ψ.tm (occurrence (pairFrame star) (nIdx star)))) :=
  (translateFiring (S := setting) facts roots heads church names realization label start takeFiring).take_solved
    solved (p := Ψ.tm (occurrence (pairFrame star) (mIdx star))) (o := 1)
    (List.mem_singleton_self _)

/-- **The results correspond.** -/
theorem binder_take_results :
    (step setting.levels Nat).result
        (translateFiring (S := setting) facts roots heads church names realization label start takeFiring)
        binder_take_admitted.2 =
      translateState (S := setting) facts roots heads church names realization label
        (takeFiring.result label start) :=
  result_translate (S := setting) facts roots heads church names realization label start takeFiring _

/-! ## The negative control: a helper of dependent pair type -/

/-- The type `Σ point. point` over the translated frame. -/
def pairType : TypeOver (Ψ.obj (pairFrame star)) :=
  ⟨pointPair, .sort (.max Tower.zero Tower.zero), .sort _, pointPair_typed _⟩

/-- The translated state of the positive control. -/
abbrev translatedStart : State setting.R Nat :=
  translateState (S := setting) facts roots heads church names realization label start

/-- **A firing with a fresh helper `p : Σ point. point`**, and nothing else. -/
def pairFiring : Firing setting.levels translatedStart where
  helpers := .cons pairType (.nil _)
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := []

theorem pair_admitted : (step setting.levels Nat).Admits pairFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (enabled_iff pairFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩, ?_, ?_⟩
  · refine ⟨pairFiring.helpers.frame, 𝟙 _, fun e member => absurd member ?_⟩
    show e ∉ ([] : EquationStore (TotalTerm pairFiring.helpers.frame))
    exact List.not_mem_nil
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **No first-order firing translates to it**: translated firings make no helpers. -/
theorem pair_not_translated
    (g : AnnotatedRuns.Firing (Obs (pairFrame star))
      (Binding.ContextualFamily.Assignment (S := pointSig) (pairFrame star).get (pairFrame star).get) Nat) :
    translateFiring (S := setting) facts roots heads church names realization label start g ≠ pairFiring := by
  intro same
  have helpers := congrArg Firing.helpers same
  cases helpers

/-- A variable of dependent pair type. -/
def HasSigma (Γ : Context setting.R) : Prop :=
  ∃ (i : Fin Γ.arity) (A : Tm Tower.Head Γ.arity) (B : Tm Tower.Head (Γ.arity + 1)),
    Ctx.lookup Γ.raw i = .sigma A B

theorem telescopeType_cases {sig : Binding.Signature} (nm : BindingSignatureEmbedding.Names sig) :
    ∀ (bound : List sig.Srt) (result : Tm Tower.Head 0),
      BindingSignatureEmbedding.telescopeType nm bound result = result ∨
        ∃ d c, BindingSignatureEmbedding.telescopeType nm bound result =
          BindingSignatureEmbedding.closedArrow d c
  | [], _ => .inl rfl
  | sort :: bound, result => by
      rcases telescopeType_cases nm bound (BindingSignatureEmbedding.closedArrow
          (BindingSignatureEmbedding.sortType nm sort) result) with same | ⟨d, c, same⟩
      · exact .inr ⟨_, _, same⟩
      · exact .inr ⟨d, c, same⟩

theorem rename_ne_sigma {n m : Nat} (ρ : Ren n m) {t : Tm Tower.Head n}
    (notSigma : ∀ A B, t ≠ .sigma A B) : ∀ A B, rename ρ t ≠ .sigma A B := by
  intro A B same
  cases t with
  | sigma A' B' => exact notSigma A' B' rfl
  | _ => cases same

/-- **No translated telescope has a variable of dependent pair type**: every type of a translated
telescope is a sort or a function type. -/
theorem translated_no_sigma (N : List (Binding.MetaArity pointSig)) : ¬ HasSigma (Ψ.obj N) := by
  rintro ⟨i, A, B, same⟩
  have lookup : Ctx.lookup (Ψ.obj N).raw i =
      liftClosed (BindingSignatureEmbedding.bindingType names (N.get i).1 (N.get i).2) :=
    metaCtx_lookup names N i
  rw [lookup] at same
  have closed : ∀ A B, BindingSignatureEmbedding.bindingType names (N.get i).1 (N.get i).2 ≠
      (.sigma A B : Tm Tower.Head 0) := by
    intro A' B'
    rcases telescopeType_cases names (N.get i).1
        (BindingSignatureEmbedding.sortType names (N.get i).2) with same' | ⟨d, c, same'⟩
    · intro h
      have h' : (BindingSignatureEmbedding.sortType names (N.get i).2 : Tm Tower.Head 0) = .sigma A' B' :=
        same'.symm.trans h
      cases h'
    · intro h
      have h' : BindingSignatureEmbedding.closedArrow d c = (.sigma A' B' : Tm Tower.Head 0) :=
        same'.symm.trans h
      cases h'
  exact rename_ne_sigma Fin.elim0 closed A B same

/-- **The pair firing's result frame has a variable of dependent pair type.** -/
theorem pair_result_has_sigma :
    HasSigma ((step setting.levels Nat).result pairFiring pair_admitted).frame :=
  ⟨⟨0, Nat.succ_pos _⟩, _, _, rfl⟩

/-- **Its result lies outside the fibre**: its frame is no translated telescope. -/
theorem pair_result_not_translated (N : List (Binding.MetaArity pointSig)) :
    ((step setting.levels Nat).result pairFiring pair_admitted).frame ≠ Ψ.obj N := by
  intro same
  exact translated_no_sigma N (same ▸ pair_result_has_sigma)

end DependentFull.FibreControls

#print axioms DependentFull.FibreControls.endo_principal
#print axioms DependentFull.FibreControls.takeFiring_firstOrder
#print axioms DependentFull.FibreControls.binder_take_admitted
#print axioms DependentFull.FibreControls.binder_take_constrains
#print axioms DependentFull.FibreControls.binder_take_results
#print axioms DependentFull.FibreControls.pair_admitted
#print axioms DependentFull.FibreControls.pair_not_translated
#print axioms DependentFull.FibreControls.translated_no_sigma
#print axioms DependentFull.FibreControls.pair_result_has_sigma
#print axioms DependentFull.FibreControls.pair_result_not_translated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
