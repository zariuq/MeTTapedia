import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationImage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBinding

/-!
# Definitions transfer on the image

A **definition** at a list frame is the equation `m(x̄) ≐ t` where `t`, over `m`'s parameters, does
not mention `m` (`definitionStore`). This is the information a helper firing adds.

* **Second order** (`definition_principal`): the binding `m ↦ t` is a principal answer
  (`ContextualBinding.answer`).
* **Dependent frames, on the image** (`definition_factorsOnImage`): the translated binding factors
  every dependent solution of the translated definition on translated terms. The proof only uses
  that a variable agrees applicatively with its eta expansion (`appAgree_generator`): the code of
  the identity assignment applied to arguments beta-reduces to the variable applied to them.
* **Hence** (`definition_entails_iff`): asks of translated equation guards are preserved and
  reflected at every definition, and both sides are solvable (`definition_solvable`). On the
  definition fragment, admission with equation guards is preserved and reflected by the
  translation, although principal answers on all judged terms are not (`pattern_no_principal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace Translation

open CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type} {S : Binding.Signature} (names : BindingSignatureEmbedding.Names S)

/-! ## The translation of a metavariable applied to its parameters -/

theorem encodeArgs_selfArgs (M : List (Binding.MetaArity S)) :
    ∀ (P : List S.Srt) (k : Fin P.length)
      (h : P.length = (P.map (fun sort => (([] : List S.Srt), sort))).length),
      encodeArgs (Head := Head) names M (Binding.ContextualFamily.selfArgs (T := Sig S M) P)
        (Fin.cast h k) = .var (inner k)
  | [], k, _ => k.elim0
  | p :: P, k, _ => by
      refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · have moved := encodeArgs_rename (Head := Head) (Δ := p :: P) names M
          (Binding.ContextualFamily.selfArgs (T := Sig S M) P) (fun _ v => .succ v) wk
          (renGood_weaken M p) (Fin.cast (by simp) k)
        rw [encodeArgs_selfArgs M P k (by simp)] at moved
        exact moved

theorem encode_generator (M : List (Binding.MetaArity S)) (j : Fin M.length) :
    encode (Head := Head) names M (Binding.ContextualFamily.generator M.get j) =
      spine (.var (outer j)) (fun k => .var (inner k)) := by
  have castLength : (M.get j).1.length =
      ((M.get j).1.map (fun sort => (([] : List S.Srt), sort))).length := by simp
  show spine (.var (outer j)) (fun k => encodeArgs names M
      (Binding.ContextualFamily.selfArgs (T := Sig S M) (M.get j).1) (Fin.cast castLength k)) = _
  exact congrArg (spine (.var (outer j)))
    (funext fun k => encodeArgs_selfArgs names M (M.get j).1 k castLength)

section Agreement

variable {rules : Rules Head}

/-- Agreement survives conversion of the second head. -/
theorem AppAgree.conv_right {n : Nat} {f g g' : Tm Head n} {p : Nat}
    (agree : AppAgree (headEq := rules.headEq) (root := rules.computation) f g p)
    (same : Conv rules.headEq g g' rules.computation) :
    AppAgree (headEq := rules.headEq) (root := rules.computation) f g' p := by
  intro k ρ w w' arguments
  exact .trans _ _ _ (agree ρ w w' arguments)
    (conv_spine (Conv.renameTerms ρ same) (fun _ => .refl _))

/-- **A metavariable agrees applicatively with the code of the identity**, under every substitution:
the eta expansion applied to arguments beta-reduces to the variable applied to them. -/
theorem appAgree_generator (M : List (Binding.MetaArity S)) {n : Nat}
    (τ : Sub Head M.length n) (j : Fin M.length) :
    AppAgree (headEq := rules.headEq) (root := rules.computation) (τ j)
      (subst τ (homCode names M M (Binding.ContextualFamily.generator M.get) j))
      (M.get j).1.length := by
  intro k ρ w w' arguments
  have beta := conv_of_beta (headEq := rules.headEq) (root := rules.computation)
    (spine_beta (fun i => rename ρ (τ i)) (M.get j).1.length
      (encode names M (Binding.ContextualFamily.generator M.get j)) w')
  have target : subst (appendSub w' (fun i => rename ρ (τ i)))
      (encode (Head := Head) names M (Binding.ContextualFamily.generator M.get j)) =
        spine (rename ρ (τ j)) w' := by
    rw [encode_generator, subst_spine]
    show spine (appendSub w' (fun i => rename ρ (τ i)) (outer j))
      (fun k => appendSub w' (fun i => rename ρ (τ i)) (inner k)) = _
    simp only [appendSub_outer, appendSub_inner]
  rw [target] at beta
  have source : rename ρ (subst τ (homCode names M M (Binding.ContextualFamily.generator M.get) j)) =
      subst (fun i => rename ρ (τ i))
        (abstractN (M.get j).1.length (encode names M (Binding.ContextualFamily.generator M.get j))) :=
    rename_subst _ _ _
  show Conv rules.headEq (spine (rename ρ (τ j)) w)
    (spine (rename ρ (subst τ (homCode names M M (Binding.ContextualFamily.generator M.get) j))) w')
    rules.computation
  rw [source]
  exact .trans _ _ _ (conv_spine (.refl _) arguments) (.symm _ _ beta)

end Agreement

/-! ## Definitions -/

section Definitions

variable {rules : Rules Head} (realization : BindingSignatureEmbedding.Realization names rules)
  (M : List (Binding.MetaArity S)) (i : Fin M.length)
  (t : Binding.Term (Sig S M) (M.get i).1 (M.get i).2)

/-- **The definition** `m(x̄) ≐ t`. -/
def definitionStore : EquationStore (Binding.ContextualFamily.Observation S M.get) :=
  [(occurrence M i, ⟨(M.get i).1, (M.get i).2, t⟩)]

theorem definition_listModels_iff {N : List (Binding.MetaArity S)}
    (f : Binding.ContextualFamily.Assignment (S := S) M.get N.get) :
    (listFrames S).Models (a := M) (b := N) f (definitionStore M i t) ↔
      f i = Binding.ContextualFamily.instantiate f t := by
  have image := Binding.ContextualFamily.instantiate_generator f i
  constructor
  · intro solved
    have equation := solved _ (List.mem_singleton_self _)
    change Binding.ContextualFamily.observe (Binding.ContextualFamily.instantiate f
        (Binding.ContextualFamily.generator M.get i)) =
      Binding.ContextualFamily.observe (Binding.ContextualFamily.instantiate f t) at equation
    rw [image] at equation
    exact Binding.ContextualFamily.observe_injective equation
  · intro same e member
    obtain rfl := List.mem_singleton.mp member
    change Binding.ContextualFamily.observe (Binding.ContextualFamily.instantiate f
        (Binding.ContextualFamily.generator M.get i)) =
      Binding.ContextualFamily.observe (Binding.ContextualFamily.instantiate f t)
    rw [image]
    exact congrArg Binding.ContextualFamily.observe same

/-- **A definition has a principal second-order answer**: the binding `m ↦ t`. -/
theorem definition_principal (absent : i ∉ Binding.ContextualFamily.support t) :
    (listFrames S).Principal (a := M) (m := M) (definitionStore M i t)
      (ContextualBinding.answer i t) where
  sound := (definition_listModels_iff M i t _).mpr
    ((ContextualBinding.answer_same i t).trans
      (ContextualBinding.instantiate_answer_of_absent i t t absent).symm)
  factors := by
    intro N f solved
    have binding := (definition_listModels_iff M i t f).mp solved
    refine ⟨f, fun o => ?_⟩
    show Binding.ContextualFamily.instantiateObservation f o =
      Binding.ContextualFamily.instantiateObservation
        (Binding.ContextualFamily.Assignment.compose f (ContextualBinding.answer i t)) o
    have pointwise : f =
        Binding.ContextualFamily.Assignment.compose f (ContextualBinding.answer i t) :=
      ContextualBinding.candidate_factors i t f binding
    rw [← pointwise]

theorem definition_factors_core {b : Context rules} (τ : b ⟶ ctxOf names realization M)
    (equation : Conv rules.headEq
      (subst τ.substitution (homCode names M M (Binding.ContextualFamily.generator M.get) i))
      (subst τ.substitution (abstractN (M.get i).1.length (encode names M t))) rules.computation) :
    ∀ o : Binding.ContextualFamily.Observation S M.get,
      Dependent.Entry.Convertible ((entry names realization o).reindex τ)
        ((entry names realization o).reindex
          (τ ≫ homOf names realization (ContextualBinding.answer i t))) := by
  intro o
  obtain ⟨Γ, sort, u⟩ := o
  refine ⟨?_, ?_⟩
  · show Conv rules.headEq
      (subst τ.substitution (liftClosed (BindingSignatureEmbedding.bindingType names Γ sort)))
      (subst _ (liftClosed (BindingSignatureEmbedding.bindingType names Γ sort))) rules.computation
    rw [subst_liftClosed, subst_liftClosed]
    exact .refl _
  · show Conv rules.headEq (subst τ.substitution (abstractN Γ.length (encode names M u)))
      (subst (subComp τ.substitution (homCode names M M (ContextualBinding.answer i t)))
        (abstractN Γ.length (encode names M u))) rules.computation
    rw [subst_abstractN, subst_abstractN]
    refine conv_abstractN Γ.length
      (encode_conv_of_appAgree names M u _ _ ⟨fun j => ?_, fun j => ?_⟩)
    · rw [liftN_inner, liftN_inner]
      exact .refl _
    · rw [liftN_outer_rename, liftN_outer_rename]
      apply AppAgree.renamed
      show AppAgree (τ.substitution j)
        (subst τ.substitution (homCode names M M (ContextualBinding.answer i t) j)) _
      by_cases same : j = i
      · subst same
        have bound : homCode (Head := Head) names M M (ContextualBinding.answer j t) j =
            abstractN (M.get j).1.length (encode names M t) := by
          unfold homCode
          rw [ContextualBinding.answer_same]
        rw [bound]
        exact AppAgree.conv_right (appAgree_generator names M τ.substitution j) equation
      · have other : homCode (Head := Head) names M M (ContextualBinding.answer i t) j =
            homCode names M M (Binding.ContextualFamily.generator M.get) j := by
          unfold homCode
          rw [ContextualBinding.answer_other i j same t]
        rw [other]
        exact appAgree_generator names M τ.substitution j

/-- **On translated terms, the translated binding factors every solution of the translated
definition.** -/
theorem definition_factorsOnImage :
    (translation names realization).FactorsOnImage (definitionStore M i t)
      ((translation names realization).hom (ContextualBinding.answer i t)) :=
  fun _ τ solved => ⟨τ, definition_factors_core names realization M i t τ
    (solved _ (List.mem_singleton_self _)).2⟩

/-- **Asks of translated equation guards are preserved and reflected at every definition.** -/
theorem definition_entails_iff (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) (sortInjective : Function.Injective names.sort)
    (operatorInjective : ∀ {s : S.Srt}, Function.Injective (names.operator (sort := s)))
    (absent : i ∉ Binding.ContextualFamily.support t)
    (G : EquationStore (Binding.ContextualFamily.Observation S M.get)) :
    (Dependent.frames rules).Entails ((translation names realization).store (definitionStore M i t))
        (fun _ g => (Dependent.frames rules).Models g ((translation names realization).store G)) ↔
      (listFrames S).Entails (a := M) (definitionStore M i t)
        (fun _ f => (listFrames S).Models f G) :=
  (translation names realization).entails_iff_of_factorsOnImage
    (translation_reflects names realization empty symmetric sortInjective @operatorInjective)
    (definition_principal M i t absent) (definition_factorsOnImage names realization M i t)

/-- Both sides of a definition are solvable. -/
theorem definition_solvable (absent : i ∉ Binding.ContextualFamily.support t) :
    (listFrames S).Solvable (a := M) (definitionStore M i t) ∧
      (Dependent.frames rules).Solvable
        ((translation names realization).store (definitionStore M i t)) :=
  ⟨(definition_principal M i t absent).solvable,
    translation_solvable names realization (definition_principal M i t absent).solvable⟩

end Definitions

end Translation

#print axioms Translation.encode_generator
#print axioms Translation.appAgree_generator
#print axioms Translation.definition_principal
#print axioms Translation.definition_factorsOnImage
#print axioms Translation.definition_entails_iff
#print axioms Translation.definition_solvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
