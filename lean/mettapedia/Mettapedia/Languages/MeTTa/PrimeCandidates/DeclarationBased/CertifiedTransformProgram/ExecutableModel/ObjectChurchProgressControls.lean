import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchProgress

/-!
# Controls for progress of the object package's annotated types

**Positive.**

* **A type that steps.** The decoding redex `holds (p ⇒ q)` at two code variables is a type of
  the universe of proofs that is not in weak-head form; progress yields its weak-head step
  (`decodeRedex_steps`).
* **Types in weak-head form.** The numbers, a type constant of an inductive type, and the decoder
  stuck on a code variable, a neutral type, take no step; progress yields their weak-head
  forms (`num_typeForm`, `stuckDecode_typeForm`).
* **The outcomes exclude each other.** The stuck decoder has a weak-head normal shape
  (`stuckDecode_whnfShape`); the decoding redex has none (`decodeRedex_not_whnfShape`).

**Negative.**

* **The typing premise is necessary.** `zero zero` takes no step and its erasure is not in
  weak-head form as a type (`zeroZero_not_progress`); so it is typed at no universe
  (`zeroZero_untyped`). Likewise the partial application `add zero`, a weak-head normal form
  that is no type (`addZero_not_progress`, `addZero_untyped`).
* **A type is needed, not a typed term.** Reflexivity at zero is typed, at an identity type,
  and neither steps nor is in weak-head form as a type (`reflZero_typed`,
  `reflZero_not_progress`).
* **Canonical forms tell the numbers from the codes.** Zero is typed at the numbers
  (`zero_typed_num`) and not at the codes (`zero_not_typed_prop`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated

namespace CodeModel

namespace ProgressControls

open Progress

/-! ## Types in weak-head form take no step -/

/-- A type in weak-head form is a weak-head normal form of the object package. -/
theorem typeForm_whnf {n : Nat} {t : Tower.Tm n} (form : IsTypeForm objectRoles t) :
    Whnf objectRules objectRoles t := by
  rcases form with ⟨h, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, a, b, rfl⟩ | neutral |
    ⟨T, cs, role, rfl⟩
  · exact head_whnf objectShape h
  · exact pi_whnf objectShape A B
  · exact sigma_whnf objectShape A B
  · exact id_whnf objectShape A a b
  · exact neutral.whnf objectShape
  · exact inductive_whnf objectShape role

/-- An annotated term whose erasure is a type in weak-head form takes no weak-head step. -/
theorem typeForm_no_step {n : Nat} {t : CTm Tower.Head n} (form : IsTypeForm objectRoles t.erase)
    (t' : CTm Tower.Head n) : ¬ CWhStepR objectChurch objectRoles t t' :=
  CWhStepR.not_of_whnf (typeForm_whnf form) t'

/-- The codes form a type, in every context. -/
theorem prop_isType {n : Nat} {Γ : CCtx Tower.Head n} : CIsType objectChurch Γ (.const propN) :=
  ⟨_, .sort _, const_U0_typed (c := propN) (by decide)⟩

/-! ## Positive: a type that steps -/

/-- Two code variables. -/
abbrev codeCtx : CCtx Tower.Head 2 := .snoc (.snoc .nil (.const propN)) (.const propN)

theorem codeCtx_formed : CCtxFormed objectChurch codeCtx :=
  .snoc (.snoc .nil prop_isType) prop_isType

/-- The implication of the two code variables, `p ⇒ q`. -/
abbrev impVars : CTm Tower.Head 2 := .app (.app (.const impN) (.var 1)) (.var 0)

/-- The decoding redex `holds (p ⇒ q)`. -/
abbrev decodeRedex : CTm Tower.Head 2 := .app (.const holdsN) impVars

theorem impVars_typed : CTyped objectChurch codeCtx impVars (.const propN) := by
  have partial₁ : CTyped objectChurch codeCtx (.app (.const impN) (.var 1))
      (.pi (.const propN) (.const propN)) :=
    .appElim cimp_typed (.var 1)
  exact .appElim partial₁ (.var 0)

/-- The decoding redex is a type of the universe of proofs. -/
theorem decodeRedex_typed :
    CTyped objectChurch codeCtx decodeRedex (.head (.sort Tower.zero)) :=
  holds_app_typed impVars_typed

/-- The decoding redex is not in weak-head form: it is a root redex. -/
theorem decodeRedex_not_typeForm : ¬ IsTypeForm objectRoles decodeRedex.erase := by
  intro form
  obtain ⟨r, step⟩ := holds_step_imp (.var 1 : CTm Tower.Head 2) (.var 0)
  exact typeForm_no_step form r (.root step)

/-- **Positive**: progress yields the weak-head step of the decoding redex. -/
theorem decodeRedex_steps : ∃ A', CWhStepR objectChurch objectRoles decodeRedex A' :=
  (objectChurch_typeProgress codeCtx_formed (.sort _) decodeRedex_typed).resolve_right
    decodeRedex_not_typeForm

/-- The two outcomes of progress exclude each other: the decoding redex, which steps, has no
weak-head normal shape. -/
theorem decodeRedex_not_whnfShape : ¬ WhnfShape decodeRedex := by
  intro shape
  obtain ⟨r, step⟩ := holds_step_imp (.var 1 : CTm Tower.Head 2) (.var 0)
  exact shape.no_step r (.root step)

/-! ## Positive: types in weak-head form -/

theorem num_typed :
    CTyped objectChurch (.nil : CCtx Tower.Head 0) (.const numN) (.head (.sort Tower.zero)) :=
  const_U0_typed (by decide)

/-- **Positive**: progress yields the weak-head form of the numbers, which take no step. -/
theorem num_typeForm : IsTypeForm objectRoles (CTm.const numN : CTm Tower.Head 0).erase :=
  (objectChurch_typeProgress .nil (.sort _) num_typed).resolve_left fun ⟨A', step⟩ =>
    CWhStepR.not_of_whnf (inductive_whnf objectShape objectRoles_num) A' step

/-- One code variable. -/
abbrev codeVarCtx : CCtx Tower.Head 1 := .snoc .nil (.const propN)

/-- The decoder at a code variable, stuck. -/
abbrev stuckDecode : CTm Tower.Head 1 := .app (.const holdsN) (.var 0)

theorem stuckDecode_typed :
    CTyped objectChurch codeVarCtx stuckDecode (.head (.sort Tower.zero)) :=
  holds_app_typed (.var 0)

/-- The decoder at a code variable is neutral: stuck on its scrutinee. -/
theorem stuckDecode_neutral : Neutral objectRoles stuckDecode.erase :=
  Neutral.stuck_single (before := []) (after := []) objectRoles_holds rfl (.var 0)

/-- The stuck decoder has a weak-head normal shape. -/
theorem stuckDecode_whnfShape : WhnfShape stuckDecode := .neutral stuckDecode_neutral

/-- **Positive**: progress yields the weak-head form of the stuck decoder, a neutral type,
which takes no step. -/
theorem stuckDecode_typeForm : IsTypeForm objectRoles stuckDecode.erase :=
  (objectChurch_typeProgress (.snoc .nil prop_isType) (.sort _) stuckDecode_typed).resolve_left
    fun ⟨A', step⟩ => CWhStepR.not_of_whnf (stuckDecode_neutral.whnf objectShape) A' step

/-! ## Negative: the typing premise is necessary -/

/-- Zero applied to zero. -/
abbrev zeroZero : CTm Tower.Head 0 := .app (.const zeroN) (.const zeroN)

/-- **Negative**: `zero zero` neither takes a step nor is in weak-head form as a type. -/
theorem zeroZero_not_progress :
    ¬ ((∃ A', CWhStepR objectChurch objectRoles zeroZero A') ∨
      IsTypeForm objectRoles zeroZero.erase) := by
  rintro (⟨A', step⟩ | form)
  · exact CWhStepR.not_of_whnf (constSpine_whnf objectShape (c := zeroN)
      (fun _ _ h => nomatch objectRoles_zero.symm.trans h) [.const zeroN]) A' step
  · rcases form with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | neutral |
      ⟨_, _, _, e⟩
    · cases e
    · cases e
    · cases e
    · cases e
    · exact neutral.not_canonical (.inr ⟨zeroN, 0, [.const zeroN], objectRoles_zero, rfl⟩)
    · cases e

/-- So `zero zero` is typed at no universe: without the typing premise, progress fails. -/
theorem zeroZero_untyped {u : Tower.Head} (hu : objectRules.isUniverse u) :
    ¬ CTyped objectChurch .nil zeroZero (.head u) :=
  fun typing => zeroZero_not_progress (objectChurch_typeProgress .nil hu typing)

/-- Addition applied to zero only. -/
abbrev addZero : CTm Tower.Head 0 := .app (.const addN) (.const zeroN)

/-- **Negative**: `add zero`, a computing constant below its arity, neither takes a step nor is
in weak-head form as a type. -/
theorem addZero_not_progress :
    ¬ ((∃ A', CWhStepR objectChurch objectRoles addZero A') ∨
      IsTypeForm objectRoles addZero.erase) := by
  rintro (⟨A', step⟩ | form)
  · exact CWhStepR.not_of_whnf (partialSpine_whnf objectShape objectRoles_add
      (args := [.const zeroN]) (by decide)) A' step
  · rcases form with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | neutral |
      ⟨_, _, _, e⟩
    · cases e
    · cases e
    · cases e
    · cases e
    · rcases neutral.constSpine (c := addN) (args := [.const zeroN]) rfl with rigid |
        ⟨arity, _, pre, post, _, _, computes, split, length, _⟩
      · rw [objectRoles_add] at rigid; cases rigid
      · rw [objectRoles_add] at computes
        cases computes
        have lengths := congrArg List.length split
        rw [List.length_append, length] at lengths
        have one : 1 = 2 + post.length := lengths
        omega
    · cases e

/-- So `add zero` is typed at no universe. -/
theorem addZero_untyped {u : Tower.Head} (hu : objectRules.isUniverse u) :
    ¬ CTyped objectChurch .nil addZero (.head u) :=
  fun typing => addZero_not_progress (objectChurch_typeProgress .nil hu typing)

/-! ## Negative: a type is needed, not a typed term -/

/-- Zero is a number. -/
theorem zero_typed_num {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectChurch Γ (.const zeroN) (.const numN) :=
  const_typed (T := Package.numT) (by decide) rfl (const_U0_typed (by decide)) (.sort _)

/-- Reflexivity at zero. -/
abbrev reflZero : CTm Tower.Head 0 := .refl (.const zeroN)

theorem reflZero_typed :
    CTyped objectChurch .nil reflZero (.id (.const numN) (.const zeroN) (.const zeroN)) :=
  .reflIntro zero_typed_num

/-- **Negative**: reflexivity at zero, a typed term whose type is no universe, neither takes a
step nor is in weak-head form as a type. -/
theorem reflZero_not_progress :
    ¬ ((∃ A', CWhStepR objectChurch objectRoles reflZero A') ∨
      IsTypeForm objectRoles reflZero.erase) := by
  rintro (⟨A', step⟩ | form)
  · exact CWhStepR.not_of_whnf (refl_whnf objectShape _) A' step
  · rcases form with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | neutral |
      ⟨_, _, _, e⟩
    · cases e
    · cases e
    · cases e
    · cases e
    · exact neutral.ne_refl rfl
    · cases e

/-! ## Negative: canonical forms tell the numbers from the codes -/

/-- **Negative**: zero is not a code. -/
theorem zero_not_typed_prop :
    ¬ CTyped objectChurch (.nil : CCtx Tower.Head 0) (.const zeroN) (.const propN) := by
  intro typing
  rcases canonical_at .nil (whnfShape_const zeroN) typing (kind := .prop) rfl with neutral | fits
  · exact neutral.not_canonical (.inr ⟨zeroN, 0, [], objectRoles_zero, rfl⟩)
  · rcases fits with ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ <;> cases e

end ProgressControls

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
