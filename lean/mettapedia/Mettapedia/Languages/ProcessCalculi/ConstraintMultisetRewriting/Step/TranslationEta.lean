import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationPrincipal
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Functionality

/-!
# Dependent frames with eta keep the second-order principal answer

The dependent frames of `Dependent.frames` compare judged terms by untyped conversion, which has no
eta for products. The tree also has a **typed definitional equality with eta** for dependent
functions and pairs (`TypedEquality`). This module builds the frame instance over it
(`etaFrames`):

* frames are raw telescopes, morphisms are substitutions typed by the typed judgment;
* a judged term is a type at a fixed universe with a term of it;
* the equivalence is typed equality of both components;
* the action is substitution on raw syntax, so the action laws hold on the nose. No quotient and no
  choice of representatives is involved.

**The pattern equation `m(x) ≐ n(x)` has a principal answer here** (`eta_pattern_principal`): the
translation of the second-order principal answer, `m, n ↦ λx. g x`. Its judged terms are the codes
of the translation (`occurrence_code`). Compare `pattern_no_principal`: without eta, no principal
answer exists. Eta is exactly what the dependent frames need for the second-order fibre to keep
its principal answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace Translation
namespace EtaFrames

open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality

variable {Head : Type} (rules : Rules Head) (level : Head)

/-- A frame: a raw telescope. -/
structure Frame (Head : Type) where
  arity : Nat
  raw : Ctx Head arity

/-- A judged term: a type at the fixed universe and a term of it. -/
structure Entry (Γ : Frame Head) where
  type : Tm Head Γ.arity
  formed : Typed rules Γ.raw type (.head level)
  term : Tm Head Γ.arity
  typed : Typed rules Γ.raw term type

/-- A morphism from `Γ` to `Δ`: a typed substitution of `Γ`'s variables by terms over `Δ`. -/
structure Hom (Γ Δ : Frame Head) where
  substitution : Sub Head Γ.arity Δ.arity
  typed : SubstMor rules Γ.raw Δ.raw substitution

variable {rules level}

theorem Entry.ext {Γ : Frame Head} {s t : Entry rules level Γ} (sameType : s.type = t.type)
    (sameTerm : s.term = t.term) : s = t := by
  cases s
  cases t
  cases sameType
  cases sameTerm
  rfl

variable (rules level) in
/-- **Dependent frames with eta.** The equivalence is typed definitional equality, which validates
beta and eta for dependent functions and pairs. -/
def etaFrames (universeIs : rules.isUniverse level) :
    Frames (fun Γ : Frame Head => Entry rules level Γ) (fun Γ Δ => Hom rules Γ Δ) where
  E s t := Equal rules _ s.type t.type (.head level) ∧ Equal rules _ s.term t.term s.type
  equivalence _ :=
    ⟨fun s => ⟨.refl s.formed, .refl s.typed⟩,
      fun same => ⟨.symm same.1, .convEq (.symm same.2) same.1 universeIs⟩,
      fun first second => ⟨.trans first.1 second.1,
        .trans first.2 (.convEq second.2 (.symm first.1) universeIs)⟩⟩
  act σ t := ⟨subst σ.substitution t.type, t.formed.substitute σ.typed,
    subst σ.substitution t.term, t.typed.substitute σ.typed⟩
  id Γ := ⟨ids, fun i => by
    rw [subst_ids]
    exact Derivable.var i⟩
  comp g f := ⟨subComp g.substitution f.substitution, fun i => by
    have typed := (f.typed i).substitute g.typed
    rw [subst_subComp] at typed
    exact typed⟩
  act_id t := Entry.ext (subst_ids _) (subst_ids _)
  act_comp g f t := Entry.ext (subst_subComp _ _ _).symm (subst_subComp _ _ _).symm
  preserves := fun {_ _} σ {_ _} same =>
    And.intro (same.1.substitute σ.typed) (same.2.substitute σ.typed)

/-- Substitutions that are pointwise equal act equally on every judged term. -/
theorem act_equal_of_substEq (universeIs : rules.isUniverse level) {Γ Δ : Frame Head}
    {σ τ : Hom rules Γ Δ} (equal : SubstEq rules Γ.raw Δ.raw σ.substitution τ.substitution)
    (t : Entry rules level Γ) :
    (etaFrames rules level universeIs).E ((etaFrames rules level universeIs).act σ t)
      ((etaFrames rules level universeIs).act τ t) :=
  And.intro (t.formed.functional equal) (t.typed.functional equal)

/-! ## The pattern equation with eta -/

variable {S : Binding.Signature} (names : BindingSignatureEmbedding.Names S)
  (realization : BindingSignatureEmbedding.Realization names rules) (s : S.Srt)

/-- The closed type `Π s. s` of a unary metavariable. -/
abbrev arrow : Tm Head 0 := unaryType names s

theorem sort_typed {n : Nat} (Γ : Ctx Head n) :
    Typed rules Γ (BindingSignatureEmbedding.sortType names s) (.head realization.typeUniverse) :=
  Derivable.const (realization.sortLookup s) (Derivable.headType realization.universeTyped)
    realization.aboveIs

theorem arrow_typed {n : Nat} (Γ : Ctx Head n) :
    Typed rules Γ (liftClosed (arrow names s)) (.head realization.typeUniverse) := by
  change Typed rules Γ (liftClosed (BindingSignatureEmbedding.closedArrow
    (BindingSignatureEmbedding.sortType names s) (BindingSignatureEmbedding.sortType names s)))
    (.head realization.typeUniverse)
  rw [BindingSignatureEmbedding.liftClosed_closedArrow]
  exact Derivable.cumul (.piForm (sort_typed names realization s Γ) realization.universeIs
    (sort_typed names realization s _) realization.universeIs realization.joinSelf)
    realization.collapseSelf

/-- The body `u x` of an eta expansion, in the extended telescope. -/
theorem body_typed {n : Nat} {Γ : Ctx Head n} {u : Tm Head n}
    (typed : Typed rules Γ u (liftClosed (arrow names s))) :
    Typed rules (.snoc Γ (BindingSignatureEmbedding.sortType names s)) (.app (rename wk u) (.var 0))
      (BindingSignatureEmbedding.sortType names s) := by
  have weakened := typed.weaken (extension := BindingSignatureEmbedding.sortType names s)
  change Typed rules _ (rename wk u) (rename wk (liftClosed (BindingSignatureEmbedding.closedArrow
    (BindingSignatureEmbedding.sortType names s) (BindingSignatureEmbedding.sortType names s))))
    at weakened
  rw [BindingSignatureEmbedding.liftClosed_closedArrow] at weakened
  exact Derivable.appElim weakened (Derivable.var 0)

include realization in
/-- An eta expansion of a term of `Π s. s` has type `Π s. s`. -/
theorem eta_typed {n : Nat} {Γ : Ctx Head n} {u : Tm Head n}
    (typed : Typed rules Γ u (liftClosed (arrow names s))) :
    Typed rules Γ (etaOf u) (liftClosed (arrow names s)) := by
  have formed := arrow_typed names realization s Γ
  change Typed rules Γ (liftClosed (BindingSignatureEmbedding.closedArrow
    (BindingSignatureEmbedding.sortType names s) (BindingSignatureEmbedding.sortType names s)))
    (.head realization.typeUniverse) at formed
  change Typed rules Γ (etaOf u) (liftClosed (BindingSignatureEmbedding.closedArrow
    (BindingSignatureEmbedding.sortType names s) (BindingSignatureEmbedding.sortType names s)))
  rw [BindingSignatureEmbedding.liftClosed_closedArrow] at formed ⊢
  exact Derivable.lamIntro formed realization.universeIs (body_typed names s typed)

include realization in
/-- **Eta**: a term of `Π s. s` equals its eta expansion. -/
theorem eta_equal {n : Nat} {Γ : Ctx Head n} {u : Tm Head n}
    (typed : Typed rules Γ u (liftClosed (arrow names s))) :
    Equal rules Γ u (etaOf u) (liftClosed (arrow names s)) := by
  have expanded := eta_typed names realization s typed
  have weakTyped : Typed rules (.snoc Γ (BindingSignatureEmbedding.sortType names s)) (rename wk u)
      (liftClosed (arrow names s)) := by
    have weakened := typed.weaken (extension := BindingSignatureEmbedding.sortType names s)
    rw [rename_liftClosed] at weakened
    exact weakened
  have comm : rename (liftRen wk) (rename wk u) = rename wk (rename wk u) := by
    rw [rename_comp, rename_comp]
    rfl
  have bodyTyped : Typed rules (.snoc (.snoc Γ (BindingSignatureEmbedding.sortType names s))
      (BindingSignatureEmbedding.sortType names s))
      (.app (rename (liftRen wk) (rename wk u)) (.var 0))
      (BindingSignatureEmbedding.sortType names s) := by
    rw [comm]
    exact body_typed names s weakTyped
  have weakFormed := (arrow_typed names realization s (.snoc Γ
    (BindingSignatureEmbedding.sortType names s)))
  change Typed rules _ (liftClosed (BindingSignatureEmbedding.closedArrow
    (BindingSignatureEmbedding.sortType names s) (BindingSignatureEmbedding.sortType names s)))
    (.head realization.typeUniverse) at weakFormed
  rw [BindingSignatureEmbedding.liftClosed_closedArrow] at weakFormed
  have reduce := Derivable.betaPi weakFormed realization.universeIs bodyTyped (Derivable.var 0)
  have collapsed : inst0 (.var 0 : Tm Head (n + 1))
      (Tm.app (rename (liftRen wk) (rename wk u)) (.var 0)) = .app (rename wk u) (.var 0) := by
    show Tm.app (inst0 (.var 0) (rename (liftRen wk) (rename wk u))) (.var 0) = _
    rw [comm, inst0_rename_wk]
  rw [collapsed] at reduce
  change Typed rules Γ u (liftClosed (BindingSignatureEmbedding.closedArrow
    (BindingSignatureEmbedding.sortType names s) (BindingSignatureEmbedding.sortType names s)))
    at typed
  change Typed rules Γ (etaOf u) (liftClosed (BindingSignatureEmbedding.closedArrow
    (BindingSignatureEmbedding.sortType names s) (BindingSignatureEmbedding.sortType names s)))
    at expanded
  change Equal rules Γ u (etaOf u) (liftClosed (BindingSignatureEmbedding.closedArrow
    (BindingSignatureEmbedding.sortType names s) (BindingSignatureEmbedding.sortType names s)))
  rw [BindingSignatureEmbedding.liftClosed_closedArrow] at typed expanded ⊢
  exact .etaPi typed expanded (.symm reduce)

theorem pairFrame_get (i : Fin (pairFrame s).length) : (pairFrame s).get i = ([s], s) := by
  rcases i with ⟨_ | _ | k, bound⟩
  · rfl
  · rfl
  · exact absurd bound (by simp)

theorem unaryFrame_get (i : Fin (unaryFrame s).length) : (unaryFrame s).get i = ([s], s) := by
  rcases i with ⟨_ | k, bound⟩
  · rfl
  · exact absurd bound (by simp)

/-- The two-metavariable telescope `m, n : Π s. s`. -/
abbrev pairEta : Frame Head := ⟨_, metaCtx names (pairFrame s)⟩

/-- The one-metavariable telescope `g : Π s. s`. -/
abbrev unaryEta : Frame Head := ⟨_, metaCtx names (unaryFrame s)⟩

/-- The judged term `λx. m x : Π s. s`, the translation of the occurrence `m(x)`. -/
def occurrenceEta (i : Fin (pairFrame s).length) :
    Entry rules realization.typeUniverse (pairEta names s) :=
  ⟨liftClosed (arrow names s), arrow_typed names realization s _, etaOf (.var i),
    eta_typed names realization s (by
      have typed := Derivable.var (R := rules) (Γ := metaCtx (Head := Head) names (pairFrame s)) i
      rw [metaCtx_lookup, pairFrame_get] at typed
      exact typed)⟩

/-- These judged terms carry exactly the codes of the translation. -/
theorem occurrence_code :
    (occurrenceEta names realization s (mIdx s)).term =
        (entry names realization (occurrence (pairFrame s) (mIdx s))).term.code ∧
      (occurrenceEta names realization s (nIdx s)).term =
        (entry names realization (occurrence (pairFrame s) (nIdx s))).term.code :=
  ⟨rfl, rfl⟩

/-- The pattern equation `λx. m x ≐ λx. n x` at the eta frames. -/
def patternEta : EquationStore (Entry rules realization.typeUniverse (pairEta names s)) :=
  [(occurrenceEta names realization s (mIdx s), occurrenceEta names realization s (nIdx s))]

/-- The translated principal answer `m, n ↦ λx. g x`. -/
def answerEta : Hom rules (pairEta names s) (unaryEta names s) where
  substitution := consSub (etaOf (.var 0)) (consSub (etaOf (.var 0)) (fun k => k.elim0))
  typed := by
    have component : Typed rules (metaCtx names (unaryFrame s)) (etaOf (.var 0))
        (liftClosed (arrow names s)) := by
      refine eta_typed names realization s ?_
      have typed := Derivable.var (R := rules) (Γ := metaCtx (Head := Head) names (unaryFrame s)) 0
      rw [metaCtx_lookup] at typed
      exact typed
    intro (i : Fin (pairFrame s).length)
    show Typed rules (metaCtx names (unaryFrame s)) _
      (subst _ (Ctx.lookup (metaCtx names (pairFrame s)) i))
    rw [metaCtx_lookup, subst_liftClosed]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact component
    · refine Fin.cases ?_ (fun k => k.elim0) j
      exact component

/-- **With eta, the pattern equation has a principal answer**: the translation of the second-order
principal answer. -/
theorem eta_pattern_principal :
    (etaFrames rules realization.typeUniverse realization.universeIs).Principal
      (a := pairEta names s) (m := unaryEta names s) (patternEta names realization s)
      (answerEta names realization s) where
  sound := by
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact And.intro (.refl ((occurrenceEta names realization s (mIdx s)).formed.substitute
        (answerEta names realization s).typed))
      (.refl ((occurrenceEta names realization s (mIdx s)).typed.substitute
        (answerEta names realization s).typed))
  factors := by
    intro b τ solved
    have equation := (solved _ (List.mem_singleton_self _)).2
    have typedAt : ∀ i : Fin (pairFrame s).length,
        Typed rules b.raw (τ.substitution i) (liftClosed (arrow names s)) := by
      intro i
      have typed := τ.typed i
      change Typed rules b.raw (τ.substitution i)
        (subst τ.substitution (Ctx.lookup (metaCtx names (pairFrame s)) i)) at typed
      rw [metaCtx_lookup, subst_liftClosed, pairFrame_get] at typed
      exact typed
    let residual : Hom rules (unaryEta names s) b :=
      ⟨consSub (τ.substitution (mIdx s)) (fun k => k.elim0), by
        intro (i : Fin (unaryFrame s).length)
        show Typed rules b.raw _ (subst _ (Ctx.lookup (metaCtx names (unaryFrame s)) i))
        rw [metaCtx_lookup, subst_liftClosed]
        refine Fin.cases ?_ (fun k => k.elim0) i
        exact typedAt (mIdx s)⟩
    refine ⟨residual, act_equal_of_substEq realization.universeIs ⟨τ.typed, fun i => ?_⟩⟩
    change Equal rules b.raw (etaOf (τ.substitution (mIdx s))) (etaOf (τ.substitution (nIdx s)))
      (subst τ.substitution (liftClosed (arrow names s))) at equation
    rw [subst_liftClosed] at equation
    rcases i with ⟨_ | _ | k, bound⟩
    · change Equal rules b.raw (τ.substitution (mIdx s)) (etaOf (τ.substitution (mIdx s)))
        (subst τ.substitution (Ctx.lookup (metaCtx names (pairFrame s)) (mIdx s)))
      rw [metaCtx_lookup, subst_liftClosed]
      exact eta_equal names realization s (typedAt (mIdx s))
    · change Equal rules b.raw (τ.substitution (nIdx s)) (etaOf (τ.substitution (mIdx s)))
        (subst τ.substitution (Ctx.lookup (metaCtx names (pairFrame s)) (nIdx s)))
      rw [metaCtx_lookup, subst_liftClosed]
      exact .trans (eta_equal names realization s (typedAt (nIdx s))) (.symm equation)
    · exact absurd bound (by simp)

end EtaFrames
end Translation

#print axioms Translation.EtaFrames.etaFrames
#print axioms Translation.EtaFrames.eta_equal
#print axioms Translation.EtaFrames.eta_pattern_principal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
