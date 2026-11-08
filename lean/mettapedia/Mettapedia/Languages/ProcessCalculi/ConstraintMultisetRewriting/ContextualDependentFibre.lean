import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongReflection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaBridge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Constants

/-!
# The second-order step as the η-long fibre: translated terms are η-long

The raising translation of second-order frames (`Translation.translation`) lands in the
raw-conversion dependent frames; the comparison of the Codex lane (`BetaBridge`) carries those to
the typed βη frame of the dependent unifier. Their composite is a map of frame instances from the
second-order step into the unifier's frame (`fibre`).

Every judged term in the image of the translation is an η-long β-normal form at its type, and so
is every type code (`entry_long`, `type_long`):

* a metavariable of arity `(Γ, s)` has the closed type `Π Γ. s` over sort constants;
* an object variable is neutral at its sort;
* a metavariable occurrence is the metavariable applied to normal arguments at sorts;
* an operator application is the rigid operator constant applied to abstractions, each normal at
  the binding type of its argument.

No universe or ground head occurs in a translation (`entry_headFree`, `type_headFree`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFibre

open CategoryTheory Interface Interface.Translation
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong

universe uO uT uH uO' uT' uH' uO'' uT'' uH''

/-! ## Composing maps of frame instances -/

/-- The composite of two maps of frame instances. -/
def FrameMap.comp {Obj : Type uO} {Tm₁ : Obj → Type uT} {Hom₁ : Obj → Obj → Type uH}
    {Obj' : Type uO'} {Tm₂ : Obj' → Type uT'} {Hom₂ : Obj' → Obj' → Type uH'}
    {Obj'' : Type uO''} {Tm₃ : Obj'' → Type uT''} {Hom₃ : Obj'' → Obj'' → Type uH''}
    {X : Frames Tm₁ Hom₁} {Y : Frames Tm₂ Hom₂} {Z : Frames Tm₃ Hom₃}
    (Φ : Translation.FrameMap X Y) (Ψ : Translation.FrameMap Y Z) : Translation.FrameMap X Z where
  obj a := Ψ.obj (Φ.obj a)
  tm t := Ψ.tm (Φ.tm t)
  hom f := Ψ.hom (Φ.hom f)
  act f t := (Z.equivalence _).trans (Ψ.preserves (Φ.act f t)) (Ψ.act (Φ.hom f) (Φ.tm t))
  preserves same := Ψ.preserves (Φ.preserves same)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

section Maps

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (church : ConversionCoherence.ChurchRosser S.R)

/-- The comparison of the Codex lane as a map of frame instances: codes are kept, typing
certificates are reconstructed. -/
def bridge :
    Translation.FrameMap (Interface.Dependent.frames S.R) (ContextualDependentEta.frames S.levels) where
  obj := ContextualDependentEta.BetaBridge.context facts roots heads church
  tm := ContextualDependentEta.BetaBridge.entry facts roots heads church
  hom := ContextualDependentEta.BetaBridge.hom facts roots heads church
  act _ _ :=
    ((ContextualDependentEta.frames S.levels).equivalence _).refl _
  preserves := ContextualDependentEta.BetaBridge.preserves facts roots heads church

variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)

/-- **The second-order step inside the unifier's typed βη frame.** -/
def fibre :
    Translation.FrameMap (listFrames sig) (ContextualDependentEta.frames S.levels) :=
  FrameMap.comp (translation names realization) (bridge facts roots heads church)

theorem fibre_obj_raw (M : List (Binding.MetaArity sig)) :
    ((fibre facts roots heads church names realization).obj M).raw = metaCtx names M := rfl

theorem fibre_tm_type {M : List (Binding.MetaArity sig)}
    (o : Binding.ContextualFamily.Observation sig M.get) :
    ((fibre facts roots heads church names realization).tm o).1.code =
      liftClosed (BindingSignatureEmbedding.bindingType names o.1 o.2.1) := rfl

theorem fibre_tm_term {M : List (Binding.MetaArity sig)}
    (o : Binding.ContextualFamily.Observation sig M.get) :
    ((fibre facts roots heads church names realization).tm o).2.code =
      abstractN o.1.length (encode names M o.2.2) := rfl

theorem fibre_hom_substitution {M N : List (Binding.MetaArity sig)}
    (σa : Binding.ContextualFamily.Assignment (S := sig) M.get N.get) :
    ((fibre facts roots heads church names realization).hom σa).substitution =
      homCode names M N σa := rfl

end Maps

/-! ## Closed types of the translation -/

section ClosedTypes

variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)

theorem sort_typed {n : Nat} (Γ : Ctx Head n) (s : sig.Srt) :
    Typed S.R Γ (BindingSignatureEmbedding.sortType names s) (.head realization.typeUniverse) :=
  Derivable.const (realization.sortLookup s) (.headType realization.universeTyped)
    realization.aboveIs

theorem closedArrow_typed {d r : Tm Head 0}
    (td : Typed S.R .nil d (.head realization.typeUniverse))
    (tr : Typed S.R .nil r (.head realization.typeUniverse)) :
    Typed S.R .nil (BindingSignatureEmbedding.closedArrow d r) (.head realization.typeUniverse) :=
  .cumul (.piForm td realization.universeIs (Normalization.Typed.liftClosed tr) realization.universeIs
    realization.joinSelf) realization.collapseSelf

theorem telescope_typed : ∀ (bound : List sig.Srt) {result : Tm Head 0},
    Typed S.R .nil result (.head realization.typeUniverse) →
    Typed S.R .nil (BindingSignatureEmbedding.telescopeType names bound result)
      (.head realization.typeUniverse)
  | [], _, typed => typed
  | s :: bound, _, typed =>
      telescope_typed bound (closedArrow_typed names realization (sort_typed names realization .nil s) typed)

theorem bindingType_typed (bound : List sig.Srt) (s : sig.Srt) :
    Typed S.R .nil (BindingSignatureEmbedding.bindingType names bound s)
      (.head realization.typeUniverse) :=
  telescope_typed names realization bound (sort_typed names realization .nil s)

theorem argumentsType_typed : ∀ (as : List (List sig.Srt × sig.Srt)) {result : Tm Head 0},
    Typed S.R .nil result (.head realization.typeUniverse) →
    Typed S.R .nil (BindingSignatureEmbedding.argumentsType names as result)
      (.head realization.typeUniverse)
  | [], _, typed => typed
  | (bound, s) :: as, _, typed =>
      closedArrow_typed names realization (bindingType_typed names realization bound s)
        (argumentsType_typed as typed)

theorem lifted_isType {n : Nat} (Γ : Ctx Head n) {T : Tm Head 0}
    (typed : Typed S.R .nil T (.head realization.typeUniverse)) :
    IsType S.R Γ (liftClosed T) :=
  ⟨_, realization.universeIs, Normalization.Typed.liftClosed typed⟩

end ClosedTypes

/-! ## Translations are η-long -/

section Long

variable (facts : FormFacts S.R S.roles) (rigid : ∀ name, S.roles name = .rigid)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)

include facts rigid in
/-- A sort is not equal to a dependent function or pair type. -/
theorem sort_base {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (s : sig.Srt) :
    Base S.R Γ (BindingSignatureEmbedding.sortType names s) := by
  have neutral : Neutral S.roles (BindingSignatureEmbedding.sortType names s : Tm Head n) :=
    Neutral.rigid (c := names.sort s) [] (rigid _)
  exact ⟨fun A B e => (TypeEq.neutral_form facts e formed neutral
      (.inr (.inl ⟨A, B, rfl⟩))).not_former.2.1 A B rfl,
    fun A B e => (TypeEq.neutral_form facts e formed neutral
      (.inr (.inr (.inl ⟨A, B, rfl⟩)))).not_former.2.2.1 A B rfl⟩

include facts rigid realization in
/-- A neutral term at a sort is η-long there. -/
theorem long_at_sort {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t : Tm Head n}
    {s : sig.Srt}
    (spine : Long S.R S.roles (.spine Γ t (BindingSignatureEmbedding.sortType names s))) :
    Long S.R S.roles (.term Γ t (BindingSignatureEmbedding.sortType names s)) :=
  .neutral spine (IsType.below_refl ⟨_, realization.universeIs, sort_typed names realization Γ s⟩)
    spine.spine_typed (sort_base facts rigid names formed s)

/-- Applying a head to normal arguments, first argument first. -/
theorem long_applyVec {n : Nat} {Γ : Ctx Head n} (result : Tm Head 0)
    (tResult : Typed S.R .nil result (.head realization.typeUniverse)) :
    ∀ (as : List (List sig.Srt × sig.Srt)) {f : Tm Head n} {w : Sub Head as.length n},
      Long S.R S.roles (.spine Γ f (liftClosed (BindingSignatureEmbedding.argumentsType names as result))) →
      (∀ j : Fin as.length, Long S.R S.roles (.term Γ (w j)
        (liftClosed (BindingSignatureEmbedding.bindingType names (as.get j).1 (as.get j).2)))) →
      Long S.R S.roles (.spine Γ (applyVec f w) (liftClosed result))
  | [], _, _, lf, _ => lf
  | (bound, s) :: as, f, w, lf, args => by
      have tRest := argumentsType_typed names realization as tResult
      have tArrow := closedArrow_typed names realization (bindingType_typed names realization bound s) tRest
      have isArrow := lifted_isType names realization Γ tArrow
      have lf' : Long S.R S.roles (.spine Γ f (liftClosed (BindingSignatureEmbedding.closedArrow
          (BindingSignatureEmbedding.bindingType names bound s)
          (BindingSignatureEmbedding.argumentsType names as result)))) := lf
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at lf' isArrow
      have applied : Long S.R S.roles (.spine Γ (.app f (w 0))
          (liftClosed (BindingSignatureEmbedding.argumentsType names as result))) := by
        refine .app lf' (IsType.refl isArrow) (args 0) ?_
        rw [inst0, subst_liftClosed]
        exact IsType.refl (lifted_isType names realization Γ tRest)
      exact long_applyVec result tResult as applied (fun j => args j.succ)

/-- Applying a metavariable to normal arguments at sorts, last argument first. -/
theorem long_spine {n : Nat} {Γ : Ctx Head n} :
    ∀ (P : List sig.Srt) {result : Tm Head 0},
      Typed S.R .nil result (.head realization.typeUniverse) →
      ∀ {f : Tm Head n} {w : Sub Head P.length n},
      Long S.R S.roles (.spine Γ f (liftClosed (BindingSignatureEmbedding.telescopeType names P result))) →
      (∀ j : Fin P.length,
        Long S.R S.roles (.term Γ (w j) (BindingSignatureEmbedding.sortType names (P.get j)))) →
      Long S.R S.roles (.spine Γ (spine f w) (liftClosed result))
  | [], _, _, _, _, lf, _ => lf
  | p :: P, result, tResult, f, w, lf, args => by
      have tArrow := closedArrow_typed names realization (sort_typed names realization .nil p) tResult
      have earlier := long_spine P tArrow (w := fun j => w j.succ) lf (fun j => args j.succ)
      have isArrow := lifted_isType names realization Γ tArrow
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at earlier isArrow
      refine .app earlier (IsType.refl isArrow) (args 0) ?_
      rw [inst0, subst_liftClosed]
      exact IsType.refl (lifted_isType names realization Γ tResult)

/-- Closing the binders of one operator argument. -/
theorem long_abstractB {k : Nat} {c : Ctx Head k} {Γ : Binding.Ctx sig} :
    ∀ (bound : List sig.Srt) {result : Tm Head 0},
      Typed S.R .nil result (.head realization.typeUniverse) →
      ∀ (body : Tm Head (k + (bound ++ Γ).length)),
        Long S.R S.roles (.term (extendCtx names c (bound ++ Γ)) body (liftClosed result)) →
        Long S.R S.roles (.term (extendCtx names c Γ) (abstractB bound body)
          (liftClosed (BindingSignatureEmbedding.telescopeType names bound result)))
  | [], _, _, _, long => long
  | s :: bound, result, tResult, body, long => by
      have tArrow := closedArrow_typed names realization (sort_typed names realization .nil s) tResult
      have isArrow := lifted_isType names realization (extendCtx names c (bound ++ Γ)) tArrow
      have tLifted := Normalization.Typed.liftClosed (Δ := extendCtx names c (bound ++ Γ)) tArrow
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at isArrow tLifted
      have lamLong : Long S.R S.roles (.term (extendCtx names c (bound ++ Γ)) (.lam body)
          (liftClosed (BindingSignatureEmbedding.closedArrow
            (BindingSignatureEmbedding.sortType names s) result))) := by
        rw [BindingSignatureEmbedding.liftClosed_closedArrow]
        exact .lam (IsType.refl isArrow) ⟨_, realization.universeIs, sort_typed names realization _ s⟩
          (.lamIntro tLifted realization.universeIs long.typed) long
      exact long_abstractB bound tArrow (.lam body) lamLong

/-- Closing an object context of sorts. -/
theorem long_abstractN {k : Nat} {c : Ctx Head k} :
    ∀ (Γ : Binding.Ctx sig) {result : Tm Head 0},
      Typed S.R .nil result (.head realization.typeUniverse) →
      ∀ (body : Tm Head (k + Γ.length)),
        Long S.R S.roles (.term (extendCtx names c Γ) body (liftClosed result)) →
        Long S.R S.roles (.term c (abstractN Γ.length body)
          (liftClosed (BindingSignatureEmbedding.telescopeType names Γ result)))
  | [], _, _, _, long => long
  | s :: Γ, result, tResult, body, long => by
      have tArrow := closedArrow_typed names realization (sort_typed names realization .nil s) tResult
      have isArrow := lifted_isType names realization (extendCtx names c Γ) tArrow
      have tLifted := Normalization.Typed.liftClosed (Δ := extendCtx names c Γ) tArrow
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at isArrow tLifted
      have lamLong : Long S.R S.roles (.term (extendCtx names c Γ) (.lam body)
          (liftClosed (BindingSignatureEmbedding.closedArrow
            (BindingSignatureEmbedding.sortType names s) result))) := by
        rw [BindingSignatureEmbedding.liftClosed_closedArrow]
        exact .lam (IsType.refl isArrow) ⟨_, realization.universeIs, sort_typed names realization _ s⟩
          (.lamIntro tLifted realization.universeIs long.typed) long
      exact long_abstractN Γ tArrow (.lam body) lamLong

include realization in
/-- The telescope of a list frame is formed. -/
theorem metaCtx_formed : ∀ M : List (Binding.MetaArity sig), CtxFormed S.R (metaCtx (Head := Head) names M)
  | [] => .nil
  | a :: M => .snoc (metaCtx_formed M) (lifted_isType names realization _ (bindingType_typed names realization a.1 a.2))

include realization in
/-- A telescope extended by sorts is formed. -/
theorem extendCtx_formed {k : Nat} {c : Ctx Head k} (formed : CtxFormed S.R c) :
    ∀ Γ : Binding.Ctx sig, CtxFormed S.R (extendCtx names c Γ)
  | [] => formed
  | s :: Γ => .snoc (extendCtx_formed formed Γ) ⟨_, realization.universeIs, sort_typed names realization _ s⟩

include facts rigid realization

set_option linter.unusedSectionVars false in
mutual

/-- **Translated terms are η-long** at their sorts. -/
theorem long_encode (M : List (Binding.MetaArity sig)) :
    ∀ {Γ : Binding.Ctx sig} {s : sig.Srt} (t : Binding.Term (Sig sig M) Γ s),
      Long S.R S.roles (.term (extendCtx names (metaCtx names M) Γ) (encode names M t)
        (BindingSignatureEmbedding.sortType names s))
  | Γ, s, .var v => by
      have formed := extendCtx_formed names realization (metaCtx_formed names realization M) Γ
      refine long_at_sort facts rigid names realization formed (.var _ ?_)
      rw [extendCtx_inner]
      exact IsType.refl ⟨_, realization.universeIs, sort_typed names realization _ s⟩
  | Γ, s, .op (.inl o) args => by
      have formed := extendCtx_formed names realization (metaCtx_formed names realization M) Γ
      have tSort := sort_typed names realization (Head := Head) .nil s
      have tOperator := argumentsType_typed names realization (sig.arity o) tSort
      have head : Long S.R S.roles (.spine (extendCtx names (metaCtx names M) Γ) (.const (names.operator o))
          (liftClosed (BindingSignatureEmbedding.argumentsType names (sig.arity o)
            (BindingSignatureEmbedding.sortType names s)))) :=
        .const (rigid _) (realization.operatorLookup o)
          (Derivable.const (realization.operatorLookup o) tOperator realization.universeIs)
          (IsType.refl (lifted_isType names realization _ tOperator))
      exact long_at_sort facts rigid names realization formed
        (long_applyVec names realization _ tSort (sig.arity o) head (long_encodeArgs M args))
  | Γ, _, .op (.inr (.mk i)) args => by
      have formed := extendCtx_formed names realization (metaCtx_formed names realization M) Γ
      have tSort := sort_typed names realization (Head := Head) .nil (M.get i).2
      have tType := bindingType_typed names realization (M.get i).1 (M.get i).2
      have castLength : (M.get i).1.length =
          ((M.get i).1.map (fun sort => (([] : List sig.Srt), sort))).length := by simp
      have head : Long S.R S.roles (.spine (extendCtx names (metaCtx names M) Γ) (.var (outer i))
          (liftClosed (BindingSignatureEmbedding.telescopeType names (M.get i).1
            (BindingSignatureEmbedding.sortType names (M.get i).2)))) := by
        refine .var _ ?_
        rw [extendCtx_outer names (metaCtx names M) (metaCtx_lookup names M i) Γ]
        exact IsType.refl (lifted_isType names realization _ tType)
      refine long_at_sort facts rigid names realization formed
        (long_spine names realization (M.get i).1 tSort head (fun j => ?_))
      have component := long_encodeArgs M args (Fin.cast castLength j)
      rw [get_map_cast (M.get i).1 castLength j] at component
      exact component

/-- Translated operator arguments are η-long at their binding types. -/
theorem long_encodeArgs (M : List (Binding.MetaArity sig)) :
    ∀ {as : List (List sig.Srt × sig.Srt)} {Γ : Binding.Ctx sig}
      (args : Binding.Args (Sig sig M) as Γ) (j : Fin as.length),
      Long S.R S.roles (.term (extendCtx names (metaCtx names M) Γ) (encodeArgs names M args j)
        (liftClosed (BindingSignatureEmbedding.bindingType names (as.get j).1 (as.get j).2)))
  | _, _, .nil, j => j.elim0
  | _, _, .cons (bs := bound) (s := sort) body rest, j => by
      refine Fin.cases ?_ (fun j => long_encodeArgs M rest j) j
      exact long_abstractB names realization bound (sort_typed names realization .nil sort)
        (encode names M body) (long_encode M body)

end

/-- **The judged term of every observation is η-long** at its type `Π Γ. s`. -/
theorem entry_long {M : List (Binding.MetaArity sig)}
    (o : Binding.ContextualFamily.Observation sig M.get) :
    Long S.R S.roles (.term (metaCtx names M) (abstractN o.1.length (encode names M o.2.2))
      (liftClosed (BindingSignatureEmbedding.bindingType names o.1 o.2.1))) :=
  long_abstractN names realization o.1 (sort_typed names realization .nil o.2.1) _
    (long_encode facts rigid names realization M o.2.2)

omit facts in
/-- Closed arrow types over sorts are normal types. -/
theorem telescope_long : ∀ (bound : List sig.Srt) {result : Tm Head 0},
    Typed S.R .nil result (.head realization.typeUniverse) →
    (∀ {n : Nat} (Δ : Ctx Head n), Long S.R S.roles (.type Δ (liftClosed result))) →
    ∀ {n : Nat} (Δ : Ctx Head n),
      Long S.R S.roles (.type Δ (liftClosed (BindingSignatureEmbedding.telescopeType names bound result)))
  | [], _, _, long, _, Δ => long Δ
  | s :: bound, result, tResult, long, _, Δ => by
      have tArrow := closedArrow_typed names realization (sort_typed names realization .nil s) tResult
      refine telescope_long bound tArrow (fun Δ' => ?_) Δ
      have isArrow := lifted_isType names realization Δ' tArrow
      have sortLong : ∀ {m : Nat} (Θ : Ctx Head m),
          Long S.R S.roles (.type Θ (BindingSignatureEmbedding.sortType names s)) := fun Θ =>
        .neutralType (.const (rigid _) (realization.sortLookup s)
            (Derivable.const (realization.sortLookup s) (.headType realization.universeTyped)
              realization.aboveIs)
            (IsType.refl (IsType.head_of_universe (S := S) realization.universeIs)))
          realization.universeIs
          (IsType.below_refl (IsType.head_of_universe (S := S) realization.universeIs))
      rw [BindingSignatureEmbedding.liftClosed_closedArrow] at isArrow ⊢
      exact .pi (sortLong Δ') (long _) isArrow

omit facts in
/-- **The type code of every observation is a normal type.** -/
theorem type_long {n : Nat} (Δ : Ctx Head n) (bound : List sig.Srt) (s : sig.Srt) :
    Long S.R S.roles (.type Δ (liftClosed (BindingSignatureEmbedding.bindingType names bound s))) := by
  refine telescope_long rigid names realization bound (sort_typed names realization .nil s)
    (fun Θ => ?_) Δ
  exact .neutralType (.const (rigid _) (realization.sortLookup s)
      (Derivable.const (realization.sortLookup s) (.headType realization.universeTyped)
        realization.aboveIs)
      (IsType.refl (IsType.head_of_universe (S := S) realization.universeIs)))
    realization.universeIs
    (IsType.below_refl (IsType.head_of_universe (S := S) realization.universeIs))

end Long

/-! ## No head occurs in a translation -/

section HeadFree

variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)

theorem HeadFree.rename {n m : Nat} (ρ : Ren n m) {t : Tm Head n} (free : HeadFree t) :
    HeadFree (Presentation.rename ρ t) := by
  induction t generalizing m with
  | var => exact trivial
  | const => exact trivial
  | head => exact free
  | pi _ _ ih₁ ih₂ => exact And.intro (ih₁ ρ free.1) (ih₂ (liftRen ρ) free.2)
  | sigma _ _ ih₁ ih₂ => exact And.intro (ih₁ ρ free.1) (ih₂ (liftRen ρ) free.2)
  | id _ _ _ ih₁ ih₂ ih₃ =>
      exact And.intro (ih₁ ρ free.1) (And.intro (ih₂ ρ free.2.1) (ih₃ ρ free.2.2))
  | lam _ ih => exact ih (liftRen ρ) free
  | app _ _ ih₁ ih₂ => exact And.intro (ih₁ ρ free.1) (ih₂ ρ free.2)
  | pair _ _ ih₁ ih₂ => exact And.intro (ih₁ ρ free.1) (ih₂ ρ free.2)
  | fst _ ih => exact ih ρ free
  | snd _ ih => exact ih ρ free
  | refl _ ih => exact ih ρ free

theorem telescope_headFree : ∀ (bound : List sig.Srt) {result : Tm Head 0}, HeadFree result →
    HeadFree (BindingSignatureEmbedding.telescopeType names bound result)
  | [], _, free => free
  | _ :: bound, _, free => telescope_headFree bound (And.intro trivial (HeadFree.rename _ free))

theorem type_headFree {n : Nat} (bound : List sig.Srt) (s : sig.Srt) :
    HeadFree (liftClosed (BindingSignatureEmbedding.bindingType names bound s) : Tm Head n) :=
  HeadFree.rename _ (telescope_headFree names bound (result := BindingSignatureEmbedding.sortType names s)
    trivial)

theorem applyVec_headFree {n : Nat} : ∀ {p : Nat} {f : Tm Head n} {w : Sub Head p n},
    HeadFree f → (∀ j, HeadFree (w j)) → HeadFree (applyVec f w)
  | 0, _, _, free, _ => free
  | p + 1, f, w, free, args =>
      applyVec_headFree (p := p) (f := .app f (w 0)) (w := fun j => w j.succ) (And.intro free (args 0))
        (fun j => args j.succ)

theorem spine_headFree {n : Nat} : ∀ {p : Nat} {f : Tm Head n} {w : Sub Head p n},
    HeadFree f → (∀ j, HeadFree (w j)) → HeadFree (spine f w)
  | 0, _, _, free, _ => free
  | p + 1, f, w, free, args =>
      And.intro (spine_headFree (p := p) (f := f) (w := fun j => w j.succ) free (fun j => args j.succ))
        (args 0)

theorem abstractB_headFree {k : Nat} {Γ : List sig.Srt} :
    ∀ (bound : List sig.Srt) {body : Tm Head (k + (bound ++ Γ).length)}, HeadFree body →
      HeadFree (abstractB (Γ := Γ) bound body)
  | [], _, free => free
  | _ :: bound, _, free => abstractB_headFree bound (body := .lam _) free

theorem abstractN_headFree {k : Nat} : ∀ (p : Nat) {body : Tm Head (k + p)}, HeadFree body →
    HeadFree (abstractN p body)
  | 0, _, free => free
  | p + 1, _, free => abstractN_headFree p (body := .lam _) free

mutual

theorem encode_headFree (M : List (Binding.MetaArity sig)) :
    ∀ {Γ : Binding.Ctx sig} {s : sig.Srt} (t : Binding.Term (Sig sig M) Γ s),
      HeadFree (encode (Head := Head) names M t)
  | _, _, .var _ => trivial
  | _, _, .op (.inl _) args => applyVec_headFree trivial (encodeArgs_headFree M args)
  | _, _, .op (.inr (.mk _)) args => spine_headFree trivial (fun _ => encodeArgs_headFree M args _)

theorem encodeArgs_headFree (M : List (Binding.MetaArity sig)) :
    ∀ {as : List (List sig.Srt × sig.Srt)} {Γ : Binding.Ctx sig}
      (args : Binding.Args (Sig sig M) as Γ) (j : Fin as.length),
      HeadFree (encodeArgs (Head := Head) names M args j)
  | _, _, .nil, j => j.elim0
  | _, _, .cons (bs := bound) body rest, j =>
      Fin.cases (abstractB_headFree bound (encode_headFree M body))
        (fun j => encodeArgs_headFree M rest j) j

end

theorem entry_headFree {M : List (Binding.MetaArity sig)}
    (o : Binding.ContextualFamily.Observation sig M.get) :
    HeadFree (abstractN o.1.length (encode (Head := Head) names M o.2.2)) :=
  abstractN_headFree _ (encode_headFree names M o.2.2)

end HeadFree

end ContextualDependentFibre
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
