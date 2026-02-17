import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.ObservationalQuotient
import Mathlib.Logic.Relation

/-!
# GF Semantic Kernel: Top-Step Joinability + Quotient Instantiation

This module packages the top-level GF semantic rewrite families used in the
OSLF bridge and proves:

1. determinism of top-level semantic steps;
2. explicit joinability for one-step forks;
3. a concrete `ObservationalQuotient` instantiation with family-level
   independence and symmetry action.
4. context-closure local commutation for the independent pair
   `.useN` / `.pastTense`:
   - `gf_context_commuteAt_useN_pastTense`
   - `gf_context_independent_commuting_useN_pastTense`
5. a regression counterexample showing `.useN` / `.activePassive`
   is not universally commuting in this context-closed relation:
   - `gf_context_not_commuteAt_useN_activePassive`

This is the "critical-pair/top-step" layer designed to extend naturally to
full context-closure confluence proofs.
-/

namespace Mettapedia.Languages.GF.SemanticKernelConfluence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework

/-- GF rewrite labels in the compact semantic kernel. -/
inductive GFRewriteLabel where
  | useN | positA | useV | useComp | useN2 | useA2
  | activePassive
  | presentTense | pastTense | futureTense
  deriving DecidableEq, Repr

/-- Rewrite families for independence reasoning. -/
inductive GFRewriteFamily where
  | wrapper
  | voice
  | tense
  deriving DecidableEq, Repr

/-- Family classification of GF rewrite labels. -/
def labelFamily : GFRewriteLabel → GFRewriteFamily
  | .useN | .positA | .useV | .useComp | .useN2 | .useA2 => .wrapper
  | .activePassive => .voice
  | .presentTense | .pastTense | .futureTense => .tense

/-- One-step top-level GF semantic rewrite relation by explicit label. -/
inductive GFTopStep : GFRewriteLabel → Pattern → Pattern → Prop where
  | useN (p : Pattern) :
      GFTopStep .useN (.apply "UseN" [p]) p
  | positA (p : Pattern) :
      GFTopStep .positA (.apply "PositA" [p]) p
  | useV (p : Pattern) :
      GFTopStep .useV (.apply "UseV" [p]) p
  | useComp (p : Pattern) :
      GFTopStep .useComp (.apply "UseComp" [p]) p
  | useN2 (p : Pattern) :
      GFTopStep .useN2 (.apply "UseN2" [p]) p
  | useA2 (p : Pattern) :
      GFTopStep .useA2 (.apply "UseA2" [p]) p
  | activePassive (v np1 np2 : Pattern) :
      GFTopStep .activePassive
        (.apply "PredVP" [np1, .apply "ComplSlash" [.apply "SlashV2a" [v], np2]])
        (.apply "PredVP" [np2, .apply "PassV2" [v]])
  | presentTense (cl : Pattern) :
      GFTopStep .presentTense
        (.apply "UseCl"
          [ .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]
          , .apply "PPos" []
          , cl ])
        (.apply "⊛temporal" [cl, .apply "0" []])
  | pastTense (cl : Pattern) :
      GFTopStep .pastTense
        (.apply "UseCl"
          [ .apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []]
          , .apply "PPos" []
          , cl ])
        (.apply "⊛temporal" [cl, .apply "-1" []])
  | futureTense (cl : Pattern) :
      GFTopStep .futureTense
        (.apply "UseCl"
          [ .apply "TTAnt" [.apply "TFut" [], .apply "ASimul" []]
          , .apply "PPos" []
          , cl ])
        (.apply "⊛temporal" [cl, .apply "1" []])

/-- Unlabeled top-step reduction relation for the semantic kernel. -/
def GFTopReduces (x y : Pattern) : Prop := ∃ ℓ, GFTopStep ℓ x y

/-- Deterministic top-step output of the compact GF semantic kernel. -/
def topStepOut : Pattern → Option Pattern
  | .apply "UseN" [p] => some p
  | .apply "PositA" [p] => some p
  | .apply "UseV" [p] => some p
  | .apply "UseComp" [p] => some p
  | .apply "UseN2" [p] => some p
  | .apply "UseA2" [p] => some p
  | .apply "PredVP" [_, .apply "ComplSlash" [.apply "SlashV2a" [v], np2]] =>
      some (.apply "PredVP" [np2, .apply "PassV2" [v]])
  | .apply "UseCl"
      [ .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]
      , .apply "PPos" []
      , cl ] =>
      some (.apply "⊛temporal" [cl, .apply "0" []])
  | .apply "UseCl"
      [ .apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []]
      , .apply "PPos" []
      , cl ] =>
      some (.apply "⊛temporal" [cl, .apply "-1" []])
  | .apply "UseCl"
      [ .apply "TTAnt" [.apply "TFut" [], .apply "ASimul" []]
      , .apply "PPos" []
      , cl ] =>
      some (.apply "⊛temporal" [cl, .apply "1" []])
  | _ => none

/-- Family selected by the top-step matcher. -/
def topStepFamily : Pattern → Option GFRewriteFamily
  | .apply "UseN" [_] => some .wrapper
  | .apply "PositA" [_] => some .wrapper
  | .apply "UseV" [_] => some .wrapper
  | .apply "UseComp" [_] => some .wrapper
  | .apply "UseN2" [_] => some .wrapper
  | .apply "UseA2" [_] => some .wrapper
  | .apply "PredVP" [_, .apply "ComplSlash" [.apply "SlashV2a" [_], _]] => some .voice
  | .apply "UseCl"
      [ .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]
      , .apply "PPos" []
      , _ ] =>
      some .tense
  | .apply "UseCl"
      [ .apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []]
      , .apply "PPos" []
      , _ ] =>
      some .tense
  | .apply "UseCl"
      [ .apply "TTAnt" [.apply "TFut" [], .apply "ASimul" []]
      , .apply "PPos" []
      , _ ] =>
      some .tense
  | _ => none

theorem topStepOut_of_GFTopStep
    {ℓ : GFRewriteLabel} {x y : Pattern}
    (h : GFTopStep ℓ x y) :
    topStepOut x = some y := by
  cases h <;> rfl

theorem topStepFamily_of_GFTopStep
    {ℓ : GFRewriteLabel} {x y : Pattern}
    (h : GFTopStep ℓ x y) :
    topStepFamily x = some (labelFamily ℓ) := by
  cases h <;> rfl

/-- Top-step semantics are deterministic: same source gives the same reduct. -/
theorem gf_topstep_deterministic
    {ℓ₁ ℓ₂ : GFRewriteLabel} {x y₁ y₂ : Pattern}
    (h₁ : GFTopStep ℓ₁ x y₁) (h₂ : GFTopStep ℓ₂ x y₂) :
    y₁ = y₂ := by
  have hOut1 : topStepOut x = some y₁ := topStepOut_of_GFTopStep h₁
  have hOut2 : topStepOut x = some y₂ := topStepOut_of_GFTopStep h₂
  have hs : some y₁ = some y₂ := hOut1.symm.trans hOut2
  exact Option.some.inj hs

/-- Explicit one-step joinability for the top semantic kernel. -/
theorem gf_topstep_explicit_joinable
    {x y₁ y₂ : Pattern}
    (h₁ : GFTopReduces x y₁) (h₂ : GFTopReduces x y₂) :
    ∃ z,
      Relation.ReflTransGen GFTopReduces y₁ z ∧
      Relation.ReflTransGen GFTopReduces y₂ z := by
  rcases h₁ with ⟨ℓ₁, h₁⟩
  rcases h₂ with ⟨ℓ₂, h₂⟩
  have hy : y₁ = y₂ := gf_topstep_deterministic h₁ h₂
  subst hy
  exact ⟨y₁, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-! ## Context-Closed Lift (Apply-Argument Contexts) -/

/-- Context-closed labeled semantic step:
top-step rewrites lifted through `.apply` argument contexts. -/
inductive GFContextStep (ℓ : GFRewriteLabel) : Pattern → Pattern → Prop where
  | top {x y : Pattern} :
      GFTopStep ℓ x y →
      GFContextStep ℓ x y
  | appCtx {f : String} {pre post : List Pattern} {p q : Pattern} :
      GFContextStep ℓ p q →
      GFContextStep ℓ (.apply f (pre ++ p :: post)) (.apply f (pre ++ q :: post))

/-- One-hole `.apply` frame used to decompose context-closed steps. -/
structure ApplyFrame where
  f : String
  pre : List Pattern
  post : List Pattern

/-- Plug a term into one `.apply` frame. -/
def plugFrame (fr : ApplyFrame) (p : Pattern) : Pattern :=
  .apply fr.f (fr.pre ++ p :: fr.post)

/-- Plug a term through a stack of outer-to-inner frames. -/
def plugFrames (frs : List ApplyFrame) (p : Pattern) : Pattern :=
  frs.foldr plugFrame p

/-- Decompose a context-closed step into frames plus one focused top-step redex. -/
theorem gfContextStep_decompose
    {ℓ : GFRewriteLabel} {x y : Pattern}
    (h : GFContextStep ℓ x y) :
    ∃ frs p q,
      GFTopStep ℓ p q ∧
      x = plugFrames frs p ∧
      y = plugFrames frs q := by
  induction h with
  | top htop =>
      refine ⟨[], _, _, htop, ?_, ?_⟩ <;> rfl
  | @appCtx f pre post p q hstep ih =>
      rcases ih with ⟨frs, p0, q0, htop, hx, hy⟩
      refine ⟨{ f := f, pre := pre, post := post } :: frs, p0, q0, htop, ?_, ?_⟩
      · simp [plugFrames, plugFrame, hx]
      · simp [plugFrames, plugFrame, hy]

/-- Reconstruct a context-closed step from a focused top-step and frames. -/
theorem gfContextStep_of_frames
    {ℓ : GFRewriteLabel} {frs : List ApplyFrame} {p q : Pattern}
    (h : GFTopStep ℓ p q) :
    GFContextStep ℓ (plugFrames frs p) (plugFrames frs q) := by
  induction frs with
  | nil =>
      simpa [plugFrames] using GFContextStep.top h
  | cons fr frs ih =>
      simpa [plugFrames, plugFrame] using GFContextStep.appCtx ih

lemma singleton_eq_append_cons
    {α : Type*} {a b : α} {pre post : List α}
    (h : [a] = pre ++ b :: post) :
    pre = [] ∧ post = [] ∧ a = b := by
  cases pre with
  | nil =>
      simp at h
      rcases h with ⟨ha, hpost⟩
      exact ⟨rfl, hpost, ha⟩
  | cons p ps =>
      simp at h

/-- Unlabeled context-closed semantic relation. -/
def GFSemStep (x y : Pattern) : Prop := ∃ ℓ, GFContextStep ℓ x y

/-- Lift top-step reflexive-transitive closure into context-closed closure. -/
theorem rtg_top_to_sem {p q : Pattern}
    (h : Relation.ReflTransGen GFTopReduces p q) :
    Relation.ReflTransGen GFSemStep p q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hrest hstep ih =>
      rcases hstep with ⟨ℓ, hℓ⟩
      exact Relation.ReflTransGen.tail ih ⟨ℓ, GFContextStep.top hℓ⟩

/-- Lift a context-closed path through the same `.apply` argument context. -/
theorem rtg_sem_lift_appCtx
    {f : String} {pre post : List Pattern} {p q : Pattern}
    (h : Relation.ReflTransGen GFSemStep p q) :
    Relation.ReflTransGen GFSemStep
      (.apply f (pre ++ p :: post))
      (.apply f (pre ++ q :: post)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hrest hstep ih =>
      rcases hstep with ⟨ℓ, hℓ⟩
      exact Relation.ReflTransGen.tail ih ⟨ℓ, GFContextStep.appCtx hℓ⟩

/-- Explicit joinability lifted from top-step forks into a shared apply context. -/
theorem gf_semstep_explicit_joinable_in_app_context
    {f : String} {pre post : List Pattern} {x y₁ y₂ : Pattern}
    (h₁ : GFTopReduces x y₁) (h₂ : GFTopReduces x y₂) :
    ∃ z,
      Relation.ReflTransGen GFSemStep (.apply f (pre ++ y₁ :: post)) z ∧
      Relation.ReflTransGen GFSemStep (.apply f (pre ++ y₂ :: post)) z := by
  rcases gf_topstep_explicit_joinable h₁ h₂ with ⟨z0, hz1, hz2⟩
  refine ⟨.apply f (pre ++ z0 :: post), ?_, ?_⟩
  · exact rtg_sem_lift_appCtx (rtg_top_to_sem hz1)
  · exact rtg_sem_lift_appCtx (rtg_top_to_sem hz2)

/-- Family-level independence: labels are independent when families differ. -/
def gfIndependent (ℓ₁ ℓ₂ : GFRewriteLabel) : Prop :=
  labelFamily ℓ₁ ≠ labelFamily ℓ₂

theorem gfIndependent_symm : Symmetric gfIndependent := by
  intro ℓ₁ ℓ₂ h
  exact Ne.symm h

/-- Concrete GF label-independence structure. -/
def gfLabelIndependence : LabelIndependence GFRewriteLabel where
  indep := gfIndependent
  symm := gfIndependent_symm

/-- Concrete labeled rewrite object for GF top-step semantic rewrites. -/
def gfLabeledRewrite : LabeledRewrite GFRewriteLabel Pattern where
  step := GFTopStep

/-- Context-closed labeled rewrite object (top-step + app-arg closure). -/
def gfContextLabeledRewrite : LabeledRewrite GFRewriteLabel Pattern where
  step := GFContextStep

/-- Two independent families cannot both fire as top-level steps on one source. -/
theorem gf_no_parallel_independent
    {ℓ₁ ℓ₂ : GFRewriteLabel} {x y₁ y₂ : Pattern}
    (hInd : gfIndependent ℓ₁ ℓ₂)
    (h₁ : GFTopStep ℓ₁ x y₁) (h₂ : GFTopStep ℓ₂ x y₂) : False := by
  have hFam1 : topStepFamily x = some (labelFamily ℓ₁) := topStepFamily_of_GFTopStep h₁
  have hFam2 : topStepFamily x = some (labelFamily ℓ₂) := topStepFamily_of_GFTopStep h₂
  have hs : some (labelFamily ℓ₁) = some (labelFamily ℓ₂) := hFam1.symm.trans hFam2
  have hEq : labelFamily ℓ₁ = labelFamily ℓ₂ := Option.some.inj hs
  exact hInd hEq

/-- Independent top-level families commute vacuously (no parallel redex overlap). -/
theorem gf_independent_commuteAt (ℓ₁ ℓ₂ : GFRewriteLabel)
    (hInd : gfIndependent ℓ₁ ℓ₂) :
    CommuteAt gfLabeledRewrite ℓ₁ ℓ₂ := by
  intro x y₁ y₂ h₁ h₂
  exact False.elim (gf_no_parallel_independent hInd h₁ h₂)

instance : Group PUnit where
  mul _ _ := PUnit.unit
  mul_assoc _ _ _ := rfl
  one := PUnit.unit
  one_mul _ := rfl
  mul_one _ := rfl
  inv _ := PUnit.unit
  inv_mul_cancel _ := rfl

/-- Trivial symmetry action on patterns (identity action). -/
def gfIdentitySymmetry : SymmetryAction PUnit Pattern where
  act _ x := x
  one_act _ := rfl
  mul_act _ _ _ := rfl

/-- The identity action is equivariant for any GF top-step rewrite. -/
theorem gf_topstep_equivariant :
    StepEquivariant gfLabeledRewrite gfIdentitySymmetry := by
  intro g ℓ x y h
  simpa [gfIdentitySymmetry] using h

/-- Identity-action equivariance for context-closed labeled steps. -/
theorem gf_context_equivariant :
    StepEquivariant gfContextLabeledRewrite gfIdentitySymmetry := by
  intro g ℓ x y h
  induction h with
  | top htop =>
      exact GFContextStep.top (by simpa [gfIdentitySymmetry] using htop)
  | appCtx h ih =>
      exact GFContextStep.appCtx ih

/-- Concrete observable-kernel package for GF top semantic rewrites. -/
def gfObservableKernelTop : ObservableKernel GFRewriteLabel PUnit Pattern where
  rewrite := gfLabeledRewrite
  indep := gfLabelIndependence
  symm := gfIdentitySymmetry
  equivariant := gf_topstep_equivariant

/-- Family-level independent labels satisfy the kernel's commuting predicate. -/
theorem gf_independent_commuting
    (ℓ₁ ℓ₂ : GFRewriteLabel)
    (hInd : gfObservableKernelTop.indep.indep ℓ₁ ℓ₂) :
    gfObservableKernelTop.IndependentCommuting ℓ₁ ℓ₂ := by
  exact ⟨hInd, gf_independent_commuteAt ℓ₁ ℓ₂ hInd⟩

/-- Context-closed observable-kernel package for GF semantic rewrites. -/
def gfObservableKernelCtx : ObservableKernel GFRewriteLabel PUnit Pattern where
  rewrite := gfContextLabeledRewrite
  indep := gfLabelIndependence
  symm := gfIdentitySymmetry
  equivariant := gf_context_equivariant

private def useNSeed (p : Pattern) : Pattern := .apply "UseN" [p]
private def pastSeed (cl : Pattern) : Pattern :=
  .apply "UseCl"
    [ .apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []]
    , .apply "PPos" []
    , cl ]
private def pastOut (cl : Pattern) : Pattern :=
  .apply "⊛temporal" [cl, .apply "-1" []]

private def commuteWitnessSource : Pattern :=
  .apply "Pair" [useNSeed (.fvar "n"), pastSeed (.fvar "cl")]
private def commuteWitnessY1 : Pattern :=
  .apply "Pair" [.fvar "n", pastSeed (.fvar "cl")]
private def commuteWitnessY2 : Pattern :=
  .apply "Pair" [useNSeed (.fvar "n"), pastOut (.fvar "cl")]
private def commuteWitnessZ : Pattern :=
  .apply "Pair" [.fvar "n", pastOut (.fvar "cl")]

private def activeSeed (v np1 np2 : Pattern) : Pattern :=
  .apply "PredVP" [np1, .apply "ComplSlash" [.apply "SlashV2a" [v], np2]]
private def activeOut (v np2 : Pattern) : Pattern :=
  .apply "PredVP" [np2, .apply "PassV2" [v]]

private def voiceWitnessSource : Pattern :=
  .apply "Pair" [useNSeed (.fvar "n"), activeSeed (.fvar "v") (.fvar "np1") (.fvar "np2")]
private def voiceWitnessY1 : Pattern :=
  .apply "Pair" [.fvar "n", activeSeed (.fvar "v") (.fvar "np1") (.fvar "np2")]
private def voiceWitnessY2 : Pattern :=
  .apply "Pair" [useNSeed (.fvar "n"), activeOut (.fvar "v") (.fvar "np2")]
private def voiceWitnessZ : Pattern :=
  .apply "Pair" [.fvar "n", activeOut (.fvar "v") (.fvar "np2")]

lemma useN_top_shape {x y : Pattern} (h : GFTopStep .useN x y) :
    ∃ p, x = useNSeed p ∧ y = p := by
  cases h
  exact ⟨_, rfl, rfl⟩

lemma past_top_shape {x y : Pattern} (h : GFTopStep .pastTense x y) :
    ∃ cl, x = pastSeed cl ∧ y = pastOut cl := by
  cases h
  exact ⟨_, rfl, rfl⟩

lemma lift_useN_into_pastSeed {cl q : Pattern}
    (h : GFContextStep .useN cl q) :
    GFContextStep .useN (pastSeed cl) (pastSeed q) := by
  simpa [pastSeed] using
    (GFContextStep.appCtx
      (f := "UseCl")
      (pre :=
        [ .apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []]
        , .apply "PPos" [] ])
      (post := [])
      h)

lemma lift_useN_into_pastOut {cl q : Pattern}
    (h : GFContextStep .useN cl q) :
    GFContextStep .useN (pastOut cl) (pastOut q) := by
  simpa [pastOut] using
    (GFContextStep.appCtx
      (f := "⊛temporal")
      (pre := [])
      (post := [.apply "-1" []])
      h)

lemma pair_split {α : Type} {a b m : α} {pre post : List α}
    (h : [a, b] = pre ++ m :: post) :
    (pre = [] ∧ post = [b] ∧ m = a) ∨
    (pre = [a] ∧ post = [] ∧ m = b) := by
  cases pre with
  | nil =>
      simp at h
      exact Or.inl ⟨rfl, h.2.symm, h.1.symm⟩
  | cons x xs =>
      cases xs with
      | nil =>
          simp at h
          rcases h with ⟨hx, hm, hpost⟩
          subst hx
          exact Or.inr ⟨rfl, hpost, hm.symm⟩
      | cons y ys =>
          simp at h

lemma triple_split {α : Type} {a b c m : α} {pre post : List α}
    (h : [a, b, c] = pre ++ m :: post) :
    (pre = [] ∧ post = [b, c] ∧ m = a) ∨
    (pre = [a] ∧ post = [c] ∧ m = b) ∨
    (pre = [a, b] ∧ post = [] ∧ m = c) := by
  cases pre with
  | nil =>
      simp at h
      exact Or.inl ⟨rfl, h.2.symm, h.1.symm⟩
  | cons x xs =>
      cases xs with
      | nil =>
          simp at h
          rcases h with ⟨hx, hm, hpost⟩
          subst hx
          exact Or.inr (Or.inl ⟨rfl, hpost.symm, hm.symm⟩)
      | cons y ys =>
          cases ys with
          | nil =>
              simp at h
              rcases h with ⟨hx, hy, hm, hpost⟩
              subst hx
              subst hy
              exact Or.inr (Or.inr ⟨rfl, hpost, hm.symm⟩)
          | cons z zs =>
              simp at h

lemma one_hole_eq_cases {α : Type} {pre post pre' post' : List α} {a b : α}
    (h : pre ++ a :: post = pre' ++ b :: post') :
    (pre = pre' ∧ a = b ∧ post = post') ∨
    (∃ s, pre' = pre ++ a :: s ∧ post = s ++ b :: post') ∨
    (∃ s, pre = pre' ++ b :: s ∧ post' = s ++ a :: post) := by
  induction pre generalizing pre' with
  | nil =>
      cases pre' with
      | nil =>
          simp at h
          rcases h with ⟨hab, hpost⟩
          exact Or.inl ⟨rfl, hab, hpost⟩
      | cons x xs =>
          simp at h
          rcases h with ⟨hx, htail⟩
          subst hx
          exact Or.inr (Or.inl ⟨xs, rfl, htail⟩)
  | cons x xs ih =>
      cases pre' with
      | nil =>
          simp at h
          rcases h with ⟨hx, htail⟩
          subst hx
          exact Or.inr (Or.inr ⟨xs, rfl, htail.symm⟩)
      | cons y ys =>
          simp at h
          rcases h with ⟨hxy, htail⟩
          subst hxy
          rcases ih htail with hsame | hright | hleft
          · rcases hsame with ⟨hpre, hab, hpost⟩
            exact Or.inl ⟨by simp [hpre], hab, hpost⟩
          · rcases hright with ⟨s, hpre', hpost⟩
            refine Or.inr (Or.inl ⟨s, ?_, hpost⟩)
            simp [hpre']
          · rcases hleft with ⟨s, hpre, hpost'⟩
            refine Or.inr (Or.inr ⟨s, ?_, hpost'⟩)
            simp [hpre]

lemma same_hole_appCtx_arg_inversion {α : Type} {pre : List α} {a b : α} {post : List α}
    (h : pre ++ a :: post = pre ++ b :: post) :
    a = b := by
  have hcons : a :: post = b :: post := List.append_right_injective pre h
  exact (List.cons.inj hcons).1

lemma no_useN_step_nullary {f : String} (hf : f ≠ "UseN") {y : Pattern} :
    ¬ GFContextStep .useN (.apply f []) y := by
  intro h
  rcases gfContextStep_decompose h with ⟨frs, p0, q0, htop, hx, hy⟩
  rcases useN_top_shape htop with ⟨p, rfl, rfl⟩
  cases frs with
  | nil =>
      have hhead := congrArg (fun t =>
        match t with
        | .apply g _ => g
        | _ => "") hx
      have : f = "UseN" := by
        simp [plugFrames, useNSeed] at hhead
        exact hhead
      exact hf this
  | cons fr rest =>
      have hargs := congrArg (fun t =>
        match t with
        | .apply _ args => args
        | _ => ([] : List Pattern)) hx
      simp [plugFrames, plugFrame] at hargs

lemma no_useN_step_ttant {y : Pattern} :
    ¬ GFContextStep .useN
      (.apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []]) y := by
  intro h
  rcases gfContextStep_decompose h with ⟨frs, p0, q0, htop, hx, hy⟩
  rcases useN_top_shape htop with ⟨p, hp0, hq0⟩
  cases frs with
  | nil =>
      have hhead := congrArg (fun t =>
        match t with
        | .apply g _ => g
        | _ => "") hx
      have : "TTAnt" = "UseN" := by
        simp [hp0, plugFrames, useNSeed] at hhead
      exact (by decide : "TTAnt" ≠ "UseN") this
  | cons fr rest =>
      have hargs :
          [.apply "TPast" [], .apply "ASimul" []] =
            fr.pre ++ plugFrames rest (useNSeed p) :: fr.post := by
        have hEq := congrArg (fun t =>
          match t with
          | .apply _ args => args
          | _ => ([] : List Pattern)) hx
        simpa [hp0, plugFrames, plugFrame] using hEq
      rcases pair_split hargs with hsplit | hsplit
      · rcases hsplit with ⟨hpre, hpost, hmid⟩
        have hmid' : .apply "TPast" [] = plugFrames rest (useNSeed p) := by
          simpa [hpre, hpost] using hmid.symm
        have hstep : GFContextStep .useN (.apply "TPast" []) (plugFrames rest p) := by
          simpa [hmid'] using
            (gfContextStep_of_frames (frs := rest) (GFTopStep.useN p))
        exact (no_useN_step_nullary (f := "TPast") (by decide)) hstep
      · rcases hsplit with ⟨hpre, hpost, hmid⟩
        have hmid' : .apply "ASimul" [] = plugFrames rest (useNSeed p) := by
          simpa [hpre, hpost] using hmid.symm
        have hstep : GFContextStep .useN (.apply "ASimul" []) (plugFrames rest p) := by
          simpa [hmid'] using
            (gfContextStep_of_frames (frs := rest) (GFTopStep.useN p))
        exact (no_useN_step_nullary (f := "ASimul") (by decide)) hstep

lemma useN_step_under_pastSeed
    {cl y : Pattern}
    (h : GFContextStep .useN (pastSeed cl) y) :
    ∃ q, GFContextStep .useN cl q ∧ y = pastSeed q := by
  rcases gfContextStep_decompose h with ⟨frs, p0, q0, htop, hx, hy⟩
  rcases useN_top_shape htop with ⟨p, hp0, hq0⟩
  cases frs with
  | nil =>
      have hhead := congrArg (fun t =>
        match t with
        | .apply g _ => g
        | _ => "") hx
      have : "UseCl" = "UseN" := by
        simp [hp0, pastSeed, plugFrames, useNSeed] at hhead
      exact (False.elim ((by decide : "UseCl" ≠ "UseN") this))
  | cons fr rest =>
      have hhead : "UseCl" = fr.f := by
        have hEq := congrArg (fun t =>
          match t with
          | .apply g _ => g
          | _ => "") hx
        simpa [hp0, pastSeed, plugFrames, plugFrame] using hEq
      have hargs :
          [ .apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []]
          , .apply "PPos" []
          , cl ] = fr.pre ++ plugFrames rest (useNSeed p) :: fr.post := by
        have hEq := congrArg (fun t =>
          match t with
          | .apply _ args => args
          | _ => ([] : List Pattern)) hx
        simpa [hp0, pastSeed, plugFrames, plugFrame] using hEq
      rcases triple_split hargs with h0 | h1 | h2
      · rcases h0 with ⟨hpre, hpost, hmid⟩
        have hmid' :
            .apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []] =
              plugFrames rest (useNSeed p) := by
          simpa [hpre, hpost] using hmid.symm
        have hstep :
            GFContextStep .useN
              (.apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []])
              (plugFrames rest p) := by
          simpa [hmid'] using
            (gfContextStep_of_frames (frs := rest) (GFTopStep.useN p))
        exact (no_useN_step_ttant hstep).elim
      · rcases h1 with ⟨hpre, hpost, hmid⟩
        have hmid' : .apply "PPos" [] = plugFrames rest (useNSeed p) := by
          simpa [hpre, hpost] using hmid.symm
        have hstep : GFContextStep .useN (.apply "PPos" []) (plugFrames rest p) := by
          simpa [hmid'] using
            (gfContextStep_of_frames (frs := rest) (GFTopStep.useN p))
        exact ((no_useN_step_nullary (f := "PPos") (by decide)) hstep).elim
      · rcases h2 with ⟨hpre, hpost, hmid⟩
        have hcl : cl = plugFrames rest (useNSeed p) := by
          simpa [hpre, hpost] using hmid.symm
        subst hcl
        refine ⟨plugFrames rest p, ?_, ?_⟩
        · simpa using gfContextStep_of_frames (frs := rest) (GFTopStep.useN p)
        · simpa [hhead, hq0, pastSeed, plugFrames, plugFrame, hpre, hpost] using hy

lemma useN_step_under_pastOut
    {cl y : Pattern}
    (h : GFContextStep .useN (pastOut cl) y) :
    ∃ q, GFContextStep .useN cl q ∧ y = pastOut q := by
  rcases gfContextStep_decompose h with ⟨frs, p0, q0, htop, hx, hy⟩
  rcases useN_top_shape htop with ⟨p, hp0, hq0⟩
  cases frs with
  | nil =>
      have hhead := congrArg (fun t =>
        match t with
        | .apply g _ => g
        | _ => "") hx
      have : "⊛temporal" = "UseN" := by
        simp [hp0, pastOut, plugFrames, useNSeed] at hhead
      exact (False.elim ((by decide : "⊛temporal" ≠ "UseN") this))
  | cons fr rest =>
      have hhead : "⊛temporal" = fr.f := by
        have hEq := congrArg (fun t =>
          match t with
          | .apply g _ => g
          | _ => "") hx
        simpa [hp0, pastOut, plugFrames, plugFrame] using hEq
      have hargs : [cl, .apply "-1" []] = fr.pre ++ plugFrames rest (useNSeed p) :: fr.post := by
        have hEq := congrArg (fun t =>
          match t with
          | .apply _ args => args
          | _ => ([] : List Pattern)) hx
        simpa [hp0, pastOut, plugFrames, plugFrame] using hEq
      rcases pair_split hargs with h0 | h1
      · rcases h0 with ⟨hpre, hpost, hmid⟩
        have hcl : cl = plugFrames rest (useNSeed p) := by
          simpa [hpre, hpost] using hmid.symm
        subst hcl
        refine ⟨plugFrames rest p, ?_, ?_⟩
        · simpa using gfContextStep_of_frames (frs := rest) (GFTopStep.useN p)
        · simpa [hhead, hq0, pastOut, plugFrames, plugFrame, hpre, hpost] using hy
      · rcases h1 with ⟨hpre, hpost, hmid⟩
        have hmid' : .apply "-1" [] = plugFrames rest (useNSeed p) := by
          simpa [hpre, hpost] using hmid.symm
        have hstep : GFContextStep .useN (.apply "-1" []) (plugFrames rest p) := by
          simpa [hmid'] using
            (gfContextStep_of_frames (frs := rest) (GFTopStep.useN p))
        exact ((no_useN_step_nullary (f := "-1") (by decide)) hstep).elim

lemma past_step_under_useN
    {p y : Pattern}
    (h : GFContextStep .pastTense (useNSeed p) y) :
    ∃ q, GFContextStep .pastTense p q ∧ y = useNSeed q := by
  rcases gfContextStep_decompose h with ⟨frs, p0, q0, htop, hx, hy⟩
  cases htop with
  | pastTense cl =>
      cases frs with
      | nil =>
          simp [useNSeed, plugFrames] at hx
      | cons fr rest =>
          have hhead : "UseN" = fr.f := by
            have hEq := congrArg (fun t =>
              match t with
              | .apply f _ => f
              | _ => "") hx
            simpa [useNSeed, plugFrames, plugFrame] using hEq
          have hargs : [p] = fr.pre ++ plugFrames rest (pastSeed cl) :: fr.post := by
            have hEq := congrArg (fun t =>
              match t with
              | .apply _ args => args
              | _ => ([] : List Pattern)) hx
            simpa [useNSeed, plugFrames, plugFrame] using hEq
          rcases singleton_eq_append_cons hargs with ⟨hpre, hpost, hp⟩
          subst hp
          refine ⟨plugFrames rest (pastOut cl), ?_, ?_⟩
          · simpa [pastSeed, hpre, hpost] using
              (gfContextStep_of_frames (frs := rest) (GFTopStep.pastTense cl))
          · simpa [useNSeed, plugFrames, plugFrame, hpre, hpost, hhead] using hy

/-- Second non-vacuous commuting square: wrapper (`.useN`) with voice (`.activePassive`). -/
theorem gf_nonvacuous_commute_square_useN_activePassive :
    ∃ x y₁ y₂ z,
      gfContextLabeledRewrite.step .useN x y₁ ∧
      gfContextLabeledRewrite.step .activePassive x y₂ ∧
      gfContextLabeledRewrite.step .activePassive y₁ z ∧
      gfContextLabeledRewrite.step .useN y₂ z := by
  refine ⟨voiceWitnessSource, voiceWitnessY1, voiceWitnessY2, voiceWitnessZ, ?_, ?_, ?_, ?_⟩
  · simpa [gfContextLabeledRewrite, voiceWitnessSource, voiceWitnessY1, useNSeed, activeSeed] using
      (GFContextStep.appCtx (f := "Pair") (pre := []) (post := [activeSeed (.fvar "v") (.fvar "np1") (.fvar "np2")])
        (GFContextStep.top (GFTopStep.useN (.fvar "n"))))
  · simpa [gfContextLabeledRewrite, voiceWitnessSource, voiceWitnessY2, useNSeed, activeSeed, activeOut] using
      (GFContextStep.appCtx (f := "Pair") (pre := [useNSeed (.fvar "n")]) (post := [])
        (GFContextStep.top (GFTopStep.activePassive (.fvar "v") (.fvar "np1") (.fvar "np2"))))
  · simpa [gfContextLabeledRewrite, voiceWitnessY1, voiceWitnessZ, activeSeed, activeOut] using
      (GFContextStep.appCtx (f := "Pair") (pre := [.fvar "n"]) (post := [])
        (GFContextStep.top (GFTopStep.activePassive (.fvar "v") (.fvar "np1") (.fvar "np2"))))
  · simpa [gfContextLabeledRewrite, voiceWitnessY2, voiceWitnessZ, useNSeed, activeOut] using
      (GFContextStep.appCtx (f := "Pair") (pre := []) (post := [activeOut (.fvar "v") (.fvar "np2")])
        (GFContextStep.top (GFTopStep.useN (.fvar "n"))))

/-- The second non-vacuous pair is also independent by family. -/
theorem gf_nonvacuous_pair_independent_voice :
    gfObservableKernelCtx.indep.indep .useN .activePassive := by
  simp [gfObservableKernelCtx, gfLabelIndependence, gfIndependent, labelFamily]

/-- Non-vacuous commuting square for an independent pair in context closure:
`.useN` on one argument and `.pastTense` on another argument commute. -/
theorem gf_nonvacuous_commute_square_useN_pastTense :
    ∃ x y₁ y₂ z,
      gfContextLabeledRewrite.step .useN x y₁ ∧
      gfContextLabeledRewrite.step .pastTense x y₂ ∧
      gfContextLabeledRewrite.step .pastTense y₁ z ∧
      gfContextLabeledRewrite.step .useN y₂ z := by
  refine ⟨commuteWitnessSource, commuteWitnessY1, commuteWitnessY2, commuteWitnessZ, ?_, ?_, ?_, ?_⟩
  · simpa [gfContextLabeledRewrite, commuteWitnessSource, commuteWitnessY1, useNSeed, pastSeed] using
      (GFContextStep.appCtx (f := "Pair") (pre := []) (post := [pastSeed (.fvar "cl")])
        (GFContextStep.top (GFTopStep.useN (.fvar "n"))))
  · simpa [gfContextLabeledRewrite, commuteWitnessSource, commuteWitnessY2, useNSeed, pastSeed, pastOut] using
      (GFContextStep.appCtx (f := "Pair") (pre := [useNSeed (.fvar "n")]) (post := [])
        (GFContextStep.top (GFTopStep.pastTense (.fvar "cl"))))
  · simpa [gfContextLabeledRewrite, commuteWitnessY1, commuteWitnessZ, pastSeed, pastOut] using
      (GFContextStep.appCtx (f := "Pair") (pre := [.fvar "n"]) (post := [])
        (GFContextStep.top (GFTopStep.pastTense (.fvar "cl"))))
  · simpa [gfContextLabeledRewrite, commuteWitnessY2, commuteWitnessZ, useNSeed, pastOut] using
      (GFContextStep.appCtx (f := "Pair") (pre := []) (post := [pastOut (.fvar "cl")])
        (GFContextStep.top (GFTopStep.useN (.fvar "n"))))

/-- The non-vacuous witness pair is independent by family. -/
theorem gf_nonvacuous_pair_independent :
    gfObservableKernelCtx.indep.indep .useN .pastTense := by
  simp [gfObservableKernelCtx, gfLabelIndependence, gfIndependent, labelFamily]

/-- Universal context-level commutation for the non-vacuous independent pair
`.useN` and `.pastTense`. -/
theorem gf_context_commuteAt_useN_pastTense :
    CommuteAt gfContextLabeledRewrite .useN .pastTense := by
  intro x y₁ y₂ hUse hPast
  revert y₁ hUse
  induction hPast with
  | top hPastTop =>
      intro y₁ hUse
      rcases past_top_shape hPastTop with ⟨cl, rfl, rfl⟩
      rcases useN_step_under_pastSeed hUse with ⟨q, hq, hy₁⟩
      refine ⟨pastOut q, ?_, ?_⟩
      · simpa [hy₁] using (GFContextStep.top (GFTopStep.pastTense q))
      · exact lift_useN_into_pastOut hq
  | @appCtx f pre post p q hPastInner ih =>
      intro y₁ hUse
      rcases gfContextStep_decompose hUse with ⟨frsU, pU, qU, hUseTop, hxUse, hyUse⟩
      rcases useN_top_shape hUseTop with ⟨u, hpU, hqU⟩
      cases frsU with
      | nil =>
          have hPastAll : GFContextStep .pastTense (useNSeed u) (.apply f (pre ++ q :: post)) := by
            simpa [hxUse, hpU, plugFrames] using
              (GFContextStep.appCtx (f := f) (pre := pre) (post := post) hPastInner)
          rcases past_step_under_useN hPastAll with ⟨r, hr, hy₂⟩
          refine ⟨r, ?_, ?_⟩
          · simpa [hyUse, plugFrames, hqU] using hr
          · simpa [hyUse, hy₂, plugFrames, hqU] using (GFContextStep.top (GFTopStep.useN r))
      | cons frU restU =>
          let hole : Pattern := plugFrames restU (useNSeed u)
          let hole' : Pattern := plugFrames restU u
          have hHead : frU.f = f := by
            have hEq := congrArg (fun t =>
              match t with
              | .apply g _ => g
              | _ => "") hxUse
            simpa [plugFrames, plugFrame] using hEq.symm
          have hArgs : pre ++ p :: post = frU.pre ++ hole :: frU.post := by
            have hEq := congrArg (fun t =>
              match t with
              | .apply _ args => args
              | _ => ([] : List Pattern)) hxUse
            simpa [plugFrames, plugFrame, hpU, hole] using hEq
          have hUseHole : GFContextStep .useN hole hole' := by
            simpa [hole, hole'] using gfContextStep_of_frames (frs := restU) (GFTopStep.useN u)
          rcases one_hole_eq_cases hArgs with hSame | hAfter | hBefore
          · rcases hSame with ⟨hpreEq, hholeEq, hpostEq⟩
            have hSameHole : pre ++ p :: post = pre ++ hole :: post := by
              simpa [hpreEq, hpostEq] using hArgs
            have hpEq : p = hole := same_hole_appCtx_arg_inversion hSameHole
            have hUseOnP : GFContextStep .useN p hole' := by
              simpa [hpEq] using hUseHole
            rcases ih hole' hUseOnP with ⟨zInner, hzPastInner, hzUseInner⟩
            have hy₁' : y₁ = .apply f (pre ++ hole' :: post) := by
              simpa [plugFrames, plugFrame, hpU, hqU, hHead, hpreEq, hpostEq, hole'] using hyUse
            refine ⟨.apply f (pre ++ zInner :: post), ?_, ?_⟩
            · simpa [hy₁'] using
                (GFContextStep.appCtx (f := f) (pre := pre) (post := post) hzPastInner)
            · simpa using
                (GFContextStep.appCtx (f := f) (pre := pre) (post := post) hzUseInner)
          · rcases hAfter with ⟨s, hpreU, hpost⟩
            have hy₁' : y₁ = .apply f (pre ++ p :: (s ++ hole' :: frU.post)) := by
              simpa [plugFrames, plugFrame, hpU, hqU, hHead, hpreU, hpost, hole', List.append_assoc] using hyUse
            have hy₂' : Pattern.apply f (pre ++ q :: post) = Pattern.apply f (pre ++ q :: (s ++ hole :: frU.post)) := by
              simp [hpost, hole]
            refine ⟨.apply f (pre ++ q :: (s ++ hole' :: frU.post)), ?_, ?_⟩
            · simpa [hy₁', List.append_assoc] using
                (GFContextStep.appCtx (f := f) (pre := pre) (post := (s ++ hole' :: frU.post)) hPastInner)
            · have hzUse' :
                  GFContextStep .useN
                    (.apply f (pre ++ q :: (s ++ hole :: frU.post)))
                    (.apply f (pre ++ q :: (s ++ hole' :: frU.post))) := by
                  simpa [List.append_assoc] using
                    (GFContextStep.appCtx (f := f) (pre := (pre ++ q :: s)) (post := frU.post) hUseHole)
              simpa [hy₂'] using hzUse'
          · rcases hBefore with ⟨s, hpre, hpostU⟩
            have hy₁' : y₁ = .apply f (frU.pre ++ hole' :: (s ++ p :: post)) := by
              simpa [plugFrames, plugFrame, hpU, hqU, hHead, hpre, hpostU, hole', List.append_assoc] using hyUse
            have hy₂' : Pattern.apply f (pre ++ q :: post) = Pattern.apply f (frU.pre ++ hole :: (s ++ q :: post)) := by
              simp [hpre, List.append_assoc, hole]
            refine ⟨.apply f (frU.pre ++ hole' :: (s ++ q :: post)), ?_, ?_⟩
            · simpa [hy₁', List.append_assoc] using
                (GFContextStep.appCtx (f := f) (pre := (frU.pre ++ hole' :: s)) (post := post) hPastInner)
            · have hzUse' :
                  GFContextStep .useN
                    (.apply f (frU.pre ++ hole :: (s ++ q :: post)))
                    (.apply f (frU.pre ++ hole' :: (s ++ q :: post))) := by
                  simpa [List.append_assoc] using
                    (GFContextStep.appCtx (f := f) (pre := frU.pre) (post := (s ++ q :: post)) hUseHole)
              simpa [hy₂'] using hzUse'

theorem gf_context_independent_commuting_useN_pastTense :
    (gfObservableKernelCtx.{0}).IndependentCommuting .useN .pastTense :=
  ⟨gf_nonvacuous_pair_independent.{0}, gf_context_commuteAt_useN_pastTense⟩

private def activeCounterSrc : Pattern :=
  activeSeed (.fvar "v") (useNSeed (.fvar "n")) (.fvar "np2")
private def activeCounterYUse : Pattern :=
  activeSeed (.fvar "v") (.fvar "n") (.fvar "np2")
private def activeCounterYAct : Pattern :=
  activeOut (.fvar "v") (.fvar "np2")

lemma no_useN_step_fvar {n : String} {y : Pattern} :
    ¬ GFContextStep .useN (.fvar n) y := by
  intro h
  rcases gfContextStep_decompose h with ⟨frs, p0, q0, htop, hx, hy⟩
  rcases useN_top_shape htop with ⟨p, rfl, rfl⟩
  cases frs with
  | nil =>
      simp [plugFrames, useNSeed] at hx
  | cons fr rest =>
      have htag := congrArg (fun t =>
        match t with
        | .fvar _ => true
        | _ => false) hx
      simp [plugFrames, plugFrame] at htag

lemma no_useN_step_passV2_fvar {v : String} {y : Pattern} :
    ¬ GFContextStep .useN (.apply "PassV2" [.fvar v]) y := by
  intro h
  rcases gfContextStep_decompose h with ⟨frs, p0, q0, htop, hx, hy⟩
  rcases useN_top_shape htop with ⟨p, hxUse, hyUse⟩
  cases frs with
  | nil =>
      have hhead := congrArg (fun t =>
        match t with
        | .apply f _ => f
        | _ => "") hx
      simp [hxUse, plugFrames, useNSeed] at hhead
  | cons fr rest =>
      have hargs : [.fvar v] = fr.pre ++ plugFrames rest (useNSeed p) :: fr.post := by
        have hEq := congrArg (fun t =>
          match t with
          | .apply _ args => args
          | _ => ([] : List Pattern)) hx
        simpa [hxUse, plugFrames, plugFrame] using hEq
      rcases singleton_eq_append_cons hargs with ⟨hpre, hpost, hmid⟩
      have hv : .fvar v = plugFrames rest (useNSeed p) := by simpa [hpre, hpost] using hmid
      have hstep : GFContextStep .useN (.fvar v) (plugFrames rest p) := by
        simpa [hv] using
          (gfContextStep_of_frames (frs := rest) (GFTopStep.useN p))
      exact (no_useN_step_fvar hstep)

lemma no_useN_step_activeCounterYAct {y : Pattern} :
    ¬ GFContextStep .useN activeCounterYAct y := by
  intro h
  rcases gfContextStep_decompose h with ⟨frs, p0, q0, htop, hx, hy⟩
  rcases useN_top_shape htop with ⟨p, hxUse, hyUse⟩
  cases frs with
  | nil =>
      have hhead := congrArg (fun t =>
        match t with
        | .apply f _ => f
        | _ => "") hx
      simp [hxUse, activeCounterYAct, activeOut, plugFrames, useNSeed] at hhead
  | cons fr rest =>
      have hargs :
          [.fvar "np2", .apply "PassV2" [.fvar "v"]] =
            fr.pre ++ plugFrames rest (useNSeed p) :: fr.post := by
        have hEq := congrArg (fun t =>
          match t with
          | .apply _ args => args
          | _ => ([] : List Pattern)) hx
        simpa [hxUse, activeCounterYAct, activeOut, plugFrames, plugFrame] using hEq
      rcases pair_split hargs with h0 | h1
      · rcases h0 with ⟨hpre, hpost, hmid⟩
        have hv : .fvar "np2" = plugFrames rest (useNSeed p) := by
          simpa [hpre, hpost] using hmid.symm
        have hstep : GFContextStep .useN (.fvar "np2") (plugFrames rest p) := by
          simpa [hv] using
            (gfContextStep_of_frames (frs := rest) (GFTopStep.useN p))
        exact no_useN_step_fvar hstep
      · rcases h1 with ⟨hpre, hpost, hmid⟩
        have hv : .apply "PassV2" [.fvar "v"] = plugFrames rest (useNSeed p) := by
          simpa [hpre, hpost] using hmid.symm
        have hstep : GFContextStep .useN (.apply "PassV2" [.fvar "v"]) (plugFrames rest p) := by
          simpa [hv] using
            (gfContextStep_of_frames (frs := rest) (GFTopStep.useN p))
        exact no_useN_step_passV2_fvar hstep

/-- Regression theorem: unlike `.useN`/`.pastTense`, the pair
`.useN`/`.activePassive` is not universally commuting under context closure. -/
theorem gf_context_not_commuteAt_useN_activePassive :
    ¬ CommuteAt gfContextLabeledRewrite .useN .activePassive := by
  intro hComm
  have hUse :
      gfContextLabeledRewrite.step .useN activeCounterSrc activeCounterYUse := by
    simpa [gfContextLabeledRewrite, activeCounterSrc, activeCounterYUse, activeSeed, useNSeed] using
      (GFContextStep.appCtx
        (f := "PredVP")
        (pre := [])
        (post := [.apply "ComplSlash" [.apply "SlashV2a" [.fvar "v"], .fvar "np2"]])
        (GFContextStep.top (GFTopStep.useN (.fvar "n"))))
  have hAct :
      gfContextLabeledRewrite.step .activePassive activeCounterSrc activeCounterYAct := by
    simpa [gfContextLabeledRewrite, activeCounterSrc, activeCounterYAct, activeSeed, activeOut] using
      (GFContextStep.top (GFTopStep.activePassive (.fvar "v") (useNSeed (.fvar "n")) (.fvar "np2")))
  rcases hComm activeCounterSrc activeCounterYUse activeCounterYAct hUse hAct with ⟨z, hzAct, hzUse⟩
  exact no_useN_step_activeCounterYAct hzUse

end Mettapedia.Languages.GF.SemanticKernelConfluence
