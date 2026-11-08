import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationReflection

/-!
# Principal answers do not survive the translation without eta

Take two unary metavariables `m, n` of one sort and the pattern equation `m(x) ≐ n(x)`.

* **Second order** (`pattern_principal`): the assignment `m, n ↦ g(x)` into a frame with one unary
  metavariable `g` is a principal answer. A second-order solution is determined by its images, and
  the equation says exactly that the two images are equal.
* **Dependent frames** (`pattern_no_principal`): the translated equation has **no** principal answer
  in `Dependent.frames`, over any rule package with no declared root computation and a symmetric
  head equality. The solutions `m ↦ g, n ↦ λx. g x` and `m ↦ λx. g x, n ↦ g` (into the telescope
  `g : Π s. s`) both solve it, and no single solution factors both on every judged term: a common
  answer would make the images of `m` and `n` convertible, and then `g` would convert to its eta
  expansion. Conversion has no eta for products, so it does not.

The second-order instance only observes metavariables applied to their parameters; the dependent
instance also observes the bare variable `m : Π s. s`, and there `m` and `λx. m x` differ.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace Translation

open CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type}

/-! ## Conversion facts under Church–Rosser -/

/-- The eta expansion `λx. u x`. -/
def etaOf {n : Nat} (u : Tm Head n) : Tm Head n := .lam (.app (rename wk u) (.var 0))

section Conversion

variable {rules : Rules Head} (cr : ConversionCoherence.ChurchRosser rules)
  (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ rules.computation.step a b)

theorem conv_of_steps {n : Nat} {a b : Tm Head n}
    (steps : Relation.ReflTransGen (StepCore rules.computation rules.headEq) a b) :
    Conv rules.headEq a b rules.computation := by
  induction steps with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

include noRoot in
/-- Every reduct of an abstraction is an abstraction of a reduct. -/
theorem lam_steps {n : Nat} {body : Tm Head (n + 1)} {target : Tm Head n}
    (steps : Relation.ReflTransGen (StepCore rules.computation rules.headEq) (.lam body) target) :
    ∃ body', target = .lam body' ∧
      Relation.ReflTransGen (StepCore rules.computation rules.headEq) body body' := by
  induction steps with
  | refl => exact ⟨body, rfl, .refl⟩
  | tail _ last ih =>
      obtain ⟨middle, rfl, toMiddle⟩ := ih
      cases last with
      | root h => exact (noRoot _ _ h).elim
      | congLam inner => exact ⟨_, rfl, .tail toMiddle inner⟩

include cr noRoot in
/-- A variable does not convert to an abstraction. -/
theorem var_not_conv_lam {n : Nat} (x : Fin n) (body : Tm Head (n + 1)) :
    ¬ Conv rules.headEq (.var x) (.lam body) rules.computation := by
  intro conv
  obtain ⟨common, fromVar, fromLam⟩ := cr conv
  have same := eq_of_steps_normal (var_normal noRoot x) fromVar
  obtain ⟨_, isLam, _⟩ := lam_steps noRoot fromLam
  rw [← same] at isLam
  cases isLam

include cr noRoot in
/-- Conversion of abstractions is conversion of their bodies. -/
theorem conv_lam_inj {n : Nat} {body body' : Tm Head (n + 1)}
    (conv : Conv rules.headEq (.lam body) (.lam body') rules.computation) :
    Conv rules.headEq body body' rules.computation := by
  obtain ⟨common, first, second⟩ := cr conv
  obtain ⟨reduct, rfl, toReduct⟩ := lam_steps noRoot first
  obtain ⟨reduct', same, toReduct'⟩ := lam_steps noRoot second
  cases same
  exact .trans _ _ _ (conv_of_steps toReduct) (.symm _ _ (conv_of_steps toReduct'))

include noRoot in
/-- Applying a term that never converts to an abstraction to a variable only reduces the term. -/
theorem app_var_steps {n : Nat} {t : Tm Head n} (x : Fin n)
    (neverLam : ∀ body, ¬ Conv rules.headEq t (.lam body) rules.computation) {target : Tm Head n}
    (steps : Relation.ReflTransGen (StepCore rules.computation rules.headEq) (.app t (.var x)) target) :
    ∃ t', target = .app t' (.var x) ∧
      Relation.ReflTransGen (StepCore rules.computation rules.headEq) t t' := by
  induction steps with
  | refl => exact ⟨t, rfl, .refl⟩
  | tail _ last ih =>
      obtain ⟨middle, rfl, toMiddle⟩ := ih
      cases last with
      | betaPi body _ => exact (neverLam body (conv_of_steps toMiddle)).elim
      | root h => exact (noRoot _ _ h).elim
      | congAppFun inner => exact ⟨_, rfl, .tail toMiddle inner⟩
      | congAppArg inner => exact (var_normal noRoot x _ inner).elim

/-- Weakening reflects convertibility to an abstraction. -/
theorem weaken_never_lam {n : Nat} {t : Tm Head n}
    (neverLam : ∀ body, ¬ Conv rules.headEq t (.lam body) rules.computation) :
    ∀ body, ¬ Conv rules.headEq (rename wk t) (.lam body) rules.computation := by
  intro body conv
  have back := Conv.substitute (subst0 (.const .anonymous)) conv
  have restored : subst (subst0 (.const .anonymous)) (rename wk t) = t :=
    inst0_rename_wk (.const .anonymous) t
  rw [restored] at back
  exact neverLam _ back

include cr noRoot in
/-- **The eta core.** If `λx. a x` and `λx. b x` convert, a substitution sends `a` to a variable and
`b` to its eta expansion, and another sends `b` to a variable, then conversion is inconsistent. -/
theorem eta_pattern_contradiction {θ k : Nat} {a b : Tm Head θ} {ρ₁ ρ₂ : Sub Head θ k} (x : Fin k)
    (sound : Conv rules.headEq (etaOf a) (etaOf b) rules.computation)
    (first₀ : Conv rules.headEq (.var x) (subst ρ₁ a) rules.computation)
    (first₁ : Conv rules.headEq (etaOf (.var x)) (subst ρ₁ b) rules.computation)
    (second₁ : Conv rules.headEq (.var x) (subst ρ₂ b) rules.computation) : False := by
  have neverLamA : ∀ body, ¬ Conv rules.headEq a (.lam body) rules.computation := by
    intro body conv
    have moved := Conv.substitute ρ₁ conv
    exact var_not_conv_lam cr noRoot x _ (.trans _ _ _ first₀ moved)
  have neverLamB : ∀ body, ¬ Conv rules.headEq b (.lam body) rules.computation := by
    intro body conv
    have moved := Conv.substitute ρ₂ conv
    exact var_not_conv_lam cr noRoot x _ (.trans _ _ _ second₁ moved)
  have bodies := conv_lam_inj cr noRoot sound
  obtain ⟨common, fromA, fromB⟩ := cr bodies
  obtain ⟨a', rfl, toA⟩ := app_var_steps noRoot 0 (weaken_never_lam neverLamA) fromA
  obtain ⟨b', same, toB⟩ := app_var_steps noRoot 0 (weaken_never_lam neverLamB) fromB
  obtain ⟨heads, _⟩ := Tm.app.inj same
  subst heads
  have weakened : Conv rules.headEq (rename wk a) (rename wk b) rules.computation :=
    .trans _ _ _ (conv_of_steps toA) (.symm _ _ (conv_of_steps toB))
  have back := Conv.substitute (subst0 (.const .anonymous)) weakened
  rw [show subst (subst0 (.const .anonymous)) (rename wk a) = a from
      inst0_rename_wk (.const .anonymous) a,
    show subst (subst0 (.const .anonymous)) (rename wk b) = b from
      inst0_rename_wk (.const .anonymous) b] at back
  have imaged := Conv.substitute ρ₁ back
  have clash : Conv rules.headEq (.var x) (etaOf (.var x)) rules.computation :=
    .trans _ _ _ first₀ (.trans _ _ _ imaged (.symm _ _ first₁))
  exact var_not_conv_lam cr noRoot x _ clash

end Conversion

/-! ## The pattern equation -/

variable {S : Binding.Signature} (names : BindingSignatureEmbedding.Names S)
  {rules : Rules Head} (realization : BindingSignatureEmbedding.Realization names rules)
  (s : S.Srt)

/-- Two unary metavariables of sort `s`. -/
abbrev pairFrame : List (Binding.MetaArity S) := [([s], s), ([s], s)]

/-- One unary metavariable of sort `s`. -/
abbrev unaryFrame : List (Binding.MetaArity S) := [([s], s)]

/-- The metavariable `m`. -/
def mIdx : Fin (pairFrame s).length := ⟨0, by simp⟩

/-- The metavariable `n`. -/
def nIdx : Fin (pairFrame s).length := ⟨1, by simp⟩

/-- The metavariable `g`. -/
def gIdx : Fin (unaryFrame s).length := ⟨0, by simp⟩

/-- The occurrence `m(x̄)` of a metavariable applied to its parameters. -/
def occurrence (M : List (Binding.MetaArity S)) (i : Fin M.length) :
    Binding.ContextualFamily.Observation S M.get :=
  ⟨(M.get i).1, (M.get i).2, Binding.ContextualFamily.generator M.get i⟩

/-- **The pattern equation** `m(x) ≐ n(x)`. -/
def patternStore : EquationStore (Binding.ContextualFamily.Observation S (pairFrame s).get) :=
  [(occurrence (pairFrame s) (mIdx s), occurrence (pairFrame s) (nIdx s))]

/-! ### Dependent solutions -/

/-- The closed type `Π s. s` of a unary metavariable. -/
abbrev unaryType : Tm Head 0 := BindingSignatureEmbedding.bindingType names [s] s

include realization in
theorem eta_typing {Δ : Context rules} {u : Tm Head Δ.arity}
    (typed : FormationSensitive.Typing rules Δ.raw u (liftClosed (unaryType names s))) :
    FormationSensitive.Typing rules Δ.raw (etaOf u) (liftClosed (unaryType names s)) := by
  have formed := FormationCheckedTelescopePrograms.liftClosed_typing
    (realization.toSortRealization.bindingType_formed [s] s) Δ.raw
  change FormationSensitive.Typing rules Δ.raw
    (liftClosed (BindingSignatureEmbedding.closedArrow (BindingSignatureEmbedding.sortType names s)
      (BindingSignatureEmbedding.sortType names s))) (liftClosed (.head _)) at formed
  change FormationSensitive.Typing rules Δ.raw u
    (liftClosed (BindingSignatureEmbedding.closedArrow (BindingSignatureEmbedding.sortType names s)
      (BindingSignatureEmbedding.sortType names s))) at typed
  rw [BindingSignatureEmbedding.liftClosed_closedArrow] at formed typed
  have weakened := typed.weaken (extension := liftClosed (BindingSignatureEmbedding.sortType names s))
  have applied := FormationSensitive.Typing.appElim weakened
    (FormationSensitive.Typing.var (R := rules)
      (Γ := .snoc Δ.raw (liftClosed (BindingSignatureEmbedding.sortType names s))) 0)
  have abstracted := FormationSensitive.Typing.lamIntro formed realization.universeIs applied
  change FormationSensitive.Typing rules Δ.raw (etaOf u)
    (liftClosed (BindingSignatureEmbedding.closedArrow (BindingSignatureEmbedding.sortType names s)
      (BindingSignatureEmbedding.sortType names s)))
  rw [BindingSignatureEmbedding.liftClosed_closedArrow]
  exact abstracted

/-- A solution of the two metavariables by two terms of type `Π s. s`. -/
def twoHom {Δ : Context rules} (u₀ u₁ : Tm Head Δ.arity)
    (typed₀ : FormationSensitive.Typing rules Δ.raw u₀ (liftClosed (unaryType names s)))
    (typed₁ : FormationSensitive.Typing rules Δ.raw u₁ (liftClosed (unaryType names s))) :
    Δ ⟶ ctxOf names realization (pairFrame s) where
  substitution := consSub u₀ (consSub u₁ (fun k => k.elim0))
  typed := by
    intro (i : Fin (pairFrame s).length)
    show FormationSensitive.Typing rules Δ.raw _
      (subst _ (Ctx.lookup (metaCtx names (pairFrame s)) i))
    rw [metaCtx_lookup, subst_liftClosed]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact typed₀
    · refine Fin.cases ?_ (fun k => k.elim0) j
      exact typed₁

/-- The variable `g` of the unary telescope has type `Π s. s`. -/
theorem unary_var_typing :
    FormationSensitive.Typing rules (ctxOf names realization (unaryFrame s)).raw (.var (gIdx s))
      (liftClosed (unaryType names s)) := by
  have typed := FormationSensitive.Typing.var (R := rules)
    (Γ := metaCtx (Head := Head) names (unaryFrame s)) (gIdx s)
  rw [metaCtx_lookup] at typed
  exact typed

/-- The solution `m ↦ g, n ↦ λx. g x`. -/
def firstSolution :
    ctxOf names realization (unaryFrame s) ⟶ ctxOf names realization (pairFrame s) :=
  twoHom names realization s (.var (gIdx s)) (etaOf (.var (gIdx s)))
    (unary_var_typing names realization s)
    (eta_typing names realization s (unary_var_typing names realization s))

/-- The solution `m ↦ λx. g x, n ↦ g`. -/
def secondSolution :
    ctxOf names realization (unaryFrame s) ⟶ ctxOf names realization (pairFrame s) :=
  twoHom names realization s (etaOf (.var (gIdx s))) (.var (gIdx s))
    (eta_typing names realization s (unary_var_typing names realization s))
    (unary_var_typing names realization s)

/-- Under a solution `μ`, the translated pattern equation reads `λx. μ(m) x ≐ λx. μ(n) x`. -/
theorem pattern_models_iff {Δ : Context rules} (τ : Δ ⟶ ctxOf names realization (pairFrame s)) :
    (Dependent.frames rules).Models τ ((translation names realization).store (patternStore s)) ↔
      Conv rules.headEq (etaOf (τ.substitution (mIdx s))) (etaOf (τ.substitution (nIdx s)))
        rules.computation := by
  constructor
  · intro solved
    exact (solved _ (List.mem_singleton_self _)).2
  · intro conv e member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨.refl _, conv⟩

theorem firstSolution_models :
    (Dependent.frames rules).Models (firstSolution names realization s)
      ((translation names realization).store (patternStore s)) := by
  rw [pattern_models_iff]
  exact Conv.congLam (.symm _ _ (.rel _ _ (StepCore.betaPi (.app (.var 2) (.var 0)) (.var 0))))

theorem secondSolution_models :
    (Dependent.frames rules).Models (secondSolution names realization s)
      ((translation names realization).store (patternStore s)) := by
  rw [pattern_models_iff]
  exact Conv.congLam (.rel _ _ (StepCore.betaPi (.app (.var 2) (.var 0)) (.var 0)))

/-- **No principal answer at dependent frames.** Over a rule package with no declared root
computation and a symmetric head equality, the translated pattern equation `m(x) ≐ n(x)` has no
principal answer: no solution through which every solution factors on every judged term. -/
theorem pattern_no_principal (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) :
    ¬ ∃ (Θ : Context rules) (answer : Θ ⟶ ctxOf names realization (pairFrame s)),
      (Dependent.frames rules).Principal (a := ctxOf names realization (pairFrame s)) (m := Θ)
        ((translation names realization).store (patternStore s)) answer := by
  rintro ⟨Θ, answer, principal⟩
  have cr : ConversionCoherence.ChurchRosser rules :=
    EmptyRootConversion.churchRosser rules empty symmetric
  have noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ rules.computation.step a b := by
    intro n a b step
    rw [empty] at step
    exact step
  have sound := (pattern_models_iff names realization s answer).mp principal.sound
  obtain ⟨residual₁, through₁⟩ := principal.factors _ (firstSolution names realization s)
    (firstSolution_models names realization s)
  obtain ⟨residual₂, through₂⟩ := principal.factors _ (secondSolution names realization s)
    (secondSolution_models names realization s)
  have pointwise₁ := Dependent.pointwise_of_convertible_reindex through₁
  have pointwise₂ := Dependent.pointwise_of_convertible_reindex through₂
  exact eta_pattern_contradiction cr noRoot (gIdx s) sound (pointwise₁ (mIdx s)) (pointwise₁ (nIdx s))
    (pointwise₂ (nIdx s))

/-! ### The second-order principal answer -/

/-- The image `g(x)`. -/
def unaryOccurrence : Binding.Term (Sig S (unaryFrame s)) [s] s :=
  Binding.ContextualFamily.generator (unaryFrame s).get ⟨0, by simp⟩

/-- The assignment `m, n ↦ g(x)`. -/
def collapse : Binding.ContextualFamily.Assignment (S := S) (pairFrame s).get (unaryFrame s).get
  | ⟨0, _⟩ => unaryOccurrence s
  | ⟨1, _⟩ => unaryOccurrence s
  | ⟨_ + 2, h⟩ => absurd h (by simp)

/-- The residual `g ↦ f(m)` of a solution `f`. -/
def residualOf {N : List (Binding.MetaArity S)}
    (f : Binding.ContextualFamily.Assignment (S := S) (pairFrame s).get N.get) :
    Binding.ContextualFamily.Assignment (S := S) (unaryFrame s).get N.get
  | ⟨0, _⟩ => f (mIdx s)
  | ⟨_ + 1, h⟩ => absurd h (by simp)

theorem pattern_listModels_iff {N : List (Binding.MetaArity S)}
    (f : Binding.ContextualFamily.Assignment (S := S) (pairFrame s).get N.get) :
    (listFrames S).Models (a := pairFrame s) (b := N) f (patternStore s) ↔
      f (mIdx s) = f (nIdx s) := by
  have images : ∀ i, Binding.ContextualFamily.instantiate f
      (Binding.ContextualFamily.generator (pairFrame s).get i) = f i :=
    fun i => Binding.ContextualFamily.instantiate_generator f i
  constructor
  · intro solved
    have equation := solved _ (List.mem_singleton_self _)
    change Binding.ContextualFamily.observe (Binding.ContextualFamily.instantiate f
        (Binding.ContextualFamily.generator (pairFrame s).get (mIdx s))) =
      Binding.ContextualFamily.observe (Binding.ContextualFamily.instantiate f
        (Binding.ContextualFamily.generator (pairFrame s).get (nIdx s))) at equation
    rw [images, images] at equation
    exact Binding.ContextualFamily.observe_injective equation
  · intro same e member
    obtain rfl := List.mem_singleton.mp member
    change Binding.ContextualFamily.observe (Binding.ContextualFamily.instantiate f
        (Binding.ContextualFamily.generator (pairFrame s).get (mIdx s))) =
      Binding.ContextualFamily.observe (Binding.ContextualFamily.instantiate f
        (Binding.ContextualFamily.generator (pairFrame s).get (nIdx s)))
    rw [images, images]
    exact congrArg Binding.ContextualFamily.observe same

/-- **The second-order pattern equation has a principal answer**: `m, n ↦ g(x)`. -/
theorem pattern_principal :
    (listFrames S).Principal (a := pairFrame s) (m := unaryFrame s) (patternStore s)
      (collapse s) where
  sound := (pattern_listModels_iff s (collapse s)).mpr rfl
  factors := by
    intro N f solved
    have same := (pattern_listModels_iff s f).mp solved
    refine ⟨residualOf s f, fun t => ?_⟩
    have pointwise : f =
        Binding.ContextualFamily.Assignment.compose (residualOf s f) (collapse s) := by
      funext i
      rcases i with ⟨_ | _ | k, h⟩
      · exact (Binding.ContextualFamily.instantiate_generator (residualOf s f) ⟨0, by simp⟩).symm
      · exact same.symm.trans
          (Binding.ContextualFamily.instantiate_generator (residualOf s f) ⟨0, by simp⟩).symm
      · exact absurd h (by simp)
    show Binding.ContextualFamily.instantiateObservation f t =
      Binding.ContextualFamily.instantiateObservation
        (Binding.ContextualFamily.Assignment.compose (residualOf s f) (collapse s)) t
    rw [← pointwise]

/-! ### Principal answers are not preserved -/

/-- A map of frame instances **preserves principal answers** when the image of every principal answer
is principal for the translated store. -/
def PreservesPrincipal {Obj Obj' : Type _} {Tm : Obj → Type _} {Hom : Obj → Obj → Type _}
    {Tm' : Obj' → Type _} {Hom' : Obj' → Obj' → Type _} {X : Frames Tm Hom}
    {Y : Frames Tm' Hom'} (Φ : FrameMap X Y) : Prop :=
  ∀ (a m : Obj) (K : EquationStore (Tm a)) (answer : Hom a m),
    X.Principal K answer → Y.Principal (Φ.store K) (Φ.hom answer)

include s in
/-- **The translation does not preserve principal answers**, as soon as the signature has a sort:
the second-order principal answer of `m(x) ≐ n(x)` has no principal counterpart. -/
theorem translation_not_preservesPrincipal (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) : ¬ PreservesPrincipal (translation names realization) := by
  intro preserves
  exact pattern_no_principal names realization s empty symmetric
    ⟨_, _, preserves _ _ _ _ (pattern_principal s)⟩

end Translation

#print axioms Translation.eta_pattern_contradiction
#print axioms Translation.firstSolution_models
#print axioms Translation.secondSolution_models
#print axioms Translation.pattern_no_principal
#print axioms Translation.pattern_principal
#print axioms Translation.translation_not_preservesPrincipal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
