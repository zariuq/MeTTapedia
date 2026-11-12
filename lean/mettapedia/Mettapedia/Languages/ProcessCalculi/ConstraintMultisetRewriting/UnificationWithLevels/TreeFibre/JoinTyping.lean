import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinContexts

/-!
# The join widening: a normal form typed over two telescopes is typed over their join

Let `J` join `Γ₁` and `Γ₂` (`JoinOf`): the same telescope, with a least upper bound of the two universes wherever
they declare different universes. **A normal term of a type over `Γ₁` and over `Γ₂` has that type over `J`**
(`typed_join`), whenever the type is a type over `J`. Its universe declarations need not be comparable: over `x : U_a`
and over `x : U_b` with level variables `a`, `b`, a normal form is typed over `x : U_{max a b}`.

The proof runs the kernel's bidirectional typing (`KernelTyping`), which is complete on normal forms
(`normal_checked`) and sound, and inducts on the normal term.

* **Synthesis joins** (`SynthJoin`): synthesized types are syntax-directed, so the two derivations have the same
  shape; the synthesized types over `Γ₁`, `Γ₂` and `J` are the same type, or universes with the one over `J` a least
  upper bound of the other two (`TJoin`). A variable declared at two universes synthesizes their join; a type former
  synthesizes the join of its parts' universes; an elimination's head is never such a variable, since a universe is
  not a function or pair type, so its type is the same in the three telescopes and its weak-head form too.
* **Checking joins** (`CheckJoin`): a synthesizable term has its principal type below the expected type over `Γ₁`
  and `Γ₂`, hence over `J` (`below_wide` when the principal type is the same; the universe order and the weak-head
  form of the expected type when it is a universe); an abstraction, a pair or a reflexivity proof is checked against
  the weak-head form of the expected type, which weak-head reduction computes alike in the three telescopes.

The hypothesis that the term is normal excludes β-redexes, whose kernel rule chooses an annotation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentCumulative ContextualDependentNormalChecking

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Joined types -/

section Joined

/-- **`T` joins the synthesized types `T₁` and `T₂`**: the same type, or universes with `T`'s a least upper bound. -/
def TJoin (R : Rules Head) {n : Nat} (T₁ T₂ T : Tm Head n) : Prop :=
  (T = T₁ ∧ T = T₂) ∨ ∃ u v w, T₁ = .head u ∧ T₂ = .head v ∧ T = .head w ∧ R.isUniverse u ∧ R.isUniverse v ∧
    R.isUniverse w ∧ IsLub R w u v

variable {S : Setting Head L}

theorem isLub_of_join (algebra : CumulativeAlgebra S.R) {u v w : Head} (joined : S.R.join u v w) :
    IsLub S.R w u v :=
  ⟨(S.levels.join_upper joined).1, (S.levels.join_upper joined).2,
    fun _ _ cu cv => algebra.join_least joined cu cv⟩

theorem isLub_self {u : Head} (hu : S.R.isUniverse u) : IsLub S.R u u u :=
  ⟨S.levels.cumulative_refl hu, S.levels.cumulative_refl hu, fun _ _ c _ => c⟩

/-- **Joins of joins**: the join of the least upper bounds of the parts is a least upper bound of the joins. -/
theorem isLub_join4 (algebra : CumulativeAlgebra S.R) {u₁ v₁ w₁ u₂ v₂ w₂ uJ vJ w : Head}
    (j₁ : S.R.join u₁ v₁ w₁) (j₂ : S.R.join u₂ v₂ w₂) (lubU : IsLub S.R uJ u₁ u₂) (lubV : IsLub S.R vJ v₁ v₂)
    (j : S.R.join uJ vJ w) : IsLub S.R w w₁ w₂ := by
  obtain ⟨uw, vw⟩ := S.levels.join_upper j
  refine ⟨algebra.join_least j₁ (algebra.trans lubU.1 uw) (algebra.trans lubV.1 vw),
    algebra.join_least j₂ (algebra.trans lubU.2.1 uw) (algebra.trans lubV.2.1 vw), fun r hr c₁ c₂ => ?_⟩
  obtain ⟨u₁w₁, v₁w₁⟩ := S.levels.join_upper j₁
  obtain ⟨u₂w₂, v₂w₂⟩ := S.levels.join_upper j₂
  exact algebra.join_least j (lubU.2.2 r hr (algebra.trans u₁w₁ c₁) (algebra.trans u₂w₂ c₂))
    (lubV.2.2 r hr (algebra.trans v₁w₁ c₁) (algebra.trans v₂w₂ c₂))

/-- A head reaches only itself by weak-head reduction. -/
theorem whRed_head {n : Nat} {h : Head} {X : Tm Head n} (red : WhRed S.R S.roles (.head h) X) : X = .head h := by
  rcases Relation.ReflTransGen.cases_head red with same | ⟨c, step, _⟩
  · exact same.symm
  · exact absurd step (head_whnf S.shape h c)

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)

include facts roots in
/-- **Universes of joined synthesized types**: when the synthesized types reduce to universes over `Γ₁` and `Γ₂`, the
joined one reduces to a least upper bound of them over `J`. -/
theorem universe_of_tjoin {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} (formedJ : CtxFormed S.R J) {TA₁ TA₂ TA : Tm Head n}
    {u₁ u₂ : Head} (r₁ : RedTy S.R S.roles Γ₁ TA₁ (.head u₁)) (r₂ : RedTy S.R S.roles Γ₂ TA₂ (.head u₂))
    (hu₁ : S.R.isUniverse u₁) (isTA : IsType S.R J TA) (joined : TJoin S.R TA₁ TA₂ TA) :
    ∃ uJ, RedTy S.R S.roles J TA (.head uJ) ∧ S.R.isUniverse uJ ∧ IsLub S.R uJ u₁ u₂ := by
  rcases joined with ⟨rfl, rfl⟩ | ⟨a₁, a₂, aJ, rfl, rfl, rfl, _, _, haJ, lub⟩
  · have same := WhRed.whnf_unique S.shape r₁.red r₂.red (head_whnf S.shape _) (head_whnf S.shape _)
    cases same
    exact ⟨u₁, redTy_wide facts roots formedJ r₁.red isTA, hu₁, isLub_self hu₁⟩
  · have e₁ := whRed_head r₁.red
    have e₂ := whRed_head r₂.red
    cases e₁
    cases e₂
    exact ⟨aJ, RedTy.refl isTA, haJ, lub⟩

/-- **A joined type whose weak-head form is not a head is the same type** in the three telescopes. -/
theorem same_of_tjoin {n : Nat} {F₁ F₂ F X : Tm Head n} (red : WhRed S.R S.roles F₁ X) (notHead : ∀ h, X ≠ .head h)
    (joined : TJoin S.R F₁ F₂ F) : F = F₁ ∧ F = F₂ := by
  rcases joined with same | ⟨u, _, _, rfl, _, _, _, _, _, _⟩
  · exact same
  · exact absurd (whRed_head red) (notHead u)

/-- A universe is not of rigid shape. -/
theorem rigidShape_not_universe {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    (shape : RigidShape S.R S.roles Γ A) : ∀ {u : Head}, A = .head u → S.R.isUniverse u → False := by
  induction shape with
  | head nh => intro u e hu; cases e; exact nh hu
  | neutral nA => intro u e _; exact nA.not_former.1 u e
  | id => intro u e; cases e
  | inductiveType _ => intro u e; cases e
  | pi _ _ => intro u e; cases e
  | sigma _ _ _ _ => intro u e; cases e
  | red r _ ih =>
      intro u e hu
      subst e
      exact ih (whRed_head r.red) hu

include facts roots in
/-- **Rigid shape is kept in a telescope where the type is a type.** -/
theorem RigidShape.wide {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (shape : RigidShape S.R S.roles Γ A) :
    ∀ {W : Ctx Head n}, CtxFormed S.R W → IsType S.R W A → RigidShape S.R S.roles W A := by
  induction shape with
  | head nh => intro _ _ _; exact .head nh
  | neutral nA => intro _ _ _; exact .neutral nA
  | id => intro _ _ _; exact .id
  | inductiveType role => intro _ _ _; exact .inductiveType role
  | pi _ ih =>
      intro W formedW isPi
      obtain ⟨isA, isB⟩ := IsType.pi_parts isPi
      exact .pi (ih (formedW.snoc isA) isB)
  | sigma _ _ ihA ihB =>
      intro W formedW isSigma
      obtain ⟨isA, isB⟩ := IsType.sigma_parts isSigma
      exact .sigma (ihA formedW isA) (ihB (formedW.snoc isA) isB)
  | red r _ ih =>
      intro W formedW isA
      have rW := redTy_wide facts roots formedW r.red isA
      exact .red rW (ih formedW rW.targetType)

end Joined

/-! ## The join of typings -/

section Typing

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')

/-- Synthesis joins at `t`. -/
def SynthJoin {n : Nat} (t : Tm Head n) : Prop :=
  ∀ {Γ₁ Γ₂ J : Ctx Head n} {T₁ T₂ : Tm Head n}, JoinOf S.R Γ₁ Γ₂ J → CtxFormed S.R Γ₁ → CtxFormed S.R Γ₂ →
    CtxFormed S.R J → Normal (S := S) t → Synth S.R S.roles Γ₁ t T₁ → Synth S.R S.roles Γ₂ t T₂ →
      ∃ T, Synth S.R S.roles J t T ∧ TJoin S.R T₁ T₂ T

/-- Typing joins at `t`. -/
def CheckJoin {n : Nat} (t : Tm Head n) : Prop :=
  ∀ {Γ₁ Γ₂ J : Ctx Head n} {E : Tm Head n}, JoinOf S.R Γ₁ Γ₂ J → CtxFormed S.R Γ₁ → CtxFormed S.R Γ₂ →
    CtxFormed S.R J → Normal (S := S) t → Typed S.R Γ₁ t E → Typed S.R Γ₂ t E → IsType S.R J E →
      Typed S.R J t E

include facts roots heads algebra rigid complete headsTyped in
/-- **Checking from synthesis**: a synthesizable term whose synthesis joins has every common type over `J`. -/
theorem check_of_synth {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} (j : JoinOf S.R Γ₁ Γ₂ J) (formed₁ : CtxFormed S.R Γ₁)
    (formed₂ : CtxFormed S.R Γ₂) (formedJ : CtxFormed S.R J) {t E : Tm Head n}
    (fragment : Bidirectional .synth t)
    (synth : ∀ {T₁ T₂ : Tm Head n}, Synth S.R S.roles Γ₁ t T₁ → Synth S.R S.roles Γ₂ t T₂ →
      ∃ T, Synth S.R S.roles J t T ∧ TJoin S.R T₁ T₂ T)
    (typed₁ : Typed S.R Γ₁ t E) (typed₂ : Typed S.R Γ₂ t E) (isE : IsType S.R J E) : Typed S.R J t E := by
  have completeSynth : KernelComplete S .synth t := Bidirectional.complete facts algebra headsTyped fragment
  obtain ⟨T₁, s₁⟩ := completeSynth formed₁ typed₁
  obtain ⟨T₂, s₂⟩ := completeSynth formed₂ typed₂
  obtain ⟨T, sJ, joined⟩ := synth s₁ s₂
  have le₁ := TypeLe.toBelow ((Synth.principal facts algebra headsTyped s₁ formed₁).2 typed₁)
    (Typed.isType typed₁ formed₁)
  have le₂ := TypeLe.toBelow ((Synth.principal facts algebra headsTyped s₂ formed₂).2 typed₂)
    (Typed.isType typed₂ formed₂)
  have tJ := (Synth.principal facts algebra headsTyped sJ formedJ).1
  refine .sub tJ ?_
  rcases joined with ⟨rfl, rfl⟩ | ⟨u, v, w, rfl, rfl, rfl, hu, hv, hw, lub⟩
  · exact below_wide facts roots heads algebra rigid complete j.narrows_left formedJ formed₁
      (Typed.isType tJ formedJ) isE le₁
  · obtain ⟨r₁, hr₁, eE₁, c₁⟩ := (Below.universe_iff facts algebra formed₁ hu).1 le₁
    obtain ⟨e₁, rE₁, he₁⟩ := IsType.universe_whnf facts formed₁ (Typed.isType typed₁ formed₁) hr₁ eE₁
    have c₁' : S.R.cumulative u e₁ := algebra.same_right c₁
      (TypeEq.head_injective facts (TypeEq.trans S.levels (TypeEq.symm eE₁) rE₁.typeEq) formed₁)
    obtain ⟨r₂, hr₂, eE₂, c₂⟩ := (Below.universe_iff facts algebra formed₂ hv).1 le₂
    obtain ⟨e₂, rE₂, _⟩ := IsType.universe_whnf facts formed₂ (Typed.isType typed₂ formed₂) hr₂ eE₂
    have c₂' : S.R.cumulative v e₂ := algebra.same_right c₂
      (TypeEq.head_injective facts (TypeEq.trans S.levels (TypeEq.symm eE₂) rE₂.typeEq) formed₂)
    have same := WhRed.whnf_unique S.shape rE₁.red rE₂.red (head_whnf S.shape _) (head_whnf S.shape _)
    cases same
    have rEJ := redTy_wide facts roots formedJ rE₁.red isE
    exact (Below.universe_iff facts algebra formedJ hw).2 ⟨e₁, he₁, rEJ.typeEq, lub.2.2 e₁ he₁ c₁' c₂'⟩

include facts in
/-- The synthesizable fragment of a normal term that is not an introduction. -/
theorem synth_fragment {n : Nat} {Γ : Ctx Head n} {t E : Tm Head n} (formed : CtxFormed S.R Γ)
    (typed : Typed S.R Γ t E) (normal : Normal (S := S) t) (notLam : ∀ b, t ≠ .lam b)
    (notPair : ∀ a b, t ≠ .pair a b) (notRefl : ∀ x, t ≠ .refl x) : Bidirectional .synth t := by
  cases normal_checkable facts t formed typed normal with
  | lam _ => exact absurd rfl (notLam _)
  | pair _ _ => exact absurd rfl (notPair _ _)
  | refl _ => exact absurd rfl (notRefl _)
  | synthesized h => exact h

include facts roots heads algebra rigid complete headsTyped in
/-- **The join of typings**, synthesis and checking, by induction on the normal term. -/
theorem join_typing : ∀ {n : Nat} (t : Tm Head n), SynthJoin (S := S) t ∧ CheckJoin (S := S) t := by
  intro n t
  induction t with
  | var i =>
      have synthPart : SynthJoin (S := S) (.var i) := by
        intro Γ₁ Γ₂ J T₁ T₂ j _ _ _ _ s₁ s₂
        cases s₁
        cases s₂
        refine ⟨_, .var i, ?_⟩
        rcases j.lookup i with ⟨eJ, e₂⟩ | ⟨u, v, w, e₁, e₂, eJ, hu, hv, hw, lub⟩
        · exact .inl ⟨eJ, eJ.trans e₂.symm⟩
        · exact .inr ⟨u, v, w, e₁, e₂, eJ, hu, hv, hw, lub⟩
      exact ⟨synthPart, fun j f₁ f₂ fJ normal t₁ t₂ isE =>
        check_of_synth facts roots heads algebra rigid complete headsTyped j f₁ f₂ fJ (.var i)
          (fun s₁ s₂ => synthPart j f₁ f₂ fJ normal s₁ s₂) t₁ t₂ isE⟩
  | @head m h =>
      have synthPart : SynthJoin (S := S) (Tm.head h : Tm Head m) := by
        intro Γ₁ Γ₂ J T₁ T₂ _ _ _ _ _ s₁ s₂
        cases s₁ with
        | head ht₁ =>
            cases s₂ with
            | head ht₂ =>
                cases headsTyped ht₁ ht₂
                exact ⟨_, .head ht₁, .inl ⟨rfl, rfl⟩⟩
      exact ⟨synthPart, fun j f₁ f₂ fJ normal t₁ t₂ isE =>
        check_of_synth facts roots heads algebra rigid complete headsTyped j f₁ f₂ fJ (.head h)
          (fun s₁ s₂ => synthPart j f₁ f₂ fJ normal s₁ s₂) t₁ t₂ isE⟩
  | @const m name =>
      have synthPart : SynthJoin (S := S) (Tm.const name : Tm Head m) := by
        intro Γ₁ Γ₂ J T₁ T₂ _ _ _ _ _ s₁ s₂
        cases s₁ with
        | const declared₁ typing₁ hu₁ =>
            cases s₂ with
            | const declared₂ _ _ =>
                rw [declared₁] at declared₂
                cases declared₂
                exact ⟨_, .const declared₁ typing₁ hu₁, .inl ⟨rfl, rfl⟩⟩
      exact ⟨synthPart, fun j f₁ f₂ fJ normal t₁ t₂ isE =>
        check_of_synth facts roots heads algebra rigid complete headsTyped j f₁ f₂ fJ (.const name)
          (fun s₁ s₂ => synthPart j f₁ f₂ fJ normal s₁ s₂) t₁ t₂ isE⟩
  | pi A B ihA ihB =>
      have synthPart : SynthJoin (S := S) (.pi A B) := by
        intro Γ₁ Γ₂ J T₁ T₂ j f₁ f₂ fJ normal s₁ s₂
        cases s₁ with
        | pi sA₁ rA₁ hu₁ sB₁ rB₁ hv₁ joined₁ =>
            cases s₂ with
            | pi sA₂ rA₂ hu₂ sB₂ rB₂ _ joined₂ =>
                have nA : Normal (S := S) A := fun _ step => normal _ (.congPiDom step)
                have nB : Normal (S := S) B := fun _ step => normal _ (.congPiCod step)
                obtain ⟨TA, sA, joinedA⟩ := ihA.1 j f₁ f₂ fJ nA sA₁ sA₂
                have tA := (Synth.principal facts algebra headsTyped sA fJ).1
                obtain ⟨uJ, rAJ, huJ, lubU⟩ :=
                  universe_of_tjoin facts roots fJ rA₁ rA₂ hu₁ (Typed.isType tA fJ) joinedA
                have isA₁ : IsType S.R Γ₁ A :=
                  ⟨_, hu₁, Typed.convType (Synth.principal facts algebra headsTyped sA₁ f₁).1 rA₁.typeEq⟩
                have isA₂ : IsType S.R Γ₂ A :=
                  ⟨_, hu₂, Typed.convType (Synth.principal facts algebra headsTyped sA₂ f₂).1 rA₂.typeEq⟩
                have isAJ : IsType S.R J A := ⟨uJ, huJ, Typed.convType tA rAJ.typeEq⟩
                obtain ⟨TB, sB, joinedB⟩ :=
                  ihB.1 (.same A j) (f₁.snoc isA₁) (f₂.snoc isA₂) (fJ.snoc isAJ) nB sB₁ sB₂
                have tB := (Synth.principal facts algebra headsTyped sB (fJ.snoc isAJ)).1
                obtain ⟨vJ, rBJ, hvJ, lubV⟩ :=
                  universe_of_tjoin facts roots (fJ.snoc isAJ) rB₁ rB₂ hv₁ (Typed.isType tB (fJ.snoc isAJ))
                    joinedB
                obtain ⟨w, joined⟩ := S.levels.join_exists huJ hvJ
                exact ⟨_, .pi sA rAJ huJ sB rBJ hvJ joined,
                  .inr ⟨_, _, w, rfl, rfl, rfl, (S.levels.join_level joined₁).1,
                    (S.levels.join_level joined₂).1, (S.levels.join_level joined).1,
                    isLub_join4 algebra joined₁ joined₂ lubU lubV joined⟩⟩
      exact ⟨synthPart, fun j f₁ f₂ fJ normal t₁ t₂ isE =>
        check_of_synth facts roots heads algebra rigid complete headsTyped j f₁ f₂ fJ
          (synth_fragment facts f₁ t₁ normal (fun _ h => nomatch h) (fun _ _ h => nomatch h)
            (fun _ h => nomatch h))
          (fun s₁ s₂ => synthPart j f₁ f₂ fJ normal s₁ s₂) t₁ t₂ isE⟩
  | sigma A B ihA ihB =>
      have synthPart : SynthJoin (S := S) (.sigma A B) := by
        intro Γ₁ Γ₂ J T₁ T₂ j f₁ f₂ fJ normal s₁ s₂
        cases s₁ with
        | sigma sA₁ rA₁ hu₁ sB₁ rB₁ hv₁ joined₁ =>
            cases s₂ with
            | sigma sA₂ rA₂ hu₂ sB₂ rB₂ _ joined₂ =>
                have nA : Normal (S := S) A := fun _ step => normal _ (.congSigmaDom step)
                have nB : Normal (S := S) B := fun _ step => normal _ (.congSigmaCod step)
                obtain ⟨TA, sA, joinedA⟩ := ihA.1 j f₁ f₂ fJ nA sA₁ sA₂
                have tA := (Synth.principal facts algebra headsTyped sA fJ).1
                obtain ⟨uJ, rAJ, huJ, lubU⟩ :=
                  universe_of_tjoin facts roots fJ rA₁ rA₂ hu₁ (Typed.isType tA fJ) joinedA
                have isA₁ : IsType S.R Γ₁ A :=
                  ⟨_, hu₁, Typed.convType (Synth.principal facts algebra headsTyped sA₁ f₁).1 rA₁.typeEq⟩
                have isA₂ : IsType S.R Γ₂ A :=
                  ⟨_, hu₂, Typed.convType (Synth.principal facts algebra headsTyped sA₂ f₂).1 rA₂.typeEq⟩
                have isAJ : IsType S.R J A := ⟨uJ, huJ, Typed.convType tA rAJ.typeEq⟩
                obtain ⟨TB, sB, joinedB⟩ :=
                  ihB.1 (.same A j) (f₁.snoc isA₁) (f₂.snoc isA₂) (fJ.snoc isAJ) nB sB₁ sB₂
                have tB := (Synth.principal facts algebra headsTyped sB (fJ.snoc isAJ)).1
                obtain ⟨vJ, rBJ, hvJ, lubV⟩ :=
                  universe_of_tjoin facts roots (fJ.snoc isAJ) rB₁ rB₂ hv₁ (Typed.isType tB (fJ.snoc isAJ))
                    joinedB
                obtain ⟨w, joined⟩ := S.levels.join_exists huJ hvJ
                exact ⟨_, .sigma sA rAJ huJ sB rBJ hvJ joined,
                  .inr ⟨_, _, w, rfl, rfl, rfl, (S.levels.join_level joined₁).1,
                    (S.levels.join_level joined₂).1, (S.levels.join_level joined).1,
                    isLub_join4 algebra joined₁ joined₂ lubU lubV joined⟩⟩
      exact ⟨synthPart, fun j f₁ f₂ fJ normal t₁ t₂ isE =>
        check_of_synth facts roots heads algebra rigid complete headsTyped j f₁ f₂ fJ
          (synth_fragment facts f₁ t₁ normal (fun _ h => nomatch h) (fun _ _ h => nomatch h)
            (fun _ h => nomatch h))
          (fun s₁ s₂ => synthPart j f₁ f₂ fJ normal s₁ s₂) t₁ t₂ isE⟩
  | id A a b ihA iha ihb =>
      have synthPart : SynthJoin (S := S) (.id A a b) := by
        intro Γ₁ Γ₂ J T₁ T₂ j f₁ f₂ fJ normal s₁ s₂
        cases s₁ with
        | id sA₁ rA₁ hu₁ ca₁ cb₁ =>
            cases s₂ with
            | id sA₂ rA₂ hu₂ ca₂ cb₂ =>
                have nA : Normal (S := S) A := fun _ step => normal _ (.congIdTy step)
                have na : Normal (S := S) a := fun _ step => normal _ (.congIdLeft step)
                have nb : Normal (S := S) b := fun _ step => normal _ (.congIdRight step)
                obtain ⟨TA, sA, joinedA⟩ := ihA.1 j f₁ f₂ fJ nA sA₁ sA₂
                have tA := (Synth.principal facts algebra headsTyped sA fJ).1
                obtain ⟨uJ, rAJ, huJ, lubU⟩ :=
                  universe_of_tjoin facts roots fJ rA₁ rA₂ hu₁ (Typed.isType tA fJ) joinedA
                have isAJ : IsType S.R J A := ⟨uJ, huJ, Typed.convType tA rAJ.typeEq⟩
                have taJ := iha.2 j f₁ f₂ fJ na (KernelTyping.sound facts algebra headsTyped ca₁ f₁)
                  (KernelTyping.sound facts algebra headsTyped ca₂ f₂) isAJ
                have tbJ := ihb.2 j f₁ f₂ fJ nb (KernelTyping.sound facts algebra headsTyped cb₁ f₁)
                  (KernelTyping.sound facts algebra headsTyped cb₂ f₂) isAJ
                exact ⟨_, .id sA rAJ huJ (normal_checked facts algebra headsTyped fJ taJ na)
                  (normal_checked facts algebra headsTyped fJ tbJ nb),
                  .inr ⟨_, _, uJ, rfl, rfl, rfl, hu₁, hu₂, huJ, lubU⟩⟩
      exact ⟨synthPart, fun j f₁ f₂ fJ normal t₁ t₂ isE =>
        check_of_synth facts roots heads algebra rigid complete headsTyped j f₁ f₂ fJ
          (synth_fragment facts f₁ t₁ normal (fun _ h => nomatch h) (fun _ _ h => nomatch h)
            (fun _ h => nomatch h))
          (fun s₁ s₂ => synthPart j f₁ f₂ fJ normal s₁ s₂) t₁ t₂ isE⟩
  | lam body ih =>
      refine ⟨(fun _ _ _ _ _ s₁ _ => by cases s₁), ?_⟩
      intro Γ₁ Γ₂ J E j f₁ f₂ fJ normal t₁ t₂ isE
      have nBody : Normal (S := S) body := fun _ step => normal _ (.congLam step)
      obtain ⟨A, B, r₁⟩ : ∃ A B, RedTy S.R S.roles Γ₁ E (.pi A B) := by
        rcases IsType.pi_or facts f₁ (Typed.isType t₁ f₁) with found | none
        · exact found
        · obtain ⟨D, C, e⟩ := lambda_type facts f₁ t₁
          exact absurd e (none D C)
      have r₂ := redTy_wide facts roots f₂ r₁.red (Typed.isType t₂ f₂)
      have rJ := redTy_wide facts roots fJ r₁.red isE
      obtain ⟨isA₁, _⟩ := IsType.pi_parts r₁.targetType
      obtain ⟨isA₂, _⟩ := IsType.pi_parts r₂.targetType
      obtain ⟨isAJ, isBJ⟩ := IsType.pi_parts rJ.targetType
      have b₁ := Typed.lam_inv facts (Typed.convType t₁ r₁.typeEq) f₁
      have b₂ := Typed.lam_inv facts (Typed.convType t₂ r₂.typeEq) f₂
      have bJ := ih.2 (.same A j) (f₁.snoc isA₁) (f₂.snoc isA₂) (fJ.snoc isAJ) nBody b₁ b₂ isBJ
      obtain ⟨u, hu, tPi⟩ := rJ.targetType
      exact Typed.convType (Derivable.lamIntro tPi hu bJ) (TypeEq.symm rJ.typeEq)
  | app f a ihf iha =>
      have synthPart : SynthJoin (S := S) (.app f a) := by
        intro Γ₁ Γ₂ J T₁ T₂ j f₁ f₂ fJ normal s₁ s₂
        cases s₁ with
        | redex _ _ _ => exact absurd (.betaPi _ _) (normal _)
        | app sf₁ rF₁ ca₁ =>
            cases s₂ with
            | redex _ _ _ => exact absurd (.betaPi _ _) (normal _)
            | app sf₂ rF₂ ca₂ =>
                have nf : Normal (S := S) f := fun _ step => normal _ (.congAppFun step)
                have na : Normal (S := S) a := fun _ step => normal _ (.congAppArg step)
                obtain ⟨F, sF, joinedF⟩ := ihf.1 j f₁ f₂ fJ nf sf₁ sf₂
                obtain ⟨rfl, rfl⟩ := same_of_tjoin rF₁.red (fun _ h => nomatch h) joinedF
                have samePi := WhRed.whnf_unique S.shape rF₁.red rF₂.red (pi_whnf S.shape _ _) (pi_whnf S.shape _ _)
                cases samePi
                have tF := (Synth.principal facts algebra headsTyped sF fJ).1
                have rFJ := redTy_wide facts roots fJ rF₁.red (Typed.isType tF fJ)
                obtain ⟨isAJ, _⟩ := IsType.pi_parts rFJ.targetType
                have taJ := iha.2 j f₁ f₂ fJ na (KernelTyping.sound facts algebra headsTyped ca₁ f₁)
                  (KernelTyping.sound facts algebra headsTyped ca₂ f₂) isAJ
                exact ⟨_, .app sF rFJ (normal_checked facts algebra headsTyped fJ taJ na), .inl ⟨rfl, rfl⟩⟩
      exact ⟨synthPart, fun j f₁ f₂ fJ normal t₁ t₂ isE =>
        check_of_synth facts roots heads algebra rigid complete headsTyped j f₁ f₂ fJ
          (synth_fragment facts f₁ t₁ normal (fun _ h => nomatch h) (fun _ _ h => nomatch h)
            (fun _ h => nomatch h))
          (fun s₁ s₂ => synthPart j f₁ f₂ fJ normal s₁ s₂) t₁ t₂ isE⟩
  | pair a b iha ihb =>
      refine ⟨(fun _ _ _ _ _ s₁ _ => by cases s₁), ?_⟩
      intro Γ₁ Γ₂ J E j f₁ f₂ fJ normal t₁ t₂ isE
      have na : Normal (S := S) a := fun _ step => normal _ (.congPairFst step)
      have nb : Normal (S := S) b := fun _ step => normal _ (.congPairSnd step)
      obtain ⟨A, B, r₁⟩ : ∃ A B, RedTy S.R S.roles Γ₁ E (.sigma A B) := by
        rcases IsType.sigma_or facts f₁ (Typed.isType t₁ f₁) with found | none
        · exact found
        · obtain ⟨D, C, e⟩ := pair_type facts f₁ t₁
          exact absurd e (none D C)
      have r₂ := redTy_wide facts roots f₂ r₁.red (Typed.isType t₂ f₂)
      have rJ := redTy_wide facts roots fJ r₁.red isE
      obtain ⟨isAJ, ⟨uB, huB, tB⟩⟩ := IsType.sigma_parts rJ.targetType
      obtain ⟨ta₁, tb₁⟩ := Typed.pair_inv facts (Typed.convType t₁ r₁.typeEq) f₁
      obtain ⟨ta₂, tb₂⟩ := Typed.pair_inv facts (Typed.convType t₂ r₂.typeEq) f₂
      have taJ := iha.2 j f₁ f₂ fJ na ta₁ ta₂ isAJ
      have isBa : IsType S.R J (inst0 a B) := ⟨uB, huB, Typed.instantiate tB taJ⟩
      have tbJ := ihb.2 j f₁ f₂ fJ nb tb₁ tb₂ isBa
      obtain ⟨u, hu, tSigma⟩ := rJ.targetType
      exact Typed.convType (Derivable.pairIntro tSigma hu taJ tbJ) (TypeEq.symm rJ.typeEq)
  | fst p ih =>
      have synthPart : SynthJoin (S := S) (.fst p) := by
        intro Γ₁ Γ₂ J T₁ T₂ j f₁ f₂ fJ normal s₁ s₂
        cases s₁ with
        | fst sp₁ rP₁ =>
            cases s₂ with
            | fst sp₂ rP₂ =>
                have np : Normal (S := S) p := fun _ step => normal _ (.congFst step)
                obtain ⟨P, sP, joinedP⟩ := ih.1 j f₁ f₂ fJ np sp₁ sp₂
                obtain ⟨rfl, rfl⟩ := same_of_tjoin rP₁.red (fun _ h => nomatch h) joinedP
                have sameSigma :=
                  WhRed.whnf_unique S.shape rP₁.red rP₂.red (sigma_whnf S.shape _ _) (sigma_whnf S.shape _ _)
                cases sameSigma
                have tP := (Synth.principal facts algebra headsTyped sP fJ).1
                exact ⟨_, .fst sP (redTy_wide facts roots fJ rP₁.red (Typed.isType tP fJ)), .inl ⟨rfl, rfl⟩⟩
      exact ⟨synthPart, fun j f₁ f₂ fJ normal t₁ t₂ isE =>
        check_of_synth facts roots heads algebra rigid complete headsTyped j f₁ f₂ fJ
          (synth_fragment facts f₁ t₁ normal (fun _ h => nomatch h) (fun _ _ h => nomatch h)
            (fun _ h => nomatch h))
          (fun s₁ s₂ => synthPart j f₁ f₂ fJ normal s₁ s₂) t₁ t₂ isE⟩
  | snd p ih =>
      have synthPart : SynthJoin (S := S) (.snd p) := by
        intro Γ₁ Γ₂ J T₁ T₂ j f₁ f₂ fJ normal s₁ s₂
        cases s₁ with
        | snd sp₁ rP₁ =>
            cases s₂ with
            | snd sp₂ rP₂ =>
                have np : Normal (S := S) p := fun _ step => normal _ (.congSnd step)
                obtain ⟨P, sP, joinedP⟩ := ih.1 j f₁ f₂ fJ np sp₁ sp₂
                obtain ⟨rfl, rfl⟩ := same_of_tjoin rP₁.red (fun _ h => nomatch h) joinedP
                have sameSigma :=
                  WhRed.whnf_unique S.shape rP₁.red rP₂.red (sigma_whnf S.shape _ _) (sigma_whnf S.shape _ _)
                cases sameSigma
                have tP := (Synth.principal facts algebra headsTyped sP fJ).1
                exact ⟨_, .snd sP (redTy_wide facts roots fJ rP₁.red (Typed.isType tP fJ)), .inl ⟨rfl, rfl⟩⟩
      exact ⟨synthPart, fun j f₁ f₂ fJ normal t₁ t₂ isE =>
        check_of_synth facts roots heads algebra rigid complete headsTyped j f₁ f₂ fJ
          (synth_fragment facts f₁ t₁ normal (fun _ h => nomatch h) (fun _ _ h => nomatch h)
            (fun _ h => nomatch h))
          (fun s₁ s₂ => synthPart j f₁ f₂ fJ normal s₁ s₂) t₁ t₂ isE⟩
  | refl x ih =>
      refine ⟨?_, ?_⟩
      · intro Γ₁ Γ₂ J T₁ T₂ j f₁ f₂ fJ normal s₁ s₂
        cases s₁ with
        | refl sx₁ rs₁ =>
            cases s₂ with
            | refl sx₂ _ =>
                have nx : Normal (S := S) x := fun _ step => normal _ (.congRefl step)
                obtain ⟨A, sx, joinedA⟩ := ih.1 j f₁ f₂ fJ nx sx₁ sx₂
                rcases joinedA with ⟨rfl, rfl⟩ | ⟨u, _, _, rfl, _, _, hu, _, _, _⟩
                · have tx := (Synth.principal facts algebra headsTyped sx fJ).1
                  exact ⟨_, .refl sx (RigidShape.wide facts roots rs₁ fJ (Typed.isType tx fJ)), .inl ⟨rfl, rfl⟩⟩
                · exact absurd hu (rigidShape_not_universe rs₁ rfl)
      · intro Γ₁ Γ₂ J E j f₁ f₂ fJ normal t₁ t₂ isE
        have nx : Normal (S := S) x := fun _ step => normal _ (.congRefl step)
        obtain ⟨C, eC⟩ := refl_type facts f₁ t₁
        obtain ⟨C', a', b', r₁⟩ : ∃ C a b, RedTy S.R S.roles Γ₁ E (.id C a b) := by
          rcases IsType.id_or facts f₁ (Typed.isType t₁ f₁) with found | none
          · exact found
          · exact absurd eC (none C x x)
        have r₂ := redTy_wide facts roots f₂ r₁.red (Typed.isType t₂ f₂)
        have rJ := redTy_wide facts roots fJ r₁.red isE
        -- over each telescope, the subject has the carrier and equals both endpoints
        have parts : ∀ {Γ : Ctx Head _}, CtxFormed S.R Γ → Typed S.R Γ (.refl x) E →
            RedTy S.R S.roles Γ E (.id C' a' b') →
            Typed S.R Γ x C' ∧ Equal S.R Γ x a' C' ∧ Equal S.R Γ x b' C' := by
          intro Γ formed typed red
          obtain ⟨D, txD, below⟩ := typed.generation
          have eD : TypeEq S.R Γ E (.id D x x) :=
            (TypeLe.id_eq facts below (Typed.isType typed formed) formed).symm
          obtain ⟨eCar, ea, eb⟩ :=
            TypeEq.id_injective facts (TypeEq.trans S.levels (TypeEq.symm eD) red.typeEq) formed
          exact ⟨Typed.convType txD eCar, Equal.convType ea eCar, Equal.convType eb eCar⟩
        obtain ⟨tx₁, ea₁, eb₁⟩ := parts f₁ t₁ r₁
        obtain ⟨tx₂, _, _⟩ := parts f₂ t₂ r₂
        obtain ⟨u, hu, tId⟩ := rJ.targetType
        have generation : GenerationAt S.R J (.id C' a' b') (.head u) := Typed.generation tId
        obtain ⟨u₁, tC, hu₁, ta, tb, _⟩ := generation
        have isCJ : IsType S.R J C' := ⟨u₁, hu₁, tC⟩
        have txJ := ih.2 j f₁ f₂ fJ nx tx₁ tx₂ isCJ
        have eaJ := equal_of_narrows facts roots heads algebra rigid complete j.narrows_left fJ f₁ txJ ta ea₁
        have ebJ := equal_of_narrows facts roots heads algebra rigid complete j.narrows_left fJ f₁ txJ tb eb₁
        have eId : Equal S.R J (.id C' x x) (.id C' a' b') (.head u₁) :=
          Derivable.idCong (.refl tC) hu₁ eaJ ebJ
        exact Typed.convType (Typed.convType (Derivable.reflIntro txJ) ⟨u₁, hu₁, eId⟩) (TypeEq.symm rJ.typeEq)

include facts roots heads algebra rigid complete headsTyped in
/-- **The join widening.** A normal term of a type over `Γ₁` and over `Γ₂` has that type over their join, when the
type is a type there. -/
theorem typed_join {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} (j : JoinOf S.R Γ₁ Γ₂ J) (formed₁ : CtxFormed S.R Γ₁)
    (formed₂ : CtxFormed S.R Γ₂) (formedJ : CtxFormed S.R J) {t E : Tm Head n} (normal : Normal (S := S) t)
    (typed₁ : Typed S.R Γ₁ t E) (typed₂ : Typed S.R Γ₂ t E) (isE : IsType S.R J E) : Typed S.R J t E :=
  (join_typing facts roots heads algebra rigid complete headsTyped t).2 j formed₁ formed₂ formedJ normal typed₁
    typed₂ isE

end Typing

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
