import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Decision

/-!
# Definitional unfolding diverges at an abstract accessibility proof

An evaluator for the strong variant rewrites with beta and with the unfolding
of the recursor, anywhere in a term (`StrongStep`).  The strong definitional
equality is contained in the equivalence closure of these steps
(`strong_conv_sub_strongConv`), and beta conversion is contained in it too.

**Negative control.**  Take the step `loopStep := λx z. z x`, a relation
variable `r` and a point variable `a`.  With the two abstract hypotheses
`accCode r a` and `respCode r loopStep`, the strong variant licenses the
unfolding of `rec r loopStep a` (`loop_unfold_licensed`).  The evaluator then
returns to the same term after four steps (`loop_cycle`), and no sequence of
steps from it ever reaches a normal form (`loop_no_normal_form`): every
term reachable from it has a further step.  The invariant `Looping` describes
all such terms; it is closed under every step (`Looping.step_closed`) and
each of its terms has a step (`Looping.has_step`).

The same conversion problem is decided in the carved variant, where the
recursor never unfolds: `rec r loopStep a` is beta normal, and the unfolding
beta-reduces back to it (`loop_carved_decided`).

The hypotheses are jointly unsatisfiable (a relation whose accessibility
proof is abstract, with a step that calls itself at its own argument); the
divergence needs no closed term, only an abstract proof.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding.AccessibleRecursion

open Mettapedia.Logic
open Mettapedia.TypeTheory.Unfolding
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

variable {A P : Ty}

/-- One step of the strong variant's evaluator: beta, or the unfolding of the
recursor, anywhere in a term. -/
inductive StrongStep : {Γ : List Ty} → {T : Ty} → Tm A P Γ T → Tm A P Γ T → Prop
  | beta {Γ : List Ty} {B T : Ty} (body : Tm A P (B :: Γ) T) (argument : Tm A P Γ B) :
      StrongStep (Γ := Γ) (.app (.lam body) argument) (inst body argument)
  | unfold {Γ : List Ty} (R : Tm A P Γ (relTy A)) (F : Tm A P Γ (stepTy A P))
      (point : Tm A P Γ A) :
      StrongStep (Γ := Γ) (recTerm R F point) (unfoldTerm R F point)
  | lam {Γ : List Ty} {B T : Ty} {body body' : Tm A P (B :: Γ) T} :
      StrongStep (Γ := B :: Γ) body body' → StrongStep (Γ := Γ) (.lam body) (.lam body')
  | appLeft {Γ : List Ty} {B T : Ty} {function function' : Tm A P Γ (.arr B T)}
      {argument : Tm A P Γ B} :
      StrongStep (Γ := Γ) function function' →
        StrongStep (Γ := Γ) (.app function argument) (.app function' argument)
  | appRight {Γ : List Ty} {B T : Ty} {function : Tm A P Γ (.arr B T)}
      {argument argument' : Tm A P Γ B} :
      StrongStep (Γ := Γ) argument argument' →
        StrongStep (Γ := Γ) (.app function argument) (.app function argument')

/-- Conversion of the strong evaluator. -/
abbrev StrongConv {Γ : List Ty} {T : Ty} (left right : Tm A P Γ T) : Prop :=
  Relation.EqvGen (StrongStep (Γ := Γ)) left right

private theorem strongStep_of_betaStep_aux :
    ∀ {Δ : List Ty} {T : Ty} {left right : Term Δ T}, BetaStep left right →
      ∀ (Γ : List Ty), Δ = Γ ++ signature A P → ∀ (left' right' : Tm A P Γ T),
        HEq left left' → HEq right right' → StrongStep (A := A) (P := P) (Γ := Γ) left' right' := by
  intro Δ T left right step
  induction step with
  | beta body argument =>
      intro Γ context left' right' sameLeft sameRight
      subst context
      cases eq_of_heq sameLeft
      cases eq_of_heq sameRight
      exact StrongStep.beta body argument
  | @lam Δ B T body body' _ ih =>
      intro Γ context left' right' sameLeft sameRight
      subst context
      cases eq_of_heq sameLeft
      cases eq_of_heq sameRight
      exact StrongStep.lam (ih (B :: Γ) rfl body body' HEq.rfl HEq.rfl)
  | @appLeft Δ B T function function' argument _ ih =>
      intro Γ context left' right' sameLeft sameRight
      subst context
      cases eq_of_heq sameLeft
      cases eq_of_heq sameRight
      exact StrongStep.appLeft (ih Γ rfl function function' HEq.rfl HEq.rfl)
  | @appRight Δ B T function argument argument' _ ih =>
      intro Γ context left' right' sameLeft sameRight
      subst context
      cases eq_of_heq sameLeft
      cases eq_of_heq sameRight
      exact StrongStep.appRight (ih Γ rfl argument argument' HEq.rfl HEq.rfl)

/-- A beta step is a step of the strong evaluator. -/
theorem strongStep_of_betaStep {Γ : List Ty} {T : Ty} {left right : Tm A P Γ T}
    (step : BetaStep left right) : StrongStep (Γ := Γ) left right :=
  strongStep_of_betaStep_aux step Γ rfl left right HEq.rfl HEq.rfl

/-- Beta conversion is strong conversion. -/
theorem strongConv_of_betaConv {Γ : List Ty} {T : Ty} {left right : Tm A P Γ T}
    (convertible : BetaConv left right) : StrongConv left right := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (strongStep_of_betaStep step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem StrongConv.appLeft {Γ : List Ty} {B T : Ty} {function function' : Tm A P Γ (.arr B T)}
    (argument : Tm A P Γ B) (functions : StrongConv function function') :
    StrongConv (Γ := Γ) (.app function argument) (.app function' argument) := by
  induction functions with
  | rel _ _ step => exact .rel _ _ (.appLeft step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem StrongConv.appRight {Γ : List Ty} {B T : Ty} (function : Tm A P Γ (.arr B T))
    {argument argument' : Tm A P Γ B} (arguments : StrongConv argument argument') :
    StrongConv (Γ := Γ) (.app function argument) (.app function argument') := by
  induction arguments with
  | rel _ _ step => exact .rel _ _ (.appRight step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem StrongConv.app {Γ : List Ty} {B T : Ty} {function function' : Tm A P Γ (.arr B T)}
    {argument argument' : Tm A P Γ B} (functions : StrongConv function function')
    (arguments : StrongConv argument argument') :
    StrongConv (Γ := Γ) (.app function argument) (.app function' argument') :=
  .trans _ _ _ (StrongConv.appLeft argument functions) (StrongConv.appRight function' arguments)

theorem StrongConv.lam {Γ : List Ty} {B T : Ty} {body body' : Tm A P (B :: Γ) T}
    (bodies : StrongConv (Γ := B :: Γ) body body') :
    StrongConv (Γ := Γ) (.lam body) (.lam body') := by
  induction bodies with
  | rel _ _ step => exact .rel _ _ (.lam step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- What strong derivability says about definitional equality: the two sides
are related by the strong evaluator's conversion. -/
def StrongConvMeaning : Judgment A P → Prop
  | .holds _ _ _ => True
  | .conv Γ _ _ left right => StrongConv (Γ := Γ) left right
  | .equal _ _ _ _ _ => True

/-- **Strong definitional equality is contained in the evaluator's
conversion.** -/
theorem strong_conv_sub_strongConv {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
    {left right : Tm A P Γ T} (derivation : Strong A P (.conv Γ hyps T left right)) :
    StrongConv (Γ := Γ) left right := by
  have meaning : StrongConvMeaning (Judgment.conv Γ hyps T left right) := by
    refine Derives.least StrongConvMeaning ?_ derivation
    intro premises conclusion rule meanings
    rcases rule with (rule | rule) | rule
    · cases rule <;> trivial
    · cases rule with
      | beta left right convertible => exact strongConv_of_betaConv convertible
      | symm left right => exact Relation.EqvGen.symm _ _ (meanings _ mem₀)
      | trans left middle right =>
          exact Relation.EqvGen.trans _ _ _ (meanings _ mem₀) (meanings _ mem₁)
      | app function function' argument argument' =>
          exact StrongConv.app (meanings _ mem₀) (meanings _ mem₁)
      | lam body body' => exact StrongConv.lam (meanings _ mem₀)
    · cases rule with
      | unfold R F point => exact .rel _ _ (StrongStep.unfold R F point)
  exact meaning

/-! ## The loop -/

/-- The step `λx z. z x`: it calls the recursion at its own argument. -/
def loopStep {Γ : List Ty} : Tm A P Γ (stepTy A P) :=
  .lam (.lam (.app (.var .zero) (.var (.succ .zero))))

@[simp] theorem wk_loopStep {Γ : List Ty} {B : Ty} :
    wk (B := B) (loopStep (A := A) (P := P) (Γ := Γ)) = loopStep := rfl

/-- The terms reachable from `rec r loopStep a` for variables `r` and `a`. -/
inductive Looping : {Γ : List Ty} → Tm A P Γ P → Prop
  | start {Γ : List Ty} (relation : Var (Γ ++ signature A P) (relTy A))
      (point : Var (Γ ++ signature A P) A) :
      Looping (Γ := Γ) (recTerm (.var relation) loopStep (.var point))
  | unfolded {Γ : List Ty} (point : Var (Γ ++ signature A P) A) (body : Tm A P (A :: Γ) P) :
      Looping (Γ := A :: Γ) body →
        Looping (Γ := Γ) (.app (.app loopStep (.var point)) (.lam body))
  | halfway {Γ : List Ty} (point : Var (Γ ++ signature A P) A) (body : Tm A P (A :: Γ) P) :
      Looping (Γ := A :: Γ) body →
        Looping (Γ := Γ) (.app (.lam (.app (.var .zero) (.var (.succ point)))) (.lam body))
  | calling {Γ : List Ty} (point : Var (Γ ++ signature A P) A) (body : Tm A P (A :: Γ) P) :
      Looping (Γ := A :: Γ) body → Looping (Γ := Γ) (.app (.lam body) (.var point))

/-- Every looping term has a step. -/
theorem Looping.has_step {Γ : List Ty} {term : Tm A P Γ P} (looping : Looping term) :
    ∃ next, StrongStep (Γ := Γ) term next := by
  cases looping with
  | start relation point => exact ⟨_, StrongStep.unfold _ _ _⟩
  | unfolded point body _ => exact ⟨_, StrongStep.appLeft (StrongStep.beta _ _)⟩
  | halfway point body _ => exact ⟨_, StrongStep.beta _ _⟩
  | calling point body _ => exact ⟨_, StrongStep.beta _ _⟩

/-! ### Substitutions that rename variables and fix the signature -/

/-- A substitution sending every variable to a variable and every signature
symbol to itself. -/
def RenamesFixingSignature {Γ Δ : List Ty}
    (σ : Substitution (Γ ++ signature A P) (Δ ++ signature A P)) : Prop :=
  (∀ {T : Ty} (x : Var (Γ ++ signature A P) T), ∃ y, σ x = .var y) ∧
    ∀ {T : Ty} (symbol : Var (signature A P) T), σ (liftSymbol Γ symbol) = .var (liftSymbol Δ symbol)

theorem RenamesFixingSignature.lift {Γ Δ : List Ty} {B : Ty}
    {σ : Substitution (Γ ++ signature A P) (Δ ++ signature A P)}
    (renames : RenamesFixingSignature σ) :
    RenamesFixingSignature (Γ := B :: Γ) (Δ := B :: Δ) (liftSubstitution σ) := by
  refine ⟨?_, ?_⟩
  · intro T x
    cases x with
    | zero => exact ⟨.zero, rfl⟩
    | succ x =>
        obtain ⟨y, hy⟩ := renames.1 x
        refine ⟨.succ y, ?_⟩
        change (σ x).rename weakening = _
        rw [show σ x = .var y from hy]
        rfl
  · intro T symbol
    change (σ (liftSymbol Γ symbol)).rename weakening = _
    rw [show σ (liftSymbol Γ symbol) = .var (liftSymbol Δ symbol) from renames.2 symbol]
    rfl

theorem RenamesFixingSignature.newest {Γ : List Ty} {B : Ty} (x : Var (Γ ++ signature A P) B) :
    RenamesFixingSignature (Γ := B :: Γ) (Δ := Γ) (newestSubstitution (.var x)) := by
  refine ⟨?_, ?_⟩
  · intro T y
    cases y with
    | zero => exact ⟨x, rfl⟩
    | succ y => exact ⟨y, rfl⟩
  · intro T symbol
    rfl

theorem Looping.substitute {Γ : List Ty} {term : Tm A P Γ P} (looping : Looping term) :
    ∀ {Δ : List Ty} {σ : Substitution (Γ ++ signature A P) (Δ ++ signature A P)},
      RenamesFixingSignature σ → Looping (Γ := Δ) (term.substitute σ) := by
  induction looping with
  | @start Γ relation point =>
      intro Δ σ renames
      obtain ⟨relation', hr⟩ := renames.1 relation
      obtain ⟨point', hp⟩ := renames.1 point
      have hsym := renames.2 (recSymbol A P)
      change Looping (.app (.app (.app (σ (liftSymbol Γ (recSymbol A P))) (σ relation))
        (loopStep.substitute σ)) (σ point))
      rw [show σ (liftSymbol Γ (recSymbol A P)) = .var (liftSymbol Δ (recSymbol A P)) from hsym,
        show σ relation = .var relation' from hr, show σ point = .var point' from hp]
      exact .start relation' point'
  | @unfolded Γ point body _ ih =>
      intro Δ σ renames
      obtain ⟨point', hp⟩ := renames.1 point
      change Looping (.app (.app (loopStep.substitute σ) (σ point))
        (.lam (body.substitute (liftSubstitution σ))))
      rw [show σ point = .var point' from hp]
      exact .unfolded point' _ (ih renames.lift)
  | @halfway Γ point body _ ih =>
      intro Δ σ renames
      obtain ⟨point', hp⟩ := renames.1 point
      change Looping (.app (.lam (.app (.var .zero) ((σ point).rename weakening)))
        (.lam (body.substitute (liftSubstitution σ))))
      rw [show σ point = .var point' from hp]
      exact .halfway point' _ (ih renames.lift)
  | @calling Γ point body _ ih =>
      intro Δ σ renames
      obtain ⟨point', hp⟩ := renames.1 point
      change Looping (.app (.lam (body.substitute (liftSubstitution σ))) (σ point))
      rw [show σ point = .var point' from hp]
      exact .calling point' _ (ih renames.lift)

/-! ### Closure under steps

The inversion lemmas keep every type index a variable, so that case analysis
never has to refute an occurs-check equation such as `P = A → P`; those are
refuted by the structural lemmas `ty_ne_arr_left` and `ty_ne_arr_right`. -/

theorem ty_ne_arr_left : ∀ (S T : Ty), S ≠ .arr S T := by
  intro S
  induction S with
  | atom => intro T h; exact Ty.noConfusion h
  | arr S₁ S₂ ih₁ _ =>
      intro T h
      injection h with h₁ _
      exact ih₁ S₂ h₁

theorem ty_ne_arr_right : ∀ (S T : Ty), T ≠ .arr S T := by
  intro S T
  induction T with
  | atom => intro h; exact Ty.noConfusion h
  | arr T₁ T₂ _ ih₂ =>
      intro h
      injection h with h₁ h₂
      exact ih₂ (h₁ ▸ h₂)

/-- Inversion of a step from an abstraction. -/
theorem StrongStep.lam_inv {Γ : List Ty} {B T : Ty} {body : Tm A P (B :: Γ) T}
    {next : Tm A P Γ (.arr B T)} (step : StrongStep (Γ := Γ) (.lam body) next) :
    ∃ body', next = .lam body' ∧ StrongStep (Γ := B :: Γ) body body' := by
  cases step with
  | lam inner => exact ⟨_, rfl, inner⟩

/-- Inversion of a step from an application. -/
theorem StrongStep.app_inv {Γ : List Ty} {B T : Ty} {function : Tm A P Γ (.arr B T)}
    {argument : Tm A P Γ B} {next : Tm A P Γ T}
    (step : StrongStep (Γ := Γ) (.app function argument) next) :
    (∃ body : Tm A P (B :: Γ) T, function = .lam body ∧ next = inst body argument) ∨
      (∃ (R : Tm A P Γ (relTy A)) (F : Tm A P Γ (stepTy A P)) (point : Tm A P Γ A),
        A = B ∧ P = T ∧
          HEq function (Term.app (Term.app (sym Γ (recSymbol A P)) R) F : Tm A P Γ (.arr A P)) ∧
          HEq argument point ∧ HEq next (unfoldTerm R F point)) ∨
      (∃ function', next = .app function' argument ∧ StrongStep (Γ := Γ) function function') ∨
      (∃ argument', next = .app function argument' ∧ StrongStep (Γ := Γ) argument argument') := by
  cases step with
  | beta body argument => exact .inl ⟨body, rfl, rfl⟩
  | unfold R F point => exact .inr (.inl ⟨R, F, point, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩)
  | appLeft inner => exact .inr (.inr (.inl ⟨_, rfl, inner⟩))
  | appRight inner => exact .inr (.inr (.inr ⟨_, rfl, inner⟩))

/-- Inversion of a step from an application at the result type, where an
unfolding may fire at the root. -/
theorem StrongStep.app_inv_result {Γ : List Ty} {function : Tm A P Γ (.arr A P)}
    {argument : Tm A P Γ A} {next : Tm A P Γ P}
    (step : StrongStep (Γ := Γ) (.app function argument) next) :
    (∃ body : Tm A P (A :: Γ) P, function = .lam body ∧ next = inst body argument) ∨
      (∃ (R : Tm A P Γ (relTy A)) (F : Tm A P Γ (stepTy A P)),
        function = .app (.app (sym Γ (recSymbol A P)) R) F ∧ next = unfoldTerm R F argument) ∨
      (∃ function', next = .app function' argument ∧ StrongStep (Γ := Γ) function function') ∨
      (∃ argument', next = .app function argument' ∧ StrongStep (Γ := Γ) argument argument') := by
  cases step with
  | beta body argument => exact .inl ⟨body, rfl, rfl⟩
  | unfold R F point => exact .inr (.inl ⟨R, F, rfl, rfl⟩)
  | appLeft inner => exact .inr (.inr (.inl ⟨_, rfl, inner⟩))
  | appRight inner => exact .inr (.inr (.inr ⟨_, rfl, inner⟩))

private theorem recHead_inj {Γ : List Ty} {R R' : Tm A P Γ (relTy A)}
    {F F' : Tm A P Γ (stepTy A P)}
    (same : (Term.app (Term.app (sym Γ (recSymbol A P)) R) F : Tm A P Γ (.arr A P)) =
      Term.app (Term.app (sym Γ (recSymbol A P)) R') F') :
    R = R' ∧ F = F' := by
  obtain ⟨_, headSame, stepSame⟩ := Term.app.inj same
  obtain ⟨_, _, relationSame⟩ := Term.app.inj (eq_of_heq headSame)
  exact ⟨eq_of_heq relationSame, eq_of_heq stepSame⟩

private theorem var_no_step {Γ : List Ty} {T : Ty} (x : Var (Γ ++ signature A P) T)
    {next : Tm A P Γ T} : ¬ StrongStep (Γ := Γ) (.var x) next := by
  intro step
  cases step

private theorem varApp_no_step {Γ : List Ty} {B T : Ty}
    (function : Var (Γ ++ signature A P) (.arr B T)) (argument : Var (Γ ++ signature A P) B)
    {next : Tm A P Γ T} : ¬ StrongStep (Γ := Γ) (.app (.var function) (.var argument)) next := by
  intro step
  cases step with
  | appLeft inner => exact var_no_step _ inner
  | appRight inner => exact var_no_step _ inner

private theorem loopStep_no_step {Γ : List Ty} {next : Tm A P Γ (stepTy A P)} :
    ¬ StrongStep (Γ := Γ) loopStep next := by
  intro step
  obtain ⟨_, _, inner⟩ := StrongStep.lam_inv step
  obtain ⟨_, _, inner'⟩ := StrongStep.lam_inv inner
  exact varApp_no_step _ _ inner'

private theorem halfwayHead_no_step {Γ : List Ty} (point : Var (Γ ++ signature A P) A)
    {next : Tm A P Γ (.arr (.arr A P) P)} :
    ¬ StrongStep (Γ := Γ) (.lam (.app (.var .zero) (.var (.succ point)))) next := by
  intro step
  obtain ⟨_, _, inner⟩ := StrongStep.lam_inv step
  exact varApp_no_step _ _ inner

private theorem recHead_no_step {Γ : List Ty} (relation : Var (Γ ++ signature A P) (relTy A))
    {next : Tm A P Γ (.arr A P)} :
    ¬ StrongStep (Γ := Γ)
      (.app (.app (sym Γ (recSymbol A P)) (.var relation)) loopStep) next := by
  intro step
  rcases StrongStep.app_inv step with ⟨_, same, _⟩ | ⟨_, _, _, sameA, _, _, _, _⟩ |
      ⟨_, _, inner⟩ | ⟨_, _, inner⟩
  · cases same
  · exact ty_ne_arr_left _ _ sameA
  · rcases StrongStep.app_inv inner with ⟨_, same, _⟩ | ⟨_, _, _, sameA', _, _, _, _⟩ |
        ⟨_, _, inner'⟩ | ⟨_, _, inner'⟩
    · cases same
    · exact ty_ne_arr_left _ _ sameA'
    · exact var_no_step _ inner'
    · exact var_no_step _ inner'
  · exact loopStep_no_step inner

/-- **Looping terms step only to looping terms.** -/
theorem Looping.step_closed {Γ : List Ty} {term : Tm A P Γ P} (looping : Looping term) :
    ∀ {next : Tm A P Γ P}, StrongStep (Γ := Γ) term next → Looping (Γ := Γ) next := by
  induction looping with
  | @start Γ relation point =>
      intro next step
      rcases StrongStep.app_inv_result step with ⟨_, same, _⟩ | ⟨R, F, same, nextEq⟩ |
          ⟨_, _, inner⟩ | ⟨_, _, inner⟩
      · cases same
      · obtain ⟨relationEq, stepEq⟩ := recHead_inj same
        subst relationEq
        subst stepEq
        subst nextEq
        exact .unfolded point _ (.start (Γ := A :: Γ) (.succ relation) .zero)
      · exact absurd inner (recHead_no_step relation)
      · exact absurd inner (var_no_step _)
  | @unfolded Γ point body bodyLooping ih =>
      intro next step
      rcases StrongStep.app_inv step with ⟨_, same, _⟩ | ⟨_, _, _, sameA, _, _, _, _⟩ |
          ⟨_, nextEq, inner⟩ | ⟨_, nextEq, inner⟩
      · cases same
      · exact absurd sameA (ty_ne_arr_left A P)
      · subst nextEq
        rcases StrongStep.app_inv inner with ⟨body', same, reduct⟩ | ⟨_, _, _, _, sameP, _, _, _⟩ |
            ⟨_, _, inner'⟩ | ⟨_, _, inner'⟩
        · injection same with _ _ _ bodySame
          subst bodySame
          subst reduct
          exact .halfway point body bodyLooping
        · exact absurd sameP (ty_ne_arr_right _ P)
        · exact absurd inner' loopStep_no_step
        · exact absurd inner' (var_no_step _)
      · subst nextEq
        obtain ⟨_, argumentEq, inner'⟩ := StrongStep.lam_inv inner
        subst argumentEq
        exact .unfolded point _ (ih inner')
  | @halfway Γ point body bodyLooping ih =>
      intro next step
      rcases StrongStep.app_inv step with ⟨body', same, reduct⟩ | ⟨_, _, _, sameA, _, _, _, _⟩ |
          ⟨_, _, inner⟩ | ⟨_, nextEq, inner⟩
      · injection same with _ _ _ bodySame
        subst bodySame
        subst reduct
        exact .calling point body bodyLooping
      · exact absurd sameA (ty_ne_arr_left A P)
      · exact absurd inner (halfwayHead_no_step point)
      · subst nextEq
        obtain ⟨_, argumentEq, inner'⟩ := StrongStep.lam_inv inner
        subst argumentEq
        exact .halfway point _ (ih inner')
  | @calling Γ point body bodyLooping ih =>
      intro next step
      rcases StrongStep.app_inv_result step with ⟨body', same, reduct⟩ | ⟨_, _, same, _⟩ |
          ⟨_, nextEq, inner⟩ | ⟨_, _, inner⟩
      · injection same with _ _ _ bodySame
        subst bodySame
        subst reduct
        exact bodyLooping.substitute (RenamesFixingSignature.newest point)
      · cases same
      · subst nextEq
        obtain ⟨_, functionEq, inner'⟩ := StrongStep.lam_inv inner
        subst functionEq
        exact .calling point _ (ih inner')
      · exact absurd inner (var_no_step _)

/-- **No normal form.**  Every term reachable from `rec r loopStep a` has a
further step. -/
theorem loop_no_normal_form {Γ : List Ty} (relation : Var (Γ ++ signature A P) (relTy A))
    (point : Var (Γ ++ signature A P) A) {reached : Tm A P Γ P}
    (steps : Relation.ReflTransGen (StrongStep (Γ := Γ))
      (recTerm (.var relation) loopStep (.var point)) reached) :
    ∃ next, StrongStep (Γ := Γ) reached next := by
  have looping : Looping (Γ := Γ) reached := by
    induction steps with
    | refl => exact .start relation point
    | tail _ step ih => exact ih.step_closed step
  exact looping.has_step

/-- The four terms of the evaluator's cycle. -/
def loopContinuation {Γ : List Ty} (relation : Var (Γ ++ signature A P) (relTy A)) :
    Tm A P Γ (.arr A P) :=
  .lam (recTerm (Γ := A :: Γ) (.var (.succ relation)) loopStep (.var .zero))

/-- **The cycle.**  Unfolding, then three beta steps, return to the start. -/
theorem loop_cycle {Γ : List Ty} (relation : Var (Γ ++ signature A P) (relTy A))
    (point : Var (Γ ++ signature A P) A) :
    StrongStep (Γ := Γ) (recTerm (.var relation) loopStep (.var point))
        (.app (.app loopStep (.var point)) (loopContinuation relation)) ∧
      StrongStep (Γ := Γ) (.app (.app loopStep (.var point)) (loopContinuation relation))
        (.app (.lam (.app (.var .zero) (.var (.succ point)))) (loopContinuation relation)) ∧
      StrongStep (Γ := Γ)
        (.app (.lam (.app (.var .zero) (.var (.succ point)))) (loopContinuation relation))
        (.app (loopContinuation relation) (.var point)) ∧
      StrongStep (Γ := Γ) (.app (loopContinuation relation) (.var point))
        (recTerm (.var relation) loopStep (.var point)) :=
  ⟨StrongStep.unfold (Γ := Γ) (.var relation) loopStep (.var point),
    StrongStep.appLeft (StrongStep.beta (Γ := Γ) (.lam (.app (.var .zero) (.var (.succ .zero))))
      (.var point)),
    StrongStep.beta (Γ := Γ) (.app (.var .zero) (.var (.succ point))) (loopContinuation relation),
    StrongStep.beta (Γ := Γ) (recTerm (Γ := A :: Γ) (.var (.succ relation)) loopStep (.var .zero))
      (.var point)⟩

/-! ### The strong variant licenses the unfolding; the carved variant decides the problem -/

/-- The negative control's context: a point of the carrier and a relation. -/
abbrev loopContext (A : Ty) : List Ty := [A, relTy A]

/-- The point variable of the negative control. -/
def loopPoint : Var (loopContext A ++ signature A P) A := .zero

/-- The relation variable of the negative control. -/
def loopRelation : Var (loopContext A ++ signature A P) (relTy A) := .succ .zero

/-- The abstract hypotheses: an accessibility proof and a respect proof, both
assumed. -/
def loopHyps : List (Tm A P (loopContext A) prop) :=
  [accCode (.var loopRelation) (.var loopPoint), respCode (.var loopRelation) loopStep]

/-- The strong variant licenses the unfolding at the abstract proof. -/
theorem loop_unfold_licensed :
    Strong A P (.conv (loopContext A) loopHyps P
      (recTerm (.var loopRelation) loopStep (.var loopPoint))
      (unfoldTerm (.var loopRelation) loopStep (.var loopPoint))) :=
  derives₂ (Or.inr (UnfoldRule.unfold _ _ _))
    (derives₀ (Or.inl (Or.inl (SharedRule.hyp mem₀))))
    (derives₀ (Or.inl (Or.inl (SharedRule.hyp mem₁))))

/-- The unfolding of the loop beta-reduces back to the recursor application. -/
theorem loop_unfold_betaConv {Γ : List Ty} (relation : Var (Γ ++ signature A P) (relTy A))
    (point : Var (Γ ++ signature A P) A) :
    BetaConv (recTerm (.var relation) loopStep (.var point))
      (unfoldTerm (.var relation) loopStep (.var point)) := by
  have first : BetaStep (unfoldTerm (Γ := Γ) (.var relation) loopStep (.var point))
      (.app (.lam (.app (.var .zero) (.var (.succ point)))) (loopContinuation relation)) :=
    BetaStep.appLeft (BetaStep.beta (.lam (.app (.var .zero) (.var (.succ .zero)))) (.var point))
  have second : BetaStep (Γ := Γ ++ signature A P)
      (.app (.lam (.app (.var .zero) (.var (.succ point)))) (loopContinuation relation))
      (.app (loopContinuation relation) (.var point)) :=
    BetaStep.beta (.app (.var .zero) (.var (.succ point))) (loopContinuation relation)
  have third : BetaStep (Γ := Γ ++ signature A P) (.app (loopContinuation relation) (.var point))
      (recTerm (.var relation) loopStep (.var point)) :=
    BetaStep.beta (recTerm (Γ := A :: Γ) (.var (.succ relation)) loopStep (.var .zero)) (.var point)
  exact .symm _ _ (.trans _ _ _ (.rel _ _ first) (.trans _ _ _ (.rel _ _ second) (.rel _ _ third)))

/-- **The carved variant decides the same problem.**  The recursor
application and its unfolding are carved-convertible, decided by comparing
beta normal forms; no unfolding is ever performed. -/
theorem loop_carved_decided :
    decideCarvedConv (recTerm (A := A) (P := P) (.var loopRelation) loopStep (.var loopPoint))
      (unfoldTerm (.var loopRelation) loopStep (.var loopPoint)) = true :=
  (decideCarvedConv_iff (hyps := loopHyps)).mpr
    (carved_conv_iff.mpr (loop_unfold_betaConv _ _))

end Mettapedia.TypeTheory.Unfolding.AccessibleRecursion
