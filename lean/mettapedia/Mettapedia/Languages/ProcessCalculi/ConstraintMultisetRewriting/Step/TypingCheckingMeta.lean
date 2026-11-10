import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingChecking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongReflection

/-!
# Checking as firings with metavariables at dependent frames

R54's checking as firings has no metavariables: its obligations are propositions, discharged when
told. Here a checking problem lives over a frame `Θ` of the dependent frames, whose variables are
the metavariables; the goals' terms and types mention them. A goal also carries a telescope of
local binders over `Θ` (`Tele`), so abstractions are checked under their binders.

## Obligations over a frame (`obligationFrames`)

An obligation over `Θ` is a property of the solutions out of `Θ`, kept under further substitution.
Obligations form a frame instance over the typed contextual category: the action is precomposition,
and two obligations are equivalent when they hold at the same solutions. An obligation is told as
the equation `p ≐ ⊤`; a solution of a store of told obligations is a substitution at which every
obligation holds (`models_tells_iff`).

## Postponement

A conversion obligation the checker cannot decide while its metavariables are open is **told and
waits**: the firing is admitted as long as the knowledge stays solvable. The residuals are type
equations and subtypings under the eventual solution, in the goal's telescope substituted by the
solution (`typeEqAt`, `belowAt`): an equation under a binder waits there. A type equation
between typed types of `Θ` is an equation of the unifier's typed βη frame
(`typeEquation`); its two annotations may be different universes, which is the heterogeneous,
twin reading of R76 (`typeEquation_sound`).

## Soundness

`completed_run_derives`: a completed run from the root goal gives, at every solution of its
knowledge, the root goal under that solution. For the kernel's rules (`Kernel.varFiring`,
`appFiring`, `lamFiring`, `switchFiring`) this is a typing derivation under the solution
(`checking_run_sound`), in particular at every solution of a unifier store that entails the
residuals (`checking_run_sound_of_store`).

## Completeness on variable applications

For a variable, and for a variable of a syntactic dependent function type applied to an argument,
every residual the checker postpones holds at the identity solution whenever the goal is typed in
the frame itself, hence at every later solution (`switch_complete`, `app_complete`): the checker
never refuses a goal the frame already types. Completeness at an arbitrary later solution is not
claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingCheckingMeta

open _root_.CategoryTheory
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Obligations over a frame -/

/-- An obligation over the frame `Θ`: a property of solutions out of `Θ`, kept under further
substitution. -/
structure Obligation (Θ : Context S.R) where
  holds : ∀ {Δ : Context S.R}, (Δ ⟶ Θ) → Prop
  stable : ∀ {Δ Δ' : Context S.R} (σ : Δ ⟶ Θ) (ρ : Δ' ⟶ Δ), holds σ → holds (ρ ≫ σ)

theorem Obligation.ext' {Θ : Context S.R} {P Q : Obligation Θ}
    (same : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), P.holds σ = Q.holds σ) : P = Q := by
  cases P with
  | mk holdsP stableP =>
  cases Q with
  | mk holdsQ stableQ =>
  have : @holdsP = @holdsQ := by
    funext Δ σ
    exact same σ
  subst this
  rfl

/-- An obligation read at a later frame. -/
def Obligation.pull {Θ Θ' : Context S.R} (ρ : Θ' ⟶ Θ) (P : Obligation Θ) : Obligation Θ' where
  holds τ := P.holds (τ ≫ ρ)
  stable σ ρ' held := by simpa [Category.assoc] using P.stable (σ ≫ ρ) ρ' held

/-- The obligation that always holds. -/
def Obligation.truth (Θ : Context S.R) : Obligation Θ := ⟨fun _ => True, fun _ _ _ => trivial⟩

variable (S) in
/-- **Obligations as a frame instance** over the typed contextual category. -/
def obligationFrames :
    Frames (fun Θ : Context S.R => Obligation Θ) (fun Θ Δ : Context S.R => Δ ⟶ Θ) where
  E P Q := ∀ {Δ : Context S.R} (σ : Δ ⟶ _), P.holds σ ↔ Q.holds σ
  equivalence _ := ⟨fun _ _ _ => Iff.rfl, fun same _ σ => (same σ).symm,
    fun first second _ σ => (first σ).trans (second σ)⟩
  act ρ P := P.pull ρ
  id Θ := 𝟙 Θ
  comp g f := g ≫ f
  act_id P := Obligation.ext' fun σ => by simp [Obligation.pull]
  act_comp g f P := Obligation.ext' fun σ => by simp [Obligation.pull, Category.assoc]
  preserves := fun {_ _} f {_ _} same {_} σ => same (σ ≫ f)

/-- Tell an obligation. -/
def tell {Θ : Context S.R} (P : Obligation Θ) : Equation (Obligation Θ) := (P, Obligation.truth Θ)

/-- **A solution of told obligations is a substitution at which they hold.** -/
theorem models_tells_iff {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (ps : List (Obligation Θ)) :
    (obligationFrames S).Models σ (ps.map tell) ↔ ∀ P ∈ ps, P.holds σ := by
  constructor
  · intro solved P member
    have equation := solved (tell P) (List.mem_map_of_mem member) (𝟙 _)
    simpa [Obligation.pull, obligationFrames, tell, Obligation.truth] using equation
  · intro holds e member
    obtain ⟨P, present, rfl⟩ := List.mem_map.mp member
    intro _ τ
    exact iff_true_intro (P.stable σ τ (holds P present))

/-! ## Local telescopes -/

/-- A substitution lifted under `k` binders. -/
def liftK {m m' : Nat} (σ : Sub Head m m') : (k : Nat) → Sub Head (m + k) (m' + k)
  | 0 => σ
  | k + 1 => liftSub (liftK σ k)

theorem liftK_subComp {m m' m'' : Nat} (ρ : Sub Head m' m'') (σ : Sub Head m m') :
    ∀ k, subComp (liftK ρ k) (liftK σ k) = liftK (subComp ρ σ) k
  | 0 => rfl
  | k + 1 => by
      show subComp (liftSub (liftK ρ k)) (liftSub (liftK σ k)) = liftSub (liftK (subComp ρ σ) k)
      rw [liftSub_subComp, liftK_subComp ρ σ k]

variable (Head) in
/-- A telescope of `k` local binders over a scope of `m` variables. -/
inductive Tele (m : Nat) : Nat → Type
  | nil : Tele m 0
  | snoc {k : Nat} (rest : Tele m k) (A : Tm Head (m + k)) : Tele m (k + 1)

/-- A context extended by a telescope. -/
def Tele.ctx {m : Nat} (Γ : Ctx Head m) : {k : Nat} → Tele Head m k → Ctx Head (m + k)
  | _, .nil => Γ
  | _, .snoc rest A => .snoc (rest.ctx Γ) A

/-- A telescope under a substitution of its scope. -/
def Tele.map {m m' : Nat} (σ : Sub Head m m') : {k : Nat} → Tele Head m k → Tele Head m' k
  | _, .nil => .nil
  | _, .snoc (k := j) rest A => .snoc (rest.map σ) (subst (liftK σ j) A)

theorem Tele.map_comp {m m' m'' : Nat} (ρ : Sub Head m' m'') (σ : Sub Head m m') :
    ∀ {k : Nat} (T : Tele Head m k), (T.map σ).map ρ = T.map (subComp ρ σ)
  | _, .nil => rfl
  | _, .snoc (k := j) rest A => by
      show Tele.snoc ((rest.map σ).map ρ) (subst (liftK ρ j) (subst (liftK σ j) A)) =
        Tele.snoc (rest.map (subComp ρ σ)) (subst (liftK (subComp ρ σ) j) A)
      rw [Tele.map_comp ρ σ rest, subst_subComp, liftK_subComp]

/-- A typed substitution of the scope is a typed substitution of the extended contexts. -/
theorem Tele.substMor {m m' : Nat} {Γ : Ctx Head m} {Δ : Ctx Head m'} {σ : Sub Head m m'}
    (typed : SubstMor S.R Γ Δ σ) :
    ∀ {k : Nat} (T : Tele Head m k), SubstMor S.R (T.ctx Γ) ((T.map σ).ctx Δ) (liftK σ k)
  | _, .nil => typed
  | _, .snoc rest A => (Tele.substMor typed rest).lift A

/-! ## The residual obligations of checking -/

/-- The obligation that two types are equal under the solution, in a local telescope. -/
def typeEqAt {Θ : Context S.R} {k : Nat} (T : Tele Head Θ.arity k) (A B : Tm Head (Θ.arity + k)) :
    Obligation Θ where
  holds {Δ} σ := TypeEq S.R ((T.map σ.substitution).ctx Δ.raw)
    (subst (liftK σ.substitution k) A) (subst (liftK σ.substitution k) B)
  stable {_ Δ'} σ ρ held := by
    obtain ⟨u, hu, e⟩ := held
    have moved := e.substitute (Tele.substMor ρ.typed (T.map σ.substitution))
    show TypeEq S.R ((T.map (subComp ρ.substitution σ.substitution)).ctx Δ'.raw)
      (subst (liftK (subComp ρ.substitution σ.substitution) k) A)
      (subst (liftK (subComp ρ.substitution σ.substitution) k) B)
    rw [← Tele.map_comp, ← liftK_subComp, ← subst_subComp, ← subst_subComp]
    exact ⟨u, hu, moved⟩

/-- The obligation that one type is usable at another under the solution, in a local
telescope. -/
def belowAt {Θ : Context S.R} {k : Nat} (T : Tele Head Θ.arity k) (A B : Tm Head (Θ.arity + k)) :
    Obligation Θ where
  holds {Δ} σ := Below S.R ((T.map σ.substitution).ctx Δ.raw)
    (subst (liftK σ.substitution k) A) (subst (liftK σ.substitution k) B)
  stable {_ Δ'} σ ρ held := by
    have moved : Below S.R (((T.map σ.substitution).map ρ.substitution).ctx Δ'.raw)
        (subst (liftK ρ.substitution k) (subst (liftK σ.substitution k) A))
        (subst (liftK ρ.substitution k) (subst (liftK σ.substitution k) B)) :=
      Derivable.substitutes held (Tele.substMor ρ.typed (T.map σ.substitution))
    show Below S.R ((T.map (subComp ρ.substitution σ.substitution)).ctx Δ'.raw)
      (subst (liftK (subComp ρ.substitution σ.substitution) k) A)
      (subst (liftK (subComp ρ.substitution σ.substitution) k) B)
    rw [← Tele.map_comp, ← liftK_subComp, ← subst_subComp, ← subst_subComp]
    exact moved

/-- The type equation of two typed types of `Θ`, as an equation of the unifier's typed βη frame.
Its annotations are the two universes, which may differ: a heterogeneous equation. -/
noncomputable def typeEquation {Θ : Context S.R} (A B : TypeOver Θ) : Equation (TotalTerm Θ) :=
  (⟨⟨.head A.level, _, (S.levels.successor A.universeWitness).choose_spec.1,
      .headType (S.levels.successor A.universeWitness).choose_spec.2.1⟩, ⟨A.code, A.formed⟩⟩,
    ⟨⟨.head B.level, _, (S.levels.successor B.universeWitness).choose_spec.1,
      .headType (S.levels.successor B.universeWitness).choose_spec.2.1⟩, ⟨B.code, B.formed⟩⟩)

/-- **A solution of the frame equation solves the type equation obligation.** -/
theorem typeEquation_sound {Θ Δ : Context S.R} (A B : TypeOver Θ) (σ : Δ ⟶ Θ)
    (solved : (ContextualDependentEta.frames S.levels).Solves σ (typeEquation A B)) :
    (typeEqAt .nil A.code B.code).holds σ := by
  show TypeEq S.R Δ.raw (subst σ.substitution A.code) (subst σ.substitution B.code)
  exact ⟨A.level, A.universeWitness, solved.2⟩

/-! ## Goals and goal firings -/

/-- A checking goal over `Θ`: a local telescope, a mode, a term and a type, mentioning the
metavariables of `Θ`. -/
structure Goal (Θ : Context S.R) where
  k : Nat
  tele : Tele Head Θ.arity k
  mode : Mode
  term : Tm Head (Θ.arity + k)
  type : Tm Head (Θ.arity + k)

variable {Θ : Context S.R}

/-- A goal **holds under a solution**: whenever its local context is formed under the solution,
a synthesis goal is a typing of the instance, and a checking goal is one whenever its
instantiated type is a type. -/
def HoldsAt {Δ : Context S.R} (σ : Δ ⟶ Θ) : Goal Θ → Prop
  | ⟨k, T, .synth, t, A⟩ => CtxFormed S.R ((T.map σ.substitution).ctx Δ.raw) →
      Typed S.R ((T.map σ.substitution).ctx Δ.raw) (subst (liftK σ.substitution k) t)
        (subst (liftK σ.substitution k) A)
  | ⟨k, T, .check, t, A⟩ => CtxFormed S.R ((T.map σ.substitution).ctx Δ.raw) →
      IsType S.R ((T.map σ.substitution).ctx Δ.raw) (subst (liftK σ.substitution k) A) →
      Typed S.R ((T.map σ.substitution).ctx Δ.raw) (subst (liftK σ.substitution k) t)
        (subst (liftK σ.substitution k) A)

variable {O : Type} [DecidableEq O]

variable (Θ O) in
/-- A state of checking: goal labels, present goals and told obligations over `Θ`. -/
structure GoalState where
  goal : O → Goal Θ
  present : Finset O
  knowledge : EquationStore (Obligation Θ)

/-- **A goal firing with postponed residuals**: it takes one goal, makes premise goals and tells
residual obligations. Its certificate is local and holds at every solution. -/
structure GoalFiring (s : GoalState Θ O) where
  taken : O
  made : List O
  premise : O → Goal Θ
  residuals : List (Obligation Θ)
  sound : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), (∀ o ∈ made, HoldsAt σ (premise o)) →
    (∀ P ∈ residuals, P.holds σ) → HoldsAt σ (s.goal taken)

namespace GoalFiring

variable {s : GoalState Θ O} (f : GoalFiring s)

def selection : Selection O := ⟨[f.taken], [], f.made⟩

/-- The state after a goal firing: the residuals are told and wait. -/
def after : GoalState Θ O :=
  ⟨fun o => if o ∈ f.made then f.premise o else s.goal o,
    fire s.present (f.selection.commit (T := Unit)), s.knowledge ++ f.residuals.map tell⟩

end GoalFiring

variable (Θ O) in
/-- **The checking step with metavariables**, over the obligation frames at the frame `Θ`. -/
def metaGoalStep :
    Interface.Step.Standard (obligationFrames S) O (GoalState Θ O) (fun s => GoalFiring s) where
  frame _ := Θ
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target _ := Θ
  extension _ := 𝟙 Θ
  information {s} f := s.knowledge ++ f.residuals.map tell
  transported := by
    intro s _ e member
    have same : ((obligationFrames S).act ((obligationFrames S).id Θ) e.1,
        (obligationFrames S).act ((obligationFrames S).id Θ) e.2) = e := by
      rw [(obligationFrames S).act_id, (obligationFrames S).act_id]
    exact same ▸ List.mem_append_left _ member
  Shapes f := f.made.Nodup
  Holds _ _ _ := True
  Admits {s} f := f.made.Nodup ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (obligationFrames S).Solvable (a := Θ) (s.knowledge ++ f.residuals.map tell) ∧
    (obligationFrames S).Entails (a := Θ) (s.knowledge ++ f.residuals.map tell) (fun _ _ => True)
  admits_iff _ := Iff.rfl
  preparedResult f _ := f.after
  present_preparedResult _ _ := rfl
  preparedSettle _ _ := 𝟙 Θ
  knowledge_preparedResult {s} f _ :=
    (Frames.applyStore_id (X := obligationFrames S) (s.knowledge ++ f.residuals.map tell)).symm

/-- A state **reaches** the root when, at every solution of its knowledge, its present goals give
the root. -/
def Reaches (root : Goal Θ) (s : GoalState Θ O) : Prop :=
  ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), (obligationFrames S).Models σ s.knowledge →
    (∀ o ∈ s.present, HoldsAt σ (s.goal o)) → HoldsAt σ root

/-- **Admitted firings keep reaching the root.** -/
theorem reaches_step {root : Goal Θ} {s : GoalState Θ O} (f : GoalFiring s)
    (admitted : (metaGoalStep Θ O).Admits f) (reach : Reaches root s) :
    Reaches root f.after := by
  intro Δ σ solved derived
  have old : (obligationFrames S).Models σ s.knowledge :=
    fun e member => solved e (List.mem_append_left _ member)
  have told : (obligationFrames S).Models σ (f.residuals.map tell) :=
    fun e member => solved e (List.mem_append_right _ member)
  have residual := (models_tells_iff σ f.residuals).mp told
  have premises : ∀ o ∈ f.made, HoldsAt σ (f.premise o) := by
    intro o made
    have present : o ∈ f.after.present :=
      mem_fire.mpr (.inr (by simpa [GoalFiring.selection, Selection.commit] using made))
    have := derived o present
    simpa [GoalFiring.after, made] using this
  have takenHolds := f.sound σ premises residual
  apply reach σ old
  intro o present
  by_cases taken : o = f.taken
  · rw [taken]
    exact takenHolds
  · have stays : o ∈ f.after.present :=
      mem_fire.mpr (.inl ⟨present, by simpa [GoalFiring.selection, Selection.commit] using taken⟩)
    have notMade : o ∉ f.made := by
      have outside := Finset.disjoint_right.mp admitted.2.1.fresh present
      simpa [GoalFiring.selection, Selection.commit] using outside
    have := derived o stays
    simpa [GoalFiring.after, notMade] using this

/-- **Every run keeps reaching the root.** -/
theorem reaches_run {root : Goal Θ} : ∀ {s : GoalState Θ O} (r : (metaGoalStep Θ O).Run s),
    Reaches root s → Reaches root r.last
  | _, .nil _, reach => reach
  | _, .cons f admitted rest, reach => reaches_run rest (reaches_step f admitted reach)

/-- **Soundness**: a completed run from the root goal gives the root under every solution of
its final knowledge, the postponed residuals included. -/
theorem completed_run_derives {root : Goal Θ} {s₀ : GoalState Θ O} {o₀ : O}
    (start : s₀.present = {o₀}) (rootGoal : s₀.goal o₀ = root) (r : (metaGoalStep Θ O).Run s₀)
    (done : r.last.present = ∅) {Δ : Context S.R} (σ : Δ ⟶ Θ)
    (solved : (obligationFrames S).Models σ r.last.knowledge)
    (initial : (obligationFrames S).Models σ s₀.knowledge) : HoldsAt σ root := by
  have reach : Reaches root s₀ := fun σ' _ derived => by
    rw [← rootGoal]
    exact derived o₀ (by rw [start]; exact Finset.mem_singleton_self o₀)
  have _ := initial
  exact reaches_run r reach σ solved (fun o present => by rw [done] at present; cases present)

/-- A firing whose told residuals cannot hold together with the knowledge is refused. -/
theorem refused_of_unsolvable {s : GoalState Θ O} (f : GoalFiring s)
    (unsolvable : ¬ (obligationFrames S).Solvable (a := Θ) (s.knowledge ++ f.residuals.map tell)) :
    ¬ (metaGoalStep Θ O).Admits f :=
  fun admitted => unsolvable admitted.2.2.1

/-! ## The kernel's rules -/

namespace Kernel

/-- Synthesize a variable, local, metavariable or not. -/
def varFiring (s : GoalState Θ O) (taken : O) {k : Nat} (T : Tele Head Θ.arity k)
    (i : Fin (Θ.arity + k))
    (labelled : s.goal taken = ⟨k, T, .synth, .var i, Ctx.lookup (T.ctx Θ.raw) i⟩) :
    GoalFiring s where
  taken := taken
  made := []
  premise _ := ⟨k, T, .synth, .var i, Ctx.lookup (T.ctx Θ.raw) i⟩
  residuals := []
  sound σ _ _ := by
    rw [labelled]
    intro _
    exact Typed.substitute (Derivable.var i) (Tele.substMor σ.typed T)

/-- Synthesize an application: synthesize the function at `F`, check the argument at `A`, and
tell that `F` is the dependent function type `Π A B` under the solution. The equation waits when
`F` is a metavariable. -/
def appFiring (s : GoalState Θ O) (taken first second : O) (distinct : first ≠ second)
    {k : Nat} (T : Tele Head Θ.arity k) (f a F A : Tm Head (Θ.arity + k))
    (B : Tm Head (Θ.arity + k + 1))
    (labelled : s.goal taken = ⟨k, T, .synth, .app f a, inst0 a B⟩) : GoalFiring s where
  taken := taken
  made := [first, second]
  premise o := if o = first then ⟨k, T, .synth, f, F⟩ else ⟨k, T, .check, a, A⟩
  residuals := [typeEqAt T F (.pi A B)]
  sound {Δ} σ premises residual := by
    rw [labelled]
    intro formed
    have function : HoldsAt σ ⟨k, T, .synth, f, F⟩ := by
      have premise := premises first (by simp)
      rwa [if_pos rfl] at premise
    have argument : HoldsAt σ ⟨k, T, .check, a, A⟩ := by
      have premise := premises second (by simp)
      rwa [if_neg (Ne.symm distinct)] at premise
    have equal : TypeEq S.R ((T.map σ.substitution).ctx Δ.raw)
        (subst (liftK σ.substitution k) F)
        (.pi (subst (liftK σ.substitution k) A) (subst (liftSub (liftK σ.substitution k)) B)) :=
      residual _ (List.mem_singleton_self _)
    have tf := Typed.convType (function formed) equal
    have isPi := (TypeEq.isType equal formed).2
    have ta := argument formed (IsType.pi_parts isPi).1
    show Typed S.R _ (subst (liftK σ.substitution k) (.app f a))
      (subst (liftK σ.substitution k) (inst0 a B))
    rw [subst_inst0]
    exact .appElim tf ta

/-- Check an abstraction: tell that the expected type is the dependent function type `Π A B`
under the solution, and check the body under the binder `A`. The equation waits while the
expected type has open metavariables. -/
def lamFiring (s : GoalState Θ O) (taken made : O) {k : Nat} (T : Tele Head Θ.arity k)
    (b : Tm Head (Θ.arity + k + 1)) (E A : Tm Head (Θ.arity + k)) (B : Tm Head (Θ.arity + k + 1))
    (labelled : s.goal taken = ⟨k, T, .check, .lam b, E⟩) : GoalFiring s where
  taken := taken
  made := [made]
  premise _ := ⟨k + 1, T.snoc A, .check, b, B⟩
  residuals := [typeEqAt T E (.pi A B)]
  sound {Δ} σ premises residual := by
    rw [labelled]
    intro formed _
    have equal : TypeEq S.R ((T.map σ.substitution).ctx Δ.raw)
        (subst (liftK σ.substitution k) E)
        (.pi (subst (liftK σ.substitution k) A) (subst (liftSub (liftK σ.substitution k)) B)) :=
      residual _ (List.mem_singleton_self _)
    have isPi := (TypeEq.isType equal formed).2
    obtain ⟨⟨u, hu, tA⟩, ⟨v, hv, tB⟩⟩ := IsType.pi_parts isPi
    have formedA : CtxFormed S.R (.snoc ((T.map σ.substitution).ctx Δ.raw)
        (subst (liftK σ.substitution k) A)) := .snoc formed ⟨u, hu, tA⟩
    have body := premises made (List.mem_singleton_self _) formedA ⟨v, hv, tB⟩
    obtain ⟨w, hw, tPi⟩ := isPi
    exact Typed.convType (.lamIntro tPi hw body) equal.symm

/-- Check by synthesis: synthesize a type `T`, and tell that it is usable at the expected type.
The subtyping waits while either side has open metavariables. -/
def switchFiring (s : GoalState Θ O) (taken made : O) {k : Nat} (T : Tele Head Θ.arity k)
    (t A E : Tm Head (Θ.arity + k)) (labelled : s.goal taken = ⟨k, T, .check, t, E⟩) :
    GoalFiring s where
  taken := taken
  made := [made]
  premise _ := ⟨k, T, .synth, t, A⟩
  residuals := [belowAt T A E]
  sound σ premises residual := by
    rw [labelled]
    intro formed _
    exact .sub (premises made (List.mem_singleton_self _) formed)
      (residual _ (List.mem_singleton_self _))

end Kernel

/-- **A completed checking run is a typing derivation under every solution of its knowledge.** -/
theorem checking_run_sound {s₀ : GoalState Θ O} {o₀ : O} {t T : Tm Head Θ.arity}
    (start : s₀.present = {o₀}) (rootGoal : s₀.goal o₀ = ⟨0, .nil, .check, t, T⟩)
    (r : (metaGoalStep Θ O).Run s₀) (done : r.last.present = ∅) {Δ : Context S.R} (σ : Δ ⟶ Θ)
    (solved : (obligationFrames S).Models σ r.last.knowledge)
    (initial : (obligationFrames S).Models σ s₀.knowledge)
    (type : IsType S.R Δ.raw (subst σ.substitution T)) :
    Typed S.R Δ.raw (subst σ.substitution t) (subst σ.substitution T) :=
  completed_run_derives start rootGoal r done σ solved initial Δ.formed type

/-- **Solutions of the unifier**: a solution of a store of the unifier's frame that entails every
residual of a completed run gives the typing under that solution. -/
theorem checking_run_sound_of_store {s₀ : GoalState Θ O} {o₀ : O} {t T : Tm Head Θ.arity}
    (start : s₀.present = {o₀}) (rootGoal : s₀.goal o₀ = ⟨0, .nil, .check, t, T⟩)
    (r : (metaGoalStep Θ O).Run s₀) (done : r.last.present = ∅)
    (K : EquationStore (TotalTerm Θ))
    (entails : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), (ContextualDependentEta.frames S.levels).Models σ K →
      (obligationFrames S).Models σ r.last.knowledge)
    (initial : (obligationFrames S).Models (𝟙 Θ) s₀.knowledge)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) (solved : (ContextualDependentEta.frames S.levels).Models σ K)
    (type : IsType S.R Δ.raw (subst σ.substitution T)) :
    Typed S.R Δ.raw (subst σ.substitution t) (subst σ.substitution T) := by
  have initialAt : (obligationFrames S).Models σ s₀.knowledge := by
    have moved := Frames.models_comp initial σ
    have same : (obligationFrames S).comp σ (𝟙 Θ) = σ := Category.comp_id σ
    rwa [same] at moved
  exact checking_run_sound start rootGoal r done σ (entails σ solved) initialAt type

/-! ## Completeness on variable applications -/

theorem subst_identity (t : Tm Head Θ.arity) :
    subst (𝟙 Θ : Θ ⟶ Θ).substitution t = t := subst_ids t

/-- **The postponed subtyping of a variable is necessary**: if the variable is typed at `E` in the
frame itself, its type is usable at `E` at the identity solution, hence at every solution. -/
theorem switch_complete (i : Fin Θ.arity) {E : Tm Head Θ.arity}
    (typed : Typed S.R Θ.raw (.var i) E) : (belowAt .nil (Ctx.lookup Θ.raw i) E).holds (𝟙 Θ) := by
  show Below S.R Θ.raw (subst (𝟙 Θ : Θ ⟶ Θ).substitution (Ctx.lookup Θ.raw i))
    (subst (𝟙 Θ : Θ ⟶ Θ).substitution E)
  rw [subst_identity, subst_identity]
  exact TypeLe.toBelow (typed.generation : TypeLe S.R Θ.raw (Ctx.lookup Θ.raw i) E)
    (Typed.isType typed Θ.formed)

/-- **The residuals of a variable application are necessary**: for `f a` with `f` a variable of
the syntactic type `Π A B`, if `f a` is typed at `T` in the frame itself, then the argument is
typed at `A`, and the told equation and subtyping hold at the identity solution, hence at every
solution. -/
theorem app_complete (facts : FormFacts S.R S.roles) (j : Fin Θ.arity) {a A T : Tm Head Θ.arity}
    {B : Tm Head (Θ.arity + 1)} (declared : Ctx.lookup Θ.raw j = .pi A B)
    (typed : Typed S.R Θ.raw (.app (.var j) a) T) :
    Typed S.R Θ.raw a A ∧ (typeEqAt .nil (Ctx.lookup Θ.raw j) (.pi A B)).holds (𝟙 Θ) ∧
      (belowAt .nil (inst0 a B) T).holds (𝟙 Θ) := by
  obtain ⟨A', B', tf, ta, le⟩ := typed.generation
  have lookupLe : TypeLe S.R Θ.raw (Ctx.lookup Θ.raw j) (.pi A' B') := tf.generation
  rw [declared] at lookupLe
  have isPi' : IsType S.R Θ.raw (.pi A' B') := Typed.isType tf Θ.formed
  obtain ⟨eA, leB⟩ := TypeLe.pi_parts facts lookupLe isPi' Θ.formed
  have ta' : Typed S.R Θ.raw a A := Typed.convType ta eA.symm
  have isPi : IsType S.R Θ.raw (.pi A B) := by
    rw [← declared]
    exact Typed.isType (Derivable.var j) Θ.formed
  refine ⟨ta', ?_, ?_⟩
  · show TypeEq S.R Θ.raw (subst (𝟙 Θ : Θ ⟶ Θ).substitution (Ctx.lookup Θ.raw j))
      (subst (𝟙 Θ : Θ ⟶ Θ).substitution (.pi A B))
    rw [subst_identity, subst_identity, declared]
    exact IsType.refl isPi
  · show Below S.R Θ.raw (subst (𝟙 Θ : Θ ⟶ Θ).substitution (inst0 a B))
      (subst (𝟙 Θ : Θ ⟶ Θ).substitution T)
    rw [subst_identity, subst_identity]
    have below : Below S.R Θ.raw (inst0 a B) (inst0 a B') :=
      Derivable.substitutes leB (SubstMor.single ta')
    exact .subTrans below (TypeLe.toBelow le (Typed.isType typed Θ.formed))

#print axioms obligationFrames
#print axioms models_tells_iff
#print axioms Tele.substMor
#print axioms typeEquation_sound
#print axioms reaches_step
#print axioms reaches_run
#print axioms completed_run_derives
#print axioms refused_of_unsolvable
#print axioms Kernel.lamFiring
#print axioms checking_run_sound
#print axioms checking_run_sound_of_store
#print axioms switch_complete
#print axioms app_complete

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingCheckingMeta
