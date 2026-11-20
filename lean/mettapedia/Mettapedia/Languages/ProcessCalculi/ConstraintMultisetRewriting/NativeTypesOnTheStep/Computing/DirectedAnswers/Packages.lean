import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Normalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Syntax.Qualified
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.ListFunction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.ValueType
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.QualifiedControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Spines

/-!
# The hypotheses of the answer theorems, across the qualified packages of the tree

The existence theorem at an inductive type (`inductive_reaches`, `inductive_answer`) asks of a package a
normalization model, an inductive type whose constructor fields are all recursive, and that no closed
neutral term is typed at that type. The relation between the two notions of answer
(`answer_iff_headFree`) asks for a constructor presentation whose heads are related to themselves. This
module says which packages meet which hypothesis.

* **A third package for the existence theorem**: in the bare numbers package every closed number has
  exactly one answer, a numeral (`numbers_num_answer`), besides the vectors package (`num_answer`) and
  `Eventually.Erasing` (`erasing_num_answer`).
* **The hypothesis on closed neutral terms at the type cannot be dropped** (`lists_control`). The lists
  package is qualified, its numbers are an inductive type with recursive fields, and it declares a
  function `step : num → num → num` without equations. The closed term `step zero zero` is neutral and
  typed at the numbers; it is a directed normal form, its own and only answer, and no constructor tree.
  Every other hypothesis of `inductive_answer` holds there.
* **The hypothesis on all types is stronger than the theorem needs** (`executable_separates`). The
  executable package is qualified and its numbers are an inductive type with recursive fields. The
  hypothesis on all types fails there, at the rigid declared sort `set : U₀`, a closed neutral term of
  a universe (`executable_has_closed_neutral`). The hypothesis at the type holds: no closed neutral
  term is typed at its numbers (`executable_noNeutralAt`), because its rigid constants, the sort of sets
  and the power set, are typed above `U₀`, `set → set` and `set` only, and every computing constant
  inspects an argument of the numbers or of an identity type (`executable_rigid_types`,
  `executable_inspected`, by the general criterion `noClosedNeutralAt_of_rigid`). So every closed number
  of that package answers a numeral (`executable_num_answer`).
* **Recursive fields**: the lists package's type of lists has a field of a closed type, so the existence
  theorem does not apply at lists (`lists_outside`).
* **Qualification does not give the hypothesis on closed neutral terms**: the rigid vectors package is
  qualified and types the closed neutral term `zero` (`rigid_has_closed_neutral`).
* **Heads related to themselves**: in each of the seven qualified packages of the tree every head is
  related to itself (`qualified_heads_reflexive`), so there the answers of the full reduction are exactly
  the answers without heads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DirectedAnswers

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u)
open Definitions (nat)

variable (lv : LevelExpr Nat)

/-! ## The bare numbers package -/

/-- Every declared constant of the numbers package is not rigid. -/
theorem numbers_declared (c : DeclName) (type : Tm Tower.Head 0)
    (declared : (TowerNumbersModel.rules lv).constantType c = some type) :
    TowerNumbersModel.roles c ≠ .rigid := by
  intro rigid
  by_cases hnum : c = num
  · subst hnum
    rw [TowerNumbersModel.roles_num] at rigid
    cases rigid
  by_cases hzero : c = zero
  · subst hzero
    rw [TowerNumbersModel.roles_zero] at rigid
    cases rigid
  by_cases hsucc : c = succ
  · subst hsucc
    rw [TowerNumbersModel.roles_succ] at rigid
    cases rigid
  by_cases hrec : c = numRec
  · subst hrec
    rw [TowerNumbersModel.roles_numRec] at rigid
    cases rigid
  have undeclared : (TowerNumbersModel.rules lv).constantType c = none := by
    simp [TowerNumbersModel.rules, TowerNumbersModel.constantType, hnum, hzero, hsucc, hrec]
  rw [undeclared] at declared
  cases declared

/-- Its computing constant inspects one argument. -/
theorem numbers_inspects (c : DeclName) (arity : Nat) (inspect : InspectTree)
    (role : TowerNumbersModel.roles c = .computes arity inspect) :
    inspect = .leaf ∨ ∃ k, inspect = .split k .constructor fun _ => .leaf := by
  by_cases hrec : c = numRec
  · subst hrec
    rw [TowerNumbersModel.roles_numRec] at role
    cases role
    exact .inr ⟨3, rfl⟩
  by_cases hnum : c = num
  · subst hnum
    rw [TowerNumbersModel.roles_num] at role
    cases role
  by_cases hzero : c = zero
  · subst hzero
    rw [TowerNumbersModel.roles_zero] at role
    cases role
  by_cases hsucc : c = succ
  · subst hsucc
    rw [TowerNumbersModel.roles_succ] at role
    cases role
  have rigid : TowerNumbersModel.roles c = .rigid := by
    simp [TowerNumbersModel.roles, hnum, hzero, hsucc, hrec]
  rw [rigid] at role
  cases role

/-- No closed neutral term is typed in the numbers package. -/
theorem numbers_noNeutral : NoClosedNeutral (TowerNumbersModel.setting lv fun _ => 0) :=
  fun _ A neutral typed => no_closed_neutral (numbers_declared lv) numbers_inspects neutral rfl .nil A typed

/-- **In the bare numbers package every closed number has exactly one answer, a numeral.** -/
theorem numbers_num_answer {t : Tm Tower.Head 0}
    (typing : Typed (TowerNumbersModel.rules lv) .nil t (.const num)) :
    ∃ k, DirectedAnswer (TowerNumbersModel.rules lv) t (nat k) ∧
      ∀ w, DirectedAnswer (TowerNumbersModel.rules lv) t w ↔ w = nat k := by
  obtain ⟨v, tree, answer, -, unique⟩ := inductive_answer (S := TowerNumbersModel.setting lv fun _ => 0)
    (ValueType.numbers_qualified lv) (noClosedNeutralAt_of (numbers_noNeutral lv) num)
    (show (TowerNumbersModel.setting lv fun _ => 0).roles num = .inductive ctors from TowerNumbersModel.roles_num)
    numbers_recursive typing
  obtain ⟨k, rfl⟩ := ctorTree_numeral tree
  exact ⟨k, answer, fun w => ⟨unique w, fun same => same ▸ answer⟩⟩

/-! ## The lists package: a closed neutral term at the numbers -/

section Lists

open TowerListAccumulatorsModel (step)

/-- `step zero zero`: a call of the declared function `step : num → num → num`, which has no
equations. -/
abbrev stepCall : Tm Tower.Head 0 := appSpine (.const step) [.const zero, .const zero]

/-- It is a neutral term: a rigid constant applied to arguments. -/
theorem stepCall_neutral : Neutral (TowerListAccumulatorsModel.setting lv fun _ => 0).roles stepCall :=
  Neutral.rigid (roles := (TowerListAccumulatorsModel.setting lv fun _ => 0).roles) _
    TowerListAccumulatorsModel.roles_step

/-- It is typed at the numbers. -/
theorem stepCall_typed : Typed (TowerListAccumulatorsModel.rules lv) .nil stepCall (.const num) := by
  have numT : ∀ {n : Nat} {Γ : Ctx Tower.Head n},
      Typed (TowerListAccumulatorsModel.rules lv) Γ (.const num) (.head u) :=
    TowerListAccumulatorsModel.const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
  have zeroT : Typed (TowerListAccumulatorsModel.rules lv) .nil (.const zero : Tm Tower.Head 0) (.const num) :=
    .const (type := ctorType num []) rfl numT (.sort _)
  have stepT : Typed (TowerListAccumulatorsModel.rules lv) .nil (.const step : Tm Tower.Head 0)
      (.pi (.const num) (.pi (.const num) (.const num))) :=
    .const (type := TowerListAccumulatorsModel.stepType) rfl
      (.piForm numT (.sort _) (.piForm numT (.sort _) numT (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _))
      (.sort _)
  exact .appElim (.appElim stepT zeroT) zeroT

/-- It is a directed normal form: `step` and `zero` do not compute. -/
theorem stepCall_normal :
    ContextualDependentExecutableJoin.Normal (TowerListAccumulatorsModel.rules lv) stepCall := by
  have zeroNormal : ContextualDependentExecutableJoin.Normal (TowerListAccumulatorsModel.rules lv)
      (.const zero : Tm Tower.Head 0) :=
    ctorSpine_normal (S := TowerListAccumulatorsModel.setting lv fun _ => 0) (k := zero) (m := 0)
      (show (TowerListAccumulatorsModel.setting lv fun _ => 0).roles zero = .constructor 0 from
        TowerListAccumulatorsModel.roles_zero) []
      (fun _ member => absurd member List.not_mem_nil)
  refine spine_normal (S := TowerListAccumulatorsModel.setting lv fun _ => 0) (k := step) ?_ _ ?_
  · intro arity inspect computes
    have rigid : (TowerListAccumulatorsModel.setting lv fun _ => 0).roles step = .rigid :=
      TowerListAccumulatorsModel.roles_step
    rw [rigid] at computes
    cases computes
  · intro a member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst member
    exact zeroNormal

/-- It is no constructor tree of the numbers. -/
theorem stepCall_not_tree :
    ¬ CtorTree (ctors : List (DeclName × List (Normalization.Field Tower.Head))) stepCall := by
  intro tree
  obtain ⟨k, fields, args, mem, same⟩ := tree.head_mem
  obtain ⟨rfl, -⟩ := appSpine_const_injective same
  simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

/-- **The hypothesis on closed neutral terms at the type cannot be dropped.** In the lists package, which
is qualified and whose numbers are an inductive type with recursive fields, the closed term
`step zero zero` is neutral and typed at the numbers, so the hypothesis fails; the term is its own and
only answer, and it reaches no constructor tree. No other hypothesis of `inductive_answer` fails. -/
theorem lists_control :
    Nonempty (Qualified (TowerListAccumulatorsModel.setting lv fun _ => 0)) ∧
      (TowerListAccumulatorsModel.setting lv fun _ => 0).roles num = .inductive ctors ∧
      RecursiveFields (ctors : List (DeclName × List (Normalization.Field Tower.Head))) ∧
      Typed (TowerListAccumulatorsModel.rules lv) .nil stepCall (.const num) ∧
      ¬ NoClosedNeutralAt (TowerListAccumulatorsModel.setting lv fun _ => 0) num ∧
      (∀ w, DirectedAnswer (TowerListAccumulatorsModel.rules lv) stepCall w ↔ w = stepCall) ∧
      ¬ ∃ v, CtorTree (ctors : List (DeclName × List (Normalization.Field Tower.Head))) v ∧
        StrongNormalization.ReducesStar (TowerListAccumulatorsModel.rules lv) stepCall v := by
  have self : DirectedAnswer (TowerListAccumulatorsModel.rules lv) stepCall stepCall :=
    .self (stepCall_normal lv)
  refine ⟨⟨ListFunction.lists_qualified lv⟩, TowerListAccumulatorsModel.roles_num, numbers_recursive,
    stepCall_typed lv, fun noNeutral => noNeutral _ (stepCall_neutral lv) (stepCall_typed lv),
    fun w => ⟨fun answer => unique_of_qualified (ListFunction.lists_qualified lv) answer self, ?_⟩, ?_⟩
  · rintro rfl
    exact self
  · rintro ⟨v, tree, steps⟩
    have same : v = stepCall :=
      ContextualDependentExecutableJoin.Normal.star_eq (stepCall_normal lv) steps
    subst same
    exact stepCall_not_tree tree

/-- **The lists package is qualified, its lists are an inductive type, and the field of `cons` holding
the element is closed**, so the existence theorem does not apply at lists. -/
theorem lists_outside :
    Nonempty (Qualified (TowerListAccumulatorsModel.setting lv fun _ => 0)) ∧
      TowerListAccumulatorsModel.roles TowerListAccumulatorsModel.list =
        .inductive TowerListAccumulatorsModel.listCtors ∧
      ¬ RecursiveFields TowerListAccumulatorsModel.listCtors :=
  ⟨⟨ListFunction.lists_qualified lv⟩, TowerListAccumulatorsModel.roles_list,
    fun recursive => recursive _ _ TowerListAccumulatorsModel.mem_cons (.const num) (List.mem_cons_self ..)⟩

end Lists

/-! ## The rigid vectors package -/

/-- **The rigid vectors package is qualified and types a closed neutral term**, `zero`: qualification
does not give the hypothesis on closed neutral terms. -/
theorem rigid_has_closed_neutral :
    Nonempty (Qualified ProgrammingOnTheStep.VectorPackage.setting) ∧
      ¬ NoClosedNeutral ProgrammingOnTheStep.VectorPackage.setting :=
  ⟨⟨Vectors.rigid_qualified⟩, fun noNeutral =>
    noNeutral _ _ (Neutral.rigid [] rfl) (ProgrammingOnTheStep.VectorPackage.zero_typed .nil)⟩

/-! ## Neutral terms and typed spines: auxiliary facts -/

section Spines

variable {R : Rules Tower.Head} {roles : Roles Tower.Head}

/-- A neutral constant is rigid or computes. -/
theorem neutral_const_role {c : DeclName} (neutral : Neutral roles (.const c : Tm Tower.Head 0)) :
    roles c = .rigid ∨ ∃ arity inspect, roles c = .computes arity inspect := by
  generalize h : (.const c : Tm Tower.Head 0) = t at neutral
  cases neutral with
  | var i => exact i.elim0
  | app _ => cases h
  | fst _ => cases h
  | snd _ => cases h
  | @rigid c' args role =>
      obtain ⟨rfl, -⟩ :=
        appSpine_const_injective (show appSpine (.const c) [] = appSpine (.const c') args from h)
      exact .inl role
  | @stuck c' arity inspect args kind a role _ _ _ _ =>
      obtain ⟨rfl, -⟩ :=
        appSpine_const_injective (show appSpine (.const c) [] = appSpine (.const c') args from h)
      exact .inr ⟨arity, inspect, role⟩

/-- A closed neutral term is no universe, function type, pair type or identity type. -/
theorem neutral_not_former {t : Tm Tower.Head 0} (neutral : Neutral roles t) :
    (∀ h, t ≠ .head h) ∧ (∀ A B, t ≠ .pi A B) ∧ (∀ A B, t ≠ .sigma A B) ∧ ∀ C a b, t ≠ .id C a b := by
  have spine : ∀ (c : DeclName) (args : List (Tm Tower.Head 0)),
      (∀ h, appSpine (.const c) args ≠ .head h) ∧ (∀ A B, appSpine (.const c) args ≠ .pi A B) ∧
        (∀ A B, appSpine (.const c) args ≠ .sigma A B) ∧ ∀ C a b, appSpine (.const c) args ≠ .id C a b := by
    intro c args
    have found := ConstructorSystem.spineHead_appSpine_const c args
    refine ⟨fun h e => ?_, fun A B e => ?_, fun A B e => ?_, fun C a b e => ?_⟩ <;>
    · rw [e] at found
      cases found
  cases neutral with
  | var i => exact i.elim0
  | app _ => refine ⟨fun _ e => ?_, fun _ _ e => ?_, fun _ _ e => ?_, fun _ _ _ e => ?_⟩ <;> cases e
  | fst _ => refine ⟨fun _ e => ?_, fun _ _ e => ?_, fun _ _ e => ?_, fun _ _ _ e => ?_⟩ <;> cases e
  | snd _ => refine ⟨fun _ e => ?_, fun _ _ e => ?_, fun _ _ e => ?_, fun _ _ _ e => ?_⟩ <;> cases e
  | rigid args _ => exact spine _ args
  | stuck _ _ _ _ _ => exact spine _ _

/-- The function at the head of a typed application spine is typed. -/
theorem appSpine_head_typed {f : Tm Tower.Head 0} :
    ∀ (rest : List (Tm Tower.Head 0)) {T : Tm Tower.Head 0},
      Typed R .nil (appSpine f rest) T → ∃ T', Typed R .nil f T' := by
  intro rest
  induction rest using List.reverseRecOn with
  | nil => intro T typing; exact ⟨T, typing⟩
  | append_singleton init last ih =>
      intro T typing
      rw [appSpine_concat] at typing
      obtain ⟨A, B, tf, _, _⟩ := Typed.generation typing
      exact ih tf

/-- Every list of the right length is the list of arguments of a telescope substitution. -/
theorem exists_telescope_sub {k : Nat} (Θ : Ctx Tower.Head k) : ∀ (args : List (Tm Tower.Head 0)),
    args.length = k → ∃ σ : Sub Tower.Head k 0, telescopeArgs Θ σ = args := by
  induction Θ with
  | nil =>
      intro args len
      obtain rfl : args = [] := List.eq_nil_of_length_eq_zero len
      exact ⟨fun i => i.elim0, rfl⟩
  | snoc Θ E ih =>
      intro args len
      rcases List.eq_nil_or_concat' args with rfl | ⟨init, last, rfl⟩
      · simp at len
      · obtain ⟨σ', hσ⟩ := ih init (by simpa using len)
        refine ⟨consSub last σ', ?_⟩
        show telescopeArgs Θ (tailSub (consSub last σ')) ++ [consSub last σ' 0] = _
        rw [tailSub_consSub, hσ]
        rfl

/-- An inspected argument in the last position: nothing follows it. -/
theorem last_of_focus {k : Nat} {args before after : List (Tm Tower.Head 0)} {a : Tm Tower.Head 0}
    (len : args.length = k + 1) (hb : before.length = k) (split : args = before ++ a :: after) :
    args = before ++ [a] := by
  have empty : after = [] := by
    apply List.eq_nil_of_length_eq_zero
    have lengths := congrArg List.length split
    simp only [List.length_append, List.length_cons] at lengths
    omega
  rw [split, empty]

/-- The last argument of a telescope substitution is its newest value. -/
theorem telescopeArgs_last {k : Nat} (Θ : Ctx Tower.Head (k + 1)) (σ : Sub Tower.Head (k + 1) 0)
    {before : List (Tm Tower.Head 0)} {a : Tm Tower.Head 0} (same : telescopeArgs Θ σ = before ++ [a]) :
    σ 0 = a := by
  cases Θ with
  | snoc Θ' E =>
      have unfolded : telescopeArgs Θ' (tailSub σ) ++ [σ 0] = before ++ [a] := same
      exact List.singleton_inj.mp (List.append_inj_right' unfolded rfl)

end Spines

/-! ## The executable package: a rigid sort -/

section Executable

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram

/-- The constructors of the executable package's numbers have only recursive fields. -/
theorem executable_recursive : RecursiveFields ExecutableModel.ctors := by
  intro k fields mem
  simp only [ExecutableModel.ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

/-- The sort of sets is a rigid constant. -/
theorem set_rigid : (ExecutableModel.setting fun _ => 0).roles ExecutableModel.setN = .rigid := rfl

/-- The sort of sets is typed at `U₀`. -/
theorem set_typed :
    Typed ExecutableModel.rules .nil (.const ExecutableModel.setN : Tower.Tm 0)
      (TowerVectorsModel.U0 : Tower.Tm 0) :=
  .const (type := (TowerVectorsModel.U0 : Tower.Tm 0)) rfl (.headType (LevelTower.HeadTyping.sort _))
    (LevelTower.IsUniverse.sort _)

/-- **The hypothesis on all types excludes a qualified package for a reason that does not concern its
numbers.** The executable package is qualified, its numbers are an inductive type with recursive fields,
and it types a closed neutral term: the rigid declared sort of sets, at `U₀`. -/
theorem executable_has_closed_neutral :
    Nonempty (Qualified (ExecutableModel.setting fun _ => 0)) ∧
      ExecutableModel.roles ExecutableModel.numN = .inductive ExecutableModel.ctors ∧
      RecursiveFields ExecutableModel.ctors ∧
      ¬ NoClosedNeutral (ExecutableModel.setting fun _ => 0) :=
  ⟨⟨executable_qualified⟩, ExecutableModel.roles_num, executable_recursive,
    fun noNeutral => noNeutral (.const ExecutableModel.setN) _
      (Neutral.rigid (roles := (ExecutableModel.setting fun _ => 0).roles) [] set_rigid) set_typed⟩

/-! ### At the numbers of the executable package no closed neutral term is typed

The rigid declared constants are the sort of sets, of type `U₀`, and the power set, of type
`set → set`. Applied to arguments they are typed above `U₀`, above `set → set` and above `set`, and at
no other type. The argument that a computing constant inspects is typed at the numbers (the recursor,
addition, the iterated power set, the iterator) or at an identity type (the eliminator of identity). So
a rigid spine is never an inspected or a projected argument, every typed closed neutral term is a rigid
spine (`closed_neutral_rigid`), and none is typed at the numbers. -/

open ExecutableModel (numN setN powerN)

/-- The setting of the executable package. -/
abbrev executableSetting : Setting Tower.Head ℕ := ExecutableModel.setting fun _ => 0

/-- **The class of types kept away from the rigid constants** of the executable package: the numbers,
the pair types and the identity types, up to typed equality. The argument a computing constant inspects
is typed at one of them, and so is a term that is projected. -/
def ExecutableGuarded (X : Tower.Tm 0) : Prop :=
  TypeEq ExecutableModel.rules .nil X (.const numN) ∨
    (∃ A B, TypeEq ExecutableModel.rules .nil X (.sigma A B)) ∨
    ∃ C a b, TypeEq ExecutableModel.rules .nil X (.id C a b)

/-- A type above a universe is not in the class. -/
theorem executable_above_universe {u : Tower.Head} (hu : ExecutableModel.rules.isUniverse u)
    {T : Tower.Tm 0} (le : TypeLe ExecutableModel.rules .nil (.head u) T)
    (typeT : IsType ExecutableModel.rules .nil T) : ¬ ExecutableGuarded T := by
  obtain ⟨v, -, eT, -⟩ := Below.universe_source (S := executableSetting) ExecutableModel.facts
    (TypeLe.toBelow le typeT) .nil hu (IsType.refl (IsType.head_of_universe (S := executableSetting) hu))
  rintro (guarded | ⟨A, B, guarded⟩ | ⟨C, a, b, guarded⟩)
  · exact TypeEq.inductive_ne_head ExecutableModel.facts ExecutableModel.roles_num .nil
      (TypeEq.trans executableSetting.levels guarded.symm eT)
  · exact TypeEq.sigma_ne_head ExecutableModel.facts .nil
      (TypeEq.trans executableSetting.levels guarded.symm eT)
  · exact TypeEq.id_ne_head ExecutableModel.facts .nil
      (TypeEq.trans executableSetting.levels guarded.symm eT)

/-- A type above a function type is not in the class. -/
theorem executable_above_pi {A : Tower.Tm 0} {B : Tower.Tm 1} {T : Tower.Tm 0}
    (le : TypeLe ExecutableModel.rules .nil (.pi A B) T)
    (typeX : IsType ExecutableModel.rules .nil (.pi A B)) (typeT : IsType ExecutableModel.rules .nil T) :
    ¬ ExecutableGuarded T := by
  obtain ⟨A', B', eT, -, -⟩ := Below.pi_source (S := executableSetting) ExecutableModel.facts
    (TypeLe.toBelow le typeT) .nil (IsType.refl typeX)
  rintro (guarded | ⟨A₁, B₁, guarded⟩ | ⟨C, a, b, guarded⟩)
  · exact TypeEq.inductive_ne_pi ExecutableModel.facts ExecutableModel.roles_num .nil
      (TypeEq.trans executableSetting.levels guarded.symm eT)
  · exact TypeEq.pi_ne_sigma ExecutableModel.facts .nil
      (TypeEq.trans executableSetting.levels eT.symm guarded)
  · exact TypeEq.pi_ne_id ExecutableModel.facts .nil (TypeEq.trans executableSetting.levels eT.symm guarded)

/-- The sort of sets is a neutral type. -/
theorem set_neutral : Neutral ExecutableModel.roles (.const setN : Tower.Tm 0) :=
  Neutral.rigid (roles := ExecutableModel.roles) [] ExecutableModel.roles_set

/-- A type above the sort of sets is equal to it. -/
theorem executable_above_set_eq {T : Tower.Tm 0} (le : TypeLe ExecutableModel.rules .nil (.const setN) T)
    (typeT : IsType ExecutableModel.rules .nil T) : TypeEq ExecutableModel.rules .nil (.const setN) T :=
  TypeLe.rigid (S := executableSetting) le typeT .nil
    (fun u _ e => (neutral_not_former (TypeEq.neutral_form ExecutableModel.facts e .nil set_neutral
      (.inl ⟨u, rfl⟩))).1 u rfl)
    (fun A B e => (neutral_not_former (TypeEq.neutral_form ExecutableModel.facts e .nil set_neutral
      (.inr (.inl ⟨A, B, rfl⟩)))).2.1 A B rfl)
    (fun A B e => (neutral_not_former (TypeEq.neutral_form ExecutableModel.facts e .nil set_neutral
      (.inr (.inr (.inl ⟨A, B, rfl⟩))))).2.2.1 A B rfl)

/-- A type above the sort of sets is not in the class. -/
theorem executable_above_set {T : Tower.Tm 0} (le : TypeLe ExecutableModel.rules .nil (.const setN) T)
    (typeT : IsType ExecutableModel.rules .nil T) : ¬ ExecutableGuarded T := by
  have equal := executable_above_set_eq le typeT
  rintro (guarded | ⟨A, B, guarded⟩ | ⟨C, a, b, guarded⟩)
  · have neutral := TypeEq.neutral_form ExecutableModel.facts
      (TypeEq.trans executableSetting.levels equal guarded) .nil set_neutral
      (.inr (.inr (.inr (.inr (.inr ⟨numN, ExecutableModel.ctors, ExecutableModel.roles_num, rfl⟩)))))
    rcases neutral_const_role neutral with rigid | ⟨arity, inspect, computes⟩
    · rw [ExecutableModel.roles_num] at rigid
      cases rigid
    · rw [ExecutableModel.roles_num] at computes
      cases computes
  · exact (neutral_not_former (TypeEq.neutral_form ExecutableModel.facts
      (TypeEq.trans executableSetting.levels equal guarded) .nil set_neutral
      (.inr (.inr (.inl ⟨A, B, rfl⟩))))).2.2.1 A B rfl
  · exact (neutral_not_former (TypeEq.neutral_form ExecutableModel.facts
      (TypeEq.trans executableSetting.levels equal guarded) .nil set_neutral
      (.inr (.inr (.inr (.inl ⟨C, a, b, rfl⟩)))))).2.2.2 C a b rfl

/-- A declared constant of the executable package is listed in its table. -/
theorem executable_declared_mem {c : DeclName} {type : Tower.Tm 0}
    (declared : ExecutableModel.rules.constantType c = some type) :
    (c, type) ∈ ExecutableModel.declarations :=
  ExecutableModel.mem_of_lookup (show ExecutableModel.declarations.lookup c = some type from declared)

/-- The sort of sets applied to arguments is typed at no type of the class: alone it is typed above
`U₀`, and applied it is not typed. -/
theorem executable_set_spine {args : List (Tower.Tm 0)} {T : Tower.Tm 0}
    (typing : Typed ExecutableModel.rules .nil (appSpine (.const setN) args) T)
    (typeT : IsType ExecutableModel.rules .nil T) : ¬ ExecutableGuarded T := by
  have setDeclared :
      ExecutableModel.rules.constantType setN = some (TowerVectorsModel.U0 : Tower.Tm 0) := rfl
  have aboveU0 : ∀ {X : Tower.Tm 0}, Typed ExecutableModel.rules .nil (.const setN) X →
      TypeLe ExecutableModel.rules .nil (TowerVectorsModel.U0 : Tower.Tm 0) X := by
    intro X tc
    obtain ⟨type', u, declared', -, -, le⟩ := Typed.generation tc
    rw [setDeclared] at declared'
    obtain rfl := Option.some.inj declared'
    exact le
  match args, typing with
  | [], typing => exact executable_above_universe (LevelTower.IsUniverse.sort _) (aboveU0 typing) typeT
  | a :: rest, typing =>
      obtain ⟨T', th⟩ := appSpine_head_typed rest
        (show Typed ExecutableModel.rules .nil (appSpine (.app (.const setN) a) rest) T from typing)
      obtain ⟨A, B, tf, -, -⟩ := Typed.generation th
      have typePi : IsType ExecutableModel.rules .nil (.pi A B) :=
        Typed.isType (S := executableSetting) tf .nil
      obtain ⟨v, -, eT, -⟩ := Below.universe_source (S := executableSetting) ExecutableModel.facts
        (TypeLe.toBelow (aboveU0 tf) typePi) .nil (LevelTower.IsUniverse.sort _)
        (IsType.refl (IsType.head_of_universe (S := executableSetting) (LevelTower.IsUniverse.sort _)))
      exact absurd eT (TypeEq.pi_ne_head ExecutableModel.facts .nil)

/-- The power set applied to arguments is typed at no type of the class: alone it is typed above
`set → set`, at one argument above `set`, and at more it is not typed. -/
theorem executable_power_spine {args : List (Tower.Tm 0)} {T : Tower.Tm 0}
    (typing : Typed ExecutableModel.rules .nil (appSpine (.const powerN) args) T)
    (typeT : IsType ExecutableModel.rules .nil T) : ¬ ExecutableGuarded T := by
  have powerDeclared : ExecutableModel.rules.constantType powerN =
      some (closeType (.snoc .nil (.const setN)) (.const setN)) := rfl
  match args, typing with
  | [], typing =>
      have tc : Typed ExecutableModel.rules .nil (.const powerN : Tower.Tm 0) T := typing
      obtain ⟨type', u, declared', typedType, hu, le⟩ := Typed.generation tc
      rw [powerDeclared] at declared'
      obtain rfl := Option.some.inj declared'
      have le' : TypeLe ExecutableModel.rules .nil (.pi (.const setN) (.const setN)) T := le
      exact executable_above_pi le' ⟨u, hu, typedType⟩ typeT
  | [a], typing =>
      have typing' : Typed ExecutableModel.rules .nil
          (applyClosed (.snoc .nil (.const setN)) (fun _ => a) (.const powerN)) T := typing
      obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := executableSetting) ExecutableModel.facts .nil
        (.snoc .nil (.const setN)) (.const setN) powerDeclared typing'
      exact executable_above_set le typeT
  | a :: b :: rest, typing =>
      obtain ⟨T', th⟩ := appSpine_head_typed rest
        (show Typed ExecutableModel.rules .nil (appSpine (.app (.app (.const powerN) a) b) rest) T from
          typing)
      obtain ⟨A, B, tf, -, -⟩ := Typed.generation th
      have tf' : Typed ExecutableModel.rules .nil
          (applyClosed (.snoc .nil (.const setN)) (fun _ => a) (.const powerN)) (.pi A B) := tf
      obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := executableSetting) ExecutableModel.facts .nil
        (.snoc .nil (.const setN)) (.const setN) powerDeclared tf'
      have equal := executable_above_set_eq le (Typed.isType (S := executableSetting) tf .nil)
      exact absurd rfl ((neutral_not_former (TypeEq.neutral_form ExecutableModel.facts equal .nil
        set_neutral (.inr (.inl ⟨A, B, rfl⟩)))).2.1 A B)

/-- **A rigid spine of the executable package is typed at no type of the class.** Its rigid declared
constants are the sort of sets and the power set. -/
theorem executable_rigid_types {c : DeclName} {args : List (Tower.Tm 0)} {T : Tower.Tm 0}
    (role : ExecutableModel.roles c = .rigid)
    (typing : Typed ExecutableModel.rules .nil (appSpine (.const c) args) T) : ¬ ExecutableGuarded T := by
  obtain ⟨type, declared⟩ := TowerVectorsLookup.spine_head_declared args typing
  have typeT : IsType ExecutableModel.rules .nil T := Typed.isType (S := executableSetting) typing .nil
  have mem := executable_declared_mem declared
  simp only [ExecutableModel.declarations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [ExecutableModel.roles_num] at role; cases role
  · exact executable_set_spine typing typeT
  · rw [ExecutableModel.roles_zero] at role; cases role
  · rw [ExecutableModel.roles_suc] at role; cases role
  · rw [ExecutableModel.roles_add] at role; cases role
  · exact executable_power_spine typing typeT
  · rw [ExecutableModel.roles_pow] at role; cases role
  · rw [ExecutableModel.roles_numRec] at role; cases role
  · rw [ExecutableModel.roles_j] at role; cases role
  · rw [ExecutableModel.roles_eqAt] at role; cases role
  · rw [ExecutableModel.roles_sucMove] at role; cases role
  · rw [ExecutableModel.roles_keep] at role; cases role
  · rw [ExecutableModel.roles_transport] at role; cases role
  · rw [ExecutableModel.roles_compose] at role; cases role
  · rw [ExecutableModel.roles_iter] at role; cases role
  · rw [ExecutableModel.roles_returnIter] at role; cases role
  · rw [ExecutableModel.roles_sucStep] at role; cases role

/-- A typed full application of a declared constant has its arguments typed along the declared
telescope. -/
theorem executable_spine_typed {c : DeclName} {k : Nat} (Θ : Ctx Tower.Head k) (C : Tower.Tm k)
    (declared : ExecutableModel.rules.constantType c = some (closeType Θ C)) {args : List (Tower.Tm 0)}
    (len : args.length = k) {T : Tower.Tm 0}
    (typing : Typed ExecutableModel.rules .nil (appSpine (.const c) args) T) :
    ∃ σ : Sub Tower.Head k 0, telescopeArgs Θ σ = args ∧ SubstMor ExecutableModel.rules Θ .nil σ := by
  obtain ⟨σ, hσ⟩ := exists_telescope_sub Θ args len
  refine ⟨σ, hσ, ?_⟩
  have typing' : Typed ExecutableModel.rules .nil (applyClosed Θ σ (.const c)) T := by
    rw [applyClosed_eq_appSpine, hσ]
    exact typing
  exact (Typed.telescope_inv (S := executableSetting) ExecutableModel.facts .nil Θ C declared typing').1

/-- **The argument a computing constant of the executable package inspects is typed at a type of the
class**: at the numbers for the recursor, addition, the iterated power set and the iterator, and at an
identity type for the eliminator of identity. -/
theorem executable_inspected {c : DeclName} {arity : Nat} {inspect : InspectTree}
    {args : List (Tower.Tm 0)} {kind : Inspection} {a T : Tower.Tm 0}
    (role : ExecutableModel.roles c = .computes arity inspect) (len : args.length = arity)
    (focus : inspect.Focus ExecutableModel.roles args args kind a a)
    (typing : Typed ExecutableModel.rules .nil (appSpine (.const c) args) T) :
    ∃ A, Typed ExecutableModel.rules .nil a A ∧ ExecutableGuarded A := by
  have number : ∀ {x : Tower.Tm 0}, Typed ExecutableModel.rules .nil x (.const numN) →
      ∃ A, Typed ExecutableModel.rules .nil x A ∧ ExecutableGuarded A :=
    fun tx => ⟨_, tx, .inl (IsType.refl (Typed.isType (S := executableSetting) tx .nil))⟩
  obtain ⟨type, declared⟩ := TowerVectorsLookup.spine_head_declared args typing
  have mem := executable_declared_mem declared
  simp only [ExecutableModel.declarations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [ExecutableModel.roles_num] at role; cases role
  · rw [ExecutableModel.roles_set] at role; cases role
  · rw [ExecutableModel.roles_zero] at role; cases role
  · rw [ExecutableModel.roles_suc] at role; cases role
  · -- addition inspects its second argument, the last
    rw [ExecutableModel.roles_add] at role
    cases role
    obtain ⟨before, after, hb, split, -, -⟩ := focus.single
    obtain ⟨σ, hσ, mor⟩ := executable_spine_typed (ofEntries ExecutableModel.addEntries (1 + 1 + 0))
      Package.numT
      (ExecutableModel.declaresAdd (fun _ => 0) (ExecutableModel.laws fun _ => 0)).declared len typing
    have same := telescopeArgs_last (k := 1) _ σ (hσ.trans (last_of_focus len hb split))
    subst same
    exact number (mor 0)
  · rw [ExecutableModel.roles_power] at role; cases role
  · -- the iterated power set inspects its first argument
    rw [ExecutableModel.roles_pow] at role
    cases role
    obtain ⟨before, after, hb, split, -, -⟩ := focus.single
    obtain rfl : before = [] := List.eq_nil_of_length_eq_zero hb
    obtain ⟨σ, hσ, mor⟩ := executable_spine_typed (ofEntries ExecutableModel.powEntries (0 + 1 + 1))
      ExecutableModel.setT
      (ExecutableModel.declaresPow (fun _ => 0) (ExecutableModel.laws fun _ => 0)).declared len typing
    have listed : telescopeArgs (ofEntries ExecutableModel.powEntries (0 + 1 + 1)) σ = [σ 1, σ 0] := rfl
    rw [listed, split] at hσ
    have same : σ 1 = a := (List.cons.inj hσ).1
    subst same
    exact number (mor 1)
  · -- the recursor inspects its fourth argument, the last
    rw [ExecutableModel.roles_numRec] at role
    cases role
    obtain ⟨before, after, hb, split, -, -⟩ := focus.single
    have declaredRec : ExecutableModel.rules.constantType Package.numRecName =
        some (closeType (recTele numN (LevelTower.Head.sort Tower.zero) ExecutableModel.ctors)
          (recBody ExecutableModel.ctors.length)) :=
      (ExecutableModel.declaresNum (E := declarative ExecutableModel.rules) fun _ => 0).toRecursor.recDeclared
    obtain ⟨σ, hσ, mor⟩ := executable_spine_typed _ _ declaredRec len typing
    have same := telescopeArgs_last (k := 3) _ σ (hσ.trans (last_of_focus len hb split))
    subst same
    exact number (mor 0)
  · -- the eliminator of identity inspects its sixth argument, the last: a proof of an identity
    rw [ExecutableModel.roles_j] at role
    cases role
    obtain ⟨before, after, hb, split, -, -⟩ := focus.single
    have declaredJ : ExecutableModel.rules.constantType Package.jName =
        some (closeType (elimTelescope (LevelTower.Head.sort Tower.zero) (LevelTower.Head.sort Tower.zero))
          elimBody) :=
      (ExecutableModel.declaresJ (E := declarative ExecutableModel.rules) fun _ => 0).declared
    obtain ⟨σ, hσ, mor⟩ := executable_spine_typed _ _ declaredJ len typing
    have same := telescopeArgs_last (k := 5) _ σ (hσ.trans (last_of_focus len hb split))
    subst same
    have ta := mor 0
    exact ⟨_, ta, .inr (.inr ⟨_, _, _, IsType.refl (Typed.isType (S := executableSetting) ta .nil)⟩)⟩
  · rw [ExecutableModel.roles_eqAt] at role; cases role; exact absurd focus InspectTree.Focus.not_leaf
  · rw [ExecutableModel.roles_sucMove] at role; cases role; exact absurd focus InspectTree.Focus.not_leaf
  · rw [ExecutableModel.roles_keep] at role; cases role; exact absurd focus InspectTree.Focus.not_leaf
  · rw [ExecutableModel.roles_transport] at role; cases role; exact absurd focus InspectTree.Focus.not_leaf
  · rw [ExecutableModel.roles_compose] at role; cases role; exact absurd focus InspectTree.Focus.not_leaf
  · -- the iterator inspects its first argument
    rw [ExecutableModel.roles_iter] at role
    cases role
    obtain ⟨before, after, hb, split, -, -⟩ := focus.single
    obtain rfl : before = [] := List.eq_nil_of_length_eq_zero hb
    obtain ⟨σ, hσ, mor⟩ := executable_spine_typed (ofEntries ExecutableModel.iterEntries (0 + 1 + 5))
      ExecutableModel.iterResult
      (ExecutableModel.declaresIter (fun _ => 0) (ExecutableModel.laws fun _ => 0)).declared len typing
    have listed : telescopeArgs (ofEntries ExecutableModel.iterEntries (0 + 1 + 5)) σ =
        [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0] := rfl
    rw [listed, split] at hσ
    have same : σ 5 = a := (List.cons.inj hσ).1
    subst same
    exact number (mor 5)
  · rw [ExecutableModel.roles_returnIter] at role; cases role; exact absurd focus InspectTree.Focus.not_leaf
  · rw [ExecutableModel.roles_sucStep] at role; cases role; exact absurd focus InspectTree.Focus.not_leaf

/-- **No closed neutral term is typed at the numbers of the executable package.** -/
theorem executable_noNeutralAt : NoClosedNeutralAt executableSetting numN :=
  noClosedNeutralAt_of_rigid (S := executableSetting) ExecutableGuarded
    (fun tp => .inr (.inl ⟨_, _, IsType.refl (Typed.isType (S := executableSetting) tp .nil)⟩))
    executable_rigid_types executable_inspected
    (fun typed => .inl (IsType.refl (Typed.isType (S := executableSetting) typed .nil)))

/-- **The hypothesis at the type admits what the hypothesis on all types excludes**: in the executable
package no closed neutral term is typed at the numbers, and a closed neutral term is typed at `U₀`. -/
theorem executable_separates :
    NoClosedNeutralAt executableSetting numN ∧ ¬ NoClosedNeutral executableSetting :=
  ⟨executable_noNeutralAt, executable_has_closed_neutral.2.2.2⟩

/-- **Every closed number of the executable package has exactly one answer, a constructor tree of the
numbers**: the existence theorem at the type, at a package that the hypothesis on all types excludes.
Strong normalization of that package gave an answer already (`executable_answer`); this says the answer
is a numeral. -/
theorem executable_num_answer {t : Tower.Tm 0}
    (typing : Typed ExecutableModel.rules .nil t (.const numN)) :
    ∃ v, CtorTree ExecutableModel.ctors v ∧ DirectedAnswer ExecutableModel.rules t v ∧
      Typed ExecutableModel.rules .nil v (.const numN) ∧
      ∀ w, DirectedAnswer ExecutableModel.rules t w → w = v :=
  inductive_answer (S := executableSetting) executable_qualified executable_noNeutralAt
    ExecutableModel.roles_num executable_recursive typing

end Executable

/-! ## Heads related to themselves -/

/-- Every head of the tower is related to itself. -/
theorem tower_reflexive (h : Tower.Head) : LevelTower.HeadEq h h := by
  cases h with
  | legacyGround => trivial
  | sort level => exact fun _ => rfl

/-- **Every head is related to itself** in each of the seven qualified packages of the tree: the
vectors package, the bare numbers, the lists, the syntax package, `Eventually.Erasing`, the rigid
vectors package and the executable package. So in each of them an answer of the full reduction is
exactly an answer without heads (`answer_iff_headFree`). -/
theorem qualified_heads_reflexive :
    (∀ h, (TowerVectorsModel.rules lv).headEq h h) ∧
      (∀ h, (TowerNumbersModel.rules lv).headEq h h) ∧
      (∀ h, (TowerListAccumulatorsModel.rules lv).headEq h h) ∧
      (∀ h, (TowerSyntaxModel.rules lv).headEq h h) ∧
      (∀ h, Eventually.Erasing.rules.headEq h h) ∧
      (∀ h, ProgrammingOnTheStep.VectorPackage.rules.headEq h h) ∧
      (∀ h, Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.rules.headEq h h) :=
  ⟨tower_reflexive, tower_reflexive, tower_reflexive, tower_reflexive, tower_reflexive, tower_reflexive,
    tower_reflexive⟩

end NativeTypesOnTheStep.Computing.DirectedAnswers

section Audit
open NativeTypesOnTheStep.Computing.DirectedAnswers
#print axioms numbers_noNeutral
#print axioms numbers_num_answer
#print axioms stepCall_typed
#print axioms stepCall_normal
#print axioms stepCall_not_tree
#print axioms lists_control
#print axioms lists_outside
#print axioms rigid_has_closed_neutral
#print axioms executable_has_closed_neutral
#print axioms executable_rigid_types
#print axioms executable_inspected
#print axioms executable_noNeutralAt
#print axioms executable_separates
#print axioms executable_num_answer
#print axioms qualified_heads_reflexive
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
