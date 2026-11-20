import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Heads
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsLookup

/-!
# Answers at inductive types, from the logical relation

For every package with a normalization model (`Setting` with its laws and semantic constants), every
closed term typed at a simple inductive type `T` whose constructors have only recursive fields reaches,
by directed steps, a closed constructor tree (`inductive_reaches`), provided no closed neutral term is
typed **at `T`** (`NoClosedNeutralAt`). Strong normalization is not assumed. What is used is the
normalization model itself: the proof is an induction on the reducibility of the term, which the model
provides for every typed term (`Typed.reducible`, `Reducible.inductive_view`); the weak-head termination
of the package's recursive constants is the content of its semantic constants.

* The reducibility of a term of an inductive type is a typed weak-head reduction to a constructor
  applied to reducible arguments, or to a neutral term (`IndRedTm`, `IndNf`). Weak-head steps are
  directed steps (`whRed_directed`); the neutral case is excluded by the hypothesis, at the type `T`
  and nowhere else; the arguments are trees by induction (`tree_of_redTm`).
* **A constructor tree is a directed normal form**: a root step starts at a computing constant, and a
  constructor does not compute (`spine_normal`, `ctorSpine_normal`, `CtorTree.normal`). It has no head
  (`CtorTree.headFree`).
* **In a qualified package the tree is the call's only answer, of its type** (`inductive_answer`).
* **The hypothesis on all types** (`NoClosedNeutral`) implies the one at each type
  (`noClosedNeutralAt_of`). It fails in a qualified package for a reason that has nothing to do with
  the inductive type: a rigid declared sort is a closed neutral term at a universe, while no closed
  neutral term is typed at that package's numbers (`executable_separates`, module `Packages`). The
  hypothesis at the type cannot be dropped: a rigid declared function into the numbers gives a closed
  number with no constructor tree (`lists_control`, module `Packages`).
* **No closed neutral term is typed** in every package over the tower whose declared constants are not
  rigid and whose computing constants inspect at most one argument (`no_closed_neutral`): a neutral term
  is headed by a variable or a rigid constant, or stuck on an argument that is neutral itself.
* **With rigid declared constants**, the hypothesis at the type holds when the rigid constants are
  typed away from the types of inspected and projected terms (`closed_neutral_rigid`,
  `noClosedNeutralAt_of_rigid`): every typed closed neutral term is then a rigid constant applied to
  arguments.

A field of a closed type, which this statement excludes, would need besides the reducibility of the
argument at that type that the type be a data type itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DirectedAnswers

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

/-! ## Directed reduction along spines -/

section Spines

variable {Head : Type} {R : Rules Head}

/-- **Weak-head reduction is directed reduction.** -/
theorem whRed_directed {roles : Roles Head} {n : Nat} {t u : Tm Head n} (red : WhRed R roles t u) :
    StrongNormalization.ReducesStar R t u := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Eventually.whStep_directed R step)

theorem star_appSpine_head {n : Nat} {f f' : Tm Head n} (steps : StrongNormalization.ReducesStar R f f') :
    ∀ (as : List (Tm Head n)), StrongNormalization.ReducesStar R (appSpine f as) (appSpine f' as)
  | [] => steps
  | a :: as => star_appSpine_head
      (ContextualDependentExecutableJoin.star_map (R := R) (fun g => Tm.app g a) (fun step => .congAppFun step)
        steps) as

theorem star_appSpine_args {n : Nat} : ∀ (f : Tm Head n) {as bs : List (Tm Head n)},
    List.Forall₂ (StrongNormalization.ReducesStar R) as bs →
      StrongNormalization.ReducesStar R (appSpine f as) (appSpine f bs)
  | _, [], [], .nil => .refl
  | f, _ :: _, b :: _, .cons first rest =>
      (star_appSpine_head (ContextualDependentExecutableJoin.star_map (R := R) (fun x => Tm.app f x)
        (fun step => .congAppArg step) first) _).trans (star_appSpine_args (.app f b) rest)

/-- A spine of terms without heads has no head. -/
theorem headFree_appSpine {n : Nat} : ∀ {f : Tm Head n} {as : List (Tm Head n)},
    HeadFree f → (∀ a ∈ as, HeadFree a) → HeadFree (appSpine f as)
  | _, [], free, _ => free
  | _, a :: as, free, frees =>
      headFree_appSpine (as := as) ⟨free, frees a (List.mem_cons_self ..)⟩
        (fun b member => frees b (List.mem_cons_of_mem _ member))

end Spines

/-! ## Constructor trees -/

section Trees

variable {Head : Type}

/-- **A closed constructor tree** of an inductive type: one of its constructors applied to as many trees
as it has fields. -/
inductive CtorTree (ctors : List (DeclName × List (Normalization.Field Head))) : Tm Head 0 → Prop
  | mk {k : DeclName} {fields : List (Normalization.Field Head)} {args : List (Tm Head 0)} :
      (k, fields) ∈ ctors → args.length = fields.length → (∀ a ∈ args, CtorTree ctors a) →
        CtorTree ctors (appSpine (.const k) args)

/-- A constructor tree has no head. -/
theorem CtorTree.headFree {ctors : List (DeclName × List (Normalization.Field Head))} {v : Tm Head 0}
    (tree : CtorTree ctors v) : HeadFree v := by
  induction tree with
  | mk _ _ _ ih => exact headFree_appSpine trivial ih

/-- A constructor tree is headed by a constructor of the type. -/
theorem CtorTree.head_mem {ctors : List (DeclName × List (Normalization.Field Head))} {v : Tm Head 0}
    (tree : CtorTree ctors v) :
    ∃ (k : DeclName) (fields : List (Normalization.Field Head)) (args : List (Tm Head 0)),
      (k, fields) ∈ ctors ∧ v = appSpine (.const k) args := by
  cases tree with
  | mk mem _ _ => exact ⟨_, _, _, mem, rfl⟩

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- No root step starts at a spine whose head does not compute: root steps start at computing
constants. -/
theorem no_root_spine {k : DeclName} (inert : ∀ arity inspect, S.roles k ≠ .computes arity inspect)
    {n : Nat} {args : List (Tm Head n)} {u : Tm Head n} :
    ¬ S.R.computation.step (appSpine (.const k) args) u := by
  intro step
  obtain ⟨c, arity, inspect, args', computes, shape, -⟩ := S.shape.spine step
  obtain ⟨rfl, -⟩ := appSpine_const_injective shape
  exact inert _ _ computes

/-- **A constant that does not compute, applied to directed normal forms, is a directed normal form.** -/
theorem spine_normal {k : DeclName} (inert : ∀ arity inspect, S.roles k ≠ .computes arity inspect)
    {n : Nat} : ∀ (args : List (Tm Head n)), (∀ a ∈ args, ContextualDependentExecutableJoin.Normal S.R a) →
      ContextualDependentExecutableJoin.Normal S.R (appSpine (.const k) args) := by
  intro args
  induction args using List.reverseRecOn with
  | nil =>
      intro _
      show ContextualDependentExecutableJoin.Normal S.R (.const k)
      intro u step
      cases step with
      | root h => exact no_root_spine inert (args := []) h
  | append_singleton init last ih =>
      intro normals
      rw [appSpine_concat]
      intro u step
      generalize hf : appSpine (.const k) init = f at step
      cases step with
      | root h =>
          subst hf
          rw [← appSpine_concat] at h
          exact no_root_spine inert h
      | betaPi body a => exact (appSpine_const_ne_lam' hf).elim
      | congAppFun inner =>
          subst hf
          exact ih (fun a member => normals a (List.mem_append_left _ member)) _ inner
      | congAppArg inner => exact normals last (List.mem_append_right _ (List.mem_singleton_self _)) _ inner

/-- A constructor does not compute. -/
theorem constructor_inert {k : DeclName} {m : Nat} (role : S.roles k = .constructor m) :
    ∀ arity inspect, S.roles k ≠ .computes arity inspect := by
  intro arity inspect computes
  rw [role] at computes
  cases computes

/-- No root step starts at a constructor spine. -/
theorem no_root_ctorSpine {k : DeclName} {m : Nat} (role : S.roles k = .constructor m) {n : Nat}
    {args : List (Tm Head n)} {u : Tm Head n} : ¬ S.R.computation.step (appSpine (.const k) args) u :=
  no_root_spine (constructor_inert role)

/-- **A constructor applied to directed normal forms is a directed normal form.** -/
theorem ctorSpine_normal {k : DeclName} {m : Nat} (role : S.roles k = .constructor m) {n : Nat} :
    ∀ (args : List (Tm Head n)), (∀ a ∈ args, ContextualDependentExecutableJoin.Normal S.R a) →
      ContextualDependentExecutableJoin.Normal S.R (appSpine (.const k) args) :=
  spine_normal (constructor_inert role)

/-- **A constructor tree is a directed normal form.** -/
theorem CtorTree.normal {T : DeclName} {ctors : List (DeclName × List (Normalization.Field Head))}
    (role : S.roles T = .inductive ctors) {v : Tm Head 0} (tree : CtorTree ctors v) :
    ContextualDependentExecutableJoin.Normal S.R v := by
  induction tree with
  | mk mem _ _ ih => exact ctorSpine_normal (S.constructors.arity role mem) _ ih

end Trees

/-! ## From the logical relation -/

section Relation

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} {T : DeclName}
  {ctors : List (DeclName × List (Normalization.Field Head))}

/-- **No closed neutral term is typed at the inductive type `T`.** This is the hypothesis the
existence theorem uses. -/
abbrev NoClosedNeutralAt (S : Setting Head L) (T : DeclName) : Prop :=
  ∀ t : Tm Head 0, Neutral S.roles t → ¬ Typed S.R .nil t (.const T)

/-- No closed neutral term is typed, at any type. -/
abbrev NoClosedNeutral (S : Setting Head L) : Prop :=
  ∀ (t A : Tm Head 0), Neutral S.roles t → ¬ Typed S.R .nil t A

/-- The hypothesis on all types gives the one at each type. -/
theorem noClosedNeutralAt_of (noNeutral : NoClosedNeutral S) (T : DeclName) : NoClosedNeutralAt S T :=
  fun t neutral => noNeutral t _ neutral

/-- Every field of every constructor is recursive. -/
abbrev RecursiveFields (ctors : List (DeclName × List (Normalization.Field Head))) : Prop :=
  ∀ (k : DeclName) (fields : List (Normalization.Field Head)), (k, fields) ∈ ctors →
    ∀ F, Normalization.Field.closed F ∉ fields

mutual

theorem tree_of_redTm (noNeutral : NoClosedNeutralAt S T) (recursive : RecursiveFields ctors)
    {fieldPack : Tm Head 0 → Pack Head 0} :
    ∀ {t : Tm Head 0}, IndRedTm S .nil T ctors fieldPack t →
      ∃ v, CtorTree ctors v ∧ StrongNormalization.ReducesStar S.R t v
  | _, .mk red _ normal => by
      obtain ⟨v, tree, steps⟩ := tree_of_nf noNeutral recursive normal red.target
      exact ⟨v, tree, (whRed_directed red.red).trans steps⟩

theorem tree_of_nf (noNeutral : NoClosedNeutralAt S T) (recursive : RecursiveFields ctors)
    {fieldPack : Tm Head 0 → Pack Head 0} :
    ∀ {nf : Tm Head 0}, IndNf S .nil T ctors fieldPack nf → Typed S.R .nil nf (.const T) →
      ∃ v, CtorTree ctors v ∧ StrongNormalization.ReducesStar S.R nf v
  | _, .ctor mem arguments, _ => by
      obtain ⟨vs, length, trees, steps⟩ :=
        trees_of_fields noNeutral recursive arguments (recursive _ _ mem)
      exact ⟨_, .mk mem length trees, star_appSpine_args _ steps⟩
  | _, .neutral neutral _, typed => absurd typed (noNeutral _ neutral)

theorem trees_of_fields (noNeutral : NoClosedNeutralAt S T) (recursive : RecursiveFields ctors)
    {fieldPack : Tm Head 0 → Pack Head 0} :
    ∀ {fields : List (Normalization.Field Head)} {args : List (Tm Head 0)},
      IndFields S .nil T ctors fieldPack fields args → (∀ F, Normalization.Field.closed F ∉ fields) →
        ∃ vs : List (Tm Head 0), vs.length = fields.length ∧ (∀ v ∈ vs, CtorTree ctors v) ∧
          List.Forall₂ (StrongNormalization.ReducesStar S.R) args vs
  | _, _, .nil, _ => ⟨[], rfl, fun _ member => absurd member List.not_mem_nil, .nil⟩
  | _, _, .recursive head tail, noClosed => by
      obtain ⟨v, tree, steps⟩ := tree_of_redTm noNeutral recursive head
      obtain ⟨vs, length, trees, rest⟩ :=
        trees_of_fields noNeutral recursive tail fun F inTail => noClosed F (List.mem_cons_of_mem _ inTail)
      refine ⟨v :: vs, by simp [length], fun w member => ?_, .cons steps rest⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact tree
      · exact trees w later
  | _, _, .closed _ _, noClosed => absurd (List.mem_cons_self ..) (noClosed _)

end

/-- **Every closed term typed at an inductive type `T` with recursive fields reaches a constructor tree
by directed steps**, in every package with a normalization model in which no closed neutral term is
typed at `T`. -/
theorem inductive_reaches (laws : S.E.Laws S.R S.roles) (constants : SemanticConstants S)
    (noNeutral : NoClosedNeutralAt S T) (role : S.roles T = .inductive ctors)
    (recursive : RecursiveFields ctors) {t : Tm Head 0} (typing : Typed S.R .nil t (.const T)) :
    ∃ v, CtorTree ctors v ∧ StrongNormalization.ReducesStar S.R t v := by
  obtain ⟨r, h⟩ := Typed.reducible laws constants typing .nil
  obtain ⟨fieldPack, same, -⟩ := Reducible.inductive_view role r
  rw [same] at h
  exact tree_of_redTm noNeutral recursive h

/-- **In a qualified package, such a term has exactly one answer, a constructor tree of its type.** -/
theorem inductive_answer (q : Qualified S) (noNeutral : NoClosedNeutralAt S T)
    (role : S.roles T = .inductive ctors) (recursive : RecursiveFields ctors) {t : Tm Head 0}
    (typing : Typed S.R .nil t (.const T)) :
    ∃ v, CtorTree ctors v ∧ DirectedAnswer S.R t v ∧ Typed S.R .nil v (.const T) ∧
      ∀ w, DirectedAnswer S.R t w → w = v := by
  obtain ⟨v, tree, steps⟩ := inductive_reaches q.laws q.constants noNeutral role recursive typing
  have answer : DirectedAnswer S.R t v := ⟨steps, tree.normal role⟩
  exact ⟨v, tree, answer, (typed_of_qualified q .nil typing answer).1,
    fun w other => unique_of_qualified q other answer⟩

end Relation

/-! ## Closed neutral terms over the tower -/

/-- **No closed neutral term is typed** in a package over the tower whose declared constants are not
rigid and whose computing constants inspect at most one argument: a closed neutral term is headed by a
rigid constant, which no typing can use, or stuck on a neutral argument, which is typed itself. -/
theorem no_closed_neutral {R : Rules Tower.Head} {roles : Roles Tower.Head}
    (declared : ∀ (c : DeclName) (type : Tm Tower.Head 0), R.constantType c = some type → roles c ≠ .rigid)
    (inspects : ∀ (c : DeclName) (arity : Nat) (inspect : InspectTree), roles c = .computes arity inspect →
      inspect = .leaf ∨ ∃ k, inspect = .split k .constructor fun _ => .leaf) :
    ∀ {n : Nat} {t : Tm Tower.Head n}, Neutral roles t → n = 0 →
      ∀ (Γ : Ctx Tower.Head n) (T : Tm Tower.Head n), ¬ Typed R Γ t T := by
  intro n t neutral
  induction neutral with
  | var i =>
      intro h
      subst h
      exact i.elim0
  | app _ ih =>
      intro h Γ T typing
      obtain ⟨A, B, tf, _, _⟩ := Typed.generation typing
      exact ih h Γ _ tf
  | fst _ ih =>
      intro h Γ T typing
      obtain ⟨A, B, tp, _⟩ := Typed.generation typing
      exact ih h Γ _ tp
  | snd _ ih =>
      intro h Γ T typing
      obtain ⟨A, B, tp, _⟩ := Typed.generation typing
      exact ih h Γ _ tp
  | rigid args role =>
      intro _ Γ T typing
      obtain ⟨type, found⟩ := TowerVectorsLookup.spine_head_declared args typing
      exact declared _ _ found role
  | @stuck _ _ _ args _ a role _ focus _ _ ih =>
      intro h Γ T typing
      rcases inspects _ _ _ role with rfl | ⟨k, rfl⟩
      · exact InspectTree.Focus.not_leaf focus
      · obtain ⟨before, after, _, split, _, _⟩ := focus.single
        have mem : a ∈ args := by
          rw [split]
          simp
        obtain ⟨A, ta⟩ := TowerVectorsLookup.spine_args_typed args typing a mem
        exact ih h Γ A ta

/-! ## Closed neutral terms in a package with rigid declared constants -/

section Rigid

variable {R : Rules Tower.Head} {roles : Roles Tower.Head}

/-- **Every typed closed neutral term is a rigid constant applied to arguments**, in a package with a
class of closed types (`Guarded`) such that: a rigid constant applied to arguments is never typed at a
type of the class; the type of a term that is projected is in the class; and the argument that a
computing constant inspects is typed at a type of the class. A neutral term is an application or a
projection of a neutral term, a rigid spine, or a computing constant stuck on a neutral argument. An
application of a rigid spine is a rigid spine; a projection of one, and a constant stuck on one, are
excluded by the class. -/
theorem closed_neutral_rigid (Guarded : Tm Tower.Head 0 → Prop)
    (projected : ∀ {p A : Tm Tower.Head 0} {B : Tm Tower.Head 1}, Typed R .nil p (.sigma A B) →
      Guarded (.sigma A B))
    (rigidTypes : ∀ {c : DeclName} {args : List (Tm Tower.Head 0)} {T : Tm Tower.Head 0},
      roles c = .rigid → Typed R .nil (appSpine (.const c) args) T → ¬ Guarded T)
    (inspected : ∀ {c : DeclName} {arity : Nat} {inspect : InspectTree} {args : List (Tm Tower.Head 0)}
      {kind : Inspection} {a T : Tm Tower.Head 0}, roles c = .computes arity inspect → args.length = arity →
      inspect.Focus roles args args kind a a → Typed R .nil (appSpine (.const c) args) T →
      ∃ A, Typed R .nil a A ∧ Guarded A) :
    ∀ {n : Nat} {t : Tm Tower.Head n}, Neutral roles t → n = 0 →
      ∀ (Γ : Ctx Tower.Head n) (T : Tm Tower.Head n), Typed R Γ t T →
        ∃ (c : DeclName) (args : List (Tm Tower.Head n)), t = appSpine (.const c) args ∧ roles c = .rigid := by
  intro n t neutral
  induction neutral with
  | var i =>
      intro h
      subst h
      exact i.elim0
  | @app f a _ ih =>
      intro h Γ T typing
      obtain ⟨A, B, tf, _, _⟩ := Typed.generation typing
      obtain ⟨c, args, rfl, role⟩ := ih h Γ _ tf
      exact ⟨c, args ++ [a], (appSpine_concat _ _ _).symm, role⟩
  | @fst p _ ih =>
      intro h Γ T typing
      subst h
      cases Γ
      obtain ⟨A, B, tp, _⟩ := Typed.generation typing
      obtain ⟨c, args, rfl, role⟩ := ih rfl .nil _ tp
      exact absurd (projected tp) (rigidTypes role tp)
  | @snd p _ ih =>
      intro h Γ T typing
      subst h
      cases Γ
      obtain ⟨A, B, tp, _⟩ := Typed.generation typing
      obtain ⟨c, args, rfl, role⟩ := ih rfl .nil _ tp
      exact absurd (projected tp) (rigidTypes role tp)
  | rigid args role =>
      intro _ _ _ _
      exact ⟨_, args, rfl, role⟩
  | @stuck c arity inspect args kind a role len focus _ _ ih =>
      intro h Γ T typing
      subst h
      cases Γ
      obtain ⟨A, ta, guarded⟩ := inspected role len focus typing
      obtain ⟨c', args', rfl, role'⟩ := ih rfl .nil A ta
      exact absurd guarded (rigidTypes role' ta)

end Rigid

/-- **A criterion for the hypothesis at the type**, which a package with rigid declared constants can
meet: with a class of closed types as in `closed_neutral_rigid` that contains the inductive type, no
closed neutral term is typed at the inductive type. The rigid constants may well be typed elsewhere. -/
theorem noClosedNeutralAt_of_rigid {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Tower.Head L}
    (Guarded : Tm Tower.Head 0 → Prop)
    (projected : ∀ {p A : Tm Tower.Head 0} {B : Tm Tower.Head 1}, Typed S.R .nil p (.sigma A B) →
      Guarded (.sigma A B))
    (rigidTypes : ∀ {c : DeclName} {args : List (Tm Tower.Head 0)} {T : Tm Tower.Head 0},
      S.roles c = .rigid → Typed S.R .nil (appSpine (.const c) args) T → ¬ Guarded T)
    (inspected : ∀ {c : DeclName} {arity : Nat} {inspect : InspectTree} {args : List (Tm Tower.Head 0)}
      {kind : Inspection} {a T : Tm Tower.Head 0}, S.roles c = .computes arity inspect → args.length = arity →
      inspect.Focus S.roles args args kind a a → Typed S.R .nil (appSpine (.const c) args) T →
      ∃ A, Typed S.R .nil a A ∧ Guarded A)
    {T : DeclName} (atType : ∀ {t : Tm Tower.Head 0}, Typed S.R .nil t (.const T) → Guarded (.const T)) :
    NoClosedNeutralAt S T := by
  intro t neutral typed
  obtain ⟨c, args, rfl, role⟩ :=
    closed_neutral_rigid Guarded projected rigidTypes inspected neutral rfl .nil _ typed
  exact rigidTypes role typed (atType typed)

end NativeTypesOnTheStep.Computing.DirectedAnswers

section Audit
open NativeTypesOnTheStep.Computing.DirectedAnswers
#print axioms whRed_directed
#print axioms star_appSpine_args
#print axioms spine_normal
#print axioms ctorSpine_normal
#print axioms noClosedNeutralAt_of
#print axioms CtorTree.normal
#print axioms CtorTree.headFree
#print axioms inductive_reaches
#print axioms inductive_answer
#print axioms no_closed_neutral
#print axioms closed_neutral_rigid
#print axioms noClosedNeutralAt_of_rigid
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
