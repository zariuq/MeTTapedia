import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Inductive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Existence

/-!
# Answers at data types, from the logical relation

In the vectors package (`ProgrammingOnTheStep.IndexedFamilies.Eliminator.pkg`) every closed term typed at
a data type has exactly one answer, and it is a value. Strong normalization of the package is not
assumed (and not proved). The proof uses the package's normalization model, which its qualification
provides: it is an induction on the reducibility that the model assigns to every typed term
(`Typed.reducible`), and the weak-head termination of the recursive constants is in the model's semantic
constants.

* **Data types** (`DataType`): the numbers, the unit type, the empty type, dependent pairs whose second
  component does not depend on the first, and every closed type typed-equal to one of these. A function
  type is none (`pi_not_dataType`), nor a universe or any other head (`head_not_dataType`), nor an
  identity type (`id_not_dataType`). **Values** (`Value`): `zero`, `succ v`, `tt` and pairs of values. A
  value has no head and is a normal form (`Value.normal`).
* **The logical relation gives the reduction.** At the numbers and the unit type this is the general
  theorem for inductive types (`DirectedAnswers.inductive_reaches`), with the package's fact that no
  closed neutral term is typed (`TowerVectorsLookup.no_closed_neutral`), used at these two types; a
  constructor tree of the numbers is a numeral (`ctorTree_numeral`). A reducible term of a pair type reduces by weak-head steps to
  a pair or to a neutral term (`SigmaRedTm`), so a closed one reaches a pair, whose components are typed
  at the components of its type by subject reduction of the projections (`sigma_reaches`).
* **Every closed term typed at a data type has exactly one answer, a value of that type**
  (`data_answer`). At the numbers the answer is a numeral (`num_answer`): every closed number has
  exactly one answer, `nat k` for exactly one `k`. Since a value has no head, the conversion reading is
  literal here too: every directed normal form convertible with the term is its answer
  (`data_conv_answer`).
* **Vectors over a data type, at every closed length, are data types** (`vec_dataType`): the length has a
  numeral answer, and `vec A (succ j)` and `vec A zero` are typed-equal to a pair type and to the unit
  type. So every closed vector of numbers has exactly one answer, a value.

**Which inductive types.** The argument works as it stands for every inductive type of the package
whose constructor fields are recursive: the numbers, the unit type and the empty type (which has no
closed term, `TowerVectorsLookup.void_empty`). A field of a closed type `F` would need, besides the
reducibility of the argument at `F` that the relation provides, that `F` be a data type itself. The
general statement needs of a package two things used here: a normalization model (laws and semantic
constants), and that no closed neutral term is typed at the inductive type in question
(`NoClosedNeutralAt`); at other types closed neutral terms do no harm. Function types and universes are
not data types: an answer at a function type is an abstraction or a partial application, and at a
universe it may be a head or a function type (`DirectedAnswers.Calls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DirectedAnswers

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerNumbersModel (num zero succ ctors u)
open TowerVectorsModel (unit tt unitCtors U0 numC zeroC succC unitC ttC voidC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)
open Definitions (nat nat_typed nat_normal)

/-! ## Data types and values -/

/-- **Closed data types** of the vectors package. -/
inductive DataType : Tower.Tm 0 → Prop
  | num : DataType numC
  | unit : DataType unitC
  | void : DataType voidC
  | sigma {A B : Tower.Tm 0} : DataType A → DataType B → DataType (.sigma A (rename wk B))
  | conv {A B : Tower.Tm 0} : TypeEq pkg .nil A B → DataType B → DataType A

/-- The closed forms that data types are equal to: the numbers, the unit type, the empty type and the
pair types. -/
def Canonical (C : Tower.Tm 0) : Prop :=
  C = numC ∨ C = unitC ∨ C = voidC ∨ ∃ A B, C = .sigma A B

/-- A data type is one of the closed forms or typed-equal to one. -/
theorem DataType.canonical {D' : Tower.Tm 0} (data : DataType D') :
    Canonical D' ∨ ∃ C, Canonical C ∧ TypeEq pkg .nil D' C := by
  induction data with
  | num => exact .inl (.inl rfl)
  | unit => exact .inl (.inr (.inl rfl))
  | void => exact .inl (.inr (.inr (.inl rfl)))
  | sigma _ _ _ _ => exact .inl (.inr (.inr (.inr ⟨_, _, rfl⟩)))
  | @conv A B equal _ ih =>
      rcases ih with canonical | ⟨C, canonical, equal'⟩
      · exact .inr ⟨B, canonical, equal⟩
      · exact .inr ⟨C, canonical, TypeEq.trans Vectors.vecS.levels equal equal'⟩

/-- **A function type is not a data type**: it is typed-equal to no number, unit, empty or pair type. -/
theorem pi_not_dataType {A : Tower.Tm 0} {B : Tower.Tm 1} : ¬ DataType (.pi A B) := by
  intro data
  have facts := (Vectors.vq level1).facts
  rcases data.canonical with canonical | ⟨C, canonical, equal⟩
  · rcases canonical with same | same | same | ⟨_, _, same⟩ <;> cases same
  · rcases canonical with rfl | rfl | rfl | ⟨A', B', rfl⟩
    · exact TypeEq.inductive_ne_pi facts
        (show Vectors.vecS.roles num = .inductive ctors from TowerVectorsModel.roles_num) .nil equal.symm
    · exact TypeEq.inductive_ne_pi facts
        (show Vectors.vecS.roles unit = .inductive unitCtors from TowerVectorsModel.roles_unit) .nil equal.symm
    · exact TypeEq.inductive_ne_pi facts
        (show Vectors.vecS.roles TowerVectorsModel.void = .inductive [] from TowerVectorsModel.roles_void) .nil
        equal.symm
    · exact TypeEq.pi_ne_sigma facts .nil equal

/-- **A universe, and every other head, is not a data type.** -/
theorem head_not_dataType (h : Tower.Head) : ¬ DataType (.head h : Tower.Tm 0) := by
  intro data
  have facts := (Vectors.vq level1).facts
  rcases data.canonical with canonical | ⟨C, canonical, equal⟩
  · rcases canonical with same | same | same | ⟨_, _, same⟩ <;> cases same
  · rcases canonical with rfl | rfl | rfl | ⟨A', B', rfl⟩
    · exact TypeEq.inductive_ne_head facts
        (show Vectors.vecS.roles num = .inductive ctors from TowerVectorsModel.roles_num) .nil equal.symm
    · exact TypeEq.inductive_ne_head facts
        (show Vectors.vecS.roles unit = .inductive unitCtors from TowerVectorsModel.roles_unit) .nil
        equal.symm
    · exact TypeEq.inductive_ne_head facts
        (show Vectors.vecS.roles TowerVectorsModel.void = .inductive [] from TowerVectorsModel.roles_void)
        .nil equal.symm
    · exact TypeEq.sigma_ne_head facts .nil equal.symm

/-- **An identity type is not a data type.** -/
theorem id_not_dataType {A a b : Tower.Tm 0} : ¬ DataType (.id A a b) := by
  intro data
  have facts := (Vectors.vq level1).facts
  rcases data.canonical with canonical | ⟨C, canonical, equal⟩
  · rcases canonical with same | same | same | ⟨_, _, same⟩ <;> cases same
  · rcases canonical with rfl | rfl | rfl | ⟨A', B', rfl⟩
    · exact TypeEq.inductive_ne_id facts
        (show Vectors.vecS.roles num = .inductive ctors from TowerVectorsModel.roles_num) .nil equal.symm
    · exact TypeEq.inductive_ne_id facts
        (show Vectors.vecS.roles unit = .inductive unitCtors from TowerVectorsModel.roles_unit) .nil
        equal.symm
    · exact TypeEq.inductive_ne_id facts
        (show Vectors.vecS.roles TowerVectorsModel.void = .inductive [] from TowerVectorsModel.roles_void)
        .nil equal.symm
    · exact TypeEq.sigma_ne_id facts .nil equal.symm

/-- **Values**: closed constructor trees of the data types. -/
inductive Value : Tower.Tm 0 → Prop
  | zero : Value zeroC
  | succ {t : Tower.Tm 0} : Value t → Value (succC t)
  | tt : Value ttC
  | pair {a b : Tower.Tm 0} : Value a → Value b → Value (.pair a b)

theorem nat_value : ∀ k, Value (nat k)
  | 0 => .zero
  | k + 1 => .succ (nat_value k)

/-- A value has no head. -/
theorem Value.headFree {v : Tower.Tm 0} (value : Value v) : HeadFree v := by
  induction value with
  | zero => trivial
  | succ _ ih => exact ⟨trivial, ih⟩
  | tt => trivial
  | pair _ _ iha ihb => exact ⟨iha, ihb⟩

/-- **A value is a normal form**, of the full reduction and so of the directed one. -/
theorem Value.normal {v : Tower.Tm 0} (value : Value v) : ConstructorSystem.Normal pkg v := by
  induction value with
  | zero => exact Vectors.const_normal level1 (by decide)
  | succ _ ih => exact Vectors.succ_normal level1 ih
  | tt => exact Vectors.const_normal level1 (by decide)
  | pair _ _ iha ihb => exact Vectors.pair_normal level1 iha ihb

theorem Value.directedNormal {v : Tower.Tm 0} (value : Value v) :
    ContextualDependentExecutableJoin.Normal pkg v :=
  directedNormal_of_normal value.normal

/-! ## Reduction from the logical relation -/

section Relation

theorem star_pair {a a' b b' : Tower.Tm 0} (first : StrongNormalization.ReducesStar pkg a a')
    (second : StrongNormalization.ReducesStar pkg b b') :
    StrongNormalization.ReducesStar pkg (.pair a b) (.pair a' b') :=
  (ContextualDependentExecutableJoin.star_map (R := pkg) (fun x => Tm.pair x b)
    (fun step => .congPairFst step) first).trans
  (ContextualDependentExecutableJoin.star_map (R := pkg) (fun x => Tm.pair a' x)
    (fun step => .congPairSnd step) second)

/-- The constructors of the numbers have only recursive fields. -/
theorem numbers_recursive : RecursiveFields (ctors : List (DeclName × List (Normalization.Field Tower.Head))) := by
  intro k fields mem
  simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

/-- The constructor of the unit type has no field. -/
theorem unit_recursive : RecursiveFields (unitCtors : List (DeclName × List (Normalization.Field Tower.Head))) := by
  intro k fields mem
  simp only [unitCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  obtain ⟨_, rfl⟩ := mem
  simp

/-- **A constructor tree of the numbers is a numeral.** -/
theorem ctorTree_numeral {v : Tower.Tm 0} (tree : CtorTree ctors v) : ∃ k, v = nat k := by
  induction tree with
  | @mk k fields args mem length _ ih =>
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain rfl : args = [] := List.eq_nil_of_length_eq_zero length
        exact ⟨0, rfl⟩
      · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := List.length_eq_one_iff.mp length
        obtain ⟨j, rfl⟩ := ih a (List.mem_singleton_self _)
        exact ⟨j + 1, rfl⟩

/-- **A constructor tree of the unit type is `tt`.** -/
theorem ctorTree_tt {v : Tower.Tm 0} (tree : CtorTree unitCtors v) : v = ttC := by
  cases tree with
  | @mk k fields args mem length _ =>
      simp only [unitCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      obtain ⟨rfl, rfl⟩ := mem
      obtain rfl : args = [] := List.eq_nil_of_length_eq_zero length
      rfl

/-- **No closed neutral term is typed** in the vectors package, at any type. -/
theorem vectors_noNeutral : NoClosedNeutral Vectors.vecS :=
  fun _ A neutral typed => TowerVectorsLookup.no_closed_neutral level1 neutral rfl .nil A typed

/-- **Every closed number reaches a numeral by directed steps**, by the logical relation. -/
theorem num_reaches {t : Tower.Tm 0} (typing : Typed pkg .nil t numC) :
    ∃ k, StrongNormalization.ReducesStar pkg t (nat k) := by
  obtain ⟨v, tree, steps⟩ := inductive_reaches (S := Vectors.vecS) (TowerVectorsModel.laws level1 _)
    (TowerVectorsModel.constants level1 _) (noClosedNeutralAt_of vectors_noNeutral num)
    (show Vectors.vecS.roles num = .inductive ctors from TowerVectorsModel.roles_num) numbers_recursive typing
  obtain ⟨k, rfl⟩ := ctorTree_numeral tree
  exact ⟨k, steps⟩

/-- **Every closed term of the unit type reaches `tt` by directed steps.** -/
theorem unit_reaches {t : Tower.Tm 0} (typing : Typed pkg .nil t unitC) :
    StrongNormalization.ReducesStar pkg t ttC := by
  obtain ⟨v, tree, steps⟩ := inductive_reaches (S := Vectors.vecS) (TowerVectorsModel.laws level1 _)
    (TowerVectorsModel.constants level1 _) (noClosedNeutralAt_of vectors_noNeutral unit)
    (show Vectors.vecS.roles unit = .inductive unitCtors from TowerVectorsModel.roles_unit) unit_recursive typing
  rw [ctorTree_tt tree] at steps
  exact steps

/-- **A closed term of a nondependent pair type reaches a pair** of closed terms of the components. -/
theorem sigma_reaches {A B t : Tower.Tm 0} (typing : Typed pkg .nil t (.sigma A (rename wk B))) :
    ∃ a b, StrongNormalization.ReducesStar pkg t (.pair a b) ∧ Typed pkg .nil a A ∧ Typed pkg .nil b B := by
  obtain ⟨r, h⟩ := Typed.reducible (S := Vectors.vecS) (TowerVectorsModel.laws level1 _)
    (TowerVectorsModel.constants level1 _) typing .nil
  obtain ⟨PP, same, -⟩ := Reducible.sigma_raw (S := Vectors.vecS) r
  rw [same] at h
  change SigmaRedTm Vectors.vecS PP t at h
  obtain ⟨nf, red, shape, -, -⟩ := h
  rcases shape with ⟨a, b, rfl⟩ | neutral
  · have typedPair : Typed pkg .nil (.pair a b) (.sigma A (rename wk B)) := red.target
    have typedA : Typed pkg .nil a A :=
      (Vectors.vectors_subjectReduction level1 .nil (.single (.betaSigmaFst a b)) (.fstElim typedPair)).1
    have typedB : Typed pkg .nil b B := by
      have typed := (Vectors.vectors_subjectReduction level1 .nil (.single (.betaSigmaSnd a b))
        (.sndElim typedPair)).1
      rwa [inst0_rename_wk] at typed
    exact ⟨a, b, whRed_directed red.red, typedA, typedB⟩
  · exact absurd red.target (TowerVectorsLookup.no_closed_neutral level1 neutral rfl .nil _)

end Relation

/-! ## Answers at data types -/

/-- **Every closed term typed at a data type reaches a value by directed steps.** -/
theorem reaches_value {D' : Tower.Tm 0} (data : DataType D') :
    ∀ {t : Tower.Tm 0}, Typed pkg .nil t D' → ∃ v, Value v ∧ StrongNormalization.ReducesStar pkg t v := by
  induction data with
  | num =>
      intro t typing
      obtain ⟨k, steps⟩ := num_reaches typing
      exact ⟨nat k, nat_value k, steps⟩
  | unit =>
      intro t typing
      exact ⟨ttC, .tt, unit_reaches typing⟩
  | void =>
      intro t typing
      exact absurd typing (TowerVectorsLookup.void_empty level1)
  | sigma _ _ ihA ihB =>
      intro t typing
      obtain ⟨a, b, steps, typedA, typedB⟩ := sigma_reaches typing
      obtain ⟨va, valueA, stepsA⟩ := ihA typedA
      obtain ⟨vb, valueB, stepsB⟩ := ihB typedB
      exact ⟨.pair va vb, .pair valueA valueB, steps.trans (star_pair stepsA stepsB)⟩
  | conv equal _ ih =>
      intro t typing
      exact ih (Typed.convType typing equal)

/-- **Every closed term typed at a data type has exactly one answer, a value of that type.** -/
theorem data_answer {D' t : Tower.Tm 0} (data : DataType D') (typing : Typed pkg .nil t D') :
    ∃ v, Value v ∧ DirectedAnswer pkg t v ∧ Typed pkg .nil v D' ∧ Equal pkg .nil t v D' ∧
      ∀ w, DirectedAnswer pkg t w → w = v := by
  obtain ⟨v, value, steps⟩ := reaches_value data typing
  have answer : DirectedAnswer pkg t v := ⟨steps, value.directedNormal⟩
  obtain ⟨typed, equal⟩ := typed_of_qualified (Vectors.vq level1) .nil typing answer
  exact ⟨v, value, answer, typed, equal, fun w other => DirectedAnswer.unique
    (Vectors.vectorConstructors level1) other answer⟩

/-- **At a data type the conversion reading is literal as well**: every directed normal form convertible
with a closed term of a data type is its answer, a value. -/
theorem data_conv_answer {D' t : Tower.Tm 0} (data : DataType D') (typing : Typed pkg .nil t D')
    {w : Tower.Tm 0} (conversion : Conv pkg.headEq t w pkg.computation)
    (normal : ContextualDependentExecutableJoin.Normal pkg w) : DirectedAnswer pkg t w ∧ Value w := by
  obtain ⟨v, value, answer, -, -, -⟩ := data_answer data typing
  have same : w = v := eq_of_conv_headFree (Vectors.vectorConstructors level1) normal value.directedNormal
    (.trans _ _ _ (.symm _ _ conversion) answer.conv) value.headFree
  subst same
  exact ⟨answer, value⟩

/-- **Every closed number has exactly one answer, a numeral**, and the numeral is unique. -/
theorem num_answer {t : Tower.Tm 0} (typing : Typed pkg .nil t numC) :
    ∃ k, DirectedAnswer pkg t (nat k) ∧ Equal pkg .nil t (nat k) numC ∧
      (∀ w, DirectedAnswer pkg t w ↔ w = nat k) ∧ ∀ j, DirectedAnswer pkg t (nat j) → j = k := by
  obtain ⟨k, steps⟩ := num_reaches typing
  have answer : DirectedAnswer pkg t (nat k) := ⟨steps, (nat_value k).directedNormal⟩
  have unique : ∀ w, DirectedAnswer pkg t w → w = nat k := fun w other =>
    DirectedAnswer.unique (Vectors.vectorConstructors level1) other answer
  refine ⟨k, answer, (typed_of_qualified (Vectors.vq level1) .nil typing answer).2,
    fun w => ⟨unique w, fun same => same ▸ answer⟩, fun j other => ?_⟩
  exact nat_injective (unique _ other)
where
  nat_injective : ∀ {j k : Nat}, (nat j : Tower.Tm 0) = nat k → j = k
    | 0, 0, _ => rfl
    | j + 1, k + 1, same => by
        simp only [nat, Tm.app.injEq, true_and] at same
        rw [nat_injective same]
    | 0, _ + 1, same => by simp [nat] at same
    | _ + 1, 0, same => by simp [nat] at same

/-! ## Vectors over data types -/

/-- `vec A j`, at a numeral length, is a data type over a data type `A`. -/
theorem vec_numeral_dataType {A : Tower.Tm 0} (typedA : Typed pkg .nil A U0) (dataA : DataType A) :
    ∀ j, DataType (vecC A (nat j))
  | 0 => .conv (D.vec_zero_eq typedA) .unit
  | j + 1 => .conv (D.vec_succ_eq typedA (nat_typed j)) (.sigma dataA (vec_numeral_dataType typedA dataA j))

/-- **Vectors over a data type, at every closed length, are data types.** -/
theorem vec_dataType {A k : Tower.Tm 0} (typedA : Typed pkg .nil A U0) (dataA : DataType A)
    (typedK : Typed pkg .nil k numC) : DataType (vecC A k) := by
  obtain ⟨j, answer, equal, -⟩ := num_answer typedK
  exact .conv (TowerVectorsPrograms.vec_congr level1 typedA equal) (vec_numeral_dataType typedA dataA j)

/-- **Every closed vector of numbers has exactly one answer, a value of its type.** -/
theorem vec_answer {k t : Tower.Tm 0} (typedK : Typed pkg .nil k numC) (typing : Typed pkg .nil t (vecC numC k)) :
    ∃ v, Value v ∧ DirectedAnswer pkg t v ∧ Typed pkg .nil v (vecC numC k) ∧
      ∀ w, DirectedAnswer pkg t w → w = v := by
  obtain ⟨v, value, answer, typed, -, unique⟩ :=
    data_answer (vec_dataType D.num_typed .num typedK) typing
  exact ⟨v, value, answer, typed, unique⟩

end NativeTypesOnTheStep.Computing.DirectedAnswers

section Audit
open NativeTypesOnTheStep.Computing.DirectedAnswers
#print axioms DataType.canonical
#print axioms pi_not_dataType
#print axioms head_not_dataType
#print axioms id_not_dataType
#print axioms Value.normal
#print axioms ctorTree_numeral
#print axioms vectors_noNeutral
#print axioms num_reaches
#print axioms unit_reaches
#print axioms sigma_reaches
#print axioms reaches_value
#print axioms data_answer
#print axioms data_conv_answer
#print axioms num_answer
#print axioms vec_dataType
#print axioms vec_answer
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
