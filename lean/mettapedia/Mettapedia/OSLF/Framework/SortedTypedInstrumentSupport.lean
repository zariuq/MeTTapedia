import Mettapedia.OSLF.Framework.SortedTypedInstrumentProfile
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!+# Hereditary observer support and genuinely sorted source reconstruction

The measure counts every auxiliary constructor at every actual coordinate.
Generated AC1 equations preserve the measure. Zero support reconstructs an
original source term at the same declared sort, including its full tuple of
children. The reconstruction uses no inhabitant of an arbitrary source sort
and does not erase arbitrary observer-bearing native values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open Mettapedia.OSLF.SortedCommutative
open scoped BigOperators

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

def constructorWeight : Constructor source Parallel → Nat
  | .original _ => 0
  | .arguments _ => 1
  | .probe _ => 1
  | .cut _ => 1

def observerCount {sort : Srt source Parallel}
    (supplied : Value (source := source) (Parallel := Parallel) sort) : Nat :=
  @Term.rec (signature source Parallel) NativeParallel (fun _ _ => Nat)
    (fun _ => 0) (fun _ _ _ first second => first + second)
    (fun constructor _ arguments => constructorWeight constructor + ∑ position, arguments position)
    sort supplied

@[simp] theorem observerCount_zero {sort : Srt source Parallel} (parallel : NativeParallel sort) :
    observerCount (.zero parallel : Value (source := source) (Parallel := Parallel) sort) = 0 := rfl

@[simp] theorem observerCount_cut {sort : Srt source Parallel} (parallel : NativeParallel sort)
    (first second : Value (source := source) (Parallel := Parallel) sort) :
    observerCount (.cut parallel first second) = observerCount first + observerCount second := rfl

@[simp] theorem observerCount_node (constructor : Constructor source Parallel)
    (arguments : (position : Fin ((signature source Parallel).arity constructor)) →
      Value (source := source) (Parallel := Parallel) ((signature source Parallel).input constructor position)) :
    observerCount (.node (signature := signature source Parallel) (Parallel := NativeParallel)
      constructor arguments) = constructorWeight constructor + ∑ position, observerCount (arguments position) := rfl

theorem observerCount_equation {sort : Srt source Parallel}
    {first second : Value (source := source) (Parallel := Parallel) sort}
    (equation : Equation first second) : observerCount first = observerCount second := by
  apply @Equation.rec (signature source Parallel) NativeParallel
    (fun {_sort} {first second} _ => observerCount first = observerCount second) (t := equation)
  · intro sort term
    rfl
  · intro sort first second equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro sort first second third before after firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor first second equations inductionHypothesis
    exact congrArg (fun total => constructorWeight constructor + total)
      (Finset.sum_congr rfl (fun position _ => inductionHypothesis position))
  · intro sort parallel first first' second second' before after firstRead secondRead
    exact congrArg₂ (· + ·) firstRead secondRead
  · intro sort parallel first second third
    exact Nat.add_assoc _ _ _
  · intro sort parallel first second
    exact Nat.add_comm _ _
  · intro sort parallel term
    exact Nat.add_zero _

def classObserverCount {sort : Srt source Parallel} :
    ValueClass (source := source) (Parallel := Parallel) sort → Nat :=
  Quotient.lift observerCount (fun _ _ equation => observerCount_equation equation)

theorem observerCount_embed {sort : source.Srt} (supplied : Term source Parallel sort) :
    observerCount (embed supplied) = 0 := by
  induction supplied with
  | zero => rfl
  | cut _ _ _ firstRead secondRead =>
    change observerCount (embed _) + observerCount (embed _) = 0
    rw [firstRead, secondRead]
  | node constructor arguments inductionHypothesis =>
    change 0 + (∑ position, observerCount (embed (arguments position))) = 0
    simp only [inductionHypothesis, Finset.sum_const_zero, Nat.add_zero]

theorem classObserverCount_embedding {sort : source.Srt} (supplied : Class source Parallel sort) :
    classObserverCount (classEmbedding supplied) = 0 :=
  Quotient.inductionOn supplied observerCount_embed

theorem observerCount_zero_reconstruction {sort : Srt source Parallel}
    (supplied : Value (source := source) (Parallel := Parallel) sort)
    (pure : observerCount supplied = 0) :
    ∃ original : source.Srt, ∃ term : Term source Parallel original,
      sort = .original original ∧ HEq (embed term) supplied := by
  classical
  revert pure
  apply @Term.rec (signature source Parallel) NativeParallel
    (fun sort supplied => observerCount supplied = 0 →
      ∃ original : source.Srt, ∃ term : Term source Parallel original,
        sort = .original original ∧ HEq (embed term) supplied) (t := supplied)
  · intro sort parallel _
    cases sort with
    | original original => exact ⟨original, .zero parallel, rfl, HEq.rfl⟩
    | arguments => exact parallel.elim
    | probe => exact parallel.elim
  · intro sort parallel first second firstRead secondRead pure
    cases sort with
    | original original =>
      change observerCount first + observerCount second = 0 at pure
      rcases Nat.add_eq_zero_iff.mp pure with ⟨firstPure, secondPure⟩
      rcases firstRead firstPure with ⟨firstSort, firstSource, firstSortEq, firstEq⟩
      rcases secondRead secondPure with ⟨secondSort, secondSource, secondSortEq, secondEq⟩
      have firstSortRead : original = firstSort := Srt.original.inj firstSortEq
      have secondSortRead : original = secondSort := Srt.original.inj secondSortEq
      subst firstSort
      subst secondSort
      exact ⟨original, .cut parallel firstSource secondSource, rfl,
        heq_of_eq (congrArg₂ (Term.cut (signature := signature source Parallel)
          (Parallel := NativeParallel) (sort := .original original) parallel)
            (eq_of_heq firstEq) (eq_of_heq secondEq))⟩
    | arguments => exact parallel.elim
    | probe => exact parallel.elim
  · intro constructor arguments inductionHypothesis pure
    cases constructor with
    | original constructor =>
      change 0 + (∑ position, observerCount (arguments position)) = 0 at pure
      have totalZero : (∑ position, observerCount (arguments position)) = 0 := by omega
      have eachZero : ∀ position, observerCount (arguments position) = 0 := by
        intro position
        have bounded := Finset.single_le_sum
          (fun other _ => Nat.zero_le (observerCount (arguments other)))
          (Finset.mem_univ position)
        omega
      have eachSource : ∀ position, ∃ term : Term source Parallel (source.input constructor position),
          embed term = arguments position := by
        intro position
        rcases inductionHypothesis position (eachZero position) with ⟨original, term, sortEq, read⟩
        have inputRead : source.input constructor position = original := Srt.original.inj sortEq
        subst original
        exact ⟨term, eq_of_heq read⟩
      choose children readings using eachSource
      exact ⟨source.output constructor, .node constructor children, rfl,
        heq_of_eq (congrArg (Term.node (signature := signature source Parallel)
          (Parallel := NativeParallel) (.original constructor)) (funext readings))⟩
    | arguments head =>
      change 1 + (∑ position, observerCount (arguments position)) = 0 at pure
      omega
    | probe instrument =>
      change 1 + (∑ position, observerCount (arguments position)) = 0 at pure
      omega
    | cut instrument =>
      change 1 + (∑ position, observerCount (arguments position)) = 0 at pure
      omega

theorem observerCount_zero_original {sort : source.Srt}
    (supplied : Value (source := source) (Parallel := Parallel) (.original sort))
    (pure : observerCount supplied = 0) :
    ∃ term : Term source Parallel sort, embed term = supplied := by
  rcases observerCount_zero_reconstruction supplied pure with ⟨original, term, sortEq, read⟩
  have originalEq : sort = original := Srt.original.inj sortEq
  subst original
  exact ⟨term, eq_of_heq read⟩

theorem classObserverCount_zero_original {sort : source.Srt}
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original sort))
    (pure : classObserverCount supplied = 0) :
    ∃ term : Class source Parallel sort, classEmbedding term = supplied := by
  revert pure
  refine Quotient.inductionOn supplied ?_
  intro raw pure
  obtain ⟨term, read⟩ := observerCount_zero_original raw pure
  exact ⟨classOf term, congrArg classOf read⟩

theorem classObserverCount_original_iff_source_image {sort : source.Srt}
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original sort)) :
    classObserverCount supplied = 0 ↔
      ∃ term : Class source Parallel sort, classEmbedding term = supplied := by
  refine ⟨classObserverCount_zero_original supplied, ?_⟩
  rintro ⟨term, rfl⟩
  exact classObserverCount_embedding term

end Mettapedia.OSLF.Framework.SortedTypedInstruments
