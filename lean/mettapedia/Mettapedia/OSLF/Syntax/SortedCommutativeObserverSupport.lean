import Mettapedia.OSLF.Framework.SortedCommutativeSourceCategory
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Hereditary auxiliary-head support in the actual equation category

The measure counts every observer head in complete values and all siblings
of a context. Original constructor frames have weight zero. Actual generated
term/context equations preserve it; complete filling and composition add
these measures. No source-image reconstruction or observer equivalence is
assumed by this support calculation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open scoped BigOperators

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

def constructorWeight : Constructor arity → Nat
  | .original _ => 0
  | .arguments _ => 1
  | .probe _ => 1
  | .cut _ => 1

def observerCount {sort : Srt arity} (supplied : Value arity sort) : Nat :=
  @Term.rec (signature arity) (Parallel arity) (fun _ _ => Nat)
    (fun _ => 0) (fun _ _ _ first second => first + second)
    (fun constructor _ arguments => constructorWeight constructor + ∑ position, arguments position) sort supplied

@[simp] theorem observerCount_zero {sort : Srt arity} (parallel : Parallel arity sort) :
    observerCount (.zero parallel : Value arity sort) = 0 := rfl

@[simp] theorem observerCount_cut {sort : Srt arity} (parallel : Parallel arity sort)
    (first second : Value arity sort) :
    observerCount (.cut parallel first second) = observerCount first + observerCount second := rfl

@[simp] theorem observerCount_node (constructor : Constructor arity)
    (arguments : (position : Fin ((signature arity).arity constructor)) →
      Value arity ((signature arity).input constructor position)) :
    observerCount (.node (signature := signature arity) constructor arguments) =
      constructorWeight constructor + ∑ position, observerCount (arguments position) := rfl

theorem observerCount_equation {sort : Srt arity} {first second : Value arity sort}
    (equation : Equation (signature := signature arity) (Parallel := Parallel arity) first second) :
    observerCount first = observerCount second := by
  apply @Equation.rec (signature arity) (Parallel arity)
    (fun {_sort} {first second} _ => observerCount first = observerCount second) (t := equation)
  · intro sort term
    rfl
  · intro sort first second equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro sort first second third before after firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor first second equations inductionHypothesis
    exact congrArg (fun value => constructorWeight constructor + value)
      (Finset.sum_congr rfl (fun position _ => inductionHypothesis position))
  · intro sort parallel first first' second second' before after firstRead secondRead
    exact congrArg₂ (· + ·) firstRead secondRead
  · intro sort parallel first second third
    exact Nat.add_assoc _ _ _
  · intro sort parallel first second
    exact Nat.add_comm _ _
  · intro sort parallel term
    exact Nat.add_zero _

def classObserverCount {sort : Srt arity} : ValueClass arity sort → Nat :=
  Quotient.lift observerCount (fun _ _ equation => observerCount_equation equation)

def siblingCount (constructor : Constructor arity) (position : Fin ((signature arity).arity constructor))
    (siblings : (other : Fin ((signature arity).arity constructor)) → other ≠ position →
      Value arity ((signature arity).input constructor other)) : Nat :=
  ∑ other, if absent : other ≠ position then observerCount (siblings other absent) else 0

theorem insert_count (constructor : Constructor arity) (position : Fin ((signature arity).arity constructor))
    (siblings : (other : Fin ((signature arity).arity constructor)) → other ≠ position →
      Value arity ((signature arity).input constructor other))
    (supplied : Value arity ((signature arity).input constructor position)) :
    (∑ other, observerCount (RawContext.insert constructor position siblings supplied other)) =
      observerCount supplied + siblingCount constructor position siblings := by
  calc
    _ = ∑ other, ((if other = position then observerCount supplied else 0) +
        (if absent : other ≠ position then observerCount (siblings other absent) else 0)) := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases same : other = position
      · subst other
        simp only [RawContext.insert, dite_true, if_true, ne_eq, not_true_eq_false, dite_false, Nat.add_zero]
      · simp only [RawContext.insert, dif_neg same, if_neg same, dif_pos same, Nat.zero_add]
    _ = observerCount supplied + siblingCount constructor position siblings := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, siblingCount]

def contextObserverCount {source target : Srt arity}
    (supplied : RawContext (signature arity) (Parallel arity) source target) : Nat :=
  @RawContext.rec (signature arity) (Parallel arity) source (fun _ _ => Nat) 0
    (fun constructor position siblings _ inner => constructorWeight constructor + siblingCount constructor position siblings + inner)
    (fun _ _ sibling inner => inner + observerCount sibling)
    (fun _ sibling _ inner => observerCount sibling + inner) target supplied

theorem contextObserverCount_equation {source target : Srt arity}
    {first second : RawContext (signature arity) (Parallel arity) source target}
    (equation : ContextEquation (signature := signature arity) (Parallel := Parallel arity) first second) :
    contextObserverCount first = contextObserverCount second := by
  apply @ContextEquation.rec (signature arity) (Parallel arity) source
    (fun {_target} {first second} _ => contextObserverCount first = contextObserverCount second) (t := equation)
  · intro target context
    rfl
  · intro target first second equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro target first second third before after firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor position firstSiblings secondSiblings first second siblings equation inductionHypothesis
    have siblingRead : siblingCount constructor position firstSiblings = siblingCount constructor position secondSiblings := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases absent : other ≠ position
      · simpa only [siblingCount, dif_pos absent] using observerCount_equation (siblings other absent)
      · simp only [dif_neg absent]
    exact congrArg₂ (fun count inner => constructorWeight constructor + count + inner) siblingRead inductionHypothesis
  · intro target parallel first second before after inner sibling inductionHypothesis
    exact congrArg₂ (· + ·) inductionHypothesis (observerCount_equation sibling)
  · intro target parallel before after first second sibling inner inductionHypothesis
    exact congrArg₂ (· + ·) (observerCount_equation sibling) inductionHypothesis
  · intro target parallel inner sibling
    exact Nat.add_comm _ _
  · intro target parallel inner first second
    exact Nat.add_assoc _ _ _
  · intro target parallel inner
    exact Nat.add_zero _

theorem contextObserverCount_fill {source target : Srt arity}
    (context : RawContext (signature arity) (Parallel arity) source target) (supplied : Value arity source) :
    observerCount (context.fill supplied) = contextObserverCount context + observerCount supplied := by
  apply @RawContext.rec (signature arity) (Parallel arity) source
    (fun _ context => observerCount (context.fill supplied) = contextObserverCount context + observerCount supplied)
    (t := context)
  · exact (Nat.zero_add _).symm
  · intro constructor position siblings inner inductionHypothesis
    change constructorWeight constructor +
      (∑ other, observerCount (RawContext.insert constructor position siblings (inner.fill supplied) other)) = _
    rw [insert_count, inductionHypothesis]
    change _ = (constructorWeight constructor + siblingCount constructor position siblings + contextObserverCount inner) + observerCount supplied
    omega
  · intro target parallel inner sibling inductionHypothesis
    change observerCount (inner.fill supplied) + observerCount sibling = _
    rw [inductionHypothesis]
    change _ = (contextObserverCount inner + observerCount sibling) + observerCount supplied
    omega
  · intro target parallel sibling inner inductionHypothesis
    change observerCount sibling + observerCount (inner.fill supplied) = _
    rw [inductionHypothesis]
    change _ = (observerCount sibling + contextObserverCount inner) + observerCount supplied
    omega

theorem contextObserverCount_comp {source middle target : Srt arity}
    (inner : RawContext (signature arity) (Parallel arity) source middle)
    (outer : RawContext (signature arity) (Parallel arity) middle target) :
    contextObserverCount (inner.comp outer) = contextObserverCount inner + contextObserverCount outer := by
  apply @RawContext.rec (signature arity) (Parallel arity) middle
    (fun _ outer => contextObserverCount (inner.comp outer) = contextObserverCount inner + contextObserverCount outer)
    (t := outer)
  · exact (Nat.add_zero _).symm
  · intro constructor position siblings outer inductionHypothesis
    change constructorWeight constructor + siblingCount constructor position siblings + contextObserverCount (inner.comp outer) = _
    rw [inductionHypothesis]
    change _ = contextObserverCount inner + (constructorWeight constructor + siblingCount constructor position siblings + contextObserverCount outer)
    omega
  · intro target parallel outer sibling inductionHypothesis
    change contextObserverCount (inner.comp outer) + observerCount sibling = _
    rw [inductionHypothesis]
    exact Nat.add_assoc _ _ _
  · intro target parallel sibling outer inductionHypothesis
    change observerCount sibling + contextObserverCount (inner.comp outer) = _
    rw [inductionHypothesis]
    change _ = contextObserverCount inner + (observerCount sibling + contextObserverCount outer)
    omega

def classContextObserverCount {source target : Srt arity} :
    ContextClass (signature arity) (Parallel arity) source target → Nat :=
  Quotient.lift contextObserverCount (fun _ _ equation => contextObserverCount_equation equation)

theorem classCount_fill {source target : Srt arity}
    (context : ContextClass (signature arity) (Parallel arity) source target) (supplied : ValueClass arity source) :
    classObserverCount (context.fill supplied) = classContextObserverCount context + classObserverCount supplied :=
  Quotient.inductionOn₂ context supplied contextObserverCount_fill

theorem classCount_comp {source middle target : Srt arity}
    (inner : ContextClass (signature arity) (Parallel arity) source middle)
    (outer : ContextClass (signature arity) (Parallel arity) middle target) :
    classContextObserverCount (inner.comp outer) = classContextObserverCount inner + classContextObserverCount outer :=
  Quotient.inductionOn₂ inner outer contextObserverCount_comp

def arrowObserverCount : {source target : ContextCategory arity} → (source ⟶ target) → Nat
  | _, _, .identity => 0
  | _, _, .value supplied => classObserverCount supplied
  | _, _, .context supplied => classContextObserverCount supplied

theorem arrowCount_comp {source middle target : ContextCategory arity} (first : source ⟶ middle) (second : middle ⟶ target) :
    arrowObserverCount (first ≫ second) = arrowObserverCount first + arrowObserverCount second := by
  cases first with
  | identity => exact (Nat.zero_add _).symm
  | value supplied =>
    cases second with
    | context suppliedContext => exact (classCount_fill suppliedContext supplied).trans (Nat.add_comm _ _)
  | context inner =>
    cases second with
    | context outer => exact classCount_comp inner outer

theorem observerCount_probe (instrument : Probe arity) : observerCount (probe arity instrument) = 1 := by
  change 1 + (∑ position : Fin 0, observerCount (Fin.elim0 position)) = 1
  simp only [Fin.sum_univ_zero, Nat.add_zero]

theorem contextObserverCount_probeContext (instrument : Probe arity) :
    contextObserverCount (probeContext arity instrument) = 2 := by
  unfold probeContext
  change 1 + siblingCount (.cut instrument) 1 _ + 0 = 2
  unfold siblingCount
  change 1 + (∑ other : Fin 2, _) + 0 = 2
  rw [Fin.sum_univ_two]
  norm_num [Fin.cases]
  change 1 + observerCount (probe arity instrument) = 2
  rw [observerCount_probe]

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support
