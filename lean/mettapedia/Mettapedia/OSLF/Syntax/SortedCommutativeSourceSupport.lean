import Mettapedia.OSLF.Syntax.SortedCommutativeObserverSupport

/-!
# Source reconstruction from hereditary zero observer support

Zero support reconstructs the independently formed source value and context,
including all children, siblings and residues. The reconstruction is earned
on actual raw terms and descends through their generated equations. It is
restricted to contexts whose input is the original base sort; no arbitrary
observer-frame erasure is claimed to preserve closed-value action.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open scoped BigOperators

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

theorem observerCount_zero_reconstruction {sort : Srt arity} (supplied : Value arity sort)
    (pure : observerCount supplied = 0) :
    sort = .base ∧ HEq (Source.embed (Source.erase supplied)) supplied := by
  revert pure
  apply @Term.rec (signature arity) (Parallel arity)
    (fun sort supplied => observerCount supplied = 0 →
      sort = .base ∧ HEq (Source.embed (Source.erase supplied)) supplied) (t := supplied)
  · intro sort parallel _
    change sort = .base at parallel
    subst sort
    exact ⟨rfl, HEq.rfl⟩
  · intro sort parallel first second firstRead secondRead pure
    change sort = .base at parallel
    subst sort
    change observerCount first + observerCount second = 0 at pure
    rcases Nat.add_eq_zero_iff.mp pure with ⟨firstPure, secondPure⟩
    exact ⟨rfl, heq_of_eq (congrArg₂ (Term.cut (signature := signature arity)
      (Parallel := Parallel arity) rfl) (eq_of_heq (firstRead firstPure).2)
        (eq_of_heq (secondRead secondPure).2))⟩
  · intro constructor arguments inductionHypothesis pure
    cases constructor with
    | original symbol =>
      change 0 + (∑ position, observerCount (arguments position)) = 0 at pure
      have totalZero : (∑ position, observerCount (arguments position)) = 0 := by omega
      have eachZero : ∀ position, observerCount (arguments position) = 0 := by
        intro position
        have bounded := Finset.single_le_sum (fun other _ => Nat.zero_le (observerCount (arguments other)))
          (Finset.mem_univ position)
        omega
      exact ⟨rfl, heq_of_eq (congrArg (Term.node (signature := signature arity)
        (Parallel := Parallel arity) (Constructor.original symbol))
          (funext (fun position => eq_of_heq (inductionHypothesis position (eachZero position)).2)))⟩
    | arguments constructor =>
      change 1 + (∑ position, observerCount (arguments position)) = 0 at pure
      omega
    | probe instrument =>
      change 1 + (∑ position, observerCount (arguments position)) = 0 at pure
      omega
    | cut instrument =>
      change 1 + (∑ position, observerCount (arguments position)) = 0 at pure
      omega

theorem observerCount_zero_sort {sort : Srt arity} (supplied : Value arity sort)
    (pure : observerCount supplied = 0) : sort = .base :=
  (observerCount_zero_reconstruction supplied pure).1

theorem observerCount_zero_readback (supplied : Value arity .base) (pure : observerCount supplied = 0) :
    Source.embed (Source.erase supplied) = supplied :=
  eq_of_heq (observerCount_zero_reconstruction supplied pure).2

theorem observerCount_embed {sort : (Source.signature arity).Srt}
    (supplied : Term (Source.signature arity) (Source.Parallel arity) sort) :
    observerCount (Source.embed supplied) = 0 := by
  apply @Term.rec (Source.signature arity) (Source.Parallel arity)
    (fun _ supplied => observerCount (Source.embed supplied) = 0) (t := supplied)
  · intro sort parallel
    rfl
  · intro sort parallel first second firstRead secondRead
    change observerCount (Source.embed first) + observerCount (Source.embed second) = 0
    rw [firstRead, secondRead]
  · intro constructor arguments inductionHypothesis
    change 0 + (∑ position, observerCount (Source.embed (arguments position))) = 0
    simp only [inductionHypothesis, Finset.sum_const_zero, Nat.add_zero]

theorem classObserverCount_zero_sort {sort : Srt arity} (supplied : ValueClass arity sort)
    (pure : classObserverCount supplied = 0) : sort = .base := by
  revert pure
  exact Quotient.inductionOn supplied (fun raw => observerCount_zero_sort raw)

theorem classObserverCount_zero_readback (supplied : ValueClass arity .base)
    (pure : classObserverCount supplied = 0) :
    Source.classEmbedding (Source.classRetraction supplied) = supplied := by
  revert pure
  refine Quotient.inductionOn supplied ?_
  intro raw pure
  exact congrArg classOf (observerCount_zero_readback raw pure)

theorem classObserverCount_embedding (supplied : Source.ValueClass arity) :
    classObserverCount (Source.classEmbedding supplied) = 0 :=
  Quotient.inductionOn supplied observerCount_embed

theorem siblingCount_zero {constructor : Constructor arity}
    {position : Fin ((signature arity).arity constructor)}
    (siblings : (other : Fin ((signature arity).arity constructor)) → other ≠ position →
      Value arity ((signature arity).input constructor other))
    (pure : siblingCount constructor position siblings = 0)
    (other : Fin ((signature arity).arity constructor)) (absent : other ≠ position) :
    observerCount (siblings other absent) = 0 := by
  classical
  have bounded := Finset.single_le_sum
    (fun index _ => Nat.zero_le (if different : index ≠ position then observerCount (siblings index different) else 0))
    (Finset.mem_univ other)
  simp only [dif_pos absent] at bounded
  change _ ≤ siblingCount constructor position siblings at bounded
  omega

theorem contextObserverCount_zero_reconstruction {target : Srt arity}
    (supplied : RawContext (signature arity) (Parallel arity) .base target)
    (pure : contextObserverCount supplied = 0) :
    target = .base ∧ HEq (Source.embedContext (Source.eraseContext supplied)) supplied := by
  revert pure
  apply @RawContext.rec (signature arity) (Parallel arity) .base
    (fun target supplied => contextObserverCount supplied = 0 →
      target = .base ∧ HEq (Source.embedContext (Source.eraseContext supplied)) supplied) (t := supplied)
  · intro _
    exact ⟨rfl, HEq.rfl⟩
  · intro constructor position siblings inner inductionHypothesis pure
    cases constructor with
    | original symbol =>
      change 0 + siblingCount (.original symbol) position siblings + contextObserverCount inner = 0 at pure
      have siblingsPure : siblingCount (.original symbol) position siblings = 0 := by omega
      have innerPure : contextObserverCount inner = 0 := by omega
      have siblingsRead :
          (fun other absent => Source.embed (Source.erase (siblings other absent))) = siblings := by
        funext other absent
        exact observerCount_zero_readback (siblings other absent) (siblingCount_zero siblings siblingsPure other absent)
      exact ⟨rfl, heq_of_eq (congrArg₂
        (RawContext.frame (signature := signature arity) (Parallel := Parallel arity)
          (Constructor.original symbol) position) siblingsRead (eq_of_heq (inductionHypothesis innerPure).2))⟩
    | arguments constructor =>
      change 1 + siblingCount (.arguments constructor) position siblings + contextObserverCount inner = 0 at pure
      omega
    | probe instrument =>
      change 1 + siblingCount (.probe instrument) position siblings + contextObserverCount inner = 0 at pure
      omega
    | cut instrument =>
      change 1 + siblingCount (.cut instrument) position siblings + contextObserverCount inner = 0 at pure
      omega
  · intro target parallel inner sibling inductionHypothesis pure
    change target = .base at parallel
    subst target
    change contextObserverCount inner + observerCount sibling = 0 at pure
    rcases Nat.add_eq_zero_iff.mp pure with ⟨innerPure, siblingPure⟩
    exact ⟨rfl, heq_of_eq (congrArg₂
      (RawContext.left (signature := signature arity) (Parallel := Parallel arity) rfl)
        (eq_of_heq (inductionHypothesis innerPure).2) (observerCount_zero_readback sibling siblingPure))⟩
  · intro target parallel sibling inner inductionHypothesis pure
    change target = .base at parallel
    subst target
    change observerCount sibling + contextObserverCount inner = 0 at pure
    rcases Nat.add_eq_zero_iff.mp pure with ⟨siblingPure, innerPure⟩
    exact ⟨rfl, heq_of_eq (congrArg₂
      (RawContext.right (signature := signature arity) (Parallel := Parallel arity) rfl)
        (observerCount_zero_readback sibling siblingPure) (eq_of_heq (inductionHypothesis innerPure).2))⟩

theorem contextObserverCount_zero_sort {target : Srt arity}
    (supplied : RawContext (signature arity) (Parallel arity) .base target)
    (pure : contextObserverCount supplied = 0) : target = .base :=
  (contextObserverCount_zero_reconstruction supplied pure).1

theorem contextObserverCount_zero_readback
    (supplied : RawContext (signature arity) (Parallel arity) .base .base)
    (pure : contextObserverCount supplied = 0) :
    Source.embedContext (Source.eraseContext supplied) = supplied :=
  eq_of_heq (contextObserverCount_zero_reconstruction supplied pure).2

theorem contextObserverCount_embed {source target : (Source.signature arity).Srt}
    (supplied : RawContext (Source.signature arity) (Source.Parallel arity) source target) :
    contextObserverCount (Source.embedContext supplied) = 0 := by
  apply @RawContext.rec (Source.signature arity) (Source.Parallel arity) source
    (fun _ supplied => contextObserverCount (Source.embedContext supplied) = 0) (t := supplied)
  · rfl
  · intro constructor position siblings inner inductionHypothesis
    change 0 + siblingCount (.original constructor) position
      (fun other absent => Source.embed (siblings other absent)) + contextObserverCount (Source.embedContext inner) = 0
    rw [inductionHypothesis]
    unfold siblingCount
    simp only [observerCount_embed, dite_eq_ite, ite_self, Finset.sum_const_zero, Nat.add_zero]
  · intro target parallel inner sibling inductionHypothesis
    change contextObserverCount (Source.embedContext inner) + observerCount (Source.embed sibling) = 0
    rw [inductionHypothesis, observerCount_embed]
  · intro target parallel sibling inner inductionHypothesis
    change observerCount (Source.embed sibling) + contextObserverCount (Source.embedContext inner) = 0
    rw [observerCount_embed, inductionHypothesis]

theorem classContextObserverCount_zero_sort {target : Srt arity}
    (supplied : ContextClass (signature arity) (Parallel arity) .base target)
    (pure : classContextObserverCount supplied = 0) : target = .base := by
  revert pure
  exact Quotient.inductionOn supplied (fun raw => contextObserverCount_zero_sort raw)

theorem classContextObserverCount_zero_readback
    (supplied : ContextClass (signature arity) (Parallel arity) .base .base)
    (pure : classContextObserverCount supplied = 0) :
    Source.contextEmbedding (Source.contextRetraction supplied) = supplied := by
  revert pure
  refine Quotient.inductionOn supplied ?_
  intro raw pure
  exact congrArg contextClassOf (contextObserverCount_zero_readback raw pure)

theorem classContextObserverCount_embedding
    (supplied : ContextClass (Source.signature arity) (Source.Parallel arity) (ULift.up ()) (ULift.up ())) :
    classContextObserverCount (Source.contextEmbedding supplied) = 0 :=
  Quotient.inductionOn supplied contextObserverCount_embed

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support
