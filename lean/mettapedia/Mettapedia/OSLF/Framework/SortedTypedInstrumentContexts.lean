import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceReadout

/-!+# Complete heterogeneous source contexts and zero-support reconstruction

Source contexts include every sibling at its actual declared sort. The
hereditary measure covers siblings and parallel residues as well as the
selected constructor path. A zero-support context from an original sort
reconstructs a complete source context, without assuming a ground inhabitant
or a faithful ground filling action.
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

def embedContext {first second : source.Srt} : RawContext source Parallel first second →
    RawContext (signature source Parallel) NativeParallel (.original first) (.original second)
  | .hole => .hole
  | .frame constructor position siblings inner =>
      RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel)
        (.original constructor) position (fun other absent => embed (siblings other absent)) (embedContext inner)
  | .left parallel inner sibling =>
      RawContext.left (signature := signature source Parallel) (Parallel := NativeParallel)
        (sort := .original _) parallel (embedContext inner) (embed sibling)
  | .right parallel sibling inner =>
      RawContext.right (signature := signature source Parallel) (Parallel := NativeParallel)
        (sort := .original _) parallel (embed sibling) (embedContext inner)

theorem embedContext_equation {first second : source.Srt}
    {before after : RawContext source Parallel first second} (equation : ContextEquation before after) :
    ContextEquation (embedContext before) (embedContext after) := by
  induction equation with
  | refl => exact .refl _
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstRead secondRead => exact firstRead.trans secondRead
  | frame constructor position siblings _ inductionHypothesis =>
    exact ContextEquation.frame (signature := signature source Parallel) (Parallel := NativeParallel)
      (.original constructor) position
      (fun other absent => embed_equation (siblings other absent)) inductionHypothesis
  | left parallel _ sibling inductionHypothesis =>
    exact ContextEquation.left (signature := signature source Parallel) (Parallel := NativeParallel)
      (target := .original _) parallel inductionHypothesis (embed_equation sibling)
  | right parallel sibling _ inductionHypothesis =>
    exact ContextEquation.right (signature := signature source Parallel) (Parallel := NativeParallel)
      (target := .original _) parallel (embed_equation sibling) inductionHypothesis
  | comm parallel inner sibling =>
    exact ContextEquation.comm (signature := signature source Parallel) (Parallel := NativeParallel)
      (target := .original _) parallel (embedContext inner) (embed sibling)
  | assoc parallel inner first second =>
    exact ContextEquation.assoc (signature := signature source Parallel) (Parallel := NativeParallel)
      (target := .original _) parallel (embedContext inner) (embed first) (embed second)
  | unit parallel inner =>
    exact ContextEquation.unit (signature := signature source Parallel) (Parallel := NativeParallel)
      (target := .original _) parallel (embedContext inner)

theorem embedContext_fill {first second : source.Srt}
    (context : RawContext source Parallel first second) (supplied : Term source Parallel first) :
    (embedContext context).fill (embed supplied) = embed (context.fill supplied) := by
  induction context with
  | hole => rfl
  | frame constructor position siblings inner inductionHypothesis =>
    apply congrArg (Term.node (signature := signature source Parallel) (Parallel := NativeParallel) (.original constructor))
    funext other
    by_cases same : other = position
    · subst other
      simpa only [RawContext.insert, dite_true] using inductionHypothesis
    · simp only [RawContext.insert, dif_neg same]
  | left parallel inner sibling inductionHypothesis =>
    exact congrArg (fun value => Term.cut (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original _) parallel value (embed sibling)) inductionHypothesis
  | right parallel sibling inner inductionHypothesis =>
    exact congrArg (Term.cut (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original _) parallel (embed sibling)) inductionHypothesis

theorem embedContext_comp {first second third : source.Srt}
    (before : RawContext source Parallel first second) (after : RawContext source Parallel second third) :
    embedContext (before.comp after) = (embedContext before).comp (embedContext after) := by
  induction after with
  | hole => rfl
  | frame constructor position siblings inner inductionHypothesis =>
    exact congrArg (RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel)
      (.original constructor) position (fun other absent => embed (siblings other absent))) inductionHypothesis
  | left parallel inner sibling inductionHypothesis =>
    exact congrArg (fun context => RawContext.left (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original _) parallel context (embed sibling)) inductionHypothesis
  | right parallel sibling inner inductionHypothesis =>
    exact congrArg (RawContext.right (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original _) parallel (embed sibling)) inductionHypothesis

def contextEmbedding {first second : source.Srt} : ContextClass source Parallel first second →
    ContextClass (signature source Parallel) NativeParallel (.original first) (.original second) :=
  Quotient.map embedContext (fun _ _ equation => embedContext_equation equation)

theorem contextEmbedding_fill {first second : source.Srt}
    (context : ContextClass source Parallel first second) (supplied : Class source Parallel first) :
    (contextEmbedding context).fill (classEmbedding supplied) = classEmbedding (context.fill supplied) :=
  Quotient.inductionOn₂ context supplied (fun raw term => congrArg classOf (embedContext_fill raw term))

theorem contextEmbedding_comp {first second third : source.Srt}
    (before : ContextClass source Parallel first second) (after : ContextClass source Parallel second third) :
    contextEmbedding (before.comp after) = (contextEmbedding before).comp (contextEmbedding after) :=
  Quotient.inductionOn₂ before after (fun before after => congrArg contextClassOf (embedContext_comp before after))

def siblingCount (constructor : Constructor source Parallel)
    (position : Fin ((signature source Parallel).arity constructor))
    (siblings : (other : Fin ((signature source Parallel).arity constructor)) → other ≠ position →
      Value (source := source) (Parallel := Parallel) ((signature source Parallel).input constructor other)) : Nat :=
  ∑ other, if absent : other ≠ position then observerCount (siblings other absent) else 0

theorem siblingCount_zero {constructor : Constructor source Parallel}
    {position : Fin ((signature source Parallel).arity constructor)}
    (siblings : (other : Fin ((signature source Parallel).arity constructor)) → other ≠ position →
      Value (source := source) (Parallel := Parallel) ((signature source Parallel).input constructor other))
    (pure : siblingCount constructor position siblings = 0)
    (other : Fin ((signature source Parallel).arity constructor)) (absent : other ≠ position) :
    observerCount (siblings other absent) = 0 := by
  classical
  have bounded := Finset.single_le_sum
    (fun index _ => Nat.zero_le (if different : index ≠ position then observerCount (siblings index different) else 0))
    (Finset.mem_univ other)
  simp only [dif_pos absent] at bounded
  change _ ≤ siblingCount constructor position siblings at bounded
  omega

def contextObserverCount {first second : Srt source Parallel}
    (supplied : RawContext (signature source Parallel) NativeParallel first second) : Nat :=
  @RawContext.rec (signature source Parallel) NativeParallel first (fun _ _ => Nat) 0
    (fun constructor position siblings _ inner => constructorWeight constructor + siblingCount constructor position siblings + inner)
    (fun _ _ sibling inner => inner + observerCount sibling)
    (fun _ sibling _ inner => observerCount sibling + inner) second supplied

theorem contextObserverCount_equation {first second : Srt source Parallel}
    {before after : RawContext (signature source Parallel) NativeParallel first second}
    (equation : ContextEquation before after) : contextObserverCount before = contextObserverCount after := by
  apply @ContextEquation.rec (signature source Parallel) NativeParallel first
    (fun {_target} {before after} _ => contextObserverCount before = contextObserverCount after) (t := equation)
  · intro target context
    rfl
  · intro target before after equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro target before middle after firstEq secondEq firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor position firstSiblings secondSiblings before after siblings equation inductionHypothesis
    have siblingsRead : siblingCount constructor position firstSiblings = siblingCount constructor position secondSiblings := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases absent : other ≠ position
      · simpa only [dif_pos absent] using observerCount_equation (siblings other absent)
      · simp only [dif_neg absent]
    exact congrArg₂ (fun siblings inner => constructorWeight constructor + siblings + inner) siblingsRead inductionHypothesis
  · intro target parallel before after first second inner sibling inductionHypothesis
    exact congrArg₂ (· + ·) inductionHypothesis (observerCount_equation sibling)
  · intro target parallel first second before after sibling inner inductionHypothesis
    exact congrArg₂ (· + ·) (observerCount_equation sibling) inductionHypothesis
  · intro target parallel inner sibling
    exact Nat.add_comm _ _
  · intro target parallel inner first second
    exact Nat.add_assoc _ _ _
  · intro target parallel inner
    exact Nat.add_zero _

def classContextObserverCount {first second : Srt source Parallel} :
    ContextClass (signature source Parallel) NativeParallel first second → Nat :=
  Quotient.lift contextObserverCount (fun _ _ equation => contextObserverCount_equation equation)

theorem contextObserverCount_embed {first second : source.Srt} (supplied : RawContext source Parallel first second) :
    contextObserverCount (embedContext supplied) = 0 := by
  induction supplied with
  | hole => rfl
  | frame constructor position siblings inner inductionHypothesis =>
    change 0 + siblingCount (.original constructor) position
      (fun other absent => embed (siblings other absent)) + contextObserverCount (embedContext inner) = 0
    rw [inductionHypothesis]
    unfold siblingCount
    simp only [observerCount_embed, dite_eq_ite, ite_self, Finset.sum_const_zero, Nat.add_zero]
  | left parallel inner sibling inductionHypothesis =>
    change contextObserverCount (embedContext inner) + observerCount (embed sibling) = 0
    rw [inductionHypothesis, observerCount_embed]
  | right parallel sibling inner inductionHypothesis =>
    change observerCount (embed sibling) + contextObserverCount (embedContext inner) = 0
    rw [observerCount_embed, inductionHypothesis]

theorem contextObserverCount_zero_reconstruction {first : source.Srt} {second : Srt source Parallel}
    (supplied : RawContext (signature source Parallel) NativeParallel (.original first) second)
    (pure : contextObserverCount supplied = 0) :
    ∃ original : source.Srt, ∃ context : RawContext source Parallel first original,
      second = .original original ∧ HEq (embedContext context) supplied := by
  classical
  revert pure
  apply @RawContext.rec (signature source Parallel) NativeParallel (.original first)
    (fun second supplied => contextObserverCount supplied = 0 →
      ∃ original : source.Srt, ∃ context : RawContext source Parallel first original,
        second = .original original ∧ HEq (embedContext context) supplied) (t := supplied)
  · intro _
    exact ⟨first, .hole, rfl, HEq.rfl⟩
  · intro constructor position siblings inner inductionHypothesis pure
    cases constructor with
    | original constructor =>
      change 0 + siblingCount (.original constructor) position siblings + contextObserverCount inner = 0 at pure
      have siblingsPure : siblingCount (.original constructor) position siblings = 0 := by omega
      have innerPure : contextObserverCount inner = 0 := by omega
      have siblingsSource : ∀ other absent, ∃ term : Term source Parallel (source.input constructor other),
          embed term = siblings other absent := by
        intro other absent
        exact observerCount_zero_original (siblings other absent) (siblingCount_zero siblings siblingsPure other absent)
      choose sourceSiblings siblingRead using siblingsSource
      rcases inductionHypothesis innerPure with ⟨original, sourceInner, sortEq, innerRead⟩
      have originalEq : source.input constructor position = original := Srt.original.inj sortEq
      subst original
      exact ⟨source.output constructor, .frame constructor position sourceSiblings sourceInner, rfl,
        heq_of_eq (congrArg₂
          (RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel)
            (.original constructor) position)
          (funext (fun other => funext (siblingRead other))) (eq_of_heq innerRead))⟩
    | arguments head =>
      change 1 + siblingCount (.arguments head) position siblings + contextObserverCount inner = 0 at pure
      omega
    | probe instrument =>
      change 1 + siblingCount (.probe instrument) position siblings + contextObserverCount inner = 0 at pure
      omega
    | cut instrument =>
      change 1 + siblingCount (.cut instrument) position siblings + contextObserverCount inner = 0 at pure
      omega
  · intro second parallel inner sibling inductionHypothesis pure
    cases second with
    | original original =>
      change contextObserverCount inner + observerCount sibling = 0 at pure
      rcases Nat.add_eq_zero_iff.mp pure with ⟨innerPure, siblingPure⟩
      rcases inductionHypothesis innerPure with ⟨sourceSort, sourceInner, sortEq, innerRead⟩
      have sourceSortEq : original = sourceSort := Srt.original.inj sortEq
      subst sourceSort
      obtain ⟨sourceSibling, siblingRead⟩ := observerCount_zero_original sibling siblingPure
      exact ⟨original, .left parallel sourceInner sourceSibling, rfl,
        heq_of_eq (congrArg₂ (RawContext.left (signature := signature source Parallel)
          (Parallel := NativeParallel) (sort := .original original) parallel)
            (eq_of_heq innerRead) siblingRead)⟩
    | arguments => exact parallel.elim
    | probe => exact parallel.elim
  · intro second parallel sibling inner inductionHypothesis pure
    cases second with
    | original original =>
      change observerCount sibling + contextObserverCount inner = 0 at pure
      rcases Nat.add_eq_zero_iff.mp pure with ⟨siblingPure, innerPure⟩
      rcases inductionHypothesis innerPure with ⟨sourceSort, sourceInner, sortEq, innerRead⟩
      have sourceSortEq : original = sourceSort := Srt.original.inj sortEq
      subst sourceSort
      obtain ⟨sourceSibling, siblingRead⟩ := observerCount_zero_original sibling siblingPure
      exact ⟨original, .right parallel sourceSibling sourceInner, rfl,
        heq_of_eq (congrArg₂ (RawContext.right (signature := signature source Parallel)
          (Parallel := NativeParallel) (sort := .original original) parallel)
            siblingRead (eq_of_heq innerRead))⟩
    | arguments => exact parallel.elim
    | probe => exact parallel.elim

theorem contextObserverCount_zero_original {first second : source.Srt}
    (supplied : RawContext (signature source Parallel) NativeParallel (.original first) (.original second))
    (pure : contextObserverCount supplied = 0) :
    ∃ context : RawContext source Parallel first second, embedContext context = supplied := by
  rcases contextObserverCount_zero_reconstruction supplied pure with ⟨original, context, sortEq, read⟩
  have originalEq : second = original := Srt.original.inj sortEq
  subst original
  exact ⟨context, eq_of_heq read⟩

theorem classContextObserverCount_original_iff_source_image {first second : source.Srt}
    (supplied : ContextClass (signature source Parallel) NativeParallel (.original first) (.original second)) :
    classContextObserverCount supplied = 0 ↔
      ∃ context : ContextClass source Parallel first second, contextEmbedding context = supplied := by
  refine ⟨?_, ?_⟩
  · refine Quotient.inductionOn supplied ?_
    intro raw pure
    obtain ⟨context, read⟩ := contextObserverCount_zero_original raw pure
    exact ⟨contextClassOf context, congrArg contextClassOf read⟩
  · rintro ⟨context, rfl⟩
    exact Quotient.inductionOn context contextObserverCount_embed

end Mettapedia.OSLF.Framework.SortedTypedInstruments
