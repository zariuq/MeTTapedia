import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderContextRuns

/-!
# The native first-order trace quotient on complete firing words

Its generators exchange an admitted pair at its actual before state. Both
orders must be admitted; the native result transport closes the square.
Similarity adds no firing-word equations in this one-frame profile. This
presentation is distinct from the stronger write-ignorance test for rounds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns

open AnnotatedRuns (Firing firstOrder firstOrderTransport follow)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

theorem similar_sites : ∀ {left right : Configuration T O}
    (first : (firstOrder A label).toStep.Run left) (second : (firstOrder A label).toStep.Run right),
    (firstOrderTransport A label).Similar first second → sites A label first = sites A label second
  | _, _, .nil _, .nil _, _ => rfl
  | _, _, .nil _, .cons _ _ _, impossible => False.elim impossible
  | _, _, .cons _ _ _, .nil _, impossible => False.elim impossible
  | _, _, .cons f _ rest, .cons g _ later, related => by
      obtain ⟨_, same, tail⟩ := related
      have fg : f = g := same
      subst g
      exact congrArg (List.cons f) (similar_sites rest later tail)

theorem similar_of_sites {left right : Configuration T O}
    (iso : (firstOrderTransport A label).Iso left right)
    (first : (firstOrder A label).toStep.Run left) (second : (firstOrder A label).toStep.Run right)
    (same : sites A label first = sites A label second) : (firstOrderTransport A label).Similar first second := by
  have equal : (firstOrderTransport A label).moveRun iso first = second :=
    sites_injective A label ((sites_moveRun A label iso first).trans same)
  rw [← equal]
  exact Transport.Similar.moveRun iso first

inductive WordSwap (state : Configuration T O) : List (Firing T S O) → List (Firing T S O) → Prop
  | swap (before suffix : List (Firing T S O)) (f g : Firing T S O)
      (independent : (firstOrderTransport A label).Independent (follow label state before) f g) :
      WordSwap state (before ++ f :: g :: suffix) (before ++ g :: f :: suffix)

abbrev WordTrace (state : Configuration T O) := Relation.EqvGen (WordSwap A label state)

theorem WordSwap.symm {state : Configuration T O} {first second : List (Firing T S O)}
    (swapped : WordSwap A label state first second) : WordSwap A label state second first := by
  cases swapped with
  | swap before suffix f g independent => exact .swap before suffix g f independent.symm

instance wordSwapSymm (state : Configuration T O) : Std.Symm (WordSwap A label state) where
  symm _ _ swapped := swapped.symm A label

theorem WordSwap.cons {state : Configuration T O} (f : Firing T S O)
    {first second : List (Firing T S O)} (swapped : WordSwap A label (f.result label state) first second) :
    WordSwap A label state (f :: first) (f :: second) := by
  cases swapped with
  | swap before suffix g h independent => exact .swap (f :: before) suffix g h independent

theorem native_swap_word {state : Configuration T O}
    {first second : (firstOrder A label).toStep.Run state}
    (swapped : (firstOrderTransport A label).SwapStep first second) :
    WordSwap A label state (sites A label first) (sites A label second) := by
  induction swapped with
  | @here state f g af ag g1 sameG afg f1 sameF agf rest later related =>
      have independent := Transport.swap_independent af ag sameG afg sameF agf related
      have gg : g = g1 := sameG
      have ff : f = f1 := sameF
      subst g1
      subst f1
      have tails := similar_sites A label rest later related
      change WordSwap A label state (f :: g :: sites A label rest) (g :: f :: sites A label later)
      rw [← tails]
      exact .swap [] _ f g independent
  | later f _ _ ih => exact ih.cons A label f

theorem swap_realizes : ∀ (before suffix : List (Firing T S O)) (state : Configuration T O) (f g : Firing T S O),
    (firstOrderTransport A label).Independent (follow label state before) f g →
      ∀ run : (firstOrder A label).toStep.Run state, sites A label run = before ++ f :: g :: suffix →
        ∃ other : (firstOrder A label).toStep.Run state,
          sites A label other = before ++ g :: f :: suffix ∧ (firstOrderTransport A label).TraceEquiv state run other
  | [], suffix, state, f, g, independent, run, word => by
      cases run with
      | nil => cases word
      | cons x allowed rest =>
          have parts := List.cons.inj word
          have head : x = f := parts.1
          subst x
          cases rest with
          | nil => cases parts.2
          | cons y later tail =>
              have second := List.cons.inj parts.2
              have head : y = g := second.1
              subst y
              obtain ⟨af, ag, afg, agf, close, exchange⟩ := independent.swap
              let other : (firstOrder A label).toStep.Run state :=
                .cons g ag (.cons f agf ((firstOrderTransport A label).moveRun close tail))
              refine ⟨other, ?_, .rel _ _ (.inl (exchange tail))⟩
              change g :: f :: sites A label ((firstOrderTransport A label).moveRun close tail) = g :: f :: suffix
              exact congrArg (fun word => g :: f :: word) ((sites_moveRun A label close tail).trans second.2)
  | x :: before, suffix, state, f, g, independent, run, word => by
      cases run with
      | nil => cases word
      | cons y allowed rest =>
          have parts := List.cons.inj word
          have head : y = x := parts.1
          subst y
          obtain ⟨later, sites, related⟩ := swap_realizes before suffix (x.result label state) f g independent rest parts.2
          exact ⟨.cons x allowed later, congrArg (List.cons x) sites, related.cons⟩

theorem WordSwap.realizes {state : Configuration T O} {first second : List (Firing T S O)}
    (swapped : WordSwap A label state first second)
    (run : (firstOrder A label).toStep.Run state) (word : sites A label run = first) :
    ∃ other : (firstOrder A label).toStep.Run state,
      sites A label other = second ∧ (firstOrderTransport A label).TraceEquiv state run other := by
  cases swapped with
  | swap before suffix f g independent => exact swap_realizes A label before suffix state f g independent run word

theorem WordTrace.realizes {state : Configuration T O} {first second : List (Firing T S O)}
    (related : WordTrace A label state first second) :
    ∀ run : (firstOrder A label).toStep.Run state, sites A label run = first →
      ∃ other : (firstOrder A label).toStep.Run state,
        sites A label other = second ∧ (firstOrderTransport A label).TraceEquiv state run other := by
  have path : Relation.ReflTransGen (WordSwap A label state) first second := by
    rw [← Relation.EqvGen.eqvGen_eq_reflTransGen]
    exact related
  clear related
  induction path with
  | refl => exact fun run word => ⟨run, word, .refl _⟩
  | tail _ swapped ih =>
      intro run word
      obtain ⟨middle, middleWord, firstTrace⟩ := ih run word
      obtain ⟨last, lastWord, lastTrace⟩ := swapped.realizes A label middle middleWord
      exact ⟨last, lastWord, .trans _ _ _ firstTrace lastTrace⟩

theorem native_trace_iff_word_trace {state : Configuration T O}
    (first second : (firstOrder A label).toStep.Run state) :
    (firstOrderTransport A label).TraceEquiv state first second ↔
      WordTrace A label state (sites A label first) (sites A label second) := by
  constructor
  · intro related
    induction related with
    | rel a b generator =>
        rcases generator with swapped | similar
        · exact .rel _ _ (native_swap_word A label swapped)
        · rw [similar_sites A label a b similar]
          exact .refl _
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ left right => exact .trans _ _ _ left right
  · intro related
    obtain ⟨other, word, trace⟩ := related.realizes A label first rfl
    have equal : other = second := sites_injective A label word
    exact equal ▸ trace

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns
