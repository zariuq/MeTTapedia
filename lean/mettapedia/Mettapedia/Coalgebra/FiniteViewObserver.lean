import Mettapedia.Coalgebra.StreamFinality
import Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

/-!
# Finite stream views as observer-relative authority

The final stream coalgebra admits a coherent family of finite observers.  This
module connects those observers to the generic observer-relative
transformation and selection interfaces.

Overwriting the first unobserved position is lawful for the corresponding
finite observer and unlawful for the complete observation tower.  Likewise,
two streams which agree through a finite depth admit observational selection
at that depth but not at the identity observer.

The point is not that finite observation licenses arbitrary loss.  It licenses
exactly the transformations and selections proved constant on the declared
observer fibre.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.FiniteViewObserver

open Mettapedia.Coalgebra.StreamFinality
open Mettapedia.Cybernetics
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

universe uLabel

/-! ## The coherent observer tower -/

def finiteObserver {Label : Type uLabel} (depth : Nat) :
    Observer (Stream Label) (Prefix Label depth) where
  observe := finiteView depth

def completeTowerObserver {Label : Type uLabel} :
    Observer (Stream Label) ((depth : Nat) → Prefix Label depth) where
  observe := allPrefixes

theorem finiteObserver_not_injective {Label : Type uLabel}
    (depth : Nat) {ordinary changed : Label}
    (different : ordinary ≠ changed) :
    ¬ Function.Injective
      (finiteObserver (Label := Label) depth).observe :=
  finiteView_not_injective depth different

theorem completeTowerObserver_injective {Label : Type uLabel} :
    Function.Injective
      (completeTowerObserver (Label := Label)).observe :=
  allPrefixes_injective

/-- Earlier observation is exactly a postcomposition of every longer view. -/
theorem finiteObserver_postcompose
    {Label : Type uLabel} {earlier later : Nat}
    (bounded : earlier ≤ later) :
    finiteObserver (Label := Label) earlier =
      (finiteObserver (Label := Label) later).postcompose
        (restrictPrefix bounded) := by
  have observationEquality :
      (@finiteView Label earlier) =
        restrictPrefix bounded ∘ (@finiteView Label later) := by
    funext stream
    exact restrictPrefix_finiteView bounded stream
  cases observationEquality
  rfl

/-! ## A transformation lawful at one finite observer -/

/-- Replace the label at one selected position, retaining every other
position. -/
def overwriteAt {Label : Type uLabel}
    (depth : Nat) (replacement : Label) (stream : Stream Label) :
    Stream Label :=
  fun index => if index = depth then replacement else stream index

/-- Replacing position `depth` cannot be seen by the prefix of length
`depth`. -/
def overwritePreservesFinite {Label : Type uLabel}
    (depth : Nat) (replacement : Label) :
    ObserverPreservingMap (Stream Label) (Stream Label) (Prefix Label depth)
      (finiteObserver depth) (finiteObserver depth) where
  transform := overwriteAt depth replacement
  preserves := by
    intro stream
    funext index
    have different : index.val ≠ depth := Nat.ne_of_lt index.isLt
    simp [finiteObserver, finiteView, overwriteAt, different]

/-- The same overwrite is visible to the complete tower whenever it changes
the selected label. -/
theorem overwrite_does_not_preserve_completeTower
    (depth : Nat) :
    ¬ ∀ stream : Stream Bool,
      (completeTowerObserver.observe
          (overwriteAt depth false stream)) =
        completeTowerObserver.observe stream := by
  intro alleged
  have towerEquality := alleged (constant true)
  have streamEquality :
      overwriteAt depth false (constant true) = constant true :=
    completeTowerObserver_injective towerEquality
  have atDepth := congrFun streamEquality depth
  simp [overwriteAt, constant] at atDepth

/-! ## Observer-indexed selection over retained worlds -/

/-- A complete two-world fibre: the worlds first differ exactly at `depth`. -/
def finitePairFamily (depth : Nat) :
    AlternativeFamily Unit (Stream Bool) where
  accepts := fun _ stream =>
    stream = constant false ∨
      stream = changedAt depth false true

theorem finitePairFamily_covered (depth : Nat) :
    (finitePairFamily depth).Covered := by
  intro question
  exact ⟨constant false, Or.inl rfl⟩

theorem finitePairFamily_finite_invariant (depth : Nat) :
    (finitePairFamily depth).ObserverInvariant (finiteObserver depth) := by
  intro question first second firstAccepted secondAccepted
  rcases firstAccepted with firstConstant | firstChanged <;>
    rcases secondAccepted with secondConstant | secondChanged
  · subst first
    subst second
    rfl
  · subst first
    subst second
    exact finiteView_constant_changedAt depth false true
  · subst first
    subst second
    exact (finiteView_constant_changedAt depth false true).symm
  · subst first
    subst second
    rfl

theorem finitePairFamily_not_identity_invariant (depth : Nat) :
    ¬ (finitePairFamily depth).ObserverInvariant
      (Observer.identity (Stream Bool)) := by
  intro invariant
  have equalStreams := invariant ()
    (first := constant false)
    (second := changedAt depth false true)
    (Or.inl rfl) (Or.inr rfl)
  exact constant_ne_changedAt depth Bool.false_ne_true equalStreams

/-- The retained pair admits representative selection for the finite observer.
The family itself is not deleted or identified. -/
theorem finitePairFamily_has_finite_resolution (depth : Nat) :
    Nonempty
      ((finitePairFamily depth).ObservationalResolution
        (finiteObserver depth)) :=
  ((AlternativeFamily.ObservationalResolution.nonempty_iff_covered_and_invariant
    (finitePairFamily depth) (finiteObserver depth))).2
      ⟨finitePairFamily_covered depth,
        finitePairFamily_finite_invariant depth⟩

/-- The same pair admits no exact representative at the identity observer. -/
theorem finitePairFamily_has_no_identity_resolution (depth : Nat) :
    ¬ Nonempty
      ((finitePairFamily depth).ObservationalResolution
        (Observer.identity (Stream Bool))) := by
  intro resolution
  have coveredAndInvariant :=
    (AlternativeFamily.ObservationalResolution.nonempty_iff_covered_and_invariant
      (finitePairFamily depth) (Observer.identity (Stream Bool))).1 resolution
  exact finitePairFamily_not_identity_invariant depth coveredAndInvariant.2

/-- Paired selection canary: one and the same retained alternative family is
selectable at its finite observation and unselectable at exact identity. -/
theorem finite_selection_is_observer_relative (depth : Nat) :
    Nonempty
        ((finitePairFamily depth).ObservationalResolution
          (finiteObserver depth)) ∧
      ¬ Nonempty
        ((finitePairFamily depth).ObservationalResolution
          (Observer.identity (Stream Bool))) :=
  ⟨finitePairFamily_has_finite_resolution depth,
    finitePairFamily_has_no_identity_resolution depth⟩

/-! ## Axiom audit -/

#print axioms finiteObserver_postcompose
#print axioms overwritePreservesFinite
#print axioms overwrite_does_not_preserve_completeTower
#print axioms finitePairFamily_finite_invariant
#print axioms finitePairFamily_not_identity_invariant
#print axioms finitePairFamily_has_finite_resolution
#print axioms finitePairFamily_has_no_identity_resolution
#print axioms finite_selection_is_observer_relative

end Mettapedia.Coalgebra.FiniteViewObserver
