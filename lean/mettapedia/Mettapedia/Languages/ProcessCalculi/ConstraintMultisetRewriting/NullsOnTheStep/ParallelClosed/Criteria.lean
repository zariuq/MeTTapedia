import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Separation

/-!
# A context per operator: what the separation needs from the target's parallel context

A translation **compositional with a context per operator** for parallel composition
(`CompositionalTranslation`) sends `s ∥ s'` to `C∥[image s, image s']` for one fixed target context
`C∥`, up to the static equivalence. The uniform criterion is the case `C∥ = ∥`
(`UniformTranslation.toCompositional`).

`no_compositionalTranslation`: the separation holds for every compositional translation whose
context **keeps reachable success of its first hole** (`KeepsFirst`). Parallel composition keeps it
in a persistent calculus (`keepsFirst_par`). So the lemma a context-per-operator criterion needs
about the target is `KeepsFirst` for the context the translation chooses. It fails for a context
that guards its hole: `Controls.guarded_context`, on bags, puts its first hole beside a token the
target never makes and keeps it only when the token is there.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed

universe u v

/-- **A translation compositional with a context per operator**, for parallel composition: the image
of a composite is, up to the target's static equivalence, the context filled with the images of the
parts; reachable success is preserved and reflected. -/
structure CompositionalTranslation (L : ParallelCalculus.{u}) (M : ParallelCalculus.{v}) where
  map : L.Term → M.Term
  context : M.Term → M.Term → M.Term
  compositional : ∀ s s', L.composable s s' →
    M.same (map (L.par s s')) (context (map s) (map s'))
  preserves : ∀ s, L.Succeeds s → M.Succeeds (map s)
  reflects : ∀ s, M.Succeeds (map s) → L.Succeeds s

/-- A target context **keeps reachable success of its first hole**. -/
def KeepsFirst (M : ParallelCalculus.{v}) (context : M.Term → M.Term → M.Term) : Prop :=
  ∀ t u, M.Succeeds t → M.Succeeds (context t u)

/-- A uniform translation is compositional with parallel composition as its context. -/
def UniformTranslation.toCompositional {L : ParallelCalculus.{u}} {M : ParallelCalculus.{v}}
    (τ : UniformTranslation L M) : CompositionalTranslation L M where
  map := τ.map
  context := M.par
  compositional := τ.homomorphic
  preserves := τ.preserves
  reflects := τ.reflects

/-- In a persistent calculus, parallel composition keeps reachable success of its first hole. -/
theorem keepsFirst_par {M : ParallelCalculus.{v}} (persistent : M.Persistent) :
    KeepsFirst M M.par :=
  fun _ u succeeds => persistent.succeeds_par u succeeds

/-- **The separation for compositional translations whose context keeps its first hole.** -/
theorem no_compositionalTranslation {L : ParallelCalculus.{u}} {M : ParallelCalculus.{v}}
    (switchable : L.Switchable)
    (respects : ∀ t t', M.same t t' → M.Succeeds t' → M.Succeeds t)
    (τ : CompositionalTranslation L M) (keeps : KeepsFirst M τ.context) : False := by
  obtain ⟨s, s', composable, succeeds, blocked⟩ := switchable
  exact blocked (τ.reflects _ (respects _ _ (τ.compositional s s' composable)
    (keeps _ (τ.map s') (τ.preserves s succeeds))))

/-- **`no_uniformTranslation` is the case of parallel composition as the context.** -/
theorem no_uniformTranslation_via_context {L : ParallelCalculus.{u}} {M : ParallelCalculus.{v}}
    (switchable : L.Switchable) (persistent : M.Persistent) (τ : UniformTranslation L M) : False :=
  no_compositionalTranslation switchable persistent.respects τ.toCompositional
    (keepsFirst_par persistent)

namespace Controls

open NamesOnTheStep NamesOnTheStep.IssuingControls

/-- **A guarded context**: the first hole counts only beside the token `W`, which no rule of the
inert bag calculus makes. -/
noncomputable def guardedContext (x y : Multiset Expr) : Multiset Expr := by
  classical
  exact if factW ∈ y then x + y else y

/-- **The guarded context does not keep its first hole.** In the inert bag calculus, `T` succeeds,
and the context with `T` in its first hole and nothing in its second shows no `T`. -/
theorem guarded_context :
    ¬ KeepsFirst (bagCalculus fun _ => False) guardedContext := by
  intro keeps
  have shows := (inert_succeeds_iff _).mp
    (keeps ({factT} : Multiset Expr) (0 : Multiset Expr)
      ((inert_succeeds_iff _).mpr (Multiset.mem_singleton_self _)))
  simp [guardedContext] at shows

end Controls

#print axioms no_compositionalTranslation
#print axioms keepsFirst_par
#print axioms no_uniformTranslation_via_context
#print axioms Controls.guarded_context

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
