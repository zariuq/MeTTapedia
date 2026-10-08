import Mettapedia.GSLT.Topos.PresheafPredicateTotalExponential

/-!
# Function-object reification of predicate transformers

Curried evaluation sends a predicate on the function object to a *transformer*
of predicates: from a set of functions and a set of arguments it produces the
set of results obtainable by applying one to the other.  Reification is its
right adjoint, taking a transformer back to a predicate on the function
object.

* `applyPred Θ α` — curried evaluation, the direct image along evaluation of
  "the argument satisfies `α` and the function satisfies `Θ`";
* `reifyPred T` — reification, the meet over all argument predicates of the
  exponential-style predicate for `α` and `T α`;
* `reify_adjunction` — the adjunction, as a biconditional;
* `reifyPred_unique` — anything satisfying that biconditional is `reifyPred`,
  so this is an adjunction rather than a bound that happens to hold.

The transformer argument is an arbitrary function `Subfunctor a → Subfunctor b`.
Monotonicity is never used, so it is not assumed; `applyPred_mono_arg` records
that the evaluation side is monotone regardless.

Unit and counit are derived from the biconditional rather than proved
separately, so they cannot drift apart from it.

## References

- Williams & Stay, "Native Type Theory" (ACT 2021), Prop 17.
- Jacobs, "Categorical Logic and Type Theory" (1999), Ch. 1 (direct image and
  reindexing as an adjoint pair) and Ch. 5.
-/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

variable {C : Type u} [Category.{u} C] (a b : PresheafPredicateTotal C)

/-! ## Curried evaluation -/

/-- Curried evaluation on predicates: the results obtainable by applying a
function satisfying `Θ` to an argument satisfying `α`. -/
noncomputable def applyPred (Θ : Subfunctor (expBase a b))
    (α : Subfunctor a.base) : Subfunctor b.base :=
  (α.preimage (fst a.base (expBase a b)) ⊓
    Θ.preimage (snd a.base (expBase a b))).image (expEval a b)

/-- One-argument adjointness: the chain every later result factors through. -/
theorem applyPred_le_iff (Θ : Subfunctor (expBase a b))
    (α : Subfunctor a.base) (β : Subfunctor b.base) :
    applyPred a b Θ α ≤ β ↔
      Θ ≤ forallAlong (snd a.base (expBase a b))
        (α.preimage (fst a.base (expBase a b)) ⇨
          β.preimage (expEval a b)) := by
  rw [applyPred, Subfunctor.image_le_iff, ← preimage_le_iff_le_forallAlong,
    le_himp_iff, inf_comm]

theorem applyPred_mono_arg (Θ : Subfunctor (expBase a b)) :
    Monotone (applyPred a b Θ) := by
  intro α α' below U value member
  obtain ⟨source, held, image⟩ := member
  exact ⟨source, ⟨below U held.1, held.2⟩, image⟩

/-- Nothing is produced from no arguments. -/
@[simp] theorem applyPred_bot (Θ : Subfunctor (expBase a b)) :
    applyPred a b Θ ⊥ = ⊥ := by
  rw [applyPred]
  refine le_antisymm ?_ bot_le
  rw [Subfunctor.image_le_iff]
  intro U value member
  exact member.1.elim

/-! ## Reification -/

/-- Reification of a predicate transformer: a function satisfies it when, for
every argument predicate, it carries that predicate into the transformer's
value on it. -/
noncomputable def reifyPred
    (T : Subfunctor a.base → Subfunctor b.base) : Subfunctor (expBase a b) :=
  ⨅ α : Subfunctor a.base,
    forallAlong (snd a.base (expBase a b))
      (α.preimage (fst a.base (expBase a b)) ⇨ (T α).preimage (expEval a b))

/-- **The adjunction.** Curried evaluation is left adjoint to reification,
with the transformer order taken pointwise. -/
theorem reify_adjunction (Θ : Subfunctor (expBase a b))
    (T : Subfunctor a.base → Subfunctor b.base) :
    (∀ α, applyPred a b Θ α ≤ T α) ↔ Θ ≤ reifyPred a b T := by
  constructor
  · intro holds
    refine le_iInf ?_
    intro α
    exact (applyPred_le_iff a b Θ α (T α)).mp (holds α)
  · intro below α
    refine (applyPred_le_iff a b Θ α (T α)).mpr ?_
    exact le_trans below (iInf_le _ α)

/-- Counit: applying a reified transformer never exceeds it. -/
theorem applyPred_reifyPred_le
    (T : Subfunctor a.base → Subfunctor b.base) (α : Subfunctor a.base) :
    applyPred a b (reifyPred a b T) α ≤ T α :=
  (reify_adjunction a b (reifyPred a b T) T).mpr (le_refl _) α

/-- Unit: every predicate on the function object is below the reification of
its own evaluation transformer. -/
theorem le_reifyPred_applyPred (Θ : Subfunctor (expBase a b)) :
    Θ ≤ reifyPred a b (applyPred a b Θ) :=
  (reify_adjunction a b Θ (applyPred a b Θ)).mp (fun _ => le_refl _)

theorem reifyPred_mono
    {T T' : Subfunctor a.base → Subfunctor b.base}
    (below : ∀ α, T α ≤ T' α) : reifyPred a b T ≤ reifyPred a b T' :=
  (reify_adjunction a b (reifyPred a b T) T').mp
    (fun α => le_trans (applyPred_reifyPred_le a b T α) (below α))

/-- Reification is determined by the adjunction: any operation satisfying the
same biconditional is this one.  So this is an adjoint, not a bound that
happens to hold. -/
theorem reifyPred_unique
    (R : (Subfunctor a.base → Subfunctor b.base) → Subfunctor (expBase a b))
    (adjoint : ∀ Θ T, (∀ α, applyPred a b Θ α ≤ T α) ↔ Θ ≤ R T)
    (T : Subfunctor a.base → Subfunctor b.base) :
    R T = reifyPred a b T := by
  refine le_antisymm ?_ ?_
  · exact (reify_adjunction a b (R T) T).mp ((adjoint (R T) T).mpr (le_refl _))
  · exact (adjoint (reifyPred a b T) T).mp (applyPred_reifyPred_le a b T)

/-! ## Comparison with the exponential predicate -/

/-- The exponential predicate is the component of reification at the source
object's own predicate: reification is below it whenever the transformer
agrees there. -/
theorem reifyPred_le_expPredicate
    (T : Subfunctor a.base → Subfunctor b.base)
    (agrees : T (objectPredicate a) = objectPredicate b) :
    reifyPred a b T ≤ expPredicate a b := by
  have component := iInf_le
    (fun α : Subfunctor a.base =>
      forallAlong (snd a.base (expBase a b))
        (α.preimage (fst a.base (expBase a b)) ⇨
          (T α).preimage (expEval a b)))
    (objectPredicate a)
  rw [expPredicate, ← agrees]
  exact component

/-- Conversely the exponential predicate is exactly the one-component
statement, so the two constructions agree on that component. -/
theorem expPredicate_eq_component :
    expPredicate a b =
      forallAlong (snd a.base (expBase a b))
        ((objectPredicate a).preimage (fst a.base (expBase a b)) ⇨
          (objectPredicate b).preimage (expEval a b)) := rfl

/-! ## Controls -/

/-- The transformer that is everywhere the top predicate reifies to the top
predicate: reification is not constantly small. -/
@[simp] theorem reifyPred_top :
    reifyPred a b (fun _ => (⊤ : Subfunctor b.base)) = ⊤ :=
  le_antisymm le_top
    ((reify_adjunction a b ⊤ (fun _ => ⊤)).mp (fun _ => le_top))

end Mettapedia.GSLT.Topos

#print axioms Mettapedia.GSLT.Topos.applyPred_le_iff
#print axioms Mettapedia.GSLT.Topos.applyPred_mono_arg
#print axioms Mettapedia.GSLT.Topos.applyPred_bot
#print axioms Mettapedia.GSLT.Topos.reify_adjunction
#print axioms Mettapedia.GSLT.Topos.applyPred_reifyPred_le
#print axioms Mettapedia.GSLT.Topos.le_reifyPred_applyPred
#print axioms Mettapedia.GSLT.Topos.reifyPred_mono
#print axioms Mettapedia.GSLT.Topos.reifyPred_unique
#print axioms Mettapedia.GSLT.Topos.reifyPred_le_expPredicate
#print axioms Mettapedia.GSLT.Topos.reifyPred_top
