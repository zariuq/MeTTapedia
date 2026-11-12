import Mathlib.Algebra.FreeMonoid.Basic
import Mettapedia.Logic.LinearLogic.KnowledgeTensorControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Traces

/-!
# Controls for proof-relevant initiality

Two declarations with the same effect, `left` and `right`: each takes `a` and makes `b`.

* `twins_two_runs`: **a sequent with two witnessed runs**. From `a` to `b` there are two, and they
  differ.
* `twins_separated`: the unique map into the free monoid of weights separates them
  (`weights_unique`), so the proof-relevant initial model keeps them apart.
* `reachability_model`, `twins_identified`: the relation "some run joins the two states" is a
  relational model in the sense of `KnowledgeTensorInitial`, and it holds of the two runs alike:
  the relational initiality cannot say which run took place.
* `twins_swap_respected`: a commutative monoid of weights respects every swap of the twins, so by
  `interp_cell` it is constant along every interchange cell.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.InitialControls

open Mettapedia.Logic.LinearLogic.KnowledgeTensor
open Mettapedia.Logic.LinearLogic.KnowledgeTensorControls (Item Knowledge)
open Mettapedia.Logic.LinearLogic.KnowledgeTensorControls.Item

/-- Two declarations with the same effect. -/
inductive Twin where
  | left | right
  deriving DecidableEq

open Twin

/-- Both take `a` and make `b`; nothing is read, told or asked. -/
def twins : System Knowledge Item Twin where
  take := fun _ => {a}
  read := fun _ => 0
  make := fun _ => {b}
  tell := fun _ => Set.univ
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro

theorem twin_runs (which : Twin) :
    twins.Run Set.univ {a} [which] (Set.univ ⊓ Set.univ) {b} :=
  System.Run.fire ⟨0, by simp [System.premises, twins], True.intro, rfl,
    by simp [System.conclusions, twins]⟩ (System.Run.done _ _)

/-- The witnessed run of one twin. -/
def twinPath (which : Twin) : Path twins Set.univ {a} (Set.univ ⊓ Set.univ) {b} :=
  Path.ofRun [which] (twin_runs which)

theorem twinPath_uses (which : Twin) : (twinPath which).uses = [which] :=
  Path.uses_ofRun _ _

/-- **A sequent with two witnessed runs.** -/
theorem twins_two_runs : twinPath left ≠ twinPath right := by
  intro same
  have words := congrArg Path.uses same
  rw [twinPath_uses, twinPath_uses] at words
  exact absurd words (by decide)

/-- **The unique map into the free monoid of weights separates them.** -/
theorem twins_separated
    (F : ModelMap (paths twins) (weights (sys := twins) (FreeMonoid Twin) FreeMonoid.of)) :
    F.map (twinPath left) ≠ F.map (twinPath right) := by
  rw [weights_unique, weights_unique, twinPath_uses, twinPath_uses]
  intro same
  have lists := congrArg FreeMonoid.toList same
  simp at lists

/-- Reachability is a relational model. -/
theorem reachability_model :
    twins.Model (fun k Γ _ k' Γ' => ∃ uses : List Twin, twins.Run k Γ uses k' Γ') where
  identity k Γ := ⟨[], System.Run.done k Γ⟩
  rule declaration k asked := ⟨[declaration], System.Derives.run (System.Derives.rule declaration k asked)⟩
  frame extra := fun ⟨uses, run⟩ => ⟨uses, System.Run.frame extra run⟩
  strengthen more := fun ⟨uses, run⟩ => ⟨uses, System.Run.strengthen more run⟩
  cut := fun ⟨first, one⟩ ⟨second, two⟩ => ⟨first ++ second, System.Run.append one two⟩

/-- **The relational model holds of the two runs alike**: holding there says only that some run
joins the two states. -/
theorem twins_identified (which : Twin) :
    (fun k Γ (_ : List Twin) k' Γ' => ∃ uses : List Twin, twins.Run k Γ uses k' Γ')
        Set.univ {a} [which] (Set.univ ⊓ Set.univ) {b} ↔
      (fun k Γ (_ : List Twin) k' Γ' => ∃ uses : List Twin, twins.Run k Γ uses k' Γ')
        Set.univ {a} [left] (Set.univ ⊓ Set.univ) {b} :=
  Iff.rfl

/-- **A commutative monoid of weights respects every swap of the twins.** -/
theorem twins_swap_respected (weight : Twin → Nat) :
    RespectsSwaps (weights (sys := twins) Nat weight) :=
  weights_respectSwaps weight

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.InitialControls
