import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Independent capabilities of Tarski universe families

A family of Tarski codes does not by itself determine cumulativity, closure
under type formers, or whether a universe contains a code for its own code
type.  This module separates those properties before any concrete dependent
calculus or set-theoretic model is selected.

The finite-rank control has codes `Fin n` at level `n`; a code of rank `k`
decodes to `Fin k`.  It is strictly cumulative and no level codes its own code
type, but it is not closed under dependent products.  A second one-level
control codes itself and is closed under dependent products and sums.  A
third control is closed under dependent products at every level but cannot be
cumulative along its declared level edge.

These are small independence models, not proposed universes for a production
type theory.  Their role is to prevent a working contextual universe
formation from silently installing unrelated hierarchy policies.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.TarskiUniverseCapabilities

universe uLevel uCode uEl

/-- Level-indexed Tarski codes and their decoded types.  No order, lift, or
closure operation is included. -/
structure TarskiCodeFamily where
  Level : Type uLevel
  Code : Level → Type uCode
  El : (level : Level) → Code level → Type uEl

namespace TarskiCodeFamily

variable (family : TarskiCodeFamily.{uLevel, uCode, uEl})

/-- Cumulativity along a separately supplied strict level relation.  A lifted
code decodes to a type equivalent to the original decoded type. -/
structure Cumulative (Below : family.Level → family.Level → Prop) where
  lift : ∀ {lower upper}, Below lower upper →
    family.Code lower → family.Code upper
  decodeLift : ∀ {lower upper} (below : Below lower upper)
    (code : family.Code lower),
    family.El upper (lift below code) ≃ family.El lower code

/-- One level is closed under dependent products when every decoded domain
and decoded codomain family has a code at that same level. -/
def PiClosedAt (level : family.Level) : Prop :=
  ∀ (domain : family.Code level)
    (codomain : family.El level domain → family.Code level),
    ∃ product : family.Code level,
      Nonempty
        (family.El level product ≃
          ((argument : family.El level domain) →
            family.El level (codomain argument)))

/-- One level is closed under dependent sums. -/
def SigmaClosedAt (level : family.Level) : Prop :=
  ∀ (domain : family.Code level)
    (codomain : family.El level domain → family.Code level),
    ∃ sum : family.Code level,
      Nonempty
        (family.El level sum ≃
          (Σ argument : family.El level domain,
            family.El level (codomain argument)))

/-- Every level has dependent-product closure. -/
def PiClosed : Prop := ∀ level, family.PiClosedAt level

/-- Every level has dependent-sum closure. -/
def SigmaClosed : Prop := ∀ level, family.SigmaClosedAt level

/-- A precise semantic self-code property at one level.  It says that some
decoded code is equivalent to the level's code carrier.  It is not conflated
with a syntactic `U : U` judgment or its conversion rules. -/
def CodesItselfAt (level : family.Level) : Prop :=
  ∃ code : family.Code level,
    Nonempty (family.El level code ≃ family.Code level)

/-- No level contains such a self-code. -/
def PredicativeRanks : Prop :=
  ∀ level, ¬ family.CodesItselfAt level

end TarskiCodeFamily

/-! ## A strictly cumulative finite-rank family -/

namespace FiniteRank

/-- At level `n`, codes have ranks strictly below `n`; rank `k` decodes to
the finite type `Fin k`. -/
abbrev family : TarskiCodeFamily.{0, 0, 0} where
  Level := Nat
  Code := Fin
  El := fun _level code => Fin code.val

/-- Strict level comparison. -/
def Below (lower upper : family.Level) : Prop := lower < upper

/-- Finite-rank codes lift strictly while retaining their rank. -/
def cumulative : family.Cumulative Below where
  lift := fun {lower upper} below code =>
    ⟨code.val, Nat.lt_trans code.isLt below⟩
  decodeLift := by
    intro lower upper below code
    exact Equiv.refl (Fin code.val)

/-- The finite-rank family is genuinely cumulative: a rank-one code at level
two lifts to the same rank at level three. -/
example :
    cumulative.lift (show Below 2 3 by simp [Below])
        (⟨1, by omega⟩ : Fin 2) =
      (⟨1, by omega⟩ : Fin 3) :=
  rfl

/-- No finite-rank level codes its own code carrier. -/
theorem predicativeRanks : family.PredicativeRanks := by
  intro level selfCode
  rcases selfCode with ⟨code, ⟨equivalence⟩⟩
  have equalCardinality := Fintype.card_congr equivalence
  simp only [family, Fintype.card_fin] at equalCardinality
  exact (Nat.ne_of_lt code.isLt) equalCardinality

/-- Level three contains a code for `Fin 2`, but it has no code for the
dependent function space `Fin 2 → Fin 2`, whose cardinality is four.  Thus
cumulativity does not imply dependent-product closure. -/
theorem not_piClosedAt_three : ¬ family.PiClosedAt 3 := by
  intro closed
  let boolCode : family.Code 3 := ⟨2, by omega⟩
  obtain ⟨product, ⟨equivalence⟩⟩ :=
    closed boolCode (fun _ => boolCode)
  have equalCardinality := Fintype.card_congr equivalence
  have productCardinality : product.val = 4 := by
    simpa [family, boolCode] using equalCardinality
  have productBelowLevel : product.val < 3 := product.isLt
  omega

theorem cumulative_does_not_imply_piClosure :
    Nonempty (family.Cumulative Below) ∧ ¬ family.PiClosedAt 3 :=
  ⟨⟨cumulative⟩, not_piClosedAt_three⟩

end FiniteRank

/-! ## A one-level self-coding closed family -/

namespace UnitClosed

/-- The unique code decodes to the unique type. -/
abbrev family : TarskiCodeFamily.{0, 0, 0} where
  Level := PUnit
  Code := fun _ => PUnit
  El := fun _ _ => PUnit

def functionEquiv : PUnit ≃ (PUnit → PUnit) where
  toFun := fun _ _ => PUnit.unit
  invFun := fun _ => PUnit.unit
  left_inv := by intro value; exact Subsingleton.elim _ _
  right_inv := by
    intro function
    funext argument
    exact Subsingleton.elim _ _

def sigmaEquiv : PUnit ≃ (Σ _ : PUnit, PUnit) where
  toFun := fun _ => ⟨PUnit.unit, PUnit.unit⟩
  invFun := fun _ => PUnit.unit
  left_inv := by intro value; exact Subsingleton.elim _ _
  right_inv := by
    intro value
    obtain ⟨index, payload⟩ := value
    cases index
    cases payload
    rfl

theorem piClosed : family.PiClosed := by
  intro level domain codomain
  exact ⟨PUnit.unit, ⟨functionEquiv⟩⟩

theorem sigmaClosed : family.SigmaClosed := by
  intro level domain codomain
  exact ⟨PUnit.unit, ⟨sigmaEquiv⟩⟩

theorem codesItself : family.CodesItselfAt PUnit.unit :=
  ⟨PUnit.unit, ⟨Equiv.refl PUnit⟩⟩

/-- Closure under products and sums does not by itself enforce predicative
ranks. -/
theorem closure_does_not_imply_predicativeRanks :
    family.PiClosed ∧ family.SigmaClosed ∧ ¬ family.PredicativeRanks := by
  refine ⟨piClosed, sigmaClosed, ?_⟩
  intro predicative
  exact predicative PUnit.unit codesItself

end UnitClosed

/-! ## Product closure without cumulativity -/

namespace NonCumulative

/-- The lower level has one unit code; the upper level has no codes. -/
abbrev family : TarskiCodeFamily.{0, 0, 0} where
  Level := Bool
  Code := fun level => if level then Empty else PUnit
  El := fun level => by
    cases level <;> simp
    · exact fun _ => PUnit
    · exact fun code => code.elim

/-- The declared hierarchy contains one edge from the inhabited lower code
level to the empty upper code level. -/
def Below (lower upper : Bool) : Prop := lower = false ∧ upper = true

theorem piClosed : family.PiClosed := by
  intro level
  cases level with
  | false =>
      intro domain codomain
      exact ⟨PUnit.unit, ⟨UnitClosed.functionEquiv⟩⟩
  | true =>
      intro domain
      exact domain.elim

/-- No cumulative lift can cross the declared edge, because it would have to
map the lower unit code into the empty upper code carrier. -/
theorem not_cumulative : ¬ Nonempty (family.Cumulative Below) := by
  rintro ⟨cumulative⟩
  have below : Below false true := ⟨rfl, rfl⟩
  exact (cumulative.lift below PUnit.unit).elim

/-- Dependent-product closure and cumulativity are independent capabilities. -/
theorem piClosure_does_not_imply_cumulativity :
    family.PiClosed ∧ ¬ Nonempty (family.Cumulative Below) :=
  ⟨piClosed, not_cumulative⟩

end NonCumulative

/-! ## Independence summary -/

/-- Cumulativity, dependent-product closure, and semantic self-coding cannot
be inferred from one another. -/
theorem universe_capabilities_are_independent :
    (Nonempty (FiniteRank.family.Cumulative FiniteRank.Below) ∧
      ¬ FiniteRank.family.PiClosedAt 3) ∧
    (UnitClosed.family.PiClosed ∧ UnitClosed.family.SigmaClosed ∧
      ¬ UnitClosed.family.PredicativeRanks) ∧
    (NonCumulative.family.PiClosed ∧
      ¬ Nonempty
        (NonCumulative.family.Cumulative NonCumulative.Below)) :=
  ⟨FiniteRank.cumulative_does_not_imply_piClosure,
    UnitClosed.closure_does_not_imply_predicativeRanks,
    NonCumulative.piClosure_does_not_imply_cumulativity⟩

#print axioms FiniteRank.predicativeRanks
#print axioms FiniteRank.not_piClosedAt_three
#print axioms FiniteRank.cumulative_does_not_imply_piClosure
#print axioms UnitClosed.piClosed
#print axioms UnitClosed.sigmaClosed
#print axioms UnitClosed.closure_does_not_imply_predicativeRanks
#print axioms NonCumulative.piClosed
#print axioms NonCumulative.not_cumulative
#print axioms NonCumulative.piClosure_does_not_imply_cumulativity
#print axioms universe_capabilities_are_independent

end Mettapedia.TypeTheory.TarskiUniverseCapabilities
