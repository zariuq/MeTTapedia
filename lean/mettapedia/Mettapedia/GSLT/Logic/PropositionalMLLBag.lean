import Mettapedia.GSLT.Logic.PropositionalMLL
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

/-!
# Multiset presentation of the existing MLL proof objects

`Provable` stores an actual proof of the existing list-sequent calculus and
its multiset presentation equality. All constructors below build those
existing proof objects, using its exchange rule. No new logical calculus or
proof acceptance condition is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.PropositionalMLL.Bag

def Provable (context : Multiset Formula) : Prop :=
  ∃ ordered : List Formula, (ordered : Multiset Formula) = context ∧ Nonempty (Derives ordered)

theorem ofProof {context : List Formula} (proof : Derives context) : Provable (context : Multiset Formula) :=
  ⟨context, rfl, ⟨proof⟩⟩

theorem cast {context other : Multiset Formula} (same : context = other) (proof : Provable context) : Provable other :=
  same ▸ proof

theorem represent {context : Multiset Formula} (proof : Provable context)
    (ordered : List Formula) (same : (ordered : Multiset Formula) = context) : Nonempty (Derives ordered) := by
  obtain ⟨source, presentation, ⟨actual⟩⟩ := proof
  exact ⟨.ex actual (Multiset.coe_eq_coe.mp (presentation.trans same.symm))⟩

private theorem head_presentation (head : Formula) (tail : Multiset Formula) :
    ((head :: tail.toList : List Formula) : Multiset Formula) = head ::ₘ tail := by
  change head ::ₘ (tail.toList : Multiset Formula) = _
  rw [Multiset.coe_toList]

private theorem two_heads_presentation (first second : Formula) (tail : Multiset Formula) :
    ((first :: second :: tail.toList : List Formula) : Multiset Formula) = first ::ₘ second ::ₘ tail := by
  change first ::ₘ second ::ₘ (tail.toList : Multiset Formula) = _
  rw [Multiset.coe_toList]

theorem atom (name : Nat) : Provable ({Formula.atom name, Formula.natom name} : Multiset Formula) :=
  ofProof (.ax name)

theorem identity (formula : Formula) : Provable ({formula, dual formula} : Multiset Formula) :=
  ofProof (PropositionalMLL.identity formula)

theorem one : Provable ({Formula.one} : Multiset Formula) := ofProof .one

theorem bot {context : Multiset Formula} (proof : Provable context) : Provable (Formula.bot ::ₘ context) := by
  obtain ⟨ordered, presentation, ⟨actual⟩⟩ := proof
  refine ⟨Formula.bot :: ordered, ?_, ⟨.bot actual⟩⟩
  exact congrArg (Multiset.cons Formula.bot) presentation

theorem tensor {left right : Formula} {first second : Multiset Formula}
    (leftProof : Provable (left ::ₘ first)) (rightProof : Provable (right ::ₘ second)) :
    Provable (Formula.tensor left right ::ₘ (first + second)) := by
  obtain ⟨leftActual⟩ := represent leftProof (left :: first.toList) (head_presentation _ _)
  obtain ⟨rightActual⟩ := represent rightProof (right :: second.toList) (head_presentation _ _)
  refine ⟨Formula.tensor left right :: (first.toList ++ second.toList), ?_, ⟨.tensor leftActual rightActual⟩⟩
  change Formula.tensor left right ::ₘ ((first.toList ++ second.toList : List Formula) : Multiset Formula) = _
  rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList]

theorem par {left right : Formula} {context : Multiset Formula}
    (proof : Provable (left ::ₘ right ::ₘ context)) : Provable (Formula.par left right ::ₘ context) := by
  obtain ⟨actual⟩ := represent proof (left :: right :: context.toList) (two_heads_presentation _ _ _)
  exact ⟨Formula.par left right :: context.toList, head_presentation _ _, ⟨.par actual⟩⟩

theorem cut {formula : Formula} {first second : Multiset Formula}
    (left : Provable (formula ::ₘ first)) (right : Provable (dual formula ::ₘ second)) : Provable (first + second) := by
  obtain ⟨leftActual⟩ := represent left (formula :: first.toList) (head_presentation _ _)
  obtain ⟨rightActual⟩ := represent right (dual formula :: second.toList) (head_presentation _ _)
  refine ⟨first.toList ++ second.toList, ?_, ⟨.cut leftActual rightActual⟩⟩
  rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList]

end Mettapedia.GSLT.Logic.PropositionalMLL.Bag
