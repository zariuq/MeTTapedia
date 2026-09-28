import Mettapedia.OSLF.Syntax.FiniteRulePremiseLists

/-!
# Evidence at every ordered premise

These constructors supply the dependent function expected by the finite rule
polynomial. They retain the list address even when two premises have the same
judgment. No witness is selected from a proposition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRulePremiseLists

universe u v

variable {J : Type u} (D : J → Type v)

abbrev Evidence (premises : List J) :=
  (position : Fin premises.length) → D (premises.get position)

def noEvidence : Evidence D [] := fun position => Fin.elim0 position

def consEvidence {head : J} {tail : List J} (first : D head)
    (rest : Evidence D tail) : Evidence D (head :: tail) :=
  Fin.cases first rest

@[simp] theorem consEvidence_zero {head : J} {tail : List J} (first : D head)
    (rest : Evidence D tail) : consEvidence D first rest 0 = first := rfl

@[simp] theorem consEvidence_succ {head : J} {tail : List J} (first : D head)
    (rest : Evidence D tail) (position : Fin tail.length) :
    consEvidence D first rest position.succ = rest position := rfl

/-- Decomposing and reassembling premise evidence recovers the whole function. -/
theorem consEvidence_eta {head : J} {tail : List J}
    (evidence : Evidence D (head :: tail)) :
    consEvidence D (evidence 0) (fun position => evidence position.succ) = evidence := by
  funext position
  exact Fin.cases rfl (fun _ => rfl) position

end Mettapedia.OSLF.Binding.FiniteRulePremiseLists
