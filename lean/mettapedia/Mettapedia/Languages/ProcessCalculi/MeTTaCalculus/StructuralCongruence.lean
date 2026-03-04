import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Syntax

/-!
# MeTTa-Calculus Structural Congruence

Structural congruence layer for MeTTa-calculus process terms, focused on
parallel-bag algebra and the inactive process law.

## Source attribution

Aligned with the structural `equiv` clauses in:

- `/home/zar/claude/hyperon/rho4u/metta-calculus/metta-calculus.core.tex`

including:

- `P | 0 ≡ P`
- commutativity/associativity of parallel composition.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Structural congruence for MeTTa-calculus processes. -/
inductive SC : Proc → Proc → Prop where
  | refl (p : Proc) : SC p p
  | symm (p q : Proc) : SC p q → SC q p
  | trans (p q r : Proc) : SC p q → SC q r → SC p r
  | alpha (p q : Proc) : p = q → SC p q
  | par_singleton (p : Proc) :
      SC (.collection .hashBag [p] none) p
  | par_nil_left (p : Proc) :
      SC (.collection .hashBag [.apply "MZero" [], p] none) p
  | par_nil_right (p : Proc) :
      SC (.collection .hashBag [p, .apply "MZero" []] none) p
  | par_comm (p q : Proc) :
      SC (.collection .hashBag [p, q] none)
         (.collection .hashBag [q, p] none)
  | par_assoc (p q r : Proc) :
      SC (.collection .hashBag [.collection .hashBag [p, q] none, r] none)
         (.collection .hashBag [p, .collection .hashBag [q, r] none] none)
  | par_perm (xs ys : List Proc) :
      xs.Perm ys →
      SC (.collection .hashBag xs none) (.collection .hashBag ys none)
  | par_cong (xs ys : List Proc) :
      xs.length = ys.length →
      (∀ i hx hy, SC (xs.get ⟨i, hx⟩) (ys.get ⟨i, hy⟩)) →
      SC (.collection .hashBag xs none) (.collection .hashBag ys none)

notation:50 p " ≈ₘ " q => SC p q

theorem SC_equivalence : Equivalence SC where
  refl := SC.refl
  symm := SC.symm _ _
  trans := SC.trans _ _ _

theorem nil_left (p : Proc) : pPar [pZero, p] ≈ₘ p := SC.par_nil_left p

theorem nil_right (p : Proc) : pPar [p, pZero] ≈ₘ p := SC.par_nil_right p

theorem comm (p q : Proc) : pPar [p, q] ≈ₘ pPar [q, p] := SC.par_comm p q

theorem assoc (p q r : Proc) :
    pPar [pPar [p, q], r] ≈ₘ pPar [p, pPar [q, r]] := SC.par_assoc p q r

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
