import Mettapedia.Logic.HOL.TermModel.Denote

/-!
# The canonical term `PreModel`

Packaging the denotation/realization data into the existing `PreModel` interface:
base-type carriers are the closed-term quotients, admissibility is representability,
constants denote via `tval`.  Every base/prop element is admissible; admissibility is
closed under application; constants are admissible by `rep_tval`.
-/

namespace Mettapedia.Logic.HOL
namespace ClosedTheorySet

open Mettapedia.Logic.HOL.WithParams
open scoped Classical

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- The canonical general model as a `PreModel`: term-quotient carriers, representability
admissibility, `tval` constant denotations. -/
noncomputable def termPreModel (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier) :
    PreModel Base (WithParams Const) where
  Carrier := termCarrier M
  adm := admissible M
  base_mem := fun b x => ⟨Quotient.out x.down, by
    show x = (ULift.up (TermDom.mk M (Quotient.out x.down)) : termCarrier M b)
    rw [show TermDom.mk M (Quotient.out x.down) = x.down from Quotient.out_eq x.down]⟩
  prop_mem := fun p => by
    by_cases hp : p.down
    · exact ⟨.top, iff_of_true hp World.top_mem⟩
    · exact ⟨.bot, iff_of_false hp World.bot_not_mem⟩
  app_mem := fun {σ τ f x} hf hx => by
    obtain ⟨tf, hf'⟩ := hf
    obtain ⟨tx, hx'⟩ := hx
    exact ⟨.app tf tx, hf' x tx hx'⟩
  constDen := fun {τ} c => tval M τ (.const c)
  const_mem := fun {τ} c => ⟨.const c, rep_tval M hC (.const c)⟩

@[simp] theorem termPreModel_Carrier (M : World (WithParams Const)) (hC) :
    (termPreModel M hC).Carrier = termCarrier M := rfl

@[simp] theorem termPreModel_adm (M : World (WithParams Const)) (hC) :
    (termPreModel M hC).adm = admissible M := rfl

@[simp] theorem termPreModel_constDen (M : World (WithParams Const)) (hC)
    {τ : Ty Base} (c : WithParams Const τ) :
    (termPreModel M hC).constDen c = tval M τ (.const c) := rfl

end ClosedTheorySet
end Mettapedia.Logic.HOL
