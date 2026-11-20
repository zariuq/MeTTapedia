import Mettapedia.GSLT.Contracts.PaperRho
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence

/-!
# The literal-slot profile and the older Pattern equations

The translation is a plain readback of the independent source syntax:
it does not resolve names, execute drops, or use a target normalizer.
The existing Pattern equations contain the translated source equations,
but the converse is false even for closed subject spellings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho.PatternBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus (StructuralCongruence NameEquiv)

mutual
  def encodeName : Name → Pattern
    | .bound index => .bvar index
    | .quote code => .apply "NQuote" [encodeProcess code]
  def encodeProcess : Process → Pattern
    | .zero => .apply "PZero" []
    | .par left right => .collection .hashBag [encodeProcess left, encodeProcess right] none
    | .send name code => .apply "POutput" [encodeName name, encodeProcess code]
    | .receive name body => .apply "PInput" [encodeName name, .lambda none (encodeProcess body)]
    | .drop name => .apply "PDrop" [encodeName name]
end

private theorem pair_congr {a b c d : Pattern}
    (first : StructuralCongruence a b) (second : StructuralCongruence c d) :
    ∀ i h₁ h₂, StructuralCongruence ([a, c].get ⟨i, h₁⟩) ([b, d].get ⟨i, h₂⟩) := by
  intro i bounded _
  have below : i < 2 := by simpa using bounded
  have index : i = 0 ∨ i = 1 := by omega
  rcases index with rfl | rfl
  · exact first
  · exact second

theorem process_equations_preserved {p q : Process} (eq : ProcEq p q) :
    StructuralCongruence (encodeProcess p) (encodeProcess q) := by
  induction eq with
  | refl p => exact .refl _
  | symm _ ih => exact .symm _ _ ih
  | trans _ _ first second => exact .trans _ _ _ first second
  | unit p => exact .par_nil_right (encodeProcess p)
  | swap p q => exact .par_comm (encodeProcess p) (encodeProcess q)
  | assoc p q r => exact .par_assoc (encodeProcess p) (encodeProcess q) (encodeProcess r)
  | par _ _ first second => exact .par_cong _ _ rfl (pair_congr first second)
  | send name _ ih =>
      exact .apply_cong "POutput" _ _ rfl (pair_congr (.refl (encodeName name)) ih)
  | receive name _ ih =>
      exact .apply_cong "PInput" _ _ rfl
        (pair_congr (.refl (encodeName name)) (.lambda_cong none _ _ ih))

theorem name_equations_preserved {x y : Name} (eq : NameEq x y) :
    NameEquiv (encodeName x) (encodeName y) := by
  induction eq with
  | refl x => exact .refl _
  | symm _ ih => exact .symm _ _ ih
  | trans _ _ first second => exact .trans _ _ _ first second
  | quote_drop x => exact .quote_drop (encodeName x)
  | quote eq => exact .struct_equiv _ _ (process_equations_preserved eq)

open Separation (base wrapped alias_separation)

private theorem promoted_subject :
    StructuralCongruence (encodeProcess (.send wrapped .zero)) (encodeProcess (.send base .zero)) :=
  .apply_cong "POutput" _ _ rfl
    (pair_congr (.quote_drop (encodeName base)) (.refl _))

/-- A checked obstruction to using the old process relation as the
reference, even when both source processes are closed. -/
theorem process_equations_not_reflected :
    ScopedProcess 0 (.send wrapped .zero) ∧ ScopedProcess 0 (.send base .zero) ∧
      StructuralCongruence (encodeProcess (.send wrapped .zero)) (encodeProcess (.send base .zero)) ∧
      ¬ ProcEq (.send wrapped .zero) (.send base .zero) :=
  ⟨.send (.literal (.drop (.literal .zero))) .zero, .send (.literal .zero) .zero,
    promoted_subject, alias_separation.2.1⟩

/-- The discrepancy survives quotation. It can affect equality of a
channel itself, so it is stronger than a difference in display syntax. -/
theorem name_equations_not_reflected :
    NameEquiv (encodeName (.quote (.send wrapped .zero))) (encodeName (.quote (.send base .zero))) ∧
      ¬ NameEq (.quote (.send wrapped .zero)) (.quote (.send base .zero)) :=
  ⟨.struct_equiv _ _ promoted_subject, alias_separation.2.2⟩

#print axioms process_equations_preserved
#print axioms name_equations_preserved
#print axioms process_equations_not_reflected
#print axioms name_equations_not_reflected

end Mettapedia.GSLT.Contracts.PaperRho.PatternBoundary
