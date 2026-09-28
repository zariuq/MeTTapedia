import Mettapedia.Languages.Agda.Structural.Presentation
import Mettapedia.Languages.Agda.Structural.RootCorrespondence

/-!
# Completeness of the structural computation presentation

Compatible derivations are encoded in the actual authored rule table. Root
constructors use their six declared addresses. A congruence records the
operator's declared argument position and the result produced by its child.
All address lookup is constructive and preserves the selected occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

namespace Authored

/-- A selected declaration address, with its exact dependent telescope. -/
structure Address (r : LocalRule sig) where
  index : Fin computationRules.length
  selected : computationRules.get index = r

def rootAddress (index : Fin roots.length) : Address (roots.get index) where
  index := ⟨index.val, by
    have bound := index.isLt
    change index.val < roots.length + generatedCongruences.length
    omega⟩
  selected := by simp only [computationRules, List.get_eq_getElem, List.getElem_append_left index.isLt]

private def offsetIndex {size : Nat} (offset : Nat) (bound : offset + size ≤ 29)
    (position : Fin size) : Fin computationRules.length :=
  ⟨offset + position.val, by
    change offset + position.val < 29
    have position_bound := position.isLt
    omega⟩

/-- Concrete lookup into the generated declaration blocks. -/
def congruenceIndex : {s : Srt} → (op : Op s) →
    Fin (sig.arity op).length → Fin computationRules.length
  | _, .lam, position => offsetIndex 6 (by decide) position
  | _, .lamNoAbs, position => offsetIndex 7 (by decide) position
  | _, .pi, position => offsetIndex 8 (by decide) position
  | _, .piNoAbs, position => offsetIndex 10 (by decide) position
  | _, .eliminate, position => offsetIndex 12 (by decide) position
  | _, .defined _, position => Fin.elim0 position
  | _, .constructor _, position => Fin.elim0 position
  | _, .natLiteral _, position => Fin.elim0 position
  | _, .sortTerm, position => offsetIndex 14 (by decide) position
  | _, .levelTerm, position => offsetIndex 15 (by decide) position
  | _, .el, position => offsetIndex 16 (by decide) position
  | _, .set, position => offsetIndex 18 (by decide) position
  | _, .prop, position => offsetIndex 19 (by decide) position
  | _, .setOmega _, position => Fin.elim0 position
  | _, .levelClosed _, position => Fin.elim0 position
  | _, .levelSuc, position => offsetIndex 20 (by decide) position
  | _, .levelMax, position => offsetIndex 21 (by decide) position
  | _, .levelNeutral, position => offsetIndex 23 (by decide) position
  | _, .apply, position => offsetIndex 24 (by decide) position
  | _, .proj _, position => Fin.elim0 position
  | _, .nil, position => Fin.elim0 position
  | _, .cons, position => offsetIndex 25 (by decide) position
  | _, .append, position => offsetIndex 27 (by decide) position

/-- Lookup is checked against the generated table itself. -/
theorem congruenceIndex_selected {s : Srt} (op : Op s)
    (position : Fin (sig.arity op).length) :
    computationRules.get (congruenceIndex op position) =
      IntrinsicScopedLocalCongruence.rule op position := by
  cases op <;> rcases position with ⟨n, bound⟩
  all_goals simp only [sig, List.length_cons, List.length_nil] at bound
  all_goals
    match n with
    | 0 => first | rfl | (exfalso; omega)
    | 1 => first | rfl | (exfalso; omega)
    | n + 2 => exfalso; omega

def congruenceAddress {s : Srt} (op : Op s)
    (position : Fin (sig.arity op).length) :
    Address (IntrinsicScopedLocalCongruence.rule op position) :=
  ⟨congruenceIndex op position, congruenceIndex_selected op position⟩

def localOccurrence (r : LocalRule sig) (Γ : Ctx sig)
    (values : Valuation (M := r.1) algebra Γ)
    (close : Sub sig r.2.conclusion.ctx Γ) : Instance [r] algebra :=
  ⟨0, Γ, values, close⟩

/-- Fire a located rule using children in the whole presentation. -/
def fireAddress {r : LocalRule sig} (address : Address r) (Γ : Ctx sig)
    (values : Valuation (M := r.1) algebra Γ)
    (close : Sub sig r.2.conclusion.ctx Γ)
    (children : (position : Fin r.2.premises.length) →
      Tree computationRules algebra
        (childJudgment [r] algebra (localOccurrence r Γ values close) position)) :
    Tree computationRules algebra
      (conclusionJudgment [r] algebra (localOccurrence r Γ values close)) := by
  rcases address with ⟨index, same⟩
  subst r
  exact .roll ⟨⟨index, Γ, values, close⟩, rfl⟩ children

theorem root_premises_empty (index : Fin roots.length) :
    (roots.get index).2.premises = [] := by
  rcases index with ⟨i, bound⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | i + 6 =>
      exfalso
      simp only [roots, List.length_cons, List.length_nil] at bound
      omega

/-- A structural root selects its authored address and complete local data. -/
def rootTree {Γ : Ctx sig} {s : Srt} {source target : Term sig Γ s}
    (root : Root source target) : Tree computationRules algebra ⟨Γ, s, source, target⟩ := by
  let shape := shapeOfRoot root
  have built := fireAddress (rootAddress shape.1.index) shape.1.ambient
    shape.1.valuation shape.1.close (fun position =>
      Fin.elim0 (Fin.cast (congrArg List.length (root_premises_empty shape.1.index)) position))
  exact shape.2 ▸ built

/-- The selected argument is the sole child of the generated declaration. -/
def congruenceTree {Γ : Ctx sig} {s : Srt} (op : Op s)
    (args : Args sig (sig.arity op) Γ) (position : Fin (sig.arity op).length)
    (result : Term sig (((sig.arity op).get position).1 ++ Γ) ((sig.arity op).get position).2)
    (child : Tree computationRules algebra
      ⟨((sig.arity op).get position).1 ++ Γ, ((sig.arity op).get position).2,
        IntrinsicScopedLocalCongruence.getArg args position, result⟩) :
    Tree computationRules algebra ⟨Γ, s, .op op args,
      .op op (IntrinsicScopedLocalCongruence.replaceArg args position result)⟩ := by
  let values := IntrinsicScopedLocalCongruence.valuation (S := sig) op position args result
  have built := fireAddress (congruenceAddress op position) Γ values
    (IntrinsicScopedLocalCongruence.emptyClose Γ) (fun childPosition => by
      have zero : childPosition = (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) :=
        Fin.eq_zero childPosition
      subst childPosition
      exact (congrArg (Tree computationRules algebra)
        (IntrinsicScopedLocalCongruence.child_occurrence (S := sig) op position args result)).mpr child)
  exact (congrArg (Tree computationRules algebra)
    (IntrinsicScopedLocalCongruence.conclusion_occurrence (S := sig) op position args result)).mp built

end Authored

/-- The one changed argument together with its complete firing history. -/
structure SelectedArgument {Γ : Ctx sig} {arity : List (MetaArity sig)}
    (source target : Args sig arity Γ) where
  position : Fin arity.length
  result : Term sig ((arity.get position).1 ++ Γ) (arity.get position).2
  replaced : IntrinsicScopedLocalCongruence.replaceArg source position result = target
  child : Tree Authored.computationRules Authored.algebra
    ⟨(arity.get position).1 ++ Γ, (arity.get position).2,
      IntrinsicScopedLocalCongruence.getArg source position, result⟩

mutual
/-- Encode every compatible step in the actual 29-rule polynomial. -/
def stepToTree : ∀ {Γ : Ctx sig} {s : Srt} {source target : Term sig Γ s},
    Step source target → Tree Authored.computationRules Authored.algebra ⟨Γ, s, source, target⟩
  | _, _, _, _, .root root => Authored.rootTree root
  | _, _, _, _, .congr op arguments =>
      let selected := selectArgument arguments
      selected.replaced ▸ Authored.congruenceTree op _ selected.position selected.result selected.child

def selectArgument : ∀ {Γ : Ctx sig} {arity : List (MetaArity sig)}
    {source target : Args sig arity Γ}, ArgsStep source target → SelectedArgument source target
  | _, _, _, _, .head (target := target) _tail derivation =>
      ⟨0, target, rfl, stepToTree derivation⟩
  | _, _, _, _, .tail head derivation =>
      let selected := selectArgument derivation
      ⟨selected.position.succ, selected.result,
        congrArg (Args.cons head) selected.replaced, selected.child⟩
end

#print axioms Authored.congruenceIndex_selected
#print axioms Authored.rootTree
#print axioms Authored.congruenceTree
#print axioms stepToTree

end Mettapedia.Languages.Agda.Structural
