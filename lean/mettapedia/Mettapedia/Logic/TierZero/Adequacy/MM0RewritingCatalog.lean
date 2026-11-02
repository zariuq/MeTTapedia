import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingSchedules
import Mettapedia.Languages.MM0.Kernel.FirstOrderTheories

/-!
# The finite MM0 rule catalog covers every declared inference scheme

The catalog is computed from the actual declaration tables. The imported
context-sort lemma is general; no first-order restriction is imposed here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel

structure Covers (theory : Theory) (keys : List RuleKey) : Prop where
  theorem_ : ∀ index declaration, theory.theoremSignature index = some declaration → .theorem_ index ∈ keys
  congruence : ∀ symbol declaration, theory.termSignature symbol = some declaration → .congruence symbol ∈ keys
  unfolding : ∀ symbol body, theory.definitionSignature symbol = some body → .unfolding symbol ∈ keys
  basic : ∀ sort, theory.sortSignature sort ≠ none → ∀ kind, .basic kind sort ∈ keys

def catalog (theory : Theory) : List RuleKey :=
  theory.theorems.map (fun entry => .theorem_ entry.1) ++
    theory.terms.map (fun entry => .congruence entry.1) ++
    theory.definitions.map (fun entry => .unfolding entry.1) ++
    theory.sorts.flatMap (fun entry =>
      [.basic .reflexivity entry.1, .basic .symmetry entry.1,
        .basic .transitivity entry.1, .basic .transport entry.1])

private theorem lookup_member {A : Type} {entries : List (Nat × A)} {index : Nat} {value : A}
    (known : entries.lookup index = some value) : (index, value) ∈ entries := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp known
  simp

theorem catalog_covers (theory : Theory) : Covers theory (catalog theory) := by
  constructor
  · intro index declaration known
    have present : RuleKey.theorem_ index ∈ theory.theorems.map (fun entry => RuleKey.theorem_ entry.1) :=
      List.mem_map.mpr ⟨(index, declaration), lookup_member known, rfl⟩
    simp [catalog, present]
  · intro symbol declaration known
    have present : RuleKey.congruence symbol ∈ theory.terms.map (fun entry => RuleKey.congruence entry.1) :=
      List.mem_map.mpr ⟨(symbol, declaration), lookup_member known, rfl⟩
    simp [catalog, present]
  · intro symbol body known
    have present : RuleKey.unfolding symbol ∈ theory.definitions.map (fun entry => RuleKey.unfolding entry.1) :=
      List.mem_map.mpr ⟨(symbol, body), lookup_member known, rfl⟩
    simp [catalog, present]
  · intro sort known kind
    cases found : theory.sortSignature sort with
    | none => exact False.elim (known found)
    | some info =>
      have present : RuleKey.basic kind sort ∈ theory.sorts.flatMap (fun entry =>
          [RuleKey.basic .reflexivity entry.1, RuleKey.basic .symmetry entry.1,
            RuleKey.basic .transitivity entry.1, RuleKey.basic .transport entry.1]) := by
        apply List.mem_flatMap.mpr
        exact ⟨(sort, info), lookup_member found, by cases kind <;> simp⟩
      simp [catalog, present]

theorem typed_sort_declared {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) {expression : Preterm} {remaining : Context} {sort : Nat}
    (typed : Preterm.HasType theory.termSignature target expression remaining sort) :
    theory.sortSignature sort ≠ none := by
  induction typed with
  | var known => exact formed.sortDeclared _ (List.mem_of_getElem? known)
  | term known =>
      obtain ⟨info, found, _⟩ := (wellFormed.terms _ _ known).result
      simp [found]
  | bound _ _ ih => exact ih
  | regular _ _ functionIH _ => exact functionIH

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
