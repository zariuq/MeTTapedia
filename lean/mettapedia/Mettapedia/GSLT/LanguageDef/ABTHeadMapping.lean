import Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

/-! # Structural head maps preserve the common ABT's binding coordinates -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

variable {A B : Type}

mutual
def mapHeads (change : A → B) : Term A → Term B
  | .idx index => .idx index
  | .node head fields => .node (change head) (mapFieldHeads change fields)

def mapFieldHeads (change : A → B) : Fields A → Fields B
  | .nil => .nil
  | .cons depth term rest => .cons depth (mapHeads change term) (mapFieldHeads change rest)
end

mutual
theorem mapHeads_scope (change : A → B) (depth : Nat) (term : Term A) :
    Term.supportedAt depth (mapHeads change term) = Term.supportedAt depth term := by
  cases term with
  | idx index => rfl
  | node head fields => exact mapFieldHeads_scope change depth fields

theorem mapFieldHeads_scope (change : A → B) (depth : Nat) (fields : Fields A) :
    Term.Fields.supportedAt depth (mapFieldHeads change fields) = Term.Fields.supportedAt depth fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [mapFieldHeads, Term.Fields.supportedAt, mapHeads_scope, mapFieldHeads_scope]
end

mutual
theorem mapHeads_injective (change : A → B) (injective : Function.Injective change) :
    ∀ first second : Term A, mapHeads change first = mapHeads change second → first = second
  | .idx first, .idx second, same => congrArg Term.idx (Term.idx.inj same)
  | .idx _, .node _ _, same => by cases same
  | .node _ _, .idx _, same => by cases same
  | .node head fields, .node other others, same => by
      obtain ⟨heads, children⟩ := Term.node.inj same
      have sameHead := injective heads
      subst other
      exact congrArg (Term.node head) (mapFieldHeads_injective change injective fields others children)

theorem mapFieldHeads_injective (change : A → B) (injective : Function.Injective change) :
    ∀ first second : Fields A, mapFieldHeads change first = mapFieldHeads change second → first = second
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _ _, same => by cases same
  | .cons _ _ _, .nil, same => by cases same
  | .cons depth term rest, .cons other child tail, same => by
      obtain ⟨depths, terms, tails⟩ := Fields.cons.inj same
      subst other
      rw [mapHeads_injective change injective term child terms,
        mapFieldHeads_injective change injective rest tail tails]
end

end Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
