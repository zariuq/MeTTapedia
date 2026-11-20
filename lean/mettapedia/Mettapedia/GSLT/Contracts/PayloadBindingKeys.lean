import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

/-!
# Binding keys for embedded payloads

The parameter is a payload shape and its reference positions. Each
position has a lexical scope at the embedding boundary, which may be
empty for a sealed payload. The bound and free cases are disjoint:
a bound reference is keyed by its position in the scope; a free
reference preserves its declared identity. Neither the type of free
identity nor the order of keys is fixed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PayloadBindingKeys

variable {Token Other Free : Type*}

def reference [DecidableEq Token] (scope : List Token) (identity : Token → Free) (token : Token) :
    Nat ⊕ Free :=
  match scope.idxOf? token with
  | some slot => .inl slot
  | none => .inr (identity token)

private theorem index_rename [DecidableEq Token] [DecidableEq Other] (rename : Token ↪ Other)
    (scope : List Token) (token : Token) :
    (scope.map rename).idxOf? (rename token) = scope.idxOf? token := by
  simp only [List.idxOf?, List.findIdx?_map]
  congr 1
  funext candidate
  simp only [Function.comp_apply]
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq, rename.injective.eq_iff]

/-- The lexical address is invariant under a hygienic change of
spelling. The identity obligation is only on genuinely free references. -/
theorem reference_rename [DecidableEq Token] [DecidableEq Other] (rename : Token ↪ Other)
    (scope : List Token) (identity : Token → Free) (newIdentity : Other → Free) (token : Token)
    (freeInvariant : scope.idxOf? token = none → newIdentity (rename token) = identity token) :
    reference (scope.map rename) newIdentity (rename token) = reference scope identity token := by
  unfold reference
  rw [index_rename]
  cases hit : scope.idxOf? token with
  | none => simp [freeInvariant hit]
  | some _ => rfl

variable (P : PFunctor)

/-- Resolve only references; neither reconstruct a source term from its
key nor apply the source language's evaluator to the payload. -/
def resolve [DecidableEq Token] (scopes : ∀ s : P.A, P.B s → List Token)
    (identity : Token → Free) (payload : P Token) : P (Nat ⊕ Free) :=
  ⟨payload.1, fun i => reference (scopes payload.1 i) identity (payload.2 i)⟩

theorem resolve_rename [DecidableEq Token] [DecidableEq Other] (rename : Token ↪ Other)
    (scopes : ∀ s : P.A, P.B s → List Token)
    (identity : Token → Free) (newIdentity : Other → Free) (payload : P Token)
    (freeInvariant : ∀ i, (scopes payload.1 i).idxOf? (payload.2 i) = none →
      newIdentity (rename (payload.2 i)) = identity (payload.2 i)) :
    resolve P (fun s i => (scopes s i).map rename) newIdentity (P.map rename payload) =
      resolve P scopes identity payload := by
  rcases payload with ⟨shape, tokens⟩
  apply congrArg (Sigma.mk shape)
  funext position
  exact reference_rename rename (scopes shape position) identity newIdentity
    (tokens position) (freeInvariant position)

/-- If the source says which positions have no enclosing binders, a
resolved lookup in those positions preserves the free identity. -/
theorem sealed_free [DecidableEq Token] (identity : Token → Free) (payload : P Token) :
    resolve P (fun _ _ => []) identity payload = P.map (.inr ∘ identity) payload := by
  rcases payload with ⟨shape, tokens⟩
  rfl

namespace Controls

private def value : PFunctor where
  A := Unit
  B := fun _ => Fin 1

private def scalar (spelling : String) : value String :=
  ⟨(), fun _ => spelling⟩

theorem shared_and_sealed_differ :
    resolve value (fun _ _ => ["x"]) id (scalar "x") =
      resolve value (fun _ _ => ["y"]) id (scalar "y") ∧
    resolve value (fun _ _ => ([] : List String)) id (scalar "x") ≠
      resolve value (fun _ _ => ([] : List String)) id (scalar "y") := by
  refine ⟨rfl, fun h => ?_⟩
  have same := congrArg (fun row : value (Nat ⊕ String) => row.2 (0 : Fin 1)) h
  change Sum.inr (α := Nat) "x" = Sum.inr "y" at same
  exact (by decide : "x" ≠ "y") (Sum.inr.inj same)

/-- The raw payload and the surrounding scope are independent inputs.
Neither raw ordering nor indiscriminately forgetting variable spellings
can implement the boundary. -/
theorem no_uniform_scope_blind_key :
    ¬ ∃ key : value String → value (Nat ⊕ String),
      ∀ scope payload, key payload = resolve value (fun _ _ => scope) id payload := by
  rintro ⟨key, correct⟩
  have different := (correct ["x"] (scalar "x")).symm.trans (correct [] (scalar "x"))
  have same := congrArg (fun row : value (Nat ⊕ String) => row.2 (0 : Fin 1)) different
  change Sum.inl (β := String) 0 = Sum.inr "x" at same
  cases same

end Controls

#print axioms reference_rename
#print axioms resolve_rename
#print axioms Controls.shared_and_sealed_differ
#print axioms Controls.no_uniform_scope_blind_key

end Mettapedia.GSLT.Contracts.PayloadBindingKeys
