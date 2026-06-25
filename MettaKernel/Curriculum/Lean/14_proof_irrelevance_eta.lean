/- Lean 14 — KERNEL CONVERSION features: definitional proof irrelevance + eta.
   Lean's kernel proves these by `rfl` (Coq's kernel does NOT have proof irrelevance) -- a
   faithful kernel must implement both. -/
namespace L14

-- definitional PROOF IRRELEVANCE: any two proofs of a Prop are DEFINITIONALLY equal
example (p : Prop) (h1 h2 : p) : h1 = h2 := rfl

-- consequence: subtype values are equal regardless of which proof they carry
example (P : Nat → Prop) (h1 h2 : P 3) : (⟨3, h1⟩ : {n // P n}) = ⟨3, h2⟩ := rfl

-- ETA for functions: f is definitionally its own eta-expansion
example (f : Nat → Nat) : f = (fun x => f x) := rfl

-- ETA for structures: a structure equals its field-wise reconstruction
structure Point where
  x : Nat
  y : Nat
example (p : Point) : p = ⟨p.x, p.y⟩ := rfl

end L14
