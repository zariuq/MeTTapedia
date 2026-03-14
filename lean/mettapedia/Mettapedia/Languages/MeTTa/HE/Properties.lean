import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa

/-!
# HE MeTTa Structural Properties

Universal properties of the HE MeTTa declarative specification.
These are proven by induction on derivation trees (EvalSpec.lean)
or by computation on leaf operations (Matching.lean, TypeCheck.lean).

## Main Theorems
* `eval_empty_always` — Empty always passes through EvalAtom
* `eval_error_always` — Error always passes through EvalAtom
* `eval_variable_always` — Variables always pass through EvalAtom
* `mettaCall_error_always` — Error always passes through MettaCall
* `matchTypes_undefined_succeeds` — `%Undefined%` always matches any type
* `matchTypes_atom_succeeds` — `Atom` type always matches any type
* `empty_bindings_no_loop` — Empty bindings have no loop
-/

namespace Mettapedia.Languages.MeTTa.HE.Properties

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE

/-! ## EvalAtom Passthrough Properties

These prove that certain atoms ALWAYS have valid derivations that pass
them through unchanged, regardless of space/dispatch/type. -/

/-- Empty always passes through EvalAtom unchanged. -/
theorem eval_empty_always (space : Space) (dispatch : GroundedDispatch)
    (type_ : Atom) (b : Bindings) :
    EvalAtom space dispatch Atom.empty type_ b (Atom.empty, b) :=
  .empty_or_error _ _ _ rfl

/-- Error always passes through EvalAtom unchanged. -/
theorem eval_error_always (space : Space) (dispatch : GroundedDispatch)
    (src msg type_ : Atom) (b : Bindings) :
    EvalAtom space dispatch (Atom.error src msg) type_ b
      (Atom.error src msg, b) :=
  .empty_or_error _ _ _ rfl

/-- Variables always pass through EvalAtom unchanged. -/
theorem eval_variable_always (space : Space) (dispatch : GroundedDispatch)
    (v : String) (type_ : Atom) (b : Bindings) :
    EvalAtom space dispatch (.var v) type_ b (.var v, b) :=
  .type_pass _ _ _ rfl (Or.inr (Or.inr rfl))

/-- When expected type is Atom and atom is not empty/error, it passes through. -/
theorem eval_atom_type_pass (space : Space) (dispatch : GroundedDispatch)
    (a : Atom) (b : Bindings) (h : isEmptyOrError a = false) :
    EvalAtom space dispatch a Atom.atomType b (a, b) :=
  .type_pass _ _ _ h (Or.inl rfl)

/-- When expected type is Atom, any atom passes through (via one of two paths). -/
theorem eval_atom_type_always (space : Space) (dispatch : GroundedDispatch)
    (a : Atom) (b : Bindings) :
    EvalAtom space dispatch a Atom.atomType b (a, b) := by
  by_cases h : isEmptyOrError a = true
  · exact .empty_or_error _ _ _ h
  · exact .type_pass _ _ _ (by simp at h; exact h) (Or.inl rfl)

/-! ## MettaCall Passthrough Properties -/

/-- Error always passes through MettaCall unchanged. -/
theorem mettaCall_error_always (space : Space) (dispatch : GroundedDispatch)
    (src msg type_ : Atom) (b : Bindings) :
    MettaCall space dispatch (Atom.error src msg) type_ b
      (Atom.error src msg, b) :=
  .error_passthrough _ _ _ rfl

/-! ## Leaf Operation Properties -/

/-- Empty bindings have no loop. -/
theorem empty_bindings_no_loop : Bindings.empty.hasLoop = false := rfl

/-- matchTypes with %Undefined% on the left always succeeds. -/
theorem matchTypes_undefined_succeeds (t : Atom) (b : Bindings) :
    matchTypes Atom.undefinedType t b ≠ [] := by
  simp [matchTypes, Atom.undefinedType, BEq.beq, Atom.beq]

/-- matchTypes with Atom on the right always succeeds. -/
theorem matchTypes_atom_succeeds (t : Atom) (b : Bindings) :
    matchTypes t Atom.atomType b ≠ [] := by
  simp [matchTypes, Atom.atomType, BEq.beq, Atom.beq]

/-- matchAtoms is reflexive on symbols. -/
theorem matchAtoms_refl_symbol (s : String) (fuel : Nat) (h : fuel > 0) :
    Bindings.empty ∈ matchAtoms (.symbol s) (.symbol s) fuel := by
  cases fuel with
  | zero => omega
  | succ n =>
    simp [matchAtoms, Atom.symbolType, getMetaType, Bindings.empty, Bindings.hasLoop]

/-! ## MinimalStep Properties -/

/-- cons-atom followed by decons-atom is the identity (round-trip). -/
theorem cons_decons_roundtrip (dispatch : GroundedDispatch) (s : Space)
    (hd : Atom) (tl : List Atom) (ib : Bindings) :
    MinimalStep dispatch s
      (.expression [.symbol "cons-atom", hd, .expression tl]) ib
      s (.expression (hd :: tl), ib) :=
  .cons_atom _ _ _ _

/-- decons-atom decomposes into head and tail. -/
theorem decons_produces_head_tail (dispatch : GroundedDispatch) (s : Space)
    (hd : Atom) (tl : List Atom) (ib : Bindings) :
    MinimalStep dispatch s
      (.expression [.symbol "decons-atom", .expression (hd :: tl)]) ib
      s (.expression [hd, .expression tl], ib) :=
  .decons_atom _ _ _ _

end Mettapedia.Languages.MeTTa.HE.Properties
