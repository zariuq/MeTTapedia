import Mettapedia.Languages.MeTTa.HE.VariantQueryCorrectness

/-!
# Renaming recursive assignment resolution

Assignment-key renaming commutes with recursive resolution when it fixes the
stored values. The fuel and visited-variable list are transported explicitly;
compound values may contain references to other assignments.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private theorem assignedVarAux_renamed
    (r : VarRenaming) {b b' : Bindings}
    (hrel : BindingsKeysRenamedBy r b b') :
    ∀ fuel a,
      b'.hasAssignedVarAux fuel (applyAtomTotal r a) =
        b.hasAssignedVarAux fuel a := by
  intro fuel
  induction fuel with
  | zero => intro a; rfl
  | succ fuel ih =>
      intro a
      cases a with
      | var v => simpa [applyAtomTotal, Bindings.hasAssignedVarAux, Bindings.isBound] using (hrel.bound_iff v).symm
      | symbol _ => simp [applyAtomTotal, Bindings.hasAssignedVarAux]
      | grounded _ => simp [applyAtomTotal, Bindings.hasAssignedVarAux]
      | expression es =>
          simp only [applyAtomTotal, Bindings.hasAssignedVarAux, List.any_map]
          simp only [Function.comp_def, ih]

private theorem assignedVar_fixed
    (r : VarRenaming) {b b' : Bindings}
    (hrel : BindingsKeysRenamedBy r b b')
    {a : Atom} (hfix : applyAtomTotal r a = a) :
    b'.hasAssignedVar a = b.hasAssignedVar a := by
  unfold Bindings.hasAssignedVar
  conv_lhs => arg 3; rw [← hfix]
  exact assignedVarAux_renamed r hrel _ a

private theorem renamed_lookup_none
    (r : VarRenaming) {b b' : Bindings}
    (hrel : BindingsKeysRenamedBy r b b') {v : String}
    (h : b.lookup v = none) : b'.lookup (r.rename v) = none := by
  have bound := hrel.bound_iff v
  simpa [h] using bound.symm

/-- Recursive assignment resolution preserves its result, exhaustion, and
cycle detection under injective key renaming that fixes assignment values. -/
theorem resolveAtomAux_keysRenamed
    (r : VarRenaming) (hr : r.Injective) {b b' : Bindings}
    (hrel : BindingsKeysRenamedBy r b b')
    (hfix : ∀ {v value}, b.lookup v = some value → applyAtomTotal r value = value) :
    ∀ fuel visited a,
      b'.resolveAtomAux fuel (visited.map r.rename) (applyAtomTotal r a) =
        (b.resolveAtomAux fuel visited a).map (applyAtomTotal r) := by
  intro fuel
  induction fuel with
  | zero => intro visited a; rfl
  | succ fuel ih =>
      intro visited a
      cases a with
      | symbol _ => simp [applyAtomTotal, Bindings.resolveAtomAux]
      | grounded _ => simp [applyAtomTotal, Bindings.resolveAtomAux]
      | var v =>
          have visitedEq : (visited.map r.rename).contains (r.rename v) =
              visited.contains v := by
            apply Bool.eq_iff_iff.mpr
            simp only [List.contains_iff_mem, List.mem_map, hr.eq_iff]
            simp
          simp only [applyAtomTotal, Bindings.resolveAtomAux, visitedEq]
          cases hv : visited.contains v <;> simp only [Bool.false_eq_true, ↓reduceIte]
          · cases hl : b.lookup v with
            | none => simp [renamed_lookup_none r hrel hl, applyAtomTotal]
            | some value =>
                have hl' := hrel.forward v value hl
                have fixed := hfix hl
                simp only [hl', assignedVar_fixed r hrel fixed]
                cases hs : b.hasAssignedVar value
                · simp [fixed]
                · simpa [fixed] using ih (v :: visited) value
          · rfl
      | expression es =>
          simp only [applyAtomTotal, Bindings.resolveAtomAux]
          have mapped :
              List.mapM (b'.resolveAtomAux fuel (visited.map r.rename))
                  (es.map (applyAtomTotal r)) =
                (List.mapM (b.resolveAtomAux fuel visited) es).map
                  (List.map (applyAtomTotal r)) := by
            induction es with
            | nil => rfl
            | cons a es tail =>
                simp only [List.map_cons, List.mapM_cons, ih, tail]
                cases b.resolveAtomAux fuel visited a <;>
                  cases List.mapM (b.resolveAtomAux fuel visited) es <;> rfl
          rw [mapped]
          cases List.mapM (b.resolveAtomAux fuel visited) es <;> simp [applyAtomTotal]

/-- The public assignment resolver transports through the same renaming. -/
theorem resolve_keysRenamed
    (r : VarRenaming) (hr : r.Injective) {b b' : Bindings}
    (hrel : BindingsKeysRenamedBy r b b')
    (hfix : ∀ {v value}, b.lookup v = some value → applyAtomTotal r value = value)
    (fuel : Nat) (v : String) :
    b'.resolve (r.rename v) fuel = (b.resolve v fuel).map (applyAtomTotal r) := by
  unfold Bindings.resolve
  cases hl : b.lookup v with
  | none => simp [renamed_lookup_none r hrel hl]
  | some value =>
      rw [hrel.forward v value hl]
      simpa [applyAtomTotal] using resolveAtomAux_keysRenamed r hr hrel hfix fuel [] (.var v)

/-- Applying recursively resolved assignments commutes with the renaming at
any fuel, including fuel too small to finish a compound binding chain. -/
theorem apply_keysRenamed
    (r : VarRenaming) (hr : r.Injective) {b b' : Bindings}
    (hrel : BindingsKeysRenamedBy r b b')
    (hfix : ∀ {v value}, b.lookup v = some value → applyAtomTotal r value = value) :
    ∀ fuel a,
      b'.apply (applyAtomTotal r a) fuel = applyAtomTotal r (b.apply a fuel) := by
  intro fuel
  induction fuel with
  | zero => intro a; rfl
  | succ fuel ih =>
      intro a
      cases a with
      | symbol _ => simp [applyAtomTotal, Bindings.apply]
      | grounded _ => simp [applyAtomTotal, Bindings.apply]
      | var v =>
          simp only [applyAtomTotal, Bindings.apply, resolve_keysRenamed r hr hrel hfix]
          cases b.resolve v fuel <;> simp [applyAtomTotal]
      | expression es =>
          simp [Bindings.apply, applyAtomTotal, List.map_map, Function.comp_def, ih]

namespace ResolutionCanary

private def chain : Bindings :=
  { assignments := [("y", .symbol "A"),
      ("x", .expression [.symbol "f", .var "y"])], equalities := [] }

/-- A compound assignment resolves its nested dependency with enough fuel. -/
theorem nested_dependency_resolves :
    chain.apply (.var "x") 4 = .expression [.symbol "f", .symbol "A"] := by
  decide +kernel

/-- The old expression-only fuel bound cannot resolve this binding chain. -/
theorem expression_only_fuel_is_insufficient :
    chain.apply (.var "x") 2 = .var "x" := by
  decide +kernel

private def cycle : Bindings :=
  { assignments := [("x", .expression [.symbol "f", .var "x"])], equalities := [] }

/-- Recursive resolution rejects a cyclic compound assignment. -/
theorem compound_cycle_is_rejected : cycle.resolve "x" 10 = none := by
  decide +kernel

end ResolutionCanary

end Mettapedia.Languages.MeTTa.HE
