import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Normal

/-!
# Solution theory of finite type presentations

A finite type substitution denotes the equations carried by its entries.
Normal substitutions have a canonical syntactic valuation: apply the finite
substitution once to each variable.  This valuation satisfies every stored
equation, and every other satisfying valuation factors through it by ordinary
homomorphic atom substitution.  These facts separate principality from any
particular matcher or equality-class representation.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement

/-- Equation semantics of one finite type presentation. -/
def TypeSubstSatisfied
    (valuation : String → Atom) (substitution : TypeSubst) : Prop :=
  ∀ name value, (name, value) ∈ substitution →
    valuation name = applyTypeValuation valuation value

/-- The syntactic valuation presented by one-pass finite substitution. -/
def presentedValuation (substitution : TypeSubst) : String → Atom :=
  fun name => substitution.apply (.var name)

private theorem atom_size_pos (atom : Atom) : 0 < sizeOf atom := by
  cases atom <;> simp

private theorem atom_size_lt_of_mem {atom : Atom} :
    ∀ {atoms : List Atom}, atom ∈ atoms → sizeOf atom < sizeOf atoms
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp
        omega
      · have hlt := atom_size_lt_of_mem htail
        simp
        omega

/-- Mapping every variable to itself is the identity valuation on atoms. -/
@[simp] theorem applyTypeValuation_var_identity : ∀ atom : Atom,
    applyTypeValuation (fun name => .var name) atom = atom := by
  intro atom
  suffices key : ∀ n (current : Atom), sizeOf current ≤ n →
      applyTypeValuation (fun name => .var name) current = current by
    exact key (sizeOf atom) atom le_rfl
  intro n
  induction n with
  | zero =>
      intro current hsize
      exact absurd hsize (by have := atom_size_pos current; omega)
  | succ n ih =>
      intro current hsize
      cases current with
      | symbol name => simp [applyTypeValuation]
      | var name => simp [applyTypeValuation]
      | grounded value => simp [applyTypeValuation]
      | expression atoms =>
          simp only [applyTypeValuation, Atom.expression.injEq]
          calc
            List.map
                (applyTypeValuation (fun name => .var name)) atoms =
                List.map id atoms := by
              apply List.map_congr_left
              intro child hchild
              apply ih child
              have hlt := atom_size_lt_of_mem hchild
              have hatoms : sizeOf atoms ≤ n := by
                simp at hsize
                omega
              omega
            _ = atoms := List.map_id atoms

/-- Applying a valuation after a finite presentation is the same as applying
the valuation induced by the presentation directly. -/
theorem applyTypeValuation_presentedValuation
    (valuation : String → Atom) (substitution : TypeSubst) :
    ∀ atom,
      applyTypeValuation valuation (substitution.apply atom) =
        applyTypeValuation
          (fun name => applyTypeValuation valuation
            (presentedValuation substitution name)) atom := by
  suffices key : ∀ n (atom : Atom), sizeOf atom ≤ n →
      applyTypeValuation valuation (substitution.apply atom) =
        applyTypeValuation
          (fun name => applyTypeValuation valuation
            (presentedValuation substitution name)) atom by
    intro atom
    exact key (sizeOf atom) atom le_rfl
  intro n
  induction n with
  | zero =>
      intro atom hsize
      exact absurd hsize (by have := atom_size_pos atom; omega)
  | succ n ih =>
      intro atom hsize
      cases atom with
      | symbol name => simp [TypeSubst.apply, applyTypeValuation]
      | var name => simp [applyTypeValuation, presentedValuation]
      | grounded value => simp [TypeSubst.apply, applyTypeValuation]
      | expression atoms =>
          simp only [TypeSubst.apply, applyTypeValuation,
            Atom.expression.injEq, List.map_map]
          apply List.map_congr_left
          intro child hchild
          apply ih child
          have hlt := atom_size_lt_of_mem hchild
          have hatoms : sizeOf atoms ≤ n := by
            simp at hsize
            omega
          omega

/-- A satisfying valuation absorbs one-pass presentation on every atom. -/
theorem TypeSubstSatisfied.absorbs
    {valuation : String → Atom} {substitution : TypeSubst}
    (satisfied : TypeSubstSatisfied valuation substitution) :
    ∀ atom,
      applyTypeValuation valuation (substitution.apply atom) =
        applyTypeValuation valuation atom := by
  intro atom
  rw [applyTypeValuation_presentedValuation]
  congr 1
  funext name
  unfold presentedValuation
  simp only [TypeSubst.apply]
  cases hlookup : substitution.lookup name with
  | none => simp [Option.getD, applyTypeValuation]
  | some value =>
      exact (satisfied name value
        (TypeSubst.lookup_eq_some_mem hlookup)).symm

/-- Applying the presented valuation homomorphically is literally one-pass
finite substitution. -/
theorem applyTypeValuation_presented_eq_apply
    (substitution : TypeSubst) (atom : Atom) :
    applyTypeValuation (presentedValuation substitution) atom =
      substitution.apply atom := by
  have composition := applyTypeValuation_presentedValuation
    (fun name => .var name) substitution atom
  simpa only [applyTypeValuation_var_identity] using composition.symm

private theorem lookup_eq_some_of_mem_of_nodup :
    ∀ {substitution : TypeSubst} {name : String} {value : Atom},
      substitution.keys.Nodup →
      (name, value) ∈ substitution →
      substitution.lookup name = some value := by
  intro substitution
  induction substitution with
  | nil => simp
  | cons head tail ih =>
      rcases head with ⟨key, stored⟩
      intro name value hnodup hmem
      simp only [TypeSubst.keys, List.map_cons,
        List.nodup_cons] at hnodup
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        simp [TypeSubst.lookup]
      · have hne : name ≠ key := by
          intro heq
          subst name
          apply hnodup.1
          have : key ∈ tail.map Prod.fst := by
            exact List.mem_map.mpr ⟨(key, value), htail, rfl⟩
          simpa [TypeSubst.keys] using this
        simp [TypeSubst.lookup, hne, ih hnodup.2 htail]

/-- The presented valuation of a normal substitution satisfies every stored
equation. -/
theorem normal_presentedValuation_satisfied
    {substitution : TypeSubst} (normal : substitution.Normal) :
    TypeSubstSatisfied (presentedValuation substitution) substitution := by
  intro name value hmem
  have hlookup : substitution.lookup name = some value :=
    lookup_eq_some_of_mem_of_nodup normal.1 hmem
  have hleft : presentedValuation substitution name = value := by
    simp [presentedValuation, TypeSubst.apply, hlookup, Option.getD]
  rw [hleft]
  symm
  rw [applyTypeValuation_presented_eq_apply]
  apply TypeSubst.apply_eq_self_of_variables_not_keys
  exact normal.2 name value hmem

/-- Every satisfying valuation factors through the normal presentation's
canonical valuation. -/
theorem typeSubst_factorization
    {substitution : TypeSubst}
    {valuation : String → Atom}
    (satisfied : TypeSubstSatisfied valuation substitution) :
    ∀ atom,
      applyTypeValuation valuation
          (applyTypeValuation (presentedValuation substitution) atom) =
        applyTypeValuation valuation atom := by
  intro atom
  have hcanonicalApply :
      applyTypeValuation (presentedValuation substitution) atom =
        substitution.apply atom :=
    applyTypeValuation_presented_eq_apply substitution atom
  rw [hcanonicalApply]
  exact satisfied.absorbs atom

/-! ## Boundary examples -/

private def tToA : TypeSubst := [("t", .symbol "A")]

/-- Positive: the canonical presentation of `$t := A` is a genuine model of
its stored equation. -/
theorem tToA_presented_model :
    TypeSubstSatisfied (presentedValuation tToA) tToA := by
  have normal : tToA.Normal := by
    simp [tToA, TypeSubst.Normal, TypeSubst.keys, TypeSubst.typeVars]
  exact normal_presentedValuation_satisfied normal

private def chainedNonNormal : TypeSubst :=
  [("x", .var "y"), ("y", .symbol "A")]

/-- Negative: a non-normal chained presentation is not generally its own
one-pass model; `$x := $y, $y := A` still presents `$x` as `$y` after one
pass, so its first equation is false under that presentation. -/
theorem chained_non_normal_presentation_not_model :
    ¬TypeSubstSatisfied
      (presentedValuation chainedNonNormal) chainedNonNormal := by
  intro satisfied
  have first := satisfied "x" (.var "y") (by
    simp [chainedNonNormal])
  simp [presentedValuation, chainedNonNormal,
    TypeSubst.apply, TypeSubst.lookup, applyTypeValuation,
    Option.getD] at first

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory
