import Mettapedia.Languages.MeTTa.HE.Spec.Type.Instantiation
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance

/-!
# Finite presentations of LeaTTa type-binding resolution

LeaTTa's repaired type matcher carries equality-class bindings, whereas the
executable-independent presentation layer carries finite first-hit type
substitutions.  This module is the single adapter between those carriers.

For a finite observation scope, `leaCanonicalTypeSubstOn` records the total
class solution at every scoped name.  Applying that finite substitution to an
atom whose variables lie in the scope is exactly LeaTTa instantiation, after
structural decoding.  No matcher execution or fuel appears in the statement.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypeCanonicalSubst

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Instantiation
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaTypeConformance

/-- The finite graph of LeaTTa's total class solution on one observation
scope.  `eraseDups` makes the first-hit carrier key-unique without choosing
or changing any equality-class representative. -/
def leaCanonicalTypeSubstOn
    (bindings : Metta.Bindings) (scope : List String) : TypeSubst :=
  scope.eraseDups.map fun name =>
    (name, fromLeaTTaAtom (leaClassSolution bindings name))

private theorem lookup_map_self
    (value : String → Atom) : ∀ (names : List String) (name : String),
    TypeSubst.lookup (names.map fun key => (key, value key)) name =
      if name ∈ names then some (value name) else none := by
  intro names
  induction names with
  | nil => intro name; simp
  | cons key names ih =>
      intro name
      simp only [List.map_cons, TypeSubst.lookup]
      by_cases hkey : name = key
      · subst key
        simp
      · simp [hkey, ih]

/-- Lookup in the canonical finite graph is exactly the class solution on
the supplied scope and is absent outside it. -/
theorem leaCanonicalTypeSubstOn_lookup
    (bindings : Metta.Bindings) (scope : List String) (name : String) :
    TypeSubst.lookup (leaCanonicalTypeSubstOn bindings scope) name =
      if name ∈ scope then
        some (fromLeaTTaAtom (leaClassSolution bindings name))
      else none := by
  unfold leaCanonicalTypeSubstOn
  rw [lookup_map_self]
  simp only [List.mem_eraseDups]

private theorem typeVars_mem_typeVarsList_of_mem
    {atom : Atom} {atoms : List Atom} (hatom : atom ∈ atoms) :
    ∀ name, name ∈ TypeSubst.typeVars atom →
      name ∈ TypeSubst.typeVarsList atoms := by
  induction atoms with
  | nil => simp at hatom
  | cons head tail ih =>
      simp only [List.mem_cons] at hatom
      rcases hatom with rfl | htail
      · intro name hname
        simp [TypeSubst.typeVarsList, hname]
      · intro name hname
        simp only [TypeSubst.typeVarsList, List.mem_append]
        exact Or.inr (ih htail name hname)

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

/-- On atoms observed by the finite scope, first-hit application of the
canonical graph is homomorphic application of the decoded class solution. -/
theorem leaCanonicalTypeSubstOn_apply_eq
    (bindings : Metta.Bindings) (scope : List String) (atom : Atom)
    (hscope : ∀ name, name ∈ TypeSubst.typeVars atom → name ∈ scope) :
    (leaCanonicalTypeSubstOn bindings scope).apply atom =
      applyTypeValuation
        (fun name => fromLeaTTaAtom (leaClassSolution bindings name)) atom := by
  suffices key : ∀ n (current : Atom), sizeOf current ≤ n →
      (∀ name, name ∈ TypeSubst.typeVars current → name ∈ scope) →
      (leaCanonicalTypeSubstOn bindings scope).apply current =
        applyTypeValuation
          (fun name => fromLeaTTaAtom (leaClassSolution bindings name))
          current by
    exact key (sizeOf atom) atom le_rfl hscope
  intro n
  induction n with
  | zero =>
      intro current hsize
      exact absurd hsize (by have := atom_size_pos current; omega)
  | succ n ih =>
      intro current hsize hcurrent
      cases current with
      | symbol name =>
          simp [TypeSubst.apply, applyTypeValuation]
      | var name =>
          have hname : name ∈ scope :=
            hcurrent name (by simp [TypeSubst.typeVars])
          simp [TypeSubst.apply, applyTypeValuation,
            leaCanonicalTypeSubstOn_lookup, hname]
      | grounded value =>
          simp [TypeSubst.apply, applyTypeValuation]
      | expression atoms =>
          simp only [TypeSubst.apply, applyTypeValuation,
            Atom.expression.injEq]
          apply List.map_congr_left
          intro child hchild
          apply ih child
          · have hlt := atom_size_lt_of_mem hchild
            have hatoms : sizeOf atoms ≤ n := by
              simp at hsize
              omega
            omega
          · intro name hname
            apply hcurrent name
            simpa only [TypeSubst.typeVars] using
              typeVars_mem_typeVarsList_of_mem hchild name hname

/-- The canonical finite presentation and LeaTTa's equality-class resolver
produce exactly the same decoded atom on the stated finite scope. -/
theorem leaCanonicalTypeSubstOn_apply_eq_instantiate
    (bindings : Metta.Bindings) (scope : List String) (atom : Atom)
    (hscope : ∀ name, name ∈ TypeSubst.typeVars atom → name ∈ scope) :
    (leaCanonicalTypeSubstOn bindings scope).apply atom =
      fromLeaTTaAtom (Metta.instantiate bindings (toLeaTTaAtom atom)) := by
  rw [leaCanonicalTypeSubstOn_apply_eq bindings scope atom hscope]
  rw [← fromLeaTTaAtom_applyClassSolution]
  rw [applyClassSolution_lea_eq_instantiate]

/-! ## Boundary examples -/

/-- Positive: a scoped equality alias is presented exactly as the runtime
resolver presents it. -/
theorem scoped_alias_presentation :
    (leaCanonicalTypeSubstOn
        [Metta.BindingRel.eq "x" "y"] ["x", "y"]).apply
          (.expression [.var "x", .var "y"]) =
      fromLeaTTaAtom
        (Metta.instantiate [Metta.BindingRel.eq "x" "y"]
          (toLeaTTaAtom (.expression [.var "x", .var "y"]))) := by
  apply leaCanonicalTypeSubstOn_apply_eq_instantiate
  intro name hname
  simp [TypeSubst.typeVars, TypeSubst.typeVarsList] at hname ⊢
  exact hname

/-- Negative: omitting an observed variable from the finite graph is not a
valid presentation of a binding that resolves that variable. -/
theorem omitted_alias_scope_changes_observation :
    (leaCanonicalTypeSubstOn
        [Metta.BindingRel.eq "x" "y"] []).apply (.var "x") ≠
      fromLeaTTaAtom
        (Metta.instantiate [Metta.BindingRel.eq "x" "y"]
          (toLeaTTaAtom (.var "x"))) := by
  simp [leaCanonicalTypeSubstOn,
    toLeaTTaAtom, fromLeaTTaAtom, Metta.instantiate,
    Metta.Bindings.resolveAtom, leaClassSolution, Metta.Bindings.resolve,
    Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
    Metta.Bindings.classValues, Metta.Bindings.lookupVal,
    Metta.Bindings.eqClass, Metta.Bindings.eqClassAux,
    Metta.Bindings.eqStep, Metta.Bindings.resolveAtomAux,
    Metta.Bindings.eqRepresentative, Metta.Bindings.resolutionFuel,
    Metta.Bindings.relationResolutionFuel, Metta.Atom.size]

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypeCanonicalSubst
