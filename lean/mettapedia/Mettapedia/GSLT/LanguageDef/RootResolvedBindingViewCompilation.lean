import Mettapedia.GSLT.LanguageDef.MixedQueryViewCompilation

/-!
# Root resolution of finite triangular binding stores

An executable occurrence check admits a finite, topologically ordered binding
store. Complete forcing recursively substitutes through that order. A separate
root resolver repeatedly looks up the current variable in the whole store and
stops at the first rigid root or unbound variable; it does not visit children.
Their correspondence is derived from the actual lookup and substitution code.

The resulting root/child observer instantiates the existing rigid-prefix
unification theorem. Open variables retain their generation-qualified identity,
so repeated occurrences and cross-equation correlations are preserved. A root
work allowance is physical: exhaustion falls back to complete forcing.

This is an immutable finite-term observation boundary. It does not establish a
mutable builder append/rollback refinement, logical-cons or arbitrary
expression-head encoding, raw binding-entry equality, C pointer ownership, or
the adequacy of a resolver which identifies variables by printed spelling.
After a binding update the observer must use the new store. The conservative
matching corollary forces the residual system at the first capture; the existing
fully resumed matcher has a separate logical substitution-composition law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RootResolvedBindingViewCompilation

open CompiledPlanOpenActivationViewCompilation
open DelayedSourceBindingCompilation
open TermObservationCoalgebra
open UnificationEliminationTraceCompilation
open MixedQueryViewCompilation
open Mettapedia.Languages.MeTTa.TermViewCompilation
open Mettapedia.Logic.LP

abbrev Binding := LogicVariable × OpenTerm
abbrev Store := List Binding

mutual
def termVariables : OpenTerm → List LogicVariable
  | .variable name => [name]
  | .application _ children => termsVariables children
  | _ => []

def termsVariables : OpenTerms → List LogicVariable
  | .nil => []
  | .cons head tail => termVariables head ++ termsVariables tail
end

/-- No entry may mention its own key or an earlier key. Distinct keys and
absence of backward dependencies are checked from the complete stored terms.
This is a topological presentation, not the chronology of mutable writes. -/
def check : Store → Bool
  | [] => true
  | (key, value) :: rest =>
      decide (key ∉ termVariables value ∧
        ∀ binding ∈ rest, binding.1 ≠ key ∧ key ∉ termVariables binding.2) && check rest

def lookup : Store → LogicVariable → Option OpenTerm
  | [], _ => none
  | (key, value) :: rest, name =>
      if name = key then some value else lookup rest name

/-- Independent complete substitution, following the triangular store. -/
def substitution : Store → OpenSubstitution
  | [] => emptyOpenSubstitution
  | (key, value) :: rest => fun name =>
      if name = key then some (substituteOpen (substitution rest) value)
      else substitution rest name

def force (store : Store) (value : OpenTerm) : OpenTerm :=
  substituteOpen (substitution store) value

@[simp] theorem force_empty (value : OpenTerm) : force [] value = value :=
  substituteOpen_empty value

mutual
theorem substitute_eq_of_agrees (first second : OpenSubstitution)
    (value : OpenTerm)
    (agrees : ∀ name ∈ termVariables value, first name = second name) :
    substituteOpen first value = substituteOpen second value := by
  cases value with
  | symbol name => rfl
  | string value => rfl
  | integer value => rfl
  | «variable» name =>
      simp only [substituteOpen]
      rw [agrees name (by simp [termVariables])]
  | application head children =>
      simp only [substituteOpen]
      congr 1
      exact substituteTerms_eq_of_agrees first second children agrees

theorem substituteTerms_eq_of_agrees (first second : OpenSubstitution)
    (values : OpenTerms)
    (agrees : ∀ name ∈ termsVariables values, first name = second name) :
    substituteOpenTerms first values = substituteOpenTerms second values := by
  cases values with
  | nil => rfl
  | cons head tail =>
      simp only [substituteOpenTerms]
      congr 1
      · apply substitute_eq_of_agrees
        intro name present
        exact agrees name (by simp [termsVariables, present])
      · apply substituteTerms_eq_of_agrees
        intro name present
        exact agrees name (by simp [termsVariables, present])
end

theorem force_cons_of_absent (key : LogicVariable) (stored value : OpenTerm)
    (rest : Store) (absent : key ∉ termVariables value) :
    force ((key, stored) :: rest) value = force rest value := by
  apply substitute_eq_of_agrees
  intro name present
  have different : name ≠ key := by
    intro same
    exact absent (same ▸ present)
  simp [substitution, different]

theorem lookup_mem (store : Store) (name : LogicVariable) (value : OpenTerm)
    (found : lookup store name = some value) : (name, value) ∈ store := by
  induction store with
  | nil => simp [lookup] at found
  | cons binding rest inductionHypothesis =>
      rcases binding with ⟨key, stored⟩
      simp only [lookup] at found
      split at found
      · rename_i same
        cases found
        simp [same]
      · exact List.mem_cons_of_mem _ (inductionHypothesis found)

theorem force_unbound (store : Store) (name : LogicVariable)
    (unbound : lookup store name = none) :
    force store (.variable name) = .variable name := by
  induction store with
  | nil => simp
  | cons binding rest inductionHypothesis =>
      rcases binding with ⟨key, stored⟩
      simp only [lookup] at unbound
      split at unbound
      · contradiction
      · rename_i different
        simpa [force, substituteOpen, substitution, different]
          using inductionHypothesis unbound

/-- Every admitted raw lookup is an equation of complete forcing. This is
derived from the executable support check rather than postulated for a view. -/
theorem force_lookup (store : Store) (admitted : check store = true)
    (name : LogicVariable) (value : OpenTerm)
    (found : lookup store name = some value) :
    force store (.variable name) = force store value := by
  induction store with
  | nil => simp [lookup] at found
  | cons binding rest inductionHypothesis =>
      rcases binding with ⟨key, stored⟩
      have conditions :
          (key ∉ termVariables stored ∧
            ∀ binding ∈ rest, binding.1 ≠ key ∧ key ∉ termVariables binding.2) ∧
          check rest = true := by
        simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using admitted
      simp only [lookup] at found
      split at found
      · rename_i same
        cases found
        subst name
        rw [force_cons_of_absent key value value rest conditions.1.1]
        simp [force, substituteOpen, substitution]
      · rename_i different
        have absent := (conditions.1.2 (name, value) (lookup_mem rest name value found)).2
        rw [force_cons_of_absent key stored value rest absent]
        have tailExact := inductionHypothesis conditions.2 found
        simpa [force, substituteOpen, substitution, different] using tailExact

/-- The operational resolver keeps the whole store at every alias lookup.
An exhausted allowance returns `none`, never an unbound-variable judgment. -/
def resolveRoot? (store : Store) : Nat → OpenTerm → Option OpenTerm
  | 0, _ => none
  | fuel + 1, .variable name =>
      match lookup store name with
      | none => some (.variable name)
      | some value => resolveRoot? store fuel value
  | _ + 1, value => some value

def RootStable (store : Store) : OpenTerm → Prop
  | .variable name => lookup store name = none
  | _ => True

/-- Completed root resolution preserves the entire open value, and its
returned variable (if any) is genuinely unbound in the same store. -/
theorem resolveRoot?_exact (store : Store) (admitted : check store = true)
    (fuel : Nat) (source resolved : OpenTerm)
    (completed : resolveRoot? store fuel source = some resolved) :
    force store resolved = force store source ∧ RootStable store resolved := by
  induction fuel generalizing source resolved with
  | zero => simp [resolveRoot?] at completed
  | succ fuel inductionHypothesis =>
      cases source with
      | «variable» name =>
          simp only [resolveRoot?] at completed
          cases found : lookup store name with
          | none =>
              simp [found] at completed
              subst resolved
              exact ⟨rfl, found⟩
          | some value =>
              rw [found] at completed
              obtain ⟨exactValue, stable⟩ := inductionHypothesis value resolved completed
              exact ⟨exactValue.trans (force_lookup store admitted name value found).symm,
                stable⟩
      | symbol name | string value | integer value | application head children =>
          simp [resolveRoot?] at completed
          subst resolved
          exact ⟨rfl, trivial⟩

theorem openTermsToList_substitute (store : Store) (values : OpenTerms) :
    openTermsToList (substituteOpenTerms (substitution store) values) =
      (openTermsToList values).map (force store) := by
  cases values with
  | nil => rfl
  | cons head tail =>
      simp [substituteOpenTerms, openTermsToList, force,
        openTermsToList_substitute store tail]

theorem stable_root_layer (store : Store) (value : OpenTerm)
    (stable : RootStable store value) :
    (outOpen value).map (force store) = outOpen (force store value) := by
  cases value with
  | symbol name | string value | integer value => rfl
  | «variable» name =>
      rw [force_unbound store name stable]
      rfl
  | application head children =>
      simp only [outOpen, TermLayer.map, force, substituteOpen]
      exact congrArg (TermLayer.application head)
        (openTermsToList_substitute store children).symm

/-- A borrowed root and its original children carry exactly the same layer
as full substitution. Unrelated open fields need not be materialized. -/
theorem resolved_root_layer (store : Store) (admitted : check store = true)
    (fuel : Nat) (source resolved : OpenTerm)
    (completed : resolveRoot? store fuel source = some resolved) :
    (outOpen resolved).map (force store) = outOpen (force store source) := by
  obtain ⟨same, stable⟩ := resolveRoot?_exact store admitted fuel source resolved completed
  rw [stable_root_layer store resolved stable, same]

/-- An immutable, checked store is retained at every child. -/
structure View where
  store : Store
  admitted : check store = true
  source : OpenTerm

def View.force (view : View) : OpenTerm :=
  RootResolvedBindingViewCompilation.force view.store view.source

def View.eager (value : OpenTerm) : View := ⟨[], rfl, value⟩

def View.out (rootBudget : Nat) (view : View) : TermLayer View :=
  match resolveRoot? view.store rootBudget view.source with
  | some root => (outOpen root).map fun child => { view with source := child }
  | none => (outOpen view.force).map View.eager

/-- Root allowance controls the implementation route only. Declining root
resolution uses full forcing and retains the exact layer. -/
theorem View.out_exact (rootBudget : Nat) (view : View) :
    (view.out rootBudget).map View.force = outOpen view.force := by
  unfold View.out
  cases completed : resolveRoot? view.store rootBudget view.source with
  | none =>
      simp only [TermLayer.map_comp, Function.comp_def, View.eager, View.force,
        force_empty]
      exact TermLayer.map_id _
  | some root =>
      simp only [TermLayer.map_comp]
      exact resolved_root_layer view.store view.admitted rootBudget
        view.source root completed

/-- Reuse the independent rigid-prefix matcher; its first capture transfers
the complete correlated residual system to the existing unifier. -/
def runPrefix (rootBudget fuel : Nat) (work : List (View × View)) :
    EliminationTrace openSignature :=
  runDirect (View.out rootBudget) View.force fuel work

theorem runPrefix_exact (rootBudget fuel : Nat) (work : List (View × View)) :
    runPrefix rootBudget fuel work = runTrace fuel (encodeWork View.force work) :=
  runDirect_exact (View.out rootBudget) View.force (View.out_exact rootBudget) fuel work

theorem observe_runPrefix_exact (rootBudget fuel : Nat) (work : List (View × View)) :
    observe (runPrefix rootBudget fuel work) =
      unifyFuel fuel (encodeWork View.force work) := by
  rw [runPrefix_exact]
  exact observe_runTrace_exact fuel _

namespace Canaries

private def x : LogicVariable := ⟨1, 0⟩
private def y : LogicVariable := ⟨1, 1⟩
private def otherX : LogicVariable := ⟨2, 0⟩
private def box (value : OpenTerm) : OpenTerm :=
  .application [10] (.cons value .nil)
private def pair (left right : OpenTerm) : OpenTerm :=
  .application [11] (.cons left (.cons right .nil))
private def chain : Store := [(x, .variable y), (y, box (.integer 7))]
private def openChain : Store := [(x, box (.variable y))]

theorem acyclic_chain_admitted : check chain = true := by decide

theorem root_chain_resolves :
    resolveRoot? chain 3 (.variable x) = some (box (.integer 7)) := by decide

theorem open_child_retained :
    resolveRoot? openChain 2 (.variable x) = some (box (.variable y)) ∧
      force openChain (.variable x) = box (.variable y) := by decide

theorem insufficient_root_allowance_declines :
    resolveRoot? chain 1 (.variable x) = none := by decide

theorem self_cycle_rejected : check [(x, box (.variable x))] = false := by decide

theorem alias_cycle_rejected :
    check [(x, .variable y), (y, .variable x)] = false := by decide

theorem duplicate_keys_rejected :
    check [(x, .integer 1), (x, .integer 2)] = false := by decide

theorem generations_remain_distinct :
    force chain (.variable otherX) = .variable otherX := by decide

/-- A retained constructor root does not freeze its unresolved children. -/
theorem later_binding_changes_observation :
    resolveRoot? openChain 2 (.variable x) =
      resolveRoot? (openChain ++ [(y, .integer 9)]) 2 (.variable x) ∧
    force openChain (.variable x) ≠
      force (openChain ++ [(y, .integer 9)]) (.variable x) := by decide

private def sharedLeft : View :=
  ⟨openChain, by decide, pair (.variable x) (.variable y)⟩
private def sharedRight : View :=
  .eager (pair (box (.integer 3)) (.integer 4))

/-- The first field binds y=3; the repeated use in the second then conflicts.
Treating each child as an independent wildcard would incorrectly accept. -/
theorem correlated_fields_reject :
    (runPrefix 3 12 [(sharedLeft, sharedRight)]).stop = .constructorConflict := by decide

theorem correlated_fields_accept :
    (runPrefix 3 12 [(sharedLeft,
      View.eager (pair (box (.integer 3)) (.integer 3)))]).stop = .success := by decide

theorem occurs_after_open_capture :
    (runPrefix 3 12 [(View.eager (.variable y),
      ⟨openChain, by decide, .variable x⟩)]).stop = .occursCheck := by decide

end Canaries

#print axioms force_lookup
#print axioms resolveRoot?_exact
#print axioms resolved_root_layer
#print axioms View.out_exact
#print axioms runPrefix_exact
#print axioms observe_runPrefix_exact

end Mettapedia.GSLT.LanguageDef.RootResolvedBindingViewCompilation
