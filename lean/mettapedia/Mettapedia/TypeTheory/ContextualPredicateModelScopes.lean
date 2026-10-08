import Mettapedia.TypeTheory.ContextualPredicateAssumptions
import Mettapedia.TypeTheory.ContextualModelTelescopes

/-!
# Mixed dependent scopes in local predicate models

Data binders use the supplied dependent comprehension. Assumption binders
use its guarded context inclusion and retain every prior dependent variable
by substitution. The data arity does not count assumption positions.
Complete arguments are checked against both their dependent types and their
actual assumption guards, then assembled uniquely into a model map.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateModelScopes

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateAssumptions ContextualModelTelescopes

universe c s t m p
variable {C : CwfWithTerminal.{c, s, t, m}}
variable {doctrine : PredicateDoctrine.{c, s, t, m, p} C.toCwf}
variable (assumptions : AssumptionOperations doctrine)

/-- The actual guard, rather than data components alone, admits a map into
an assumption context. -/
noncomputable def select? {source target : C.toCwf.Ctx}
    (predicate : doctrine.Predicate target) (substitution : C.toCwf.Sub source target) :
    Option (C.toCwf.Sub source (assumptions.assumed target predicate)) := by
  classical
  exact if guard : doctrine.reindex substitution predicate = ⊤ then
    some (assumptions.select predicate substitution guard) else none

theorem select?_eq_some_iff {source target : C.toCwf.Ctx}
    (predicate : doctrine.Predicate target) (substitution : C.toCwf.Sub source target)
    (selected : C.toCwf.Sub source (assumptions.assumed target predicate)) :
    select? assumptions predicate substitution = some selected ↔
      C.toCwf.compS (assumptions.inclusion predicate) selected = substitution := by
  classical
  by_cases guard : doctrine.reindex substitution predicate = ⊤
  · rw [select?, dif_pos guard, Option.some.injEq]
    constructor
    · intro same
      exact same ▸ assumptions.select_beta predicate substitution guard
    · intro projection
      exact (select_unique assumptions predicate substitution guard selected projection).symm
  · rw [select?, dif_neg guard]
    constructor
    · intro impossible
      cases impossible
    · intro projection
      apply False.elim
      apply guard
      rw [← projection]
      exact arrow_guard assumptions predicate selected

theorem select?_supplied {source target : C.toCwf.Ctx}
    (predicate : doctrine.Predicate target)
    (selected : C.toCwf.Sub source (assumptions.assumed target predicate)) :
    select? assumptions predicate (C.toCwf.compS (assumptions.inclusion predicate) selected) =
      some selected :=
  (select?_eq_some_iff assumptions predicate _ selected).mpr rfl

inductive ScopeData (C : CwfWithTerminal.{c, s, t, m})
    (doctrine : PredicateDoctrine.{c, s, t, m, p} C.toCwf)
    (assumptions : AssumptionOperations doctrine) :
    Nat → C.toCwf.Ctx → Type (max c t p) where
  | nil : ScopeData C doctrine assumptions 0 C.empty
  | snoc {n : Nat} {context : C.toCwf.Ctx}
      (previous : ScopeData C doctrine assumptions n context) (type : C.toCwf.Ty context) :
      ScopeData C doctrine assumptions (n + 1) (C.toCwf.ext context type)
  | assume {n : Nat} {context : C.toCwf.Ctx}
      (previous : ScopeData C doctrine assumptions n context) (predicate : doctrine.Predicate context) :
      ScopeData C doctrine assumptions n (assumptions.assumed context predicate)

abbrev Scope (C : CwfWithTerminal.{c, s, t, m})
    (doctrine : PredicateDoctrine.{c, s, t, m, p} C.toCwf)
    (assumptions : AssumptionOperations doctrine) (n : Nat) :=
  Σ context : C.toCwf.Ctx, ScopeData C doctrine assumptions n context

namespace Scope

variable {assumptions}

abbrev nil (C : CwfWithTerminal.{c, s, t, m})
    (doctrine : PredicateDoctrine.{c, s, t, m, p} C.toCwf)
    (assumptions : AssumptionOperations doctrine) : Scope C doctrine assumptions 0 :=
  ⟨C.empty, .nil⟩

abbrev snoc {n : Nat} (scope : Scope C doctrine assumptions n)
    (type : C.toCwf.Ty scope.1) : Scope C doctrine assumptions (n + 1) :=
  ⟨C.toCwf.ext scope.1 type, .snoc scope.2 type⟩

abbrev assume {n : Nat} (scope : Scope C doctrine assumptions n)
    (predicate : doctrine.Predicate scope.1) : Scope C doctrine assumptions n :=
  ⟨assumptions.assumed scope.1 predicate, .assume scope.2 predicate⟩

end Scope

namespace ScopeData

variable {assumptions} {n : Nat} {source target earlier : C.toCwf.Ctx}

/-- The actual generic variable is stored; earlier variables are reindexed
through every subsequent data or assumption binder. -/
def lookup : {n : Nat} → {context : C.toCwf.Ctx} →
    ScopeData C doctrine assumptions n context → Fin n → Value C.toCwf context
  | _, _, .nil, index => Fin.elim0 index
  | _, _, .snoc previous type, index =>
      Fin.cases ⟨C.toCwf.tySub type (C.toCwf.wk type), C.toCwf.vz type⟩
        (fun older => (lookup previous older).substitute (C.toCwf.wk type)) index
  | _, _, .assume previous predicate, index =>
      (lookup previous index).substitute (assumptions.inclusion predicate)

@[simp] theorem lookup_zero (previous : ScopeData C doctrine assumptions n target)
    (type : C.toCwf.Ty target) :
    lookup (.snoc previous type) 0 = ⟨C.toCwf.tySub type (C.toCwf.wk type), C.toCwf.vz type⟩ := rfl

@[simp] theorem lookup_succ (previous : ScopeData C doctrine assumptions n target)
    (type : C.toCwf.Ty target) (index : Fin n) :
    lookup (.snoc previous type) index.succ = (lookup previous index).substitute (C.toCwf.wk type) := rfl

@[simp] theorem lookup_assume (previous : ScopeData C doctrine assumptions n target)
    (predicate : doctrine.Predicate target) (index : Fin n) :
    lookup (.assume previous predicate) index =
      (lookup previous index).substitute (assumptions.inclusion predicate) := rfl

def components (scope : ScopeData C doctrine assumptions n target)
    (substitution : C.toCwf.Sub source target) : Fin n → Value C.toCwf source :=
  fun index => (scope.lookup index).substitute substitution

theorem components_composition (scope : ScopeData C doctrine assumptions n target)
    (substitution : C.toCwf.Sub source target) (prior : C.toCwf.Sub earlier source) (index : Fin n) :
    components scope (C.toCwf.compS substitution prior) index =
      (components scope substitution index).substitute prior :=
  Value.substitute_composition _ _ _

@[simp] theorem components_succ (previous : ScopeData C doctrine assumptions n target)
    (type : C.toCwf.Ty target) (substitution : C.toCwf.Sub source (C.toCwf.ext target type))
    (index : Fin n) :
    components (.snoc previous type) substitution index.succ =
      components previous (C.toCwf.compS (C.toCwf.wk type) substitution) index :=
  (Value.substitute_composition _ _ _).symm

@[simp] theorem components_assume (previous : ScopeData C doctrine assumptions n target)
    (predicate : doctrine.Predicate target)
    (substitution : C.toCwf.Sub source (assumptions.assumed target predicate)) (index : Fin n) :
    components (.assume previous predicate) substitution index =
      components previous (C.toCwf.compS (assumptions.inclusion predicate) substitution) index :=
  (Value.substitute_composition _ _ _).symm

theorem components_pair_zero (previous : ScopeData C doctrine assumptions n target)
    (type : C.toCwf.Ty target) (substitution : C.toCwf.Sub source target)
    (term : C.toCwf.Tm source (C.toCwf.tySub type substitution)) :
    components (.snoc previous type) (C.toCwf.pair substitution type term) 0 =
      ⟨C.toCwf.tySub type substitution, term⟩ := by
  apply Sigma.ext
  · change C.toCwf.tySub (C.toCwf.tySub type (C.toCwf.wk type))
      (C.toCwf.pair substitution type term) = _
    rw [← C.toCwf.tySub_comp, C.toCwf.wk_pair]
  · exact (heq_of_eq (C.toCwf.vz_pair substitution type term)).trans (cast_heq _ _)

theorem components_pair_succ (previous : ScopeData C doctrine assumptions n target)
    (type : C.toCwf.Ty target) (substitution : C.toCwf.Sub source target)
    (term : C.toCwf.Tm source (C.toCwf.tySub type substitution)) (index : Fin n) :
    components (.snoc previous type) (C.toCwf.pair substitution type term) index.succ =
      components previous substitution index := by
  rw [components_succ, C.toCwf.wk_pair]

noncomputable def assemble? : {n : Nat} → {context : C.toCwf.Ctx} →
    ScopeData C doctrine assumptions n context →
      (Fin n → Option (Value C.toCwf source)) → Option (C.toCwf.Sub source context)
  | _, _, .nil, _ => some (C.toEmpty source)
  | _, _, .snoc previous type, supplied =>
      match assemble? previous (fun index => supplied index.succ) with
      | none => none
      | some older =>
          match supplied 0 with
          | none => none
          | some value =>
              match value.atType? (C.toCwf.tySub type older) with
              | none => none
              | some term => some (C.toCwf.pair older type term)
  | _, _, .assume previous predicate, supplied =>
      match assemble? previous supplied with
      | none => none
      | some older => select? assumptions predicate older

theorem assemble?_components : {n : Nat} → {context : C.toCwf.Ctx} →
    (scope : ScopeData C doctrine assumptions n context) →
    (substitution : C.toCwf.Sub source context) →
    assemble? scope (fun index => some (components scope substitution index)) = some substitution
  | _, _, .nil, substitution => congrArg some (C.toEmpty_unique source substitution).symm
  | _, _, .snoc previous type, substitution => by
      have earlierResult := assemble?_components previous (C.toCwf.compS (C.toCwf.wk type) substitution)
      have inputs :
          (fun index => some (components (.snoc previous type) substitution index.succ)) =
            (fun index => some (components previous (C.toCwf.compS (C.toCwf.wk type) substitution) index)) := by
        funext index
        rw [components_succ]
      rw [assemble?, inputs, earlierResult]
      simp only [components, lookup_zero, Value.substitute]
      have equal : C.toCwf.tySub (C.toCwf.tySub type (C.toCwf.wk type)) substitution =
          C.toCwf.tySub type (C.toCwf.compS (C.toCwf.wk type) substitution) :=
        (C.toCwf.tySub_comp _ _ _).symm
      rw [Value.atType?_cast _ _ equal]
      exact congrArg some (C.toCwf.pair_eta type substitution)
  | _, _, .assume previous predicate, substitution => by
      have inputs :
          (fun index => some (components (.assume previous predicate) substitution index)) =
            (fun index => some (components previous
              (C.toCwf.compS (assumptions.inclusion predicate) substitution) index)) := by
        funext index
        rw [components_assume]
      rw [assemble?, inputs,
        assemble?_components previous (C.toCwf.compS (assumptions.inclusion predicate) substitution)]
      exact select?_supplied assumptions predicate substitution

theorem assemble?_sound : {n : Nat} → {context : C.toCwf.Ctx} →
    (scope : ScopeData C doctrine assumptions n context) →
    (supplied : Fin n → Option (Value C.toCwf source)) →
    (substitution : C.toCwf.Sub source context) → assemble? scope supplied = some substitution →
    ∀ index, supplied index = some (components scope substitution index)
  | _, _, .nil, _, _, _, index => Fin.elim0 index
  | _, _, .snoc previous type, supplied, substitution, assembled, index => by
      cases earlierResult : assemble? previous (fun index => supplied index.succ) with
      | none => simp [assemble?, earlierResult] at assembled
      | some older =>
          cases newest : supplied 0 with
          | none => simp [assemble?, earlierResult, newest] at assembled
          | some value =>
              cases checked : value.atType? (C.toCwf.tySub type older) with
              | none => simp [assemble?, earlierResult, newest, checked] at assembled
              | some term =>
                  have same : C.toCwf.pair older type term = substitution := by
                    simpa only [assemble?, earlierResult, newest, checked, Option.some.injEq] using assembled
                  subst substitution
                  cases index using Fin.cases with
                  | zero =>
                      rw [components_pair_zero, newest]
                      exact congrArg some ((Value.atType?_eq_some_iff _ _ _).mp checked)
                  | succ olderIndex =>
                      rw [components_pair_succ]
                      exact assemble?_sound previous _ older earlierResult olderIndex
  | _, _, .assume previous predicate, supplied, substitution, assembled, index => by
      cases earlierResult : assemble? previous supplied with
      | none => simp [assemble?, earlierResult] at assembled
      | some older =>
          have restricted : select? assumptions predicate older = some substitution := by
            simpa only [assemble?, earlierResult] using assembled
          have projection := (select?_eq_some_iff assumptions predicate _ _).mp restricted
          rw [components_assume, projection]
          exact assemble?_sound previous supplied older earlierResult index

theorem assemble?_eq_some_iff (scope : ScopeData C doctrine assumptions n target)
    (supplied : Fin n → Option (Value C.toCwf source)) (substitution : C.toCwf.Sub source target) :
    assemble? scope supplied = some substitution ↔
      ∀ index, supplied index = some (components scope substitution index) := by
  constructor
  · exact assemble?_sound scope supplied substitution
  · intro all
    rw [funext all]
    exact assemble?_components scope substitution

theorem assemble?_substitution (scope : ScopeData C doctrine assumptions n target)
    (supplied : Fin n → Option (Value C.toCwf source)) (substitution : C.toCwf.Sub source target)
    (assembled : assemble? scope supplied = some substitution) (prior : C.toCwf.Sub earlier source) :
    assemble? scope (fun index => (supplied index).map (fun value => value.substitute prior)) =
      some (C.toCwf.compS substitution prior) := by
  apply (assemble?_eq_some_iff _ _ _).mpr
  intro index
  rw [assemble?_sound scope supplied substitution assembled index, Option.map_some,
    components_composition]

theorem components_injective (scope : ScopeData C doctrine assumptions n target) :
    Function.Injective (components (source := source) scope) := by
  intro first second equal
  have recovered := congrArg (fun supplied => assemble? scope (fun index => some (supplied index))) equal
  rw [assemble?_components, assemble?_components] at recovered
  exact Option.some.inj recovered

end ScopeData

end Mettapedia.TypeTheory.ContextualPredicateModelScopes
