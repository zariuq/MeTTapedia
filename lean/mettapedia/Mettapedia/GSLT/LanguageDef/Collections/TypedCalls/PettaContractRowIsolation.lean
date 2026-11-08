import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol

/-!
# What the native two-occurrence row test establishes

The selected parameter is an occurrence in an ordered row, represented by a
prefix/current/suffix view. Authored demand and the type after constant
instantiation are separate fields. The native scan excludes CONSTANT
parameters from its occurrence sum; their fix-closed evidence is a separate
obligation and is not converted here into syntactic absence.

Counts are natural numbers. Relating the current uint32 native counter to
them requires no overflow; the capped-count lemma records an alternative
which preserves the small decisions without wraparound.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaContractRowIsolation

structure Parameter (V : Type := String) where
  authored : Ty String
  resolved : Ty V
  constant : Bool := false

variable {V : Type} [DecidableEq V] [BEq V] [LawfulBEq V]

def count (name : V) (type : Ty V) : Nat := type.vars.count name

def contribution (name : V) (parameter : Parameter V) : Nat :=
  if parameter.constant then 0 else count name parameter.resolved

def uses (name : V) (parameters : List (Parameter V)) (range : Ty V) : Nat :=
  count name range + (parameters.map (contribution name)).sum

/-- The UNINTERPRETED branch of `contract_entry_facts`, at one real parameter
occurrence after constant-parameter instantiation. -/
def recognizes (before : List (Parameter V)) (current : Parameter V) (after : List (Parameter V))
    (authoredRange : Ty String) (resolvedRange : Ty V) : Option V :=
  match resolvedRange with
  | .var name =>
      if ResultGuarded authoredRange ∧ demand current.authored = .guarded ∧
          current.constant = false ∧ current.resolved = .var name ∧
          uses name (before ++ current :: after) resolvedRange = 2 then some name else none
  | _ => none

omit [LawfulBEq V] in
theorem recognition_fields (before : List (Parameter V)) (current : Parameter V) (after : List (Parameter V))
    (authoredRange : Ty String) (resolvedRange : Ty V) (name : V)
    (recognized : recognizes before current after authoredRange resolvedRange = some name) :
    resolvedRange = .var name ∧ ResultGuarded authoredRange ∧ demand current.authored = .guarded ∧
      current.constant = false ∧ current.resolved = .var name ∧
      uses name (before ++ current :: after) resolvedRange = 2 := by
  unfold recognizes at recognized
  split at recognized
  · split at recognized
    · rename_i accepted
      cases Option.some.inj recognized
      exact ⟨rfl, accepted⟩
    · cases recognized
  · cases recognized

/-- The two counted occurrences are exhausted by this parameter and result.
Every other NONconstant formal is therefore clear of the selected name. -/
theorem recognition_clears_other_formals (before : List (Parameter V)) (current : Parameter V)
    (after : List (Parameter V)) (authoredRange : Ty String) (resolvedRange : Ty V) (name : V)
    (recognized : recognizes before current after authoredRange resolvedRange = some name) :
    ∀ parameter ∈ before ++ after, parameter.constant = false → name ∉ parameter.resolved.vars := by
  obtain ⟨range, _guardedRange, _demand, nonconstant, formal, total⟩ :=
    recognition_fields before current after authoredRange resolvedRange name recognized
  have remaining : ((before ++ after).map (contribution name)).sum = 0 := by
    simp only [uses, range, List.map_append, List.map_cons, List.sum_append, List.sum_cons,
      contribution, nonconstant, Bool.false_eq_true, ↓reduceIte, formal, count, Ty.vars_var,
      List.count_cons_self, List.count_nil] at total ⊢
    omega
  intro parameter member ordinary
  have zero : contribution name parameter = 0 :=
    (List.sum_eq_zero_iff_forall_eq_nat.mp remaining) _ (List.mem_map.mpr ⟨parameter, member, rfl⟩)
  apply List.not_mem_of_count_eq_zero
  simpa only [contribution, ordinary, Bool.false_eq_true, ↓reduceIte, count] using zero

/-- Earlier constant instantiation must not recompute literal demand. -/
theorem instantiating_atom_does_not_make_authored_variable_raw (name : String) :
    demand (.var name) = .guarded ∧ demand (.sym "Atom") = .raw := by
  simp [demand, Unchecked]

theorem capped_small_decision (actual wanted : Nat) (small : wanted < 3) :
    min 3 actual = wanted ↔ actual = wanted := by omega

namespace Controls

def selected : Parameter := ⟨.var "a", .var "a", false⟩
def any : Parameter := ⟨.sym "%Undefined%", .sym "%Undefined%", false⟩
def constant : Parameter := ⟨arrow [.var "a"] (.sym "Nat"), arrow [.var "a"] (.sym "Nat"), true⟩

theorem isolated_pair_is_recognized :
    recognizes [any] selected [any] (.var "a") (.var "a") = some "a" := by decide +kernel

theorem repeated_parameter_occurrence_is_rejected :
    recognizes [] selected [selected] (.var "a") (.var "a") = none := by decide +kernel

/-- Exclusion from the count is not proof that the constant guard omits a.
The actual FixesClosed/constant-selector theorem is still required. -/
theorem constant_exclusion_is_not_syntactic_absence :
    recognizes [constant] selected [] (.var "a") (.var "a") = some "a" ∧
      "a" ∈ constant.resolved.vars := by
  constructor <;> decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaContractRowIsolation
