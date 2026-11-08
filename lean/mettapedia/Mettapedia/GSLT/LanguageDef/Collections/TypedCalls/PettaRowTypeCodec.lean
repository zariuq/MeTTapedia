import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaContractRowIsolation
import Mettapedia.Languages.MeTTa.PeTTa.StableGroundGuardDischarge

/-!
# Row-variable isolation in the intrinsic query carrier

The row scan counts variables of finite type syntax. The intrinsic query and
caller join use first-order terms with occurrence-fresh natural coordinates.
This codec preserves those variables exactly. It therefore transports the
computed row-isolation fact to the reached caller observations, rather than
equating two type-variable carriers by convention.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaRowTypeCodec

open Mettapedia.Logic.LP (Term Subst)
open Mettapedia.Languages.MeTTa.PeTTa.IntrinsicTypeFacts (TypeTerm signature)
open PettaContractRowIsolation (Parameter recognizes)

variable {V : Type}

def encode (rename : V → Nat) : Ty V → TypeTerm
  | .var name => .var (rename name)
  | .sym name => .const (.symbol name)
  | .app children => .app (children.length : Nat)
      (fun index => encode rename (children.get index))
termination_by type => sizeOf type
decreasing_by
  have := List.sizeOf_lt_of_mem (List.get_mem children index)
  simp only [Ty.app.sizeOf_spec]
  omega

theorem encoded_variable_iff (rename : V → Nat) (type : Ty V) (name : Nat) :
    name ∈ (encode rename type).freeVars ↔ ∃ source ∈ type.vars, rename source = name := by
  cases type with
  | var source => simp [encode, Term.freeVars, Ty.vars_var, eq_comm]
  | sym symbol => simp [encode, Term.freeVars, Ty.vars_sym]
  | app children =>
      rw [encode, Term.mem_freeVars_app (σ := signature)]
      simp only [Ty.vars_app, List.mem_flatMap]
      constructor
      · rintro ⟨index, present⟩
        obtain ⟨source, occurs, same⟩ :=
          (encoded_variable_iff rename (children.get index) name).mp present
        exact ⟨source, ⟨children.get index, List.get_mem children index, occurs⟩, same⟩
      · rintro ⟨source, ⟨child, present, occurs⟩, same⟩
        obtain ⟨index, rfl⟩ := List.mem_iff_get.mp present
        exact ⟨index, (encoded_variable_iff rename (children.get index) name).mpr ⟨source, occurs, same⟩⟩
termination_by sizeOf type
decreasing_by
  all_goals
    have := List.sizeOf_lt_of_mem (List.get_mem children index)
    simp only [Ty.app.sizeOf_spec]
    omega

theorem encode_preserves_clear (rename : V → Nat) (injective : Function.Injective rename)
    (type : Ty V) (name : V) (clear : name ∉ type.vars) :
    rename name ∉ (encode rename type).freeVars := by
  intro present
  obtain ⟨source, occurs, same⟩ := (encoded_variable_iff rename type (rename name)).mp present
  exact clear (injective same ▸ occurs)

theorem encoded_instantiation {W : Type} (sourceNames : V → Nat) (residualNames : W → Nat)
    (instance_ : V → Ty W) (caller : Subst signature)
    (reads : ∀ name, caller (sourceNames name) = encode residualNames (instance_ name))
    (type : Ty V) :
    caller.applyTerm (encode sourceNames type) = encode residualNames (type.bind instance_) := by
  cases type with
  | var name => simpa only [encode, Subst.applyTerm, Ty.bind_var'] using reads name
  | sym symbol => simp only [Ty.bind_sym, encode, Subst.applyTerm]
  | app children =>
      rw [Ty.bind_app]
      simp only [encode, Subst.applyTerm]
      congr 1 <;> try simp only [List.length_map]
      apply Function.hfunext (by simp only [List.length_map])
      intro index other same
      apply heq_of_eq
      simp only [List.get_eq_getElem, List.getElem_map]
      have sameValue := Fin.val_eq_val_of_heq same
      simpa only [List.get_eq_getElem, ← sameValue] using
        encoded_instantiation sourceNames residualNames instance_ caller reads (children.get index)
termination_by sizeOf type
decreasing_by
  have := List.sizeOf_lt_of_mem (List.get_mem children index)
  simp only [Ty.app.sizeOf_spec]
  omega

theorem ground_encoding_iff (rename : V → Nat) (type : Ty V) :
    (encode rename type).isGround ↔ type.vars = [] := by
  rw [Term.isGround_iff_freeVars_empty (σ := signature),
    Finset.eq_empty_iff_forall_notMem, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro empty source present
    exact empty (rename source) ((encoded_variable_iff rename type (rename source)).mpr ⟨source, present, rfl⟩)
  · intro empty name present
    obtain ⟨source, occurs, _⟩ := (encoded_variable_iff rename type name).mp present
    exact empty source occurs

variable [DecidableEq V] [BEq V] [LawfulBEq V]

/-- The native two-occurrence decision earns independence of every other
nonconstant request in the actual query carrier. Constant requests use their
separate effective-query and residual-instance theorem. -/
theorem recognized_pair_clears_encoded_requests
    (before : List (Parameter V)) (current : Parameter V) (after : List (Parameter V))
    (authoredRange : Ty String) (resolvedRange : Ty V) (name : V)
    (recognized : recognizes before current after authoredRange resolvedRange = some name)
    (rename : V → Nat) (injective : Function.Injective rename) :
    ∀ parameter ∈ before ++ after, parameter.constant = false →
      rename name ∉ (encode rename parameter.resolved).freeVars := by
  intro parameter present ordinary
  exact encode_preserves_clear rename injective parameter.resolved name
    (PettaContractRowIsolation.recognition_clears_other_formals before current after
      authoredRange resolvedRange name recognized parameter present ordinary)

/-- The reached caller read is explicit: absence in authored syntax alone
does not exclude an alias into this private type variable. -/
theorem recognized_pair_preserves_reached_requests
    (before : List (Parameter V)) (current : Parameter V) (after : List (Parameter V))
    (authoredRange : Ty String) (resolvedRange : Ty V) (name : V)
    (recognized : recognizes before current after authoredRange resolvedRange = some name)
    (rename : V → Nat) (injective : Function.Injective rename)
    (caller : Subst signature) (request : Parameter V → TypeTerm)
    (reached : ∀ parameter ∈ before ++ after, parameter.constant = false →
      caller.applyTerm (request parameter) = encode rename parameter.resolved)
    (replacement : TypeTerm) :
    ∀ parameter ∈ before ++ after, parameter.constant = false →
      (Subst.comp (Subst.single (rename name) replacement) caller).applyTerm (request parameter) =
        caller.applyTerm (request parameter) := by
  intro parameter present ordinary
  rw [Subst.applyTerm_comp, reached parameter present ordinary]
  apply Subst.applyTerm_eq_self
  intro other occurs
  exact Subst.single_ne replacement (fun same =>
    recognized_pair_clears_encoded_requests before current after authoredRange resolvedRange name
      recognized rename injective parameter present ordinary (same ▸ occurs))

theorem recognized_pair_preserves_source_requests
    (before : List (Parameter V)) (current : Parameter V) (after : List (Parameter V))
    (authoredRange : Ty String) (resolvedRange : Ty V) (name : V)
    (recognized : recognizes before current after authoredRange resolvedRange = some name)
    (sourceNames : String → Nat) (residualNames : V → Nat)
    (injective : Function.Injective residualNames) (instance_ : String → Ty V)
    (caller : Subst signature)
    (reads : ∀ name, caller (sourceNames name) = encode residualNames (instance_ name))
    (resolved : ∀ parameter ∈ before ++ after, parameter.constant = false →
      parameter.authored.bind instance_ = parameter.resolved)
    (replacement : TypeTerm) :
    ∀ parameter ∈ before ++ after, parameter.constant = false →
      (Subst.comp (Subst.single (residualNames name) replacement) caller).applyTerm
          (encode sourceNames parameter.authored) =
        caller.applyTerm (encode sourceNames parameter.authored) := by
  apply recognized_pair_preserves_reached_requests before current after authoredRange resolvedRange
    name recognized residualNames injective caller (fun parameter => encode sourceNames parameter.authored)
  intro parameter present ordinary
  rw [encoded_instantiation sourceNames residualNames instance_ caller reads,
    resolved parameter present ordinary]

namespace Controls

theorem coordinate_collision_invalidates_syntactic_clearance :
    (0 : Nat) ∉ (Ty.var 1 : Ty Nat).vars ∧
      (0 : Nat) ∈ (encode (fun _ : Nat => 0) (.var 1)).freeVars := by
  constructor <;> decide +kernel

theorem reached_alias_invalidates_authored_clearance :
    (0 : Nat) ∉ (encode id (.var 1)).freeVars ∧
      (Subst.comp (Subst.single (σ := signature) 0 (.const (.symbol "Number")))
        (Subst.single (σ := signature) 1 (.var 0))).applyTerm (encode id (.var 1)) ≠
      (Subst.single (σ := signature) 1 (.var 0)).applyTerm (encode id (.var 1)) := by
  constructor
  · decide +kernel
  · simp [encode, Subst.comp, Subst.single]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaRowTypeCodec
