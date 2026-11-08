import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeDependencyAdmission

/-!
# Fresh type instances at individual read occurrences

The existing injective HE type-signature freshener is reused. The supply
retains caller-visible names and every previously produced type variable.
One signature uses one map, preserving its repeated-variable equations;
later reads cannot reuse that signature's variables.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSupply

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE

structure Supply where
  used : List String := []
  next : Nat := 0
  deriving DecidableEq

def remember (state : Supply) (atoms : List Atom) : Supply :=
  { state with used := atomListVariables atoms ++ state.used }

theorem remember_old (state : Supply) (atoms : List Atom) : state.used ⊆ (remember state atoms).used :=
  fun _ member => List.mem_append_right _ member

theorem remember_new (state : Supply) (atoms : List Atom) :
    atomListVariables atoms ⊆ (remember state atoms).used := fun _ member => List.mem_append_left _ member

def fresh (state : Supply) (signature : Atom) : Atom × Supply :=
  let result := instantiateTypeSignature state.used state.next signature
  (result, ⟨atomVariables result ++ state.used, state.next + 1⟩)

def freshList : Supply → List Atom → List Atom × Supply
  | state, [] => ([], state)
  | state, signature :: rest =>
      let first := fresh state signature
      let later := freshList first.2 rest
      (first.1 :: later.1, later.2)

mutual
theorem variables_rename (rename : String → String) : ∀ atom,
    atomVariables (renameAtom rename atom) = (atomVariables atom).map rename
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded _ => rfl
  | .expression children => variablesList_rename rename children
theorem variablesList_rename (rename : String → String) : ∀ atoms,
    atomListVariables (renameAtomList rename atoms) = (atomListVariables atoms).map rename
  | [] => rfl
  | atom :: atoms => by
      simp only [renameAtomList, atomListVariables, variables_rename, variablesList_rename,
        List.map_append]
end

theorem fresh_avoids (state : Supply) (signature : Atom) (name : String)
    (member : name ∈ atomVariables (fresh state signature).1) : name ∉ state.used := by
  simp only [fresh, instantiateTypeSignature, variables_rename, List.mem_map] at member
  obtain ⟨original, _, rfl⟩ := member
  exact instanceName_not_mem _ _ _ _

theorem fresh_remembers (state : Supply) (signature : Atom) :
    state.used ⊆ (fresh state signature).2.used ∧
    atomVariables (fresh state signature).1 ⊆ (fresh state signature).2.used := by
  constructor
  · exact fun _ member => List.mem_append_right _ member
  · exact fun _ member => List.mem_append_left _ member

theorem freshList_remembers (state : Supply) (signatures : List Atom) :
    state.used ⊆ (freshList state signatures).2.used := by
  induction signatures generalizing state with
  | nil => exact fun _ member => member
  | cons signature rest ih =>
      exact fun name member => ih (fresh state signature).2 ((fresh_remembers state signature).1 member)

theorem freshList_length (state : Supply) (signatures : List Atom) :
    (freshList state signatures).1.length = signatures.length := by
  induction signatures generalizing state with
  | nil => rfl
  | cons signature rest ih => simp [freshList, ih]

theorem freshList_existing (state : Supply) (signatures : List Atom) :
    (freshList state signatures).1 = instantiateTypeSignatures state.used state.next signatures := by
  induction signatures generalizing state with
  | nil => rfl
  | cons signature rest ih =>
      simpa only [freshList, fresh, instantiateTypeSignatures] using
        congrArg (instantiateTypeSignature state.used state.next signature :: ·)
          (ih (fresh state signature).2)

theorem freshList_output_remembers (state : Supply) (signatures : List Atom) :
    atomListVariables (freshList state signatures).1 ⊆ (freshList state signatures).2.used := by
  induction signatures generalizing state with
  | nil => intro name member; cases member
  | cons signature rest ih =>
      intro name member
      rcases List.mem_append.mp member with first | later
      · exact freshList_remembers (fresh state signature).2 rest ((fresh_remembers state signature).2 first)
      · exact ih (fresh state signature).2 later

theorem freshList_avoids (state : Supply) (signatures : List Atom) (name : String)
    (member : name ∈ atomListVariables (freshList state signatures).1) : name ∉ state.used := by
  induction signatures generalizing state with
  | nil => cases member
  | cons signature rest ih =>
      rcases List.mem_append.mp member with first | later
      · exact fresh_avoids state signature name first
      · intro old
        exact ih (fresh state signature).2 later ((fresh_remembers state signature).1 old)

theorem later_read_is_apart (state : Supply) (first second : Atom) (name : String)
    (earlier : name ∈ atomVariables (fresh state first).1) :
    name ∉ atomVariables (fresh (fresh state first).2 second).1 := by
  intro later
  exact fresh_avoids _ _ name later ((fresh_remembers state first).2 earlier)

theorem fresh_map_injective (state : Supply) (signature : Atom) :
    Function.Injective (instanceName state.used (atomVariables signature).eraseDups state.next) :=
  instanceName_injective _ _ _

theorem fresh_resourceFree (state : Supply) (signature : Atom) :
    TypeDependencyAdmission.resourceFree (fresh state signature).1 =
      TypeDependencyAdmission.resourceFree signature :=
  TypeDependencyAdmission.rename_resourceFree _ _

theorem freshList_resourceFree (state : Supply) (signatures : List Atom)
    (safe : TypeDependencyAdmission.resourceFreeList signatures = true) :
    TypeDependencyAdmission.resourceFreeList (freshList state signatures).1 = true := by
  induction signatures generalizing state with
  | nil => rfl
  | cons signature rest ih =>
      simp only [TypeDependencyAdmission.resourceFreeList, Bool.and_eq_true] at safe
      simp only [freshList, TypeDependencyAdmission.resourceFreeList, fresh_resourceFree]
      exact Bool.and_eq_true_iff.mpr ⟨safe.1, ih _ safe.2⟩

namespace Controls

def repeated : Atom := .expression [.symbol "Pair", .var "element", .var "element"]

theorem sharing_inside_one_instance_is_preserved (state : Supply) :
    ∃ name, (fresh state repeated).1 = .expression [.symbol "Pair", .var name, .var name] := by
  exact ⟨_, rfl⟩

theorem caller_name_is_not_captured :
    "element#0" ∉ atomVariables (fresh ⟨["element#0"], 0⟩ repeated).1 :=
  fun member => fresh_avoids _ _ _ member (by simp)

theorem equal_templates_receive_distinct_variables :
    (fresh ⟨[], 0⟩ repeated).1 ≠ (fresh (fresh ⟨[], 0⟩ repeated).2 repeated).1 := by
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSupply
