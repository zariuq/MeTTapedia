import Mettapedia.Languages.HOLLight.MeTTa.DeclarationTable
import Mettapedia.Languages.OpenTheory.SyntaxEncoding

/-!
# Existing finite declaration tables recover the exact source signature

Full structural symbols, including definition provenance, are the lookup
keys. The registered/complete fields of the original finite table owners
prove equality with the original function-valued signature. No printed-name
guess or replay of declaration history is needed to recover that function.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteSignatureLookup

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.MeTTa

variable {A B : Type*} [DecidableEq A]

def rowLookup (key : A) : List (A × B) → Option B
  | [] => none
  | (candidate, value) :: rest => if candidate = key then some value else rowLookup key rest

theorem rowLookup_member {key : A} {value : B} {rows : List (A × B)}
    (found : rowLookup key rows = some value) : (key, value) ∈ rows := by
  induction rows with
  | nil => simp [rowLookup] at found
  | cons first rest earlier =>
      obtain ⟨candidate, result⟩ := first
      by_cases same : candidate = key
      · simp only [rowLookup, if_pos same, Option.some.injEq] at found
        subst candidate
        subst value
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (earlier (by simpa [rowLookup, same] using found))

theorem rowLookup_of_consistent_member {key : A} {value : B} {rows : List (A × B)}
    (consistent : ∀ first ∈ rows, ∀ second ∈ rows, first.1 = second.1 → first.2 = second.2)
    (member : (key, value) ∈ rows) : rowLookup key rows = some value := by
  induction rows with
  | nil => simp at member
  | cons first rest earlier =>
      obtain ⟨candidate, result⟩ := first
      by_cases same : candidate = key
      · have sameValue := consistent (candidate, result) (List.mem_cons_self ..) (key, value) member same
        simp only [rowLookup, if_pos same]
        exact congrArg some sameValue
      · have remaining : (key, value) ∈ rest := by
          rcases List.mem_cons.mp member with equal | selected
          · exact False.elim (same (congrArg Prod.fst equal).symm)
          · exact selected
        have restConsistent : ∀ first ∈ rest, ∀ second ∈ rest, first.1 = second.1 → first.2 = second.2 :=
          fun first firstMember second secondMember =>
            consistent first (List.mem_cons_of_mem _ firstMember) second (List.mem_cons_of_mem _ secondMember)
        simpa [rowLookup, same] using earlier restConsistent remaining

theorem rowLookup_exact_at : ∀ (rows : List (A × B)) (source : A → Option B) (key : A),
    (∀ entry ∈ rows, source entry.1 = some entry.2) →
    (∀ value, source key = some value → (key, value) ∈ rows) →
    rowLookup key rows = source key
  | [], source, key, _, complete => by
      cases known : source key with
      | none => rfl
      | some value => exact False.elim (by simpa using complete value known)
  | (candidate, result) :: rest, source, key, registered, complete => by
      by_cases same : candidate = key
      · simp only [rowLookup, if_pos same]
        exact (same ▸ registered (candidate, result) (List.mem_cons_self ..)).symm
      · simp only [rowLookup, if_neg same]
        apply rowLookup_exact_at rest source key
        · intro entry member
          exact registered entry (List.mem_cons_of_mem _ member)
        · intro value found
          rcases List.mem_cons.mp (complete value found) with first | remaining
          · exact False.elim (same (congrArg Prod.fst first).symm)
          · exact remaining

theorem rowLookup_exact (rows : List (A × B)) (source : A → Option B)
    (registered : ∀ entry ∈ rows, source entry.1 = some entry.2)
    (complete : ∀ key value, source key = some value → (key, value) ∈ rows) :
    (fun key => rowLookup (A := A) (B := B) key rows) = source := by
  funext key
  exact rowLookup_exact_at rows source key registered (complete key)

local instance : DecidableEq TypeOp := SyntaxEncoding.typeOpCodec.decEq
local instance : DecidableEq Const := SyntaxEncoding.constantCodec.decEq

theorem operator_table_exact {context : TheoryContext} (table : OperatorTable.Table context) :
    (fun key => rowLookup key table.entries) = context.signature.typeOperators :=
  rowLookup_exact table.entries context.signature.typeOperators table.registered table.complete

theorem constant_table_exact {context : TheoryContext} (table : DeclarationTable.Table context) :
    (fun key => rowLookup key table.constants) = context.signature.constants :=
  rowLookup_exact table.constants context.signature.constants table.registered table.complete

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteSignatureLookup
