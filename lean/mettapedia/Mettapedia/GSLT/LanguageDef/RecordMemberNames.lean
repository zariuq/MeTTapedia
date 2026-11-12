import Mathlib.Logic.Function.Basic

/-!
# Record-qualified member names

Member spellings are local to a record. Instantiating a family therefore
preserves the pair of owner identity and member identity, not a global field
spelling. The laws permit different records to reuse `data` or `next` while
requiring distinct fields within each record to remain distinguishable.

This is a model of declaration-template binding. C layout, receiver typing
and executable function bodies have separate compiler checks.
-/

namespace Mettapedia.GSLT.LanguageDef.RecordMemberNames

set_option autoImplicit false

def qualify {Owner Field : Type} (recordName : Owner → String)
    (fieldName : Owner → Field → String) (member : Owner × Field) : String × String :=
  (recordName member.1, fieldName member.1 member.2)

theorem qualify_injective {Owner Field : Type} {recordName : Owner → String}
    {fieldName : Owner → Field → String}
    (records : Function.Injective recordName)
    (fields : ∀ owner, Function.Injective (fieldName owner)) :
    Function.Injective (qualify recordName fieldName) := by
  intro a b same
  obtain ⟨ao, af⟩ := a
  obtain ⟨bo, bf⟩ := b
  have owner := records (congrArg Prod.fst same)
  change ao = bo at owner
  subst bo
  have field := fields ao (congrArg Prod.snd same)
  change af = bf at field
  subst bf
  rfl

theorem distinct_owners {Owner Field : Type} {recordName : Owner → String}
    {fieldName : Owner → Field → String} (records : Function.Injective recordName)
    {a b : Owner × Field} (different : a.1 ≠ b.1) :
    qualify recordName fieldName a ≠ qualify recordName fieldName b := by
  intro same
  exact different (records (congrArg Prod.fst same))

private def records : Bool → String | false => "Cursor" | true => "Worklist"
private def fields : Bool → Bool → String
  | _, false => "data"
  | false, true => "next"
  | true, true => "len"

example : Function.Injective (qualify records fields) := by
  apply qualify_injective
  · intro a b h
    cases a <;> cases b <;> simp_all [records]
  · intro owner a b h
    cases owner <;> cases a <;> cases b <;> simp_all [fields]

example : qualify records fields (false, false) ≠ qualify records fields (true, false) := by decide

-- Dropping the owner loses identity even though each record is unambiguous.
example : fields false false = fields true false := by decide

end Mettapedia.GSLT.LanguageDef.RecordMemberNames
