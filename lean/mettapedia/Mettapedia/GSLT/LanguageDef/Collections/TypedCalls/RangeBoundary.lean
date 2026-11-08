import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol

/-!
# Transport of open ranges across a call boundary

Equal range syntax does not imply equal instantiated ranges. The exact
information an inherited range needs is agreement on its variable support.
For the free type-term grammar, this condition is also necessary. Passing an
argument at the same instantiated formal transfers the required agreement
when that formal contains every variable of the range.

These laws state the missing obligation for open-range elision. They do not
assert that a native call-site analysis already establishes it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RangeBoundary

variable {V W : Type}

/-- In a free type term, equality of its instances determines every variable
that actually occurs, not the unused part of either environment. -/
theorem agree_of_bind_eq {left right : V → Ty W} : ∀ term : Ty V,
    term.bind left = term.bind right → ∀ v ∈ term.vars, left v = right v
  | .var x, equal, v, member => by
      have same : v = x := by simpa using member
      subst v
      exact equal
  | .sym _, _, _, member => by simp at member
  | .app terms, equal, v, member => by
      rw [Ty.bind_app, Ty.bind_app] at equal
      have children := List.map_inj_left.mp (Ty.app.inj equal)
      obtain ⟨child, present, occurs⟩ := List.mem_flatMap.mp (by simpa using member)
      exact agree_of_bind_eq child (children child present) v occurs

theorem bind_eq_iff_agree (range : Ty V) (caller callee : V → Ty W) :
    range.bind caller = range.bind callee ↔
      ∀ v ∈ range.vars, caller v = callee v :=
  ⟨agree_of_bind_eq range, Ty.bind_congr range⟩

/-- A forwarded argument's instantiated formal can carry the whole return
obligation. Unused bindings need not be copied or compared. -/
theorem range_from_formal (formal range : Ty V) (caller callee : V → Ty W)
    (covered : ∀ v ∈ range.vars, v ∈ formal.vars)
    (sameArgumentType : formal.bind caller = formal.bind callee) :
    range.bind caller = range.bind callee :=
  Ty.bind_congr range fun v occurs =>
    agree_of_bind_eq formal sameArgumentType v (covered v occurs)

/-- Several arguments may jointly determine the return range. -/
theorem range_from_formals (formals : List (Ty V)) (range : Ty V)
    (caller callee : V → Ty W)
    (covered : ∀ v ∈ range.vars,
      ∃ formal ∈ formals, v ∈ formal.vars)
    (sameArgumentTypes : ∀ formal ∈ formals, formal.bind caller = formal.bind callee) :
    range.bind caller = range.bind callee := by
  apply Ty.bind_congr
  intro v occurs
  obtain ⟨formal, present, included⟩ := covered v occurs
  exact agree_of_bind_eq formal (sameArgumentTypes formal present) v included

/-- Transport preserves the actual result guard's complete answer bag,
including duplicate derivations. Its internal stores are not exported. -/
theorem inherited_result_guard (decls : Decls)
    (kind : Mettapedia.Languages.MeTTa.OSLFCore.Atom → String)
    (formal range : Ty V) (caller callee : V → Ty Empty)
    (covered : ∀ v ∈ range.vars, v ∈ formal.vars)
    (sameArgumentType : formal.bind caller = formal.bind callee)
    (position : Nat) (store : List (Eqn CallVar))
    (answer : Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    resultGuard decls kind position (range.bind caller).lift store answer =
      resultGuard decls kind position (range.bind callee).lift store answer := by
  rw [range_from_formal formal range caller callee covered sameArgumentType]

namespace Controls

def listRange : Ty String := .app [.sym "List", .var "a"]
def numbers : String → Ty Empty := fun _ => .sym "Number"
def strings : String → Ty Empty := fun _ => .sym "String"

/-- Identical open syntax can denote different caller and callee ranges. -/
theorem same_syntax_different_instances :
    listRange.bind numbers ≠ listRange.bind strings := by decide

def forwarded : Ty String := .app [.sym "Pair", .var "a", .var "b"]
def caller : String → Ty Empty := fun name =>
  if name = "a" then .sym "Number" else .sym "String"
def sameNeeded : String → Ty Empty := fun name =>
  if name = "a" then .sym "Number" else .sym "Bool"

/-- Bindings outside the range's support may differ harmlessly. -/
theorem unrelated_bindings_need_not_agree :
    listRange.bind caller = listRange.bind sameNeeded ∧ caller "b" ≠ sameNeeded "b" := by
  constructor
  · decide
  · decide

/-- Checking a formal that does not mention the range variable supplies no
return information, even though both formal instances agree. -/
theorem uncovered_variable_breaks_transport :
    (Ty.sym "Number" : Ty String).bind numbers = (Ty.sym "Number").bind strings ∧
      listRange.bind numbers ≠ listRange.bind strings := by
  exact ⟨rfl, same_syntax_different_instances⟩

/-- A concrete forwarded structural formal determines its list range. -/
theorem forwarded_pair_determines_range (left right : String → Ty Empty)
    (same : forwarded.bind left = forwarded.bind right) :
    listRange.bind left = listRange.bind right := by
  apply range_from_formal forwarded listRange left right _ same
  intro v member
  have same : v = "a" := by simpa [listRange] using member
  simp [forwarded, same]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RangeBoundary
