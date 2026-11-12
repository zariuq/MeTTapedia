import Mathlib.Data.List.Basic

/-!
# Development laws for Cesta record-visitor contracts

The model concerns the added declarations: complete field classification,
nominal owner-role compatibility and visitor access. Native policy behavior,
C declaration projection, generated C execution and collector root discovery
remain separate boundaries. Cesta never loads this development module.
-/

namespace Mettapedia.GSLT.LanguageDef.RecordVisitors

set_option autoImplicit false

inductive Storage where
  | value | borrow | own
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure Declaration where
  name : String
  reference : Bool
  deriving DecidableEq, Repr

structure Policy where
  name : String
  owner : String
  write : Bool
  address : Bool
  counted : Bool
  obligation : String
  deriving DecidableEq, Repr

structure Field where
  name : String
  storage : Storage
  owner : String
  write : Bool
  visitor : Option String
  keep : Bool
  counted : Bool
  deriving DecidableEq, Repr

structure Environment where
  owners : List String
  policies : List Policy

structure Record where
  declarations : List Declaration
  fields : List Field
  write : Bool

def uniqueNames : List String → Bool
  | [] => true
  | name :: names => !names.contains name && uniqueNames names

theorem uniqueNames_iff (names : List String) : uniqueNames names = true ↔ names.Nodup := by
  induction names with
  | nil => simp [uniqueNames]
  | cons name names ih => simp [uniqueNames, List.nodup_cons, ih]

def lookupPolicy : List Policy → String → Option Policy
  | [], _ => none
  | p :: ps, name => if p.name == name then some p else lookupPolicy ps name

def checkPolicy (write : Bool) (f : Field) (p : Policy) : Bool :=
  (f.owner == p.owner) &&
  (!p.write || (write && f.storage != .own && (p.address || f.write))) &&
  (f.counted == p.counted)

def checkField (e : Environment) (write : Bool) (d : Declaration) (f : Field) : Bool :=
  (d.name == f.name) && (d.reference == (f.storage != .value)) &&
  if f.storage == .value then f.owner.isEmpty && f.visitor.isNone && !f.keep && !f.counted
  else e.owners.any (· == f.owner) &&
    match f.visitor with
    | none => f.keep && !f.counted
    | some name => match lookupPolicy e.policies name with
      | none => false
      | some p => checkPolicy write f p

def checkEnvironment (e : Environment) : Bool :=
  uniqueNames e.owners && uniqueNames (e.policies.map Policy.name) &&
  e.policies.all fun p => e.owners.any (· == p.owner) && !p.obligation.isEmpty

def checkRecord (e : Environment) (r : Record) : Bool :=
  checkEnvironment e && uniqueNames (r.declarations.map Declaration.name) &&
  uniqueNames (r.fields.map Field.name) &&
  r.declarations.all (fun d => r.fields.any fun f => checkField e r.write d f) &&
  r.fields.all (fun f => r.declarations.any fun d => d.name == f.name)

theorem checkPolicy_owner {write : Bool} {f : Field} {p : Policy}
    (accepted : checkPolicy write f p = true) : f.owner = p.owner := by
  simp only [checkPolicy, Bool.and_eq_true, beq_iff_eq] at accepted
  exact accepted.1.1

theorem checkPolicy_mutation {write : Bool} {f : Field} {p : Policy}
    (accepted : checkPolicy write f p = true) (mutates : p.write = true) :
    write = true ∧ f.storage ≠ .own ∧ (p.address = true ∨ f.write = true) := by
  simp [checkPolicy, mutates] at accepted
  exact ⟨accepted.1.2.1.1, accepted.1.2.1.2, accepted.1.2.2⟩

theorem read_receiver_refuses_mutation {f : Field} {p : Policy}
    (mutates : p.write = true) : checkPolicy false f p = false := by
  simp [checkPolicy, mutates]

theorem owning_field_refuses_mutation {write : Bool} {f : Field} {p : Policy}
    (owns : f.storage = .own) (mutates : p.write = true) : checkPolicy write f p = false := by
  simp [checkPolicy, owns, mutates]

theorem checkField_name {e : Environment} {write : Bool} {d : Declaration} {f : Field}
    (accepted : checkField e write d f = true) : d.name = f.name := by
  simp only [checkField, Bool.and_eq_true, beq_iff_eq] at accepted
  exact accepted.1.1

theorem checkField_owner {e : Environment} {write : Bool} {d : Declaration} {f : Field}
    (accepted : checkField e write d f = true) (reference : d.reference = true) :
    f.owner ∈ e.owners := by
  cases storage : f.storage <;> simp_all [checkField, List.any_eq_true]

theorem admitted_unique_fields {e : Environment} {r : Record}
    (accepted : checkRecord e r = true) : (r.fields.map Field.name).Nodup := by
  simp only [checkRecord, Bool.and_eq_true, uniqueNames_iff] at accepted
  exact accepted.1.1.2

theorem admitted_field_coverage {e : Environment} {r : Record}
    (accepted : checkRecord e r = true) {d : Declaration} (declared : d ∈ r.declarations) :
    ∃ f ∈ r.fields, d.name = f.name ∧ checkField e r.write d f = true := by
  have covered : r.declarations.all (fun d => r.fields.any fun f => checkField e r.write d f) = true := by
    simp only [checkRecord, Bool.and_eq_true] at accepted
    exact accepted.1.2
  obtain ⟨f, member, valid⟩ := List.any_eq_true.mp (List.all_eq_true.mp covered d declared)
  exact ⟨f, member, checkField_name valid, valid⟩

theorem admitted_no_extra_fields {e : Environment} {r : Record}
    (accepted : checkRecord e r = true) {f : Field} (classified : f ∈ r.fields) :
    ∃ d ∈ r.declarations, d.name = f.name := by
  simp only [checkRecord, Bool.and_eq_true] at accepted
  obtain ⟨d, member, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp accepted.2 f classified)
  exact ⟨d, member, by simpa using same⟩

theorem admitted_reference_owner {e : Environment} {r : Record}
    (accepted : checkRecord e r = true) {d : Declaration}
    (declared : d ∈ r.declarations) (reference : d.reference = true) :
    ∃ f ∈ r.fields, d.name = f.name ∧ f.owner ∈ e.owners := by
  obtain ⟨f, member, same, valid⟩ := admitted_field_coverage accepted declared
  exact ⟨f, member, same, checkField_owner valid reference⟩

private def atoms : Policy := ⟨"move", "atoms", true, true, false,
  "Native relocation preserves sharing and obeys the declared owner role."⟩
private def environment : Environment := ⟨["atoms", "episode"], [atoms]⟩
private def left : Field := ⟨"left", .borrow, "atoms", false, some "move", false, false⟩
private def right : Field := { left with name := "right" }
private def pair : Record := ⟨[⟨"left",true⟩, ⟨"right",true⟩], [left,right], true⟩

theorem shared_borrows_admitted : checkRecord environment pair = true := by decide
theorem missing_field_refused : checkRecord environment { pair with fields := [left] } = false := by decide
theorem duplicate_field_refused : checkRecord environment { pair with fields := [left,left] } = false := by decide
theorem wrong_owner_refused :
    checkRecord environment { pair with fields := [{left with owner := "episode"},right] } = false := by decide
theorem read_receiver_refused : checkRecord environment { pair with write := false } = false := by decide
theorem owning_mutation_refused :
    checkRecord environment { pair with fields := [{left with storage := .own},right] } = false := by decide

end Mettapedia.GSLT.LanguageDef.RecordVisitors
