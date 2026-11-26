import Mettapedia.Languages.MeTTa.Seal.NativeContract
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaImportProtection
import Mettapedia.Languages.MeTTa.SpaceTheory.HETypeQueries
import Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations
import Mettapedia.Languages.MeTTa.SpaceTheory.ModuleReferences

/-!
# Authority to change the declarations of a MeTTa head

The seal belongs to a head of an instance, not to its spelling in an
importer. A holder must offer a sealing facet of the designated brand,
not merely a name, a box, or the opening facet. A proposal is an atomic
substitution of one block of atoms for another in the current space.

This policy conservatively includes open definitions, subtyping and
equations in each potentially affected head. Data remains separate.
It preserves the indicated declaration observations, not every
evaluation that eventually invokes that head.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HeadSealing

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.Seal (Brand Rights Val Config)
open Atoms (Content classify)

/-- Definition/type observations of a name; an open declaration is
not assigned to a made-up disjoint name. Ordinary data is not covered. -/
def concerns (head : String) (atom : Atom) : Bool :=
  let tag := classify atom
  match tag.kind with
  | .data => false
  | _ => match tag.head with
    | none => true
    | some name => name == head

def projection (head : String) (atoms : List Atom) : List Atom :=
  atoms.filter (concerns head)

structure Address (Instance : Type*) where
  instanceId : Instance
  head : String
  deriving DecidableEq

def Address.atReference {Instance : Type*} (view : ModuleReferences.Reference Instance) (name : String) :
    Address Instance := ⟨view.instanceId, view.names.symm name⟩

theorem renaming_keeps_address {Instance : Type*} (view : ModuleReferences.Reference Instance)
    (names : Equiv.Perm String) (name : String) :
    Address.atReference (view.rename names) (names name) = Address.atReference view name := by
  simp [Address.atReference, ModuleReferences.Reference.rename]

structure Registry (Instance : Type*) where
  brand : Address Instance → Option Brand
  separate : ∀ {first second b}, brand first = some b → brand second = some b → first = second

def Registry.one {Instance : Type*} [DecidableEq Instance] (address : Address Instance) (brand : Brand) :
    Registry Instance where
  brand := fun where_ => if where_ = address then some brand else none
  separate := by
    intro a b token left right
    by_cases first : a = address <;> by_cases second : b = address <;>
      simp_all

theorem Registry.one_exact {Instance : Type*} [DecidableEq Instance] {address other : Address Instance}
    {brand token : Brand} :
    (Registry.one address brand).brand other = some token ↔ other = address ∧ brand = token := by
  by_cases same : other = address <;> simp [Registry.one, same]

/-- The evidence belongs to the caller's actual holdings. The local
host designates the seal right of this brand as its write facet. -/
def OffersWrite (authority : Config Atom) (caller : Nat) (offered : List Nat) (brand : Brand) : Prop :=
  ∃ slot ∈ offered, ∃ rights, authority.held caller slot = some (.cap brand rights) ∧ rights.sealRight = true

theorem offered_cap {authority : Config Atom} {caller : Nat} {offered : List Nat} {brand : Brand}
    (proof : OffersWrite authority caller offered brand) : authority.anyCap brand Rights.sealRight := by
  obtain ⟨slot, _, rights, held, allowed⟩ := proof
  exact ⟨caller, .cap brand rights, Config.mem_of_held held, ⟨rfl, allowed⟩⟩

open Mettapedia.Languages.MeTTa.Seal in
theorem native_offer_exact (authority : NativeContract.Config Atom) (caller : Nat) (slots : List Nat) (brand : Brand) :
    OffersWrite authority.erase caller slots brand ↔
      ∃ slot ∈ slots, ∃ rights, authority.held caller slot = some (.cap brand rights) ∧ rights.sealRight = true := by
  constructor
  · rintro ⟨slot, member, rights, held, enabled⟩
    rw [NativeContract.Config.erase_held] at held
    obtain ⟨native, supplied, erased⟩ := Option.map_eq_some_iff.mp held
    cases native <;> simp only [NativeContract.Value.erase, Val.cap.injEq] at erased
    all_goals try contradiction
    obtain ⟨rfl, rfl⟩ := erased
    exact ⟨slot, member, _, supplied, enabled⟩
  · rintro ⟨slot, member, rights, held, enabled⟩
    exact ⟨slot, member, rights, by rw [NativeContract.Config.erase_held, held]; rfl, enabled⟩

/-- A block replacement identifies occurrences by their surroundings,
not by collapsing equal atoms into one element of a set. -/
structure Edit (Instance : Type*) where
  instanceId : Instance
  earlier : List Atom
  removed : List Atom
  inserted : List Atom
  later : List Atom
  deriving DecidableEq

abbrev Spaces (Instance : Type*) := Instance → List Atom

def Edit.expected {Instance : Type*} (edit : Edit Instance) : List Atom :=
  edit.earlier ++ edit.removed ++ edit.later

def Edit.replacement {Instance : Type*} (edit : Edit Instance) : List Atom :=
  edit.earlier ++ edit.inserted ++ edit.later

def Edit.touches {Instance : Type*} (edit : Edit Instance) (head : String) : Prop :=
  ∃ atom ∈ edit.removed ++ edit.inserted, concerns head atom = true

def Applied {Instance : Type*} [DecidableEq Instance] (edit : Edit Instance)
    (before after : Spaces Instance) : Prop :=
  before edit.instanceId = edit.expected ∧ after = Function.update before edit.instanceId edit.replacement

def Allowed {Instance : Type*} (seals : Registry Instance) (authority : Config Atom)
    (caller : Nat) (offered : List Nat) (edit : Edit Instance) : Prop :=
  ∀ h brand, seals.brand ⟨edit.instanceId, h⟩ = some brand → edit.touches h →
    OffersWrite authority caller offered brand

def LocalWrite {Instance : Type*} [DecidableEq Instance] (seals : Registry Instance) (authority : Config Atom)
    (caller : Nat) (offered : List Nat) (edit : Edit Instance) (before after : Spaces Instance) : Prop :=
  Allowed seals authority caller offered edit ∧ Applied edit before after

theorem no_facet_refuses {Instance : Type*} [DecidableEq Instance]
    {seals : Registry Instance} {authority : Config Atom} {caller : Nat} {offered : List Nat}
    {edit : Edit Instance} {before after : Spaces Instance} {h : String} {brand : Brand}
    (sealed : seals.brand ⟨edit.instanceId, h⟩ = some brand) (changes : edit.touches h)
    (absent : ¬OffersWrite authority caller offered brand) :
    ¬LocalWrite seals authority caller offered edit before after :=
  fun step => absent (step.1 h brand sealed changes)

theorem two_seals_need_distinct_offers {Instance : Type*}
    {seals : Registry Instance} {authority : Config Atom} {caller : Nat} {offered : List Nat}
    {edit : Edit Instance} {first second : String} {firstBrand secondBrand : Brand}
    (apart : first ≠ second)
    (one : seals.brand ⟨edit.instanceId, first⟩ = some firstBrand)
    (two : seals.brand ⟨edit.instanceId, second⟩ = some secondBrand)
    (touchesFirst : edit.touches first) (touchesSecond : edit.touches second)
    (permitted : Allowed seals authority caller offered edit) :
    ∃ left ∈ offered, ∃ right ∈ offered, left ≠ right := by
  obtain ⟨left, hasLeft, lRight, readLeft, _⟩ := permitted first firstBrand one touchesFirst
  obtain ⟨right, hasRight, rRight, readRight, _⟩ := permitted second secondBrand two touchesSecond
  refine ⟨left, hasLeft, right, hasRight, ?_⟩
  rintro rfl
  have same := (Val.cap.inj (Option.some.inj (readLeft.symm.trans readRight))).1
  have sameAddress := seals.separate one (same.symm ▸ two)
  exact apart (congrArg Address.head sameAddress)

theorem successful_write_is_from_existing_authority {Instance : Type*} [DecidableEq Instance]
    {seals : Registry Instance} {old authority : Config Atom}
    {policy : Mettapedia.Languages.MeTTa.Seal.Policy Atom} {caller : Nat} {offered : List Nat}
    {edit : Edit Instance} {before after : Spaces Instance} {h : String} {brand : Brand}
    (run : Mettapedia.Languages.MeTTa.Seal.Reach policy old authority) (issued : brand < old.nextBrand)
    (sealed : seals.brand ⟨edit.instanceId, h⟩ = some brand) (changes : edit.touches h)
    (step : LocalWrite seals authority caller offered edit before after) :
    old.anyCap brand Rights.sealRight :=
  Mettapedia.Languages.MeTTa.Seal.anyCap_of_reach .sealing run issued
    (offered_cap (step.1 h brand sealed changes))

private theorem empty_filter_of_rejected {A : Type*} (test : A → Bool) (atoms : List A)
    (rejected : ∀ a ∈ atoms, test a ≠ true) : atoms.filter test = [] := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
    have no : test atom = false := Bool.eq_false_iff.mpr (rejected atom List.mem_cons_self)
    have rest := ih fun a present => rejected a (List.mem_cons_of_mem _ present)
    simp only [List.filter_cons, no, Bool.false_eq_true, if_false, rest]

theorem silent_edit_keeps_projection {Instance : Type*} {edit : Edit Instance} {h : String}
    (silent : ¬edit.touches h) : projection h edit.expected = projection h edit.replacement := by
  have removed := empty_filter_of_rejected (concerns h) edit.removed fun atom found reports =>
    silent ⟨atom, List.mem_append_left _ found, reports⟩
  have inserted := empty_filter_of_rejected (concerns h) edit.inserted fun atom found reports =>
    silent ⟨atom, List.mem_append_right _ found, reports⟩
  simp only [projection, Edit.expected, Edit.replacement, List.filter_append, removed, inserted]

theorem no_facet_keeps_projection {Instance : Type*} [DecidableEq Instance]
    {seals : Registry Instance} {authority : Config Atom} {caller : Nat} {offered : List Nat}
    {edit : Edit Instance} {before after : Spaces Instance} {address : Address Instance} {brand : Brand}
    (sealed : seals.brand address = some brand) (absent : ¬OffersWrite authority caller offered brand)
    (step : LocalWrite seals authority caller offered edit before after) :
    projection address.head (before address.instanceId) = projection address.head (after address.instanceId) := by
  obtain ⟨permitted, fresh, rfl⟩ := step
  by_cases same : address.instanceId = edit.instanceId
  · have sealThere : seals.brand ⟨edit.instanceId, address.head⟩ = some brand := by
      rcases address with ⟨home, head⟩
      change home = _ at same
      subst home
      exact sealed
    have silent : ¬edit.touches address.head :=
      fun touches => absent (permitted address.head brand sealThere touches)
    rw [same, fresh, Function.update_self]
    exact silent_edit_keeps_projection silent
  · rw [Function.update_of_ne same]

theorem no_facet_path_keeps_projection {Instance : Type*} [DecidableEq Instance]
    {seals : Registry Instance} {address : Address Instance} {brand : Brand} {start finish : Spaces Instance}
    (sealed : seals.brand address = some brand)
    (path : Relation.ReflTransGen (fun before after =>
      ∃ authority : Config Atom, ∃ caller offered edit,
        ¬OffersWrite authority caller offered brand ∧ LocalWrite seals authority caller offered edit before after)
      start finish) :
    projection address.head (start address.instanceId) = projection address.head (finish address.instanceId) := by
  induction path with
  | refl => rfl
  | tail _ step ih =>
    obtain ⟨_, _, _, _, absent, lands⟩ := step
    exact ih.trans (no_facet_keeps_projection sealed absent lands)

private theorem equation_concerns_all (pref : Atoms.Preference) (left right : Atom) (rest : List Atom)
    (head : String) : concerns head (Content.equation pref left right rest).syntax = true := by
  cases pref <;> rfl

theorem eq_of_projections {first second : List Atom} {h : String}
    (same : projection h first = projection h second) (a b : Atom) :
    AtomEquations.Equivalent first a b ↔ AtomEquations.Equivalent second a b := by
  have preserves (one other : List Atom) (reads : projection h one = projection h other)
      (x y : Atom) (written : AtomEquations.Generator one x y) : AtomEquations.Equivalent other x y := by
    obtain ⟨pref, next, rest, present, member⟩ := written
    have retained : (Content.equation pref x next rest).syntax ∈ projection h one :=
      List.mem_filter.mpr ⟨present, equation_concerns_all pref x next rest h⟩
    rw [reads] at retained
    exact AtomEquations.authored ⟨pref, next, rest, (List.mem_filter.mp retained).1, member⟩
  exact ⟨AtomEquations.least first (AtomEquations.setoid second) (preserves first second same)
      (fun c _ _ eq => AtomEquations.fill_equivalent c eq),
    AtomEquations.least second (AtomEquations.setoid first) (preserves second first same.symm)
      (fun c _ _ eq => AtomEquations.fill_equivalent c eq)⟩

section Queries

open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (annotationType? annotationType?_eq_some_iff)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval (scopedTypeLookup)
open Mettapedia.Languages.MeTTa.PeTTa
open PeTTaExecution (programAt)
open PeTTaImportProtection (view definitions assignments formalFor)

private theorem filterMap_keeps_answers {A B : Type*} (test : A → Bool) (read : A → Option B)
    (atoms : List A) (included : ∀ a b, read a = some b → test a = true) :
    (atoms.filter test).filterMap read = atoms.filterMap read := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    cases retained : test atom with
    | true => simp only [List.filter_cons, retained, if_true, List.filterMap_cons, ih]
    | false =>
      cases result : read atom with
      | none => simp only [List.filter_cons, retained, Bool.false_eq_true, if_false, List.filterMap_cons, result, ih]
      | some b => exact (Bool.false_ne_true (retained.symm.trans (included _ b result))).elim

theorem he_assignments_from_projection {head : String} {subject : Atom}
    (fits : Atoms.literalHead subject = none ∨ Atoms.literalHead subject = some head) (space : Space) :
    HETypeQueries.assignments (Space.ofList (projection head space.atoms)) subject =
      HETypeQueries.assignments space subject := by
  change ((space.atoms.filter (concerns head)).filterMap (annotationType? subject)) =
    space.atoms.filterMap (annotationType? subject)
  apply filterMap_keeps_answers
  intro written type recognized
  obtain rfl := annotationType?_eq_some_iff.mp recognized
  rcases fits with absent | named
  · simp [concerns, classify, Atoms.content, Atoms.Content.tag, absent]
  · simp [concerns, classify, Atoms.content, Atoms.Content.tag, named]

theorem he_scoped_queries_of_projection {before after : Space} {head : String} {subject : Atom}
    (fits : Atoms.literalHead subject = none ∨ Atoms.literalHead subject = some head)
    (same : projection head before.atoms = projection head after.atoms) (names : List String) :
    HETypeQueries.SameQuery (scopedTypeLookup names before) (scopedTypeLookup names after) subject := by
  apply HETypeQueries.scoped_query _ names
  rw [← he_assignments_from_projection fits before, ← he_assignments_from_projection fits after, same]

private theorem petta_singleton_outside {head : String} {atom : Atom} {program : SpaceSemantics.Program}
    (indexed : SpaceSemantics.Indexes [atom] program) (outside : concerns head atom = false) :
    view program head = ([], []) := by
  cases indexed with
  | equation name arguments body rest =>
    cases rest
    change (name == head) = false at outside
    simp [view, definitions, assignments, outside]
  | declaration subject type rest =>
    cases rest
    suffices noFormal : formalFor head (.expression [.symbol ":", subject, type]) = false by
      simp [view, definitions, assignments, noFormal]
    cases subject with
    | symbol name =>
      change (name == head) = false at outside
      unfold formalFor
      split
      · simp_all
      · rfl
    | var | grounded | expression => rfl
  | fact atom notEquation notDeclaration rest =>
    cases rest
    rfl

private theorem peTTa_view_cons (head : String) (atom : Atom) (rest : List Atom) :
    view (programAt (atom :: rest)) head =
      ((view (programAt [atom]) head).1 ++ (view (programAt rest) head).1,
        (view (programAt [atom]) head).2 ++ (view (programAt rest) head).2) := by
  change view (programAt ([atom] ++ rest)) head = _
  rw [PeTTaExecution.declaration_contributions_compose, PeTTaImportProtection.append_view]

theorem petta_view_from_projection (head : String) (atoms : List Atom) :
    view (programAt (projection head atoms)) head = view (programAt atoms) head := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    unfold projection at ih ⊢
    cases affects : concerns head atom with
    | false =>
      have noContribution := petta_singleton_outside (SpaceSemantics.index_exact [atom]) affects
      rw [← PeTTaExecution.programAt_exact] at noContribution
      simp only [List.filter_cons, affects, Bool.false_eq_true, if_false, ih]
      rw [peTTa_view_cons head atom rest, noContribution]
      rfl
    | true =>
      simp only [List.filter_cons, affects, if_true]
      rw [peTTa_view_cons head atom (rest.filter (concerns head)), peTTa_view_cons head atom rest, ih]

/-- Absence of definitions and exact dispatch at the designated head
are consequences of the protected declaration view, not a blanket
claim about calls to other heads in its body. -/
theorem petta_agreement_of_projection {before after : List Atom} {head : String}
    (same : projection head before = projection head after) :
    Eval.ProgramAgreementOn (fun name => name == head) (programAt before) (programAt after) := by
  apply PeTTaImportProtection.protects_queries
  intro name check
  have rightHead : name = head := beq_iff_eq.mp check
  subst name
  rw [← petta_view_from_projection head before, ← petta_view_from_projection head after, same]

end Queries

section Controls

private def focus : Address Unit := ⟨(), "predict"⟩
private def seals := Registry.one focus 9
private def holder (rights : Rights) : Config Atom :=
  ⟨fun _ => [.cap 9 rights], 10, 0⟩
private def definition (head : String) : Atom :=
  .expression [.symbol "=", .expression [.symbol head], .symbol "warm"]
private def put (atom : Atom) : Edit Unit := ⟨(), [], [], [atom], []⟩
private def empty : Spaces Unit := fun _ => []

theorem writer_can_extend_sealed_head :
    LocalWrite seals (holder Rights.sealOnly) 3 [0] (put (definition "predict")) empty
      (fun _ => [definition "predict"]) := by
  constructor
  · intro h token addressed _
    have issued := Registry.one_exact.mp addressed
    obtain rfl := issued.2
    exact ⟨0, List.mem_cons_self, Rights.sealOnly, rfl, rfl⟩
  · exact ⟨rfl, funext fun _ => by simp [Edit.replacement, put]⟩

theorem opener_cannot_extend_sealed_head (after : Spaces Unit) :
    ¬LocalWrite seals (holder Rights.unsealOnly) 3 [0] (put (definition "predict")) empty after := by
  apply no_facet_refuses (h := "predict") (brand := 9)
  · rfl
  · exact ⟨definition "predict", List.mem_cons_self, rfl⟩
  · rintro ⟨slot, listed, rights, actual, yes⟩
    obtain rfl := List.mem_singleton.mp listed
    have same : Rights.unsealOnly = rights := by
      have equality := Option.some.inj actual
      exact (Val.cap.inj equality).2
    rw [← same] at yes
    exact Bool.false_ne_true yes

theorem ordinary_data_does_not_need_a_write_facet :
    LocalWrite seals (holder Rights.unsealOnly) 3 [] (put (.symbol "note")) empty
      (fun _ => [.symbol "note"]) := by
  constructor
  · intro h token addressed
    rintro ⟨atom, found, touches⟩
    obtain rfl : atom = .symbol "note" := List.mem_singleton.mp found
    cases touches
  · exact ⟨rfl, funext fun _ => by simp [Edit.replacement, put]⟩

theorem open_definition_and_equation_touch_the_sealed_head :
    (put (.expression [.symbol "=", .var "call", .symbol "warm"])).touches "predict" ∧
      (put (.expression [.symbol "=e", .symbol "cold", .symbol "warm"])).touches "predict" :=
  ⟨⟨_, List.mem_cons_self, rfl⟩, ⟨_, List.mem_cons_self, rfl⟩⟩

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.HeadSealing
