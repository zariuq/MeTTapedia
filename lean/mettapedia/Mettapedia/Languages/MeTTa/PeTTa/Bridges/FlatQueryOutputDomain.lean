import Mettapedia.GSLT.Dynamics.ConjunctiveOutputDomain
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryConjunctionCompilation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionRank

/-!
# Finite output catalogues from actual PeTTa query bindings

Source matches retain their full substitutions and occurrence paths. The
existing row compiler projects only declared slots; its domain theorem then
bounds instantiated output constructor rows. Head constants are included in
the domain even when absent from every input row.

This catalogue is a proof enclosure, not a grounding algorithm. Its cardinal
does not replace answer multiplicity or the recursive continuation's returns.
Reusing one catalogue across a driver still requires a fixed-domain invariant
for all later reads and admitted output schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryOutputDomain

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance ConjunctiveRowMatching ConjunctiveBindingDomain
open FlatQueryRowCodec FlatQueryPatternExtraction FlatQueryRelationCompilation FlatQueryConjunctionCompilation
open SpaceSemantics
open scoped BigOperators

variable {Value : Type} [DecidableEq Value]

private theorem literal_subst {atom : Atom} (literal : Literal atom) (bindings : Subst) :
    applySubst bindings atom = atom := by
  induction literal with
  | symbol | grounded => rfl
  | expression items ordinary members ih =>
      clear ordinary members
      simp only [applySubst]
      congr 1
      induction items with
      | nil => rfl
      | cons first rest tail =>
          simp only [applySubst.applySubstList, List.cons.injEq]
          exact ⟨ih first List.mem_cons_self, tail (fun item member => ih item (List.mem_cons_of_mem _ member))⟩

omit [DecidableEq Value] in
theorem instantiate_cell (codec : Codec Value) (names : Inventory String)
    (environment : DenseEnvironment names Value) (bindings : Subst)
    (represented : Represents codec names environment bindings) (cell : Cell names.Slot Value) (value : Value)
    (held : holds environment cell value) : applySubst bindings (encodeCell codec names cell) = codec.encode value := by
  cases cell with
  | constant expected =>
      change expected = value at held
      subst value
      exact literal_subst (codec.literal expected) bindings
  | «variable» name =>
      change environment name = some value at held
      simp only [encodeCell, applySubst, represented name, held, Option.map_some, Option.getD_some]

omit [DecidableEq Value] in
theorem instantiate_head {codec : Codec Value} {names : Inventory String} {source : Atom}
    (head : Compiled codec names source) (environment : DenseEnvironment names Value) (bindings : Subst)
    (represented : Represents codec names environment bindings) (values : List Value)
    (rendered : ConjunctiveOutputDomain.instantiate environment head.cells = some values) :
    applySubst bindings source = row codec head.head values := by
  rcases head with ⟨tag, ordinary, cells, sourceEq⟩
  subst source
  have matched := (ConjunctiveOutputDomain.instantiate_iff environment cells values).mp rendered
  clear rendered
  have fields : applySubst.applySubstList bindings (cells.map (encodeCell codec names)) = values.map codec.encode := by
    induction matched with
    | nil => rfl
    | @cons cell value cells values held _ ih =>
        simp only [List.map_cons, applySubst.applySubstList,
          instantiate_cell codec names environment bindings represented cell value held, ih]
  change Atom.expression (.symbol tag :: applySubst.applySubstList bindings (cells.map (encodeCell codec names))) =
    Atom.expression (.symbol tag :: values.map codec.encode)
  rw [fields]

theorem source_preserves {codec : Codec Value} {names : Inventory String} {rows : List Atom}
    (legs : List (Leg codec names rows)) (environment : DenseEnvironment names Value) (bindings : Subst)
    (represented : Represents codec names environment bindings) (answer : Subst × List Nat)
    (produced : answer ∈ sourceRun rows bindings (legs.map Leg.source)) :
    Represents codec names (readback codec names answer.1) answer.1 := by
  induction legs generalizing environment bindings answer with
  | nil =>
      have same : answer = (bindings, []) := List.mem_singleton.mp produced
      subst answer
      simpa only [readback_exact codec names environment bindings represented] using represented
  | cons leg legs ih =>
      obtain ⟨first, member, rest⟩ := List.mem_flatMap.mp produced
      obtain ⟨last, later, same⟩ := List.mem_map.mp rest
      cases same
      exact ih (readback codec names first.2) first.2
        (leg.relation.preserves environment bindings represented first member) last later

abbrev Head (codec : Codec Value) (names : Inventory String) := (source : Atom) × Compiled codec names source

def compileHead (codec : Codec Value) (names : Inventory String) (source : Atom) : Option (Head codec names) :=
  (compilePattern codec names source).map fun compiled => ⟨source, compiled⟩

def headIR {codec : Codec Value} {names : Inventory String} (head : Head codec names) :
    ConjunctiveOutputDomain.Head String Value names.keys.length := (head.2.head, head.2.cells)

def catalogue (codec : Codec Value) (domain : Finset Value) (shapes : Finset (String × Nat)) : Finset Atom :=
  (ConjunctiveOutputDomain.catalogue domain shapes).image fun fact => row codec fact.1 fact.2

theorem catalogue_card_le (codec : Codec Value) (domain : Finset Value) (shapes : Finset (String × Nat)) :
    (catalogue codec domain shapes).card ≤ ∑ shape ∈ shapes, domain.card ^ shape.2 :=
  Finset.card_image_le.trans (ConjunctiveOutputDomain.catalogue_card_le domain shapes)

omit [DecidableEq Value] in
private theorem encoded_row_injective (codec : Codec Value) :
    Function.Injective (fun fact : String × List Value => row codec fact.1 fact.2) := by
  rintro ⟨first, values⟩ ⟨second, other⟩ same
  have parts := List.cons.inj (Atom.expression.inj same)
  exact Prod.ext (Atom.symbol.inj parts.1) ((List.map_injective_iff.mpr codec.injective) parts.2)

theorem catalogue_card (codec : Codec Value) (domain : Finset Value) (shapes : Finset (String × Nat)) :
    (catalogue codec domain shapes).card = ∑ shape ∈ shapes, domain.card ^ shape.2 := by
  calc
    _ = (ConjunctiveOutputDomain.catalogue domain shapes).card :=
      Finset.card_image_iff.mpr (encoded_row_injective codec).injOn
    _ = _ := ConjunctiveOutputDomain.catalogue_card domain shapes

omit [DecidableEq Value] in
theorem decodeValues_roundtrip (codec : Codec Value) (values : List Value) :
    decodeValues codec (values.map codec.encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change (values.map codec.encode).mapM codec.decode = some values at ih
      simp only [decodeValues, List.map_cons, List.mapM_cons, codec.roundtrip,
        Option.bind_eq_bind, Option.bind_some, ih]
      rfl

/-- Checking an actual source row does not enumerate the semantic universe. -/
def checkRow (codec : Codec Value) (domain : Finset Value) (shapes : Finset (String × Nat)) : Atom → Bool
  | .expression (.symbol head :: fields) =>
      match decodeValues codec fields with
      | none => false
      | some values => ConjunctiveOutputDomain.contains domain shapes (head, values)
  | _ => false

theorem checkRow_encoded (codec : Codec Value) (domain : Finset Value) (shapes : Finset (String × Nat))
    (head : String) (values : List Value) :
    checkRow codec domain shapes (row codec head values) = ConjunctiveOutputDomain.contains domain shapes (head, values) := by
  simp [checkRow, row, decodeValues_roundtrip]

theorem checkRow_iff (codec : Codec Value) (domain : Finset Value) (shapes : Finset (String × Nat)) (atom : Atom) :
    checkRow codec domain shapes atom = true ↔ atom ∈ catalogue codec domain shapes := by
  constructor
  · intro checked
    cases atom with
    | var | symbol | grounded => cases checked
    | expression fields =>
        cases fields with
        | nil => cases checked
        | cons first fields =>
            cases first with
            | var | grounded | expression => cases checked
            | symbol head =>
                cases decoded : decodeValues codec fields with
                | none => simp [checkRow, decoded] at checked
                | some values =>
                    have inside := (ConjunctiveOutputDomain.contains_iff domain shapes (head, values)).mp
                      (by simpa [checkRow, decoded] using checked)
                    refine Finset.mem_image.mpr ⟨(head, values), inside, ?_⟩
                    change Atom.expression (.symbol head :: values.map codec.encode) = Atom.expression (.symbol head :: fields)
                    rw [decodeValues_exact codec fields values decoded]
  · intro inside
    obtain ⟨⟨head, values⟩, member, rfl⟩ := Finset.mem_image.mp inside
    rw [checkRow_encoded, ConjunctiveOutputDomain.contains_iff]
    exact member

theorem source_head_in_catalogue {codec : Codec Value} {names : Inventory String} {rows : List Atom}
    (legs : List (Leg codec names rows)) (head : Head codec names)
    (domain : Finset Value) (shapes : Finset (String × Nat))
    (shape : (head.2.head, head.2.cells.length) ∈ shapes)
    (environment : DenseEnvironment names Value) (bindings : Subst)
    (represented : Represents codec names environment bindings)
    (initial : InDomain domain environment) (allRows : RowsInDomain domain (factors legs))
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (covered : Covered environment (factors legs)) (answer : Subst × List Nat)
    (produced : answer ∈ sourceRun rows bindings (legs.map Leg.source)) :
    applySubst answer.1 head.1 ∈ catalogue codec domain shapes := by
  have native : resultReadback codec names answer ∈ ConjunctiveBindingJoin.run environment (factors legs) := by
    rw [conjunctive_readback_exact legs environment bindings represented]
    exact List.mem_map.mpr ⟨answer, produced, rfl⟩
  obtain ⟨values, rendered, inside⟩ := ConjunctiveOutputDomain.run_head_in_catalogue domain shapes environment (factors legs)
    (headIR head) shape initial allRows constants covered (resultReadback codec names answer) native
  have source := instantiate_head head.2 (readback codec names answer.1) answer.1
    (source_preserves legs environment bindings represented answer produced) values rendered
  exact Finset.mem_image.mpr ⟨(head.2.head, values), inside, source.symm⟩

def derivedDomain {codec : Codec Value} {names : Inventory String} {rows : List Atom}
    (environment : DenseEnvironment names Value) (legs : List (Leg codec names rows)) (heads : List (Head codec names)) : Finset Value :=
  ConjunctiveOutputDomain.activeDomain environment (factors legs) (heads.map headIR)

def derivedShapes {codec : Codec Value} {names : Inventory String} (heads : List (Head codec names)) : Finset (String × Nat) :=
  ConjunctiveOutputDomain.shapes (heads.map headIR)

theorem source_head_bounded {codec : Codec Value} {names : Inventory String} {rows : List Atom}
    (legs : List (Leg codec names rows)) (heads : List (Head codec names)) (head : Head codec names) (present : head ∈ heads)
    (environment : DenseEnvironment names Value) (bindings : Subst)
    (represented : Represents codec names environment bindings) (covered : Covered environment (factors legs))
    (answer : Subst × List Nat) (produced : answer ∈ sourceRun rows bindings (legs.map Leg.source)) :
    applySubst answer.1 head.1 ∈ catalogue codec (derivedDomain environment legs heads) (derivedShapes heads) := by
  have headMember : headIR head ∈ heads.map headIR := List.mem_map.mpr ⟨head, present, rfl⟩
  exact source_head_in_catalogue legs head _ _
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨headIR head, headMember, rfl⟩))
    environment bindings represented (ConjunctiveOutputDomain.activeDomain_captures _ _ _)
    (ConjunctiveOutputDomain.activeDomain_rows _ _ _)
    (ConjunctiveOutputDomain.activeDomain_constant _ _ _ _ headMember) covered answer produced

/-- The head enclosure discharges the catalogue membership required by the
actual fresh-insertion rank theorem. -/
theorem source_fresh_entry_decreases {codec : Codec Value} {names : Inventory String} {rows : List Atom}
    (legs : List (Leg codec names rows)) (heads : List (Head codec names)) (head : Head codec names) (present : head ∈ heads)
    (environment : DenseEnvironment names Value) (bindings : Subst)
    (represented : Represents codec names environment bindings) (covered : Covered environment (factors legs))
    (answer : Subst × List Nat) (produced : answer ∈ sourceRun rows bindings (legs.map Leg.source))
    (target : NamedSpaces.Handle) (before after : Effects.State) (old result : List Atom)
    (beforeRead : before.read target = some old) (afterRead : after.read target = some result)
    (inserted : FreshInsertionSource.update before target (applySubst answer.1 head.1) = some (after, true)) :
    FreshInsertionRank.remaining (catalogue codec (derivedDomain environment legs heads) (derivedShapes heads)) result + 1 =
      FreshInsertionRank.remaining (catalogue codec (derivedDomain environment legs heads) (derivedShapes heads)) old :=
  FreshInsertionRank.fresh_entry_decreases _ target _ before after old result
    (source_head_bounded legs heads head present environment bindings represented covered answer produced)
    beforeRead afterRead inserted

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryOutputDomain
