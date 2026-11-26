import Mettapedia.Languages.MeTTa.SpaceTheory.Modules
import Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations
import Mettapedia.Languages.MeTTa.SpaceTheory.Assignments
import Mettapedia.Languages.MeTTa.SpaceTheory.NativeVocabulary
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Gluing native MeTTa declarations

The inclusions are on the language of authored equations, function
definitions and type assignments. They do not assert that a newly
callable atom stays data, or that an extending import preserves a
negative observation. The two dialects choose their evaluation
contexts separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.ModuleTheories

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern applyBindings)
open Mettapedia.OSLF.MeTTaIL.Syntax (RewriteRule)
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Atoms (Content content)
open Mettapedia.Languages.MeTTa.HE (ModuleStore ModuleNode ModId)

/-- Instantiation uses the existing native Atom vocabulary. This is a
definition contribution, not either dialect's evaluator strategy. -/
def InstanceOf (declaration source target : Atom) : Prop :=
  ∃ left right, content declaration = .definition left right ∧
    ∃ binding ∈ matchPattern (GroundData.schema left) (GroundData.encode source),
      GroundData.decode (applyBindings binding (GroundData.schema right)) = some target

def Authored (base : Atom → Atom → Prop) (atoms : List Atom) (source target : Atom) : Prop :=
  base source target ∨ ∃ declaration ∈ atoms, InstanceOf declaration source target

def theory (base : Atom → Atom → Prop) (atoms : List Atom) : GSLT :=
  AtomEquations.theory atoms (Authored base atoms)

theorem authored_mono {first second : List Atom} {old new : Atom → Atom → Prop}
    (included : first ⊆ second) (baseIncluded : ∀ a b, old a b → new a b) {a b : Atom} :
    Authored old first a b → Authored new second a b := by
  rintro (base | ⟨decl, member, instanceOf⟩)
  · exact Or.inl (baseIncluded _ _ base)
  · exact Or.inr ⟨decl, included member, instanceOf⟩

/-- A positive inclusion preserves equations and authored firings. It
may expose extra steps and is therefore not an unconditional
bisimilarity-preserving map. -/
def includeTheory {first second : List Atom} {old new : Atom → Atom → Prop}
    (included : first ⊆ second) (baseIncluded : ∀ a b, old a b → new a b) :
    OperationalTranslation (theory old first) (theory new second) where
  mapTerm := id
  mapEquiv := AtomEquations.monotone included
  mapStep := by
    intro a b
    rintro ⟨source, target, into, fires, out⟩
    exact ⟨source, target, AtomEquations.monotone included into, authored_mono included baseIncluded fires,
      AtomEquations.monotone included out⟩

def extendBase (base : Atom → Atom → Prop) (atoms : List Atom) :
    OperationalTranslation (theory base []) (theory base atoms) :=
  includeTheory (List.nil_subset _) (fun _ _ h => h)

private theorem part_for_member {before : List Content} {after : List Presentation.Contribution}
    (graph : List.Forall₂ (fun c p => NativeVocabulary.contribution c = some p) before after)
    (wanted : Content) (present : wanted ∈ before) :
    ∃ part ∈ after, NativeVocabulary.contribution wanted = some part := by
  induction graph with
  | nil => cases present
  | cons result _ ih =>
    rcases List.mem_cons.mp present with rfl | earlier
    · exact ⟨_, List.mem_cons_self, result⟩
    · obtain ⟨part, found, checked⟩ := ih earlier
      exact ⟨part, List.mem_cons_of_mem _ found, checked⟩

/-- This interpretation of a definition is precisely an instantiated
contribution in the existing native presentation. It introduces no
additional matching judgment or body language. -/
theorem native_contribution_iff (atoms : List Atom) {parts : List Presentation.Contribution}
    (prepared : NativeVocabulary.parts atoms = some parts) (source target : Atom) :
    (∃ rule ∈ parts.flatMap Presentation.Contribution.rewrites,
      ∃ binding ∈ matchPattern rule.left (GroundData.encode source),
        GroundData.decode (applyBindings binding rule.right) = some target) ↔
      Authored (fun _ _ => False) atoms source target := by
  constructor
  · rintro ⟨rule, member, binding, found, output⟩
    obtain ⟨part, present, contains⟩ := List.mem_flatMap.mp member
    obtain ⟨kind, origin, compiled⟩ := Mettapedia.Data.List.option_mapM_origin NativeVocabulary.contribution
      (atoms.map content) parts prepared part present
    obtain ⟨atom, stored, rfl⟩ := List.mem_map.mp origin
    obtain ⟨left, right, definition, l, r, _, _⟩ :=
      Presentation.contribution_rule_origin (definitionTerm := some ∘ GroundData.schema) compiled contains
    exact Or.inr ⟨atom, stored, left, right, definition, binding,
      (Option.some.inj l).symm ▸ found, (Option.some.inj r).symm ▸ output⟩
  · rintro (no | ⟨atom, member, left, right, definition, binding, found, output⟩)
    · exact no.elim
    · have contains : content atom ∈ atoms.map content := List.mem_map_of_mem member
      have graph := Mettapedia.Data.List.option_mapM_forall₂ NativeVocabulary.contribution _ parts prepared
      obtain ⟨part, selected, computed⟩ := part_for_member graph (content atom) contains
      rw [definition] at computed
      let rule : RewriteRule :=
        { name := "space definition", typeContext := NativeTyping.schemaContext left right, premises := []
          left := GroundData.schema left, right := GroundData.schema right }
      have known : NativeVocabulary.contribution (.definition left right) = some {rewrites := [rule]} :=
        NativeVocabulary.written_definition left right
      obtain rfl := Option.some.inj (computed.symm.trans known)
      exact ⟨rule, List.mem_flatMap.mpr ⟨_, selected, List.mem_cons_self⟩, binding, found, output⟩

def CoversUnion (left right combined : List Atom) : Prop :=
  ∀ atom, atom ∈ combined ↔ atom ∈ left ∨ atom ∈ right

theorem authored_union {left right combined : List Atom} (same : CoversUnion left right combined)
    (base : Atom → Atom → Prop) (a b : Atom) :
    Authored base combined a b ↔ Authored base left a b ∨ Authored base right a b := by
  constructor
  · rintro (baseFires | ⟨decl, member, instanced⟩)
    · exact Or.inl (Or.inl baseFires)
    · rcases (same decl).mp member with own | own
      · exact Or.inl (Or.inr ⟨decl, own, instanced⟩)
      · exact Or.inr (Or.inr ⟨decl, own, instanced⟩)
  · intro fires
    rcases fires with owned | owned
    · exact authored_mono (fun {d} h => (same d).mpr (Or.inl h)) (fun _ _ h => h) owned
    · exact authored_mono (fun {d} h => (same d).mpr (Or.inr h)) (fun _ _ h => h) owned

def EqJoin (left right : List Atom) (a b : Atom) : Prop :=
  Relation.EqvGen (fun x y => AtomEquations.Equivalent left x y ∨ AtomEquations.Equivalent right x y) a b

private theorem eqJoinFills (left right : List Atom) (c : AtomEquations.Context) {a b : Atom}
    (within : EqJoin left right a b) : EqJoin left right (c.fill a) (c.fill b) := by
  induction within with
  | rel _ _ step =>
    exact .rel _ _ (step.elim (fun first => Or.inl (AtomEquations.fill_equivalent c first))
      (fun second => Or.inr (AtomEquations.fill_equivalent c second)))
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

/-- The joined native congruence is exactly the join of the two
congruences, including consequences that alternate between modules. -/
theorem equations_join {left right combined : List Atom} (same : CoversUnion left right combined) (a b : Atom) :
    AtomEquations.Equivalent combined a b ↔ EqJoin left right a b := by
  let joined : Setoid Atom := ⟨EqJoin left right, ⟨.refl, fun h => .symm _ _ h, fun h h' => .trans _ _ _ h h'⟩⟩
  constructor
  · apply AtomEquations.least combined joined
    · rintro first last ⟨pref, next, tail, declared, member⟩
      rcases (same _).mp declared with own | own
      · exact .rel _ _ (Or.inl (AtomEquations.authored ⟨pref, next, tail, own, member⟩))
      · exact .rel _ _ (Or.inr (AtomEquations.authored ⟨pref, next, tail, own, member⟩))
    · exact fun c _ _ h => eqJoinFills left right c h
  · intro available
    induction available with
    | rel _ _ step =>
      rcases step with fromLeft | fromRight
      · exact AtomEquations.monotone (fun {d} h => (same d).mpr (Or.inl h)) fromLeft
      · exact AtomEquations.monotone (fun {d} h => (same d).mpr (Or.inr h)) fromRight
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

def inclusion (base : Atom → Atom → Prop) {first second : List Atom} (included : first ⊆ second) :
    OperationalTranslation (theory base first) (theory base second) :=
  includeTheory included (fun _ _ h => h)

private theorem map_joined_equations {base : Atom → Atom → Prop} {left right : List Atom} {destination : GSLT}
    (f : OperationalTranslation (theory base left) destination)
    (g : OperationalTranslation (theory base right) destination)
    (same : ∀ atom : Atom, f.mapTerm atom = g.mapTerm atom)
    {a b : Atom} (connected : EqJoin left right a b) :
    destination.Equiv (f.mapTerm a) (f.mapTerm b) := by
  induction connected with
  | rel x y authored =>
    rcases authored with h | h
    · exact f.mapEquiv h
    · rw [same x, same y]
      exact g.mapEquiv h
  | refl => exact destination.equations.iseqv.refl _
  | symm _ _ _ ih => exact destination.equations.iseqv.symm ih
  | trans _ _ _ _ _ ih ih' => exact destination.equations.iseqv.trans ih ih'

/-- Interpret a union in any GSLT. The case where a firing uses equality
from one side and a function definition from the other is required:
simply taking the union of the two step relations would miss it. -/
def glue (base : Atom → Atom → Prop) {left right combined : List Atom}
    (cover : CoversUnion left right combined) {destination : GSLT}
    (f : OperationalTranslation (theory base left) destination)
    (g : OperationalTranslation (theory base right) destination)
    (agree : ∀ atom : Atom, f.mapTerm atom = g.mapTerm atom) :
    OperationalTranslation (theory base combined) destination where
  mapTerm := f.mapTerm
  mapEquiv := fun {a b} h => map_joined_equations f g agree ((equations_join cover a b).mp h)
  mapStep := by
    intro a b
    rintro ⟨before, after, enter, fires, leave⟩
    have input := map_joined_equations f g agree ((equations_join cover a before).mp enter)
    have output := map_joined_equations f g agree ((equations_join cover after b).mp leave)
    have one : destination.Step (f.mapTerm before) (f.mapTerm after) := by
      rcases (authored_union cover base before after).mp fires with h | h
      · exact f.mapStep (EndpointSaturation.contains (equations := AtomEquations.setoid left) h)
      · rw [agree before, agree after]
        exact g.mapStep (EndpointSaturation.contains (equations := AtomEquations.setoid right) h)
    obtain ⟨reached, moved, equated⟩ := destination.rewrites_resp_left
      (destination.equations.iseqv.symm input) one
    exact destination.rewrites_resp_right moved
      (destination.equations.iseqv.trans (destination.equations.iseqv.symm equated) output)

/-- Pushout in the fixed Atom signature for forward operational maps.
The shared theory already has that signature, so agreement on its map
is exactly agreement on the common terms. Origins and occurrence
enumerations are separate from this extensional universal property. -/
theorem theory_pushout (base : Atom → Atom → Prop) {shared left right combined : List Atom}
    (inLeft : shared ⊆ left) (inRight : shared ⊆ right) (cover : CoversUnion left right combined)
    {destination : GSLT} (f : OperationalTranslation (theory base left) destination)
    (g : OperationalTranslation (theory base right) destination) :
    let leftInto := inclusion base (fun {a} h => (cover a).mpr (Or.inl h))
    let rightInto := inclusion base (fun {a} h => (cover a).mpr (Or.inr h))
    (inclusion base inLeft).comp f = (inclusion base inRight).comp g ↔
      ∃! lift : OperationalTranslation (theory base combined) destination,
        leftInto.comp lift = f ∧ rightInto.comp lift = g := by
  dsimp only
  constructor
  · intro equal
    have agree (atom : Atom) : f.mapTerm atom = g.mapTerm atom :=
      congrArg (fun map : OperationalTranslation (theory base shared) destination => map.mapTerm atom) equal
    refine ⟨glue base cover f g agree, ⟨?_, ?_⟩, ?_⟩
    · apply OperationalTranslation.ext; rfl
    · apply OperationalTranslation.ext; exact funext agree
    · intro lift facts
      apply OperationalTranslation.ext
      have onTerms := congrArg (fun map : OperationalTranslation (theory base left) destination => map.mapTerm) facts.1
      exact onTerms
  · rintro ⟨lift, ⟨onLeft, onRight⟩, _⟩
    apply OperationalTranslation.ext
    funext atom
    have leftTerms := congrArg (fun map : OperationalTranslation (theory base left) destination => map.mapTerm atom) onLeft
    have rightTerms := congrArg (fun map : OperationalTranslation (theory base right) destination => map.mapTerm atom) onRight
    exact leftTerms.symm.trans rightTerms

/-- The native import interpretation includes both visible sides.
This uses the actual main-then-dependencies HE view and its fresh
import law, not a flattening of effectful commands. -/
theorem he_import_presents_union (store : ModuleStore) (before imported : ModuleNode) (id : ModId)
    (names : store id = imported.main) (first : id ∉ before.deps) :
    CoversUnion (before.view store) (imported.view store) ((before.importModule id imported.deps).view store) :=
  fun _ => ModuleNode.mem_view_importModule_iff names first

def heImportMap (base : Atom → Atom → Prop) (store : ModuleStore) (before imported : ModuleNode) (id : ModId)
    (names : store id = imported.main) (first : id ∉ before.deps) :
    OperationalTranslation (theory base (imported.view store))
      (theory base ((before.importModule id imported.deps).view store)) :=
  includeTheory (fun {d} h => (he_import_presents_union store before imported id names first d).mpr (Or.inr h))
    (fun _ _ h => h)

theorem he_import_classes (store : ModuleStore) (before imported : ModuleNode) (id : ModId)
    (names : store id = imported.main) (first : id ∉ before.deps) (a b : Atom) :
    AtomEquations.Equivalent ((before.importModule id imported.deps).view store) a b ↔
      EqJoin (before.view store) (imported.view store) a b :=
  equations_join (he_import_presents_union store before imported id names first) a b

section Controls

private def a : Atom := .symbol "A"
private def b : Atom := .symbol "B"
private def c : Atom := .symbol "C"
private def ok : Atom := .symbol "OK"
private def first : List Atom := [(Content.equation .indifferent a b []).syntax]
private def second : List Atom :=
  [(Content.equation .rightward b c []).syntax, (Content.definition c ok).syntax]
private def noBase : Atom → Atom → Prop := fun _ _ => False

/-- A joint declaration can use equations from both imported views.
Neither local theory on its own has the combined congruence. -/
theorem equations_across_modules_open_a_definition :
    (theory noBase (first ++ second)).Step a ok := by
  have union : CoversUnion first second (first ++ second) := fun _ => List.mem_append
  have ab : AtomEquations.Equivalent first a b :=
    AtomEquations.authored ⟨.indifferent, b, [], List.mem_cons_self, List.mem_cons_self⟩
  have bc : AtomEquations.Equivalent second b c :=
    AtomEquations.authored ⟨.rightward, c, [], List.mem_cons_self, List.mem_cons_self⟩
  refine ⟨c, ok, (equations_join union a c).mpr
    (.trans _ _ _ (.rel _ _ (Or.inl ab)) (.rel _ _ (Or.inr bc))), ?_, .refl _⟩
  refine Or.inr ⟨(Content.definition c ok).syntax, by simp [second], c, ok, rfl, [], ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem an_import_cannot_be_judged_by_the_original_rewrites_alone :
    ¬ (theory noBase first).Step a ok := by
  rintro ⟨_, _, _, fires, _⟩
  rcases fires with base | ⟨decl, member, lhs, rhs, read, _⟩
  · exact base.elim
  · obtain rfl := List.mem_singleton.mp member
    cases read

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.ModuleTheories
