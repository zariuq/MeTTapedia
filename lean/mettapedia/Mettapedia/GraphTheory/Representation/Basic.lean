import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.GSLT.Core.GSLT

/-!
# Operational foundations for finite graph representations

Finite simple graphs have many concrete presentations.  This module keeps
their common mathematical meaning separate from their operational behaviour.
A presentation supplies an extensional `SimpleGraph (Fin n)`, an executable
edge observer, and a proof that the observer agrees with that meaning.

The small linear-probe GSLT below is shared by list-shaped representations.
Its proof-relevant rewrite paths expose the exact number of inspected entries.
An adjacency matrix will use a different, constant-probe machine rather than
being forced through this interface.
-/

namespace Mettapedia.GraphTheory.Representation

open Mettapedia.GSLT
open CategoryTheory

/-- A computed value paired with the exact amount of representation work used
to obtain it.  `work` counts primitive inspected cells or entries; it is not a
wall-clock claim. -/
structure Measured (Result : Type*) where
  value : Result
  work : Nat
deriving DecidableEq, Repr

/-- The common semantic and observational boundary for a finite simple-graph
representation.  Different carriers may expose other efficient observations;
edge lookup is the one observation shared by every presentation in the
portfolio. -/
structure Presentation (n : Nat) where
  Carrier : Type*
  denote : Carrier → SimpleGraph (Fin n)
  edge : Carrier → Fin n → Fin n → Measured Bool
  edge_sound : ∀ graph u v,
    (edge graph u v).value = true ↔ (denote graph).Adj u v
  storageCells : Carrier → Nat

/-- A named representation refinement is a construction together with its
semantic commuting law.  Equality of separately authored outcomes is not a
refinement until such a function is supplied. -/
structure Refinement {n : Nat} (source target : Presentation n) where
  map : source.Carrier → target.Carrier
  commute : ∀ graph, target.denote (map graph) = source.denote graph

namespace Refinement

/-- Two representation rules are equal when their constructed carrier maps
are equal.  Their commuting fields are propositions and therefore carry no
additional computational identity. -/
@[ext] theorem ext {n : Nat} {source target : Presentation n}
    {first second : Refinement source target}
    (map_eq : first.map = second.map) : first = second := by
  cases first
  cases second
  cases map_eq
  rfl

/-- Identity representation rule. -/
def id {n : Nat} (presentation : Presentation n) :
    Refinement presentation presentation where
  map := _root_.id
  commute := by simp

/-- Representation rules compose in data-flow order. -/
def comp {n : Nat} {first middle last : Presentation n}
    (earlier : Refinement first middle) (later : Refinement middle last) :
    Refinement first last where
  map := later.map ∘ earlier.map
  commute := by
    intro graph
    change last.denote (later.map (earlier.map graph)) = first.denote graph
    rw [later.commute, earlier.commute]

@[simp] theorem id_map {n : Nat} (presentation : Presentation n)
    (graph : presentation.Carrier) :
    (id presentation).map graph = graph :=
  rfl

@[simp] theorem comp_map {n : Nat} {first middle last : Presentation n}
    (earlier : Refinement first middle) (later : Refinement middle last)
    (graph : first.Carrier) :
    (earlier.comp later).map graph = later.map (earlier.map graph) :=
  rfl

/-- Composition is associative at the constructed carrier map. -/
theorem comp_assoc_map {n : Nat}
    {first second third fourth : Presentation n}
    (one : Refinement first second) (two : Refinement second third)
    (three : Refinement third fourth) (graph : first.Carrier) :
    ((one.comp two).comp three).map graph =
      (one.comp (two.comp three)).map graph :=
  rfl

end Refinement

/-- Finite graph presentations with meaning-preserving constructions form a
category.  This is the abstract composition layer underneath the operational
representation GSLT: a GSLT chooses executable generating arrows, while this
category supplies their identity and composition laws. -/
instance presentationCategory (n : Nat) :
    CategoryTheory.Category (Presentation n) where
  Hom := Refinement
  id := Refinement.id
  comp earlier later := earlier.comp later
  id_comp := by
    intro source target rule
    apply Refinement.ext
    rfl
  comp_id := by
    intro source target rule
    apply Refinement.ext
    rfl
  assoc := by
    intro first second third fourth one two three
    apply Refinement.ext
    rfl

@[simp] theorem category_comp_map {n : Nat}
    {first middle last : Presentation n}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (graph : first.Carrier) :
    (earlier ≫ later).map graph = later.map (earlier.map graph) :=
  rfl

/-- A channel is a pair of concrete representations certified to denote the
same graph.  It is the proof-bearing analogue of a Conjure channelling
constraint. -/
structure Channel {n : Nat} (left right : Presentation n) where
  leftState : left.Carrier
  rightState : right.Carrier
  coherent : left.denote leftState = right.denote rightState

/-- Every refinement constructs a coherent channel from its input. -/
def Refinement.channel {n : Nat} {source target : Presentation n}
    (refinement : Refinement source target) (graph : source.Carrier) :
    Channel source target where
  leftState := graph
  rightState := refinement.map graph
  coherent := (refinement.commute graph).symm

namespace LinearProbe

variable {Entry Query : Type}

/-- Inspect a list from left to right until one entry matches. -/
def run (accepts : Entry → Query → Bool) (query : Query) :
    List Entry → Measured Bool
  | [] => ⟨false, 0⟩
  | entry :: rest =>
      if accepts entry query then
        ⟨true, 1⟩
      else
        let tail := run accepts query rest
        ⟨tail.value, tail.work + 1⟩

@[simp] theorem run_nil (accepts : Entry → Query → Bool) (query : Query) :
    run accepts query [] = ⟨false, 0⟩ :=
  rfl

@[simp] theorem run_cons (accepts : Entry → Query → Bool) (query : Query)
    (entry : Entry) (rest : List Entry) :
    run accepts query (entry :: rest) =
      if accepts entry query then ⟨true, 1⟩
      else
        let tail := run accepts query rest
        ⟨tail.value, tail.work + 1⟩ :=
  rfl

/-- The executable scan reports exactly the same Boolean as `List.any`. -/
theorem run_value_eq_any (accepts : Entry → Query → Bool) (query : Query)
    (entries : List Entry) :
    (run accepts query entries).value = entries.any (accepts · query) := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      by_cases hit : accepts entry query = true
      · simp [run, hit]
      · have miss : accepts entry query = false := Bool.eq_false_of_not_eq_true hit
        simp [run, miss, inductionHypothesis]

/-- A scan never inspects more entries than are present. -/
theorem run_work_le_length (accepts : Entry → Query → Bool) (query : Query)
    (entries : List Entry) :
    (run accepts query entries).work ≤ entries.length := by
  induction entries with
  | nil => simp [run]
  | cons entry rest inductionHypothesis =>
      by_cases hit : accepts entry query = true
      · simp [run, hit]
      · have miss : accepts entry query = false := Bool.eq_false_of_not_eq_true hit
        simpa [run, miss, Nat.add_comm] using
          Nat.add_le_add_right inductionHypothesis 1

/-- Negative linear-search canary: if no entry matches, every entry is
inspected. -/
theorem run_work_eq_length_of_no_match
    (accepts : Entry → Query → Bool) (query : Query) (entries : List Entry)
    (none : ∀ entry ∈ entries, accepts entry query = false) :
    (run accepts query entries).work = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      have headMiss : accepts entry query = false := none entry (by simp)
      have restMiss : ∀ candidate ∈ rest, accepts candidate query = false := by
        intro candidate member
        exact none candidate (by simp [member])
      simp [run, headMiss, inductionHypothesis restMiss]

/-- The explicit states of the list-observation machine. -/
inductive State (Entry Query : Type*) where
  | scan (query : Query) (remaining : List Entry)
  | answer (value : Bool)
deriving DecidableEq, Repr

/-- The three rules of linear observation: hit, skip, and exhausted. -/
inductive Step (accepts : Entry → Query → Bool) :
    State Entry Query → State Entry Query → Prop where
  | hit {query entry rest} (matched : accepts entry query = true) :
      Step accepts (.scan query (entry :: rest)) (.answer true)
  | skip {query entry rest} (missed : accepts entry query = false) :
      Step accepts (.scan query (entry :: rest)) (.scan query rest)
  | exhausted {query} :
      Step accepts (.scan query []) (.answer false)

/-- The authentic linear-query GSLT.  It computes from the entries and never
receives the final answer as a premise. -/
def theory (accepts : Entry → Query → Bool) : GSLT where
  Term := State Entry Query
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step accepts
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Every executable scan has a proof-relevant path to its computed answer. -/
def runPath (accepts : Entry → Query → Bool) (query : Query) :
    (entries : List Entry) →
      (theory accepts).RewritePath (.scan query entries)
        (.answer (run accepts query entries).value)
  | [] => .cons .exhausted (.nil _)
  | entry :: rest => by
      by_cases hit : accepts entry query = true
      · simpa [run, hit] using
          ((.cons (.hit hit) (.nil _)) :
            (theory accepts).RewritePath
              (.scan query (entry :: rest)) (.answer true))
      · have miss : accepts entry query = false := Bool.eq_false_of_not_eq_true hit
        simpa [run, miss] using
          ((.cons (.skip miss) (runPath accepts query rest)) :
            (theory accepts).RewritePath
              (.scan query (entry :: rest))
              (.answer (run accepts query rest).value))

/-- Answers are terminal in the linear-query GSLT. -/
theorem answer_normal (accepts : Entry → Query → Bool) (answer : Bool) :
    (theory accepts).IsNormalForm (.answer answer) := by
  rintro ⟨target, step⟩
  cases step

end LinearProbe

#print axioms LinearProbe.run_value_eq_any
#print axioms LinearProbe.run_work_eq_length_of_no_match
#print axioms LinearProbe.answer_normal
#print axioms Refinement.comp_assoc_map
#print axioms category_comp_map

end Mettapedia.GraphTheory.Representation
