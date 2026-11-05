import Mettapedia.Languages.Datalog.Syntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsExec

/-!
# Datalog atom matching is the `match` reference on encoded facts

The positive Datalog core, the gold language D0 that the GSLT module format
compiles, matches a schema atom against a ground fact under one assignment of
its variables. Encode values, relation names and facts as ground MeTTa atoms
and schema variables as atom variables. For schemas without anonymous
arguments:

* `atom_matches_iff`: a Datalog assignment matching a schema against a fact
  exists exactly when the encoded schema matches the encoded fact in the sense
  of `MeTTaOperationsMatch.Matches`;
* `match_answers_are_datalog_matches`: the occurrences that answer the
  `match` encoding over an encoded fact base are those whose fact the schema
  matches in Datalog;
* `exec_rows_are_datalog_matches`: a row of a one-source MM2 exec over an
  encoded fact base is a Datalog match of its source schema against a stored
  fact.

Anonymous arguments are excluded; Datalog reads each one as a fresh variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsDatalog

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsMatch

/-! ## Encoding -/

def encValue : Mettapedia.Languages.Datalog.Value → Atom
  | .symbol s => .grounded (.string s)
  | .number n => .grounded (.int n)
  | .unsigned n => .expression [.symbol "unsigned", .grounded (.int n)]
  | .floating w => .expression [.symbol "floating", .grounded (.int w.toNat)]

theorem encValue_injective : Function.Injective encValue := by
  intro v w same
  cases v <;> cases w <;> simp [encValue] at same ⊢
  · exact same
  · exact same
  · exact same
  · exact UInt64.toNat_inj.mp same

theorem encValue_vars (v : Mettapedia.Languages.Datalog.Value) : vars (encValue v) = [] := by
  cases v <;> rfl

theorem encValue_ne_var (v : Mettapedia.Languages.Datalog.Value) (name : Var) : encValue v ≠ .var name := by
  cases v <;> simp [encValue]

def encRelation (relation : List String) : Atom := .expression (relation.map fun s => .grounded (.string s))

theorem encRelation_vars (relation : List String) : vars (encRelation relation) = [] := by
  unfold encRelation
  simp only [vars]
  induction relation with
  | nil => rfl
  | cons s rest ih => simp only [List.map_cons, vars.varsList, ih]; rfl

theorem encRelation_injective : Function.Injective encRelation := by
  intro first second same
  simp only [encRelation, Atom.expression.injEq] at same
  exact List.map_injective_iff.mpr (fun _ _ h => by simpa using h) same

def encArgument : Mettapedia.Languages.Datalog.Argument → Atom
  | .literal v => encValue v
  | .var name => .var name
  | .anonymous => .var "_"

def encFact (fact : Mettapedia.Languages.Datalog.GroundFact) : Atom :=
  .expression (encRelation fact.relation :: fact.values.map encValue)

def encSchema (schema : Mettapedia.Languages.Datalog.Atom) : Atom :=
  .expression (encRelation schema.relation :: schema.arguments.map encArgument)

theorem substList_eq_map (σ : Subst) (atoms : List Atom) : subst.substList σ atoms = atoms.map (subst σ) := by
  induction atoms with
  | nil => rfl
  | cons a rest ih => simp only [subst.substList, List.map_cons, ih]

/-! ## Assignments and substitutions -/

def toSubst (model : Mettapedia.Languages.Datalog.Assignment) : Subst := fun name => (model name).map encValue

noncomputable def decodeValue (a : Atom) : Option Mettapedia.Languages.Datalog.Value := by
  classical
  exact if h : ∃ v, encValue v = a then some (Classical.choose h) else none

theorem decode_encode (v : Mettapedia.Languages.Datalog.Value) : decodeValue (encValue v) = some v := by
  classical
  unfold decodeValue
  rw [dif_pos ⟨v, rfl⟩]
  exact congrArg some (encValue_injective (Classical.choose_spec (⟨v, rfl⟩ : ∃ w, encValue w = encValue v)))

noncomputable def toModel (σ : Subst) : Mettapedia.Languages.Datalog.Assignment := fun name => (σ name).bind decodeValue

theorem argument_forward (model : Mettapedia.Languages.Datalog.Assignment)
    {argument : Mettapedia.Languages.Datalog.Argument} {value : Mettapedia.Languages.Datalog.Value}
    (matched : argument.Matches model value) (named : argument ≠ .anonymous) :
    subst (toSubst model) (encArgument argument) = encValue value := by
  cases argument with
  | literal expected =>
    change expected = value at matched
    subst matched
    exact subst_of_vars_eq_nil _ _ (encValue_vars expected)
  | var name =>
    change model name = some value at matched
    simp [encArgument, subst, toSubst, matched]
  | anonymous => exact absurd rfl named

theorem argument_backward (σ : Subst) {argument : Mettapedia.Languages.Datalog.Argument}
    {value : Mettapedia.Languages.Datalog.Value}
    (solved : subst σ (encArgument argument) = encValue value) (named : argument ≠ .anonymous) :
    argument.Matches (toModel σ) value := by
  cases argument with
  | literal expected =>
    change expected = value
    rw [encArgument, subst_of_vars_eq_nil _ _ (encValue_vars expected)] at solved
    exact encValue_injective solved
  | var name =>
    change (σ name).bind decodeValue = some value
    simp only [encArgument, subst] at solved
    cases found : σ name with
    | none =>
      rw [found] at solved
      exact absurd solved.symm (encValue_ne_var value name)
    | some bound =>
      rw [found] at solved
      simp only [Option.getD_some] at solved
      simp [solved, decode_encode]
  | anonymous => exact absurd rfl named

theorem arguments_forward (model : Mettapedia.Languages.Datalog.Assignment) :
    ∀ {arguments : List Mettapedia.Languages.Datalog.Argument} {values : List Mettapedia.Languages.Datalog.Value},
      List.Forall₂ (Mettapedia.Languages.Datalog.Argument.Matches model) arguments values →
      (∀ argument ∈ arguments, argument ≠ .anonymous) →
      (arguments.map encArgument).map (subst (toSubst model)) = values.map encValue
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons head tail, named => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨argument_forward model head (named _ List.mem_cons_self),
      arguments_forward model tail (fun argument member => named argument (List.mem_cons_of_mem _ member))⟩

theorem arguments_backward (σ : Subst) :
    ∀ {arguments : List Mettapedia.Languages.Datalog.Argument} {values : List Mettapedia.Languages.Datalog.Value},
      (arguments.map encArgument).map (subst σ) = values.map encValue →
      (∀ argument ∈ arguments, argument ≠ .anonymous) →
      List.Forall₂ (Mettapedia.Languages.Datalog.Argument.Matches (toModel σ)) arguments values
  | [], [], _, _ => .nil
  | [], _ :: _, same, _ => by simp at same
  | _ :: _, [], same, _ => by simp at same
  | argument :: rest, value :: values, same, named => by
    simp only [List.map_cons, List.cons.injEq] at same
    exact .cons (argument_backward σ same.1 (named _ List.mem_cons_self))
      (arguments_backward σ same.2 (fun other member => named other (List.mem_cons_of_mem _ member)))

/-! ## The bridge -/

/-- **Datalog matching is `match`.** For a schema without anonymous
arguments, some Datalog assignment matches it against a fact exactly when its
encoding matches the encoded fact. -/
theorem atom_matches_iff (schema : Mettapedia.Languages.Datalog.Atom)
    (fact : Mettapedia.Languages.Datalog.GroundFact)
    (named : ∀ argument ∈ schema.arguments, argument ≠ .anonymous) :
    (∃ model, schema.Matches model fact) ↔ Matches (encSchema schema) (encFact fact) := by
  constructor
  · rintro ⟨model, sameRelation, arguments⟩
    refine ⟨toSubst model, ?_⟩
    simp only [encSchema, encFact, subst, substList_eq_map, List.map_cons, Atom.expression.injEq,
      List.cons.injEq]
    refine ⟨?_, arguments_forward model arguments named⟩
    rw [subst_of_vars_eq_nil _ _ (encRelation_vars _), sameRelation]
  · rintro ⟨σ, solved⟩
    simp only [encSchema, encFact, subst, substList_eq_map, List.map_cons, Atom.expression.injEq,
      List.cons.injEq] at solved
    refine ⟨toModel σ, ?_, arguments_backward σ solved.2 named⟩
    rw [subst_of_vars_eq_nil _ _ (encRelation_vars _)] at solved
    exact encRelation_injective solved.1

variable {O : Type*} [DecidableEq O]

/-- The answers of the `match` encoding over an encoded fact base are the
occurrences whose fact the schema matches in Datalog. -/
theorem match_answers_are_datalog_matches {facts : O → Mettapedia.Languages.Datalog.GroundFact}
    {schema : Mettapedia.Languages.Datalog.Atom} {template : Atom}
    {before : Configuration Atom O}
    (prepared : Prepared (fun o => encFact (facts o)) (encSchema schema) template before)
    (named : ∀ argument ∈ schema.arguments, argument ≠ .anonymous) (o : O) :
    o ∈ answerOccurrences (fun o => encFact (facts o)) (encSchema schema) template before ↔
      o ∈ before.present ∧ ∃ model, schema.Matches model (facts o) := by
  rw [mem_answerOccurrences_iff prepared, atom_matches_iff schema (facts o) named]

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsExec in
/-- A row of a one-source MM2 exec over an encoded fact base is a Datalog
match of the source schema against a stored fact. -/
theorem exec_rows_are_datalog_matches (schema : Mettapedia.Languages.Datalog.Atom)
    (named : ∀ argument ∈ schema.arguments, argument ≠ .anonymous)
    (space : Finset Atom) (exec : Exec) (sources : exec.sources = [encSchema schema])
    (encoded : ∀ a ∈ space.erase exec.self, ∃ fact, a = encFact fact) :
    (∃ σ, Row space exec σ) ↔
      ∃ fact, encFact fact ∈ space.erase exec.self ∧ ∃ model, schema.Matches model fact := by
  constructor
  · rintro ⟨σ, row⟩
    have inside := row (encSchema schema) (by simp [sources])
    obtain ⟨fact, same⟩ := encoded _ inside
    exact ⟨fact, same ▸ inside, (atom_matches_iff schema fact named).mpr ⟨σ, same⟩⟩
  · rintro ⟨fact, inside, matched⟩
    obtain ⟨σ, solved⟩ := (atom_matches_iff schema fact named).mp matched
    refine ⟨σ, ?_⟩
    intro p member
    rw [sources, List.mem_singleton] at member
    subst member
    rw [solved]
    exact inside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsDatalog
