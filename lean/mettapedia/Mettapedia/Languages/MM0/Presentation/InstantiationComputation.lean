import Mettapedia.GSLT.LanguageDef.ComputationContract
import Mettapedia.Languages.MM0.Presentation.InstantiationCorrespondence

/-!
# MM0 admissible instantiation as an authored computation

The authored MM0 instantiation program checks that the supplied expressions are
admissible for the formal binders — their dependencies respect the bound
variables of the target context — and then substitutes them. Its exact contract
against the independent kernel makes it an authored computation of the shared
interface. The relation is the kernel's: admissibility together with
substitution. A program that substitutes without the admissibility check
returns answers outside this relation and has no such contract.

A calculus qualification for MM0 is the next step: MM0 has no rule package in
the shared checker yet.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.InstantiationComputation

open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.Authored.Contract
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.Languages.MM0
open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.MM0.Presentation
open Mettapedia.Languages.MM0.Presentation.ComputationalContext
open Mettapedia.Languages.MM0.Presentation.ComputationalArguments
open Mettapedia.Languages.MM0.Presentation.ComputationalTyping
open Mettapedia.Languages.MM0.Presentation.ComputationalInstantiation

/-- An instantiation query: the declared term table, the formal binders, the
target context, the supplied expressions and the body. -/
structure Query where
  table : SignatureTable
  formal : Context
  target : Context
  expressions : List Preterm
  body : Preterm

/-- The kernel's meaning of instantiation: admissible expressions, and the
substituted body. -/
def Instantiates (query : Query) (result : Preterm) : Prop :=
  Substitution.Admissible (signatureOf query.table) query.formal query.target query.expressions ∧
    Preterm.Substitutes (Substitution.ofList query.expressions) query.body result

/-- **MM0 admissible instantiation is an authored computation** of the shared
interface. -/
def authored : AuthoredComputation Query Preterm where
  relation := Instantiates
  program := instantiationProgram
  host := computationalHost
  head := "mm0:instantiate-term"
  encodeQuery query :=
    [encodeTable query.table, encodeContext query.formal, encodeContext query.target,
      encodeExpressions query.expressions, encode query.body]
  encodeAnswer := encodeResult
  accepts query result := instantiation_accepts_iff query.table query.formal query.target
    query.expressions query.body result
  refuses query := by
    refine (instantiation_refuses_iff query.table query.formal query.target query.expressions
      query.body).trans ?_
    rw [Option.eq_none_iff_forall_ne_some]
    constructor
    · rintro never ⟨result, related⟩
      exact never result ((Substitution.instantiate_eq_some_iff _ _ _ _ _ _).mpr related)
    · intro never result computed
      exact never ⟨result, (Substitution.instantiate_eq_some_iff _ _ _ _ _ _).mp computed⟩

/-- The answer of an instantiation is unique. -/
theorem instantiates_functional {query : Query} {first second : Preterm}
    (left : Instantiates query first) (right : Instantiates query second) : first = second :=
  authored.relation_functional encodeResult_injective left right

/-- **Admissibility is part of the meaning**: a query whose expressions are not
admissible is refused, whatever the substitution would give. -/
theorem refused_of_inadmissible {query : Query}
    (inadmissible : ¬ Substitution.Admissible (signatureOf query.table) query.formal query.target
      query.expressions) :
    ¬ ∃ result, authored.relation query result :=
  fun ⟨_, related⟩ => inadmissible related.1

/-- Reused MM0 instantiation evidence keeps the contract under every step. -/
theorem contract_preserved :
    Holds authored ≤ derivedForwardBox (span authored) (Holds authored) :=
  holds_preserved authored

/-! ## Control: the theory belongs to the key -/

/-- A table declaring one constant term of sort zero. -/
def withConstant : SignatureTable := [(0, ⟨[], 0, ∅⟩)]

/-- Instantiating a regular binder of sort zero by that constant, in a theory
that declares it. -/
def recorded : Query := ⟨withConstant, [.regular 0 ∅], [], [.term 0], .var 0⟩

/-- The same query in a theory that declares nothing. -/
def asked : Query := ⟨[], [.regular 0 ∅], [], [.term 0], .var 0⟩

theorem recorded_instantiates : Instantiates recorded (.term 0) :=
  (Substitution.instantiate_eq_some_iff _ _ _ _ _ _).mp (by decide)

theorem asked_refused : ¬ Instantiates asked (.term 0) := by
  intro related
  have computed := (Substitution.instantiate_eq_some_iff _ _ _ _ _ _).mpr related
  revert computed
  decide

/-- The key without the theory. -/
def withoutTheory (query : Query) : Context × Context × List Preterm × Preterm :=
  (query.formal, query.target, query.expressions, query.body)

/-- **A memo keyed without the theory returns an unrelated answer**: the answer
recorded in the theory that declares the constant is returned for the theory
that does not, where the query is refused. The recorded entry itself satisfies
the contract. -/
theorem theory_free_key_unsound :
    Holds authored [(⟨recorded, Preterm.term 0, .replayed⟩ : Entry Query Preterm)] ∧
      lookupBy withoutTheory [(⟨recorded, Preterm.term 0, .replayed⟩ : Entry Query Preterm)] asked = some (Preterm.term 0) ∧
      ¬ authored.relation asked (Preterm.term 0) := by
  refine ⟨?_, coarse_key_unsound authored withoutTheory rfl asked_refused⟩
  intro entry member
  rcases List.mem_singleton.mp member with rfl
  exact ⟨recorded_instantiates, fun _ impossible => by cases impossible⟩

end Mettapedia.Languages.MM0.Presentation.InstantiationComputation
