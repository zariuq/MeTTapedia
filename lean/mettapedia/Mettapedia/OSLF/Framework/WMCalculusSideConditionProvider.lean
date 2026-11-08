import Mettapedia.OSLF.Framework.WMCalculusDenotationalSoundness

/-!
# Checked providers for every WM side condition

A `CheckedRelationProvider` answers every relation that a premise of the WM
calculus queries, from a list of handles and a valuation of free names.  For a
relation call it lists candidate rows: an argument that denotes stays fixed, an
argument that does not (an unbound metavariable, an output position such as the
scope of anti-hallucination or the strong channel of utility transport) ranges
over the handles.  A candidate is returned only when it denotes and the
provider's Boolean check accepts its values, and every accepted check carries a
proof of the relation's meaning (`CheckedRelationProvider.check_sound`).  So the
provider's environment certifies `meaning` under its valuation
(`providerEnv_certifies`), and the soundness theorems apply to every step and
every run under it (`provider_step_sound`, `provider_run_sound`).

Soundness is relative to the valuation, which is the provider's handle table:
a handle the table does not decode denotes nothing, and no row mentions it.

`exactProvider` decides every relation classically.  It returns exactly the
rows over its handles whose values are related (`exactProvider_rows`), so every
premise of the calculus has a sound provider that is also complete over its
handles.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusSideConditionProvider

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusPatternDenotation
open Mettapedia.OSLF.Framework.WMCalculusDenotationalSoundness
open Mettapedia.PLN.Evidence.EvidenceClass (EvidenceType)
open Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore (ConjugateEvidence)
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric (AdditiveWorldModel)

variable {State Query Ev : Type} [EvidenceType State] [ConjugateEvidence Ev]
  [AdditiveWorldModel State Query Ev]

/-- Handles, their valuation, and a Boolean decision per relation whose
acceptances are proved. -/
structure CheckedRelationProvider (M : WMModel State Query Ev) where
  handles : List Pattern
  valuation : String → Option (WMValue M)
  check : WMRelation → List (WMValue M) → Bool
  check_sound : ∀ relation values, check relation values = true → meaningAt M relation values

variable {M : WMModel State Query Ev}

namespace CheckedRelationProvider

variable (P : CheckedRelationProvider M)

/-- The candidates for one argument: the argument itself when it denotes, every
handle otherwise. -/
noncomputable def candidates (argument : Pattern) : List Pattern :=
  match denote (algebra M) P.valuation argument with
  | some _ => [argument]
  | none => P.handles

/-- A candidate row is accepted when it denotes values the check accepts. -/
noncomputable def accepts (relation : WMRelation) (row : List Pattern) : Bool :=
  match denoteList (algebra M) P.valuation row with
  | some values => P.check relation values
  | none => false

/-- The rows returned for a relation call. -/
noncomputable def rows (relation : String) (arguments : List Pattern) : List (List Pattern) :=
  match WMRelation.parse relation with
  | some parsed => ((arguments.map P.candidates).sections).filter (P.accepts parsed)
  | none => []

end CheckedRelationProvider

/-- The relation environment of a checked provider. -/
noncomputable def providerEnv (P : CheckedRelationProvider M) : RelationEnv where
  tuples := P.rows

/-- **Every returned row carries its proof**: the provider's environment
certifies the meaning of every relation under the provider's valuation. -/
theorem providerEnv_certifies (P : CheckedRelationProvider M) :
    Certifies (algebra M) (meaning M) P.valuation (providerEnv P) := by
  intro relation arguments row returned
  simp only [providerEnv, CheckedRelationProvider.rows] at returned
  cases parse : WMRelation.parse relation with
  | none => simp [parse] at returned
  | some parsed =>
      simp only [parse, List.mem_filter] at returned
      obtain ⟨_, accepted⟩ := returned
      simp only [CheckedRelationProvider.accepts] at accepted
      cases values : denoteList (algebra M) P.valuation row with
      | none => simp [values] at accepted
      | some found =>
          simp only [values] at accepted
          refine ⟨found, rfl, ?_⟩
          rw [meaning_of_parse M parse]
          exact P.check_sound parsed found accepted

/-- Under a checked provider, every step of every full vertex's congruence
closure preserves the denotation. -/
theorem provider_step_sound (P : CheckedRelationProvider M) (v : WMFullVertex)
    {source target : Pattern}
    (step : langReducesUsing (providerEnv P) (wmFullVertexLanguageDefWithCong v) source target) :
    ∀ value, denote (algebra M) P.valuation source = some value →
      denote (algebra M) P.valuation target = some value :=
  wmFullWithCong_step_sound (providerEnv_certifies P) v step

/-- And so does every run. -/
theorem provider_run_sound (P : CheckedRelationProvider M) (v : WMFullVertex)
    {source target : Pattern}
    (run : Relation.ReflTransGen
      (langReducesUsing (providerEnv P) (wmFullVertexLanguageDefWithCong v)) source target) :
    ∀ value, denote (algebra M) P.valuation source = some value →
      denote (algebra M) P.valuation target = some value :=
  wmFullWithCong_run_sound (providerEnv_certifies P) v run

/-- The provider that decides every relation classically. -/
noncomputable def exactProvider (M : WMModel State Query Ev) (handles : List Pattern)
    (valuation : String → Option (WMValue M)) : CheckedRelationProvider M where
  handles := handles
  valuation := valuation
  check relation values := @decide (meaningAt M relation values) (Classical.propDecidable _)
  check_sound _ _ accepted :=
    @of_decide_eq_true _ (Classical.propDecidable _) accepted

/-- The exact provider returns a candidate row exactly when it denotes related
values. -/
theorem exactProvider_rows (handles : List Pattern) (valuation : String → Option (WMValue M))
    {relation : String} {parsed : WMRelation} (parse : WMRelation.parse relation = some parsed)
    {arguments row : List Pattern}
    (candidate : row ∈ (arguments.map (exactProvider M handles valuation).candidates).sections) :
    row ∈ (providerEnv (exactProvider M handles valuation)).tuples relation arguments ↔
      ∃ values, denoteList (algebra M) valuation row = some values ∧
        meaningAt M parsed values := by
  simp only [providerEnv, CheckedRelationProvider.rows, parse, List.mem_filter,
    CheckedRelationProvider.accepts]
  constructor
  · rintro ⟨_, accepted⟩
    cases values : denoteList (algebra M) valuation row with
    | none =>
        simp only [exactProvider] at accepted
        simp [values] at accepted
    | some found =>
        simp only [exactProvider, values] at accepted
        exact ⟨found, rfl, @of_decide_eq_true _ (Classical.propDecidable _) accepted⟩
  · rintro ⟨found, values, related⟩
    refine ⟨candidate, ?_⟩
    simp only [exactProvider, values]
    exact @decide_eq_true _ (Classical.propDecidable _) related

#print axioms providerEnv_certifies
#print axioms provider_step_sound
#print axioms provider_run_sound
#print axioms exactProvider_rows

end Mettapedia.OSLF.Framework.WMCalculusSideConditionProvider
