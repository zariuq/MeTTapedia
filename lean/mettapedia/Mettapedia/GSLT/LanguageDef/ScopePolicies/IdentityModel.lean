import Mettapedia.GSLT.LanguageDef.ScopePolicies.Translators

/-!
# The translator from rule M in the identity model, and the degrees of the explicit form

## In the identity model

In the identity model of `TemplateScope.LexicalFresh` the translation is exact:
lexical fresh elaborates the translated program to the very judgment that rule
M elaborates the source to (`run_toLexical`).  So there the translator is a
hosting map with no renaming at all: the static equivalence is identity of
judgments, the domain is every program, and the discipline is arbitrary.

* `idCoreGSLT` — the identity-model core: judgments and observations, compared
  by identity; evaluation as reduction.
* `idPolicy` — rule M, or lexical fresh, read along its identity-model
  elaboration, at a discipline.
* `toLexicalIdMap`, `toLexicalIdMap_hosting` — `toLexical` as a hosting map
  between them, for every program.

## Degrees

`ContextTheory.Embeds` (a morphism that is hosting and exhausting) is the
existing preorder on theories.  `explicitCapture_embeds_explicit` and
`explicit_embeds_explicitCapture`: explicit capture and the theory of explicit
programs, read under any ownership policy, embed in each other.

The other three ownership policies are hosted by the theory of explicit
programs on a domain: `queryWide_hosted_by_explicit` and
`lexicalFresh_hosted_by_explicit` on programs whose lambdas carry no crossing
set, `mercury_hosted_by_explicit` on admissible such programs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

universe u v

/-- A term of the identity-model core: a judgment still to run, or an
observation. -/
inductive IdCore (S : Type u) (X : Type v) where
  | run (d : Disc) (prog : S → Option (Tm S (BId X))) (t : Tm S (BId X))
  | done (bag : Result S (BId X))

/-- An authored term for the identity model: a program, or an observation. -/
inductive IdAuthored (S : Type u) (X : Type v) where
  | program (text : Program S X)
  | done (bag : Result S (BId X))

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- The identity-model elaboration of a reading, at a discipline. -/
def idElabState (reading : Reading) (d : Disc) (u : X) (unit : S) : IdAuthored S X → IdCore S X
  | .program text => .run d (reading.idProg u unit text.clauses) (reading.idQuery text.query)
  | .done bag => .done bag

/-- Translate the program of an authored term. -/
def IdAuthored.mapProgram (convert : Program S X → Program S X) : IdAuthored S X → IdAuthored S X
  | .program text => .program (convert text)
  | .done bag => .done bag

/-- **The translation is exact in the identity model**: one judgment. -/
theorem idElabState_toLexical (d : Disc) (u : X) (unit : S) (term : IdAuthored S X) :
    idElabState .lexicalFresh d u unit (term.mapProgram toLexProgram) =
      idElabState .mercury d u unit term := by
  cases term with
  | program text =>
      have programs : Reading.lexicalFresh.idProg u unit (toLexProgram text).clauses =
          Reading.mercury.idProg u unit text.clauses := progLF_toLexicalProg u unit text.clauses
      have queries : Reading.lexicalFresh.idQuery (toLexProgram text).query =
          Reading.mercury.idQuery text.query := elabLFFormAt_toLexicalAt [] text.query
      simp only [idElabState, IdAuthored.mapProgram, programs, queries]
  | done bag => rfl

variable [DecidableEq S]

/-- Evaluation in the identity model. -/
def IdEvaluates : IdCore S X → IdCore S X → Prop
  | .run d prog t, .done bag => ∃ n, run d prog n [] Store.empty t = some bag
  | _, _ => False

/-- **The identity-model core, as a theory**: terms compared by identity,
evaluation as reduction. -/
def idCoreGSLT (S : Type u) (X : Type v) [DecidableEq X] [DecidableEq S] : GSLT.{max u v} where
  Term := IdCore S X
  equations := ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
  rewrites := IdEvaluates
  rewrites_resp_left := by
    rintro term _ next rfl evaluates
    exact ⟨next, evaluates, rfl⟩
  rewrites_resp_right := by
    rintro term next _ evaluates rfl
    exact evaluates

/-- Every reduct is an observation, and an observation is the elaboration of
itself. -/
theorem idElabState_readingClosed (reading : Reading) (d : Disc) (u : X) (unit : S) :
    GSLT.ReadingClosed (target := idCoreGSLT S X) (idElabState reading d u unit) := by
  intro origin value step
  cases value with
  | run _ _ _ => cases hOrigin : idElabState reading d u unit origin <;>
      (rw [hOrigin] at step; exact step.elim)
  | done bag => exact ⟨.done bag, rfl⟩

/-- **A reading, as a theory on authored text**: the identity-model core read
along the reading's elaboration, at a discipline. -/
def idPolicy (reading : Reading) (d : Disc) (u : X) (unit : S) : GSLT.{max u v} :=
  (idCoreGSLT S X).readAlong (idElabState reading d u unit)

/-- **`toLexical` in the identity model, as a map of theories**, for every
program and at every discipline. -/
def toLexicalIdMap (d : Disc) (u : X) (unit : S) :
    ContextMap (idPolicy (S := S) (X := X) .mercury d u unit).termsAlone
      (idPolicy (S := S) (X := X) .lexicalFresh d u unit).termsAlone :=
  GSLT.translate (target := idCoreGSLT S X) (idElabState .mercury d u unit)
    (idElabState .lexicalFresh d u unit) (IdAuthored.mapProgram toLexProgram)
    (idElabState_toLexical d u unit)

/-- **It is hosting**, from `run_toLexical` alone: no renaming, no condition on
the text, any discipline. -/
theorem toLexicalIdMap_hosting (d : Disc) (u : X) (unit : S) :
    (toLexicalIdMap (S := S) (X := X) d u unit).Hosting :=
  GSLT.translate_hosting _ _ _ _ (idElabState_readingClosed .mercury d u unit)

/-- Positive: a symbol runs to itself in the identity model. -/
theorem idSymbol_steps (d : Disc) (s : S) :
    (idCoreGSLT S X).rewrites (.run d (fun _ => none) (.sym s)) (.done [(.sym s, Store.empty)]) :=
  ⟨1, rfl⟩

/-- Negative: an observation has no step in the identity model. -/
theorem idDone_no_step (bag : Result S (BId X)) (next : IdCore S X) :
    ¬ (idCoreGSLT S X).rewrites (.done bag) next := by
  intro step
  cases next <;> exact step.elim

/-! ## Degrees of the explicit form -/

/-- **Explicit capture embeds in the theory of explicit programs**, read under
any ownership policy: the map that writes out what explicit capture inferred
is hosting and exhausting. -/
theorem explicitCapture_embeds_explicit (ownership : Ownership) (lifetime : Lifetime)
    (readout : Readout) (u : X) (unit : S) :
    ContextTheory.Embeds
      (policyOn (S := S) (X := X) ⟨.explicitCapture, lifetime, readout⟩ u unit fun _ => True).termsAlone
      (policyOn (S := S) (X := X) ⟨ownership, lifetime, readout⟩ u unit Program.Explicit).termsAlone :=
  have hosting := explicitCapture_hosted_by_explicit (S := S) ownership lifetime readout u unit
  ⟨ContextMorphism.ofTransitions _ hosting.preserves hosting.reflects, hosting,
    explicit_hosts_explicitCapture_exhausting ownership lifetime readout u unit⟩

/-- **And the theory of explicit programs embeds in explicit capture**: the
identity on text is hosting, and exhausting because every program of explicit
capture elaborates as its explicit form. -/
theorem explicit_embeds_explicitCapture (ownership : Ownership) (lifetime : Lifetime)
    (readout : Readout) (u : X) (unit : S) :
    ContextTheory.Embeds
      (policyOn (S := S) (X := X) ⟨ownership, lifetime, readout⟩ u unit Program.Explicit).termsAlone
      (policyOn (S := S) (X := X) ⟨.explicitCapture, lifetime, readout⟩ u unit fun _ => True).termsAlone := by
  have hosting := explicit_hosted (S := S) ownership .explicitCapture lifetime readout u unit
    (fun _ => True) (fun _ _ => trivial)
  refine ⟨ContextMorphism.ofTransitions _ hosting.preserves hosting.reflects, hosting, ?_⟩
  show (translator (translates_explicit (S := S) ownership .explicitCapture lifetime readout u unit)
    fun _ _ => trivial).Exhausting
  rw [translator_exhausting_iff]
  intro text' _
  refine ⟨text'.map explicateEC, text'.explicit_map_explicateEC, ?_⟩
  rw [elabState_explicateEC ownership lifetime readout u unit text']
  exact .refl _

omit [DecidableEq S] [DecidableEq X] in
/-- The explicit forms of a program under the query-wide policy and under
lexical fresh are explicit programs. -/
theorem Program.explicit_map_explicateQ (text : Program S X) : (text.map explicateQ).Explicit :=
  text.all_true.map fun t _ => explicit_explicateQ t

omit [DecidableEq S] in
theorem Program.explicit_map_explicateLF (text : Program S X) :
    (text.map (explicateLF [])).Explicit :=
  text.all_true.map fun t _ => explicit_explicateLF t []

/-- **The query-wide policy is hosted by the theory of explicit programs**, on
programs whose lambdas carry no crossing set. -/
theorem queryWide_hosted_by_explicit (ownership : Ownership) (lifetime : Lifetime)
    (readout : Readout) (u : X) (unit : S) :
    (translator (domain' := Program.Explicit)
      (translates_explicateQ (S := S) ownership lifetime readout u unit)
      fun text _ => text.explicit_map_explicateQ).Hosting :=
  translator_hosting _ _

/-- **Lexical fresh is hosted by the theory of explicit programs**, on programs
whose lambdas carry no crossing set. -/
theorem lexicalFresh_hosted_by_explicit (ownership : Ownership) (lifetime : Lifetime)
    (readout : Readout) (u : X) (unit : S) :
    (translator (domain' := Program.Explicit)
      (translates_explicateLF (S := S) ownership lifetime readout u unit)
      fun text _ => text.explicit_map_explicateLF).Hosting :=
  translator_hosting _ _

/-- **Rule M is hosted by the theory of explicit programs**, on admissible
programs whose lambdas carry no crossing set, per call and reference:
translate into lexical fresh, then write the result out. -/
theorem mercury_hosted_by_explicit (ownership : Ownership) (u : X) (unit : S) :
    (translator (domain' := Program.Explicit) (translates_mercury (S := S) ownership u unit)
      fun text _ => (toLexProgram text).explicit_map_explicateLF).Hosting :=
  translator_hosting _ _

#print axioms toLexicalIdMap_hosting
#print axioms explicitCapture_embeds_explicit
#print axioms explicit_embeds_explicitCapture
#print axioms mercury_hosted_by_explicit

end Mettapedia.GSLT.LanguageDef.ScopePolicies
