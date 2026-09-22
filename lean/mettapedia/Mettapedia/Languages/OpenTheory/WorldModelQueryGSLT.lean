import Mettapedia.Languages.OpenTheory.WorldModelInterpretation
import Mettapedia.Languages.OpenTheory.TheoryReplay
import Mettapedia.Logic.WorldModel.GSLTRealization
import Mettapedia.OSLF.Framework.WMCalculusSemantics

/-!
# Theorem-list worlds: WM-calculus meaning and a scanning query GSLT

1. The generic reading of the WM calculus (`WMReading`, `denote`, `Agree`,
   `CoreLaws`, subject reduction at the root and at every depth) lives in
   `Mettapedia.OSLF.Framework.WMCalculusSemantics`; this file instantiates it.
2. `theoremListReading` reads `Revise` as append, `Extract` as membership,
   `Combine` as disjunction and `EvidenceZero` as `False`.  Theorems enter the
   calculus as atom names; `TheoremAtoms.ReadsBack scope` says the valuation
   reads each name back as its theorem.  `scopedAtoms` reads back any finite
   scope; a naming that identifies two distinct theorems reads back none
   containing both.  Under read-back, `encodeWorld Γ` denotes `Γ`,
   `Extract(Revise(Γ, Δ), t)` denotes `t ∈ Γ ++ Δ`, and so does every reduct,
   also under the contextual presentation that rewrites below constructors.
   The `evidence_add` step exists and its reduct denotes `t ∈ Γ ∨ t ∈ Δ`.
   Positive control: a `revision_comm` two constructors below the root of an
   encoded query is a contextual step, not a root step, and keeps the meaning.
3. Negative controls: `revision_comm` changes the denoted list and keeps only
   membership; under first-world-wins revision (not monoidal) the same
   `evidence_add` step changes the denoted proposition.  Two readings keep
   root subject reduction and lose it below the root: `cyclicOrderReading`,
   whose `Revise` does not respect state agreement at a query no atom names,
   and `combineInspectingDenote`, whose `Combine` inspects the syntax of its
   arguments and so is not a fold.
4. `scanQuery` is an `ExactQueryGSLT` for the membership realization: states
   are a remaining list with a target, or a Boolean answer; a step drops a
   non-matching head, a matching head answers `true`, `[]` answers `false`.
   Steps are the graph of an executable function using `DecidableEq Theorem`.
5. OpenTheory kernel states are requests of that machine: kernel steps
   preserve `true` answers; on states reachable from `[]` a `true` answer
   holds exactly for derivable theorems.  Every scan step leaves the remaining
   list no longer, every kernel step makes the theorem list one longer, so no
   kernel step is a scan step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT

open Mettapedia.GSLT
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.OperationalGSLT
open Mettapedia.Languages.OpenTheory.WorldModelInterpretation
open Mettapedia.Languages.OpenTheory.AxiomPolicyCanary
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures
open Mettapedia.Logic.WorldModel.GSLTRealization
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Theorem lists in the WM calculus -/

/-- Atom names for theorem lists: `name t` names the unit world `[t]` and the
query `t`; `emptyName` names the empty world.  `world` and `query` are the
valuations of state and query atoms. -/
structure TheoremAtoms where
  name : Theorem → String
  emptyName : String
  world : String → List Theorem
  query : String → Theorem

namespace TheoremAtoms

/-- The valuations read `emptyName` as `[]` and the name of every theorem of
`scope` back as that theorem. -/
def ReadsBack (atoms : TheoremAtoms) (scope : List Theorem) : Prop :=
  atoms.world atoms.emptyName = [] ∧
    ∀ t ∈ scope, atoms.world (atoms.name t) = [t] ∧ atoms.query (atoms.name t) = t

theorem ReadsBack.mono {atoms : TheoremAtoms} {scope smaller : List Theorem}
    (readsBack : atoms.ReadsBack scope) (sub : ∀ t ∈ smaller, t ∈ scope) :
    atoms.ReadsBack smaller :=
  ⟨readsBack.1, fun t member => readsBack.2 t (sub t member)⟩

end TheoremAtoms

/-- Positional atoms for a finite scope: the theorem at index `i` is named by a
string of length `i + 1`, and the empty string names the empty world.
Out-of-scope names read as `fallback`. -/
def scopedAtoms (scope : List Theorem) (fallback : Theorem) : TheoremAtoms where
  name t := String.ofList (List.replicate (scope.idxOf t + 1) 'a')
  emptyName := ""
  world atom := if atom.length = 0 then [] else [scope.getD (atom.length - 1) fallback]
  query atom := scope.getD (atom.length - 1) fallback

theorem scopedAtoms_readsBack (scope : List Theorem) (fallback : Theorem) :
    (scopedAtoms scope fallback).ReadsBack scope := by
  refine ⟨by simp [scopedAtoms], fun t member => ?_⟩
  have bound := List.idxOf_lt_length_of_mem member
  simp [scopedAtoms, List.getElem?_eq_getElem bound, List.getElem_idxOf bound]

theorem axiomP_ne_axiomQ : axiomP ≠ axiomQ := fun same =>
  onlyP_axiomQ_not_reachable (same ▸ onlyP_axiomP_reachable)

/-- Read-back makes the naming injective on the scope. -/
theorem TheoremAtoms.ReadsBack.name_injOn {atoms : TheoremAtoms} {scope : List Theorem}
    (readsBack : atoms.ReadsBack scope) : Set.InjOn atoms.name {t | t ∈ scope} := by
  intro first firstMember second secondMember sameName
  have firstBack := (readsBack.2 first firstMember).2
  have secondBack := (readsBack.2 second secondMember).2
  rw [sameName] at firstBack
  exact firstBack.symm.trans secondBack

/-- A constant naming, such as a single `Thm` token, reads back no scope
containing two distinct theorems. -/
theorem constant_naming_not_readsBack (atoms : TheoremAtoms)
    (constant : ∀ first second, atoms.name first = atoms.name second) :
    ¬ atoms.ReadsBack [axiomP, axiomQ] := fun readsBack =>
  axiomP_ne_axiomQ
    (readsBack.name_injOn (by simp) (by simp) (constant axiomP axiomQ))

/-- The theorem-list reading: `Revise` is append, `Extract` is membership,
`Combine` is disjunction, `EvidenceZero` is `False`. -/
def theoremListReading (atoms : TheoremAtoms) :
    WMReading (List Theorem) Theorem Prop where
  revise := theoremListWorld.revise
  extract := theoremListWorld.extract
  combine := Or
  zero := False
  world := atoms.world
  query := atoms.query

theorem theoremListReading_coreLaws (atoms : TheoremAtoms) :
    (theoremListReading atoms).CoreLaws where
  extract_revise _ _ _ := propext List.mem_append
  combine_comm _ _ := propext or_comm
  combine_assoc _ _ _ := propext or_assoc
  combine_zero value := or_false value

/-- A theorem list as a WM state term: a right-nested revision of unit-world
atoms ending in the empty-world atom. -/
def worldTerm (atoms : TheoremAtoms) : List Theorem → WMTerm .state
  | [] => .state atoms.emptyName
  | head :: rest => .revise (.state (atoms.name head)) (worldTerm atoms rest)

/-- `Extract(Revise(Γ, Δ), t)` as a WM evidence term. -/
def queryTerm (atoms : TheoremAtoms) (Γ Δ : List Theorem) (t : Theorem) :
    WMTerm .evidence :=
  .extract (.revise (worldTerm atoms Γ) (worldTerm atoms Δ)) (.query (atoms.name t))

/-- `Combine(Extract(Γ, t), Extract(Δ, t))` as a WM evidence term. -/
def combinedTerm (atoms : TheoremAtoms) (Γ Δ : List Theorem) (t : Theorem) :
    WMTerm .evidence :=
  .combine (.extract (worldTerm atoms Γ) (.query (atoms.name t)))
    (.extract (worldTerm atoms Δ) (.query (atoms.name t)))

/-- Pattern of the query atom for a theorem. -/
def encodeTheorem (atoms : TheoremAtoms) (t : Theorem) : Pattern :=
  encodeWM (WMTerm.query (atoms.name t))

/-- Pattern of a theorem list as a WM state. -/
def encodeWorld (atoms : TheoremAtoms) (Γ : List Theorem) : Pattern :=
  encodeWM (worldTerm atoms Γ)

/-- `Extract(Revise(Γ, Δ), t)` as a WM-calculus pattern. -/
def extractReviseQuery (atoms : TheoremAtoms) (Γ Δ : List Theorem) (t : Theorem) :
    Pattern :=
  pExtract (pRevise (encodeWorld atoms Γ) (encodeWorld atoms Δ)) (encodeTheorem atoms t)

/-- Its `evidence_add` reduct, one extraction per source world. -/
def combinedExtracts (atoms : TheoremAtoms) (Γ Δ : List Theorem) (t : Theorem) :
    Pattern :=
  pCombine (pExtract (encodeWorld atoms Γ) (encodeTheorem atoms t))
    (pExtract (encodeWorld atoms Δ) (encodeTheorem atoms t))

theorem extractReviseQuery_eq_encodeWM (atoms : TheoremAtoms)
    (Γ Δ : List Theorem) (t : Theorem) :
    extractReviseQuery atoms Γ Δ t = encodeWM (queryTerm atoms Γ Δ t) :=
  rfl

theorem combinedExtracts_eq_encodeWM (atoms : TheoremAtoms)
    (Γ Δ : List Theorem) (t : Theorem) :
    combinedExtracts atoms Γ Δ t = encodeWM (combinedTerm atoms Γ Δ t) :=
  rfl

/-- `Extract(Revise(Γ, Δ), t)` on theorem lists is disjunction of membership. -/
theorem extract_revise_is_or (Γ Δ : List Theorem) (t : Theorem) :
    theoremListWorld.extract (theoremListWorld.revise Γ Δ) t ↔
      theoremListWorld.extract Γ t ∨ theoremListWorld.extract Δ t :=
  List.mem_append

theorem extractReviseQuery_isDecomposable (atoms : TheoremAtoms)
    (Γ Δ : List Theorem) (t : Theorem) :
    isDecomposable (extractReviseQuery atoms Γ Δ t) :=
  ⟨encodeWorld atoms Γ, encodeWorld atoms Δ, encodeTheorem atoms t, rfl⟩

theorem combinedExtracts_isCombined (atoms : TheoremAtoms)
    (Γ Δ : List Theorem) (t : Theorem) :
    isCombined (combinedExtracts atoms Γ Δ t) :=
  ⟨pExtract (encodeWorld atoms Γ) (encodeTheorem atoms t),
    pExtract (encodeWorld atoms Δ) (encodeTheorem atoms t), rfl⟩

section Adequacy

variable {atoms : TheoremAtoms}

/-- Adequacy of the world encoding: under read-back, `worldTerm Γ` denotes `Γ`. -/
theorem denote_worldTerm :
    ∀ {Γ : List Theorem}, atoms.ReadsBack Γ →
      (theoremListReading atoms).denote (worldTerm atoms Γ) = Γ
  | [], readsBack => readsBack.1
  | head :: rest, readsBack => by
      have restBack : atoms.ReadsBack rest :=
        readsBack.mono fun t member => List.mem_cons_of_mem head member
      change theoremListWorld.revise (atoms.world (atoms.name head))
          ((theoremListReading atoms).denote (worldTerm atoms rest)) = head :: rest
      rw [(readsBack.2 head List.mem_cons_self).1, denote_worldTerm restBack]
      rfl

theorem encodeWorld_denotes {Γ : List Theorem} (readsBack : atoms.ReadsBack Γ) :
    (theoremListReading atoms).PatternDenotes .state (encodeWorld atoms Γ) Γ :=
  ⟨worldTerm atoms Γ, rfl, denote_worldTerm readsBack⟩

theorem denote_queryTerm {Γ Δ : List Theorem} {t : Theorem}
    (readsBack : atoms.ReadsBack (t :: (Γ ++ Δ))) :
    (theoremListReading atoms).denote (queryTerm atoms Γ Δ t) = (t ∈ Γ ++ Δ) := by
  have left : atoms.ReadsBack Γ := readsBack.mono fun _ member => by simp [member]
  have right : atoms.ReadsBack Δ := readsBack.mono fun _ member => by simp [member]
  change (atoms.query (atoms.name t) ∈
      (theoremListReading atoms).denote (worldTerm atoms Γ) ++
        (theoremListReading atoms).denote (worldTerm atoms Δ)) = (t ∈ Γ ++ Δ)
  rw [(readsBack.2 t List.mem_cons_self).2, denote_worldTerm left, denote_worldTerm right]

theorem denote_combinedTerm {Γ Δ : List Theorem} {t : Theorem}
    (readsBack : atoms.ReadsBack (t :: (Γ ++ Δ))) :
    (theoremListReading atoms).denote (combinedTerm atoms Γ Δ t) = (t ∈ Γ ∨ t ∈ Δ) := by
  have left : atoms.ReadsBack Γ := readsBack.mono fun _ member => by simp [member]
  have right : atoms.ReadsBack Δ := readsBack.mono fun _ member => by simp [member]
  change (atoms.query (atoms.name t) ∈
      (theoremListReading atoms).denote (worldTerm atoms Γ) ∨
        atoms.query (atoms.name t) ∈
          (theoremListReading atoms).denote (worldTerm atoms Δ)) = (t ∈ Γ ∨ t ∈ Δ)
  rw [(readsBack.2 t List.mem_cons_self).2, denote_worldTerm left, denote_worldTerm right]

theorem extractReviseQuery_denotes_mem_append {Γ Δ : List Theorem} {t : Theorem}
    (readsBack : atoms.ReadsBack (t :: (Γ ++ Δ))) :
    (theoremListReading atoms).PatternDenotes .evidence
      (extractReviseQuery atoms Γ Δ t) (t ∈ Γ ++ Δ) :=
  ⟨queryTerm atoms Γ Δ t, rfl, denote_queryTerm readsBack⟩

/-- Subject reduction on the query: every reduct of `Extract(Revise(Γ, Δ), t)`
at the minimal vertex denotes `t ∈ Γ ++ Δ`. -/
theorem extractReviseQuery_reduct_denotes_mem_append {Γ Δ : List Theorem} {t : Theorem}
    (readsBack : atoms.ReadsBack (t :: (Γ ++ Δ))) {pattern : Pattern}
    (reduces : LangReducesStar (wmExtVertexLanguageDef wmExtVertexMinimal)
      (extractReviseQuery atoms Γ Δ t) pattern) :
    (theoremListReading atoms).PatternDenotes .evidence pattern (t ∈ Γ ++ Δ) := by
  have denotes := (theoremListReading_coreLaws atoms).core_evidence_reduct_denotes
    (queryTerm atoms Γ Δ t) (minimalVertex_reducesStar_to_core reduces)
  rwa [denote_queryTerm readsBack] at denotes

/-- One-step form: every minimal-vertex step from `Extract(Revise(Γ, Δ), t)`
reaches a pattern denoting `t ∈ Γ ++ Δ`. -/
theorem extractReviseQuery_step_denotes_mem_append {Γ Δ : List Theorem} {t : Theorem}
    (readsBack : atoms.ReadsBack (t :: (Γ ++ Δ))) {pattern : Pattern}
    (step : langSemanticReduces (wmExtVertexLanguageDef wmExtVertexMinimal)
      (extractReviseQuery atoms Γ Δ t) pattern) :
    (theoremListReading atoms).PatternDenotes .evidence pattern (t ∈ Γ ++ Δ) :=
  extractReviseQuery_reduct_denotes_mem_append readsBack (.step step (.refl _))

/-- ◇ at `Extract(Revise(Γ, Δ), t)`: a step reaches a `Combine` pattern that
denotes `t ∈ Γ ∨ t ∈ Δ`. -/
theorem diamond_extractReviseQuery_combined_mem_or {Γ Δ : List Theorem} {t : Theorem}
    (readsBack : atoms.ReadsBack (t :: (Γ ++ Δ))) :
    langDiamond (wmExtVertexLanguageDef wmExtVertexMinimal)
      (wmExtPredicate wmExtVertexMinimal fun pattern =>
        isCombined pattern ∧
          (theoremListReading atoms).PatternDenotes .evidence pattern (t ∈ Γ ∨ t ∈ Δ))
      (extractReviseQuery atoms Γ Δ t) := by
  rw [langDiamond_spec]
  exact ⟨combinedExtracts atoms Γ Δ t,
    langReduces_to_semantic _ (wmLangReduces_evidenceAdd wmExtVertexMinimal _ _ _),
    combinedExtracts_isCombined atoms Γ Δ t,
    combinedTerm atoms Γ Δ t, rfl, denote_combinedTerm readsBack⟩

end Adequacy

/-! ## Subject reduction at every depth -/

section ContextualAdequacy

variable {atoms : TheoremAtoms}

/-- Every reduct of `Extract(Revise(Γ, Δ), t)` under the contextual
presentation, with rewrites at any depth, denotes `t ∈ Γ ++ Δ`. -/
theorem extractReviseQuery_contextual_reduct_denotes_mem_append
    {Γ Δ : List Theorem} {t : Theorem}
    (readsBack : atoms.ReadsBack (t :: (Γ ++ Δ))) {pattern : Pattern}
    (reduces : LangReducesStar (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      (extractReviseQuery atoms Γ Δ t) pattern) :
    (theoremListReading atoms).PatternDenotes .evidence pattern (t ∈ Γ ++ Δ) := by
  have denotes := (theoremListReading_coreLaws atoms).contextual_evidence_reduct_denotes
    (queryTerm atoms Γ Δ t) reduces
  rwa [denote_queryTerm readsBack] at denotes

/-- `Extract(Revise(Revise(rest, head), Δ), t)`: the query `queryTerm (head ::
rest) Δ t` with the two arguments of the first revision of its left world
swapped. -/
def innerSwapTerm (atoms : TheoremAtoms) (head : Theorem) (rest Δ : List Theorem)
    (t : Theorem) : WMTerm .evidence :=
  .extract (.revise (.revise (worldTerm atoms rest) (.state (atoms.name head)))
    (worldTerm atoms Δ)) (.query (atoms.name t))

/-- Positive control.  Swapping the arguments of the `Revise` two constructors
below the root of `Extract(Revise(head :: rest, Δ), t)` is a step of the
contextual presentation and not a step of the root-only minimal vertex; its
reduct denotes the same membership fact. -/
theorem innerSwap_contextual_not_root_preserves_mem_append {head : Theorem} {rest Δ : List Theorem}
    {t : Theorem} (readsBack : atoms.ReadsBack (t :: (head :: rest ++ Δ))) :
    langSemanticReduces (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
        (extractReviseQuery atoms (head :: rest) Δ t)
        (encodeWM (innerSwapTerm atoms head rest Δ t)) ∧
      ¬ langSemanticReduces (wmExtVertexLanguageDef wmExtVertexMinimal)
        (extractReviseQuery atoms (head :: rest) Δ t)
        (encodeWM (innerSwapTerm atoms head rest Δ t)) ∧
      (theoremListReading atoms).PatternDenotes .evidence
        (encodeWM (innerSwapTerm atoms head rest Δ t)) (t ∈ head :: rest ++ Δ) := by
  have step : WMContextStep (queryTerm atoms (head :: rest) Δ t)
      (innerSwapTerm atoms head rest Δ t) :=
    .extract_left _ (.revise_left _ (.root (.revision_comm _ _)))
  have contextual := (wmContextStep_iff _ _).mp step
  refine ⟨contextual, fun rootStep => ?_,
    extractReviseQuery_contextual_reduct_denotes_mem_append readsBack
      (.step contextual (.refl _))⟩
  have coreStep := (wmStep_iff (queryTerm atoms (head :: rest) Δ t)
    (innerSwapTerm atoms head rest Δ t)).mpr ((minimalVertex_step_iff_core _ _).mp rootStep)
  cases coreStep

end ContextualAdequacy

/-! ## Negative controls -/

/-- `revision_comm` is a WM step whose two sides denote different theorem
lists with the same members: state denotation is preserved only up to
extraction. -/
theorem revisionComm_changes_list_keeps_membership (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    WMStep (WMTerm.revise (.state (atoms.name axiomP)) (.state (atoms.name axiomQ)))
        (WMTerm.revise (.state (atoms.name axiomQ)) (.state (atoms.name axiomP))) ∧
      (theoremListReading atoms).denote
          (WMTerm.revise (.state (atoms.name axiomP)) (.state (atoms.name axiomQ))) ≠
        (theoremListReading atoms).denote
          (WMTerm.revise (.state (atoms.name axiomQ)) (.state (atoms.name axiomP))) ∧
      (theoremListReading atoms).Agree .state
        ((theoremListReading atoms).denote
          (WMTerm.revise (.state (atoms.name axiomP)) (.state (atoms.name axiomQ))))
        ((theoremListReading atoms).denote
          (WMTerm.revise (.state (atoms.name axiomQ)) (.state (atoms.name axiomP)))) := by
  have unitP := (readsBack.2 axiomP (by simp)).1
  have unitQ := (readsBack.2 axiomQ (by simp)).1
  refine ⟨.revision_comm _ _, ?_,
    (theoremListReading_coreLaws atoms).agree_of_step (.revision_comm _ _)⟩
  change atoms.world (atoms.name axiomP) ++ atoms.world (atoms.name axiomQ) ≠
    atoms.world (atoms.name axiomQ) ++ atoms.world (atoms.name axiomP)
  rw [unitP, unitQ]
  intro same
  exact axiomP_ne_axiomQ (List.cons.inj same).1

/-- First-world-wins revision: `revise Γ Δ = Γ`, with membership extraction.
It has no left unit, so it is not monoidal. -/
def firstWinsReading (atoms : TheoremAtoms) : WMReading (List Theorem) Theorem Prop where
  revise first _ := first
  extract Γ t := t ∈ Γ
  combine := Or
  zero := False
  world := atoms.world
  query := atoms.query

theorem firstWins_not_left_unital (atoms : TheoremAtoms) :
    ¬ ∀ Γ : List Theorem, (firstWinsReading atoms).revise [] Γ = Γ := fun unital =>
  List.cons_ne_nil axiomP [] (unital [axiomP]).symm

/-- Extraction does not send first-world-wins revision to combination. -/
theorem firstWins_extract_not_additive (atoms : TheoremAtoms) :
    ¬ ∀ first second query,
      (firstWinsReading atoms).extract ((firstWinsReading atoms).revise first second) query =
        (firstWinsReading atoms).combine ((firstWinsReading atoms).extract first query)
          ((firstWinsReading atoms).extract second query) := fun distributes => by
  have law := distributes [] [axiomP] axiomP
  change (axiomP ∈ ([] : List Theorem)) = (axiomP ∈ ([] : List Theorem) ∨ axiomP ∈ [axiomP])
    at law
  exact List.not_mem_nil (law ▸ Or.inr List.mem_cons_self)

/-- Atoms reading back `[axiomP]`. -/
def axiomPAtoms : TheoremAtoms := scopedAtoms [axiomP] axiomP

/-- The `evidence_add` step exists at the minimal vertex from
`Extract(Revise([], [axiomP]), axiomP)`; under first-world-wins revision the
source denotes a false proposition and the reduct a true one. -/
theorem firstWins_evidenceAdd_changes_meaning :
    langSemanticReduces (wmExtVertexLanguageDef wmExtVertexMinimal)
        (extractReviseQuery axiomPAtoms [] [axiomP] axiomP)
        (combinedExtracts axiomPAtoms [] [axiomP] axiomP) ∧
      ¬ (firstWinsReading axiomPAtoms).denote (queryTerm axiomPAtoms [] [axiomP] axiomP) ∧
      (firstWinsReading axiomPAtoms).denote (combinedTerm axiomPAtoms [] [axiomP] axiomP) := by
  have readsBack : axiomPAtoms.ReadsBack [axiomP] := scopedAtoms_readsBack [axiomP] axiomP
  have emptyBack : axiomPAtoms.world axiomPAtoms.emptyName = [] := readsBack.1
  have unitBack := readsBack.2 axiomP List.mem_cons_self
  refine ⟨langReduces_to_semantic _ (wmLangReduces_evidenceAdd wmExtVertexMinimal _ _ _),
    ?_, ?_⟩
  · change ¬ axiomPAtoms.query (axiomPAtoms.name axiomP) ∈
      axiomPAtoms.world axiomPAtoms.emptyName
    rw [emptyBack]
    exact List.not_mem_nil
  · change axiomPAtoms.query (axiomPAtoms.name axiomP) ∈
        axiomPAtoms.world axiomPAtoms.emptyName ∨
      axiomPAtoms.query (axiomPAtoms.name axiomP) ∈
        axiomPAtoms.world (axiomPAtoms.name axiomP)
    rw [unitBack.1, unitBack.2]
    exact Or.inr List.mem_cons_self

/-- Under the append reading the same step keeps the meaning. -/
theorem append_evidenceAdd_keeps_meaning :
    (theoremListReading axiomPAtoms).denote (queryTerm axiomPAtoms [] [axiomP] axiomP) =
      (theoremListReading axiomPAtoms).denote
        (combinedTerm axiomPAtoms [] [axiomP] axiomP) :=
  (theoremListReading_coreLaws axiomPAtoms).agree_of_step (.evidence_add _ _ _)

/-! ### A compositional reading whose `Revise` is not a congruence -/

/-- `[P, Q, P, Q]`, the cyclic word observed by `cyclicOrderExtract`. -/
def cyclicWord : List Theorem := [axiomP, axiomQ, axiomP, axiomQ]

/-- Extraction with one query beyond the named ones: `some t` asks membership
of `t`; `none` asks whether the world is a rotation of `cyclicWord`. -/
def cyclicOrderExtract : List Theorem → Option Theorem → Prop
  | Γ, some t => t ∈ Γ
  | Γ, none => Γ ~r cyclicWord

/-- Append revision, `cyclicOrderExtract`, disjunction.  Atoms name only
`some` queries, so the cyclic query `none` is outside the calculus. -/
def cyclicOrderReading (atoms : TheoremAtoms) :
    WMReading (List Theorem) (Option Theorem) Prop where
  revise := List.append
  extract := cyclicOrderExtract
  combine := Or
  zero := False
  world := atoms.world
  query name := some (atoms.query name)

/-- Every root `WMStep` preserves the cyclic-order denotation. -/
theorem cyclicOrder_agree_of_step (atoms : TheoremAtoms) {s : WMSort}
    {source target : WMTerm s} (step : WMStep source target) :
    (cyclicOrderReading atoms).Agree s ((cyclicOrderReading atoms).denote source)
      ((cyclicOrderReading atoms).denote target) := by
  cases step with
  | evidence_add first second query =>
      cases query with
      | query name => exact propext List.mem_append
  | revision_comm first second =>
      intro query
      cases query with
      | some t => exact propext (List.perm_append_comm.mem_iff)
      | none =>
          exact propext ⟨fun rotated => List.isRotated_append.trans rotated,
            fun rotated => List.isRotated_append.trans rotated⟩
  | revision_assoc first second third =>
      intro query
      change cyclicOrderExtract (_ ++ _ ++ _) query = cyclicOrderExtract (_ ++ (_ ++ _)) query
      rw [List.append_assoc]
  | combine_comm first second => exact propext or_comm
  | combine_zero value => exact or_false _

/-- `Revise(P, Q)`. -/
def reviseTermPQ (atoms : TheoremAtoms) : WMTerm .state :=
  .revise (.state (atoms.name axiomP)) (.state (atoms.name axiomQ))

/-- `Revise(Q, P)`. -/
def reviseTermQP (atoms : TheoremAtoms) : WMTerm .state :=
  .revise (.state (atoms.name axiomQ)) (.state (atoms.name axiomP))

theorem qppq_not_isRotated_cyclicWord :
    ¬ [axiomQ, axiomP, axiomP, axiomQ] ~r cyclicWord := by
  rintro ⟨n, rotated⟩
  rw [← List.rotate_mod] at rotated
  have bound : n % 4 < 4 := Nat.mod_lt n (by decide)
  generalize n % 4 = k at rotated bound
  interval_cases k <;>
    simp [cyclicWord, List.rotate, axiomP_ne_axiomQ, axiomP_ne_axiomQ.symm] at rotated

/-- Negative control.  `Revise(Revise(P, Q), Revise(P, Q))` steps to
`Revise(Revise(Q, P), Revise(P, Q))` by `revision_comm` below the root, also in
the contextual presentation.  Under the cyclic-order reading the inner
redex and its reduct agree, as root subject reduction says, but the two whole
states disagree: `[P, Q, P, Q]` is a rotation of `cyclicWord` and
`[Q, P, P, Q]` is not. -/
theorem cyclicOrder_innerSwap_breaks_agreement (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    WMContextStep (.revise (reviseTermPQ atoms) (reviseTermPQ atoms))
        (.revise (reviseTermQP atoms) (reviseTermPQ atoms)) ∧
      langSemanticReduces (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
        (encodeWM (WMTerm.revise (reviseTermPQ atoms) (reviseTermPQ atoms)))
        (encodeWM (WMTerm.revise (reviseTermQP atoms) (reviseTermPQ atoms))) ∧
      (cyclicOrderReading atoms).Agree .state
        ((cyclicOrderReading atoms).denote (reviseTermPQ atoms))
        ((cyclicOrderReading atoms).denote (reviseTermQP atoms)) ∧
      ¬ (cyclicOrderReading atoms).Agree .state
        ((cyclicOrderReading atoms).denote
          (.revise (reviseTermPQ atoms) (reviseTermPQ atoms)))
        ((cyclicOrderReading atoms).denote
          (.revise (reviseTermQP atoms) (reviseTermPQ atoms))) := by
  have step : WMContextStep (.revise (reviseTermPQ atoms) (reviseTermPQ atoms))
      (.revise (reviseTermQP atoms) (reviseTermPQ atoms)) :=
    .revise_left _ (.root (.revision_comm _ _))
  refine ⟨step, (wmContextStep_iff _ _).mp step,
    cyclicOrder_agree_of_step atoms (.revision_comm _ _), fun agree => ?_⟩
  have unitP := (readsBack.2 axiomP (by simp)).1
  have unitQ := (readsBack.2 axiomQ (by simp)).1
  have atCyclicQuery := agree none
  change cyclicOrderExtract
      ((atoms.world (atoms.name axiomP) ++ atoms.world (atoms.name axiomQ)) ++
        (atoms.world (atoms.name axiomP) ++ atoms.world (atoms.name axiomQ))) none =
    cyclicOrderExtract
      ((atoms.world (atoms.name axiomQ) ++ atoms.world (atoms.name axiomP)) ++
        (atoms.world (atoms.name axiomP) ++ atoms.world (atoms.name axiomQ))) none
    at atCyclicQuery
  rw [unitP, unitQ] at atCyclicQuery
  simp only [cyclicOrderExtract, List.cons_append, List.nil_append] at atCyclicQuery
  exact qppq_not_isRotated_cyclicWord (cast atCyclicQuery (List.IsRotated.refl cyclicWord))

/-- The same step keeps agreement at every named query: the disagreement is
confined to the cyclic query `none`, which no atom names. -/
theorem cyclicOrder_innerSwap_keeps_named_queries (atoms : TheoremAtoms) :
    (cyclicOrderReading atoms).NamedQueryAgree .state
      (.revise (reviseTermPQ atoms) (reviseTermPQ atoms))
      (.revise (reviseTermQP atoms) (reviseTermPQ atoms)) :=
  WMReading.namedQueryAgree_of_contextStep_of_root (cyclicOrder_agree_of_step atoms)
    (.revise_left _ (.root (.revision_comm _ _)))

/-- The cyclic-order `Revise` does not respect state agreement, so the
reading fails `CoreLaws`: root subject reduction holds for every step, and
contextual subject reduction fails. -/
theorem cyclicOrder_not_reviseRespectsAgree (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    ¬ (cyclicOrderReading atoms).ReviseRespectsAgree := fun revise =>
  (cyclicOrder_innerSwap_breaks_agreement atoms readsBack).2.2.2
    (WMReading.agree_of_contextStep_of_root revise (cyclicOrder_agree_of_step atoms)
      (cyclicOrder_innerSwap_breaks_agreement atoms readsBack).1)

theorem cyclicOrder_not_coreLaws (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    ¬ (cyclicOrderReading atoms).CoreLaws := fun laws =>
  cyclicOrder_not_reviseRespectsAgree atoms readsBack laws.reviseRespectsAgree

/-! ### A non-compositional evidence denotation -/

/-- Whether a term is syntactically a `Combine`. -/
def isCombineTerm : {s : WMSort} → WMTerm s → Bool
  | _, .combine _ _ => true
  | _, _ => false

/-- A denotation whose `Combine` inspects syntax: `Combine(e₁, e₂)` is read
as `⟦e₁⟧ ∨ ⟦e₂⟧`, and also holds when both arguments are syntactically
`Combine` terms.  Every other constructor is read as in
`theoremListReading`. -/
def combineInspectingDenote (atoms : TheoremAtoms) :
    {s : WMSort} → WMTerm s → SortValue (List Theorem) Theorem Prop s
  | _, .state name => atoms.world name
  | _, .query name => atoms.query name
  | _, .revise first second =>
      theoremListWorld.revise (combineInspectingDenote atoms first)
        (combineInspectingDenote atoms second)
  | _, .extract world query =>
      theoremListWorld.extract (combineInspectingDenote atoms world)
        (combineInspectingDenote atoms query)
  | _, .combine first second =>
      combineInspectingDenote atoms first ∨ combineInspectingDenote atoms second ∨
        (isCombineTerm first && isCombineTerm second) = true
  | _, .zero => False

/-- `combineInspectingDenote` agreement, compared by the agreement of
`theoremListReading`. -/
def CombineInspectingAgree (atoms : TheoremAtoms) (s : WMSort)
    (first second : WMTerm s) : Prop :=
  (theoremListReading atoms).Agree s (combineInspectingDenote atoms first)
    (combineInspectingDenote atoms second)

/-- Every root `WMStep` preserves the syntax-inspecting denotation. -/
theorem combineInspecting_agree_of_step (atoms : TheoremAtoms) {s : WMSort}
    {source target : WMTerm s} (step : WMStep source target) :
    CombineInspectingAgree atoms s source target := by
  cases step with
  | evidence_add first second query =>
      change (combineInspectingDenote atoms query ∈
          combineInspectingDenote atoms first ++ combineInspectingDenote atoms second) =
        ((combineInspectingDenote atoms query ∈ combineInspectingDenote atoms first) ∨
          (combineInspectingDenote atoms query ∈ combineInspectingDenote atoms second) ∨
            (false && false) = true)
      simp only [Bool.and_false, Bool.false_eq_true, or_false]
      exact propext List.mem_append
  | revision_comm first second =>
      intro query
      exact propext List.perm_append_comm.mem_iff
  | revision_assoc first second third =>
      intro query
      change (query ∈ (_ ++ _ ++ _ : List Theorem)) = (query ∈ (_ ++ (_ ++ _) : List Theorem))
      rw [List.append_assoc]
  | combine_comm first second =>
      change (combineInspectingDenote atoms first ∨ combineInspectingDenote atoms second ∨
          (isCombineTerm first && isCombineTerm second) = true) =
        (combineInspectingDenote atoms second ∨ combineInspectingDenote atoms first ∨
          (isCombineTerm second && isCombineTerm first) = true)
      rw [Bool.and_comm]
      exact propext or_left_comm
  | combine_zero value =>
      change (combineInspectingDenote atoms value ∨ False ∨
          (isCombineTerm value && false) = true) = combineInspectingDenote atoms value
      simp

/-- `Combine(Extract(Revise(∅, ∅), t), Combine(0, 0))`. -/
def inspectedSourceTerm (atoms : TheoremAtoms) (t : Theorem) : WMTerm .evidence :=
  .combine (queryTerm atoms [] [] t) (.combine .zero .zero)

/-- `Combine(Combine(Extract(∅, t), Extract(∅, t)), Combine(0, 0))`. -/
def inspectedTargetTerm (atoms : TheoremAtoms) (t : Theorem) : WMTerm .evidence :=
  .combine (combinedTerm atoms [] [] t) (.combine .zero .zero)

/-- Negative control.  `evidence_add` below the left argument of a `Combine`
is a contextual step from an encoded evidence term containing the query
`Extract(Revise(∅, ∅), t)`.  Root subject reduction holds for the
syntax-inspecting denotation (`combineInspecting_agree_of_step`), yet the
source denotes a false proposition and the reduct a true one, because the
step turns the left argument into a `Combine`.  The fold
`theoremListReading` keeps the meaning of the same step. -/
theorem combineInspecting_innerEvidenceAdd_changes_meaning {atoms : TheoremAtoms}
    {t : Theorem} (readsBack : atoms.ReadsBack [t]) :
    WMContextStep (inspectedSourceTerm atoms t) (inspectedTargetTerm atoms t) ∧
      langSemanticReduces (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
        (encodeWM (inspectedSourceTerm atoms t)) (encodeWM (inspectedTargetTerm atoms t)) ∧
      ¬ combineInspectingDenote atoms (inspectedSourceTerm atoms t) ∧
      combineInspectingDenote atoms (inspectedTargetTerm atoms t) ∧
      (theoremListReading atoms).denote (inspectedSourceTerm atoms t) =
        (theoremListReading atoms).denote (inspectedTargetTerm atoms t) := by
  have step : WMContextStep (inspectedSourceTerm atoms t) (inspectedTargetTerm atoms t) :=
    .combine_left _ (.root (.evidence_add _ _ _))
  have emptyWorld : atoms.world atoms.emptyName = [] := readsBack.1
  refine ⟨step, (wmContextStep_iff _ _).mp step, ?_, ?_,
    (theoremListReading_coreLaws atoms).agree_of_contextStep step⟩
  · change ¬ ((atoms.query (atoms.name t) ∈
        atoms.world atoms.emptyName ++ atoms.world atoms.emptyName) ∨
      (False ∨ False ∨ (false && false) = true) ∨ (false && true) = true)
    simp [emptyWorld]
  · change (_ ∨ _ ∨ (false && false) = true) ∨ (False ∨ False ∨ (false && false) = true) ∨
      (true && true) = true
    simp

/-- The syntax-inspecting agreement is not a congruence. -/
theorem combineInspectingAgree_not_congruence {atoms : TheoremAtoms} {t : Theorem}
    (readsBack : atoms.ReadsBack [t]) :
    ¬ WMTermCongruence (fun {s} first second => CombineInspectingAgree atoms s first second) :=
  fun congruence => by
    obtain ⟨step, -, notSource, target, -⟩ :=
      combineInspecting_innerEvidenceAdd_changes_meaning readsBack
    have preserved : combineInspectingDenote atoms (inspectedSourceTerm atoms t) =
        combineInspectingDenote atoms (inspectedTargetTerm atoms t) :=
      congruence.holds_of_contextStep (combineInspecting_agree_of_step atoms) step
    exact notSource (cast preserved.symm target)

/-! ## A scanning query GSLT for membership -/

def theoremListRealization :
    Realization (List Theorem) (List Theorem) Theorem Prop where
  denote := id
  empty := []
  revise := List.append
  extract := fun Γ t => t ∈ Γ
  empty_sound := rfl
  revise_sound := fun _ _ => rfl
  extract_sound := fun _ _ => rfl

/-- States of the scanning machine. -/
inductive ScanState where
  | scan (remaining : List Theorem) (target : Theorem)
  | answer (value : Bool)

/-- Drop a non-matching head; answer `true` on a matching head, `false` on `[]`. -/
inductive ScanStep : ScanState → ScanState → Prop where
  | skip (head target : Theorem) (rest : List Theorem) (differ : head ≠ target) :
      ScanStep (.scan (head :: rest) target) (.scan rest target)
  | hit (target : Theorem) (rest : List Theorem) :
      ScanStep (.scan (target :: rest) target) (.answer true)
  | miss (target : Theorem) :
      ScanStep (.scan [] target) (.answer false)

/-- The executable transition function, using `DecidableEq Theorem`. -/
def scanNext : ScanState → Option ScanState
  | .scan [] _ => some (.answer false)
  | .scan (head :: rest) target =>
      if head = target then some (.answer true) else some (.scan rest target)
  | .answer _ => none

theorem scanStep_iff_scanNext (source target : ScanState) :
    ScanStep source target ↔ scanNext source = some target := by
  constructor
  · rintro (⟨head, target, rest, differ⟩ | ⟨target, rest⟩ | ⟨target⟩) <;>
      simp [scanNext, *]
  · intro next
    match source, next with
    | .scan [] target, next =>
        simp only [scanNext, Option.some.injEq] at next
        subst next
        exact .miss target
    | .scan (head :: rest) target', next =>
        by_cases same : head = target'
        · subst same
          simp only [scanNext, if_true, Option.some.injEq] at next
          subst next
          exact .hit head rest
        · simp only [scanNext, same, if_false, Option.some.injEq] at next
          subst next
          exact .skip head target' rest same

def scanGSLT : GSLT where
  Term := ScanState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ScanStep
  rewrites_resp_left := by
    intro t t' u htt step
    exact ⟨u, htt ▸ step, rfl⟩
  rewrites_resp_right := by
    intro t u u' step huu
    exact huu ▸ step

theorem scanGSLT_step_iff (source target : ScanState) :
    scanGSLT.Step source target ↔ ScanStep source target :=
  Iff.rfl

/-- The membership verdict a state determines. -/
def ScanState.verdict : ScanState → Bool
  | .scan remaining target => decide (target ∈ remaining)
  | .answer value => value

theorem scanStep_preserves_verdict {source target : ScanState}
    (step : scanGSLT.Step source target) : target.verdict = source.verdict := by
  cases (scanGSLT_step_iff source target).mp step with
  | skip head target rest differ =>
      simp [ScanState.verdict, List.mem_cons, Ne.symm differ]
  | hit target rest => simp [ScanState.verdict]
  | miss target => simp [ScanState.verdict]

theorem rewritePath_preserves_verdict : {source target : ScanState} →
    scanGSLT.RewritePath source target → target.verdict = source.verdict
  | _, _, .nil _ => rfl
  | _, _, .cons step rest =>
      (rewritePath_preserves_verdict rest).trans (scanStep_preserves_verdict step)

theorem scan_isNormalForm_iff (state : ScanState) :
    scanGSLT.IsNormalForm state ↔ ∃ value, state = .answer value := by
  constructor
  · intro normal
    cases state with
    | scan remaining target =>
        exfalso
        cases remaining with
        | nil => exact normal ⟨_, ScanStep.miss target⟩
        | cons head rest =>
            by_cases same : head = target
            · subst same
              exact normal ⟨_, ScanStep.hit head rest⟩
            · exact normal ⟨_, ScanStep.skip head target rest same⟩
    | answer value => exact ⟨value, rfl⟩
  · rintro ⟨value, rfl⟩ ⟨next, step⟩
    cases (scanGSLT_step_iff _ next).mp step

/-- The scan from `(remaining, target)` to the verdict `target ∈ remaining`. -/
def scanPath (target : Theorem) : (remaining : List Theorem) →
    scanGSLT.RewritePath (.scan remaining target)
      (.answer (decide (target ∈ remaining)))
  | [] => by
      rw [show decide (target ∈ ([] : List Theorem)) = false by simp]
      exact .cons (ScanStep.miss target) (.nil _)
  | head :: rest =>
      if same : head = target then by
        subst same
        rw [show decide (head ∈ head :: rest) = true by simp]
        exact .cons (ScanStep.hit head rest) (.nil _)
      else by
        rw [show decide (target ∈ head :: rest) = decide (target ∈ rest) by
          simp [List.mem_cons, Ne.symm same]]
        exact .cons (ScanStep.skip head target rest same) (scanPath target rest)

/-- The scanning machine is an exact query GSLT for membership.  The semantic
value is a proposition, placed among the Boolean answers by classical
decision. -/
noncomputable def scanQuery : ExactQueryGSLT theoremListRealization where
  theory := scanGSLT
  request := fun Γ t => .scan Γ t
  answer := fun _ value => .answer (@decide value (Classical.propDecidable value))
  executePath := fun Γ t => by
    change scanGSLT.RewritePath (.scan Γ t)
      (.answer (@decide (t ∈ Γ) (Classical.propDecidable _)))
    rw [show @decide (t ∈ Γ) (Classical.propDecidable _) = decide (t ∈ Γ) from
      decide_eq_decide.mpr Iff.rfl]
    exact scanPath t Γ
  answer_normal := fun _ _ => (scan_isNormalForm_iff _).mpr ⟨_, rfl⟩
  answer_reflect := fun Γ t value path => by
    have verdict := rewritePath_preserves_verdict path
    change @decide value (Classical.propDecidable value) = decide (t ∈ Γ) at verdict
    exact propext (decide_eq_decide.mp verdict)
  covered_normal := fun _ _ terminal _ normal => by
    obtain ⟨value, rfl⟩ := (scan_isNormalForm_iff terminal).mp normal
    refine ⟨value = true, ?_⟩
    change ScanState.answer value =
      .answer (@decide (value = true) (Classical.propDecidable _))
    congr 1
    cases value
    · exact (@decide_eq_false _ (Classical.propDecidable _) Bool.false_ne_true).symm
    · exact (@decide_eq_true _ (Classical.propDecidable _) rfl).symm

theorem scan_answers_true_iff_mem (Γ : List Theorem) (t : Theorem) :
    Nonempty (scanGSLT.RewritePath (.scan Γ t) (.answer true)) ↔ t ∈ Γ := by
  constructor
  · rintro ⟨path⟩
    have verdict := rewritePath_preserves_verdict path
    change true = decide (t ∈ Γ) at verdict
    exact of_decide_eq_true verdict.symm
  · intro member
    have path := scanPath t Γ
    rw [decide_eq_true member] at path
    exact ⟨path⟩

theorem scan_answers_false_iff_not_mem (Γ : List Theorem) (t : Theorem) :
    Nonempty (scanGSLT.RewritePath (.scan Γ t) (.answer false)) ↔ t ∉ Γ := by
  constructor
  · rintro ⟨path⟩
    have verdict := rewritePath_preserves_verdict path
    change false = decide (t ∈ Γ) at verdict
    exact of_decide_eq_false verdict.symm
  · intro absent
    have path := scanPath t Γ
    rw [decide_eq_false absent] at path
    exact ⟨path⟩

/-! ## OpenTheory kernel states as scan requests -/

section Interpretation

variable (policy : AxiomPolicy)

/-- A kernel step preserves every `true` answer. -/
theorem openTheory_step_preserves_true_answer {Γ Δ : List Theorem}
    (step : (openTheoryGSLT policy).Step Γ Δ) {t : Theorem}
    (answered : Nonempty (scanGSLT.RewritePath (.scan Γ t) (.answer true))) :
    Nonempty (scanGSLT.RewritePath (.scan Δ t) (.answer true)) :=
  (scan_answers_true_iff_mem Δ t).mpr
    (expand_persists policy step t ((scan_answers_true_iff_mem Γ t).mp answered))

theorem openTheory_multiStep_preserves_true_answer {Γ Δ : List Theorem}
    (steps : (openTheoryGSLT policy).MultiStep Γ Δ) {t : Theorem}
    (answered : Nonempty (scanGSLT.RewritePath (.scan Γ t) (.answer true))) :
    Nonempty (scanGSLT.RewritePath (.scan Δ t) (.answer true)) :=
  match steps with
  | .refl _ => answered
  | .step first rest =>
      openTheory_multiStep_preserves_true_answer rest
        (openTheory_step_preserves_true_answer policy first answered)

/-- Soundness: on a state reachable from `[]`, a `true` answer is a derivable
theorem. -/
theorem derives_of_reachable_true_answer {Γ : List Theorem}
    (reachable : (openTheoryGSLT policy).MultiStep [] Γ) {t : Theorem}
    (answered : Nonempty (scanGSLT.RewritePath (.scan Γ t) (.answer true))) :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) t :=
  derives_of_reachable policy reachable ((scan_answers_true_iff_mem Γ t).mp answered)

/-- Completeness: every derivable theorem is answered `true` on some state
reachable from `[]`. -/
theorem reachable_true_answer_of_derives {t : Theorem}
    (derivable : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) t) :
    ∃ Γ : List Theorem, (openTheoryGSLT policy).MultiStep [] Γ ∧
      Nonempty (scanGSLT.RewritePath (.scan Γ t) (.answer true)) := by
  obtain ⟨Γ, reachable, member⟩ := reachable_of_derives policy derivable
  exact ⟨Γ, reachable, (scan_answers_true_iff_mem Γ t).mpr member⟩

theorem derives_iff_reachable_true_answer (t : Theorem) :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) t ↔
      ∃ Γ : List Theorem, (openTheoryGSLT policy).MultiStep [] Γ ∧
        Nonempty (scanGSLT.RewritePath (.scan Γ t) (.answer true)) :=
  ⟨reachable_true_answer_of_derives policy,
    fun ⟨_, reachable, answered⟩ => derives_of_reachable_true_answer policy reachable answered⟩

/-! ### Separation by list length -/

/-- The unscanned part of a state; an answer has none. -/
def ScanState.remaining : ScanState → List Theorem
  | .scan remaining _ => remaining
  | .answer _ => []

theorem scan_step_never_lengthens {source target : ScanState}
    (step : scanGSLT.Step source target) :
    target.remaining.length ≤ source.remaining.length := by
  cases (scanGSLT_step_iff source target).mp step <;> simp [ScanState.remaining]

theorem scan_step_between_scans_shortens {Γ Δ : List Theorem} {t t' : Theorem}
    (step : scanGSLT.Step (.scan Γ t) (.scan Δ t')) : Δ.length < Γ.length := by
  cases (scanGSLT_step_iff _ _).mp step
  simp

theorem openTheory_step_lengthens {Γ Δ : List Theorem}
    (step : (openTheoryGSLT policy).Step Γ Δ) : Δ.length = Γ.length + 1 := by
  obtain ⟨result, rfl⟩ := expand_cons_eq policy step
  rfl

theorem openTheory_step_is_not_scan_step {Γ Δ : List Theorem}
    (step : (openTheoryGSLT policy).Step Γ Δ) (t t' : Theorem) :
    ¬ scanGSLT.Step (.scan Γ t) (.scan Δ t') := fun scanStep => by
  have shorter := scan_step_between_scans_shortens scanStep
  have longer := openTheory_step_lengthens policy step
  omega

end Interpretation

#print axioms extractReviseQuery_contextual_reduct_denotes_mem_append
#print axioms innerSwap_contextual_not_root_preserves_mem_append
#print axioms cyclicOrder_agree_of_step
#print axioms qppq_not_isRotated_cyclicWord
#print axioms cyclicOrder_innerSwap_breaks_agreement
#print axioms cyclicOrder_innerSwap_keeps_named_queries
#print axioms cyclicOrder_not_reviseRespectsAgree
#print axioms cyclicOrder_not_coreLaws
#print axioms combineInspecting_agree_of_step
#print axioms combineInspecting_innerEvidenceAdd_changes_meaning
#print axioms combineInspectingAgree_not_congruence
#print axioms scopedAtoms_readsBack
#print axioms constant_naming_not_readsBack
#print axioms extract_revise_is_or
#print axioms denote_worldTerm
#print axioms encodeWorld_denotes
#print axioms TheoremAtoms.ReadsBack.name_injOn
#print axioms denote_queryTerm
#print axioms extractReviseQuery_reduct_denotes_mem_append
#print axioms extractReviseQuery_step_denotes_mem_append
#print axioms diamond_extractReviseQuery_combined_mem_or
#print axioms revisionComm_changes_list_keeps_membership
#print axioms firstWins_not_left_unital
#print axioms firstWins_extract_not_additive
#print axioms firstWins_evidenceAdd_changes_meaning
#print axioms append_evidenceAdd_keeps_meaning
#print axioms scanStep_iff_scanNext
#print axioms scanQuery
#print axioms scan_answers_true_iff_mem
#print axioms scan_answers_false_iff_not_mem
#print axioms openTheory_multiStep_preserves_true_answer
#print axioms openTheory_step_preserves_true_answer
#print axioms derives_of_reachable_true_answer
#print axioms reachable_true_answer_of_derives
#print axioms derives_iff_reachable_true_answer
#print axioms scan_step_never_lengthens
#print axioms openTheory_step_lengthens
#print axioms openTheory_step_is_not_scan_step

end Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
