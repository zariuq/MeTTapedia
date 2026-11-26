import Mettapedia.GSLT.Compilation.Uniform.RowReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Executable
import Mettapedia.OSLF.MeTTaIL.NoncontextualPremiseCheck

/-!
# Hosting an executable OSLF frontier on Transform

A reference implementation calls an independently given executable
one-step frontier. A single Transform schema takes the current row, asks
the built-in frontier relation on that row, and makes the returned row. Iteration is
performed by Transform firings.

The host proves endpoint preservation and reflection for finite runs.
The source semantics is independent of its frontier. Soundness gives
readback and completeness gives the source-to-target direction. An OSLF
root instance uses the canonical semantics and the existing executable
root enumeration theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.OSLFReferenceOnTheStep

open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep (NoncontextualPremises check_noncontextualRules_iff)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines (rowRule rowState rowState_reads row_of_singleton ReadsBag RootStep)
open RuleSyntax.ComputedConditions
open Uniform.RowReadback (readPattern readPattern_encode)
open RootRewritesOnTheStep (encode)

universe u

/-- Reversible storage of source states on the chosen observation. -/
structure Encoding (State : Type u) where
  store : State → Expr
  read : Expr → Option State
  read_store : ∀ s, read (store s) = some s

theorem Encoding.injective {State : Type u} (E : Encoding State) : Function.Injective E.store :=
  fun s t same => Option.some.inj ((E.read_store s).symm.trans ((congrArg E.read same).trans (E.read_store t)))

def patternEncoding : Encoding Pattern := ⟨encode, readPattern, readPattern_encode⟩

private def call : Condition ℕ Tm := { name := 0, arguments := [.var 0], value := .var 1 }

/-- The reference rule matches one source row and publishes one successor. -/
def schema : Executable.Schema := ⟨.var 0, [call], .var 1⟩

private theorem ready : Executable.Ready schema.right [schema.left] schema.conditions := by
  decide +kernel

/-- Answer the built-in relation only when one argument decodes to a canonical source
row. The list order is inherited from the supplied frontier. -/
def builtins {State : Type u} (E : Encoding State) (frontier : State → List State) : Executable.Builtins
  | 0, [row] =>
      match E.read row with
      | some source => if E.store source = row then (frontier source).map E.store else []
      | none => []
  | _, _ => []

@[simp] theorem provider_store {State : Type u} (E : Encoding State) (frontier : State → List State)
    (source : State) :
    builtins E frontier 0 [E.store source] = (frontier source).map E.store := by
  simp [builtins, E.read_store]

private theorem relation_at_source {State : Type u} (E : Encoding State) (frontier : State → List State)
    (source : State) (after : Multiset Expr) :
    RelationStep (builtins E frontier).relates schema.rule {E.store source} after ↔
      ∃ target ∈ frontier source, after = {E.store target} := by
  constructor
  · rintro ⟨θ, rest, split, _, _, asked, output⟩
    have head : θ 0 = E.store source ∧ rest = 0 := by
      apply row_of_singleton
      exact split
    have answered := asked call (List.mem_singleton_self _)
    change θ 1 ∈ builtins E frontier 0 [θ 0] at answered
    rw [head.1, provider_store] at answered
    obtain ⟨target, member, named⟩ := List.mem_map.mp answered
    exact ⟨target, member, by simpa [schema, Executable.Schema.rule, rowRule, inst,
      head.2, ← named] using output⟩
  · rintro ⟨target, member, rfl⟩
    let θ : ℕ → Expr := fun index => if index = 0 then E.store source else E.store target
    refine ⟨θ, 0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [schema, Executable.Schema.rule, rowRule, θ, inst]
    · simp [schema, Executable.Schema.rule, rowRule]
    · simp [schema, Executable.Schema.rule, rowRule, equationsOf]
    · intro c h
      have equal : c = call := List.mem_singleton.mp h
      subst c
      change θ 1 ∈ builtins E frontier 0 [θ 0]
      change E.store target ∈ builtins E frontier 0 [E.store source]
      rw [provider_store]
      exact List.mem_map_of_mem member
    · simp [schema, Executable.Schema.rule, rowRule, θ, inst]

/-- The executable Transform interpreter reads exactly the successors of
the built-in relation on a source row. -/
theorem mem_successors {State : Type u} (E : Encoding State) (frontier : State → List State)
    (source : State) (row : Expr) :
    row ∈ Executable.successors (builtins E frontier) [schema] (E.store source) ↔
      ∃ target ∈ frontier source, row = E.store target := by
  change row ∈ (schema.successors (builtins E frontier) (E.store source) ++ []) ↔ _
  rw [List.append_nil, Executable.mem_successors_iff _ _ ready, relation_at_source]
  simp only [Multiset.singleton_inj]

/-- Enumerate the encoded endpoints at exactly this depth using the fixed
Transform rule, at each stage calling only the one-step built-in relation. -/
def rowsAt {State : Type u} (E : Encoding State) (frontier : State → List State) :
    ℕ → Expr → List Expr
  | 0, row => [row]
  | n + 1, row =>
      (Executable.successors (builtins E frontier) [schema] row).flatMap (rowsAt E frontier n)

/-- Bounded execution of the reference rule preserves and reflects the depth
of every source path. -/
theorem mem_rowsAt (source : GSLT.{0}) (E : Encoding source.Term) (frontier : source.Term → List source.Term)
    (exactStep : ∀ s t, t ∈ frontier s ↔ source.Step s t) :
    ∀ (n : ℕ) (start : source.Term) (row : Expr), row ∈ rowsAt E frontier n (E.store start) ↔
      ∃ finish, row = E.store finish ∧ ∃ path : source.RewritePath start finish, path.length = n := by
  intro depth
  induction depth with
  | zero =>
      intro start row
      constructor
      · intro member
        exact ⟨start, List.mem_singleton.mp member, .nil start, rfl⟩
      · rintro ⟨finish, rfl, path, length⟩
        cases path with
        | nil => exact List.mem_singleton_self _
        | cons _ _ => simp [GSLT.RewritePath.length] at length
  | succ n ih =>
      intro start row
      simp only [rowsAt, List.mem_flatMap]
      constructor
      · rintro ⟨middleRow, offered, remaining⟩
        obtain ⟨middle, member, rfl⟩ := (mem_successors E frontier start middleRow).mp offered
        obtain ⟨finish, encoded, rest, length⟩ := (ih middle row).mp remaining
        exact ⟨finish, encoded, .cons ((exactStep start middle).mp member) rest,
          by simp [GSLT.RewritePath.length, length, Nat.add_comm]⟩
      · rintro ⟨finish, encoded, path, length⟩
        cases path with
        | nil => simp [GSLT.RewritePath.length] at length
        | @cons _ middle _ first rest =>
            have member := (exactStep start middle).mpr first
            refine ⟨E.store middle, (mem_successors E frontier start _).mpr ⟨middle, member, rfl⟩,
              (ih middle row).mpr ⟨finish, encoded, rest, ?_⟩⟩
            rw [GSLT.RewritePath.length] at length
            omega


/-- The fixed finite schema, interpreted by the built-in relation at each binding. -/
abbrev schemas : Set (RuleWithCondition ℕ Tm) := {schema.rule}

def compiledStep {State : Type u} (E : Encoding State) (frontier : State → List State) : GSLT :=
  programSystem ℕ (specialized rows (relationGraph (builtins E frontier).relates) schemas)

private def atBags (source : GSLT.{u}) (E : Encoding source.Term) (frontier : source.Term → List source.Term)
    (exactStep : ∀ s t, t ∈ frontier s ↔ source.Step s t) :
    OperationalCorrespondence source (relationEvaluation (builtins E frontier).relates schemas) where
  related s bag := bag = ({E.store s} : Multiset Expr)
  readStep := by
    rintro s _ next rfl ⟨rule, member, fired⟩
    have equal : rule = schema.rule := member
    subst rule
    obtain ⟨t, occurs, same⟩ := (relation_at_source E frontier s next).mp fired
    exact Or.inr ⟨t, (exactStep s t).mp occurs, same⟩
  forward := by
    rintro s t _ rfl moved
    refine ⟨({E.store t} : Multiset Expr), (executionPath_nonempty_iff_multiStep _ _ _).mpr
      (.step ?_ (.refl _)), rfl⟩
    exact ⟨schema.rule, rfl,
      (relation_at_source E frontier s _).mpr ⟨t, (exactStep s t).mpr moved, rfl⟩⟩

private theorem restricted : schema.rule.RangeRestrictedWith := by
  decide +kernel

/-- The finite schema is a reference implementation of the given theory
when its built-in relation enumerates precisely the theory's one-step frontier. -/
def correspondence (source : GSLT.{u}) (E : Encoding source.Term) (frontier : source.Term → List source.Term)
    (exactStep : ∀ s t, t ∈ frontier s ↔ source.Step s t) :
    OperationalCorrespondence source (compiledStep E frontier) :=
  (atBags source E frontier exactStep).comp (relationCorrespondence
    (fun ρ member => by
      have equal : ρ = schema.rule := member
      subst ρ
      rfl)
    (fun ρ member => by
      have equal : ρ = schema.rule := member
      subst ρ
      rfl)
    (fun ρ member => by
      have equal : ρ = schema.rule := member
      subst ρ
      exact restricted))

/-- The reference program really reaches exactly the original endpoints.
The comparison reads a Transform state by its singleton row, allowing
fresh occurrence identities at different firings. -/
theorem reaches_iff (source : GSLT.{u}) (E : Encoding source.Term) (frontier : source.Term → List source.Term)
    (exactStep : ∀ s t, t ∈ frontier s ↔ source.Step s t) (first last : source.Term) :
    source.MultiStep first last ↔
      ∃ final, (compiledStep E frontier).MultiStep (rowState (E.store first)) final ∧
        ReadsBag final {E.store last} := by
  let compare := correspondence source E frontier exactStep
  have haveSource : compare.related first (rowState (E.store first)) :=
    ⟨({E.store first} : Multiset Expr), rfl, rowState_reads _⟩
  have observations : ∀ {s current}, compare.related s current →
      (s = last ↔ ReadsBag current {E.store last}) := by
    rintro s current ⟨bag, atSource, atTarget⟩
    change bag = ({E.store s} : Multiset Expr) at atSource
    subst bag
    refine ⟨fun h => h ▸ atTarget, fun held => ?_⟩
    have same := readsAs_unique atTarget.readsAs.1 atTarget.readsAs.2 held.readsAs.2
    have rowsEqual : E.store s = E.store last := by simpa using same
    exact E.injective rowsEqual
  have compared := compare.reachable_iff (· = last) (fun current => ReadsBag current {E.store last})
    observations haveSource
  refine ⟨fun path => compared.mp ⟨last, path, rfl⟩, fun run => ?_⟩
  obtain ⟨_, path, rfl⟩ := compared.mpr run
  exact path

/-- Instance of the reference bridge for the existing executable OSLF root
frontier over the canonical authored semantics. -/
theorem oslf_reaches_iff (relations : RelationEnv) (language : LanguageDef)
    (noEquations : language.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ language.rewrites, NoncontextualPremises rule.premises)
    (first last : Pattern) :
    (langGSLTUsing relations language).MultiStep first last ↔
      ∃ final,
        (compiledStep patternEncoding (rewriteStepWithPremisesUsing relations language)).MultiStep
          (rowState (encode first)) final ∧ ReadsBag final {encode last} :=
  reaches_iff (langGSLTUsing relations language) patternEncoding
    (rewriteStepWithPremisesUsing relations language)
    (mem_rootFrontier_iff_langGSLTUsing_step relations language noEquations nonrecursive) first last

/-- On the overlap, the directly lowered root schemas and the interpreter
have the same row successors. The reference built-in relation can therefore check
this observation of a more selective compiler. -/
theorem direct_agrees_with_reference (relations : RelationEnv) {language : LanguageDef}
    {direct : List (Tm × Tm)} (compiled : RootRewritesOnTheStep.compile language = .ok direct)
    (first : Pattern) (row : Expr) :
    row ∈ Executable.successors (builtins patternEncoding (rewriteStepWithPremisesUsing relations language))
        [schema] (encode first) ↔
      RootStep direct (encode first) row := by
  have nonrecursive : ∀ rule ∈ language.rewrites, NoncontextualPremises rule.premises := by
    intro rule member
    rw [(RootRewritesOnTheStep.compile_plain compiled rule member).1]
    exact .nil
  have exactStep := mem_rootFrontier_iff_langReducesUsing relations language nonrecursive
  change row ∈ Executable.successors (builtins patternEncoding (rewriteStepWithPremisesUsing relations language))
      [schema] (patternEncoding.store first) ↔ _
  rw [mem_successors]
  constructor
  · rintro ⟨target, stepped, rfl⟩
    exact RootRewritesOnTheStep.rootStep_of_step compiled ((exactStep first target).mp stepped)
  · intro stepped
    obtain ⟨target, reduced, rfl⟩ := RootRewritesOnTheStep.rootStep_image (relEnv := relations) compiled stepped
    exact ⟨target, (exactStep first target).mpr reduced, rfl⟩


namespace Controls

/-- A one-rule presentation with binding syntax at the root. -/
def identity : Pattern := .lambda none (.bvar 0)
def constant : Pattern := .lambda none (.lambda none (.bvar 1))

def language : LanguageDef :=
  { LanguageDef.empty "BindingRewrite" with
    rewrites := [{ name := "change", typeContext := [], premises := [], left := identity, right := constant }] }

private theorem root_binder_frontier :
    rewriteStepWithPremisesUsing RelationEnv.empty language identity = [constant] := by
  decide +kernel

private theorem root_binder_no_more :
    rewriteStepWithPremisesUsing RelationEnv.empty language constant = [] := by
  decide +kernel

theorem reference_matches_binder (row : Expr) :
    row ∈ Executable.successors (builtins patternEncoding (rewriteStepWithPremisesUsing RelationEnv.empty language))
      [schema] (encode identity) ↔ row = encode constant := by
  rw [show encode identity = patternEncoding.store identity from rfl, mem_successors, root_binder_frontier]
  simp [patternEncoding]

theorem reference_stops (row : Expr) :
    row ∉ Executable.successors (builtins patternEncoding (rewriteStepWithPremisesUsing RelationEnv.empty language))
      [schema] (encode constant) := by
  rw [show encode constant = patternEncoding.store constant from rfl, mem_successors, root_binder_no_more]
  simp

theorem direct_root_compiler_refuses : RootRewritesOnTheStep.compile language = .error (.notFirstOrder "change") := by
  rfl

theorem binder_reaches_on_the_step :
    ∃ final, (compiledStep patternEncoding (rewriteStepWithPremisesUsing RelationEnv.empty language)).MultiStep
      (rowState (encode identity)) final ∧ ReadsBag final {encode constant} := by
  have noEquations : language.isEquationFree = true := by decide +kernel
  have nonrecursive : ∀ r ∈ language.rewrites, NoncontextualPremises r.premises :=
    (check_noncontextualRules_iff _).mp (by decide +kernel)
  have moved := (mem_rootFrontier_iff_langGSLTUsing_step RelationEnv.empty language noEquations
    nonrecursive identity constant).mp (by simp [root_binder_frontier])
  exact (oslf_reaches_iff RelationEnv.empty language noEquations nonrecursive identity constant).mp
    (.step moved (.refl _))

end Controls

#print axioms mem_successors
#print axioms mem_rowsAt
#print axioms reaches_iff
#print axioms oslf_reaches_iff
#print axioms direct_agrees_with_reference
#print axioms Controls.reference_matches_binder
#print axioms Controls.binder_reaches_on_the_step

end Mettapedia.GSLT.Compilation.OSLFReferenceOnTheStep
