import Mettapedia.Languages.VibeITP.Presentation.Rules

/-!
# Vibe-ITP presentation: the facts admitted for a theory

A checker run admits zero-premise rules as it goes: the declaration of every
allocated symbol, every axiom, and the defining equation of every definition.
Allocated symbols are identified by their numeric identity; axioms and
definitions are numbered from one in admission order.

`Hosted` collects the invariants that every theory reached by the protocol
satisfies: the built-in constants carry their fixed data, the allocated symbols
are exactly the first `allocated` fresh identities, free variables bind
nothing, axioms are closed well-formed terms, and every definition was
admissible for its fresh constant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

def symbolRuleId (n : Nat) : String := "vibe-symbol-" ++ Nat.repr n
def axiomRuleId (k : Nat) : String := "vibe-axiom-" ++ Nat.repr k
def definitionRuleId (k : Nat) : String := "vibe-definition-" ++ Nat.repr k

/-- The declaration of the `n`-th allocated symbol. -/
def symbolRule (sig : Sig) (n : Nat) : FORule :=
  mkRule (symbolRuleId (symNumber (.fresh n))) [] [] (jSymDecl (encSym sig (.fresh n)))

/-- The `k`-th axiom. -/
def axiomRule (sig : Sig) (k : Nat) (φ : Term) : FORule :=
  mkRule (axiomRuleId k) [] [] (jThm (encTerm sig φ))

/-- The defining equation of the `k`-th definition. -/
def definitionRule (sig : Sig) (k : Nat) (d : Definition) : FORule :=
  mkRule (definitionRuleId k) [] []
    (jThm (encTerm sig (definitionStatement sig d.symbol d.fvars d.value)))

def axiomRules (sig : Sig) : Nat → List Term → List FORule
  | _, [] => []
  | k, φ :: φs => axiomRule sig k φ :: axiomRules sig (k + 1) φs

def theoryDefinitionRules (sig : Sig) : Nat → List Definition → List FORule
  | _, [] => []
  | k, d :: ds => definitionRule sig k d :: theoryDefinitionRules sig (k + 1) ds

/-- All facts admitted for a theory with `allocated` allocated symbols. -/
def theoryRules (T : Theory) (allocated : Nat) : List FORule :=
  (List.range allocated).map (symbolRule T.sig) ++ axiomRules T.sig 1 T.axioms ++
    theoryDefinitionRules T.sig 1 T.definitions

/-- The signature gives every built-in constant its fixed data. -/
def BuiltinsFixed (sig : Sig) : Prop := ∀ b : Builtin, sig (.builtin b) = some b.info

/-- Free-variable symbols bind nothing in any argument. -/
def FvarsBindNothing (sig : Sig) : Prop :=
  ∀ s info, sig s = some info → info.kind = .fvar → ∀ b ∈ info.binders, b = 0

/-- Invariants of a theory reached by the checker protocol. -/
structure Hosted (T : Theory) (allocated : Nat) : Prop where
  builtin : BuiltinsFixed T.sig
  fresh : ∀ n, (T.sig (.fresh n)).isSome = true ↔ n < allocated
  fvarBinders : FvarsBindNothing T.sig
  axiomsWf : ∀ φ ∈ T.axioms, WellFormed T.sig φ = true ∧ depth T.sig φ = 0
  definitionsOk : ∀ d ∈ T.definitions,
    T.sig d.symbol = some (definitionInfo T.sig d.fvars) ∧ WellFormed T.sig d.value = true ∧
      ∃ hints, definitionAdmissible T.sig d.fvars hints d.value = true

/-! ## Membership -/

theorem mem_axiomRules {sig : Sig} {r : FORule} :
    ∀ {k : Nat} {φs : List Term}, r ∈ axiomRules sig k φs →
      ∃ j, ∃ φ ∈ φs, r = axiomRule sig j φ
  | _, [], h => by simp [axiomRules] at h
  | k, φ :: φs, h => by
      simp only [axiomRules, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨k, φ, by simp, rfl⟩
      · obtain ⟨j, ψ, hψ, rfl⟩ := mem_axiomRules h
        exact ⟨j, ψ, by simp [hψ], rfl⟩

theorem axiomRule_mem {sig : Sig} {φ : Term} :
    ∀ {k : Nat} {φs : List Term}, φ ∈ φs → ∃ j, axiomRule sig j φ ∈ axiomRules sig k φs
  | _, [], h => by simp at h
  | k, ψ :: φs, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨k, by simp [axiomRules]⟩
      · obtain ⟨j, hj⟩ := axiomRule_mem (sig := sig) (k := k + 1) h
        exact ⟨j, List.mem_cons_of_mem _ hj⟩

theorem mem_theoryDefinitionRules {sig : Sig} {r : FORule} :
    ∀ {k : Nat} {ds : List Definition}, r ∈ theoryDefinitionRules sig k ds →
      ∃ j, ∃ d ∈ ds, r = definitionRule sig j d
  | _, [], h => by simp [theoryDefinitionRules] at h
  | k, d :: ds, h => by
      simp only [theoryDefinitionRules, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨k, d, by simp, rfl⟩
      · obtain ⟨j, e, he, rfl⟩ := mem_theoryDefinitionRules h
        exact ⟨j, e, by simp [he], rfl⟩

theorem definitionRule_mem {sig : Sig} {d : Definition} :
    ∀ {k : Nat} {ds : List Definition}, d ∈ ds →
      ∃ j, definitionRule sig j d ∈ theoryDefinitionRules sig k ds
  | _, [], h => by simp at h
  | k, e :: ds, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨k, by simp [theoryDefinitionRules]⟩
      · obtain ⟨j, hj⟩ := definitionRule_mem (sig := sig) (k := k + 1) h
        exact ⟨j, List.mem_cons_of_mem _ hj⟩

end Mettapedia.Languages.VibeITP.Presentation
