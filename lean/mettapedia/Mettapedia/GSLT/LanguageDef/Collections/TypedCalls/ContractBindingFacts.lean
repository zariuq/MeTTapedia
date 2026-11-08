import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameCertificate

/-!
# Native bind-any facts and current-variable dependencies

The local flag structure follows contract_pattern_uninterpreted,
contract_pattern_keeps_claims and contract_bind_any. The symbol exclusion
oracle here is the established declaration family; the native predicate also
checks equations and primitive ownership, so its correspondence is separate.
The inputs are facts about source variable names. Facts describe the values
currently reached through a substitution, not merely those names' spelling.

A counterexample below uses the actual two-way unifier: an ANY variable and
a separately tracked uninterpreted variable can alias. The raw-name test
allows binding the first to declared data and thereby invalidates the
second's claim. This refutes a flag-only preservation inference; it does not
by itself establish that every native admission path accepts that caller.

The repaired sufficient contract keeps the clean-operands rule and adds a
current-support check for inherited claims in the arbitrary-value branch.
Ground observations are always retained. Source lowering, native fact-table
representation and hidden resource support remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ContractBindingFacts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions UnifyingFrames OpenFrameEffects

structure Flags where
  ground : Bool
  uninterpreted : Bool
  deriving DecidableEq

abbrev Facts := List (String × Flags)

structure ValueFlags extends Flags where
  bottom : Bool := false
  deriving DecidableEq

def Holds (Γ : Decls) (σ : Substitution) (name : String) (flags : Flags) : Prop :=
  (flags.ground = true → support (σ name) = ∅) ∧
    (flags.uninterpreted = true → Uninterp Γ (σ name))

def Sound (Γ : Decls) (σ : Substitution) (facts : Facts) : Prop :=
  ∀ entry ∈ facts, Holds Γ σ entry.1 entry.2

def FreshUnknown (facts : Facts) (σ : Substitution) (pattern : Atom) : Prop :=
  ∀ name ∈ support pattern, facts.lookup name = none → σ name = .var name

def ValueFaithful (Γ : Decls) (σ : Substitution) (value : Atom) (flags : ValueFlags) : Prop :=
  (flags.ground = true → support (substA σ value) = ∅) ∧
    (flags.uninterpreted = true → Uninterp Γ (substA σ value))

mutual
def patternUninterpreted (Γ : Decls) (facts : Facts) : Atom → Bool
  | .var name => ((facts.lookup name).map Flags.uninterpreted).getD true
  | .symbol name => (Γ name).isEmpty
  | .grounded _ => true
  | .expression values => patternsUninterpreted Γ facts values

def patternsUninterpreted (Γ : Decls) (facts : Facts) : List Atom → Bool
  | [] => true
  | value :: values => patternUninterpreted Γ facts value && patternsUninterpreted Γ facts values
end

theorem lookup_sound {Γ : Decls} {σ : Substitution} {facts : Facts}
    (sound : Sound Γ σ facts) {name : String} {flags : Flags}
    (found : facts.lookup name = some flags) : Holds Γ σ name flags := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp found
  exact sound (name, flags) (by simp [same])

mutual
/-- Unknown pattern variables must still be fresh. A missing fact entry is
not evidence that an arbitrary existing runtime value is uninterpreted. -/
theorem patternUninterpreted_sound {Γ : Decls} {facts : Facts} {σ : Substitution}
    (sound : Sound Γ σ facts) : ∀ pattern,
      FreshUnknown facts σ pattern → patternUninterpreted Γ facts pattern = true →
        Uninterp Γ (substA σ pattern)
  | .var name, fresh, checked => by
      cases found : facts.lookup name with
      | none =>
          have unused : name ∈ support (.var name) := by
            simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
          rw [substA, fresh name unused found]
          trivial
      | some flags =>
          exact (lookup_sound sound found).2 (by simpa [patternUninterpreted, found] using checked)
  | .symbol name, _, checked => List.isEmpty_iff.mp checked
  | .grounded _, _, _ => trivial
  | .expression values, fresh, checked => by
      rw [substA]
      exact UnifyAtoms.uninterp_of_all (patternsUninterpreted_sound sound values fresh checked)

theorem patternsUninterpreted_sound {Γ : Decls} {facts : Facts} {σ : Substitution}
    (sound : Sound Γ σ facts) : ∀ values,
      FreshUnknown facts σ (.expression values) → patternsUninterpreted Γ facts values = true →
        ∀ value ∈ substL σ values, Uninterp Γ value
  | [], _, _, _, member => by cases member
  | first :: rest, fresh, checked, value, member => by
      have checks := Bool.and_eq_true_iff.mp checked
      have headFresh : FreshUnknown facts σ first := by
        intro name occurs missing
        exact fresh name ((support_expression _ name).mpr ⟨first, by simp, occurs⟩) missing
      have tailFresh : FreshUnknown facts σ (.expression rest) := by
        intro name occurs missing
        obtain ⟨part, present, occurs⟩ := (support_expression _ name).mp occurs
        exact fresh name ((support_expression _ name).mpr ⟨part, by simp [present], occurs⟩) missing
      have head := patternUninterpreted_sound sound first headFresh checks.1
      have tail := patternsUninterpreted_sound sound rest tailFresh checks.2
      rcases List.mem_cons.mp member with same | present
      · simpa only [same] using head
      · exact tail value present
end

mutual
def patternKeepsClaims (facts : Facts) : Atom → Bool
  | .var name => match facts.lookup name with
      | none => true
      | some flags => flags.ground || !flags.uninterpreted
  | .expression values => patternsKeepClaims facts values
  | _ => true

def patternsKeepClaims (facts : Facts) : List Atom → Bool
  | [] => true
  | value :: values => patternKeepsClaims facts value && patternsKeepClaims facts values
end

/-- The return boolean of the native flag check, excluding allocation
failure. Updating the fact table is a separate operation. -/
def nativeAllows (Γ : Decls) (facts : Facts) (pattern : Pat) (value : ValueFlags) : Bool :=
  if value.uninterpreted && patternUninterpreted Γ facts pattern.toAtom then true
  else if value.uninterpreted && !value.ground then false
  else patternKeepsClaims facts pattern.toAtom

/-- In the arbitrary-value branch, protect every inherited uninterpreted
claim by its current dependencies. Ground flags need no additional test. -/
def observedClaims (facts : Facts) (σ : Substitution) (pattern : Pat) (value : Atom) : Bool :=
  facts.all fun entry => !entry.2.uninterpreted || entry.2.ground ||
    decide (Disjoint (support (σ entry.1)) (bindSupport σ pattern value))

theorem ground_observation_preserved {σ τ : Substitution} {pattern : Pat} {value : Atom}
    (bound : bindPattern σ pattern value = some τ) (name : String)
    (ground : support (σ name) = ∅) : τ name = σ name := by
  have separate : Disjoint (observedSupport σ (.var name)) (bindSupport σ pattern value) := by
    simp only [observedSupport, substA, ground]
    exact Finset.disjoint_empty_left _
  exact bindPattern_preserves_frame bound separate

theorem observedClaims_sound {Γ : Decls} {σ τ : Substitution} {facts : Facts}
    {pattern : Pat} {value : Atom} (before : Sound Γ σ facts)
    (checked : observedClaims facts σ pattern value = true)
    (bound : bindPattern σ pattern value = some τ) : Sound Γ τ facts := by
  intro entry member
  have old := before entry member
  have checkedEntry := (List.all_eq_true.mp checked) entry member
  refine ⟨fun ground => ?_, fun uninterpreted => ?_⟩
  · rw [ground_observation_preserved bound entry.1 (old.1 ground)]
    exact old.1 ground
  · by_cases ground : entry.2.ground = true
    · rw [ground_observation_preserved bound entry.1 (old.1 ground)]
      exact old.2 uninterpreted
    · have separate : Disjoint (support (σ entry.1)) (bindSupport σ pattern value) := by
        simpa only [uninterpreted, Bool.not_true, Bool.false_or, ground, Bool.false_eq_true,
          false_or, decide_eq_true_eq] using checkedEntry
      have same := bindPattern_preserves_frame (frame := .var entry.1) bound separate
      change τ entry.1 = σ entry.1 at same
      rw [same]
      exact old.2 uninterpreted

/-- Clean operands yield a clean MGU, preserving all inherited uninterpreted
claims even when they share variables with those operands. -/
theorem clean_operands_preserve_facts {Γ : Decls} {σ τ : Substitution} {facts : Facts}
    {pattern : Pat} {value : Atom} (before : Sound Γ σ facts)
    (patternClean : Uninterp Γ (substA σ pattern.toAtom))
    (valueClean : Uninterp Γ (substA σ value))
    (bound : bindPattern σ pattern value = some τ) : Sound Γ τ facts := by
  obtain ⟨extension, _⟩ := bindPattern_clean_operands patternClean valueClean bound
  intro entry member
  have old := before entry member
  refine ⟨fun ground => ?_, fun uninterpreted => ?_⟩
  · rw [ground_observation_preserved bound entry.1 (old.1 ground)]
    exact old.1 ground
  · obtain ⟨delta, clean, rfl⟩ := extension
    exact uninterp_substA clean (σ entry.1) (old.2 uninterpreted)

/-- A source checker can discharge either sufficient branch. This is a
local claim-preservation obligation, not an assumed whole-run equivalence. -/
theorem bind_any_preserves_facts {Γ : Decls} {σ τ : Substitution} {facts : Facts}
    {pattern : Pat} {value : Atom} (before : Sound Γ σ facts)
    (admitted : (Uninterp Γ (substA σ pattern.toAtom) ∧ Uninterp Γ (substA σ value)) ∨
      observedClaims facts σ pattern value = true)
    (bound : bindPattern σ pattern value = some τ) : Sound Γ τ facts := by
  rcases admitted with ⟨patternClean, valueClean⟩ | observed
  · exact clean_operands_preserve_facts before patternClean valueClean bound
  · exact observedClaims_sound before observed bound

def checkedAllows (Γ : Decls) (facts : Facts) (σ : Substitution)
    (pattern : Pat) (value : Atom) (flags : ValueFlags) : Bool :=
  nativeAllows Γ facts pattern flags &&
    ((flags.uninterpreted && patternUninterpreted Γ facts pattern.toAtom) ||
      observedClaims facts σ pattern value)

/-- The executable repaired check derives both branches of claim transport
from local representation evidence and actual two-way unification. -/
theorem checked_bind_preserves_facts {Γ : Decls} {σ τ : Substitution} {facts : Facts}
    {pattern : Pat} {value : Atom} {flags : ValueFlags}
    (before : Sound Γ σ facts) (fresh : FreshUnknown facts σ pattern.toAtom)
    (valueFaithful : ValueFaithful Γ σ value flags)
    (checked : checkedAllows Γ facts σ pattern value flags = true)
    (bound : bindPattern σ pattern value = some τ) : Sound Γ τ facts := by
  apply bind_any_preserves_facts before ?_ bound
  have branches := (Bool.and_eq_true_iff.mp checked).2
  rcases Bool.or_eq_true_iff.mp branches with clean | observed
  · have pair := Bool.and_eq_true_iff.mp clean
    exact Or.inl ⟨patternUninterpreted_sound before pattern.toAtom fresh pair.2,
      valueFaithful.2 pair.1⟩
  · exact Or.inr observed

def mergeFlags (first second : Flags) : Flags :=
  ⟨first.ground || second.ground, first.uninterpreted || second.uninterpreted⟩

/-- Repeated marks are conjunction of promises; the OR in the native flag
representation does not mean either promise can be forgotten. -/
theorem mergeFlags_holds (Γ : Decls) (σ : Substitution) (name : String) (first second : Flags) :
    Holds Γ σ name (mergeFlags first second) ↔
      Holds Γ σ name first ∧ Holds Γ σ name second := by
  simp only [Holds, mergeFlags, Bool.or_eq_true, or_imp]
  tauto

theorem bindPattern_equation {σ τ : Substitution} {pattern : Pat} {value : Atom}
    (bound : bindPattern σ pattern value = some τ) :
    substA τ pattern.toAtom = substA τ value := by
  unfold bindPattern at bound
  cases unified : UnifyAtoms.unify (substA σ pattern.toAtom) (substA σ value) with
  | none => simp [unified] at bound
  | some theta =>
      have changed : compose (UnifyAtoms.readBack theta) σ = τ := by simpa [unified] using bound
      rw [← changed, ← substA_compose, ← substA_compose]
      exact UnifyAtoms.unify_instance unified

/-- Groundness of a matched value is transported to every source variable
inside the pattern, including variables reached through an old alias. -/
theorem ground_pattern_marks {σ τ : Substitution} {pattern : Pat} {value : Atom}
    (bound : bindPattern σ pattern value = some τ)
    (ground : support (substA σ value) = ∅) :
    ∀ name ∈ support pattern.toAtom, support (τ name) = ∅ := by
  have separate : Disjoint (observedSupport σ value) (bindSupport σ pattern value) := by
    rw [observedSupport, ground]
    exact Finset.disjoint_empty_left _
  have kept := bindPattern_preserves_frame bound separate
  have patternGround : support (substA τ pattern.toAtom) = ∅ := by
    rw [bindPattern_equation bound, kept, ground]
  intro name occurs
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro freeName present
  have escaped := (support_subst τ pattern.toAtom freeName).mpr ⟨name, occurs, present⟩
  rw [patternGround] at escaped
  exact Finset.notMem_empty freeName escaped

theorem uninterpreted_member {Γ : Decls} : ∀ values,
    SafeAll Γ Atom.var values → ∀ value ∈ values, Uninterp Γ value
  | [], _, _, member => by cases member
  | first :: rest, safe, value, member => by
      rcases List.mem_cons.mp member with same | present
      · simpa only [same] using safe.1
      · exact uninterpreted_member rest safe.2 value present

theorem uninterpreted_substituted_variable {Γ : Decls} (σ : Substitution) (value : Atom) :
    Uninterp Γ (substA σ value) → ∀ name ∈ support value, Uninterp Γ (σ name) := by
  induction value using Atom.rec
    (motive_2 := fun values => ∀ value ∈ values, Uninterp Γ (substA σ value) →
      ∀ name ∈ support value, Uninterp Γ (σ name)) with
  | var variableName =>
      intro clean name occurs
      have same : name = variableName := by
        simpa [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] using occurs
      simpa only [same, substA] using clean
  | symbol _ =>
      intro _ name occurs
      simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
  | grounded _ =>
      intro _ name occurs
      simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
  | expression values ih =>
      intro clean name occurs
      obtain ⟨part, present, occurs⟩ := (support_expression values name).mp occurs
      have all : SafeAll Γ Atom.var (substL σ values) := UnifyAtoms.safeAll_of_uninterp clean
      have selected : Uninterp Γ (substA σ part) :=
        uninterpreted_member _ all _ (by rw [UnifyAtoms.substL_eq_map]; exact List.mem_map.mpr ⟨part, present, rfl⟩)
      exact ih part present selected name occurs
  | nil value member => cases member
  | cons first rest ihFirst ihRest value member clean name occurs =>
      rcases List.mem_cons.mp member with same | present
      · exact ihFirst (by simpa only [same] using clean) name (by simpa only [same] using occurs)
      · exact ihRest value present clean name occurs

theorem uninterpreted_pattern_marks {Γ : Decls} {σ τ : Substitution} {pattern : Pat} {value : Atom}
    (bound : bindPattern σ pattern value = some τ)
    (patternClean : Uninterp Γ (substA σ pattern.toAtom))
    (valueClean : Uninterp Γ (substA σ value)) :
    ∀ name ∈ support pattern.toAtom, Uninterp Γ (τ name) := by
  obtain ⟨⟨delta, clean, changed⟩, _⟩ := bindPattern_clean_operands patternClean valueClean bound
  apply uninterpreted_substituted_variable τ pattern.toAtom
  rw [changed, ← substA_compose]
  exact uninterp_substA clean _ patternClean

def newFlags (Γ : Decls) (facts : Facts) (pattern : Pat) (value : ValueFlags) : Flags :=
  if value.uninterpreted && patternUninterpreted Γ facts pattern.toAtom then
    ⟨value.ground, true⟩
  else ⟨value.ground && !value.bottom, false⟩

/-- Repeating one variable in a pattern merely repeats its promise. The
OR-merge law above relates these claims to the native merged flag cell. -/
noncomputable def markedClaims (Γ : Decls) (facts : Facts) (pattern : Pat) (value : ValueFlags) : Facts :=
  facts ++ (support pattern.toAtom).toList.map fun name => (name, newFlags Γ facts pattern value)

/-- Both inherited and newly marked facts follow from the checked binding.
No fact about a sibling variable is inferred solely from its source name. -/
theorem checked_bind_marks_sound {Γ : Decls} {σ τ : Substitution} {facts : Facts}
    {pattern : Pat} {value : Atom} {flags : ValueFlags}
    (before : Sound Γ σ facts) (fresh : FreshUnknown facts σ pattern.toAtom)
    (valueFaithful : ValueFaithful Γ σ value flags)
    (checked : checkedAllows Γ facts σ pattern value flags = true)
    (bound : bindPattern σ pattern value = some τ) :
    Sound Γ τ (markedClaims Γ facts pattern flags) := by
  intro entry member
  rcases List.mem_append.mp member with old | new
  · exact checked_bind_preserves_facts before fresh valueFaithful checked bound entry old
  · obtain ⟨name, present, rfl⟩ := List.mem_map.mp new
    have occurs := Finset.mem_toList.mp present
    unfold newFlags
    split
    next clean =>
      have pair := Bool.and_eq_true_iff.mp clean
      refine ⟨fun ground => ground_pattern_marks bound (valueFaithful.1 ground) name occurs, ?_⟩
      intro _
      exact uninterpreted_pattern_marks bound
        (patternUninterpreted_sound before pattern.toAtom fresh pair.2)
        (valueFaithful.2 pair.1) name occurs
    next arbitrary =>
      refine ⟨fun ground => ?_, by simp⟩
      exact ground_pattern_marks bound (valueFaithful.1 (Bool.and_eq_true_iff.mp ground).1) name occurs

namespace Controls

def declarations : Decls := UnifyingFrames.Controls.declarations
def aliases : Substitution := UnifyingFrames.Controls.aliases
def facts : Facts := [("source-a", ⟨false, true⟩), ("source-b", ⟨false, false⟩)]
def pattern : Pat := .var "source-b"
def known : Atom := .symbol "Known"
def knownFlags : ValueFlags := ⟨⟨true, false⟩, false⟩

theorem facts_initially_sound : Sound declarations aliases facts := by
  intro entry member
  simp only [facts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [Holds, aliases, UnifyingFrames.Controls.aliases, Uninterp, Safe]

theorem raw_name_gate_allows_interpreted_binding :
    nativeAllows declarations facts pattern knownFlags = true := by decide +kernel

theorem current_support_gate_refuses : observedClaims facts aliases pattern known = false := by
  decide +kernel

/-- The actual MGU changes the protected observation from a free variable
to a declared symbol, while the local flag test accepts the binding. -/
theorem alias_binding_invalidates_protected_fact :
    ((bindPattern aliases pattern known).map fun next => next "source-a") = some known ∧
      Uninterp declarations (aliases "source-a") ∧ ¬ Uninterp declarations known := by
  constructor
  · cbv
  · constructor
    · trivial
    · simp [declarations, known, UnifyingFrames.Controls.declarations, Uninterp, Safe]

def aliasBody : Expr := .letE pattern (.const known) (.var "source-a")

/-- The same alias flow occurs in the existing source evaluator, not only
in an isolated unification query. The returned old recipe is instantiated
by the binding performed through the other source variable. -/
theorem actual_source_alias_returns_interpreted :
    (evalUnifying (fun _ _ => 0) (fun _ => 0) aliasBody aliases).map observe = {known} := by
  cbv

theorem native_gate_not_sufficient :
    ¬ (∀ next, bindPattern aliases pattern known = some next → Sound declarations next facts) := by
  intro sound
  have changed := alias_binding_invalidates_protected_fact.1
  cases bound : bindPattern aliases pattern known with
  | none => simp [bound] at changed
  | some next =>
      have value : next "source-a" = known := by simpa [bound] using changed
      have kept := (sound next bound ("source-a", ⟨false, true⟩) (by simp [facts])).2 rfl
      rw [value] at kept
      exact alias_binding_invalidates_protected_fact.2.2 kept

def freshPattern : Pat := .var "fresh"

theorem fresh_interpreted_binding_allowed :
    nativeAllows declarations facts freshPattern knownFlags = true ∧
      observedClaims facts aliases freshPattern known = true := by decide +kernel

theorem clean_alias_binding_keeps_uninterpreted :
    ∀ next, bindPattern aliases pattern (.grounded (.int 7)) = some next →
      Sound declarations next facts := by
  intro next bound
  exact clean_operands_preserve_facts facts_initially_sound (by trivial) (by trivial) bound

theorem disjoint_native_binding_keeps_facts :
    ∀ next, bindPattern aliases freshPattern known = some next →
      Sound declarations next facts := by
  intro next bound
  apply checked_bind_preserves_facts (flags := knownFlags) facts_initially_sound ?_ ?_
    (by decide +kernel) bound
  · intro name occurs _
    have same : name = "fresh" := by
      simpa [freshPattern, Pat.toAtom, support, UnifyAtoms.encode,
        Mettapedia.Logic.LP.Term.freeVars] using occurs
    subst name
    rfl
  · constructor
    · intro _
      decide +kernel
    · intro impossible
      cases impossible

theorem unknown_fact_does_not_prove_freshness :
    patternUninterpreted declarations facts (.var "unrelated") = true ∧
      ¬ FreshUnknown facts aliases (.var "unrelated") := by
  constructor
  · decide +kernel
  · intro fresh
    have bad := fresh "unrelated" (by decide +kernel) (by rfl)
    simp [aliases, UnifyingFrames.Controls.aliases] at bad

theorem ground_mark_reaches_alias :
    ∀ next, bindPattern aliases pattern known = some next →
      support (next "source-b") = ∅ := by
  intro next bound
  exact ground_pattern_marks bound (by decide +kernel) "source-b" (by decide +kernel)

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ContractBindingFacts
