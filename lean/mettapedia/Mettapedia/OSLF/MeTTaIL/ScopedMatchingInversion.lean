import Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

/-!
# Inverting the scoped matcher

What one capture of the scoped matcher says about the matched term, one pattern former at a time: a constructor
matches a term with the same constructor and argument count, a binder matches a binder of any display name, and a
metavariable captures through its declared occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

open Syntax RuleBinding

variable {compare : String → Pattern → Pattern → Bool} {rule : RewriteRule} {spec : RuleBindingSpec}
  {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat} {assignment found : Assignment}

theorem mem_matchAtWith_fvar {name : String} {target : Pattern} :
    found ∈ matchAtWith compare rule spec ambient site path depth assignment (.fvar name) target ↔
      captureWith? compare rule spec ambient depth site path assignment name target = some found := by
  simp [matchAtWith]

theorem mem_matchAtWith_apply {constructor : String} {patterns : List Pattern} {target : Pattern} :
    found ∈ matchAtWith compare rule spec ambient site path depth assignment (.apply constructor patterns) target ↔
      ∃ targets, target = .apply constructor targets ∧
        found ∈ matchArgsAtWith compare rule spec ambient site path depth assignment 0 patterns targets := by
  cases target with
  | apply actual targets =>
      by_cases same : constructor = actual
      · subst same
        simp [matchAtWith]
      · simp [matchAtWith, same, Ne.symm same]
  | _ => simp [matchAtWith]

theorem mem_matchAtWith_lambda {binder : Option String} {body target : Pattern} :
    found ∈ matchAtWith compare rule spec ambient site path depth assignment (.lambda binder body) target ↔
      ∃ actual inner, target = .lambda actual inner ∧
        found ∈ matchAtWith compare rule spec ambient site (path ++ [0]) (depth + 1) assignment body inner := by
  cases target with
  | lambda actual inner => simp [matchAtWith]
  | _ => simp [matchAtWith]

theorem mem_matchArgsAtWith_nil {index : Nat} {targets : List Pattern} :
    found ∈ matchArgsAtWith compare rule spec ambient site path depth assignment index [] targets ↔
      targets = [] ∧ found = assignment := by
  cases targets <;> simp [matchArgsAtWith]

theorem mem_matchArgsAtWith_cons {index : Nat} {pattern : Pattern} {patterns targets : List Pattern} :
    found ∈ matchArgsAtWith compare rule spec ambient site path depth assignment index (pattern :: patterns)
        targets ↔
      ∃ target rest middle, targets = target :: rest ∧
        middle ∈ matchAtWith compare rule spec ambient site (path ++ [index]) depth assignment pattern target ∧
        found ∈ matchArgsAtWith compare rule spec ambient site path depth middle (index + 1) patterns rest := by
  cases targets with
  | nil => simp [matchArgsAtWith]
  | cons target rest =>
      simp only [matchArgsAtWith, List.mem_flatMap]
      constructor
      · rintro ⟨middle, first, second⟩
        exact ⟨target, rest, middle, rfl, first, second⟩
      · rintro ⟨_, _, middle, equal, first, second⟩
        simp only [List.cons.injEq] at equal
        obtain ⟨rfl, rfl⟩ := equal
        exact ⟨middle, first, second⟩

theorem mem_matchBagAtWith_cons {index : Nat} {pattern : Pattern} {patterns : List Pattern}
    {rest : Option String} {kind : CollType} {targets : List Pattern} :
    found ∈ matchBagAtWith compare rule spec ambient site path depth assignment index (pattern :: patterns) rest
        kind targets ↔
      ∃ target selected, (target, selected) ∈ targets.zipIdx ∧ ∃ middle,
        middle ∈ matchAtWith compare rule spec ambient site (path ++ [index]) depth assignment pattern target ∧
        found ∈ matchBagAtWith compare rule spec ambient site path depth middle (index + 1) patterns rest kind
          (targets.eraseIdx selected) := by
  simp only [matchBagAtWith, List.mem_flatMap, Prod.exists]

theorem mem_matchBagAtWith_rest {index : Nat} {name : String} {kind : CollType} {targets : List Pattern} :
    found ∈ matchBagAtWith compare rule spec ambient site path depth assignment index [] (some name) kind targets ↔
      captureRestWith? compare rule spec ambient depth site (path ++ [index]) assignment name kind targets =
        some found := by
  simp [matchBagAtWith]

/-- A bag pattern matches exactly a bag without a rest, through the bag matcher. -/
theorem mem_matchAtWith_bag {patterns : List Pattern} {rest : Option String} {target : Pattern} :
    found ∈ matchAtWith compare rule spec ambient site path depth assignment (.collection .hashBag patterns rest)
        target ↔
      ∃ targets, target = .collection .hashBag targets none ∧
        found ∈ matchBagAtWith compare rule spec ambient site path depth assignment 0 patterns rest .hashBag
          targets := by
  cases target with
  | collection actualKind targets actualRest =>
      unfold matchAtWith
      by_cases admitted : (CollType.hashBag == actualKind && actualRest.isNone) = true
      · simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at admitted
        obtain ⟨rfl, rfl⟩ := admitted
        simp
      · rw [if_neg admitted]
        simp only [List.not_mem_nil, false_iff, not_exists, not_and]
        intro other equal
        simp only [Pattern.collection.injEq] at equal
        obtain ⟨rfl, -, rfl⟩ := equal
        exact absurd (by simp) admitted
  | _ => simp [matchAtWith]

/-- **Negative**: a constructor never matches a term with another constructor. -/
theorem matchAtWith_apply_other {constructor actual : String} {patterns targets : List Pattern}
    (different : constructor ≠ actual) :
    matchAtWith compare rule spec ambient site path depth assignment (.apply constructor patterns)
      (.apply actual targets) = [] := by
  simp [matchAtWith, different]

end Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
