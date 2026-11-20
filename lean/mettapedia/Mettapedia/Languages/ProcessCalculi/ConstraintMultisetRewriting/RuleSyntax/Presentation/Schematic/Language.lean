import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Terms

/-!
# A program with unknowns as a language definition

A rule with unknowns (`SRule`: a rule at the one frame over rows with unknowns) is presented by one
rewrite (`schematicRewrite`) whose metavariables are the rule's unknowns:

* **left**: the codes of its take patterns beside the rest, `{p₁, …, pₙ, ...rest}`; the framework's bag
  matcher picks distinct rows for them, and its agreement check makes an unknown that occurs twice match
  equal subterms;
* **premises**, decided by the framework's builtin equality relation `eq`, in order:
  - for each read pattern `q`, the **read premise** `rest = {q, ...qⱼ}`: the rest decomposes as a row of
    the pattern beside a remainder. It is a match of `q` against the rest that consumes nothing, so two
    reads may read one row and no read reads a taken row, exactly as the step's reads;
  - for each tell and each equation guard `l = r`, the premise `l = r`;
* **right**: the codes of its made rows beside the same rest, `{m₁, …, mₖ, ...rest}`.

No premise asks the step: the relation is the framework's builtin `eq` on instantiated arguments.

**The fragment** (`RangeRestrictedPositive`): no collect pattern, only equation checks, and **range restriction**
(`RangeRestricted`): every unknown of a tell, a check or a made row occurs in a take or read pattern
(`Bound`).

What is proved here about the premises, for every relation environment that adds no tuple to `eq`:
* `equationPremise_sound`, `readPremise_sound`: what a premise's result binds: equal sides, or a read
  pattern sent into the rest;
* `equationPremise_complete`, `readPremise_complete`: when the sides of an equation are equal under an
  instantiation, or a read pattern's instance is a row of the rest, the premise has a result;
* `premisesAt_sound`, `premisesAt_complete`: the same along a list of premises.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv relationQueryStep builtinRelationTuples
  matchRelationArgs matchRelationArgument)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator engineBasePremises NoncontextualPremises
  PremiseAt PremisesAt)
open NamesOnTheStep (Expr)

/-- **A rule with unknowns**: a rule at the one frame over rows with unknowns. -/
abbrev SRule := Rule (OneFrame.Terms Tm)

/-! ## The fragment -/

/-- An unknown a rule binds by matching: one of a take or read pattern. -/
def Bound (r : SRule) (x : ℕ) : Prop := ∃ t ∈ r.body.take ++ r.body.read, x ∈ Term.freeVars (σ := rowSig) t

/-- The terms a rule tells, asks or makes. -/
def written (r : SRule) : List Tm :=
  r.body.tell.map Prod.fst ++ r.body.tell.map Prod.snd ++ r.body.checks.flatMap checkTerms ++ r.body.produce

/-- **Range restriction**: every unknown of a tell, a check or a made row is bound by matching. -/
def RangeRestricted (r : SRule) : Prop := ∀ t ∈ written r, ∀ x ∈ Term.freeVars (σ := rowSig) t, Bound r x

/-- An equation guard. -/
def isGuard : Check Tm → Bool
  | .equal _ _ => true
  | _ => false

/-- **The fragment**: no collect pattern, only equation checks, range restriction. -/
def RangeRestrictedPositive (r : SRule) : Prop :=
  r.collect = [] ∧ r.body.checks.all isGuard = true ∧ RangeRestricted r

instance (r : SRule) (x : ℕ) : Decidable (Bound r x) := by
  unfold Bound
  infer_instance

instance (r : SRule) : Decidable (RangeRestricted r) := by
  unfold RangeRestricted
  infer_instance

instance (r : SRule) : Decidable (RangeRestrictedPositive r) := by
  unfold RangeRestrictedPositive
  infer_instance

/-- The sides of an equation guard. -/
def guardOf : Check Tm → List (Tm × Tm)
  | .equal l r => [(l, r)]
  | _ => []

/-- **The equations a rule asks of its match**: its tells and its equation guards. -/
def equationsOf (r : SRule) : List (Tm × Tm) := r.body.tell ++ r.body.checks.flatMap guardOf

theorem mem_written_of_tell {r : SRule} {e : Tm × Tm} (member : e ∈ r.body.tell) :
    e.1 ∈ written r ∧ e.2 ∈ written r := by
  refine ⟨?_, ?_⟩ <;> simp only [written, List.mem_append, List.mem_map]
  · exact Or.inl (Or.inl (Or.inl ⟨e, member, rfl⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨e, member, rfl⟩))

theorem mem_written_of_equation {r : SRule} {e : Tm × Tm} (member : e ∈ equationsOf r) :
    e.1 ∈ written r ∧ e.2 ∈ written r := by
  rcases List.mem_append.mp member with told | guarded
  · exact mem_written_of_tell told
  · obtain ⟨c, inChecks, inGuard⟩ := List.mem_flatMap.mp guarded
    cases c with
    | equal l r' =>
        rw [guardOf, List.mem_singleton] at inGuard
        subst inGuard
        refine ⟨?_, ?_⟩ <;> simp only [written, List.mem_append, List.mem_flatMap]
        · exact Or.inl (Or.inr ⟨.equal l r', inChecks, by simp [checkTerms]⟩)
        · exact Or.inl (Or.inr ⟨.equal l r', inChecks, by simp [checkTerms]⟩)
    | predicate quantifier _ => simp [guardOf] at inGuard
    | count _ _ => simp [guardOf] at inGuard

theorem mem_written_of_produce {r : SRule} {t : Tm} (member : t ∈ r.body.produce) : t ∈ written r := by
  simp only [written, List.mem_append]
  exact Or.inr member

/-! ## The presentation -/

/-- **The read premise**: the rest decomposes as a row of the read pattern beside a remainder. -/
def readPremise (j : ℕ) (q : Tm) : Premise :=
  .relationQuery "eq" [.fvar "rest", .collection .hashBag [termCode q] (some (readRestName j))]

/-- **The premise of an equation**: its two sides are equal. -/
def equationPremise (e : Tm × Tm) : Premise := .relationQuery "eq" [termCode e.1, termCode e.2]

/-- The premises of a rule: one per read, then one per tell and equation guard. -/
def premisesOf (r : SRule) : List Premise :=
  r.body.read.mapIdx readPremise ++ (equationsOf r).map equationPremise

/-- **The rewrite of a rule**: its takes beside the rest become its made rows beside the rest, under its
premises. -/
def schematicRewrite (index : ℕ) (r : SRule) : RewriteRule where
  name := "Fire" ++ toString index
  typeContext := [("rest", .bag (.base "Row"))]
  premises := premisesOf r
  left := .collection .hashBag (r.body.take.map termCode) (some "rest")
  right := .collection .hashBag (r.body.produce.map termCode) (some "rest")

/-- **The presentation of a program with unknowns**: the sorts and constructors of the ground
presentation, no equations, one rewrite per rule. -/
def presentSchematic (rules : List SRule) : LanguageDef where
  name := "StepOfAProgramWithUnknowns"
  types := ["Nat", "Row", "Store"]
  terms := rowFormers ++ [storeFormer]
  equations := []
  rewrites := rules.mapIdx schematicRewrite

variable {rules : List SRule}

theorem presentSchematic_equations : (presentSchematic rules).equations = [] := rfl

theorem presentSchematic_noAlgebra : (presentSchematic rules).hasAlgebraDeclarations = false := rfl

theorem presentSchematic_formers : rowFormers ⊆ (presentSchematic rules).terms := List.subset_append_left _ _

theorem presentSchematic_store : storeFormer ∈ (presentSchematic rules).terms :=
  List.mem_append_right _ (List.mem_singleton_self _)

/-- **Every rewrite of the presentation is the rewrite of a rule.** -/
theorem of_mem_rewrites {rule : RewriteRule} (member : rule ∈ (presentSchematic rules).rewrites) :
    ∃ r ∈ rules, ∃ index, schematicRewrite index r = rule := by
  obtain ⟨index, bound, named⟩ := List.mem_mapIdx.mp member
  exact ⟨_, List.getElem_mem bound, index, named⟩

/-- **Every rule has its rewrite in the presentation.** -/
theorem exists_mem_rewrites {r : SRule} (member : r ∈ rules) :
    ∃ index, schematicRewrite index r ∈ (presentSchematic rules).rewrites := by
  obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
  exact ⟨index, List.mem_mapIdx.mpr ⟨index, bound, by rw [found]⟩⟩

theorem binderFree_termCode : ∀ p : Tm, binderFree (termCode p) = true
  | .var _ => rfl
  | .const (.sym k) => binderFree_rowCode (.sym k)
  | .const (.name n) => binderFree_rowCode (.name n)
  | .app .app ts => by
      simp [termCode, binderFree, binderFreeList, binderFree_termCode (ts head), binderFree_termCode (ts tail)]
  | .app .code ts => by
      simp [termCode, binderFree, binderFreeList, binderFree_termCode (ts body)]

theorem binderFreeList_termCode : ∀ ps : List Tm, binderFreeList (ps.map termCode) = true
  | [] => rfl
  | p :: ps => by
      simp only [List.map_cons, binderFreeList, binderFree_termCode p, binderFreeList_termCode ps, Bool.and_self]

/-- **Every rewrite moves no metavariable across a binder.** -/
theorem schematicRewrite_aligned (index : ℕ) (r : SRule) :
    ruleDepthAligned (schematicRewrite index r) = true :=
  ruleDepthAligned_of_binderFree _ (binderFreeList_termCode _) (binderFreeList_termCode _)

/-- **No premise of the presentation is contextual**: each is a query of the builtin equality. -/
theorem premisesOf_noncontextual (r : SRule) : NoncontextualPremises (premisesOf r) := by
  have queries : ∀ p ∈ premisesOf r, ∃ args, p = .relationQuery "eq" args := by
    intro p member
    rcases List.mem_append.mp member with read | equation
    · obtain ⟨j, -, rfl⟩ := List.mem_mapIdx.mp read
      exact ⟨_, rfl⟩
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp equation
      exact ⟨_, rfl⟩
  exact ofQueries (premisesOf r) queries
where
  ofQueries : ∀ ps : List Premise, (∀ p ∈ ps, ∃ args, p = .relationQuery "eq" args) → NoncontextualPremises ps
    | [], _ => .nil
    | p :: ps, each => by
        obtain ⟨args, rfl⟩ := each p List.mem_cons_self
        exact .relationQuery (ofQueries ps fun q member => each q (List.mem_cons_of_mem _ member))

/-! ## The builtin equality on instantiated arguments -/

variable {relEnv : RelationEnv}

theorem builtin_eq (L : LanguageDef) (a b : Pattern) : builtinRelationTuples L "eq" [a, b] = [[a, a], [b, b]] := by
  simp [builtinRelationTuples]

/-- **A query of the builtin equality**, when the relation environment adds nothing to it. -/
theorem relationQuery_eq_iff (noEq : ∀ args, relEnv.tuples "eq" args = []) (L : LanguageDef) (b : Bindings)
    (a1 a2 : Pattern) (res : Bindings) :
    res ∈ premiseStepWithEnv relEnv L b (.relationQuery "eq" [a1, a2]) ↔
      ∃ v, (v = applyBindings b a1 ∨ v = applyBindings b a2) ∧
        ∃ bPrem ∈ matchRelationArgs b [a1, a2] [v, v], mergeBindings b bPrem = some res := by
  simp only [premiseStepWithEnv, relationQueryStep, List.map_cons, List.map_nil, noEq, List.append_nil,
    builtin_eq, List.mem_flatMap, List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨tuple, (rfl | rfl), bPrem, member, merged⟩
    · exact ⟨_, Or.inl rfl, bPrem, member, merged⟩
    · exact ⟨_, Or.inr rfl, bPrem, member, merged⟩
  · rintro ⟨v, (rfl | rfl), bPrem, member, merged⟩
    · exact ⟨_, Or.inl rfl, bPrem, member, merged⟩
    · exact ⟨_, Or.inr rfl, bPrem, member, merged⟩

theorem mem_matchRelationArgs_cons {seed : Bindings} {a v : Pattern} {as vs : List Pattern} {bPrem : Bindings} :
    bPrem ∈ matchRelationArgs seed (a :: as) (v :: vs) ↔
      ∃ h ∈ matchRelationArgument seed a v, ∃ ext, mergeBindings seed h = some ext ∧
        ∃ t ∈ matchRelationArgs ext as vs, mergeBindings h t = some bPrem := by
  rw [matchRelationArgs]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨h, member, inner⟩
    cases merged : mergeBindings seed h with
    | none =>
        rw [merged] at inner
        simp at inner
    | some ext =>
        rw [merged] at inner
        simp only [List.mem_filterMap] at inner
        exact ⟨h, member, ext, merged, inner⟩
  · rintro ⟨h, member, ext, merged, t, tMember, tMerged⟩
    refine ⟨h, member, ?_⟩
    rw [merged]
    exact List.mem_filterMap.mpr ⟨t, tMember, tMerged⟩

theorem matchRelationArgs_nil (seed : Bindings) : matchRelationArgs seed [] [] = [[]] := by
  rw [matchRelationArgs]

/-- A last argument, matched and merged. -/
theorem mem_matchRelationArgs_one {seed : Bindings} {a v : Pattern} {t : Bindings} :
    t ∈ matchRelationArgs seed [a] [v] ↔
      t ∈ matchRelationArgument seed a v ∧ ∃ ext, mergeBindings seed t = some ext := by
  rw [mem_matchRelationArgs_cons]
  constructor
  · rintro ⟨h, member, ext, merged, t', inner, tMerged⟩
    rw [matchRelationArgs_nil, List.mem_singleton] at inner
    subst inner
    rw [mergeBindings_nil] at tMerged
    cases tMerged
    exact ⟨member, ext, merged⟩
  · rintro ⟨member, ext, merged⟩
    exact ⟨t, member, ext, merged, [], by rw [matchRelationArgs_nil]; exact List.mem_singleton_self _,
      mergeBindings_nil t⟩

theorem matchRelationArgument_fvar_bound {seed : Bindings} {n m : String} {existing : Pattern} (value : Pattern)
    (found : seed.find? (·.1 == n) = some (m, existing)) :
    matchRelationArgument seed (.fvar n) value = if existing = value then [[]] else [] := by
  simp [matchRelationArgument, Bindings.lookup, found]

theorem matchRelationArgument_fvar_free {seed : Bindings} {n : String} (value : Pattern)
    (missing : seed.find? (·.1 == n) = none) :
    matchRelationArgument seed (.fvar n) value = [[(n, value)]] := by
  simp [matchRelationArgument, Bindings.lookup, missing]

theorem matchRelationArgument_other (seed : Bindings) {a : Pattern} (value : Pattern) (notName : ∀ n, a ≠ .fvar n) :
    matchRelationArgument seed a value = matchPattern a value := by
  cases a with
  | fvar n => exact absurd rfl (notName n)
  | _ => rfl

/-- A merge extends whatever extends both of its arguments. -/
theorem extends_merge {b1 b2 b f : Bindings} (merged : mergeBindings b1 b2 = some b) (first : BindingsExtends b1 f)
    (second : BindingsExtends b2 f) : BindingsExtends b f := by
  intro x v found
  rw [mergeBindings_find merged x, List.find?_append] at found
  cases inFirst : b1.find? (·.1 == x) with
  | none =>
      rw [inFirst, Option.none_or] at found
      exact second x v found
  | some entry =>
      rw [inFirst, Option.some_or] at found
      rw [found] at inFirst
      exact first x v inFirst

/-- **What a matched argument binds**: under every extension of the seed and of the argument's bindings, the
argument is instantiated to the value. -/
theorem matchRelationArgument_sound {seed h final : Bindings} {a v : Pattern} (correct : Pattern.isMatchCorrect a = true)
    (member : h ∈ matchRelationArgument seed a v) (seedExt : BindingsExtends seed final)
    (hExt : BindingsExtends h final) : applyBindings final a = v := by
  by_cases name : ∃ n, a = .fvar n
  · obtain ⟨n, rfl⟩ := name
    cases found : seed.find? (·.1 == n) with
    | none =>
        rw [matchRelationArgument_fvar_free v found, List.mem_singleton] at member
        subst member
        exact applyBindings_fvar_some (hExt n v (by simp))
    | some entry =>
        obtain ⟨m, existing⟩ := entry
        rw [matchRelationArgument_fvar_bound v found] at member
        split_ifs at member with same
        · obtain ⟨named, -⟩ := find?_spec found
          have named' : m = n := named
          rw [named'] at found
          rw [applyBindings_fvar_some (seedExt n existing found), same]
        · exact absurd member List.not_mem_nil
  · have notName : ∀ n, a ≠ .fvar n := fun n same => name ⟨n, same⟩
    rw [matchRelationArgument_other seed v notName, matchPattern_iff_matchRel] at member
    exact matchRel_correct_of_extends member correct hExt

/-! ## What a premise binds -/

variable (relEnv)

/-- **An equation premise's result makes the two sides equal under every extension.** -/
theorem equationPremise_sound (noEq : ∀ args, relEnv.tuples "eq" args = []) {L : LanguageDef} {b res : Bindings}
    {e : Tm × Tm} (member : res ∈ premiseStepWithEnv relEnv L b (equationPremise e)) :
    BindingsExtends b res ∧ ∀ final, BindingsExtends res final →
      applyBindings final (termCode e.1) = applyBindings final (termCode e.2) := by
  obtain ⟨v, -, bPrem, prem, merged⟩ := (relationQuery_eq_iff noEq L b _ _ res).mp member
  obtain ⟨h1, h1Member, ext, extMerged, t, tMember, tMerged⟩ := mem_matchRelationArgs_cons.mp prem
  obtain ⟨h2Member, ext2, -⟩ := mem_matchRelationArgs_one.mp tMember
  refine ⟨extends_left merged, fun final finalExt => ?_⟩
  have bPremExt : BindingsExtends bPrem final := extends_trans (extends_right merged) finalExt
  have bExt : BindingsExtends b final := extends_trans (extends_left merged) finalExt
  have h1Ext : BindingsExtends h1 final := extends_trans (extends_left tMerged) bPremExt
  have h2Ext : BindingsExtends t final := extends_trans (extends_right tMerged) bPremExt
  have extExt : BindingsExtends ext final := extends_merge extMerged bExt h1Ext
  rw [matchRelationArgument_sound (isMatchCorrect_termCode _) h1Member bExt h1Ext,
    matchRelationArgument_sound (isMatchCorrect_termCode _) h2Member extExt h2Ext]

/-- **A read premise's result sends the read pattern into the rest under every extension.** -/
theorem readPremise_sound (noEq : ∀ args, relEnv.tuples "eq" args = []) {L : LanguageDef} {b res : Bindings}
    {j : ℕ} {q : Tm} {B : List Pattern}
    (restBound : b.find? (·.1 == "rest") = some ("rest", .collection .hashBag B none))
    (member : res ∈ premiseStepWithEnv relEnv L b (readPremise j q)) :
    BindingsExtends b res ∧ ∀ final, BindingsExtends res final → applyBindings final (termCode q) ∈ B := by
  obtain ⟨v, -, bPrem, prem, merged⟩ := (relationQuery_eq_iff noEq L b _ _ res).mp member
  obtain ⟨h1, h1Member, ext, -, t, tMember, tMerged⟩ := mem_matchRelationArgs_cons.mp prem
  obtain ⟨h2Member, -, -⟩ := mem_matchRelationArgs_one.mp tMember
  rw [matchRelationArgument_fvar_bound v restBound] at h1Member
  split_ifs at h1Member with same
  · subst same
    rw [matchRelationArgument_other ext _ (fun _ different => by cases different),
      matchPattern_iff_matchRel] at h2Member
    cases h2Member with
    | collection _ bagMatch =>
        cases bagMatch with
        | cons index bound headMatch _ hMerged =>
            refine ⟨extends_left merged, fun final finalExt => ?_⟩
            have bPremExt : BindingsExtends bPrem final := extends_trans (extends_right merged) finalExt
            have tExt : BindingsExtends t final := extends_trans (extends_right tMerged) bPremExt
            have headExt := extends_trans (extends_left hMerged) tExt
            rw [matchRel_correct_of_extends headMatch (isMatchCorrect_termCode q) headExt]
            exact List.getElem_mem bound
  · exact absurd h1Member List.not_mem_nil

/-! ## When a premise has a result -/

/-- **A matched argument has a result agreeing with the assignment**, at a value that is the code of the
argument's instance. -/
theorem matchRelationArgument_complete (f : String → Option Pattern) (θ : ℕ → Expr)
    (agreeθ : ∀ x, f (unknownName x) = some (rowCode (θ x))) {seed : Bindings} (seedAgrees : Agrees f seed)
    (p : Tm) : ∃ h ∈ matchRelationArgument seed (termCode p) (rowCode (inst θ p)), Agrees f h ∧
      ∀ x ∈ p.freeVars, (unknownName x, rowCode (θ x)) ∈ seed ∨ (unknownName x, rowCode (θ x)) ∈ h := by
  cases p with
  | var x =>
      show ∃ h ∈ matchRelationArgument seed (.fvar (unknownName x)) (rowCode (θ x)), _
      cases found : seed.find? (·.1 == unknownName x) with
      | none =>
          rw [matchRelationArgument_fvar_free _ found]
          refine ⟨_, List.mem_singleton_self _, fun e member => ?_, fun y member => ?_⟩
          · rw [List.mem_singleton.mp member]
            exact agreeθ x
          · rw [mem_vars_var.mp member]
            exact Or.inr (List.mem_singleton_self _)
      | some entry =>
          obtain ⟨m, existing⟩ := entry
          obtain ⟨named, present⟩ := find?_spec found
          have known := seedAgrees _ present
          have named' : m = unknownName x := named
          rw [named', agreeθ x] at known
          have same : existing = rowCode (θ x) := (Option.some.inj known).symm
          rw [matchRelationArgument_fvar_bound _ found, if_pos same]
          refine ⟨[], List.mem_singleton_self _, fun _ member => absurd member List.not_mem_nil, fun y member => ?_⟩
          rw [mem_vars_var.mp member]
          refine Or.inl ?_
          rw [← named', ← same]
          exact present
  | const c =>
      obtain ⟨hb, matched, sub, all⟩ := matchRel_termCode θ (.const c)
      refine ⟨hb, ?_, fun e member => ?_, fun x member => Or.inr (all x member)⟩
      · rw [matchRelationArgument_other seed _ (fun n different => by
          cases c <;> simp [termCode] at different), matchPattern_iff_matchRel]
        exact matched
      · obtain ⟨x, -, rfl⟩ := sub e member
        exact agreeθ x
  | app g ts =>
      obtain ⟨hb, matched, sub, all⟩ := matchRel_termCode θ (.app g ts)
      refine ⟨hb, ?_, fun e member => ?_, fun x member => Or.inr (all x member)⟩
      · rw [matchRelationArgument_other seed _ (fun n different => by
          cases g <;> simp [termCode] at different), matchPattern_iff_matchRel]
        exact matched
      · obtain ⟨x, -, rfl⟩ := sub e member
        exact agreeθ x

/-- **An equation premise has a result** where the two sides have equal instances and the unknowns of the
first side are bound. -/
theorem equationPremise_complete (noEq : ∀ args, relEnv.tuples "eq" args = []) (L : LanguageDef)
    (f : String → Option Pattern) (θ : ℕ → Expr) (agreeθ : ∀ x, f (unknownName x) = some (rowCode (θ x)))
    {b : Bindings} (agrees : Agrees f b) {e : Tm × Tm}
    (bound : ∀ x ∈ e.1.freeVars, (unknownName x, rowCode (θ x)) ∈ b) (holds : inst θ e.1 = inst θ e.2) :
    ∃ res ∈ premiseStepWithEnv relEnv L b (equationPremise e), Agrees f res ∧ ∀ entry ∈ b, entry ∈ res := by
  have value : applyBindings b (termCode e.1) = rowCode (inst θ e.1) :=
    applyBindings_termCode_of_lookup b θ e.1 fun x member => find?_of_agrees agrees (bound x member)
  obtain ⟨h1, h1Member, h1Agrees, -⟩ := matchRelationArgument_complete f θ agreeθ agrees e.1
  obtain ⟨ext, extMerged, extAgrees, -, -⟩ := merge_exists f h1 b agrees h1Agrees
  obtain ⟨h2, h2Member, h2Agrees, -⟩ := matchRelationArgument_complete f θ agreeθ extAgrees e.2
  rw [← holds] at h2Member
  obtain ⟨ext2, ext2Merged, -, -, -⟩ := merge_exists f h2 ext extAgrees h2Agrees
  obtain ⟨bPrem, bPremMerged, bPremAgrees, -, -⟩ := merge_exists f h2 h1 h1Agrees h2Agrees
  obtain ⟨res, merged, resAgrees, -, super⟩ := merge_exists f bPrem b agrees bPremAgrees
  refine ⟨res, (relationQuery_eq_iff noEq L b _ _ res).mpr ⟨_, Or.inl value.symm, bPrem, ?_, merged⟩, resAgrees,
    fun entry member => super entry (List.mem_append_left _ member)⟩
  exact mem_matchRelationArgs_cons.mpr ⟨h1, h1Member, ext, extMerged, h2,
    mem_matchRelationArgs_one.mpr ⟨h2Member, ext2, ext2Merged⟩, bPremMerged⟩

/-- The bag the rest of a read binds: the rest without the row read. -/
def readBag (rem : List Expr) (row : Expr) : Pattern :=
  .collection .hashBag ((rem.map rowCode).eraseIdx (rem.idxOf row)) none

/-- **A read premise has a result** where the read pattern's instance is a row of the rest. -/
theorem readPremise_complete (noEq : ∀ args, relEnv.tuples "eq" args = []) (L : LanguageDef)
    (f : String → Option Pattern) (θ : ℕ → Expr) (agreeθ : ∀ x, f (unknownName x) = some (rowCode (θ x)))
    {b : Bindings} (agrees : Agrees f b) {j : ℕ} {q : Tm} {rem : List Expr}
    (restIn : ("rest", .collection .hashBag (rem.map rowCode) none) ∈ b) (inRest : inst θ q ∈ rem)
    (restRead : f (readRestName j) = some (readBag rem (inst θ q))) :
    ∃ res ∈ premiseStepWithEnv relEnv L b (readPremise j q), Agrees f res ∧ (∀ entry ∈ b, entry ∈ res) ∧
      ∀ x ∈ q.freeVars, (unknownName x, rowCode (θ x)) ∈ res := by
  have restFound := find?_of_agrees agrees restIn
  have value : applyBindings b (.fvar "rest") = .collection .hashBag (rem.map rowCode) none :=
    applyBindings_fvar_some restFound
  have h1Member : [] ∈ matchRelationArgument b (.fvar "rest") (.collection .hashBag (rem.map rowCode) none) := by
    rw [matchRelationArgument_fvar_bound _ restFound, if_pos rfl]
    exact List.mem_singleton_self _
  obtain ⟨hq, headMatch, hqSub, hqAll⟩ := matchRel_termCode θ q
  have hqAgrees : Agrees f hq := fun e member => by
    obtain ⟨x, -, rfl⟩ := hqSub e member
    exact agreeθ x
  have restAgrees : Agrees f [(readRestName j, readBag rem (inst θ q))] := fun e member => by
    rw [List.mem_singleton.mp member]
    exact restRead
  obtain ⟨h2, hMerged, h2Agrees, -, h2Super⟩ := merge_exists f _ hq hqAgrees restAgrees
  have bound : rem.idxOf (inst θ q) < (rem.map rowCode).length := by
    rw [List.length_map]
    exact List.idxOf_lt_length_of_mem inRest
  have atIndex : (rem.map rowCode)[rem.idxOf (inst θ q)] = rowCode (inst θ q) := by
    rw [List.getElem_map, List.getElem_idxOf]
  have h2Member : h2 ∈ matchRelationArgument b (.collection .hashBag [termCode q] (some (readRestName j)))
      (.collection .hashBag (rem.map rowCode) none) := by
    rw [matchRelationArgument_other b _ (fun _ different => by cases different), matchPattern_iff_matchRel]
    refine .collection (by decide) (.cons (rem.idxOf (inst θ q)) bound ?_ .nilRest hMerged)
    rw [atIndex]
    exact headMatch
  obtain ⟨ext2, ext2Merged, -, -, -⟩ := merge_exists f h2 b agrees h2Agrees
  obtain ⟨bPrem, bPremMerged, bPremAgrees, -, bPremSuper⟩ := merge_exists f h2 [] (fun _ member => absurd member
    List.not_mem_nil) h2Agrees
  obtain ⟨res, merged, resAgrees, -, super⟩ := merge_exists f bPrem b agrees bPremAgrees
  refine ⟨res, (relationQuery_eq_iff noEq L b _ _ res).mpr ⟨_, Or.inl value.symm, bPrem, ?_, merged⟩, resAgrees,
    fun entry member => super entry (List.mem_append_left _ member), fun x member => ?_⟩
  · exact mem_matchRelationArgs_cons.mpr ⟨[], h1Member, b, mergeBindings_nil b, h2,
      mem_matchRelationArgs_one.mpr ⟨h2Member, ext2, ext2Merged⟩, bPremMerged⟩
  · exact super _ (List.mem_append_right _ (bPremSuper _ (List.mem_append_right _
      (h2Super _ (List.mem_append_left _ (hqAll x member))))))

/-! ## Along a list of premises -/

variable {relEnv}

/-- **Every premise along a derivation constrains its final bindings.** -/
theorem premisesAt_sound {base : BasePremiseEvaluator} {L : LanguageDef} {fuel : ℕ}
    (allowed : Premise → Prop) (Inv : Bindings → Prop) (Q : Premise → Bindings → Prop)
    (each : ∀ b p res, allowed p → Inv b → PremiseAt base L fuel b p res →
      BindingsExtends b res ∧ Inv res ∧ ∀ final, BindingsExtends res final → Q p final) :
    ∀ {ps : List Premise} {b final : Bindings}, (∀ p ∈ ps, allowed p) → Inv b →
      PremisesAt base L fuel b ps final →
        BindingsExtends b final ∧ Inv final ∧ ∀ p ∈ ps, ∀ final', BindingsExtends final final' → Q p final'
  | [], b, final, _, inv, derivation => by
      cases derivation
      exact ⟨extends_refl _, inv, fun _ member => absurd member List.not_mem_nil⟩
  | p :: ps, b, final, allowedAll, inv, derivation => by
      cases derivation with
      | cons first rest =>
          obtain ⟨extended, invMid, holds⟩ := each _ p _ (allowedAll p List.mem_cons_self) inv first
          obtain ⟨extendedRest, invFinal, holdsRest⟩ := premisesAt_sound allowed Inv Q each
            (fun q member => allowedAll q (List.mem_cons_of_mem _ member)) invMid rest
          refine ⟨extends_trans extended extendedRest, invFinal, fun q member final' finalExt => ?_⟩
          rcases List.mem_cons.mp member with rfl | member
          · exact holds final' (extends_trans extendedRest finalExt)
          · exact holdsRest q member final' finalExt

/-- **A list of premises each of which has a result has a derivation.** -/
theorem premisesAt_complete {base : BasePremiseEvaluator} {L : LanguageDef} {fuel : ℕ}
    (allowed : Premise → Prop) (Inv : Bindings → Prop) (Q : Premise → Bindings → Prop)
    (upward : ∀ p b b', Q p b → (∀ e ∈ b, e ∈ b') → Q p b')
    (each : ∀ b p, allowed p → Inv b →
      ∃ res, PremiseAt base L fuel b p res ∧ Inv res ∧ (∀ e ∈ b, e ∈ res) ∧ Q p res) :
    ∀ {ps : List Premise}, (∀ p ∈ ps, allowed p) → ∀ b, Inv b →
      ∃ final, PremisesAt base L fuel b ps final ∧ Inv final ∧ (∀ e ∈ b, e ∈ final) ∧ ∀ p ∈ ps, Q p final
  | [], _, b, inv => ⟨b, .nil b, inv, fun _ member => member, fun _ member => absurd member List.not_mem_nil⟩
  | p :: ps, allowedAll, b, inv => by
      obtain ⟨mid, first, invMid, superMid, holds⟩ := each b p (allowedAll p List.mem_cons_self) inv
      obtain ⟨final, rest, invFinal, superFinal, holdsRest⟩ := premisesAt_complete allowed Inv Q upward each
        (fun q member => allowedAll q (List.mem_cons_of_mem _ member)) mid invMid
      refine ⟨final, .cons first rest, invFinal, fun e member => superFinal e (superMid e member),
        fun q member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact upward _ _ _ holds superFinal
      · exact holdsRest q member

theorem premisesAt_append {base : BasePremiseEvaluator} {L : LanguageDef} {fuel : ℕ} :
    ∀ {ps qs : List Premise} {b final : Bindings},
      PremisesAt base L fuel b (ps ++ qs) final ↔ ∃ mid, PremisesAt base L fuel b ps mid ∧ PremisesAt base L fuel mid qs final
  | [], qs, b, final => by
      constructor
      · intro derivation
        exact ⟨b, .nil b, derivation⟩
      · rintro ⟨mid, first, rest⟩
        cases first
        exact rest
  | p :: ps, qs, b, final => by
      constructor
      · intro derivation
        cases derivation with
        | cons first rest =>
            obtain ⟨mid, restFirst, restSecond⟩ := (premisesAt_append (ps := ps)).mp rest
            exact ⟨mid, .cons first restFirst, restSecond⟩
      · rintro ⟨mid, first, rest⟩
        cases first with
        | cons head tail =>
            exact .cons head ((premisesAt_append (ps := ps)).mpr ⟨mid, tail, rest⟩)

#print axioms premisesOf_noncontextual
#print axioms relationQuery_eq_iff
#print axioms extends_merge
#print axioms matchRelationArgument_sound
#print axioms equationPremise_sound
#print axioms readPremise_sound
#print axioms matchRelationArgument_complete
#print axioms equationPremise_complete
#print axioms readPremise_complete
#print axioms premisesAt_sound
#print axioms premisesAt_complete
#print axioms premisesAt_append

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic
