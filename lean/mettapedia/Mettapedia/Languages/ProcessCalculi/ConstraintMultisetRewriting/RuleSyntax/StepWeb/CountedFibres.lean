import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedClasses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.RunFibres

/-!
# Answer multiplicities counted by origin fibres

Over a firing of the set presentation by a rule `r`, the held presentation (`CountedTransitions`)
has one firing for each **origin** of `r`: the ambient control rule `r` itself, if `r` is one, and
each held occurrence whose equation has the schema `r`. This module counts those origins and
carries the count to classes of histories, to the bag of answers, and to the run fibres of the
held-rule step.

The constructions are those of `CountedTransitions` (both: a bag store of rows, one match per step,
guards asked after the firing's own tells, one knowledge store), the set presentation with its rules
fixed beside the store as a set, the held presentation with the control rules fixed beside the store
and the equations held in it as persistent occurrences indexed by their positions.

## What is shown

* `originCount`, `originCount_eq`: the origins of a rule are the ambient occurrence, if the rule is a
  control rule, and the held occurrences that hold it. `originCount_control`: a control rule has one
  origin; `originCount_schema`: a schema has as many origins as equations with that schema, since no
  schema is a control rule (`schema_not_control`).
* `originWords_card`: the words of available origins over a word of rules are counted by the
  product of the origin counts (`originWays`).
* `completeHeld_iff_rule`, `finishedHeld_iff_rule`: a word of available origins is a complete, resp.
  finished, held class exactly when its word of rules is a complete, resp. finished, class by rules
  (`Hosting.Alternatives.CompleteRuleClass`). These hold for every source program, not only the first
  fragment. `classAnswer_rule`: on a word of names the answer observer
  `Hosting.Alternatives.classAnswer` is the answer of the class by rules of its rules.
* **`origin_fibre_card`, `bag_by_origin_counts`**: for a program and a query of the first fragment and
  every source run that ends, the delivered multiset of words of names of `bag_of_held_classes` splits
  by words of rules into origin fibres: over a complete class by rules lie exactly as many words of
  names as the product of its rules' origin counts, each kept with its names and origins, all with
  one answer; the bag of answers is the multiset of answer sets `classAnswer` of the finished
  members.
* `bag_by_rule_counts`: the coarser reading that forgets the names in each fibre: each complete class
  by rules counted as many times as the product of its rules' origin counts. With pairwise distinct
  schemas every count is one (`originWays_of_nodup`), and it gives back
  `Hosting.Alternatives.bag_of_rule_classes` (`bag_of_rule_classes_of_nodup`); without that
  hypothesis the counts are what the set of rules loses.
* `held_run_fibre_card`: for every actual run of the set presentation with fixed openings and row
  identities, the actual runs of the held-rule step over it (the run fibres of
  `Interface.Bridges.LiveRules.Origins`) number the product of the origin counts of its rules: the
  same count, at the level of runs.

## What is not shown here

Concurrent executions and equivalences between them are not treated: the histories counted here are
the histories of one alternative, in which each firing takes the row the firing before it made. The
closed example and its controls are in `CountedExample`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Counted

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Hosting Hosting.Alternatives
open RuleOccurrences
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S} {Ty : Type}

/-! ## Origins of a rule -/

section Origins

variable (P : SourceLanguage.Program κ Γ star Ty)

/-- **An available origin**: a control rule of the ambient program, or a held occurrence. -/
def OriginAvailable : Use (CRule S) ℕ → Prop
  | .ambient c => c ∈ controlRules N
  | .held i => i ∈ heldIds P

/-- **The rule of an origin**: the control rule, or the rule the occurrence holds. -/
def heldCode : Use (CRule S) ℕ → CRule S
  | .ambient c => c
  | .held i => heldRule N P i

theorem available_iff (s : HostState S) (u : Use (CRule S) ℕ) :
    (heldState N P s).Available (controlRules N) u ↔ OriginAvailable N P u := by
  cases u <;> exact Iff.rfl

theorem codeOf_eq (s : HostState S) (u : Use (CRule S) ℕ) :
    (heldState N P s).codeOf u = heldCode N P u := by
  cases u <;> rfl

variable {N P} in
/-- **The origin of a name that denotes a rule holds that rule and is available.** -/
theorem origin_code {n : RuleName} {r : CRule S} (named : ruleNamed N P n = some r) :
    heldCode N P (origin N n) = r ∧ OriginAvailable N P (origin N n) := by
  cases n with
  | ret =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      exact ⟨rfl, (mem_controlRules N).mpr (Or.inl rfl)⟩
  | unmatched =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      exact ⟨rfl, (mem_controlRules N).mpr (Or.inr (Or.inl rfl))⟩
  | left =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      exact ⟨rfl, (mem_controlRules N).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
  | right =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      exact ⟨rfl, (mem_controlRules N).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | eqn i =>
      obtain ⟨e, get, rfl⟩ := Option.map_eq_some_iff.mp named
      obtain ⟨small, -⟩ := List.getElem?_eq_some_iff.mp get
      exact ⟨heldRule_of_get get, Finset.mem_range.mpr small⟩

/-- **The rules of a word of names are the rules of its origins**, and its origins are available,
when every name denotes a rule. -/
theorem rules_of_names : ∀ ν : List RuleName, (∀ n ∈ ν, ∃ r, ruleNamed N P n = some r) →
    ν.filterMap (ruleNamed N P) = (ν.map (origin N)).map (heldCode N P) ∧
      ∀ u ∈ ν.map (origin N), OriginAvailable N P u
  | [], _ => ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩
  | n :: rest, valid => by
      obtain ⟨r, named⟩ := valid n List.mem_cons_self
      obtain ⟨code, available⟩ := origin_code named
      obtain ⟨rules, availableRest⟩ :=
        rules_of_names rest fun n' member => valid n' (List.mem_cons_of_mem _ member)
      refine ⟨?_, ?_⟩
      · rw [List.filterMap_cons_some named, List.map_cons, List.map_cons, rules, code]
      · intro u member
        rcases List.mem_cons.mp member with rfl | later
        · exact available
        · exact availableRest u later

/-- **The origins of a rule.** -/
abbrev OriginsOf (r : CRule S) := {u : Use (CRule S) ℕ // OriginAvailable N P u ∧ heldCode N P u = r}

/-- **The number of origins of a rule.** -/
noncomputable def originCount (r : CRule S) : ℕ := Nat.card (OriginsOf N P r)

/-- **The number of words of origins over a word of rules**: the product of the origin counts. -/
noncomputable def originWays (ρ : List (CRule S)) : ℕ := (ρ.map (originCount N P)).prod

/-- **An origin is the ambient occurrence or a held one.** -/
def originSplit (r : CRule S) :
    OriginsOf N P r ≃ {_point : Unit // r ∈ controlRules N} ⊕ {i : ℕ // i ∈ heldIds P ∧ heldRule N P i = r} where
  toFun origin := by
    obtain ⟨use, available, aligned⟩ := origin
    cases use with
    | ambient rule => exact .inl ⟨(), aligned ▸ available⟩
    | held identity => exact .inr ⟨identity, available, aligned⟩
  invFun
    | .inl available => ⟨.ambient r, available.property, rfl⟩
    | .inr available => ⟨.held available.val, available.property.1, available.property.2⟩
  left_inv origin := by
    obtain ⟨use, available, aligned⟩ := origin
    cases use with
    | ambient rule => exact Subtype.ext (congrArg Use.ambient aligned.symm)
    | held identity => rfl
  right_inv origin := by
    cases origin with
    | inl available => cases available with | mk point available => cases point; rfl
    | inr available => rfl

theorem heldIdentities_finite (r : CRule S) : Finite {i : ℕ // i ∈ heldIds P ∧ heldRule N P i = r} :=
  Finite.of_injective (fun value => (⟨value.val, value.property.1⟩ : {i : ℕ // i ∈ heldIds P}))
    (fun _ _ same => Subtype.ext (congrArg (fun value : {i : ℕ // i ∈ heldIds P} => value.val) same))

/-- **The origin count**: one for the ambient program, if the rule is a control rule, and one for
each occurrence that holds the rule. -/
theorem originCount_eq (r : CRule S) :
    originCount N P r = Nat.card {_point : Unit // r ∈ controlRules N} +
      Nat.card {i : ℕ // i ∈ heldIds P ∧ heldRule N P i = r} := by
  have := heldIdentities_finite N P r
  rw [originCount, Nat.card_congr (originSplit N P r), Nat.card_sum]

omit P in
theorem bindStartRule_headTag : HeadTag N (bindStartRule N) .bind := by
  intro pat member B h
  rw [List.mem_singleton.mp member]
  refine ⟨![instantiate h (unk .pattern), instantiate h (unk .first), instantiate h (unk .second)],
    instantiate h (unk .stack), ?_⟩
  change observe (instantiate h _) = _
  rw [instantiate_altN, instantiate_evalN, instantiate_bindN]

omit P in
/-- **No schema is a control rule**: by the tag under `eval` it takes, by its checks, or by its
tells. -/
theorem schema_not_control (e : SourceLanguage.Equation κ Γ star Ty) : schema N e ∉ controlRules N := by
  intro member
  rcases (mem_controlRules N).mp member with h | h | h | h | h | h
  · exact ne_of_headTag N (List.cons_ne_nil _ _) (retRule_headTag N) (schema_headTag N e) (by decide) h.symm
  · exact checks_ne (by show (0 : ℕ) ≠ 1; omega) h
  · exact ne_of_headTag N (List.cons_ne_nil _ _) (choiceLeftRule_headTag N) (schema_headTag N e) (by decide)
      h.symm
  · exact ne_of_headTag N (List.cons_ne_nil _ _) (choiceRightRule_headTag N) (schema_headTag N e) (by decide)
      h.symm
  · exact ne_of_headTag N (List.cons_ne_nil _ _) (bindStartRule_headTag N) (schema_headTag N e) (by decide)
      h.symm
  · have tells := congrArg (fun r : CRule S => r.body.tell.length) h
    exact absurd tells (by show (0 : ℕ) ≠ 1; omega)

theorem heldRule_not_control {i : ℕ} (held : i ∈ heldIds P) : heldRule N P i ∉ controlRules N := by
  rw [heldRule_lt (Finset.mem_range.mp held)]
  exact schema_not_control N _

/-- **A control rule has one origin**: the ambient program; no occurrence holds it. -/
theorem originCount_control {c : CRule S} (control : c ∈ controlRules N) : originCount N P c = 1 := by
  rw [originCount_eq]
  have none : Nat.card {i : ℕ // i ∈ heldIds P ∧ heldRule N P i = c} = 0 := by
    rw [Nat.card_eq_zero]
    exact Or.inl ⟨fun ⟨i, held, same⟩ => heldRule_not_control N P held (same ▸ control)⟩
  have : Nonempty {_point : Unit // c ∈ controlRules N} := ⟨⟨(), control⟩⟩
  have one : Nat.card {_point : Unit // c ∈ controlRules N} = 1 := Nat.card_unique
  rw [none, one]

/-- **A schema has one origin for each equation with that schema.** -/
theorem originCount_schema (e : SourceLanguage.Equation κ Γ star Ty) :
    originCount N P (schema N e) = Nat.card {i : ℕ // i ∈ heldIds P ∧ heldRule N P i = schema N e} := by
  rw [originCount_eq]
  have none : Nat.card {_point : Unit // schema N e ∈ controlRules N} = 0 := by
    rw [Nat.card_eq_zero]
    exact Or.inl ⟨fun ⟨_, inside⟩ => schema_not_control N e inside⟩
  rw [none, zero_add]

/-- **With pairwise distinct schemas, an equation's schema has one origin.** -/
theorem originCount_of_nodup (distinct : (P.equations.map (schema N)).Nodup) {i : ℕ}
    (small : i < P.equations.length) : originCount N P (schema N P.equations[i]) = 1 := by
  rw [originCount_schema]
  have : Nonempty {j : ℕ // j ∈ heldIds P ∧ heldRule N P j = schema N P.equations[i]} :=
    ⟨⟨i, Finset.mem_range.mpr small, heldRule_lt small⟩⟩
  have : Subsingleton {j : ℕ // j ∈ heldIds P ∧ heldRule N P j = schema N P.equations[i]} := by
    constructor
    rintro ⟨j, heldJ, sameJ⟩ ⟨k, heldK, sameK⟩
    have smallJ := Finset.mem_range.mp heldJ
    have smallK := Finset.mem_range.mp heldK
    rw [heldRule_lt smallJ] at sameJ
    rw [heldRule_lt smallK] at sameK
    have mapped : (P.equations.map (schema N))[j]'(by simpa using smallJ) =
        (P.equations.map (schema N))[k]'(by simpa using smallK) := by
      simp only [List.getElem_map, sameJ, sameK]
    exact Subtype.ext ((distinct.getElem_inj_iff).mp mapped)
  exact Nat.card_unique

/-! ## Words of origins over a word of rules -/

/-- **The words of available origins over a word of rules.** -/
abbrev OriginWords (ρ : List (CRule S)) :=
  {w : List (Use (CRule S) ℕ) // w.map (heldCode N P) = ρ ∧ ∀ u ∈ w, OriginAvailable N P u}

/-- **There are as many words of origins over a word of rules as the product of the origin counts
of its rules.** -/
theorem originWords_card : ∀ ρ : List (CRule S), Nat.card (OriginWords N P ρ) = originWays N P ρ
  | [] => by
      have empty : OriginWords N P [] ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => ⟨[], rfl, fun _ member => absurd member List.not_mem_nil⟩
          left_inv := fun w => Subtype.ext (List.map_eq_nil_iff.mp w.property.1).symm
          right_inv := fun _ => rfl }
      rw [Nat.card_congr empty, Nat.card_unique]
      rfl
  | r :: ρ => by
      let cons : OriginsOf N P r × OriginWords N P ρ → OriginWords N P (r :: ρ) := fun x =>
        ⟨x.1.val :: x.2.val, by rw [List.map_cons, x.1.property.2, x.2.property.1],
          fun u member => by
            rcases List.mem_cons.mp member with rfl | later
            · exact x.1.property.1
            · exact x.2.property.2 u later⟩
      have bijective : Function.Bijective cons := by
        constructor
        · rintro ⟨⟨u, _⟩, ⟨w, _⟩⟩ ⟨⟨u', _⟩, ⟨w', _⟩⟩ same
          have lists := congrArg Subtype.val same
          simp only [cons, List.cons.injEq] at lists
          obtain ⟨rfl, rfl⟩ := lists
          rfl
        · rintro ⟨w, codes, available⟩
          obtain ⟨u, w', rfl, code, codes'⟩ := List.map_eq_cons_iff.mp codes
          refine ⟨(⟨u, available u List.mem_cons_self, code⟩,
            ⟨w', codes', fun x member => available x (List.mem_cons_of_mem _ member)⟩), rfl⟩
      rw [← Nat.card_congr (Equiv.ofBijective cons bijective), Nat.card_prod, originWords_card ρ]
      show originCount N P r * originWays N P ρ = originWays N P (r :: ρ)
      unfold originWays
      rw [List.map_cons, List.prod_cons]

/-- **With pairwise distinct schemas, every word of rules of the translated program has one word of
origins over it.** -/
theorem originWays_of_nodup (distinct : (P.equations.map (schema N)).Nodup) :
    ∀ ρ : List (CRule S), (∀ r ∈ ρ, r ∈ translate N P) → originWays N P ρ = 1
  | [], _ => rfl
  | r :: ρ, inside => by
      unfold originWays
      rw [List.map_cons, List.prod_cons]
      have rest : originWays N P ρ = 1 :=
        originWays_of_nodup distinct ρ fun r' member => inside r' (List.mem_cons_of_mem _ member)
      unfold originWays at rest
      rw [rest, mul_one]
      rcases (mem_translate N).mp (inside r List.mem_cons_self) with control | ⟨e, member, rfl⟩
      · exact originCount_control N P control
      · obtain ⟨i, small, rfl⟩ := List.getElem_of_mem member
        exact originCount_of_nodup N P distinct small

end Origins

/-! ## Held classes over classes by rules -/

section OverRules

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star} (q : Comp κ Γ star D.Ty)

/-- **Forgetting origins**: a held history is a history of the set presentation by the origins'
rules. -/
theorem ruleFrom_of_heldFrom {w : List (Use (CRule S) ℕ)} {s : HostState S} {a : ℕ}
    (held : HeldFrom N P q w s a) : RuleFrom N P q (w.map (heldCode N P)) s a :=
  Chain.map (heldCode N P) (fun u s _ _ _ fired => (codeOf_eq N P s u) ▸ heldFires_firesAt fired) held

/-- **The origins of a held history are available.** -/
theorem heldFrom_available {w : List (Use (CRule S) ℕ)} {s : HostState S} {a : ℕ}
    (held : HeldFrom N P q w s a) : ∀ u ∈ w, OriginAvailable N P u := by
  induction held with
  | nil => intro u member; cases member
  | snoc _ last ih =>
      intro u member
      rcases List.mem_append.mp member with old | new
      · exact ih u old
      · rw [List.mem_singleton.mp new]
        obtain ⟨f, use, admitted, -⟩ := last
        have shapes := admitted.1.2.2.available
        rw [use] at shapes
        exact (available_iff N P _ _).mp shapes

/-- **Lifting a history of the set presentation along a word of available origins** of its rules. -/
theorem heldFrom_of_ruleFrom {ρ : List (CRule S)} {s : HostState S} {a : ℕ} (chain : RuleFrom N P q ρ s a) :
    ∀ {w : List (Use (CRule S) ℕ)}, w.map (heldCode N P) = ρ → (∀ u ∈ w, OriginAvailable N P u) →
      HeldFrom N P q w s a := by
  induction chain with
  | nil =>
      intro w codes _
      rw [List.map_eq_nil_iff.mp codes]
      exact .nil _ _
  | snoc _ last ih =>
      intro w codes available
      obtain ⟨w₁, w₂, rfl, codes₁, codes₂⟩ := List.map_eq_append_iff.mp codes
      obtain ⟨u, rfl, code⟩ := List.map_eq_singleton_iff.mp codes₂
      have before : ∀ x ∈ w₁, OriginAvailable N P x := fun x member =>
        available x (List.mem_append_left _ member)
      have here : OriginAvailable N P u := available u (List.mem_append_right _ List.mem_cons_self)
      exact .snoc (ih codes₁ before)
        (heldFires_of_firesAt ((available_iff N P _ u).mpr here) ((codeOf_eq N P _ u).trans code) last)

/-- **A word of origins is a complete held class exactly when its origins are available and its word
of rules is a complete class by rules.** -/
theorem completeHeld_iff_rule (w : List (Use (CRule S) ℕ)) :
    CompleteHeldClass N P q w ↔
      CompleteRuleClass N P q (w.map (heldCode N P)) ∧ ∀ u ∈ w, OriginAvailable N P u := by
  constructor
  · rintro ⟨s, a, held, still⟩
    exact ⟨⟨s, a, ruleFrom_of_heldFrom N q held, (heldTerminal_iff N s).mp still⟩,
      heldFrom_available N q held⟩
  · rintro ⟨⟨s, a, chain, terminal⟩, available⟩
    exact ⟨s, a, heldFrom_of_ruleFrom N q chain rfl available, (heldTerminal_iff N s).mpr terminal⟩

theorem finishedHeld_iff_rule {w : List (Use (CRule S) ℕ)} (available : ∀ u ∈ w, OriginAvailable N P u) :
    FinishedHeldClass N P q w ↔ FinishedRuleClass N P q (w.map (heldCode N P)) := by
  constructor
  · rintro ⟨s, a, held, finished⟩
    exact ⟨s, a, ruleFrom_of_heldFrom N q held, finished⟩
  · rintro ⟨s, a, chain, finished⟩
    exact ⟨s, a, heldFrom_of_ruleFrom N q chain rfl available, finished⟩

/-- The members of a multiset of distinct elements are counted by its cardinality. -/
theorem card_of_nodup {α : Type*} {M : Multiset α} (nodup : M.Nodup) :
    Nat.card {x // x ∈ M} = Multiset.card M := by
  rw [← Multiset.toFinset_card_of_nodup nodup, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Multiset.mem_toFinset.symm)

/-- **Classes of names and classes by rules show one answer**: the agreed observer on a word of names
is the answer of the class by rules of its rules, for a program and a query of the first fragment
and a word of names that denote rules. -/
theorem classAnswer_rule (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {ν : List RuleName}
    (valid : ∀ n ∈ ν, ∃ r, ruleNamed N P n = some r) :
    classAnswer N P q ν = ruleClassAnswer N P q (ν.filterMap (ruleNamed N P)) := by
  obtain ⟨rules, available⟩ := rules_of_names N P ν valid
  rw [classAnswer_held N q plainP plainQ unopened ν, rules]
  ext g
  constructor
  · rintro ⟨s, a, held, shown⟩
    exact ⟨s, a, ruleFrom_of_heldFrom N q held, shown⟩
  · rintro ⟨s, a, chain, shown⟩
    exact ⟨s, a, heldFrom_of_ruleFrom N q chain rfl available, shown⟩

/-- **The origin fibres inside the delivered multiset.** In a multiset of words of names counted by
the complete runs of the held-rule step (as in `bag_of_held_classes`), the words whose rules form the
word `ρ` number the product of the origin counts of `ρ`'s rules when `ρ` is a complete class by rules,
and none otherwise: they are the words of the origins over `ρ`, each kept with its own names. -/
theorem origin_fibre_card (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {M : Multiset (List RuleName)}
    (count : ∀ ν, M.count ν = if CompleteHeldRun N P q (ν.map (origin N)) then 1 else 0) (ρ : List (CRule S)) :
    Multiset.card (M.filter fun ν => ν.filterMap (ruleNamed N P) = ρ) =
      if CompleteRuleClass N P q ρ then originWays N P ρ else 0 := by
  have nodupM : M.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro ν
    rw [count ν]
    split <;> omega
  have memM : ∀ ν, ν ∈ M ↔ CompleteClass N P q ν := by
    intro ν
    rw [← Multiset.count_pos, count ν, ← completeHeldRun_map_iff N q plainP plainQ unopened ν]
    split
    · exact ⟨fun _ => by assumption, fun _ => Nat.one_pos⟩
    · exact ⟨fun positive => absurd positive (lt_irrefl 0), fun complete => absurd complete (by assumption)⟩
  have validOf : ∀ ν ∈ M, ∀ n ∈ ν, ∃ r, ruleNamed N P n = some r := by
    intro ν member
    obtain ⟨s, a, named, -⟩ := (memM ν).mp member
    exact chain_valid N named
  have heldOf : ∀ ν ∈ M, CompleteHeldClass N P q (ν.map (origin N)) := fun ν member =>
    (completeHeld_map_iff N q plainP plainQ unopened ν).mpr ((memM ν).mp member)
  by_cases complete : CompleteRuleClass N P q ρ
  · rw [if_pos complete]
    let toOrigins : {ν // ν ∈ M.filter fun ν => ν.filterMap (ruleNamed N P) = ρ} → OriginWords N P ρ :=
      fun ν => ⟨ν.1.map (origin N),
        ((rules_of_names N P ν.1 (validOf ν.1 (Multiset.mem_of_mem_filter ν.2))).1.symm.trans
          (Multiset.mem_filter.mp ν.2).2),
        (rules_of_names N P ν.1 (validOf ν.1 (Multiset.mem_of_mem_filter ν.2))).2⟩
    have bijective : Function.Bijective toOrigins := by
      constructor
      · intro ν ν' same
        exact Subtype.ext (List.map_injective_iff.mpr (origin_injective N) (congrArg Subtype.val same))
      · rintro ⟨w, codes, available⟩
        have completeW : CompleteHeldClass N P q w :=
          (completeHeld_iff_rule N q w).mpr ⟨codes ▸ complete, available⟩
        obtain ⟨ν, rfl⟩ := completeHeld_named N q plainP plainQ unopened completeW
        have member : ν ∈ M := (memM ν).mpr ((completeHeld_map_iff N q plainP plainQ unopened ν).mp completeW)
        have rules : ν.filterMap (ruleNamed N P) = ρ :=
          (rules_of_names N P ν (validOf ν member)).1.trans codes
        exact ⟨⟨ν, Multiset.mem_filter.mpr ⟨member, rules⟩⟩, rfl⟩
    have nodupF : (M.filter fun ν => ν.filterMap (ruleNamed N P) = ρ).Nodup := Multiset.Nodup.filter _ nodupM
    rw [← card_of_nodup nodupF, Nat.card_congr (Equiv.ofBijective toOrigins bijective)]
    exact originWords_card N P ρ
  · rw [if_neg complete, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro ν member same
    have rules := (rules_of_names N P ν (validOf ν member)).1
    exact complete (same ▸ rules ▸ ((completeHeld_iff_rule N q _).mp (heldOf ν member)).1)

/-- **The bag of answers counted by origin fibres, on the agreed observer.** For a program and a
query of the first fragment, and every source run that ends, the multiset `M` of words of names of
`bag_of_held_classes` (each counted once when its origins are the word of a complete run of the
held-rule step) splits by words of rules into origin fibres: over a complete class by rules `ρ` lie
exactly the product of the origin counts of `ρ`'s rules many words of names, all with one answer
(`Hosting.Alternatives.answer_of_rule_word`), and the bag of answers is the multiset of answer sets
`classAnswer` of the finished members. No hypothesis on the schemas. -/
theorem bag_by_origin_counts (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ M : Multiset (List RuleName),
      (∀ ν, M.count ν = if CompleteHeldRun N P q (ν.map (origin N)) then 1 else 0) ∧
        (∀ ρ, Multiset.card (M.filter fun ν => ν.filterMap (ruleNamed N P) = ρ) =
          if CompleteRuleClass N P q ρ then originWays N P ρ else 0) ∧
        (∀ ν ∈ M, ∀ ν' ∈ M, ν.filterMap (ruleNamed N P) = ν'.filterMap (ruleNamed N P) →
          classAnswer N P q ν = classAnswer N P q ν') ∧
        C.answers (D := D) =
          (M.filter fun ν => FinishedHeldClass N P q (ν.map (origin N))).map (classAnswer N P q) := by
  obtain ⟨M, count, -, answers⟩ := bag_of_held_classes N spaces q plainP plainQ unopened runs quiet
  refine ⟨M, count, origin_fibre_card N q plainP plainQ unopened count, fun ν member ν' member' same => ?_,
    answers⟩
  have reachedOf : ∀ μ ∈ M, ∃ s a, NamedFrom N P q μ s a := by
    intro μ inside
    have positive := Multiset.count_pos.mpr inside
    rw [count μ] at positive
    by_cases completeRun : CompleteHeldRun N P q (μ.map (origin N))
    · obtain ⟨s, a, named, -⟩ := (completeHeldRun_map_iff N q plainP plainQ unopened μ).mp completeRun
      exact ⟨s, a, named⟩
    · rw [if_neg completeRun] at positive
      exact absurd positive (lt_irrefl 0)
  obtain ⟨s₀, a₀, h₀⟩ := reachedOf ν member
  obtain ⟨s₀', a₀', h₀'⟩ := reachedOf ν' member'
  ext g
  constructor
  · rintro ⟨s, a, h, shown⟩
    refine ⟨s₀', a₀', h₀', ?_⟩
    rw [← (answer_of_rule_word N q same h h₀').1]
    exact shown
  · rintro ⟨s, a, h, shown⟩
    refine ⟨s₀, a₀, h₀, ?_⟩
    rw [← (answer_of_rule_word N q same.symm h h₀).1]
    exact shown

/-- **The coarser reading by words of rules.** Forgetting the names of the origin fibres of
`bag_by_origin_counts` leaves a multiset `E` of words of rules in which each complete class by rules
is counted as many times as the product of its rules' origin counts, read by the answer of the class
by rules (`Hosting.Alternatives.ruleClassAnswer`, equal to `classAnswer` on every word of names over
it, `classAnswer_rule`). This form forgets which origins a class used; it is kept to compare with
`Hosting.Alternatives.bag_of_rule_classes`. -/
theorem bag_by_rule_counts (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ E : Multiset (List (CRule S)),
      (∀ ρ, E.count ρ = if CompleteRuleClass N P q ρ then originWays N P ρ else 0) ∧
        C.answers (D := D) = (E.filter (FinishedRuleClass N P q)).map (ruleClassAnswer N P q) := by
  obtain ⟨M, count, fibres, -, answers⟩ := bag_by_origin_counts N q spaces plainP plainQ unopened runs quiet
  have validOf : ∀ ν ∈ M, ∀ n ∈ ν, ∃ r, ruleNamed N P n = some r := by
    intro ν member
    have positive := Multiset.count_pos.mpr member
    rw [count ν] at positive
    by_cases completeRun : CompleteHeldRun N P q (ν.map (origin N))
    · obtain ⟨s, a, named, -⟩ := (completeHeldRun_map_iff N q plainP plainQ unopened ν).mp completeRun
      exact chain_valid N named
    · rw [if_neg completeRun] at positive
      exact absurd positive (lt_irrefl 0)
  refine ⟨M.map fun ν => ν.filterMap (ruleNamed N P), fun ρ => ?_, ?_⟩
  · rw [Multiset.count_map, ← fibres ρ]
    congr 1
    exact Multiset.filter_congr fun ν _ => eq_comm
  · rw [answers, Multiset.filter_map, Multiset.map_map]
    have sameFilter : M.filter (FinishedRuleClass N P q ∘ fun ν => ν.filterMap (ruleNamed N P)) =
        M.filter fun ν => FinishedHeldClass N P q (ν.map (origin N)) := by
      refine Multiset.filter_congr fun ν member => ?_
      obtain ⟨rules, available⟩ := rules_of_names N P ν (validOf ν member)
      show FinishedRuleClass N P q (ν.filterMap (ruleNamed N P)) ↔ _
      rw [rules]
      exact (finishedHeld_iff_rule N q available).symm
    rw [sameFilter]
    apply Multiset.map_congr rfl
    intro ν member
    exact classAnswer_rule N q plainP plainQ unopened (validOf ν (Multiset.mem_of_mem_filter member))

/-- **With pairwise distinct schemas every count is one**, and `bag_by_rule_counts` gives back
`Hosting.Alternatives.bag_of_rule_classes`: each complete class by rules counted once. -/
theorem bag_of_rule_classes_of_nodup (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (distinct : (P.equations.map (schema N)).Nodup) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ E : Multiset (List (CRule S)),
      (∀ ρ, E.count ρ = if CompleteRuleClass N P q ρ then 1 else 0) ∧
        C.answers (D := D) = (E.filter (FinishedRuleClass N P q)).map (ruleClassAnswer N P q) := by
  obtain ⟨E, count, answers⟩ := bag_by_rule_counts N q spaces plainP plainQ unopened runs quiet
  refine ⟨E, fun ρ => ?_, answers⟩
  rw [count ρ]
  by_cases complete : CompleteRuleClass N P q ρ
  · obtain ⟨_, _, chain, _⟩ := id complete
    rw [if_pos complete, if_pos complete, originWays_of_nodup N P distinct ρ (chain_rules_mem chain)]
  · rw [if_neg complete, if_neg complete]

end OverRules

/-! ## The run fibres of the held-rule step -/

section RunFibres

open Interface.Bridges.LiveRules.Origins (Uses baseEvents ways HeldRuns projectRun run_fibre_card)

variable (P : SourceLanguage.Program κ Γ star Ty)

/-- **The origins counted above a firing of the set presentation are the origins of its rule.** -/
def usesEquiv (state : HostState S)
    (firing : (baseEvents (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
      (P := controlRules N) (Q := equationRules N P)).Choice state) :
    Uses (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S) (ids := heldIds P)
        (code := heldRule N P) (fun _ => ()) state firing ≃
      OriginsOf N P firing.val.rule :=
  Equiv.subtypeEquivRight fun u => and_congr (available_iff N P state u) (by rw [codeOf_eq N P state u])

/-- **The ways of choosing origins along an execution of the set presentation** are the product of
the origin counts of its rules. -/
theorem ways_eq : ∀ {count : ℕ} {state : HostState S}
    (run : (baseEvents (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
      (P := controlRules N) (Q := equationRules N P)).Execution count state),
    ways (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S) (ids := heldIds P)
        (code := heldRule N P) (fun _ => ()) run =
      originWays N P (((baseEvents (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
        (P := controlRules N) (Q := equationRules N P)).word run).map Prod.fst)
  | 0, _, _ => rfl
  | count + 1, state, ⟨firing, rest⟩ => by
      have here : ways (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S) (ids := heldIds P)
          (code := heldRule N P) (fun _ => ()) (P := controlRules N) (Q := equationRules N P)
            (count := count + 1) (state := state) ⟨firing, rest⟩ =
          Nat.card (Uses (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
            (ids := heldIds P) (code := heldRule N P) (fun _ => ()) state firing) *
            ways (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S) (ids := heldIds P)
              (code := heldRule N P) (fun _ => ()) rest := rfl
      rw [here, Nat.card_congr (usesEquiv N P state firing), ways_eq rest]
      show originCount N P firing.val.rule * originWays N P _ = originWays N P (firing.val.rule :: _)
      unfold originWays
      rw [List.map_cons, List.prod_cons]

/-- **The held-rule runs over one run of the set presentation are counted by the origin counts of
its rules.** The run is fixed with its openings and row identities; the held-rule runs over it are
the run fibre of `Interface.Bridges.LiveRules.Origins.run_fibre_card`. -/
theorem held_run_fibre_card (state : HostState S) (count : ℕ)
    (exec : (baseEvents (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
      (P := controlRules N) (Q := equationRules N P)).Execution count state) :
    Nat.card {run : HeldRuns (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
        (P := controlRules N) (ids := heldIds P) (code := heldRule N P) (fun _ => ()) state count //
        projectRun (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S) (fun _ => ())
          (offers N P) state count run =
          (RuleSyntax.step (Interface.Frames.contextual S) ℕ (RuleSyntax.Contextual.declarations S)
            (controlRules N ∪ equationRules N P)).toStep.countedExecutionRunEquiv
              (fun {_} firing => (firing.rule, firing.selection)) state count exec} =
      originWays N P (((baseEvents (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
        (P := controlRules N) (Q := equationRules N P)).word exec).map Prod.fst) := by
  rw [run_fibre_card, Equiv.symm_apply_apply, ways_eq]

end RunFibres

#print axioms originCount_eq
#print axioms schema_not_control
#print axioms originCount_control
#print axioms originCount_schema
#print axioms originCount_of_nodup
#print axioms originWords_card
#print axioms originWays_of_nodup
#print axioms completeHeld_iff_rule
#print axioms finishedHeld_iff_rule
#print axioms origin_code
#print axioms rules_of_names
#print axioms classAnswer_rule
#print axioms origin_fibre_card
#print axioms bag_by_origin_counts
#print axioms bag_by_rule_counts
#print axioms bag_of_rule_classes_of_nodup
#print axioms ways_eq
#print axioms held_run_fibre_card

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Counted
