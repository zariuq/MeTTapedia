import Mettapedia.GSLT.LanguageDef.DecidableRelations.Membership

/-!
# Frame monotonicity: non-membership needs a premise over the rest

A **local rule** rewrites a top-level bag with no premises, `{l₁, …, lₙ, ...rest} ~> {r₁, …, rₘ, ...rest}`, with
first-order patterns that do not mention `rest` (`LocalRule`). It reads and writes only what it matches, as the local
actions of separation logic do. From the bag with extra elements it steps to its result with the same extra elements
(`frame_step`), so a language of local rules is frame monotone (`frame_monotone`).

A rule guarded by non-membership is not. `{p, ...rest} ~> {p, p, ...rest}` if `p` is not a member of `rest` copies an
element that occurs once (`Copying.copyRule`):
- it steps from `{a}` to `{a, a}` (`Copying.copy_step`);
- nothing steps from `{a, a}`, so the frame `{a}` loses the step (`Copying.not_frame_monotone`).

So no language of local rules has its steps (`Copying.nonMembership_needs_premise`). Non-membership is not definable by
rules that leave the rest of the bag alone: it needs a premise over the rest, such as `forAll` with a complemented
disequality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-! ## Bindings with an extended rest -/

/-- A collection value with extra elements appended. -/
def appendFrame (frame : List Pattern) : Pattern → Pattern
  | .collection kind elements none => .collection kind (elements ++ frame) none
  | value => value

/-- The bindings with the rest variable's collection extended by the frame. -/
def extendRest (rest : String) (frame : List Pattern) (bindings : Bindings) : Bindings :=
  bindings.map fun entry => if entry.1 = rest then (entry.1, appendFrame frame entry.2) else entry

/-- Extending the rest entry by entry. -/
theorem extendRest_cons (rest : String) (frame : List Pattern) (entry : String × Pattern) (bindings : Bindings) :
    extendRest rest frame (entry :: bindings) =
      (if entry.1 = rest then (entry.1, appendFrame frame entry.2) else entry) :: extendRest rest frame bindings :=
  rfl

/-- Bindings that do not name the rest are unchanged. -/
theorem extendRest_of_avoids {rest : String} {frame : List Pattern} :
    ∀ {bindings : Bindings}, (∀ entry ∈ bindings, entry.1 ≠ rest) → extendRest rest frame bindings = bindings
  | [], _ => rfl
  | entry :: bindings, avoids => by
      simp only [extendRest, List.map_cons, avoids entry (List.mem_cons_self ..), if_false, List.cons.injEq, true_and]
      exact extendRest_of_avoids fun other member => avoids other (List.mem_cons_of_mem _ member)

/-- Extending the rest does not change what other names find. -/
theorem find?_extendRest_of_ne {rest name : String} {frame : List Pattern} (different : name ≠ rest)
    (bindings : Bindings) :
    (extendRest rest frame bindings).find? (·.1 == name) = bindings.find? (·.1 == name) := by
  unfold extendRest
  rw [List.find?_map]
  have sameTest : ((fun entry : String × Pattern => entry.1 == name) ∘
      fun entry => if entry.1 = rest then (entry.1, appendFrame frame entry.2) else entry) =
      fun entry => entry.1 == name := by
    funext entry
    by_cases isRest : entry.1 = rest <;> simp [isRest]
  rw [sameTest]
  cases found : bindings.find? (·.1 == name) with
  | none => rfl
  | some entry =>
      have named : entry.1 = name := by simpa using List.find?_some found
      have notRest : ¬ entry.1 = rest := fun isRest => different (named.symm.trans isRest)
      simp [notRest]

/-- **One step of a merge**: a new name is added in front, a known name must agree. -/
theorem mergeBindings_cons (accumulated : Bindings) (next : String × Pattern) (added : Bindings) :
    mergeBindings accumulated (next :: added) =
      match accumulated.find? (·.1 == next.1) with
      | none => mergeBindings (next :: accumulated) added
      | some (_, existing) => if existing == next.2 then mergeBindings accumulated added else none := by
  unfold mergeBindings
  rw [List.foldlM_cons]
  cases found : accumulated.find? (·.1 == next.1) with
  | none => simp only [found]; rfl
  | some entry =>
      obtain ⟨name, existing⟩ := entry
      simp only [found]
      by_cases agrees : existing == next.2
      · simp only [agrees, if_true]; rfl
      · simp only [agrees, Bool.false_eq_true, if_false]; rfl

/-- Merging a name the accumulated bindings lack adds it in front. -/
theorem mergeBindings_cons_of_missing {accumulated : Bindings} {next : String × Pattern} (added : Bindings)
    (missing : accumulated.find? (·.1 == next.1) = none) :
    mergeBindings accumulated (next :: added) = mergeBindings (next :: accumulated) added := by
  rw [mergeBindings_cons, missing]

/-- Merging a name the accumulated bindings have checks that the two values agree. -/
theorem mergeBindings_cons_of_found {accumulated : Bindings} {next : String × Pattern} (added : Bindings)
    {name : String} {existing : Pattern} (found : accumulated.find? (·.1 == next.1) = some (name, existing)) :
    mergeBindings accumulated (next :: added) = if existing == next.2 then mergeBindings accumulated added else none := by
  rw [mergeBindings_cons, found]

/-- A name absent from a list is not found in it. -/
theorem find?_eq_none_of_not_mem {name : String} {bindings : Bindings} (absent : name ∉ bindings.map Prod.fst) :
    bindings.find? (·.1 == name) = none := by
  rw [List.find?_eq_none]
  intro entry member same
  simp only [beq_iff_eq] at same
  exact absent (same ▸ List.mem_map_of_mem member)

/-- The names of merged bindings come from the two merged lists. -/
theorem mergeBindings_names : ∀ {accumulated added result : Bindings},
    mergeBindings accumulated added = some result →
      ∀ entry ∈ result, entry.1 ∈ accumulated.map Prod.fst ∨ entry.1 ∈ added.map Prod.fst
  | accumulated, [], result, merged => by
      simp only [mergeBindings_nil_right, Option.some.injEq] at merged
      intro entry member
      exact .inl (List.mem_map_of_mem (merged ▸ member))
  | accumulated, next :: added, result, merged => by
      intro entry member
      cases found : accumulated.find? (·.1 == next.1) with
      | none =>
          rw [mergeBindings_cons_of_missing added found] at merged
          rcases mergeBindings_names merged entry member with inFront | inAdded
          · rw [List.map_cons, List.mem_cons] at inFront
            rcases inFront with isNext | earlier
            · exact .inr (by rw [List.map_cons, isNext]; exact List.mem_cons_self ..)
            · exact .inl earlier
          · exact .inr (List.mem_cons_of_mem _ inAdded)
      | some known =>
          obtain ⟨name, existing⟩ := known
          rw [mergeBindings_cons_of_found added found] at merged
          split at merged
          · rcases mergeBindings_names merged entry member with early | inAdded
            · exact .inl early
            · exact .inr (List.mem_cons_of_mem _ inAdded)
          · cases merged

/-- **Merging keeps names distinct.** -/
theorem mergeBindings_nodup : ∀ {accumulated added result : Bindings}, (accumulated.map Prod.fst).Nodup →
    mergeBindings accumulated added = some result → (result.map Prod.fst).Nodup
  | accumulated, [], result, distinct, merged => by
      simp only [mergeBindings_nil_right, Option.some.injEq] at merged
      exact merged ▸ distinct
  | accumulated, next :: added, result, distinct, merged => by
      rw [mergeBindings_cons] at merged
      split at merged
      · rename_i missing
        refine mergeBindings_nodup ?_ merged
        rw [List.map_cons, List.nodup_cons]
        refine ⟨fun present => ?_, distinct⟩
        obtain ⟨entry, member, same⟩ := List.mem_map.mp present
        have := List.find?_eq_none.mp missing entry member
        simp [same] at this
      · split at merged
        · exact mergeBindings_nodup distinct merged
        · cases merged

/-- Merging extends the found entry of a name the accumulated bindings already have. -/
theorem find?_mergeBindings_of_found {name : String} : ∀ {accumulated added result : Bindings} {entry : String × Pattern},
    accumulated.find? (·.1 == name) = some entry → mergeBindings accumulated added = some result →
      result.find? (·.1 == name) = some entry
  | accumulated, [], result, entry, found, merged => by
      simp only [mergeBindings_nil_right, Option.some.injEq] at merged
      exact merged ▸ found
  | accumulated, next :: added, result, entry, found, merged => by
      rw [mergeBindings_cons] at merged
      split at merged
      · rename_i missing
        have different : ¬ (next.1 == name) = true := by
          intro same
          simp only [beq_iff_eq] at same
          rw [same] at missing
          rw [missing] at found
          cases found
        exact find?_mergeBindings_of_found (by simp [List.find?, different, found]) merged
      · split at merged
        · exact find?_mergeBindings_of_found found merged
        · cases merged

/-- Merging into bindings without a name gives the added list's entry of that name. -/
theorem find?_mergeBindings_of_missing {name : String} : ∀ {accumulated added result : Bindings},
    accumulated.find? (·.1 == name) = none → mergeBindings accumulated added = some result →
      result.find? (·.1 == name) = added.find? (·.1 == name)
  | accumulated, [], result, missing, merged => by
      simp only [mergeBindings_nil_right, Option.some.injEq] at merged
      rw [← merged, missing]
      rfl
  | accumulated, next :: added, result, missing, merged => by
      by_cases named : next.1 = name
      · subst named
        rw [mergeBindings_cons_of_missing added missing] at merged
        rw [find?_mergeBindings_of_found (entry := next) (by simp [List.find?]) merged]
        simp [List.find?]
      · have otherwise : (next.1 == name) = false := by simpa using named
        cases found : accumulated.find? (·.1 == next.1) with
        | none =>
            rw [mergeBindings_cons_of_missing added found] at merged
            rw [find?_mergeBindings_of_missing (by simp [List.find?, otherwise, missing]) merged]
            simp [List.find?, otherwise]
        | some entry =>
            obtain ⟨other, existing⟩ := entry
            rw [mergeBindings_cons_of_found added found] at merged
            split at merged
            · rw [find?_mergeBindings_of_missing missing merged]
              simp [List.find?, otherwise]
            · cases merged

/-- Extending the rest in bindings that merge only other names. -/
theorem mergeBindings_extendRest_of_avoids {rest : String} {frame : List Pattern} :
    ∀ {accumulated added result : Bindings}, (∀ entry ∈ added, entry.1 ≠ rest) →
      mergeBindings accumulated added = some result →
        mergeBindings (extendRest rest frame accumulated) added = some (extendRest rest frame result)
  | accumulated, [], result, _, merged => by
      simp only [mergeBindings_nil_right, Option.some.injEq] at merged ⊢
      exact congrArg _ merged
  | accumulated, next :: added, result, avoids, merged => by
      have notRest := avoids next (List.mem_cons_self ..)
      have tail := fun entry member => avoids entry (List.mem_cons_of_mem _ member)
      rw [mergeBindings_cons] at merged ⊢
      rw [find?_extendRest_of_ne notRest]
      split at merged
      · have extended : extendRest rest frame (next :: accumulated) = next :: extendRest rest frame accumulated := by
          simp [extendRest, notRest]
        rw [← extended]
        exact mergeBindings_extendRest_of_avoids tail merged
      · split at merged
        · rename_i agrees
          simp only [agrees, if_true]
          exact mergeBindings_extendRest_of_avoids tail merged
        · cases merged

/-- **Extending the rest commutes with a merge**: into bindings that do not name the rest, of bindings that name it
at most once. -/
theorem mergeBindings_extendRest {rest : String} {frame : List Pattern} :
    ∀ {accumulated added result : Bindings}, (∀ entry ∈ accumulated, entry.1 ≠ rest) →
      (added.map Prod.fst).Nodup → mergeBindings accumulated added = some result →
        mergeBindings accumulated (extendRest rest frame added) = some (extendRest rest frame result)
  | accumulated, [], result, avoids, _, merged => by
      simp only [mergeBindings_nil_right, Option.some.injEq] at merged
      subst merged
      simp only [extendRest, List.map_nil, mergeBindings_nil_right]
      exact congrArg some (extendRest_of_avoids avoids).symm
  | accumulated, next :: added, result, avoids, distinct, merged => by
      rw [List.map_cons, List.nodup_cons] at distinct
      by_cases isRest : next.1 = rest
      · have laterAvoid : ∀ entry ∈ added, entry.1 ≠ rest := by
          intro entry member same
          exact distinct.1 (isRest ▸ same ▸ List.mem_map_of_mem member)
        have missing : accumulated.find? (·.1 == next.1) = none :=
          find?_eq_none_of_not_mem fun present => by
            obtain ⟨entry, member, same⟩ := List.mem_map.mp present
            exact avoids entry member (same.trans isRest)
        rw [mergeBindings_cons_of_missing added missing] at merged
        rw [extendRest_cons, if_pos isRest, extendRest_of_avoids laterAvoid,
          mergeBindings_cons_of_missing (next := (next.1, appendFrame frame next.2)) added missing]
        have extendedAccumulated : extendRest rest frame (next :: accumulated) =
            (next.1, appendFrame frame next.2) :: accumulated := by
          rw [extendRest_cons, if_pos isRest, extendRest_of_avoids avoids]
        rw [← extendedAccumulated]
        exact mergeBindings_extendRest_of_avoids laterAvoid merged
      · rw [extendRest_cons, if_neg isRest]
        have nextAvoids : ∀ entry ∈ next :: accumulated, entry.1 ≠ rest := by
          intro entry member
          rcases List.mem_cons.mp member with same | earlier
          · exact same ▸ isRest
          · exact avoids entry earlier
        cases found : accumulated.find? (·.1 == next.1) with
        | none =>
            rw [mergeBindings_cons_of_missing added found] at merged
            rw [mergeBindings_cons_of_missing _ found]
            exact mergeBindings_extendRest nextAvoids distinct.2 merged
        | some entry =>
            obtain ⟨name, existing⟩ := entry
            rw [mergeBindings_cons_of_found added found] at merged
            rw [mergeBindings_cons_of_found _ found]
            split at merged
            · rename_i agrees
              rw [if_pos agrees]
              exact mergeBindings_extendRest avoids distinct.2 merged
            · cases merged

/-! ## First-order patterns that avoid the rest -/

/-- **A first-order pattern that does not mention `name`**: applications of such patterns, and metavariables other
than `name`. -/
inductive Avoids (name : String) : Pattern → Prop
  | fvar {other : String} : other ≠ name → Avoids name (.fvar other)
  | apply {constructor : String} {arguments : List Pattern} :
      (∀ argument ∈ arguments, Avoids name argument) → Avoids name (.apply constructor arguments)

/-- What a match binds: distinct names, none of them the rest. -/
def BindsAvoiding (rest : String) (bindings : Bindings) : Prop :=
  (∀ entry ∈ bindings, entry.1 ≠ rest) ∧ (bindings.map Prod.fst).Nodup

/-- Merging two such matches gives one. -/
theorem BindsAvoiding.merge {rest : String} {first second merged : Bindings} (firstAvoids : BindsAvoiding rest first)
    (secondAvoids : BindsAvoiding rest second) (merging : mergeBindings first second = some merged) :
    BindsAvoiding rest merged := by
  refine ⟨fun entry member isRest => ?_, mergeBindings_nodup firstAvoids.2 merging⟩
  rcases mergeBindings_names merging entry member with inFirst | inSecond
  · obtain ⟨other, otherMember, same⟩ := List.mem_map.mp inFirst
    exact firstAvoids.1 other otherMember (same.trans isRest)
  · obtain ⟨other, otherMember, same⟩ := List.mem_map.mp inSecond
    exact secondAvoids.1 other otherMember (same.trans isRest)

/-- Matching argument lists whose arguments bind avoiding names binds avoiding names. -/
theorem bindsAvoiding_of_matchArgsRel {rest : String} :
    ∀ {patterns terms : List Pattern} {bindings : Bindings},
      (∀ pattern ∈ patterns, ∀ {term : Pattern} {bindings : Bindings}, MatchRel pattern term bindings →
        BindsAvoiding rest bindings) →
      MatchArgsRel patterns terms bindings → BindsAvoiding rest bindings
  | [], _, _, _, related => by
      cases related
      exact ⟨by simp, by simp⟩
  | pattern :: patterns, _, _, inner, related => by
      cases related with
      | cons headRelated tailRelated merged =>
          exact (inner pattern (List.mem_cons_self ..) headRelated).merge
            (bindsAvoiding_of_matchArgsRel (fun other member => inner other (List.mem_cons_of_mem _ member))
              tailRelated) merged

/-- Matching a pattern that avoids the rest binds distinct names, none of them the rest. -/
theorem bindsAvoiding_of_matchRel {rest : String} {pattern : Pattern} (avoids : Avoids rest pattern) :
    ∀ {term : Pattern} {bindings : Bindings}, MatchRel pattern term bindings → BindsAvoiding rest bindings := by
  induction avoids with
  | fvar different =>
      intro term bindings related
      cases related
      exact ⟨by simpa using different, by simp⟩
  | apply _ inner =>
      intro term bindings related
      cases related with
      | apply argumentsRelated _ => exact bindsAvoiding_of_matchArgsRel inner argumentsRelated

/-- A bag match of a leading pattern at a position of the stored elements, with a frame after them. -/
theorem matchBagRel_cons_append {pattern : Pattern} {taken stored frame : List Pattern} {rest : Option String}
    {kind : CollType} {head tail bindings : Bindings} (index : Nat) (inside : index < stored.length)
    (headRelated : MatchRel pattern stored[index] head)
    (tailRelated : MatchBagRel taken rest kind (stored.eraseIdx index ++ frame) tail)
    (merged : mergeBindings head tail = some bindings) :
    MatchBagRel (pattern :: taken) rest kind (stored ++ frame) bindings := by
  have position : index < (stored ++ frame).length := by
    rw [List.length_append]
    omega
  refine .cons index position ?_ ?_ merged
  · rw [List.getElem_append_left inside]
    exact headRelated
  · rw [List.eraseIdx_append_of_lt_length inside]
    exact tailRelated

/-- **Bag matching survives a frame**: matching avoiding patterns with a rest against a bag with extra elements binds
the rest to its former value with the extra elements. The bindings name each variable once, and the rest is bound to
a collection of the bag's elements. -/
theorem matchBagRel_frame {rest : String} {kind : CollType} {frame : List Pattern} :
    ∀ {taken stored : List Pattern} {bindings : Bindings}, MatchBagRel taken (some rest) kind stored bindings →
      (∀ pattern ∈ taken, Avoids rest pattern) →
      MatchBagRel taken (some rest) kind (stored ++ frame) (extendRest rest frame bindings) ∧
        (bindings.map Prod.fst).Nodup ∧
        ∃ remaining, (∀ x ∈ remaining, x ∈ stored) ∧
          bindings.find? (·.1 == rest) = some (rest, .collection kind remaining none)
  | [], stored, _, related, _ => by
      cases related
      refine ⟨?_, by simp, stored, fun _ member => member, by simp [List.find?]⟩
      have extended : extendRest rest frame [(rest, .collection kind stored none)] =
          [(rest, .collection kind (stored ++ frame) none)] := by
        simp [extendRest, appendFrame]
      rw [extended]
      exact .nilRest
  | pattern :: taken, stored, _, related, avoids => by
      cases related with
      | cons index inside headRelated restRelated merged =>
          have headAvoids := bindsAvoiding_of_matchRel (avoids _ (List.mem_cons_self ..)) headRelated
          obtain ⟨restFrame, restDistinct, remaining, remainingIn, restFound⟩ :=
            matchBagRel_frame restRelated (fun other member => avoids other (List.mem_cons_of_mem _ member))
          refine ⟨matchBagRel_cons_append index inside headRelated restFrame
              (mergeBindings_extendRest headAvoids.1 restDistinct merged),
            mergeBindings_nodup headAvoids.2 merged, remaining,
            fun x member => List.mem_of_mem_eraseIdx (remainingIn x member), ?_⟩
          rw [find?_mergeBindings_of_missing (find?_eq_none_of_not_mem fun present => by
            obtain ⟨entry, member, same⟩ := List.mem_map.mp present
            exact headAvoids.1 entry member same) merged]
          exact restFound

/-- Scoped application of a pattern avoiding the rest ignores the rest's value. -/
theorem applyBindingsScoped_extendRest {rest : String} {frame : List Pattern} {lhs : Pattern} {bindings : Bindings}
    {depth : Nat} {pattern : Pattern} (avoids : Avoids rest pattern) :
    applyBindingsScoped lhs (extendRest rest frame bindings) depth pattern =
      applyBindingsScoped lhs bindings depth pattern := by
  induction avoids with
  | fvar different =>
      simp only [applyBindingsScoped, find?_extendRest_of_ne different]
  | apply _ inner =>
      rw [applyBindingsScoped_apply, applyBindingsScoped_apply]
      congr 1
      exact List.map_congr_left inner

/-- Finding the rest in bindings with the rest extended. -/
theorem find?_extendRest_rest {rest : String} {frame : List Pattern} {bindings : Bindings} {kind : CollType}
    {remaining : List Pattern}
    (found : bindings.find? (·.1 == rest) = some (rest, .collection kind remaining none)) :
    (extendRest rest frame bindings).find? (·.1 == rest) =
      some (rest, .collection kind (remaining ++ frame) none) := by
  unfold extendRest
  rw [List.find?_map]
  have sameTest : ((fun entry : String × Pattern => entry.1 == rest) ∘
      fun entry => if entry.1 = rest then (entry.1, appendFrame frame entry.2) else entry) =
      fun entry => entry.1 == rest := by
    funext entry
    by_cases isRest : entry.1 = rest <;> simp [isRest]
  rw [sameTest, found]
  simp [appendFrame]

/-- The scoped applier on a collection: its elements, then the spliced rest. -/
theorem applyBindingsScoped_collection (lhs : Pattern) (bindings : Bindings) (depth : Nat) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    applyBindingsScoped lhs bindings depth (.collection kind elements rest) =
      .collection kind (elements.map (applyBindingsScoped lhs bindings depth) ++
        (restSplice lhs bindings depth kind rest).1) (restSplice lhs bindings depth kind rest).2 := by
  simp only [applyBindingsScoped, applyBindingsScopedList_eq_map]

/-- **A rest bound to first-order elements is spliced as they are.** -/
theorem restSplice_of_found {rest : String} {lhs : Pattern} {bindings : Bindings} {depth : Nat} {kind : CollType}
    {remaining : List Pattern}
    (found : bindings.find? (·.1 == rest) = some (rest, .collection kind remaining none))
    (remainingFirst : ∀ x ∈ remaining, FirstOrder x) :
    restSplice lhs bindings depth kind (some rest) = (remaining, none) := by
  have lifted : ∀ shift : Nat, remaining.map (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 shift) = remaining := by
    intro shift
    conv => rhs; rw [← List.map_id remaining]
    exact List.map_congr_left fun x member => liftBVars_firstOrder 0 shift (remainingFirst x member)
  simp only [restSplice, found, beq_self_eq_true, ↓reduceIte]
  split
  · rw [lifted]
  · rfl

/-! ## Local rules keep their steps under a frame -/

/-- **A local rule**: no premises, a top-level bag of first-order patterns with a rest on the left, and the same rest
after first-order patterns on the right, none of them mentioning the rest. It reads and writes only what it matches. -/
structure LocalRule (rule : RewriteRule) (kind : CollType) (rest : String) : Prop where
  notVector : kind ≠ .vec
  noPremises : rule.premises = []
  left : ∃ taken, rule.left = .collection kind taken (some rest) ∧ ∀ pattern ∈ taken, Avoids rest pattern
  right : ∃ made, rule.right = .collection kind made (some rest) ∧ ∀ pattern ∈ made, Avoids rest pattern

/-- A collection's elements with extra elements appended, as a term. -/
theorem appendFrame_collection (kind : CollType) (elements frame : List Pattern) :
    appendFrame frame (.collection kind elements none) = .collection kind (elements ++ frame) none := rfl

/-- **A local rule's step carries a frame along**: from the bag with extra first-order elements it steps to its result
with the same extra elements. -/
theorem frame_step {relEnv : RelationEnv} {language : LanguageDef} {rule : RewriteRule} {kind : CollType}
    {rest : String} (local_ : LocalRule rule kind rest) (member : rule ∈ language.rewrites)
    {stored frame : List Pattern} (storedFirst : ∀ x ∈ stored, FirstOrder x) (frameFirst : ∀ x ∈ frame, FirstOrder x)
    {initial : Bindings} (matched : initial ∈ matchPattern rule.left (.collection kind stored none)) :
    ∃ witness, StepValid relEnv language (.collection kind (stored ++ frame) none) witness
      (appendFrame frame (applyBindingsScoped (captureSites rule) initial 0 rule.right)) := by
  obtain ⟨taken, leftShape, takenAvoid⟩ := local_.left
  obtain ⟨made, rightShape, madeAvoid⟩ := local_.right
  rw [leftShape] at matched
  have related := matchPattern_sound matched
  cases related with
  | collection _ bagRelated =>
    obtain ⟨frameRelated, _, remaining, remainingIn, found⟩ := matchBagRel_frame (frame := frame) bagRelated takenAvoid
    have frameMatched : extendRest rest frame initial ∈
        matchPattern rule.left (.collection kind (stored ++ frame) none) := by
      rw [leftShape]
      exact matchRel_complete (.collection local_.notVector frameRelated)
    have premises : PremisesValid relEnv language (captureSites rule) (extendRest rest frame initial) rule.premises []
        (extendRest rest frame initial) := by
      rw [local_.noPremises]
      exact .nil _
    obtain ⟨index, rulePosition⟩ := List.mem_iff_getElem?.mp member
    have step := StepValid.rule (relEnv := relEnv) (language := language) rulePosition
      (by rw [matchPatternForRule_eq_syntactic]; exact frameMatched) premises
    have remainingFirst : ∀ x ∈ remaining, FirstOrder x := fun x inRemaining => storedFirst x (remainingIn x inRemaining)
    have allFirst : ∀ x ∈ remaining ++ frame, FirstOrder x := by
      intro x inAll
      rcases List.mem_append.mp inAll with early | late
      · exact remainingFirst x early
      · exact frameFirst x late
    have target : applyBindingsScoped (captureSites rule) (extendRest rest frame initial) 0 rule.right =
        appendFrame frame (applyBindingsScoped (captureSites rule) initial 0 rule.right) := by
      rw [rightShape]
      simp only [applyBindingsScoped, applyBindingsScopedList_eq_map,
        restSplice_of_found (find?_extendRest_rest found) allFirst, restSplice_of_found found remainingFirst,
        appendFrame_collection]
      rw [List.append_assoc]
      congr 2
      exact List.map_congr_left fun pattern inMade => applyBindingsScoped_extendRest (madeAvoid pattern inMade)
    rw [target] at step
    exact ⟨_, step⟩
  | vectorRest _ _ => exact absurd rfl local_.notVector

/-- The data of a step: a rule of the language matched the term, its premises held, and the target is its right side. -/
theorem stepValid_rule_cases {relEnv : RelationEnv} {language : LanguageDef} {term target : Pattern}
    {witness : Witness} (step : StepValid relEnv language term witness target) :
    ∃ rule ∈ language.rewrites, ∃ initial final witnesses, initial ∈ matchPattern rule.left term ∧
      PremisesValid relEnv language (captureSites rule) initial rule.premises witnesses final ∧
      target = applyBindingsScoped (captureSites rule) final 0 rule.right := by
  cases step with
  | rule found matched premises =>
      exact ⟨_, List.mem_of_getElem? found, _, _, _, by rwa [matchPatternForRule_eq_syntactic] at matched,
        premises, rfl⟩

/-- **A language whose rules are local is frame monotone**: each step from a bag of first-order elements is matched by a
step from the bag with extra first-order elements to the result with them. -/
theorem frame_monotone {relEnv : RelationEnv} {language : LanguageDef} {kind : CollType}
    (locals : ∀ rule ∈ language.rewrites, ∃ rest, LocalRule rule kind rest) {stored frame : List Pattern}
    (storedFirst : ∀ x ∈ stored, FirstOrder x) (frameFirst : ∀ x ∈ frame, FirstOrder x) {witness : Witness}
    {target : Pattern} (step : StepValid relEnv language (.collection kind stored none) witness target) :
    ∃ witness', StepValid relEnv language (.collection kind (stored ++ frame) none) witness'
      (appendFrame frame target) := by
  obtain ⟨rule, member, initial, final, witnesses, matched, premises, rfl⟩ := stepValid_rule_cases step
  obtain ⟨rest, local_⟩ := locals rule member
  rw [local_.noPremises] at premises
  cases premises
  exact frame_step local_ member storedFirst frameFirst matched


/-! ## A rule guarded by non-membership is not frame monotone -/

namespace Copying

/-- One constant. -/
def signature : List (String × Nat) := [("A", 0)]

/-- The constant. -/
def a : Pattern := .apply "A" []

theorem a_over : TermOf signature a := .apply (by simp [signature]) (by simp)

theorem a_firstOrder : FirstOrder a := a_over.firstOrder

/-- `{p, ...rest} ~> {p, p, ...rest}` if `p` is not a member of `rest`: copy an element that occurs once. -/
def copyRule : RewriteRule :=
  ⟨"CopyOnce", [], [nonMemberPremise], .collection .hashBag [.fvar "p"] (some "rest"),
    .collection .hashBag [.fvar "p", .fvar "p"] (some "rest"), none⟩

/-- The copying rule, with the equality and disequality of its signature. -/
def language : LanguageDef := ⟨"CopyOnce", [], [], [], disequalityRules signature ++ [copyRule]⟩

theorem private_ : Private language signature := by
  intro rule member notGenerated arguments
  simp only [language, List.mem_append, List.mem_singleton] at member
  rcases member with generated | rfl
  · exact absurd generated notGenerated
  · constructor <;> simp [copyRule, matchPattern]

/-- The copying rule applied to an element and the rest of a bag of first-order elements. -/
theorem copy_result {lhs element : Pattern} {elements : List Pattern} (elementFirst : FirstOrder element)
    (elementsFirst : ∀ x ∈ elements, FirstOrder x) :
    applyBindingsScoped lhs (nonMemberBindings element (.collection .hashBag elements none)) 0 copyRule.right =
      .collection .hashBag (element :: element :: elements) none := by
  have copied : applyBindingsScoped lhs (nonMemberBindings element (.collection .hashBag elements none)) 0
      (.fvar "p") = element :=
    applyBindingsScoped_fvar elementFirst (by simp [applyBindings, List.find?])
  have spliced : restSplice lhs (nonMemberBindings element (.collection .hashBag elements none)) 0 .hashBag
      (some "rest") = (elements, none) :=
    restSplice_of_found (by simp [List.find?]) elementsFirst
  show applyBindingsScoped lhs _ 0 (.collection .hashBag [.fvar "p", .fvar "p"] (some "rest")) = _
  rw [applyBindingsScoped_collection, spliced, List.map_cons, List.map_cons, List.map_nil, copied]
  rfl

/-- **The copying rule steps from `{a}` to `{a, a}`**: the rest is empty, so `a` occurs once. -/
theorem copy_step (relEnv : RelationEnv) :
    ∃ witness, StepValid relEnv language (.collection .hashBag [a] none) witness (.collection .hashBag [a, a] none) := by
  have matched : nonMemberBindings a (.collection .hashBag [] none) ∈
      matchPattern copyRule.left (.collection .hashBag [a] none) := by
    simp [copyRule, matchPattern, matchBag, mergeBindings]
  have premises : PremisesValid relEnv language (captureSites copyRule)
      (nonMemberBindings a (.collection .hashBag [] none)) copyRule.premises [.forAll []]
      (nonMemberBindings a (.collection .hashBag [] none)) :=
    .cons (.forAll (kind := .hashBag) (elements := []) (by simp [Bindings.lookup, List.find?]) .nil) (.nil _)
  obtain ⟨index, position⟩ := List.mem_iff_getElem?.mp (show copyRule ∈ language.rewrites by simp [language])
  have step := StepValid.rule (relEnv := relEnv) (language := language) position
    (by rw [matchPatternForRule_eq_syntactic]; exact matched) premises
  rw [copy_result a_firstOrder (by simp)] at step
  exact ⟨_, step⟩

/-- **Nothing steps from `{a, a}`**: the copying rule binds the rest to `{a}`, where `a` is a member, and the
disequality rules do not match a bag. -/
theorem no_step_from_pair (relEnv : RelationEnv) {witness : Witness} {target : Pattern} :
    ¬ StepValid relEnv language (.collection .hashBag [a, a] none) witness target := by
  intro step
  obtain ⟨rule, member, initial, final, witnesses, matched, premises, -⟩ := stepValid_rule_cases step
  simp only [language, List.mem_append, List.mem_singleton] at member
  rcases member with generated | rfl
  · rcases mem_disequalityRules generated with rfl | ⟨first, _, second, _, _, rfl⟩ | ⟨constructor, _, position, _, rfl⟩
    all_goals simp [equalRule, clashRule, argumentRule, constructorPattern, matchPattern] at matched
  · have bound : initial = nonMemberBindings a (.collection .hashBag [a] none) := by
      simp [copyRule, matchPattern, matchBag, mergeBindings, a] at matched
      exact matched
    subst bound
    cases premises with
    | cons premise rest =>
        cases premise with
        | base isBaseTrue _ => simp [nonMemberPremise, isBase] at isBaseTrue
        | step endpoints _ _ _ => simp [nonMemberPremise, stepEndpoints] at endpoints
        | forAll found valid =>
            simp only [Bindings.lookup, List.find?, beq_self_eq_true, Option.map_some,
              Option.some.injEq, Pattern.collection.injEq] at found
            obtain ⟨rfl, rfl, -⟩ := found
            have unequal := unequal_of_forAllValid a_firstOrder valid (by simp [a_firstOrder]) a (by simp)
            exact ne_of_derives_unequal private_ a_firstOrder a_firstOrder unequal rfl

/-- **The copying rule is not frame monotone**: it steps from `{a}` to `{a, a}`, but with a frame `{a}` there is no
step to `{a, a, a}`. -/
theorem not_frame_monotone (relEnv : RelationEnv) :
    (∃ witness, StepValid relEnv language (.collection .hashBag [a] none) witness (.collection .hashBag [a, a] none)) ∧
      ¬ ∃ witness, StepValid relEnv language (.collection .hashBag ([a] ++ [a]) none) witness
        (appendFrame [a] (.collection .hashBag [a, a] none)) :=
  ⟨copy_step relEnv, fun ⟨_, step⟩ => no_step_from_pair relEnv step⟩

/-- **Non-membership needs a premise over the rest**: no language of local rules has the steps of the copying rule on
bags of first-order terms. -/
theorem nonMembership_needs_premise (relEnv : RelationEnv) :
    ¬ ∃ other : LanguageDef, (∀ rule ∈ other.rewrites, ∃ rest, LocalRule rule .hashBag rest) ∧
      ∀ stored : List Pattern, (∀ x ∈ stored, FirstOrder x) → ∀ target : Pattern,
        ((∃ witness, StepValid relEnv other (.collection .hashBag stored none) witness target) ↔
          (∃ witness, StepValid relEnv language (.collection .hashBag stored none) witness target)) := by
  rintro ⟨other, locals, same⟩
  have single : ∀ x ∈ [a], FirstOrder x := by simp [a_firstOrder]
  obtain ⟨_, step⟩ := (same [a] single _).mpr (copy_step relEnv)
  obtain ⟨_, framed⟩ := frame_monotone locals single single step
  obtain ⟨_, copied⟩ := (same ([a] ++ [a]) (by simp [a_firstOrder]) _).mp ⟨_, framed⟩
  exact no_step_from_pair relEnv copied

end Copying

end Mettapedia.GSLT.LanguageDef.DecidableRelations
