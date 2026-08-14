import Mettapedia.OSLF.MeTTaIL.DerivedContexts
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalInversion
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalRootDichotomy

/-!
# Filler-generic collapse elimination for the reflective canonicalizer

A one-hole context may canonically evaporate: filling it with a pattern and
canonicalizing may return just the canonical filler, possibly under a
residual tower of the declared drop constructor.  Quote/Drop absorption,
parallel unit siblings, singleton parallel wrappers, and nested parallel
flattening all produce such contexts, in arbitrary finite mixtures.

Enumerating those shells syntactically is not stable: each new collapsing
interaction (for example a parallel node holding one survivor plus
canonically-unit siblings) would extend the grammar.  This module proves the
semantic elimination instead:

* if a context evaporates on one *fresh* free variable, it evaporates the
  same way on *every* filler (`canonicalize_fill_eq_iterDrop_of_collapse`);
* in particular, with no residual drop tower, canonicalizing the filled
  context is canonicalizing the filler
  (`canonicalize_fill_eq_of_collapse_fvar`).

The freshness hypothesis is essential: the collapse must be attributable to
the hole, not to an equal-looking variable in the surrounding frame.  The
quote/drop distinctness hypothesis is supplied for validated presentations
by `quoteConstructor_ne_dropConstructor_of_validate`.

LLM primer: the induction is structural on the context with the drop-tower
level generalized; quote absorption raises the level, a drop head lowers it,
parallel wrappers preserve it, and every binder or rigid head refutes the
collapse hypothesis outright because its canonical root survives.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-! ## Residual drop towers -/

/-- Finite tower of the declared drop constructor over a payload. -/
def iterDrop (declaration : ReflectivePresentationDecl) :
    Nat → Pattern → Pattern
  | 0, pattern => pattern
  | level + 1, pattern =>
      .apply declaration.dropConstructor [iterDrop declaration level pattern]

@[simp]
theorem iterDrop_zero (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) : iterDrop declaration 0 pattern = pattern := rfl

theorem freeFvarNames_iterDrop (declaration : ReflectivePresentationDecl) :
    ∀ (level : Nat) (pattern : Pattern),
      (iterDrop declaration level pattern).freeFvarNames =
        pattern.freeFvarNames
  | 0, _ => rfl
  | level + 1, pattern => by
      simp [iterDrop, Pattern.freeFvarNames,
        freeFvarNames_iterDrop declaration level pattern]

/-- A drop tower over a free variable is either the bare variable or a drop
application; no other root constructor can appear. -/
theorem iterDrop_fvar_shape (declaration : ReflectivePresentationDecl)
    (level : Nat) (name : String) :
    iterDrop declaration level (.fvar name) = .fvar name ∨
      ∃ inner, iterDrop declaration level (.fvar name) =
        .apply declaration.dropConstructor [inner] := by
  cases level with
  | zero => exact Or.inl rfl
  | succ level =>
      exact Or.inr ⟨iterDrop declaration level (.fvar name), rfl⟩

/-! ## Frame support of one-hole contexts -/

/-- Free variable names contributed by a one-hole context away from its
hole.  Collection rests are counted, mirroring `Pattern.freeFvarNames`. -/
def contextFrameFreeFvarNames : OneHoleContext → List String
  | .hole => []
  | .apply _ before inner after =>
      before.flatMap Pattern.freeFvarNames ++
        contextFrameFreeFvarNames inner ++
        after.flatMap Pattern.freeFvarNames
  | .lambda _ inner => contextFrameFreeFvarNames inner
  | .multiLambda _ _ inner => contextFrameFreeFvarNames inner
  | .substBody inner replacement =>
      contextFrameFreeFvarNames inner ++ replacement.freeFvarNames
  | .substReplacement body inner =>
      body.freeFvarNames ++ contextFrameFreeFvarNames inner
  | .collection _ before inner after rest =>
      before.flatMap Pattern.freeFvarNames ++
        contextFrameFreeFvarNames inner ++
        after.flatMap Pattern.freeFvarNames ++ rest.toList

/-! ## Inversion helpers -/

/-- The quote arm of `finishNormalizeReflectiveApply` either absorbs a
sole drop-application argument or keeps the quote application intact. -/
theorem finishNormalizeReflectiveApply_quote_cases
    (declaration : ReflectivePresentationDecl) (arguments : List Pattern) :
    (∃ inner, arguments = [.apply declaration.dropConstructor [inner]] ∧
        finishNormalizeReflectiveApply declaration
          declaration.quoteConstructor arguments = inner) ∨
      finishNormalizeReflectiveApply declaration
          declaration.quoteConstructor arguments =
        .apply declaration.quoteConstructor arguments := by
  unfold finishNormalizeReflectiveApply
  simp only [beq_self_eq_true, if_true]
  split
  · rename_i dropCandidate innerValue
    by_cases isDrop : dropCandidate = declaration.dropConstructor
    · subst dropCandidate
      exact Or.inl ⟨innerValue, rfl, by simp⟩
    · right
      simp [isDrop]
  · exact Or.inr rfl

/-- A parallel collapse producing a drop tower over a variable forces the
normalized element list to be exactly that singleton. -/
private theorem collapseParallel_eq_iterDrop_fvar
    (declaration : ReflectivePresentationDecl) {patterns : List Pattern}
    {level : Nat} {name : String}
    (equation : collapseParallel declaration patterns =
      iterDrop declaration level (.fvar name)) :
    patterns = [iterDrop declaration level (.fvar name)] := by
  cases patterns with
  | nil =>
      cases level <;> simp [collapseParallel, iterDrop] at equation
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [collapseParallel] at equation
          rw [equation]
      | cons second tail =>
          cases level <;> simp [collapseParallel, iterDrop] at equation

/-- A mapped `before ++ hole :: after` list equal to a singleton forces both
side lists empty and identifies the mapped hole. -/
private theorem map_append_cons_eq_singleton
    {α β : Type} {mapped : α → β} {before after : List α} {hole : α}
    {value : β}
    (equation : (before.map mapped ++ mapped hole :: after.map mapped) =
      [value]) :
    before = [] ∧ after = [] ∧ mapped hole = value := by
  have lengths := congrArg List.length equation
  simp only [List.length_append, List.length_map, List.length_cons,
    List.length_nil] at lengths
  have beforeNil : before = [] := by
    cases before with
    | nil => rfl
    | cons head tail => simp at lengths; omega
  have afterNil : after = [] := by
    cases after with
    | nil => rfl
    | cons head tail => simp at lengths; omega
  subst beforeNil
  subst afterNil
  simp only [List.map_nil, List.nil_append, List.cons.injEq,
    and_true] at equation
  exact ⟨rfl, rfl, equation⟩

/-! ## The collapse-elimination theorem -/

/-- If a one-hole context canonically evaporates onto one fresh free
variable, leaving a residual drop tower of some height, then it evaporates
onto every filler with the same residual tower.

This is the semantic elimination that any syntactic shell grammar
approximates: quote/drop absorption chains, parallel unit junk, singleton
wrappers, and nested flattening are all consequences of the single collapse
hypothesis, not separate cases. -/
theorem canonicalize_fill_eq_iterDrop_of_collapse
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop :
      declaration.quoteConstructor ≠ declaration.dropConstructor) :
    ∀ (context : OneHoleContext) (level : Nat) {name : String},
      name ∉ contextFrameFreeFvarNames context →
      canonicalize declaration (context.fill (.fvar name)) =
        iterDrop declaration level (.fvar name) →
      ∀ filler : Pattern,
        canonicalize declaration (context.fill filler) =
          iterDrop declaration level (canonicalize declaration filler) := by
  intro context
  induction context with
  | hole =>
      intro level name fresh collapse filler
      simp only [OneHoleContext.fill] at collapse ⊢
      cases level with
      | zero => rfl
      | succ level => simp [canonicalize, iterDrop] at collapse
  | apply constructor before inner after innerElimination =>
      intro level name fresh collapse filler
      simp only [contextFrameFreeFvarNames, List.mem_append, not_or] at fresh
      obtain ⟨⟨freshBefore, freshInner⟩, freshAfter⟩ := fresh
      simp only [OneHoleContext.fill] at collapse ⊢
      rw [canonicalize_apply_eq_finish] at collapse
      rw [canonicalize_apply_eq_finish]
      simp only [List.map_append, List.map_cons] at collapse ⊢
      by_cases isQuote : constructor = declaration.quoteConstructor
      · subst isQuote
        rcases finishNormalizeReflectiveApply_quote_cases declaration
            (before.map (canonicalize declaration) ++
              canonicalize declaration (inner.fill (.fvar name)) ::
                after.map (canonicalize declaration)) with
          ⟨innerValue, argumentsEq, resultEq⟩ | resultEq
        · rw [resultEq] at collapse
          obtain ⟨beforeNil, afterNil, holeEq⟩ :=
            map_append_cons_eq_singleton argumentsEq
          subst beforeNil
          subst afterNil
          have holeCollapse :
              canonicalize declaration (inner.fill (.fvar name)) =
                iterDrop declaration (level + 1) (.fvar name) := by
            rw [holeEq, collapse]
            rfl
          have innerEq := innerElimination (level + 1) freshInner
            holeCollapse filler
          simp only [List.map_nil, List.nil_append]
          rw [innerEq]
          exact finishNormalizeReflectiveApply_quote_drop declaration _
        · rw [resultEq] at collapse
          rcases iterDrop_fvar_shape declaration level name with
            shape | ⟨residual, shape⟩
          · rw [shape] at collapse
            exact Pattern.noConfusion collapse
          · rw [shape] at collapse
            simp only [Pattern.apply.injEq] at collapse
            exact absurd collapse.1 quoteNeDrop
      · rw [finishNormalizeReflectiveApply_of_ne_quote declaration isQuote]
          at collapse
        rw [finishNormalizeReflectiveApply_of_ne_quote declaration isQuote]
        cases level with
        | zero =>
            simp only [iterDrop] at collapse
            exact Pattern.noConfusion collapse
        | succ level =>
            simp only [iterDrop, Pattern.apply.injEq] at collapse
            obtain ⟨constructorEq, argumentsEq⟩ := collapse
            obtain ⟨beforeNil, afterNil, holeEq⟩ :=
              map_append_cons_eq_singleton argumentsEq
            subst beforeNil
            subst afterNil
            have innerEq := innerElimination level freshInner holeEq filler
            simp only [List.map_nil, List.nil_append]
            rw [innerEq, constructorEq]
            rfl
  | lambda binderName inner innerElimination =>
      intro level name fresh collapse filler
      simp only [OneHoleContext.fill, canonicalize] at collapse
      rcases iterDrop_fvar_shape declaration level name with
        shape | ⟨residual, shape⟩ <;> rw [shape] at collapse <;>
          exact Pattern.noConfusion collapse
  | multiLambda arity binderNames inner innerElimination =>
      intro level name fresh collapse filler
      simp only [OneHoleContext.fill, canonicalize] at collapse
      rcases iterDrop_fvar_shape declaration level name with
        shape | ⟨residual, shape⟩ <;> rw [shape] at collapse <;>
          exact Pattern.noConfusion collapse
  | substBody inner replacement innerElimination =>
      intro level name fresh collapse filler
      simp only [OneHoleContext.fill, canonicalize] at collapse
      rcases iterDrop_fvar_shape declaration level name with
        shape | ⟨residual, shape⟩ <;> rw [shape] at collapse <;>
          exact Pattern.noConfusion collapse
  | substReplacement body inner innerElimination =>
      intro level name fresh collapse filler
      simp only [OneHoleContext.fill, canonicalize] at collapse
      rcases iterDrop_fvar_shape declaration level name with
        shape | ⟨residual, shape⟩ <;> rw [shape] at collapse <;>
          exact Pattern.noConfusion collapse
  | collection collectionType before inner after rest innerElimination =>
      intro level name fresh collapse filler
      simp only [contextFrameFreeFvarNames, List.mem_append, not_or] at fresh
      obtain ⟨⟨⟨freshBefore, freshInner⟩, freshAfter⟩, freshRest⟩ := fresh
      simp only [OneHoleContext.fill] at collapse ⊢
      cases rest with
      | some restName =>
          rw [canonicalize_collection_rest] at collapse
          rcases iterDrop_fvar_shape declaration level name with
            shape | ⟨residual, shape⟩ <;> rw [shape] at collapse <;>
              exact Pattern.noConfusion collapse
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst isParallel
            rw [canonicalize_parallel] at collapse
            rw [canonicalize_parallel]
            simp only [List.map_append, List.map_cons] at collapse ⊢
            have contentsSplit : ∀ hole : Pattern,
                parallelContents declaration
                    (before.map (canonicalize declaration) ++
                      hole :: after.map (canonicalize declaration)) =
                  parallelContents declaration
                      (before.map (canonicalize declaration)) ++
                    (parallelContents declaration [hole] ++
                      parallelContents declaration
                        (after.map (canonicalize declaration))) := by
              intro hole
              rw [show before.map (canonicalize declaration) ++
                    hole :: after.map (canonicalize declaration) =
                  before.map (canonicalize declaration) ++
                    ([hole] ++ after.map (canonicalize declaration)) by simp,
                parallelContents_append, parallelContents_append]
            rw [normalizeParallelElements_eq_sort_parallelContents,
              contentsSplit] at collapse
            have sortedEq :=
              collapseParallel_eq_iterDrop_fvar declaration collapse
            have contentsPerm :
                (parallelContents declaration
                    (before.map (canonicalize declaration)) ++
                  (parallelContents declaration
                      [canonicalize declaration (inner.fill (.fvar name))] ++
                    parallelContents declaration
                      (after.map (canonicalize declaration)))).Perm
                  [iterDrop declaration level (.fvar name)] := by
              have sorted := sortPatterns_perm
                (parallelContents declaration
                    (before.map (canonicalize declaration)) ++
                  (parallelContents declaration
                      [canonicalize declaration (inner.fill (.fvar name))] ++
                    parallelContents declaration
                      (after.map (canonicalize declaration))))
              rw [sortedEq] at sorted
              exact sorted.symm
            have contentsEq :
                parallelContents declaration
                    (before.map (canonicalize declaration)) ++
                  (parallelContents declaration
                      [canonicalize declaration (inner.fill (.fvar name))] ++
                    parallelContents declaration
                      (after.map (canonicalize declaration))) =
                  [iterDrop declaration level (.fvar name)] :=
              List.perm_singleton.mp contentsPerm
            have nameInSurvivor :
                name ∈ (iterDrop declaration level
                  (.fvar name)).freeFvarNames := by
              rw [freeFvarNames_iterDrop]
              simp [Pattern.freeFvarNames]
            have sideNil : ∀ side : List Pattern,
                name ∉ side.flatMap Pattern.freeFvarNames →
                (∀ member ∈ parallelContents declaration
                    (side.map (canonicalize declaration)),
                  member ∈ (parallelContents declaration
                      (before.map (canonicalize declaration)) ++
                    (parallelContents declaration
                        [canonicalize declaration
                          (inner.fill (.fvar name))] ++
                      parallelContents declaration
                        (after.map (canonicalize declaration))))) →
                parallelContents declaration
                  (side.map (canonicalize declaration)) = [] := by
              intro side freshSide inclusion
              cases sideEq : parallelContents declaration
                  (side.map (canonicalize declaration)) with
              | nil => rfl
              | cons member tail =>
                  exfalso
                  have memberIn := inclusion member
                    (by rw [sideEq]; simp)
                  rw [contentsEq] at memberIn
                  have memberEq :
                      member = iterDrop declaration level (.fvar name) := by
                    simpa using memberIn
                  have nameAggregate :
                      name ∈ (side.map
                          (canonicalize declaration)).flatMap
                        Pattern.freeFvarNames :=
                    (mem_flatMap_freeFvarNames_parallelContents_iff
                        declaration name _).mp
                      (List.mem_flatMap.mpr ⟨member,
                        by rw [sideEq]; simp,
                        memberEq ▸ nameInSurvivor⟩)
                  apply freshSide
                  rcases List.mem_flatMap.mp nameAggregate with
                    ⟨canonicalMember, canonicalMemberIn, nameIn⟩
                  rcases List.mem_map.mp canonicalMemberIn with
                    ⟨sourceMember, sourceMemberIn, rfl⟩
                  exact List.mem_flatMap.mpr ⟨sourceMember, sourceMemberIn,
                    (mem_freeFvarNames_canonicalize_iff declaration name
                      sourceMember).mp nameIn⟩
            have beforeContentsNil := sideNil before freshBefore
              (fun member memberIn => by simp [memberIn])
            have afterContentsNil := sideNil after freshAfter
              (fun member memberIn => by simp [memberIn])
            have holeContentsEq :
                parallelContents declaration
                    [canonicalize declaration (inner.fill (.fvar name))] =
                  [iterDrop declaration level (.fvar name)] := by
              have := contentsEq
              rw [beforeContentsNil, afterContentsNil] at this
              simpa using this
            have holeCanonical := canonicalize_isCanonical declaration
              (inner.fill (.fvar name))
            have holeCollapse :
                canonicalize declaration (inner.fill (.fvar name)) =
                  iterDrop declaration level (.fvar name) := by
              by_cases isHoleParallel : ∃ elements,
                  canonicalize declaration (inner.fill (.fvar name)) =
                    .collection declaration.parallelCollection elements
                      none
              · exfalso
                obtain ⟨elements, holeIsParallel⟩ := isHoleParallel
                rw [holeIsParallel] at holeContentsEq holeCanonical
                have properties := holeCanonical.2 ⟨rfl, rfl⟩
                have expanded : parallelContents declaration
                    [.collection declaration.parallelCollection elements
                      none] = elements := by
                  simp only [parallelContents, List.flatMap_cons,
                    List.flatMap_nil, List.append_nil, parallelSplice,
                    beq_self_eq_true, if_true]
                  exact List.filter_eq_self.mpr
                    (fun element membership => by
                      simpa using (properties.2.2 element membership).1)
                rw [expanded] at holeContentsEq
                have twoOrMore := properties.1
                rw [holeContentsEq] at twoOrMore
                simp at twoOrMore
              · have splice : parallelSplice declaration
                    (canonicalize declaration (inner.fill (.fvar name))) =
                    [canonicalize declaration (inner.fill (.fvar name))] :=
                  parallelSplice_eq_singleton_of_not_parallel declaration _
                    (by
                      intro elements equation
                      exact isHoleParallel ⟨elements, equation⟩)
                by_cases isHoleUnit :
                    canonicalize declaration (inner.fill (.fvar name)) =
                      .apply declaration.parallelUnitConstructor []
                · exfalso
                  have emptied : parallelContents declaration
                      [canonicalize declaration
                        (inner.fill (.fvar name))] = [] := by
                    rw [isHoleUnit]
                    simp [parallelContents, parallelSplice]
                  rw [emptied] at holeContentsEq
                  cases holeContentsEq
                · have kept : parallelContents declaration
                      [canonicalize declaration
                        (inner.fill (.fvar name))] =
                      [canonicalize declaration
                        (inner.fill (.fvar name))] := by
                    simp [parallelContents, splice, isHoleUnit]
                  rw [kept] at holeContentsEq
                  simpa using holeContentsEq
            have innerEq := innerElimination level freshInner holeCollapse
              filler
            have fillerSplit := contentsSplit
              (canonicalize declaration (inner.fill filler))
            rw [normalizeParallelElements_eq_sort_parallelContents,
              fillerSplit, beforeContentsNil, afterContentsNil,
              List.nil_append, List.append_nil,
              ← normalizeParallelElements_eq_sort_parallelContents,
              collapse_normalize_singleton_of_isCanonical declaration
                (canonicalize_isCanonical declaration (inner.fill filler)),
              innerEq]
          · rw [canonicalize_collection_of_ne_parallel declaration
              isParallel] at collapse
            rcases iterDrop_fvar_shape declaration level name with
              shape | ⟨residual, shape⟩ <;> rw [shape] at collapse <;>
                exact Pattern.noConfusion collapse

/-- Boundary-survivor law: a context that canonically evaporates onto one
fresh free variable transmits canonicalization to every filler.

This is the exact fact a semantic-cut provider needs at a collapsing root:
when the whole static frame canonicalizes to the surviving occurrence, the
canonical class of the whole term is the canonical class of that
occurrence's content — for the exact stopped occurrence, not merely some
equal-looking one. -/
theorem canonicalize_fill_eq_of_collapse_fvar
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop :
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    {context : OneHoleContext} {name : String}
    (fresh : name ∉ contextFrameFreeFvarNames context)
    (collapse : canonicalize declaration (context.fill (.fvar name)) =
      .fvar name)
    (filler : Pattern) :
    canonicalize declaration (context.fill filler) =
      canonicalize declaration filler :=
  canonicalize_fill_eq_iterDrop_of_collapse declaration quoteNeDrop context 0
    fresh collapse filler

/-! ## Occurrence-count preservation and hypothesis-free elimination

Canonicalization never deletes a free-variable occurrence (unit removal
deletes only variable-free units, absorption keeps the payload) and never
duplicates one.  Counting occurrences therefore shows that a collapse onto
one variable already implies that variable is fresh in the frame, so the
freshness hypothesis of the elimination theorem is derivable rather than
assumed. -/

/-- Number of free occurrences of one name, counting collection rests like
`Pattern.freeFvarNames` does. -/
def fvarOccurrenceCount (name : String) : Pattern → Nat
  | .bvar _ => 0
  | .fvar other => if other = name then 1 else 0
  | .apply _ arguments =>
      (arguments.map (fvarOccurrenceCount name)).sum
  | .lambda _ body => fvarOccurrenceCount name body
  | .multiLambda _ _ body => fvarOccurrenceCount name body
  | .subst body replacement =>
      fvarOccurrenceCount name body + fvarOccurrenceCount name replacement
  | .collection _ elements rest =>
      (elements.map (fvarOccurrenceCount name)).sum +
        rest.elim 0 (fun restName => if restName = name then 1 else 0)

/-- Frame occurrence count of a one-hole context away from its hole. -/
def contextFrameFvarOccurrenceCount (name : String) :
    OneHoleContext → Nat
  | .hole => 0
  | .apply _ before inner after =>
      (before.map (fvarOccurrenceCount name)).sum +
        contextFrameFvarOccurrenceCount name inner +
        (after.map (fvarOccurrenceCount name)).sum
  | .lambda _ inner => contextFrameFvarOccurrenceCount name inner
  | .multiLambda _ _ inner => contextFrameFvarOccurrenceCount name inner
  | .substBody inner replacement =>
      contextFrameFvarOccurrenceCount name inner +
        fvarOccurrenceCount name replacement
  | .substReplacement body inner =>
      fvarOccurrenceCount name body +
        contextFrameFvarOccurrenceCount name inner
  | .collection _ before inner after rest =>
      (before.map (fvarOccurrenceCount name)).sum +
        contextFrameFvarOccurrenceCount name inner +
        (after.map (fvarOccurrenceCount name)).sum +
        rest.elim 0 (fun restName => if restName = name then 1 else 0)

/-- Filling decomposes the count into frame plus filler. -/
theorem fvarOccurrenceCount_fill (name : String) :
    ∀ (context : OneHoleContext) (filler : Pattern),
      fvarOccurrenceCount name (context.fill filler) =
        contextFrameFvarOccurrenceCount name context +
          fvarOccurrenceCount name filler := by
  intro context
  induction context with
  | hole =>
      intro filler
      simp [OneHoleContext.fill, contextFrameFvarOccurrenceCount]
  | apply constructor before inner after innerCount =>
      intro filler
      simp only [OneHoleContext.fill, fvarOccurrenceCount,
        contextFrameFvarOccurrenceCount, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons, innerCount filler]
      omega
  | lambda binderName inner innerCount =>
      intro filler
      simp [OneHoleContext.fill, fvarOccurrenceCount,
        contextFrameFvarOccurrenceCount, innerCount filler]
  | multiLambda arity binderNames inner innerCount =>
      intro filler
      simp [OneHoleContext.fill, fvarOccurrenceCount,
        contextFrameFvarOccurrenceCount, innerCount filler]
  | substBody inner replacement innerCount =>
      intro filler
      simp only [OneHoleContext.fill, fvarOccurrenceCount,
        contextFrameFvarOccurrenceCount, innerCount filler]
      omega
  | substReplacement body inner innerCount =>
      intro filler
      simp only [OneHoleContext.fill, fvarOccurrenceCount,
        contextFrameFvarOccurrenceCount, innerCount filler]
      omega
  | collection collectionType before inner after rest innerCount =>
      intro filler
      simp only [OneHoleContext.fill, fvarOccurrenceCount,
        contextFrameFvarOccurrenceCount, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons, innerCount filler]
      omega

private theorem perm_nat_sum_eq {left right : List Nat}
    (permutation : left.Perm right) : left.sum = right.sum := by
  induction permutation with
  | nil => rfl
  | cons head _ tailSum => simp [tailSum]
  | swap first second rest =>
      simp only [List.sum_cons]
      omega
  | trans _ _ leftSum rightSum => exact leftSum.trans rightSum

private theorem eq_zero_of_mem_of_nat_sum_eq_zero :
    ∀ {items : List Nat}, items.sum = 0 →
      ∀ {item : Nat}, item ∈ items → item = 0
  | [], _, _, membership => by cases membership
  | head :: tail, zero, item, membership => by
      simp only [List.sum_cons, Nat.add_eq_zero_iff] at zero
      rcases List.mem_cons.mp membership with rfl | tailMembership
      · exact zero.1
      · exact eq_zero_of_mem_of_nat_sum_eq_zero zero.2 tailMembership

private theorem sum_map_flatMap {α β : Type} (convert : α → List β)
    (measure : β → Nat) :
    ∀ items : List α,
      ((items.flatMap convert).map measure).sum =
        (items.map (fun item => ((convert item).map measure).sum)).sum
  | [] => rfl
  | item :: items => by
      simp [List.flatMap_cons, List.map_append, List.sum_append,
        sum_map_flatMap convert measure items]

private theorem sum_map_filter_of_dropped_zero {α : Type}
    (keep : α → Bool) (measure : α → Nat) :
    ∀ items : List α, (∀ item ∈ items, keep item = false →
        measure item = 0) →
      ((items.filter keep).map measure).sum = (items.map measure).sum
  | [], _ => rfl
  | item :: items, dropped => by
      have tail := sum_map_filter_of_dropped_zero keep measure items
        (fun member membership refused =>
          dropped member (by simp [membership]) refused)
      cases kept : keep item with
      | true => simp [kept, tail]
      | false =>
          simp [kept, tail, dropped item (by simp) kept]

/-- Splicing one pattern into parallel contents preserves its occurrence
count. -/
private theorem sum_map_parallelSplice
    (declaration : ReflectivePresentationDecl) (name : String)
    (pattern : Pattern) :
    ((parallelSplice declaration pattern).map
      (fvarOccurrenceCount name)).sum = fvarOccurrenceCount name pattern := by
  cases pattern with
  | collection collectionType elements rest =>
      cases rest with
      | some restName => simp [parallelSplice, fvarOccurrenceCount]
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst isParallel
            simp [parallelSplice, fvarOccurrenceCount]
          · simp [parallelSplice, isParallel, fvarOccurrenceCount]
  | bvar index => simp [parallelSplice, fvarOccurrenceCount]
  | fvar other => simp [parallelSplice, fvarOccurrenceCount]
  | apply constructor arguments => simp [parallelSplice, fvarOccurrenceCount]
  | lambda binderName body => simp [parallelSplice, fvarOccurrenceCount]
  | multiLambda arity binderNames body =>
      simp [parallelSplice, fvarOccurrenceCount]
  | subst body replacement => simp [parallelSplice, fvarOccurrenceCount]

/-- Full parallel normalization preserves the aggregate occurrence count:
splicing redistributes, unit removal deletes only variable-free units, and
sorting permutes. -/
private theorem sum_map_normalizeParallelElements
    (declaration : ReflectivePresentationDecl) (name : String)
    (patterns : List Pattern) :
    ((normalizeParallelElements declaration patterns).map
        (fvarOccurrenceCount name)).sum =
      (patterns.map (fvarOccurrenceCount name)).sum := by
  rw [normalizeParallelElements_eq_sort_parallelContents]
  have sorted := (sortPatterns_perm
    (parallelContents declaration patterns)).map (fvarOccurrenceCount name)
  rw [perm_nat_sum_eq sorted]
  unfold parallelContents
  rw [sum_map_filter_of_dropped_zero _ _ _
    (fun item _ refused => by
      have isUnit : item = .apply declaration.parallelUnitConstructor [] := by
        simpa using refused
      simp [isUnit, fvarOccurrenceCount])]
  rw [sum_map_flatMap]
  congr 1
  exact List.map_congr_left (fun pattern _ =>
    sum_map_parallelSplice declaration name pattern)

/-- Rebuilding the parallel node preserves the aggregate count. -/
private theorem fvarOccurrenceCount_collapseParallel
    (declaration : ReflectivePresentationDecl) (name : String)
    (patterns : List Pattern) :
    fvarOccurrenceCount name (collapseParallel declaration patterns) =
      (patterns.map (fvarOccurrenceCount name)).sum := by
  cases patterns with
  | nil => simp [collapseParallel, fvarOccurrenceCount]
  | cons first rest =>
      cases rest with
      | nil => simp [collapseParallel]
      | cons second tail =>
          simp [collapseParallel, fvarOccurrenceCount]

/-- Quote/Drop orientation preserves the aggregate count. -/
private theorem fvarOccurrenceCount_finishNormalizeReflectiveApply
    (declaration : ReflectivePresentationDecl) (name constructor : String)
    (arguments : List Pattern) :
    fvarOccurrenceCount name
        (finishNormalizeReflectiveApply declaration constructor arguments) =
      (arguments.map (fvarOccurrenceCount name)).sum := by
  unfold finishNormalizeReflectiveApply
  by_cases isQuote : constructor = declaration.quoteConstructor
  · subst isQuote
    simp only [beq_self_eq_true, if_true]
    split
    · rename_i dropCandidate innerValue
      by_cases isDrop : dropCandidate = declaration.dropConstructor
      · subst isDrop
        simp [fvarOccurrenceCount]
      · simp [isDrop, fvarOccurrenceCount]
    · simp [fvarOccurrenceCount]
  · simp [isQuote, fvarOccurrenceCount]

/-- Canonicalization preserves the exact number of free occurrences of every
name: no rule deletes or duplicates a variable. -/
theorem fvarOccurrenceCount_canonicalize
    (declaration : ReflectivePresentationDecl) (name : String) :
    ∀ pattern : Pattern,
      fvarOccurrenceCount name (canonicalize declaration pattern) =
        fvarOccurrenceCount name pattern
  | .bvar index => rfl
  | .fvar other => rfl
  | .apply constructor arguments => by
      rw [canonicalize_apply_eq_finish,
        fvarOccurrenceCount_finishNormalizeReflectiveApply]
      simp only [fvarOccurrenceCount, List.map_map]
      congr 1
      exact List.map_congr_left (fun argument _ =>
        fvarOccurrenceCount_canonicalize declaration name argument)
  | .lambda binderName body => by
      simp only [canonicalize, fvarOccurrenceCount]
      exact fvarOccurrenceCount_canonicalize declaration name body
  | .multiLambda arity binderNames body => by
      simp only [canonicalize, fvarOccurrenceCount]
      exact fvarOccurrenceCount_canonicalize declaration name body
  | .subst body replacement => by
      simp only [canonicalize, fvarOccurrenceCount]
      rw [fvarOccurrenceCount_canonicalize declaration name body,
        fvarOccurrenceCount_canonicalize declaration name replacement]
  | .collection collectionType elements rest => by
      cases rest with
      | some restName =>
          rw [canonicalize_collection_rest]
          simp only [fvarOccurrenceCount, List.map_map]
          congr 2
          exact List.map_congr_left (fun element _ =>
            fvarOccurrenceCount_canonicalize declaration name element)
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst isParallel
            rw [canonicalize_parallel,
              fvarOccurrenceCount_collapseParallel,
              sum_map_normalizeParallelElements]
            simp only [fvarOccurrenceCount, List.map_map]
            congr 1
            exact List.map_congr_left (fun element _ =>
              fvarOccurrenceCount_canonicalize declaration name element)
          · rw [canonicalize_collection_of_ne_parallel declaration isParallel]
            simp only [fvarOccurrenceCount, List.map_map]
            congr 2
            exact List.map_congr_left (fun element _ =>
              fvarOccurrenceCount_canonicalize declaration name element)

/-- A pattern with zero occurrences of a name does not carry that name. -/
theorem not_mem_freeFvarNames_of_count_zero (name : String) :
    ∀ pattern : Pattern,
      fvarOccurrenceCount name pattern = 0 →
      name ∉ pattern.freeFvarNames := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro _ nameIn
      simp [Pattern.freeFvarNames] at nameIn
  | hfvar other =>
      intro zero nameIn
      simp only [Pattern.freeFvarNames, List.mem_singleton] at nameIn
      subst nameIn
      simp [fvarOccurrenceCount] at zero
  | happly constructor arguments recurse =>
      intro zero nameIn
      simp only [fvarOccurrenceCount] at zero
      simp only [Pattern.freeFvarNames] at nameIn
      obtain ⟨argument, argumentIn, nameInArgument⟩ :=
        List.mem_flatMap.mp nameIn
      exact recurse argument argumentIn
        (eq_zero_of_mem_of_nat_sum_eq_zero zero
          (List.mem_map.mpr ⟨argument, argumentIn, rfl⟩)) nameInArgument
  | hlambda binderName body recurse =>
      intro zero
      simp only [fvarOccurrenceCount] at zero
      simp only [Pattern.freeFvarNames]
      exact recurse zero
  | hmultiLambda arity binderNames body recurse =>
      intro zero
      simp only [fvarOccurrenceCount] at zero
      simp only [Pattern.freeFvarNames]
      exact recurse zero
  | hsubst body replacement recurseBody recurseReplacement =>
      intro zero nameIn
      simp only [fvarOccurrenceCount, Nat.add_eq_zero_iff] at zero
      simp only [Pattern.freeFvarNames, List.mem_append] at nameIn
      rcases nameIn with inBody | inReplacement
      · exact recurseBody zero.1 inBody
      · exact recurseReplacement zero.2 inReplacement
  | hcollection collectionType elements rest recurse =>
      intro zero nameIn
      simp only [fvarOccurrenceCount, Nat.add_eq_zero_iff] at zero
      simp only [Pattern.freeFvarNames, List.mem_append] at nameIn
      rcases nameIn with inElements | inRest
      · obtain ⟨element, elementIn, nameInElement⟩ :=
          List.mem_flatMap.mp inElements
        exact recurse element elementIn
          (eq_zero_of_mem_of_nat_sum_eq_zero zero.1
            (List.mem_map.mpr ⟨element, elementIn, rfl⟩)) nameInElement
      · cases rest with
        | none => simp at inRest
        | some restName =>
            simp only [Option.toList, List.mem_singleton] at inRest
            subst inRest
            simp at zero

/-- A frame with zero occurrences of a name does not carry that name. -/
theorem not_mem_contextFrameFreeFvarNames_of_count_zero (name : String) :
    ∀ context : OneHoleContext,
      contextFrameFvarOccurrenceCount name context = 0 →
      name ∉ contextFrameFreeFvarNames context := by
  intro context
  induction context with
  | hole =>
      intro _ nameIn
      simp [contextFrameFreeFvarNames] at nameIn
  | apply constructor before inner after innerFresh =>
      intro zero nameIn
      simp only [contextFrameFvarOccurrenceCount,
        Nat.add_eq_zero_iff] at zero
      simp only [contextFrameFreeFvarNames, List.mem_append] at nameIn
      rcases nameIn with (inBefore | inInner) | inAfter
      · obtain ⟨pattern, patternIn, nameInPattern⟩ :=
          List.mem_flatMap.mp inBefore
        exact not_mem_freeFvarNames_of_count_zero name pattern
          (eq_zero_of_mem_of_nat_sum_eq_zero zero.1.1
            (List.mem_map.mpr ⟨pattern, patternIn, rfl⟩)) nameInPattern
      · exact innerFresh zero.1.2 inInner
      · obtain ⟨pattern, patternIn, nameInPattern⟩ :=
          List.mem_flatMap.mp inAfter
        exact not_mem_freeFvarNames_of_count_zero name pattern
          (eq_zero_of_mem_of_nat_sum_eq_zero zero.2
            (List.mem_map.mpr ⟨pattern, patternIn, rfl⟩)) nameInPattern
  | lambda binderName inner innerFresh =>
      intro zero
      simp only [contextFrameFvarOccurrenceCount] at zero
      simp only [contextFrameFreeFvarNames]
      exact innerFresh zero
  | multiLambda arity binderNames inner innerFresh =>
      intro zero
      simp only [contextFrameFvarOccurrenceCount] at zero
      simp only [contextFrameFreeFvarNames]
      exact innerFresh zero
  | substBody inner replacement innerFresh =>
      intro zero nameIn
      simp only [contextFrameFvarOccurrenceCount,
        Nat.add_eq_zero_iff] at zero
      simp only [contextFrameFreeFvarNames, List.mem_append] at nameIn
      rcases nameIn with inInner | inReplacement
      · exact innerFresh zero.1 inInner
      · exact not_mem_freeFvarNames_of_count_zero name replacement zero.2
          inReplacement
  | substReplacement body inner innerFresh =>
      intro zero nameIn
      simp only [contextFrameFvarOccurrenceCount,
        Nat.add_eq_zero_iff] at zero
      simp only [contextFrameFreeFvarNames, List.mem_append] at nameIn
      rcases nameIn with inBody | inInner
      · exact not_mem_freeFvarNames_of_count_zero name body zero.1 inBody
      · exact innerFresh zero.2 inInner
  | collection collectionType before inner after rest innerFresh =>
      intro zero nameIn
      simp only [contextFrameFvarOccurrenceCount,
        Nat.add_eq_zero_iff] at zero
      simp only [contextFrameFreeFvarNames, List.mem_append] at nameIn
      rcases nameIn with ((inBefore | inInner) | inAfter) | inRest
      · obtain ⟨pattern, patternIn, nameInPattern⟩ :=
          List.mem_flatMap.mp inBefore
        exact not_mem_freeFvarNames_of_count_zero name pattern
          (eq_zero_of_mem_of_nat_sum_eq_zero zero.1.1.1
            (List.mem_map.mpr ⟨pattern, patternIn, rfl⟩)) nameInPattern
      · exact innerFresh zero.1.1.2 inInner
      · obtain ⟨pattern, patternIn, nameInPattern⟩ :=
          List.mem_flatMap.mp inAfter
        exact not_mem_freeFvarNames_of_count_zero name pattern
          (eq_zero_of_mem_of_nat_sum_eq_zero zero.1.2
            (List.mem_map.mpr ⟨pattern, patternIn, rfl⟩)) nameInPattern
      · cases rest with
        | none => simp at inRest
        | some restName =>
            simp only [Option.toList, List.mem_singleton] at inRest
            subst inRest
            simp at zero

/-- The collapse hypothesis alone already certifies frame freshness: the
canonical image retains exactly one occurrence, which the hole supplies. -/
theorem not_mem_contextFrameFreeFvarNames_of_collapse
    (declaration : ReflectivePresentationDecl)
    {context : OneHoleContext} {name : String}
    (collapse : canonicalize declaration (context.fill (.fvar name)) =
      .fvar name) :
    name ∉ contextFrameFreeFvarNames context := by
  apply not_mem_contextFrameFreeFvarNames_of_count_zero
  have preserved := fvarOccurrenceCount_canonicalize declaration name
    (context.fill (.fvar name))
  rw [collapse, fvarOccurrenceCount_fill] at preserved
  simp only [fvarOccurrenceCount] at preserved
  omega

/-- A context which canonically evaporates onto the variable placed in its
hole contains no other free-variable occurrences in its fixed frame.

This strengthens the single-name freshness theorem above.  It is useful when
the filler is subsequently renamed by a finite semantic environment: the
fixed frame is then definitionally unaffected by that renaming. -/
theorem contextFrameFreeFvarNames_eq_nil_of_collapse
    (declaration : ReflectivePresentationDecl)
    {context : OneHoleContext} {survivor : String}
    (collapse : canonicalize declaration (context.fill (.fvar survivor)) =
      .fvar survivor) :
    contextFrameFreeFvarNames context = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name nameIn
  by_cases nameEq : name = survivor
  · subst name
    exact not_mem_contextFrameFreeFvarNames_of_collapse declaration collapse
      nameIn
  · have preserved := fvarOccurrenceCount_canonicalize declaration name
        (context.fill (.fvar survivor))
    rw [collapse, fvarOccurrenceCount_fill] at preserved
    simp only [fvarOccurrenceCount] at preserved
    have frameCountZero :
        contextFrameFvarOccurrenceCount name context = 0 := by
      omega
    exact not_mem_contextFrameFreeFvarNames_of_count_zero name context
      frameCountZero nameIn

/-- Hypothesis-free boundary-survivor law: a canonical collapse onto one
variable transmits canonicalization to every filler; the freshness of that
variable in the frame is a consequence, not an assumption. -/
theorem canonicalize_fill_eq_of_collapse
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop :
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    {context : OneHoleContext} {name : String}
    (collapse : canonicalize declaration (context.fill (.fvar name)) =
      .fvar name)
    (filler : Pattern) :
    canonicalize declaration (context.fill filler) =
      canonicalize declaration filler :=
  canonicalize_fill_eq_of_collapse_fvar declaration quoteNeDrop
    (not_mem_contextFrameFreeFvarNames_of_collapse declaration collapse)
    collapse filler

/-- Occurrence-level form: if some selected occurrence's surrounding context
canonically evaporates onto a test variable, then the whole term shares the
canonical class of exactly that occurrence's content.

The test is decidable for any concrete occurrence, so a provider may branch
on it directly: `Selects` hands the zipper, and no syntactic shell grammar
or occurrence trace is required. -/
theorem canonicalize_eq_of_selects_collapse
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop :
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    {content term : Pattern} {context : OneHoleContext} {witness : String}
    (selected : Selects content context term)
    (collapse : canonicalize declaration (context.fill (.fvar witness)) =
      .fvar witness) :
    canonicalize declaration term = canonicalize declaration content := by
  rw [← selected.fill_eq]
  exact canonicalize_fill_eq_of_collapse declaration quoteNeDrop collapse
    content

/-! ## Quote-absorption resolution

`@(hole)` is not filler-generic: it absorbs exactly the fillers whose
canonical form is a drop application.  The collapsing lane therefore has one
arm the evaporating-context theorem cannot cover.  This section closes it
without any new cut constructor or measure change: whenever the quote's
argument canonicalizes to a drop application, some *strictly smaller*
pattern already carries the canonical class of the whole quote application,
so the standard size-sum recursion applies unchanged. -/

/-- Canonicalizing a quote application either absorbs a sole
drop-application argument or keeps the quote root over the canonicalized
argument.  The two cases are exclusive by inspection of the second
component. -/
theorem canonicalize_quote_app_cases
    (declaration : ReflectivePresentationDecl) (argument : Pattern) :
    (∃ payload,
      canonicalize declaration argument =
          .apply declaration.dropConstructor [payload] ∧
        canonicalize declaration
            (.apply declaration.quoteConstructor [argument]) = payload) ∨
      canonicalize declaration
          (.apply declaration.quoteConstructor [argument]) =
        .apply declaration.quoteConstructor
          [canonicalize declaration argument] := by
  rw [canonicalize_apply_eq_finish]
  simp only [List.map_cons, List.map_nil]
  rcases finishNormalizeReflectiveApply_quote_cases declaration
      [canonicalize declaration argument] with
    ⟨payload, argumentsEq, resultEq⟩ | resultEq
  · left
    refine ⟨payload, ?_, resultEq⟩
    simpa using argumentsEq
  · right
    exact resultEq

/-- Wrapping canonically equal arguments in the declared quote constructor
preserves canonical equality.  This is the one-constructor instance of fill
congruence, restated locally to keep this module below the language layer. -/
theorem canonicalize_quote_app_congr
    (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (arguments : canonicalize declaration left =
      canonicalize declaration right) :
    canonicalize declaration (.apply declaration.quoteConstructor [left]) =
      canonicalize declaration
        (.apply declaration.quoteConstructor [right]) := by
  rw [canonicalize_apply_eq_finish, canonicalize_apply_eq_finish]
  simp only [List.map_cons, List.map_nil, arguments]

private theorem exists_singleton_contribution {α β : Type}
    (contribute : α → List β) :
    ∀ items : List α, ∀ {value : β},
      items.flatMap contribute = [value] →
      ∃ item ∈ items, contribute item = [value]
  | [], value, equation => by cases equation
  | item :: items, value, equation => by
      rw [List.flatMap_cons] at equation
      cases headEq : contribute item with
      | nil =>
          rw [headEq, List.nil_append] at equation
          obtain ⟨found, membership, foundEq⟩ :=
            exists_singleton_contribution contribute items equation
          exact ⟨found, by simp [membership], foundEq⟩
      | cons headValue headTail =>
          rw [headEq] at equation
          simp only [List.cons_append, List.cons.injEq] at equation
          obtain ⟨headValueEq, restEq⟩ := equation
          have headTailNil : headTail = [] :=
            List.eq_nil_of_append_eq_nil restEq |>.1
          exact ⟨item, by simp, by rw [headEq, headValueEq, headTailNil]⟩

private theorem filter_flatMap_eq_flatMap_filter {α β : Type}
    (convert : α → List β) (keep : β → Bool) :
    ∀ items : List α,
      (items.flatMap convert).filter keep =
        items.flatMap fun item => (convert item).filter keep
  | [] => rfl
  | item :: items => by
      simp [List.flatMap_cons, List.filter_append,
        filter_flatMap_eq_flatMap_filter convert keep items]

/-- If a parallel node canonicalizes to a non-unit, non-parallel result,
exactly one element carries that canonical class; the others are canonical
units. -/
theorem exists_member_of_parallel_collapse
    (declaration : ReflectivePresentationDecl)
    {elements : List Pattern} {result : Pattern}
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      result)
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none) :
    ∃ element ∈ elements,
      canonicalize declaration element = result := by
  rw [canonicalize_parallel] at collapsed
  have normalizedEq : normalizeParallelElements declaration
      (elements.map (canonicalize declaration)) =
      [result] := by
    cases listEq : normalizeParallelElements declaration
        (elements.map (canonicalize declaration)) with
    | nil =>
        rw [listEq] at collapsed
        simp only [collapseParallel] at collapsed
        exact absurd collapsed.symm notUnit
    | cons first rest =>
        cases rest with
        | nil =>
            rw [listEq] at collapsed
            simp only [collapseParallel] at collapsed
            rw [collapsed]
        | cons second tail =>
            rw [listEq] at collapsed
            exact absurd collapsed.symm (notParallel _)
  have contentsEq : parallelContents declaration
      (elements.map (canonicalize declaration)) =
      [result] := by
    have sorted := sortPatterns_perm (parallelContents declaration
      (elements.map (canonicalize declaration)))
    rw [normalizeParallelElements_eq_sort_parallelContents] at normalizedEq
    rw [normalizedEq] at sorted
    exact List.perm_singleton.mp sorted.symm
  unfold parallelContents at contentsEq
  rw [filter_flatMap_eq_flatMap_filter] at contentsEq
  obtain ⟨member, memberIn, memberEq⟩ :=
    exists_singleton_contribution _ _ contentsEq
  obtain ⟨element, elementIn, elementEq⟩ := List.mem_map.mp memberIn
  refine ⟨element, elementIn, ?_⟩
  rw [elementEq]
  by_cases isParallel : ∃ nested, member =
      .collection declaration.parallelCollection nested none
  · exfalso
    obtain ⟨nested, rfl⟩ := isParallel
    have memberCanonical : IsCanonical declaration
        (.collection declaration.parallelCollection nested none) := by
      rw [← elementEq]
      exact canonicalize_isCanonical declaration element
    have properties := memberCanonical.2 ⟨rfl, rfl⟩
    have spliced : parallelSplice declaration
        (.collection declaration.parallelCollection nested none) =
        nested := by
      simp [parallelSplice]
    rw [spliced, List.filter_eq_self.mpr (fun nestedMember membership => by
      simpa using (properties.2.2 nestedMember membership).1)] at memberEq
    have lengths := congrArg List.length memberEq
    have twoOrMore := properties.1
    simp at lengths
    omega
  · have spliced : parallelSplice declaration member = [member] :=
      parallelSplice_eq_singleton_of_not_parallel declaration member (by
        intro nested equation
        exact isParallel ⟨nested, equation⟩)
    rw [spliced] at memberEq
    by_cases isUnit : member =
        .apply declaration.parallelUnitConstructor []
    · simp [isUnit] at memberEq
    · simp only [List.filter_cons, List.filter_nil] at memberEq
      rw [if_pos (by simpa using isUnit)] at memberEq
      simpa using memberEq

/-- Application-shaped specialization of
`exists_member_of_parallel_collapse`. -/
theorem exists_member_of_parallel_collapse_apply
    (declaration : ReflectivePresentationDecl)
    {elements : List Pattern} {constructor : String}
    {arguments : List Pattern}
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      .apply constructor arguments)
    (notUnit : Pattern.apply constructor arguments ≠
      .apply declaration.parallelUnitConstructor []) :
    ∃ element ∈ elements,
      canonicalize declaration element = .apply constructor arguments := by
  exact exists_member_of_parallel_collapse declaration collapsed notUnit
    (fun nested equality => Pattern.noConfusion equality)

/-- Bound-variable specialization: a parallel collapsing to one rigid index
contains an actual member with that canonical form. -/
theorem exists_member_of_parallel_collapse_bvar
    (declaration : ReflectivePresentationDecl)
    {elements : List Pattern} {index : Nat}
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      .bvar index) :
    ∃ element ∈ elements,
      canonicalize declaration element = .bvar index := by
  exact exists_member_of_parallel_collapse declaration collapsed
    (fun equality => Pattern.noConfusion equality)
    (fun nested equality => Pattern.noConfusion equality)

/-- A parallel collapse onto a bound variable exposes a strictly smaller
member in the same canonical class. -/
theorem exists_smaller_of_parallel_collapse_bvar
    (declaration : ReflectivePresentationDecl)
    {elements : List Pattern} {index : Nat}
    (collapsed : canonicalize declaration
    (.collection declaration.parallelCollection elements none) =
      .bvar index) :
    ∃ smaller : Pattern,
      sizeOf smaller <
          sizeOf (Pattern.collection declaration.parallelCollection elements
            none) ∧
        canonicalize declaration smaller = .bvar index := by
  obtain ⟨smaller, membership, smallerCanonical⟩ :=
    exists_member_of_parallel_collapse_bvar declaration collapsed
  refine ⟨smaller, ?_, smallerCanonical⟩
  have memberSmaller := List.sizeOf_lt_of_mem membership
  simp_wf
  omega

/-- Absorption witness: when the quote's argument canonicalizes to a drop
application, some strictly smaller pattern carries the canonical class of
the whole quote application.

This closes the quote-absorption arm of a collapsing-root case analysis
with the standard size-sum recursion: replace the quote application by the
witness and recurse; no dedicated cut constructor, no measure change, and
no dependence on constructor-name sizes. -/
theorem exists_smaller_quote_collapse
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop :
      declaration.quoteConstructor ≠ declaration.dropConstructor) :
    ∀ (fuel : Nat) (argument payload : Pattern),
      sizeOf argument ≤ fuel →
      canonicalize declaration argument =
        .apply declaration.dropConstructor [payload] →
      ∃ smaller : Pattern,
        sizeOf smaller <
          sizeOf (Pattern.apply declaration.quoteConstructor [argument]) ∧
        canonicalize declaration smaller =
          canonicalize declaration
            (.apply declaration.quoteConstructor [argument])
  | 0, argument, payload, bound, absorbed => by
      exfalso
      cases argument <;> simp at bound
  | fuel + 1, argument, payload, bound, absorbed => by
      cases argument with
      | bvar index => simp [canonicalize] at absorbed
      | fvar name => simp [canonicalize] at absorbed
      | lambda binderName body => simp [canonicalize] at absorbed
      | multiLambda arity binderNames body =>
          simp [canonicalize] at absorbed
      | subst body replacement => simp [canonicalize] at absorbed
      | apply constructor arguments =>
          rw [canonicalize_apply_eq_finish] at absorbed
          by_cases isQuote : constructor = declaration.quoteConstructor
          · subst isQuote
            rcases finishNormalizeReflectiveApply_quote_cases declaration
                (arguments.map (canonicalize declaration)) with
              ⟨innerValue, argumentsEq, resultEq⟩ | resultEq
            · rw [resultEq] at absorbed
              have argumentsShape : ∃ inner, arguments = [inner] ∧
                  canonicalize declaration inner =
                    .apply declaration.dropConstructor [innerValue] := by
                cases arguments with
                | nil => cases argumentsEq
                | cons first rest =>
                    cases rest with
                    | nil =>
                        refine ⟨first, rfl, ?_⟩
                        simpa using argumentsEq
                    | cons second tail => simp at argumentsEq
              obtain ⟨inner, rfl, innerCanonical⟩ := argumentsShape
              rw [absorbed] at innerCanonical
              have innerBound : sizeOf inner ≤ fuel := by
                simp at bound
                omega
              obtain ⟨intermediate, intermediateSmaller,
                  intermediateCanonical⟩ :=
                exists_smaller_quote_collapse declaration quoteNeDrop fuel
                  inner (.apply declaration.dropConstructor [payload])
                  innerBound innerCanonical
              have intermediateAbsorbed :
                  canonicalize declaration intermediate =
                    .apply declaration.dropConstructor [payload] := by
                rw [intermediateCanonical, canonicalize_apply_eq_finish]
                simp only [List.map_cons, List.map_nil, innerCanonical]
                rw [show finishNormalizeReflectiveApply declaration
                    declaration.quoteConstructor
                    [.apply declaration.dropConstructor
                      [.apply declaration.dropConstructor [payload]]] =
                    .apply declaration.dropConstructor [payload] from
                  finishNormalizeReflectiveApply_quote_drop declaration _]
              have intermediateBound : sizeOf intermediate ≤ fuel := by
                simp at intermediateSmaller bound
                omega
              obtain ⟨smaller, smallerBound, smallerCanonical⟩ :=
                exists_smaller_quote_collapse declaration quoteNeDrop fuel
                  intermediate payload intermediateBound
                  intermediateAbsorbed
              refine ⟨smaller, ?_, ?_⟩
              · simp at smallerBound intermediateSmaller ⊢
                omega
              · rw [smallerCanonical]
                exact canonicalize_quote_app_congr declaration
                  intermediateCanonical
            · rw [resultEq] at absorbed
              simp only [Pattern.apply.injEq] at absorbed
              exact absurd absorbed.1 quoteNeDrop
          · rw [finishNormalizeReflectiveApply_of_ne_quote declaration
              isQuote] at absorbed
            simp only [Pattern.apply.injEq] at absorbed
            obtain ⟨constructorEq, argumentsEq⟩ := absorbed
            have argumentsShape : ∃ inner, arguments = [inner] := by
              cases arguments with
              | nil => cases argumentsEq
              | cons first rest =>
                  cases rest with
                  | nil => exact ⟨first, rfl⟩
                  | cons second tail => simp at argumentsEq
            obtain ⟨inner, rfl⟩ := argumentsShape
            subst constructorEq
            refine ⟨inner, ?_, ?_⟩
            · simp
              omega
            · exact (canonicalize_quote_drop declaration
                quoteNeDrop.symm inner).symm
      | collection collectionType elements rest =>
          cases rest with
          | some restName => simp [canonicalize] at absorbed
          | none =>
              by_cases isParallel :
                  collectionType = declaration.parallelCollection
              · subst isParallel
                obtain ⟨element, elementIn, elementCanonical⟩ :=
                  exists_member_of_parallel_collapse_apply declaration
                    absorbed (by simp)
                have elementBound : sizeOf element ≤ fuel := by
                  have := List.sizeOf_lt_of_mem elementIn
                  simp at bound
                  omega
                obtain ⟨smaller, smallerBound, smallerCanonical⟩ :=
                  exists_smaller_quote_collapse declaration quoteNeDrop
                    fuel element payload elementBound elementCanonical
                refine ⟨smaller, ?_, ?_⟩
                · have := List.sizeOf_lt_of_mem elementIn
                  simp at smallerBound ⊢
                  omega
                · rw [smallerCanonical]
                  exact canonicalize_quote_app_congr declaration
                    (by rw [elementCanonical, absorbed])
              · rw [canonicalize_collection_of_ne_parallel declaration
                  isParallel] at absorbed
                cases absorbed

/-- A quote application collapsing to a bound variable exposes a strictly
smaller representative in that canonical class.  The quote must have
absorbed a canonically drop-rooted sole argument; the general absorption
witness then supplies the descent. -/
theorem exists_smaller_of_quote_collapse_bvar
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop :
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    {arguments : List Pattern} {index : Nat}
    (collapsed : canonicalize declaration
        (.apply declaration.quoteConstructor arguments) = .bvar index) :
    ∃ smaller : Pattern,
      sizeOf smaller <
          sizeOf (Pattern.apply declaration.quoteConstructor arguments) ∧
        canonicalize declaration smaller = .bvar index := by
  have wholeCollapsed := collapsed
  rw [canonicalize_apply_eq_finish] at collapsed
  rcases finishNormalizeReflectiveApply_quote_cases declaration
      (arguments.map (canonicalize declaration)) with
    ⟨inner, argumentsEq, resultEq⟩ | resultEq
  · rw [resultEq] at collapsed
    subst inner
    cases arguments with
    | nil => cases argumentsEq
    | cons first rest =>
        cases rest with
        | nil =>
            have firstCanonical : canonicalize declaration first =
                .apply declaration.dropConstructor [.bvar index] := by
              simpa using argumentsEq
            obtain ⟨smaller, smallerBound, smallerCanonical⟩ :=
              exists_smaller_quote_collapse declaration quoteNeDrop
                (sizeOf first) first (.bvar index) (by rfl) firstCanonical
            exact ⟨smaller, by simpa using smallerBound,
              smallerCanonical.trans wholeCollapsed⟩
        | cons second tail =>
            simp only [List.map_cons, List.cons.injEq] at argumentsEq
            cases argumentsEq.2
  · rw [resultEq] at collapsed
    exact Pattern.noConfusion collapsed

/-- Every collapsing root whose canonical result is a bound variable admits
a strictly smaller representative with that same result.  Quote absorption
uses `exists_smaller_quote_collapse`; parallel collapse selects the unique
non-unit survivor. -/
theorem exists_smaller_of_collapsingRoot_bvar
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop :
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    {pattern : Pattern} {index : Nat}
    (collapsing : CollapsingRoot declaration pattern)
    (collapsed : canonicalize declaration pattern = .bvar index) :
    ∃ smaller : Pattern,
      sizeOf smaller < sizeOf pattern ∧
        canonicalize declaration smaller = .bvar index := by
  rcases collapsing with ⟨arguments, rfl⟩ | ⟨elements, rfl⟩
  · exact exists_smaller_of_quote_collapse_bvar declaration quoteNeDrop
      collapsed
  · exact exists_smaller_of_parallel_collapse_bvar declaration collapsed

/-! ## Positive and negative examples -/

private def exampleDeclaration : ReflectivePresentationDecl :=
  rhoReflectivePresentation.toReflectivePresentationDecl

-- Positive: a parallel with a canonically-unit sibling evaporates although
-- it is neither a Quote/Drop shell nor a singleton parallel.  This is the
-- shape outside the syntactic shell grammar.
#guard canonicalize exampleDeclaration
    (.collection .hashBag
      [.fvar "survivor", .apply "PZero" []] none) == .fvar "survivor"

-- Positive: bound-variable survivors are reachable and therefore cannot be
-- omitted from a total collapsing-root dispatcher.
#guard canonicalize exampleDeclaration
    (.collection .hashBag
      [.bvar 2, .apply "PZero" []] none) == .bvar 2

-- Negative: a bare bound variable is already rigid, not a collapsing root.
example : ¬ CollapsingRoot exampleDeclaration (.bvar 2) := by
  simp [CollapsingRoot]

-- Positive: mixed nesting — quote/drop absorption around a parallel that
-- flattens away unit junk.
#guard canonicalize exampleDeclaration
    (.apply "NQuote"
      [.apply "PDrop"
        [.collection .hashBag
          [.collection .hashBag [.fvar "survivor"] none,
            .apply "PZero" []] none]]) == .fvar "survivor"

-- Positive (absorption lane): the quote's argument is not syntactically a
-- drop application, yet after its parallel collapses the quote absorbs.
-- This is the shape the absorption witness recursion resolves.
#guard canonicalize exampleDeclaration
    (.apply "NQuote"
      [.collection .hashBag
        [.apply "PDrop" [.fvar "y"], .apply "PZero" []] none]) ==
  .fvar "y"

-- Negative: a bare quote context does not evaporate on a variable...
example : canonicalize exampleDeclaration
    (.apply "NQuote" [.fvar "x"]) ≠ .fvar "x" := by
  intro collapse
  exact Pattern.noConfusion collapse

-- ...and indeed the conclusion fails there for a drop filler, showing the
-- collapse hypothesis cannot be dropped.
example : canonicalize exampleDeclaration
      (.apply "NQuote" [.apply "PDrop" [.fvar "y"]]) ≠
    canonicalize exampleDeclaration (.apply "PDrop" [.fvar "y"]) := by
  intro collapse
  exact Pattern.noConfusion collapse

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
