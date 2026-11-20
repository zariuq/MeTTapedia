import Mathlib.Data.Finset.Max
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.List.Perm.Basic

/-!
# One ordered representative of each CMR pattern-assignment bag

Profile: one occurrence-bag store and ambient rules. This combinatorial
component chooses no firing discipline or guard timing. Within each group of
identical source patterns, reads rise non-strictly and distinct takes rise
strictly. Assignments to different patterns remain distinguished.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.PatternAssignmentOrder

universe uPattern uOccurrence

variable {Pattern : Type uPattern} {Occurrence : Type uOccurrence}
  [DecidableEq Pattern] [LinearOrder Occurrence]

def Ordered (pairs : List (Pattern × Occurrence)) : Prop :=
  pairs.Pairwise fun first second => first.1 = second.1 → first.2 ≤ second.2

def StrictlyOrdered (pairs : List (Pattern × Occurrence)) : Prop :=
  pairs.Pairwise fun first second => first.1 = second.1 → first.2 < second.2

def fibre (bag : Multiset (Pattern × Occurrence)) (pattern : Pattern) : Multiset Occurrence :=
  (bag.filter fun pair => pair.1 = pattern).map Prod.snd

theorem fibre_count (bag : Multiset (Pattern × Occurrence)) (pattern : Pattern) (o : Occurrence) :
    (fibre bag pattern).count o = bag.count (pattern, o) := by
  induction bag using Multiset.induction_on with
  | empty => simp [fibre]
  | cons pair rest ih =>
    obtain ⟨p, row⟩ := pair
    by_cases hp : p = pattern
    · subst p
      by_cases ho : row = o
      · subst row; simp [fibre] at ih ⊢; exact ih
      · simp [fibre, Ne.symm ho] at ih ⊢; exact ih
    · simp [fibre, hp, Ne.symm hp] at ih ⊢; exact ih

theorem pairs_eq_of_fibres (patterns : List Pattern)
    (first second : Multiset (Pattern × Occurrence))
    (firstSupply : first.map Prod.fst = (patterns : Multiset Pattern))
    (secondSupply : second.map Prod.fst = (patterns : Multiset Pattern))
    (fibres : ∀ pattern ∈ patterns, fibre first pattern = fibre second pattern) : first = second := by
  apply Multiset.ext.mpr
  rintro ⟨pattern, o⟩
  by_cases member : pattern ∈ patterns
  · rw [← fibre_count first pattern o, ← fibre_count second pattern o, fibres pattern member]
  · have outside : ∀ bag : Multiset (Pattern × Occurrence),
        bag.map Prod.fst = (patterns : Multiset Pattern) → (pattern, o) ∉ bag := by
      intro bag supply inside
      have image : pattern ∈ bag.map Prod.fst := Multiset.mem_map.mpr ⟨(pattern, o), inside, rfl⟩
      rw [supply] at image
      exact member image
    rw [Multiset.count_eq_zero.mpr (outside first firstSupply),
      Multiset.count_eq_zero.mpr (outside second secondSupply)]

def values (pattern : Pattern) (bag : Multiset (Pattern × Occurrence)) : Finset Occurrence :=
  ((bag.filter fun pair => pair.1 = pattern).map Prod.snd).toFinset

theorem mem_values (pattern : Pattern) (bag : Multiset (Pattern × Occurrence)) (o : Occurrence) :
    o ∈ values pattern bag ↔ (pattern, o) ∈ bag := by
  simp only [values, Multiset.mem_toFinset, Multiset.mem_map, Multiset.mem_filter]
  constructor
  · rintro ⟨⟨p, found⟩, ⟨member, samePattern⟩, sameOccurrence⟩
    change p = pattern at samePattern
    change found = o at sameOccurrence
    subst p
    subst found
    exact member
  · intro member
    exact ⟨(pattern, o), ⟨member, rfl⟩, rfl⟩

def pick (pattern : Pattern) (bag : Multiset (Pattern × Occurrence)) : Option Occurrence :=
  if nonempty : (values pattern bag).Nonempty then some ((values pattern bag).min' nonempty) else none

theorem pick_exists {pattern : Pattern} {bag : Multiset (Pattern × Occurrence)}
    {o : Occurrence} (member : (pattern, o) ∈ bag) : ∃ chosen, pick pattern bag = some chosen := by
  have nonempty : (values pattern bag).Nonempty := ⟨o, (mem_values _ _ _).mpr member⟩
  exact ⟨_, dif_pos nonempty⟩

theorem pick_spec {pattern : Pattern} {bag : Multiset (Pattern × Occurrence)} {o : Occurrence}
    (picked : pick pattern bag = some o) :
    (pattern, o) ∈ bag ∧ ∀ other, (pattern, other) ∈ bag → o ≤ other := by
  unfold pick at picked
  split at picked
  · rename_i nonempty
    have same := Option.some.inj picked
    subst o
    exact ⟨(mem_values _ _ _).mp (Finset.min'_mem _ nonempty),
      fun other member => Finset.min'_le _ other ((mem_values _ _ _).mpr member)⟩
  · cases picked

/-- Consume one least occurrence for the next source pattern. Equal read
occurrences are retained as separate entries of the remaining multiset. -/
def normalize : List Pattern → Multiset (Pattern × Occurrence) → Option (List (Pattern × Occurrence))
  | [], bag => if bag = 0 then some [] else none
  | pattern :: rest, bag =>
    match pick pattern bag with
    | none => none
    | some o => (normalize rest (bag.erase (pattern, o))).map ((pattern, o) :: ·)

theorem normalize_complete : ∀ (patterns : List Pattern) (bag : Multiset (Pattern × Occurrence)),
    bag.map Prod.fst = (patterns : Multiset Pattern) →
    ∃ pairs, normalize patterns bag = some pairs ∧
      (pairs : Multiset (Pattern × Occurrence)) = bag ∧ pairs.map Prod.fst = patterns ∧ Ordered pairs := by
  intro patterns
  induction patterns with
  | nil =>
    intro bag supply
    have empty : bag = 0 := Multiset.map_eq_zero.mp supply
    subst bag
    exact ⟨[], by simp [normalize], rfl, rfl, List.Pairwise.nil⟩
  | cons pattern rest ih =>
    intro bag supply
    have inMap : pattern ∈ bag.map Prod.fst := by rw [supply]; simp
    obtain ⟨pair, member, samePattern⟩ := Multiset.mem_map.mp inMap
    have available : (pattern, pair.2) ∈ bag := by
      simpa only [← samePattern] using member
    obtain ⟨o, picked⟩ := pick_exists available
    obtain ⟨chosenMember, least⟩ := pick_spec picked
    have tailSupply : (bag.erase (pattern, o)).map Prod.fst = (rest : Multiset Pattern) := by
      have mapped := congrArg (Multiset.map Prod.fst) (Multiset.cons_erase chosenMember)
      rw [Multiset.map_cons, supply] at mapped
      exact (Multiset.cons_inj_right pattern).mp mapped
    obtain ⟨pairs, run, content, source, ordered⟩ := ih _ tailSupply
    refine ⟨(pattern, o) :: pairs, ?_, ?_, by simp [source], ?_⟩
    · simp [normalize, picked, run]
    · change (pattern, o) ::ₘ (pairs : Multiset (Pattern × Occurrence)) = bag
      rw [content]
      exact Multiset.cons_erase chosenMember
    · apply List.pairwise_cons.mpr
      refine ⟨?_, ordered⟩
      intro later inPairs same
      have inTail : later ∈ bag.erase (pattern, o) := by
        rw [← content]
        exact inPairs
      have inBag := Multiset.mem_of_mem_erase inTail
      have samePair : (pattern, later.2) = later := by
        exact Prod.ext same rfl
      exact least later.2 (samePair ▸ inBag)

omit [DecidableEq Pattern] in
theorem head_le {head pair : Pattern × Occurrence} {rest : List (Pattern × Occurrence)}
    (ordered : Ordered (head :: rest)) (member : pair ∈ head :: rest)
    (same : head.1 = pair.1) : head.2 ≤ pair.2 := by
  rcases List.mem_cons.mp member with rfl | later
  · exact le_rfl
  · exact (List.pairwise_cons.mp ordered).1 pair later same

omit [DecidableEq Pattern] in
/-- Equal pair bags and equal source-pattern positions have only one
group-ordered representation. -/
theorem ordered_unique : ∀ (first second : List (Pattern × Occurrence)),
    first.map Prod.fst = second.map Prod.fst → first.Perm second →
    Ordered first → Ordered second → first = second := by
  intro first
  induction first with
  | nil =>
    intro second _ perm _ _
    exact perm.nil_eq
  | cons head rest ih =>
    intro second sources perm orderedFirst orderedSecond
    cases second with
    | nil => cases sources
    | cons other later =>
      have pattern := (List.cons.inj sources).1
      have below := head_le orderedFirst (perm.mem_iff.mpr List.mem_cons_self) pattern
      have above := head_le orderedSecond (perm.mem_iff.mp List.mem_cons_self) pattern.symm
      have same : head = other := Prod.ext pattern (le_antisymm below above)
      subst other
      exact congrArg (head :: ·) (ih later (List.cons.inj sources).2
        (List.Perm.cons_inv perm) (List.pairwise_cons.mp orderedFirst).2
        (List.pairwise_cons.mp orderedSecond).2)

omit [DecidableEq Pattern] in
theorem normalize_unique {patterns : List Pattern} {bag : Multiset (Pattern × Occurrence)}
    {pairs other : List (Pattern × Occurrence)}
    (content : (pairs : Multiset (Pattern × Occurrence)) = bag)
    (source : pairs.map Prod.fst = patterns) (ordered : Ordered pairs)
    (otherContent : (other : Multiset (Pattern × Occurrence)) = bag)
    (otherSource : other.map Prod.fst = patterns) (otherOrdered : Ordered other) : pairs = other :=
  ordered_unique pairs other (source.trans otherSource.symm)
    (Multiset.coe_eq_coe.mp (content.trans otherContent.symm)) ordered otherOrdered

omit [DecidableEq Pattern] in
/-- Distinct take occurrences strengthen the same nondecreasing normal
form to strict increase within each identical-pattern group. -/
theorem strict_of_distinct : ∀ (pairs : List (Pattern × Occurrence)),
    Ordered pairs → (pairs.map Prod.snd).Nodup → StrictlyOrdered pairs := by
  intro pairs
  induction pairs with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons head rest ih =>
    intro ordered distinct
    obtain ⟨headOrder, tailOrder⟩ := List.pairwise_cons.mp ordered
    obtain ⟨notLater, tailDistinct⟩ := List.nodup_cons.mp distinct
    refine List.pairwise_cons.mpr ⟨?_, ih tailOrder tailDistinct⟩
    intro later member same
    apply lt_of_le_of_ne (headOrder later member same)
    intro equal
    exact notLater (List.mem_map.mpr ⟨later, member, equal.symm⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.PatternAssignmentOrder
