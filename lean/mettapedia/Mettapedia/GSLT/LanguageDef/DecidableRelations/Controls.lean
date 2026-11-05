import Mettapedia.GSLT.LanguageDef.DecidableRelations.Observers

/-!
# Controls: complemented relations, positive and negative

A small signature (two spaces, two claims and a placement) and the language holding its equality and disequality
rules:
- different placements are derived unequal and not equal; the same placement is derived equal and not unequal;
- **privacy is needed**: one extra rule `Unequal(x, x) ~> Yes` makes a term both equal and unequal to itself, so the
  pair is no longer complemented;
- **a closed fact store**: an edge stored is answered, an edge not stored is answered by the complement ("that's all"),
  and never both;
- **non-membership in a closed bag**, the transform calculus's sealed-space check: in the bag `{thm:A, pub:B}`,
  `thm:B` is derived a non-member and not a member, and `thm:A` a member and not a non-member;
- **keyed indexes**:
  - an index keyed injectively misses `thm:B`, as the language derives;
  - an index keyed by head constructors contains a key of `thm:B`, so it does not host equality and must decline
    (`headIndex_not_hosting`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-- Two spaces, two claims and a placement of a claim in a space. -/
def signature : List (String × Nat) := [("Thm", 0), ("Pub", 0), ("A", 0), ("B", 0), ("At", 2)]

/-- The language of the signature's equality and disequality. -/
def language : LanguageDef := ⟨"Equality", [], [], [], disequalityRules signature⟩

theorem rules : ∀ rule ∈ disequalityRules signature, rule ∈ language.rewrites := fun _ member => member

theorem private_ : Private language signature := fun _ member notGenerated => absurd member notGenerated

theorem names : (signature.map Prod.fst).Nodup := by decide

def thm : Pattern := .apply "Thm" []
def pub : Pattern := .apply "Pub" []
def claimA : Pattern := .apply "A" []
def claimB : Pattern := .apply "B" []
def at_ (space claim : Pattern) : Pattern := .apply "At" [space, claim]

theorem over_constant {name : String} (member : (name, 0) ∈ signature) : TermOf signature (.apply name []) :=
  .apply member (by simp)

theorem over_at {space claim : Pattern} (overSpace : TermOf signature space)
    (overClaim : TermOf signature claim) : TermOf signature (at_ space claim) :=
  .apply (by simp [signature]) (by
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact overSpace
    · exact overClaim)

theorem over_thm : TermOf signature thm := over_constant (by simp [signature])
theorem over_pub : TermOf signature pub := over_constant (by simp [signature])
theorem over_a : TermOf signature claimA := over_constant (by simp [signature])

/-- Positive: different placements are derived unequal. -/
theorem unequal_placements :
    Derives RelationEnv.empty language unequalJudgment [at_ thm claimA, at_ pub claimA] :=
  (derives_unequal_iff rules private_ names (over_at over_thm over_a) (over_at over_pub over_a)).mpr
    (by simp [at_, thm, pub])

/-- Negative: different placements are not derived equal. -/
theorem not_equal_placements :
    ¬ Derives RelationEnv.empty language equalJudgment [at_ thm claimA, at_ pub claimA] := by
  rw [derives_equal_iff rules private_]
  simp [at_, thm, pub]

/-- Positive: a placement is derived equal to itself. -/
theorem equal_same : Derives RelationEnv.empty language equalJudgment [at_ thm claimA, at_ thm claimA] :=
  (derives_equal_iff rules private_).mpr rfl

/-- Negative: a placement is not derived unequal to itself. -/
theorem not_unequal_same : ¬ Derives RelationEnv.empty language unequalJudgment [at_ thm claimA, at_ thm claimA] := by
  rw [derives_unequal_iff rules private_ names (over_at over_thm over_a) (over_at over_thm over_a)]
  simp

/-! ## Privacy is needed -/

/-- One extra rule: `Unequal(x, x) ~> Yes`. -/
def leak : RewriteRule := ⟨"Leak", [], [], .apply unequalJudgment [.fvar "x", .fvar "x"], yes, none⟩

/-- The language with the extra rule. -/
def leaky : LanguageDef := ⟨"Leaky", [], [], [], disequalityRules signature ++ [leak]⟩

/-- **With the extra rule a claim is both equal and unequal to itself.** -/
theorem leaky_both :
    Derives RelationEnv.empty leaky equalJudgment [claimA, claimA] ∧
      Derives RelationEnv.empty leaky unequalJudgment [claimA, claimA] :=
  ⟨stepValid_of_rule (List.mem_append_left _ (List.mem_cons_self ..)) (matchPattern_equal_self claimA) (.nil _) rfl,
    stepValid_of_rule (List.mem_append_right _ (List.mem_singleton_self _))
      (matchPattern_repeated_self unequalJudgment claimA) (.nil _) rfl⟩

/-- So the pair is not complemented there. -/
theorem leaky_not_complemented :
    ¬ Complemented (fun pair : Pattern × Pattern => Derives RelationEnv.empty leaky equalJudgment [pair.1, pair.2])
      (fun pair => Derives RelationEnv.empty leaky unequalJudgment [pair.1, pair.2])
      (fun pair => TermOf signature pair.1 ∧ TermOf signature pair.2) := by
  intro complemented
  exact complemented.disjoint (claimA, claimA) ⟨over_a, over_a⟩ leaky_both.1 leaky_both.2

/-! ## A closed fact store -/

/-- One edge, from `A` to `B`, and that's all. -/
def edges : RelationEnv := factStore "Edge" "NoEdge" [[claimA, claimB]]

theorem firstOrder_constant (name : String) : FirstOrder (.apply name []) := .apply (by simp)

theorem firstOrder_pair (first second : String) :
    ∀ argument ∈ [Pattern.apply first [], Pattern.apply second []], FirstOrder argument := by
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact firstOrder_constant _

/-- Positive: the stored edge is answered. -/
theorem edge_stored : Answers edges language "Edge" [claimA, claimB] :=
  (factStore_answers_iff (by decide) (firstOrder_pair "A" "B")).mpr (by simp [claimA, claimB])

/-- That's all: the edge back is answered by the complement. -/
theorem no_edge_back : Answers edges language "NoEdge" [claimB, claimA] :=
  (factStore_answers_complement_iff (by decide) (by decide) (firstOrder_pair "B" "A")).mpr (by simp [claimA, claimB])

/-- Negative: the stored edge is not answered by the complement. -/
theorem stored_not_complement : ¬ Answers edges language "NoEdge" [claimA, claimB] := fun answered =>
  (factStore_answers_complement_iff (by decide) (by decide) (firstOrder_pair "A" "B")).mp answered (by simp [claimA, claimB])

/-! ## Non-membership in a closed bag -/

/-- The language of membership and non-membership over bags of placements. -/
def placements : LanguageDef := ⟨"Placements", [], [], [], membershipRules signature .hashBag⟩

theorem placements_rules : ∀ rule ∈ membershipRules signature .hashBag, rule ∈ placements.rewrites :=
  fun _ member => member

theorem placements_private : MembershipPrivate placements signature .hashBag :=
  fun _ member notGenerated => absurd member notGenerated

theorem over_b : TermOf signature claimB := over_constant (by simp [signature])

/-- The bag `{thm:A, pub:B}`. -/
def store : List Pattern := [at_ thm claimA, at_ pub claimB]

theorem store_over : ∀ value ∈ store, TermOf signature value := by
  intro value member
  simp only [store, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact over_at over_thm over_a
  · exact over_at over_pub over_b

/-- Positive: `thm:B` is derived a non-member of the bag. -/
theorem nonMember_thmB : Derives RelationEnv.empty placements nonMemberJudgment
    [at_ thm claimB, .collection .hashBag store none] :=
  (derives_nonMember_iff placements_rules placements_private names (by decide) (over_at over_thm over_b) store_over).mpr
    (by simp [store, at_, thm, pub, claimA, claimB])

/-- Negative: `thm:B` is not derived a member. -/
theorem not_member_thmB : ¬ Derives RelationEnv.empty placements memberJudgment
    [at_ thm claimB, .collection .hashBag store none] := by
  rw [derives_member_iff placements_rules placements_private (by decide)]
  simp [store, at_, thm, pub, claimA, claimB]

/-- Positive: `thm:A` is derived a member. -/
theorem member_thmA : Derives RelationEnv.empty placements memberJudgment
    [at_ thm claimA, .collection .hashBag store none] :=
  (derives_member_iff placements_rules placements_private (by decide)).mpr (by simp [store])

/-- Negative: `thm:A` is not derived a non-member. -/
theorem not_nonMember_thmA : ¬ Derives RelationEnv.empty placements nonMemberJudgment
    [at_ thm claimA, .collection .hashBag store none] := by
  rw [derives_nonMember_iff placements_rules placements_private names (by decide) (over_at over_thm over_a) store_over]
  simp [store]

/-! ## Keyed indexes: hosting and declining -/

/-- Positive: an index keyed injectively misses `thm:B`, as the language derives. -/
theorem identityIndex_misses : indexContains id store (at_ thm claimB) = false :=
  (index_misses_iff_derives_nonMember id Function.injective_id placements_rules placements_private names (by decide)
    (over_at over_thm over_b) store_over).mpr nonMember_thmB

/-- The head constructor of a pattern: a key that forgets the arguments. -/
def headKey : Pattern → String
  | .apply constructor _ => constructor
  | _ => ""

/-- Keyed by head constructors, the index contains a key of `thm:B` in `{thm:A, pub:B}`. -/
theorem headIndex_contains : indexContains headKey store (at_ thm claimB) = true := by
  simp [indexContains, headKey, store, at_]

/-- **Negative: head keys are not a canonical form for equality**, so that index does not host it and must decline. -/
theorem headIndex_not_hosting :
    ¬ ∀ stored element, indexContains headKey stored element = true ↔ ∃ x ∈ stored, x = element := by
  intro hosts
  have present := (hosts store (at_ thm claimB)).mp headIndex_contains
  simp [store, at_, thm, pub, claimA, claimB] at present

end Mettapedia.GSLT.LanguageDef.DecidableRelations.Controls
