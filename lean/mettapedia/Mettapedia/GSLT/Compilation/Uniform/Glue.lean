import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Insert
import Mettapedia.GSLT.Compilation.Uniform.DemandTransformation

/-!
# Gluing two parts of a least fixed point through what each offers the other

A relation given by rules is the least fixed point of the map that fires every rule once. Split the rules into two
parts, each run by its own route. Given what the other route offers, a route computes the least element closed under
its own rules, their premises answered by itself and by the offer (`relative`). The two routes, each asked again with
what the other found until nothing new appears, compute exactly the least fixed point of all the rules
(`lfp_glued`). So do rounds in which each route does any amount of work between one firing and its whole closure
relative to what was known (`rounds_reach`, for rules that use finitely many premises at a time). Nothing is lost at the
seam, and nothing is invented; a premise of one part that a rule of the other
answers, in either direction and through any number of crossings, is covered.

Asking each other is necessary. The least fixed points of the two parts taken apart can miss what the rules give
together (`Controls.apart_misses`, beside `Controls.glued_finds`).

For clauses: the least model of a program is the least fixed point of firing its clauses once (`derives_iff_lfp`),
firing a program split in two is firing each part (`fire_append`), so the facts of the whole program are the two parts
glued (`derives_glued`). A route that runs one part, its questions to the other part answered by the other route
through a bridge clause, computes `relative` of its part, together with what it was offered (`derives_bridged`). Controls: `Controls.whole_derives`, `Controls.first_alone_misses`,
`Controls.second_alone_misses`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.Glue

open OrderHom

variable {α : Type*} [CompleteLattice α]

/-- A part whose premises are also answered by an offer. -/
def withOffer (f : α →o α) (offer : α) : α →o α :=
  ⟨fun known => f (known ⊔ offer), fun _ _ below => f.mono (sup_le_sup_right below offer)⟩

/-- **One part, relative to an offer**: the least element closed under the part, its premises answered by itself and
the offer. -/
def relative (f : α →o α) (offer : α) : α := lfp (withOffer f offer)

theorem relative_fixed (f : α →o α) (offer : α) : f (relative f offer ⊔ offer) = relative f offer :=
  map_lfp (withOffer f offer)

theorem relative_mono (f : α →o α) : Monotone (relative f) := by
  intro smaller larger below
  apply lfp_le (withOffer f smaller)
  calc f (relative f larger ⊔ smaller) ≤ f (relative f larger ⊔ larger) := f.mono (sup_le_sup_left below _)
    _ = relative f larger := relative_fixed f larger

/-- **The glued map**: each part relative to what is known so far. -/
def glued (f g : α →o α) : α →o α :=
  ⟨fun known => relative f known ⊔ relative g known,
    fun _ _ below => sup_le_sup (relative_mono f below) (relative_mono g below)⟩

theorem sup_apply (f g : α →o α) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl

/-- **A part relative to an offer, with the offer**: the least fixed point of the part beside a constant offer. -/
theorem lfp_sup_const (f : α →o α) (offer : α) :
    lfp (f ⊔ OrderHom.const α offer) = relative f offer ⊔ offer := by
  have fixedOffer : f (relative f offer ⊔ offer) = relative f offer := relative_fixed f offer
  apply le_antisymm
  · apply lfp_le (f ⊔ OrderHom.const α offer)
    show f (relative f offer ⊔ offer) ⊔ offer ≤ relative f offer ⊔ offer
    rw [fixedOffer]
  · have fixed : f (lfp (f ⊔ OrderHom.const α offer)) ⊔ offer = lfp (f ⊔ OrderHom.const α offer) :=
      map_lfp (f ⊔ OrderHom.const α offer)
    have offerBelow : offer ≤ lfp (f ⊔ OrderHom.const α offer) := le_sup_right.trans fixed.le
    refine sup_le (lfp_le (withOffer f offer) ?_) offerBelow
    show f (lfp (f ⊔ OrderHom.const α offer) ⊔ offer) ≤ lfp (f ⊔ OrderHom.const α offer)
    rw [sup_eq_left.mpr offerBelow]
    exact le_sup_left.trans fixed.le

/-- What the glued map gives at the least fixed point of all the rules stays below it. -/
theorem glued_lfp_le (f g : α →o α) : glued f g (lfp (f ⊔ g)) ≤ lfp (f ⊔ g) := by
  have fixed : f (lfp (f ⊔ g)) ⊔ g (lfp (f ⊔ g)) = lfp (f ⊔ g) := map_lfp (f ⊔ g)
  refine sup_le (lfp_le (withOffer f _) ?_) (lfp_le (withOffer g _) ?_)
  · show f (lfp (f ⊔ g) ⊔ lfp (f ⊔ g)) ≤ lfp (f ⊔ g)
    rw [sup_idem]
    exact le_sup_left.trans fixed.le
  · show g (lfp (f ⊔ g) ⊔ lfp (f ⊔ g)) ≤ lfp (f ⊔ g)
    rw [sup_idem]
    exact le_sup_right.trans fixed.le

/-- **Rounds with any work in between reach exactly the least fixed point**: when each round finds at least one
firing of every rule on what was known, and at most each part's closure relative to what was known, the rounds
together reach the least fixed point of all the rules, for rules that use finitely many premises at a time
(`ωScottContinuous`). A round may so run each route for any budget between one firing and its full closure. -/
theorem rounds_reach (f g : α →o α) (continuous : OmegaCompletePartialOrder.ωScottContinuous (f ⊔ g)) (known : ℕ → α)
    (start : known 0 = ⊥) (atLeast : ∀ n, (f ⊔ g) (known n) ≤ known (n + 1))
    (atMost : ∀ n, known (n + 1) ≤ glued f g (known n)) :
    ⨆ n, known n = lfp (f ⊔ g) := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    induction n with
    | zero => rw [start]; exact bot_le
    | succ n ih => exact (atMost n).trans ((glued f g).mono ih |>.trans (glued_lfp_le f g))
  · rw [fixedPoints.lfp_eq_sSup_iterate (f ⊔ g) continuous]
    refine iSup_le fun n => le_iSup_of_le n ?_
    induction n with
    | zero => exact bot_le
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact ((f ⊔ g).mono ih).trans (atLeast n)

/-- **Gluing loses nothing and invents nothing**: the two parts asked of each other compute the least fixed point of
all the rules. -/
theorem lfp_glued (f g : α →o α) : lfp (glued f g) = lfp (f ⊔ g) := by
  apply le_antisymm
  · exact lfp_le (glued f g) (glued_lfp_le f g)
  · apply lfp_le (f ⊔ g)
    have fixed : relative f (lfp (glued f g)) ⊔ relative g (lfp (glued f g)) = lfp (glued f g) :=
      map_lfp (glued f g)
    rw [sup_apply]
    refine sup_le ?_ ?_
    · calc f (lfp (glued f g)) ≤ f (relative f (lfp (glued f g)) ⊔ lfp (glued f g)) := f.mono le_sup_right
        _ = relative f (lfp (glued f g)) := relative_fixed f _
        _ ≤ lfp (glued f g) := le_sup_left.trans fixed.le
    · calc g (lfp (glued f g)) ≤ g (relative g (lfp (glued f g)) ⊔ lfp (glued f g)) := g.mono le_sup_right
        _ = relative g (lfp (glued f g)) := relative_fixed g _
        _ ≤ lfp (glued f g) := le_sup_right.trans fixed.le

section Clauses

open Mettapedia.GSLT.Compilation.Uniform.DemandTransformation (Goal Clause goalHolds DerivesAt Derives goalHolds_mono
  derives_of_clause)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.ComputedConditions (Relations)
open RuleSyntax.Presentation.Schematic
open NamesOnTheStep (Expr)

/-- **One firing of the clauses**: the facts — relation, input, output — each clause gives at an instance whose goals
hold among the known facts. -/
def fire (R : Relations) (program : List Clause) : Set (ℕ × Expr × Expr) →o Set (ℕ × Expr × Expr) where
  toFun known := {fact | ∃ c ∈ program, c.relation = fact.1 ∧ ∃ θ : ℕ → Expr, inst θ c.input = fact.2.1 ∧
    inst θ c.output = fact.2.2 ∧ ∀ g ∈ c.body, goalHolds R (fun r x y => (r, x, y) ∈ known) θ g}
  monotone' _ _ below _ fired := by
    obtain ⟨c, member, relationIs, θ, inputIs, outputIs, goals⟩ := fired
    exact ⟨c, member, relationIs, θ, inputIs, outputIs,
      fun g inside => goalHolds_mono (fun _ _ _ held => below held) (goals g inside)⟩

/-- **The least model is the least fixed point of firing the clauses.** -/
theorem derives_iff_lfp (R : Relations) (program : List Clause) (relation : ℕ) (x y : Expr) :
    Derives R program relation x y ↔ (relation, x, y) ∈ lfp (fire R program) := by
  constructor
  · rintro ⟨depth, derived⟩
    induction depth generalizing relation x y with
    | zero => exact derived.elim
    | succ depth ih =>
        obtain ⟨c, member, relationIs, θ, inputIs, outputIs, goals⟩ := derived
        rw [← map_lfp (fire R program)]
        exact ⟨c, member, relationIs, θ, inputIs, outputIs,
          fun g inside => goalHolds_mono (fun _ _ _ held => ih _ _ _ held) (goals g inside)⟩
  · intro inside
    have prefixed : fire R program {fact | Derives R program fact.1 fact.2.1 fact.2.2} ≤
        {fact | Derives R program fact.1 fact.2.1 fact.2.2} := by
      rintro ⟨relation', x', y'⟩ ⟨c, member, relationIs, θ, inputIs, outputIs, goals⟩
      have derived := derives_of_clause member θ fun g inside => goals g inside
      simp only at relationIs inputIs outputIs
      rw [relationIs, inputIs, outputIs] at derived
      exact derived
    exact lfp_le (fire R program) prefixed inside

/-- Firing a program split in two is firing each part. -/
theorem fire_append (R : Relations) (first second : List Clause) :
    fire R (first ++ second) = fire R first ⊔ fire R second := by
  refine OrderHom.ext _ _ (funext fun known => Set.ext fun fact => ?_)
  constructor
  · rintro ⟨c, member, rest⟩
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact Or.inl ⟨c, inFirst, rest⟩
    · exact Or.inr ⟨c, inSecond, rest⟩
  · rintro (⟨c, member, rest⟩ | ⟨c, member, rest⟩)
    · exact ⟨c, List.mem_append_left _ member, rest⟩
    · exact ⟨c, List.mem_append_right _ member, rest⟩

/-- **A program split in two is computed by gluing its parts**: a fact of the whole program is a fact of the two
parts, each run relative to what the other offers. -/
theorem derives_glued (R : Relations) (first second : List Clause) (relation : ℕ) (x y : Expr) :
    Derives R (first ++ second) relation x y ↔ (relation, x, y) ∈ lfp (glued (fire R first) (fire R second)) := by
  rw [derives_iff_lfp, fire_append, lfp_glued]

/-- **A bridge to another route**: the relation also holds where the other route, asked by a query, answers. -/
def bridge (relation route : ℕ) : Clause :=
  { relation, input := .var 0, output := .var 1, body := [.query { name := route, arguments := [.var 0], value := .var 1 }] }

/-- What the other route offers through a bridge. -/
def offered (R : Relations) (relation route : ℕ) : Set (ℕ × Expr × Expr) :=
  {fact | fact.1 = relation ∧ R route [fact.2.1] fact.2.2}

theorem fire_bridge (R : Relations) (relation route : ℕ) :
    fire R [bridge relation route] = OrderHom.const _ (offered R relation route) := by
  refine OrderHom.ext _ _ (funext fun known => Set.ext fun fact => ?_)
  obtain ⟨r, x, y⟩ := fact
  constructor
  · rintro ⟨c, member, relationIs, θ, inputIs, outputIs, goals⟩
    rw [List.mem_singleton] at member
    subst member
    have asked := goals _ List.mem_cons_self
    simp only [goalHolds, List.map_cons, List.map_nil, DemandTransformation.inst_unknown] at asked
    simp only [bridge, DemandTransformation.inst_unknown] at relationIs inputIs outputIs
    refine ⟨relationIs.symm, ?_⟩
    rw [← inputIs, ← outputIs]
    exact asked
  · rintro ⟨relationIs, answered⟩
    refine ⟨bridge relation route, List.mem_singleton_self _, relationIs.symm,
      fun index => if index = 0 then x else y, rfl, rfl, fun g inside => ?_⟩
    simp only [bridge, List.mem_cons, List.not_mem_nil, or_false] at inside
    subst inside
    simpa [goalHolds] using answered

/-- **A route that bridges to the other route computes its part relative to what the other offers**, together with
the offer. -/
theorem derives_bridged (R : Relations) (part : List Clause) (relation route : ℕ) (r : ℕ) (x y : Expr) :
    Derives R (part ++ [bridge relation route]) r x y ↔
      (r, x, y) ∈ relative (fire R part) (offered R relation route) ⊔ offered R relation route := by
  rw [derives_iff_lfp, fire_append, fire_bridge, lfp_sup_const]

end Clauses

namespace Controls

/-- A part that starts at `0` and steps from an even number to the next. -/
def fromEven : Set ℕ →o Set ℕ where
  toFun known := {n | n = 0 ∨ ∃ m ∈ known, m % 2 = 0 ∧ n = m + 1}
  monotone' _ _ below n inside := by
    rcases inside with rfl | ⟨m, member, even, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨m, below member, even, rfl⟩

/-- A part that steps from an odd number to the next. -/
def fromOdd : Set ℕ →o Set ℕ where
  toFun known := {n | ∃ m ∈ known, m % 2 = 1 ∧ n = m + 1}
  monotone' _ _ below _ inside := by
    obtain ⟨m, member, odd, rfl⟩ := inside
    exact ⟨m, below member, odd, rfl⟩

/-- **Positive**: together, the two parts reach every number. -/
theorem together_all : lfp (fromEven ⊔ fromOdd) = Set.univ := by
  refine Set.eq_univ_of_forall fun n => ?_
  induction n with
  | zero =>
      rw [← map_lfp (fromEven ⊔ fromOdd)]
      exact Or.inl (Or.inl rfl)
  | succ n ih =>
      rw [← map_lfp (fromEven ⊔ fromOdd)]
      rcases Nat.mod_two_eq_zero_or_one n with even | odd
      · exact Or.inl (Or.inr ⟨n, ih, even, rfl⟩)
      · exact Or.inr ⟨n, ih, odd, rfl⟩

/-- **Positive**: glued, the two parts reach `2`, which needs a step of each. -/
theorem glued_finds : 2 ∈ lfp (glued fromEven fromOdd) := by
  rw [lfp_glued, together_all]
  trivial

theorem fromEven_apart : lfp fromEven ≤ {0, 1} := by
  apply lfp_le fromEven
  rintro n (rfl | ⟨m, member, even, rfl⟩)
  · exact Or.inl rfl
  · rcases member with rfl | rfl
    · exact Or.inr rfl
    · exact absurd even (by decide)

theorem fromOdd_apart : lfp fromOdd ≤ ∅ := by
  apply lfp_le fromOdd
  rintro n ⟨m, member, -, -⟩
  exact member

/-- **Negative**: taken apart, the least fixed points of the two parts miss `2`. -/
theorem apart_misses : 2 ∉ lfp fromEven ⊔ lfp fromOdd := by
  rintro (inEven | inOdd)
  · rcases fromEven_apart inEven with same | same <;> exact absurd same (by decide)
  · exact fromOdd_apart inOdd


open Mettapedia.GSLT.Compilation.Uniform.DemandTransformation (Clause Derives derives_cases)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RootRewritesOnTheStep (symTerm)

/-- The first part: the fact that relation `0` relates `1` to `2`. -/
def first : List Clause := [{ relation := 0, input := symTerm 1, output := symTerm 2, body := [] }]

/-- The second part: relation `0` relates `1` to `3` where it relates `1` to `2`. -/
def second : List Clause :=
  [{ relation := 0, input := symTerm 1, output := symTerm 3, body := [.ask 0 (symTerm 1) (symTerm 2)] }]

/-- **Positive**: the whole program relates `1` to `3`, through a fact of each part. -/
theorem whole_derives : Derives (fun _ _ _ => False) (first ++ second) 0 (.sym 1) (.sym 3) := by
  have firstFact : Derives (fun _ _ _ => False) (first ++ second) 0 (.sym 1) (.sym 2) :=
    DemandTransformation.derives_of_clause (List.mem_append_left _ List.mem_cons_self) (fun _ => .sym 0)
      fun _ inside => absurd inside List.not_mem_nil
  exact DemandTransformation.derives_of_clause (List.mem_append_right _ List.mem_cons_self) (fun _ => .sym 0)
    fun g inside => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      subst inside
      exact firstFact

/-- **Negative**: the first part alone does not relate `1` to `3`. -/
theorem first_alone_misses : ¬ Derives (fun _ _ _ => False) first 0 (.sym 1) (.sym 3) := by
  intro derived
  obtain ⟨c, member, -, θ, -, outputIs, -⟩ := derives_cases derived
  simp only [first, List.mem_singleton] at member
  subst member
  simp [RootRewritesOnTheStep.inst_symTerm] at outputIs

/-- **Negative**: the second part alone does not relate `1` to `3`: it never relates `1` to `2`. -/
theorem second_alone_misses : ¬ Derives (fun _ _ _ => False) second 0 (.sym 1) (.sym 3) := by
  have never : ∀ depth, ¬ DemandTransformation.DerivesAt (fun _ _ _ => False) second depth 0 (.sym 1) (.sym 2) := by
    intro depth derived
    cases depth with
    | zero => exact derived
    | succ depth =>
        obtain ⟨c, member, -, θ, -, outputIs, -⟩ := derived
        simp only [second, List.mem_singleton] at member
        subst member
        simp [RootRewritesOnTheStep.inst_symTerm] at outputIs
  intro derived
  obtain ⟨c, member, -, θ, -, -, goals⟩ := derives_cases derived
  simp only [second, List.mem_singleton] at member
  subst member
  obtain ⟨depth, held⟩ := goals _ List.mem_cons_self
  exact never depth held

end Controls

end Mettapedia.GSLT.Compilation.Uniform.Glue

#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.lfp_glued
#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.rounds_reach
#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.Controls.glued_finds
#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.Controls.apart_misses
#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.derives_glued
#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.lfp_sup_const
#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.derives_bridged
#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.Controls.whole_derives
#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.Controls.first_alone_misses
#print axioms Mettapedia.GSLT.Compilation.Uniform.Glue.Controls.second_alone_misses
