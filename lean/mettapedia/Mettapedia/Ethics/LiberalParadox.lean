import Mathlib.Logic.Relation
import Mathlib.Data.Countable.Basic

/-!
# Sen's liberal paradox

Verdict equivalence compares paradigms that judge one agent's act.  Aggregating
several agents' judgments meets a different obstruction.  A rule aggregating
individual preferences into a social preference cannot at once

* respect **minimal liberty** — two different individuals each decide the social
  ranking of one pair of alternatives that concerns them (`DecisiveOver`);
* respect **Pareto** — what everyone prefers is socially preferred
  (`WeakPareto`); and
* stay **acyclic** — no alternative is socially preferred to itself through a
  chain, for every profile of strict rankings (`AcyclicOnRankings`).

Rights in this sense are the side constraints of consent; Pareto is aggregate
welfare.  `liberal_paradox` proves the incompatibility in the shape of Sen's own
example, where the two personal pairs share one alternative, and
`liberal_paradox_disjoint` for two disjoint pairs.  Any two of the three
conditions are jointly satisfiable, so each is load-bearing:

* unanimity is Pareto and acyclic (`unanimity_pareto`, `unanimity_acyclic`);
* unanimity together with the two personal decisions is Pareto and liberal
  (`unanimityOrRights_liberal`);
* the two personal decisions alone, on disjoint pairs, are liberal and acyclic
  (`rights_acyclic`).
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.LiberalParadox

universe u v

variable {Individual : Type u} {Alternative : Type v}

/-- Each individual's strict preference: `profile i a b` says `i` prefers `a` to
`b`. -/
abbrev Profile (Individual : Type u) (Alternative : Type v) :=
  Individual → Alternative → Alternative → Prop

/-- A rule assigning a strict social preference to every profile. -/
abbrev SocialRule (Individual : Type u) (Alternative : Type v) :=
  Profile Individual Alternative → Alternative → Alternative → Prop

/-- Every individual's preference is a strict ranking: better alternatives have
smaller ranks, and no two alternatives share a rank. -/
def Ranked (profile : Profile Individual Alternative) : Prop :=
  ∃ rank : Individual → Alternative → ℕ, (∀ i, Function.Injective (rank i)) ∧
    ∀ i a b, profile i a b ↔ rank i a < rank i b

/-- What everyone prefers is socially preferred. -/
def WeakPareto (rule : SocialRule Individual Alternative) : Prop :=
  ∀ profile a b, (∀ i, profile i a b) → rule profile a b

/-- The individual decides the social ranking of the two alternatives, both ways. -/
def DecisiveOver (rule : SocialRule Individual Alternative) (i : Individual) (a b : Alternative) :
    Prop :=
  ∀ profile, (profile i a b → rule profile a b) ∧ (profile i b a → rule profile b a)

/-- No alternative is socially preferred to itself through a chain, whenever
every individual ranks strictly. -/
def AcyclicOnRankings (rule : SocialRule Individual Alternative) : Prop :=
  ∀ profile, Ranked profile → ∀ a, ¬ Relation.TransGen (rule profile) a a

/-- The profile given by one rank function per individual. -/
def rankProfile (rank : Individual → Alternative → ℕ) : Profile Individual Alternative :=
  fun i a b => rank i a < rank i b

theorem rankProfile_ranked (rank : Individual → Alternative → ℕ)
    (injective : ∀ i, Function.Injective (rank i)) : Ranked (rankProfile rank) :=
  ⟨rank, injective, fun _ _ _ => Iff.rfl⟩

section ThreeAlternatives

variable [DecidableEq Individual] [DecidableEq Alternative]

/-- A strict ranking placing three alternatives first, second and third, and every
other alternative after them in an injective way. -/
def rankOf (first second third : Alternative) (encode : Alternative → ℕ) (a : Alternative) : ℕ :=
  if a = first then 0 else if a = second then 1 else if a = third then 2 else encode a + 3

theorem rankOf_injective {first second third : Alternative} (distinct : first ≠ second ∧
    first ≠ third ∧ second ≠ third) {encode : Alternative → ℕ} (encodeInjective : Function.Injective encode) :
    Function.Injective (rankOf first second third encode) := by
  intro a b same
  unfold rankOf at same
  have injectiveAt := @encodeInjective a b
  obtain ⟨h12, h13, h23⟩ := distinct
  by_cases a1 : a = first <;> by_cases a2 : a = second <;> by_cases a3 : a = third <;>
    by_cases b1 : b = first <;> by_cases b2 : b = second <;> by_cases b3 : b = third <;>
    simp_all

theorem rankOf_first (first second third : Alternative) (encode : Alternative → ℕ) :
    rankOf first second third encode first = 0 := if_pos rfl

theorem rankOf_second {first second : Alternative} (third : Alternative) (encode : Alternative → ℕ)
    (ne₁ : second ≠ first) : rankOf first second third encode second = 1 := by
  simp [rankOf, ne₁]

theorem rankOf_third {first second third : Alternative} (encode : Alternative → ℕ)
    (ne₁ : third ≠ first) (ne₂ : third ≠ second) : rankOf first second third encode third = 2 := by
  simp [rankOf, ne₁, ne₂]

/-- **Sen's liberal paradox**, in the shape of his own example: one individual
decides the pair `x, y`, another the pair `y, z`. -/
theorem liberal_paradox [Countable Alternative] {rule : SocialRule Individual Alternative}
    {i j : Individual} (different : i ≠ j) {x y z : Alternative}
    (distinct : x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (liberalI : DecisiveOver rule i x y) (liberalJ : DecisiveOver rule j y z)
    (pareto : WeakPareto rule) : ¬ AcyclicOnRankings rule := by
  intro acyclic
  obtain ⟨encode, encodeInjective⟩ := exists_injective_nat Alternative
  obtain ⟨hxy, hxz, hyz⟩ := distinct
  -- `i` ranks z, x, y; everyone else ranks y, z, x.
  let rank : Individual → Alternative → ℕ := fun k =>
    if k = i then rankOf z x y encode else rankOf y z x encode
  have injective : ∀ k, Function.Injective (rank k) := by
    intro k
    by_cases ki : k = i
    · simp only [rank, ki, if_true]
      exact rankOf_injective ⟨Ne.symm hxz, Ne.symm hyz, hxy⟩ encodeInjective
    · simp only [rank, ki, if_false]
      exact rankOf_injective ⟨hyz, Ne.symm hxy, Ne.symm hxz⟩ encodeInjective
  have atI : rank i = rankOf z x y encode := if_pos rfl
  have atOther : ∀ k, k ≠ i → rank k = rankOf y z x encode := fun _ ki => if_neg ki
  have xy : rule (rankProfile rank) x y := (liberalI _).1 (by
    show rank i x < rank i y
    rw [atI, rankOf_second _ _ hxz, rankOf_third _ hyz (Ne.symm hxy)]
    decide)
  have yz : rule (rankProfile rank) y z := (liberalJ _).1 (by
    show rank j y < rank j z
    rw [atOther j (Ne.symm different), rankOf_first, rankOf_second _ _ (Ne.symm hyz)]
    decide)
  have zx : rule (rankProfile rank) z x := pareto _ _ _ fun k => by
    show rank k z < rank k x
    by_cases ki : k = i
    · rw [ki, atI, rankOf_first, rankOf_second _ _ hxz]
      decide
    · rw [atOther k ki, rankOf_second _ _ (Ne.symm hyz), rankOf_third _ hxy hxz]
      decide
  exact acyclic _ (rankProfile_ranked rank injective) x
    (.tail (.tail (.single xy) yz) zx)

end ThreeAlternatives

/-! ## Two disjoint pairs -/

section FourAlternatives

variable [DecidableEq Individual] [DecidableEq Alternative]

/-- A strict ranking placing four alternatives first to fourth, and every other
alternative after them injectively. -/
def rankOf4 (a₁ a₂ a₃ a₄ : Alternative) (encode : Alternative → ℕ) (a : Alternative) : ℕ :=
  if a = a₁ then 0 else if a = a₂ then 1 else if a = a₃ then 2 else if a = a₄ then 3
  else encode a + 4

theorem rankOf4_injective {a₁ a₂ a₃ a₄ : Alternative}
    (distinct : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₁ ≠ a₄ ∧ a₂ ≠ a₃ ∧ a₂ ≠ a₄ ∧ a₃ ≠ a₄)
    {encode : Alternative → ℕ} (encodeInjective : Function.Injective encode) :
    Function.Injective (rankOf4 a₁ a₂ a₃ a₄ encode) := by
  intro a b same
  unfold rankOf4 at same
  have injectiveAt := @encodeInjective a b
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := distinct
  by_cases a1 : a = a₁ <;> by_cases a2 : a = a₂ <;> by_cases a3 : a = a₃ <;> by_cases a4 : a = a₄ <;>
    by_cases b1 : b = a₁ <;> by_cases b2 : b = a₂ <;> by_cases b3 : b = a₃ <;> by_cases b4 : b = a₄ <;>
    simp_all

theorem rankOf4_first (a₁ a₂ a₃ a₄ : Alternative) (encode : Alternative → ℕ) :
    rankOf4 a₁ a₂ a₃ a₄ encode a₁ = 0 := if_pos rfl

theorem rankOf4_second {a₁ a₂ : Alternative} (a₃ a₄ : Alternative) (encode : Alternative → ℕ)
    (ne₁ : a₂ ≠ a₁) : rankOf4 a₁ a₂ a₃ a₄ encode a₂ = 1 := by
  simp [rankOf4, ne₁]

theorem rankOf4_third {a₁ a₂ a₃ : Alternative} (a₄ : Alternative) (encode : Alternative → ℕ)
    (ne₁ : a₃ ≠ a₁) (ne₂ : a₃ ≠ a₂) : rankOf4 a₁ a₂ a₃ a₄ encode a₃ = 2 := by
  simp [rankOf4, ne₁, ne₂]

theorem rankOf4_fourth {a₁ a₂ a₃ a₄ : Alternative} (encode : Alternative → ℕ)
    (ne₁ : a₄ ≠ a₁) (ne₂ : a₄ ≠ a₂) (ne₃ : a₄ ≠ a₃) : rankOf4 a₁ a₂ a₃ a₄ encode a₄ = 3 := by
  simp [rankOf4, ne₁, ne₂, ne₃]

/-- **The liberal paradox for disjoint pairs**: one individual decides `x, y`,
another decides `z, w`, and the four alternatives are distinct. -/
theorem liberal_paradox_disjoint [Countable Alternative] {rule : SocialRule Individual Alternative}
    {i j : Individual} (different : i ≠ j) {x y z w : Alternative}
    (distinct : x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w)
    (liberalI : DecisiveOver rule i x y) (liberalJ : DecisiveOver rule j z w)
    (pareto : WeakPareto rule) : ¬ AcyclicOnRankings rule := by
  intro acyclic
  obtain ⟨encode, encodeInjective⟩ := exists_injective_nat Alternative
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := distinct
  -- `i` ranks w, x, y, z; everyone else ranks y, z, w, x.
  let rank : Individual → Alternative → ℕ := fun k =>
    if k = i then rankOf4 w x y z encode else rankOf4 y z w x encode
  have injective : ∀ k, Function.Injective (rank k) := by
    intro k
    by_cases ki : k = i
    · simp only [rank, ki, if_true]
      exact rankOf4_injective ⟨Ne.symm hxw, Ne.symm hyw, Ne.symm hzw, hxy, hxz, hyz⟩ encodeInjective
    · simp only [rank, ki, if_false]
      exact rankOf4_injective ⟨hyz, hyw, Ne.symm hxy, hzw, Ne.symm hxz, Ne.symm hxw⟩ encodeInjective
  have atI : rank i = rankOf4 w x y z encode := if_pos rfl
  have atOther : ∀ k, k ≠ i → rank k = rankOf4 y z w x encode := fun _ ki => if_neg ki
  have xy : rule (rankProfile rank) x y := (liberalI _).1 (by
    show rank i x < rank i y
    rw [atI, rankOf4_second _ _ _ hxw, rankOf4_third _ _ hyw (Ne.symm hxy)]
    decide)
  have zw : rule (rankProfile rank) z w := (liberalJ _).1 (by
    show rank j z < rank j w
    rw [atOther j (Ne.symm different), rankOf4_second _ _ _ (Ne.symm hyz),
      rankOf4_third _ _ (Ne.symm hyw) (Ne.symm hzw)]
    decide)
  have yz : rule (rankProfile rank) y z := pareto _ _ _ fun k => by
    show rank k y < rank k z
    by_cases ki : k = i
    · rw [ki, atI, rankOf4_third _ _ hyw (Ne.symm hxy), rankOf4_fourth _ hzw (Ne.symm hxz) (Ne.symm hyz)]
      decide
    · rw [atOther k ki, rankOf4_first, rankOf4_second _ _ _ (Ne.symm hyz)]
      decide
  have wx : rule (rankProfile rank) w x := pareto _ _ _ fun k => by
    show rank k w < rank k x
    by_cases ki : k = i
    · rw [ki, atI, rankOf4_first, rankOf4_second _ _ _ hxw]
      decide
    · rw [atOther k ki, rankOf4_third _ _ (Ne.symm hyw) (Ne.symm hzw), rankOf4_fourth _ hxy hxz hxw]
      decide
  exact acyclic _ (rankProfile_ranked rank injective) x
    (.tail (.tail (.tail (.single xy) yz) zw) wx)

end FourAlternatives

/-! ## Each condition is load-bearing -/

/-- The unanimity rule: socially prefer what everyone prefers. -/
def unanimity : SocialRule Individual Alternative :=
  fun profile a b => ∀ i, profile i a b

theorem unanimity_pareto : WeakPareto (unanimity : SocialRule Individual Alternative) :=
  fun _ _ _ everyone => everyone

/-- **Pareto and acyclicity together.**  A chain of unanimous preferences is a
chain in any one individual's ranking, which strictly lowers the rank. -/
theorem unanimity_acyclic [Nonempty Individual] :
    AcyclicOnRankings (unanimity : SocialRule Individual Alternative) := by
  rintro profile ⟨rank, -, ranks⟩ a cycle
  obtain ⟨i⟩ := ‹Nonempty Individual›
  have lower : ∀ b c, Relation.TransGen (unanimity profile) b c → rank i b < rank i c := by
    intro b c chain
    induction chain with
    | single step => exact (ranks i _ _).mp (step i)
    | tail _ step ih => exact Nat.lt_trans ih ((ranks i _ _).mp (step i))
  exact Nat.lt_irrefl _ (lower a a cycle)

/-- Unanimity together with two personal decisions. -/
def unanimityOrRights (i j : Individual) (x y z w : Alternative) : SocialRule Individual Alternative :=
  fun profile a b => unanimity profile a b ∨
    (((a = x ∧ b = y) ∨ (a = y ∧ b = x)) ∧ profile i a b) ∨
    (((a = z ∧ b = w) ∨ (a = w ∧ b = z)) ∧ profile j a b)

/-- **Pareto and liberty together.** -/
theorem unanimityOrRights_liberal (i j : Individual) (x y z w : Alternative) :
    WeakPareto (unanimityOrRights i j x y z w) ∧ DecisiveOver (unanimityOrRights i j x y z w) i x y ∧
      DecisiveOver (unanimityOrRights i j x y z w) j z w :=
  ⟨fun _ _ _ everyone => .inl everyone,
    fun _ => ⟨fun prefers => .inr (.inl ⟨.inl ⟨rfl, rfl⟩, prefers⟩),
      fun prefers => .inr (.inl ⟨.inr ⟨rfl, rfl⟩, prefers⟩)⟩,
    fun _ => ⟨fun prefers => .inr (.inr ⟨.inl ⟨rfl, rfl⟩, prefers⟩),
      fun prefers => .inr (.inr ⟨.inr ⟨rfl, rfl⟩, prefers⟩)⟩⟩

/-- The two personal decisions alone. -/
def rights (i j : Individual) (x y z w : Alternative) : SocialRule Individual Alternative :=
  fun profile a b =>
    (((a = x ∧ b = y) ∨ (a = y ∧ b = x)) ∧ profile i a b) ∨
    (((a = z ∧ b = w) ∨ (a = w ∧ b = z)) ∧ profile j a b)

/-- **Liberty and acyclicity together**, for disjoint pairs: every step stays in
one pair and follows that pair's decider, so it strictly lowers a rank read off
the pair. -/
theorem rights_acyclic [DecidableEq Alternative] (i j : Individual) {x y z w : Alternative}
    (disjoint : x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w) :
    DecisiveOver (rights i j x y z w) i x y ∧ DecisiveOver (rights i j x y z w) j z w ∧
      AcyclicOnRankings (rights i j x y z w) := by
  refine ⟨fun _ => ⟨fun prefers => .inl ⟨.inl ⟨rfl, rfl⟩, prefers⟩,
      fun prefers => .inl ⟨.inr ⟨rfl, rfl⟩, prefers⟩⟩,
    fun _ => ⟨fun prefers => .inr ⟨.inl ⟨rfl, rfl⟩, prefers⟩,
      fun prefers => .inr ⟨.inr ⟨rfl, rfl⟩, prefers⟩⟩, ?_⟩
  rintro profile ⟨rank, -, ranks⟩ a cycle
  obtain ⟨hxz, hxw, hyz, hyw⟩ := disjoint
  let potential : Alternative → ℕ := fun b => if b = x ∨ b = y then rank i b else rank j b
  have lower : ∀ b c, Relation.TransGen (rights i j x y z w profile) b c → potential b < potential c := by
    have step : ∀ b c, rights i j x y z w profile b c → potential b < potential c := by
      rintro b c (⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), prefers⟩ | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), prefers⟩)
      · simpa [potential] using (ranks i _ _).mp prefers
      · simpa [potential] using (ranks i _ _).mp prefers
      · simpa [potential, Ne.symm hxz, Ne.symm hyz, Ne.symm hxw, Ne.symm hyw] using
          (ranks j _ _).mp prefers
      · simpa [potential, Ne.symm hxz, Ne.symm hyz, Ne.symm hxw, Ne.symm hyw] using
          (ranks j _ _).mp prefers
    intro b c chain
    induction chain with
    | single edge => exact step _ _ edge
    | tail _ edge ih => exact Nat.lt_trans ih (step _ _ edge)
  exact Nat.lt_irrefl _ (lower a a cycle)

#print axioms liberal_paradox
#print axioms liberal_paradox_disjoint
#print axioms unanimity_acyclic
#print axioms unanimityOrRights_liberal
#print axioms rights_acyclic

end Mettapedia.Ethics.LiberalParadox
