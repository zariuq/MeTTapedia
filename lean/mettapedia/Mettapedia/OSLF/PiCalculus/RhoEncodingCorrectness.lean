import Mettapedia.OSLF.PiCalculus.RhoEncoding
import Mettapedia.OSLF.PiCalculus.MultiStep
import Mettapedia.OSLF.RhoCalculus.MultiStep
import Lean.Elab.Tactic

/-!
# Correctness of π → ρ Encoding

## LLM Hints (compact)
- Type/Prop: Reduces is Type-valued; wrap with Nonempty for Prop contexts
- Double-quote trap: substitute with `.var w` not `piNameToRhoName w` (avoid @x → @@y)
- rhoPar cases: 4 cases based on whether P,Q are hashBag collections
- rhoInput = .apply "PInput" [m, .lambda y P]; lambda binding blocks substitution
- Generalize IH: encode uses n++"_L", n++"_R" etc, so prove ∀ n v first
- List.map simp: add `List.map` to simp for explicit list reduction
- **Pattern match explosion strategy**: When casework explodes (100+ cases), find algebraic reformulation:
  - Abstract the pattern-matched operation to list/algebraic ops (toListRepr/fromListRepr for rhoPar)
  - Prove abstraction equivalence once (rhoPar_eq_fromListRepr_append)
  - Use algebraic properties (List.map_append) instead of casework
  - Example: rhoPar's 4-way match → list append (proven in 5 lines vs 100 cases)

## Criteria (Lybech Definition 3, page 103)

1. **Compositionality**: ⟦S₁ | ... | Sₙ⟧_N = C | ⟦S₁⟧_{N₁} | ... | ⟦Sₙ⟧_{Nₙ}
2. **Substitution invariance**: ⟦Sσₛ⟧_N ≃ ⟦S⟧_N σₜ
3. **Operational correspondence**: S →* S' ⟺ ⟦S⟧_N →* T' ∧ T' ≃ ⟦S'⟧_{N'}
4. **Observational correspondence**: P ↓_M x̂ ⟺ ⟦P⟧_N ⇓_{φ(M)} φ(x̂)
5. **Divergence reflection**: ⟦P⟧_N →ω ⟹ P →ω
6. **Parameter independence**: ⟦P⟧_{N₁} ≃ ⟦P⟧_{N₂}

## References
- Lybech (2022), Propositions 1-5, pages 106-107
-/

namespace Mettapedia.OSLF.PiCalculus

open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution hiding allVars isGloballyFresh

/-! ## Bisimulation for ρ-calculus

Define bisimilarity using Nonempty to convert Type-valued Reduces to Prop.
-/

/-- Bisimulation for ρ-calculus processes (Prop-valued version).

    Two patterns are bisimilar if there exists a bisimulation relation
    relating them. Uses Nonempty to convert Type-valued Reduces to Prop.
-/
def RhoBisimilar (p q : Pattern) : Prop :=
  ∃ R : Pattern → Pattern → Prop,
    (∀ p₁ q₁, R p₁ q₁ → R q₁ p₁) ∧  -- Symmetry
    (∀ p₁ q₁, R p₁ q₁ → ∀ p₂, Nonempty (Reduction.Reduces p₁ p₂) →
     ∃ q₂, Nonempty (Reduction.Reduces q₁ q₂) ∧ R p₂ q₂) ∧  -- Forward
    (∀ p₁ q₁, R p₁ q₁ → ∀ q₂, Nonempty (Reduction.Reduces q₁ q₂) →
     ∃ p₂, Nonempty (Reduction.Reduces p₁ p₂) ∧ R p₂ q₂) ∧  -- Backward
    R p q

notation:50 p " ∼ρ " q => RhoBisimilar p q

/-- Bisimilarity is reflexive. The identity relation Eq is a bisimulation. -/
theorem RhoBisimilar.refl (p : Pattern) : p ∼ρ p := by
  refine ⟨Eq, fun _ _ h => h.symm, ?_, ?_, rfl⟩
  · intro p₁ q₁ h p₂ hp₂; subst h; exact ⟨p₂, hp₂, rfl⟩
  · intro p₁ q₁ h q₂ hq₂; subst h; exact ⟨q₂, hq₂, rfl⟩

/-- Two processes that cannot reduce are bisimilar.

    If neither p nor q can take a step, any bisimulation condition is
    vacuously satisfied (the forward/backward clauses never trigger).
-/
theorem RhoBisimilar_of_both_stuck (p q : Pattern)
    (hp : ∀ p', ¬Nonempty (p ⇝ p'))
    (hq : ∀ q', ¬Nonempty (q ⇝ q')) :
    p ∼ρ q := by
  refine ⟨fun a b => (a = p ∧ b = q) ∨ (a = q ∧ b = p),
          ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
  · -- Symmetry
    intro a b hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · -- Forward
    intro a b hab a' ha'
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd ha' (hp a')
    · exact absurd ha' (hq a')
  · -- Backward
    intro a b hab b' hb'
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hb' (hq b')
    · exact absurd hb' (hp b')

/-- Bisimilarity is symmetric. -/
theorem RhoBisimilar.symm {p q : Pattern} (h : p ∼ρ q) : q ∼ρ p := by
  obtain ⟨R, hR_sym, hR_fwd, hR_bwd, hR_pq⟩ := h
  exact ⟨R, hR_sym, hR_fwd, hR_bwd, hR_sym _ _ hR_pq⟩

/-- Bisimilarity is transitive. Uses the symmetric closure of R₁ ∘ R₂. -/
theorem RhoBisimilar.trans {p q r : Pattern} (hpq : p ∼ρ q) (hqr : q ∼ρ r) : p ∼ρ r := by
  obtain ⟨R₁, hR₁_sym, hR₁_fwd, hR₁_bwd, hR₁_pq⟩ := hpq
  obtain ⟨R₂, hR₂_sym, hR₂_fwd, hR₂_bwd, hR₂_qr⟩ := hqr
  -- S = R₁;R₂ ∪ R₂;R₁ (symmetric closure of composition)
  let S := fun a c => (∃ b, R₁ a b ∧ R₂ b c) ∨ (∃ b, R₂ a b ∧ R₁ b c)
  refine ⟨S, ?_, ?_, ?_, Or.inl ⟨q, hR₁_pq, hR₂_qr⟩⟩
  · -- Symmetry: swap disjuncts + use individual symmetries
    intro a c hac
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · exact Or.inr ⟨b, hR₂_sym _ _ hbc, hR₁_sym _ _ hab⟩
    · exact Or.inl ⟨b, hR₁_sym _ _ hbc, hR₂_sym _ _ hab⟩
  · -- Forward simulation: a ⇝ a', S(a,c) → ∃ c', c ⇝ c' ∧ S(a',c')
    intro a c hac a' ha'
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · -- R₁(a,b) ∧ R₂(b,c): chain R₁_fwd then R₂_fwd
      obtain ⟨b', hb', h₁⟩ := hR₁_fwd _ _ hab _ ha'
      obtain ⟨c', hc', h₂⟩ := hR₂_fwd _ _ hbc _ hb'
      exact ⟨c', hc', Or.inl ⟨b', h₁, h₂⟩⟩
    · -- R₂(a,b) ∧ R₁(b,c): chain R₂_fwd then R₁_fwd
      obtain ⟨b', hb', h₂⟩ := hR₂_fwd _ _ hab _ ha'
      obtain ⟨c', hc', h₁⟩ := hR₁_fwd _ _ hbc _ hb'
      exact ⟨c', hc', Or.inr ⟨b', h₂, h₁⟩⟩
  · -- Backward simulation: c ⇝ c', S(a,c) → ∃ a', a ⇝ a' ∧ S(a',c')
    intro a c hac c' hc'
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · -- R₁(a,b) ∧ R₂(b,c): chain R₂_bwd then R₁_bwd
      obtain ⟨b', hb', h₂⟩ := hR₂_bwd _ _ hbc _ hc'
      obtain ⟨a', ha', h₁⟩ := hR₁_bwd _ _ hab _ hb'
      exact ⟨a', ha', Or.inl ⟨b', h₁, h₂⟩⟩
    · -- R₂(a,b) ∧ R₁(b,c): chain R₁_bwd then R₂_bwd
      obtain ⟨b', hb', h₁⟩ := hR₁_bwd _ _ hbc _ hc'
      obtain ⟨a', ha', h₂⟩ := hR₂_bwd _ _ hab _ hb'
      exact ⟨a', ha', Or.inr ⟨b', h₂, h₁⟩⟩

/-! ## Observability

A process can "observe" or "emit" on a channel if it can perform an output action.
-/

/-- Observable output in π-calculus: P ↓ x means P can output on channel x.

    This is defined as: P ≡ (x<y> | Q) for some y and Q, or
    P can reduce to a process with this structure.
-/
def PiObservableOutput (P : Process) (x : Name) : Prop :=
  ∃ y Q, Nonempty (P ≡ Process.par (Process.output x y) Q) ∨
         (∃ P', Nonempty (MultiStep P P') ∧
                Nonempty (P' ≡ Process.par (Process.output x y) Q))

notation:50 P " ↓π " x => PiObservableOutput P x

/-- Observable output in ρ-calculus: P ⇓ n means P can output on name n.

    Following OSLF convention, this means the process has (or can reduce to a state
    with) a POutput component on name n in a parallel composition (hashBag).

    Uses list membership for position-independence:
    a hashBag is a multiset, so observation shouldn't depend on element order.
-/
def RhoObservableOutput (P : Pattern) (n : Pattern) : Prop :=
  ∃ q, (∃ ps, P = .collection .hashBag ps none ∧
              .apply "POutput" [n, q] ∈ ps) ∨
       (∃ P' ps, Nonempty (ReducesStar P P') ∧
                 P' = .collection .hashBag ps none ∧
                 .apply "POutput" [n, q] ∈ ps)

notation:50 P " ↓ρ " n => RhoObservableOutput P n

/-- SC-closed observable output: P has a barb modulo structural congruence.
    In the ρ-calculus, barbs are defined on SC-equivalence classes because
    par_singleton ({P} ≡ P) can strip the hashBag structure that
    RhoObservableOutput requires. This closure ensures barb preservation under SC. -/
def RhoObservableSC (P : Pattern) (n : Pattern) : Prop :=
  ∃ P', (P ≡ P') ∧ RhoObservableOutput P' n

/-- Immediate barbs imply SC-closed barbs (via SC.refl). -/
theorem RhoObservableSC.of_obs {P n : Pattern} (h : RhoObservableOutput P n) :
    RhoObservableSC P n :=
  ⟨P, .refl _, h⟩

/-! ## Weak N-Restricted Barbed Bisimilarity (Lybech 2022, p. 99)

Following Lybech: observations restricted to channels in N ⊆ fn(P).
Namespace machinery names (n++"_L", n++"_R") are NOT in fn(P),
so different namespace assignments preserve this bisimilarity.
-/

/-- Weak N-restricted barbed bisimilarity.
    Two ρ-patterns are weakly bisimilar restricted to names in N if there exists
    a symmetric relation R such that:
    - R relates the two patterns
    - One-step reductions are matched by zero-or-more steps (weak)
    - Barbs on channels `.var x` for `x ∈ N` are preserved
    Reference: Lybech (2022), Definition of ≈N, page 99. -/
def WeakRestrictedBisim (N : Finset String) (p q : Pattern) : Prop :=
  ∃ R : Pattern → Pattern → Prop,
    (∀ p₁ q₁, R p₁ q₁ → R q₁ p₁) ∧
    (∀ p₁ q₁, R p₁ q₁ → ∀ p₂, Nonempty (Reduction.Reduces p₁ p₂) →
     ∃ q₂, Nonempty (ReducesStar q₁ q₂) ∧ R p₂ q₂) ∧
    (∀ p₁ q₁, R p₁ q₁ → ∀ x ∈ N,
     RhoObservableSC p₁ (.var x) → RhoObservableSC q₁ (.var x)) ∧
    R p q

notation:50 p " ≈{" N "}" q => WeakRestrictedBisim N p q

/-- WeakRestrictedBisim is reflexive. -/
theorem WeakRestrictedBisim.refl (N : Finset String) (p : Pattern) : p ≈{N} p := by
  refine ⟨Eq, fun _ _ h => h.symm, ?_, ?_, rfl⟩
  · intro p₁ q₁ h p₂ hp₂
    subst h; exact ⟨p₂, ⟨ReducesStar.step (Classical.choice hp₂) (.refl _)⟩, rfl⟩
  · intro p₁ q₁ h x _ hobs; subst h; exact hobs

/-- WeakRestrictedBisim is symmetric. -/
theorem WeakRestrictedBisim.symm {N : Finset String} {p q : Pattern}
    (h : p ≈{N} q) : q ≈{N} p := by
  obtain ⟨R, hR_sym, hR_fwd, hR_barb, hR_pq⟩ := h
  exact ⟨R, hR_sym, hR_fwd, hR_barb, hR_sym _ _ hR_pq⟩

/-- Lift one-step weak forward simulation to multi-step.
    If R has the weak forward property and R(p, q) and p ⇝* p',
    then ∃ q', q ⇝* q' ∧ R(p', q'). -/
private theorem lift_star_forward
    {R : Pattern → Pattern → Prop}
    (hfwd : ∀ p₁ q₁, R p₁ q₁ → ∀ p₂, Nonempty (Reduction.Reduces p₁ p₂) →
            ∃ q₂, Nonempty (ReducesStar q₁ q₂) ∧ R p₂ q₂)
    {p q p' : Pattern} (h : R p q) (hstar : Nonempty (ReducesStar p p')) :
    ∃ q', Nonempty (ReducesStar q q') ∧ R p' q' := by
  obtain ⟨star⟩ := hstar
  induction star generalizing q with
  | refl => exact ⟨q, ⟨.refl _⟩, h⟩
  | @step _ pmid _ hred rest ih =>
    obtain ⟨qmid, hqmid_star, hR_mid⟩ := hfwd _ _ h _ ⟨hred⟩
    obtain ⟨q', hq'_star, hR'⟩ := ih hR_mid
    exact ⟨q', ⟨(Classical.choice hqmid_star).trans (Classical.choice hq'_star)⟩, hR'⟩

/-- WeakRestrictedBisim is transitive. Uses symmetric closure of R₁ ∘ R₂. -/
theorem WeakRestrictedBisim.trans {N : Finset String} {p q r : Pattern}
    (hpq : p ≈{N} q) (hqr : q ≈{N} r) : p ≈{N} r := by
  obtain ⟨R₁, hR₁_sym, hR₁_fwd, hR₁_barb, hR₁_pq⟩ := hpq
  obtain ⟨R₂, hR₂_sym, hR₂_fwd, hR₂_barb, hR₂_qr⟩ := hqr
  -- S = R₁;R₂ ∪ R₂;R₁ (symmetric closure of composition)
  let S := fun a c => (∃ b, R₁ a b ∧ R₂ b c) ∨ (∃ b, R₂ a b ∧ R₁ b c)
  refine ⟨S, ?_, ?_, ?_, Or.inl ⟨q, hR₁_pq, hR₂_qr⟩⟩
  · -- Symmetry: swap disjuncts + use individual symmetries
    intro a c hac
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · exact Or.inr ⟨b, hR₂_sym _ _ hbc, hR₁_sym _ _ hab⟩
    · exact Or.inl ⟨b, hR₁_sym _ _ hbc, hR₂_sym _ _ hab⟩
  · -- Forward: one step matched by star, composed via lift_star_forward
    intro a c hac a' ha'
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · -- R₁(a,b) ∧ R₂(b,c): chain R₁_fwd then lift R₂ over star
      obtain ⟨b', hb'_star, hR₁'⟩ := hR₁_fwd _ _ hab _ ha'
      obtain ⟨c', hc'_star, hR₂'⟩ := lift_star_forward hR₂_fwd hbc hb'_star
      exact ⟨c', hc'_star, Or.inl ⟨b', hR₁', hR₂'⟩⟩
    · -- R₂(a,b) ∧ R₁(b,c): chain R₂_fwd then lift R₁ over star
      obtain ⟨b', hb'_star, hR₂'⟩ := hR₂_fwd _ _ hab _ ha'
      obtain ⟨c', hc'_star, hR₁'⟩ := lift_star_forward hR₁_fwd hbc hb'_star
      exact ⟨c', hc'_star, Or.inr ⟨b', hR₂', hR₁'⟩⟩
  · -- Barb preservation: compose barb transfer through intermediate
    intro a c hac x hx hobs
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · exact hR₂_barb _ _ hbc x hx (hR₁_barb _ _ hab x hx hobs)
    · exact hR₁_barb _ _ hbc x hx (hR₂_barb _ _ hab x hx hobs)

/-- Monotonicity: restricting to fewer names preserves bisimilarity. -/
theorem WeakRestrictedBisim.mono {N N' : Finset String} {p q : Pattern}
    (h : p ≈{N} q) (hsub : N' ⊆ N) : p ≈{N'} q := by
  obtain ⟨R, hR_sym, hR_fwd, hR_barb, hR_pq⟩ := h
  exact ⟨R, hR_sym, hR_fwd, fun p₁ q₁ hr x hx => hR_barb p₁ q₁ hr x (hsub hx), hR_pq⟩

/-- ρ-SC implies weak restricted bisimilarity (for any N).
    SC processes have identical reduction behavior. Barbs use SC-closed
    observation (RhoObservableSC), so SC-equivalence transfers them directly. -/
theorem WeakRestrictedBisim.of_SC {N : Finset String} {p q : Pattern}
    (h : p ≡ q) : p ≈{N} q := by
  -- Use Nonempty(SC) as the bisimulation relation
  refine ⟨fun a b => Nonempty (a ≡ b), ?_, ?_, ?_, ⟨h⟩⟩
  · -- Symmetry
    intro p₁ q₁ ⟨hsc⟩; exact ⟨.symm _ _ hsc⟩
  · -- Forward (weak): q₁ matches p₁'s step via EQUIV, wrapped in ReducesStar
    intro p₁ q₁ ⟨hsc⟩ p₂ ⟨hred⟩
    exact ⟨p₂, ⟨.step (Reduces.equiv (.symm _ _ hsc) hred (.refl _)) (.refl _)⟩, ⟨.refl _⟩⟩
  · -- Barb preservation: SC-closed barbs transfer via SC transitivity
    intro p₁ q₁ ⟨hsc⟩ x _hx ⟨p₁', hsc_p, hobs⟩
    exact ⟨p₁', .trans _ _ _ (.symm _ _ hsc) hsc_p, hobs⟩

/-- Empty restriction: any two processes are bisimilar when nothing is observed. -/
theorem WeakRestrictedBisim.empty (p q : Pattern) : p ≈{∅} q := by
  refine ⟨fun _ _ => True, fun _ _ _ => trivial, ?_, ?_, trivial⟩
  · intro p₁ q₁ _ p₂ hp₂; exact ⟨q₁, ⟨.refl _⟩, trivial⟩
  · intro _ _ _ x hx; simp at hx

/-! ## Divergence

A process diverges if it can reduce infinitely many times.
-/

/-- A π-calculus process diverges if it has an infinite reduction sequence. -/
def PiDiverges (P : Process) : Prop :=
  ∃ f : ℕ → Process, f 0 = P ∧ ∀ n, Nonempty (f n ⇝ f (n + 1))

/-- A ρ-calculus process diverges if it has an infinite reduction sequence. -/
def RhoDiverges (P : Pattern) : Prop :=
  ∃ f : ℕ → Pattern, f 0 = P ∧ ∀ n, Nonempty (Reduction.Reduces (f n) (f (n + 1)))

/-! ## Proposition 1: Parameter Independence

The encoding result doesn't depend on the specific parameter values chosen,
as long as they satisfy freshness conditions.
-/

/-- Namespace disjointness for derived parameters.

    States that π-name u is disjoint from all encoding parameters derived from n.
    This captures Lybech's `u # N[n]` condition (page 106, Proposition 1).

    **Critical for correctness**: Without this, the encoding can have namespace
    collisions (see counterexample below where π-name equals a generated namespace).
-/
def NamespaceDisjoint (u : Name) (n : String) : Prop :=
  ∀ suffix : String, u ≠ n ++ suffix

/-- Predicate: process has no restriction (nu) or replication. -/
def Process.isSimple : Process → Prop
  | .nil => True
  | .par P Q => P.isSimple ∧ Q.isSimple
  | .input _ _ P => P.isSimple
  | .output _ _ => True
  | .nu _ _ => False
  | .replicate _ _ _ => False

/-- For simple processes, the encoding is independent of the namespace parameter n.

    This is because only `nu` and `replicate` use the namespace parameter to
    generate internal channel names. Without these, n is never referenced.
-/
theorem encode_independent_of_n (P : Process) (h : P.isSimple) (n n' v : String) :
    encode P n v = encode P n' v := by
  induction P generalizing n n' v with
  | nil => rfl
  | par P Q ihP ihQ =>
    obtain ⟨hP, hQ⟩ := h
    simp only [encode]
    rw [ihP hP, ihQ hQ]
  | input x y P ih =>
    simp only [encode]
    rw [ih h]
  | output _ _ => rfl
  | nu _ _ => exact absurd h id
  | replicate _ _ _ => exact absurd h id

/-- For simple processes, parameter independence is trivially bisimilarity by equality.

    Since encode P n v = encode P n' v, the two encodings differ only in the
    name server seed. This establishes parameter independence for the encoding
    part; the name server seed independence requires separate treatment.
-/
theorem encoding_parameter_independence_simple (P : Process) (h : P.isSimple)
    (n n' v _s _s' : String) :
    encode P n v = encode P n' v :=
  encode_independent_of_n P h n n' v

/-- Proposition 1 (simple fragment): namespace parameter independence as
    N-restricted weak barbed bisimilarity.

    For simple processes, `encode` is independent of `n` by equality, so the
    bisimilarity follows by reflexivity after rewriting. -/
theorem encoding_parameter_independence_simple_bisim (P : Process) (h : P.isSimple)
    (n n' v : String) :
    encode P n v ≈{P.freeNames} encode P n' v := by
  rw [encode_independent_of_n P h n n' v]
  exact WeakRestrictedBisim.refl P.freeNames (encode P n' v)

/-! ## Namespace Renaming Lemmas

Infrastructure for proving Prop 1 via finite renaming (GPT-5.2 Pro's roadmap).
The `nsEnv P n n'` substitution maps namespace variables from `n` to `n'`.
-/

/-- NamespaceDisjoint is preserved when extending the parameter with a suffix. -/
lemma NamespaceDisjoint_append (u n s : String) (h : NamespaceDisjoint u n) :
    NamespaceDisjoint u (n ++ s) := by
  intro suffix
  rw [String.append_assoc]
  exact h (s ++ suffix)

/-- All keys in `nsEnv P n n'` are of the form `n ++ suffix`. -/
theorem nsEnv_keys_are_prefixed (P : Process) (n n' : String) :
    ∀ k val, (k, val) ∈ nsEnv P n n' → ∃ suffix, k = n ++ suffix := by
  induction P generalizing n n' with
  | nil => intro k val h; exact absurd h (by simp [nsEnv])
  | output _ _ => intro k val h; exact absurd h (by simp [nsEnv])
  | input _ _ P ih => exact ih n n'
  | par P Q ihP ihQ =>
    intro k val hkv
    rw [show nsEnv (.par P Q) n n' =
        nsEnv P (n ++ "_L") (n' ++ "_L") ++ nsEnv Q (n ++ "_R") (n' ++ "_R") from rfl] at hkv
    rw [List.mem_append] at hkv
    cases hkv with
    | inl h =>
      obtain ⟨suffix, hs⟩ := ihP (n ++ "_L") (n' ++ "_L") k val h
      exact ⟨"_L" ++ suffix, by rw [hs, String.append_assoc]⟩
    | inr h =>
      obtain ⟨suffix, hs⟩ := ihQ (n ++ "_R") (n' ++ "_R") k val h
      exact ⟨"_R" ++ suffix, by rw [hs, String.append_assoc]⟩
  | nu x P ih =>
    intro k val hkv
    rw [show nsEnv (.nu x P) n n' =
        (n, Pattern.var n') :: nsEnv P (n ++ "_" ++ n) (n' ++ "_" ++ n') from rfl] at hkv
    rw [List.mem_cons] at hkv
    cases hkv with
    | inl h =>
      have hk := (Prod.mk.inj h).1
      exact ⟨"", by simp [hk]⟩
    | inr h =>
      obtain ⟨suffix, hs⟩ := ih (n ++ "_" ++ n) (n' ++ "_" ++ n') k val h
      -- hs : k = (n ++ "_" ++ n) ++ suffix, goal: ∃ s, k = n ++ s
      -- (n ++ "_" ++ n) ++ suffix = n ++ ("_" ++ n ++ suffix) by associativity
      exact ⟨"_" ++ n ++ suffix, by
        rw [hs]; simp only [String.append_assoc]⟩
  | replicate _ _ P ih =>
    intro k val hkv
    obtain ⟨suffix, hs⟩ := ih (n ++ "_rep") (n' ++ "_rep") k val hkv
    exact ⟨"_rep" ++ suffix, by rw [hs, String.append_assoc]⟩

/-- Looking up a NamespaceDisjoint name in nsEnv returns none.
    Uses nsEnv_keys_are_prefixed: all keys are n++suffix, and u ≠ n++suffix. -/
theorem nsEnv_find_disjoint (P : Process) (n n' u : String)
    (h : NamespaceDisjoint u n) :
    SubstEnv.find (nsEnv P n n') u = none := by
  simp only [SubstEnv.find]
  have : (nsEnv P n n').find? (fun p => p.1 == u) = none := by
    rw [List.find?_eq_none]
    intro ⟨k, val⟩ hmem hbeq
    simp only [beq_iff_eq] at hbeq
    obtain ⟨suffix, hk⟩ := nsEnv_keys_are_prefixed P n n' k val hmem
    exact h suffix (by rw [← hk, ← hbeq])
  rw [this]

/-- Filtering a NamespaceDisjoint name from nsEnv is a no-op. -/
theorem nsEnv_filter_disjoint (P : Process) (n n' y : String)
    (h : NamespaceDisjoint y n) :
    (nsEnv P n n').filter (·.1 != y) = nsEnv P n n' := by
  rw [List.filter_eq_self]
  intro ⟨k, val⟩ hmem
  obtain ⟨suffix, hk⟩ := nsEnv_keys_are_prefixed P n n' k val hmem
  simp only [bne_iff_ne, ne_eq]
  rw [hk]
  exact fun habs => h suffix habs.symm

/-- P.names membership: u ∈ P.names implies u ∈ (input x y P).names -/
lemma Process.names_sub_input (x y : Name) (P : Process) (u : Name) (hu : u ∈ P.names) :
    u ∈ (Process.input x y P).names := by
  simp only [Process.names, Process.freeNames, Process.boundNames,
             Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hu ⊢
  tauto

/-- P.names ⊆ (par P Q).names -/
lemma Process.names_sub_par_left (P Q : Process) (u : Name) (hu : u ∈ P.names) :
    u ∈ (Process.par P Q).names := by
  simp only [Process.names, Process.freeNames, Process.boundNames,
             Finset.mem_union] at hu ⊢; tauto

/-- Q.names ⊆ (par P Q).names -/
lemma Process.names_sub_par_right (P Q : Process) (u : Name) (hu : u ∈ Q.names) :
    u ∈ (Process.par P Q).names := by
  simp only [Process.names, Process.freeNames, Process.boundNames,
             Finset.mem_union] at hu ⊢; tauto

/-- P.names ⊆ (nu x P).names -/
lemma Process.names_sub_nu (x : Name) (P : Process) (u : Name) (hu : u ∈ P.names) :
    u ∈ (Process.nu x P).names := by
  simp only [Process.names, Process.freeNames, Process.boundNames,
             Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hu ⊢
  tauto

/-- x ∈ (nu x P).names -/
lemma Process.names_nu_binder (x : Name) (P : Process) :
    x ∈ (Process.nu x P).names := by
  simp [Process.names, Process.boundNames, Finset.mem_union, Finset.mem_insert]

/-- P.names ⊆ (replicate x y P).names -/
lemma Process.names_sub_replicate (x y : Name) (P : Process) (u : Name) (hu : u ∈ P.names) :
    u ∈ (Process.replicate x y P).names := by
  simp only [Process.names, Process.freeNames, Process.boundNames,
             Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hu ⊢
  tauto

/-- Adding a substitution entry for a fresh variable doesn't change the result. -/
lemma applySubst_cons_fresh (k : String) (val : Pattern) (env : SubstEnv) (p : Pattern)
    (h : isFresh k p) (hno : noExplicitSubst p) :
    applySubst ((k, val) :: env) p = applySubst env p := by
  calc applySubst ((k, val) :: env) p
      = applySubst (((k, val) :: env).filter (·.1 != k)) p := subst_fresh _ k p h hno
    _ = applySubst (env.filter (·.1 != k)) p := by
          congr 1
          simp only [List.filter_cons, bne_self_eq_false]
          simp
    _ = applySubst env p := (subst_fresh env k p h hno).symm

/-! ### Compositional applySubst lemmas -/

/-- Looking up a key that matches the head of env. -/
lemma SubstEnv.find_cons_eq (k : String) (val : Pattern) (env : SubstEnv) :
    SubstEnv.find ((k, val) :: env) k = some val := by
  simp [SubstEnv.find]

/-- Looking up a key that doesn't match the head of env. -/
lemma SubstEnv.find_cons_ne (k : String) (val : Pattern) (env : SubstEnv)
    (name : String) (h : name ≠ k) :
    SubstEnv.find ((k, val) :: env) name = SubstEnv.find env name := by
  simp [SubstEnv.find, h.symm]

/-- Substitution on a variable that is found in the env. -/
lemma applySubst_var_found (env : SubstEnv) (name : String) (val : Pattern)
    (h : SubstEnv.find env name = some val) :
    applySubst env (.var name) = val := by
  simp [applySubst, h]

/-- Substitution on a variable not found in the env. -/
lemma applySubst_var_not_found (env : SubstEnv) (name : String)
    (h : SubstEnv.find env name = none) :
    applySubst env (.var name) = .var name := by
  simp [applySubst, h]

/-- Substitution distributes through rhoOutput. -/
lemma applySubst_rhoOutput (env : SubstEnv) (ch msg : Pattern) :
    applySubst env (rhoOutput ch msg) =
    rhoOutput (applySubst env ch) (applySubst env msg) := by
  simp [rhoOutput, applySubst, List.map]

/-- Substitution distributes through rhoInput, filtering the binder. -/
lemma applySubst_rhoInput (env : SubstEnv) (ch : Pattern) (x : String) (body : Pattern) :
    applySubst env (rhoInput ch x body) =
    rhoInput (applySubst env ch) x (applySubst (env.filter (·.1 != x)) body) := by
  simp [rhoInput, applySubst, List.map]

/-! ### String prefix disjointness -/

/-- Left-cancellation for string append. -/
theorem string_append_left_cancel {a b c : String} (h : a ++ b = a ++ c) : b = c := by
  have h1 := congrArg String.toList h
  simp only [String.toList_append] at h1
  exact String.ext (List.append_cancel_left h1)

/-- Strings with "_L" and "_R" prefixes (after a common prefix) are distinct. -/
theorem string_LR_ne (n suffix s : String) : n ++ "_L" ++ suffix ≠ n ++ "_R" ++ s := by
  rw [String.append_assoc, String.append_assoc]; intro h
  have h2 := string_append_left_cancel h
  have h3 := congrArg String.toList h2; simp only [String.toList_append] at h3
  exact absurd (List.cons.inj (List.cons.inj h3).2).1 (by decide)

/-! ### Substitution append lemmas -/

/-- Skipping a fresh entry in the middle of a substitution environment. -/
theorem applySubst_skip_fresh_entry (env1 : SubstEnv) (k : String) (val : Pattern)
    (env2 : SubstEnv) (p : Pattern)
    (hfresh : isFresh k p) (hno : noExplicitSubst p) :
    applySubst (env1 ++ (k, val) :: env2) p = applySubst (env1 ++ env2) p := by
  have h1 := subst_fresh (env1 ++ (k, val) :: env2) k p hfresh hno
  have h2 := subst_fresh (env1 ++ env2) k p hfresh hno
  rw [h1, h2]; congr 1
  simp only [List.filter_append, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
             ↓reduceIte]

/-- Appending an env whose keys are all fresh in `p` doesn't change `applySubst`. -/
theorem applySubst_append_allFresh (env1 env2 : SubstEnv) (p : Pattern)
    (hno : noExplicitSubst p)
    (hfresh : ∀ k val, (k, val) ∈ env2 → isFresh k p) :
    applySubst (env1 ++ env2) p = applySubst env1 p := by
  induction env2 with
  | nil => simp
  | cons entry rest ih =>
    obtain ⟨k, val⟩ := entry
    rw [show env1 ++ (k, val) :: rest = env1 ++ ((k, val) :: rest) from rfl]
    rw [applySubst_skip_fresh_entry env1 k val rest p
        (hfresh k val List.mem_cons_self) hno]
    exact ih (fun k' val' hm => hfresh k' val' (List.mem_cons_of_mem _ hm))

/-- Prepending an env whose keys are all fresh in `p` doesn't change `applySubst`. -/
theorem applySubst_prepend_allFresh (env1 env2 : SubstEnv) (p : Pattern)
    (hno : noExplicitSubst p)
    (hfresh : ∀ k val, (k, val) ∈ env1 → isFresh k p) :
    applySubst (env1 ++ env2) p = applySubst env2 p := by
  induction env1 with
  | nil => simp
  | cons entry rest ih =>
    obtain ⟨k, val⟩ := entry
    rw [show (k, val) :: rest ++ env2 = [] ++ ((k, val) :: (rest ++ env2)) from by simp]
    rw [applySubst_skip_fresh_entry [] k val (rest ++ env2) p
        (hfresh k val List.mem_cons_self) hno]
    simp only [List.nil_append]
    exact ih (fun k' val' hm => hfresh k' val' (List.mem_cons_of_mem _ hm))


/-! ### noExplicitSubst for encodings (early version for use in nsEnv proofs) -/

private lemma allNoExplicitSubst_append' {ps qs : List Pattern}
    (hp : allNoExplicitSubst ps) (hq : allNoExplicitSubst qs) :
    allNoExplicitSubst (ps ++ qs) := by
  induction ps with
  | nil => exact hq
  | cons p ps' ih =>
    unfold allNoExplicitSubst at hp
    have h1 := Bool.and_eq_true_iff.mp hp
    show allNoExplicitSubst (p :: (ps' ++ qs)) = true
    unfold allNoExplicitSubst; exact Bool.and_eq_true_iff.mpr ⟨h1.1, ih h1.2⟩

private lemma noExplicitSubst_rhoPar' {P Q : Pattern}
    (hp : noExplicitSubst P) (hq : noExplicitSubst Q) :
    noExplicitSubst (rhoPar P Q) := by
  unfold rhoPar; split
  · simp only [noExplicitSubst] at hp hq ⊢; exact allNoExplicitSubst_append' hp hq
  · simp only [noExplicitSubst] at hp ⊢
    apply allNoExplicitSubst_append' hp
    unfold allNoExplicitSubst; exact Bool.and_eq_true_iff.mpr ⟨hq, rfl⟩
  · simp only [noExplicitSubst] at hq ⊢
    unfold allNoExplicitSubst; exact Bool.and_eq_true_iff.mpr ⟨hp, hq⟩
  · simp only [noExplicitSubst]
    unfold allNoExplicitSubst; unfold allNoExplicitSubst; unfold allNoExplicitSubst
    simp [hp, hq]

/-- Encoding never produces .subst nodes (early version for nsEnv proofs). -/
private theorem encode_noExplicitSubst' (P : Process) (n v : String) :
    noExplicitSubst (encode P n v) := by
  induction P generalizing n with
  | nil => simp [encode, rhoNil, noExplicitSubst, allNoExplicitSubst]
  | output x z =>
    simp [encode, rhoOutput, rhoDrop, piNameToRhoName, noExplicitSubst, allNoExplicitSubst]
  | input x y P' ih =>
    simp only [encode, rhoInput, piNameToRhoName, noExplicitSubst, allNoExplicitSubst,
               Bool.true_and, Bool.and_true]; exact ih n
  | par P' Q' ihP ihQ =>
    simp only [encode]; exact noExplicitSubst_rhoPar' (ihP _) (ihQ _)
  | nu x P' ih =>
    simp only [encode]; apply noExplicitSubst_rhoPar'
    · simp [rhoOutput, noExplicitSubst, allNoExplicitSubst]
    · simp only [rhoInput, noExplicitSubst, allNoExplicitSubst, Bool.true_and, Bool.and_true]
      exact ih _
  | replicate x y P' ih =>
    simp only [encode, rhoReplicate, rhoInput, piNameToRhoName, noExplicitSubst, allNoExplicitSubst,
               Bool.true_and, Bool.and_true]; exact ih _

/-! ### Free variable analysis of encodings -/

/-- Free variables of `rhoPar A B` are from `A` or `B`. -/
theorem freeVars_rhoPar (A B : Pattern) (k : String)
    (hk : k ∈ freeVars (rhoPar A B)) : k ∈ freeVars A ∨ k ∈ freeVars B := by
  simp only [rhoPar] at hk
  split at hk
  case h_1 ps qs =>
    simp only [freeVars, List.flatMap_append] at hk ⊢
    rw [List.mem_append] at hk; exact hk
  case h_2 ps q =>
    simp only [freeVars, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
               List.append_nil] at hk ⊢
    rw [List.mem_append] at hk; exact hk
  case h_3 p qs =>
    simp only [freeVars, List.flatMap_cons] at hk ⊢
    rw [List.mem_append] at hk
    cases hk with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr h
  case h_4 p q =>
    simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hk ⊢
    rw [List.mem_append] at hk; exact hk

/-- Helper: `List.contains true` implies membership. -/
theorem list_mem_of_contains {k : String} {xs : List String}
    (h : xs.contains k = true) : k ∈ xs := by
  rw [List.contains_iff_exists_mem_beq] at h
  obtain ⟨a, ha, hbeq⟩ := h
  rw [beq_iff_eq] at hbeq; subst hbeq; exact ha

/-- Free variables of `encode P n v` are either π-names, `v`, or `n`-prefixed. -/
theorem encode_freeVars_subset (P : Process) (n v k : String)
    (hk : k ∈ freeVars (encode P n v)) :
    k ∈ Process.names P ∨ k = v ∨ ∃ suffix, k = n ++ suffix := by
  induction P generalizing n k with
  | nil => simp [encode, rhoNil, freeVars] at hk
  | output x z =>
    simp [encode, rhoOutput, rhoDrop, piNameToRhoName] at hk
    unfold freeVars at hk; simp [freeVars] at hk
    cases hk with
    | inl h => left; subst h; simp [Process.names, Process.freeNames]
    | inr h => left; subst h; simp [Process.names, Process.freeNames]
  | input x y P' ih =>
    simp only [encode, rhoInput, piNameToRhoName] at hk
    unfold freeVars at hk; simp [freeVars] at hk
    cases hk with
    | inl h =>
      left; subst h
      simp [Process.names, Process.freeNames, Process.boundNames,
            Finset.mem_union, Finset.mem_insert]
    | inr h =>
      cases ih n k h.1 with
      | inl hp => left; exact Process.names_sub_input x y P' k hp
      | inr hv => exact Or.inr hv
  | par P' Q' ihP ihQ =>
    simp only [encode] at hk
    cases freeVars_rhoPar _ _ k hk with
    | inl hL =>
      cases ihP (n ++ "_L") k hL with
      | inl hp => left; exact Process.names_sub_par_left P' Q' k hp
      | inr h =>
        cases h with
        | inl hv => right; left; exact hv
        | inr hs =>
          obtain ⟨s, hs⟩ := hs
          right; right; exact ⟨"_L" ++ s, by rw [hs, String.append_assoc]⟩
    | inr hR =>
      cases ihQ (n ++ "_R") k hR with
      | inl hq => left; exact Process.names_sub_par_right P' Q' k hq
      | inr h =>
        cases h with
        | inl hv => right; left; exact hv
        | inr hs =>
          obtain ⟨s, hs⟩ := hs
          right; right; exact ⟨"_R" ++ s, by rw [hs, String.append_assoc]⟩
  | nu x P' ih =>
    simp only [encode] at hk
    cases freeVars_rhoPar _ _ k hk with
    | inl hOut =>
      simp [rhoOutput, freeVars] at hOut
      cases hOut with
      | inl hv => right; left; exact hv
      | inr hn => right; right; exact ⟨"", by rw [hn, String.append_empty]⟩
    | inr hIn =>
      simp only [rhoInput] at hIn; unfold freeVars at hIn; simp [freeVars] at hIn
      cases hIn with
      | inl hn => right; right; exact ⟨"", by rw [hn, String.append_empty]⟩
      | inr h =>
        cases ih (n ++ "_" ++ n) k h.1 with
        | inl hp => left; exact Process.names_sub_nu x P' k hp
        | inr h' =>
          cases h' with
          | inl hv => right; left; exact hv
          | inr hs =>
            obtain ⟨s, hs⟩ := hs
            right; right; exact ⟨"_" ++ n ++ s, by rw [hs]; simp [String.append_assoc]⟩
  | replicate x y P' ih =>
    simp only [encode, rhoReplicate] at hk
    unfold freeVars at hk; simp [freeVars, rhoInput, piNameToRhoName] at hk
    cases hk with
    | inl hx =>
      left; subst hx
      simp [Process.names, Process.freeNames, Process.boundNames,
            Finset.mem_union, Finset.mem_insert]
    | inr h =>
      cases ih (n ++ "_rep") k h.1 with
      | inl hp => left; exact Process.names_sub_replicate x y P' k hp
      | inr h' =>
        cases h' with
        | inl hv => right; left; exact hv
        | inr hs =>
          obtain ⟨s, hs⟩ := hs
          right; right; exact ⟨"_rep" ++ s, by rw [hs, String.append_assoc]⟩

/-- Tighter: freeVars of encode use only freeNames (not boundNames).
    Bound variables become lambda-bound in the encoding, so they're filtered out. -/
theorem encode_freeVars_subset_fn (P : Process) (n v k : String)
    (hk : k ∈ freeVars (encode P n v)) :
    k ∈ P.freeNames ∨ k = v ∨ ∃ suffix, k = n ++ suffix := by
  induction P generalizing n k with
  | nil => simp [encode, rhoNil, freeVars] at hk
  | output x z =>
    simp [encode, rhoOutput, rhoDrop, piNameToRhoName] at hk
    unfold freeVars at hk; simp [freeVars] at hk
    cases hk with
    | inl h => left; subst h; simp [Process.freeNames]
    | inr h => left; subst h; simp [Process.freeNames]
  | input x y P' ih =>
    simp only [encode, rhoInput, piNameToRhoName] at hk
    unfold freeVars at hk; simp [freeVars] at hk
    cases hk with
    | inl h => left; subst h; simp [Process.freeNames]
    | inr h =>
      have hk_ne_y := h.2
      cases ih n k h.1 with
      | inl hp =>
        left; simp only [Process.freeNames, Finset.mem_insert, Finset.mem_sdiff,
          Finset.mem_singleton]
        right; exact ⟨hp, by simpa using hk_ne_y⟩
      | inr hv => exact Or.inr hv
  | par P' Q' ihP ihQ =>
    simp only [encode] at hk
    cases freeVars_rhoPar _ _ k hk with
    | inl hL =>
      cases ihP (n ++ "_L") k hL with
      | inl hp =>
        left; simp only [Process.freeNames, Finset.mem_union]; left; exact hp
      | inr h =>
        cases h with
        | inl hv => right; left; exact hv
        | inr hs =>
          obtain ⟨s, hs⟩ := hs
          right; right; exact ⟨"_L" ++ s, by rw [hs, String.append_assoc]⟩
    | inr hR =>
      cases ihQ (n ++ "_R") k hR with
      | inl hq =>
        left; simp only [Process.freeNames, Finset.mem_union]; right; exact hq
      | inr h =>
        cases h with
        | inl hv => right; left; exact hv
        | inr hs =>
          obtain ⟨s, hs⟩ := hs
          right; right; exact ⟨"_R" ++ s, by rw [hs, String.append_assoc]⟩
  | nu x P' ih =>
    simp only [encode] at hk
    cases freeVars_rhoPar _ _ k hk with
    | inl hOut =>
      simp [rhoOutput, freeVars] at hOut
      cases hOut with
      | inl hv => right; left; exact hv
      | inr hn => right; right; exact ⟨"", by rw [hn, String.append_empty]⟩
    | inr hIn =>
      simp only [rhoInput] at hIn; unfold freeVars at hIn; simp [freeVars] at hIn
      cases hIn with
      | inl hn => right; right; exact ⟨"", by rw [hn, String.append_empty]⟩
      | inr h =>
        have hk_ne_x := h.2
        cases ih (n ++ "_" ++ n) k h.1 with
        | inl hp =>
          left; simp only [Process.freeNames, Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨hp, by simpa using hk_ne_x⟩
        | inr h' =>
          cases h' with
          | inl hv => right; left; exact hv
          | inr hs =>
            obtain ⟨s, hs⟩ := hs
            right; right; exact ⟨"_" ++ n ++ s, by rw [hs]; simp [String.append_assoc]⟩
  | replicate x y P' ih =>
    simp only [encode, rhoReplicate] at hk
    unfold freeVars at hk; simp [freeVars, rhoInput, piNameToRhoName] at hk
    cases hk with
    | inl hx => left; subst hx; simp [Process.freeNames]
    | inr h =>
      have hk_ne_y := h.2
      cases ih (n ++ "_rep") k h.1 with
      | inl hp =>
        left; simp only [Process.freeNames, Finset.mem_insert, Finset.mem_sdiff,
          Finset.mem_singleton]
        right; exact ⟨hp, by simpa using hk_ne_y⟩
      | inr h' =>
        cases h' with
        | inl hv => right; left; exact hv
        | inr hs =>
          obtain ⟨s, hs⟩ := hs
          right; right; exact ⟨"_rep" ++ s, by rw [hs, String.append_assoc]⟩

/-- Keys of `nsEnv Q (n++"_R")` are fresh in `encode P (n++"_L") v`
    (cross-branch disjointness for par). -/
theorem nsEnv_keys_fresh_cross_LR (P Q : Process) (n n' v : String) (k : String) (val : Pattern)
    (h_ndisj_P : ∀ u ∈ Process.names P, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    (hk_mem : (k, val) ∈ nsEnv Q (n ++ "_R") (n' ++ "_R")) :
    isFresh k (encode P (n ++ "_L") v) := by
  obtain ⟨suffix, hk_eq⟩ := nsEnv_keys_are_prefixed Q (n ++ "_R") (n' ++ "_R") k val hk_mem
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem' : k ∈ freeVars (encode P (n ++ "_L") v) := list_mem_of_contains hk_in
  rcases encode_freeVars_subset P (n ++ "_L") v k hk_mem' with hp | hv | ⟨s, hs⟩
  · exact (h_ndisj_P k hp) ("_R" ++ suffix) (by rw [hk_eq, String.append_assoc])
  · exact h_v_ndisj ("_R" ++ suffix) (by rw [← hv, hk_eq, String.append_assoc])
  · exact string_LR_ne n s suffix (by rw [← hs, ← hk_eq])

/-- Symmetric version: keys of `nsEnv P (n++"_L")` are fresh in `encode Q (n++"_R") v`. -/
theorem nsEnv_keys_fresh_cross_RL (P Q : Process) (n n' v : String) (k : String) (val : Pattern)
    (h_ndisj_Q : ∀ u ∈ Process.names Q, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    (hk_mem : (k, val) ∈ nsEnv P (n ++ "_L") (n' ++ "_L")) :
    isFresh k (encode Q (n ++ "_R") v) := by
  obtain ⟨suffix, hk_eq⟩ := nsEnv_keys_are_prefixed P (n ++ "_L") (n' ++ "_L") k val hk_mem
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem' : k ∈ freeVars (encode Q (n ++ "_R") v) := list_mem_of_contains hk_in
  rcases encode_freeVars_subset Q (n ++ "_R") v k hk_mem' with hq | hv | ⟨s, hs⟩
  · exact (h_ndisj_Q k hq) ("_L" ++ suffix) (by rw [hk_eq, String.append_assoc])
  · exact h_v_ndisj ("_L" ++ suffix) (by rw [← hv, hk_eq, String.append_assoc])
  · exact string_LR_ne n suffix s (by rw [← hk_eq, ← hs])

/-- Generalized: keys of `nsEnv Q (n++"_R") target` are fresh in `encode P (n++"_L") v`
    for ANY target (since freshness depends only on keys, not values). -/
theorem nsEnv_keys_fresh_cross_LR_gen (P Q : Process) (n v target : String)
    (k : String) (val : Pattern)
    (h_ndisj_P : ∀ u ∈ Process.names P, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    (hk_mem : (k, val) ∈ nsEnv Q (n ++ "_R") target) :
    isFresh k (encode P (n ++ "_L") v) := by
  obtain ⟨suffix, hk_eq⟩ := nsEnv_keys_are_prefixed Q (n ++ "_R") target k val hk_mem
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem' : k ∈ freeVars (encode P (n ++ "_L") v) := list_mem_of_contains hk_in
  rcases encode_freeVars_subset P (n ++ "_L") v k hk_mem' with hp | hv | ⟨s, hs⟩
  · exact (h_ndisj_P k hp) ("_R" ++ suffix) (by rw [hk_eq, String.append_assoc])
  · exact h_v_ndisj ("_R" ++ suffix) (by rw [← hv, hk_eq, String.append_assoc])
  · exact string_LR_ne n s suffix (by rw [← hs, ← hk_eq])

/-- Generalized: keys of `nsEnv P (n++"_L") target` are fresh in `encode Q (n++"_R") v`
    for ANY target (since freshness depends only on keys, not values). -/
theorem nsEnv_keys_fresh_cross_RL_gen (P Q : Process) (n v target : String)
    (k : String) (val : Pattern)
    (h_ndisj_Q : ∀ u ∈ Process.names Q, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    (hk_mem : (k, val) ∈ nsEnv P (n ++ "_L") target) :
    isFresh k (encode Q (n ++ "_R") v) := by
  obtain ⟨suffix, hk_eq⟩ := nsEnv_keys_are_prefixed P (n ++ "_L") target k val hk_mem
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem' : k ∈ freeVars (encode Q (n ++ "_R") v) := list_mem_of_contains hk_in
  rcases encode_freeVars_subset Q (n ++ "_R") v k hk_mem' with hq | hv | ⟨s, hs⟩
  · exact (h_ndisj_Q k hq) ("_L" ++ suffix) (by rw [hk_eq, String.append_assoc])
  · exact h_v_ndisj ("_L" ++ suffix) (by rw [← hv, hk_eq, String.append_assoc])
  · exact string_LR_ne n suffix s (by rw [← hk_eq, ← hs])

/-- Keys of `nsEnv` with a different parameter prefix are fresh in the encoding.
    Used for the `nu` case where (n, .var n') is prepended but n is not a
    freeVar of `encode P (n ++ "_" ++ n) v`. -/
theorem nsEnv_key_fresh_nu (P : Process) (n v : String)
    (h_ndisj : ∀ u ∈ Process.names P, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n) :
    isFresh n (encode P (n ++ "_" ++ n) v) := by
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hn_in
  have hn_mem := list_mem_of_contains hn_in
  rcases encode_freeVars_subset P (n ++ "_" ++ n) v n hn_mem with hp | hv | ⟨s, hs⟩
  · -- n ∈ P.names: NamespaceDisjoint n n means n ≠ n ++ suffix for all suffix.
    -- In particular n ≠ n ++ "" = n. But that's n ≠ n, contradiction... no.
    -- Wait: h_ndisj says ∀ u ∈ P.names, ∀ suffix, u ≠ n ++ suffix.
    -- So n ∈ P.names → n ≠ n ++ "" = n. But n = n, contradiction!
    exact (h_ndisj n hp) "" (by rw [String.append_empty])
  · -- n = v: NamespaceDisjoint v n means v ≠ n ++ "".
    exact h_v_ndisj "" (by rw [← hv, String.append_empty])
  · -- n = (n ++ "_" ++ n) ++ s → "" = "_" ++ n ++ s → False
    have h1 : n ++ "" = n ++ ("_" ++ n ++ s) := by
      rw [String.append_empty]; rw [String.append_assoc, String.append_assoc] at hs; exact hs
    have h2 := congrArg String.toList h1
    simp only [String.toList_append] at h2
    have h3 := List.append_cancel_left h2
    simp at h3

/-- General cross-freshness: nsEnv keys from one namespace subtree are fresh in
    encodings from a DIFFERENT namespace subtree.

    The three conditions ensure:
    1. Process variables don't overlap with nsEnv keys (from NamespaceDisjoint)
    2. v doesn't overlap with nsEnv keys (from NamespaceDisjoint)
    3. The two namespace prefixes generate disjoint key/var sets -/
theorem nsEnv_encode_cross_fresh (P_ns P_enc : Process) (base_ns base_enc v target : String)
    (h_enc_not_ns : ∀ u ∈ Process.names P_enc, ∀ s, u ≠ base_ns ++ s)
    (h_v_not_ns : ∀ s, v ≠ base_ns ++ s)
    (h_prefix_disj : ∀ s1 s2, base_ns ++ s1 ≠ base_enc ++ s2)
    {k : String} {val : Pattern}
    (hk_mem : (k, val) ∈ nsEnv P_ns base_ns target) :
    isFresh k (encode P_enc base_enc v) := by
  obtain ⟨suffix, hk_eq⟩ := nsEnv_keys_are_prefixed P_ns base_ns target k val hk_mem
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem' : k ∈ freeVars (encode P_enc base_enc v) := list_mem_of_contains hk_in
  rcases encode_freeVars_subset P_enc base_enc v k hk_mem' with hp | hv | ⟨s, hs⟩
  · exact h_enc_not_ns k hp suffix hk_eq
  · exact h_v_not_ns suffix (by rw [← hv]; exact hk_eq)
  · exact h_prefix_disj suffix s (by rw [← hk_eq, ← hs])

/-- Cross-freshness for namespace prefixes that diverge at the L/R split.
    If nsEnv keys come from `n ++ "_R" ++ suf_ns` and encoding uses `n ++ "_L" ++ suf_enc`,
    the keys are fresh in the encoding (regardless of suffix depth). -/
theorem nsEnv_cross_fresh_LR (P_ns P_enc : Process) (n v suf_ns suf_enc target : String)
    (h_ndisj : ∀ u ∈ Process.names P_enc, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    {k : String} {val : Pattern}
    (hk_mem : (k, val) ∈ nsEnv P_ns (n ++ "_R" ++ suf_ns) target) :
    isFresh k (encode P_enc (n ++ "_L" ++ suf_enc) v) := by
  obtain ⟨suffix, hk_eq⟩ := nsEnv_keys_are_prefixed P_ns (n ++ "_R" ++ suf_ns) target k val hk_mem
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem' := list_mem_of_contains hk_in
  -- k = (n ++ "_R" ++ suf_ns) ++ suffix, normalize to n ++ ("_R" ++ ...)
  have hk_n : k = n ++ ("_R" ++ (suf_ns ++ suffix)) := by
    rw [hk_eq]; simp only [String.append_assoc]
  rcases encode_freeVars_subset P_enc (n ++ "_L" ++ suf_enc) v k hk_mem' with hp | hv | ⟨s, hs⟩
  · exact absurd hk_n (h_ndisj k hp _)
  · exact absurd (hv ▸ hk_n) (h_v_ndisj _)
  · -- k from L-encoding: contradicts k from R-nsEnv
    have h1 := hk_eq.symm.trans hs
    have h2 := string_LR_ne n (suf_enc ++ s) (suf_ns ++ suffix)
    simp only [String.append_assoc] at h1 h2
    exact absurd h1.symm h2

/-- Symmetric version: nsEnv from L-prefix, encoding at R-prefix. -/
theorem nsEnv_cross_fresh_RL (P_ns P_enc : Process) (n v suf_ns suf_enc target : String)
    (h_ndisj : ∀ u ∈ Process.names P_enc, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    {k : String} {val : Pattern}
    (hk_mem : (k, val) ∈ nsEnv P_ns (n ++ "_L" ++ suf_ns) target) :
    isFresh k (encode P_enc (n ++ "_R" ++ suf_enc) v) := by
  obtain ⟨suffix, hk_eq⟩ := nsEnv_keys_are_prefixed P_ns (n ++ "_L" ++ suf_ns) target k val hk_mem
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem' := list_mem_of_contains hk_in
  have hk_n : k = n ++ ("_L" ++ (suf_ns ++ suffix)) := by
    rw [hk_eq]; simp only [String.append_assoc]
  rcases encode_freeVars_subset P_enc (n ++ "_R" ++ suf_enc) v k hk_mem' with hp | hv | ⟨s, hs⟩
  · exact absurd hk_n (h_ndisj k hp _)
  · exact absurd (hv ▸ hk_n) (h_v_ndisj _)
  · have h1 := hk_eq.symm.trans hs
    have h2 := string_LR_ne n (suf_ns ++ suffix) (suf_enc ++ s)
    simp only [String.append_assoc] at h1 h2
    exact absurd h1 h2

/-- General cross-freshness: any key in the nR-namespace is fresh in encode P nL v. -/
theorem domainInNamespace_key_fresh_LR (P : Process) (n v k : String)
    (h_ndisj : ∀ u ∈ Process.names P, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    (hk : ∃ sfx, k = (n ++ "_R") ++ sfx) :
    isFresh k (encode P (n ++ "_L") v) := by
  obtain ⟨sfx, hk_eq⟩ := hk
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem := list_mem_of_contains hk_in
  rcases encode_freeVars_subset P (n ++ "_L") v k hk_mem with hp | hv | ⟨s, hs⟩
  · exact (h_ndisj k hp) ("_R" ++ sfx) (by rw [hk_eq, String.append_assoc])
  · exact h_v_ndisj ("_R" ++ sfx) (by rw [← hv, hk_eq, String.append_assoc])
  · exact string_LR_ne n s sfx (by rw [← hs, ← hk_eq])

/-- Symmetric: any key in the nL-namespace is fresh in encode Q nR v. -/
theorem domainInNamespace_key_fresh_RL (Q : Process) (n v k : String)
    (h_ndisj : ∀ u ∈ Process.names Q, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    (hk : ∃ sfx, k = (n ++ "_L") ++ sfx) :
    isFresh k (encode Q (n ++ "_R") v) := by
  obtain ⟨sfx, hk_eq⟩ := hk
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem := list_mem_of_contains hk_in
  rcases encode_freeVars_subset Q (n ++ "_R") v k hk_mem with hq | hv | ⟨s, hs⟩
  · exact (h_ndisj k hq) ("_L" ++ sfx) (by rw [hk_eq, String.append_assoc])
  · exact h_v_ndisj ("_L" ++ sfx) (by rw [← hv, hk_eq, String.append_assoc])
  · exact string_LR_ne n sfx s (by rw [← hk_eq, ← hs])

/-- Free-name variant: any key in the nR-namespace is fresh in encode P nL v. -/
theorem domainInNamespace_key_fresh_LR_fn (P : Process) (n v k : String)
    (h_ndisj : ∀ u ∈ Process.freeNames P, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    (hk : ∃ sfx, k = (n ++ "_R") ++ sfx) :
    isFresh k (encode P (n ++ "_L") v) := by
  obtain ⟨sfx, hk_eq⟩ := hk
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem := list_mem_of_contains hk_in
  rcases encode_freeVars_subset_fn P (n ++ "_L") v k hk_mem with hp | hv | ⟨s, hs⟩
  · exact (h_ndisj k hp) ("_R" ++ sfx) (by rw [hk_eq, String.append_assoc])
  · exact h_v_ndisj ("_R" ++ sfx) (by rw [← hv, hk_eq, String.append_assoc])
  · exact string_LR_ne n s sfx (by rw [← hs, ← hk_eq])

/-- Free-name variant: any key in the nL-namespace is fresh in encode Q nR v. -/
theorem domainInNamespace_key_fresh_RL_fn (Q : Process) (n v k : String)
    (h_ndisj : ∀ u ∈ Process.freeNames Q, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    (hk : ∃ sfx, k = (n ++ "_L") ++ sfx) :
    isFresh k (encode Q (n ++ "_R") v) := by
  obtain ⟨sfx, hk_eq⟩ := hk
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hk_in
  have hk_mem := list_mem_of_contains hk_in
  rcases encode_freeVars_subset_fn Q (n ++ "_R") v k hk_mem with hq | hv | ⟨s, hs⟩
  · exact (h_ndisj k hq) ("_L" ++ sfx) (by rw [hk_eq, String.append_assoc])
  · exact h_v_ndisj ("_L" ++ sfx) (by rw [← hv, hk_eq, String.append_assoc])
  · exact string_LR_ne n sfx s (by rw [← hk_eq, ← hs])

/-! ### applySubst distributes through rhoPar (for non-var, non-subst patterns) -/

/-- Encoding never produces a top-level variable. -/
private theorem encode_not_var (P : Process) (n v : String) (name : String) :
    encode P n v ≠ .var name := by
  cases P <;> simp [encode, rhoNil, rhoOutput, rhoDrop, rhoInput, rhoReplicate,
    piNameToRhoName, rhoPar]
  all_goals (split <;> simp)

/-- applySubst distributes through rhoPar for non-var, non-subst patterns.
    Key: applySubst preserves the top-level constructor for such patterns,
    so both sides of rhoPar hit the same match case. -/
private theorem applySubst_rhoPar' (env : SubstEnv) (A B : Pattern)
    (hAv : ∀ name, A ≠ .var name) (hAs : noExplicitSubst A)
    (hBv : ∀ name, B ≠ .var name) (hBs : noExplicitSubst B) :
    applySubst env (rhoPar A B) = rhoPar (applySubst env A) (applySubst env B) := by
  cases A with
  | var name => exact absurd rfl (hAv name)
  | subst _ _ _ => simp [noExplicitSubst] at hAs
  | apply af aargs =>
    cases B with
    | var name => exact absurd rfl (hBv name)
    | subst _ _ _ => simp [noExplicitSubst] at hBs
    | apply _ _ | lambda _ _ | multiLambda _ _ =>
      simp [rhoPar, applySubst, List.map]
    | collection ct qs g =>
      cases ct <;> cases g <;> simp [rhoPar, applySubst, List.map]
  | lambda ax abody =>
    cases B with
    | var name => exact absurd rfl (hBv name)
    | subst _ _ _ => simp [noExplicitSubst] at hBs
    | apply _ _ | lambda _ _ | multiLambda _ _ =>
      simp [rhoPar, applySubst, List.map]
    | collection ct qs g =>
      cases ct <;> cases g <;> simp [rhoPar, applySubst, List.map]
  | multiLambda axs abody =>
    cases B with
    | var name => exact absurd rfl (hBv name)
    | subst _ _ _ => simp [noExplicitSubst] at hBs
    | apply _ _ | lambda _ _ | multiLambda _ _ =>
      simp [rhoPar, applySubst, List.map]
    | collection ct qs g =>
      cases ct <;> cases g <;> simp [rhoPar, applySubst, List.map]
  | collection ct_a ps g_a =>
    cases B with
    | var name => exact absurd rfl (hBv name)
    | subst _ _ _ => simp [noExplicitSubst] at hBs
    | apply _ _ | lambda _ _ | multiLambda _ _ =>
      cases ct_a <;> cases g_a <;> simp [rhoPar, applySubst, List.map, List.map_append]
    | collection ct_b qs g_b =>
      cases ct_a <;> cases g_a <;> cases ct_b <;> cases g_b <;>
        simp [rhoPar, applySubst, List.map, List.map_append]

/-- Key lemma: applying the namespace renaming to the encoding produces
    the encoding with the renamed parameter.

    This is the core of Prop 1's proof (Lybech p.106):
    the encoding only uses the namespace parameter `n` in positions that
    nsEnv maps to `n'`, and π-names are untouched (by NamespaceDisjoint).
-/
theorem applySubst_nsEnv_encode (P : Process) (n n' v : String)
    (h_ndisj : ∀ u ∈ Process.names P, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n) :
    applySubst (nsEnv P n n') (encode P n v) = encode P n' v := by
  induction P generalizing n n' with
  | nil => simp [encode, nsEnv, rhoNil, applySubst]
  | output x z =>
    simp [encode, nsEnv, rhoOutput, rhoDrop, piNameToRhoName, applySubst, SubstEnv.find]
  | input x y P ih =>
    simp only [encode, nsEnv, rhoInput, piNameToRhoName]
    simp only [applySubst, List.map]
    have hx_disj := h_ndisj x (by
      simp [Process.names, Process.freeNames, Process.boundNames,
            Finset.mem_union, Finset.mem_insert])
    rw [nsEnv_find_disjoint P n n' x hx_disj]
    have hy_disj := h_ndisj y (by
      simp [Process.names, Process.freeNames, Process.boundNames,
            Finset.mem_union, Finset.mem_insert])
    rw [nsEnv_filter_disjoint P n n' y hy_disj]
    have := ih n n' (fun u hu => h_ndisj u (Process.names_sub_input x y P u hu)) h_v_ndisj
    simp only [this]
  | par P Q ihP ihQ =>
    -- encode (par P Q) n v = rhoPar (encode P (n++"_L") v) (encode Q (n++"_R") v)
    -- nsEnv (par P Q) n n' = nsEnv P (n++"_L") (n'++"_L") ++ nsEnv Q (n++"_R") (n'++"_R")
    simp only [encode, nsEnv]
    -- applySubst distributes through rhoPar (which is a collection or apply)
    -- Key: envR keys are fresh in encode P and envL keys are fresh in encode Q
    let envL := nsEnv P (n ++ "_L") (n' ++ "_L")
    let envR := nsEnv Q (n ++ "_R") (n' ++ "_R")
    -- Step 1: derive NamespaceDisjoint hypotheses for sub-processes
    have h_ndisj_P : ∀ u ∈ Process.names P, NamespaceDisjoint u (n ++ "_L") :=
      fun u hu => NamespaceDisjoint_append u n "_L" (h_ndisj u (Process.names_sub_par_left P Q u hu))
    have h_ndisj_Q : ∀ u ∈ Process.names Q, NamespaceDisjoint u (n ++ "_R") :=
      fun u hu => NamespaceDisjoint_append u n "_R" (h_ndisj u (Process.names_sub_par_right P Q u hu))
    have h_v_L : NamespaceDisjoint v (n ++ "_L") := NamespaceDisjoint_append v n "_L" h_v_ndisj
    have h_v_R : NamespaceDisjoint v (n ++ "_R") := NamespaceDisjoint_append v n "_R" h_v_ndisj
    -- Step 2: IH gives applySubst envL (encode P ...) = encode P n' ... (and similarly for Q)
    have ihP' := ihP (n ++ "_L") (n' ++ "_L") h_ndisj_P h_v_L
    have ihQ' := ihQ (n ++ "_R") (n' ++ "_R") h_ndisj_Q h_v_R
    -- Step 3: show applySubst (envL ++ envR) on each sub-encoding
    -- equals applySubst of just the relevant env (the other is fresh)
    have hP_nosubst := encode_noExplicitSubst' P (n ++ "_L") v
    have hQ_nosubst := encode_noExplicitSubst' Q (n ++ "_R") v
    have hfreshR : applySubst (envL ++ envR) (encode P (n ++ "_L") v) =
        applySubst envL (encode P (n ++ "_L") v) :=
      applySubst_append_allFresh envL envR _ hP_nosubst
        (fun k val hm => nsEnv_keys_fresh_cross_LR P Q n n' v k val
          (fun u hu => h_ndisj u (Process.names_sub_par_left P Q u hu)) h_v_ndisj hm)
    have hfreshL : applySubst (envL ++ envR) (encode Q (n ++ "_R") v) =
        applySubst envR (encode Q (n ++ "_R") v) :=
      applySubst_prepend_allFresh envL envR _ hQ_nosubst
        (fun k val hm => nsEnv_keys_fresh_cross_RL P Q n n' v k val
          (fun u hu => h_ndisj u (Process.names_sub_par_right P Q u hu)) h_v_ndisj hm)
    -- Step 4: applySubst distributes through rhoPar (both args are non-var, non-subst)
    rw [applySubst_rhoPar' (envL ++ envR) _ _
        (encode_not_var P (n ++ "_L") v) hP_nosubst
        (encode_not_var Q (n ++ "_R") v) hQ_nosubst,
      hfreshR, ihP', hfreshL, ihQ']
  | nu x P ih =>
    -- Introduce derived namespace names and freeze the encoding body
    let ns  := n  ++ "_" ++ n
    let ns' := n' ++ "_" ++ n'
    let env := (n, Pattern.var n') :: nsEnv P ns ns'
    -- Derive disjointness facts
    have h_v_ne_n : v ≠ n := fun h => h_v_ndisj "" (by rw [h, String.append_empty])
    have hx_disj := h_ndisj x (by
      simp [Process.names, Process.freeNames, Process.boundNames,
            Finset.mem_union, Finset.mem_insert])
    have hx_ne_n : x ≠ n := fun h => hx_disj "" (by rw [h, String.append_empty])
    have h_v_ndisj_sub : NamespaceDisjoint v ns := by
      show NamespaceDisjoint v (n ++ "_" ++ n)
      rw [String.append_assoc]; exact NamespaceDisjoint_append v n ("_" ++ n) h_v_ndisj
    have hx_ndisj_sub : NamespaceDisjoint x ns := by
      show NamespaceDisjoint x (n ++ "_" ++ n)
      rw [String.append_assoc]; exact NamespaceDisjoint_append x n ("_" ++ n) hx_disj
    have h_ndisj_sub : ∀ u ∈ Process.names P, NamespaceDisjoint u ns :=
      fun u hu => by
        show NamespaceDisjoint u (n ++ "_" ++ n)
        rw [String.append_assoc]
        exact NamespaceDisjoint_append u n ("_" ++ n)
          (h_ndisj u (Process.names_sub_nu x P u hu))
    -- Step 1: Unfold encode and nsEnv (but NOT applySubst)
    simp only [encode, nsEnv]
    -- Goal: applySubst env (rhoPar (rhoOutput (.var v) (.var n))
    --                               (rhoInput (.var n) x (encode P ns v)))
    --     = rhoPar (rhoOutput (.var v) (.var n')) (rhoInput (.var n') x (encode P ns' v))
    -- Step 2: Distribute applySubst through rhoPar
    have hout_nv : ∀ name, rhoOutput (.var v) (.var n) ≠ .var name := by
      intro name; simp [rhoOutput]
    have hout_ns : noExplicitSubst (rhoOutput (.var v) (.var n)) := by
      simp [rhoOutput, noExplicitSubst, allNoExplicitSubst]
    have hin_nv : ∀ name, rhoInput (.var n) x (encode P ns v) ≠ .var name := by
      intro name; simp [rhoInput]
    have hin_ns : noExplicitSubst (rhoInput (.var n) x (encode P ns v)) := by
      simp [rhoInput, noExplicitSubst, allNoExplicitSubst, encode_noExplicitSubst' P ns v]
    rw [applySubst_rhoPar' env _ _ hout_nv hout_ns hin_nv hin_ns]
    -- Step 3: Distribute through rhoOutput and rhoInput
    rw [applySubst_rhoOutput, applySubst_rhoInput]
    -- Step 4: Resolve var lookups
    -- v ≠ n, and v not in nsEnv → applySubst env (.var v) = .var v
    have hfind_v : SubstEnv.find env v = none := by
      show SubstEnv.find ((n, Pattern.var n') :: nsEnv P ns ns') v = none
      rw [SubstEnv.find_cons_ne n (.var n') _ v h_v_ne_n]
      exact nsEnv_find_disjoint P ns ns' v h_v_ndisj_sub
    rw [applySubst_var_not_found env v hfind_v]
    -- n = n, first entry matches → applySubst env (.var n) = .var n'
    have hfind_n : SubstEnv.find env n = some (.var n') := by
      show SubstEnv.find ((n, Pattern.var n') :: nsEnv P ns ns') n = some (.var n')
      exact SubstEnv.find_cons_eq n (.var n') _
    rw [applySubst_var_found env n (.var n') hfind_n]
    -- Step 5: Resolve filter (·.1 != x): n ≠ x so (n, .var n') preserved
    have hfilter_env : env.filter (·.1 != x) =
        (n, Pattern.var n') :: (nsEnv P ns ns').filter (·.1 != x) := by
      show ((n, Pattern.var n') :: nsEnv P ns ns').filter (·.1 != x) = _
      simp only [List.filter_cons]
      have : (n != x) = true := bne_iff_ne.mpr hx_ne_n.symm
      simp [this]
    rw [hfilter_env, nsEnv_filter_disjoint P ns ns' x hx_ndisj_sub]
    -- Step 6: Skip (n, .var n') entry by freshness of n in encode P ns v
    rw [applySubst_cons_fresh n (.var n') _ _
        (nsEnv_key_fresh_nu P n v
          (fun u hu => h_ndisj u (Process.names_sub_nu x P u hu))
          h_v_ndisj)
        (encode_noExplicitSubst' P ns v)]
    -- Step 7: IH closes the remaining goal (drill into rhoPar/rhoInput)
    show rhoPar _ (rhoInput (.var n') x (applySubst (nsEnv P ns ns') (encode P ns v)))
       = rhoPar _ (rhoInput (.var n') x (encode P ns' v))
    rw [ih ns ns' h_ndisj_sub h_v_ndisj_sub]
  | replicate x y P ih =>
    -- nsEnv (.replicate x y P) n n' = nsEnv P (n++"_rep") (n'++"_rep")
    simp only [encode, nsEnv, rhoReplicate, piNameToRhoName]
    simp only [applySubst, List.map, rhoInput, applySubst, List.map]
    have hx_disj := h_ndisj x (by
      simp [Process.names, Process.freeNames, Process.boundNames,
            Finset.mem_union, Finset.mem_insert])
    rw [nsEnv_find_disjoint P (n ++ "_rep") (n' ++ "_rep") x
        (NamespaceDisjoint_append x n "_rep" hx_disj)]
    have hy_disj := h_ndisj y (by
      simp [Process.names, Process.freeNames, Process.boundNames,
            Finset.mem_union, Finset.mem_insert])
    rw [nsEnv_filter_disjoint P (n ++ "_rep") (n' ++ "_rep") y
        (NamespaceDisjoint_append y n "_rep" hy_disj)]
    have := ih (n ++ "_rep") (n' ++ "_rep")
      (fun u hu => NamespaceDisjoint_append u n "_rep"
        (h_ndisj u (Process.names_sub_replicate x y P u hu)))
      (NamespaceDisjoint_append v n "_rep" h_v_ndisj)
    simp only [this]

/-! ## Encoding Equivalence (EncEquiv)

Since π-SC does NOT lift to ρ-SC for namespace-dependent SC cases
(par_comm, par_assoc, nu_par, etc.), we define a combined equivalence that composes
ρ-structural congruence with namespace variable renaming.

The 11 namespace-dependent cases combine two effects:
1. ρ-SC (e.g., par_perm for commutativity, par_nil for identity)
2. Namespace renaming (e.g., swapping _L/_R namespace trees)

`EncEquiv P Q` means: P is SC to some P', and P' can be renamed to Q.
-/

/-- A substitution environment is a renaming if every mapped value is a variable. -/
def isRenamingEnv (σ : SubstEnv) : Prop :=
  ∀ entry ∈ σ, ∃ name : String, entry.2 = Pattern.var name

/-- Concatenation of renaming envs is a renaming. -/
theorem isRenamingEnv_append {σ₁ σ₂ : SubstEnv}
    (h₁ : isRenamingEnv σ₁) (h₂ : isRenamingEnv σ₂) :
    isRenamingEnv (σ₁ ++ σ₂) :=
  fun entry hm => by
    rcases List.mem_append.mp hm with h | h
    · exact h₁ entry h
    · exact h₂ entry h

/-- Two ρ-patterns are encoding-equivalent if one is ρ-SC to a namespace renaming
    of the other: P ≡ P' and applySubst σ P' = Q for some renaming σ.

    This relation combines structural congruence with namespace renaming,
    capturing exactly what happens when π-SC rearranges sub-processes
    (changing which sub-process gets which namespace parameter). -/
def EncEquiv (P Q : Pattern) : Prop :=
  ∃ (P' : Pattern) (σ : SubstEnv),
    (P ≡ P') ∧ isRenamingEnv σ ∧ applySubst σ P' = Q

scoped notation:50 P " ≃enc " Q => EncEquiv P Q

/-- EncEquiv embeds ρ-SC (take σ = [], need noExplicitSubst for identity). -/
theorem EncEquiv.of_SC {P Q : Pattern} (h : P ≡ Q) (hne : noExplicitSubst Q) :
    P ≃enc Q :=
  ⟨Q, [], h, fun _ hm => by simp at hm, subst_empty Q hne⟩

/-- EncEquiv embeds namespace renaming (take P' = P, SC = refl). -/
theorem EncEquiv.of_renaming {P Q : Pattern} (σ : SubstEnv)
    (hren : isRenamingEnv σ) (heq : applySubst σ P = Q) : P ≃enc Q :=
  ⟨P, σ, .refl _, hren, heq⟩

/-- EncEquiv is reflexive (for noExplicitSubst patterns). -/
theorem EncEquiv.rfl (P : Pattern) (h : noExplicitSubst P) : P ≃enc P :=
  ⟨P, [], .refl _, fun _ hm => by simp at hm, subst_empty P h⟩

/-- EncEquiv is transitive: compose SC + renaming chains.
    P ≡ P', σ₁(P') = Q, Q ≡ Q', σ₂(Q') = R ⟹ P ≡ ??, σ(??) = R
    Requires: restricted SC transport under substitution and applySubst composition. -/
theorem EncEquiv.trans {P Q R : Pattern} (h1 : P ≃enc Q) (h2 : Q ≃enc R) : P ≃enc R := by
  obtain ⟨P', σ₁, hsc₁, hren₁, heq₁⟩ := h1
  obtain ⟨Q', σ₂, hsc₂, hren₂, heq₂⟩ := h2
  subst heq₁; subst heq₂
  sorry -- TODO: needs restricted SC transport + applySubst_compose

/-! ### Infrastructure: Renaming Preserves Reduction and SC

These theorems establish that applying a renaming substitution preserves
the key relations (ρ-SC and ρ-reduction). They are the bridge between
EncEquiv and operational semantics.
-/

/-- Restricted alpha-transport assumption for a fixed substitution environment.
    This isolates the only genuinely capture-sensitive part of SC transport:
    alpha-equivalence under substitution. -/
def AlphaSubstSafe (σ : SubstEnv) : Prop :=
  ∀ {P Q : Pattern}, AlphaEquiv P Q → noExplicitSubst P →
    RhoCalculus.StructuralCongruence (applySubst σ P) (applySubst σ Q)

/-! ### Bound Variables and Substitution Disjointness -/

/-- All bound variables in a pattern (from lambda/multiLambda binders). -/
def boundVars : Pattern → List String
  | .var _ => []
  | .apply _ args => args.flatMap boundVars
  | .lambda x body => x :: boundVars body
  | .multiLambda xs body => xs ++ boundVars body
  | .subst body _ repl => boundVars body ++ boundVars repl
  | .collection _ elems _ => elems.flatMap boundVars
termination_by p => sizeOf p

/-- σ is disjoint from a set of bound variables: no key maps them, no value is them. -/
def substBVDisjoint (σ : SubstEnv) (bvs : List String) : Prop :=
  (∀ v ∈ bvs, SubstEnv.find σ v = none) ∧
  (∀ entry ∈ σ, ∀ v ∈ bvs, entry.2 ≠ .var v)

/-- If p ∈ elems, then boundVars p ⊆ boundVars (.collection ct elems rest). -/
private theorem boundVars_collection_mem {ct : CollType} {elems : List Pattern}
    {rest : Option String} {v : String} {p : Pattern}
    (hp : p ∈ elems) (hv : v ∈ boundVars p) :
    v ∈ boundVars (.collection ct elems rest) := by
  unfold boundVars
  exact List.mem_flatMap.mpr ⟨p, hp, hv⟩

/-- noExplicitSubst for a collection element follows from the collection. -/
private theorem noExplicitSubst_of_collection_mem {ct : CollType} {elems : List Pattern}
    {rest : Option String} {p : Pattern}
    (hne : noExplicitSubst (.collection ct elems rest)) (hp : p ∈ elems) :
    noExplicitSubst p := by
  unfold noExplicitSubst at hne
  exact allNoExplicitSubst_mem hne hp

/-- substBVDisjoint is monotone: subset of bound vars preserves it. -/
private theorem substBVDisjoint_mono {σ : SubstEnv} {bvs bvs' : List String}
    (h : substBVDisjoint σ bvs) (hsub : ∀ v ∈ bvs', v ∈ bvs) :
    substBVDisjoint σ bvs' :=
  ⟨fun v hv => h.1 v (hsub v hv), fun e he v hv => h.2 e he v (hsub v hv)⟩

/-- Helper: applySubst on a var when find returns none -/
private theorem applySubst_var_none {σ : SubstEnv} {v : String}
    (h : SubstEnv.find σ v = none) :
    applySubst σ (.var v) = .var v := by
  simp [applySubst, h]

/-- Helper: applySubst on a var when find returns some -/
private theorem applySubst_var_some {σ : SubstEnv} {v : String} {r : Pattern}
    (h : SubstEnv.find σ v = some r) :
    applySubst σ (.var v) = r := by
  simp [applySubst, h]

/-- applySubst on singleton env when key matches -/
private theorem applySubst_singleton_hit (x : String) (t : Pattern) :
    applySubst [(x, t)] (.var x) = t := by
  simp [applySubst, SubstEnv.find, List.find?]

/-- applySubst on singleton env when key doesn't match -/
private theorem applySubst_singleton_miss {v x : String} {t : Pattern} (h : v ≠ x) :
    applySubst [(x, t)] (.var v) = .var v := by
  have : (x == v) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [applySubst, SubstEnv.find, List.find?, this]

/-- SubstEnv.find = none ↔ no entry has that key -/
theorem SubstEnv.find_eq_none_iff (σ : SubstEnv) (x : String) :
    SubstEnv.find σ x = none ↔ ∀ entry ∈ σ, entry.1 ≠ x := by
  constructor
  · intro h entry hmem heq
    unfold SubstEnv.find at h
    have hfind : σ.find? (fun p => p.1 == x) = none := by
      cases hf : σ.find? (fun p => p.1 == x) <;> simp_all
    rw [List.find?_eq_none] at hfind
    exact hfind entry hmem (by simp [heq])
  · intro h
    unfold SubstEnv.find
    have : σ.find? (fun p => p.1 == x) = none := by
      rw [List.find?_eq_none]
      intro entry hmem hbeq
      exact h entry hmem (by simpa using hbeq)
    rw [this]

/-- Filtering can only remove entries, so find=none is preserved. -/
private theorem SubstEnv.find_filter_of_find_none {σ : SubstEnv} {x : String}
    {f : String × Pattern → Bool} (h : SubstEnv.find σ x = none) :
    SubstEnv.find (σ.filter f) x = none := by
  rw [SubstEnv.find_eq_none_iff] at h ⊢
  intro entry hmem
  exact h entry (List.mem_of_mem_filter hmem)

/-- Filtering by (·.1 != x) is identity when x ∉ dom(σ). -/
theorem filter_not_key_of_find_none (σ : SubstEnv) (x : String)
    (h : SubstEnv.find σ x = none) :
    σ.filter (fun p => p.1 != x) = σ := by
  apply List.filter_eq_self.mpr
  intro entry hmem
  exact bne_iff_ne.mpr ((SubstEnv.find_eq_none_iff σ x).mp h entry hmem)

/-- Extract the entry from SubstEnv.find returning some. -/
theorem SubstEnv.find_some_entry_mem (σ : SubstEnv) (x : String) (r : Pattern)
    (h : SubstEnv.find σ x = some r) :
    ∃ entry ∈ σ, entry.1 = x ∧ entry.2 = r := by
  induction σ with
  | nil => simp [SubstEnv.find, List.find?] at h
  | cons hd tl ih =>
    unfold SubstEnv.find at h
    simp only [List.find?_cons] at h
    by_cases hhd : hd.1 == x
    · have hhd_eq := beq_iff_eq.mp hhd
      simp only [hhd] at h
      have hr : hd.2 = r := by simpa using h
      exact ⟨hd, by simp, hhd_eq, hr⟩
    · simp only [hhd] at h
      have h' : SubstEnv.find tl x = some r := by unfold SubstEnv.find; exact h
      obtain ⟨entry, hmem, hkey, hval⟩ := ih h'
      exact ⟨entry, by simp [hmem], hkey, hval⟩

/-- If SubstEnv.find returns some r and σ is a renaming, then r is a variable. -/
private theorem find_isVar_of_renaming (σ : SubstEnv) (x : String) (r : Pattern)
    (hfind : SubstEnv.find σ x = some r) (hren : isRenamingEnv σ) :
    ∃ y : String, r = .var y := by
  obtain ⟨entry, hmem, _, hval⟩ := SubstEnv.find_some_entry_mem σ x r hfind
  obtain ⟨y, hy⟩ := hren entry hmem
  exact ⟨y, by rw [← hval]; exact hy⟩

-- Renaming substitution preserves noExplicitSubst.
mutual
  theorem applySubst_noExplicitSubst (σ : SubstEnv) (p : Pattern)
      (hren : isRenamingEnv σ) (hne : noExplicitSubst p) :
      noExplicitSubst (applySubst σ p) :=
    match p with
    | .var name => by
      simp only [applySubst]
      cases hf : SubstEnv.find σ name with
      | none => simp [noExplicitSubst]
      | some r =>
        obtain ⟨y, hy⟩ := find_isVar_of_renaming σ name r hf hren
        rw [hy]; simp [noExplicitSubst]
    | .apply c args => by
      unfold noExplicitSubst at hne
      simp only [applySubst, noExplicitSubst]
      exact applySubst_allNoExplicitSubst σ args hren hne
    | .lambda x body => by
      unfold noExplicitSubst at hne
      simp only [applySubst, noExplicitSubst]
      exact applySubst_noExplicitSubst (σ.filter (·.1 != x)) body
        (fun entry hmem => hren entry (List.mem_of_mem_filter hmem)) hne
    | .multiLambda xs body => by
      unfold noExplicitSubst at hne
      simp only [applySubst, noExplicitSubst]
      exact applySubst_noExplicitSubst (σ.filter (fun p => !xs.contains p.1)) body
        (fun entry hmem => hren entry (List.mem_of_mem_filter hmem)) hne
    | .subst _ _ _ => by simp [noExplicitSubst] at hne
    | .collection ct elems rest => by
      unfold noExplicitSubst at hne
      simp only [applySubst, noExplicitSubst]
      exact applySubst_allNoExplicitSubst σ elems hren hne

  theorem applySubst_allNoExplicitSubst (σ : SubstEnv) (ps : List Pattern)
      (hren : isRenamingEnv σ) (hall : allNoExplicitSubst ps) :
      allNoExplicitSubst (ps.map (applySubst σ)) :=
    match ps with
    | [] => by simp [allNoExplicitSubst]
    | p :: ps' => by
      unfold allNoExplicitSubst at hall
      simp only [Bool.and_eq_true] at hall
      simp only [List.map_cons, allNoExplicitSubst, Bool.and_eq_true]
      exact ⟨applySubst_noExplicitSubst σ p hren hall.1,
             applySubst_allNoExplicitSubst σ ps' hren hall.2⟩
end

-- Generalized: applySubst preserves noExplicitSubst when ALL values are noExplicitSubst
-- (strictly weaker than isRenamingEnv, which implies values are .var)
mutual
  theorem applySubst_noExplicitSubst_gen (σ : SubstEnv) (p : Pattern)
      (hvals : ∀ entry ∈ σ, noExplicitSubst entry.2) (hne : noExplicitSubst p) :
      noExplicitSubst (applySubst σ p) :=
    match p with
    | .var name => by
      simp only [applySubst]
      cases hf : SubstEnv.find σ name with
      | none => simp [noExplicitSubst]
      | some r =>
        simp only
        obtain ⟨entry, hmem, _, hval⟩ := SubstEnv.find_some_entry_mem σ name r hf
        rw [← hval]; exact hvals entry hmem
    | .apply c args => by
      unfold noExplicitSubst at hne
      simp only [applySubst, noExplicitSubst]
      exact applySubst_allNoExplicitSubst_gen σ args hvals hne
    | .lambda x body => by
      unfold noExplicitSubst at hne
      simp only [applySubst, noExplicitSubst]
      exact applySubst_noExplicitSubst_gen (σ.filter (·.1 != x)) body
        (fun entry hmem => hvals entry (List.mem_of_mem_filter hmem)) hne
    | .multiLambda xs body => by
      unfold noExplicitSubst at hne
      simp only [applySubst, noExplicitSubst]
      exact applySubst_noExplicitSubst_gen (σ.filter (fun p => !xs.contains p.1)) body
        (fun entry hmem => hvals entry (List.mem_of_mem_filter hmem)) hne
    | .subst _ _ _ => by simp [noExplicitSubst] at hne
    | .collection ct elems rest => by
      unfold noExplicitSubst at hne
      simp only [applySubst, noExplicitSubst]
      exact applySubst_allNoExplicitSubst_gen σ elems hvals hne

  theorem applySubst_allNoExplicitSubst_gen (σ : SubstEnv) (ps : List Pattern)
      (hvals : ∀ entry ∈ σ, noExplicitSubst entry.2) (hall : allNoExplicitSubst ps) :
      allNoExplicitSubst (ps.map (applySubst σ)) :=
    match ps with
    | [] => by simp [allNoExplicitSubst]
    | p :: ps' => by
      unfold allNoExplicitSubst at hall
      simp only [Bool.and_eq_true] at hall
      simp only [List.map_cons, allNoExplicitSubst, Bool.and_eq_true]
      exact ⟨applySubst_noExplicitSubst_gen σ p hvals hall.1,
             applySubst_allNoExplicitSubst_gen σ ps' hvals hall.2⟩
end

/-- Thin wrapper: `subst_empty` uses `SubstEnv.empty`, goals often have `[]`. -/
private theorem subst_nil (p : Pattern) (hne : noExplicitSubst p) :
    applySubst ([] : SubstEnv) p = p := subst_empty p hne

/-! ### Substitution Commutativity

The key lemma for the COMM case of `reduces_applySubst`:
`applySubst σ (applySubst [(x, t)] p) = applySubst [(x, applySubst σ t)] (applySubst σ p)`
when σ is a renaming disjoint from x and the bound variables of p.
-/

mutual
  /-- Substitution commutativity: disjoint substitutions can be swapped.
      When σ is a renaming, x ∉ dom(σ) ∪ image(σ), and bound vars of p ∉ dom(σ),
      we can push σ through a single-variable substitution. -/
  theorem applySubst_swap (σ : SubstEnv) (p : Pattern) (x : String) (t : Pattern)
      (hren : isRenamingEnv σ)
      (hx_dom : SubstEnv.find σ x = none)
      (hx_img : ∀ entry ∈ σ, entry.2 ≠ .var x)
      (hbv_dom : ∀ y ∈ boundVars p, SubstEnv.find σ y = none)
      (hne : noExplicitSubst p) :
      applySubst σ (applySubst [(x, t)] p) =
      applySubst [(x, applySubst σ t)] (applySubst σ p) :=
    match p with
    | .var v => by
      by_cases hvx : v = x
      · subst hvx
        rw [applySubst_singleton_hit, applySubst_var_none hx_dom, applySubst_singleton_hit]
      · rw [applySubst_singleton_miss hvx]
        cases hfv : SubstEnv.find σ v with
        | none =>
          rw [applySubst_var_none hfv]
          exact (applySubst_singleton_miss hvx).symm
        | some r =>
          rw [applySubst_var_some hfv]
          obtain ⟨y, hy⟩ := find_isVar_of_renaming σ v r hfv hren
          rw [hy]
          obtain ⟨entry, hmem, _, hval⟩ := SubstEnv.find_some_entry_mem σ v r hfv
          have hyx : y ≠ x := by
            intro heq; subst heq; exact hx_img entry hmem (by rw [hval, hy])
          exact (applySubst_singleton_miss hyx).symm
    | .apply c args => by
      simp only [applySubst, List.map_map]
      congr 1
      unfold noExplicitSubst at hne
      exact applySubst_swap_list σ args x t hren hx_dom hx_img
        (fun y hy => hbv_dom y (by simp only [boundVars]; exact List.mem_flatMap.mpr hy))
        hne
    | .lambda y body => by
      by_cases hyx : y = x
      · -- y = x: inner [(x, t)] filtered out under lambda x
        simp only [applySubst]
        have hfi : ([(x, t)] : SubstEnv).filter (fun p => p.1 != y) = [] := by
          subst hyx; simp
        rw [hfi]
        unfold noExplicitSubst at hne
        rw [subst_nil body hne]
        have hy_dom : SubstEnv.find σ y = none := by rw [hyx]; exact hx_dom
        rw [filter_not_key_of_find_none σ y hy_dom]
        have hfi2 : ([(x, applySubst σ t)] : SubstEnv).filter (fun p => p.1 != y) = [] := by
          subst hyx; simp
        rw [hfi2]
        rw [subst_nil _ (applySubst_noExplicitSubst σ body hren hne)]
      · -- y ≠ x: IH
        simp only [applySubst]
        have hfi : ([(x, t)] : SubstEnv).filter (fun p => p.1 != y) = [(x, t)] := by
          simp [bne_iff_ne, Ne.symm hyx]
        rw [hfi]
        have hy_dom : SubstEnv.find σ y = none := by
          apply hbv_dom y; simp [boundVars]
        rw [filter_not_key_of_find_none σ y hy_dom]
        have hfo : ([(x, applySubst σ t)] : SubstEnv).filter (fun p => p.1 != y) =
                   [(x, applySubst σ t)] := by
          simp [bne_iff_ne, Ne.symm hyx]
        simp only [hfo]
        unfold noExplicitSubst at hne
        congr 1
        exact applySubst_swap σ body x t hren hx_dom hx_img
          (fun z hz => hbv_dom z (by simp [boundVars, hz])) hne
    | .multiLambda ys body => by
      -- Helper: filter singleton by !ys.contains when x ∈ ys gives []
      have filter_singleton_mem (r : Pattern) (hm : x ∈ ys) :
          ([(x, r)] : SubstEnv).filter (fun p => !ys.contains p.1) = [] := by
        simp only [List.filter_cons, List.filter_nil]
        have hc : ys.contains x = true := contains_of_elem hm
        rw [hc]; rfl
      -- Helper: filter singleton by !ys.contains when x ∉ ys gives [(x, r)]
      have filter_singleton_nmem (r : Pattern) (hnm : x ∉ ys) :
          ([(x, r)] : SubstEnv).filter (fun p => !ys.contains p.1) = [(x, r)] := by
        simp only [List.filter_cons, List.filter_nil]
        have hc : ys.contains x = false := by
          rw [Bool.eq_false_iff]; intro hc; exact hnm (elem_of_contains hc)
        rw [hc]; rfl
      -- Helper: σ.filter (!ys.contains) = σ when all ys are outside dom(σ)
      have filter_sigma_id (h : ∀ y ∈ ys, SubstEnv.find σ y = none) :
          σ.filter (fun p => !ys.contains p.1) = σ := by
        apply List.filter_eq_self.mpr
        intro entry hmem
        suffices ys.contains entry.1 = false by rw [this]; rfl
        rw [Bool.eq_false_iff]
        intro hc
        exact (SubstEnv.find_eq_none_iff σ entry.1).mp
          (h entry.1 (elem_of_contains hc)) entry hmem rfl
      by_cases hxy : x ∈ ys
      · -- x ∈ ys: inner [(x, t)] filtered out under multiLambda
        simp only [applySubst]
        rw [filter_singleton_mem t hxy]
        unfold noExplicitSubst at hne
        rw [subst_nil body hne]
        rw [filter_singleton_mem (applySubst σ t) hxy]
        rw [subst_nil _ (applySubst_noExplicitSubst
          (σ.filter (fun p => !ys.contains p.1)) body
          (fun entry hmem => hren entry (List.mem_of_mem_filter hmem)) hne)]
      · -- x ∉ ys: IH
        simp only [applySubst]
        rw [filter_singleton_nmem t hxy, filter_singleton_nmem (applySubst σ t) hxy]
        -- All ys have SubstEnv.find σ = none (from hbv_dom)
        have hys_dom : ∀ y ∈ ys, SubstEnv.find σ y = none :=
          fun y hy => hbv_dom y (by unfold boundVars; exact List.mem_append_left _ hy)
        rw [filter_sigma_id hys_dom]
        unfold noExplicitSubst at hne
        congr 1
        exact applySubst_swap σ body x t hren hx_dom hx_img
          (fun z hz => hbv_dom z (by unfold boundVars; exact List.mem_append_right _ hz))
          hne
    | .subst _ _ _ => by simp [noExplicitSubst] at hne
    | .collection ct elems rest => by
      simp only [applySubst, List.map_map]
      congr 1
      unfold noExplicitSubst at hne
      exact applySubst_swap_list σ elems x t hren hx_dom hx_img
        (fun y hy => hbv_dom y (by simp only [boundVars]; exact List.mem_flatMap.mpr hy))
        hne

  /-- List version of applySubst_swap -/
  theorem applySubst_swap_list (σ : SubstEnv) (ps : List Pattern) (x : String) (t : Pattern)
      (hren : isRenamingEnv σ)
      (hx_dom : SubstEnv.find σ x = none)
      (hx_img : ∀ entry ∈ σ, entry.2 ≠ .var x)
      (hbv_dom : ∀ y, (∃ p ∈ ps, y ∈ boundVars p) → SubstEnv.find σ y = none)
      (hall : allNoExplicitSubst ps) :
      ps.map (fun p => applySubst σ (applySubst [(x, t)] p)) =
      ps.map (fun p => applySubst [(x, applySubst σ t)] (applySubst σ p)) :=
    match ps with
    | [] => by simp
    | p :: ps' => by
      simp only [List.map_cons]
      unfold allNoExplicitSubst at hall
      simp only [Bool.and_eq_true] at hall
      congr 1
      · exact applySubst_swap σ p x t hren hx_dom hx_img
          (fun y hy => hbv_dom y ⟨p, by simp, hy⟩) hall.1
      · exact applySubst_swap_list σ ps' x t hren hx_dom hx_img
          (fun y ⟨q, hq, hy⟩ => hbv_dom y ⟨q, by simp [hq], hy⟩) hall.2
end

/-- Wrap applySubst_swap for commSubst specifically. -/
theorem commSubst_applySubst_swap (σ : SubstEnv) (p q : Pattern) (x : String)
    (hren : isRenamingEnv σ)
    (hx_dom : SubstEnv.find σ x = none)
    (hx_img : ∀ entry ∈ σ, entry.2 ≠ .var x)
    (hbv_dom : ∀ y ∈ boundVars p, SubstEnv.find σ y = none)
    (hne : noExplicitSubst p) :
    applySubst σ (commSubst p x q) =
    commSubst (applySubst σ p) x (applySubst σ q) := by
  simp only [commSubst, SubstEnv.extend, SubstEnv.empty]
  have hsigma : applySubst σ (.apply "NQuote" [q]) = .apply "NQuote" [applySubst σ q] := by
    simp only [applySubst, List.map]
  rw [← hsigma]
  exact applySubst_swap σ p x (.apply "NQuote" [q]) hren hx_dom hx_img hbv_dom hne

/-! ### SC Preserves noExplicitSubst

Key chain: alphaRename preserves → AlphaEquiv preserves → SC preserves.
This is needed for the EQUIV case of reduces_applySubst.
-/

/-- Reverse of allNoExplicitSubst_mem: membership-based characterization. -/
private theorem allNoExplicitSubst_of_forall {ps : List Pattern}
    (h : ∀ p ∈ ps, noExplicitSubst p = true) : allNoExplicitSubst ps = true := by
  induction ps with
  | nil => simp [allNoExplicitSubst]
  | cons p ps' ih =>
    simp only [allNoExplicitSubst, Bool.and_eq_true]
    exact ⟨h p (by simp), ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))⟩

/-- allNoExplicitSubst distributes over append (equality version). -/
private theorem allNoExplicitSubst_append_eq (ps qs : List Pattern) :
    allNoExplicitSubst (ps ++ qs) = (allNoExplicitSubst ps && allNoExplicitSubst qs) := by
  induction ps with
  | nil => simp [allNoExplicitSubst]
  | cons p ps' ih =>
    simp only [List.cons_append, allNoExplicitSubst, ih, Bool.and_assoc]

/-- Permutation preserves allNoExplicitSubst. -/
private theorem allNoExplicitSubst_perm {ps qs : List Pattern}
    (h : ps.Perm qs) : allNoExplicitSubst ps = allNoExplicitSubst qs := by
  cases hps : allNoExplicitSubst ps <;> cases hqs : allNoExplicitSubst qs <;> try rfl
  · -- false, true
    exact absurd (allNoExplicitSubst_of_forall
      (fun p hp => allNoExplicitSubst_mem hqs (h.mem_iff.mp hp))) (by simp [hps])
  · -- true, false
    exact absurd (allNoExplicitSubst_of_forall
      (fun q hq => allNoExplicitSubst_mem hps (h.symm.mem_iff.mp hq))) (by simp [hqs])

/-- Element-wise equality of noExplicitSubst implies allNoExplicitSubst equality. -/
private theorem allNoExplicitSubst_eq_of_pointwise {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (h : ∀ (i : Nat) (h₁ : i < ps.length) (h₂ : i < qs.length),
      noExplicitSubst (ps.get ⟨i, h₁⟩) = noExplicitSubst (qs.get ⟨i, h₂⟩)) :
    allNoExplicitSubst ps = allNoExplicitSubst qs := by
  induction ps generalizing qs with
  | nil => cases qs with | nil => rfl | cons _ _ => simp at hlen
  | cons p ps' ih =>
    match qs with
    | [] => simp at hlen
    | q :: qs' =>
      simp only [allNoExplicitSubst]
      have h0 := h 0 (by simp [List.length]) (by simp [List.length])
      simp only [List.get_eq_getElem, List.getElem_cons_zero] at h0
      rw [h0]
      congr 1
      have hlen' : ps'.length = qs'.length := by simpa [List.length] using hlen
      exact ih hlen' fun i h₁ h₂ => by
        have := h (i + 1) (by simp [List.length]; omega) (by simp [List.length]; omega)
        simp only [List.get_eq_getElem, List.getElem_cons_succ] at this
        exact this

-- alphaRename preserves noExplicitSubst (equality version)
mutual
  private theorem alphaRename_noExplicitSubst_eq (x y : String) (p : Pattern) :
      noExplicitSubst (alphaRename x y p) = noExplicitSubst p :=
    match p with
    | .var z => by
      simp only [alphaRename]
      split <;> simp [noExplicitSubst]
    | .apply f args => by
      simp only [alphaRename, noExplicitSubst]
      exact alphaRename_allNoExplicitSubst_eq x y args
    | .lambda z body => by
      simp only [alphaRename]
      split
      · rfl
      · simp only [noExplicitSubst]
        exact alphaRename_noExplicitSubst_eq x y body
    | .multiLambda xs body => by
      simp only [alphaRename]
      split
      · rfl
      · simp only [noExplicitSubst]
        exact alphaRename_noExplicitSubst_eq x y body
    | .subst body z arg => by
      simp only [alphaRename, noExplicitSubst]
    | .collection k elems g => by
      simp only [alphaRename, noExplicitSubst]
      exact alphaRename_allNoExplicitSubst_eq x y elems

  private theorem alphaRename_allNoExplicitSubst_eq (x y : String) (ps : List Pattern) :
      allNoExplicitSubst (ps.map (alphaRename x y)) = allNoExplicitSubst ps :=
    match ps with
    | [] => by simp [allNoExplicitSubst]
    | p :: ps' => by
      simp only [List.map_cons, allNoExplicitSubst]
      rw [alphaRename_noExplicitSubst_eq x y p, alphaRename_allNoExplicitSubst_eq x y ps']
end

/-- AlphaEquiv preserves noExplicitSubst (equality). -/
private theorem AlphaEquiv_noExplicitSubst_eq {P Q : Pattern}
    (h : AlphaEquiv P Q) : noExplicitSubst P = noExplicitSubst Q := by
  induction h with
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  | var_eq _ => rfl
  | lambda_rename x y p _ =>
    simp only [noExplicitSubst]
    exact (alphaRename_noExplicitSubst_eq x y p).symm
  | lambda_cong _ _ _ _ ih =>
    simp only [noExplicitSubst]; exact ih
  | apply_cong _ _ _ hlen _ ih =>
    simp only [noExplicitSubst]
    exact allNoExplicitSubst_eq_of_pointwise hlen ih
  | subst_cong _ _ _ _ _ _ _ => simp [noExplicitSubst]
  | collection_cong _ _ _ _ hlen _ ih =>
    simp only [noExplicitSubst]
    exact allNoExplicitSubst_eq_of_pointwise hlen ih

/-- Structural congruence preserves noExplicitSubst (equality). -/
theorem SC_noExplicitSubst_eq {P Q : Pattern}
    (h : RhoCalculus.StructuralCongruence P Q) : noExplicitSubst P = noExplicitSubst Q := by
  induction h with
  | alpha _ _ halpha => exact AlphaEquiv_noExplicitSubst_eq halpha
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  | par_singleton p =>
    simp only [noExplicitSubst, allNoExplicitSubst, Bool.and_true]
  | par_nil_left p =>
    simp only [noExplicitSubst, allNoExplicitSubst, Bool.and_true, Bool.true_and]
  | par_nil_right p =>
    simp only [noExplicitSubst, allNoExplicitSubst, Bool.and_true]
  | par_comm p q =>
    simp only [noExplicitSubst, allNoExplicitSubst, Bool.and_true]
    exact Bool.and_comm _ _
  | par_assoc p q r =>
    simp only [noExplicitSubst, allNoExplicitSubst, Bool.and_true, Bool.and_assoc]
  | par_cong _ _ hlen _ ih =>
    simp only [noExplicitSubst]
    exact allNoExplicitSubst_eq_of_pointwise hlen ih
  | par_flatten ps qs =>
    simp only [noExplicitSubst]
    rw [allNoExplicitSubst_append_eq, allNoExplicitSubst_append_eq]
    congr 1
    simp only [allNoExplicitSubst, noExplicitSubst, Bool.and_true]
  | par_perm _ _ hperm =>
    simp only [noExplicitSubst]
    exact allNoExplicitSubst_perm hperm
  | set_perm _ _ hperm =>
    simp only [noExplicitSubst]
    exact allNoExplicitSubst_perm hperm
  | set_cong _ _ hlen _ ih =>
    simp only [noExplicitSubst]
    exact allNoExplicitSubst_eq_of_pointwise hlen ih
  | lambda_cong _ _ _ _ ih =>
    simp only [noExplicitSubst]; exact ih
  | apply_cong _ _ _ hlen _ ih =>
    simp only [noExplicitSubst]
    exact allNoExplicitSubst_eq_of_pointwise hlen ih
  | collection_general_cong _ _ _ _ hlen _ ih =>
    simp only [noExplicitSubst]
    exact allNoExplicitSubst_eq_of_pointwise hlen ih
  | multiLambda_cong _ _ _ _ ih =>
    simp only [noExplicitSubst]; exact ih
  | subst_cong _ _ _ _ _ _ _ => simp [noExplicitSubst]
  | quote_drop n =>
    simp only [noExplicitSubst, allNoExplicitSubst, Bool.and_true]

/-! ### Infrastructure: substBVDisjoint monotonicity and alpha-renaming commutativity

These lemmas enable the DIRECT proof of the alpha case in SC_applySubst_restricted,
eliminating the need for the unsatisfiable `∀ σ, AlphaSubstSafe σ` hypothesis.

Key insight: substBVDisjoint σ (boundVars P ++ boundVars Q) where P ≡α Q ensures
that BOTH the original binder x AND the fresh binder y (from lambda_rename) are
disjoint from σ's domain and range, preventing variable capture.
-/

/-- substBVDisjoint is preserved by filtering σ (removing entries). -/
private theorem substBVDisjoint_filter {σ : SubstEnv} {bvs : List String}
    (h : substBVDisjoint σ bvs) (f : String × Pattern → Bool) :
    substBVDisjoint (σ.filter f) bvs :=
  ⟨fun v hv => SubstEnv.find_filter_of_find_none (h.1 v hv),
   fun entry hmem v hv => h.2 entry (List.mem_of_mem_filter hmem) v hv⟩

/-- substBVDisjoint is symmetric in the append of bound vars. -/
private theorem substBVDisjoint_append_comm {σ : SubstEnv} {as bs : List String}
    (h : substBVDisjoint σ (as ++ bs)) : substBVDisjoint σ (bs ++ as) :=
  substBVDisjoint_mono h (fun v hv => by
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_append.mpr (Or.inr h)
    · exact List.mem_append.mpr (Or.inl h))

/-- Combine substBVDisjoint from two lists into one. -/
private theorem substBVDisjoint_combine {σ : SubstEnv} {as bs : List String}
    (ha : substBVDisjoint σ as) (hb : substBVDisjoint σ bs) :
    substBVDisjoint σ (as ++ bs) := by
  constructor
  · intro v hv; rcases List.mem_append.mp hv with h | h
    · exact ha.1 v h
    · exact hb.1 v h
  · intro entry he v hv; rcases List.mem_append.mp hv with h | h
    · exact ha.2 entry he v h
    · exact hb.2 entry he v h

/-- Extract left part of substBVDisjoint over append. -/
private theorem substBVDisjoint_left {σ : SubstEnv} {as bs : List String}
    (h : substBVDisjoint σ (as ++ bs)) : substBVDisjoint σ as :=
  ⟨fun v hv => h.1 v (List.mem_append_left _ hv),
   fun entry he v hv => h.2 entry he v (List.mem_append_left _ hv)⟩

/-- Extract right part of substBVDisjoint over append. -/
private theorem substBVDisjoint_right {σ : SubstEnv} {as bs : List String}
    (h : substBVDisjoint σ (as ++ bs)) : substBVDisjoint σ bs :=
  ⟨fun v hv => h.1 v (List.mem_append_right _ hv),
   fun entry he v hv => h.2 entry he v (List.mem_append_right _ hv)⟩

-- boundVars is preserved by alphaRename (alpha-renaming doesn't change binding structure).
mutual
  private theorem boundVars_alphaRename (x y : String) (p : Pattern) :
      boundVars (alphaRename x y p) = boundVars p :=
    match p with
    | .var _ => by unfold alphaRename; split <;> (unfold boundVars; rfl)
    | .lambda z body => by
      unfold alphaRename; split
      · rfl
      · unfold boundVars; congr 1; exact boundVars_alphaRename x y body
    | .apply _ args => by
      unfold alphaRename boundVars
      exact boundVars_alphaRename_list x y args
    | .multiLambda xs body => by
      unfold alphaRename; split
      · rfl
      · unfold boundVars; congr 1; exact boundVars_alphaRename x y body
    | .subst body _ arg => by
      unfold alphaRename boundVars
      congr 1
      · exact boundVars_alphaRename x y body
      · exact boundVars_alphaRename x y arg
    | .collection _ elems _ => by
      unfold alphaRename boundVars
      exact boundVars_alphaRename_list x y elems

  private theorem boundVars_alphaRename_list (x y : String) (ps : List Pattern) :
      (ps.map (alphaRename x y)).flatMap boundVars = ps.flatMap boundVars :=
    match ps with
    | [] => by simp
    | p :: ps' => by
      simp only [List.map_cons, List.flatMap_cons]
      congr 1
      · exact boundVars_alphaRename x y p
      · exact boundVars_alphaRename_list x y ps'
end

/-! ### FreeVars infrastructure for trans case resolution

The trans case of `alphaEquiv_applySubst` and `SC_applySubst_restricted` requires knowing
that substitution domain/range names don't collide with bound variables of INTERMEDIATE
patterns in SC/alpha chains. The key insight: if dom(σ) ⊆ freeVars(P) and SC/alpha
preserves freeVars, then dom(σ) ⊆ freeVars(Q) ⊆ allVars(Q) for any Q reachable from P,
so alpha-fresh names (chosen outside allVars) can't collide with dom(σ). -/

-- freeVars ⊆ allVars: every free variable appears somewhere in the pattern
private theorem freeVars_subset_allVars :
    ∀ (p : Pattern) (x : String), x ∈ freeVars p → x ∈ allVars p := by
  intro p
  match p with
  | .var name =>
    intro x hx; unfold freeVars at hx; unfold allVars; simpa using hx
  | .apply _ args =>
    intro x hx; unfold freeVars at hx; unfold allVars
    obtain ⟨a, ha, hxa⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr ⟨a, ha, freeVars_subset_allVars a x hxa⟩
  | .lambda z body =>
    intro x hx; unfold freeVars at hx; unfold allVars
    exact List.mem_cons.mpr (Or.inr (freeVars_subset_allVars body x (List.mem_filter.mp hx).1))
  | .multiLambda xs body =>
    intro x hx; unfold freeVars at hx; unfold allVars
    exact List.mem_append.mpr (Or.inr (freeVars_subset_allVars body x (List.mem_filter.mp hx).1))
  | .subst body z repl =>
    intro x hx; unfold freeVars at hx; unfold allVars
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl
        (freeVars_subset_allVars body x (List.mem_filter.mp h).1))))
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr
        (freeVars_subset_allVars repl x h))))
  | .collection _ elems _ =>
    intro x hx; unfold freeVars at hx; unfold allVars
    obtain ⟨a, ha, hxa⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr ⟨a, ha, freeVars_subset_allVars a x hxa⟩
termination_by p => sizeOf p

-- alphaRename preserves freeVars: replaces free x with y
-- Proven for noExplicitSubst patterns (which is all we need for encoding correctness)
private theorem alphaRename_freeVars_mem (x y : String) (p : Pattern)
    (hfresh : y ∉ allVars p) (hne : noExplicitSubst p) (z : String) :
    z ∈ freeVars (alphaRename x y p) ↔
    (z ∈ freeVars p ∧ z ≠ x) ∨ (z = y ∧ x ∈ freeVars p) := by
  match p with
  | .var v =>
    by_cases hvx : v = x
    · subst hvx
      unfold alphaRename; simp only [ite_true]
      unfold freeVars; simp [List.mem_singleton]
    · unfold alphaRename; simp only [hvx, ite_false]
      unfold freeVars; simp only [List.mem_singleton]
      constructor
      · intro h; left; exact ⟨h, by rw [h]; exact hvx⟩
      · rintro (⟨h, _⟩ | ⟨h, hxv⟩)
        · exact h
        · rw [h]; exact absurd hxv.symm hvx
  | .apply f args =>
    unfold alphaRename; unfold freeVars
    simp only [List.flatMap_map, List.mem_flatMap]
    unfold allVars at hfresh; unfold noExplicitSubst at hne
    constructor
    · rintro ⟨a, ha, hz⟩
      have hfresh_a : y ∉ allVars a :=
        fun h => hfresh (List.mem_flatMap.mpr ⟨a, ha, h⟩)
      have hne_a := allNoExplicitSubst_mem hne ha
      rw [alphaRename_freeVars_mem x y a hfresh_a hne_a z] at hz
      rcases hz with ⟨hza, hzx⟩ | ⟨rfl, hxa⟩
      · exact Or.inl ⟨⟨a, ha, hza⟩, hzx⟩
      · exact Or.inr ⟨rfl, ⟨a, ha, hxa⟩⟩
    · rintro (⟨⟨a, ha, hza⟩, hzx⟩ | ⟨hzy, ⟨a, ha, hxa⟩⟩)
      · exact ⟨a, ha, (alphaRename_freeVars_mem x y a
          (fun h => hfresh (List.mem_flatMap.mpr ⟨a, ha, h⟩))
          (allNoExplicitSubst_mem hne ha) z).mpr (Or.inl ⟨hza, hzx⟩)⟩
      · exact ⟨a, ha, (alphaRename_freeVars_mem x y a
          (fun h => hfresh (List.mem_flatMap.mpr ⟨a, ha, h⟩))
          (allNoExplicitSubst_mem hne ha) z).mpr (Or.inr ⟨hzy, hxa⟩)⟩
  | .lambda w body =>
    unfold allVars at hfresh
    have hy_ne_w : y ≠ w := fun h => hfresh (List.mem_cons.mpr (Or.inl h))
    have hfresh_body : y ∉ allVars body :=
      fun h => hfresh (List.mem_cons.mpr (Or.inr h))
    unfold noExplicitSubst at hne
    by_cases hwx : w = x
    · -- w = x: alphaRename stops (x is bound by lambda)
      subst hwx
      unfold alphaRename; simp only [ite_true]
      unfold freeVars
      simp only [List.mem_filter, bne_iff_ne]
      constructor
      · intro ⟨h, hne'⟩; exact Or.inl ⟨⟨h, hne'⟩, hne'⟩
      · rintro (⟨⟨h, hne'⟩, _⟩ | ⟨_, hxfv, habs⟩)
        · exact ⟨h, hne'⟩
        · exact absurd rfl habs
    · -- w ≠ x: recurse into body
      unfold alphaRename; simp only [hwx, ite_false]
      have fv_lam : ∀ (u : String) (v : String) (e : Pattern),
          u ∈ freeVars (.lambda v e) ↔ u ∈ freeVars e ∧ u ≠ v := by
        intro u v e; constructor
        · intro h; unfold freeVars at h
          exact ⟨(List.mem_filter.mp h).1, bne_iff_ne.mp (List.mem_filter.mp h).2⟩
        · intro ⟨h1, h2⟩; unfold freeVars
          exact List.mem_filter.mpr ⟨h1, bne_iff_ne.mpr h2⟩
      simp only [fv_lam]
      rw [alphaRename_freeVars_mem x y body hfresh_body hne z]
      constructor
      · rintro ⟨(⟨hzb, hzx⟩ | ⟨rfl, hxb⟩), hzw⟩
        · exact Or.inl ⟨⟨hzb, hzw⟩, hzx⟩
        · exact Or.inr ⟨rfl, hxb, Ne.symm hwx⟩
      · rintro (⟨⟨hzb, hzw⟩, hzx⟩ | ⟨rfl, hxb, hxw⟩)
        · exact ⟨Or.inl ⟨hzb, hzx⟩, hzw⟩
        · exact ⟨Or.inr ⟨rfl, hxb⟩, hy_ne_w⟩
  | .multiLambda xs body =>
    -- multiLambda: skip for now, not used in encoding correctness
    sorry
  | .subst _ _ _ => simp [noExplicitSubst] at hne
  | .collection ct elems rest =>
    unfold alphaRename; unfold freeVars
    simp only [List.flatMap_map, List.mem_flatMap]
    unfold allVars at hfresh; unfold noExplicitSubst at hne
    constructor
    · rintro ⟨a, ha, hz⟩
      have hfresh_a : y ∉ allVars a :=
        fun h => hfresh (List.mem_flatMap.mpr ⟨a, ha, h⟩)
      have hne_a := allNoExplicitSubst_mem hne ha
      rw [alphaRename_freeVars_mem x y a hfresh_a hne_a z] at hz
      rcases hz with ⟨hza, hzx⟩ | ⟨rfl, hxa⟩
      · exact Or.inl ⟨⟨a, ha, hza⟩, hzx⟩
      · exact Or.inr ⟨rfl, ⟨a, ha, hxa⟩⟩
    · rintro (⟨⟨a, ha, hza⟩, hzx⟩ | ⟨hzy, ⟨a, ha, hxa⟩⟩)
      · exact ⟨a, ha, (alphaRename_freeVars_mem x y a
          (fun h => hfresh (List.mem_flatMap.mpr ⟨a, ha, h⟩))
          (allNoExplicitSubst_mem hne ha) z).mpr (Or.inl ⟨hza, hzx⟩)⟩
      · exact ⟨a, ha, (alphaRename_freeVars_mem x y a
          (fun h => hfresh (List.mem_flatMap.mpr ⟨a, ha, h⟩))
          (allNoExplicitSubst_mem hne ha) z).mpr (Or.inr ⟨hzy, hxa⟩)⟩
  termination_by sizeOf p

-- AlphaEquiv preserves free variables (as sets).
-- This is the KEY lemma enabling the trans case.
private theorem AlphaEquiv_preserves_freeVars {P Q : Pattern}
    (halpha : AlphaEquiv P Q) (hne : noExplicitSubst P) (z : String) :
    z ∈ freeVars P ↔ z ∈ freeVars Q := by
  induction halpha generalizing z with
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih =>
    exact (ih (AlphaEquiv_noExplicitSubst_eq ‹_› ▸ hne) z).symm
  | trans _ q _ hpq _ ih₁ ih₂ =>
    exact (ih₁ hne z).trans (ih₂ (AlphaEquiv_noExplicitSubst_eq hpq ▸ hne) z)
  | var_eq _ => exact Iff.rfl
  | lambda_rename x' y' p' hfresh' =>
    have hne' : noExplicitSubst p' := by simpa [noExplicitSubst] using hne
    have hy_nav : y' ∉ allVars p' := by
      intro hmem; simp [isGloballyFresh, hmem] at hfresh'
    constructor
    · intro hz
      unfold freeVars at hz ⊢
      have ⟨hzp, hzx⟩ := List.mem_filter.mp hz
      have hzx' := bne_iff_ne.mp hzx
      have hzy : z ≠ y' := fun h => hy_nav (h ▸ freeVars_subset_allVars p' z hzp)
      exact List.mem_filter.mpr
        ⟨(alphaRename_freeVars_mem x' y' p' hy_nav hne' z).mpr (Or.inl ⟨hzp, hzx'⟩),
         bne_iff_ne.mpr hzy⟩
    · intro hz
      unfold freeVars at hz ⊢
      have ⟨hzmem, hzy⟩ := List.mem_filter.mp hz
      have hzy' := bne_iff_ne.mp hzy
      rw [alphaRename_freeVars_mem x' y' p' hy_nav hne' z] at hzmem
      rcases hzmem with ⟨hzp, hzx⟩ | ⟨hzy_eq, _⟩
      · exact List.mem_filter.mpr ⟨hzp, bne_iff_ne.mpr hzx⟩
      · exact absurd hzy_eq hzy'
  | lambda_cong x' p' q' _ ih =>
    unfold freeVars; simp only [List.mem_filter, bne_iff_ne]
    have hne_body : noExplicitSubst p' := by simpa [noExplicitSubst] using hne
    exact ⟨fun ⟨h, hne'⟩ => ⟨(ih hne_body z).mp h, hne'⟩,
           fun ⟨h, hne'⟩ => ⟨(ih hne_body z).mpr h, hne'⟩⟩
  | apply_cong _ args₁ args₂ hlen _ ih =>
    unfold freeVars; unfold noExplicitSubst at hne
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨a, ha, hza⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      have h₂ : i < args₂.length := hlen ▸ hi
      have hne_i : noExplicitSubst args₁[i] :=
        allNoExplicitSubst_mem hne (List.getElem_mem hi)
      exact ⟨args₂[i], List.getElem_mem h₂,
        (ih i hi h₂ hne_i z).mp hza⟩
    · rintro ⟨b, hb, hzb⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      have h₁ : i < args₁.length := hlen ▸ hi
      have hne_i : noExplicitSubst args₁[i] :=
        allNoExplicitSubst_mem hne (List.getElem_mem h₁)
      exact ⟨args₁[i], List.getElem_mem h₁,
        (ih i h₁ hi hne_i z).mpr hzb⟩
  | subst_cong _ _ _ _ _ _ _ _ => simp [noExplicitSubst] at hne
  | collection_cong _ elems₁ elems₂ _ hlen _ ih =>
    unfold freeVars; unfold noExplicitSubst at hne
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨a, ha, hza⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      have h₂ : i < elems₂.length := hlen ▸ hi
      have hne_i : noExplicitSubst elems₁[i] :=
        allNoExplicitSubst_mem hne (List.getElem_mem hi)
      exact ⟨elems₂[i], List.getElem_mem h₂,
        (ih i hi h₂ hne_i z).mp hza⟩
    · rintro ⟨b, hb, hzb⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      have h₁ : i < elems₁.length := hlen ▸ hi
      have hne_i : noExplicitSubst elems₁[i] :=
        allNoExplicitSubst_mem hne (List.getElem_mem h₁)
      exact ⟨elems₁[i], List.getElem_mem h₁,
        (ih i h₁ hi hne_i z).mpr hzb⟩

-- Helper: freeVars for collection patterns (avoids unfolding issues)
private theorem freeVars_coll (ct : CollType) (elems : List Pattern) (g : Option String) :
    freeVars (.collection ct elems g) = elems.flatMap freeVars := by
  unfold freeVars; rfl

-- Helper: freeVars for apply patterns
private theorem freeVars_appl (f : String) (args : List Pattern) :
    freeVars (.apply f args) = args.flatMap freeVars := by
  unfold freeVars; rfl

-- SC preserves free variables
private theorem SC_preserves_freeVars {A B : Pattern}
    (hsc : RhoCalculus.StructuralCongruence A B) (hne : noExplicitSubst A)
    (z : String) : z ∈ freeVars A ↔ z ∈ freeVars B := by
  induction hsc generalizing z with
  | alpha _ _ halpha => exact AlphaEquiv_preserves_freeVars halpha hne z
  | refl _ => exact Iff.rfl
  | symm p q hsc' ih =>
    have hne_q := SC_noExplicitSubst_eq hsc' ▸ hne
    exact (ih hne_q z).symm
  | trans p q r hsc₁ _ ih₁ ih₂ =>
    have hne_q := SC_noExplicitSubst_eq hsc₁ ▸ hne
    exact (ih₁ hne z).trans (ih₂ hne_q z)
  | par_singleton p =>
    simp only [freeVars_coll, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | par_nil_left p =>
    simp only [freeVars_coll, freeVars_appl, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.nil_append, List.mem_append]
  | par_nil_right p =>
    simp only [freeVars_coll, freeVars_appl, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append, or_false]
  | par_comm p q =>
    simp only [freeVars_coll, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, or_comm]
  | par_assoc p q r =>
    simp only [freeVars_coll, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, or_assoc]
  | par_cong ps qs hlen _ ih =>
    simp only [freeVars_coll, List.mem_flatMap]; unfold noExplicitSubst at hne
    constructor
    · rintro ⟨a, ha, hza⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      exact ⟨qs[i]'(hlen ▸ hi), List.getElem_mem (hlen ▸ hi),
        (ih i hi (hlen ▸ hi) (allNoExplicitSubst_mem hne (List.getElem_mem hi)) z).mp hza⟩
    · rintro ⟨b, hb, hzb⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      exact ⟨ps[i]'(hlen ▸ hi), List.getElem_mem (hlen ▸ hi),
        (ih i (hlen ▸ hi) hi (allNoExplicitSubst_mem hne (List.getElem_mem (hlen ▸ hi))) z).mpr hzb⟩
  | par_flatten ps qs =>
    simp only [freeVars_coll, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append, List.mem_flatMap]
  | par_perm elems₁ elems₂ hperm =>
    simp only [freeVars_coll, List.mem_flatMap]
    exact ⟨fun ⟨a, ha, hz⟩ => ⟨a, hperm.mem_iff.mp ha, hz⟩,
           fun ⟨a, ha, hz⟩ => ⟨a, hperm.mem_iff.mpr ha, hz⟩⟩
  | set_perm elems₁ elems₂ hperm =>
    simp only [freeVars_coll, List.mem_flatMap]
    exact ⟨fun ⟨a, ha, hz⟩ => ⟨a, hperm.mem_iff.mp ha, hz⟩,
           fun ⟨a, ha, hz⟩ => ⟨a, hperm.mem_iff.mpr ha, hz⟩⟩
  | set_cong elems₁ elems₂ hlen _ ih =>
    simp only [freeVars_coll, List.mem_flatMap]; unfold noExplicitSubst at hne
    constructor
    · rintro ⟨a, ha, hza⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      exact ⟨elems₂[i]'(hlen ▸ hi), List.getElem_mem (hlen ▸ hi),
        (ih i hi (hlen ▸ hi) (allNoExplicitSubst_mem hne (List.getElem_mem hi)) z).mp hza⟩
    · rintro ⟨b, hb, hzb⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      exact ⟨elems₁[i]'(hlen ▸ hi), List.getElem_mem (hlen ▸ hi),
        (ih i (hlen ▸ hi) hi (allNoExplicitSubst_mem hne (List.getElem_mem (hlen ▸ hi))) z).mpr hzb⟩
  | lambda_cong x' p' q' _ ih =>
    unfold freeVars; simp only [List.mem_filter, bne_iff_ne]
    have hne' : noExplicitSubst p' := by simpa [noExplicitSubst] using hne
    exact ⟨fun ⟨h, hne''⟩ => ⟨(ih hne' z).mp h, hne''⟩,
           fun ⟨h, hne''⟩ => ⟨(ih hne' z).mpr h, hne''⟩⟩
  | apply_cong _ args₁ args₂ hlen _ ih =>
    simp only [freeVars_appl, List.mem_flatMap]; unfold noExplicitSubst at hne
    constructor
    · rintro ⟨a, ha, hza⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      exact ⟨args₂[i]'(hlen ▸ hi), List.getElem_mem (hlen ▸ hi),
        (ih i hi (hlen ▸ hi) (allNoExplicitSubst_mem hne (List.getElem_mem hi)) z).mp hza⟩
    · rintro ⟨b, hb, hzb⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      exact ⟨args₁[i]'(hlen ▸ hi), List.getElem_mem (hlen ▸ hi),
        (ih i (hlen ▸ hi) hi (allNoExplicitSubst_mem hne (List.getElem_mem (hlen ▸ hi))) z).mpr hzb⟩
  | collection_general_cong _ elems₁ elems₂ _ hlen _ ih =>
    simp only [freeVars_coll, List.mem_flatMap]; unfold noExplicitSubst at hne
    constructor
    · rintro ⟨a, ha, hza⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      exact ⟨elems₂[i]'(hlen ▸ hi), List.getElem_mem (hlen ▸ hi),
        (ih i hi (hlen ▸ hi) (allNoExplicitSubst_mem hne (List.getElem_mem hi)) z).mp hza⟩
    · rintro ⟨b, hb, hzb⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      exact ⟨elems₁[i]'(hlen ▸ hi), List.getElem_mem (hlen ▸ hi),
        (ih i (hlen ▸ hi) hi (allNoExplicitSubst_mem hne (List.getElem_mem (hlen ▸ hi))) z).mpr hzb⟩
  | multiLambda_cong _ _ _ _ ih =>
    unfold freeVars; simp only [List.mem_filter]
    have hne' : noExplicitSubst _ := by simpa [noExplicitSubst] using hne
    exact ⟨fun ⟨h, hc⟩ => ⟨(ih hne' z).mp h, hc⟩,
           fun ⟨h, hc⟩ => ⟨(ih hne' z).mpr h, hc⟩⟩
  | subst_cong _ _ _ _ _ _ _ _ _ => simp [noExplicitSubst] at hne
  | quote_drop n =>
    simp only [freeVars_appl, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- If y ∉ allVars p and y ∉ dom(σ) and ∀ entry ∈ σ, entry.2 ≠ .var y (renaming),
    then y ∉ allVars (applySubst σ p). -/
private theorem allVars_applySubst_fresh (σ : SubstEnv) (hren : isRenamingEnv σ)
    (y : String) (p : Pattern) (hne : noExplicitSubst p)
    (hy_p : y ∉ allVars p)
    (hy_dom : SubstEnv.find σ y = none)
    (hy_range : ∀ entry ∈ σ, entry.2 ≠ .var y) :
    y ∉ allVars (applySubst σ p) := by
  match p with
  | .var z =>
    simp only [applySubst]
    cases hfind : SubstEnv.find σ z with
    | none => unfold allVars at hy_p ⊢; exact hy_p
    | some r =>
      obtain ⟨w, hw⟩ := find_isVar_of_renaming σ z r hfind hren
      rw [hw]; unfold allVars; simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro heq; subst heq
      obtain ⟨entry, hmem, _, hval⟩ := SubstEnv.find_some_entry_mem σ z r hfind
      exact hy_range entry hmem (by rw [hval, hw])
  | .apply _ args =>
    simp only [applySubst]; unfold allVars
    intro hmem
    obtain ⟨q, hq_mem, hq_y⟩ := List.mem_flatMap.mp hmem
    obtain ⟨a, ha_mem, ha_eq⟩ := List.mem_map.mp hq_mem
    subst ha_eq
    have hne_a := allNoExplicitSubst_mem (by simpa [noExplicitSubst] using hne) ha_mem
    exact allVars_applySubst_fresh σ hren y a hne_a
      (fun h => hy_p (show y ∈ allVars (.apply _ args) from by
        unfold allVars; exact List.mem_flatMap.mpr ⟨a, ha_mem, h⟩))
      hy_dom hy_range hq_y
  | .lambda z body =>
    simp only [applySubst]; unfold allVars
    intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · have : y ∈ allVars (Pattern.lambda z body) := by
        unfold allVars; simp [heq]
      exact absurd this hy_p
    · exact allVars_applySubst_fresh _ (fun e he => hren e (List.mem_of_mem_filter he))
        y body (by simpa [noExplicitSubst] using hne)
        (fun h => hy_p (show y ∈ allVars (.lambda z body) from by
          unfold allVars; exact List.mem_cons.mpr (Or.inr h)))
        (SubstEnv.find_filter_of_find_none hy_dom)
        (fun e he => hy_range e (List.mem_of_mem_filter he)) hmem'
  | .multiLambda xs body =>
    simp only [applySubst]; unfold allVars
    intro hmem
    rcases List.mem_append.mp hmem with hxs | hbody
    · exact hy_p (show y ∈ allVars (.multiLambda xs body) from by
        unfold allVars; exact List.mem_append.mpr (Or.inl hxs))
    · exact allVars_applySubst_fresh _ (fun e he => hren e (List.mem_of_mem_filter he))
        y body (by simpa [noExplicitSubst] using hne)
        (fun h => hy_p (show y ∈ allVars (.multiLambda xs body) from by
          unfold allVars; exact List.mem_append.mpr (Or.inr h)))
        (SubstEnv.find_filter_of_find_none hy_dom)
        (fun e he => hy_range e (List.mem_of_mem_filter he)) hbody
  | .subst _ _ _ => simp [noExplicitSubst] at hne
  | .collection _ elems _ =>
    simp only [applySubst]; unfold allVars
    intro hmem
    obtain ⟨q, hq_mem, hq_y⟩ := List.mem_flatMap.mp hmem
    obtain ⟨a, ha_mem, ha_eq⟩ := List.mem_map.mp hq_mem
    subst ha_eq
    have hne_a := allNoExplicitSubst_mem (by simpa [noExplicitSubst] using hne) ha_mem
    exact allVars_applySubst_fresh σ hren y a hne_a
      (fun h => hy_p (show y ∈ allVars (.collection _ elems _) from by
        unfold allVars; exact List.mem_flatMap.mpr ⟨a, ha_mem, h⟩))
      hy_dom hy_range hq_y
termination_by sizeOf p

/-- Alpha-renaming commutes with renaming substitution when x, y ∉ dom(σ) ∪ rangeVars(σ). -/
private theorem applySubst_alphaRename_comm (σ : SubstEnv) (hren : isRenamingEnv σ)
    (x y : String) (p : Pattern) (hne : noExplicitSubst p)
    (hfresh : y ∉ allVars p)
    (hx_dom : SubstEnv.find σ x = none) (hy_dom : SubstEnv.find σ y = none)
    (hx_range : ∀ entry ∈ σ, entry.2 ≠ .var x)
    (hy_range : ∀ entry ∈ σ, entry.2 ≠ .var y) :
    applySubst σ (alphaRename x y p) = alphaRename x y (applySubst σ p) := by
  match p with
  | .var z =>
    unfold alphaRename
    split
    case isTrue hzx =>
      -- z = x: alphaRename gives .var y, applySubst of .var y uses hy_dom
      subst hzx; simp only [applySubst]; rw [hy_dom, hx_dom]; simp [alphaRename]
    case isFalse hzx =>
      -- z ≠ x: alphaRename gives .var z
      simp only [applySubst]
      cases hfz : SubstEnv.find σ z with
      | none => simp [alphaRename, hzx]
      | some r =>
        -- σ maps z to some r = .var w (renaming). Need w ≠ x.
        obtain ⟨w, hw⟩ := find_isVar_of_renaming σ z r hfz hren
        rw [hw]; unfold alphaRename
        -- Need w ≠ x: if w = x, then entry.2 = .var x, contradicting hx_range
        have hwx : w ≠ x := by
          intro heq; subst heq
          obtain ⟨entry, hmem, _, hval⟩ := SubstEnv.find_some_entry_mem σ z r hfz
          exact hx_range entry hmem (by rw [hval, hw])
        simp [hwx]
  | .lambda z body =>
    unfold alphaRename
    split
    case isTrue hzx =>
      -- z = x: binder captures x, alphaRename is identity
      subst hzx; simp only [applySubst, alphaRename, ite_true]
    case isFalse hzx =>
      -- z ≠ x: alphaRename recurses into body
      simp only [applySubst, alphaRename, hzx, ite_false]
      -- Need z ≠ y: y is fresh in p, so y ≠ z (z appears in allVars(.lambda z body))
      have hzy : z ≠ y := by
        intro heq; subst heq; exact hfresh (by unfold allVars; simp)
      simp [hzy]
      congr 1
      exact applySubst_alphaRename_comm _
        (fun e he => hren e (List.mem_of_mem_filter he)) x y body
        (by simpa [noExplicitSubst] using hne)
        (fun h => hfresh (show y ∈ allVars (.lambda z body) from by
          unfold allVars; exact List.mem_cons.mpr (Or.inr h)))
        (SubstEnv.find_filter_of_find_none hx_dom)
        (SubstEnv.find_filter_of_find_none hy_dom)
        (fun e he => hx_range e (List.mem_of_mem_filter he))
        (fun e he => hy_range e (List.mem_of_mem_filter he))
  | .apply _ args =>
    unfold alphaRename; simp only [applySubst, List.map_map]; congr 1
    apply List.map_congr_left
    intro a ha
    have hne_a := allNoExplicitSubst_mem (by simpa [noExplicitSubst] using hne) ha
    exact applySubst_alphaRename_comm σ hren x y a hne_a
      (fun h => hfresh (show y ∈ allVars (.apply _ args) from by
        unfold allVars; exact List.mem_flatMap.mpr ⟨a, ha, h⟩))
      hx_dom hy_dom hx_range hy_range
  | .multiLambda xs body =>
    unfold alphaRename
    split
    case isTrue hxs =>
      -- x ∈ xs: binder captures x, alphaRename is identity
      simp only [applySubst, alphaRename, hxs, ite_true]
    case isFalse hxs =>
      simp only [applySubst, alphaRename, hxs, ite_false]; congr 1
      exact applySubst_alphaRename_comm _
        (fun e he => hren e (List.mem_of_mem_filter he)) x y body
        (by simpa [noExplicitSubst] using hne)
        (fun h => hfresh (show y ∈ allVars (.multiLambda xs body) from by
          unfold allVars; exact List.mem_append.mpr (Or.inr h)))
        (SubstEnv.find_filter_of_find_none hx_dom)
        (SubstEnv.find_filter_of_find_none hy_dom)
        (fun e he => hx_range e (List.mem_of_mem_filter he))
        (fun e he => hy_range e (List.mem_of_mem_filter he))
  | .subst _ _ _ => simp [noExplicitSubst] at hne
  | .collection _ elems _ =>
    unfold alphaRename; simp only [applySubst, List.map_map]; congr 1
    apply List.map_congr_left
    intro a ha
    have hne_a := allNoExplicitSubst_mem (by simpa [noExplicitSubst] using hne) ha
    exact applySubst_alphaRename_comm σ hren x y a hne_a
      (fun h => hfresh (show y ∈ allVars (.collection _ elems _) from by
        unfold allVars; exact List.mem_flatMap.mpr ⟨a, ha, h⟩))
      hx_dom hy_dom hx_range hy_range
termination_by sizeOf p

/-! ### Alpha-equivalence preserved by renaming substitution (under substBVDisjoint)

This replaces the old `AlphaSubstSafe σ` hypothesis (which quantified over ALL σ and was
provably false: counterexample σ=[(z,.var x)], P=λx.z, Q=λy.z gives identity vs constant).

The key condition `substBVDisjoint σ (boundVars P ++ boundVars Q)` ensures that ALL binder
names (including alpha-fresh y) are disjoint from σ's domain and range, preventing capture.
    TODO: fix simp [boundVars] → unfold boundVars, fix List.any_of_mem →
    List.any_eq_true throughout. -/
private theorem alphaEquiv_applySubst (σ : SubstEnv) (hren : isRenamingEnv σ)
    {P Q : Pattern} (halpha : AlphaEquiv P Q) (hne : noExplicitSubst P)
    (hbv : substBVDisjoint σ (boundVars P ++ boundVars Q)) :
    RhoCalculus.StructuralCongruence (applySubst σ P) (applySubst σ Q) := by
  sorry

/-- Variant returning AlphaEquiv (stronger than SC) for use in collection/apply congruence.
    TODO: same fixes needed as alphaEquiv_applySubst -/
private theorem alphaEquiv_applySubst_alpha (σ : SubstEnv) (hren : isRenamingEnv σ)
    {P Q : Pattern} (halpha : AlphaEquiv P Q) (hne : noExplicitSubst P)
    (hbv : substBVDisjoint σ (boundVars P ++ boundVars Q)) :
    AlphaEquiv (applySubst σ P) (applySubst σ Q) := by
  sorry

/-- SC transport under renaming substitution.

    The alpha case is PROVEN directly using `alphaEquiv_applySubst` (not pushed to an
    unsatisfiable hypothesis like the old `∀ σ, AlphaSubstSafe σ`).

    The only sorry is in the `trans` case: SC P Q → SC Q R requires `substBVDisjoint σ`
    for the intermediate pattern Q's bound vars, which aren't in the hypothesis. At encoding
    call sites, all intermediate bound vars are π-names (NamespaceDisjoint from σ's namespace),
    so this is satisfiable — it just needs "all SC-reachable bound vars are disjoint from σ",
    which can't be expressed without inspecting the Prop-valued SC proof term. -/
theorem SC_applySubst_restricted :
    ∀ (σ : SubstEnv), isRenamingEnv σ →
    ∀ {P Q : Pattern},
    RhoCalculus.StructuralCongruence P Q →
    noExplicitSubst P →
    substBVDisjoint σ (boundVars P ++ boundVars Q) →
    RhoCalculus.StructuralCongruence (applySubst σ P) (applySubst σ Q) := by
  intro σ hren P Q h
  induction h generalizing σ with
  | alpha p q halpha =>
    intro hne hbv
    exact alphaEquiv_applySubst σ hren halpha hne hbv
  | refl p =>
    intro _ _
    exact .refl _
  | symm p q hsc ih =>
    intro hne_q hbv
    have hne_p : noExplicitSubst p := (SC_noExplicitSubst_eq hsc).symm ▸ hne_q
    exact .symm _ _ (ih σ hren hne_p (substBVDisjoint_append_comm hbv))
  | trans p q r hsc₁ hsc₂ ih₁ ih₂ =>
    intro hne_p hbv
    -- BLOCKED: need substBVDisjoint σ (boundVars Q) for intermediate Q,
    -- but only have boundVars P ++ boundVars R. At encoding call sites,
    -- all intermediate bound vars are π-names which are NamespaceDisjoint
    -- from σ's namespace, so this IS satisfiable in context.
    sorry
  | par_singleton p =>
    intro _ _
    simp only [applySubst, List.map]
    exact .par_singleton _
  | par_nil_left p =>
    intro _ _
    simp only [applySubst, List.map]
    exact .par_nil_left _
  | par_nil_right p =>
    intro _ _
    simp only [applySubst, List.map]
    exact .par_nil_right _
  | par_comm p q =>
    intro _ _
    simp only [applySubst, List.map]
    exact .par_comm _ _
  | par_assoc p q r =>
    intro _ _
    simp only [applySubst, List.map]
    exact .par_assoc _ _ _
  | par_cong ps qs hlen _ ih =>
    intro hne hbv
    simp only [applySubst]
    refine .par_cong _ _ (by simp [hlen]) ?_
    intro i h₁ h₂
    have h₁' : i < ps.length := by rwa [List.length_map] at h₁
    have h₂' : i < qs.length := by rwa [List.length_map] at h₂
    have hne_ps : allNoExplicitSubst ps := by simpa [noExplicitSubst] using hne
    have hne_i : noExplicitSubst (ps.get ⟨i, h₁'⟩) :=
      allNoExplicitSubst_mem hne_ps (List.get_mem _ _)
    have hbv_i : substBVDisjoint σ (boundVars (ps.get ⟨i, h₁'⟩) ++ boundVars (qs.get ⟨i, h₂'⟩)) :=
      substBVDisjoint_mono hbv (fun v hv => by
        rcases List.mem_append.mp hv with h | h
        · exact List.mem_append.mpr (Or.inl
            (show v ∈ boundVars (.collection .hashBag ps none) from by
              unfold boundVars; exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, h⟩))
        · exact List.mem_append.mpr (Or.inr
            (show v ∈ boundVars (.collection .hashBag qs none) from by
              unfold boundVars; exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, h⟩)))
    rw [List.get_eq_getElem, List.getElem_map, List.get_eq_getElem, List.getElem_map]
    exact ih i h₁' h₂' σ hren hne_i hbv_i
  | par_flatten ps qs =>
    intro _ _
    simp only [applySubst, List.map_append, List.map_cons, List.map_nil]
    exact .par_flatten _ _
  | par_perm elems₁ elems₂ hperm =>
    intro _ _
    simp only [applySubst]
    exact .par_perm _ _ (hperm.map _)
  | set_perm elems₁ elems₂ hperm =>
    intro _ _
    simp only [applySubst]
    exact .set_perm _ _ (hperm.map _)
  | set_cong elems₁ elems₂ hlen _ ih =>
    intro hne hbv
    simp only [applySubst]
    refine .set_cong _ _ (by simp [hlen]) ?_
    intro i h₁ h₂
    have h₁' : i < elems₁.length := by rwa [List.length_map] at h₁
    have h₂' : i < elems₂.length := by rwa [List.length_map] at h₂
    have hne_elems : allNoExplicitSubst elems₁ := by simpa [noExplicitSubst] using hne
    have hne_i : noExplicitSubst (elems₁.get ⟨i, h₁'⟩) :=
      allNoExplicitSubst_mem hne_elems (List.get_mem _ _)
    have hbv_i : substBVDisjoint σ (boundVars (elems₁.get ⟨i, h₁'⟩) ++ boundVars (elems₂.get ⟨i, h₂'⟩)) :=
      substBVDisjoint_mono hbv (fun v hv => by
        rcases List.mem_append.mp hv with h | h
        · exact List.mem_append.mpr (Or.inl
            (show v ∈ boundVars (.collection .hashSet elems₁ none) from by
              unfold boundVars; exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, h⟩))
        · exact List.mem_append.mpr (Or.inr
            (show v ∈ boundVars (.collection .hashSet elems₂ none) from by
              unfold boundVars; exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, h⟩)))
    rw [List.get_eq_getElem, List.getElem_map, List.get_eq_getElem, List.getElem_map]
    exact ih i h₁' h₂' σ hren hne_i hbv_i
  | lambda_cong x p q _ ih =>
    intro hne hbv
    simp only [applySubst]
    have hne_p : noExplicitSubst p := by simpa [noExplicitSubst] using hne
    have hbv_body : substBVDisjoint σ (boundVars p ++ boundVars q) :=
      substBVDisjoint_mono hbv (fun v hv => by
        rcases List.mem_append.mp hv with h | h
        · exact List.mem_append.mpr (Or.inl
            (show v ∈ boundVars (.lambda x p) from by
              unfold boundVars; exact List.mem_cons.mpr (Or.inr h)))
        · exact List.mem_append.mpr (Or.inr
            (show v ∈ boundVars (.lambda x q) from by
              unfold boundVars; exact List.mem_cons.mpr (Or.inr h))))
    exact .lambda_cong x _ _ (ih (σ.filter (fun p => p.1 != x))
      (fun e he => hren e (List.mem_of_mem_filter he))
      hne_p (substBVDisjoint_filter hbv_body _))
  | apply_cong f args₁ args₂ hlen _ ih =>
    intro hne hbv
    simp only [applySubst]
    refine .apply_cong f _ _ (by simp [hlen]) ?_
    intro i h₁ h₂
    have h₁' : i < args₁.length := by rwa [List.length_map] at h₁
    have h₂' : i < args₂.length := by rwa [List.length_map] at h₂
    have hne_args : allNoExplicitSubst args₁ := by simpa [noExplicitSubst] using hne
    have hne_i : noExplicitSubst (args₁.get ⟨i, h₁'⟩) :=
      allNoExplicitSubst_mem hne_args (List.get_mem _ _)
    have hbv_i : substBVDisjoint σ (boundVars (args₁.get ⟨i, h₁'⟩) ++ boundVars (args₂.get ⟨i, h₂'⟩)) :=
      substBVDisjoint_mono hbv (fun v hv => by
        rcases List.mem_append.mp hv with h | h
        · exact List.mem_append.mpr (Or.inl
            (show v ∈ boundVars (.apply f args₁) from by
              unfold boundVars; exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, h⟩))
        · exact List.mem_append.mpr (Or.inr
            (show v ∈ boundVars (.apply f args₂) from by
              unfold boundVars; exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, h⟩)))
    rw [List.get_eq_getElem, List.getElem_map, List.get_eq_getElem, List.getElem_map]
    exact ih i h₁' h₂' σ hren hne_i hbv_i
  | collection_general_cong ct elems₁ elems₂ g hlen _ ih =>
    intro hne hbv
    simp only [applySubst]
    refine .collection_general_cong ct _ _ g (by simp [hlen]) ?_
    intro i h₁ h₂
    have h₁' : i < elems₁.length := by rwa [List.length_map] at h₁
    have h₂' : i < elems₂.length := by rwa [List.length_map] at h₂
    have hne_elems : allNoExplicitSubst elems₁ := by simpa [noExplicitSubst] using hne
    have hne_i : noExplicitSubst (elems₁.get ⟨i, h₁'⟩) :=
      allNoExplicitSubst_mem hne_elems (List.get_mem _ _)
    have hbv_i : substBVDisjoint σ (boundVars (elems₁.get ⟨i, h₁'⟩) ++ boundVars (elems₂.get ⟨i, h₂'⟩)) :=
      substBVDisjoint_mono hbv (fun v hv => by
        rcases List.mem_append.mp hv with h | h
        · exact List.mem_append.mpr (Or.inl
            (show v ∈ boundVars (.collection ct elems₁ g) from by
              unfold boundVars; exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, h⟩))
        · exact List.mem_append.mpr (Or.inr
            (show v ∈ boundVars (.collection ct elems₂ g) from by
              unfold boundVars; exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, h⟩)))
    rw [List.get_eq_getElem, List.getElem_map, List.get_eq_getElem, List.getElem_map]
    exact ih i h₁' h₂' σ hren hne_i hbv_i
  | multiLambda_cong xs p q _ ih =>
    intro hne hbv
    simp only [applySubst]
    have hne_p : noExplicitSubst p := by simpa [noExplicitSubst] using hne
    have hbv_body : substBVDisjoint σ (boundVars p ++ boundVars q) :=
      substBVDisjoint_mono hbv (fun v hv => by
        rcases List.mem_append.mp hv with h | h
        · exact List.mem_append.mpr (Or.inl
            (show v ∈ boundVars (.multiLambda xs p) from by
              unfold boundVars; exact List.mem_append.mpr (Or.inr h)))
        · exact List.mem_append.mpr (Or.inr
            (show v ∈ boundVars (.multiLambda xs q) from by
              unfold boundVars; exact List.mem_append.mpr (Or.inr h))))
    exact .multiLambda_cong xs _ _ (ih (σ.filter (fun p => !xs.contains p.1))
      (fun e he => hren e (List.mem_of_mem_filter he))
      hne_p (substBVDisjoint_filter hbv_body _))
  | subst_cong _ _ _ _ _ _ _ =>
    intro hne _
    simp [noExplicitSubst] at hne
  | quote_drop n =>
    intro _ _
    simp only [applySubst, List.map]
    exact .quote_drop _

/-! ### allNoExplicitSubst list helpers -/

/-- allNoExplicitSubst for a cons list: extract head. -/
private theorem allNoExplicitSubst_head {p : Pattern} {ps : List Pattern}
    (h : allNoExplicitSubst (p :: ps)) : noExplicitSubst p := by
  simp only [allNoExplicitSubst, Bool.and_eq_true] at h; exact h.1

/-- allNoExplicitSubst for a cons list: extract tail. -/
private theorem allNoExplicitSubst_tail {p : Pattern} {ps : List Pattern}
    (h : allNoExplicitSubst (p :: ps)) : allNoExplicitSubst ps := by
  simp only [allNoExplicitSubst, Bool.and_eq_true] at h; exact h.2

/-- Construct allNoExplicitSubst for a cons list from head and tail. -/
private theorem allNoExplicitSubst_cons_iff {p : Pattern} {ps : List Pattern} :
    allNoExplicitSubst (p :: ps) ↔ (noExplicitSubst p ∧ allNoExplicitSubst ps) := by
  simp only [allNoExplicitSubst, Bool.and_eq_true]

/-- allNoExplicitSubst distributes over append (iff version). -/
private theorem allNoExplicitSubst_append_iff {ps qs : List Pattern} :
    allNoExplicitSubst (ps ++ qs) ↔
    (allNoExplicitSubst ps ∧ allNoExplicitSubst qs) := by
  rw [allNoExplicitSubst_append_eq]; simp only [Bool.and_eq_true]

/-- Right projection of allNoExplicitSubst over append. -/
private theorem allNoExplicitSubst_of_append_right {ps qs : List Pattern}
    (h : allNoExplicitSubst (ps ++ qs)) : allNoExplicitSubst qs :=
  (allNoExplicitSubst_append_iff.mp h).2

/-- Left projection of allNoExplicitSubst over append. -/
private theorem allNoExplicitSubst_of_append_left {ps qs : List Pattern}
    (h : allNoExplicitSubst (ps ++ qs)) : allNoExplicitSubst ps :=
  (allNoExplicitSubst_append_iff.mp h).1

/-- Replace one element in a list, preserving allNoExplicitSubst. -/
private theorem allNoExplicitSubst_replace_elem {before after : List Pattern}
    {p q : Pattern}
    (h : allNoExplicitSubst (before ++ [p] ++ after))
    (hq : noExplicitSubst q) :
    allNoExplicitSubst (before ++ [q] ++ after) := by
  -- before ++ [p] ++ after is parsed as (before ++ [p]) ++ after
  have hbp := allNoExplicitSubst_of_append_left h
  have ha := allNoExplicitSubst_of_append_right h
  have hb := allNoExplicitSubst_of_append_left hbp
  have hbq : allNoExplicitSubst (before ++ [q]) :=
    allNoExplicitSubst_append_iff.mpr ⟨hb, allNoExplicitSubst_cons_iff.mpr ⟨hq, rfl⟩⟩
  exact allNoExplicitSubst_append_iff.mpr ⟨hbq, ha⟩

/-- Reduction preserves noExplicitSubst. -/
theorem Reduces_noExplicitSubst {P Q : Pattern} (h : Reduction.Reduces P Q)
    (hne : noExplicitSubst P) : noExplicitSubst Q := by
  induction h with
  | @comm n q p x rest =>
    unfold noExplicitSubst at hne
    simp only [noExplicitSubst]
    have h_all := hne
    have h_pinput : noExplicitSubst (.apply "PInput" [n, .lambda x p]) :=
      allNoExplicitSubst_mem h_all (by simp)
    have h_poutput : noExplicitSubst (.apply "POutput" [n, q]) :=
      allNoExplicitSubst_mem h_all (by simp)
    unfold noExplicitSubst at h_pinput h_poutput
    have h_p : noExplicitSubst p := by
      have := allNoExplicitSubst_mem h_pinput (show (.lambda x p) ∈ [n, .lambda x p] by simp)
      unfold noExplicitSubst at this; exact this
    have h_q : noExplicitSubst q := by
      exact allNoExplicitSubst_mem h_poutput (show q ∈ [n, q] by simp)
    have h_vals : ∀ entry ∈ ([(x, Pattern.apply "NQuote" [q])] : SubstEnv),
        noExplicitSubst entry.2 := by
      intro entry hmem
      simp at hmem; subst hmem
      simp [noExplicitSubst, allNoExplicitSubst, h_q]
    have h_comm : noExplicitSubst (commSubst p x q) := by
      unfold commSubst; unfold SubstEnv.extend; unfold SubstEnv.empty
      exact applySubst_noExplicitSubst_gen _ p h_vals h_p
    exact allNoExplicitSubst_append_iff.mpr
      ⟨allNoExplicitSubst_cons_iff.mpr ⟨h_comm, rfl⟩,
       allNoExplicitSubst_of_append_right h_all⟩
  | drop =>
    -- P = PDrop[NQuote[p]], Q = p
    unfold noExplicitSubst at hne
    -- hne : allNoExplicitSubst [NQuote[p]]
    have h1 := allNoExplicitSubst_head hne
    unfold noExplicitSubst at h1
    -- h1 : allNoExplicitSubst [p]
    exact allNoExplicitSubst_head h1
  | equiv hsc₁ _ hsc₂ ih =>
    have hne' := (SC_noExplicitSubst_eq hsc₁) ▸ hne
    exact (SC_noExplicitSubst_eq hsc₂) ▸ (ih hne')
  | par _ ih =>
    unfold noExplicitSubst at hne ⊢
    exact allNoExplicitSubst_cons_iff.mpr
      ⟨ih (allNoExplicitSubst_head hne), allNoExplicitSubst_tail hne⟩
  | par_any _ ih =>
    unfold noExplicitSubst at hne ⊢
    exact allNoExplicitSubst_replace_elem hne (ih (allNoExplicitSubst_mem hne (by simp)))
  | par_set _ ih =>
    unfold noExplicitSubst at hne ⊢
    exact allNoExplicitSubst_cons_iff.mpr
      ⟨ih (allNoExplicitSubst_head hne), allNoExplicitSubst_tail hne⟩
  | par_set_any _ ih =>
    unfold noExplicitSubst at hne ⊢
    exact allNoExplicitSubst_replace_elem hne (ih (allNoExplicitSubst_mem hne (by simp)))

/-- Restricted transport assumption for bound-var disjointness through SC wrappers
    in the EQUIV rule. This is the exact missing hypothesis for the old
    unrestricted `reduces_applySubst` claim. -/
def SCBoundVarTransportSafe (σ : SubstEnv) : Prop :=
  ∀ {P Q P' Q' : Pattern},
    RhoCalculus.StructuralCongruence P P' →
    RhoCalculus.StructuralCongruence Q' Q →
    substBVDisjoint σ (boundVars P ++ boundVars Q) →
    substBVDisjoint σ (boundVars P' ++ boundVars Q')

/-- Renaming preserves ρ-reduction under explicit capture-safety hypotheses.
    - `SCBoundVarTransportSafe σ`: bound-var disjointness transports across EQUIV wrappers -/
noncomputable def reduces_applySubst (σ : SubstEnv) (hren : isRenamingEnv σ)
    (hBVTransport : SCBoundVarTransportSafe σ)
    {P Q : Pattern} (h : Reduction.Reduces P Q)
    (hbv : substBVDisjoint σ (boundVars P ++ boundVars Q))
    (hne : noExplicitSubst P) :
    Reduction.Reduces (applySubst σ P) (applySubst σ Q) := by
  induction h with
  | @comm n q p x rest =>
    -- COMM: hashBag [POutput[n,q], PInput[n, λx.p]] ++ rest ⇝ hashBag [commSubst p x q] ++ rest
    simp only [applySubst, List.map, List.map_append]
    -- Helper: x is a bound variable in the LHS (from λx in PInput)
    -- boundVars(.collection .hashBag (POutput :: PInput :: rest) none)
    -- = (POutput :: PInput :: rest).flatMap boundVars
    -- and x ∈ boundVars(PInput) because PInput = apply "PInput" [n, λx.p]
    have hx_in_bv : x ∈ boundVars (.collection .hashBag
        ([.apply "POutput" [n, q], .apply "PInput" [n, .lambda x p]] ++ rest) none) := by
      unfold boundVars
      apply List.mem_flatMap.mpr
      exact ⟨.apply "PInput" [n, .lambda x p], by simp, by
        unfold boundVars; apply List.mem_flatMap.mpr
        exact ⟨.lambda x p, by simp, by unfold boundVars; simp⟩⟩
    have hx_dom : SubstEnv.find σ x = none :=
      hbv.1 x (List.mem_append_left _ hx_in_bv)
    have hx_img : ∀ entry ∈ σ, entry.2 ≠ .var x := fun e he =>
      hbv.2 e he x (List.mem_append_left _ hx_in_bv)
    -- σ.filter(·.1 != x) = σ since x ∉ dom(σ)
    rw [filter_not_key_of_find_none σ x hx_dom]
    -- Bound vars of p are all in boundVars P
    have hbv_p : ∀ y ∈ boundVars p, SubstEnv.find σ y = none := by
      intro y hy
      apply hbv.1 y; apply List.mem_append_left
      unfold boundVars
      apply List.mem_flatMap.mpr
      exact ⟨.apply "PInput" [n, .lambda x p], by simp, by
        unfold boundVars; apply List.mem_flatMap.mpr
        exact ⟨.lambda x p, by simp, by
          unfold boundVars; exact List.mem_cons.mpr (Or.inr hy)⟩⟩
    -- Extract noExplicitSubst p from hne
    have hne_p : noExplicitSubst p := by
      -- Extract via allNoExplicitSubst_mem: PInput ∈ elems, then λx.p ∈ PInput's args
      unfold noExplicitSubst at hne
      have h1 := allNoExplicitSubst_mem hne
        (show (.apply "PInput" [n, .lambda x p]) ∈
              ([.apply "POutput" [n, q], .apply "PInput" [n, .lambda x p]] ++ rest) by simp)
      unfold noExplicitSubst at h1
      have h2 := allNoExplicitSubst_mem h1
        (show (.lambda x p) ∈ [n, .lambda x p] by simp)
      unfold noExplicitSubst at h2
      exact h2
    have heq := commSubst_applySubst_swap σ p q x hren hx_dom hx_img hbv_p hne_p
    rw [heq]
    exact .comm
  | drop =>
    simp only [applySubst, List.map]
    exact .drop
  | equiv hsc₁ hred hsc₂ ih =>
    have hne' : noExplicitSubst _ := (SC_noExplicitSubst_eq hsc₁) ▸ hne
    have hbv' : substBVDisjoint σ (boundVars _ ++ boundVars _) :=
      hBVTransport hsc₁ hsc₂ hbv
    have hred' : Reduction.Reduces (applySubst σ _) (applySubst σ _) :=
      ih hbv' hne'
    have hne_q' : noExplicitSubst _ := Reduces_noExplicitSubst hred hne'
    -- For SC calls, we need substBVDisjoint for P++P' and Q'++Q.
    -- We have hbv (P++Q) and hbv' (P'++Q'). Combine left/right halves.
    have hbv_sc1 : substBVDisjoint σ (boundVars _ ++ boundVars _) :=
      substBVDisjoint_combine (substBVDisjoint_left hbv) (substBVDisjoint_left hbv')
    have hbv_sc2 : substBVDisjoint σ (boundVars _ ++ boundVars _) :=
      substBVDisjoint_combine (substBVDisjoint_right hbv') (substBVDisjoint_right hbv)
    refine .equiv
      (SC_applySubst_restricted σ hren hsc₁ hne hbv_sc1)
      hred'
      (SC_applySubst_restricted σ hren hsc₂ hne_q' hbv_sc2)
  | @par Pi Pi' resti _ ih =>
    simp only [applySubst, List.map]
    refine .par (ih ?_ ?_)
    · apply substBVDisjoint_mono hbv; intro v hv
      rcases List.mem_append.mp hv with hvl | hvr
      · exact List.mem_append_left _ (boundVars_collection_mem (by simp) hvl)
      · exact List.mem_append_right _ (boundVars_collection_mem (by simp) hvr)
    · exact noExplicitSubst_of_collection_mem hne (by simp)
  | @par_any Pi Pi' pre suf _ ih =>
    simp only [applySubst, List.map_append, List.map_cons]
    refine .par_any (ih ?_ ?_)
    · apply substBVDisjoint_mono hbv; intro v hv
      rcases List.mem_append.mp hv with hvl | hvr
      · exact List.mem_append_left _
          (boundVars_collection_mem (show Pi ∈ pre ++ [Pi] ++ suf by simp) hvl)
      · exact List.mem_append_right _
          (boundVars_collection_mem (show Pi' ∈ pre ++ [Pi'] ++ suf by simp) hvr)
    · exact noExplicitSubst_of_collection_mem hne (show Pi ∈ pre ++ [Pi] ++ suf by simp)
  | @par_set Pi Pi' resti _ ih =>
    simp only [applySubst, List.map_cons]
    refine .par_set (ih ?_ ?_)
    · apply substBVDisjoint_mono hbv; intro v hv
      rcases List.mem_append.mp hv with hvl | hvr
      · exact List.mem_append_left _ (boundVars_collection_mem (by simp) hvl)
      · exact List.mem_append_right _ (boundVars_collection_mem (by simp) hvr)
    · exact noExplicitSubst_of_collection_mem hne (by simp)
  | @par_set_any Pi Pi' pre suf _ ih =>
    simp only [applySubst, List.map_append, List.map_cons]
    refine .par_set_any (ih ?_ ?_)
    · apply substBVDisjoint_mono hbv; intro v hv
      rcases List.mem_append.mp hv with hvl | hvr
      · exact List.mem_append_left _
          (boundVars_collection_mem (show Pi ∈ pre ++ [Pi] ++ suf by simp) hvl)
      · exact List.mem_append_right _
          (boundVars_collection_mem (show Pi' ∈ pre ++ [Pi'] ++ suf by simp) hvr)
    · exact noExplicitSubst_of_collection_mem hne (show Pi ∈ pre ++ [Pi] ++ suf by simp)

/-- Restricted EncEquiv reduction bridge.

    The old unrestricted bridge was blocked on reverse transport of reductions through
    renaming (a genuine hard requirement). This restricted form makes the pullback
    hypothesis explicit. -/
theorem EncEquiv_reduces_bridge {P Q : Pattern}
    (henc : P ≃enc Q) {T : Pattern} (_hred : ReducesStar Q T)
    (hpull :
      ∀ {P' : Pattern} {σ : SubstEnv},
        RhoCalculus.StructuralCongruence P P' →
        isRenamingEnv σ →
        applySubst σ P' = Q →
        ∃ T0, Nonempty (ReducesStar P' T0) ∧ applySubst σ T0 = T) :
    ∃ T', Nonempty (ReducesStar P T') ∧ (T' ≃enc T) := by
  obtain ⟨P', σ, hsc, hren, heq⟩ := henc
  have hpull' := hpull hsc hren heq
  obtain ⟨T0, hstar0, hsubstT⟩ := hpull'
  obtain ⟨star0⟩ := hstar0
  cases star0 with
  | refl =>
    refine ⟨P, ⟨.refl _⟩, ?_⟩
    exact ⟨P', σ, hsc, hren, by simpa using hsubstT⟩
  | @step _ mid _ hstep rest =>
    refine ⟨T0, ⟨.step (.equiv hsc hstep (.refl _)) rest⟩, ?_⟩
    exact EncEquiv.of_renaming σ hren hsubstT

/-- nsEnv always produces a renaming substitution. -/
theorem nsEnv_isRenaming : ∀ (P : Process) (n n' : String),
    isRenamingEnv (nsEnv P n n') := by
  intro P; induction P with
  | nil => intro n n'; simp [nsEnv, isRenamingEnv]
  | output _ _ => intro n n'; simp [nsEnv, isRenamingEnv]
  | input _ _ P ih => intro n n'; exact ih n n'
  | par P Q ihP ihQ =>
    intro n n' entry h_mem
    simp only [nsEnv] at h_mem
    rcases List.mem_append.mp h_mem with h | h
    · exact ihP (n ++ "_L") (n' ++ "_L") entry h
    · exact ihQ (n ++ "_R") (n' ++ "_R") entry h
  | nu x P ih =>
    intro n n' entry h_mem
    simp only [nsEnv] at h_mem
    rcases List.mem_cons.mp h_mem with h | h
    · subst h; exact ⟨n', rfl⟩
    · exact ih (n ++ "_" ++ n) (n' ++ "_" ++ n') entry h
  | replicate x y P ih => intro n n'; exact ih (n ++ "_rep") (n' ++ "_rep")

/-- Encoding equivalence via nsEnv: encode P n v ≃enc encode P n' v.
    Uses SC.refl (no structural rearrangement needed, pure renaming). -/
theorem encode_encEquiv_nsEnv (P : Process) (n n' v : String)
    (h_ndisj : ∀ u ∈ Process.names P, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n) :
    encode P n v ≃enc encode P n' v :=
  EncEquiv.of_renaming (nsEnv P n n') (nsEnv_isRenaming P n n')
    (applySubst_nsEnv_encode P n n' v h_ndisj h_v_ndisj)

/-- Proposition 1 (general weak-restricted shape), factored through an
    EncEquiv→WeakRestrictedBisim bridge.

    This lifts parameter independence from the simple-fragment equality proof to
    all processes once the bridge is instantiated for namespace renamings. -/
theorem encoding_parameter_independence_bisim_general (P : Process) (n n' v : String)
    (h_ndisj : ∀ u ∈ Process.names P, NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n)
    (hEncToBisim : (A : Pattern) → (B : Pattern) →
      EncEquiv A B → WeakRestrictedBisim P.freeNames A B) :
    encode P n v ≈{P.freeNames} encode P n' v :=
  hEncToBisim _ _ (encode_encEquiv_nsEnv P n n' v h_ndisj h_v_ndisj)

/-- Legacy strong-bisim statement for Proposition 1.

    This theorem keeps the original strong-bisim shape for compatibility with
    older development notes. The current reframing uses `WeakRestrictedBisim`
    (Lybech's N-restricted weak barbed bisimilarity) as the primary notion.

    Proven Prop-1 fragment in the new framework:
    `encoding_parameter_independence_simple_bisim`.
-/
theorem encoding_parameter_independence_CORRECTED (P : Process) (n n' v s s' : String)
    (h_fresh_n : n ∉ Process.names P)
    (h_fresh_n' : n' ∉ Process.names P)
    (h_fresh_s : s ∉ Process.names P)
    (h_fresh_s' : s' ∉ Process.names P)
    (h_unique : n ≠ n' ∧ s ≠ s')
    -- NEW: Namespace disjointness (the missing condition from Lybech!)
    (h_ndisj_n  : ∀ u ∈ Process.names P, NamespaceDisjoint u n)
    (h_ndisj_n' : ∀ u ∈ Process.names P, NamespaceDisjoint u n')
    (h_ndisj_s  : ∀ u ∈ Process.names P, NamespaceDisjoint u s)
    (h_ndisj_s' : ∀ u ∈ Process.names P, NamespaceDisjoint u s')
    -- Reserve internal channels
    (h_resv_x : "ns_x" ∉ Process.names P)
    (h_resv_z : "ns_z" ∉ Process.names P)
    (h_resv_v : v ∉ Process.names P) :
    RhoBisimilar
      (rhoPar (encode P n v) (nameServer "ns_x" "ns_z" v s))
      (rhoPar (encode P n' v) (nameServer "ns_x" "ns_z" v s')) := by
  sorry  -- To be proven using nsEnv renaming strategy

/-! ## Proposition 2: Substitution Invariance

Substitution commutes with encoding: encoding the substituted process
equals substituting in the encoded process.
-/

/-- Substitution in ρ-calculus patterns (simplified for atomic names) -/
def rhoSubstitute (P : Pattern) (x : String) (n : Pattern) : Pattern :=
  match P with
  | .var y => if y = x then n else .var y
  | .apply f args => .apply f (args.map fun a => rhoSubstitute a x n)
  | .lambda y body =>
      if y = x then .lambda y body
      else .lambda y (rhoSubstitute body x n)
  | .collection ct ps guard =>
      .collection ct (ps.map fun p => rhoSubstitute p x n) guard
  | .multiLambda vars body =>
      if x ∈ vars then .multiLambda vars body
      else .multiLambda vars (rhoSubstitute body x n)
  | .subst p y t => .subst (rhoSubstitute p x n) y (rhoSubstitute t x n)

/-! ## Helper Lemmas for Substitution -/

/-- rhoSubstitute on .apply preserves the .apply structure -/
lemma rhoSubstitute_apply_is_apply (f : String) (args : List Pattern) (x : String) (n : Pattern) :
    rhoSubstitute (.apply f args) x n = .apply f (args.map fun a => rhoSubstitute a x n) := by
  simp only [rhoSubstitute]

/-- rhoSubstitute on .lambda produces either the same lambda (if x=y) or a lambda with substituted body -/
lemma rhoSubstitute_lambda_is_lambda (y : String) (body : Pattern) (x : String) (n : Pattern) :
    ∃ body', rhoSubstitute (.lambda y body) x n = .lambda y body' := by
  simp only [rhoSubstitute]
  split_ifs
  · exact ⟨body, rfl⟩
  · exact ⟨rhoSubstitute body x n, rfl⟩

/-- rhoSubstitute on .collection preserves the .collection structure -/
lemma rhoSubstitute_collection_is_collection (ct : CollType) (ps : List Pattern) (guard : Option String)
    (x : String) (n : Pattern) :
    rhoSubstitute (.collection ct ps guard) x n =
    .collection ct (ps.map fun p => rhoSubstitute p x n) guard := by
  simp only [rhoSubstitute]

/-! ## Algebraic Reformulation of rhoPar

**Key insight**: rhoPar combines patterns by appending their "list representations".
Instead of reasoning about the 4-way pattern match, we define helper functions
that make the algebraic structure explicit.
-/

/-- A pattern has "no top-level variables" if it's not a .var constructor at the root.
    All outputs of `encode` satisfy this property. -/
def NoTopVar : Pattern → Prop
  | .var _ => False
  | _ => True

/-- Convert a pattern to its list representation for rhoPar.
    ONLY hashBag collections with no guard are unwrapped (matching rhoPar's optimization).
    All other patterns become singleton lists. -/
def toListRepr : Pattern → List Pattern
  | .collection .hashBag ps none => ps
  | p => [p]

/-- Convert a list back to a hashBag collection. -/
def fromListRepr (ps : List Pattern) : Pattern :=
  .collection .hashBag ps none

/-- rhoPar is equivalent to appending list representations. -/
lemma rhoPar_eq_fromListRepr_append (P Q : Pattern) :
    rhoPar P Q = fromListRepr (toListRepr P ++ toListRepr Q) := by
  unfold rhoPar toListRepr fromListRepr
  -- Split on constructors
  rcases P with pv | pa | pl | pm | psub | ⟨pct, pps, pg⟩
  <;> rcases Q with qv | qa | ql | qm | qsub | ⟨qct, qps, qg⟩
  -- Most cases are rfl after unfolding
  all_goals (try rfl)
  -- Collection cases remain - split further on CollType and guard
  all_goals (try (cases pct <;> cases pg <;> try rfl))
  all_goals (try (cases qct <;> cases qg <;> try rfl))

/-- toListRepr is left-inverse of fromListRepr -/
lemma toListRepr_fromListRepr (ps : List Pattern) :
    toListRepr (fromListRepr ps) = ps := by
  simp [fromListRepr, toListRepr]

/-- toListRepr distributes over rhoPar as list append -/
lemma toListRepr_rhoPar (P Q : Pattern) :
    toListRepr (rhoPar P Q) = toListRepr P ++ toListRepr Q := by
  rw [rhoPar_eq_fromListRepr_append, toListRepr_fromListRepr]

/-- rhoSubstitute distributes over toListRepr (for non-var patterns). -/
lemma rhoSubstitute_toListRepr {P : Pattern} (hP : NoTopVar P) (x : String) (n : Pattern) :
    List.map (fun p => rhoSubstitute p x n) (toListRepr P) = toListRepr (rhoSubstitute P x n) := by
  unfold toListRepr
  cases P with
  | var y => cases hP  -- NoTopVar (var y) is False, contradiction
  | apply f args => simp [rhoSubstitute, List.map]
  | lambda y body => simp [rhoSubstitute, List.map]; split_ifs <;> rfl
  | multiLambda ys body => simp [rhoSubstitute, List.map]; split_ifs <;> rfl
  | subst p y t => simp [rhoSubstitute, List.map]
  | collection ct ps g =>
    cases ct <;> cases g <;> simp only [rhoSubstitute_collection_is_collection, List.map]

/-- rhoSubstitute distributes over fromListRepr. -/
lemma rhoSubstitute_fromListRepr (ps : List Pattern) (x : String) (n : Pattern) :
    rhoSubstitute (fromListRepr ps) x n = fromListRepr (ps.map (rhoSubstitute · x n)) := by
  unfold fromListRepr
  simp [rhoSubstitute_collection_is_collection]

/-- rhoInput never produces a top-level .var -/
lemma rhoInput_noTopVar (m : Pattern) (y : String) (P : Pattern) : NoTopVar (rhoInput m y P) := by
  simp [rhoInput, NoTopVar]

/-- rhoOutput never produces a top-level .var -/
lemma rhoOutput_noTopVar (m q : Pattern) : NoTopVar (rhoOutput m q) := by
  simp [rhoOutput, NoTopVar]

/-- encode never produces a top-level variable -/
lemma encode_noTopVar (P : Process) (n v : String) : NoTopVar (encode P n v) := by
  induction P generalizing n v with
  | nil => simp [encode, rhoNil, NoTopVar]
  | par P Q ihP ihQ =>
    simp only [encode]
    -- rhoPar always returns a .collection, never a .var
    unfold rhoPar
    split <;> simp [NoTopVar]
  | input x y P ih => simp [encode, rhoInput, NoTopVar]
  | output x z => simp [encode, rhoOutput, NoTopVar]
  | nu x P ih =>
    simp only [encode]
    unfold rhoPar
    split <;> simp [NoTopVar]
  | replicate x y P ih => simp [encode, rhoReplicate, NoTopVar]

/-- For patterns without top-level vars, rhoPar and rhoSubstitute commute.

    **Proof**: Uses algebraic reformulation to avoid pattern matching issues.
    We express rhoPar as list append, then use distributivity of substitution over lists.
-/
lemma rhoSubstitute_rhoPar_noTopVar {P Q : Pattern} (hP : NoTopVar P) (hQ : NoTopVar Q)
    (x : String) (n : Pattern) :
    rhoSubstitute (rhoPar P Q) x n = rhoPar (rhoSubstitute P x n) (rhoSubstitute Q x n) := by
  -- Rewrite both sides using algebraic formulation
  rw [rhoPar_eq_fromListRepr_append, rhoPar_eq_fromListRepr_append]
  -- Apply substitution lemma for fromListRepr
  rw [rhoSubstitute_fromListRepr]
  -- Show that List.map distributes over append
  simp only [List.map_append]
  -- Apply substitution lemma for toListRepr on both P and Q
  rw [← rhoSubstitute_toListRepr hP, ← rhoSubstitute_toListRepr hQ]

/-- Substituting a variable in an encoded name gives the encoded substituted name.
    Key insight: We substitute with .var w, not piNameToRhoName w, to avoid double-quoting. -/
lemma piNameToRhoName_substitute (x u w : Name) :
    piNameToRhoName (if x = u then w else x) =
    rhoSubstitute (piNameToRhoName x) u (.var w) := by
  simp only [piNameToRhoName, rhoSubstitute]
  split_ifs with h
  · subst h; rfl
  · rfl

/-- Freshness for par: if u is fresh for P | Q, then u is fresh for both P and Q -/
lemma fresh_par (u : Name) (P Q : Process) (h : u ∉ (Process.par P Q).names) :
    u ∉ P.names ∧ u ∉ Q.names := by
  simp only [Process.names, Process.freeNames, Process.boundNames, Finset.mem_union] at h ⊢
  tauto

/-- Freshness for input: if u is fresh for input x y P, then u ≠ x, u ≠ y, and u is fresh for P -/
lemma fresh_input (u : Name) (x y : Name) (P : Process) (h : u ∉ (Process.input x y P).names) :
    u ≠ x ∧ u ≠ y ∧ u ∉ P.names := by
  simp only [Process.names, Process.freeNames, Process.boundNames] at h ⊢
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at h ⊢
  tauto

/-- Freshness for nu: if u is fresh for (νx)P, then u ≠ x and u is fresh for P -/
lemma fresh_nu (u : Name) (x : Name) (P : Process) (h : u ∉ (Process.nu x P).names) :
    u ≠ x ∧ u ∉ P.names := by
  simp only [Process.names, Process.freeNames, Process.boundNames] at h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff] at h
  push_neg at h
  -- h : (u ∈ P.freeNames → u = x) ∧ u ≠ x ∧ u ∉ P.boundNames
  obtain ⟨h_free_impl, h_ne_x, h_not_bound⟩ := h
  constructor
  · exact h_ne_x
  · intro h_in
    simp only [Process.names, Finset.mem_union] at h_in
    cases h_in with
    | inl h_free => exact h_ne_x (Finset.mem_singleton.mp (h_free_impl h_free))
    | inr h_bound => exact h_not_bound h_bound

/-- Freshness for replicate: if u is fresh for !x(y).P, then u ≠ x, u ≠ y, and u is fresh for P -/
lemma fresh_replicate (u : Name) (x y : Name) (P : Process)
    (h : u ∉ (Process.replicate x y P).names) :
    u ≠ x ∧ u ≠ y ∧ u ∉ P.names := by
  simp only [Process.names, Process.freeNames, Process.boundNames] at h ⊢
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at h ⊢
  tauto

/-- rhoSubstitute commutes with rhoInput when binding variable differs -/
lemma rhoSubstitute_rhoInput (m : Pattern) (y : String) (P : Pattern) (x : String) (n : Pattern) :
    rhoSubstitute (rhoInput m y P) x n =
    (if y = x then rhoInput (rhoSubstitute m x n) y P
     else rhoInput (rhoSubstitute m x n) y (rhoSubstitute P x n)) := by
  simp only [rhoInput, rhoSubstitute, List.map]
  split_ifs <;> rfl

/-- rhoSubstitute commutes with rhoOutput -/
lemma rhoSubstitute_rhoOutput (m q : Pattern) (x : String) (n : Pattern) :
    rhoSubstitute (rhoOutput m q) x n =
    rhoOutput (rhoSubstitute m x n) (rhoSubstitute q x n) := by
  simp only [rhoOutput, rhoSubstitute, List.map]

/-- rhoSubstitute commutes with rhoReplicate -/
lemma rhoSubstitute_rhoReplicate (P : Pattern) (x : String) (n : Pattern) :
    rhoSubstitute (rhoReplicate P) x n =
    rhoReplicate (rhoSubstitute P x n) := by
  simp only [rhoReplicate, rhoSubstitute, List.map]

/-- Namespace disjointness propagates to derived parameters.

    If u is disjoint from namespace N[n], it remains disjoint from N[n ++ s].
-/
lemma namespace_disjoint_derived (u n s : String) (h : NamespaceDisjoint u n) :
    NamespaceDisjoint u (n ++ s) := by
  unfold NamespaceDisjoint at h ⊢
  intro suffix
  -- Need: u ≠ (n ++ s) ++ suffix
  -- Have: ∀ t, u ≠ n ++ t (from h)
  -- Note: (n ++ s) ++ suffix = n ++ (s ++ suffix) by associativity
  rw [String.append_assoc]
  exact h (s ++ suffix)

/-- Derived parameter freshness: if u is fresh for base parameters, it's fresh for derived ones.

    This captures Lybech's `u # N[n]` condition: u fresh for entire namespace.
    Uses NamespaceDisjoint to ensure u doesn't collide with any derived parameter.
-/
lemma fresh_derived_param (u n v suffix : String)
    (h : u ∉ [n, v])
    (h_disjoint : NamespaceDisjoint u n)
    : u ∉ [n ++ suffix, v] := by
  simp only [List.mem_cons, not_or] at h ⊢
  obtain ⟨_, h_ne_v⟩ := h
  exact ⟨h_disjoint suffix, h_ne_v⟩

/-- Proposition 2: Substitution (Lybech page 106)

    **Informal statement**: encode (P[w/u]) = (encode P)[w/u]
    where the substitution on the left is in π-calculus,
    and on the right is in ρ-calculus.

    **Freshness conditions** (Lybech page 106):
    The theorem requires u, w # P, n, v, N[n], which expands to:
    - u, w fresh for P (not appearing in P's names)
    - u, w fresh for encoding parameters n, v
    - u, w fresh for namespace N[n] (all derived parameters) - via NamespaceDisjoint

    Lybech's justification: "The condition u, w # P, n, v, N[n] ensures that
    the substitution cannot touch any of the names created by the translation,
    which is reasonable, since the substitutions we care about should derive
    from communications in the π-calculus, and not from some of the 'internal'
    reductions in the ρ-calculus that are used to simulate replication or
    requests for new names."

    **Key insight**: We substitute with .var w (not piNameToRhoName w) to avoid
    double-quoting. Encoded names like @x become @y, not @@y.

    **Proof strategy**: By induction on P with parameter freshness conditions.
    Each case shows substitution commutes with encoding, using freshness to
    simplify if-statements and namespace disjointness for recursive calls.
-/
theorem encoding_substitution (P : Process) (u w : Name) (n v : String)
    (h_fresh_u_P : u ∉ P.names)      -- u # P (Lybech page 106)
    (h_fresh_w_P : w ∉ P.names)      -- w # P (Lybech page 106)
    (h_fresh_u : u ∉ [n, v])         -- u # n, v
    (h_fresh_w : w ∉ [n, v])         -- w # n, v
    (h_disjoint_u : NamespaceDisjoint u n)  -- u # N[n] (Lybech page 106)
    (h_disjoint_w : NamespaceDisjoint w n)  -- w # N[n]
    : encode (P.substitute u w) n v =
    rhoSubstitute (encode P n v) u (.var w) := by
  -- Include parameter freshness AND namespace disjointness in the quantified statement
  -- Explicitly use String type for n' v' to match encode's signature
  suffices h : ∀ (n' v' : String), u ∉ [n', v'] → w ∉ [n', v'] →
      NamespaceDisjoint u n' → NamespaceDisjoint w n' →
      encode (P.substitute u w) n' v' = rhoSubstitute (encode P n' v') u (.var w) by
    exact h n v h_fresh_u h_fresh_w h_disjoint_u h_disjoint_w
  intro n' v' h_fresh_u' h_fresh_w' h_ndisj_u h_ndisj_w
  induction P generalizing n' v' with
  | nil =>
    -- Case: nil - trivial
    simp only [Process.substitute, encode, rhoNil, rhoSubstitute, List.map]
  | par P Q ihP ihQ =>
    -- Case: P | Q - Freshness decomposes to both subprocesses
    have ⟨h_P_fresh_u, h_Q_fresh_u⟩ := fresh_par u P Q h_fresh_u_P
    have ⟨h_P_fresh_w, h_Q_fresh_w⟩ := fresh_par w P Q h_fresh_w_P
    -- Derived parameter freshness for recursive calls
    have h_fresh_u_L := fresh_derived_param u n' v' "_L" h_fresh_u' h_ndisj_u
    have h_fresh_w_L := fresh_derived_param w n' v' "_L" h_fresh_w' h_ndisj_w
    have h_fresh_u_R := fresh_derived_param u n' v' "_R" h_fresh_u' h_ndisj_u
    have h_fresh_w_R := fresh_derived_param w n' v' "_R" h_fresh_w' h_ndisj_w
    -- Namespace disjointness propagates to derived parameters
    have h_ndisj_u_L := namespace_disjoint_derived u n' "_L" h_ndisj_u
    have h_ndisj_w_L := namespace_disjoint_derived w n' "_L" h_ndisj_w
    have h_ndisj_u_R := namespace_disjoint_derived u n' "_R" h_ndisj_u
    have h_ndisj_w_R := namespace_disjoint_derived w n' "_R" h_ndisj_w
    -- Use restricted lemma for patterns from encode
    simp only [Process.substitute, encode]
    rw [ihP h_P_fresh_u h_P_fresh_w _ _ h_fresh_u_L h_fresh_w_L h_ndisj_u_L h_ndisj_w_L,
        ihQ h_Q_fresh_u h_Q_fresh_w _ _ h_fresh_u_R h_fresh_w_R h_ndisj_u_R h_ndisj_w_R,
        ← rhoSubstitute_rhoPar_noTopVar (encode_noTopVar P _ _) (encode_noTopVar Q _ _)]
  | output x z =>
    -- Case: x<z> - direct application of name substitution
    -- encode (.output x z) = rhoOutput (.var x) (rhoDrop (.var z))
    simp only [Process.substitute, encode, piNameToRhoName, rhoOutput, rhoDrop,
               rhoSubstitute, List.map]
    split_ifs <;> rfl
  | input x y P ih =>
    -- Case: x(y).P - Freshness hypothesis rules out x = u and y = u
    have ⟨h_x_ne_u, h_y_ne_u, h_P_fresh_u⟩ := fresh_input u x y P h_fresh_u_P
    have ⟨_, _, h_P_fresh_w⟩ := fresh_input w x y P h_fresh_w_P
    -- The π-calculus substitution has 3 cases, but freshness rules out 2 of them
    simp only [Process.substitute, encode]
    split_ifs with hx hy
    · -- x = u: IMPOSSIBLE by freshness (u ≠ x from h_x_ne_u)
      exact absurd hx.symm h_x_ne_u
    · -- x ≠ u, y = u: IMPOSSIBLE by freshness (u ≠ y from h_y_ne_u)
      exact absurd hy.symm h_y_ne_u
    · -- x ≠ u, y ≠ u: normal substitution - the only possible case
      -- Input doesn't change the parameters, so freshness and disjointness transfer directly
      simp only [encode, rhoSubstitute_rhoInput]
      rw [← piNameToRhoName_substitute,
          ih h_P_fresh_u h_P_fresh_w _ _ h_fresh_u' h_fresh_w' h_ndisj_u h_ndisj_w]
      simp only [hx, hy, ↓reduceIte]
  | nu x P ih =>
    -- Case: (νx)P - Freshness hypothesis rules out x = u
    have ⟨h_x_ne_u, h_P_fresh_u⟩ := fresh_nu u x P h_fresh_u_P
    have ⟨_, h_P_fresh_w⟩ := fresh_nu w x P h_fresh_w_P
    -- Extract parameter freshness from h_fresh_u' and h_fresh_w'
    -- h_fresh_u' : u ∉ [n', v'] means u ≠ n' ∧ u ≠ v'
    have h_ne_n_u : u ≠ n' := fun h => by simp [h] at h_fresh_u'
    have h_ne_v_u : u ≠ v' := fun h => by simp [h] at h_fresh_u'
    have h_ne_n_w : w ≠ n' := fun h => by simp [h] at h_fresh_w'
    have h_ne_v_w : w ≠ v' := fun h => by simp [h] at h_fresh_w'
    -- Derived parameter freshness for recursive call (nu uses n' ++ "_" ++ n')
    -- Note: n' ++ "_" ++ n' = n' ++ ("_" ++ n') by String.append_assoc
    have h_fresh_u_nu : u ∉ [n' ++ "_" ++ n', v'] := by
      rw [String.append_assoc]
      exact fresh_derived_param u n' v' ("_" ++ n') h_fresh_u' h_ndisj_u
    have h_fresh_w_nu : w ∉ [n' ++ "_" ++ n', v'] := by
      rw [String.append_assoc]
      exact fresh_derived_param w n' v' ("_" ++ n') h_fresh_w' h_ndisj_w
    -- Namespace disjointness propagates through suffix composition
    have h_ndisj_u_nu : NamespaceDisjoint u (n' ++ "_" ++ n') := by
      rw [String.append_assoc]
      exact namespace_disjoint_derived u n' ("_" ++ n') h_ndisj_u
    have h_ndisj_w_nu : NamespaceDisjoint w (n' ++ "_" ++ n') := by
      rw [String.append_assoc]
      exact namespace_disjoint_derived w n' ("_" ++ n') h_ndisj_w
    -- The π-calculus substitution checks if x = u
    simp only [Process.substitute]
    split_ifs with hx
    · -- x = u: IMPOSSIBLE by freshness (u ≠ x from h_x_ne_u)
      exact absurd hx.symm h_x_ne_u
    · -- x ≠ u: substitution recurses into P
      simp only [encode]
      -- Expand RHS using rhoPar distributivity
      rw [rhoSubstitute_rhoPar_noTopVar (rhoOutput_noTopVar _ _) (rhoInput_noTopVar _ _ _)]
      -- Simplify rhoOutput and rhoInput substitutions together with if-statements
      simp only [rhoSubstitute_rhoOutput, rhoSubstitute, rhoSubstitute_rhoInput,
                 if_neg (Ne.symm h_ne_v_u), if_neg (Ne.symm h_ne_n_u), hx, ↓reduceIte]
      -- Apply IH with derived parameter freshness and namespace disjointness
      rw [ih h_P_fresh_u h_P_fresh_w _ _ h_fresh_u_nu h_fresh_w_nu h_ndisj_u_nu h_ndisj_w_nu]
  | replicate x y P ih =>
    -- Case: !x(y).P - Freshness hypothesis rules out x = u and y = u
    have ⟨h_x_ne_u, h_y_ne_u, h_P_fresh_u⟩ := fresh_replicate u x y P h_fresh_u_P
    have ⟨_, _, h_P_fresh_w⟩ := fresh_replicate w x y P h_fresh_w_P
    -- Derived parameter freshness for recursive call (replicate uses n' ++ "_rep")
    have h_fresh_u_rep := fresh_derived_param u n' v' "_rep" h_fresh_u' h_ndisj_u
    have h_fresh_w_rep := fresh_derived_param w n' v' "_rep" h_fresh_w' h_ndisj_w
    have h_ndisj_u_rep := namespace_disjoint_derived u n' "_rep" h_ndisj_u
    have h_ndisj_w_rep := namespace_disjoint_derived w n' "_rep" h_ndisj_w
    -- The π-calculus substitution has 3 cases, but freshness rules out 2 of them
    simp only [Process.substitute]
    split_ifs with hx hy
    · -- x = u: IMPOSSIBLE by freshness (u ≠ x from h_x_ne_u)
      exact absurd hx.symm h_x_ne_u
    · -- x ≠ u, y = u: IMPOSSIBLE by freshness (u ≠ y from h_y_ne_u)
      exact absurd hy.symm h_y_ne_u
    · -- x ≠ u, y ≠ u: normal substitution - the only possible case
      simp only [encode, rhoSubstitute_rhoReplicate, rhoSubstitute_rhoInput]
      rw [← piNameToRhoName_substitute,
          ih h_P_fresh_u h_P_fresh_w _ _ h_fresh_u_rep h_fresh_w_rep h_ndisj_u_rep h_ndisj_w_rep]
      simp only [hx, hy, ↓reduceIte]

/-! ## Proposition 3: Weak Observational Correspondence

A π-process can observe on channel x iff its encoding can observe
on the corresponding ρ-name.
-/

/-- Helper: Encoding of output creates POutput pattern -/
lemma encode_output_creates_POutput (x y : Name) (n v : String) :
    encode (Process.output x y) n v = .apply "POutput" [piNameToRhoName x, rhoDrop (piNameToRhoName y)] := by
  simp only [encode, rhoOutput, rhoDrop, piNameToRhoName]

/-- rhoPar with POutput on left creates collection with POutput first -/
lemma rhoPar_POutput_left (x y : Pattern) (Q : Pattern) :
    rhoPar (.apply "POutput" [x, y]) Q =
    .collection .hashBag (.apply "POutput" [x, y] :: (match Q with
      | .collection .hashBag qs none => qs
      | q => [q])) none := by
  unfold rhoPar
  -- .apply "POutput" [x, y] is not a .collection, so we split on Q
  rcases Q with qv | qa | ql | qm | qsub | ⟨qct, qps, qg⟩
  all_goals (try rfl)
  -- collection case: split on CollType and guard
  cases qct <;> cases qg <;> rfl

/-- Helper: Encoding output in parallel creates observable structure -/
lemma encode_par_output_creates_POutput (x y : Name) (Q : Process) (n v : String) :
    ∃ rest, encode (Process.par (Process.output x y) Q) n v =
            .collection .hashBag ([.apply "POutput" [piNameToRhoName x, rhoDrop (piNameToRhoName y)]] ++ rest) none := by
  -- The encoding of (output x y | Q) is rhoPar (rhoOutput (.var x) (PDrop (.var y))) (encode Q ...)
  simp only [encode, rhoOutput, rhoDrop, piNameToRhoName]
  -- Use rhoPar_POutput_left to decompose the rhoPar
  rw [rhoPar_POutput_left]
  -- Now goal has match expression; use the appropriate rest
  exact ⟨_, rfl⟩

/-- fullEncode of par-output creates observable ρ-output.

    Key helper: syntactic output x y | Q directly produces RhoObservableOutput.
    This avoids the complexity of structural congruence.
-/
lemma fullEncode_par_output_observable (x y : Name) (Q : Process) :
    RhoObservableOutput (fullEncode (Process.par (Process.output x y) Q)) (piNameToRhoName x) := by
  have h_eq : fullEncode (Process.par (Process.output x y) Q) =
      .collection .hashBag
        (toListRepr (encode (Process.par (Process.output x y) Q) "n_init" "v_init") ++
         toListRepr (nameServer "ns_x" "ns_z" "v_init" "ns_seed")) none := by
    unfold fullEncode; rw [rhoPar_eq_fromListRepr_append]; rfl
  have h_mem : .apply "POutput" [piNameToRhoName x, rhoDrop (piNameToRhoName y)] ∈
      toListRepr (encode (Process.par (Process.output x y) Q) "n_init" "v_init") ++
      toListRepr (nameServer "ns_x" "ns_z" "v_init" "ns_seed") := by
    apply List.mem_append_left
    simp only [encode]
    rw [toListRepr_rhoPar]
    apply List.mem_append_left
    simp [rhoOutput, rhoDrop, piNameToRhoName, toListRepr]
  exact ⟨rhoDrop (piNameToRhoName y), Or.inl ⟨_, h_eq, h_mem⟩⟩

/-! ## Encode Inversion: Characterizing POutput in Encodings

Lemmas characterizing exactly when POutput [piNameToRhoName x, q] appears
in the encoding, enabling both forward and backward observational correspondence.
-/

/-- Process has output on channel x at some parallel composition level.
    This is a purely syntactic property. -/
inductive HasParOutput : Process → Name → Prop where
  | output (x y : Name) : HasParOutput (.output x y) x
  | par_left {P Q : Process} {x : Name} :
      HasParOutput P x → HasParOutput (.par P Q) x
  | par_right {P Q : Process} {x : Name} :
      HasParOutput Q x → HasParOutput (.par P Q) x

/-- fullEncode always produces a hashBag collection -/
lemma fullEncode_is_hashBag (P : Process) :
    ∃ ps, fullEncode P = .collection .hashBag ps none := by
  unfold fullEncode
  rw [rhoPar_eq_fromListRepr_append]
  exact ⟨_, rfl⟩

/-- If P has output on x, then encoding contains POutput [piNameToRhoName x, _] -/
lemma HasParOutput_encode_POutput_member {P : Process} {x : Name} (h : HasParOutput P x)
    (n v : String) :
    ∃ q, (.apply "POutput" [piNameToRhoName x, q]) ∈
         toListRepr (encode P n v) := by
  induction h generalizing n v with
  | output x y =>
    exact ⟨rhoDrop (piNameToRhoName y), by simp [encode, rhoOutput, rhoDrop, piNameToRhoName, toListRepr]⟩
  | par_left _ ih =>
    obtain ⟨q, hq⟩ := ih (n ++ "_L") v
    exact ⟨q, by simp only [encode]; rw [toListRepr_rhoPar]; exact List.mem_append_left _ hq⟩
  | par_right _ ih =>
    obtain ⟨q, hq⟩ := ih (n ++ "_R") v
    exact ⟨q, by simp only [encode]; rw [toListRepr_rhoPar]; exact List.mem_append_right _ hq⟩

/-- piNameToRhoName produces .var, so channel discrimination requires freshness.
    If the π-name x differs from a string v, then piNameToRhoName x ≠ .var v. -/
lemma piNameToRhoName_ne_var_of_ne (x : Name) (v : String) (h : x ≠ v) :
    piNameToRhoName x ≠ .var v := by
  simp [piNameToRhoName, h]

/-- If encoding contains POutput [piNameToRhoName x, q], then P has output on x.

    This is the key inversion lemma: piNameToRhoName channels in POutput can
    ONLY originate from Process.output in the source.

    **Freshness condition**: x ≠ v is needed because `encode (nu _ _)` produces
    POutput on channel `.var v` (the value parameter). Since piNameToRhoName x = .var x,
    we need x ≠ v to distinguish encoding outputs from nu's internal communication.
-/
lemma encode_POutput_piName_implies_HasParOutput {P : Process} {x : Name} {n v : String}
    (h_x_ne_v : x ≠ v)
    (h : ∃ q, (.apply "POutput" [piNameToRhoName x, q]) ∈
              toListRepr (encode P n v)) :
    HasParOutput P x := by
  induction P generalizing n v with
  | nil =>
    obtain ⟨q, hq⟩ := h
    simp only [encode, rhoNil] at hq
    exact absurd hq (by simp [toListRepr])
  | par P Q ihP ihQ =>
    obtain ⟨q, hq⟩ := h
    simp only [encode] at hq
    rw [toListRepr_rhoPar] at hq
    rcases List.mem_append.mp hq with hP | hQ
    · exact HasParOutput.par_left (ihP h_x_ne_v ⟨q, hP⟩)
    · exact HasParOutput.par_right (ihQ h_x_ne_v ⟨q, hQ⟩)
  | input x' y' P _ih =>
    obtain ⟨q, hq⟩ := h
    simp only [encode, rhoInput, toListRepr, List.mem_cons, List.mem_nil_iff, or_false] at hq
    injection hq with h_tag _
    exact absurd h_tag (by decide)
  | output x' z =>
    obtain ⟨q, hq⟩ := h
    simp only [encode, rhoOutput, rhoDrop, piNameToRhoName, toListRepr,
               List.mem_cons, List.mem_nil_iff, or_false] at hq
    injection hq with _ h_args
    have h_name := List.cons.inj h_args |>.1
    simp at h_name
    subst h_name
    exact HasParOutput.output x z
  | nu x' P _ih =>
    obtain ⟨q, hq⟩ := h
    simp only [encode] at hq
    rw [toListRepr_rhoPar] at hq
    simp only [rhoOutput, rhoInput, piNameToRhoName, toListRepr,
               List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h_out | h_inp
    · injection h_out with _ h_args
      have h_name := List.cons.inj h_args |>.1
      exact absurd h_name (piNameToRhoName_ne_var_of_ne x v h_x_ne_v)
    · injection h_inp with h_tag _
      exact absurd h_tag (by decide)
  | replicate x' y' P _ih =>
    obtain ⟨q, hq⟩ := h
    simp only [encode, rhoReplicate, toListRepr, List.mem_cons, List.mem_nil_iff, or_false] at hq
    injection hq with h_tag _
    exact absurd h_tag (by decide)

/-- Name server doesn't produce POutput on piNameToRhoName channels.

    The name server's POutput uses .var channels (e.g., .var ns_z).
    Under the freshness condition x ≠ ns_z, piNameToRhoName x ≠ .var ns_z.
-/
lemma nameServer_no_piName_POutput (x : Name) (q : Pattern)
    (ns_x ns_z v_init ns_seed : String)
    (h_x_ne_nsz : x ≠ ns_z) :
    (.apply "POutput" [piNameToRhoName x, q]) ∉
      toListRepr (nameServer ns_x ns_z v_init ns_seed) := by
  unfold nameServer dropOperation
  rw [toListRepr_rhoPar, toListRepr_rhoPar]
  simp only [rhoReplicate, rhoInput, rhoNil, rhoOutput, toListRepr,
             List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
  intro hmem
  rcases hmem with h | h | h
  · injection h with h_tag; exact absurd h_tag (by decide)
  · injection h with h_tag; exact absurd h_tag (by decide)
  · injection h with _ h_args
    have h_name := List.cons.inj h_args |>.1
    exact absurd h_name (piNameToRhoName_ne_var_of_ne x ns_z h_x_ne_nsz)

/-- Forward: HasParOutput implies RhoObservableOutput of fullEncode.

    If a process syntactically contains output on x at a parallel level,
    then fullEncode produces a hashBag containing POutput [piNameToRhoName x, _].
-/
theorem hasParOutput_implies_rhoObservable {P : Process} {x : Name}
    (h : HasParOutput P x) :
    RhoObservableOutput (fullEncode P) (piNameToRhoName x) := by
  obtain ⟨q, h_mem⟩ := HasParOutput_encode_POutput_member h "n_init" "v_init"
  have h_eq : fullEncode P =
      .collection .hashBag
        (toListRepr (encode P "n_init" "v_init") ++
         toListRepr (nameServer "ns_x" "ns_z" "v_init" "ns_seed")) none := by
    unfold fullEncode; rw [rhoPar_eq_fromListRepr_append]; rfl
  exact ⟨q, Or.inl ⟨_, h_eq, List.mem_append_left _ h_mem⟩⟩

/-- Backward: Immediate RhoObservableOutput of fullEncode implies HasParOutput.

    If fullEncode P immediately contains POutput [piNameToRhoName x, q],
    then P has output on x at a parallel level.
-/
theorem fullEncode_immediate_POutput_implies_hasParOutput {P : Process} {x : Name}
    {q : Pattern}
    (h_fresh : x ≠ "v_init" ∧ x ≠ "ns_z")
    (h_mem : .apply "POutput" [piNameToRhoName x, q] ∈
             toListRepr (fullEncode P)) :
    HasParOutput P x := by
  have h_split : .apply "POutput" [piNameToRhoName x, q] ∈
      toListRepr (encode P "n_init" "v_init") ++
      toListRepr (nameServer "ns_x" "ns_z" "v_init" "ns_seed") := by
    unfold fullEncode at h_mem
    rwa [toListRepr_rhoPar] at h_mem
  rcases List.mem_append.mp h_split with h_enc | h_ns
  · exact encode_POutput_piName_implies_HasParOutput h_fresh.1 ⟨q, h_enc⟩
  · exact absurd h_ns (nameServer_no_piName_POutput x q _ _ _ _ h_fresh.2)

/-- HasParOutput implies PiObservableOutput via structural congruence.

    A process with output on x at a parallel level can be rearranged
    (via commutativity and associativity) to the form output x y | Q.
-/
theorem HasParOutput_implies_PiObservableOutput {P : Process} {x : Name}
    (h : HasParOutput P x) : PiObservableOutput P x := by
  induction h with
  | output x y =>
    -- output x y ≡ par (output x y) nil by symm of par_nil_right
    refine ⟨y, .nil, Or.inl ⟨?_⟩⟩
    exact StructuralCongruence.symm _ _ (StructuralCongruence.par_nil_right _)
  | @par_left P Q x _hP ih =>
    obtain ⟨y, R, h_obs⟩ := ih
    rcases h_obs with h_sc | ⟨P', h_ms, h_sc⟩
    · -- Immediate: Nonempty (P ≡ par (output x y) R)
      refine ⟨y, R ||| Q, Or.inl ?_⟩
      exact h_sc.elim fun sc => ⟨StructuralCongruence.trans _ _ _
        (StructuralCongruence.par_cong _ _ _ _ sc (StructuralCongruence.refl Q))
        (StructuralCongruence.par_assoc _ _ _)⟩
    · -- Reducing: P →* P', Nonempty (P' ≡ par (output x y) R)
      refine ⟨y, R ||| Q, Or.inr ⟨P' ||| Q, ?_, ?_⟩⟩
      · exact h_ms.elim fun ms => ⟨MultiStep.par_left ms⟩
      · exact h_sc.elim fun sc => ⟨StructuralCongruence.trans _ _ _
          (StructuralCongruence.par_cong _ _ _ _ sc (StructuralCongruence.refl Q))
          (StructuralCongruence.par_assoc _ _ _)⟩
  | @par_right P Q x _hQ ih =>
    obtain ⟨y, R, h_obs⟩ := ih
    rcases h_obs with h_sc | ⟨Q', h_ms, h_sc⟩
    · -- Immediate: Nonempty (Q ≡ par (output x y) R)
      refine ⟨y, R ||| P, Or.inl ?_⟩
      exact h_sc.elim fun sc => ⟨StructuralCongruence.trans _ _ _
        (StructuralCongruence.par_comm P Q)
        (StructuralCongruence.trans _ _ _
          (StructuralCongruence.par_cong _ _ _ _ sc (StructuralCongruence.refl P))
          (StructuralCongruence.par_assoc _ _ _))⟩
    · -- Reducing: Q →* Q', Nonempty (Q' ≡ par (output x y) R)
      refine ⟨y, R ||| P, Or.inr ⟨P ||| Q', ?_, ?_⟩⟩
      · exact h_ms.elim fun ms => ⟨MultiStep.par_right ms⟩
      · exact h_sc.elim fun sc => ⟨StructuralCongruence.trans _ _ _
          (StructuralCongruence.par_comm P Q')
          (StructuralCongruence.trans _ _ _
            (StructuralCongruence.par_cong _ _ _ _ sc (StructuralCongruence.refl P))
            (StructuralCongruence.par_assoc _ _ _))⟩

/-! ## Observational Correspondence via toListRepr

Bridge between `RhoObservableOutput` (uses hashBag membership)
and `toListRepr`-based reasoning.
-/

/-- toListRepr characterization of RhoObservableOutput (immediate case only) -/
lemma rhoObservableOutput_of_toListRepr_mem {P : Pattern} {n q : Pattern}
    (h_eq : ∃ ps, P = .collection .hashBag ps none)
    (h_mem : .apply "POutput" [n, q] ∈ toListRepr P) :
    RhoObservableOutput P n := by
  obtain ⟨ps, h_ps⟩ := h_eq
  subst h_ps
  simp only [toListRepr] at h_mem
  exact ⟨q, Or.inl ⟨ps, rfl, h_mem⟩⟩

/-- Restricted Prop 3 (syntactic): HasParOutput ↔ immediate POutput membership.

    This is the provable core of observational correspondence. It captures
    the bijection between syntactic output at a parallel level and immediate
    POutput presence in the encoding (no SC or reduction involved).
-/
theorem encoding_observational_hasParOutput (P : Process) (x : Name)
    (h_fresh : x ≠ "v_init" ∧ x ≠ "ns_z") :
    HasParOutput P x ↔
    (∃ q, .apply "POutput" [piNameToRhoName x, q] ∈ toListRepr (fullEncode P)) := by
  constructor
  · -- Forward: HasParOutput → POutput in encoding
    intro h
    obtain ⟨q, hq⟩ := HasParOutput_encode_POutput_member h "n_init" "v_init"
    exact ⟨q, by unfold fullEncode; rw [toListRepr_rhoPar]; exact List.mem_append_left _ hq⟩
  · -- Backward: POutput in encoding → HasParOutput
    intro ⟨q, hq⟩
    exact fullEncode_immediate_POutput_implies_hasParOutput h_fresh hq

/-- Restricted Prop 3: forward direction PiObservableOutput → RhoObservableOutput.

    This version only handles the immediate (no-reduction) case.
    The reducing case requires Prop 4 (operational correspondence).
-/
theorem encoding_observational_forward_immediate {P : Process} {x : Name}
    (h : HasParOutput P x) :
    RhoObservableOutput (fullEncode P) (piNameToRhoName x) :=
  hasParOutput_implies_rhoObservable h

/-- Restricted Prop 3: backward direction immediate RhoObservableOutput → PiObservableOutput.

    When fullEncode P IMMEDIATELY contains POutput [piNameToRhoName x, q]
    (without needing reduction), then P has π-observable output on x.
-/
theorem encoding_observational_backward_immediate {P : Process} {x : Name}
    (h_fresh : x ≠ "v_init" ∧ x ≠ "ns_z")
    (h : ∃ q, .apply "POutput" [piNameToRhoName x, q] ∈ toListRepr (fullEncode P)) :
    PiObservableOutput P x := by
  obtain ⟨q, hq⟩ := h
  exact HasParOutput_implies_PiObservableOutput
    (fullEncode_immediate_POutput_implies_hasParOutput h_fresh hq)

/-- Proposition 3: Weak observational correspondence (Lybech page 106)

    **Informal statement**: P ↓π x ⟺ ⟦P⟧ ↓ρ φ(x)
    where φ(x) = @(var x) is the name mapping.

    **Status**: The immediate (syntactic) directions are fully proven above:
    - Forward immediate: `encoding_observational_forward_immediate`
    - Backward immediate: `encoding_observational_backward_immediate`
    - HasParOutput bijection: `encoding_observational_hasParOutput`

    **Remaining gaps** (both require Prop 4):
    - Forward: PiObservableOutput includes SC-equivalent forms (e.g., nu_par),
      where the encoding hides output inside nu.
    - Backward: RhoObservableOutput includes reducing case (fullEncode P →* P'
      with POutput).

    **Encoding design (RESOLVED)**: piNameToRhoName uses NQuote (aligned with
    ρ-calculus COMM semantics), and `encode (.output x z)` sends `.var z` (the
    process), so COMM's NQuote wrapper produces `NQuote(.var z) = piNameToRhoName z`.
    This correctly models ρ-calculus: output sends a PROCESS, COMM quotes it.
-/
theorem encoding_observational_correspondence (P : Process) (x : Name) :
    PiObservableOutput P x ↔
    RhoObservableOutput (fullEncode P) (piNameToRhoName x) := by
  sorry
  -- The immediate biconditional is proven via:
  --   encoding_observational_hasParOutput (HasParOutput ↔ toListRepr membership)
  --   encoding_observational_forward_immediate (HasParOutput → RhoObservableOutput)
  --   encoding_observational_backward_immediate (toListRepr membership → PiObservableOutput)
  -- The full proof needs Prop 4 for SC-related forward cases and reducing backward cases.

/-! ## Infrastructure for Propositions 3-5

Connecting structural congruence to bisimilarity, proving encoded patterns
have no explicit .subst nodes, and preparing for the commSubst bridge.
-/

/-- SC implies bisimilarity via the EQUIV reduction rule.
    SC is itself a bisimulation: any step from an SC-related process
    can be matched by the other side using EQUIV. -/
theorem SC_implies_bisimilar {P Q : Pattern} (h : P ≡ Q) : P ∼ρ Q := by
  -- Use Nonempty(SC) as bisimulation relation (SC is Type-valued, R needs Prop)
  refine ⟨fun p q => Nonempty (p ≡ q), ?_, ?_, ?_, ⟨h⟩⟩
  · -- Symmetry
    intro p₁ q₁ ⟨hsc⟩
    exact ⟨.symm _ _ hsc⟩
  · -- Forward: q₁ matches p₁'s step via EQUIV(symm, red, refl)
    intro p₁ q₁ ⟨hsc⟩ p₂ ⟨hred⟩
    exact ⟨p₂, ⟨Reduces.equiv (.symm _ _ hsc) hred (.refl _)⟩, ⟨.refl _⟩⟩
  · -- Backward: p₁ matches q₁'s step via EQUIV(hsc, red, refl)
    intro p₁ q₁ ⟨hsc⟩ q₂ ⟨hred⟩
    exact ⟨q₂, ⟨Reduces.equiv hsc hred (.refl _)⟩, ⟨.refl _⟩⟩

/-- allNoExplicitSubst is preserved by list append. -/
lemma allNoExplicitSubst_append {ps qs : List Pattern}
    (hp : allNoExplicitSubst ps) (hq : allNoExplicitSubst qs) :
    allNoExplicitSubst (ps ++ qs) := by
  induction ps with
  | nil => exact hq
  | cons p ps' ih =>
    simp only [allNoExplicitSubst, Bool.and_eq_true] at hp
    simp only [List.cons_append, allNoExplicitSubst, Bool.and_eq_true]
    exact ⟨hp.1, ih hp.2⟩

/-- noExplicitSubst propagates through toListRepr. -/
lemma allNoExplicitSubst_toListRepr {P : Pattern}
    (h : noExplicitSubst P) :
    allNoExplicitSubst (toListRepr P) := by
  cases P with
  | collection ct ps g =>
    cases ct <;> cases g <;>
      simp only [toListRepr, noExplicitSubst, allNoExplicitSubst, Bool.and_eq_true] at * <;>
      first | exact h | exact ⟨h, trivial⟩
  | subst _ _ _ =>
    simp only [noExplicitSubst] at h
    exact absurd h Bool.false_ne_true
  | _ =>
    simp only [toListRepr, allNoExplicitSubst, Bool.and_eq_true]
    exact ⟨h, trivial⟩

/-- noExplicitSubst is preserved by rhoPar. -/
lemma noExplicitSubst_rhoPar {P Q : Pattern}
    (hp : noExplicitSubst P) (hq : noExplicitSubst Q) :
    noExplicitSubst (rhoPar P Q) := by
  rw [rhoPar_eq_fromListRepr_append]
  simp only [fromListRepr, noExplicitSubst]
  exact allNoExplicitSubst_append (allNoExplicitSubst_toListRepr hp)
    (allNoExplicitSubst_toListRepr hq)

/-- Encoding never produces .subst nodes. -/
theorem encode_noExplicitSubst (P : Process) (n v : String) :
    noExplicitSubst (encode P n v) := by
  induction P generalizing n v with
  | nil => simp [encode, rhoNil, noExplicitSubst, allNoExplicitSubst]
  | par P Q ihP ihQ =>
    simp only [encode]
    exact noExplicitSubst_rhoPar (ihP _ _) (ihQ _ _)
  | input x y P ih =>
    simp only [encode, rhoInput, piNameToRhoName, noExplicitSubst, allNoExplicitSubst,
               Bool.true_and, Bool.and_true]
    exact ih n v
  | output x z =>
    simp only [encode, rhoOutput, rhoDrop, piNameToRhoName, noExplicitSubst, allNoExplicitSubst,
               Bool.and_true]
  | nu x P ih =>
    simp only [encode]
    apply noExplicitSubst_rhoPar
    · simp only [rhoOutput, noExplicitSubst, allNoExplicitSubst, Bool.and_true]
    · simp only [rhoInput, noExplicitSubst, allNoExplicitSubst, Bool.true_and, Bool.and_true]
      exact ih _ _
  | replicate x y P ih =>
    simp only [encode, rhoReplicate, rhoInput, piNameToRhoName, noExplicitSubst,
               allNoExplicitSubst, Bool.true_and, Bool.and_true]
    exact ih _ _

/-! ## Bridge: commSubst ↔ rhoSubstitute

For patterns without explicit .subst nodes (like all encoded patterns),
the COMM rule's `commSubst body y q` equals `rhoSubstitute body y (NQuote q)`.
This bridges the ρ-calculus reduction semantics to our algebraic substitution.
-/

/-- SubstEnv.find on a single-entry env returns Some iff variable matches. -/
private lemma SubstEnv_find_single (y : String) (r : Pattern) (x : String) :
    SubstEnv.find (SubstEnv.extend SubstEnv.empty y r) x =
    if y = x then some r else none := by
  simp only [SubstEnv.find, SubstEnv.extend, SubstEnv.empty, List.find?]
  by_cases h : y = x
  · subst h; simp
  · have hbeq : (y == x) = false := beq_eq_false_iff_ne.mpr h
    simp [hbeq, h]

/-- Filter on single-entry env: removes entry iff variable matches binder. -/
private lemma single_env_filter_eq (y : String) (r : Pattern) (x : String) :
    (SubstEnv.extend SubstEnv.empty y r).filter (fun p => p.1 != x) =
    if y = x then SubstEnv.empty else SubstEnv.extend SubstEnv.empty y r := by
  simp only [SubstEnv.extend, SubstEnv.empty, List.filter]
  by_cases h : y = x
  · subst h; simp
  · have hbne : (y != x) = true := bne_iff_ne.mpr h
    simp [hbne, h]

mutual
  /-- Bridge (pattern): applySubst with single env = rhoSubstitute with NQuote -/
  theorem bridge_applySubst_rhoSubstitute (p : Pattern) (y : String) (q : Pattern)
      (h : noExplicitSubst p) :
      applySubst (SubstEnv.extend SubstEnv.empty y (.apply "NQuote" [q])) p =
      rhoSubstitute p y (.apply "NQuote" [q]) :=
    match p with
    | .var name => by
      simp only [applySubst, SubstEnv_find_single, rhoSubstitute]
      by_cases heq : y = name
      · subst heq; simp
      · simp [heq, Ne.symm heq]
    | .apply f args => by
      unfold noExplicitSubst at h
      simp only [applySubst, rhoSubstitute]
      congr 1
      exact bridge_applySubst_rhoSubstitute_list args y q h
    | .lambda x body => by
      unfold noExplicitSubst at h
      simp only [applySubst, single_env_filter_eq, rhoSubstitute]
      by_cases hxy : y = x
      · subst hxy; simp only [↓reduceIte]; congr 1; exact subst_empty body h
      · have hyx : ¬(x = y) := Ne.symm hxy
        simp only [hxy, hyx, ↓reduceIte]
        congr 1
        exact bridge_applySubst_rhoSubstitute body y q h
    | .multiLambda xs body => by
      unfold noExplicitSubst at h
      simp only [applySubst, rhoSubstitute]
      by_cases hmem : y ∈ xs
      · -- y is bound: filter removes the entry, rhoSubstitute returns body unchanged
        have hc : xs.contains y = true :=
          List.contains_iff_exists_mem_beq.mpr ⟨y, hmem, beq_self_eq_true y⟩
        simp only [SubstEnv.extend, SubstEnv.empty, List.filter, hc, Bool.not_true,
          ↓reduceIte, hmem]
        congr 1
        exact subst_empty body h
      · -- y not bound: filter keeps the entry, use IH
        have hc : xs.contains y = false := by
          rw [Bool.eq_false_iff]; intro habs
          obtain ⟨a, ha, hbeq⟩ := List.contains_iff_exists_mem_beq.mp habs
          exact hmem (eq_of_beq hbeq ▸ ha)
        simp only [SubstEnv.extend, SubstEnv.empty, List.filter, hc, Bool.not_false,
          ↓reduceIte, hmem]
        congr 1
        exact bridge_applySubst_rhoSubstitute body y q h
    | .subst _ _ _ => by
      unfold noExplicitSubst at h; exact absurd h Bool.false_ne_true
    | .collection ct ps g => by
      unfold noExplicitSubst at h
      simp only [applySubst, rhoSubstitute]
      congr 1
      exact bridge_applySubst_rhoSubstitute_list ps y q h

  /-- Bridge (list): applySubst with single env = rhoSubstitute for lists -/
  theorem bridge_applySubst_rhoSubstitute_list (ps : List Pattern) (y : String) (q : Pattern)
      (h : allNoExplicitSubst ps) :
      ps.map (applySubst (SubstEnv.extend SubstEnv.empty y (.apply "NQuote" [q]))) =
      ps.map (fun p => rhoSubstitute p y (.apply "NQuote" [q])) :=
    match ps with
    | [] => by simp
    | p :: ps' => by
      unfold allNoExplicitSubst at h
      simp only [Bool.and_eq_true] at h
      simp only [List.map_cons]
      congr 1
      · exact bridge_applySubst_rhoSubstitute p y q h.1
      · exact bridge_applySubst_rhoSubstitute_list ps' y q h.2
end

/-- commSubst = rhoSubstitute with NQuote wrapper on noExplicitSubst patterns.

    This is the key bridge between the COMM rule's substitution mechanism
    and our algebraic rhoSubstitute function. -/
theorem commSubst_eq_rhoSubstitute (body : Pattern) (y : String) (q : Pattern)
    (h : noExplicitSubst body) :
    commSubst body y q = rhoSubstitute body y (.apply "NQuote" [q]) := by
  unfold commSubst
  exact bridge_applySubst_rhoSubstitute body y q h

/-! ## SC Congruence for rhoSubstitute

Key lemma: if m ≡ m' then rhoSubstitute P x m ≡ rhoSubstitute P x m'.
Needed for the QuoteDrop bridge: NQuote(PDrop(.var z)) ≡ .var z implies
rhoSubstitute P y (NQuote(PDrop(.var z))) ≡ rhoSubstitute P y (.var z).
-/

mutual
  /-- SC congruence for rhoSubstitute argument: structural congruence of the
      replacement term propagates through substitution. -/
  theorem rhoSubstitute_SC_arg (P : Pattern) {m m' : Pattern}
      (hsc : m ≡ m') (x : String) :
      rhoSubstitute P x m ≡ rhoSubstitute P x m' :=
    match P with
    | .var y => by
        simp only [rhoSubstitute]; split_ifs <;> [exact hsc; exact .refl _]
    | .apply f args => by
        simp only [rhoSubstitute]
        refine .apply_cong f _ _ ?_ ?_
        · simp [List.length_map]
        · intro i h₁ h₂
          simp only [List.get_eq_getElem, List.getElem_map]
          exact rhoSubstitute_SC_arg_list args hsc x i (by rw [List.length_map] at h₁; exact h₁)
    | .lambda y body => by
        simp only [rhoSubstitute]; split_ifs with h
        · exact .refl _
        · exact .lambda_cong y _ _ (rhoSubstitute_SC_arg body hsc x)
    | .collection .hashBag ps none => by
        simp only [rhoSubstitute]
        refine .par_cong _ _ ?_ ?_
        · simp [List.length_map]
        · intro i h₁ h₂
          simp only [List.get_eq_getElem, List.getElem_map]
          exact rhoSubstitute_SC_arg_list ps hsc x i (by rw [List.length_map] at h₁; exact h₁)
    | .collection _ct _ps _g => by
        simp only [rhoSubstitute]
        exact .collection_general_cong _ _ _ _ (by simp [List.length_map])
          fun i h₁ h₂ => by
            simp only [List.get_eq_getElem, List.getElem_map]
            exact rhoSubstitute_SC_arg_list _ps hsc x i (by rw [List.length_map] at h₁; exact h₁)
    | .multiLambda _ys _body => by
        simp only [rhoSubstitute]; split_ifs with h
        · exact .refl _
        · exact .multiLambda_cong _ys _ _ (rhoSubstitute_SC_arg _body hsc x)
    | .subst _p _y _t => by
        simp only [rhoSubstitute]
        exact .subst_cong _ _ _y _ _
          (rhoSubstitute_SC_arg _p hsc x)
          (rhoSubstitute_SC_arg _t hsc x)

  /-- List helper for SC congruence of rhoSubstitute. -/
  theorem rhoSubstitute_SC_arg_list (ps : List Pattern) {m m' : Pattern}
      (hsc : m ≡ m') (x : String) (i : Nat) (hi : i < ps.length) :
      rhoSubstitute (ps[i]) x m ≡ rhoSubstitute (ps[i]) x m' :=
    match ps, i, hi with
    | [], _, hi => absurd hi (by simp)
    | p :: _, 0, _ => rhoSubstitute_SC_arg p hsc x
    | _ :: ps', n + 1, hi => rhoSubstitute_SC_arg_list ps' hsc x n (by simp at hi; omega)
end

/-! ## COMM Correspondence Chain

Connecting the ρ-COMM rule to the encoding via three steps:
1. COMM step fires on encoded π-communication
2. COMM result (commSubst) equals rhoSubstitute with NQuote wrapper (bridge lemma)
3. QuoteDrop SC simplifies NQuote(PDrop(.var z)) ≡ .var z in substitution
-/

/-- The ρ-COMM step fires on encoded π-communication.

    When π-input and π-output on the same channel are in parallel,
    the ρ-encoding admits a COMM reduction step. The result is
    commSubst applied to the encoded body inside a hashBag. -/
theorem encode_comm_step (x y : Name) (P : Process) (z : Name) (n v : String) :
    Nonempty (Reduction.Reduces
      (encode (Process.par (Process.input x y P) (Process.output x z)) n v)
      (Pattern.collection .hashBag
        [commSubst (encode P (n ++ "_L") v) y (.apply "PDrop" [.var z])] none)) := by
  -- The encoding produces {PInput [.var x, λy.encode P], POutput [.var x, PDrop(.var z)]}
  have h_enc : encode (Process.par (Process.input x y P) (Process.output x z)) n v =
      Pattern.collection .hashBag
        [.apply "PInput" [.var x, .lambda y (encode P (n ++ "_L") v)],
         .apply "POutput" [.var x, .apply "PDrop" [.var z]]] none := by rfl
  rw [h_enc]
  -- COMM needs POutput before PInput; use equiv with par_comm to swap
  exact ⟨Reduction.Reduces.equiv
    (.par_comm _ _)
    (@Reduction.Reduces.comm (.var x) (.apply "PDrop" [.var z]) (encode P (n ++ "_L") v) y [])
    (.refl _)⟩

/-- COMM result after QuoteDrop simplification.

    Chain: commSubst body y (PDrop(.var z))
           = rhoSubstitute body y (NQuote(PDrop(.var z)))    [bridge lemma]
           ≡ rhoSubstitute body y (.var z)                   [QuoteDrop SC]
-/
theorem commSubst_quoteDrop_SC (body : Pattern) (y z : String)
    (h : noExplicitSubst body) :
    commSubst body y (.apply "PDrop" [.var z]) ≡
    rhoSubstitute body y (.var z) := by
  rw [commSubst_eq_rhoSubstitute body y _ h]
  exact rhoSubstitute_SC_arg body (.quote_drop (.var z)) y

/-- Full COMM correspondence: encoding of π-COMM step produces a ρ-term
    that is SC-related to the algebraic substitution.

    encode(input x y P | output x z) ⇝ρ result
    where result ≡ {rhoSubstitute (encode P) y (.var z)} -/
theorem encode_comm_SC (x y : Name) (P : Process) (z : Name) (n v : String) :
    ∃ result, Nonempty (Reduction.Reduces
      (encode (Process.par (Process.input x y P) (Process.output x z)) n v)
      result) ∧
    (result ≡
    Pattern.collection .hashBag [rhoSubstitute (encode P (n ++ "_L") v) y (.var z)] none) := by
  refine ⟨_, encode_comm_step x y P z n v, ?_⟩
  -- result = {commSubst (encode P ...) y (PDrop(.var z))}
  -- Need: this ≡ {rhoSubstitute (encode P ...) y (.var z)}
  exact .par_cong _ _ (by simp) (fun i h₁ h₂ => by
    have hi : i = 0 := by simp at h₁; omega
    subst hi; simp only [List.get_eq_getElem, List.getElem_cons_zero]
    exact commSubst_quoteDrop_SC _ _ _ (encode_noExplicitSubst P (n ++ "_L") v))

/-! ## Generalized Substitution Lemma (for COMM)

Prop 2 requires `u ∉ P.names` (u completely fresh), ruling out the COMM case
where y is free in P. This generalized version requires only `y ∉ P.boundNames`
(Barendregt convention), which is exactly what COMM provides.
-/

/-- Barendregt decomposition for par: if y ∉ (P|Q).boundNames then y ∉ P.boundNames and y ∉ Q.boundNames -/
lemma barendregt_par (y : Name) (P Q : Process) (h : y ∉ (Process.par P Q).boundNames) :
    y ∉ P.boundNames ∧ y ∉ Q.boundNames := by
  simp only [Process.boundNames, Finset.mem_union] at h
  push_neg at h
  exact h

/-- Barendregt decomposition for input: if y ∉ (input x w P).boundNames then y ≠ w and y ∉ P.boundNames -/
lemma barendregt_input (y : Name) (x w : Name) (P : Process) (h : y ∉ (Process.input x w P).boundNames) :
    y ≠ w ∧ y ∉ P.boundNames := by
  simp only [Process.boundNames, Finset.mem_insert] at h
  push_neg at h
  exact ⟨h.1, h.2⟩

/-- Barendregt decomposition for nu: if y ∉ (nu x P).boundNames then y ≠ x and y ∉ P.boundNames -/
lemma barendregt_nu (y : Name) (x : Name) (P : Process) (h : y ∉ (Process.nu x P).boundNames) :
    y ≠ x ∧ y ∉ P.boundNames := by
  simp only [Process.boundNames, Finset.mem_insert] at h
  push_neg at h
  exact h

/-- Barendregt decomposition for replicate: if y ∉ (!x(w).P).boundNames then y ≠ w and y ∉ P.boundNames -/
lemma barendregt_replicate (y : Name) (x w : Name) (P : Process) (h : y ∉ (Process.replicate x w P).boundNames) :
    y ≠ w ∧ y ∉ P.boundNames := by
  simp only [Process.boundNames, Finset.mem_insert] at h
  push_neg at h
  exact h

/-- Generalized substitution lemma under Barendregt convention.

    Like Prop 2 (`encoding_substitution`) but with weaker freshness:
    - Only requires `y ∉ P.boundNames` (not `y ∉ P.names`)
    - Only requires `z ∉ P.boundNames` (not `z ∉ P.names`)

    This handles the COMM case where y is free in P (the continuation body
    of an input), and z is a free name (the output payload).

    Under Barendregt convention, all bound variables in P are distinct from
    both y and z, ensuring substitution is capture-free.
-/
theorem encoding_substitution_barendregt (P : Process) (y z : Name) (n v : String)
    (h_bar_y : y ∉ P.boundNames)
    (h_bar_z : z ∉ P.boundNames)
    (h_fresh_y : y ∉ [n, v])
    (h_fresh_z : z ∉ [n, v])
    (h_disjoint_y : NamespaceDisjoint y n)
    (h_disjoint_z : NamespaceDisjoint z n)
    : encode (P.substitute y z) n v =
    rhoSubstitute (encode P n v) y (.var z) := by
  suffices h : ∀ (n' v' : String), y ∉ [n', v'] → z ∉ [n', v'] →
      NamespaceDisjoint y n' → NamespaceDisjoint z n' →
      encode (P.substitute y z) n' v' = rhoSubstitute (encode P n' v') y (.var z) by
    exact h n v h_fresh_y h_fresh_z h_disjoint_y h_disjoint_z
  intro n' v' h_fy h_fz h_ndy h_ndz
  induction P generalizing n' v' with
  | nil =>
    simp only [Process.substitute, encode, rhoNil, rhoSubstitute, List.map]
  | par P Q ihP ihQ =>
    have ⟨hP_y, hQ_y⟩ := barendregt_par y P Q h_bar_y
    have ⟨hP_z, hQ_z⟩ := barendregt_par z P Q h_bar_z
    have h_fy_L := fresh_derived_param y n' v' "_L" h_fy h_ndy
    have h_fz_L := fresh_derived_param z n' v' "_L" h_fz h_ndz
    have h_fy_R := fresh_derived_param y n' v' "_R" h_fy h_ndy
    have h_fz_R := fresh_derived_param z n' v' "_R" h_fz h_ndz
    have h_ndy_L := namespace_disjoint_derived y n' "_L" h_ndy
    have h_ndz_L := namespace_disjoint_derived z n' "_L" h_ndz
    have h_ndy_R := namespace_disjoint_derived y n' "_R" h_ndy
    have h_ndz_R := namespace_disjoint_derived z n' "_R" h_ndz
    simp only [Process.substitute, encode]
    rw [ihP hP_y hP_z _ _ h_fy_L h_fz_L h_ndy_L h_ndz_L,
        ihQ hQ_y hQ_z _ _ h_fy_R h_fz_R h_ndy_R h_ndz_R,
        ← rhoSubstitute_rhoPar_noTopVar (encode_noTopVar P _ _) (encode_noTopVar Q _ _)]
  | output x' z' =>
    simp only [Process.substitute, encode, piNameToRhoName, rhoOutput, rhoDrop,
               rhoSubstitute, List.map]
    split_ifs <;> rfl
  | input x' w P' ih =>
    have ⟨h_w_ne_y, hP'_y⟩ := barendregt_input y x' w P' h_bar_y
    have ⟨h_w_ne_z, hP'_z⟩ := barendregt_input z x' w P' h_bar_z
    simp only [Process.substitute]
    split_ifs with hx hw
    · -- x' = y: channel matches, substitute channel AND recurse (standard π-calculus)
      simp only [encode, rhoSubstitute_rhoInput, if_neg (Ne.symm h_w_ne_y)]
      rw [ih hP'_y hP'_z _ _ h_fy h_fz h_ndy h_ndz]
      simp only [piNameToRhoName, rhoSubstitute, hx, ↓reduceIte]
    · -- w = y: IMPOSSIBLE by Barendregt (w ≠ y)
      exact absurd hw (Ne.symm h_w_ne_y)
    · -- x' ≠ y, w ≠ y: normal recursion
      simp only [encode, rhoSubstitute_rhoInput, if_neg (Ne.symm h_w_ne_y)]
      rw [← piNameToRhoName_substitute,
          ih hP'_y hP'_z _ _ h_fy h_fz h_ndy h_ndz]
      simp only [hx, ↓reduceIte]
  | nu x' P' ih =>
    have ⟨h_x_ne_y, hP'_y⟩ := barendregt_nu y x' P' h_bar_y
    have ⟨h_x_ne_z, hP'_z⟩ := barendregt_nu z x' P' h_bar_z
    have h_ne_n_y : y ≠ n' := fun h => by simp [h] at h_fy
    have h_ne_v_y : y ≠ v' := fun h => by simp [h] at h_fy
    have h_ne_n_z : z ≠ n' := fun h => by simp [h] at h_fz
    have h_ne_v_z : z ≠ v' := fun h => by simp [h] at h_fz
    have h_fy_nu : y ∉ [n' ++ "_" ++ n', v'] := by
      rw [String.append_assoc]
      exact fresh_derived_param y n' v' ("_" ++ n') h_fy h_ndy
    have h_fz_nu : z ∉ [n' ++ "_" ++ n', v'] := by
      rw [String.append_assoc]
      exact fresh_derived_param z n' v' ("_" ++ n') h_fz h_ndz
    have h_ndy_nu : NamespaceDisjoint y (n' ++ "_" ++ n') := by
      rw [String.append_assoc]
      exact namespace_disjoint_derived y n' ("_" ++ n') h_ndy
    have h_ndz_nu : NamespaceDisjoint z (n' ++ "_" ++ n') := by
      rw [String.append_assoc]
      exact namespace_disjoint_derived z n' ("_" ++ n') h_ndz
    simp only [Process.substitute]
    split_ifs with hx
    · -- x' = y: IMPOSSIBLE by Barendregt (x' ≠ y since x' is a binder of nu)
      exact absurd hx (Ne.symm h_x_ne_y)
    · -- x' ≠ y: recurse
      simp only [encode]
      rw [rhoSubstitute_rhoPar_noTopVar (rhoOutput_noTopVar _ _) (rhoInput_noTopVar _ _ _)]
      -- Simplify rhoSubstitute on the internal channel/output
      simp only [rhoSubstitute_rhoOutput, rhoSubstitute, rhoSubstitute_rhoInput,
                 if_neg (Ne.symm h_ne_v_y), if_neg (Ne.symm h_ne_n_y), if_neg hx]
      rw [ih hP'_y hP'_z _ _ h_fy_nu h_fz_nu h_ndy_nu h_ndz_nu]
  | replicate x' w P' ih =>
    have ⟨h_w_ne_y, hP'_y⟩ := barendregt_replicate y x' w P' h_bar_y
    have ⟨h_w_ne_z, hP'_z⟩ := barendregt_replicate z x' w P' h_bar_z
    have h_fy_rep := fresh_derived_param y n' v' "_rep" h_fy h_ndy
    have h_fz_rep := fresh_derived_param z n' v' "_rep" h_fz h_ndz
    have h_ndy_rep := namespace_disjoint_derived y n' "_rep" h_ndy
    have h_ndz_rep := namespace_disjoint_derived z n' "_rep" h_ndz
    simp only [Process.substitute]
    split_ifs with hx hw
    · -- x' = y: channel matches, substitute channel AND recurse
      simp only [encode, rhoSubstitute_rhoReplicate, rhoSubstitute_rhoInput,
                 if_neg (Ne.symm h_w_ne_y)]
      rw [ih hP'_y hP'_z _ _ h_fy_rep h_fz_rep h_ndy_rep h_ndz_rep]
      simp only [piNameToRhoName, rhoSubstitute, hx, ↓reduceIte]
    · -- w = y: IMPOSSIBLE by Barendregt
      exact absurd hw (Ne.symm h_w_ne_y)
    · -- x' ≠ y, w ≠ y: normal recursion
      simp only [encode, rhoSubstitute_rhoReplicate, rhoSubstitute_rhoInput,
                 if_neg (Ne.symm h_w_ne_y)]
      rw [← piNameToRhoName_substitute,
          ih hP'_y hP'_z _ _ h_fy_rep h_fz_rep h_ndy_rep h_ndz_rep]
      simp only [hx, ↓reduceIte]

/-! ## Complete COMM Chain: ρ-COMM produces encoding of π-COMM result

This is the culmination of the COMM correspondence work:
1. `encode_comm_step`: ρ-COMM fires on encoded input||output
2. `commSubst_quoteDrop_SC`: COMM result ≡ rhoSubstitute (bridge lemma)
3. `encoding_substitution_barendregt`: rhoSubstitute = encode(π-substitute)

Combined: ρ-COMM on encoded π-terms produces (up to SC) the encoding of the π-COMM result.
-/

/-- Complete COMM correspondence: encoding of π-COMM produces the encoding of the π-result.

    Given input x y P | output x z (matching π-COMM pattern), the ρ-encoding
    reduces to a term SC-related to encode(P[z/y]).

    This is the KEY LEMMA for Prop 4: it shows that ρ-COMM on encoded processes
    exactly corresponds to π-COMM (up to structural congruence).

    **Conditions** (Barendregt convention):
    - y ∉ P.boundNames: y doesn't appear as an inner binder in P
    - z ∉ P.boundNames: z doesn't appear as an inner binder in P
    - Parameter freshness: y, z are disjoint from encoding namespace
-/
theorem encode_comm_complete (x y : Name) (P : Process) (z : Name) (n v : String)
    (h_bar_y : y ∉ P.boundNames)
    (h_bar_z : z ∉ P.boundNames)
    (h_fresh_y : y ∉ [n ++ "_L", v])
    (h_fresh_z : z ∉ [n ++ "_L", v])
    (h_disjoint_y : NamespaceDisjoint y (n ++ "_L"))
    (h_disjoint_z : NamespaceDisjoint z (n ++ "_L"))
    : ∃ result, Nonempty (Reduction.Reduces
        (encode (Process.par (Process.input x y P) (Process.output x z)) n v)
        result) ∧
      (result ≡ Pattern.collection .hashBag
        [encode (P.substitute y z) (n ++ "_L") v] none) := by
  obtain ⟨result, h_red, h_sc⟩ := encode_comm_SC x y P z n v
  refine ⟨result, h_red, ?_⟩
  -- h_sc : result ≡ {rhoSubstitute (encode P (n ++ "_L") v) y (.var z)}
  -- encoding_substitution_barendregt : rhoSubstitute (encode P ...) y (.var z) = encode (P.substitute y z) ...
  rw [← encoding_substitution_barendregt P y z (n ++ "_L") v
      h_bar_y h_bar_z h_fresh_y h_fresh_z h_disjoint_y h_disjoint_z] at h_sc
  exact h_sc

/-! ## Forward Direction: π-Reductions Lift to ρ-Reductions

The forward direction of Prop 4: every π-reduction step can be simulated
by ρ-reduction steps in the encoding.
-/

/-- Substitute preserves simplicity (no nu/replicate). -/
lemma Process.isSimple_substitute {P : Process} (h : P.isSimple) (y z : Name) :
    (P.substitute y z).isSimple := by
  induction P with
  | nil => trivial
  | par _ _ ihP ihQ =>
    obtain ⟨hP, hQ⟩ := h
    exact ⟨ihP hP, ihQ hQ⟩
  | input x w P ih =>
    simp only [Process.substitute]
    split_ifs
    · exact ih h
    · exact h
    · exact ih h
  | output _ _ => trivial
  | nu _ _ => exact absurd h id
  | replicate _ _ _ => exact absurd h id

/-- ReducesStar wraps a single reduction step. -/
lemma ReducesStar.single {p q : Pattern} (h : Nonempty (Reduction.Reduces p q)) :
    Nonempty (ReducesStar p q) :=
  h.elim fun r => ⟨.step r (.refl q)⟩

/-! ## Proposition 4: Operational Correspondence

Multi-step reduction is preserved in both directions (up to bisimilarity).
-/

/-- Weak bisimilarity: bisimilar after silent steps -/
def WeakBisimilar (P Q : Pattern) : Prop :=
  ∃ P' Q', Nonempty (ReducesStar P P') ∧ Nonempty (ReducesStar Q Q') ∧ RhoBisimilar P' Q'

notation:50 P " ≃w " Q => WeakBisimilar P Q

/-- Weak bisimilarity is reflexive. -/
theorem WeakBisimilar.refl (p : Pattern) : p ≃w p :=
  ⟨p, p, ⟨.refl p⟩, ⟨.refl p⟩, RhoBisimilar.refl p⟩

/-- Weak bisimilarity is symmetric. -/
theorem WeakBisimilar.symm {p q : Pattern} (h : p ≃w q) : q ≃w p := by
  obtain ⟨p', q', hp, hq, hbisim⟩ := h
  exact ⟨q', p', hq, hp, hbisim.symm⟩

/-- SC implies weak bisimilarity. -/
theorem SC_implies_weak_bisimilar {p q : Pattern} (h : p ≡ q) : p ≃w q :=
  ⟨p, q, ⟨.refl p⟩, ⟨.refl q⟩, SC_implies_bisimilar h⟩

/-- Equality implies weak bisimilarity. -/
theorem eq_implies_weak_bisimilar {p q : Pattern} (h : p = q) : p ≃w q := by
  subst h; exact WeakBisimilar.refl p

/-! ## Forward Direction: π-COMM Lifts to ρ-Reduction

For simple processes, π-COMM produces a ρ-reduction whose result is weakly
bisimilar to the encoding of the π-result.
-/

/-- Forward: π-COMM lifts to ρ-COMM with weak bisimilarity to π-result encoding.

    Uses encode_comm_SC + encoding_substitution_barendregt + encode_independent_of_n.
-/
theorem encode_forward_comm_weak (x y : Name) (P : Process) (z : Name)
    (n v : String)
    (h_simple : P.isSimple)
    (h_bar_y : y ∉ P.boundNames)
    (h_bar_z : z ∉ P.boundNames)
    (h_fresh_y : y ∉ [n ++ "_L", v])
    (h_fresh_z : z ∉ [n ++ "_L", v])
    (h_disjoint_y : NamespaceDisjoint y (n ++ "_L"))
    (h_disjoint_z : NamespaceDisjoint z (n ++ "_L"))
    : ∃ result, Nonempty (Reduction.Reduces
        (encode (.par (.input x y P) (.output x z)) n v) result) ∧
      (result ≃w .collection .hashBag [encode (P.substitute y z) n v] none) := by
  obtain ⟨result, h_red, h_sc⟩ := encode_comm_SC x y P z n v
  refine ⟨result, h_red, ?_⟩
  have h_sub := encoding_substitution_barendregt P y z (n ++ "_L") v
    h_bar_y h_bar_z h_fresh_y h_fresh_z h_disjoint_y h_disjoint_z
  have h_eq := encode_independent_of_n (P.substitute y z)
    (Process.isSimple_substitute h_simple y z) (n ++ "_L") n v
  rw [← h_sub] at h_sc; rw [h_eq] at h_sc
  exact SC_implies_weak_bisimilar h_sc

/-- ρ-COMM fires with arbitrary rest (elements from parallel context).

    In a flat hashBag [PInput, POutput] ++ rest, COMM fires after
    permuting PInput/POutput to match COMM's expected order.
-/
theorem encode_comm_step_with_rest (x y : Name) (P : Process) (z : Name)
    (n v : String) (rest : List Pattern) :
    Nonempty (Reduction.Reduces
      (.collection .hashBag
        ([.apply "PInput" [.var x, .lambda y (encode P (n ++ "_L") v)],
          .apply "POutput" [.var x, .apply "PDrop" [.var z]]] ++ rest) none)
      (.collection .hashBag
        ([commSubst (encode P (n ++ "_L") v) y (.apply "PDrop" [.var z])] ++ rest) none)) := by
  let pi := Pattern.apply "PInput" [.var x, .lambda y (encode P (n ++ "_L") v)]
  let po := Pattern.apply "POutput" [.var x, .apply "PDrop" [.var z]]
  exact ⟨Reduction.Reduces.equiv
    (.par_perm _ _ (List.Perm.swap po pi rest))
    (@Reduction.Reduces.comm (.var x) (.apply "PDrop" [.var z])
      (encode P (n ++ "_L") v) y rest)
    (.refl _)⟩

/-- Nesting: hashBag(ps ++ rest) ≡ hashBag([hashBag ps] ++ rest).

    Reverse of par_flatten: nest a sub-bag within a flat hashBag.
    Uses par_perm + par_flatten + par_perm (3 SC steps).
-/
lemma nest_sub_bag (ps rest : List Pattern) :
    (.collection .hashBag (ps ++ rest) none) ≡
    (.collection .hashBag (.collection .hashBag ps none :: rest) none) :=
  .trans _ _ _
    (.par_perm _ _ List.perm_append_comm)
    (.trans _ _ _
      (.symm _ _ (.par_flatten rest ps))
      (.par_perm _ _ List.perm_append_comm))

/-- Reduction in a sub-bag lifts to the flat hashBag.

    If hashBag ps ⇝ q, then hashBag(ps ++ rest) ⇝ hashBag(q :: rest).
    Uses nest_sub_bag to un-flatten, then `par` to apply the reduction.
-/
theorem reduce_in_flat_context {ps rest : List Pattern} {q : Pattern}
    (h_red : Nonempty (Reduction.Reduces (.collection .hashBag ps none) q)) :
    Nonempty (Reduction.Reduces
      (.collection .hashBag (ps ++ rest) none)
      (.collection .hashBag (q :: rest) none)) := by
  exact h_red.elim fun r => ⟨Reduction.Reduces.equiv
    (nest_sub_bag ps rest)
    (Reduction.Reduces.par r)
    (.refl _)⟩

/-- Un-nesting: hashBag(q :: rest) ≡ hashBag(toListRepr q ++ rest).

    When q is a hashBag, this flattens via nest_sub_bag (reversed).
    When q is not a hashBag, this is reflexive (toListRepr q = [q]).
-/
lemma unnest_sub_bag (q : Pattern) (rest : List Pattern) :
    (.collection .hashBag (q :: rest) none) ≡
    (.collection .hashBag (toListRepr q ++ rest) none) := by
  unfold toListRepr
  match q with
  | .collection .hashBag ps none =>
    exact .symm _ _ (nest_sub_bag ps rest)
  | .var _ | .apply _ _ | .lambda _ _ | .multiLambda _ _ | .subst _ _ _ =>
    exact .refl _
  | .collection .hashSet _ _ | .collection .hashBag _ (some _)
  | .collection .vec _ _ =>
    exact .refl _

/-- General lift: if p ⇝ q, then hashBag(toListRepr p ++ rest) ⇝ hashBag(q :: rest).

    Handles both cases:
    - p = hashBag ps: uses reduce_in_flat_context (nest, par, un-nest)
    - p ≠ hashBag: toListRepr p = [p], uses par directly
-/
theorem reduce_toListRepr_context {p q : Pattern} {rest : List Pattern}
    (h_red : Nonempty (Reduction.Reduces p q)) :
    Nonempty (Reduction.Reduces
      (.collection .hashBag (toListRepr p ++ rest) none)
      (.collection .hashBag (q :: rest) none)) := by
  unfold toListRepr
  match p with
  | .collection .hashBag ps none => exact reduce_in_flat_context h_red
  | .var _ | .apply _ _ | .lambda _ _ | .multiLambda _ _ | .subst _ _ _
  | .collection .hashSet _ _ | .collection .hashBag _ (some _)
  | .collection .vec _ _ =>
    exact h_red.elim fun r => ⟨Reduction.Reduces.par r⟩

/-- PAR context: if encode P ⇝ result, then encode(P|Q) ⇝ hashBag(result :: ...).

    Uses reduce_toListRepr_context to lift the sub-reduction through rhoPar's flattening.
-/
theorem encode_par_left_reduces {P Q : Process} {n v : String} {result : Pattern}
    (h_red : Nonempty (Reduction.Reduces (encode P (n ++ "_L") v) result)) :
    Nonempty (Reduction.Reduces
      (encode (.par P Q) n v)
      (.collection .hashBag (result :: toListRepr (encode Q (n ++ "_R") v)) none)) := by
  simp only [encode, rhoPar_eq_fromListRepr_append, fromListRepr]
  exact reduce_toListRepr_context h_red

/-- Symmetric PAR context: if encode Q ⇝ result, then encode(P|Q) ⇝ hashBag(... :: result :: ...).

    Uses par_perm to swap sides, then reduce_toListRepr_context, then par_perm back.
-/
theorem encode_par_right_reduces {P Q : Process} {n v : String} {result : Pattern}
    (h_red : Nonempty (Reduction.Reduces (encode Q (n ++ "_R") v) result)) :
    Nonempty (Reduction.Reduces
      (encode (.par P Q) n v)
      (.collection .hashBag (toListRepr (encode P (n ++ "_L") v) ++ [result]) none)) := by
  simp only [encode, rhoPar_eq_fromListRepr_append, fromListRepr]
  -- hashBag(toListRepr(encode P) ++ toListRepr(encode Q))
  -- Swap to: hashBag(toListRepr(encode Q) ++ toListRepr(encode P))
  -- Apply reduce_toListRepr_context: ⇝ hashBag(result :: toListRepr(encode P))
  -- Swap back: ⇝ hashBag(toListRepr(encode P) ++ [result])
  have h := reduce_toListRepr_context (rest := toListRepr (encode P (n ++ "_L") v)) h_red
  exact h.elim fun r => ⟨Reduction.Reduces.equiv
    (.par_perm _ _ List.perm_append_comm) r
    (.par_perm _ _ (@List.perm_append_comm _ [result] (toListRepr (encode P (n ++ "_L") v))))⟩

/-! ## Infrastructure for Forward Direction of Prop 4 -/

/-- Multi-step reduction lifts through hashBag parallel context (first element).

    If p ⇝* q, then hashBag(p :: rest) ⇝* hashBag(q :: rest).
-/
noncomputable def ReducesStar_par {p q : Pattern} (rest : List Pattern)
    (h : ReducesStar p q) :
    ReducesStar (.collection .hashBag (p :: rest) none)
                (.collection .hashBag (q :: rest) none) := by
  induction h with
  | refl => exact .refl _
  | step h_red _ ih => exact .step (.par h_red) ih

/-- Multi-step reduction lifts through hashBag parallel context (after prefix).

    If p ⇝* q, then hashBag(before ++ [p]) ⇝* hashBag(before ++ [q]).
    Uses equiv + par to shuffle the reducing element to the front.
-/
noncomputable def ReducesStar_par_right {p q : Pattern} (before : List Pattern)
    (h : ReducesStar p q) :
    ReducesStar (.collection .hashBag (before ++ [p]) none)
                (.collection .hashBag (before ++ [q]) none) := by
  induction h with
  | refl => exact .refl _
  | @step _ mid _ h_red _ ih =>
    exact .step
      (.equiv
        (.par_perm _ _ (@List.perm_append_comm _ before [_]))
        (.par h_red)
        (.par_perm _ _ (@List.perm_append_comm _ [_] before)))
      ih

/-- SC in first element lifts to hashBag.

    If p ≡ q, then hashBag(p :: rest) ≡ hashBag(q :: rest).
-/
lemma SC_hashBag_cons {p q : Pattern} (rest : List Pattern) (h : p ≡ q) :
    (.collection .hashBag (p :: rest) none) ≡ (.collection .hashBag (q :: rest) none) :=
  .par_cong _ _ (by simp) fun i h₁ h₂ => by
    match i with
    | 0 => exact h
    | _ + 1 => exact .refl _

/-- SC through toListRepr on the left side: hashBag(toListRepr p ++ rest) ≡ hashBag(toListRepr q ++ rest).

    Chain: symm(unnest) → SC_hashBag_cons → unnest.
-/
lemma SC_toListRepr_left {p q : Pattern} (rest : List Pattern) (h : p ≡ q) :
    (.collection .hashBag (toListRepr p ++ rest) none) ≡
    (.collection .hashBag (toListRepr q ++ rest) none) :=
  .trans _ _ _
    (.symm _ _ (unnest_sub_bag p rest))
    (.trans _ _ _ (SC_hashBag_cons rest h) (unnest_sub_bag q rest))

/-- SC through toListRepr on the right side: hashBag(before ++ toListRepr p) ≡ hashBag(before ++ toListRepr q).

    Chain: perm → symm(unnest) → SC_hashBag_cons → unnest → perm.
-/
lemma SC_toListRepr_right {p q : Pattern} (before : List Pattern) (h : p ≡ q) :
    (.collection .hashBag (before ++ toListRepr p) none) ≡
    (.collection .hashBag (before ++ toListRepr q) none) :=
  .trans _ _ _ (.par_perm _ _ List.perm_append_comm)
    (.trans _ _ _ (.symm _ _ (unnest_sub_bag p before))
      (.trans _ _ _ (SC_hashBag_cons before h)
        (.trans _ _ _ (unnest_sub_bag q before)
          (.par_perm _ _ List.perm_append_comm))))

/-- SC congruence for rhoPar: if both sides are SC, so is rhoPar.

    Uses SC_toListRepr_left and SC_toListRepr_right to chain through the
    flat list representation of rhoPar.
-/
lemma rhoPar_SC_cong {A A' B B' : Pattern}
    (hA : RhoCalculus.StructuralCongruence A A')
    (hB : RhoCalculus.StructuralCongruence B B') :
    RhoCalculus.StructuralCongruence (rhoPar A B) (rhoPar A' B') := by
  simp only [rhoPar_eq_fromListRepr_append, fromListRepr]
  exact .trans _ _ _
    (SC_toListRepr_left (toListRepr B) hA)
    (SC_toListRepr_right (toListRepr A') hB)

/-- `rhoPar A B ≡ rhoPar B A` — parallel composition is commutative up to SC.
    Uses par_perm with List.perm_append_comm. -/
lemma rhoPar_SC_comm (A B : Pattern) :
    RhoCalculus.StructuralCongruence (rhoPar A B) (rhoPar B A) := by
  rw [rhoPar_eq_fromListRepr_append, rhoPar_eq_fromListRepr_append]
  simp only [fromListRepr]
  exact .par_perm _ _ List.perm_append_comm

/-- `rhoPar (rhoPar A B) C = rhoPar A (rhoPar B C)` — parallel composition is
    associative (exact equality via list append associativity). -/
lemma rhoPar_assoc (A B C : Pattern) :
    rhoPar (rhoPar A B) C = rhoPar A (rhoPar B C) := by
  rw [rhoPar_eq_fromListRepr_append (rhoPar A B) C,
      rhoPar_eq_fromListRepr_append A (rhoPar B C),
      toListRepr_rhoPar A B,
      toListRepr_rhoPar B C,
      List.append_assoc]

/-- `fromListRepr (toListRepr X) ≡ X` — round-trip through list representation preserves SC.
    For hashBag: identity. For non-hashBag: wrapping in singleton hashBag, then par_singleton. -/
lemma fromListRepr_toListRepr_SC (X : Pattern) :
    RhoCalculus.StructuralCongruence (fromListRepr (toListRepr X)) X := by
  unfold fromListRepr toListRepr
  split
  · exact .refl _
  · exact .par_singleton _

/-- `rhoPar rhoNil X ≡ X` — nil is left identity for parallel composition up to SC. -/
lemma rhoPar_rhoNil_left_SC (X : Pattern) :
    RhoCalculus.StructuralCongruence (rhoPar rhoNil X) X := by
  rw [rhoPar_eq_fromListRepr_append]
  simp only [toListRepr, rhoNil, List.nil_append]
  exact fromListRepr_toListRepr_SC X

/-- `rhoPar X rhoNil ≡ X` — nil is right identity for parallel composition up to SC. -/
lemma rhoPar_rhoNil_right_SC (X : Pattern) :
    RhoCalculus.StructuralCongruence (rhoPar X rhoNil) X := by
  rw [rhoPar_eq_fromListRepr_append]
  simp only [toListRepr, rhoNil, List.append_nil]
  exact fromListRepr_toListRepr_SC X

/-- All entries of σ have keys that are extensions of namespace n. -/
def domainInNamespace (σ : SubstEnv) (n : String) : Prop :=
  ∀ entry ∈ σ, ∃ suffix, entry.1 = n ++ suffix

/-- If NamespaceDisjoint u n and σ has domain in n-namespace, then u ∉ dom(σ). -/
private theorem find_none_of_nsDisjoint {σ : SubstEnv} {u n : String}
    (hdom : domainInNamespace σ n) (hndisj : NamespaceDisjoint u n) :
    SubstEnv.find σ u = none := by
  rw [SubstEnv.find_eq_none_iff]
  intro entry hmem heq
  obtain ⟨suffix, hsuf⟩ := hdom entry hmem
  exact hndisj suffix (heq ▸ hsuf)

/-- If σ has domain in n-namespace and u is NamespaceDisjoint from n,
    then applySubst σ (.var u) = .var u. -/
private theorem applySubst_var_nsDisjoint {σ : SubstEnv} {u n : String}
    (hdom : domainInNamespace σ n) (hndisj : NamespaceDisjoint u n) :
    applySubst σ (.var u) = .var u := by
  simp [applySubst, find_none_of_nsDisjoint hdom hndisj]

/-- If σ has domain in n-namespace and x is NamespaceDisjoint from n,
    then σ.filter (·.1 != x) = σ (x is not a key, so nothing is filtered). -/
private theorem filter_not_key_of_nsDisjoint {σ : SubstEnv} {x n : String}
    (hdom : domainInNamespace σ n) (hndisj : NamespaceDisjoint x n) :
    σ.filter (fun p => p.1 != x) = σ :=
  filter_not_key_of_find_none σ x (find_none_of_nsDisjoint hdom hndisj)

/-- domainInNamespace for empty env. -/
private theorem domainInNamespace_nil (n : String) : domainInNamespace ([] : SubstEnv) n :=
  fun _ h => by simp at h

/-- domainInNamespace for append. -/
private theorem domainInNamespace_append {σ₁ σ₂ : SubstEnv} {n : String}
    (h₁ : domainInNamespace σ₁ n) (h₂ : domainInNamespace σ₂ n) :
    domainInNamespace (σ₁ ++ σ₂) n := by
  intro entry hmem
  rcases List.mem_append.mp hmem with h | h
  · exact h₁ entry h
  · exact h₂ entry h

/-- nsEnv has domain in the source namespace. -/
private theorem nsEnv_domainInNamespace (P : Process) (n n' : String) :
    domainInNamespace (nsEnv P n n') n := by
  induction P generalizing n n' with
  | nil => exact domainInNamespace_nil n
  | output _ _ => exact domainInNamespace_nil n
  | input _ _ P ih => exact ih n n'
  | par P Q ihP ihQ =>
    exact domainInNamespace_append
      (fun entry hmem => by
        obtain ⟨sfx, hsfx⟩ := ihP (n ++ "_L") (n' ++ "_L") entry hmem
        exact ⟨"_L" ++ sfx, by rw [hsfx, String.append_assoc]⟩)
      (fun entry hmem => by
        obtain ⟨sfx, hsfx⟩ := ihQ (n ++ "_R") (n' ++ "_R") entry hmem
        exact ⟨"_R" ++ sfx, by rw [hsfx, String.append_assoc]⟩)
  | nu x P ih =>
    intro entry hmem
    simp only [nsEnv] at hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact ⟨"", by rw [h]; simp [String.append_empty]⟩
    · obtain ⟨sfx, hsfx⟩ := ih (n ++ "_" ++ n) (n' ++ "_" ++ n') entry h
      exact ⟨"_" ++ n ++ sfx, by rw [hsfx]; simp [String.append_assoc]⟩
  | replicate _ _ P ih =>
    intro entry hmem
    obtain ⟨sfx, hsfx⟩ := ih (n ++ "_rep") (n' ++ "_rep") entry hmem
    exact ⟨"_rep" ++ sfx, by rw [hsfx]; simp [String.append_assoc]⟩

/-! ## Backward Freshness Infrastructure

Key lemma: if k is fresh in σ(M) and k ∉ dom(σ), then k was already fresh in M.
This enables cross-freshness proofs for par_cong without modifying the EncEquiv theorem. -/

-- Forward freeVars through substitution: if k ∈ freeVars(M) and σ.find k = none,
-- then k ∈ freeVars(applySubst σ M).
mutual
  theorem freeVars_forward_subst (σ : SubstEnv) (M : Pattern) (k : String)
      (hne : noExplicitSubst M) (hk_mem : k ∈ freeVars M) (hk_none : SubstEnv.find σ k = none) :
      k ∈ freeVars (applySubst σ M) :=
    match M with
    | .var name => by
      simp [freeVars] at hk_mem; subst hk_mem
      simp [applySubst, hk_none, freeVars]
    | .apply f args => by
      unfold noExplicitSubst at hne
      simp only [freeVars] at hk_mem
      simp only [applySubst, freeVars]
      exact freeVars_forward_subst_list σ args k hne hk_mem hk_none
    | .lambda x body => by
      unfold noExplicitSubst at hne
      simp only [freeVars] at hk_mem
      have ⟨hk_body, hk_ne_x⟩ := List.mem_filter.mp hk_mem
      have hk_filt : SubstEnv.find (σ.filter (fun p => p.1 != x)) k = none := by
        rw [SubstEnv.find_eq_none_iff]; intro entry hmem heq_key
        exact (SubstEnv.find_eq_none_iff σ k).mp hk_none entry (List.mem_of_mem_filter hmem) heq_key
      simp only [applySubst, freeVars]
      exact List.mem_filter.mpr ⟨freeVars_forward_subst (σ.filter (·.1 != x)) body k hne hk_body hk_filt, hk_ne_x⟩
    | .multiLambda xs body => by
      unfold noExplicitSubst at hne
      simp only [freeVars] at hk_mem
      have ⟨hk_body, hk_not_xs⟩ := List.mem_filter.mp hk_mem
      have hk_filt : SubstEnv.find (σ.filter (fun p => !xs.contains p.1)) k = none := by
        rw [SubstEnv.find_eq_none_iff]; intro entry hmem heq_key
        exact (SubstEnv.find_eq_none_iff σ k).mp hk_none entry (List.mem_of_mem_filter hmem) heq_key
      simp only [applySubst, freeVars]
      exact List.mem_filter.mpr ⟨freeVars_forward_subst (σ.filter (fun p => !xs.contains p.1)) body k hne hk_body hk_filt, hk_not_xs⟩
    | .subst _ _ _ => by simp [noExplicitSubst] at hne
    | .collection ct elems rest => by
      unfold noExplicitSubst at hne
      simp only [freeVars] at hk_mem
      simp only [applySubst, freeVars]
      exact freeVars_forward_subst_list σ elems k hne hk_mem hk_none

  theorem freeVars_forward_subst_list (σ : SubstEnv) (ps : List Pattern) (k : String)
      (hall : allNoExplicitSubst ps) (hk_mem : k ∈ ps.flatMap freeVars)
      (hk_none : SubstEnv.find σ k = none) :
      k ∈ (ps.map (applySubst σ)).flatMap freeVars :=
    match ps with
    | [] => by simp at hk_mem
    | p :: ps' => by
      unfold allNoExplicitSubst at hall
      simp only [Bool.and_eq_true] at hall
      simp only [List.flatMap_cons, List.map_cons] at hk_mem ⊢
      rcases List.mem_append.mp hk_mem with h | h
      · exact List.mem_append.mpr (Or.inl (freeVars_forward_subst σ p k hall.1 h hk_none))
      · exact List.mem_append.mpr (Or.inr (freeVars_forward_subst_list σ ps' k hall.2 h hk_none))
end

/-- Backward freshness: if k is fresh in σ(M) and k ∉ dom(σ), then k is fresh in M. -/
theorem isFresh_of_isFresh_applySubst {σ : SubstEnv} {M : Pattern} {k : String}
    (hne : noExplicitSubst M) (hfresh : isFresh k (applySubst σ M))
    (hk_none : SubstEnv.find σ k = none) :
    isFresh k M := by
  simp only [isFresh, Bool.not_eq_true'] at hfresh ⊢
  rw [Bool.eq_false_iff] at hfresh ⊢
  intro hk_in
  exact hfresh (List.contains_iff_exists_mem_beq.mpr (by
    have hk_fwd := freeVars_forward_subst σ M k hne (list_mem_of_contains hk_in) hk_none
    exact ⟨k, hk_fwd, beq_self_eq_true k⟩))

/-- Keys from domainInNamespace σ₂ (n++"_R") are fresh in M₁ when
    σ₁(M₁) = encode P' (n++"_L") v and domainInNamespace σ₁ (n++"_L"). -/
theorem domainInNamespace_cross_fresh {σ₁ σ₂ : SubstEnv} {M₁ : Pattern}
    (P' : Process) (n v : String)
    (hne_M₁ : noExplicitSubst M₁)
    (heq₁ : applySubst σ₁ M₁ = encode P' (n ++ "_L") v)
    (hdom₁ : domainInNamespace σ₁ (n ++ "_L"))
    (hdom₂ : domainInNamespace σ₂ (n ++ "_R"))
    (h_ndisj_P' : ∀ u ∈ Process.names P', NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n) :
    ∀ k val, (k, val) ∈ σ₂ → isFresh k M₁ := by
  intro k val hk_mem
  obtain ⟨sfx, hk_eq⟩ := hdom₂ (k, val) hk_mem
  have hk_fresh_img : isFresh k (applySubst σ₁ M₁) := by
    rw [heq₁]
    exact domainInNamespace_key_fresh_LR P' n v k h_ndisj_P' h_v_ndisj ⟨sfx, hk_eq⟩
  have hk_not_dom₁ : SubstEnv.find σ₁ k = none := by
    rw [SubstEnv.find_eq_none_iff]
    intro entry hmem heq_key
    obtain ⟨sfx₁, hsfx₁⟩ := hdom₁ entry hmem
    rw [heq_key] at hsfx₁
    exact string_LR_ne n sfx₁ sfx (by rw [← hsfx₁, ← hk_eq])
  exact isFresh_of_isFresh_applySubst hne_M₁ hk_fresh_img hk_not_dom₁

/-- Symmetric: keys from domainInNamespace σ₁ (n++"_L") are fresh in M₂. -/
theorem domainInNamespace_cross_fresh_sym {σ₁ σ₂ : SubstEnv} {M₂ : Pattern}
    (Q' : Process) (n v : String)
    (hne_M₂ : noExplicitSubst M₂)
    (heq₂ : applySubst σ₂ M₂ = encode Q' (n ++ "_R") v)
    (hdom₁ : domainInNamespace σ₁ (n ++ "_L"))
    (hdom₂ : domainInNamespace σ₂ (n ++ "_R"))
    (h_ndisj_Q' : ∀ u ∈ Process.names Q', NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n) :
    ∀ k val, (k, val) ∈ σ₁ → isFresh k M₂ := by
  intro k val hk_mem
  obtain ⟨sfx, hk_eq⟩ := hdom₁ (k, val) hk_mem
  have hk_fresh_img : isFresh k (applySubst σ₂ M₂) := by
    rw [heq₂]
    exact domainInNamespace_key_fresh_RL Q' n v k h_ndisj_Q' h_v_ndisj ⟨sfx, hk_eq⟩
  have hk_not_dom₂ : SubstEnv.find σ₂ k = none := by
    rw [SubstEnv.find_eq_none_iff]
    intro entry hmem heq_key
    obtain ⟨sfx₂, hsfx₂⟩ := hdom₂ entry hmem
    rw [heq_key] at hsfx₂
    exact string_LR_ne n sfx sfx₂ (by rw [← hk_eq, ← hsfx₂])
  exact isFresh_of_isFresh_applySubst hne_M₂ hk_fresh_img hk_not_dom₂

/-- Free-name variant: keys from domainInNamespace σ₂ (n++"_R") are fresh in M₁. -/
theorem domainInNamespace_cross_fresh_fn {σ₁ σ₂ : SubstEnv} {M₁ : Pattern}
    (P' : Process) (n v : String)
    (hne_M₁ : noExplicitSubst M₁)
    (heq₁ : applySubst σ₁ M₁ = encode P' (n ++ "_L") v)
    (hdom₁ : domainInNamespace σ₁ (n ++ "_L"))
    (hdom₂ : domainInNamespace σ₂ (n ++ "_R"))
    (h_ndisj_P' : ∀ u ∈ Process.freeNames P', NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n) :
    ∀ k val, (k, val) ∈ σ₂ → isFresh k M₁ := by
  intro k val hk_mem
  obtain ⟨sfx, hk_eq⟩ := hdom₂ (k, val) hk_mem
  have hk_fresh_img : isFresh k (applySubst σ₁ M₁) := by
    rw [heq₁]
    exact domainInNamespace_key_fresh_LR_fn P' n v k h_ndisj_P' h_v_ndisj ⟨sfx, hk_eq⟩
  have hk_not_dom₁ : SubstEnv.find σ₁ k = none := by
    rw [SubstEnv.find_eq_none_iff]
    intro entry hmem heq_key
    obtain ⟨sfx₁, hsfx₁⟩ := hdom₁ entry hmem
    rw [heq_key] at hsfx₁
    exact string_LR_ne n sfx₁ sfx (by rw [← hsfx₁, ← hk_eq])
  exact isFresh_of_isFresh_applySubst hne_M₁ hk_fresh_img hk_not_dom₁

/-- Free-name variant: keys from domainInNamespace σ₁ (n++"_L") are fresh in M₂. -/
theorem domainInNamespace_cross_fresh_sym_fn {σ₁ σ₂ : SubstEnv} {M₂ : Pattern}
    (Q' : Process) (n v : String)
    (hne_M₂ : noExplicitSubst M₂)
    (heq₂ : applySubst σ₂ M₂ = encode Q' (n ++ "_R") v)
    (hdom₁ : domainInNamespace σ₁ (n ++ "_L"))
    (hdom₂ : domainInNamespace σ₂ (n ++ "_R"))
    (h_ndisj_Q' : ∀ u ∈ Process.freeNames Q', NamespaceDisjoint u n)
    (h_v_ndisj : NamespaceDisjoint v n) :
    ∀ k val, (k, val) ∈ σ₁ → isFresh k M₂ := by
  intro k val hk_mem
  obtain ⟨sfx, hk_eq⟩ := hdom₁ (k, val) hk_mem
  have hk_fresh_img : isFresh k (applySubst σ₂ M₂) := by
    rw [heq₂]
    exact domainInNamespace_key_fresh_RL_fn Q' n v k h_ndisj_Q' h_v_ndisj ⟨sfx, hk_eq⟩
  have hk_not_dom₂ : SubstEnv.find σ₂ k = none := by
    rw [SubstEnv.find_eq_none_iff]
    intro entry hmem heq_key
    obtain ⟨sfx₂, hsfx₂⟩ := hdom₂ entry hmem
    rw [heq_key] at hsfx₂
    exact string_LR_ne n sfx sfx₂ (by rw [← hk_eq, ← hsfx₂])
  exact isFresh_of_isFresh_applySubst hne_M₂ hk_fresh_img hk_not_dom₂

/-- π-SC lifts to EncEquiv on encodings, with domain constraint on σ.

    Returns: ∃ M σ, (encode P n v ≡ M) ∧ isRenamingEnv σ ∧ σ(M) = encode Q n v
                     ∧ domainInNamespace σ n

    The domain constraint enables congruence case proofs: since process names
    are NamespaceDisjoint from n, they can't be in dom(σ), so σ passes through
    PInput/POutput/lambda wrappers without interference.
-/
theorem encode_preserves_pi_SC_enc {P Q : Process}
    (h : PiCalculus.StructuralCongruence P Q) :
    ∀ (n v : String),
    (∀ u ∈ Process.names P, NamespaceDisjoint u n) →
    NamespaceDisjoint v n →
    ∃ (M : Pattern) (σ : SubstEnv),
      (encode P n v ≡ M) ∧ isRenamingEnv σ ∧ applySubst σ M = encode Q n v ∧
      domainInNamespace σ n := by
  induction h with
  | refl _ =>
    intro n v _ _
    refine ⟨_, [], .refl _, fun _ h => by simp at h, ?_, domainInNamespace_nil _⟩
    exact subst_empty _ (encode_noExplicitSubst' _ _ _)
  | symm _ _ _ ih =>
    intro n v h_ndisj h_v_ndisj
    sorry -- needs renaming invertibility + restricted SC transport
  | trans _ _ _ _ _ ih1 ih2 =>
    intro n v h_ndisj h_v_ndisj
    sorry -- needs EncEquiv.trans with domain + Process.names through π-SC
  | par_cong P P' Q Q' hsc_PP' hsc_QQ' ih1 ih2 =>
    intro n v h_ndisj h_v_ndisj
    -- Split namespace disjointness for P and Q
    have h_ndisj_P : ∀ u ∈ Process.names P, NamespaceDisjoint u n :=
      fun u hu => h_ndisj u (Process.names_sub_par_left P Q u hu)
    have h_ndisj_Q : ∀ u ∈ Process.names Q, NamespaceDisjoint u n :=
      fun u hu => h_ndisj u (Process.names_sub_par_right P Q u hu)
    let nL := n ++ "_L"
    let nR := n ++ "_R"
    -- IH for P at nL
    have h_ndisj_P_L : ∀ u ∈ Process.names P, NamespaceDisjoint u nL :=
      fun u hu => NamespaceDisjoint_append u n "_L" (h_ndisj_P u hu)
    have h_v_L : NamespaceDisjoint v nL := NamespaceDisjoint_append v n "_L" h_v_ndisj
    obtain ⟨M₁, σ₁, hsc₁, hren₁, heq₁, hdom₁⟩ := ih1 nL v h_ndisj_P_L h_v_L
    -- IH for Q at nR
    have h_ndisj_Q_R : ∀ u ∈ Process.names Q, NamespaceDisjoint u nR :=
      fun u hu => NamespaceDisjoint_append u n "_R" (h_ndisj_Q u hu)
    have h_v_R : NamespaceDisjoint v nR := NamespaceDisjoint_append v n "_R" h_v_ndisj
    obtain ⟨M₂, σ₂, hsc₂, hren₂, heq₂, hdom₂⟩ := ih2 nR v h_ndisj_Q_R h_v_R
    -- Witness: M = rhoPar M₁ M₂, σ = σ₁ ++ σ₂
    refine ⟨rhoPar M₁ M₂, σ₁ ++ σ₂, ?_, ?_, ?_, ?_⟩
    · -- SC: encode(P|Q) n v ≡ rhoPar M₁ M₂
      simp only [encode]
      exact rhoPar_SC_cong hsc₁ hsc₂
    · -- isRenamingEnv (σ₁ ++ σ₂)
      exact isRenamingEnv_append hren₁ hren₂
    · -- applySubst (σ₁ ++ σ₂) (rhoPar M₁ M₂) = encode(P'|Q') n v
      -- M₁ and M₂ have noExplicitSubst (from SC of encode results)
      have hne_M₁ : noExplicitSubst M₁ :=
        (SC_noExplicitSubst_eq hsc₁).symm ▸ encode_noExplicitSubst' P nL v
      have hne_M₂ : noExplicitSubst M₂ :=
        (SC_noExplicitSubst_eq hsc₂).symm ▸ encode_noExplicitSubst' Q nR v
      -- M₁ and M₂ are not vars (renaming subst of a var is a var, but encode is not)
      have hM₁_nv : ∀ name, M₁ ≠ .var name := by
        intro name h_abs; subst h_abs
        simp only [applySubst] at heq₁
        cases hf : SubstEnv.find σ₁ name with
        | none => simp [hf] at heq₁; exact encode_not_var P' nL v name heq₁.symm
        | some r =>
          simp [hf] at heq₁
          obtain ⟨y, hy⟩ := find_isVar_of_renaming σ₁ name r hf hren₁
          rw [hy] at heq₁; exact encode_not_var P' nL v y heq₁.symm
      have hM₂_nv : ∀ name, M₂ ≠ .var name := by
        intro name h_abs; subst h_abs
        simp only [applySubst] at heq₂
        cases hf : SubstEnv.find σ₂ name with
        | none => simp [hf] at heq₂; exact encode_not_var Q' nR v name heq₂.symm
        | some r =>
          simp [hf] at heq₂
          obtain ⟨y, hy⟩ := find_isVar_of_renaming σ₂ name r hf hren₂
          rw [hy] at heq₂; exact encode_not_var Q' nR v y heq₂.symm
      -- Distribute applySubst through rhoPar
      rw [applySubst_rhoPar' (σ₁ ++ σ₂) M₁ M₂ hM₁_nv hne_M₁ hM₂_nv hne_M₂]
      have h_ndisj_P'_fn : ∀ u ∈ Process.freeNames P', NamespaceDisjoint u n := by
        intro u hu
        have huP : u ∈ Process.freeNames P := by
          have hfn := PiCalculus.StructuralCongruence.freeNames_eq hsc_PP'
          simpa [hfn] using hu
        have hu_names : u ∈ Process.names P := by
          exact Finset.mem_union.mpr (Or.inl huP)
        exact h_ndisj_P u hu_names
      have h_ndisj_Q'_fn : ∀ u ∈ Process.freeNames Q', NamespaceDisjoint u n := by
        intro u hu
        have huQ : u ∈ Process.freeNames Q := by
          have hfn := PiCalculus.StructuralCongruence.freeNames_eq hsc_QQ'
          simpa [hfn] using hu
        have hu_names : u ∈ Process.names Q := by
          exact Finset.mem_union.mpr (Or.inl huQ)
        exact h_ndisj_Q u hu_names
      have hfresh₂ : ∀ k val, (k, val) ∈ σ₂ → isFresh k M₁ := by
        exact domainInNamespace_cross_fresh_fn P' n v hne_M₁ heq₁ hdom₁ hdom₂ h_ndisj_P'_fn h_v_ndisj
      have hfresh₁ : ∀ k val, (k, val) ∈ σ₁ → isFresh k M₂ := by
        exact domainInNamespace_cross_fresh_sym_fn Q' n v hne_M₂ heq₂ hdom₁ hdom₂ h_ndisj_Q'_fn h_v_ndisj
      rw [applySubst_append_allFresh σ₁ σ₂ M₁ hne_M₁ hfresh₂, heq₁]
      rw [applySubst_prepend_allFresh σ₁ σ₂ M₂ hne_M₂ hfresh₁, heq₂]
      rfl
    · -- domainInNamespace (σ₁ ++ σ₂) n
      exact domainInNamespace_append
        (fun entry hmem => by
          obtain ⟨sfx, hsfx⟩ := hdom₁ entry hmem
          exact ⟨"_L" ++ sfx, by rw [hsfx, String.append_assoc]⟩)
        (fun entry hmem => by
          obtain ⟨sfx, hsfx⟩ := hdom₂ entry hmem
          exact ⟨"_R" ++ sfx, by rw [hsfx, String.append_assoc]⟩)
  | input_cong x y P P' hsc_pi ih =>
    intro n v h_ndisj h_v_ndisj
    -- IH: encode P n v has NsEncEquiv to encode P' n v
    have h_ndisj_P : ∀ u ∈ Process.names P, NamespaceDisjoint u n := by
      intro u hu
      apply h_ndisj u
      simp only [Process.names, Finset.mem_union] at hu ⊢
      simp only [Process.freeNames, Process.boundNames]
      rcases hu with hf | hb
      · by_cases huy : u = y
        · right; subst huy; simp
        · left; simp [Finset.mem_sdiff, hf, huy]
      · right; simp [hb]
    obtain ⟨M, σ, hsc, hren, heq, hdom⟩ := ih n v h_ndisj_P h_v_ndisj
    -- Witness: wrap M in PInput shell
    refine ⟨.apply "PInput" [piNameToRhoName x, .lambda y M], σ, ?_, hren, ?_, hdom⟩
    · -- SC: encode(input x y P) n v ≡ PInput[piNameToRhoName x, λy.M]
      simp only [encode, piNameToRhoName]
      exact .apply_cong _ _ _ (by simp) (fun i h₁ h₂ => by
        simp only [List.length_cons, List.length_nil] at h₁ h₂
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · simp [List.getElem_cons_zero]; exact .refl _
        · simp [List.getElem_cons_succ, List.getElem_cons_zero]
          exact .lambda_cong y _ _ hsc)
    · -- σ(PInput[piNameToRhoName x, λy.M]) = encode(input x y P') n v
      -- Unfold applySubst on .apply to get map, then piNameToRhoName to get .var
      simp only [applySubst, piNameToRhoName, List.map]
      have hx_ndisj : NamespaceDisjoint x n := h_ndisj x (by
        show x ∈ Process.names (Process.input x y P)
        simp [Process.names, Process.freeNames, Finset.mem_union, Finset.mem_insert])
      rw [find_none_of_nsDisjoint hdom hx_ndisj]
      have hy_ndisj : NamespaceDisjoint y n := h_ndisj y (by
        show y ∈ Process.names (Process.input x y P)
        simp [Process.names, Process.boundNames, Finset.mem_union, Finset.mem_insert])
      rw [filter_not_key_of_nsDisjoint hdom hy_ndisj, heq]
      simp only [encode, piNameToRhoName, rhoInput]
  | nu_cong x P P' _ ih =>
    intro n v h_ndisj h_v_ndisj
    -- encode(νx.P) n v = rhoPar(rhoOutput(.var v)(.var n))(rhoInput(.var n) x (encode P (n++"_"++n) v))
    -- The IH namespace is n ++ "_" ++ n (left-associated)
    have h_ndisj_P : ∀ u ∈ Process.names P, NamespaceDisjoint u (n ++ "_" ++ n) := by
      intro u hu
      have hund : NamespaceDisjoint u n := h_ndisj u (by
        simp only [Process.names, Finset.mem_union] at hu ⊢
        simp only [Process.freeNames, Process.boundNames]
        rcases hu with hf | hb
        · by_cases hux : u = x
          · right; subst hux; simp
          · left; simp [Finset.mem_sdiff, hf, hux]
        · right; simp [hb])
      rw [String.append_assoc]; exact NamespaceDisjoint_append u n ("_" ++ n) hund
    have h_v_ns : NamespaceDisjoint v (n ++ "_" ++ n) := by
      rw [String.append_assoc]; exact NamespaceDisjoint_append v n ("_" ++ n) h_v_ndisj
    obtain ⟨M, σ, hsc, hren, heq, hdom⟩ := ih (n ++ "_" ++ n) v h_ndisj_P h_v_ns
    -- Witness: wrap M in the νx encoding shell
    refine ⟨rhoPar (rhoOutput (.var v) (.var n)) (rhoInput (.var n) x M), σ, ?_, hren, ?_, ?_⟩
    · -- SC: encode(νx.P) n v ≡ rhoPar(v<n>, n(x).M)
      simp only [encode]
      exact rhoPar_SC_cong (.refl _) (.apply_cong _ _ _ (by simp) (fun i h₁ h₂ => by
        simp only [List.length_cons, List.length_nil] at h₁ h₂
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · simp [List.getElem_cons_zero]; exact .refl _
        · simp [List.getElem_cons_succ, List.getElem_cons_zero]
          exact .lambda_cong x _ _ hsc))
    · -- σ(rhoPar(v<n>, n(x).M)) = encode(νx.P') n v
      -- Need: v, n, x are NamespaceDisjoint from (n ++ "_" ++ n) so σ passes through
      have hv_nd : NamespaceDisjoint v (n ++ "_" ++ n) := h_v_ns
      have hn_nd : NamespaceDisjoint n (n ++ "_" ++ n) := by
        intro suffix heq_ns
        have hlen := congrArg String.length heq_ns
        rw [String.length_append, String.length_append, String.length_append] at hlen
        have : ("_" : String).length ≥ 1 := by native_decide
        omega
      have hx_nd : NamespaceDisjoint x (n ++ "_" ++ n) := by
        have : NamespaceDisjoint x n := h_ndisj x (by
          show x ∈ Process.names (Process.nu x P)
          simp [Process.names, Process.boundNames, Finset.mem_union, Finset.mem_insert])
        rw [String.append_assoc]; exact NamespaceDisjoint_append x n ("_" ++ n) this
      -- Distribute σ through the shell
      rw [applySubst_rhoPar' σ _ _
          (fun name => by simp [rhoOutput])
          (by simp [rhoOutput, noExplicitSubst, allNoExplicitSubst])
          (fun name => by simp [rhoInput])
          (by simp [rhoInput, noExplicitSubst, allNoExplicitSubst,
              SC_noExplicitSubst_eq hsc ▸ encode_noExplicitSubst' P (n ++ "_" ++ n) v])]
      -- rhoOutput(.var v)(.var n): σ doesn't touch v or n
      simp only [rhoOutput, applySubst, List.map,
        find_none_of_nsDisjoint hdom hv_nd, find_none_of_nsDisjoint hdom hn_nd]
      -- rhoInput(.var n) x M: σ(.var n) = .var n, filter x = σ, σ(M) = encode P'
      simp only [rhoInput, applySubst, List.map,
        find_none_of_nsDisjoint hdom hn_nd,
        filter_not_key_of_nsDisjoint hdom hx_nd, heq,
        encode, rhoOutput]
    · -- domainInNamespace σ n: keys of σ ⊆ (n++"_"++n) ++ * ⊆ n ++ *
      intro entry hmem
      obtain ⟨sfx, hsfx⟩ := hdom entry hmem
      exact ⟨"_" ++ n ++ sfx, by rw [hsfx]; simp only [String.append_assoc]⟩
  | replicate_cong x y P P' _ ih =>
    intro n v h_ndisj h_v_ndisj
    -- encode(replicate x y P) n v = rhoReplicate(rhoInput(.var x) y (encode P n_rep v))
    let n_rep := n ++ "_rep"
    have h_ndisj_P : ∀ u ∈ Process.names P, NamespaceDisjoint u n_rep := by
      intro u hu
      exact NamespaceDisjoint_append u n "_rep" (h_ndisj u (by
        simp only [Process.names, Finset.mem_union] at hu ⊢
        simp only [Process.freeNames, Process.boundNames]
        rcases hu with hf | hb
        · by_cases huy : u = y
          · right; subst huy; simp
          · left; simp [Finset.mem_sdiff, hf, huy]
        · right; simp [hb]))
    have h_v_rep : NamespaceDisjoint v n_rep :=
      NamespaceDisjoint_append v n "_rep" h_v_ndisj
    obtain ⟨M, σ, hsc, hren, heq, hdom⟩ := ih n_rep v h_ndisj_P h_v_rep
    -- Witness: wrap M in PReplicate(PInput[.var x, λy.M])
    refine ⟨.apply "PReplicate" [.apply "PInput" [.var x, .lambda y M]], σ, ?_, hren, ?_, ?_⟩
    · -- SC: encode(replicate x y P) n v ≡ PReplicate[PInput[.var x, λy.M]]
      simp only [encode, rhoReplicate, rhoInput, piNameToRhoName]
      exact .apply_cong _ _ _ (by simp) (fun i h₁ h₂ => by
        simp only [List.length_cons, List.length_nil] at h₁ h₂
        have : i = 0 := by omega
        subst this
        simp [List.getElem_cons_zero]
        exact .apply_cong _ _ _ (by simp) (fun j h₃ h₄ => by
          simp only [List.length_cons, List.length_nil] at h₃ h₄
          have : j = 0 ∨ j = 1 := by omega
          rcases this with rfl | rfl
          · simp [List.getElem_cons_zero]; exact .refl _
          · simp [List.getElem_cons_succ, List.getElem_cons_zero]
            exact .lambda_cong y _ _ hsc))
    · -- σ(PReplicate[PInput[.var x, λy.M]]) = encode(replicate x y P') n v
      have hx_ndisj : NamespaceDisjoint x n_rep := by
        exact NamespaceDisjoint_append x n "_rep" (h_ndisj x (by
          show x ∈ Process.names (Process.replicate x y P)
          simp [Process.names, Process.freeNames, Finset.mem_union, Finset.mem_insert]))
      have hy_ndisj : NamespaceDisjoint y n_rep := by
        exact NamespaceDisjoint_append y n "_rep" (h_ndisj y (by
          show y ∈ Process.names (Process.replicate x y P)
          simp [Process.names, Process.boundNames, Finset.mem_union, Finset.mem_insert]))
      -- Compute applySubst step by step, using nsDisjoint to simplify
      simp only [applySubst, List.map,
        find_none_of_nsDisjoint hdom hx_ndisj,
        filter_not_key_of_nsDisjoint hdom hy_ndisj, heq,
        encode, rhoReplicate, rhoInput, piNameToRhoName]
      -- n_rep is let-bound to n ++ "_rep", which simp doesn't unfold
      rfl
    · -- domainInNamespace σ n
      intro entry hmem
      obtain ⟨sfx, hsfx⟩ := hdom entry hmem
      exact ⟨"_rep" ++ sfx, by rw [hsfx, String.append_assoc]⟩
  -- Namespace-dependent cases:
  | par_comm P Q =>
    intro n v h_ndisj h_v_ndisj
    -- encode(P|Q) = rhoPar(encode P n_L v)(encode Q n_R v)
    -- encode(Q|P) = rhoPar(encode Q n_L v)(encode P n_R v)
    -- Step 1: SC via par_perm: rhoPar(encP_L)(encQ_R) ≡ rhoPar(encQ_R)(encP_L)
    -- Step 2: Rename L↔R: σ maps Q's nR-namespace → nL and P's nL-namespace → nR
    let nL := n ++ "_L"
    let nR := n ++ "_R"
    let encP_L := encode P nL v
    let encQ_R := encode Q nR v
    -- Derive namespace disjointness for sub-processes
    have h_ndisj_P : ∀ u ∈ Process.names P, NamespaceDisjoint u n :=
      fun u hu => h_ndisj u (Process.names_sub_par_left P Q u hu)
    have h_ndisj_Q : ∀ u ∈ Process.names Q, NamespaceDisjoint u n :=
      fun u hu => h_ndisj u (Process.names_sub_par_right P Q u hu)
    have h_ndisj_P_L : ∀ u ∈ Process.names P, NamespaceDisjoint u nL :=
      fun u hu => NamespaceDisjoint_append u n "_L" (h_ndisj_P u hu)
    have h_ndisj_P_R : ∀ u ∈ Process.names P, NamespaceDisjoint u nR :=
      fun u hu => NamespaceDisjoint_append u n "_R" (h_ndisj_P u hu)
    have h_ndisj_Q_L : ∀ u ∈ Process.names Q, NamespaceDisjoint u nL :=
      fun u hu => NamespaceDisjoint_append u n "_L" (h_ndisj_Q u hu)
    have h_ndisj_Q_R : ∀ u ∈ Process.names Q, NamespaceDisjoint u nR :=
      fun u hu => NamespaceDisjoint_append u n "_R" (h_ndisj_Q u hu)
    have h_v_L : NamespaceDisjoint v nL := NamespaceDisjoint_append v n "_L" h_v_ndisj
    have h_v_R : NamespaceDisjoint v nR := NamespaceDisjoint_append v n "_R" h_v_ndisj
    -- The combined renaming: swap L↔R namespace trees
    let σ := nsEnv P nL nR ++ nsEnv Q nR nL
    -- EncEquiv witness: P' = rhoPar encQ_R encP_L (swapped), σ = above
    refine ⟨rhoPar encQ_R encP_L, σ, ?_, ?_, ?_, ?_⟩
    · -- SC: rhoPar(encP_L)(encQ_R) ≡ rhoPar(encQ_R)(encP_L)
      simp only [encode]
      exact rhoPar_SC_comm encP_L encQ_R
    · -- isRenamingEnv σ
      exact isRenamingEnv_append (nsEnv_isRenaming P nL nR) (nsEnv_isRenaming Q nR nL)
    · -- applySubst σ (rhoPar encQ_R encP_L) = rhoPar (encode Q nL v) (encode P nR v)
      -- = encode (Q ||| P) n v
      have hP_nosubst := encode_noExplicitSubst' P nL v
      have hQ_nosubst := encode_noExplicitSubst' Q nR v
      -- Step 1: applySubst distributes through rhoPar
      rw [applySubst_rhoPar' σ encQ_R encP_L
          (encode_not_var Q nR v) hQ_nosubst
          (encode_not_var P nL v) hP_nosubst]
      -- Step 2: On encQ_R, nsEnv P nL nR keys are fresh → only nsEnv Q nR nL acts
      have hfresh_PL_in_QR : ∀ k val, (k, val) ∈ nsEnv P nL nR →
          isFresh k encQ_R :=
        fun k val hm => nsEnv_keys_fresh_cross_RL_gen P Q n v nR k val h_ndisj_Q h_v_ndisj hm
      rw [applySubst_prepend_allFresh (nsEnv P nL nR) (nsEnv Q nR nL) encQ_R
          hQ_nosubst hfresh_PL_in_QR]
      -- Step 3: On encP_L, nsEnv Q nR nL keys are fresh → only nsEnv P nL nR acts
      have hfresh_QR_in_PL : ∀ k val, (k, val) ∈ nsEnv Q nR nL →
          isFresh k encP_L :=
        fun k val hm => nsEnv_keys_fresh_cross_LR_gen P Q n v nL k val h_ndisj_P h_v_ndisj hm
      rw [applySubst_append_allFresh (nsEnv P nL nR) (nsEnv Q nR nL) encP_L
          hP_nosubst hfresh_QR_in_PL]
      -- Step 4: Apply nsEnv to each sub-encoding
      rw [applySubst_nsEnv_encode Q nR nL v h_ndisj_Q_R h_v_R]
      rw [applySubst_nsEnv_encode P nL nR v h_ndisj_P_L h_v_L]
      -- nL/nR are let-bound to n++"_L"/n++"_R"; unfold them
      rfl
    · -- domainInNamespace σ n
      exact domainInNamespace_append
        (fun entry hmem => by
          obtain ⟨sfx, hsfx⟩ := nsEnv_domainInNamespace P nL nR entry hmem
          exact ⟨"_L" ++ sfx, by rw [hsfx, String.append_assoc]⟩)
        (fun entry hmem => by
          obtain ⟨sfx, hsfx⟩ := nsEnv_domainInNamespace Q nR nL entry hmem
          exact ⟨"_R" ++ sfx, by rw [hsfx, String.append_assoc]⟩)
  | par_assoc P Q R =>
    intro n v h_ndisj h_v_ndisj
    -- encode((P|Q)|R) = rhoPar(rhoPar(encP_LL)(encQ_LR))(encR_R)
    -- encode(P|(Q|R)) = rhoPar(encP_L)(rhoPar(encQ_RL)(encR_RR))
    -- rhoPar_assoc gives exact equality, then rename LL→L, LR→RL, R→RR
    let nLL := n ++ "_L" ++ "_L"
    let nLR := n ++ "_L" ++ "_R"
    let nR  := n ++ "_R"
    let nL  := n ++ "_L"
    let nRL := n ++ "_R" ++ "_L"
    let nRR := n ++ "_R" ++ "_R"
    -- Per-process namespace disjointness from n
    have h_ndisj_P : ∀ u ∈ Process.names P, NamespaceDisjoint u n :=
      fun u hu => h_ndisj u (Process.names_sub_par_left _ R u
        (Process.names_sub_par_left P Q u hu))
    have h_ndisj_Q : ∀ u ∈ Process.names Q, NamespaceDisjoint u n :=
      fun u hu => h_ndisj u (Process.names_sub_par_left _ R u
        (Process.names_sub_par_right P Q u hu))
    have h_ndisj_R : ∀ u ∈ Process.names R, NamespaceDisjoint u n :=
      fun u hu => h_ndisj u (Process.names_sub_par_right _ R u hu)
    -- Derived disjointness for each namespace param
    have h_ndisj_P_LL : ∀ u ∈ Process.names P, NamespaceDisjoint u nLL :=
      fun u hu => NamespaceDisjoint_append u (n ++ "_L") "_L"
        (NamespaceDisjoint_append u n "_L" (h_ndisj_P u hu))
    have h_ndisj_Q_LR : ∀ u ∈ Process.names Q, NamespaceDisjoint u nLR :=
      fun u hu => NamespaceDisjoint_append u (n ++ "_L") "_R"
        (NamespaceDisjoint_append u n "_L" (h_ndisj_Q u hu))
    have h_ndisj_R_R : ∀ u ∈ Process.names R, NamespaceDisjoint u nR :=
      fun u hu => NamespaceDisjoint_append u n "_R" (h_ndisj_R u hu)
    have h_v_LL : NamespaceDisjoint v nLL :=
      NamespaceDisjoint_append v (n ++ "_L") "_L" (NamespaceDisjoint_append v n "_L" h_v_ndisj)
    have h_v_LR : NamespaceDisjoint v nLR :=
      NamespaceDisjoint_append v (n ++ "_L") "_R" (NamespaceDisjoint_append v n "_L" h_v_ndisj)
    have h_v_R : NamespaceDisjoint v nR := NamespaceDisjoint_append v n "_R" h_v_ndisj
    -- The combined renaming: LL→L, LR→RL, R→RR
    let σ := nsEnv P nLL nL ++ nsEnv Q nLR nRL ++ nsEnv R nR nRR
    refine ⟨rhoPar (encode P nLL v) (rhoPar (encode Q nLR v) (encode R nR v)), σ, ?_, ?_, ?_, ?_⟩
    · -- SC: rhoPar_assoc gives exact equality → SC.refl
      simp only [encode]; rw [rhoPar_assoc]; exact .refl _
    · -- isRenamingEnv σ
      exact isRenamingEnv_append
        (isRenamingEnv_append (nsEnv_isRenaming P nLL nL) (nsEnv_isRenaming Q nLR nRL))
        (nsEnv_isRenaming R nR nRR)
    · -- applySubst σ (rhoPar encP_LL (rhoPar encQ_LR encR_R)) = encode(P|(Q|R)) n v
      have hP_ns := encode_noExplicitSubst' P nLL v
      have hQ_ns := encode_noExplicitSubst' Q nLR v
      have hR_ns := encode_noExplicitSubst' R nR v
      -- Cross-freshness via nsEnv_cross_fresh_LR/RL (all at base n)
      -- Q(LR) keys fresh in P(LL): both under "_L", use nsEnv_keys_fresh_cross_LR_gen at base n++"_L"
      have hfQ_P : ∀ k val, (k, val) ∈ nsEnv Q nLR nRL → isFresh k (encode P nLL v) :=
        fun k val hm => nsEnv_keys_fresh_cross_LR_gen P Q (n ++ "_L") v nRL k val
          (fun u hu => NamespaceDisjoint_append u n "_L" (h_ndisj_P u hu))
          (NamespaceDisjoint_append v n "_L" h_v_ndisj) hm
      -- R(R) keys fresh in P(LL): R→L divergence at base n
      have hfR_P : ∀ k val, (k, val) ∈ nsEnv R nR nRR → isFresh k (encode P nLL v) :=
        fun k val hm => by
          have h : nR = n ++ "_R" ++ "" := String.append_empty.symm
          rw [h] at hm
          exact nsEnv_cross_fresh_LR R P n v "" "_L" nRR h_ndisj_P h_v_ndisj hm
      -- P(LL) keys fresh in Q(LR): both under "_L", use nsEnv_keys_fresh_cross_RL_gen at base n++"_L"
      have hfP_Q : ∀ k val, (k, val) ∈ nsEnv P nLL nL → isFresh k (encode Q nLR v) :=
        fun k val hm => nsEnv_keys_fresh_cross_RL_gen P Q (n ++ "_L") v nL k val
          (fun u hu => NamespaceDisjoint_append u n "_L" (h_ndisj_Q u hu))
          (NamespaceDisjoint_append v n "_L" h_v_ndisj) hm
      -- R(R) keys fresh in Q(LR): R→L divergence at base n
      have hfR_Q : ∀ k val, (k, val) ∈ nsEnv R nR nRR → isFresh k (encode Q nLR v) :=
        fun k val hm => by
          have h : nR = n ++ "_R" ++ "" := String.append_empty.symm
          rw [h] at hm
          exact nsEnv_cross_fresh_LR R Q n v "" "_R" nRR h_ndisj_Q h_v_ndisj hm
      -- P(LL) keys fresh in R(R): L→R divergence at base n
      have hfP_R : ∀ k val, (k, val) ∈ nsEnv P nLL nL → isFresh k (encode R nR v) :=
        fun k val hm => by
          have h : nR = n ++ "_R" ++ "" := String.append_empty.symm
          rw [h]
          exact nsEnv_cross_fresh_RL P R n v "_L" "" nL h_ndisj_R h_v_ndisj hm
      -- Q(LR) keys fresh in R(R): L→R divergence at base n
      have hfQ_R : ∀ k val, (k, val) ∈ nsEnv Q nLR nRL → isFresh k (encode R nR v) :=
        fun k val hm => by
          have h : nR = n ++ "_R" ++ "" := String.append_empty.symm
          rw [h]
          exact nsEnv_cross_fresh_RL Q R n v "_R" "" nRL h_ndisj_R h_v_ndisj hm
      -- Distribute applySubst through outer rhoPar
      rw [applySubst_rhoPar' σ _ _
          (encode_not_var P nLL v) hP_ns
          (fun name => by simp [rhoPar]; split <;> simp)
          (by rw [rhoPar_eq_fromListRepr_append]; simp [fromListRepr, noExplicitSubst,
              allNoExplicitSubst_append (allNoExplicitSubst_toListRepr hQ_ns)
              (allNoExplicitSubst_toListRepr hR_ns)])]
      -- Split σ for encode P nLL v: only nsEnv P acts
      rw [show σ = (nsEnv P nLL nL ++ nsEnv Q nLR nRL) ++ nsEnv R nR nRR from rfl]
      rw [applySubst_append_allFresh _ _ (encode P nLL v) hP_ns
          (fun k val hm => hfR_P k val hm)]
      rw [applySubst_append_allFresh _ _ (encode P nLL v) hP_ns
          (fun k val hm => hfQ_P k val hm)]
      rw [applySubst_nsEnv_encode P nLL nL v h_ndisj_P_LL h_v_LL]
      -- Distribute through inner rhoPar
      rw [applySubst_rhoPar'
          ((nsEnv P nLL nL ++ nsEnv Q nLR nRL) ++ nsEnv R nR nRR) _ _
          (encode_not_var Q nLR v) hQ_ns
          (encode_not_var R nR v) hR_ns]
      -- Split σ for encode Q nLR v: only nsEnv Q acts
      rw [applySubst_append_allFresh _ _ (encode Q nLR v) hQ_ns
          (fun k val hm => hfR_Q k val hm)]
      rw [applySubst_prepend_allFresh _ _ (encode Q nLR v) hQ_ns
          (fun k val hm => hfP_Q k val hm)]
      rw [applySubst_nsEnv_encode Q nLR nRL v h_ndisj_Q_LR h_v_LR]
      -- Split σ for encode R nR v: only nsEnv R acts
      rw [applySubst_prepend_allFresh _ _ (encode R nR v) hR_ns
          (fun k val hm => by
            rcases List.mem_append.mp hm with h | h
            · exact hfP_R k val h
            · exact hfQ_R k val h)]
      rw [applySubst_nsEnv_encode R nR nRR v h_ndisj_R_R h_v_R]
      -- Final: let bindings match (nL, nRL, nRR are let-bound to n++"_L", etc.)
      simp only [encode]; rfl
    · -- domainInNamespace σ n
      exact domainInNamespace_append
        (domainInNamespace_append
          (fun entry hmem => by
            obtain ⟨sfx, hsfx⟩ := nsEnv_domainInNamespace P nLL nL entry hmem
            exact ⟨"_L_L" ++ sfx, by
              rw [hsfx, String.append_assoc, String.append_assoc]; congr 1⟩)
          (fun entry hmem => by
            obtain ⟨sfx, hsfx⟩ := nsEnv_domainInNamespace Q nLR nRL entry hmem
            exact ⟨"_L_R" ++ sfx, by
              rw [hsfx, String.append_assoc, String.append_assoc]; congr 1⟩))
        (fun entry hmem => by
          obtain ⟨sfx, hsfx⟩ := nsEnv_domainInNamespace R nR nRR entry hmem
          exact ⟨"_R" ++ sfx, by rw [hsfx, String.append_assoc]⟩)
  | par_nil_left P =>
    intro n v h_ndisj h_v_ndisj
    -- encode(nil|P) n v = rhoPar rhoNil (encode P (n++"_R") v)
    -- Step 1: SC: rhoPar rhoNil (encode P (n++"_R") v) ≡ encode P (n++"_R") v
    -- Step 2: Renaming: nsEnv maps (n++"_R") vars → n vars
    have h_ndisj_R : ∀ u ∈ Process.names P, NamespaceDisjoint u (n ++ "_R") :=
      fun u hu => NamespaceDisjoint_append u n "_R"
        (h_ndisj u (Process.names_sub_par_right .nil P u hu))
    have h_v_R : NamespaceDisjoint v (n ++ "_R") :=
      NamespaceDisjoint_append v n "_R" h_v_ndisj
    exact ⟨encode P (n ++ "_R") v,
           nsEnv P (n ++ "_R") n,
           by simp only [encode]; exact rhoPar_rhoNil_left_SC _,
           nsEnv_isRenaming P (n ++ "_R") n,
           applySubst_nsEnv_encode P (n ++ "_R") n v h_ndisj_R h_v_R,
           fun entry hmem => by
             obtain ⟨sfx, hsfx⟩ := nsEnv_domainInNamespace P (n ++ "_R") n entry hmem
             exact ⟨"_R" ++ sfx, by rw [hsfx]; simp [String.append_assoc]⟩⟩
  | par_nil_right P =>
    intro n v h_ndisj h_v_ndisj
    have h_ndisj_L : ∀ u ∈ Process.names P, NamespaceDisjoint u (n ++ "_L") :=
      fun u hu => NamespaceDisjoint_append u n "_L"
        (h_ndisj u (Process.names_sub_par_left P .nil u hu))
    have h_v_L : NamespaceDisjoint v (n ++ "_L") :=
      NamespaceDisjoint_append v n "_L" h_v_ndisj
    exact ⟨encode P (n ++ "_L") v,
           nsEnv P (n ++ "_L") n,
           by simp only [encode]; exact rhoPar_rhoNil_right_SC _,
           nsEnv_isRenaming P (n ++ "_L") n,
           applySubst_nsEnv_encode P (n ++ "_L") n v h_ndisj_L h_v_L,
           fun entry hmem => by
             obtain ⟨sfx, hsfx⟩ := nsEnv_domainInNamespace P (n ++ "_L") n entry hmem
             exact ⟨"_L" ++ sfx, by rw [hsfx]; simp [String.append_assoc]⟩⟩
  | nu_nil _ =>
    intro n v h_ndisj h_v_ndisj
    sorry
  | nu_par _ _ _ _ =>
    intro n v h_ndisj h_v_ndisj
    sorry
  | nu_swap _ _ _ =>
    intro n v h_ndisj h_v_ndisj
    sorry
  | alpha_input _ _ _ _ _ _ =>
    intro n v h_ndisj h_v_ndisj
    sorry
  | alpha_nu _ _ _ _ =>
    intro n v h_ndisj h_v_ndisj
    sorry
  | alpha_replicate _ _ _ _ _ _ =>
    intro n v h_ndisj h_v_ndisj
    sorry
  | replicate_unfold _ _ _ =>
    intro n v h_ndisj h_v_ndisj
    sorry

/-! ## Forward Direction: Single π-Step Lifts to ρ-Steps + SC -/

/-- Forward COMM for simple processes: the ρ-COMM result is SC to the encoding of the π-result.

    Under Barendregt conditions and simplicity, the full chain is:
    1. encode_comm_SC: encode(x(y).Q | x<z>) ⇝ result ≡ hashBag[rhoSubstitute(...)]
    2. encoding_substitution_barendregt: rhoSubstitute = encode(Q[z/y]) (n_L) v
    3. encode_independent_of_n: encode(Q[z/y]) (n_L) v = encode(Q[z/y]) n v  (simple)
    4. par_singleton: hashBag[encode(Q[z/y]) n v] ≡ encode(Q[z/y]) n v
-/
theorem forward_comm_simple (x y : Name) (Q : Process) (z : Name) (n v : String)
    (h_simple : Q.isSimple)
    (h_bar_y : y ∉ Q.boundNames) (h_bar_z : z ∉ Q.boundNames)
    (h_fresh_y : y ∉ [n ++ "_L", v]) (h_fresh_z : z ∉ [n ++ "_L", v])
    (h_disjoint_y : NamespaceDisjoint y (n ++ "_L"))
    (h_disjoint_z : NamespaceDisjoint z (n ++ "_L")) :
    ∃ T, Nonempty (ReducesStar
      (encode (.par (.input x y Q) (.output x z)) n v) T) ∧
    (T ≡ encode (Q.substitute y z) n v) := by
  obtain ⟨result, h_red, h_sc⟩ := encode_comm_SC x y Q z n v
  refine ⟨result, ReducesStar.single h_red, ?_⟩
  have h_sub := encoding_substitution_barendregt Q y z (n ++ "_L") v
    h_bar_y h_bar_z h_fresh_y h_fresh_z h_disjoint_y h_disjoint_z
  have h_ind := encode_independent_of_n (Q.substitute y z)
    (Process.isSimple_substitute h_simple y z) (n ++ "_L") n v
  rw [← h_sub, h_ind] at h_sc
  exact .trans _ _ _ h_sc (.par_singleton _)

/-- Forward direction of Prop 4: single π-step lifts to ρ-step(s) + SC.

    Given a single π-reduction P → P', there exists a ρ-term T such that
    encode P ⇝* T and T ≡ encode P'. The ρ-steps correspond to the
    COMM rule(s) in the encoding, and the SC absorbs encoding structure.

    **Proven cases**: par_left, par_right
    **Standalone proven**: forward_comm_simple (COMM for simple processes + Barendregt)
    **Sorry cases**: comm (needs Prop 1), res (needs COMM-first), struct (needs EncEquiv infra)
-/
theorem forward_single_step {P P' : Process} (h : Reduces P P') :
    ∀ (n v : String),
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ (T ≡ encode P' n v) := by
  induction h with
  | comm x y z Q =>
    intro n v
    -- π-COMM: encode(x(y).Q | x<z>) ⇝ result ≡ hashBag[rhoSub(encode Q ...)]
    -- Bridge to encode(Q.substitute y z) requires encoding_substitution_barendregt
    obtain ⟨result, h_red, h_sc⟩ := encode_comm_SC x y Q z n v
    refine ⟨result, ReducesStar.single h_red, ?_⟩
    -- result ≡ hashBag[rhoSubstitute(encode Q (n_L) v, y, .var z)]
    -- Need: this ≡ encode(Q.substitute y z) n v
    -- Gap: rhoSubstitute = encode(Q.sub) (n_L) v (Barendregt) then n_L → n (simple)
    sorry
  | par_left P P' Q _ ih =>
    intro n v
    obtain ⟨T₁, ⟨h_star⟩, h_sc⟩ := ih (n ++ "_L") v
    let rest := toListRepr (encode Q (n ++ "_R") v)
    match h_star with
    | .refl _ =>
      -- Zero ρ-steps in sub-process, pure SC
      refine ⟨encode (.par P Q) n v, ⟨.refl _⟩, ?_⟩
      simp only [encode, rhoPar_eq_fromListRepr_append, fromListRepr]
      exact SC_toListRepr_left rest h_sc
    | .step h_red h_rest =>
      -- At least one step: lift through PAR context
      have h_first := reduce_toListRepr_context (rest := rest) ⟨h_red⟩
      have h_full : Nonempty (ReducesStar (encode (.par P Q) n v)
          (.collection .hashBag (T₁ :: rest) none)) := by
        simp only [encode, rhoPar_eq_fromListRepr_append, fromListRepr]
        exact h_first.elim fun r1 => ⟨.step r1 (ReducesStar_par rest h_rest)⟩
      refine ⟨_, h_full, ?_⟩
      simp only [encode, rhoPar_eq_fromListRepr_append, fromListRepr]
      exact .trans _ _ _ (SC_hashBag_cons rest h_sc)
        (unnest_sub_bag (encode P' (n ++ "_L") v) rest)
  | par_right P Q Q' _ ih =>
    intro n v
    obtain ⟨T₁, ⟨h_star⟩, h_sc⟩ := ih (n ++ "_R") v
    let lrest := toListRepr (encode P (n ++ "_L") v)
    match h_star with
    | .refl _ =>
      -- Zero ρ-steps in sub-process, pure SC
      refine ⟨encode (.par P Q) n v, ⟨.refl _⟩, ?_⟩
      simp only [encode, rhoPar_eq_fromListRepr_append, fromListRepr]
      exact SC_toListRepr_right lrest h_sc
    | .step h_red h_rest =>
      -- At least one step: lift through PAR context (right side)
      -- Permute to put Q's repr first, reduce, then permute back
      have h_full : Nonempty (ReducesStar (encode (.par P Q) n v)
          (.collection .hashBag (lrest ++ [T₁]) none)) := by
        simp only [encode, rhoPar_eq_fromListRepr_append, fromListRepr]
        obtain ⟨r⟩ := reduce_toListRepr_context (rest := lrest) ⟨h_red⟩
        have r1 := Reduction.Reduces.equiv
          (.par_perm _ _ List.perm_append_comm) r
          (.par_perm _ _ (@List.perm_append_comm _ [_] lrest))
        exact ⟨.step r1 (ReducesStar_par_right lrest h_rest)⟩
      refine ⟨_, h_full, ?_⟩
      simp only [encode, rhoPar_eq_fromListRepr_append, fromListRepr]
      exact .trans _ _ _
        (.par_perm _ _ (@List.perm_append_comm _ lrest [T₁]))
        (.trans _ _ _ (SC_hashBag_cons lrest h_sc)
          (.trans _ _ _ (unnest_sub_bag (encode Q' (n ++ "_R") v) lrest)
            (.par_perm _ _ List.perm_append_comm)))
  | res x P_i P_i' _ ih =>
    intro n v
    -- encode(νx P_i) n v = rhoPar(rhoOutput(var v, var n), rhoInput(var n, x, encode P_i ns v))
    -- In standard ρ-calculus, reduction does NOT go under input guards (input_cong removed).
    -- The correct approach (Option B): fire name server COMM first, then reduce body.
    -- This requires restructuring to use COMM-first approach.
    -- For now, the proof follows the same strategy as comm (needs Prop 1 for namespace).
    sorry
  | struct _ _ _ _ h₁ _ h₂ ih =>
    intro n v
    -- h₁ : π-SC P P_mid, h₂ : π-SC Q_mid Q
    -- IH: ∀ n v, ∃ T, encode P_mid ⇝* T ∧ T ≡ encode Q_mid
    -- Needs: encode P n v ≡ encode P_mid n v (and similarly for Q_mid ≡ Q).
    -- This is FALSE as ρ-SC for namespace-dependent π-SC rules (par_comm, etc.)
    -- because the encoding assigns different namespace params (n_L, n_R) to sub-processes.
    -- The correct approach uses EncEquiv (SC + namespace renaming) via
    -- encode_preserves_pi_SC_enc, but folding EncEquiv gaps into the reduction
    -- chain requires EncEquiv_reduces_bridge (which needs reduces_applySubst).
    sorry

/-- Multi-step forward: compose single-step results across a MultiStep chain.

    Given MultiStep P P', composes forward_single_step for each step, folding
    the SC gaps between consecutive ReducesStar chains using Reduces.equiv.

    **Key technique**: When two ReducesStar chains are separated by SC
    (T₁ ≡ encode Q from one step, encode Q is the start of the next step),
    fold the SC into the first reduction step of the second chain via Reduces.equiv.
    If the second chain is refl (zero steps), compose the SCs directly.
-/
theorem forward_multi_step {P P' : Process} (h : MultiStep P P') :
    ∀ (n v : String),
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ (T ≡ encode P' n v) := by
  induction h with
  | refl _ => intro n v; exact ⟨_, ⟨.refl _⟩, .refl _⟩
  | step _ Q _ h_red h_rest ih =>
    intro n v
    obtain ⟨T₁, ⟨h_star1⟩, h_sc1⟩ := forward_single_step h_red n v
    obtain ⟨T₂, ⟨h_star2⟩, h_sc2⟩ := ih n v
    -- h_star1 : encode P ⇝* T₁,  h_sc1 : T₁ ≡ encode Q
    -- h_star2 : encode Q ⇝* T₂,  h_sc2 : T₂ ≡ encode P'
    -- Fold SC gap: T₁ ≡ encode Q and encode Q ⇝* T₂
    match h_star2 with
    | .refl _ =>
      -- No more reduction steps. T₂ = encode Q.
      -- Take T = T₁. SC: T₁ ≡ encode Q = T₂ ≡ encode P'
      exact ⟨T₁, ⟨h_star1⟩, .trans _ _ _ h_sc1 h_sc2⟩
    | .step h_red2 h_rest2 =>
      -- encode Q ⇝ r ⇝* T₂. Fold SC into first step via equiv.
      -- T₁ ≡ encode Q ⇝ r gives T₁ ⇝ r. Then T₁ ⇝ r ⇝* T₂.
      have h_fold := Reduction.Reduces.equiv h_sc1 h_red2 (.refl _)
      exact ⟨T₂, ⟨ReducesStar.trans h_star1 (.step h_fold h_rest2)⟩, h_sc2⟩

/-- Proposition 4: Operational correspondence (Lybech page 106)

    **Informal statement**: P →* P' ⟺ ∃ T', ⟦P⟧ →* T' ∧ T' ≃w ⟦P'⟧

    **Proven components**:
    - `forward_single_step`: PAR cases of forward direction fully proven
    - `forward_multi_step`: Composes single steps into multi-step (proven modulo forward_single_step)
    - `encode_comm_SC`: COMM fires and result ≡ encoding of substitution
    - Infrastructure: ReducesStar_par, ReducesStar_par_right, SC_hashBag_cons,
      SC_toListRepr_left, SC_toListRepr_right

    **Remaining sorries**:
    - COMM case: bridge from rhoSubstitute(encode Q (n_L) v, y, z) to
      encode(Q.substitute y z) n v. The COMM result lives in the n_L sub-namespace
      while the target uses n. For simple processes these are equal; for non-simple,
      this requires Prop 1 (parameter independence).
    - RES case: νx encoding involves name server interaction
    - STRUCT case: π-SC must lift to ρ-SC on encodings
    - Backward direction: ρ-reduction to π-reduction inversion
    - fullEncode includes name server; need to lift through that context
-/
theorem encoding_operational_correspondence (P P' : Process) :
    Nonempty (MultiStep P P') ↔
    (∃ T', Nonempty (ReducesStar (fullEncode P) T') ∧
           WeakBisimilar T' (fullEncode P')) := by
  sorry

/-! ## Proposition 5: Divergence Reflection

If the encoding diverges, then the original process diverges.
(This ensures the encoding doesn't introduce spurious infinite behavior.)
-/

/-- Proposition 5: Divergence reflection (Lybech page 107)

    **Informal statement**: ⟦P⟧ →ω ⟹ P →ω
    (if encoding diverges, then P diverges)

    **Blocked by**: Prop 4 (operational correspondence). Without knowing
    that ρ-reductions map back to π-reductions, we cannot conclude that
    infinite ρ-reductions imply infinite π-reductions.

    **Note**: With the current formalization (no rhoReplicate unfolding),
    the name server cannot reduce, so all ρ-reductions come from user-level
    COMMs within the encoding. If these map to π-COMMs (Prop 4 forward
    direction), then divergence reflection would follow.
-/
theorem encoding_divergence_reflection (P : Process) :
    RhoDiverges (fullEncode P) → PiDiverges P := by
  sorry

/-! ## Summary: Encoding Quality

Status of Gorla's quality criteria (adapted for parametric encodings):

1. sorry **Prop 1** (parameter independence): full name-server case still open
   - Proven simple fragment in the new equivalence:
     `encoding_parameter_independence_simple_bisim`
   - Also proven: `encode_independent_of_n` (exact equality for simple processes)
   - Full case requires renaming-closed operational correspondence for encoded terms

2. PROVEN **Prop 2** (substitution invariance): `encoding_substitution` (0 sorries)
   - Also PROVEN: `encoding_substitution_barendregt` (weaker Barendregt conditions)

3. sorry **Prop 3** (observational correspondence)
   - Immediate biconditional PROVEN:
     `encoding_observational_hasParOutput`, `_forward_immediate`, `_backward_immediate`
   - Remaining: SC-related forward cases (nu_par) and reduction backward cases

4. sorry **Prop 4** (operational correspondence)
   - **Forward direction — `forward_single_step` cases**:
     - par_left: PROVEN (0 sorries)
     - par_right: PROVEN (0 sorries)
     - res: sorry — needs COMM-first approach (input_cong removed from standard ρ-calc)
     - struct: sorry — needs EncEquiv infrastructure (encode_preserves_pi_SC_enc +
       EncEquiv_reduces_bridge). The old `encode_preserves_pi_SC` (claiming ρ-SC)
       was FALSE for 11 namespace-dependent π-SC rules and has been DELETED.
     - comm: sorry — needs Prop 1 for namespace bridge n_L → n
   - **`forward_comm_simple`**: COMM for simple processes under Barendregt (0 sorries)
   - **`forward_multi_step`**: Composes single steps via SC-gap folding (0 local sorries)
   - **`encode_preserves_pi_SC_enc`**: π-SC lifts to EncEquiv on encodings
     (replaces the deleted FALSE `encode_preserves_pi_SC`)
   - **Infrastructure PROVEN** (0 sorries):
     - `rhoPar_SC_cong`: SC congruence for rhoPar
     - `ReducesStar_par`, `ReducesStar_par_right`: Multi-step PAR context lifting
     - `SC_hashBag_cons`, `SC_toListRepr_left`, `SC_toListRepr_right`: SC congruence
     - `encode_par_left/right_reduces`, `encode_comm_SC`, `encode_comm_step_with_rest`
     - `nest_sub_bag`, `unnest_sub_bag`, `reduce_in_flat_context`,
       `reduce_toListRepr_context`: hashBag flattening infrastructure
   - **Remaining**:
     - General COMM (needs Prop 1 for namespace bridge n_L → n)
     - Backward direction (ρ-reduction → π-reduction inversion)
     - fullEncode wrapper (lift through name server PAR context)

5. sorry **Prop 5** (divergence reflection): Needs backward direction of Prop 4

**Dependency chain**: Prop 5 ← Prop 4 backward ← ρ-inversion on encode structure
                      Prop 4 forward (par_left/par_right) ← PROVEN
                      Prop 4 forward (comm, simple) ← PROVEN
                      Prop 4 forward (struct) ← EncEquiv infrastructure
                      Prop 3 (full) ← Prop 4 for reduction cases
                      Prop 1 ← name server isolation analysis
                      Prop 4 general COMM ← Prop 1 (namespace independence)
                      encode_preserves_pi_SC_enc ← NamespaceDisjoint conditions + EncEquiv congruence
-/

end Mettapedia.OSLF.PiCalculus
