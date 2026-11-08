import Mettapedia.Logic.ASP.Checker

/-!
# Weight rules, and their normalization by sequential weight counters

## Weight programs

A weight rule is `h :- L ≤ {l₁ = w₁, …, lₙ = wₙ}`: the literals `lᵢ` are atoms or negated
atoms, the weights `wᵢ` and the lower bound `L` are natural numbers, and the body holds when
the true literals weigh at least `L`. The head is an atom, a choice `{h₁; …; hₘ}`, or empty
(a constraint `:- L ≤ {…}`). Cardinality rules are the weight rules whose weights are all `1`.

## Stable models

The semantics is that of Simons, Niemelä and Soininen ("Extending and implementing the stable
model semantics", Artificial Intelligence 138, 2002), for bodies with a lower bound only and
natural weights, where bodies are monotone in their positive literals:

* **The reduct** (`WProgram.reduct`) by a candidate `S` reads every negated literal in `S`: the
  ones whose atom is outside `S` contribute their weight, so the bound drops by that weight
  (truncated at `0`) and the negated literals disappear. An atom head `h` keeps its rule, a
  choice head keeps one rule for each of its atoms that is in `S`, and a constraint keeps no
  rule. The result is a positive weight program (`reduct_isPositive`), whose `leastModel`
  satisfies every rule and is contained in every set that does
  (`IsPositive.models_leastModel`, `IsPositive.leastModel_subset`).
* **A stable model** (`WProgram.Stable`) is a candidate `S` that satisfies every rule
  (`WProgram.Models`: a true body forces an atom head; a constraint's body is false; a choice
  head forces nothing) and is the least model of its reduct by `S`.

Equivalently (`stable_iff`), `S` is the least fixed point of `step · S` and violates no
constraint, where `WProgram.step I N` derives heads with positive literals read in `I` and
negation and choice read against `N`.

The executable checker (`WProgram.isStable`) computes the reduct and its least model; the
enumerator (`WProgram.stableModels`) tries every set of head atoms (`mem_stableModels`).

## Normalization by sequential weight counters

`WProgram.normalize` translates a weight program into a normal program (`Program`) over
`A ⊕ Aux A`: the original atoms, and fresh auxiliary atoms. For the rule at position `r`, with
bound `L` and literals `l₁ = w₁, …, lₙ = wₙ`, the counter atoms `c(r, i, k)` (`Aux.count`)
have the rules

* `c(r, 0, 0).`
* `c(r, i, k) :- c(r, i-1, k).` for `1 ≤ i ≤ n` and `k ≤ L`;
* `c(r, i, min(L, k + wᵢ)) :- c(r, i-1, k), lᵢ.` for `1 ≤ i ≤ n` and `k ≤ L`;

and the head is attached to `c(r, n, L)`:

* an atom head `h`: `h :- c(r, n, L).`
* a choice head: for each of its atoms `h`, `h :- c(r, n, L), not h̄.` and `h̄ :- not h.`, with
  the complement atom `h̄` (`Aux.compl`);
* a constraint: `⊥ :- c(r, n, L), not ⊥.`, with one atom `⊥` (`Aux.falsum`), which no stable
  model contains.

This is the sequential weight counter of Hölldobler, Manthey and Steinke ("A compact encoding
of pseudo-Boolean constraints into SAT", KI 2012), written as normal rules, with the usual
complement-atom translation of choices; Bomanson, Gebser and Janhunen ("Improving the
normalization of weight rules in answer set programs", JELIA 2014) study such normalizations.

In the least model of the normalized program's reduct, `c(r, i, k)` holds exactly when `k` is
the weight, capped at `L`, of some set of true literals among the first `i` (`reach`); so
`c(r, n, L)` holds exactly when the body holds (`bound_mem_reach_iff`).

## The theorem

* `glOp_normalize`: for a negation context in which each complement atom is the negation of
  its atom (`WProgram.Coherent`), the least model of the normalized reduct is computed from the
  least model of the weight reduct (`WProgram.derived`).
* **`stable_normalize_iff`**: `M` is a stable model of the normalized program exactly when its
  original atoms form a stable model `S` of the weight program and `M` is the extension of `S`
  (`WProgram.extend`), which fixes every auxiliary atom.
* **`normalize_correct`**: restricting to the original atoms maps the stable models of the
  normalized program onto the stable models of the weight program, and each stable model of
  the weight program extends to exactly one stable model of the normalized program.

## General facts about normal programs

`Program.ClosedUnder P T N` says that `T` is closed under the rules of `P` with negation read
against `N`. The least model of the reduct by `N` is closed (`Program.closedUnder_glOp`) and is
contained in every closed set (`Program.glOp_subset_of_closedUnder`); closedness splits over
appended and flattened programs.

The reduct of a normal program reads only its negated atoms (`Program.glOp_congr_negAtoms`).
So its stable models are found by guessing those atoms alone: for each set of them, the least
model of the reduct, kept when it contains exactly the guessed ones (`Program.stableModelsNeg`,
`Program.mem_stableModelsNeg`). On a normalized program this guesses the original atoms that
occur negated, the complement atoms and `⊥`, never the counters, which is what makes the
controls' independent check of the normalization cheap.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

universe u

/-! ## Weight programs -/

/-- A literal of a weight body: an atom or a negated atom. -/
inductive WLit (A : Type u)
  | pos (a : A)
  | neg (a : A)
  deriving DecidableEq, Repr

/-- A weighted literal `l = w` of a weight body. -/
structure WTerm (A : Type u) where
  lit : WLit A
  weight : ℕ
  deriving DecidableEq, Repr

/-- The head of a weight rule: one atom, a choice among atoms, or none (a constraint). -/
inductive WHead (A : Type u)
  | atom (a : A)
  | choice (atoms : List A)
  | empty
  deriving DecidableEq, Repr

/-- A weight rule `head :- bound ≤ {l₁ = w₁, …, lₙ = wₙ}`. -/
structure WRule (A : Type u) where
  head : WHead A
  bound : ℕ
  body : List (WTerm A)
  deriving DecidableEq, Repr

/-- A finite weight program. -/
abbrev WProgram (A : Type u) := List (WRule A)

variable {A : Type u}

/-! ## Sets closed under the rules of a normal program -/

namespace Program

/-- `T` is closed under the rules of `P` with negation read against `N`: every rule whose body
holds has its head in `T`. -/
def ClosedUnder (P : Program A) (T N : Set A) : Prop := ∀ r ∈ P, r.Holds T N → r.head ∈ T

variable {T N : Set A}

theorem closedUnder_iff_step_subset {P : Program A} : P.ClosedUnder T N ↔ P.step T N ⊆ T := by
  constructor
  · rintro closed _ ⟨r, hr, rfl, holds⟩
    exact closed r hr holds
  · intro sub r hr holds
    exact sub ⟨r, hr, rfl, holds⟩

/-- The least model of the reduct by `N` is closed. -/
theorem closedUnder_glOp (P : Program A) (N : Set A) : P.ClosedUnder (P.glOp N) N :=
  closedUnder_iff_step_subset.mpr (P.glOp_fixed N).le

/-- The least model of the reduct by `N` is contained in every closed set. -/
theorem glOp_subset_of_closedUnder {P : Program A} (closed : P.ClosedUnder T N) : P.glOp N ⊆ T :=
  OrderHom.lfp_le _ (closedUnder_iff_step_subset.mp closed)

@[simp] theorem closedUnder_nil : ClosedUnder ([] : Program A) T N := fun _ h => absurd h List.not_mem_nil

@[simp] theorem closedUnder_cons {r : Rule A} {P : Program A} :
    ClosedUnder (r :: P) T N ↔ (r.Holds T N → r.head ∈ T) ∧ P.ClosedUnder T N :=
  List.forall_mem_cons

@[simp] theorem closedUnder_append {P Q : Program A} : ClosedUnder (P ++ Q) T N ↔ P.ClosedUnder T N ∧ Q.ClosedUnder T N :=
  List.forall_mem_append

theorem closedUnder_flatten {L : List (Program A)} : ClosedUnder L.flatten T N ↔ ∀ P ∈ L, P.ClosedUnder T N := by
  simp only [ClosedUnder, List.mem_flatten]
  constructor
  · intro h P hP r hr
    exact h r ⟨P, hP, hr⟩
  · rintro h r ⟨P, hP, hr⟩
    exact h P hP r hr

theorem closedUnder_flatMap {α : Type*} {f : α → Program A} {l : List α} :
    ClosedUnder (l.flatMap f) T N ↔ ∀ x ∈ l, (f x).ClosedUnder T N := by
  rw [List.flatMap, closedUnder_flatten]
  simp

theorem closedUnder_flatten_mapIdx {α : Type*} {f : ℕ → α → Program A} {l : List α} :
    ClosedUnder (l.mapIdx f).flatten T N ↔ ∀ i x, l[i]? = some x → (f i x).ClosedUnder T N := by
  rw [closedUnder_flatten]
  constructor
  · intro h i x hx
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hx
    exact h _ (List.mem_mapIdx.mpr ⟨i, hi, rfl⟩)
  · intro h P hP
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hP
    exact h i _ (List.getElem?_eq_getElem hi)

end Program

/-! ## Literals and weights -/

namespace WLit

/-- The literal holds: a positive atom is in `I`, a negated atom is not in `N`. -/
def Holds : WLit A → Set A → Set A → Prop
  | pos a, I, _ => a ∈ I
  | neg a, _, N => a ∉ N

theorem Holds.mono_left {l : WLit A} {I I' N : Set A} (h : l.Holds I N) (hI : I ⊆ I') : l.Holds I' N := by
  cases l with
  | pos a => exact hI h
  | neg a => exact h

/-- Positive literals. -/
def isPos : WLit A → Bool
  | pos _ => true
  | neg _ => false

end WLit

section Weight

namespace WTerm

open Classical in
/-- What the weighted literal contributes: its weight when the literal holds, else `0`. -/
noncomputable def value (t : WTerm A) (I N : Set A) : ℕ := if t.lit.Holds I N then t.weight else 0

variable {t : WTerm A} {I N : Set A}

theorem value_of_holds (h : t.lit.Holds I N) : t.value I N = t.weight := by
  classical
  exact if_pos h

theorem value_of_not_holds (h : ¬ t.lit.Holds I N) : t.value I N = 0 := by
  classical
  exact if_neg h

theorem value_mono_left {I' : Set A} (hI : I ⊆ I') : t.value I N ≤ t.value I' N := by
  by_cases h : t.lit.Holds I N
  · rw [value_of_holds h, value_of_holds (h.mono_left hI)]
  · rw [value_of_not_holds h]
    exact Nat.zero_le _

end WTerm

/-- The weight of the true literals of `ts`, positive literals read in `I` and negated ones
against `N`. -/
noncomputable def weightIn (ts : List (WTerm A)) (I N : Set A) : ℕ := (ts.map (·.value I N)).sum

@[simp] theorem weightIn_nil (I N : Set A) : weightIn [] I N = 0 := rfl

theorem weightIn_cons (t : WTerm A) (ts : List (WTerm A)) (I N : Set A) :
    weightIn (t :: ts) I N = t.value I N + weightIn ts I N := by
  simp [weightIn]

theorem weightIn_append (xs ys : List (WTerm A)) (I N : Set A) :
    weightIn (xs ++ ys) I N = weightIn xs I N + weightIn ys I N := by
  simp [weightIn]

theorem weightIn_mono_left (ts : List (WTerm A)) {I I' : Set A} (N : Set A) (h : I ⊆ I') :
    weightIn ts I N ≤ weightIn ts I' N := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih =>
    rw [weightIn_cons, weightIn_cons]
    have := t.value_mono_left (N := N) h
    omega

theorem weightIn_take_succ {ts : List (WTerm A)} {i : ℕ} {t : WTerm A} (h : ts[i]? = some t) (I N : Set A) :
    weightIn (ts.take (i + 1)) I N = weightIn (ts.take i) I N + t.value I N := by
  rw [List.take_add_one, h, Option.toList_some, weightIn_append, weightIn_cons, weightIn_nil, add_zero]

end Weight

/-- **The counter's values**: `reach L ts I N i` holds the weights, capped at `L`, of the sets
of true literals among the first `i` of `ts`. The counter atom `c(r, i, k)` of the
normalization holds exactly for these `k`. -/
def reach (L : ℕ) (ts : List (WTerm A)) (I N : Set A) : ℕ → Set ℕ
  | 0 => {0}
  | i + 1 => {k | ∃ t ∈ ts[i]?, k ∈ reach L ts I N i ∨
      ∃ k' ∈ reach L ts I N i, t.lit.Holds I N ∧ k = min L (k' + t.weight)}

section Reach

variable {L : ℕ} {ts : List (WTerm A)} {I N : Set A}

theorem reach_le_bound : ∀ {i k : ℕ}, k ∈ reach L ts I N i → k ≤ L
  | 0, k, h => by
    rw [Set.mem_singleton_iff.mp h]
    exact Nat.zero_le _
  | _ + 1, _, ⟨_, _, h⟩ => by
    rcases h with h | ⟨_, _, _, rfl⟩
    · exact reach_le_bound h
    · exact min_le_left _ _

theorem reach_le_weight : ∀ {i k : ℕ}, k ∈ reach L ts I N i → k ≤ weightIn (ts.take i) I N
  | 0, k, h => by
    rw [Set.mem_singleton_iff.mp h]
    exact Nat.zero_le _
  | i + 1, k, ⟨t, ht, h⟩ => by
    classical
    rw [weightIn_take_succ (Option.mem_def.mp ht)]
    rcases h with h | ⟨k', hk', holds, rfl⟩
    · have := reach_le_weight h
      omega
    · have := reach_le_weight hk'
      rw [WTerm.value_of_holds holds]
      omega

theorem min_mem_reach : ∀ {i : ℕ}, i ≤ ts.length → min L (weightIn (ts.take i) I N) ∈ reach L ts I N i
  | 0, _ => by simp [reach]
  | i + 1, h => by
    classical
    obtain ⟨t, ht⟩ : ∃ t, ts[i]? = some t := ⟨ts[i], List.getElem?_eq_getElem (by omega)⟩
    have ih := min_mem_reach (i := i) (by omega)
    refine ⟨t, Option.mem_def.mpr ht, ?_⟩
    rw [weightIn_take_succ ht]
    by_cases holds : t.lit.Holds I N
    · right
      refine ⟨_, ih, holds, ?_⟩
      rw [WTerm.value_of_holds holds]
      omega
    · left
      rw [WTerm.value_of_not_holds holds, add_zero]
      exact ih

/-- The final counter holds the bound exactly when the true literals weigh at least the bound. -/
theorem bound_mem_reach_iff : L ∈ reach L ts I N ts.length ↔ L ≤ weightIn ts I N := by
  constructor
  · intro h
    have := reach_le_weight h
    rwa [List.take_length] at this
  · intro h
    have := min_mem_reach (L := L) (I := I) (N := N) (le_refl ts.length)
    rwa [List.take_length, min_eq_left h] at this

end Reach

/-! ## Heads and rules -/

namespace WHead

/-- The atoms the head can derive. -/
def atoms : WHead A → List A
  | atom a => [a]
  | choice hs => hs
  | empty => []

/-- The atoms of a choice head. -/
def choices : WHead A → List A
  | choice hs => hs
  | _ => []

/-- When the body holds, the head derives `a`: its atom, or one of its choice atoms that is
in `N`. -/
def Offers : WHead A → Set A → A → Prop
  | atom h, _, a => h = a
  | choice hs, N, a => a ∈ hs ∧ a ∈ N
  | empty, _, _ => False

/-- `S` satisfies the head: it contains the atom of an atom head; every `S` satisfies a choice
head, and none the empty head. -/
def Holds : WHead A → Set A → Prop
  | atom h, S => h ∈ S
  | choice _, _ => True
  | empty, _ => False

/-- The atoms the head derives, choice read against `N`, computed. -/
def offered (N : Set A) [DecidablePred (· ∈ N)] : WHead A → List A
  | atom h => [h]
  | choice hs => hs.filter fun a => decide (a ∈ N)
  | empty => []

theorem mem_offered {h : WHead A} {N : Set A} [DecidablePred (· ∈ N)] {a : A} :
    a ∈ h.offered N ↔ h.Offers N a := by
  cases h <;> simp [offered, Offers, eq_comm]

theorem Offers.mem_atoms {h : WHead A} {N : Set A} {a : A} (offers : h.Offers N a) : a ∈ h.atoms := by
  cases h with
  | atom b => exact List.mem_singleton.mpr offers.symm
  | choice hs => exact offers.1
  | empty => exact offers.elim

theorem exists_of_mem_choices {h : WHead A} {a : A} (ha : a ∈ h.choices) :
    ∃ hs, h = choice hs ∧ a ∈ hs := by
  cases h with
  | atom b => exact absurd ha List.not_mem_nil
  | choice hs => exact ⟨hs, rfl, ha⟩
  | empty => exact absurd ha List.not_mem_nil

end WHead

/-- The body holds: the literals true in `(I, N)` weigh at least the bound. -/
def WRule.BodyHolds (ρ : WRule A) (I N : Set A) : Prop := ρ.bound ≤ weightIn ρ.body I N

/-! ## Stable models of weight programs -/

namespace WProgram

variable (W : WProgram A)

/-- The immediate-consequence operator: positive literals read in `I`, negated literals and
choice heads against `N`. -/
def step (I N : Set A) : Set A := {a | ∃ ρ ∈ W, ρ.head.Offers N a ∧ ρ.BodyHolds I N}

theorem step_mono {I I' : Set A} (N : Set A) (h : I ⊆ I') : W.step I N ⊆ W.step I' N :=
  fun _ ⟨ρ, hρ, offers, body⟩ => ⟨ρ, hρ, offers, body.trans (weightIn_mono_left _ N h)⟩

/-- The operator whose least fixed point is the least model of the reduct by `N`. -/
def reductOp (N : Set A) : Set A →o Set A where
  toFun I := W.step I N
  monotone' _ _ h := W.step_mono N h

/-- `N ↦ lfp (step · N)`. -/
def glOp (N : Set A) : Set A := (W.reductOp N).lfp

theorem glOp_fixed (N : Set A) : W.step (W.glOp N) N = W.glOp N := (W.reductOp N).map_lfp

/-- The least model, the meaning of a positive weight program. -/
def leastModel : Set A := W.glOp ∅

/-- The atoms some head can derive. -/
def headSet : Set A := {a | ∃ ρ ∈ W, a ∈ ρ.head.atoms}

theorem step_subset_headSet (I N : Set A) : W.step I N ⊆ W.headSet :=
  fun _ ⟨ρ, hρ, offers, _⟩ => ⟨ρ, hρ, offers.mem_atoms⟩

theorem glOp_subset_headSet (N : Set A) : W.glOp N ⊆ W.headSet :=
  OrderHom.lfp_le _ (W.step_subset_headSet _ _)

/-- `S` satisfies every rule: a true body forces an atom head, and no constraint has a true
body. -/
def Models (S : Set A) : Prop := ∀ ρ ∈ W, ρ.BodyHolds S S → ρ.head.Holds S

/-- A positive weight program: atom heads and positive literals only. -/
def IsPositive : Prop := ∀ ρ ∈ W, (∃ a, ρ.head = .atom a) ∧ ∀ t ∈ ρ.body, t.lit.isPos = true

end WProgram

/-! ### The reduct -/

/-- The positive literals of a body. -/
def posTerms (ts : List (WTerm A)) : List (WTerm A) := ts.filter fun t => t.lit.isPos

/-- The weight of the negated literals of `ts` whose atom is outside `S`. -/
def negWeight (S : Set A) [DecidablePred (· ∈ S)] (ts : List (WTerm A)) : ℕ :=
  (ts.map fun t => match t.lit with
    | .pos _ => 0
    | .neg b => if b ∈ S then 0 else t.weight).sum

/-- Read against `S`, the true literals weigh the true positive literals plus the negated
literals whose atom is outside `S`. -/
theorem weightIn_eq_posTerms_add_negWeight (ts : List (WTerm A)) (I S : Set A) [DecidablePred (· ∈ S)]
    (N : Set A) : weightIn ts I S = weightIn (posTerms ts) I N + negWeight S ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨l, w⟩ := t
    cases l with
    | pos a =>
      have hp : posTerms (⟨.pos a, w⟩ :: ts) = ⟨.pos a, w⟩ :: posTerms ts := by
        simp [posTerms, WLit.isPos]
      have hn : negWeight S (⟨.pos a, w⟩ :: ts) = negWeight S ts := by
        simp [negWeight]
      have hv : (⟨.pos a, w⟩ : WTerm A).value I S = (⟨.pos a, w⟩ : WTerm A).value I N := rfl
      rw [hp, hn, weightIn_cons, weightIn_cons, ih, hv]
      omega
    | neg b =>
      have hp : posTerms (⟨.neg b, w⟩ :: ts) = posTerms ts := by
        simp [posTerms, WLit.isPos]
      have hn : negWeight S (⟨.neg b, w⟩ :: ts) = (if b ∈ S then 0 else w) + negWeight S ts := by
        simp [negWeight]
      rw [hp, hn, weightIn_cons, ih]
      by_cases hb : b ∈ S
      · rw [WTerm.value_of_not_holds (t := ⟨.neg b, w⟩) (I := I) (N := S) (fun h => h hb), if_pos hb]
        omega
      · rw [WTerm.value_of_holds (t := ⟨.neg b, w⟩) (I := I) (N := S) hb, if_neg hb]
        dsimp only
        omega

namespace WRule

/-- The reduct of the body of `ρ` by `S`, under the head `h`:
`h :- (L - w) ≤ {positive literals}`, where `w` is the weight of the negated literals whose
atom is outside `S`. -/
def reductAt (S : Set A) [DecidablePred (· ∈ S)] (ρ : WRule A) (h : A) : WRule A :=
  ⟨.atom h, ρ.bound - negWeight S ρ.body, posTerms ρ.body⟩

/-- **The reduct of a weight rule** by `S`: one positive rule for an atom head, one for each
choice atom in `S`, none for a constraint. -/
def reduct (S : Set A) [DecidablePred (· ∈ S)] (ρ : WRule A) : WProgram A :=
  (ρ.head.offered S).map (ρ.reductAt S)

end WRule

namespace WProgram

variable (W : WProgram A)

/-- **The reduct of a weight program** by `S`. -/
def reduct (S : Set A) [DecidablePred (· ∈ S)] : WProgram A := W.flatMap (WRule.reduct S)

theorem reduct_isPositive (S : Set A) [DecidablePred (· ∈ S)] : (W.reduct S).IsPositive := by
  intro ρ' hρ'
  obtain ⟨ρ, -, hρ'⟩ := List.mem_flatMap.mp hρ'
  obtain ⟨h, -, rfl⟩ := List.mem_map.mp hρ'
  exact ⟨⟨h, rfl⟩, fun t ht => (List.mem_filter.mp ht).2⟩

theorem weightIn_of_isPos {ts : List (WTerm A)} (pos : ∀ t ∈ ts, t.lit.isPos = true) (I N N' : Set A) :
    weightIn ts I N = weightIn ts I N' := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [weightIn_cons, weightIn_cons, ih fun t' ht' => pos t' (List.mem_cons_of_mem _ ht')]
    obtain ⟨l, w⟩ := t
    cases l with
    | pos a => rfl
    | neg a => exact absurd (pos _ List.mem_cons_self) (by simp [WLit.isPos])

variable {W} in
/-- The operator of a positive program ignores the negation context. -/
theorem IsPositive.step_eq (pos : W.IsPositive) (I N N' : Set A) : W.step I N = W.step I N' := by
  have key : ∀ N N' : Set A, W.step I N ⊆ W.step I N' := by
    rintro N N' a ⟨ρ, hρ, offers, body⟩
    obtain ⟨⟨h, hh⟩, lits⟩ := pos ρ hρ
    refine ⟨ρ, hρ, ?_, ?_⟩
    · rw [hh] at offers ⊢
      exact offers
    · unfold WRule.BodyHolds at body ⊢
      rwa [weightIn_of_isPos lits I N' N]
  exact Set.Subset.antisymm (key N N') (key N' N)

variable {W} in
/-- **The least model of a positive program** satisfies every rule. -/
theorem IsPositive.models_leastModel (pos : W.IsPositive) : W.Models W.leastModel := by
  intro ρ hρ body
  obtain ⟨⟨h, hh⟩, -⟩ := pos ρ hρ
  rw [hh]
  show h ∈ W.leastModel
  have fixed : W.step W.leastModel ∅ = W.leastModel := W.glOp_fixed ∅
  have : h ∈ W.step W.leastModel W.leastModel := ⟨ρ, hρ, by rw [hh]; rfl, body⟩
  rwa [pos.step_eq W.leastModel W.leastModel ∅, fixed] at this

variable {W} in
/-- **The least model of a positive program** is contained in every set satisfying every rule. -/
theorem IsPositive.leastModel_subset (pos : W.IsPositive) {T : Set A} (models : W.Models T) :
    W.leastModel ⊆ T := by
  unfold leastModel glOp
  apply OrderHom.lfp_le
  rintro a ⟨ρ, hρ, offers, body⟩
  obtain ⟨⟨h, hh⟩, lits⟩ := pos ρ hρ
  rw [hh] at offers
  have same : h = a := offers
  subst same
  have body' : ρ.BodyHolds T T := by
    unfold WRule.BodyHolds at body ⊢
    rwa [weightIn_of_isPos lits T T ∅]
  have := models ρ hρ body'
  rw [hh] at this
  exact this

/-- The reduct's operator reads negation and choice against `S`, whatever it is given. -/
theorem step_reduct (S : Set A) [DecidablePred (· ∈ S)] (I N : Set A) :
    (W.reduct S).step I N = W.step I S := by
  ext a
  simp only [step, reduct, List.mem_flatMap, WRule.reduct, List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨ρ, hρ, h, hh, rfl⟩, offers, body⟩
    have same : h = a := offers
    subst same
    refine ⟨ρ, hρ, WHead.mem_offered.mp hh, ?_⟩
    have := weightIn_eq_posTerms_add_negWeight ρ.body I S N
    change ρ.bound - negWeight S ρ.body ≤ weightIn (posTerms ρ.body) I N at body
    unfold WRule.BodyHolds
    omega
  · rintro ⟨ρ, hρ, offers, body⟩
    refine ⟨_, ⟨ρ, hρ, a, WHead.mem_offered.mpr offers, rfl⟩, rfl, ?_⟩
    have := weightIn_eq_posTerms_add_negWeight ρ.body I S N
    change ρ.bound - negWeight S ρ.body ≤ weightIn (posTerms ρ.body) I N
    unfold WRule.BodyHolds at body
    omega

/-- The least model of the reduct by `S` is the least fixed point of `step · S`. -/
theorem leastModel_reduct (S : Set A) [DecidablePred (· ∈ S)] : (W.reduct S).leastModel = W.glOp S := by
  unfold leastModel glOp
  congr 1
  apply OrderHom.ext
  funext I
  exact W.step_reduct S I ∅

open Classical in
/-- **Stable model** (Simons–Niemelä–Soininen): `S` satisfies every rule and is the least model
of its reduct by `S`. -/
def Stable (S : Set A) : Prop := W.Models S ∧ S = (W.reduct S).leastModel

theorem stable_iff_glOp (S : Set A) : W.Stable S ↔ W.Models S ∧ S = W.glOp S := by
  unfold Stable
  rw [leastModel_reduct]

/-- **Stability without the reduct**: `S` is the least fixed point of `step · S` and violates no
constraint. -/
theorem stable_iff (S : Set A) :
    W.Stable S ↔ S = W.glOp S ∧ ∀ ρ ∈ W, ρ.head = .empty → ¬ ρ.BodyHolds S S := by
  rw [stable_iff_glOp]
  constructor
  · rintro ⟨models, fixed⟩
    refine ⟨fixed, fun ρ hρ hh body => ?_⟩
    have := models ρ hρ body
    rw [hh] at this
    exact this
  · rintro ⟨fixed, constraints⟩
    refine ⟨fun ρ hρ body => ?_, fixed⟩
    cases hh : ρ.head with
    | atom h =>
      show h ∈ S
      have closed : W.step S S = S := by
        have := W.glOp_fixed S
        rwa [← fixed] at this
      have : h ∈ W.step S S := ⟨ρ, hρ, by rw [hh]; rfl, body⟩
      rwa [closed] at this
    | choice hs => trivial
    | empty => exact constraints ρ hρ hh body

variable {W} in
theorem Stable.subset_headSet {S : Set A} (h : W.Stable S) : S ⊆ W.headSet :=
  ((W.stable_iff S).mp h).1 ▸ W.glOp_subset_headSet S

end WProgram

/-! ## The normalization -/

/-- The auxiliary atoms of the normalization. -/
inductive Aux (A : Type u)
  /-- The counter atom `c(r, i, k)`: some set of true literals among the first `i` of rule `r`
  weighs `k`, capped at the rule's bound. -/
  | count (r i k : ℕ)
  /-- The complement of a choice atom: it holds when the atom does not. -/
  | compl (a : A)
  /-- The atom no stable model contains, which turns a constraint into a rule. -/
  | falsum
  deriving DecidableEq, Repr

namespace WRule

/-- The counter atom `c(r, i, k)`. -/
abbrev counter (r i k : ℕ) : A ⊕ Aux A := .inr (.count r i k)

/-- `h :- c, l`: the rule from the counter atom `c` and the literal `l`. -/
def litRule (h c : A ⊕ Aux A) : WLit A → Rule (A ⊕ Aux A)
  | .pos a => ⟨h, [c, .inl a], []⟩
  | .neg a => ⟨h, [c], [.inl a]⟩

/-- The counter rules for the literal `t` in position `i` (from `0`) of rule `r` with bound `L`:
for each `k ≤ L`, `c(r, i+1, k) :- c(r, i, k).` and `c(r, i+1, min(L, k+w)) :- c(r, i, k), l.` -/
def counterRules (r L i : ℕ) (t : WTerm A) : Program (A ⊕ Aux A) :=
  (List.range (L + 1)).flatMap fun k =>
    [⟨counter r (i + 1) k, [counter r i k], []⟩,
      litRule (counter r (i + 1) (min L (k + t.weight))) (counter r i k) t.lit]

/-- The rules of a head, attached to the final counter atom `c`. -/
def headRules (c : A ⊕ Aux A) : WHead A → Program (A ⊕ Aux A)
  | .atom h => [⟨.inl h, [c], []⟩]
  | .choice hs => hs.flatMap fun h => [⟨.inl h, [c], [.inr (.compl h)]⟩, ⟨.inr (.compl h), [], [.inl h]⟩]
  | .empty => [⟨.inr .falsum, [c], [.inr .falsum]⟩]

/-- **The sequential weight counter** of the rule `ρ` at position `r`. -/
def normalize (r : ℕ) (ρ : WRule A) : Program (A ⊕ Aux A) :=
  ⟨counter r 0 0, [], []⟩ ::
    ((ρ.body.mapIdx (counterRules r ρ.bound)).flatten ++ headRules (counter r ρ.body.length ρ.bound) ρ.head)

theorem litRule_head (h c : A ⊕ Aux A) (l : WLit A) : (litRule h c l).head = h := by
  cases l <;> rfl

theorem litRule_holds (h c : A ⊕ Aux A) (l : WLit A) (T N : Set (A ⊕ Aux A)) :
    (litRule h c l).Holds T N ↔ c ∈ T ∧ l.Holds (Sum.inl ⁻¹' T) (Sum.inl ⁻¹' N) := by
  cases l <;> simp [litRule, Rule.Holds, WLit.Holds]

theorem closedUnder_counterRules (r L i : ℕ) (t : WTerm A) (T N : Set (A ⊕ Aux A)) :
    (counterRules r L i t).ClosedUnder T N ↔ ∀ k ≤ L, counter r i k ∈ T →
      counter r (i + 1) k ∈ T ∧
        (t.lit.Holds (Sum.inl ⁻¹' T) (Sum.inl ⁻¹' N) → counter r (i + 1) (min L (k + t.weight)) ∈ T) := by
  simp only [counterRules, Program.closedUnder_flatMap, List.mem_range, Program.closedUnder_cons, Program.closedUnder_nil,
    and_true, litRule_holds, litRule_head, Nat.lt_succ_iff, and_imp]
  constructor
  · intro h k hk c
    exact ⟨(h k hk).1 (by simpa [Rule.Holds] using c), (h k hk).2 c⟩
  · intro h k hk
    exact ⟨fun c => (h k hk (by simpa [Rule.Holds] using c)).1, fun c => (h k hk c).2⟩

theorem closedUnder_headRules_atom (c : A ⊕ Aux A) (h : A) (T N : Set (A ⊕ Aux A)) :
    (headRules c (.atom h)).ClosedUnder T N ↔ (c ∈ T → .inl h ∈ T) := by
  simp [headRules, Rule.Holds]

theorem closedUnder_headRules_choice (c : A ⊕ Aux A) (hs : List A) (T N : Set (A ⊕ Aux A)) :
    (headRules c (.choice hs)).ClosedUnder T N ↔
      ∀ h ∈ hs, (c ∈ T → Sum.inr (Aux.compl h) ∉ N → Sum.inl h ∈ T) ∧
        (Sum.inl h ∉ N → Sum.inr (Aux.compl h) ∈ T) := by
  simp [headRules, Program.closedUnder_flatMap, Rule.Holds]

theorem closedUnder_headRules_empty (c : A ⊕ Aux A) (T N : Set (A ⊕ Aux A)) :
    (headRules c (.empty : WHead A)).ClosedUnder T N ↔
      (c ∈ T → Sum.inr (Aux.falsum : Aux A) ∉ N → Sum.inr Aux.falsum ∈ T) := by
  simp [headRules, Rule.Holds]

theorem closedUnder_normalize_iff (ρ : WRule A) (r : ℕ) (T N : Set (A ⊕ Aux A)) :
    (ρ.normalize r).ClosedUnder T N ↔ counter r 0 0 ∈ T ∧
      (∀ i t, ρ.body[i]? = some t → (counterRules r ρ.bound i t).ClosedUnder T N) ∧
      (headRules (counter r ρ.body.length ρ.bound) ρ.head).ClosedUnder T N := by
  simp [normalize, Program.closedUnder_flatten_mapIdx, Rule.Holds]

theorem head_of_mem_counterRules {r L i : ℕ} {t : WTerm A} {ρ' : Rule (A ⊕ Aux A)}
    (h : ρ' ∈ counterRules r L i t) : ∃ k, ρ'.head = counter r (i + 1) k := by
  simp only [counterRules, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨k, -, rfl | rfl⟩ := h
  · exact ⟨k, rfl⟩
  · exact ⟨_, litRule_head _ _ _⟩

/-- A rule of the normalization is a fact for `c(r, 0, 0)`, a counter rule, or a head rule. -/
theorem mem_normalize {ρ : WRule A} {r : ℕ} {ρ' : Rule (A ⊕ Aux A)} (mem : ρ' ∈ ρ.normalize r) :
    (∃ i k, ρ'.head = counter r i k) ∨ ρ' ∈ headRules (counter r ρ.body.length ρ.bound) ρ.head := by
  simp only [normalize, List.mem_cons, List.mem_append, List.mem_flatten, List.mem_mapIdx] at mem
  rcases mem with rfl | ⟨_, ⟨i, hi, rfl⟩, mem⟩ | mem
  · exact .inl ⟨0, 0, rfl⟩
  · obtain ⟨k, hk⟩ := head_of_mem_counterRules mem
    exact .inl ⟨_, k, hk⟩
  · exact .inr mem

/-- The only rules for a complement atom are `h̄ :- not h.` for the choice atoms `h`. -/
theorem compl_rule_of_mem_normalize {ρ : WRule A} {r : ℕ} {ρ' : Rule (A ⊕ Aux A)} {a : A}
    (mem : ρ' ∈ ρ.normalize r) (head : ρ'.head = .inr (.compl a)) :
    a ∈ ρ.head.choices ∧ ρ'.neg = [.inl a] := by
  rcases mem_normalize mem with ⟨i, k, hk⟩ | mem
  · rw [hk] at head
    cases head
  · cases hρ : ρ.head with
    | atom h =>
      rw [hρ] at mem
      simp only [headRules, List.mem_singleton] at mem
      subst mem
      cases head
    | choice hs =>
      rw [hρ] at mem
      simp only [headRules, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at mem
      obtain ⟨h, hh, rfl | rfl⟩ := mem
      · cases head
      · cases head
        exact ⟨hh, rfl⟩
    | empty =>
      rw [hρ] at mem
      simp only [headRules, List.mem_singleton] at mem
      subst mem
      cases head

/-- The only rules for `⊥` have `not ⊥` in their bodies. -/
theorem falsum_mem_neg_of_mem_normalize {ρ : WRule A} {r : ℕ} {ρ' : Rule (A ⊕ Aux A)}
    (mem : ρ' ∈ ρ.normalize r) (head : ρ'.head = .inr .falsum) : .inr .falsum ∈ ρ'.neg := by
  rcases mem_normalize mem with ⟨i, k, hk⟩ | mem
  · rw [hk] at head
    cases head
  · cases hρ : ρ.head with
    | atom h =>
      rw [hρ] at mem
      simp only [headRules, List.mem_singleton] at mem
      subst mem
      cases head
    | choice hs =>
      rw [hρ] at mem
      simp only [headRules, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at mem
      obtain ⟨h, -, rfl | rfl⟩ := mem
      · cases head
      · cases head
    | empty =>
      rw [hρ] at mem
      simp only [headRules, List.mem_singleton] at mem
      subst mem
      exact List.mem_singleton_self _

end WRule

namespace WProgram

open WRule

variable (W : WProgram A)

/-- **The normalization**: the sequential weight counter of every rule, at its position. -/
def normalize : Program (A ⊕ Aux A) := (W.mapIdx fun r (ρ : WRule A) => ρ.normalize r).flatten

theorem closedUnder_normalize_iff (T N : Set (A ⊕ Aux A)) :
    W.normalize.ClosedUnder T N ↔ ∀ r (ρ : WRule A), W[r]? = some ρ → (ρ.normalize r).ClosedUnder T N :=
  Program.closedUnder_flatten_mapIdx

theorem exists_of_mem_normalize {ρ' : Rule (A ⊕ Aux A)} (mem : ρ' ∈ W.normalize) :
    ∃ r, ∃ ρ : WRule A, W[r]? = some ρ ∧ ρ' ∈ ρ.normalize r := by
  obtain ⟨P, hP, mem⟩ := List.mem_flatten.mp mem
  obtain ⟨r, hr, rfl⟩ := List.mem_mapIdx.mp hP
  exact ⟨r, _, List.getElem?_eq_getElem hr, mem⟩

/-- A choice atom: an atom of some choice head. -/
def ChoiceAtom (a : A) : Prop := ∃ ρ ∈ W, a ∈ ρ.head.choices

/-- **A coherent negation context**: the complement of each choice atom is in `N` exactly when
the atom is not. -/
def Coherent (N : Set (A ⊕ Aux A)) : Prop :=
  ∀ a, W.ChoiceAtom a → (Sum.inr (Aux.compl a) ∈ N ↔ Sum.inl a ∉ N)

/-- What the least model of the normalized reduct by `N` holds, computed from the original
atoms `V`: the counters by `reach`, the complements of the choice atoms outside `N`, and `⊥`
when it is outside `N` and some constraint body holds. -/
def derived (V : Set A) (N : Set (A ⊕ Aux A)) : Set (A ⊕ Aux A) :=
  {x | match x with
    | .inl a => a ∈ V
    | .inr (.count r i k) => ∃ ρ ∈ W[r]?, k ∈ reach ρ.bound ρ.body V (Sum.inl ⁻¹' N) i
    | .inr (.compl a) => W.ChoiceAtom a ∧ Sum.inl a ∉ N
    | .inr .falsum => Sum.inr Aux.falsum ∉ N ∧ ∃ ρ ∈ W, ρ.head = .empty ∧ ρ.BodyHolds V (Sum.inl ⁻¹' N)}

/-- **The extension** of a set `S` of original atoms: the counters by `reach`, the complements
of the choice atoms outside `S`, and never `⊥`. -/
def extend (S : Set A) : Set (A ⊕ Aux A) :=
  {x | match x with
    | .inl a => a ∈ S
    | .inr (.count r i k) => ∃ ρ ∈ W[r]?, k ∈ reach ρ.bound ρ.body S S i
    | .inr (.compl a) => W.ChoiceAtom a ∧ a ∉ S
    | .inr .falsum => False}

variable {W}

theorem preimage_inl_derived (V : Set A) (N : Set (A ⊕ Aux A)) : Sum.inl ⁻¹' W.derived V N = V := rfl

theorem preimage_inl_extend (S : Set A) : Sum.inl ⁻¹' W.extend S = S := rfl

theorem mem_derived_counter {V : Set A} {N : Set (A ⊕ Aux A)} {r i k : ℕ} {ρ : WRule A} (hρ : W[r]? = some ρ) :
    counter r i k ∈ W.derived V N ↔ k ∈ reach ρ.bound ρ.body V (Sum.inl ⁻¹' N) i := by
  simp [derived, hρ]

theorem mem_derived_compl {V : Set A} {N : Set (A ⊕ Aux A)} {a : A} :
    Sum.inr (Aux.compl a) ∈ W.derived V N ↔ W.ChoiceAtom a ∧ Sum.inl a ∉ N := Iff.rfl

theorem mem_derived_falsum {V : Set A} {N : Set (A ⊕ Aux A)} :
    Sum.inr Aux.falsum ∈ W.derived V N ↔
      Sum.inr Aux.falsum ∉ N ∧ ∃ ρ ∈ W, ρ.head = .empty ∧ ρ.BodyHolds V (Sum.inl ⁻¹' N) := Iff.rfl

theorem mem_extend_falsum {S : Set A} : Sum.inr Aux.falsum ∉ W.extend S := id

theorem mem_extend_compl {S : Set A} {a : A} :
    Sum.inr (Aux.compl a) ∈ W.extend S ↔ W.ChoiceAtom a ∧ a ∉ S := Iff.rfl

/-- **The least model of the normalized reduct.** In a coherent negation context `N`, the least
model of the reduct of the normalized program by `N` is derived from the least model of the
weight reduct by the original atoms of `N`. -/
theorem glOp_normalize {N : Set (A ⊕ Aux A)} (coherent : W.Coherent N) :
    W.normalize.glOp N = W.derived (W.glOp (Sum.inl ⁻¹' N)) N := by
  have closedG := (W.closedUnder_normalize_iff _ N).mp (W.normalize.closedUnder_glOp N)
  have rules : ∀ r (ρ : WRule A), W[r]? = some ρ → _ := fun r ρ hρ =>
    (ρ.closedUnder_normalize_iff r (W.normalize.glOp N) N).mp (closedG r ρ hρ)
  -- The counters reached from atoms of `G` are in `G`.
  have count : ∀ r (ρ : WRule A), W[r]? = some ρ → ∀ X ⊆ Sum.inl ⁻¹' W.normalize.glOp N, ∀ i k,
      k ∈ reach ρ.bound ρ.body X (Sum.inl ⁻¹' N) i → counter r i k ∈ W.normalize.glOp N := by
    intro r ρ hρ X hX i
    induction i with
    | zero =>
      intro k hk
      rw [Set.mem_singleton_iff.mp hk]
      exact (rules r ρ hρ).1
    | succ i ih =>
      rintro k ⟨t, ht, hk | ⟨k', hk', holds, rfl⟩⟩
      · have step := (closedUnder_counterRules _ _ _ _ _ _).mp ((rules r ρ hρ).2.1 i t (Option.mem_def.mp ht))
        exact (step k (reach_le_bound hk) (ih k hk)).1
      · have step := (closedUnder_counterRules _ _ _ _ _ _).mp ((rules r ρ hρ).2.1 i t (Option.mem_def.mp ht))
        exact (step k' (reach_le_bound hk') (ih k' hk')).2 (holds.mono_left hX)
  -- The original atoms of the weight reduct's least model are in `G`.
  have origin : W.glOp (Sum.inl ⁻¹' N) ⊆ Sum.inl ⁻¹' W.normalize.glOp N := by
    apply OrderHom.lfp_le
    rintro a ⟨ρ, hρ, offers, body⟩
    obtain ⟨r, hr⟩ := List.mem_iff_getElem?.mp hρ
    have final := count r ρ hr _ le_rfl _ _ (bound_mem_reach_iff.mpr body)
    have heads := (rules r ρ hr).2.2
    cases hh : ρ.head with
    | atom h =>
      rw [hh, closedUnder_headRules_atom] at heads
      rw [hh] at offers
      have same : h = a := offers
      subst same
      exact heads final
    | choice hs =>
      rw [hh, closedUnder_headRules_choice] at heads
      rw [hh] at offers
      obtain ⟨has, inN⟩ := offers
      refine (heads a has).1 final fun compl => ?_
      have choiceAtom : W.ChoiceAtom a := ⟨ρ, hρ, by rw [hh]; exact has⟩
      exact ((coherent a choiceAtom).mp compl) inN
    | empty =>
      rw [hh] at offers
      exact offers.elim
  apply le_antisymm
  · -- `G` is below the derived set, which is closed.
    apply Program.glOp_subset_of_closedUnder
    rw [closedUnder_normalize_iff]
    intro r ρ hρ
    have mem : ρ ∈ W := List.mem_iff_getElem?.mpr ⟨r, hρ⟩
    rw [WRule.closedUnder_normalize_iff]
    refine ⟨(mem_derived_counter hρ).mpr rfl, fun i t ht => ?_, ?_⟩
    · rw [closedUnder_counterRules]
      intro k _ hk
      rw [mem_derived_counter hρ] at hk
      rw [mem_derived_counter hρ, mem_derived_counter hρ, preimage_inl_derived]
      exact ⟨⟨t, Option.mem_def.mpr ht, .inl hk⟩, fun holds => ⟨t, Option.mem_def.mpr ht, .inr ⟨k, hk, holds, rfl⟩⟩⟩
    · have body : counter r ρ.body.length ρ.bound ∈ W.derived (W.glOp (Sum.inl ⁻¹' N)) N →
          ρ.BodyHolds (W.glOp (Sum.inl ⁻¹' N)) (Sum.inl ⁻¹' N) := fun hc =>
        bound_mem_reach_iff.mp ((mem_derived_counter hρ).mp hc)
      cases hh : ρ.head with
      | atom h =>
        rw [closedUnder_headRules_atom]
        intro hc
        show h ∈ W.glOp _
        rw [← W.glOp_fixed]
        exact ⟨ρ, mem, by rw [hh]; rfl, body hc⟩
      | choice hs =>
        rw [closedUnder_headRules_choice]
        intro h hh'
        have choiceAtom : W.ChoiceAtom h := ⟨ρ, mem, by rw [hh]; exact hh'⟩
        refine ⟨fun hc notCompl => ?_, fun notIn => ⟨choiceAtom, notIn⟩⟩
        have inN : Sum.inl h ∈ N := not_not.mp (mt (coherent h choiceAtom).mpr notCompl)
        show h ∈ W.glOp _
        rw [← W.glOp_fixed]
        exact ⟨ρ, mem, by rw [hh]; exact ⟨hh', inN⟩, body hc⟩
      | empty =>
        rw [closedUnder_headRules_empty]
        intro hc notIn
        exact ⟨notIn, ρ, mem, hh, body hc⟩
  · -- The derived set is below `G`.
    intro x hx
    rcases x with a | (⟨r, i, k⟩ | a | _)
    · exact origin hx
    · obtain ⟨ρ, hρ, hk⟩ := hx
      exact count _ ρ (Option.mem_def.mp hρ) _ origin _ _ hk
    · obtain ⟨⟨ρ, hρ, ha⟩, notIn⟩ := mem_derived_compl.mp hx
      obtain ⟨r, hr⟩ := List.mem_iff_getElem?.mp hρ
      obtain ⟨hs, hh, has⟩ := WHead.exists_of_mem_choices ha
      have heads := (rules r ρ hr).2.2
      rw [hh, closedUnder_headRules_choice] at heads
      exact (heads a has).2 notIn
    · obtain ⟨notIn, ρ, hρ, hh, body⟩ := mem_derived_falsum.mp hx
      obtain ⟨r, hr⟩ := List.mem_iff_getElem?.mp hρ
      have final := count r ρ hr _ origin _ _ (bound_mem_reach_iff.mpr body)
      have heads := (rules r ρ hr).2.2
      rw [hh, closedUnder_headRules_empty] at heads
      exact heads final notIn

/-- A complement atom is derived only when its atom is a choice atom outside `N`. -/
theorem compl_of_mem_step {I N : Set (A ⊕ Aux A)} {a : A} (h : Sum.inr (Aux.compl a) ∈ W.normalize.step I N) :
    W.ChoiceAtom a ∧ Sum.inl a ∉ N := by
  obtain ⟨ρ', hρ', head, holds⟩ := h
  obtain ⟨r, ρ, hρ, mem⟩ := W.exists_of_mem_normalize hρ'
  obtain ⟨ha, neg⟩ := compl_rule_of_mem_normalize mem head
  refine ⟨⟨ρ, List.mem_iff_getElem?.mpr ⟨r, hρ⟩, ha⟩, holds.2 _ ?_⟩
  rw [neg]
  exact List.mem_singleton_self _

/-- `⊥` is derived only when it is outside `N`. -/
theorem falsum_of_mem_step {I N : Set (A ⊕ Aux A)} (h : Sum.inr Aux.falsum ∈ W.normalize.step I N) :
    Sum.inr Aux.falsum ∉ N := by
  obtain ⟨ρ', hρ', head, holds⟩ := h
  obtain ⟨r, ρ, -, mem⟩ := W.exists_of_mem_normalize hρ'
  exact holds.2 _ (falsum_mem_neg_of_mem_normalize mem head)

theorem coherent_of_stable {M : Set (A ⊕ Aux A)} (stable : W.normalize.Stable M) : W.Coherent M := by
  intro a ⟨ρ, hρ, ha⟩
  constructor
  · intro h
    have h' : Sum.inr (Aux.compl a) ∈ W.normalize.glOp M := by
      rw [← stable]
      exact h
    rw [← W.normalize.glOp_fixed] at h'
    exact (compl_of_mem_step h').2
  · intro notIn
    obtain ⟨r, hr⟩ := List.mem_iff_getElem?.mp hρ
    obtain ⟨hs, hh, has⟩ := WHead.exists_of_mem_choices ha
    have heads := ((ρ.closedUnder_normalize_iff r _ M).mp ((W.closedUnder_normalize_iff _ M).mp
      (W.normalize.closedUnder_glOp M) r ρ hr)).2.2
    rw [hh, closedUnder_headRules_choice] at heads
    have := (heads a has).2 notIn
    rwa [← stable] at this

theorem falsum_not_mem_of_stable {M : Set (A ⊕ Aux A)} (stable : W.normalize.Stable M) :
    Sum.inr Aux.falsum ∉ M := by
  intro h
  have h' : Sum.inr Aux.falsum ∈ W.normalize.glOp M := by
    rw [← stable]
    exact h
  rw [← W.normalize.glOp_fixed] at h'
  exact falsum_of_mem_step h' h

theorem derived_eq_extend {S : Set A} {M : Set (A ⊕ Aux A)} (hS : Sum.inl ⁻¹' M = S)
    (constraints : ∀ ρ ∈ W, ρ.head = .empty → ¬ ρ.BodyHolds S S) : W.derived S M = W.extend S := by
  subst hS
  ext x
  rcases x with a | (⟨r, i, k⟩ | a | _)
  · rfl
  · rfl
  · rfl
  · rw [mem_derived_falsum]
    refine ⟨fun ⟨_, ρ, hρ, hh, body⟩ => constraints ρ hρ hh body, fun h => absurd h mem_extend_falsum⟩

/-- The extension of a stable model of the weight program is a stable model of the normalized
program. -/
theorem stable_extend {S : Set A} (stable : W.Stable S) : W.normalize.Stable (W.extend S) := by
  obtain ⟨fixed, constraints⟩ := (W.stable_iff S).mp stable
  have coherent : W.Coherent (W.extend S) := fun a choiceAtom => by
    rw [mem_extend_compl]
    exact ⟨fun h => h.2, fun h => ⟨choiceAtom, h⟩⟩
  unfold Program.Stable
  rw [W.glOp_normalize coherent, preimage_inl_extend, ← fixed]
  exact (derived_eq_extend (preimage_inl_extend S) constraints).symm

/-- **Stable models of the normalized program**: exactly the extensions of the stable models of
the weight program. -/
theorem stable_normalize_iff (M : Set (A ⊕ Aux A)) :
    W.normalize.Stable M ↔ W.Stable (Sum.inl ⁻¹' M) ∧ M = W.extend (Sum.inl ⁻¹' M) := by
  constructor
  · intro stable
    have key := W.glOp_normalize (coherent_of_stable stable)
    rw [← stable] at key
    have fixed : Sum.inl ⁻¹' M = W.glOp (Sum.inl ⁻¹' M) :=
      (congrArg (Sum.inl ⁻¹' ·) key).trans (preimage_inl_derived _ _)
    have constraints : ∀ ρ ∈ W, ρ.head = .empty → ¬ ρ.BodyHolds (Sum.inl ⁻¹' M) (Sum.inl ⁻¹' M) := by
      intro ρ hρ hh body
      apply falsum_not_mem_of_stable stable
      rw [key, mem_derived_falsum, ← fixed]
      exact ⟨falsum_not_mem_of_stable stable, ρ, hρ, hh, body⟩
    refine ⟨(W.stable_iff _).mpr ⟨fixed, constraints⟩, ?_⟩
    calc M = W.derived (W.glOp (Sum.inl ⁻¹' M)) M := key
      _ = W.derived (Sum.inl ⁻¹' M) M := by rw [← fixed]
      _ = W.extend (Sum.inl ⁻¹' M) := derived_eq_extend rfl constraints
  · rintro ⟨stable, hM⟩
    rw [hM]
    exact stable_extend stable

/-- The stable models of the weight program are the restrictions of the stable models of the
normalized program. -/
theorem stable_iff_exists_normalize (S : Set A) :
    W.Stable S ↔ ∃ M, W.normalize.Stable M ∧ Sum.inl ⁻¹' M = S := by
  constructor
  · intro h
    exact ⟨W.extend S, stable_extend h, preimage_inl_extend S⟩
  · rintro ⟨M, hM, rfl⟩
    exact ((stable_normalize_iff M).mp hM).1

/-- **Each stable model of the weight program extends to exactly one stable model of the
normalized program**: the auxiliary atoms are determined. -/
theorem existsUnique_normalize {S : Set A} (h : W.Stable S) :
    ∃! M, W.normalize.Stable M ∧ Sum.inl ⁻¹' M = S := by
  refine ⟨W.extend S, ⟨stable_extend h, preimage_inl_extend S⟩, ?_⟩
  rintro M ⟨hM, rfl⟩
  exact ((stable_normalize_iff M).mp hM).2

variable (W) in
/-- **The normalization is correct**: restriction to the original atoms maps the stable models
of the normalized program onto the stable models of the weight program, and each stable model
of the weight program extends to exactly one stable model of the normalized program. -/
theorem normalize_correct :
    (Sum.inl ⁻¹' ·) '' {M | W.normalize.Stable M} = {S | W.Stable S} ∧
      ∀ S, W.Stable S → ∃! M, W.normalize.Stable M ∧ Sum.inl ⁻¹' M = S := by
  refine ⟨?_, fun S => existsUnique_normalize⟩
  ext S
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  rw [stable_iff_exists_normalize]

end WProgram

/-! ## The executable checker and enumerator -/

section Executable

variable [DecidableEq A]

/-- The executable literal test. -/
def WLit.holdsFin : WLit A → Finset A → Finset A → Bool
  | .pos a, I, _ => decide (a ∈ I)
  | .neg a, _, N => decide (a ∉ N)

theorem WLit.holdsFin_iff (l : WLit A) (I N : Finset A) : l.holdsFin I N = true ↔ l.Holds ↑I ↑N := by
  cases l <;> simp [holdsFin, Holds]

/-- The weight of the true literals, computed. -/
def weightFin (ts : List (WTerm A)) (I N : Finset A) : ℕ :=
  (ts.map fun t => if t.lit.holdsFin I N then t.weight else 0).sum

theorem weightFin_eq (ts : List (WTerm A)) (I N : Finset A) : weightFin ts I N = weightIn ts ↑I ↑N := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [weightIn_cons, ← ih]
    simp only [weightFin, List.map_cons, List.sum_cons]
    congr 1
    by_cases h : t.lit.Holds ↑I ↑N
    · rw [if_pos ((t.lit.holdsFin_iff I N).mpr h), WTerm.value_of_holds h]
    · rw [if_neg (mt (t.lit.holdsFin_iff I N).mp h), WTerm.value_of_not_holds h]

/-- The executable body test. -/
def WRule.bodyHoldsFin (ρ : WRule A) (I N : Finset A) : Bool := decide (ρ.bound ≤ weightFin ρ.body I N)

theorem WRule.bodyHoldsFin_iff (ρ : WRule A) (I N : Finset A) : ρ.bodyHoldsFin I N = true ↔ ρ.BodyHolds ↑I ↑N := by
  rw [bodyHoldsFin, decide_eq_true_iff, weightFin_eq]
  rfl

/-- The executable head test. -/
def WHead.holdsFin : WHead A → Finset A → Bool
  | .atom h, S => decide (h ∈ S)
  | .choice _, _ => true
  | .empty, _ => false

theorem WHead.holdsFin_iff (h : WHead A) (S : Finset A) : h.holdsFin S = true ↔ h.Holds ↑S := by
  cases h <;> simp [holdsFin, Holds]

namespace WProgram

variable (W : WProgram A)

/-- The atoms some head can derive. -/
def heads : Finset A := (W.flatMap fun ρ => ρ.head.atoms).toFinset

theorem coe_heads : (↑W.heads : Set A) = W.headSet := by
  ext a
  simp [heads, headSet]

/-- The executable immediate-consequence step. -/
def stepFin (I N : Finset A) : Finset A :=
  (W.flatMap fun ρ => if ρ.bodyHoldsFin I N then ρ.head.offered ↑N else []).toFinset

theorem coe_stepFin (I N : Finset A) : (↑(W.stepFin I N) : Set A) = W.step ↑I ↑N := by
  ext a
  simp only [Finset.mem_coe, stepFin, List.mem_toFinset, List.mem_flatMap, step, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ρ, hρ, ha⟩
    by_cases body : ρ.bodyHoldsFin I N = true
    · rw [if_pos body] at ha
      exact ⟨ρ, hρ, WHead.mem_offered.mp ha, (ρ.bodyHoldsFin_iff I N).mp body⟩
    · rw [if_neg body] at ha
      exact absurd ha List.not_mem_nil
  · rintro ⟨ρ, hρ, offers, body⟩
    refine ⟨ρ, hρ, ?_⟩
    rw [if_pos ((ρ.bodyHoldsFin_iff I N).mpr body)]
    exact WHead.mem_offered.mpr offers

theorem stepFin_subset_heads (I N : Finset A) : W.stepFin I N ⊆ W.heads := by
  rw [← Finset.coe_subset, coe_stepFin, coe_heads]
  exact W.step_subset_headSet _ _

theorem stepFin_mono (N : Finset A) : Monotone fun I => W.stepFin I N := by
  intro I I' h
  rw [← Finset.coe_subset, coe_stepFin, coe_stepFin]
  exact W.step_mono _ (Finset.coe_subset.mpr h)

/-- The least fixed point of `step · N`, by Kleene iteration from `∅`, `|heads|` times. -/
def lfpFin (N : Finset A) : Finset A := (fun I => W.stepFin I N)^[W.heads.card] ∅

theorem coe_lfpFin (N : Finset A) : (↑(W.lfpFin N) : Set A) = W.glOp ↑N :=
  iterate_eq_lfp (fun I => W.stepFin I N) (W.reductOp ↑N) (fun I : Finset A => (↑I : Set A))
    (fun I => W.coe_stepFin I N) (by simp)
    _ (Finset.iterate_card_fixed (W.stepFin_mono N) W.heads (fun I => W.stepFin_subset_heads I N))

/-- The least model, computed. -/
def leastModelFin : Finset A := W.lfpFin ∅

theorem coe_leastModelFin : (↑W.leastModelFin : Set A) = W.leastModel := by
  rw [leastModelFin, coe_lfpFin, Finset.coe_empty]
  rfl

/-- The executable test that every rule is satisfied. -/
def modelsFin (S : Finset A) : Bool := W.all fun ρ => !ρ.bodyHoldsFin S S || ρ.head.holdsFin S

theorem modelsFin_iff (S : Finset A) : W.modelsFin S = true ↔ W.Models ↑S := by
  simp only [modelsFin, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Models]
  apply forall₂_congr
  intro ρ _
  rw [← ρ.bodyHoldsFin_iff, ← ρ.head.holdsFin_iff]
  cases ρ.bodyHoldsFin S S <;> simp

/-- **The stable-model checker**: compute the reduct, its least model, and compare. -/
def isStable (S : Finset A) : Bool := W.modelsFin S && decide ((W.reduct ↑S).leastModelFin = S)

theorem isStable_iff (S : Finset A) : W.isStable S = true ↔ W.Stable ↑S := by
  rw [isStable, Bool.and_eq_true, modelsFin_iff, decide_eq_true_iff, stable_iff_glOp,
    ← W.leastModel_reduct ↑S, ← coe_leastModelFin, eq_comm, Finset.coe_inj]

/-- The head atoms, each once. -/
def atomList : List A := (W.flatMap fun ρ => ρ.head.atoms).dedup

/-- **The enumerator**: every set of head atoms, kept when it is stable. -/
def stableModels : Finset (Finset A) :=
  ((W.atomList.sublists.filter fun l => W.isStable l.toFinset).map List.toFinset).toFinset

theorem mem_stableModels (S : Finset A) : S ∈ W.stableModels ↔ W.Stable ↑S := by
  simp only [stableModels, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨l, ⟨-, hl⟩, rfl⟩
    exact (W.isStable_iff _).mp hl
  · intro h
    refine ⟨W.atomList.filter fun a => decide (a ∈ S), ⟨List.mem_sublists.mpr List.filter_sublist, ?_⟩, ?_⟩
    all_goals
      have same : (W.atomList.filter fun a => decide (a ∈ S)).toFinset = S := by
        ext a
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, atomList, List.mem_dedup,
          List.mem_flatMap]
        refine ⟨And.right, fun ha => ⟨?_, ha⟩⟩
        obtain ⟨ρ, hρ, hρa⟩ := h.subset_headSet (show a ∈ (↑S : Set A) from ha)
        exact ⟨ρ, hρ, hρa⟩
    · rw [same]
      exact (W.isStable_iff S).mpr h
    · exact same

/-- Every stable model, over `Set`, is one of the computed ones. -/
theorem stable_iff_mem_stableModels (S : Set A) : W.Stable S ↔ ∃ M ∈ W.stableModels, ↑M = S := by
  constructor
  · intro h
    have finite : S.Finite := (W.coe_heads ▸ W.heads.finite_toSet).subset h.subset_headSet
    refine ⟨finite.toFinset, (W.mem_stableModels _).mpr ?_, finite.coe_toFinset⟩
    rw [finite.coe_toFinset]
    exact h
  · rintro ⟨M, hM, rfl⟩
    exact (W.mem_stableModels M).mp hM

end WProgram

/-- The original atoms of a set over `A ⊕ Aux A`, computed. -/
def restrictFin (M : Finset (A ⊕ Aux A)) : Finset A := (M.val.filterMap Sum.getLeft?).toFinset

theorem coe_restrictFin (M : Finset (A ⊕ Aux A)) :
    (↑(restrictFin M) : Set A) = Sum.inl ⁻¹' (↑M : Set (A ⊕ Aux A)) := by
  ext a
  simp [restrictFin]

end Executable

/-! ## Stable models of a normal program, by its negated atoms -/

section NegatedAtoms

variable [DecidableEq A]

namespace Program

variable (P : Program A)

/-- The atoms that occur negated in some rule. -/
def negAtoms : List A := (P.flatMap Rule.neg).dedup

theorem mem_negAtoms {b : A} : b ∈ P.negAtoms ↔ ∃ r ∈ P, b ∈ r.neg := by
  simp [negAtoms]

/-- The immediate-consequence operator reads only the negated atoms of the negation context. -/
theorem step_congr_negAtoms {I N N' : Set A} (same : ∀ b ∈ P.negAtoms, b ∈ N ↔ b ∈ N') :
    P.step I N = P.step I N' := by
  ext a
  constructor
  · rintro ⟨r, hr, head, pos, neg⟩
    exact ⟨r, hr, head, pos, fun b hb hbN => neg b hb ((same b (P.mem_negAtoms.mpr ⟨r, hr, hb⟩)).mpr hbN)⟩
  · rintro ⟨r, hr, head, pos, neg⟩
    exact ⟨r, hr, head, pos, fun b hb hbN => neg b hb ((same b (P.mem_negAtoms.mpr ⟨r, hr, hb⟩)).mp hbN)⟩

theorem glOp_congr_negAtoms {N N' : Set A} (same : ∀ b ∈ P.negAtoms, b ∈ N ↔ b ∈ N') :
    P.glOp N = P.glOp N' := by
  unfold glOp
  congr 1
  apply OrderHom.ext
  funext I
  exact P.step_congr_negAtoms same

/-- **Stable models by their negated atoms**: for each set `l` of negated atoms, the least model
of the reduct by `l`, kept when the negated atoms it contains are exactly those of `l`. Only the
negated atoms are guessed. -/
def stableModelsNeg : Finset (Finset A) :=
  (P.negAtoms.sublists.filterMap fun l =>
    if (P.lfpFin l.toFinset).filter (· ∈ P.negAtoms) = l.toFinset then some (P.lfpFin l.toFinset)
    else none).toFinset

theorem mem_stableModelsNeg (M : Finset A) : M ∈ P.stableModelsNeg ↔ P.Stable ↑M := by
  simp only [stableModelsNeg, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨l, -, hl⟩
    split_ifs at hl with same
    obtain rfl := Option.some.inj hl
    have agree : ∀ b ∈ P.negAtoms, b ∈ (↑l.toFinset : Set A) ↔ b ∈ P.glOp ↑l.toFinset := by
      intro b hb
      have := Finset.ext_iff.mp same b
      rw [Finset.mem_filter] at this
      rw [← P.coe_lfpFin, Finset.mem_coe, Finset.mem_coe]
      exact ⟨fun h => (this.mpr h).1, fun h => this.mp ⟨h, hb⟩⟩
    unfold Stable
    rw [P.coe_lfpFin]
    exact P.glOp_congr_negAtoms agree
  · intro stable
    refine ⟨P.negAtoms.filter fun b => decide (b ∈ M), List.mem_sublists.mpr List.filter_sublist, ?_⟩
    have agree : ∀ b ∈ P.negAtoms,
        b ∈ (↑(P.negAtoms.filter fun b => decide (b ∈ M)).toFinset : Set A) ↔ b ∈ (↑M : Set A) := by
      intro b hb
      simp [hb]
    have lfp : P.lfpFin (P.negAtoms.filter fun b => decide (b ∈ M)).toFinset = M := by
      rw [← Finset.coe_inj, P.coe_lfpFin, P.glOp_congr_negAtoms agree, ← stable]
    rw [lfp, if_pos]
    ext b
    simp [and_comm]

/-- Every stable model, over `Set`, is one of those found by the negated atoms. -/
theorem stable_iff_mem_stableModelsNeg (S : Set A) : P.Stable S ↔ ∃ M ∈ P.stableModelsNeg, ↑M = S := by
  constructor
  · intro h
    have finite : S.Finite := (P.coe_heads ▸ P.heads.finite_toSet).subset (Stable.subset_headSet P h)
    refine ⟨finite.toFinset, (P.mem_stableModelsNeg _).mpr ?_, finite.coe_toFinset⟩
    rw [finite.coe_toFinset]
    exact h
  · rintro ⟨M, hM, rfl⟩
    exact (P.mem_stableModelsNeg M).mp hM

end Program

end NegatedAtoms

end Mettapedia.Logic.ASP
