import Mettapedia.Logic.ASP.Checker

/-!
# Nogoods: the constraint representation of a conflict-driven solver

Following Gebser, Kaufmann and Schaub ("Conflict-driven answer set solving: from
theory to practice", AIJ 2012), a solver has two kinds of variables, atoms and
rule bodies (`Var`); equal bodies are one variable. A signed literal `T v` or
`F v` (`Lit`) asserts a truth value. A **nogood** is a list of literals that must
not all hold; every nogood carries the rule, body, atom or loop it came from
(`Origin`), which is the reason a solver reports when the nogood propagates.

## Completion nogoods

For each body `B = {a₁, …, aₘ, not b₁, …, not bₙ}`:
* `{F B, T a₁, …, T aₘ, F b₁, …, F bₙ}`: a body whose literals hold is true;
* `{T B, F aᵢ}` and `{T B, T bⱼ}`: a true body has true literals.

For each rule `p :- B`, `{T B, F p}`: a rule with a true body has a true head.
For each atom `p` with bodies `B₁, …, Bₖ`, `{T p, F B₁, …, F Bₖ}`: a true atom has a
true body.

**Unit bodies.** A body with exactly one literal (`Body.IsUnit`: one positive atom
and no negated atom, or the reverse) is equivalent to that literal, so it gets no
variable: its literal (`Body.lit`, `T a` for `a` and `F b` for `not b`; `T B` for any
other body) stands for it in every nogood, and it has no body nogoods. A rule
`p :- B` gives `{ℓ(B), F p}`, and a support or loop nogood has the complement
`ℓ(B)ᶜ` of the literal of each body in place of `F B`.

**Falsum atoms.** An atom `f` that heads some rule, every rule of which has `not f`
in its body (`Program.Falsum`, decided by `Program.falsum`), is the head of
integrity constraints `f :- B, not f`. No supported model holds it
(`Program.not_mem_of_falsum`), and none satisfies the body of one of its rules
without `not f` (`Program.constraint_fails`). The completion is reduced at these
atoms (`Program.ruleNogoods`): a rule of a falsum atom gives the one nogood
`{T a₁, …, T aₘ, F b₁, …, F bₙ}` of its body without `not f` (`constraintNogood`),
and no body variable; the support nogood of a falsum atom is `{T f}`. The bodies
that are variables are those of the other rules that are not unit bodies
(`Program.bodyRules`); a body shared with one of them keeps its variable.

A total assignment (`Valuation`, admissible when it makes no atom outside the
program true) satisfies all completion nogoods exactly when its atoms form a
supported model and its body variables carry the truth values of the bodies
(`completionSolution_iff`). `Program.BodiesCorrect` is stated over the literals of
the bodies and constrains exactly the body variables (`Program.bodiesCorrect_iff`).
Through `Kernel.completion_iff_supported` this is Clark's completion formula of
`ClarkCompletion` (`completionSolution_iff_clark`). Every supported model arises
(`completionSolution_canonical`): the literal of every body holds in the canonical
assignment of a set exactly when the body does (`Program.lit_sat_canonical`).

## Loop nogoods

For a set of atoms `U` and `a ∈ U`, `{T a, ℓ(B₁)ᶜ, …, ℓ(Bₖ)ᶜ}` where the `Bᵢ` are the
bodies of the rules that support `U` from outside. A completion solution
satisfies all loop nogoods exactly when its atoms form a stable model
(`loopSolution_iff_stable`); this is the Lin–Zhao theorem of `Kernel` in nogood
form. The loop nogoods of the sets without falsum atoms already suffice
(`stable_of_loops`): a supported model holds no falsum atom, so the other atoms of
a set have the same external support. Altogether, the solutions of the completion
and loop nogoods are exactly the stable models (`solution_iff_stable`).

## Reasons

* Every completion and loop nogood holds in every stable model
  (`completionNogood_entailed`, `loopNogood_entailed`), and resolution preserves
  this (`Entailed.resolve`); so does any superset (`Entailed.weaken`).
* The canonical assignment of a finite set of atoms is computable
  (`finValuation_eq_canonical`), and violation, completion solutions and
  unfoundedness are decidable.
* **Unfounded-set propagation has compact reasons.** If `U` is unfounded with
  respect to a partial assignment (every rule for an atom of `U` has a false body
  or a positive body atom in `U`), then for each `a ∈ U` every literal of the
  loop nogood except `T a` is assigned (`loopNogood_unit_of_unfounded`), so the
  nogood itself is the reason for `F a`; its size is at most one more than the
  number of rules (`loopNogood_length_le`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

universe u

variable {A : Type u}

/-- The body of a rule as a solver object. -/
structure Body (A : Type u) where
  pos : List A
  neg : List A
  deriving DecidableEq, Repr

/-- The body holds: positive atoms in `I`, negated atoms outside `N`. -/
def Body.Holds (B : Body A) (I N : Set A) : Prop := (∀ b ∈ B.pos, b ∈ I) ∧ ∀ b ∈ B.neg, b ∉ N

/-- The body of a rule. -/
def Rule.body (r : Rule A) : Body A := ⟨r.pos, r.neg⟩

@[simp] theorem Rule.body_holds (r : Rule A) (I N : Set A) : r.body.Holds I N ↔ r.Holds I N := Iff.rfl

/-- Solver variables: atoms and rule bodies. -/
inductive Var (A : Type u)
  | atom (a : A)
  | body (B : Body A)
  deriving DecidableEq, Repr

/-- A signed literal `T var` (`sign = true`) or `F var`. -/
structure Lit (A : Type u) where
  var : Var A
  sign : Bool
  deriving DecidableEq, Repr

/-- The complementary literal. -/
def Lit.compl (l : Lit A) : Lit A := ⟨l.var, !l.sign⟩

@[simp] theorem Lit.compl_compl (l : Lit A) : l.compl.compl = l := by
  simp [Lit.compl]

/-- Where a nogood came from: its reason when it propagates. -/
inductive Origin (A : Type u)
  /-- `{F B} ∪ B`: a body whose literals hold is true. A unit body has no body nogoods. -/
  | bodyTrue (B : Body A)
  /-- `{T B, F a}` for a positive atom `a` of `B`. -/
  | bodyPos (B : Body A) (a : A)
  /-- `{T B, T b}` for a negated atom `b` of `B`. -/
  | bodyNeg (B : Body A) (b : A)
  /-- `{ℓ(B), F p}` for the rule `p :- B`, with `ℓ(B)` the literal of `B`. -/
  | head (r : Rule A)
  /-- `{T a₁, …, T aₘ, F b₁, …, F bₙ}` for a rule `p :- a₁, …, aₘ, not b₁, …, not bₙ, not p` of a
  falsum atom `p`: its body without `not p`. -/
  | constraint (r : Rule A)
  /-- `{T p, ℓ(B₁)ᶜ, …, ℓ(Bₖ)ᶜ}` for the bodies of the rules for `p`. -/
  | support (a : A)
  /-- `{T a, ℓ(B₁)ᶜ, …, ℓ(Bₖ)ᶜ}` for the external bodies of `U ∋ a`. -/
  | loop (U : Finset A) (a : A)
  /-- A nogood learned in conflict analysis, with the solver's index for it. -/
  | learned (id : ℕ)
  deriving DecidableEq

/-- A nogood: literals that must not all hold, with the reason it exists. -/
structure Nogood (A : Type u) where
  lits : List (Lit A)
  origin : Origin A
  deriving DecidableEq

/-! ## Total assignments -/

/-- A total assignment: a truth value for every variable. -/
abbrev Valuation (A : Type u) := Var A → Bool

/-- A literal holds in a total assignment. -/
def Lit.Sat (v : Valuation A) (l : Lit A) : Prop := v l.var = l.sign

instance [DecidableEq A] (v : Valuation A) (l : Lit A) : Decidable (l.Sat v) :=
  inferInstanceAs (Decidable (v l.var = l.sign))

theorem Lit.sat_compl (v : Valuation A) (l : Lit A) : l.compl.Sat v ↔ ¬ l.Sat v := by
  unfold Lit.Sat Lit.compl
  cases v l.var <;> cases l.sign <;> simp

/-- A nogood is violated when all its literals hold. -/
def Nogood.Violated (v : Valuation A) (δ : Nogood A) : Prop := ∀ l ∈ δ.lits, l.Sat v

/-- The atoms a total assignment makes true. -/
def Valuation.atoms (v : Valuation A) : Set A := {a | v (.atom a) = true}

/-- The positive literal of an atom. -/
def tAtom (a : A) : Lit A := ⟨.atom a, true⟩
/-- The negative literal of an atom. -/
def fAtom (a : A) : Lit A := ⟨.atom a, false⟩
/-- The positive literal of a body. -/
def tBody (B : Body A) : Lit A := ⟨.body B, true⟩
/-- The negative literal of a body. -/
def fBody (B : Body A) : Lit A := ⟨.body B, false⟩

theorem Nogood.not_violated_iff {v : Valuation A} {δ : Nogood A} : ¬ δ.Violated v ↔ ∃ l ∈ δ.lits, ¬ l.Sat v := by
  simp [Nogood.Violated]

@[simp] theorem tAtom_sat (v : Valuation A) (a : A) : (tAtom a).Sat v ↔ a ∈ v.atoms := Iff.rfl
@[simp] theorem fAtom_sat (v : Valuation A) (a : A) : (fAtom a).Sat v ↔ a ∉ v.atoms := by
  simp [fAtom, Lit.Sat, Valuation.atoms]
@[simp] theorem tBody_sat (v : Valuation A) (B : Body A) : (tBody B).Sat v ↔ v (.body B) = true := Iff.rfl
@[simp] theorem fBody_sat (v : Valuation A) (B : Body A) : (fBody B).Sat v ↔ v (.body B) = false := Iff.rfl

/-! ## Unit bodies -/

/-- A **unit body** has exactly one literal: one positive atom and no negated atom, or the
reverse. -/
def Body.IsUnit (B : Body A) : Prop := B.pos.length + B.neg.length = 1

instance (B : Body A) : Decidable B.IsUnit := inferInstanceAs (Decidable (_ = 1))

theorem Body.isUnit_iff {B : Body A} : B.IsUnit ↔ (∃ a, B = ⟨[a], []⟩) ∨ ∃ b, B = ⟨[], [b]⟩ := by
  obtain ⟨pos, neg⟩ := B
  rcases pos with _ | ⟨a, _ | ⟨a', pos⟩⟩ <;> rcases neg with _ | ⟨b, _ | ⟨b', neg⟩⟩ <;>
    simp [Body.IsUnit]
  omega

/-- **The literal of a body**, which stands for it in every nogood: a unit body is its one literal,
`T a` for `a` and `F b` for `not b`; any other body is its variable, `T B`. -/
def Body.lit : Body A → Lit A
  | ⟨[a], []⟩ => tAtom a
  | ⟨[], [b]⟩ => fAtom b
  | B => tBody B

@[simp] theorem Body.lit_pos (a : A) : (⟨[a], []⟩ : Body A).lit = tAtom a := rfl

@[simp] theorem Body.lit_neg (b : A) : (⟨[], [b]⟩ : Body A).lit = fAtom b := rfl

theorem Body.lit_of_not_isUnit {B : Body A} (h : ¬ B.IsUnit) : B.lit = tBody B := by
  obtain ⟨pos, neg⟩ := B
  rcases pos with _ | ⟨a, _ | ⟨a', pos⟩⟩ <;> rcases neg with _ | ⟨b, _ | ⟨b', neg⟩⟩ <;>
    first | rfl | exact absurd (by simp [Body.IsUnit]) h

/-- The literal of a unit body holds exactly when the body does. -/
theorem Body.lit_sat_of_isUnit (v : Valuation A) {B : Body A} (h : B.IsUnit) :
    B.lit.Sat v ↔ B.Holds v.atoms v.atoms := by
  rcases Body.isUnit_iff.mp h with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;> simp [Body.Holds]

/-- The literal of a unit body is over an atom of the body. -/
theorem Body.lit_var_of_isUnit {B : Body A} (h : B.IsUnit) :
    ∃ a, B.lit.var = .atom a ∧ (a ∈ B.pos ∨ a ∈ B.neg) := by
  rcases Body.isUnit_iff.mp h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact ⟨a, rfl, .inl List.mem_cons_self⟩
  · exact ⟨b, rfl, .inr List.mem_cons_self⟩

namespace Program

variable (P : Program A)

/-- The atoms occurring in the program. -/
def atomSet : Set A := {a | ∃ r ∈ P, a = r.head ∨ a ∈ r.pos ∨ a ∈ r.neg}

/-! ### Falsum atoms -/

/-- A **falsum atom** heads some rule, and every rule for it negates it in its body: the head
`f` of integrity constraints `f :- B, not f`. -/
def Falsum (a : A) : Prop := (∃ r ∈ P, r.head = a) ∧ ∀ r ∈ P, r.head = a → a ∈ r.neg

/-- **No supported model holds a falsum atom**: a rule for it with a body true in the model
would have the atom both in the model and, negated, out of it. -/
theorem not_mem_of_falsum {M : Set A} (supported : P.Supported M) {a : A} (hf : P.Falsum a) : a ∉ M := by
  intro ha
  have derived : a ∈ P.step M M := by
    rw [supported]
    exact ha
  obtain ⟨r, hr, rfl, holds⟩ := derived
  exact holds.2 _ (hf.2 r hr rfl) ha

/-- **The body of a rule of a falsum atom, without the negated head, fails in every supported
model**: otherwise the whole body holds, since the head is false, and the rule derives its head. -/
theorem constraint_fails {M : Set A} (supported : P.Supported M) {r : Rule A} (hr : r ∈ P)
    (hf : P.Falsum r.head) : ¬ ((∀ b ∈ r.pos, b ∈ M) ∧ ∀ b ∈ r.neg, b ≠ r.head → b ∉ M) := by
  rintro ⟨pos, neg⟩
  have head := P.not_mem_of_falsum supported hf
  apply head
  rw [← supported]
  refine ⟨r, hr, rfl, pos, fun b hb hbM => ?_⟩
  by_cases same : b = r.head
  · exact head (same ▸ hbM)
  · exact neg b hb same hbM

/-- A total assignment of the program makes no atom outside the program true. -/
def Admissible (v : Valuation A) : Prop := ∀ a, v (.atom a) = true → a ∈ P.atomSet

/-- The literal of the body of every rule whose head is no falsum atom holds exactly when the body
does in the assignment's atoms. For a unit body this holds of every assignment, so only the body
variables are constrained (`bodiesCorrect_iff`); the bodies of the rules of falsum atoms are no
variables, so they carry nothing. -/
def BodiesCorrect (v : Valuation A) : Prop :=
  ∀ r ∈ P, ¬ P.Falsum r.head → (r.body.lit.Sat v ↔ r.Holds v.atoms v.atoms)

/-- **The body variables carry the truth values of their bodies**: correctness constrains exactly
the variables of the bodies that are not unit bodies. -/
theorem bodiesCorrect_iff (v : Valuation A) :
    P.BodiesCorrect v ↔
      ∀ r ∈ P, ¬ P.Falsum r.head → ¬ r.body.IsUnit → (v (.body r.body) = true ↔ r.Holds v.atoms v.atoms) := by
  refine forall₂_congr fun r _ => forall_congr' fun _ => ?_
  by_cases hu : r.body.IsUnit
  · simp only [hu, not_true_eq_false, false_imp_iff, iff_true]
    exact Body.lit_sat_of_isUnit v hu
  · simp only [hu, not_false_eq_true, forall_const, Body.lit_of_not_isUnit hu, tBody_sat]

/-- A nogood holds in every admissible total assignment whose atoms form a stable model. -/
def Entailed (lits : List (Lit A)) : Prop :=
  ∀ v, P.Admissible v → P.BodiesCorrect v → P.Stable v.atoms → ∃ l ∈ lits, ¬ l.Sat v

end Program

/-! ## Completion nogoods -/

section Completion

variable [DecidableEq A]

/-- The nogoods of one body: none for a unit body, which its literal stands for; otherwise
`{F B} ∪ B`, then `{T B, F a}` for each positive atom `a` and `{T B, T b}` for each negated atom `b`. -/
def bodyNogoods (B : Body A) : List (Nogood A) :=
  if B.IsUnit then [] else
    ⟨fBody B :: (B.pos.map tAtom ++ B.neg.map fAtom), .bodyTrue B⟩ ::
      (B.pos.map fun a => ⟨[tBody B, fAtom a], .bodyPos B a⟩) ++
      (B.neg.map fun b => ⟨[tBody B, tAtom b], .bodyNeg B b⟩)

/-- The nogood of one rule: a true body makes the head true. Its literals are the literal of the
body, then `F p`. -/
def headNogood (r : Rule A) : Nogood A := ⟨[r.body.lit, fAtom r.head], .head r⟩

/-- The group of a rule: its negated atoms other than its head, in order. -/
def Rule.group (r : Rule A) : List A := r.neg.filter (· != r.head)

@[simp] theorem Rule.mem_group {r : Rule A} {a : A} : a ∈ r.group ↔ a ∈ r.neg ∧ a ≠ r.head := by
  simp [Rule.group]

/-- The nogood of a rule of a falsum atom: its positive atoms true and its group false. -/
def constraintNogood (r : Rule A) : Nogood A := ⟨r.pos.map tAtom ++ r.group.map fAtom, .constraint r⟩

theorem constraintNogood_violated (v : Valuation A) (r : Rule A) :
    (constraintNogood r).Violated v ↔ (∀ b ∈ r.pos, b ∈ v.atoms) ∧ ∀ b ∈ r.group, b ∉ v.atoms := by
  simp only [Nogood.Violated, constraintNogood, List.forall_mem_append, List.forall_mem_map, tAtom_sat,
    fAtom_sat]

namespace Program

variable (P : Program A)

/-- The falsum test. -/
def falsum (a : A) : Bool := P.any (fun r => r.head == a) && P.all fun r => r.head != a || decide (a ∈ r.neg)

theorem falsum_iff {a : A} : P.falsum a = true ↔ P.Falsum a := by
  simp only [falsum, Falsum, Bool.and_eq_true, List.any_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq, decide_eq_true_eq]
  refine and_congr Iff.rfl (forall₂_congr fun r _ => ?_)
  constructor
  · exact fun h head => h.resolve_left (not_not.mpr head)
  · intro h
    by_cases head : r.head = a
    · exact .inr (h head)
    · exact .inl head

theorem falsum_eq_false_iff {a : A} : P.falsum a = false ↔ ¬ P.Falsum a := by
  rw [← P.falsum_iff, Bool.not_eq_true]

instance : DecidablePred P.Falsum := fun _ => decidable_of_iff _ P.falsum_iff

/-- The nogoods of one rule: for a rule of a falsum atom its constraint nogood, otherwise its head
nogood and its body's nogoods. -/
def ruleNogoods (r : Rule A) : List (Nogood A) :=
  if P.falsum r.head then [constraintNogood r] else headNogood r :: bodyNogoods r.body

/-- The rules whose bodies are solver variables: those of atoms that are not falsum atoms, whose
bodies are not unit bodies. -/
def bodyRules : Program A := P.filter fun r => !P.falsum r.head && !decide r.body.IsUnit

theorem mem_bodyRules {r : Rule A} : r ∈ P.bodyRules ↔ r ∈ P ∧ ¬ P.Falsum r.head ∧ ¬ r.body.IsUnit := by
  simp [bodyRules, ← P.falsum_iff]

/-- The atoms of the program, each once. -/
def allAtoms : List A := (P.flatMap fun r => r.head :: (r.pos ++ r.neg)).dedup

theorem mem_allAtoms {a : A} : a ∈ P.allAtoms ↔ a ∈ P.atomSet := by
  simp only [allAtoms, List.mem_dedup, List.mem_flatMap, List.mem_cons, List.mem_append, atomSet,
    Set.mem_ofPred_eq]

/-- The support nogood of an atom: `T a` alone for a falsum atom; otherwise a true atom has a true
body among its rules. Its literals are `T a`, then the complement of the literal of the body of each
rule for `a`, in rule order. -/
def supportNogood (a : A) : Nogood A :=
  if P.falsum a then ⟨[tAtom a], .support a⟩ else
    ⟨tAtom a :: (P.filter fun r => r.head = a).map fun r => r.body.lit.compl, .support a⟩

theorem supportNogood_violated (v : Valuation A) (a : A) :
    (P.supportNogood a).Violated v ↔
      a ∈ v.atoms ∧ (¬ P.Falsum a → ∀ r ∈ P, r.head = a → ¬ r.body.lit.Sat v) := by
  by_cases hf : P.falsum a = true
  · have := (P.falsum_iff).mp hf
    simp [Nogood.Violated, supportNogood, hf, this]
  · have := (P.falsum_eq_false_iff).mp (Bool.eq_false_iff.mpr hf)
    simp only [Nogood.Violated, supportNogood, hf, Bool.false_eq_true, ↓reduceIte, List.forall_mem_cons,
      tAtom_sat, List.forall_mem_map, List.mem_filter, decide_eq_true_eq, Lit.sat_compl, and_imp, this,
      not_false_eq_true, forall_const]

/-- **The completion nogoods** of the program: the nogoods of each rule in order, then the support
nogoods in atom order. -/
def completionNogoods : List (Nogood A) := P.flatMap P.ruleNogoods ++ P.allAtoms.map P.supportNogood

/-- A total assignment violating no completion nogood. -/
def CompletionSolution (v : Valuation A) : Prop := ∀ δ ∈ P.completionNogoods, ¬ δ.Violated v

omit [DecidableEq A] in
/-- The nogoods of a body hold exactly when the body's literal holds exactly when the body does:
for a unit body always, and otherwise when its variable carries its truth value. -/
theorem bodyNogoods_ok_iff (v : Valuation A) (B : Body A) :
    (∀ δ ∈ bodyNogoods B, ¬ δ.Violated v) ↔ (B.lit.Sat v ↔ B.Holds v.atoms v.atoms) := by
  by_cases hu : B.IsUnit
  · simp only [bodyNogoods, if_pos hu, List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    exact Body.lit_sat_of_isUnit v hu
  rw [Body.lit_of_not_isUnit hu, tBody_sat]
  simp only [bodyNogoods, if_neg hu, List.forall_mem_cons, List.forall_mem_append, List.forall_mem_map]
  have first : ¬ (⟨fBody B :: (B.pos.map tAtom ++ B.neg.map fAtom), .bodyTrue B⟩ : Nogood A).Violated v ↔
      (B.Holds v.atoms v.atoms → v (.body B) = true) := by
    simp only [Nogood.Violated, List.forall_mem_cons, List.forall_mem_append, List.forall_mem_map,
      fBody_sat, tAtom_sat, fAtom_sat, Body.Holds]
    cases v (.body B) <;> simp
  have positive : (∀ a ∈ B.pos, ¬ (⟨[tBody B, fAtom a], .bodyPos B a⟩ : Nogood A).Violated v) ↔
      (v (.body B) = true → ∀ a ∈ B.pos, a ∈ v.atoms) := by
    simp only [Nogood.Violated, List.forall_mem_cons, tBody_sat, fAtom_sat, List.not_mem_nil,
      false_imp_iff, implies_true, and_true, not_and, not_not]
    exact ⟨fun h hB a ha => h a ha hB, fun h a ha hB => h hB a ha⟩
  have negative : (∀ b ∈ B.neg, ¬ (⟨[tBody B, tAtom b], .bodyNeg B b⟩ : Nogood A).Violated v) ↔
      (v (.body B) = true → ∀ b ∈ B.neg, b ∉ v.atoms) := by
    simp only [Nogood.Violated, List.forall_mem_cons, tBody_sat, tAtom_sat, List.not_mem_nil,
      false_imp_iff, implies_true, and_true, not_and]
    exact ⟨fun h hB b hb => h b hb hB, fun h b hb hB => h hB b hb⟩
  rw [first, positive, negative, Body.Holds]
  constructor
  · rintro ⟨⟨back, pos⟩, neg⟩
    exact ⟨fun hB => ⟨pos hB, neg hB⟩, back⟩
  · intro h
    exact ⟨⟨h.mpr, fun hB => (h.mp hB).1⟩, fun hB => (h.mp hB).2⟩

omit [DecidableEq A] in
theorem headNogood_violated (v : Valuation A) (r : Rule A) :
    (headNogood r).Violated v ↔ r.body.lit.Sat v ∧ r.head ∉ v.atoms := by
  simp [Nogood.Violated, headNogood]

/-- The nogoods of a rule hold: for a rule of a falsum atom its constraint nogood, otherwise its
head nogood and its body's nogoods. -/
theorem ruleNogoods_ok_iff (v : Valuation A) (r : Rule A) :
    (∀ δ ∈ P.ruleNogoods r, ¬ δ.Violated v) ↔
      if P.falsum r.head then ¬ (constraintNogood r).Violated v
      else ¬ (headNogood r).Violated v ∧ ∀ δ ∈ bodyNogoods r.body, ¬ δ.Violated v := by
  by_cases hf : P.falsum r.head = true <;> simp [ruleNogoods, hf]

theorem completionSolution_iff_parts (v : Valuation A) :
    P.CompletionSolution v ↔
      (∀ r ∈ P, ∀ δ ∈ P.ruleNogoods r, ¬ δ.Violated v) ∧ ∀ a ∈ P.allAtoms, ¬ (P.supportNogood a).Violated v := by
  simp only [CompletionSolution, completionNogoods, List.mem_append, List.mem_flatMap, List.mem_map]
  constructor
  · intro h
    exact ⟨fun r hr δ hδ => h _ (Or.inl ⟨r, hr, hδ⟩), fun a ha => h _ (Or.inr ⟨a, ha, rfl⟩)⟩
  · rintro ⟨rules, supports⟩ δ (⟨r, hr, hδ⟩ | ⟨a, ha, rfl⟩)
    · exact rules r hr δ hδ
    · exact supports a ha

theorem falsum_ne_true {a : A} (h : ¬ P.Falsum a) : ¬ P.falsum a = true := by
  rwa [Bool.not_eq_true, P.falsum_eq_false_iff]

/-- **Completion nogoods characterize supported models**: an admissible total assignment
violates no completion nogood exactly when its atoms form a supported model and its body
variables are correct. -/
theorem completionSolution_iff (v : Valuation A) (admissible : P.Admissible v) :
    P.CompletionSolution v ↔ P.Supported v.atoms ∧ P.BodiesCorrect v := by
  rw [completionSolution_iff_parts]
  constructor
  · rintro ⟨rules, supports⟩
    have ok : ∀ r ∈ P, ¬ P.Falsum r.head →
        ¬ (headNogood r).Violated v ∧ ∀ δ ∈ bodyNogoods r.body, ¬ δ.Violated v := by
      intro r hr hf
      have := (P.ruleNogoods_ok_iff v r).mp (rules r hr)
      rwa [if_neg (P.falsum_ne_true hf)] at this
    have correct : P.BodiesCorrect v := fun r hr hf => (bodyNogoods_ok_iff v r.body).mp (ok r hr hf).2
    refine ⟨Set.Subset.antisymm ?_ ?_, correct⟩
    · rintro a ⟨r, hr, rfl, holds⟩
      by_cases hf : P.Falsum r.head
      · have := (P.ruleNogoods_ok_iff v r).mp (rules r hr)
        rw [if_pos ((P.falsum_iff).mpr hf), constraintNogood_violated] at this
        exact absurd ⟨holds.1, fun b hb => holds.2 b (Rule.mem_group.mp hb).1⟩ this
      · have head := (ok r hr hf).1
        rw [headNogood_violated, not_and, not_not] at head
        exact head ((correct r hr hf).mpr holds)
    · intro a present
      have support := supports a ((P.mem_allAtoms).mpr (admissible a present))
      rw [supportNogood_violated] at support
      simp only [present, true_and, Classical.not_imp, not_forall] at support
      obtain ⟨hf, r, hr, head, bodyTrue⟩ := support
      subst head
      exact ⟨r, hr, rfl, (correct r hr hf).mp (not_not.mp bodyTrue)⟩
  · rintro ⟨supported, correct⟩
    refine ⟨fun r hr => (P.ruleNogoods_ok_iff v r).mpr ?_, fun a _ violated => ?_⟩
    · by_cases hf : P.Falsum r.head
      · rw [if_pos ((P.falsum_iff).mpr hf), constraintNogood_violated]
        rintro ⟨pos, group⟩
        exact P.constraint_fails supported hr hf ⟨pos, fun b hb hbh => group b (Rule.mem_group.mpr ⟨hb, hbh⟩)⟩
      · rw [if_neg (P.falsum_ne_true hf)]
        refine ⟨?_, (bodyNogoods_ok_iff v r.body).mpr (correct r hr hf)⟩
        rw [headNogood_violated]
        rintro ⟨bodyTrue, notHead⟩
        apply notHead
        rw [← supported]
        exact ⟨r, hr, rfl, (correct r hr hf).mp bodyTrue⟩
    · rw [supportNogood_violated] at violated
      obtain ⟨present, bodies⟩ := violated
      by_cases hf : P.Falsum a
      · exact P.not_mem_of_falsum supported hf present
      · have derived : a ∈ P.step v.atoms v.atoms := by
          rw [supported]
          exact present
        obtain ⟨r, hr, head, holds⟩ := derived
        exact bodies hf r hr head ((correct r hr (head ▸ hf)).mpr holds)

theorem embed_mem_completionTable {a : A} (h : a ∈ P.atomSet) : embed a ∈ P.completionTable.atoms := by
  obtain ⟨r, hr, ha⟩ := h
  apply List.mem_dedup.mpr
  apply List.mem_append_left
  apply List.mem_append_right
  refine List.mem_flatMap.mpr ⟨r.toClause, List.mem_map_of_mem hr, ?_⟩
  simpa [ClarkCompletion.clauseAtoms, Rule.toClause, ClarkCompletion.goalAtoms, or_comm, or_left_comm] using ha

/-- The values of a total assignment on the atom table of Clark's completion. -/
def tableValues (v : Valuation A) : Fin P.completionTable.atoms.length → Bool :=
  fun i => v (.atom (groundEquiv (P.completionTable.atoms.get i)))

theorem unlift_tableValues (v : Valuation A) (admissible : P.Admissible v) :
    unlift (P.completionTable.interpretation (P.tableValues v)) = v.atoms := by
  ext a
  change P.completionTable.read (P.tableValues v) (embed a) = true ↔ v (.atom a) = true
  unfold ClarkCompletion.AtomTable.read
  constructor
  · intro h
    split_ifs at h with member
    have same := ClarkCompletion.AtomTable.at_index P.completionTable (embed a) member
    simp only [tableValues, same, groundEquiv_embed] at h
    exact h
  · intro h
    have member := P.embed_mem_completionTable (admissible a h)
    have same := ClarkCompletion.AtomTable.at_index P.completionTable (embed a) member
    rw [dif_pos member]
    simp only [tableValues, same, groundEquiv_embed]
    exact h

/-- **Completion nogoods are Clark's completion**: an admissible total assignment violates no
completion nogood exactly when its atoms satisfy the completion formula of
`ClarkCompletion` and its body variables are correct. -/
theorem completionSolution_iff_clark (v : Valuation A) (admissible : P.Admissible v) :
    P.CompletionSolution v ↔
      PropositionalTseitin.eval (Fin.addCases Fin.elim0 (P.tableValues v))
          (ClarkCompletion.completion P.completionTable Fin.elim0 P.clauses) = true ∧ P.BodiesCorrect v := by
  rw [completionSolution_iff P v admissible, completion_iff_supported, unlift_tableValues P v admissible]

open Classical in
/-- The total assignment of a set of atoms: atoms by membership, bodies by their truth. -/
noncomputable def canonical (M : Set A) : Valuation A
  | .atom a => decide (a ∈ M)
  | .body B => decide (B.Holds M M)

omit [DecidableEq A] in
@[simp] theorem canonical_atoms (M : Set A) : (canonical M).atoms = M := by
  ext a
  simp [Valuation.atoms, canonical]

omit [DecidableEq A] in
theorem canonical_admissible {M : Set A} (within : M ⊆ P.atomSet) : P.Admissible (canonical M) := by
  intro a h
  apply within
  simpa [canonical] using h

omit [DecidableEq A] in
open Classical in
/-- The literal of a body holds in the canonical assignment exactly when the body does: for a unit
body by its atom, otherwise by its variable. -/
theorem lit_sat_canonical (M : Set A) (B : Body A) : B.lit.Sat (canonical M) ↔ B.Holds M M := by
  by_cases hu : B.IsUnit
  · rw [Body.lit_sat_of_isUnit _ hu, canonical_atoms]
  · rw [Body.lit_of_not_isUnit hu, tBody_sat]
    exact decide_eq_true_iff

omit [DecidableEq A] in
theorem canonical_bodiesCorrect (M : Set A) : P.BodiesCorrect (canonical M) := by
  intro r _ _
  rw [canonical_atoms]
  exact lit_sat_canonical M r.body

omit [DecidableEq A] in
theorem headSet_subset_atomSet : P.headSet ⊆ P.atomSet := fun _ ⟨r, hr, head⟩ => ⟨r, hr, Or.inl head.symm⟩

/-- Every supported model is the atom set of a completion solution. -/
theorem completionSolution_canonical {M : Set A} (supported : P.Supported M) :
    P.CompletionSolution (canonical M) := by
  have within : M ⊆ P.atomSet := supported ▸ (P.step_subset_headSet M M).trans P.headSet_subset_atomSet
  rw [completionSolution_iff _ _ (P.canonical_admissible within)]
  exact ⟨by rw [canonical_atoms]; exact supported, P.canonical_bodiesCorrect M⟩

end Program

end Completion

/-! ## Loop nogoods -/

section Loops

variable [DecidableEq A]

instance (L : Finset A) (r : Rule A) : Decidable (Program.ExternalFor L r) := by
  unfold Program.ExternalFor
  infer_instance

namespace Program

variable (P : Program A)

/-- The bodies of the rules supporting `U` from outside. -/
def externalBodies (U : Finset A) : List (Body A) := (P.filter fun r => ExternalFor U r).map Rule.body

/-- **The loop nogood** of `a ∈ U`: `a` is not true while every external body of `U` is false. Its
literals are `T a`, then the complement of the literal of each external body, in rule order. -/
def loopNogood (U : Finset A) (a : A) : Nogood A :=
  ⟨tAtom a :: (P.externalBodies U).map fun B => B.lit.compl, .loop U a⟩

theorem loopNogood_length_le (U : Finset A) (a : A) : (P.loopNogood U a).lits.length ≤ P.length + 1 := by
  simp only [loopNogood, List.length_cons, List.length_map, externalBodies]
  exact Nat.succ_le_succ (List.length_filter_le _ _)

theorem loopNogood_violated (v : Valuation A) (U : Finset A) (a : A) :
    (P.loopNogood U a).Violated v ↔ a ∈ v.atoms ∧ ∀ r ∈ P, ExternalFor U r → ¬ r.body.lit.Sat v := by
  simp only [Nogood.Violated, loopNogood, externalBodies, List.forall_mem_cons, tAtom_sat,
    List.forall_mem_map, List.mem_filter, decide_eq_true_eq, Lit.sat_compl, and_imp]

/-- All loop nogoods hold. -/
def LoopSolution (v : Valuation A) : Prop := ∀ (U : Finset A), ∀ a ∈ U, ¬ (P.loopNogood U a).Violated v

theorem loopNogoods_ok_iff (v : Valuation A) (correct : P.BodiesCorrect v) (U : Finset A)
    (noFalsum : ∀ b ∈ U, ¬ P.Falsum b) :
    (∀ a ∈ U, ¬ (P.loopNogood U a).Violated v) ↔ P.LoopSatisfied v.atoms U := by
  simp only [loopNogood_violated, not_and, not_forall, LoopSatisfied, ExternalSupport]
  constructor
  · rintro h ⟨a, ha, present⟩
    obtain ⟨r, hr, external, bodyTrue⟩ := h a ha present
    exact ⟨r, hr, external, (correct r hr (noFalsum _ external.1)).mp (not_not.mp bodyTrue)⟩
  · rintro h a ha present
    obtain ⟨r, hr, external, holds⟩ := h ⟨a, ha, present⟩
    exact ⟨r, hr, external, not_not.mpr ((correct r hr (noFalsum _ external.1)).mpr holds)⟩

/-- **The loop nogoods of the sets without falsum atoms make a supported model stable**: a set
with falsum atoms has the external support of its other atoms, since a supported model holds no
falsum atom, so none is a positive atom of a supporting rule. -/
theorem stable_of_loops (v : Valuation A) (correct : P.BodiesCorrect v) (supported : P.Supported v.atoms)
    (loops : ∀ U : Finset A, (∀ b ∈ U, ¬ P.Falsum b) → ∀ a ∈ U, ¬ (P.loopNogood U a).Violated v) :
    P.Stable v.atoms := by
  rw [stable_iff_supported_loops]
  refine ⟨supported, fun L _ => ?_⟩
  set L' := L.filter fun b => P.falsum b = false
  have noFalsum : ∀ b ∈ L', ¬ P.Falsum b := fun b hb =>
    (P.falsum_eq_false_iff).mp (Finset.mem_filter.mp hb).2
  have satisfied := (P.loopNogoods_ok_iff v correct L' noFalsum).mp (loops L' noFalsum)
  rintro ⟨a, ha, present⟩
  have notFalsum : ¬ P.Falsum a := fun hf => P.not_mem_of_falsum supported hf present
  obtain ⟨r, hr, external, holds⟩ :=
    satisfied ⟨a, Finset.mem_filter.mpr ⟨ha, (P.falsum_eq_false_iff).mpr notFalsum⟩, present⟩
  refine ⟨r, hr, ⟨(Finset.mem_filter.mp external.1).1, fun b hb inside => ?_⟩, holds⟩
  have bFalsum : ¬ P.Falsum b := fun hf => P.not_mem_of_falsum supported hf (holds.1 b hb)
  exact external.2 b hb (Finset.mem_filter.mpr ⟨inside, (P.falsum_eq_false_iff).mpr bFalsum⟩)

/-- **Loop nogoods characterize stability among supported models.** -/
theorem loopSolution_iff_stable (v : Valuation A) (correct : P.BodiesCorrect v) (supported : P.Supported v.atoms) :
    P.LoopSolution v ↔ P.Stable v.atoms := by
  constructor
  · exact fun loops => P.stable_of_loops v correct supported fun U _ => loops U
  · intro stable U a ha violated
    rw [loopNogood_violated] at violated
    obtain ⟨r, hr, external, holds⟩ := P.stable_external stable U ⟨a, ha, violated.1⟩
    have head : r.head ∈ v.atoms := by
      rw [← supported]
      exact ⟨r, hr, rfl, holds⟩
    have notFalsum : ¬ P.Falsum r.head := fun hf => P.not_mem_of_falsum supported hf head
    exact violated.2 r hr external ((correct r hr notFalsum).mpr holds)

/-- **The solutions of the completion and loop nogoods are exactly the stable models.** -/
theorem solution_iff_stable (v : Valuation A) (admissible : P.Admissible v) :
    P.CompletionSolution v ∧ P.LoopSolution v ↔ P.Stable v.atoms ∧ P.BodiesCorrect v := by
  rw [completionSolution_iff P v admissible]
  constructor
  · rintro ⟨⟨supported, correct⟩, loops⟩
    exact ⟨(P.loopSolution_iff_stable v correct supported).mp loops, correct⟩
  · rintro ⟨stable, correct⟩
    have supported := P.stable_supported stable
    exact ⟨⟨supported, correct⟩, (P.loopSolution_iff_stable v correct supported).mpr stable⟩

/-! ## Entailment -/

theorem entailed_of_solution {lits : List (Lit A)}
    (h : ∀ v, P.Admissible v → P.CompletionSolution v → P.LoopSolution v → ∃ l ∈ lits, ¬ l.Sat v) :
    P.Entailed lits := by
  intro v admissible correct stable
  have := (P.solution_iff_stable v admissible).mpr ⟨stable, correct⟩
  exact h v admissible this.1 this.2

theorem completionNogood_entailed {δ : Nogood A} (h : δ ∈ P.completionNogoods) : P.Entailed δ.lits :=
  P.entailed_of_solution fun _ _ solution _ => Nogood.not_violated_iff.mp (solution δ h)

theorem loopNogood_entailed (U : Finset A) {a : A} (ha : a ∈ U) : P.Entailed (P.loopNogood U a).lits :=
  P.entailed_of_solution fun _ _ _ loops => Nogood.not_violated_iff.mp (loops U a ha)

omit [DecidableEq A] in
/-- A superset of an entailed nogood is entailed. -/
theorem Entailed.weaken {lits lits' : List (Lit A)} (h : P.Entailed lits) (sub : ∀ l ∈ lits, l ∈ lits') :
    P.Entailed lits' := by
  intro v admissible correct stable
  obtain ⟨l, hl, notSat⟩ := h v admissible correct stable
  exact ⟨l, sub l hl, notSat⟩

/-- **Resolution preserves entailment**: from nogoods containing `l` and its complement, the
union of the rest is entailed. This is the step of conflict analysis. -/
theorem Entailed.resolve {left right : List (Lit A)} (l : Lit A) (hl : P.Entailed left)
    (hr : P.Entailed right) :
    P.Entailed (left.erase l ++ right.erase l.compl) := by
  intro v admissible correct stable
  obtain ⟨m, hm, notM⟩ := hl v admissible correct stable
  obtain ⟨n, hn, notN⟩ := hr v admissible correct stable
  by_cases same : m = l
  · subst m
    by_cases same' : n = l.compl
    · subst n
      exact absurd ((Lit.sat_compl v l).mpr notM) notN
    · exact ⟨n, List.mem_append_right _ ((List.mem_erase_of_ne same').mpr hn), notN⟩
  · exact ⟨m, List.mem_append_left _ ((List.mem_erase_of_ne same).mpr hm), notM⟩

end Program

end Loops

/-! ## Partial assignments and unfounded sets -/

section Partial

variable [DecidableEq A]

namespace Program

variable (P : Program A)

/-- A set `U` is unfounded with respect to the literals assigned so far when every rule for an
atom of `U` has an assigned false body (the complement of its literal is assigned) or a positive
body atom in `U`. -/
def UnfoundedBy (assigned : List (Lit A)) (U : Finset A) : Prop :=
  ∀ r ∈ P, r.head ∈ U → r.body.lit.compl ∈ assigned ∨ ∃ b ∈ r.pos, b ∈ U

/-- **Unfounded-set propagation has a compact reason.** If `U` is unfounded, every literal of
the loop nogood of `a ∈ U` other than `T a` is assigned, so the loop nogood is the reason for
`F a`. -/
theorem loopNogood_unit_of_unfounded {assigned : List (Lit A)} {U : Finset A}
    (unfounded : P.UnfoundedBy assigned U) (a : A) :
    ∀ l ∈ (P.loopNogood U a).lits, l ≠ tAtom a → l ∈ assigned := by
  intro l hl ne
  simp only [loopNogood, List.mem_cons, externalBodies, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hl
  rcases hl with rfl | ⟨_, ⟨r, ⟨hr, external⟩, rfl⟩, rfl⟩
  · exact absurd rfl ne
  · rcases unfounded r hr external.1 with assignedFalse | ⟨b, hb, inside⟩
    · exact assignedFalse
    · exact absurd inside (external.2 b hb)

end Program

end Partial

/-! ## Executable checks -/

section Executable

variable [DecidableEq A]

instance (v : Valuation A) (δ : Nogood A) : Decidable (δ.Violated v) := by
  unfold Nogood.Violated
  infer_instance

/-- The total assignment of a finite set of atoms, computed: the canonical assignment. -/
def finValuation (M : Finset A) : Valuation A
  | .atom a => decide (a ∈ M)
  | .body B => B.pos.all (· ∈ M) && B.neg.all (· ∉ M)

theorem finValuation_eq_canonical (M : Finset A) : finValuation M = Program.canonical ↑M := by
  funext x
  apply Bool.eq_iff_iff.mpr
  cases x with
  | atom a => simp [finValuation, Program.canonical]
  | body B => simp [finValuation, Program.canonical, Body.Holds]

namespace Program

variable (P : Program A)

instance (v : Valuation A) : Decidable (P.CompletionSolution v) := by
  unfold CompletionSolution
  infer_instance

instance (assigned : List (Lit A)) (U : Finset A) : Decidable (P.UnfoundedBy assigned U) := by
  unfold UnfoundedBy
  infer_instance

end Program

end Executable

end Mettapedia.Logic.ASP
