import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOutcomes

/-!
# Rule modules and their call-by-value semantics

A rule module is a set of first-order rewrite rules for judgments, indexed by labels. A rule
`L : P1 .. Pn |- J(p) ~> r` has a left side, premises in order and a right side. A premise is a call
`K(a) ~> t` (the call `K(a)` has a value matching `t`) or a relation query `R(a)` (a row of the given
relation matches it). Calls nested in arguments are taken as flattened into premises already: every
term here is data, and only a call premise asks for a derivation.

* `Derives M Rel C w`: the call `C` has the value `w`. Some rule's left side matches `C`, each
  premise holds, and `w` is the right side, all under one substitution. Read in order, the premises
  bind the variables of their targets (`ModuleRule.bound`); under range restriction the one
  substitution is the growing one of the premises read in order.
* `Demanded M Rel C₀`: the calls asked from `C₀`. A rule matching a demanded call asks premise `i`'s
  call once premises `1 .. i-1` hold.
* `RangeRestricted`: a call's arguments and the right side use only variables already bound; it is
  equivalent to the reading's own check, premise by premise (`rangeRestricted_iff_boundOk`).
* `QueriesBound`: a relation query binds no new variable. `Exclusive`: two different rules never both
  hold at one call.

Terms are first-order terms of `Mettapedia.Logic.LP`. The terms of a module that is read live in
`readingSignature σ L`, whose function symbols (`Head`) are the module's constructors and relations
and the heads of the rows of its reading; the semantics itself is stated for any signature.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open SetStoreSyntax (apply_eq_of_agree agree_of_apply_eq)

universe u

/-! ## The terms of a module and of its reading -/

/-- The function symbols of a module's terms and of its reading's rows: the module's constructors
and relation symbols, and the reading's heads `demand` (`(demand C)`), `value` (`(value C w)`) and
`stage L i` (`(L/i C t1 .. ti)`). -/
inductive Head (F R L : Type u) where
  | con (f : F)
  | rel (r : R)
  | demand
  | value
  | stage (rule : L) (index : ℕ)
  deriving DecidableEq

/-- Arities: a constructor's and a relation's own, one for `demand`, two for `value`, and `i + 1`
for the stage `L/i` (the call and `i` targets). -/
def Head.arity {F R L : Type u} (conArity : F → ℕ) (relArity : R → ℕ) : Head F R L → ℕ
  | .con f => conArity f
  | .rel r => relArity r
  | .demand => 1
  | .value => 2
  | .stage _ i => i + 1

/-- The signature of a module whose rules are labelled by `L`, over the constructors, relations,
constants and variables of `σ`: a relation symbol also heads its rows (`Head.rel`). -/
abbrev readingSignature (σ : LPSignature.{u, u, u, u}) (L : Type u) : LPSignature.{u, u, u, u} where
  constants := σ.constants
  vars := σ.vars
  relationSymbols := σ.relationSymbols
  relationArity := σ.relationArity
  functionSymbols := Head σ.functionSymbols σ.relationSymbols L
  functionArity := Head.arity σ.functionArity σ.relationArity

/-! ## Modules -/

section Module

variable {ρ : LPSignature}

/-- A premise: a call `source ~> target`, or a relation query. -/
inductive Premise (ρ : LPSignature) where
  | call (source target : Term ρ)
  | query (atom : Atom ρ)

/-- A module rule `P1 .. Pn |- lhs ~> rhs`, its premises in order. -/
structure ModuleRule (ρ : LPSignature) where
  lhs : Term ρ
  premises : List (Premise ρ)
  rhs : Term ρ

section Variables

variable [DecidableEq ρ.vars]

/-- The variables a premise binds: those of a call's target, or of a query. -/
def Premise.binds : Premise ρ → Finset ρ.vars
  | .call _ target => target.freeVars
  | .query atom => atom.freeVars

/-- The variables of a premise. -/
def Premise.vars : Premise ρ → Finset ρ.vars
  | .call source target => source.freeVars ∪ target.freeVars
  | .query atom => atom.freeVars

/-- The variables premises bind. -/
def bindsAll : List (Premise ρ) → Finset ρ.vars
  | [] => ∅
  | p :: rest => p.binds ∪ bindsAll rest

theorem bindsAll_append (pre post : List (Premise ρ)) :
    bindsAll (pre ++ post) = bindsAll pre ∪ bindsAll post := by
  induction pre with
  | nil => simp [bindsAll]
  | cons p rest ih => simp [bindsAll, ih, Finset.union_assoc]

theorem binds_subset_bindsAll {p : Premise ρ} {ps : List (Premise ρ)} (member : p ∈ ps) :
    p.binds ⊆ bindsAll ps := by
  induction ps with
  | nil => cases member
  | cons q rest ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · exact Finset.subset_union_left
    · exact (ih inside).trans Finset.subset_union_right

/-- The variables bound once the left side has matched and the premises `pre` have held. -/
def ModuleRule.bound (r : ModuleRule ρ) (pre : List (Premise ρ)) : Finset ρ.vars :=
  r.lhs.freeVars ∪ bindsAll pre

/-- **Range restriction**: a call's arguments, and the right side, use only variables bound by the
left side or an earlier premise. -/
structure RangeRestricted (r : ModuleRule ρ) : Prop where
  calls : ∀ pre source target post, r.premises = pre ++ Premise.call source target :: post →
    source.freeVars ⊆ r.bound pre
  rhs : r.rhs.freeVars ⊆ r.bound r.premises

/-- **No relation query binds a new variable**: a query's variables are already bound. -/
def QueriesBound (r : ModuleRule ρ) : Prop :=
  ∀ pre atom post, r.premises = pre ++ Premise.query atom :: post → atom.freeVars ⊆ r.bound pre

/-- The reading's own check, premise by premise: a call's arguments are bound, its target and a
query bind their variables, and finally the right side is bound. -/
def BoundOk : Finset ρ.vars → List (Premise ρ) → Term ρ → Prop
  | bound, [], rhs => rhs.freeVars ⊆ bound
  | bound, .call source target :: rest, rhs =>
      source.freeVars ⊆ bound ∧ BoundOk (bound ∪ target.freeVars) rest rhs
  | bound, .query atom :: rest, rhs => BoundOk (bound ∪ atom.freeVars) rest rhs

theorem boundOk_iff (rhs : Term ρ) : ∀ (start : Finset ρ.vars) (ps : List (Premise ρ)),
    BoundOk start ps rhs ↔
      (∀ pre source target post, ps = pre ++ Premise.call source target :: post →
        source.freeVars ⊆ start ∪ bindsAll pre) ∧ rhs.freeVars ⊆ start ∪ bindsAll ps
  | start, [] => by
    simp only [BoundOk, bindsAll, Finset.union_empty]
    constructor
    · intro bounded
      refine ⟨fun pre source target post split => ?_, bounded⟩
      exact absurd split.symm (by simp)
    · exact fun both => both.2
  | start, .call source target :: rest => by
    simp only [BoundOk, boundOk_iff rhs (start ∪ target.freeVars) rest, bindsAll, Premise.binds,
      Finset.union_assoc]
    constructor
    · rintro ⟨first, later, final⟩
      refine ⟨fun pre s t post split => ?_, final⟩
      rcases pre with _ | ⟨p, pre⟩
      · obtain ⟨⟨rfl, rfl⟩, -⟩ : (source = s ∧ target = t) ∧ rest = post := by simpa using split
        simpa [bindsAll] using first
      · obtain ⟨rfl, rest_split⟩ : .call source target = p ∧ rest = pre ++ .call s t :: post := by
          simpa using split
        simpa [bindsAll, Premise.binds, Finset.union_assoc] using later pre s t post rest_split
    · rintro ⟨calls, final⟩
      refine ⟨by simpa [bindsAll] using calls [] source target rest rfl, ?_, final⟩
      intro pre s t post split
      simpa [bindsAll, Premise.binds, Finset.union_assoc] using
        calls (.call source target :: pre) s t post (by simp [split])
  | start, .query atom :: rest => by
    simp only [BoundOk, boundOk_iff rhs (start ∪ atom.freeVars) rest, bindsAll, Premise.binds,
      Finset.union_assoc]
    constructor
    · rintro ⟨later, final⟩
      refine ⟨fun pre s t post split => ?_, final⟩
      rcases pre with _ | ⟨p, pre⟩
      · simp at split
      · obtain ⟨rfl, rest_split⟩ : .query atom = p ∧ rest = pre ++ .call s t :: post := by
          simpa using split
        simpa [bindsAll, Premise.binds, Finset.union_assoc] using later pre s t post rest_split
    · rintro ⟨calls, final⟩
      refine ⟨fun pre s t post split => ?_, final⟩
      simpa [bindsAll, Premise.binds, Finset.union_assoc] using
        calls (.query atom :: pre) s t post (by simp [split])

/-- Range restriction is the reading's check (`tcalc-module:bound-ok` in `lib/tcalc_modules.metta`). -/
theorem rangeRestricted_iff_boundOk (r : ModuleRule ρ) :
    RangeRestricted r ↔ BoundOk r.lhs.freeVars r.premises r.rhs := by
  rw [boundOk_iff]
  exact ⟨fun rr => ⟨rr.calls, rr.rhs⟩, fun both => ⟨both.1, both.2⟩⟩

/-- Under range restriction, the variables of a premise that has held are bound. -/
theorem vars_subset_bound {r : ModuleRule ρ} (rr : RangeRestricted r) {pre post : List (Premise ρ)}
    (split : r.premises = pre ++ post) {p : Premise ρ} (member : p ∈ pre) :
    p.vars ⊆ r.bound pre := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem member
  have bindsInside : p.binds ⊆ bindsAll (before ++ p :: after) :=
    binds_subset_bindsAll (List.mem_append_right _ List.mem_cons_self)
  have earlier : r.bound before ⊆ r.bound (before ++ p :: after) := by
    unfold ModuleRule.bound
    rw [bindsAll_append]
    exact Finset.union_subset_union (Finset.Subset.refl _) Finset.subset_union_left
  cases p with
  | call source target =>
    have sourceBound := rr.calls before source target (after ++ post) (by simp [split])
    refine Finset.union_subset (sourceBound.trans earlier) ?_
    exact bindsInside.trans Finset.subset_union_right
  | query atom => exact bindsInside.trans Finset.subset_union_right

end Variables

/-! ## Semantics -/

variable {L : Type*}

/-- **The call-by-value semantics**: `Derives M Rel C w` when a rule's left side matches the call `C`,
each of its premises holds (a call by a derivation of its instance whose value is the target's
instance; a query by a row of `Rel`), and `w` is the right side, all under one substitution. -/
inductive Derives (M : L → ModuleRule ρ) (Rel : Set (Atom ρ)) : Term ρ → Term ρ → Prop
  | rule (l : L) (θ : Subst ρ)
      (calls : ∀ source target, Premise.call source target ∈ (M l).premises →
        Derives M Rel (θ.applyTerm source) (θ.applyTerm target))
      (queries : ∀ atom, Premise.query atom ∈ (M l).premises → θ.applyAtom atom ∈ Rel) :
      Derives M Rel (θ.applyTerm (M l).lhs) (θ.applyTerm (M l).rhs)

/-- A premise holds under a substitution. -/
def Holds (M : L → ModuleRule ρ) (Rel : Set (Atom ρ)) (θ : Subst ρ) : Premise ρ → Prop
  | .call source target => Derives M Rel (θ.applyTerm source) (θ.applyTerm target)
  | .query atom => θ.applyAtom atom ∈ Rel

theorem derives_iff {M : L → ModuleRule ρ} {Rel : Set (Atom ρ)} {C w : Term ρ} :
    Derives M Rel C w ↔ ∃ l θ, C = θ.applyTerm (M l).lhs ∧ w = θ.applyTerm (M l).rhs ∧
      ∀ p ∈ (M l).premises, Holds M Rel θ p := by
  constructor
  · rintro ⟨l, θ, calls, queries⟩
    refine ⟨l, θ, rfl, rfl, fun p member => ?_⟩
    cases p with
    | call source target => exact calls source target member
    | query atom => exact queries atom member
  · rintro ⟨l, θ, rfl, rfl, holds⟩
    exact .rule l θ (fun source target member => holds _ member) (fun atom member => holds _ member)

/-- **The calls asked from `C₀`**: `C₀`, and the call of premise `i` of a rule whose left side
matches a demanded call, once its premises `1 .. i-1` hold under the same substitution. -/
inductive Demanded (M : L → ModuleRule ρ) (Rel : Set (Atom ρ)) (C₀ : Term ρ) : Term ρ → Prop
  | seed : Demanded M Rel C₀ C₀
  | call {l : L} {θ : Subst ρ} {pre post : List (Premise ρ)} {source target : Term ρ} :
      Demanded M Rel C₀ (θ.applyTerm (M l).lhs) →
      (M l).premises = pre ++ Premise.call source target :: post →
      (∀ p ∈ pre, Holds M Rel θ p) →
      Demanded M Rel C₀ (θ.applyTerm source)

/-- **Semantic exclusivity**: two different rules whose left sides match one call never both have all
their premises hold there. -/
def Exclusive (M : L → ModuleRule ρ) (Rel : Set (Atom ρ)) : Prop :=
  ∀ (l₁ l₂ : L) (θ₁ θ₂ : Subst ρ), l₁ ≠ l₂ → θ₁.applyTerm (M l₁).lhs = θ₂.applyTerm (M l₂).lhs →
    (∀ p ∈ (M l₁).premises, Holds M Rel θ₁ p) → ¬ ∀ p ∈ (M l₂).premises, Holds M Rel θ₂ p

/-- Left sides that no two substitutions make equal across different rules give exclusivity. -/
theorem exclusive_of_apart {M : L → ModuleRule ρ} {Rel : Set (Atom ρ)}
    (apart : ∀ (l₁ l₂ : L) (θ₁ θ₂ : Subst ρ), l₁ ≠ l₂ →
      θ₁.applyTerm (M l₁).lhs ≠ θ₂.applyTerm (M l₂).lhs) :
    Exclusive M Rel :=
  fun l₁ l₂ θ₁ θ₂ different same _ _ => apart l₁ l₂ θ₁ θ₂ different same

/-! ## Agreement of substitutions -/

section Agreement

variable [DecidableEq ρ.vars]

theorem applyAtom_eq_of_agree (θ θ' : Subst ρ) (atom : Atom ρ)
    (agree : ∀ v ∈ atom.freeVars, θ v = θ' v) : θ.applyAtom atom = θ'.applyAtom atom := by
  have args : (fun i => θ.applyTerm (atom.args i)) = fun i => θ'.applyTerm (atom.args i) := by
    funext i
    exact apply_eq_of_agree θ θ' (atom.args i)
      (fun v inside => agree v (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, inside⟩))
  simp only [Subst.applyAtom, args]

theorem agree_of_applyAtom_eq (θ θ' : Subst ρ) (atom : Atom ρ)
    (same : θ.applyAtom atom = θ'.applyAtom atom) : ∀ v ∈ atom.freeVars, θ v = θ' v := by
  intro v inside
  obtain ⟨i, _, inArg⟩ := Finset.mem_biUnion.mp inside
  have args : (fun i => θ.applyTerm (atom.args i)) = fun i => θ'.applyTerm (atom.args i) := by
    simpa only [Subst.applyAtom, Atom.mk.injEq, heq_eq_eq, true_and] using same
  exact agree_of_apply_eq θ θ' (atom.args i) (congrFun args i) v inArg

theorem holds_congr {M : L → ModuleRule ρ} {Rel : Set (Atom ρ)} {θ θ' : Subst ρ} {p : Premise ρ}
    (agree : ∀ v ∈ p.vars, θ v = θ' v) : Holds M Rel θ p ↔ Holds M Rel θ' p := by
  cases p with
  | call source target =>
    have first : θ.applyTerm source = θ'.applyTerm source :=
      apply_eq_of_agree θ θ' source fun v inside => agree v (Finset.mem_union_left _ inside)
    have second : θ.applyTerm target = θ'.applyTerm target :=
      apply_eq_of_agree θ θ' target fun v inside => agree v (Finset.mem_union_right _ inside)
    simp only [Holds, first, second]
  | query atom =>
    simp only [Holds, applyAtom_eq_of_agree θ θ' atom agree]

/-- Substitutions that agree on the bound variables agree on the premises that have held. -/
theorem holds_transfer {M : L → ModuleRule ρ} {Rel : Set (Atom ρ)} {r : ModuleRule ρ}
    (rr : RangeRestricted r) {pre post : List (Premise ρ)} (split : r.premises = pre ++ post)
    {θ θ' : Subst ρ} (agree : ∀ v ∈ r.bound pre, θ v = θ' v) (holds : ∀ p ∈ pre, Holds M Rel θ p) :
    ∀ p ∈ pre, Holds M Rel θ' p := fun p member =>
  (holds_congr fun v inside => agree v (vars_subset_bound rr split member inside)).mp (holds p member)

end Agreement

end Module

#print axioms rangeRestricted_iff_boundOk
#print axioms vars_subset_bound
#print axioms derives_iff
#print axioms exclusive_of_apart
#print axioms holds_congr
#print axioms holds_transfer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
