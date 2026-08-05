import Mathlib.Logic.Relation

/-!
# Knot decomposition: stratified fixed points over a call relation

A language definition presents rules; rules whose bodies mention defined heads
induce a **call relation** on heads.  This module proves that recursive
structure decomposes along that relation:

* a set of heads closed under calls is **self-contained** — the rule operator
  restricted to it never consults anything outside it;
* a solution of a self-contained lower system **glues** with a solution of the
  remaining system (computed with the lower one frozen) into a solution of the
  whole — the fixed-point content of Bekić's lemma, in gluing form;
* the **knots** — classes of mutually reachable heads — are the natural units
  of that stratification: reachability sets are call-closed and depend only on
  the knot of their root.

Everything is stated over an abstract head type, an abstract answer type, and
one hypothesis on the rule operator: **locality** — the answer a rule computes
at a head depends only on the solution at the heads it directly calls.  No
lattice, no monotonicity, and no evaluation strategy appear, so the results
apply to an eager bag engine, a backtracking relational engine, and a
call-by-need engine alike: anything whose semantics is a solution of its rule
equations.

The direction of travel matters and is fixed once: `calls f g` means the rules
for `f` mention `g`, so a *call-closed* set is closed under following calls —
solving it requires nothing outside it.

Positive and negative instances close the module: on the two-head system where
`f` calls `g`, stratifying bottom-up (`{g}` first) glues into the unique
solution, while stratifying top-down (`{f}` first) manufactures a non-solution
— the closure hypothesis is load-bearing, not bookkeeping.

Deliberately out of scope here: computing the knots (a verified SCC algorithm)
and iterating the gluing along a general finite condensation chain; both build
on this module and neither is needed to *state or use* the licenses it proves.
-/

namespace Mettapedia.GSLT.Dynamics.KnotDecomposition

variable {Head : Type} {Answer : Type}

/-! ## Systems, locality, closure -/

/-- A recursive system: which heads each head's rules call, and what the rules
compute at a head given a candidate solution. -/
structure CallSystem (Head Answer : Type) where
  /-- `calls f g`: some rule for `f` mentions `g` at a call position. -/
  calls : Head → Head → Prop
  /-- One parallel application of all rules to a candidate solution. -/
  step : (Head → Answer) → Head → Answer
  /-- **Locality**: the rules at `h` consult the candidate only at the heads
  `h` directly calls. -/
  local_step : ∀ sol sol' h,
    (∀ g, calls h g → sol g = sol' g) → step sol h = step sol' h

/-- A solution: every head's rules reproduce its value. -/
def Solves (sys : CallSystem Head Answer) (sol : Head → Answer) : Prop :=
  ∀ h, sys.step sol h = sol h

/-- A set of heads closed under following calls: solving it needs nothing
outside it. -/
def CallClosed (sys : CallSystem Head Answer) (S : Head → Prop) : Prop :=
  ∀ ⦃h g⦄, S h → sys.calls h g → S g

/-- Combine a lower solution on `S` with an upper one outside `S`. -/
def glue (S : Head → Prop) [DecidablePred S]
    (low high : Head → Answer) (h : Head) : Answer :=
  if S h then low h else high h

theorem glue_of_mem {S : Head → Prop} [DecidablePred S]
    {low high : Head → Answer} {h : Head} (hh : S h) :
    glue S low high h = low h := by simp [glue, hh]

theorem glue_of_not_mem {S : Head → Prop} [DecidablePred S]
    {low high : Head → Answer} {h : Head} (hh : ¬ S h) :
    glue S low high h = high h := by simp [glue, hh]

/-! ## Self-containedness and the gluing theorem -/

/-- **Self-containedness.**  On a call-closed set, the rule operator is
determined by the candidate's values on that set alone. -/
theorem step_congr_on_closed (sys : CallSystem Head Answer)
    {S : Head → Prop} (hS : CallClosed sys S)
    {sol sol' : Head → Answer} (hagree : ∀ g, S g → sol g = sol' g)
    {h : Head} (hh : S h) :
    sys.step sol h = sys.step sol' h :=
  sys.local_step sol sol' h fun g hcall => hagree g (hS hh hcall)

/-- **Gluing (Bekić, fixed-point form).**  Let `S` be call-closed.  If

* `low` solves the `S`-system *on its own* — its values outside `S` are never
  consulted, so any `low` with `∀ h ∈ S, step low h = low h` qualifies — and
* `high` solves the remaining system *with the lower stratum frozen*,

then the glued assignment solves the whole system.  The lower stratum is
solved in complete ignorance of the upper one: that independence is the
theorem's content, and it is exactly what licenses solving, compiling,
specializing, or tabling a program knot by knot. -/
theorem glue_solves (sys : CallSystem Head Answer)
    {S : Head → Prop} [DecidablePred S] (hS : CallClosed sys S)
    {low high : Head → Answer}
    (hlow : ∀ h, S h → sys.step low h = low h)
    (hhigh : ∀ h, ¬ S h → sys.step (glue S low high) h = high h) :
    Solves sys (glue S low high) := by
  intro h
  by_cases hh : S h
  · have hagree : ∀ g, S g → glue S low high g = low g :=
      fun g hg => glue_of_mem hg
    calc sys.step (glue S low high) h
        = sys.step low h := step_congr_on_closed sys hS hagree hh
      _ = low h := hlow h hh
      _ = glue S low high h := (glue_of_mem hh).symm
  · calc sys.step (glue S low high) h
        = high h := hhigh h hh
      _ = glue S low high h := (glue_of_not_mem hh).symm

/-- **Extraction.**  Conversely, a solution of the whole system restricts to a
standalone solution of any call-closed part: replacing everything outside `S`
by arbitrary values preserves the `S`-equations.  A knot's solution can be
carved out and reused. -/
theorem extract_closed (sys : CallSystem Head Answer)
    {S : Head → Prop} [DecidablePred S] (hS : CallClosed sys S)
    {sol : Head → Answer} (hsol : Solves sys sol) (ext : Head → Answer) :
    ∀ h, S h → sys.step (glue S sol ext) h = glue S sol ext h := by
  intro h hh
  have hagree : ∀ g, S g → glue S sol ext g = sol g :=
    fun g hg => glue_of_mem hg
  calc sys.step (glue S sol ext) h
      = sys.step sol h := step_congr_on_closed sys hS hagree hh
    _ = sol h := hsol h
    _ = glue S sol ext h := (glue_of_mem hh).symm

/-- **Two-strata chain.**  Gluing iterates: solve a call-closed `S₁`, then the
rest with `S₁` frozen.  Instantiating `S₁` with successive downsets of the
knot order runs this along an entire condensation chain; each application is
one knot stratum. -/
theorem chain_glue_solves (sys : CallSystem Head Answer)
    {S₁ : Head → Prop} [DecidablePred S₁] (h₁ : CallClosed sys S₁)
    {low mid : Head → Answer}
    (hlow : ∀ h, S₁ h → sys.step low h = low h)
    (hmid : ∀ h, ¬ S₁ h → sys.step (glue S₁ low mid) h = mid h) :
    Solves sys (glue S₁ low mid) :=
  glue_solves sys h₁ hlow hmid

/-! ## Knots

Mutual reachability through the call relation is an equivalence; its classes
are the knots.  Reachability sets are call-closed and depend only on the knot
of their root, so "solve the knots bottom-up" is well-posed. -/

/-- `Reaches f g`: the rules for `f` depend, possibly through intermediaries,
on `g`. -/
def Reaches (sys : CallSystem Head Answer) : Head → Head → Prop :=
  Relation.ReflTransGen sys.calls

/-- Two heads in the same knot: each reaches the other. -/
def SameKnot (sys : CallSystem Head Answer) (f g : Head) : Prop :=
  Reaches sys f g ∧ Reaches sys g f

theorem sameKnot_refl (sys : CallSystem Head Answer) (f : Head) :
    SameKnot sys f f :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem sameKnot_symm {sys : CallSystem Head Answer} {f g : Head}
    (h : SameKnot sys f g) : SameKnot sys g f :=
  ⟨h.2, h.1⟩

theorem sameKnot_trans {sys : CallSystem Head Answer} {f g k : Head}
    (hfg : SameKnot sys f g) (hgk : SameKnot sys g k) : SameKnot sys f k :=
  ⟨hfg.1.trans hgk.1, hgk.2.trans hfg.2⟩

/-- The knots are the classes of an equivalence relation. -/
theorem sameKnot_equivalence (sys : CallSystem Head Answer) :
    Equivalence (SameKnot sys) :=
  ⟨sameKnot_refl sys, sameKnot_symm, sameKnot_trans⟩

/-- Everything a head depends on. -/
def reachSet (sys : CallSystem Head Answer) (h : Head) : Head → Prop :=
  Reaches sys h

/-- A dependency set is call-closed — it is a lawful lower stratum for
`glue_solves`. -/
theorem reachSet_callClosed (sys : CallSystem Head Answer) (h : Head) :
    CallClosed sys (reachSet sys h) :=
  fun _ _ hx hcall => hx.tail hcall

/-- The dependency set depends only on the knot: mutually reachable heads have
the same one.  Stratifying by knots is therefore well-posed. -/
theorem reachSet_eq_of_sameKnot (sys : CallSystem Head Answer) {f g : Head}
    (hfg : SameKnot sys f g) : reachSet sys f = reachSet sys g := by
  funext x
  apply propext
  exact ⟨fun hx => hfg.2.trans hx, fun hx => hfg.1.trans hx⟩

/-! ## The two-head system: closure is load-bearing

One system, two stratifications.  Heads are `Bool` with `f := true`,
`g := false`; the only call is `f → g`; the rules are `step sol f = sol g` and
`step sol g = 7`.  Its unique solution is `f = g = 7`. -/

/-- `f` calls `g`; `g` calls nothing; `f`'s rule copies `g`'s value, `g`'s
rule is the constant `7`. -/
def twoHead : CallSystem Bool Nat where
  calls := fun x y => x = true ∧ y = false
  step := fun sol x => if x then sol false else 7
  local_step := by
    intro sol sol' h hagree
    cases h with
    | true => simpa using hagree false ⟨rfl, rfl⟩
    | false => simp

/-- **Positive: bottom-up stratification succeeds.**  `{g}` is call-closed;
solving it alone gives `7`; solving `f` with `g` frozen gives `7`; the glue
solves the whole system. -/
theorem twoHead_bottomUp_solves :
    Solves twoHead (glue (fun x => x = false) (fun _ => 7) (fun _ => 7)) := by
  apply glue_solves twoHead
  · intro h g hh hcall
    exact hcall.2
  · intro h hh
    have : h = false := by simpa using hh
    simp [twoHead, this]
  · intro h hh
    have : h = true := by
      cases h with
      | true => rfl
      | false => exact absurd rfl hh
    simp [twoHead, glue, this]

/-- **Negative: top-down stratification manufactures a non-solution.**
`{f}` is *not* call-closed (`f` calls `g` outside it).  The assignment
`f ↦ 0` satisfies the naive `{f}`-equation for a candidate freezing `g ↦ 0`,
and `g ↦ 7` satisfies the upper equation, yet the glued assignment
(`f ↦ 0, g ↦ 7`) fails the system: `step glue f = 7 ≠ 0`.  Without the closure
hypothesis, `glue_solves` is false — the hypothesis is load-bearing. -/
theorem twoHead_topDown_fails :
    ¬ Solves twoHead (glue (fun x => x = true) (fun _ => 0) (fun _ => 7)) := by
  intro hsolves
  have := hsolves true
  simp [twoHead, glue] at this

/-- And indeed `{f}` is not call-closed — the exact hypothesis the failure
violates. -/
theorem twoHead_topDown_not_closed :
    ¬ CallClosed twoHead (fun x => x = true) := by
  intro hclosed
  exact absurd (hclosed rfl ⟨rfl, rfl⟩) (by simp)

end Mettapedia.GSLT.Dynamics.KnotDecomposition
