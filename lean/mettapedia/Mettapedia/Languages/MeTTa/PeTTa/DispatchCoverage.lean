import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Dispatch coverage: a reusable soundness calculus for candidate prefilters

A runtime that answers a call by scanning every equation can instead consult a
cheap *discriminator* and scan only the equations it admits.  Such a prefilter is
sound exactly when it **over-approximates** the match relation: it may admit a
equation that later fails the exact test, but it must never reject one that would
have matched.

This module states that condition once and proves, generically, that filtering
by it changes nothing observable.  Two modelling choices track the runtime:

* the equation stream is an **ordered list**, never a `Set` or `Finset` — PeTTa's
  observation is an answer bag in declaration order, so equality up to sets
  would not say what the runtime needs.  List equality preserves order and
  duplicate occurrences together.
* the exact test is **`Bool`-valued**, because in the engine it is a unification
  call returning success or failure, not an oracle.

Contents, all proved:

* `Covering` — the single obligation, and `filter_cover_eq`, the one induction
  every other result reuses.
* `filter_admits_eq`: **the reusable result** — for any covering prefilter,
  filtering before the exact test yields the identical ordered list.  Every
  future prefilter inherits it by discharging `Covering` alone.
* `keyAdmits`: the principal-key/wildcard instance CeTTa already runs
  (`space_equations_may_match_known_head` admits an equation when its head key
  equals the call's key, or when the equation has no fixed head).
* `wildcard_bucket_is_load_bearing`: dropping the wildcard admission loses a
  genuine match — the guard is not defensive decoration.
* `product_covering` / `product_filter_eq`: covering prefilters compose, so
  multi-position filters and cheap-then-exact cascades are sound with no
  further proof.
* `revisionSelect_filter_eq`: a plan pinned to a matching revision may be used;
  on mismatch the unfiltered stream is selected — either way the observation is
  the same ordered list, so a stale plan cannot change an answer.

Scope honesty: this is the *filter* half of dispatch acceleration.  Memoizing
or tabling a call replaces computation rather than narrowing candidates, and
owes a strictly stronger congruence obligation deliberately not formalized
here.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.DispatchCoverage

variable {Goal Equation Key : Type}

/-! ## The obligation, and the one induction -/

/-- The single soundness obligation for a prefilter: every equation the exact
test would accept is admitted.  The converse is not required — admitting a
equation that then fails costs time, never correctness. -/
def Covering (admits matchB : Goal → Equation → Bool) : Prop :=
  ∀ g c, matchB g c = true → admits g c = true

/-- The core lemma, proved once: filtering a list by a predicate that keeps
everything the second predicate keeps leaves the second filter's result
unchanged — same elements, same order, same multiplicity. -/
theorem filter_cover_eq {α : Type} (admits matchB : α → Bool)
    (h : ∀ a, matchB a = true → admits a = true) (l : List α) :
    (l.filter admits).filter matchB = l.filter matchB := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    by_cases hm : matchB a = true
    · have hadm : admits a = true := h a hm
      simp [hadm, hm, ih]
    · simp only [Bool.not_eq_true] at hm
      by_cases hadm : admits a = true
      · simp [hadm, hm, ih]
      · simp only [Bool.not_eq_true] at hadm
        simp [hadm, hm, ih]

/-- The equations a prefilter admits for a call, in declaration order. -/
def admitted (admits : Goal → Equation → Bool) (g : Goal) (equations : List Equation) : List Equation :=
  equations.filter (admits g)

/-- **The reusable result.**  For any covering prefilter, prefiltering the
equation list and then applying the exact test yields *exactly* the list the
exact test alone would yield — same equations, same order, same duplicate
occurrences.

Every prefilter the engine ships closes by exhibiting its admission function
and discharging `Covering`; nothing else must be reproved. -/
theorem filter_admits_eq (admits matchB : Goal → Equation → Bool)
    (hcov : Covering admits matchB) (g : Goal) (equations : List Equation) :
    (admitted admits g equations).filter (matchB g) = equations.filter (matchB g) :=
  filter_cover_eq (admits g) (matchB g) (fun c hc => hcov g c hc) equations

/-! ## The instance CeTTa already runs

`space_equations_may_match_known_head` admits an equation when its left-hand
head symbol equals the call's head, or when the equation has no fixed head — a
wildcard, which may match anything.  That is the discriminator below. -/

/-- An equation's dispatch key: a fixed principal symbol, or `wildcard` when the
equation head is not a fixed symbol. -/
inductive EquationKey (Key : Type) where
  | fixed (k : Key)
  | wildcard
deriving DecidableEq

/-- Admission for the shipped discriminator: an equation is admitted when it is a
wildcard, or when its fixed key is the call's key. -/
def keyAdmits [DecidableEq Key] (gkey : Goal → Key) (ckey : Equation → EquationKey Key)
    (g : Goal) (c : Equation) : Bool :=
  match ckey c with
  | .fixed k => decide (k = gkey g)
  | .wildcard => true

/-- **Positive instantiation.**  If every equation the exact test accepts either
is a wildcard or carries the call's own key, then `keyAdmits` never rejects a
match — the covering obligation discharged for the shipped predicate. -/
theorem keyAdmits_covering [DecidableEq Key]
    (gkey : Goal → Key) (ckey : Equation → EquationKey Key) (matchB : Goal → Equation → Bool)
    (hkey : ∀ g c k, matchB g c = true → ckey c = .fixed k → k = gkey g) :
    Covering (keyAdmits gkey ckey) matchB := by
  intro g c hm
  unfold keyAdmits
  cases hc : ckey c with
  | wildcard => rfl
  | fixed k => simpa using hkey g c k hm hc

/-- Filtering by the shipped discriminator is observationally transparent:
identical equations, identical order, identical multiplicity. -/
theorem keyAdmits_filter_eq [DecidableEq Key]
    (gkey : Goal → Key) (ckey : Equation → EquationKey Key) (matchB : Goal → Equation → Bool)
    (hkey : ∀ g c k, matchB g c = true → ckey c = .fixed k → k = gkey g)
    (g : Goal) (equations : List Equation) :
    (admitted (keyAdmits gkey ckey) g equations).filter (matchB g)
      = equations.filter (matchB g) :=
  filter_admits_eq _ _ (keyAdmits_covering gkey ckey matchB hkey) g equations

/-! ## The wildcard bucket is load-bearing

A prefilter admitting only key-equal equations — omitting wildcards — is
*unsound*.  The witness below is concrete: an equation set where the key-only
filter drops an equation the exact test accepts. -/

/-- Key-equality admission with the wildcard case wrongly omitted. -/
def keyAdmitsNoWildcard [DecidableEq Key]
    (gkey : Goal → Key) (ckey : Equation → EquationKey Key) (g : Goal) (c : Equation) : Bool :=
  match ckey c with
  | .fixed k => decide (k = gkey g)
  | .wildcard => false

/-- **Negative witness.**  One wildcard equation, one call, an exact test that
accepts it: dropping the wildcard admission makes the filtered-then-tested list
empty while the exact test alone keeps the equation.  The wildcard bucket is
required for soundness. -/
theorem wildcard_bucket_is_load_bearing :
    ∃ (gkey : Unit → Nat) (ckey : Unit → EquationKey Nat) (matchB : Unit → Unit → Bool)
      (equations : List Unit),
      (equations.filter (keyAdmitsNoWildcard gkey ckey ())).filter (matchB ())
        ≠ equations.filter (matchB ()) := by
  refine ⟨fun _ => 0, fun _ => .wildcard, fun _ _ => true, [()], ?_⟩
  simp [keyAdmitsNoWildcard]

/-- For contrast, the *correct* discriminator keeps that same equation: the
wildcard case is exactly what restores soundness. -/
theorem wildcard_admission_restores_match :
    ([()].filter (keyAdmits (fun _ => (0 : Nat)) (fun _ : Unit => EquationKey.wildcard) ())).filter
        (fun _ : Unit => true) = [()] := by
  simp [keyAdmits]

/-! ## Composition

Two sound filters compose into a sound filter, at least as precise as either.
This licenses multi-position indexing and cheap-then-exact cascades — a
fingerprint pass ahead of a structural pass, say — with no new proof per
layer. -/

/-- The product prefilter: admit only when both components admit. -/
def productAdmits (a b : Goal → Equation → Bool) (g : Goal) (c : Equation) : Bool :=
  a g c && b g c

/-- **Composition.**  If each component covers, so does the product. -/
theorem product_covering {a b matchB : Goal → Equation → Bool}
    (ha : Covering a matchB) (hb : Covering b matchB) :
    Covering (productAdmits a b) matchB := by
  intro g c hm
  simp [productAdmits, ha g c hm, hb g c hm]

/-- A product prefilter is likewise observationally transparent. -/
theorem product_filter_eq {a b matchB : Goal → Equation → Bool}
    (ha : Covering a matchB) (hb : Covering b matchB) (g : Goal) (equations : List Equation) :
    (admitted (productAdmits a b) g equations).filter (matchB g) = equations.filter (matchB g) :=
  filter_admits_eq _ _ (product_covering ha hb) g equations

/-! ## Revision staging

A compiled plan is pinned to the store revision it was built from.  A call at
that revision may use the filtered stream; a call at any other revision selects
the unfiltered oracle stream.  Either way the observation is identical, so a
stale plan can never change an answer. -/

/-- Select the filtered stream only when the plan's pinned revision matches the
current one; otherwise fall back to the full stream. -/
def revisionSelect {Rev : Type} [DecidableEq Rev] (planRev current : Rev)
    (filtered full : List Equation) : List Equation :=
  if planRev = current then filtered else full

/-- **Revision staging.**  With a covering prefilter, the selected stream —
pinned or fallen back — yields the same ordered answer list after the exact
test. -/
theorem revisionSelect_filter_eq {Rev : Type} [DecidableEq Rev]
    {admits matchB : Goal → Equation → Bool} (hcov : Covering admits matchB)
    (planRev current : Rev) (g : Goal) (equations : List Equation) :
    (revisionSelect planRev current (admitted admits g equations) equations).filter (matchB g)
      = equations.filter (matchB g) := by
  unfold revisionSelect
  by_cases h : planRev = current
  · simp only [h, if_pos]
    exact filter_admits_eq admits matchB hcov g equations
  · simp [h]

end Mettapedia.Languages.MeTTa.PeTTa.DispatchCoverage
