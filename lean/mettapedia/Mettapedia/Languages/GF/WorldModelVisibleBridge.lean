import Mettapedia.Languages.GF.VisibleLayer
import Mettapedia.OSLF.QuantifiedFormula2

/-!
# Store-Aware Semantic Bridge: VisibleLayer ↔ BinaryEvidence Semantics

Bridges the `gfReducesFull` 3-layer reduction (syntax + temporal + visible V1-V4)
to evidence-valued quantified semantics (`qsemE2`) via **store-native** evaluation.

## Core semantic claims

1. **V4 creates resolution**: `pronounBind` creates a `storeResolves` relation
   where none existed — this is the semantic content of pronoun resolution.

2. **V4 activates evidence**: Before V4, an unbound pronoun variable in a
   `qsemE2` atom evaluates to `⊥` (no evidence). After V4 binds it, the atom
   evaluates to `I pred [pos] p` — a genuine evidence change.

3. **V2 is conservative**: Scope choice commits to one quantifier nesting.
   The inverse reading ∃y.∀x is provably ≤ the surface reading ∀x.∃y
   in the BinaryEvidence lattice.

4. **State-native semantics**: `gsemE2` evaluates formulas directly over
   `GrammarState`, using the store for variable bindings and the term as
   evaluation point.

## References

- Goertzel, "TUG: Universal Grammar via TyLAA" (2026), Section 7
- Montague, "The Proper Treatment of Quantification" (1973) — scope ordering
- Kamp, "A Theory of Truth and Semantic Representation" (1981) — DRT anaphora
-/

namespace Mettapedia.Languages.GF.WorldModelVisibleBridge

open Mettapedia.Languages.GF.VisibleLayer
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.QuantifiedFormula2
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Logic.EvidenceQuantale

/-! ## 1. Store Resolution Relations

The semantic store records binding decisions (V4: `bind pr r`) and referent
introductions (V3: `ref r pos`). The **store resolution** relation captures
when these combine to resolve a pronoun to a specific position. -/

/-- The store resolves pronoun `pr` to position `pos`: there exist matching
    `bind(pr, r)` and `ref(r, pos)` atoms in the store.

    This is the semantic content of V3+V4 acting together:
    V3 introduces the referent, V4 binds the pronoun to it. -/
def storeResolves (store : Multiset StoreAtom) (pr : String) (pos : Pattern) : Prop :=
  ∃ r, StoreAtom.bind pr r ∈ store ∧ StoreAtom.ref r pos ∈ store

/-- A variable environment agrees with the store if every store resolution
    is reflected in the environment.

    This is the **correctness condition** for any environment used to
    evaluate formulas over a grammar state: the environment must respect
    the store's binding decisions. -/
def envAgreesWithStore (env : VarEnv2) (store : Multiset StoreAtom) : Prop :=
  ∀ pr pos, storeResolves store pr pos → env pr = some pos

/-! ## 2. V4 Creates Resolution (Substantive Store Effect)

The core semantic content of V4: `pronounBind` creates a `storeResolves`
relation where none existed before. This is NOT just multiset membership —
it's a semantic predicate that records the actual pronoun→referent→position
chain. -/

/-- Before V4: if no `bind pr _` atom exists in the store, then no
    resolution is possible for pronoun `pr` at ANY position.

    This captures the semantic state of an unresolved pronoun:
    the store has no binding for it. -/
theorem no_bind_no_resolution (store : Multiset StoreAtom) (pr : String)
    (hfresh : ∀ r, StoreAtom.bind pr r ∉ store) (pos : Pattern) :
    ¬ storeResolves store pr pos := by
  intro ⟨r, hbind, _⟩
  exact hfresh r hbind

/-- After V4: adding `bind pr r` to the store creates a resolution from
    `pr` to `pos` (where `ref r pos` was already in the store).

    This is the semantic effect of V4: it creates a new `storeResolves`
    fact by combining the new binding with a pre-existing referent. -/
theorem V4_creates_resolution (pr r : String) (pos : Pattern)
    (store : Multiset StoreAtom)
    (href : StoreAtom.ref r pos ∈ store) :
    storeResolves (store + {.bind pr r}) pr pos :=
  ⟨r, Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _)),
      Multiset.mem_add.mpr (Or.inl href)⟩

/-- Resolution is monotone under store growth: if `pr` resolves to `pos`
    in a smaller store, it resolves in any larger store. -/
theorem storeResolves_monotone {s1 s2 : Multiset StoreAtom}
    (hle : s1 ≤ s2) {pr : String} {pos : Pattern}
    (h : storeResolves s1 pr pos) : storeResolves s2 pr pos := by
  obtain ⟨r, hbind, href⟩ := h
  exact ⟨r, Multiset.mem_of_le hle hbind, Multiset.mem_of_le hle href⟩

/-! ## 3. BinaryEvidence Activation: V4 Changes BinaryEvidence from ⊥ to Real

The key semantic claim: `qsemE2` at a `.qatom` with an unbound variable
evaluates to `⊥` (the `none` branch in `evalTerms`). After V4 binds the
variable, the atom evaluates to the real interpretation `I pred [pos] p`.

This is the core content that distinguishes this bridge from structural
plumbing: V4 genuinely CHANGES the evidence value. -/

/-- An unbound variable in a single-argument atom gives evidence `⊥`.

    When `env pr = none`, `evalTerms env [.var pr] = none`, and
    `qsemE2` returns `⊥` at the `.qatom` case. -/
theorem unbound_var_atom_bot
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    (pr : String) (hfree : env pr = none)
    (pred : String) (p : Pattern) :
    qsemE2 R I Dom env (.qatom ⟨pred, [.var pr]⟩) p = ⊥ := by
  simp [qsemE2, evalTerms, evalTerm, hfree]

/-- A bound variable in a single-argument atom gives real evidence.

    When `extendEnv2 env pr d` is used, `evalTerms` returns `some [d]`,
    and `qsemE2` returns `I pred [d] p`. -/
theorem bound_var_atom_real
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    (pr : String) (d : Pattern)
    (pred : String) (p : Pattern) :
    qsemE2 R I Dom (extendEnv2 env pr d) (.qatom ⟨pred, [.var pr]⟩) p =
    I pred [d] p := by
  simp [qsemE2, evalTerms, evalTerm, extendEnv2]

/-! ## 4. V4 Full BinaryEvidence Bridge

Combines the operational step (V4 is reachable) with the semantic transition
(evidence jumps from `⊥` to `I pred [pos] p`).

This is the CORE THEOREM of the bridge: it proves that `VisibleStep.pronounBind`
CHANGES MEANING in the evidence semantics. -/

/-- **V4 evidence bridge**: Pronoun binding activates evidence.

    Given a grammar state where:
    - Referent `r` was introduced at position `pos` (V3)
    - Pronoun `pr` has no binding yet
    - The variable environment maps `pr` to `none`

    Then:
    1. V4 step `pronounBind pr r` is operationally reachable
    2. Before: atom evidence for predicate with unbound `pr` is `⊥`
    3. After: atom evidence with `pr` bound to `pos` is `I pred [pos] p`

    This proves V4 genuinely changes meaning: from "no evidence" to
    "real evidence determined by the world model". -/
theorem V4_evidence_bridge
    {cfg : VisibleCfg}
    (pr r : String) (pos : Pattern) (s : GrammarState)
    (href_pos : StoreAtom.ref r pos ∈ s.store)
    (hfresh : ∀ r', StoreAtom.bind pr r' ∉ s.store)
    (pred : String)
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2) (p : Pattern)
    (henv_free : env pr = none) :
    -- (1) Operational: V4 step is reachable
    VisibleStep cfg s ⟨s.term, s.store + {.bind pr r}⟩ ∧
    -- (2) Semantic: evidence transitions from ⊥ to real value
    (qsemE2 R I Dom env (.qatom ⟨pred, [.var pr]⟩) p = ⊥ ∧
     qsemE2 R I Dom (extendEnv2 env pr pos)
       (.qatom ⟨pred, [.var pr]⟩) p = I pred [pos] p) :=
  ⟨.pronounBind pr r s ⟨pos, href_pos⟩ hfresh,
   unbound_var_atom_bot R I Dom env pr henv_free pred p,
   bound_var_atom_real R I Dom env pr pos pred p⟩

/-! ## 5. Store-Native Grammar State Semantics

`storeToEnv` extracts a variable environment from the store's binding
decisions, and `gsemE2` evaluates formulas directly over grammar states. -/

/-- Decidability instance for the store resolution existential.
    Uses `Classical.propDecidable` — needed for `dite` in `storeToEnv`. -/
noncomputable instance storeResolveDec (store : Multiset StoreAtom) (x : String) :
    Decidable (∃ r pos, StoreAtom.bind x r ∈ store ∧ StoreAtom.ref r pos ∈ store) :=
  Classical.propDecidable _

/-- Store-derived variable environment.

    For each pronoun `x`, checks if the store has `bind(x, r)` and
    `ref(r, pos)` atoms; if so, returns `some pos`.

    Uses `Classical.choice` to select a witness when multiple resolutions
    exist (the uniqueness assumption is NOT built in — callers can add
    it as a hypothesis when needed). -/
noncomputable def storeToEnv (store : Multiset StoreAtom) : VarEnv2 :=
  fun x =>
    if h : ∃ r pos, StoreAtom.bind x r ∈ store ∧ StoreAtom.ref r pos ∈ store
    then some h.choose_spec.choose
    else none

/-- An unbound pronoun (no `bind` atom in store) maps to `none`. -/
theorem storeToEnv_fresh (store : Multiset StoreAtom) (pr : String)
    (hfresh : ∀ r, StoreAtom.bind pr r ∉ store) :
    storeToEnv store pr = none := by
  simp only [storeToEnv]
  rw [dif_neg]
  exact fun ⟨r, _, hb, _⟩ => hfresh r hb

/-- After V4: the store has a binding, so `storeToEnv` returns `some _`. -/
theorem storeToEnv_after_V4 (store : Multiset StoreAtom) (pr r : String)
    (pos : Pattern)
    (hbind : StoreAtom.bind pr r ∈ store)
    (href : StoreAtom.ref r pos ∈ store) :
    (storeToEnv store pr).isSome = true := by
  simp only [storeToEnv]
  rw [dif_pos ⟨r, pos, hbind, href⟩]
  rfl

/-- Grammar-state-level evidence semantics.

    Evaluates a quantified formula at a grammar state using:
    - The **term** component as the evaluation point
    - The **store**-derived environment for variable bindings
    - `R : Pattern → Pattern → Prop` for modal accessibility (on terms) -/
noncomputable def gsemE2 (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (φ : QFormula2) (s : GrammarState) : BinaryEvidence :=
  qsemE2 R I Dom (storeToEnv s.store) φ s.term

/-! ## 6. V4 Changes gsemE2 (Culminating State-Native Theorem)

The culminating result: V4 transitions `gsemE2` from `⊥` (unresolved pronoun)
to a potentially nonzero value (resolved pronoun). -/

/-- **V4 changes state-native evidence**: Before V4, `gsemE2` at an atom
    with an unresolved pronoun gives `⊥`. After V4, the binding exists
    and evidence is potentially nonzero.

    This is the full state-native bridge: the visible step CHANGES the
    grammar-state-level semantics. -/
theorem V4_changes_gsemE2
    {cfg : VisibleCfg}
    (pr r : String) (s : GrammarState)
    (hfresh_bind : ∀ r', StoreAtom.bind pr r' ∉ s.store)
    (href : ∃ pos, StoreAtom.ref r pos ∈ s.store)
    (pred : String)
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2) :
    let s' : GrammarState := ⟨s.term, s.store + {.bind pr r}⟩
    -- (1) Operational: V4 is reachable
    VisibleStep cfg s s' ∧
    -- (2) Before: unresolved pronoun → ⊥
    gsemE2 R I Dom (.qatom ⟨pred, [.var pr]⟩) s = ⊥ ∧
    -- (3) After: resolved pronoun → binding exists in store
    (storeToEnv s'.store pr).isSome = true := by
  obtain ⟨pos, hpos⟩ := href
  refine ⟨.pronounBind pr r s ⟨pos, hpos⟩ hfresh_bind, ?_, ?_⟩
  · -- Before: storeToEnv maps pr to none → atom gives ⊥
    show gsemE2 R I Dom (.qatom ⟨pred, [.var pr]⟩) s = ⊥
    have henv : storeToEnv s.store pr = none := storeToEnv_fresh s.store pr hfresh_bind
    show qsemE2 R I Dom (storeToEnv s.store) (.qatom ⟨pred, [.var pr]⟩) s.term = ⊥
    exact unbound_var_atom_bot R I Dom (storeToEnv s.store) pr henv pred s.term
  · -- After: storeToEnv maps pr to some _
    exact storeToEnv_after_V4 (s.store + {.bind pr r}) pr r pos
      (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _)))
      (Multiset.mem_add.mpr (Or.inl hpos))

/-! ## 7. Scope Ordering in BinaryEvidence Semantics

The lattice-level ordering `∃y.∀x ≤ ∀x.∃y` (from `iSup_iInf_le_iInf_iSup`)
connects V2 scope choice to the quantifier strength ordering in `qsemE2`. -/

/-- Variable environment extension commutes for distinct variables.
    Key technical lemma for the scope ordering theorem. -/
theorem extendEnv2_comm (env : VarEnv2) {x y : String} (hne : x ≠ y)
    (px py : Pattern) :
    extendEnv2 (extendEnv2 env y py) x px =
    extendEnv2 (extendEnv2 env x px) y py := by
  funext z
  simp only [extendEnv2]
  cases hzx : (z == x) <;> cases hzy : (z == y) <;> simp_all

/-- **Scope ordering theorem**: The wide-∃ (inverse scope) reading gives
    at most as much evidence as the wide-∀ (surface scope) reading.

    `∃y.∀x.φ(x,y) ≤ ∀x.∃y.φ(x,y)`

    This is `iSup_iInf_le_iInf_iSup` instantiated to `qsemE2`, with
    `extendEnv2_comm` ensuring the two nesting orders produce the same
    function of (x, y) pairs. -/
theorem scope_ordering_qsemE2
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    {x y : String} (hne : x ≠ y)
    (φ : QFormula2) (p : Pattern) :
    qsemE2 R I Dom env (.qexists y (.qforall x φ)) p ≤
    qsemE2 R I Dom env (.qforall x (.qexists y φ)) p := by
  simp only [qsemE2]
  have h_comm : ∀ (dx dy : Pattern),
      qsemE2 R I Dom (extendEnv2 (extendEnv2 env y dy) x dx) φ p =
      qsemE2 R I Dom (extendEnv2 (extendEnv2 env x dx) y dy) φ p := by
    intro dx dy
    rw [extendEnv2_comm env hne dx dy]
  conv_lhs =>
    arg 1; ext dy; arg 1; ext dx
    rw [h_comm dx.val dy.val]
  exact iSup_iInf_le_iInf_iSup _

/-- **Scope choice is conservative**: committing to q1 scoping over q2
    (surface scope: ∀q1.∃q2) selects the WEAKER reading. The inverse
    reading (∃q2.∀q1) is provably stronger.

    This justifies V2: surface scope is the safe/conservative choice. -/
theorem scopeChoice_is_conservative
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    {q1 q2 : String} (hne : q1 ≠ q2)
    (φ : QFormula2) (p : Pattern) :
    qsemE2 R I Dom env (.qexists q2 (.qforall q1 φ)) p ≤
    qsemE2 R I Dom env (.qforall q1 (.qexists q2 φ)) p :=
  scope_ordering_qsemE2 R I Dom env hne φ p

/-! ## 8. Pronoun Binding vs Quantifiers

V4 binds a free variable to a specific referent. In `qsemE2` terms, the
bound value sits between the universal (weakest) and existential (strongest)
quantification over that variable. -/

/-- Binding a pronoun to a specific domain element refines the universal
    quantification: `∀pr.φ ≤ φ[pr := d]`. -/
theorem pronounBind_refines_forall
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    (pr : String) (d : Pattern) (hd : d ∈ Dom)
    (φ : QFormula2) (p : Pattern) :
    qsemE2 R I Dom env (.qforall pr φ) p ≤
    qsemE2 R I Dom (extendEnv2 env pr d) φ p :=
  qsemE2_forall_le R I Dom env pr φ p d hd

/-- Binding a pronoun to a specific domain element witnesses the existential:
    `φ[pr := d] ≤ ∃pr.φ`. -/
theorem pronounBind_witnesses_exists
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    (pr : String) (d : Pattern) (hd : d ∈ Dom)
    (φ : QFormula2) (p : Pattern) :
    qsemE2 R I Dom (extendEnv2 env pr d) φ p ≤
    qsemE2 R I Dom env (.qexists pr φ) p :=
  qsemE2_exists_le R I Dom env pr φ p d hd

/-! ## 9. V2 Scope BinaryEvidence Bridge (End-to-End)

Combines the operational nondeterminism of V2 with the semantic ordering. -/

/-- **V2 evidence bridge**: Given two distinct quantifiers in the store,
    scope choice creates a nondeterministic fork. Both orderings are
    operationally reachable, and they are ordered in evidence:
    inverse scope (∃-wide) ≤ surface scope (∀-wide). -/
theorem V2_evidence_bridge
    {cfg : VisibleCfg}
    (q1 q2 : String) (s : GrammarState)
    (hne : q1 ≠ q2)
    (hq1 : ∃ d1 r1, StoreAtom.quant q1 d1 r1 ∈ s.store)
    (hq2 : ∃ d2 r2, StoreAtom.quant q2 d2 r2 ∈ s.store)
    (hno12 : StoreAtom.scope q1 q2 ∉ s.store)
    (hno21 : StoreAtom.scope q2 q1 ∉ s.store)
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2) (φ : QFormula2) (p : Pattern) :
    -- Both orderings are operationally reachable
    (VisibleStep cfg s ⟨s.term, s.store + {.scope q1 q2}⟩ ∧
     VisibleStep cfg s ⟨s.term, s.store + {.scope q2 q1}⟩) ∧
    -- The two readings are ordered in evidence
    qsemE2 R I Dom env (.qexists q2 (.qforall q1 φ)) p ≤
    qsemE2 R I Dom env (.qforall q1 (.qexists q2 φ)) p :=
  ⟨scope_choice_nondet q1 q2 s hne hq1 hq2 hno12 hno21,
   scope_ordering_qsemE2 R I Dom env hne φ p⟩

/-! ## 10. Store Invariants

Well-formedness conditions on the semantic store that ensure `storeToEnv`
is deterministic. These invariants are preserved by the visible layer
rules (V1-V4). -/

/-- Each pronoun is bound to at most one referent.
    V4 enforces this: `hfresh : ∀ r', bind pr r' ∉ store`. -/
def functionalBind (store : Multiset StoreAtom) : Prop :=
  ∀ pr r1 r2, StoreAtom.bind pr r1 ∈ store → StoreAtom.bind pr r2 ∈ store → r1 = r2

/-- Each referent has a unique position.
    V3 enforces this: `hfresh : ∀ p, ref r p ∉ store`. -/
def uniqueRef (store : Multiset StoreAtom) : Prop :=
  ∀ r p1 p2, StoreAtom.ref r p1 ∈ store → StoreAtom.ref r p2 ∈ store → p1 = p2

/-- Under store invariants, `storeToEnv` returns the unique resolved position.
    This makes the Classical choice in `storeToEnv` deterministic. -/
theorem storeToEnv_unique (store : Multiset StoreAtom) (pr r : String)
    (pos : Pattern)
    (hfb : functionalBind store) (hur : uniqueRef store)
    (hbind : StoreAtom.bind pr r ∈ store)
    (href : StoreAtom.ref r pos ∈ store) :
    storeToEnv store pr = some pos := by
  -- storeToEnv uses dite; the positive branch fires since ∃ r pos, ...
  have hexists : ∃ r' pos', StoreAtom.bind pr r' ∈ store ∧ StoreAtom.ref r' pos' ∈ store :=
    ⟨r, pos, hbind, href⟩
  -- After dif_pos, result is some h.choose_spec.choose for some witnesses
  simp only [storeToEnv, dif_pos hexists]
  -- The chosen witnesses must agree with r, pos by the invariants
  have hchoose_spec := hexists.choose_spec
  have hbind' := hchoose_spec.choose_spec.1
  have href' := hchoose_spec.choose_spec.2
  have hr_eq : hexists.choose = r := hfb pr _ _ hbind' hbind
  have href'' : StoreAtom.ref r hchoose_spec.choose ∈ store := hr_eq ▸ href'
  have hpos_eq : hchoose_spec.choose = pos := hur r _ _ href'' href
  rw [hpos_eq]

/-- V4 preserves `functionalBind`: the fresh-pronoun precondition ensures
    no duplicate bindings. -/
theorem V4_preserves_functionalBind (store : Multiset StoreAtom)
    (pr r : String)
    (hfb : functionalBind store)
    (hfresh : ∀ r', StoreAtom.bind pr r' ∉ store) :
    functionalBind (store + {.bind pr r}) := by
  intro pr' r1 r2 h1 h2
  rw [Multiset.mem_add, Multiset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hfb pr' r1 r2 h1 h2
  · have : pr' = pr := by injection h2
    subst this
    exact absurd h1 (hfresh r1)
  · have : pr' = pr := by injection h1
    subst this
    exact absurd h2 (hfresh r2)
  · have : r1 = r := by injection h1
    have : r2 = r := by injection h2
    exact ‹r1 = r›.trans ‹r2 = r›.symm

/-- V3 preserves `uniqueRef`: the fresh-referent precondition ensures
    no duplicate referents. -/
theorem V3_preserves_uniqueRef (store : Multiset StoreAtom)
    (ref_name : String) (pos : Pattern)
    (hur : uniqueRef store)
    (hfresh : ∀ p, StoreAtom.ref ref_name p ∉ store) :
    uniqueRef (store + {.ref ref_name pos}) := by
  intro r' p1 p2 h1 h2
  rw [Multiset.mem_add, Multiset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hur r' p1 p2 h1 h2
  · have : r' = ref_name := by injection h2
    subst this
    exact absurd h1 (hfresh p1)
  · have : r' = ref_name := by injection h1
    subst this
    exact absurd h2 (hfresh p2)
  · have : p1 = pos := by injection h1
    have : p2 = pos := by injection h2
    exact ‹p1 = pos›.trans ‹p2 = pos›.symm

/-! ## 11. gfReducesFull-Derived Accessibility

The key definition Codex demanded: modal accessibility derived from
the actual `gfReducesFull` relation, not an arbitrary `R`. -/

/-- Term-level accessibility derived from `gfReducesFull`.

    Two terms `t1`, `t2` are accessible if there exist stores making them
    `gfReducesFull`-related. This projects the state-level relation to
    the term level, which is what `qsemE2` needs for ◇/□. -/
def gfTermAccessible (cfg : VisibleCfg) (π : TemporalPolicy) :
    Pattern → Pattern → Prop :=
  fun t1 t2 => ∃ σ1 σ2 : Multiset StoreAtom,
    gfReducesFull cfg π ⟨t1, σ1⟩ ⟨t2, σ2⟩

/-- `gsemE2` instantiated with `gfReducesFull`-derived accessibility.

    This is the CANONICAL grammar-state semantics: modalities range over
    actual rewrite/temporal/visible steps, not an arbitrary relation. -/
noncomputable abbrev gsemE2Full (cfg : VisibleCfg) (π : TemporalPolicy)
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (s : GrammarState) : BinaryEvidence :=
  gsemE2 (gfTermAccessible cfg π) I Dom φ s

/-- Syntax rewrites give term-level accessibility. -/
theorem syntax_gives_term_accessible (cfg : VisibleCfg) (π : TemporalPolicy)
    {t1 t2 : Pattern} (σ : Multiset StoreAtom)
    (h : langReduces gfRGLLanguageDef t1 t2) :
    gfTermAccessible cfg π t1 t2 :=
  ⟨σ, σ, Or.inl ⟨h, rfl⟩⟩

/-- Visible steps give term-level accessibility (via the state's stores). -/
theorem visible_gives_term_accessible (cfg : VisibleCfg) (π : TemporalPolicy)
    {s1 s2 : GrammarState} (h : VisibleStep cfg s1 s2) :
    gfTermAccessible cfg π s1.term s2.term :=
  ⟨s1.store, s2.store, Or.inr (Or.inr h)⟩

/-! ## 12. V4 Post-Step Theorem (The Core Semantic Change)

The culminating theorem: evaluating `gsemE2Full` at the pre-step state gives ⊥,
and evaluating at the post-step state gives the real interpretation.
This proves V4 CHANGES MEANING under the actual `gfReducesFull` relation. -/

/-- **V4 post-step semantic change**: Under store invariants, V4 transitions
    `gsemE2Full` at a pronoun atom from `⊥` (unresolved) to the real
    world-model evidence `I pred [pos] s.term` (resolved).

    This is the CORE BRIDGE THEOREM:
    - Operational: V4 step is a `gfReducesFull` step
    - Pre-state: `gsemE2Full ... s = ⊥` (pronoun unbound)
    - Post-state: `gsemE2Full ... s' = I pred [pos] s.term` (pronoun resolved)

    The store invariants ensure `storeToEnv` is deterministic at `s'`. -/
theorem V4_post_step_semantic_change
    {cfg : VisibleCfg} {π : TemporalPolicy}
    (pr r : String) (pos : Pattern) (s : GrammarState)
    (href_pos : StoreAtom.ref r pos ∈ s.store)
    (hfresh : ∀ r', StoreAtom.bind pr r' ∉ s.store)
    (hfb : functionalBind s.store)
    (hur : uniqueRef s.store)
    (pred : String)
    (I : QEvidenceAtomSem) (Dom : Domain2) :
    let s' : GrammarState := ⟨s.term, s.store + {.bind pr r}⟩
    -- (1) Operational: V4 is a gfReducesFull step
    gfReducesFull cfg π s s' ∧
    -- (2) Pre-state: unresolved pronoun → ⊥
    gsemE2Full cfg π I Dom (.qatom ⟨pred, [.var pr]⟩) s = ⊥ ∧
    -- (3) Post-state: resolved pronoun → real evidence
    gsemE2Full cfg π I Dom (.qatom ⟨pred, [.var pr]⟩) s' = I pred [pos] s.term := by
  constructor
  · -- V4 is a gfReducesFull step (layer 3: visible)
    exact Or.inr (Or.inr (.pronounBind pr r s ⟨pos, href_pos⟩ hfresh))
  constructor
  · -- Pre-state: storeToEnv s.store pr = none → atom gives ⊥
    show gsemE2Full cfg π I Dom (.qatom ⟨pred, [.var pr]⟩) s = ⊥
    show qsemE2 (gfTermAccessible cfg π) I Dom (storeToEnv s.store) (.qatom ⟨pred, [.var pr]⟩) s.term = ⊥
    exact unbound_var_atom_bot _ I Dom _ pr (storeToEnv_fresh s.store pr hfresh) pred s.term
  · -- Post-state: storeToEnv s'.store pr = some pos → atom gives I pred [pos] s.term
    show qsemE2 (gfTermAccessible cfg π) I Dom
      (storeToEnv (s.store + {.bind pr r})) (.qatom ⟨pred, [.var pr]⟩) s.term = I pred [pos] s.term
    -- uniqueRef is preserved: adding .bind pr r doesn't add any .ref atoms
    have hur' : uniqueRef (s.store + {.bind pr r}) := by
      intro r' p1 p2 h1 h2
      rw [Multiset.mem_add, Multiset.mem_singleton] at h1 h2
      -- .ref r' p ≠ .bind pr r (different constructors), so both must be in s.store
      have h1' : StoreAtom.ref r' p1 ∈ s.store := by
        rcases h1 with h1 | h1
        · exact h1
        · exact absurd h1 (by intro h; cases h)
      have h2' : StoreAtom.ref r' p2 ∈ s.store := by
        rcases h2 with h2 | h2
        · exact h2
        · exact absurd h2 (by intro h; cases h)
      exact hur r' p1 p2 h1' h2'
    have henv : storeToEnv (s.store + {.bind pr r}) pr = some pos :=
      storeToEnv_unique (s.store + {.bind pr r}) pr r pos
        (V4_preserves_functionalBind s.store pr r hfb hfresh)
        hur'
        (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _)))
        (Multiset.mem_add.mpr (Or.inl href_pos))
    simp only [qsemE2, evalTerms, evalTerm, henv]

/-! ## 13. Store Frame Theorem: Adding Unrelated Bindings

The frame property: adding a binding for pronoun `pr` does not change
the store-derived environment for any other variable `x ≠ pr`.

This formalizes semantic locality: discourse store updates only affect
the meaning of expressions that mention the updated variable. -/

/-- Adding `bind pr r` to the store doesn't change `storeToEnv x` for `x ≠ pr`,
    under store invariants.

    The key frame property: an unrelated binding cannot create or destroy
    resolutions for a different pronoun. Store invariants ensure `storeToEnv`
    is deterministic, making the frame property hold exactly. -/
theorem storeToEnv_add_bind_ne
    (σ : Multiset StoreAtom) (pr x r : String) (hne : x ≠ pr)
    (hfb : functionalBind σ) (hur : uniqueRef σ) :
    storeToEnv (σ + {StoreAtom.bind pr r}) x = storeToEnv σ x := by
  -- Helper: bind x r' in extended store → bind x r' in σ (since x ≠ pr)
  have bind_back : ∀ r', StoreAtom.bind x r' ∈ σ + {StoreAtom.bind pr r} →
                          StoreAtom.bind x r' ∈ σ := by
    intro r' h
    rw [Multiset.mem_add, Multiset.mem_singleton] at h
    rcases h with h | h
    · exact h
    · exact absurd (by injection h : x = pr) hne
  -- Helper: ref atoms unchanged by adding bind
  have ref_back : ∀ r' pos, StoreAtom.ref r' pos ∈ σ + {StoreAtom.bind pr r} →
                             StoreAtom.ref r' pos ∈ σ := by
    intro r' pos h
    rw [Multiset.mem_add, Multiset.mem_singleton] at h
    rcases h with h | h
    · exact h
    · exact absurd h (by intro h; cases h)
  -- Case split on whether x has a resolution in σ
  by_cases h : ∃ rx posx, StoreAtom.bind x rx ∈ σ ∧ StoreAtom.ref rx posx ∈ σ
  · -- Positive: x has a resolution in both stores
    obtain ⟨rx, posx, hbind_x, href_x⟩ := h
    -- Original store: storeToEnv σ x = some posx
    have hval_orig : storeToEnv σ x = some posx :=
      storeToEnv_unique σ x rx posx hfb hur hbind_x href_x
    -- Extended store: show storeToEnv (σ + {bind pr r}) x = some posx
    -- by showing the Classical.choice witnesses must agree with rx, posx
    have hval_ext : storeToEnv (σ + {StoreAtom.bind pr r}) x = some posx := by
      simp only [storeToEnv]
      have hexists : ∃ r' pos, StoreAtom.bind x r' ∈ σ + ({StoreAtom.bind pr r} : Multiset _) ∧
                               StoreAtom.ref r' pos ∈ σ + ({StoreAtom.bind pr r} : Multiset _) :=
        ⟨rx, posx, Multiset.mem_add.mpr (Or.inl hbind_x),
                   Multiset.mem_add.mpr (Or.inl href_x)⟩
      rw [dif_pos hexists]
      -- The chosen rx' := hexists.choose satisfies bind x rx' ∈ extended
      -- Pull back: bind x rx' ∈ σ (since x ≠ pr)
      have hb_σ := bind_back hexists.choose hexists.choose_spec.choose_spec.1
      -- Pull back: ref rx' posx' ∈ σ
      have hr_σ := ref_back hexists.choose hexists.choose_spec.choose
        hexists.choose_spec.choose_spec.2
      -- By functionalBind: rx' = rx
      have hrx_eq := hfb x hexists.choose rx hb_σ hbind_x
      -- By uniqueRef: posx' = posx
      exact congr_arg some (hur hexists.choose hexists.choose_spec.choose posx
        hr_σ (hrx_eq ▸ href_x))
    rw [hval_ext, hval_orig]
  · -- Negative: x has no resolution in σ
    -- storeToEnv σ x = none
    have h1 : storeToEnv σ x = none := by
      simp only [storeToEnv]; rw [dif_neg h]
    -- storeToEnv (σ + {bind pr r}) x = none
    have h2 : storeToEnv (σ + {StoreAtom.bind pr r}) x = none := by
      simp only [storeToEnv]; rw [dif_neg]
      rintro ⟨rx, posx, hb, hr⟩
      exact h ⟨rx, posx, bind_back rx hb, ref_back rx posx hr⟩
    rw [h1, h2]

/-! ## 14. Frame: Store Atom Addition Preserves Closed BinaryEvidence

The locality principle: visible-layer updates (V1–V4) only change evidence for
formulas that mention the affected variable. Closed formulas — those with
`freeVarsQF2 φ = ∅` — are completely unaffected by ANY store modification.

This formalizes the linguistic intuition that "discourse-store updates only
matter for expressions that depend on discourse variables." -/

/-- Adding ANY store atom preserves closed formula evidence: closed formulas
    have store-independent meaning, so any visible-layer update is invisible
    to them. -/
theorem frame_closed_any_atom
    {cfg : VisibleCfg} {π : TemporalPolicy}
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (hclosed : closedQF2 φ)
    (a : StoreAtom) (s : GrammarState) :
    let s' : GrammarState := ⟨s.term, s.store + {a}⟩
    gsemE2Full cfg π I Dom φ s = gsemE2Full cfg π I Dom φ s' := by
  show qsemE2 _ I Dom (storeToEnv s.store) φ s.term =
       qsemE2 _ I Dom (storeToEnv (s.store + {a})) φ s.term
  exact qsemE2_closed_env_irrel _ I Dom hclosed _ _ s.term

/-! ## 14b. Pronoun-Specific Frame Locality

Visible updates are variable-local: binding pronoun `pr` can only affect
formulas that actually mention `pr` free. This is stronger than
`frame_closed_any_atom` and aligns with dynamic-semantics locality. -/

/-- If `pr` is not free in `φ`, adding `bind pr r` leaves evidence unchanged.

    This is a free-variable-locality theorem: pronoun-binding updates are
    semantically inert for formulas that do not mention that pronoun. -/
theorem frame_bind_irrel_if_not_free
    {cfg : VisibleCfg} {π : TemporalPolicy}
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (s : GrammarState) (pr r : String)
    (hfb : functionalBind s.store) (hur : uniqueRef s.store)
    (hnotfree : pr ∉ freeVarsQF2 φ) :
    let s' : GrammarState := ⟨s.term, s.store + {StoreAtom.bind pr r}⟩
    gsemE2Full cfg π I Dom φ s = gsemE2Full cfg π I Dom φ s' := by
  show qsemE2 _ I Dom (storeToEnv s.store) φ s.term =
       qsemE2 _ I Dom (storeToEnv (s.store + {StoreAtom.bind pr r})) φ s.term
  apply qsemE2_env_agree_on_free
  intro x hx
  have hne : x ≠ pr := by
    intro hxp
    apply hnotfree
    simpa [hxp] using hx
  simpa using (storeToEnv_add_bind_ne s.store pr x r hne hfb hur).symm

/-- V4 step is semantically inert on formulas that do not mention the bound
pronoun free. This pairs operational reachability with semantic locality. -/
theorem V4_preserves_unmentioned_formula
    {cfg : VisibleCfg} {π : TemporalPolicy}
    (pr r : String) (pos : Pattern) (s : GrammarState)
    (href_pos : StoreAtom.ref r pos ∈ s.store)
    (hfresh : ∀ r', StoreAtom.bind pr r' ∉ s.store)
    (hfb : functionalBind s.store) (hur : uniqueRef s.store)
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (hnotfree : pr ∉ freeVarsQF2 φ) :
    let s' : GrammarState := ⟨s.term, s.store + {StoreAtom.bind pr r}⟩
    gfReducesFull cfg π s s' ∧
    gsemE2Full cfg π I Dom φ s = gsemE2Full cfg π I Dom φ s' := by
  constructor
  · exact Or.inr (Or.inr (.pronounBind pr r s ⟨pos, href_pos⟩ hfresh))
  · exact frame_bind_irrel_if_not_free (cfg := cfg) (π := π) I Dom φ s pr r hfb hur hnotfree

/-! ## 15. Operational Commutation: V4+V4 Diamond

Two independent V4 steps (binding different pronouns) commute: both
orderings reach the same final state. This is the operational counterpart
of the semantic commutation theorem. -/

/-- V4 precondition survival: adding `bind pr2 r2` to the store preserves
    the V4 precondition for a DIFFERENT pronoun `pr1 ≠ pr2`. -/
theorem V4_precondition_survives_bind
    (σ : Multiset StoreAtom) (pr1 pr2 r1 r2 : String)
    (hne : pr1 ≠ pr2)
    (href1 : ∃ p, StoreAtom.ref r1 p ∈ σ)
    (hfresh1 : ∀ r', StoreAtom.bind pr1 r' ∉ σ) :
    -- After adding bind pr2 r2: ref r1 still exists and pr1 still fresh
    (∃ p, StoreAtom.ref r1 p ∈ σ + ({StoreAtom.bind pr2 r2} : Multiset _)) ∧
    (∀ r', StoreAtom.bind pr1 r' ∉ σ + ({StoreAtom.bind pr2 r2} : Multiset _)) := by
  constructor
  · -- ref atoms are unaffected by adding a bind atom
    obtain ⟨p, hp⟩ := href1
    exact ⟨p, Multiset.mem_add.mpr (Or.inl hp)⟩
  · -- bind pr1 r' ∉ extended store (since pr1 ≠ pr2 and pr1 fresh in σ)
    intro r'
    rw [Multiset.mem_add, Multiset.mem_singleton]
    rintro (h | h)
    · exact hfresh1 r' h
    · exact hne (by injection h)

/-- **V4+V4 diamond**: Two V4 steps for distinct pronouns commute.

    Given `pr1 ≠ pr2` with both V4 steps reachable from state `s`,
    both orderings reach the same final state `⟨s.term, s.store + {bind pr1 r1} + {bind pr2 r2}⟩`.

    This is the core operational commutation result. -/
theorem V4_V4_diamond
    {cfg : VisibleCfg} (s : GrammarState)
    (pr1 pr2 r1 r2 : String)
    (hne : pr1 ≠ pr2)
    (href1 : ∃ p, StoreAtom.ref r1 p ∈ s.store)
    (href2 : ∃ p, StoreAtom.ref r2 p ∈ s.store)
    (hfresh1 : ∀ r', StoreAtom.bind pr1 r' ∉ s.store)
    (hfresh2 : ∀ r', StoreAtom.bind pr2 r' ∉ s.store) :
    let sf := ⟨s.term, s.store + {StoreAtom.bind pr1 r1} + {StoreAtom.bind pr2 r2}⟩
    -- Path 1→2: first bind pr1, then bind pr2
    VisibleStep cfg s ⟨s.term, s.store + {StoreAtom.bind pr1 r1}⟩ ∧
    VisibleStep cfg ⟨s.term, s.store + {StoreAtom.bind pr1 r1}⟩ sf ∧
    -- Path 2→1: first bind pr2, then bind pr1
    VisibleStep cfg s ⟨s.term, s.store + {StoreAtom.bind pr2 r2}⟩ ∧
    VisibleStep cfg ⟨s.term, s.store + {StoreAtom.bind pr2 r2}⟩
      ⟨s.term, s.store + {StoreAtom.bind pr2 r2} + {StoreAtom.bind pr1 r1}⟩ ∧
    -- Both paths reach the same state (multiset commutativity)
    sf = ⟨s.term, s.store + {StoreAtom.bind pr2 r2} + {StoreAtom.bind pr1 r1}⟩ := by
  -- Extract survival results for both directions
  have ⟨href1', hfresh1'⟩ := V4_precondition_survives_bind s.store pr1 pr2 r1 r2 hne href1 hfresh1
  have ⟨href2', hfresh2'⟩ := V4_precondition_survives_bind s.store pr2 pr1 r2 r1 (Ne.symm hne) href2 hfresh2
  exact ⟨
    -- Path 1→2
    .pronounBind pr1 r1 s href1 hfresh1,
    .pronounBind pr2 r2 ⟨s.term, s.store + {StoreAtom.bind pr1 r1}⟩ href2' hfresh2',
    -- Path 2→1
    .pronounBind pr2 r2 s href2 hfresh2,
    .pronounBind pr1 r1 ⟨s.term, s.store + {StoreAtom.bind pr2 r2}⟩ href1' hfresh1',
    -- Multiset commutativity
    congr_arg (GrammarState.mk s.term) (independent_store_commute s.store _ _)⟩

/-! ## 16. Semantic Commutation for Independent Store Atoms (Flagship)

Independent store atom additions give the same grammar-state evidence
regardless of insertion order. This is the culminating semantic theorem:
"order of independent meaning updates doesn't matter for meaning." -/

/-- **Semantic commutation**: Adding store atoms in either order gives
    the same evidence for any formula.

    This follows directly from multiset commutativity: `σ + {a1} + {a2}`
    and `σ + {a2} + {a1}` are the SAME multiset, so `storeToEnv` receives
    identical input and produces identical output. -/
theorem gsemE2Full_commute_independent
    {cfg : VisibleCfg} {π : TemporalPolicy}
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (s : GrammarState) (a1 a2 : StoreAtom) :
    let s12a := ⟨s.term, s.store + {a1} + {a2}⟩
    let s12b := ⟨s.term, s.store + {a2} + {a1}⟩
    gsemE2Full cfg π I Dom φ s12a = gsemE2Full cfg π I Dom φ s12b := by
  -- The two stores are equal as multisets (commutativity)
  show qsemE2 _ I Dom (storeToEnv (s.store + {a1} + {a2})) φ s.term =
       qsemE2 _ I Dom (storeToEnv (s.store + {a2} + {a1})) φ s.term
  rw [independent_store_commute s.store a1 a2]

/-! ## 17. Store-Environment Equivalence Under Invariants

Stores that agree on all bind/ref atoms produce the same `storeToEnv` under
the `functionalBind`/`uniqueRef` invariants. This strengthens the multiset-
commutativity-based commutation to a semantic invariance result. -/

/-- Stores with identical bind/ref membership give the same variable environment,
    provided both satisfy the functional-bind and unique-ref invariants.

    This is strictly stronger than `gsemE2Full_commute_independent`: different
    multisets can produce the same `storeToEnv` if they agree on bindings. -/
theorem storeToEnv_invariant_equiv
    (σ₁ σ₂ : Multiset StoreAtom)
    (_hfb₁ : functionalBind σ₁) (_hur₁ : uniqueRef σ₁)
    (hfb₂ : functionalBind σ₂) (hur₂ : uniqueRef σ₂)
    (hbind : ∀ pr r, StoreAtom.bind pr r ∈ σ₁ ↔ StoreAtom.bind pr r ∈ σ₂)
    (href : ∀ r pos, StoreAtom.ref r pos ∈ σ₁ ↔ StoreAtom.ref r pos ∈ σ₂) :
    storeToEnv σ₁ = storeToEnv σ₂ := by
  funext x
  simp only [storeToEnv]
  by_cases h₁ : ∃ r pos, StoreAtom.bind x r ∈ σ₁ ∧ StoreAtom.ref r pos ∈ σ₁
  · -- x is bound in σ₁ → also bound in σ₂ (by hbind/href)
    have h₂ : ∃ r pos, StoreAtom.bind x r ∈ σ₂ ∧ StoreAtom.ref r pos ∈ σ₂ := by
      obtain ⟨r, pos, hb, hr⟩ := h₁
      exact ⟨r, pos, (hbind x r).mp hb, (href r pos).mp hr⟩
    rw [dif_pos h₁, dif_pos h₂]
    -- Extract Classical.choice witnesses from h₁ (do NOT obtain-destruct h₁)
    have hb₁ := h₁.choose_spec.choose_spec.1
    have hr₁ := h₁.choose_spec.choose_spec.2
    -- Transfer h₁'s witnesses to σ₂
    have hb₁₂ : StoreAtom.bind x h₁.choose ∈ σ₂ := (hbind x _).mp hb₁
    have hr₁₂ : StoreAtom.ref h₁.choose h₁.choose_spec.choose ∈ σ₂ :=
      (href _ _).mp hr₁
    -- Extract h₂'s witnesses
    have hb₂ := h₂.choose_spec.choose_spec.1
    have hr₂ := h₂.choose_spec.choose_spec.2
    -- By functionalBind on σ₂: h₂.choose = h₁.choose
    have heq_r : h₂.choose = h₁.choose := hfb₂ x _ _ hb₂ hb₁₂
    -- By uniqueRef on σ₂: h₂.choose_spec.choose = h₁.choose_spec.choose
    have hr₂' : StoreAtom.ref h₁.choose h₂.choose_spec.choose ∈ σ₂ := heq_r ▸ hr₂
    have heq_p : h₂.choose_spec.choose = h₁.choose_spec.choose :=
      hur₂ _ _ _ hr₂' hr₁₂
    simp only [heq_p]
  · -- x is not bound in σ₁ → also not bound in σ₂
    have h₂ : ¬∃ r pos, StoreAtom.bind x r ∈ σ₂ ∧ StoreAtom.ref r pos ∈ σ₂ := by
      intro ⟨r, pos, hb, hr⟩
      exact h₁ ⟨r, pos, (hbind x r).mpr hb, (href r pos).mpr hr⟩
    rw [dif_neg h₁, dif_neg h₂]

/-- Grammar states with the same term and equivalent stores (under invariants)
    produce the same evidence for any formula.

    This strengthens `gsemE2Full_commute_independent` from multiset equality
    to semantic equivalence: stores can differ in quant/scope atoms but still
    give the same evidence, as long as bind/ref atoms agree. -/
theorem gsemE2Full_invariant_equiv
    {cfg : VisibleCfg} {π : WorldModelSemantics.TemporalPolicy}
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (s₁ s₂ : GrammarState)
    (hterm : s₁.term = s₂.term)
    (hfb₁ : functionalBind s₁.store) (hur₁ : uniqueRef s₁.store)
    (hfb₂ : functionalBind s₂.store) (hur₂ : uniqueRef s₂.store)
    (hbind : ∀ pr r, StoreAtom.bind pr r ∈ s₁.store ↔ StoreAtom.bind pr r ∈ s₂.store)
    (href : ∀ r pos, StoreAtom.ref r pos ∈ s₁.store ↔ StoreAtom.ref r pos ∈ s₂.store) :
    gsemE2Full cfg π I Dom φ s₁ = gsemE2Full cfg π I Dom φ s₂ := by
  simp only [gsemE2Full, gsemE2]
  rw [hterm, storeToEnv_invariant_equiv s₁.store s₂.store hfb₁ hur₁ hfb₂ hur₂ hbind href]

/-! ## Base vs Visible Relation Distinction

The base relation (`gfReducesBase`) captures syntax rewrites and temporal steps —
it never changes the store. The full relation (`gfReducesFull`) additionally
includes visible semantic steps (V1–V4: scope choice, referent intro, pronoun
binding) that grow the store.

Key results:
- `visible_layer_extends_base`: every base step is also a full step.
- `visible_not_base_witness`: a scope-choice step is reachable via visible
  layer but NOT via base relation, providing a clean separation. -/

/-- Every base reduction is a full reduction (D.1). -/
theorem visible_layer_extends_base
    {cfg : VisibleCfg} {π : WorldModelSemantics.TemporalPolicy}
    {s₁ s₂ : GrammarState} (h : gfReducesBase π s₁ s₂) :
    gfReducesFull cfg π s₁ s₂ :=
  gfReducesBase_sub_gfReducesFull cfg π h

/-- D.2 separation witness: scope choice is reachable via visible layer
    but NOT via base relation.

    Proof: scope choice adds a `scope` atom to the store, changing it.
    But `gfReducesBase_preserves_store` shows base steps never change
    the store. -/
theorem visible_not_base_witness
    {cfg : VisibleCfg} {π : WorldModelSemantics.TemporalPolicy}
    (q1 q2 : String) (s : GrammarState)
    (hne : q1 ≠ q2)
    (hq1 : ∃ d1 r1, StoreAtom.quant q1 d1 r1 ∈ s.store)
    (hq2 : ∃ d2 r2, StoreAtom.quant q2 d2 r2 ∈ s.store)
    (hno12 : StoreAtom.scope q1 q2 ∉ s.store)
    (hno21 : StoreAtom.scope q2 q1 ∉ s.store) :
    gfReducesFull cfg π s ⟨s.term, s.store + {.scope q1 q2}⟩ ∧
    ¬ gfReducesBase π s ⟨s.term, s.store + {.scope q1 q2}⟩ :=
  ⟨Or.inr (Or.inr (.scopeChoice q1 q2 s hne hq1 hq2 ⟨hno12, hno21⟩)),
   scopeChoice_not_base hno12⟩

/-! ## Anaphora Adequacy

V3 (referent intro) and V4 (pronoun binding) are visible-only steps: they change
the store, which base reductions never do. This gives a clean separation for
anaphora parallel to the scope-choice separation above. -/

/-- V3+V4 anaphora chain is reachable via full relation but NOT via base.

    Given a fresh referent `r` and a fresh pronoun `pr`:
    - V3 introduces `ref r pos` (full-reachable, not base-reachable)
    - V4 binds `pr` to `r` (full-reachable from post-V3 state, not base-reachable from pre-V3)

    The second conjunct shows the V3 step alone is not base-reachable. -/
theorem anaphora_not_base_witness
    {cfg : VisibleCfg} {π : WorldModelSemantics.TemporalPolicy}
    (r : String) (pos : Pattern) (pr : String) (s : GrammarState)
    (hfresh_ref : ∀ p, StoreAtom.ref r p ∉ s.store)
    (hfresh_bind : ∀ r', StoreAtom.bind pr r' ∉ s.store) :
    -- (1) V3+V4 chain reachable via full relation
    (let s₁ : GrammarState := ⟨s.term, s.store + {.ref r pos}⟩
     gfReducesFull cfg π s s₁ ∧
     gfReducesFull cfg π s₁ ⟨s.term, s.store + {.ref r pos} + {.bind pr r}⟩) ∧
    -- (2) V3 step is not base-reachable
    ¬ gfReducesBase π s ⟨s.term, s.store + {.ref r pos}⟩ := by
  constructor
  · constructor
    · -- V3: refIntro
      exact Or.inr (Or.inr (.refIntro r pos s (hfresh_ref)))
    · -- V4: pronounBind (ref r pos now in store after V3)
      have href : ∃ p, StoreAtom.ref r p ∈ (s.store + ({.ref r pos} : Multiset StoreAtom)) :=
        ⟨pos, Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))⟩
      have hfresh' : ∀ r', StoreAtom.bind pr r' ∉ (s.store + ({.ref r pos} : Multiset StoreAtom)) := by
        intro r'
        simp only [Multiset.mem_add, Multiset.mem_singleton]
        push_neg
        exact ⟨hfresh_bind r', fun h => StoreAtom.noConfusion h⟩
      exact Or.inr (Or.inr (.pronounBind pr r ⟨s.term, s.store + {.ref r pos}⟩ href hfresh'))
  · exact refIntro_not_base (hfresh_ref pos)

/-- Visible-layer adequacy: the base relation preserves the store, every
    visible step (V1–V4) changes the store, and all base steps lift to
    full steps. This cleanly separates "what syntax can do" from "what
    semantics needs". -/
theorem visible_adequacy
    {π : WorldModelSemantics.TemporalPolicy} {s₁ s₂ : GrammarState}
    (h : gfReducesBase π s₁ s₂) :
    s₁.store = s₂.store ∧ ∀ cfg : VisibleCfg, gfReducesFull cfg π s₁ s₂ :=
  ⟨gfReducesBase_preserves_store h, fun cfg => gfReducesBase_sub_gfReducesFull cfg π h⟩

end Mettapedia.Languages.GF.WorldModelVisibleBridge
