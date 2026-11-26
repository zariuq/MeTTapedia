import Mettapedia.GSLT.Contracts.ScopedAliasDispatch

/-! # Scoped aliases: any section of the classes, and incremental re-filing

`ScopedAliasDispatch.indexed_eq_modulo` proves that indexing both the rows and
the query by the acyclic presentation's normal form (`expand`) answers exactly
the rows equal to the query modulo the equations, in source order and with
duplicates. This module states what an implementation may change without
changing those answers.

* **Any section.** A key function with the same kernel as `expand` gives the
  same lookups (`lookup_section_invariant`, `section_lookup_eq_modulo`). So the
  member chosen to print a class, whether by preference, size or term order, is
  presentation: choosing another never changes an answer, and a store keyed by
  class identity answers as one keyed by the printed member.
* **Incremental re-filing.** When the classes change, re-keying only the rows
  whose keys can change gives the index a full rebuild gives (`refile_eq_index`).
* **Ground terms over symbols.** The canonical key, each symbol replaced by its
  class's member, decides equality modulo the symbol classes (`canon_eq_iff`).
  Joining two classes by relabelling one root is a section of the joined
  equivalence (`relabel_section`), and it changes only the keys of terms that
  mention the absorbed class (`canon_relabel_avoid`). So a merge re-files only
  the rows that mention a member of the absorbed class.
-/
set_option autoImplicit false
namespace Mettapedia.GSLT.Contracts.ScopedAliasSections

open Mettapedia.GSLT.Contracts.ScopedAliasDispatch
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.EquationSemantics

variable {K R : Type*}

/-! ## Any section -/

/-- **Two key functions with one kernel give the same lookups.** -/
theorem lookup_section_invariant [DecidableEq K] (n₁ n₂ : K → K)
    (same : ∀ a b, n₁ a = n₁ b ↔ n₂ a = n₂ b) (key : R → K) (rs : List R) (q : K) :
    lookup (n₁ q) (index n₁ key rs) = lookup (n₂ q) (index n₂ key rs) := by
  rw [lookup_index, lookup_index]
  apply List.filter_congr
  intro r _
  simp only [decide_eq_decide]
  exact same (key r) q

/-- **Any section answers by the equations**: a key function with the kernel of
the acyclic presentation's normal form answers each query with exactly the rows
equal to it modulo the equations, in order and with duplicates. -/
theorem section_lookup_eq_modulo (base : BasePremiseEvaluator) {lang : LanguageDef}
    {defs : List Row} (acyclic : Acyclic defs) (authored : Presents lang defs)
    (noBag : lang.usesCollection .hashBag = false) (noSet : lang.usesCollection .hashSet = false)
    (noAlg : lang.hasAlgebraDeclarations = false)
    (norm : Pattern → Pattern) (same : ∀ a b, norm a = norm b ↔ expand defs a = expand defs b)
    (key : R → Pattern) (q : Pattern) (rs : List R) :
    lookup (norm q) (index norm key rs) = moduloRead base lang key q rs := by
  rw [lookup_section_invariant norm (expand defs) same key rs q]
  exact indexed_eq_modulo base acyclic authored noBag noSet noAlg key q rs

/-! ## Incremental re-filing -/

/-- Re-key the entries of the rows that may have moved; keep the others. -/
def refile (n : K → K) (key : R → K) (moved : R → Bool) (ix : List (K × R)) : List (K × R) :=
  ix.map fun e => if moved e.2 then (n (key e.2), e.2) else e

/-- **Re-filing the moved rows is a rebuild**: if every row not marked moved keeps
its key under the new key function, re-keying only the marked rows gives the
index built from scratch with the new keys. -/
theorem refile_eq_index (n n' : K → K) (key : R → K) (moved : R → Bool) (rs : List R)
    (stays : ∀ r ∈ rs, moved r = false → n' (key r) = n (key r)) :
    refile n' key moved (index n key rs) = index n' key rs := by
  unfold refile index
  rw [List.map_map]
  apply List.map_congr_left
  intro r mem
  cases h : moved r
  · simp [h, stays r mem h]
  · simp [h]

/-! ## Ground terms over symbols -/

/-- Ground terms whose leaves are symbols; `app` applies a term to an argument,
so `(Probe Cold)` is `app (sym Probe) (sym Cold)`. -/
inductive GTerm (S : Type*) where
  | sym : S → GTerm S
  | app : GTerm S → GTerm S → GTerm S

/-- The canonical key: every symbol replaced by `f` of it. -/
def GTerm.map {S : Type*} (f : S → S) : GTerm S → GTerm S
  | .sym s => .sym (f s)
  | .app g a => .app (g.map f) (a.map f)

/-- Equality modulo a relation on symbols: one shape, related symbols. -/
def GTerm.EqMod {S : Type*} (rel : S → S → Prop) : GTerm S → GTerm S → Prop
  | .sym s, .sym t => rel s t
  | .app f a, .app g b => EqMod rel f g ∧ EqMod rel a b
  | _, _ => False

/-- Whether a term mentions a symbol satisfying `A`. -/
def GTerm.Mentions {S : Type*} (A : S → Prop) : GTerm S → Prop
  | .sym s => A s
  | .app f a => f.Mentions A ∨ a.Mentions A

/-- **The canonical key decides equality modulo the classes**, for any section
`r` of the symbol relation. -/
theorem canon_eq_iff {S : Type*} (rel : S → S → Prop) (r : S → S)
    (sec : ∀ a b, r a = r b ↔ rel a b) :
    ∀ t u : GTerm S, t.map r = u.map r ↔ t.EqMod rel u
  | .sym s, .sym t => by simp [GTerm.map, GTerm.EqMod, sec]
  | .app f a, .app g b => by
      simp [GTerm.map, GTerm.EqMod, canon_eq_iff rel r sec f g, canon_eq_iff rel r sec a b]
  | .sym _, .app _ _ => by simp [GTerm.map, GTerm.EqMod]
  | .app _ _, .sym _ => by simp [GTerm.map, GTerm.EqMod]

/-- **Keys move only where the section moves**: if `r'` agrees with `r` outside
`A`, a term that mentions no symbol in `A` keeps its key. -/
theorem canon_relabel_avoid {S : Type*} (r r' : S → S) (A : S → Prop)
    (outside : ∀ s, ¬ A s → r' s = r s) :
    ∀ t : GTerm S, ¬ t.Mentions A → t.map r' = t.map r
  | .sym s, h => by
      simp only [GTerm.Mentions] at h
      simp [GTerm.map, outside s h]
  | .app f a, h => by
      simp only [GTerm.Mentions, not_or] at h
      simp [GTerm.map, canon_relabel_avoid r r' A outside f h.1,
        canon_relabel_avoid r r' A outside a h.2]

/-- Join the class of `a` to the class of `b` by relabelling: members of `a`'s
class now map to `b`'s member, the rest are unchanged. -/
def relabel {S : Type*} [DecidableEq S] (r : S → S) (a b : S) (s : S) : S :=
  if r s = r a then r b else r s

/-- The equivalence generated by `rel` and one new equation `a = b`. -/
def joined {S : Type*} (rel : S → S → Prop) (a b : S) (x y : S) : Prop :=
  rel x y ∨ (rel x a ∧ rel b y) ∨ (rel x b ∧ rel a y)

/-- **Relabelling is a section of the joined classes**, when `r` is a section of
the old ones. -/
theorem relabel_section {S : Type*} [DecidableEq S] (rel : S → S → Prop) (r : S → S)
    (sec : ∀ x y, r x = r y ↔ rel x y) (a b : S) :
    ∀ x y, relabel r a b x = relabel r a b y ↔ joined rel a b x y := by
  intro x y
  simp only [relabel, joined, ← sec]
  split_ifs with hx hy hy <;> grind

/-- **A merge re-files only the absorbed class's rows**: under the relabelling
merge, a term mentioning no member of `a`'s class keeps its key. -/
theorem canon_merge_avoid {S : Type*} [DecidableEq S] (r : S → S) (a b : S) (t : GTerm S)
    (h : ¬ t.Mentions (fun s => r s = r a)) :
    t.map (relabel r a b) = t.map r :=
  canon_relabel_avoid r (relabel r a b) (fun s => r s = r a)
    (fun s hs => by simp [relabel, hs]) t h

/-! ## Controls -/

namespace Controls

/-- Two symbols and a probe: `Cold`, `Warm`, `Probe`. -/
inductive Sym where
  | cold | warm | probe
  deriving DecidableEq

/-- Before `(=e Cold Warm)` every symbol is its own class. -/
def r₀ : Sym → Sym := id

/-- **Keying the query alone misses the stored alias** (w6's trap, on these
terms): with the classes joined, the query `(Probe Warm)` keyed by the joined
section is not the stored `(Probe Cold)` keyed literally; keyed by the same
section on both sides, they meet. -/
theorem query_only_misses :
    (GTerm.app (.sym Sym.probe) (.sym Sym.warm)).map (relabel r₀ .cold .warm) ≠
      (GTerm.app (.sym Sym.probe) (.sym Sym.cold)).map r₀ ∧
    (GTerm.app (.sym Sym.probe) (.sym Sym.warm)).map (relabel r₀ .cold .warm) =
      (GTerm.app (.sym Sym.probe) (.sym Sym.cold)).map (relabel r₀ .cold .warm) := by
  constructor
  · simp [GTerm.map, relabel, r₀]
  · simp [GTerm.map, relabel, r₀]

/-- **Re-filing must cover the whole absorbed class**: with `Cold` already in a
class, a row mentioning `Cold` changes key under the merge even if it does not
mention the class's printed member. -/
theorem absorbed_member_moves :
    (GTerm.app (.sym Sym.probe) (.sym Sym.cold)).map (relabel r₀ .cold .warm) ≠
      (GTerm.app (.sym Sym.probe) (.sym Sym.cold)).map r₀ := by
  simp [GTerm.map, relabel, r₀]

end Controls

end Mettapedia.GSLT.Contracts.ScopedAliasSections
