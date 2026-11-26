import Mettapedia.GSLT.LanguageDef.DefinitionalBaseLanguage
import Mettapedia.GSLT.LanguageDef.DefinitionalAdmission
import Mettapedia.GSLT.Contracts.EquationalIndex

/-! Ordered dispatch at a literal key, modulo the equations of one language.
Only keys are normalized: the caller still receives the original occurrences.
This is not unification modulo equations or rewriting under arbitrary contexts. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.Contracts.ScopedAliasDispatch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.EquationSemantics

variable {K R : Type*}

/-- Build reusable search keys without identifying equal rows. -/
def index (norm : K → K) (key : R → K) (rs : List R) : List (K × R) :=
  rs.map fun r => (norm (key r), r)

def lookup [DecidableEq K] (q : K) (ix : List (K × R)) : List R :=
  ix.filterMap fun (k, r) => if k = q then some r else none

theorem lookup_index [DecidableEq K] (norm : K → K) (key : R → K) (rs : List R) (q : K) :
    lookup q (index norm key rs) = rs.filter (fun r => decide (norm (key r) = q)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases matchKey : norm (key r) = q <;> simp [lookup, index, matchKey] at ih ⊢ <;> exact ih

/-- The exact condition for using *raw* keys for this query and catalogue.
For all possible catalogues it says the query's equivalence class is a singleton. -/
theorem raw_lookup_iff [DecidableEq K] (norm : K → K) (key : R → K) (rs : List R) (q : K) :
    lookup q (index id key rs) = lookup (norm q) (index norm key rs) ↔
      ∀ r ∈ rs, norm (key r) = norm q → key r = q := by
  simp only [lookup_index, id_eq]
  constructor
  · intro eq r member matched
    have inside : r ∈ rs.filter (fun x => decide (norm (key x) = norm q)) :=
      List.mem_filter.mpr ⟨member, decide_eq_true matched⟩
    rw [← eq] at inside
    exact of_decide_eq_true (List.mem_filter.mp inside).2
  · intro reflects
    apply List.filter_congr
    intro r member
    simp only [decide_eq_decide]
    exact ⟨congrArg norm, reflects r member⟩

/-- Specifications compare by the authored equation relation, independently of
the key algorithm. The equality is of lists, not just sets of returned values. -/
noncomputable def moduloRead (base : BasePremiseEvaluator) (lang : LanguageDef)
    (key : R → Pattern) (q : Pattern) (rs : List R) : List R := by
  classical
  exact rs.filter fun r => decide (EquationEquiv base lang (key r) q)

theorem indexed_eq_modulo (base : BasePremiseEvaluator) {lang : LanguageDef} {defs : List Row}
    (acyclic : Acyclic defs) (authored : Presents lang defs)
    (noBag : lang.usesCollection .hashBag = false) (noSet : lang.usesCollection .hashSet = false)
    (noAlg : lang.hasAlgebraDeclarations = false)
    (key : R → Pattern) (q : Pattern) (rs : List R) :
    lookup (expand defs q) (index (expand defs) key rs) = moduloRead base lang key q rs := by
  rw [lookup_index]
  apply List.filter_congr
  intro r _
  simpa only [decide_eq_decide] using
    (equationEquiv_iff_expand_eq (base := base) acyclic authored noBag noSet noAlg (key r) q).symm

/-- Compile from the assembled language, not a revision number. The literal
alternative does not call the normalizer or build normalized row keys. -/
inductive Plan (R : Type*) where
  | literal (key : R → Pattern) (rows : List R)
  | keyed (defs : List Row) (entries : List (Pattern × R))

def prepare? (lang : LanguageDef) (key : R → Pattern) (rs : List R) : Option (Plan R) :=
  if checkDefinitional lang then
    match definitions lang with
    | [] => some (.literal key rs)
    | d :: ds => some (.keyed (d :: ds) (index (expand (d :: ds)) key rs))
  else none

def Plan.answers (p : Plan R) (q : Pattern) : List R :=
  match p with
  | .literal key rs => rs.filter (fun r => decide (key r = q))
  | .keyed defs ix => lookup (expand defs q) ix

theorem prepare_exact (base : BasePremiseEvaluator) (lang : LanguageDef) (key : R → Pattern)
    (rs : List R) (plan : Plan R) (loaded : prepare? lang key rs = some plan) (q : Pattern) :
    plan.answers q = moduloRead base lang key q rs := by
  by_cases h : checkDefinitional lang = true
  · have cert := checkDefinitional_sound h
    have exactRead := indexed_eq_modulo base cert.acyclic cert.presents cert.noBags cert.noSets
      cert.noAlgebra key q rs
    cases defs : definitions lang with
    | nil =>
      simp [prepare?, h, defs] at loaded
      subst plan
      refine Eq.trans ?_ exactRead
      rw [defs, lookup_index]
      apply List.filter_congr
      intro r _
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, expand_nil]
      exact ⟨fun same => decide_eq_true same, of_decide_eq_true⟩
    | cons d ds =>
      simp [prepare?, h, defs] at loaded
      subst plan
      simpa only [defs, Plan.answers] using exactRead
  · simp [prepare?, h] at loaded

theorem unavailable_iff (lang : LanguageDef) (key : R → Pattern) (rs : List R) :
    prepare? lang key rs = none ↔ checkDefinitional lang = false := by
  cases h : checkDefinitional lang <;> cases d : definitions lang <;> simp [prepare?, h, d]

/-- A coordinate of a normal form is invariant under the declared theory;
to use one rigid bucket for an open call it must *also* be fixed by every
admissible instantiation. These are different obligations. -/
theorem rigid_bucket_iff {A V : Type*} [DecidableEq V] (base : BasePremiseEvaluator)
    {lang : LanguageDef} (checked : checkDefinitional lang = true) (project : Pattern → V)
    (instantiate : A → Pattern) (allowed : A → Prop) (answers : Pattern → List A)
    (sem : ∀ row a, a ∈ answers row ↔ allowed a ∧ EquationEquiv base lang (instantiate a) row)
    (fixed : V) :
    (∀ rs, EquationalIndex.indexedAnswers (fun t => project (expand (definitions lang) t))
      (some fixed) answers rs = rs.flatMap answers) ↔
    ∀ a, allowed a → project (expand (definitions lang) (instantiate a)) = fixed := by
  have cert := checkDefinitional_sound checked
  exact EquationalIndex.rigid_exact_iff (equationSetoid base lang) _
    (fun eq => congrArg project ((cert.equationEquiv_iff _ _).1 eq)) instantiate allowed answers sem fixed

/-- The independent quotient step: choose a stored literal rule on a
representative of the current key, then observe its target up to equality. -/
def RootStep (base : BasePremiseEvaluator) (lang : LanguageDef) (lhs rhs : R → Pattern)
    (rs : List R) (q y : Pattern) : Prop :=
  ∃ r ∈ rs, EquationEquiv base lang (lhs r) q ∧ EquationEquiv base lang (rhs r) y

theorem root_successors_iff (base : BasePremiseEvaluator) {lang : LanguageDef} {defs : List Row}
    (acyclic : Acyclic defs) (authored : Presents lang defs)
    (noBag : lang.usesCollection .hashBag = false) (noSet : lang.usesCollection .hashSet = false)
    (noAlg : lang.hasAlgebraDeclarations = false) (lhs rhs : R → Pattern) (rs : List R)
    (q y : Pattern) :
    expand defs y ∈ (lookup (expand defs q) (index (expand defs) lhs rs)).map
      (fun r => expand defs (rhs r)) ↔ RootStep base lang lhs rhs rs q y := by
  rw [lookup_index]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, RootStep]
  constructor
  · rintro ⟨r, ⟨mem, left⟩, right⟩
    exact ⟨r, mem, (equationEquiv_iff_expand_eq acyclic authored noBag noSet noAlg _ _).2 left,
      (equationEquiv_iff_expand_eq acyclic authored noBag noSet noAlg _ _).2 right⟩
  · rintro ⟨r, mem, left, right⟩
    exact ⟨r, ⟨mem, (equationEquiv_iff_expand_eq acyclic authored noBag noSet noAlg _ _).1 left⟩,
      (equationEquiv_iff_expand_eq acyclic authored noBag noSet noAlg _ _).1 right⟩

/-- An undirected support test for a ground alias graph. Isolated vertices
have singleton classes, and conversely: there is no more permissive bypass
that works for every raw catalogue. For contextual rewriting the edges must
be the induced steps on complete keys, not just the names in source text. -/
theorem singleton_iff_isolated (edge : K → K → Prop) (q : K) :
    (∀ x, Relation.EqvGen edge x q → x = q) ↔
      ∀ x, edge x q ∨ edge q x → x = q := by
  constructor
  · intro single x incident
    rcases incident with h | h
    · exact single _ (.rel _ _ h)
    · exact single _ (.symm _ _ (.rel _ _ h))
  · intro isolated
    have invariant {x y : K} (path : Relation.EqvGen edge x y) : x = q ↔ y = q := by
      induction path with
      | rel x y h =>
        exact ⟨fun e => isolated y (Or.inr (e ▸ h)), fun e => isolated x (Or.inl (e ▸ h))⟩
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact fun x path => (invariant path).2 rfl

/-- Once an atomic alias class is known to be isolated, unrelated equations
can be present without requiring canonicalization on either side of this lookup. -/
theorem isolated_raw_lookup [DecidableEq K] (edge : K → K → Prop) (norm : K → K)
    (presents : ∀ x y, Relation.EqvGen edge x y ↔ norm x = norm y)
    (q : K) (isolated : ∀ x, edge x q ∨ edge q x → x = q) (key : R → K) (rs : List R) :
    lookup q (index id key rs) = lookup (norm q) (index norm key rs) := by
  apply (raw_lookup_iff ..).2
  exact fun r _ same => (singleton_iff_isolated edge q).2 isolated _ ((presents (key r) q).2 same)

/-- The finite carrier can be built when alias declarations are loaded.
Reflexive declarations do not enlarge it. -/
def carrier [DecidableEq K] (edges : List (K × K)) : Finset K :=
  (edges.flatMap fun (x,y) => if x = y then [] else [x,y]).toFinset

theorem outside_carrier_iff [DecidableEq K] (edges : List (K × K)) (q : K) :
    q ∉ carrier edges ↔ ∀ x, Relation.EqvGen (fun a b => (a,b) ∈ edges) x q → x = q := by
  rw [singleton_iff_isolated]
  have contact : q ∈ carrier edges ↔ ∃ x, x ≠ q ∧ ((x,q) ∈ edges ∨ (q,x) ∈ edges) := by
    simp only [carrier, List.mem_toFinset, List.mem_flatMap, Prod.exists]
    constructor
    · rintro ⟨a, b, member, touched⟩
      split at touched
      · cases touched
      · rename_i ne
        rcases List.mem_cons.mp touched with rfl | last
        · exact ⟨b, Ne.symm ne, Or.inr member⟩
        · obtain rfl := List.mem_singleton.mp last
          exact ⟨a, ne, Or.inl member⟩
    · rintro ⟨x, ne, left | right⟩
      · exact ⟨x, q, left, by simp [ne]⟩
      · exact ⟨q, x, right, by simp [Ne.symm ne]⟩
  rw [contact]
  constructor
  · intro outside x incident
    by_contra diff
    exact outside ⟨x, diff, incident⟩
  · rintro isolated ⟨x, diff, incident⟩
    exact diff (isolated x incident)

/-- With prepared keys, only the query needs a support check. -/
theorem skip_query (defs : List Row) (key : R → Pattern) (q : Pattern) (rs : List R)
    (clean : ∀ d ∈ defs, Avoids d.head q) :
    lookup q (index (expand defs) key rs) = lookup (expand defs q) (index (expand defs) key rs) := by
  rw [expand_eq_self defs clean]

/-- Without prepared keys both sides must be accounted for. -/
theorem skip_both (defs : List Row) (key : R → Pattern) (q : Pattern) (rs : List R)
    (queryClean : ∀ d ∈ defs, Avoids d.head q)
    (rowsClean : ∀ r ∈ rs, ∀ d ∈ defs, Avoids d.head (key r)) :
    lookup q (index id key rs) = lookup (expand defs q) (index (expand defs) key rs) := by
  apply (raw_lookup_iff _ _ _ _).2
  intro r member same
  simpa only [expand_eq_self defs (rowsClean r member), expand_eq_self defs queryClean] using same

theorem empty_equations (key : R → Pattern) (q : Pattern) (rs : List R) :
    lookup (expand [] q) (index (expand []) key rs) = lookup q (index id key rs) := rfl

private def cold : Pattern := .apply "Cold" []
private def warm : Pattern := .apply "Warm" []
private def defs : List Row := [⟨"Cold", [], warm⟩]
private def stored := [(cold, 1), (warm, 2), (cold, 1)]

/-- The query is already normal. Raw lookup still misses two occurrences;
the prepared lookup preserves their positions and does not rewrite their payloads. -/
theorem fixed_query_can_miss :
    expand defs warm = warm ∧
    lookup warm (index id Prod.fst stored) = [(warm, 2)] ∧
    lookup warm (index (expand defs) Prod.fst stored) = stored := by decide +kernel

end Mettapedia.GSLT.Contracts.ScopedAliasDispatch
