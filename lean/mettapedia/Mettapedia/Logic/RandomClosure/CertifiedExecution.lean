import Mettapedia.Logic.RandomClosure.DistributionalEvidence
import Mettapedia.Logic.WorldModel.DistributionalSpaceExecution
import Mettapedia.Logic.LP.PropositionalChainer

/-!
# Source-derived closure tables and persistent products

The executable response uses the existing finite Horn saturator. Its
correctness is proved against finitary derivations, not an assumed response
table. Product updates rebuild ancestors without division, including when
old rows contain zeros. Counts below concern row multiplications, not bit cost.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.RandomClosure.CertifiedExecution
open Finset Mettapedia.Logic.LP Mettapedia.InformationTheory
open Mettapedia.Logic.RandomClosure.DistributionalEvidence

variable {A : Type} [Fintype A] [DecidableEq A]

structure Source (A : Type) [DecidableEq A] where
  rules : PropProgram A
  base : Finset A
  scope : Finset A
  base_inside : base ⊆ scope
  rules_inside : ∀ r ∈ rules, r.head ∈ scope ∧ r.premises ⊆ scope

namespace Source
variable (s : Source A)

def ruleRelation (body : List A) (head : A) : Prop :=
  ∃ r ∈ s.rules, r.head = head ∧ body.toFinset = r.premises

def component : Component A where
  scope := s.scope
  base := s.base
  rules := s.ruleRelation
  base_scoped := s.base_inside
  rule_scoped body head rule := by
    obtain ⟨r, hr, rfl, heq⟩ := rule
    refine ⟨(s.rules_inside r hr).1, ?_⟩
    intro a ha
    exact (s.rules_inside r hr).2 (heq ▸ List.mem_toFinset.mpr ha)

/-- The executable source closure. -/
def close (seed : Finset A) : Finset A := saturate s.rules (s.base ∪ seed)

theorem close_correct (seed : Finset A) (a : A) :
    a ∈ s.close seed ↔ a ∈ s.component.closure (seed : Set A) := by
  constructor
  · intro member
    have derived := saturate_sound s.rules (s.base ∪ seed) a member
    clear member
    induction derived with
    | fact h => exact FinitaryClosure.seeds_le_close _ _ _ (by simpa [component] using h)
    | @rule r hr _ ih =>
      apply FinitaryClosure.close_closed s.ruleRelation _ r.premises.toList r.head
      · exact ⟨r, hr, rfl, by simp⟩
      · intro b hb; exact ih b (by simpa using hb)
  · intro derived
    apply FinitaryClosure.close_le s.ruleRelation (candidate := fun b => b ∈ s.close seed) _ _ a derived
    · intro b hb
      exact saturate_contains_facts s.rules (s.base ∪ seed) (by simpa [component] using hb)
    · intro body head rule children
      obtain ⟨r, hr, rfl, heq⟩ := rule
      apply rule_closed_saturate s.rules (s.base ∪ seed) hr
      intro b hb
      exact children b (List.mem_toFinset.mp (heq.symm ▸ hb))

/-- Keep precisely the observable interface after source saturation. -/
def responseCode (boundary : Finset A) (seed : Finset boundary) : Finset boundary :=
  Finset.univ.filter fun b => b.val ∈ s.close (seed.image Subtype.val)

theorem responseCode_correct (boundary : Finset A) (seed : Finset boundary) (b : boundary) :
    b ∈ s.responseCode boundary seed ↔
      b ∈ response (boundary : Set A) s.component.closure (seed : Set boundary) := by
  simp only [responseCode, Finset.mem_filter, Finset.mem_univ, true_and, close_correct]
  change b.val ∈ s.component.closure _ ↔ b.val ∈ s.component.closure _
  rw [Finset.coe_image]
  rfl

/-- Admission checks the finite source scope before any response table is built. -/
def ofRaw? (rules : PropProgram A) (base scope : Finset A) : Option (Source A) :=
  if h : base ⊆ scope ∧ ∀ r ∈ rules, r.head ∈ scope ∧ r.premises ⊆ scope then
    some ⟨rules, base, scope, h.1, h.2⟩ else none

omit [Fintype A] in
theorem ofRaw?_none_iff (rules : PropProgram A) (base scope : Finset A) :
    ofRaw? rules base scope = none ↔
      ¬ (base ⊆ scope ∧ ∀ r ∈ rules, r.head ∈ scope ∧ r.premises ⊆ scope) := by
  simp [ofRaw?]

end Source

section Rows
variable {Ω : Type} [Fintype Ω] (sources : Ω → Source A) (weight : Ω → ℚ)
variable (boundary : Finset A)

def rowCode (family : Finset (Finset boundary)) : ℚ :=
  ∑ w, if ∀ T ∈ family, (sources w).responseCode boundary T = T then weight w else 0

noncomputable def encodeFamily (family : Finset (Finset boundary)) : Finset (Set boundary) := by
  classical
  exact family.image (fun T : Finset boundary => (T : Set boundary))

omit [Fintype Ω] in
theorem closed_code (w : Ω) (T : Finset boundary) :
    (sources w).responseCode boundary T = T ↔
      (response (boundary : Set A) (sources w).component.closure).IsClosed (T : Set boundary) := by
  rw [ClosureOperator.isClosed_iff]
  change _ ↔ (response (boundary : Set A) (sources w).component.closure) (T : Set boundary) = (T : Set boundary)
  constructor
  · intro h
    ext b
    change b ∈ (response (boundary : Set A) (sources w).component.closure) (T : Set boundary) ↔ b ∈ T
    rw [← Source.responseCode_correct, h]
  · intro h
    apply Finset.ext
    intro b
    rw [Source.responseCode_correct, h]
    rfl

theorem rowCode_correct (family : Finset (Finset boundary)) :
    rowCode sources weight boundary family =
      commonality weight (fun w => response (boundary : Set A) (sources w).component.closure)
        (encodeFamily boundary family) := by
  classical
  unfold rowCode commonality
  apply Finset.sum_congr rfl
  intro w _
  have same : (∀ T ∈ family, (sources w).responseCode boundary T = T) ↔
      Closes (response (boundary : Set A) (sources w).component.closure) (encodeFamily boundary family) := by
    simp only [Closes, encodeFamily, Finset.forall_mem_image, closed_code]
  simp only [same]

def avoidingCode (seed : Finset boundary) (q : boundary) : Finset (Finset boundary) :=
  Finset.univ.filter fun T => seed ⊆ T ∧ q ∉ T

/-- Executable inclusion-exclusion over source-compiled closure tests. -/
def queryCode (seed : Finset boundary) (q : boundary) : ℚ :=
  ∑ family ∈ (avoidingCode boundary seed q).powerset,
    (-1 : ℚ)^family.card * rowCode sources weight boundary family

omit [Fintype A] in
theorem encode_avoiding (seed : Finset boundary) (q : boundary) :
    encodeFamily boundary (avoidingCode boundary seed q) = avoiding (seed : Set boundary) q := by
  classical
  ext T
  simp only [encodeFamily, Finset.mem_image, avoidingCode, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_avoiding]
  constructor
  · rintro ⟨U, ⟨hs, hq⟩, rfl⟩; exact ⟨hs, hq⟩
  · intro h
    exact ⟨T.toFinset, ⟨by simpa using h.1, by simpa using h.2⟩, by simp⟩

theorem queryCode_correct (seed : Finset boundary) (q : boundary) :
    queryCode sources weight boundary seed q =
      ∑ w, if q ∈ (sources w).responseCode boundary seed then weight w else 0 := by
  classical
  have faithful : Function.Injective (fun U : Finset boundary => (U : Set boundary)) := Finset.coe_injective
  have eqExtract : queryCode sources weight boundary seed q =
      extract weight (fun w => response (boundary : Set A) (sources w).component.closure)
        (seed : Set boundary) q := by
    unfold extract
    rw [← encode_avoiding boundary seed q]
    unfold encodeFamily
    rw [Finset.powerset_image, Finset.sum_image]
    · unfold queryCode
      apply Finset.sum_congr rfl
      intro family _
      rw [Finset.card_image_of_injective _ faithful, rowCode_correct]
      rfl
    · intro x _ y _ h
      exact Finset.image_injective faithful h
  rw [eqExtract, extract_correct]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Source.responseCode_correct]

/-- Materialize a declared row bank once; the returned function reads the array. -/
def prepareRows {K : Nat} (bank : Fin K → Finset (Finset boundary)) : Fin K → ℚ :=
  let data := Array.ofFn (fun k => rowCode sources weight boundary (bank k))
  fun k => data[k.val]'(by simpa only [data, Array.size_ofFn] using k.isLt)

theorem prepareRows_correct {K : Nat} (bank : Fin K → Finset (Finset boundary)) (k : Fin K) :
    prepareRows sources weight boundary bank k =
      commonality weight (fun w => response (boundary : Set A) (sources w).component.closure)
        (encodeFamily boundary (bank k)) := by
  simp only [prepareRows, Array.getElem_ofFn]
  exact rowCode_correct sources weight boundary (bank k)

/-- The executable query has exactly the existing prepared-extraction meaning,
independently of whether equal intersection hulls are merged by a backend. -/
theorem queryCode_eq_prepared (seed : Finset boundary) (q : boundary) :
    queryCode sources weight boundary seed q =
      preparedExtract weight (fun w => response (boundary : Set A) (sources w).component.closure)
        (seed : Set boundary) q := by
  classical
  rw [preparedExtract_correct, queryCode_correct]
  apply Finset.sum_congr rfl
  intro w _
  change (if q ∈ (sources w).responseCode boundary seed then weight w else 0) =
    (if q ∈ response (boundary : Set A) (sources w).component.closure (seed : Set boundary) then weight w else 0)
  simp only [Source.responseCode_correct]

/-- Finite intersection closure of a family, including the empty intersection. -/
def intersectionCode (family : Finset (Finset boundary)) : Finset boundary :=
  Finset.univ.filter fun b => ∀ T ∈ family, b ∈ T

def hullCode (family : Finset (Finset boundary)) : Finset (Finset boundary) :=
  family.powerset.image (intersectionCode boundary)

omit [Fintype A] in
theorem intersectionCode_correct (family : Finset (Finset boundary)) :
    (intersectionCode boundary family : Set boundary) = sInf (encodeFamily boundary family : Set (Set boundary)) := by
  classical
  ext b
  simp [intersectionCode, encodeFamily]

omit [Fintype A] in
theorem hullCode_correct (family : Finset (Finset boundary)) :
    encodeFamily boundary (hullCode boundary family) = meetHull (encodeFamily boundary family) := by
  classical
  unfold encodeFamily hullCode meetHull
  rw [Finset.powerset_image]
  simp only [Finset.image_image]
  apply Finset.image_congr
  intro members _
  exact intersectionCode_correct boundary members

theorem rowCode_hull (family : Finset (Finset boundary)) :
    rowCode sources weight boundary (hullCode boundary family) = rowCode sources weight boundary family := by
  rw [rowCode_correct, hullCode_correct, commonality_meetHull, rowCode_correct]

def preparedFamilies (seed : Finset boundary) (q : boundary) : Finset (Finset (Finset boundary)) :=
  (avoidingCode boundary seed q).powerset.image (hullCode boundary)

def coefficient (seed : Finset boundary) (q : boundary) (row : Finset (Finset boundary)) : ℚ :=
  ∑ family ∈ (avoidingCode boundary seed q).powerset with hullCode boundary family = row,
    (-1 : ℚ)^family.card

/-- Prepared query coefficients merge families with the same intersection hull. -/
def preparedQueryCode (seed : Finset boundary) (q : boundary) : ℚ :=
  ∑ row ∈ preparedFamilies boundary seed q,
    coefficient boundary seed q row * rowCode sources weight boundary row

theorem preparedQueryCode_eq_queryCode (seed : Finset boundary) (q : boundary) :
    preparedQueryCode sources weight boundary seed q = queryCode sources weight boundary seed q := by
  unfold preparedQueryCode coefficient preparedFamilies queryCode
  simp_rw [Finset.sum_mul]
  have grouped := Finset.sum_fiberwise_of_maps_to
    (s := (avoidingCode boundary seed q).powerset)
    (t := (avoidingCode boundary seed q).powerset.image (hullCode boundary))
    (g := hullCode boundary) (fun F h => Finset.mem_image_of_mem (hullCode boundary) h)
    (fun F => (-1 : ℚ)^F.card * rowCode sources weight boundary F)
  rw [← grouped]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro family member
  rw [← (Finset.mem_filter.mp member).2, rowCode_hull]

omit [Fintype A] in
/-- Transport a finite family coefficient sum to the set-based semantics. -/
theorem coefficient_transport (seed : Finset boundary) (q : boundary)
    (rows : Finset (Finset boundary) → ℚ) (meaning : Finset (Set boundary) → ℚ)
    (agrees : ∀ F, rows F = meaning (encodeFamily boundary F)) :
    (∑ F ∈ (avoidingCode boundary seed q).powerset, (-1 : ℚ)^F.card * rows F) =
      ∑ F ∈ (avoiding (seed : Set boundary) q).powerset, (-1 : ℚ)^F.card * meaning F := by
  classical
  rw [← encode_avoiding boundary seed q]
  unfold encodeFamily
  rw [Finset.powerset_image, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro F _
    rw [Finset.card_image_of_injective _ Finset.coe_injective, agrees]
    rfl
  · intro x _ y _ h
    exact Finset.image_injective Finset.coe_injective h

end Rows

section ReferenceTables
open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable
variable {m : Nat} (positive : 0 < m)
abbrev worldDomain : Fin 1 → Nat := fun _ => m

def worldTable (f : Fin m → ℚ) : Table (worldDomain (m := m)) :=
  tabulate worldDomain (fun _ => positive) [0] (by decide) (fun x => f (x 0))

def referenceMass (f : Fin m → ℚ) : ℚ :=
  queryWeight worldDomain (fun _ => positive) [worldTable positive f] [] [0]

theorem referenceMass_correct (f : Fin m → ℚ) : referenceMass positive f = ∑ w, f w := by
  rw [referenceMass, queryWeight_correct _ _ _ _ _ (by intro v; fin_cases v; simp)]
  have val (x : Config (worldDomain (m := m))) :
      (worldTable positive f).value worldDomain (fun _ => positive) x = f (x 0) := by
    apply tabulate_value
    intro a b h
    rw [h 0 (by simp)]
  simp only [satisfies, List.not_mem_nil, false_implies, implies_true, if_true,
    combineAll_value, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, val]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin m)) _ _ (fun _ => rfl)

variable (sources : Fin m → Source A) (weights : Fin m → ℚ) (boundary : Finset A)

def referenceProbability (seed : Finset boundary) (q : boundary) : Option ℚ :=
  let z := referenceMass positive weights
  if 0 < z then some (referenceMass positive
    (fun w => if q ∈ (sources w).responseCode boundary seed then weights w else 0) / z) else none

def compiledProbability (seed : Finset boundary) (q : boundary) : Option ℚ :=
  let z := ∑ w, weights w
  if 0 < z then some (queryCode sources weights boundary seed q / z) else none

theorem compiled_eq_reference (seed : Finset boundary) (q : boundary) :
    compiledProbability sources weights boundary seed q =
      referenceProbability positive sources weights boundary seed q := by
  simp only [compiledProbability, referenceProbability, referenceMass_correct, queryCode_correct]

open Mettapedia.Logic.DistributionalSpace Mettapedia.ProbabilityTheory.BayesianInference
variable {O Id Θ : Type} [Fintype O]

/-- Exact rational input weights are interpreted as the Space's unnormalized
world masses. This is a representation condition, not an approximation claim. -/
theorem compiled_eq_space (model : Model Θ (Fin m) O Id) (θ : Θ) (E : Finset Id)
    (represents : ∀ w, (weights w : ℝ) = (model.prior θ).1 w * model.likelihood θ E w)
    (seed : Finset boundary) (q : boundary) :
    (compiledProbability sources weights boundary seed q).map (fun r => (r : ℝ)) =
      model.probability? θ E (fun w => decide (q ∈ (sources w).responseCode boundary seed)) := by
  rw [Model.probability?_formula]
  have z : model.normalizer θ E = ((∑ w, weights w : ℚ) : ℝ) := by
    simp only [Model.normalizer, evidence, ← represents, Rat.cast_sum]
  rw [z]
  have num : (∑ w, if decide (q ∈ (sources w).responseCode boundary seed) then
      (model.prior θ).1 w * model.likelihood θ E w else 0) =
      ((queryCode sources weights boundary seed q : ℚ) : ℝ) := by
    rw [queryCode_correct, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : q ∈ (sources w).responseCode boundary seed <;> simp [h, represents]
  rw [num]
  have hp : (0 : ℝ) < ((∑ w, weights w : ℚ) : ℝ) ↔ 0 < ∑ w, weights w := by norm_cast
  simp only [compiledProbability, hp]
  split_ifs <;> simp

end ReferenceTables

/-! A generic persistent tree over row vectors. A path chooses one occurrence,
so repeated component contents do not confuse component identity. -/
inductive Tree (R : Type) where
  | leaf (row : R)
  | node (left right : Tree R) (cached : R)
  deriving Repr, DecidableEq

namespace Tree
variable {R : Type} [CommMonoid R]

def root : Tree R → R
  | .leaf r => r
  | .node _ _ r => r

def meaning : Tree R → R
  | .leaf r => r
  | .node l r _ => meaning l * meaning r

def Valid : Tree R → Prop
  | .leaf _ => True
  | .node l r v => Valid l ∧ Valid r ∧ v = root l * root r

def branch (l r : Tree R) : Tree R := .node l r (root l * root r)

theorem root_eq_meaning {t : Tree R} (h : t.Valid) : t.root = t.meaning := by
  induction t with
  | leaf => rfl
  | node l r v il ir => exact h.2.2.trans (congrArg₂ (· * ·) (il h.1) (ir h.2.1))

theorem branch_valid {l r : Tree R} (hl : l.Valid) (hr : r.Valid) : (branch l r).Valid :=
  ⟨hl, hr, rfl⟩

/-- Directions are cached structural addresses, not searches for subtree maxima. -/
def replace : Tree R → List Bool → R → Option (Tree R)
  | .leaf _, [], v => some (.leaf v)
  | .node l r _, false :: p, v => (replace l p v).map fun l' => branch l' r
  | .node l r _, true :: p, v => (replace r p v).map fun r' => branch l r'
  | _, _, _ => none

/-- Independent semantic replacement, ignoring the cached values. -/
def replacedProduct : Tree R → List Bool → R → Option R
  | .leaf _, [], v => some v
  | .node l r _, false :: p, v => (replacedProduct l p v).map (· * meaning r)
  | .node l r _, true :: p, v => (replacedProduct r p v).map (meaning l * ·)
  | _, _, _ => none

theorem replace_correct (t : Tree R) (path : List Bool) (v : R) (valid : t.Valid) :
    ∀ t', replace t path v = some t' → t'.Valid ∧ some t'.root = replacedProduct t path v := by
  induction t generalizing path with
  | leaf old =>
    cases path with
    | nil => intro t' h; cases h; exact ⟨trivial, rfl⟩
    | cons => intro t' h; cases h
  | node l r old il ir =>
    cases path with
    | nil => intro t' h; cases h
    | cons direction path =>
      cases direction <;> simp only [replace, replacedProduct]
      · intro t' h
        obtain ⟨l', hl, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hv, he⟩ := il path valid.1 l' hl
        refine ⟨branch_valid hv valid.2.1, ?_⟩
        rw [← he]
        change some (l'.root * r.root) = some (l'.root * r.meaning)
        rw [root_eq_meaning valid.2.1]
      · intro t' h
        obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hv, he⟩ := ir path valid.2.1 r' hr
        refine ⟨branch_valid valid.1 hv, ?_⟩
        rw [← he]
        change some (l.root * r'.root) = some (l.meaning * r'.root)
        rw [root_eq_meaning valid.1]

def height : Tree R → Nat
  | .leaf _ => 0
  | .node l r _ => max l.height r.height + 1

theorem replace_path_bound (t : Tree R) (path : List Bool) (v : R) (t' : Tree R)
    (h : replace t path v = some t') : path.length ≤ t.height := by
  induction t generalizing path t' with
  | leaf old => cases path <;> simp_all [replace, height]
  | node l r old il ir =>
    cases path with
    | nil => cases h
    | cons dir path =>
      cases dir
      · obtain ⟨l', hl, _⟩ := Option.map_eq_some_iff.mp h
        exact Nat.succ_le_succ ((il path l' hl).trans (Nat.le_max_left _ _))
      · obtain ⟨r', hr, _⟩ := Option.map_eq_some_iff.mp h
        exact Nat.succ_le_succ ((ir path r' hr).trans (Nat.le_max_right _ _))

/-- K row multiplications per rebuilt ancestor; local compilation is separate. -/
theorem row_work_bound (t : Tree R) (path : List Bool) (v : R) (t' : Tree R)
    (h : replace t path v = some t') (K : Nat) : K * path.length ≤ K * t.height :=
  Nat.mul_le_mul_left K (replace_path_bound t path v t' h)

/-- Balanced preparation by splitting a list in halves. -/
def build (rows : List R) : Tree R :=
  match rows with
  | [] => .leaf 1
  | [r] => .leaf r
  | a :: b :: rest =>
    let rows := a :: b :: rest
    branch (build (rows.take (rows.length / 2))) (build (rows.drop (rows.length / 2)))
termination_by rows.length
 decreasing_by all_goals simp_wf; omega

theorem build_valid (rows : List R) : (build rows).Valid := by
  fun_induction build rows with
  | case1 => trivial
  | case2 => trivial
  | case3 a b rest rows il ir => exact branch_valid il ir

theorem build_product (rows : List R) : (build rows).root = rows.prod := by
  fun_induction build rows with
  | case1 => rfl
  | case2 => simp [root]
  | case3 a b rest rows il ir =>
    change (build _).root * (build _).root = _
    rw [il, ir, ← List.prod_append, List.take_append_drop]

end Tree

/-- The source composition tree has no cached answers. -/
inductive Layout (S : Type) where
  | leaf (source : S)
  | fork (left right : Layout S)

namespace Layout
variable {S R : Type} [CommMonoid R]

def compile (f : S → R) : Layout S → Tree R
  | .leaf s => .leaf (f s)
  | .fork l r => Tree.branch (compile f l) (compile f r)

def replace : Layout S → List Bool → S → Option (Layout S)
  | .leaf _, [], s => some (.leaf s)
  | .fork l r, false :: path, s => (replace l path s).map (fun l' => .fork l' r)
  | .fork l r, true :: path, s => (replace r path s).map (fun r' => .fork l r')
  | _, _, _ => none

theorem compile_valid (f : S → R) (source : Layout S) : (compile f source).Valid := by
  induction source with
  | leaf => trivial
  | fork l r il ir => exact Tree.branch_valid il ir

/-- Local cache rebuilding equals recompiling the changed source tree. This
fixes the physical occurrence being replaced, even for equal-valued leaves. -/
theorem replace_compile (f : S → R) (source : Layout S) (path : List Bool) (replacement : S) :
    Tree.replace (compile f source) path (f replacement) =
      (replace source path replacement).map (compile f) := by
  induction source generalizing path with
  | leaf s => cases path <;> rfl
  | fork l r il ir =>
    cases path with
    | nil => rfl
    | cons direction path =>
      cases direction <;> simp only [compile, Tree.branch, Tree.replace, replace]
      · rw [il]; simp only [Option.map_map]; rfl
      · rw [ir]; simp only [Option.map_map]; rfl

end Layout

section CompiledTree
variable {Ω : Type} [Fintype Ω] {N K : Nat}
variable (sources : Fin N → Ω → Source A) (weights : Fin N → Ω → ℚ)
variable (boundary : Finset A) (bank : Fin K → Finset (Finset boundary))

def checkPartition : Bool := decide
  ((∀ i w, boundary ⊆ (sources i w).scope) ∧
    ∀ i j, i ≠ j → ∀ x y, (sources i x).scope ∩ (sources j y).scope ⊆ boundary)

omit [Fintype A] in
theorem checkPartition_correct : checkPartition sources boundary = true ↔
    ((∀ i w, boundary ⊆ (sources i w).scope) ∧
      ∀ i j, i ≠ j → ∀ x y, (sources i x).scope ∩ (sources j y).scope ⊆ boundary) := by
  simp [checkPartition]

/-- A changed scope is re-admitted against every remaining component. -/
def replaceProgram? (i : Fin N) (replacement : Ω → Source A) : Option (Fin N → Ω → Source A) :=
  let updated := Function.update sources i replacement
  if checkPartition updated boundary then some updated else none

omit [Fintype A] in
theorem replaceProgram?_accepted (i : Fin N) (replacement : Ω → Source A) (updated : Fin N → Ω → Source A)
    (accepted : replaceProgram? sources boundary i replacement = some updated) :
    checkPartition updated boundary = true := by
  unfold replaceProgram? at accepted
  dsimp only at accepted
  split_ifs at accepted with h
  cases accepted
  exact h

def compileTree : Tree (Fin K → ℚ) :=
  Tree.build (List.ofFn fun i => prepareRows (sources i) (weights i) boundary bank)

theorem compileTree_valid : (compileTree sources weights boundary bank).Valid := Tree.build_valid _

theorem compileTree_rows (k : Fin K) :
    (compileTree sources weights boundary bank).root k =
      ∏ i, commonality (weights i)
        (fun w => response (boundary : Set A) (sources i w).component.closure)
        (encodeFamily boundary (bank k)) := by
  rw [compileTree, Tree.build_product, List.prod_ofFn]
  simp only [Finset.prod_apply, prepareRows_correct]

/-- The cached rows describe the joined source programs, including feedback
through the boundary, when their private scopes are disjoint. -/
theorem compileTree_source (k : Fin K)
    (inside : ∀ i w, (boundary : Set A) ⊆ (sources i w).component.scope)
    (separated : ∀ i j, i ≠ j → ∀ x y,
      (sources i x).component.scope ∩ (sources j y).component.scope ⊆ (boundary : Set A)) :
    (compileTree sources weights boundary bank).root k =
      commonality (fun w : Fin N → Ω => ∏ i, weights i (w i))
        (fun w => response (boundary : Set A)
          (Component.combineFamily fun i => (sources i (w i)).component).closure)
        (encodeFamily boundary (bank k)) := by
  rw [compileTree_rows]
  convert (component_commonality (fun i w => (sources i w).component) (boundary : Set A)
    inside separated weights (encodeFamily boundary (bank k))).symm using 1
  congr 2
  exact Subsingleton.elim _ _

/-- The all-row reference tree; an implementation may materialize only the
prepared bank using `compileTree` and the proved row interpretation. -/
def fullTree : Tree (Finset (Finset boundary) → ℚ) :=
  Tree.build (List.ofFn fun i => rowCode (sources i) (weights i) boundary)

theorem fullTree_row (F : Finset (Finset boundary)) :
    (fullTree sources weights boundary).root F = ∏ i, rowCode (sources i) (weights i) boundary F := by
  rw [fullTree, Tree.build_product, List.prod_ofFn]
  exact Finset.prod_apply _ _ _

def treeQueryMass (seed : Finset boundary) (q : boundary) : ℚ :=
  ∑ F ∈ (avoidingCode boundary seed q).powerset,
    (-1 : ℚ)^F.card * (fullTree sources weights boundary).root F

open scoped Classical in
theorem treeQueryMass_correct (seed : Finset boundary) (q : boundary)
    (inside : ∀ i w, (boundary : Set A) ⊆ (sources i w).component.scope)
    (separated : ∀ i j, i ≠ j → ∀ x y,
      (sources i x).component.scope ∩ (sources j y).component.scope ⊆ (boundary : Set A)) :
    treeQueryMass sources weights boundary seed q =
      ∑ w : Fin N → Ω,
        if q ∈ response (boundary : Set A)
          (Component.combineFamily fun i => (sources i (w i)).component).closure (seed : Set boundary)
        then ∏ i, weights i (w i) else 0 := by
  classical
  unfold treeQueryMass
  simp_rw [fullTree_row]
  rw [coefficient_transport boundary seed q
    (fun F => ∏ i, rowCode (sources i) (weights i) boundary F)
    (fun F => ∏ i, commonality (weights i)
      (fun w => response (boundary : Set A) (sources i w).component.closure) F)
    (by intro F; simp only [rowCode_correct])]
  convert component_query_mass (fun i w => (sources i w).component) (boundary : Set A)
    inside separated weights (seed : Set boundary) q using 1
  congr 1
  congr 1
  ext w
  simp

def treeProbability (seed : Finset boundary) (q : boundary) : Option ℚ :=
  let z := (fullTree sources weights boundary).root ∅
  if 0 < z then some (treeQueryMass sources weights boundary seed q / z) else none

theorem tree_normalizer : (fullTree sources weights boundary).root ∅ = ∏ i, ∑ w, weights i w := by
  rw [fullTree_row]
  simp [rowCode]

open scoped Classical in
/-- Complete probability contract for joined source programs. The same
normalizer is retained through composition and used only at the final readout. -/
theorem treeProbability_correct (seed : Finset boundary) (q : boundary)
    (inside : ∀ i w, (boundary : Set A) ⊆ (sources i w).component.scope)
    (separated : ∀ i j, i ≠ j → ∀ x y,
      (sources i x).component.scope ∩ (sources j y).component.scope ⊆ (boundary : Set A)) :
    treeProbability sources weights boundary seed q =
      if 0 < ∏ i, ∑ w, weights i w then
        some ((∑ w : Fin N → Ω,
          if q ∈ response (boundary : Set A)
            (Component.combineFamily fun i => (sources i (w i)).component).closure (seed : Set boundary)
          then ∏ i, weights i (w i) else 0) / (∏ i, ∑ w, weights i w)) else none := by
  rw [treeProbability, tree_normalizer, treeQueryMass_correct sources weights boundary seed q inside separated]

/-- Recompile the replacement's source rows before rebuilding its ancestors. -/
def replaceComponent (tree : Tree (Fin K → ℚ)) (path : List Bool)
    (replacement : Ω → Source A) (newWeights : Ω → ℚ) : Option (Tree (Fin K → ℚ)) :=
  tree.replace path (prepareRows replacement newWeights boundary bank)

theorem replaceComponent_correct (tree : Tree (Fin K → ℚ)) (valid : tree.Valid)
    (path : List Bool) (replacement : Ω → Source A) (newWeights : Ω → ℚ)
    (updated : Tree (Fin K → ℚ))
    (h : replaceComponent boundary bank tree path replacement newWeights = some updated) :
    updated.Valid ∧ some updated.root =
      tree.replacedProduct path (prepareRows replacement newWeights boundary bank) :=
  Tree.replace_correct tree path _ valid updated h

end CompiledTree

namespace Controls

def loop : Source (Fin 2) where
  rules := {⟨{0}, 0⟩}
  base := ∅
  scope := Finset.univ
  base_inside := by simp
  rules_inside := by intro r _; simp

def feedback : Source (Fin 2) where
  rules := {⟨{0}, 1⟩, ⟨{1}, 0⟩}
  base := ∅
  scope := Finset.univ
  base_inside := by simp
  rules_inside := by intro r _; simp

theorem self_loop_unsupported : loop.close ∅ = ∅ := by decide +kernel
theorem feedback_propagates : feedback.close {0} = {0,1} := by decide +kernel

theorem exact_compiled_count :
    queryCode (fun _ : Unit => feedback) (fun _ => (1 : ℚ)) Finset.univ {⟨0, by simp⟩} ⟨1, by simp⟩ = 1 := by
  decide +kernel

theorem zero_leaf_replacement :
    Tree.replace (Tree.build ([0, 2, 3, 4] : List ℚ)) [false, false] 5 =
      some (Tree.build [5, 2, 3, 4]) := by decide +kernel

theorem zero_leaf_replacement_value : (Tree.build ([5, 2, 3, 4] : List ℚ)).root = 120 := by decide +kernel

def emptyAt (scope : Finset (Fin 3)) : Source (Fin 3) where
  rules := ∅
  base := ∅
  scope := scope
  base_inside := by simp
  rules_inside := by simp

theorem hidden_scope_rejected :
    checkPartition (fun i : Fin 2 => fun _ : Unit =>
      emptyAt (if i = 0 then {0,1} else {0,1,2})) {0} = false := by decide +kernel

theorem separated_scope_accepted :
    checkPartition (fun i : Fin 2 => fun _ : Unit =>
      emptyAt (if i = 0 then {0,1} else {0,2})) {0} = true := by decide +kernel

theorem undeclared_head_rejected :
    Source.ofRaw? ({⟨{0}, 1⟩} : PropProgram (Fin 2)) ∅ {0} = none := by decide +kernel

theorem reference_agrees_literal :
    referenceProbability (by decide : 0 < 1) (fun _ : Fin 1 => feedback) (fun _ => (1 : ℚ))
      Finset.univ {⟨0, by simp⟩} ⟨1, by simp⟩ = some 1 := by decide +kernel

def cyclePart (i : Fin 2) : Source (Fin 3) where
  rules := if i = 0 then {⟨{0}, 2⟩} else {⟨{1}, 0⟩}
  base := if i = 0 then {1} else ∅
  scope := Finset.univ
  base_inside := by simp
  rules_inside := by intro r _; simp

theorem cross_component_feedback :
    treeProbability (fun i : Fin 2 => fun _ : Unit => cyclePart i) (fun _ _ => (1 : ℚ))
      Finset.univ ∅ ⟨2, by simp⟩ = some 1 := by decide +kernel

def withoutSeed : Source (Fin 3) :=
  { cyclePart 0 with base := ∅, base_inside := by simp }

def changedCycle : Fin 2 → Unit → Source (Fin 3) :=
  Function.update (fun i _ => cyclePart i) 0 (fun _ => withoutSeed)

theorem replaced_cycle_answer :
    treeProbability changedCycle (fun _ _ => (1 : ℚ)) Finset.univ ∅ ⟨2, by simp⟩ = some 0 := by
  decide +kernel

theorem local_rebuild_equals_global_rebuild :
    Tree.replace (fullTree (fun i : Fin 2 => fun _ : Unit => cyclePart i)
      (fun _ _ => (1 : ℚ)) Finset.univ) [false]
      (rowCode (fun _ : Unit => withoutSeed) (fun _ => (1 : ℚ)) Finset.univ) =
      some (fullTree changedCycle (fun _ _ => (1 : ℚ)) Finset.univ) := by
  simp [fullTree, List.ofFn_succ, Tree.build, Tree.replace, Tree.branch, Tree.root, changedCycle]

end Controls

end Mettapedia.Logic.RandomClosure.CertifiedExecution
