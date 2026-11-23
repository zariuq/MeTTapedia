import Mettapedia.ProbabilityTheory.StochasticInference.Binary
import Mettapedia.ProbabilityTheory.StochasticInference.ResidualMass

/-!
# Likelihood bounds at a partially processed diagnostic path

Each processed link transfers a pair of likelihoods toward the query.
An unprocessed link takes convex combinations of that pair. The smaller
and larger likelihood therefore bound every remaining path, regardless
of the unresolved transition rates. At the root the two likelihoods
feed the asymmetric mass envelope.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.BinaryLikelihoodEnvelope

open ResidualMass

structure Range where
  lower : ℚ
  upper : ℚ
  nonnegative : 0 ≤ lower
  ordered : lower ≤ upper

def Range.Contains (r : Range) (x : ℚ) : Prop := r.lower ≤ x ∧ x ≤ r.upper

def Range.Narrows (inner outer : Range) : Prop := outer.lower ≤ inner.lower ∧ inner.upper ≤ outer.upper

theorem Range.narrows_refl (r : Range) : r.Narrows r := ⟨le_rfl, le_rfl⟩

def Range.point (x : ℚ) (valid : 0 ≤ x) : Range := ⟨x, x, valid, le_rfl⟩

def Range.mul (a b : Range) : Range :=
  ⟨a.lower * b.lower, a.upper * b.upper, mul_nonneg a.nonnegative b.nonnegative,
    mul_le_mul a.ordered b.ordered b.nonnegative (a.nonnegative.trans a.ordered)⟩

theorem Range.contains_mul {a b : Range} {x y : ℚ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x * y) :=
  ⟨mul_le_mul hx.1 hy.1 b.nonnegative (a.nonnegative.trans hx.1),
    mul_le_mul hx.2 hy.2 (b.nonnegative.trans hy.1) (a.nonnegative.trans a.ordered)⟩

theorem Range.mul_narrows {a b c d : Range} (first : a.Narrows c) (second : b.Narrows d) :
    (a.mul b).Narrows (c.mul d) :=
  ⟨mul_le_mul first.1 second.1 d.nonnegative (a.nonnegative),
    mul_le_mul first.2 second.2 (b.nonnegative.trans b.ordered) (c.nonnegative.trans c.ordered)⟩

abbrev Message := Bool → UnitProbability
abbrev Kernel := Bool → UnitProbability

def blend (p x y : ℚ) : ℚ := (1 - p) * x + p * y

private theorem blend_mem (p : UnitProbability) {lo hi x y : ℚ}
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) :
    lo ≤ blend p.val x y ∧ blend p.val x y ≤ hi := by
  constructor
  · have cmp := add_le_add (mul_le_mul_of_nonneg_left hx.1 (sub_nonneg.mpr p.le_one))
      (mul_le_mul_of_nonneg_left hy.1 p.nonneg)
    unfold blend
    nlinarith only [cmp]
  · have cmp := add_le_add (mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr p.le_one))
      (mul_le_mul_of_nonneg_left hy.2 p.nonneg)
    unfold blend
    nlinarith only [cmp]

def transfer (kernel : Kernel) (child : Message) : Message := fun parent =>
  let p := kernel parent
  let contained := blend_mem p ⟨(child false).nonneg, (child false).le_one⟩
    ⟨(child true).nonneg, (child true).le_one⟩
  ⟨blend p.val (child false).val (child true).val, contained.1, contained.2⟩

def hull (msg : Message) : Range :=
  ⟨min (msg false).val (msg true).val, max (msg false).val (msg true).val,
    le_min (msg false).nonneg (msg true).nonneg, (min_le_left _ _).trans (le_max_left _ _)⟩

theorem hull_contains (msg : Message) (b : Bool) : (hull msg).Contains (msg b).val := by
  cases b
  · exact ⟨min_le_left _ _, le_max_left _ _⟩
  · exact ⟨min_le_right _ _, le_max_right _ _⟩

private theorem transfer_contains (kernel : Kernel) (msg : Message) (r : Range)
    (bounded : ∀ b, r.Contains (msg b).val) (b : Bool) :
    r.Contains ((transfer kernel msg) b).val :=
  blend_mem (kernel b) (bounded false) (bounded true)

/-- The path is listed in the order in which its links send messages. -/
def send (msg : Message) (links : List Kernel) : Message :=
  links.foldl (fun child kernel => transfer kernel child) msg

theorem send_contains (links : List Kernel) (msg : Message) (r : Range)
    (bounded : ∀ b, r.Contains (msg b).val) (b : Bool) :
    r.Contains ((send msg links) b).val := by
  induction links generalizing msg with
  | nil => exact bounded b
  | cons next rest ih =>
    exact ih (transfer next msg) (transfer_contains next msg r bounded)

def bounds (fuel : Nat) (msg : Message) (links : List Kernel) : Bool → Range :=
  let next := send msg (links.take fuel)
  if fuel < links.length then fun _ => hull next
  else fun b => Range.point (next b).val (next b).nonneg

theorem bounds_sound (fuel : Nat) (msg : Message) (links : List Kernel) (b : Bool) :
    (bounds fuel msg links b).Contains ((send msg links) b).val := by
  by_cases finished : links.length ≤ fuel
  · simp [bounds, if_neg (not_lt_of_ge finished), List.take_of_length_le finished, Range.Contains, Range.point]
  · unfold bounds
    rw [if_pos (lt_of_not_ge finished)]
    have suffix := send_contains (links.drop fuel) (send msg (links.take fuel)) _ (hull_contains _) b
    simpa only [send, ← List.foldl_append, List.take_append_drop] using suffix

theorem bounds_complete (fuel : Nat) (msg : Message) (links : List Kernel)
    (finished : links.length ≤ fuel) (b : Bool) :
    bounds fuel msg links b = Range.point ((send msg links) b).val ((send msg links) b).nonneg := by
  simp [bounds, if_neg (not_lt_of_ge finished), List.take_of_length_le finished]

theorem bounds_narrow (msg : Message) (links : List Kernel) {earlier later : Nat}
    (more : earlier ≤ later) (b : Bool) :
    (bounds later msg links b).Narrows (bounds earlier msg links b) := by
  by_cases complete : links.length ≤ earlier
  · rw [bounds_complete _ _ _ complete, bounds_complete _ _ _ (complete.trans more)]
    exact Range.narrows_refl _
  · have short : earlier < links.length := lt_of_not_ge complete
    let first := send msg (links.take earlier)
    let next := send msg (links.take later)
    have kept : ∀ v, (hull first).Contains (next v).val := by
      intro v
      have moreLinks : links.take later = links.take earlier ++ (links.drop earlier).take (later - earlier) := by
        conv_lhs => rw [← Nat.add_sub_of_le more]
        exact List.take_add
      have h := send_contains ((links.drop earlier).take (later - earlier)) first _ (hull_contains _) v
      simpa only [next, first, moreLinks, send, List.foldl_append] using h
    simp only [bounds, if_pos short]
    by_cases incomplete : later < links.length
    · simp only [if_pos incomplete, Range.Narrows, hull]
      exact ⟨le_min (kept false).1 (kept true).1, max_le (kept false).2 (kept true).2⟩
    · simp only [if_neg incomplete, Range.Narrows, Range.point]
      exact kept b

def partialMass (prior : UnitProbability) (likelihood : Bool → Range) : Partial where
  found := ⟨prior.val * (likelihood true).lower, (1 - prior.val) * (likelihood false).lower,
    mul_nonneg prior.nonneg (likelihood true).nonnegative,
    mul_nonneg (sub_nonneg.mpr prior.le_one) (likelihood false).nonnegative⟩
  unseen := ⟨prior.val * ((likelihood true).upper - (likelihood true).lower),
    (1 - prior.val) * ((likelihood false).upper - (likelihood false).lower),
    mul_nonneg prior.nonneg (sub_nonneg.mpr (likelihood true).ordered),
    mul_nonneg (sub_nonneg.mpr prior.le_one) (sub_nonneg.mpr (likelihood false).ordered)⟩

@[simp] private theorem partialMass_posCap (prior : UnitProbability) (likelihood : Bool → Range) :
    (partialMass prior likelihood).posCap = prior.val * (likelihood true).upper := by
  unfold Partial.posCap partialMass
  dsimp only
  ring

@[simp] private theorem partialMass_negCap (prior : UnitProbability) (likelihood : Bool → Range) :
    (partialMass prior likelihood).negCap = (1 - prior.val) * (likelihood false).upper := by
  unfold Partial.negCap partialMass
  dsimp only
  ring

def exactMass (prior : UnitProbability) (likelihood : Bool → ℚ)
    (valid : ∀ b, 0 ≤ likelihood b) : Masses :=
  ⟨prior.val * likelihood true, (1 - prior.val) * likelihood false,
    mul_nonneg prior.nonneg (valid true), mul_nonneg (sub_nonneg.mpr prior.le_one) (valid false)⟩

theorem partialMass_sound (prior : UnitProbability) (r : Bool → Range) (likelihood : Bool → ℚ)
    (bounded : ∀ b, (r b).Contains (likelihood b)) :
    Completion (partialMass prior r)
      (exactMass prior likelihood (fun b => (r b).nonnegative.trans (bounded b).1)) := by
  have notPrior : 0 ≤ 1 - prior.val := sub_nonneg.mpr prior.le_one
  refine ⟨mul_le_mul_of_nonneg_left (bounded true).1 prior.nonneg,
    mul_le_mul_of_nonneg_left (bounded false).1 notPrior, ?_, ?_⟩
  · rw [partialMass_posCap]
    exact mul_le_mul_of_nonneg_left (bounded true).2 prior.nonneg
  · rw [partialMass_negCap]
    exact mul_le_mul_of_nonneg_left (bounded false).2 notPrior

theorem partialMass_refines (prior : UnitProbability) (inner outer : Bool → Range)
    (narrower : ∀ b, (inner b).Narrows (outer b)) {actual : Masses}
    (admitted : Completion (partialMass prior inner) actual) :
    Completion (partialMass prior outer) actual := by
  have notPrior : 0 ≤ 1 - prior.val := sub_nonneg.mpr prior.le_one
  refine ⟨(mul_le_mul_of_nonneg_left (narrower true).1 prior.nonneg).trans admitted.foundPos,
    (mul_le_mul_of_nonneg_left (narrower false).1 notPrior).trans admitted.foundNeg, ?_, ?_⟩
  · have innerCap := admitted.capPos
    rw [partialMass_posCap] at innerCap ⊢
    exact innerCap.trans (mul_le_mul_of_nonneg_left (narrower true).2 prior.nonneg)
  · have innerCap := admitted.capNeg
    rw [partialMass_negCap] at innerCap ⊢
    exact innerCap.trans (mul_le_mul_of_nonneg_left (narrower false).2 notPrior)

theorem path_interval_narrows (prior : UnitProbability) (leaf : Message) (links : List Kernel)
    {earlier later : Nat} (more : earlier ≤ later) {lo hi : ℚ}
    (answer : (partialMass prior (bounds later leaf links)).interval = some (lo, hi)) :
    ∃ oldLo oldHi, (partialMass prior (bounds earlier leaf links)).interval = some (oldLo, oldHi) ∧
      oldLo ≤ lo ∧ hi ≤ oldHi :=
  interval_narrow (fun _ => partialMass_refines prior _ _ (bounds_narrow leaf links more)) answer

/-- One report on a path, with its links in upward message order. -/
structure Path where
  leaf : Message
  links : List Kernel

def Path.current (path : Path × Nat) (b : Bool) : Range :=
  bounds path.2 path.1.leaf path.1.links b

def Path.full (path : Path) (b : Bool) : ℚ := (send path.leaf path.links b).val

def jointRange (paths : List (Path × Nat)) (b : Bool) : Range :=
  paths.foldr (fun path r => (Path.current path b).mul r) (Range.point 1 (by decide))

/-- Paths in this product represent observations conditionally independent
given the root. Each path may have dependent variables along its length. -/
def jointLikelihood (paths : List (Path × Nat)) (b : Bool) : ℚ :=
  (paths.map fun (path, _) => path.full b).prod

theorem jointRange_sound (paths : List (Path × Nat)) (b : Bool) :
    (jointRange paths b).Contains (jointLikelihood paths b) := by
  induction paths with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons path rest ih =>
    exact Range.contains_mul (bounds_sound path.2 path.1.leaf path.1.links b) ih

theorem jointRange_closed (paths : List (Path × Nat)) (b : Bool)
    (done : ∀ path ∈ paths, path.1.links.length ≤ path.2) :
    (jointRange paths b).lower = jointLikelihood paths b ∧
      (jointRange paths b).upper = jointLikelihood paths b := by
  induction paths with
  | nil => exact ⟨rfl, rfl⟩
  | cons path rest ih =>
    have head := bounds_complete path.2 path.1.leaf path.1.links (done path List.mem_cons_self) b
    have tail := ih (fun r member => done r (List.mem_cons_of_mem _ member))
    simp only [jointRange, Path.current, List.foldr_cons, Range.mul, head, Range.point,
      jointLikelihood, List.map_cons, List.prod_cons, Path.full] at tail ⊢
    exact ⟨by rw [tail.1], by rw [tail.2]⟩

def pathReadout (prior : UnitProbability) (paths : List (Path × Nat)) : Option (ℚ × ℚ) :=
  (partialMass prior (jointRange paths)).interval

theorem pathReadout_sound (prior : UnitProbability) (paths : List (Path × Nat)) :
    let result := exactMass prior (jointLikelihood paths)
      (fun b => (jointRange paths b).nonnegative.trans (jointRange_sound paths b).1)
    0 < result.support →
      ∃ l u, pathReadout prior paths = some (l, u) ∧ l ≤ result.posterior ∧ result.posterior ≤ u :=
  (partialMass_sound prior _ _ (jointRange_sound paths)).interval_sound

theorem pathReadout_complete (prior : UnitProbability) (paths : List (Path × Nat))
    (done : ∀ path ∈ paths, path.1.links.length ≤ path.2)
    (possible : 0 < (partialMass prior (jointRange paths)).found.support) :
    let precise := exactMass prior (jointLikelihood paths)
      (fun b => (jointRange paths b).nonnegative.trans (jointRange_sound paths b).1)
    pathReadout prior paths = some (precise.posterior, precise.posterior) := by
  let state := partialMass prior (jointRange paths)
  have lo (b : Bool) := (jointRange_closed paths b done).1
  have hi (b : Bool) := (jointRange_closed paths b done).2
  have pos : state.unseen.positive = 0 := by simp [state, partialMass, lo, hi]
  have neg : state.unseen.negative = 0 := by simp [state, partialMass, lo, hi]
  change state.interval = _
  rw [state.interval_complete pos neg possible]
  simp only [state, Masses.posterior, Masses.support, exactMass, partialMass, lo]

theorem jointRange_refines {inner outer : List (Path × Nat)}
    (aligned : List.Forall₂ (fun i o : Path × Nat => i.1 = o.1 ∧ o.2 ≤ i.2) inner outer) (b : Bool) :
    (jointRange inner b).Narrows (jointRange outer b) := by
  induction aligned with
  | nil => exact Range.narrows_refl _
  | cons admitted _ ih =>
    obtain ⟨same, more⟩ := admitted
    apply Range.mul_narrows _ ih
    unfold Path.current
    rw [same]
    exact bounds_narrow _ _ more b

theorem pathReadout_refines (prior : UnitProbability) {inner outer : List (Path × Nat)}
    (aligned : List.Forall₂ (fun i o : Path × Nat => i.1 = o.1 ∧ o.2 ≤ i.2) inner outer)
    {l u : ℚ} (read : pathReadout prior inner = some (l, u)) :
    ∃ previousLo previousHi, pathReadout prior outer = some (previousLo, previousHi) ∧
      previousLo ≤ l ∧ u ≤ previousHi :=
  interval_narrow (fun _ => partialMass_refines prior _ _ (jointRange_refines aligned)) read

end Mettapedia.ProbabilityTheory.StochasticInference.BinaryLikelihoodEnvelope
