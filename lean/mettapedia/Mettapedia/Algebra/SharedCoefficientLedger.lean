import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Ordered coefficients with shared physical factors

A ledger records factors by physical identity, dependency and coefficient.
Merging two branches keeps their identical inherited prefix once and then
appends disjoint fresh suffixes in logical left-before-right order. A repeated
identity outside the shared prefix, including a conflicting value or dependency,
is refused. Equal values with different identities remain separate factors.

The construction is independent of an execution language or coefficient
interpreter. Its denotation needs a monoid, not commutative multiplication.
Ownership and validity of a concrete memory representation are separate runtime
correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SharedCoefficientLedger

universe uId uDependency uValue uOwner

structure Factor (Identity : Type uId) (Dependency : Type uDependency) (V : Type uValue) where
  identity : Identity
  dependency : Dependency
  coefficient : V
  deriving DecidableEq, Repr

variable {Identity : Type uId} {Dependency : Type uDependency} {V : Type uValue}

abbrev Ledger (Identity : Type uId) (Dependency : Type uDependency) (V : Type uValue) :=
  List (Factor Identity Dependency V)

def identities (ledger : Ledger Identity Dependency V) : List Identity :=
  ledger.map Factor.identity

/-- Each physical factor occurs at most once within one execution world. -/
def Valid (ledger : Ledger Identity Dependency V) : Prop := (identities ledger).Nodup

instance [DecidableEq Identity] (ledger : Ledger Identity Dependency V) :
    Decidable (Valid ledger) := inferInstanceAs (Decidable (identities ledger).Nodup)

structure PrefixSplit (Identity : Type uId) (Dependency : Type uDependency) (V : Type uValue) where
  shared : Ledger Identity Dependency V
  leftFresh : Ledger Identity Dependency V
  rightFresh : Ledger Identity Dependency V
  deriving Repr

/-- Compare complete factors, so identity agreement cannot conceal a changed
coefficient or dependency. -/
def splitPrefix [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V] :
    Ledger Identity Dependency V → Ledger Identity Dependency V →
      PrefixSplit Identity Dependency V
  | first :: left, second :: right =>
      if first = second then
        let rest := splitPrefix left right
        ⟨first :: rest.shared, rest.leftFresh, rest.rightFresh⟩
      else ⟨[], first :: left, second :: right⟩
  | left, right => ⟨[], left, right⟩

theorem splitPrefix_reconstruct [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right : Ledger Identity Dependency V) :
    (splitPrefix left right).shared ++ (splitPrefix left right).leftFresh = left ∧
      (splitPrefix left right).shared ++ (splitPrefix left right).rightFresh = right := by
  induction left generalizing right with
  | nil => simp [splitPrefix]
  | cons first rest ih =>
      cases right with
      | nil => simp [splitPrefix]
      | cons second later =>
          by_cases same : first = second
          · subst second
            simpa [splitPrefix] using ih later
          · simp [splitPrefix, same]

def PrefixSplit.ordered (parts : PrefixSplit Identity Dependency V) : Ledger Identity Dependency V :=
  parts.shared ++ parts.leftFresh ++ parts.rightFresh

/-- The caller's logical branch order is explicit; completion order is not an input. -/
def merge? [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right : Ledger Identity Dependency V) : Option (Ledger Identity Dependency V) :=
  let merged := (splitPrefix left right).ordered
  if Valid merged then some merged else none

theorem merge_accepted_iff [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right merged : Ledger Identity Dependency V) :
    merge? left right = some merged ↔
      merged = (splitPrefix left right).ordered ∧ Valid merged := by
  dsimp [merge?]
  by_cases accepted : Valid (splitPrefix left right).ordered <;> simp_all [eq_comm]

theorem merge_valid [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) : Valid merged :=
  ((merge_accepted_iff left right merged).mp accepted).2

/-- The stateful API installs a merged ledger only after successful validation. -/
def commitMerge [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right : Ledger Identity Dependency V) : Ledger Identity Dependency V × Bool :=
  match merge? left right with
  | none => (left, false)
  | some merged => (merged, true)

theorem refused_merge_retains_state [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right : Ledger Identity Dependency V) (refused : merge? left right = none) :
    commitMerge left right = (left, false) := by simp [commitMerge, refused]

theorem merge_contains_left [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) : ∀ factor ∈ left, factor ∈ merged := by
  obtain ⟨rfl, _⟩ := (merge_accepted_iff left right merged).mp accepted
  intro factor present
  rw [← (splitPrefix_reconstruct left right).1] at present
  simp only [PrefixSplit.ordered, List.mem_append] at *
  tauto

theorem merge_contains_right [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) : ∀ factor ∈ right, factor ∈ merged := by
  obtain ⟨rfl, _⟩ := (merge_accepted_iff left right merged).mp accepted
  intro factor present
  rw [← (splitPrefix_reconstruct left right).2] at present
  simp only [PrefixSplit.ordered, List.mem_append] at *
  tauto

theorem merge_no_new_factor [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) :
    ∀ factor ∈ merged, factor ∈ left ∨ factor ∈ right := by
  obtain ⟨rfl, _⟩ := (merge_accepted_iff left right merged).mp accepted
  intro factor present
  rcases List.mem_append.mp present with fromLeft | fromRight
  · exact Or.inl ((splitPrefix_reconstruct left right).1 ▸ fromLeft)
  · exact Or.inr ((splitPrefix_reconstruct left right).2 ▸
      List.mem_append.mpr (Or.inr fromRight))

/-- Chronological appending refuses a previously charged physical identity. -/
def append? [DecidableEq Identity] (ledger : Ledger Identity Dependency V)
    (factor : Factor Identity Dependency V) : Option (Ledger Identity Dependency V) :=
  if factor.identity ∈ identities ledger then none else some (ledger ++ [factor])

theorem append_valid [DecidableEq Identity]
    {ledger next : Ledger Identity Dependency V} {factor : Factor Identity Dependency V}
    (valid : Valid ledger) (accepted : append? ledger factor = some next) : Valid next := by
  unfold append? at accepted
  split at accepted
  · simp at accepted
  · cases accepted
    simpa [Valid, identities, List.nodup_append] using
      And.intro valid (show (identities ledger).Disjoint [factor.identity] from by simp_all)

def denote [Monoid V] (ledger : Ledger Identity Dependency V) : V :=
  (ledger.map Factor.coefficient).prod

theorem denote_append [Monoid V] (left right : Ledger Identity Dependency V) :
    denote (left ++ right) = denote left * denote right := by
  simp [denote, List.prod_append]

/-- Shared work is interpreted once, before both logically ordered suffixes. -/
theorem merge_denotation [Monoid V] [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) :
    denote merged = denote (splitPrefix left right).shared *
      denote (splitPrefix left right).leftFresh * denote (splitPrefix left right).rightFresh := by
  rw [((merge_accepted_iff left right merged).mp accepted).1, PrefixSplit.ordered]
  rw [denote_append, denote_append]

/-! ## Scoped observations of shared productions -/

/-- Handling a factor retains its production and records the observation
which owns it. This is a semantic map; a finite native representation has its
own allocation and representation obligations. -/
structure Scoped (Identity : Type uId) (Dependency : Type uDependency)
    (V : Type uValue) (Owner : Type uOwner) where
  productions : Ledger Identity Dependency V
  claims : Identity → Option Owner

namespace Scoped

variable {Owner : Type uOwner}

/-- Every claimed identity denotes an actual production in the world. -/
def Supported (world : Scoped Identity Dependency V Owner) : Prop :=
  ∀ identity owner, world.claims identity = some owner → identity ∈ identities world.productions

/-- Observe only unhandled productions after the captured entry position.
The prefix check belongs to admission of the enclosing scope. -/
def selected (entry : Nat) (world : Scoped Identity Dependency V Owner) :
    Ledger Identity Dependency V :=
  (world.productions.drop entry).filter fun factor => (world.claims factor.identity).isNone

theorem mem_selected (entry : Nat) (world : Scoped Identity Dependency V Owner)
    (factor : Factor Identity Dependency V) :
    factor ∈ selected entry world ↔
      factor ∈ world.productions.drop entry ∧ world.claims factor.identity = none := by
  simp [selected]

/-- The observation claims its snapshot before executing any readout callback.
It never rewrites the production list or an already owned contribution. -/
def handle [DecidableEq Identity] (entry : Nat) (owner : Owner)
    (world : Scoped Identity Dependency V Owner) : Scoped Identity Dependency V Owner where
  productions := world.productions
  claims identity := if identity ∈ identities (selected entry world) then some owner
    else world.claims identity

theorem selected_claimed [DecidableEq Identity] (entry : Nat) (owner : Owner)
    (world : Scoped Identity Dependency V Owner) {factor : Factor Identity Dependency V}
    (present : factor ∈ selected entry world) :
    (handle entry owner world).claims factor.identity = some owner := by
  have member : factor.identity ∈ identities (selected entry world) :=
    List.mem_map.mpr ⟨factor, present, rfl⟩
  simp only [handle, member, if_true]

/-- Handling a nested scope cannot move a contribution away from its existing
owner, including one inherited from a shared producer. -/
theorem prior_claim_preserved [DecidableEq Identity] (entry : Nat) (owner : Owner)
    (world : Scoped Identity Dependency V Owner) {identity : Identity} {prior : Owner}
    (claimed : world.claims identity = some prior) :
    (handle entry owner world).claims identity = some prior := by
  have absent : identity ∉ identities (selected entry world) := by
    rintro member
    obtain ⟨factor, present, equal⟩ := List.mem_map.mp member
    have free := ((mem_selected entry world factor).mp present).2
    rw [equal, claimed] at free
    cases free
  simp [handle, absent, claimed]

/-- Re-entering the same snapshot cannot charge any of its handled factors a
second time. New callback productions require a later, larger world. -/
theorem selected_after_handle [DecidableEq Identity] (entry : Nat) (owner : Owner)
    (world : Scoped Identity Dependency V Owner) :
    selected entry (handle entry owner world) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro factor present
  obtain ⟨inSuffix, unclaimed⟩ := (mem_selected entry (handle entry owner world) factor).mp present
  change factor ∈ world.productions.drop entry at inSuffix
  cases original : world.claims factor.identity with
  | none =>
      have owned := selected_claimed entry owner world
        ((mem_selected entry world factor).mpr ⟨inSuffix, original⟩)
      rw [owned] at unclaimed
      cases unclaimed
  | some prior =>
      rw [prior_claim_preserved entry owner world original] at unclaimed
      cases unclaimed

/-- Factors outside the captured snapshot retain their claim state. In
particular, a fresh callback production is available to the enclosing scope. -/
theorem outside_snapshot_unchanged [DecidableEq Identity] (entry : Nat) (owner : Owner)
    (world : Scoped Identity Dependency V Owner) {identity : Identity}
    (outside : identity ∉ identities (selected entry world)) :
    (handle entry owner world).claims identity = world.claims identity := by
  simp [handle, outside]

theorem handle_supported [DecidableEq Identity] (entry : Nat) (owner : Owner)
    (world : Scoped Identity Dependency V Owner) (supported : world.Supported) :
    (handle entry owner world).Supported := by
  intro identity claimant claimed
  dsimp [handle] at claimed ⊢
  split at claimed
  · next member =>
      obtain ⟨factor, present, equal⟩ := List.mem_map.mp member
      apply List.mem_map.mpr
      refine ⟨factor, ?_, equal⟩
      exact List.mem_of_mem_drop ((mem_selected entry world factor).mp present).1
  · exact supported identity claimant claimed

/-- Both worlds may know a claim, but then they must name the same observer. -/
def compatibleAt [DecidableEq Owner] (left right : Scoped Identity Dependency V Owner)
    (identity : Identity) : Bool :=
  match left.claims identity, right.claims identity with
  | some first, some second => decide (first = second)
  | _, _ => true

/-- Reuse the production merge, then check ownership for every retained
identity. Logical branch order is inherited from the production ledger. -/
def merge? [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V] [DecidableEq Owner]
    (left right : Scoped Identity Dependency V Owner) : Option (Scoped Identity Dependency V Owner) :=
  match SharedCoefficientLedger.merge? left.productions right.productions with
  | none => none
  | some productions =>
      if productions.all (fun factor => compatibleAt left right factor.identity) then
        some ⟨productions, fun identity => (left.claims identity).or (right.claims identity)⟩
      else none

/-- Successful scoped merging exposes both its production comparison and
the agreement check on owners; the claim map is their pointwise union. -/
theorem merge_spec [DecidableEq Identity] [DecidableEq Dependency]
    [DecidableEq V] [DecidableEq Owner]
    {left right result : Scoped Identity Dependency V Owner}
    (accepted : merge? left right = some result) :
    SharedCoefficientLedger.merge? left.productions right.productions = some result.productions ∧
      result.productions.all (fun factor => compatibleAt left right factor.identity) = true ∧
      ∀ identity, result.claims identity = (left.claims identity).or (right.claims identity) := by
  unfold merge? at accepted
  cases productionMerge : SharedCoefficientLedger.merge? left.productions right.productions with
  | none => simp [productionMerge] at accepted
  | some productions =>
      simp only [productionMerge] at accepted
      split at accepted
      · cases accepted
        exact ⟨rfl, ‹_ = true›, fun _ => rfl⟩
      · cases accepted

theorem merge_preserves_left_claim [DecidableEq Identity] [DecidableEq Dependency]
    [DecidableEq V] [DecidableEq Owner]
    {left right result : Scoped Identity Dependency V Owner}
    (accepted : merge? left right = some result) {identity : Identity} {owner : Owner}
    (claimed : left.claims identity = some owner) : result.claims identity = some owner := by
  rw [(merge_spec accepted).2.2, claimed]
  rfl

/-- A compatible right-hand claim also survives, including when the left
world is the older unclaimed snapshot. -/
theorem merge_preserves_right_claim [DecidableEq Identity] [DecidableEq Dependency]
    [DecidableEq V] [DecidableEq Owner]
    {left right result : Scoped Identity Dependency V Owner}
    (supported : right.Supported) (accepted : merge? left right = some result)
    {identity : Identity} {owner : Owner} (claimed : right.claims identity = some owner) :
    result.claims identity = some owner := by
  obtain ⟨productions, compatible, claims⟩ := merge_spec accepted
  obtain ⟨factor, present, same⟩ := List.mem_map.mp (supported identity owner claimed)
  have retained := merge_contains_right productions factor present
  have allowed := List.all_eq_true.mp compatible factor retained
  cases prior : left.claims identity with
  | none => rw [claims, prior, claimed]; rfl
  | some previous =>
      have equal : previous = owner := by
        simpa [compatibleAt, same, prior, claimed] using allowed
      rw [claims, prior, equal]
      rfl

/-- Refusal is mandatory when two supported observations claim one occurrence
under different owners, even if both return the same coefficient or value. -/
theorem conflicting_claims_refused [DecidableEq Identity] [DecidableEq Dependency]
    [DecidableEq V] [DecidableEq Owner]
    (left right : Scoped Identity Dependency V Owner) (supported : right.Supported)
    {identity : Identity} {first second : Owner}
    (one : left.claims identity = some first) (two : right.claims identity = some second)
    (different : first ≠ second) : merge? left right = none := by
  cases result : merge? left right with
  | none => rfl
  | some merged =>
      have leftClaim := merge_preserves_left_claim result one
      have rightClaim := merge_preserves_right_claim supported result two
      exact False.elim (different (Option.some.inj (leftClaim.symm.trans rightClaim)))

/-- A captured prefix has to agree in production identity, dependency, value,
and every claim it already knew. Newer claims in the suffix remain allowed. -/
def extendsCapture [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V] [DecidableEq Owner]
    (entry world : Scoped Identity Dependency V Owner) : Bool :=
  entry.productions.isPrefixOf world.productions &&
    entry.productions.all (fun factor => match entry.claims factor.identity with
      | none => true
      | some owner => decide (world.claims factor.identity = some owner))

/-- The scoped interface validates its capture before claiming the snapshot.
Allocation failure and identity-generation authority are native obligations. -/
def handle? [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V] [DecidableEq Owner]
    (entry world : Scoped Identity Dependency V Owner) (owner : Owner) :
    Option (Scoped Identity Dependency V Owner × Ledger Identity Dependency V) :=
  if extendsCapture entry world then
    some (handle entry.productions.length owner world, selected entry.productions.length world)
  else none

/-- Successful handling retains the whole production world and returns only
the selected snapshot, whose factors are unavailable to any enclosing read. -/
theorem handle_spec [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    [DecidableEq Owner] {entry world result : Scoped Identity Dependency V Owner}
    {owner : Owner} {observed : Ledger Identity Dependency V}
    (accepted : handle? entry world owner = some (result, observed)) :
    result.productions = world.productions ∧
      observed = selected entry.productions.length world ∧
      selected entry.productions.length result = [] := by
  unfold handle? at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, rfl, selected_after_handle _ _ _⟩
  · cases accepted

end Scoped

end Mettapedia.Algebra.SharedCoefficientLedger
