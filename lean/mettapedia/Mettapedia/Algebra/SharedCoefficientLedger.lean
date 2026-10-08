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

universe uId uDependency uValue uOwner uId' uDependency' uOwner'

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

/-! ## Renaming physical productions

Fresh numeric names may differ between executions. One injective renaming must
apply to all their ledgers; renaming each answer independently would forget
sharing between answers. Dependencies may have a separate type. When both
fields use one name space, the same function must rename both fields.
-/

variable {Identity' : Type uId'} {Dependency' : Type uDependency'}

def Factor.rename (name : Identity → Identity') (dependency : Dependency → Dependency')
    (factor : Factor Identity Dependency V) : Factor Identity' Dependency' V :=
  ⟨name factor.identity, dependency factor.dependency, factor.coefficient⟩

theorem Factor.rename_injective {name : Identity → Identity'}
    {dependency : Dependency → Dependency'} (names : Function.Injective name)
    (dependencies : Function.Injective dependency) :
    Function.Injective (Factor.rename name dependency :
      Factor Identity Dependency V → Factor Identity' Dependency' V) := by
  intro first second equal
  have identityEqual := names (congrArg Factor.identity equal)
  have dependencyEqual := dependencies (congrArg Factor.dependency equal)
  have coefficientEqual := congrArg Factor.coefficient equal
  cases first
  cases second
  simp_all [Factor.rename]

def rename (name : Identity → Identity') (dependency : Dependency → Dependency')
    (ledger : Ledger Identity Dependency V) : Ledger Identity' Dependency' V :=
  ledger.map (Factor.rename name dependency)

theorem rename_injective {name : Identity → Identity'}
    {dependency : Dependency → Dependency'} (names : Function.Injective name)
    (dependencies : Function.Injective dependency) :
    Function.Injective (rename name dependency :
      Ledger Identity Dependency V → Ledger Identity' Dependency' V) :=
  List.map_injective_iff.mpr (Factor.rename_injective names dependencies)

theorem identities_rename (name : Identity → Identity')
    (dependency : Dependency → Dependency') (ledger : Ledger Identity Dependency V) :
    identities (rename name dependency ledger) = (identities ledger).map name := by
  simp [identities, rename, Factor.rename, List.map_map, Function.comp_def]

theorem valid_rename_iff {name : Identity → Identity'}
    (names : Function.Injective name) (dependency : Dependency → Dependency')
    (ledger : Ledger Identity Dependency V) :
    Valid (rename name dependency ledger) ↔ Valid ledger := by
  unfold Valid
  rw [identities_rename]
  exact List.nodup_map_iff names

def PrefixSplit.rename (name : Identity → Identity') (dependency : Dependency → Dependency')
    (parts : PrefixSplit Identity Dependency V) : PrefixSplit Identity' Dependency' V :=
  ⟨SharedCoefficientLedger.rename name dependency parts.shared,
    SharedCoefficientLedger.rename name dependency parts.leftFresh,
    SharedCoefficientLedger.rename name dependency parts.rightFresh⟩

theorem PrefixSplit.ordered_rename (name : Identity → Identity')
    (dependency : Dependency → Dependency') (parts : PrefixSplit Identity Dependency V) :
    (parts.rename name dependency).ordered =
      SharedCoefficientLedger.rename name dependency parts.ordered := by
  simp [PrefixSplit.rename, ordered, SharedCoefficientLedger.rename, List.map_append]

/-- The comparison of full factors, including the dependency field, commutes
with a shared injective renaming. In particular, the shared prefix is retained. -/
theorem splitPrefix_rename [DecidableEq Identity] [DecidableEq Identity']
    [DecidableEq Dependency] [DecidableEq Dependency'] [DecidableEq V]
    {name : Identity → Identity'} {dependency : Dependency → Dependency'}
    (names : Function.Injective name) (dependencies : Function.Injective dependency)
    (left right : Ledger Identity Dependency V) :
    splitPrefix (rename name dependency left) (rename name dependency right) =
      (splitPrefix left right).rename name dependency := by
  induction left generalizing right with
  | nil => simp [rename, splitPrefix, PrefixSplit.rename]
  | cons first rest ih =>
      cases right with
      | nil => simp [rename, splitPrefix, PrefixSplit.rename]
      | cons second later =>
          by_cases same : first = second
          · subst second
            simpa [rename, splitPrefix, PrefixSplit.rename] using
              And.intro (congrArg PrefixSplit.shared (ih later))
                (And.intro (congrArg PrefixSplit.leftFresh (ih later))
                  (congrArg PrefixSplit.rightFresh (ih later)))
          · simp [rename, splitPrefix, PrefixSplit.rename, same,
              (Factor.rename_injective names dependencies).eq_iff]

/-- Successful and refused merges both commute. A coefficient-only comparison
would not justify this statement: it can lose a duplicated physical factor. -/
theorem merge_rename [DecidableEq Identity] [DecidableEq Identity']
    [DecidableEq Dependency] [DecidableEq Dependency'] [DecidableEq V]
    {name : Identity → Identity'} {dependency : Dependency → Dependency'}
    (names : Function.Injective name) (dependencies : Function.Injective dependency)
    (left right : Ledger Identity Dependency V) :
    merge? (rename name dependency left) (rename name dependency right) =
      (merge? left right).map (rename name dependency) := by
  simp only [merge?, splitPrefix_rename names dependencies, PrefixSplit.ordered_rename,
    valid_rename_iff names]
  split <;> rfl

theorem append_rename [DecidableEq Identity] [DecidableEq Identity']
    {name : Identity → Identity'} (names : Function.Injective name)
    (dependency : Dependency → Dependency') (ledger : Ledger Identity Dependency V)
    (factor : Factor Identity Dependency V) :
    append? (rename name dependency ledger) (factor.rename name dependency) =
      (append? ledger factor).map (rename name dependency) := by
  simp only [append?, identities_rename, Factor.rename,
    List.mem_map_of_injective names]
  split <;> simp [rename, Factor.rename, List.map_append]

/-- Renaming keeps the chronological product in an arbitrary monoid. No
commutation of factors, cancellation or nonzero assumption is required. -/
theorem denote_rename [Monoid V] (name : Identity → Identity')
    (dependency : Dependency → Dependency') (ledger : Ledger Identity Dependency V) :
    denote (rename name dependency ledger) = denote ledger := by
  simp [denote, rename, Factor.rename, List.map_map, Function.comp_def]

/-- A common name space also preserves aliases between the identity of one
factor and the dependency of another, including factors in different answers. -/
theorem renamed_dependency_alias_iff {Name : Type uId} {Name' : Type uId'}
    {name : Name → Name'} (names : Function.Injective name)
    (first second : Factor Name Name V) :
    (first.rename name name).identity = (second.rename name name).dependency ↔
      first.identity = second.dependency := names.eq_iff

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

/-! A transported world must also retain claims. Renaming only its production
list does not establish equivalence of nested observations. -/

theorem selected_transport {Owner' : Type uOwner'}
    (name : Identity → Identity') (dependency : Dependency → Dependency')
    (owner : Owner → Owner') (source : Scoped Identity Dependency V Owner)
    (target : Scoped Identity' Dependency' V Owner')
    (productions : target.productions = rename name dependency source.productions)
    (claims : ∀ identity, target.claims (name identity) = (source.claims identity).map owner)
    (entry : Nat) :
    selected entry target = rename name dependency (selected entry source) := by
  simp only [selected, productions, rename, ← List.map_drop, List.filter_map]
  congr 1
  apply List.filter_congr
  intro factor _
  simp only [Function.comp_def, Factor.rename, claims, Option.isNone_map]

/-- The claim acquired by a read is independent of fresh name allocation.
Injectivity prevents a newly claimed factor from stealing another factor's
identity. The owner map may be arbitrary for this one-step preservation law. -/
theorem handle_claim_transport [DecidableEq Identity] [DecidableEq Identity']
    {Owner' : Type uOwner'} {name : Identity → Identity'}
    (names : Function.Injective name) (dependency : Dependency → Dependency')
    (owner : Owner → Owner') (source : Scoped Identity Dependency V Owner)
    (target : Scoped Identity' Dependency' V Owner')
    (productions : target.productions = rename name dependency source.productions)
    (claims : ∀ identity, target.claims (name identity) = (source.claims identity).map owner)
    (entry : Nat) (observer : Owner) (identity : Identity) :
    (handle entry (owner observer) target).claims (name identity) =
      ((handle entry observer source).claims identity).map owner := by
  simp only [handle, selected_transport name dependency owner source target productions claims,
    identities_rename, List.mem_map_of_injective names]
  split <;> simp_all

/-- A renamed world with the same claims presents the same coefficient to a
readout, even when multiplication is ordered or a factor is zero. -/
theorem selected_denotation_transport [Monoid V] {Owner' : Type uOwner'}
    (name : Identity → Identity') (dependency : Dependency → Dependency')
    (owner : Owner → Owner') (source : Scoped Identity Dependency V Owner)
    (target : Scoped Identity' Dependency' V Owner')
    (productions : target.productions = rename name dependency source.productions)
    (claims : ∀ identity, target.claims (name identity) = (source.claims identity).map owner)
    (entry : Nat) : denote (selected entry target) = denote (selected entry source) := by
  rw [selected_transport name dependency owner source target productions claims, denote_rename]

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

/-- A supported claim in a captured world survives every admitted extension,
including extensions produced by ordinary readout callbacks. -/
theorem extendsCapture_preserves_claim [DecidableEq Identity] [DecidableEq Dependency]
    [DecidableEq V] [DecidableEq Owner]
    {entry world : Scoped Identity Dependency V Owner}
    (supported : entry.Supported) (extended : extendsCapture entry world = true)
    {identity : Identity} {owner : Owner} (claimed : entry.claims identity = some owner) :
    world.claims identity = some owner := by
  obtain ⟨factor, present, equal⟩ := List.mem_map.mp (supported identity owner claimed)
  simp only [extendsCapture, Bool.and_eq_true_iff] at extended
  have checked := extended.2
  have allowed := List.all_eq_true.mp checked factor present
  simpa [equal, claimed] using allowed

/-- Once a snapshot has been claimed, retaining that claimed world as a
capture prevents any of its productions from being selected again. -/
theorem handled_snapshot_not_reselected [DecidableEq Identity] [DecidableEq Dependency]
    [DecidableEq V] [DecidableEq Owner]
    (entry : Nat) (owner : Owner) (before after : Scoped Identity Dependency V Owner)
    (supported : before.Supported)
    (extended : extendsCapture (handle entry owner before) after = true)
    {factor : Factor Identity Dependency V} (observed : factor ∈ selected entry before)
    (laterEntry : Nat) : factor ∉ selected laterEntry after := by
  have claimed := extendsCapture_preserves_claim
    (handle_supported entry owner before supported) extended
    (selected_claimed entry owner before observed)
  intro reselected
  have unclaimed := ((mem_selected laterEntry after factor).mp reselected).2
  rw [claimed] at unclaimed
  cases unclaimed

/-- Appending an unclaimed production makes precisely that new production
available after the previous snapshot. No commutative algebra law is used. -/
theorem selected_append_unclaimed (entry : Nat)
    (world : Scoped Identity Dependency V Owner) (factor : Factor Identity Dependency V)
    (within : entry ≤ world.productions.length) (unclaimed : world.claims factor.identity = none) :
    selected entry ⟨world.productions ++ [factor], world.claims⟩ =
      selected entry world ++ [factor] := by
  simp only [selected, List.drop_append_of_le_length within, List.filter_append]
  simp [unclaimed]

/-- A callback's fresh unclaimed production remains visible to an enclosing
read, while the previously handled snapshot remains unavailable. -/
theorem selected_fresh_after_handle [DecidableEq Identity]
    (entry : Nat) (owner : Owner) (world : Scoped Identity Dependency V Owner)
    (factor : Factor Identity Dependency V) (within : entry ≤ world.productions.length)
    (outside : factor.identity ∉ identities (selected entry world))
    (unclaimed : world.claims factor.identity = none) :
    selected entry
        ⟨world.productions ++ [factor], (handle entry owner world).claims⟩ = [factor] := by
  have free : (handle entry owner world).claims factor.identity = none := by
    simp [handle, outside, unclaimed]
  have enlarged := selected_append_unclaimed entry (handle entry owner world) factor within free
  change selected entry
      ⟨world.productions ++ [factor], (handle entry owner world).claims⟩ =
    selected entry (handle entry owner world) ++ [factor] at enlarged
  simpa only [selected_after_handle, List.nil_append] using enlarged

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

namespace Controls

private def beforeCallback : Scoped Nat Nat Nat Nat :=
  ⟨[⟨11, 3, 4⟩], fun _ => none⟩

private def afterCallback : Scoped Nat Nat Nat Nat :=
  ⟨beforeCallback.productions ++ [⟨22, 5, 6⟩], (handle 0 7 beforeCallback).claims⟩

theorem callback_production_keeps_original_claim :
    selected 0 afterCallback = [⟨22, 5, 6⟩] ∧ afterCallback.claims 11 = some 7 := by decide

theorem erasing_claims_reselects_paid_snapshot :
    selected 0 (⟨afterCallback.productions, fun _ => none⟩ : Scoped Nat Nat Nat Nat) ≠
      [⟨22, 5, 6⟩] := by decide

end Controls

end Scoped

end Mettapedia.Algebra.SharedCoefficientLedger
