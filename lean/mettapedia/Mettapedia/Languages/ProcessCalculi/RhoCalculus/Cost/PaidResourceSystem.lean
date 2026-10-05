import Mettapedia.GSLT.Causality.ResourceProduct
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Parallel

/-!
# Funded rho communication is communication and purses fired together

A funded communication of the cost-accounted rho calculus takes its endpoints
and the top cells of some purses at its location, and adds its contractum and
the rests of those purses. The funded resource system is defined here as two
resource systems fired together: communication without payment, and purses. A
joint instance at a location is a funded event there: its communication, with
the purses it selects. Its consumption and its production are the consumed and
the produced components of the event.

Enabling, concurrency and firing then follow from the laws of systems fired
together. A funded event is enabled exactly when its communication is enabled
among the components that are not purses and the purses it selects are among
the purses of the configuration; two funded events are concurrent exactly when
their communications are and their selections are among the purses together.
No funded event is enabled at a location where no purse holds a cell.

A contractum may hold purses. On terms they are purses of the configuration
after the firing. The funded system is also the product of the two systems on
the sum of their carriers, with each purse read as its term; there a purse of
the contractum stays on the side of the terms. The two agree as transition
systems exactly where no contractum releases a purse.

What a run of funded firings takes from the purses is the law of runs of
resource systems, read on the purses: the cells of the purses before a run,
with the cells of the purses its contracta release, are the cells after it with
the heads its events select, and no purse is added or removed apart from the
released ones. A funding cover of the runtime is a firing of the purse system.

The funded events are the communications with a permitted choice of purses:
every top cell a valid signature, and the top cells summing to the demand of
the communication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

universe u

variable {Ground : Type u}

/-! ## Stacks as lists of cells -/

namespace CostStack

/-- The cells of a stack, the head first. -/
def toList : CostStack Ground → List (CostSig Ground)
  | .empty => []
  | .cons head tail => head :: tail.toList

/-- The stack with the given cells, the first on top. -/
def ofList : List (CostSig Ground) → CostStack Ground
  | [] => .empty
  | head :: tail => .cons head (ofList tail)

@[simp] theorem ofList_toList : ∀ stack : CostStack Ground, ofList stack.toList = stack
  | .empty => rfl
  | .cons head tail => congrArg (CostStack.cons head) (ofList_toList tail)

@[simp] theorem toList_ofList : ∀ cells : List (CostSig Ground), (ofList cells).toList = cells
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (toList_ofList tail)

end CostStack

/-! ## The purses among the components of a configuration -/

/-- The term of a purse given by its location and its cells, the top cell first. -/
def purseTerm (purse : CostName Ground × List (CostSig Ground)) : CostTerm Ground :=
  LocatedPurse.toTerm ⟨purse.1, CostStack.ofList purse.2⟩

namespace CostTerm

/-- The purse a term is, when it is one: its location and its cells. -/
def purse? : CostTerm Ground → Option (CostName Ground × List (CostSig Ground))
  | .purse location stack => some (location, stack.toList)
  | _ => none

/-- Whether a term is a purse. -/
def isPurse (term : CostTerm Ground) : Bool :=
  term.purse?.isSome

end CostTerm

/-- The term of a purse is that purse. -/
theorem purse?_purseTerm (purse : CostName Ground × List (CostSig Ground)) :
    (purseTerm purse).purse? = some purse := by
  obtain ⟨location, cells⟩ := purse
  change some (location, (CostStack.ofList cells).toList) = some (location, cells)
  rw [CostStack.toList_ofList]

/-- Purses with different locations or cells are different terms. -/
theorem purseTerm_injective : Function.Injective (purseTerm (Ground := Ground)) :=
  fun first second same => Option.some.inj
    ((purse?_purseTerm first).symm.trans
      ((congrArg CostTerm.purse? same).trans (purse?_purseTerm second)))

/-- The term of the purse with the cells of a stack is the purse with that stack. -/
theorem purseTerm_toList (location : CostName Ground) (stack : CostStack Ground) :
    purseTerm (location, stack.toList) = .purse location stack := by
  change CostTerm.purse location (CostStack.ofList stack.toList) = _
  rw [CostStack.ofList_toList]

/-- A term that is a purse is the term of that purse. -/
theorem purseTerm_of_purse? {term : CostTerm Ground}
    {purse : CostName Ground × List (CostSig Ground)} (found : term.purse? = some purse) :
    purseTerm purse = term := by
  cases term with
  | purse location stack =>
      obtain rfl : (location, stack.toList) = purse := Option.some.inj found
      exact purseTerm_toList location stack
  | _ => simp [CostTerm.purse?] at found

/-- The term of a purse is a purse. -/
theorem isPurse_purseTerm (purse : CostName Ground × List (CostSig Ground)) :
    (purseTerm purse).isPurse = true := by
  unfold CostTerm.isPurse
  rw [purse?_purseTerm]
  rfl

/-- Every term of a bag of purses is a purse. -/
theorem isPurse_of_mem_map {bag : Multiset (CostName Ground × List (CostSig Ground))} :
    ∀ term ∈ bag.map purseTerm, term.isPurse := by
  intro term member
  obtain ⟨purse, _, rfl⟩ := Multiset.mem_map.mp member
  exact isPurse_purseTerm purse

namespace CostConfig

/-- The purses among the components of a configuration, each as its location
and its cells. -/
def purses (config : CostConfig Ground) : Multiset (CostName Ground × List (CostSig Ground)) :=
  config.filterMap CostTerm.purse?

/-- The purses of two configurations together are the purses of each. -/
theorem purses_add (left right : CostConfig Ground) :
    purses (left + right) = purses left + purses right :=
  Multiset.filterMap_add _ _ _

/-- The purses among the terms of a bag of purses are that bag. -/
theorem purses_map_purseTerm (bag : Multiset (CostName Ground × List (CostSig Ground))) :
    purses (bag.map purseTerm) = bag := by
  unfold purses
  rw [Multiset.filterMap_map]
  have inverse : CostTerm.purse? ∘ purseTerm =
      (some : CostName Ground × List (CostSig Ground) → Option _) := funext purse?_purseTerm
  rw [inverse, Multiset.filterMap_some]

/-- **The purse components of a configuration are the terms of its purses.** -/
theorem filter_isPurse (config : CostConfig Ground) :
    config.filter (fun term => term.isPurse) = (purses config).map purseTerm := by
  induction config using Multiset.induction_on with
  | empty => rfl
  | cons term config ih =>
      unfold purses at ih ⊢
      by_cases isPurse : term.isPurse = true
      · obtain ⟨purse, found⟩ := Option.isSome_iff_exists.mp isPurse
        rw [Multiset.filter_cons_of_pos (p := fun term : CostTerm Ground => term.isPurse = true)
            config isPurse, ih, Multiset.filterMap_cons_some _ _ _ found, Multiset.map_cons,
          purseTerm_of_purse? found]
      · have absent : term.purse? = none := Option.not_isSome_iff_eq_none.mp isPurse
        rw [Multiset.filter_cons_of_neg (p := fun term : CostTerm Ground => term.isPurse = true)
            config isPurse, ih, Multiset.filterMap_cons_none _ _ absent]

/-- A configuration with no purse component has no purses. -/
theorem purses_eq_zero {config : CostConfig Ground} (none : ∀ term ∈ config, ¬ term.isPurse) :
    purses config = 0 :=
  Multiset.map_eq_zero.mp ((filter_isPurse config).symm.trans (Multiset.filter_eq_nil.mpr none))

/-- A purse is among the purses of a configuration exactly when its term is a
component. -/
theorem mem_purses_iff (config : CostConfig Ground)
    (purse : CostName Ground × List (CostSig Ground)) :
    purse ∈ config.purses ↔ purseTerm purse ∈ config := by
  constructor
  · intro member
    obtain ⟨term, inConfig, found⟩ := (Multiset.mem_filterMap _ _).mp member
    rw [purseTerm_of_purse? found]
    exact inConfig
  · intro member
    exact (Multiset.mem_filterMap _ _).mpr ⟨_, member, purse?_purseTerm purse⟩

/-- A configuration with no purses consists of components that are not purses. -/
theorem filter_not_isPurse_eq_self {config : CostConfig Ground} (none : config.purses = 0) :
    config.filter (fun term => ¬ term.isPurse) = config := by
  refine Multiset.filter_eq_self.mpr (Multiset.filter_eq_nil.mp ?_)
  rw [filter_isPurse, none]
  rfl

end CostConfig

/-! ## Communication without payment -/

/-- A communication between sealed endpoints, without its payment: the three
shapes of a funded event, with the selection of purses left out. -/
inductive UnpaidEvent (Ground : Type u) where
  | wholeRecvSend (channel : CostName Ground) (body payload : CostTerm Ground)
      (outerSig : CostSig Ground) (signature_valid : outerSig.RuntimeValid)
  | wholeSendRecv (channel : CostName Ground) (body payload : CostTerm Ground)
      (outerSig : CostSig Ground) (signature_valid : outerSig.RuntimeValid)
  | split (channel : CostName Ground) (body payload : CostTerm Ground)
      (recvSeal sendSeal : CostSig Ground) (recv_seal_valid : recvSeal.RuntimeValid)
      (send_seal_valid : sendSeal.RuntimeValid)

namespace UnpaidEvent

/-- The channel on which the endpoints meet. -/
def location : UnpaidEvent Ground → CostName Ground
  | .wholeRecvSend channel .. => channel
  | .wholeSendRecv channel .. => channel
  | .split channel .. => channel

/-- The signature the communication asks to be paid: the seals of its endpoints. -/
def demand : UnpaidEvent Ground → CostSig Ground
  | .wholeRecvSend _ _ _ outerSig _ => outerSig
  | .wholeSendRecv _ _ _ outerSig _ => outerSig
  | .split _ _ _ recvSeal sendSeal _ _ => recvSeal + sendSeal

/-- The endpoint components the communication consumes. -/
def endpoints : UnpaidEvent Ground → CostConfig Ground
  | .wholeRecvSend channel body payload outerSig _ =>
      .signed (.par (.recv channel body) (.send channel payload)) outerSig ::ₘ 0
  | .wholeSendRecv channel body payload outerSig _ =>
      .signed (.par (.send channel payload) (.recv channel body)) outerSig ::ₘ 0
  | .split channel body payload recvSeal sendSeal _ _ =>
      (.signed (.recv channel body) recvSeal ::ₘ 0) +
        (.signed (.send channel payload) sendSeal ::ₘ 0)

/-- The components of the contractum the communication produces. -/
def contractum : UnpaidEvent Ground → CostConfig Ground
  | .wholeRecvSend _ body payload _ _ => (body.commSubst payload).components
  | .wholeSendRecv _ body payload _ _ => (body.commSubst payload).components
  | .split _ body payload _ _ _ _ => (body.commSubst payload).components

/-- Pay for a communication with a selection of purses at its location whose
heads sum to its demand. -/
def fund : (unpaid : UnpaidEvent Ground) →
    FundingSelection Ground unpaid.location unpaid.demand → CostedEvent Ground
  | .wholeRecvSend channel body payload outerSig valid, funding =>
      .wholeRecvSend channel body payload outerSig valid funding
  | .wholeSendRecv channel body payload outerSig valid, funding =>
      .wholeSendRecv channel body payload outerSig valid funding
  | .split channel body payload recvSeal sendSeal recvValid sendValid, funding =>
      .split channel body payload recvSeal sendSeal recvValid sendValid funding

/-- The endpoints of a communication are sealed processes, never purses. -/
theorem not_isPurse_of_mem_endpoints (unpaid : UnpaidEvent Ground) :
    ∀ term ∈ unpaid.endpoints, ¬ term.isPurse := by
  intro term member
  cases unpaid with
  | wholeRecvSend channel body payload outerSig valid =>
      obtain rfl := Multiset.mem_singleton.mp member
      exact Bool.false_ne_true
  | wholeSendRecv channel body payload outerSig valid =>
      obtain rfl := Multiset.mem_singleton.mp member
      exact Bool.false_ne_true
  | split channel body payload recvSeal sendSeal recvValid sendValid =>
      rcases Multiset.mem_add.mp member with member | member
      · obtain rfl := Multiset.mem_singleton.mp member
        exact Bool.false_ne_true
      · obtain rfl := Multiset.mem_singleton.mp member
        exact Bool.false_ne_true

end UnpaidEvent

namespace CostedEvent

/-- The communication a funded event pays for. -/
def unpaid : CostedEvent Ground → UnpaidEvent Ground
  | .wholeRecvSend channel body payload outerSig valid _ =>
      .wholeRecvSend channel body payload outerSig valid
  | .wholeSendRecv channel body payload outerSig valid _ =>
      .wholeSendRecv channel body payload outerSig valid
  | .split channel body payload recvSeal sendSeal recvValid sendValid _ =>
      .split channel body payload recvSeal sendSeal recvValid sendValid

/-- The selection of purses of a funded event. -/
def funding : (event : CostedEvent Ground) → FundingSelection Ground event.location event.spend
  | .wholeRecvSend _ _ _ _ _ funding => funding
  | .wholeSendRecv _ _ _ _ _ funding => funding
  | .split _ _ _ _ _ _ _ funding => funding

/-- The purses a funded event selects, each as its top cell and the cells
under it. -/
def chosenPurses (event : CostedEvent Ground) :
    Multiset (CostSig Ground × List (CostSig Ground)) :=
  event.funding.chosen.map fun choice => (choice.head, choice.tail.toList)

/-- The communication of an event is at the location of the event. -/
theorem unpaid_location (event : CostedEvent Ground) : event.unpaid.location = event.location := by
  cases event <;> rfl

/-- The communication of an event asks for what the event spends. -/
theorem unpaid_demand (event : CostedEvent Ground) : event.unpaid.demand = event.spend := by
  cases event <;> rfl

/-- The communication of an event consumes the endpoints of the event. -/
theorem unpaid_endpoints (event : CostedEvent Ground) :
    event.unpaid.endpoints = event.endpoints := by
  cases event <;> rfl

/-- The communication of an event produces the contractum of the event. -/
theorem unpaid_contractum (event : CostedEvent Ground) :
    event.unpaid.contractum = event.contractum := by
  cases event <;> rfl

/-- The purse components an event consumes are its selected purses. -/
theorem fundingBefore_eq (event : CostedEvent Ground) :
    event.fundingBefore = LocatedPurse.configComponents event.funding.before := by
  cases event <;> rfl

/-- The purse components an event produces are the tails of its selected purses. -/
theorem fundingAfter_eq (event : CostedEvent Ground) :
    event.fundingAfter = LocatedPurse.configComponents event.funding.after := by
  cases event <;> rfl

/-- The top cells of the chosen purses are the selected heads. -/
theorem chosenPurses_tops (event : CostedEvent Ground) :
    event.chosenPurses.map Prod.fst = event.funding.chosen.map SelectedPurseHead.head := by
  unfold chosenPurses
  rw [Multiset.map_map]
  rfl

/-- **The selected heads sum to the demand of the event.** -/
theorem sum_selected_heads (event : CostedEvent Ground) :
    (event.funding.chosen.map SelectedPurseHead.head).sum = event.spend :=
  event.funding.demand_eq.symm

/-- Every funded event selects at least one purse. -/
theorem chosenPurses_ne_zero (event : CostedEvent Ground) : event.chosenPurses ≠ 0 := fun empty =>
  event.funding.chosen_ne_zero event.spend_valid (Multiset.map_eq_zero.mp empty)

/-- The selected purses before a firing are the terms of the chosen purses,
each at the location of the event with its top cell. -/
theorem fundingBefore_eq_map (event : CostedEvent Ground) :
    event.fundingBefore =
      (event.chosenPurses.map fun purse => (event.location, purse.1 :: purse.2)).map
        purseTerm := by
  rw [fundingBefore_eq]
  unfold chosenPurses FundingSelection.before LocatedPurse.configComponents
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun choice _ =>
    (purseTerm_toList event.location (.cons choice.head choice.tail)).symm

/-- The selected purses after a firing are the terms of the rests of the
chosen purses, each at the location of the event. -/
theorem fundingAfter_eq_map (event : CostedEvent Ground) :
    event.fundingAfter =
      (event.chosenPurses.map fun purse => (event.location, purse.2)).map purseTerm := by
  rw [fundingAfter_eq]
  unfold chosenPurses FundingSelection.after LocatedPurse.configComponents
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun choice _ => (purseTerm_toList event.location choice.tail).symm

end CostedEvent

/-! ## The two systems, and the funded system as the two fired together -/

/-- Communication without payment, as a resource system on terms: at a
location, a communication consumes its two endpoints and adds the components of
its contractum. -/
def unpaidResourceSystem (Ground : Type u) : System (CostTerm Ground) where
  Site := CostName Ground
  Instance := fun location => {unpaid : UnpaidEvent Ground // unpaid.location = location}
  consume := fun unpaid => unpaid.val.endpoints
  read := fun _ => 0
  produce := fun unpaid => unpaid.val.contractum

/-- The purses, as a resource system on terms: at a location, a choice of
purses there consumes them and adds their rests. -/
def purseResourceSystem (Ground : Type u) : System (CostTerm Ground) :=
  (pursesMany (CostName Ground) (CostSig Ground)).map purseTerm

/-- The communication of a funded event, as an instance of the unpaid system
at the location of the event. -/
def unpaidEntry {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    (unpaidResourceSystem Ground).Entry :=
  ⟨location, event.val.unpaid, event.val.unpaid_location.trans event.property⟩

/-- The purses a funded event selects, as an instance of the purse system at
the location of the event. -/
def purseEntry {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    (purseResourceSystem Ground).Entry :=
  ⟨location, event.val.chosenPurses⟩

/-- **The funded resource system: communication and purses fired together.** A
joint instance at a location is a funded event there: its communication, with
the purses it selects. The site is the rho location of the event. -/
def costResourceSystem (Ground : Type u) : System (CostTerm Ground) :=
  (unpaidResourceSystem Ground).joint (purseResourceSystem Ground) (CostName Ground)
    (fun location => {event : CostedEvent Ground // event.location = location})
    unpaidEntry purseEntry

/-- A funded event consumes its endpoints and the purses it selects. -/
theorem costResourceSystem_consume {location : (costResourceSystem Ground).Site}
    (event : (costResourceSystem Ground).Instance location) :
    (costResourceSystem Ground).consume event = event.val.consumed := by
  obtain ⟨event, rfl⟩ := event
  change event.unpaid.endpoints +
    (event.chosenPurses.map fun purse => (event.location, purse.1 :: purse.2)).map purseTerm =
      event.endpoints + event.fundingBefore
  rw [CostedEvent.unpaid_endpoints, CostedEvent.fundingBefore_eq_map]

/-- A funded event reads nothing. -/
theorem costResourceSystem_read {location : (costResourceSystem Ground).Site}
    (event : (costResourceSystem Ground).Instance location) :
    (costResourceSystem Ground).read event = 0 :=
  rfl

/-- A funded event produces its contractum and the rests of the purses it
selects. -/
theorem costResourceSystem_produce {location : (costResourceSystem Ground).Site}
    (event : (costResourceSystem Ground).Instance location) :
    (costResourceSystem Ground).produce event = event.val.produced := by
  obtain ⟨event, rfl⟩ := event
  change event.unpaid.contractum +
    (event.chosenPurses.map fun purse => (event.location, purse.2)).map purseTerm =
      event.contractum + event.fundingAfter
  rw [CostedEvent.unpaid_contractum, CostedEvent.fundingAfter_eq_map]

/-- The product of communication without payment with the purses, on the sum
of their two carriers: terms on one side, purses on the other. The joint
instances are the funded events. -/
def paidProductSystem (Ground : Type u) :
    System (CostTerm Ground ⊕ (CostName Ground × List (CostSig Ground))) :=
  (unpaidResourceSystem Ground).product (pursesMany (CostName Ground) (CostSig Ground))
    (CostName Ground) (fun location => {event : CostedEvent Ground // event.location = location})
    unpaidEntry purseEntry

/-- **The funded resource system is a product, seen on terms**: the product of
communication without payment with the purses, each purse of the second factor
read as its term. -/
theorem costResourceSystem_eq_map_product :
    costResourceSystem Ground = (paidProductSystem Ground).map (Sum.elim id purseTerm) := by
  have onTerms : ∀ (code : CostConfig Ground)
      (bag : Multiset (CostName Ground × List (CostSig Ground))),
      code + bag.map purseTerm = (marking code bag).map (Sum.elim id purseTerm) :=
    fun code bag => by rw [map_elim_marking, Multiset.map_id]
  exact System.mk_congr
    (fun {location} event => onTerms event.val.unpaid.endpoints
      ((pursesMany (CostName Ground) (CostSig Ground)).consume (site := location)
        event.val.chosenPurses))
    (fun _ => onTerms 0 0)
    (fun {location} event => onTerms event.val.unpaid.contractum
      ((pursesMany (CostName Ground) (CostSig Ground)).produce (site := location)
        event.val.chosenPurses))

/-! ## Enabling, concurrency and firing, from the laws of systems fired together -/

/-- A communication consumes and reads no purse. -/
theorem unpaid_uses {location : CostName Ground}
    (unpaid : (unpaidResourceSystem Ground).Instance location) :
    ∀ term ∈ (unpaidResourceSystem Ground).consume unpaid +
      (unpaidResourceSystem Ground).read unpaid, ¬ term.isPurse := by
  intro term member
  refine unpaid.val.not_isPurse_of_mem_endpoints term ?_
  change term ∈ unpaid.val.endpoints + 0 at member
  rwa [add_zero] at member

/-- A choice of purses consumes and reads only purses. -/
theorem purse_uses {location : CostName Ground}
    (chosen : (purseResourceSystem Ground).Instance location) :
    ∀ term ∈ (purseResourceSystem Ground).consume chosen +
      (purseResourceSystem Ground).read chosen, term.isPurse := by
  intro term member
  rcases Multiset.mem_add.mp member with member | member
  · exact isPurse_of_mem_map term member
  · exact (Multiset.notMem_zero term member).elim

/-- A choice of purses produces only purses. -/
theorem purse_produces {location : CostName Ground}
    (chosen : (purseResourceSystem Ground).Instance location) :
    ∀ term ∈ (purseResourceSystem Ground).produce chosen, term.isPurse :=
  fun term member => isPurse_of_mem_map term member

/-- **A funded event is enabled exactly when its communication is enabled among
the components that are not purses and the purses it selects are among the
purses.** -/
theorem costResource_enables_iff (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    (costResourceSystem Ground).Enables config event ↔
      (unpaidResourceSystem Ground).Enables (config.filter fun term => ¬ term.isPurse)
          (unpaidEntry event).2 ∧
        (pursesMany (CostName Ground) (CostSig Ground)).Enables config.purses
          (site := location) event.val.chosenPurses := by
  have separated := (unpaidResourceSystem Ground).joint_enables_iff (purseResourceSystem Ground)
    (@unpaidEntry Ground) (@purseEntry Ground) (fun term => term.isPurse) config event
    (unpaid_uses _) (purse_uses _)
  have mapped : (purseResourceSystem Ground).Enables (config.filter fun term => term.isPurse)
        (purseEntry event).2 ↔
      (pursesMany (CostName Ground) (CostSig Ground)).Enables config.purses
        (site := location) event.val.chosenPurses := by
    rw [CostConfig.filter_isPurse]
    exact (pursesMany (CostName Ground) (CostSig Ground)).map_enables_iff purseTerm_injective
      config.purses event.val.chosenPurses
  exact separated.trans (and_congr_right' mapped)

/-- **Two funded events are concurrent exactly when their communications are,
among the components that are not purses, and the purses they select are among
the purses together.** -/
theorem costResource_concurrent_iff (config : CostConfig Ground)
    {location₁ location₂ : CostName Ground}
    (first : {event : CostedEvent Ground // event.location = location₁})
    (second : {event : CostedEvent Ground // event.location = location₂}) :
    (costResourceSystem Ground).Concurrent config first second ↔
      (unpaidResourceSystem Ground).Concurrent (config.filter fun term => ¬ term.isPurse)
          (unpaidEntry first).2 (unpaidEntry second).2 ∧
        (pursesMany (CostName Ground) (CostSig Ground)).Concurrent config.purses
          (site₁ := location₁) (site₂ := location₂) first.val.chosenPurses
          second.val.chosenPurses := by
  have separated := (unpaidResourceSystem Ground).joint_concurrent_iff
    (purseResourceSystem Ground) (@unpaidEntry Ground) (@purseEntry Ground)
    (fun term => term.isPurse) config first second (unpaid_uses _) (purse_uses _)
    (unpaid_uses _) (purse_uses _)
  have mapped : (purseResourceSystem Ground).Concurrent (config.filter fun term => term.isPurse)
        (purseEntry first).2 (purseEntry second).2 ↔
      (pursesMany (CostName Ground) (CostSig Ground)).Concurrent config.purses
        (site₁ := location₁) (site₂ := location₂) first.val.chosenPurses
        second.val.chosenPurses := by
    rw [CostConfig.filter_isPurse]
    exact (pursesMany (CostName Ground) (CostSig Ground)).map_concurrent_iff purseTerm_injective
      config.purses first.val.chosenPurses second.val.chosenPurses
  exact separated.trans (and_congr_right' mapped)

/-- The enabling law in the words of the runtime: the endpoints are among the
components that are not purses, and the selected purses are among the purse
components. -/
theorem costResource_enables_iff_le (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    (costResourceSystem Ground).Enables config event ↔
      event.val.endpoints ≤ config.filter (fun term => ¬ term.isPurse) ∧
        event.val.fundingBefore ≤ config.filter fun term => term.isPurse := by
  rw [costResource_enables_iff, pursesMany_enables_iff, CostConfig.filter_isPurse]
  obtain ⟨event, rfl⟩ := event
  rw [CostedEvent.fundingBefore_eq_map, Multiset.map_le_map_iff purseTerm_injective,
    ← CostedEvent.unpaid_endpoints]
  refine and_congr_left' ?_
  change event.unpaid.endpoints + 0 ≤ _ ↔ _
  rw [add_zero]

/-- The concurrency law in the words of the runtime: both pairs of endpoints
are among the components that are not purses, and both selections of purses
are among the purse components together. -/
theorem costResource_concurrent_iff_le (config : CostConfig Ground)
    {location₁ location₂ : CostName Ground}
    (first : {event : CostedEvent Ground // event.location = location₁})
    (second : {event : CostedEvent Ground // event.location = location₂}) :
    (costResourceSystem Ground).Concurrent config first second ↔
      first.val.endpoints + second.val.endpoints ≤ config.filter (fun term => ¬ term.isPurse) ∧
        first.val.fundingBefore + second.val.fundingBefore ≤
          config.filter fun term => term.isPurse := by
  rw [costResource_concurrent_iff, pursesMany_concurrent_iff, CostConfig.filter_isPurse]
  obtain ⟨first, rfl⟩ := first
  obtain ⟨second, rfl⟩ := second
  rw [CostedEvent.fundingBefore_eq_map, CostedEvent.fundingBefore_eq_map, ← Multiset.map_add,
    Multiset.map_le_map_iff purseTerm_injective, ← CostedEvent.unpaid_endpoints,
    ← CostedEvent.unpaid_endpoints]
  refine and_congr_left' ?_
  change (first.unpaid.endpoints + second.unpaid.endpoints + 0 ≤ _ ∧
    first.unpaid.endpoints + second.unpaid.endpoints + 0 ≤ _) ↔ _
  rw [add_zero, and_self]

section Firing

variable [DecidableEq Ground]

/-- **Firing a funded event fires its communication among the components that
are not purses, and its selection among the purses.** -/
theorem costResource_fire (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    (costResourceSystem Ground).fire config event =
      (unpaidResourceSystem Ground).fire (config.filter fun term => ¬ term.isPurse)
          (unpaidEntry event).2 +
        ((pursesMany (CostName Ground) (CostSig Ground)).fire config.purses (site := location)
          event.val.chosenPurses).map purseTerm := by
  have fired := (unpaidResourceSystem Ground).joint_fire (purseResourceSystem Ground)
    (@unpaidEntry Ground) (@purseEntry Ground) (fun term => term.isPurse) config event
    (fun term member => unpaid_uses _ term (Multiset.mem_add.mpr (Or.inl member)))
    (fun term member => purse_uses _ term (Multiset.mem_add.mpr (Or.inl member)))
  have mapped : (purseResourceSystem Ground).fire (config.filter fun term => term.isPurse)
        (purseEntry event).2 =
      ((pursesMany (CostName Ground) (CostSig Ground)).fire config.purses (site := location)
        event.val.chosenPurses).map purseTerm := by
    rw [CostConfig.filter_isPurse]
    exact (pursesMany (CostName Ground) (CostSig Ground)).map_fire purseTerm_injective
      config.purses event.val.chosenPurses
  exact fired.trans (congrArg _ mapped)

/-- **The purses after a funded firing.** They are the purses before with each
selected purse replaced by its tail, and the purses among the components of the
contractum. A purse released by the contractum is a purse of the configuration
from then on. -/
theorem costResource_fire_purses (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    CostConfig.purses ((costResourceSystem Ground).fire config event) =
      (pursesMany (CostName Ground) (CostSig Ground)).fire config.purses (site := location)
          event.val.chosenPurses +
        event.val.contractum.purses := by
  have code : CostConfig.purses ((unpaidResourceSystem Ground).fire
      (config.filter fun term => ¬ term.isPurse) (unpaidEntry event).2) =
        event.val.contractum.purses := by
    change CostConfig.purses (config.filter (fun term => ¬ term.isPurse) -
      event.val.unpaid.endpoints + event.val.unpaid.contractum) = _
    rw [CostConfig.purses_add, CostConfig.purses_eq_zero fun term member =>
        (Multiset.mem_filter.mp (Multiset.mem_of_le (Multiset.sub_le_self _ _) member)).2,
      zero_add, CostedEvent.unpaid_contractum]
  rw [costResource_fire, CostConfig.purses_add, CostConfig.purses_map_purseTerm, code, add_comm]

/-- The components that are not purses after a funded firing: those before
less the endpoints, with the components of the contractum that are not
purses. -/
theorem costResource_fire_code (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    ((costResourceSystem Ground).fire config event).filter (fun term => ¬ term.isPurse) =
      config.filter (fun term => ¬ term.isPurse) - event.val.endpoints +
        event.val.contractum.filter fun term => ¬ term.isPurse := by
  have fired := (unpaidResourceSystem Ground).joint_fire_filter_not (purseResourceSystem Ground)
    (@unpaidEntry Ground) (@purseEntry Ground) (fun term => term.isPurse) config event
    (fun term member => unpaid_uses _ term (Multiset.mem_add.mpr (Or.inl member)))
    (fun term member => purse_uses _ term (Multiset.mem_add.mpr (Or.inl member)))
    (purse_produces _)
  rw [← CostedEvent.unpaid_endpoints, ← CostedEvent.unpaid_contractum]
  exact fired

/-- **Nothing else changes among the purses.** When a funded event is enabled,
the purses of the configuration are the selected purses beside others. After
the firing they are those others, the tails of the selected purses at the same
location, and the purses the contractum releases. -/
theorem costResource_fire_purses_frame (config : CostConfig Ground)
    {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (enabled : (costResourceSystem Ground).Enables config event) :
    ∃ others : Multiset (CostName Ground × List (CostSig Ground)),
      config.purses =
          others + event.val.chosenPurses.map (fun purse => (location, purse.1 :: purse.2)) ∧
        CostConfig.purses ((costResourceSystem Ground).fire config event) =
          others + event.val.chosenPurses.map (fun purse => (location, purse.2)) +
            event.val.contractum.purses := by
  have present := (pursesMany_enables_iff config.purses location event.val.chosenPurses).mp
    ((costResource_enables_iff config event).mp enabled).2
  exact ⟨_, (tsub_add_cancel_of_le present).symm, costResource_fire_purses config event⟩

end Firing

/-! ## What a run of funded firings takes from the purses -/

section Conservation

variable [DecidableEq Ground]

omit [DecidableEq Ground] in
/-- The purses a funded event consumes are the purses it selects. -/
theorem costResource_consume_purses {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    CostConfig.purses ((costResourceSystem Ground).consume event) =
      event.val.chosenPurses.map fun purse => (location, purse.1 :: purse.2) := by
  change CostConfig.purses (event.val.unpaid.endpoints +
    (event.val.chosenPurses.map fun purse => (location, purse.1 :: purse.2)).map purseTerm) = _
  rw [CostConfig.purses_add,
    CostConfig.purses_eq_zero event.val.unpaid.not_isPurse_of_mem_endpoints, zero_add,
    CostConfig.purses_map_purseTerm]

omit [DecidableEq Ground] in
/-- The purses a funded event produces are the purses its contractum releases
and the rests of the purses it selects. -/
theorem costResource_produce_purses {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    CostConfig.purses ((costResourceSystem Ground).produce event) =
      event.val.contractum.purses +
        event.val.chosenPurses.map fun purse => (location, purse.2) := by
  change CostConfig.purses (event.val.unpaid.contractum +
    (event.val.chosenPurses.map fun purse => (location, purse.2)).map purseTerm) = _
  rw [CostConfig.purses_add, CostConfig.purses_map_purseTerm, CostedEvent.unpaid_contractum]

/-- **Along a run of funded firings, exactly the selected heads leave the
purses.** The cells of the purses before a run, with the cells of the purses its
contracta release, are the cells of the purses after it with the heads its
events select. -/
theorem costResource_run_cells_taken {M N : CostConfig Ground}
    (p : OccurrencePath (costResourceSystem Ground).presentation M N) :
    cellBag M.purses + ((costResourceSystem Ground).instanceValuation
        fun event => cellBag event.val.contractum.purses).onPath p =
      cellBag N.purses + ((costResourceSystem Ground).instanceValuation
        fun event => event.val.funding.chosen.map SelectedPurseHead.head).onPath p := by
  have balanced := (costResourceSystem Ground).balance_observed
    (fun config => cellBag (CostConfig.purses config)) rfl
    (fun first second => by rw [CostConfig.purses_add, cellBag_add]) p
  have produced : ((costResourceSystem Ground).instanceValuation fun event =>
        cellBag (CostConfig.purses ((costResourceSystem Ground).produce event))).onPath p =
      ((costResourceSystem Ground).instanceValuation
          fun event => cellBag event.val.contractum.purses).onPath p +
        ((costResourceSystem Ground).instanceValuation fun {location} event =>
          cellBag (event.val.chosenPurses.map fun purse => (location, purse.2))).onPath p := by
    rw [← System.instanceValuation_add]
    exact (costResourceSystem Ground).instanceValuation_congr
      (fun event => (congrArg cellBag (costResource_produce_purses event)).trans
        (cellBag_add _ _)) p
  have consumed : ((costResourceSystem Ground).instanceValuation fun event =>
        cellBag (CostConfig.purses ((costResourceSystem Ground).consume event))).onPath p =
      ((costResourceSystem Ground).instanceValuation
          fun event => event.val.funding.chosen.map SelectedPurseHead.head).onPath p +
        ((costResourceSystem Ground).instanceValuation fun {location} event =>
          cellBag (event.val.chosenPurses.map fun purse => (location, purse.2))).onPath p := by
    rw [← System.instanceValuation_add]
    exact (costResourceSystem Ground).instanceValuation_congr
      (fun event => (congrArg cellBag (costResource_consume_purses event)).trans
        ((cellBag_chosen _ _).trans
          (congrArg (· + _) (CostedEvent.chosenPurses_tops event.val)))) p
  rw [produced, consumed, ← add_assoc, ← add_assoc] at balanced
  exact add_right_cancel balanced

/-- **Along a run of funded firings, no purse is added or removed** apart from
the purses the contracta release: an emptied purse stays, empty. -/
theorem costResource_run_purses_card {M N : CostConfig Ground}
    (p : OccurrencePath (costResourceSystem Ground).presentation M N) :
    M.purses.card + ((costResourceSystem Ground).instanceValuation
        fun event => event.val.contractum.purses.card).onPath p = N.purses.card := by
  have balanced := (costResourceSystem Ground).balance_observed
    (fun config => (CostConfig.purses config).card) rfl
    (fun first second => by rw [CostConfig.purses_add, Multiset.card_add]) p
  have produced : ((costResourceSystem Ground).instanceValuation fun event =>
        (CostConfig.purses ((costResourceSystem Ground).produce event)).card).onPath p =
      ((costResourceSystem Ground).instanceValuation
          fun event => event.val.contractum.purses.card).onPath p +
        ((costResourceSystem Ground).instanceValuation
          fun event => event.val.chosenPurses.card).onPath p := by
    rw [← System.instanceValuation_add]
    exact (costResourceSystem Ground).instanceValuation_congr
      (fun event => (congrArg Multiset.card (costResource_produce_purses event)).trans
        ((Multiset.card_add _ _).trans (congrArg (_ + ·) (Multiset.card_map _ _)))) p
  have consumed : ((costResourceSystem Ground).instanceValuation fun event =>
        (CostConfig.purses ((costResourceSystem Ground).consume event)).card).onPath p =
      ((costResourceSystem Ground).instanceValuation
          fun event => event.val.chosenPurses.card).onPath p := by
    exact (costResourceSystem Ground).instanceValuation_congr
      (fun event => (congrArg Multiset.card (costResource_consume_purses event)).trans
        (Multiset.card_map _ _)) p
  rw [produced, consumed, ← add_assoc] at balanced
  exact add_right_cancel balanced

/-- **Exactly the selected heads leave the purses**, in one funded firing. The
cells of the purses before it, with the cells of the purses its contractum
releases, are the cells of the purses after it with the selected heads. -/
theorem costResource_cells_taken (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (enabled : (costResourceSystem Ground).Enables config event) :
    cellBag config.purses + cellBag event.val.contractum.purses =
      cellBag (CostConfig.purses ((costResourceSystem Ground).fire config event)) +
        event.val.funding.chosen.map SelectedPurseHead.head := by
  have taken :=
    costResource_run_cells_taken ((costResourceSystem Ground).firing config event enabled)
  rwa [(costResourceSystem Ground).instanceValuation_firing
      (fun event => cellBag event.val.contractum.purses) event enabled,
    (costResourceSystem Ground).instanceValuation_firing
      (fun event => event.val.funding.chosen.map SelectedPurseHead.head) event enabled] at taken

/-- **A funded firing neither adds nor removes a purse**, apart from the purses
its contractum releases. -/
theorem costResource_purses_card (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (enabled : (costResourceSystem Ground).Enables config event) :
    config.purses.card + event.val.contractum.purses.card =
      (CostConfig.purses ((costResourceSystem Ground).fire config event)).card := by
  have kept :=
    costResource_run_purses_card ((costResourceSystem Ground).firing config event enabled)
  rwa [(costResourceSystem Ground).instanceValuation_firing
    (fun event => event.val.contractum.purses.card) event enabled] at kept

end Conservation

/-! ## A funding cover is a firing of the purses -/

/-- A located purse as a place with its cells, the top cell first. -/
def LocatedPurse.toPurse (purse : LocatedPurse Ground) : CostName Ground × List (CostSig Ground) :=
  (purse.location, purse.stack.toList)

/-- The located purses of a configuration are its purses. -/
theorem LocatedPurse.purses_configComponents (purses : Multiset (LocatedPurse Ground)) :
    (LocatedPurse.configComponents purses).purses = purses.map LocatedPurse.toPurse := by
  have terms :
      LocatedPurse.configComponents purses = (purses.map LocatedPurse.toPurse).map purseTerm := by
    unfold LocatedPurse.configComponents
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun purse _ => (purseTerm_toList purse.location purse.stack).symm
  rw [terms, CostConfig.purses_map_purseTerm]

/-- **A funding cover fires the purse system**: the available purses enable the
choice of the selected purses at the location of the cover, and the firing
leaves the residual purses. -/
theorem LocatedTokenCover.purses_firing [DecidableEq Ground] {location : CostName Ground}
    {demand : CostSig Ground} {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual) :
    (pursesMany (CostName Ground) (CostSig Ground)).Enables (available.map LocatedPurse.toPurse)
        (site := location) (cover.chosen.map fun choice => (choice.head, choice.tail.toList)) ∧
      (pursesMany (CostName Ground) (CostSig Ground)).fire (available.map LocatedPurse.toPurse)
          (site := location) (cover.chosen.map fun choice => (choice.head, choice.tail.toList)) =
        residual.map LocatedPurse.toPurse := by
  have before : available.map LocatedPurse.toPurse =
      cover.untouched.map LocatedPurse.toPurse +
        (cover.chosen.map fun choice => (choice.head, choice.tail.toList)).map
          fun purse => (location, purse.1 :: purse.2) :=
    (congrArg (Multiset.map LocatedPurse.toPurse) cover.available_eq).trans (by
      rw [Multiset.map_add, Multiset.map_map, Multiset.map_map, add_comm]
      rfl)
  have after : residual.map LocatedPurse.toPurse =
      cover.untouched.map LocatedPurse.toPurse +
        (cover.chosen.map fun choice => (choice.head, choice.tail.toList)).map
          fun purse => (location, purse.2) :=
    (congrArg (Multiset.map LocatedPurse.toPurse) cover.residual_eq).trans (by
      rw [Multiset.map_add, Multiset.map_map, Multiset.map_map, add_comm]
      rfl)
  rw [before, after, pursesMany_enables_iff, pursesMany_fire_add]
  exact ⟨Multiset.le_add_left _ _, rfl⟩

/-- **The cells a funding cover takes are its selected heads.** -/
theorem LocatedTokenCover.cells_taken [DecidableEq Ground] {location : CostName Ground}
    {demand : CostSig Ground} {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual) :
    cellBag (available.map LocatedPurse.toPurse) =
      cellBag (residual.map LocatedPurse.toPurse) + cover.chosen.map SelectedPurseHead.head := by
  obtain ⟨enabled, fired⟩ := cover.purses_firing
  rw [← fired, pursesMany_cells_taken _ _ _ enabled, Multiset.map_map]
  rfl

/-! ## Where no purse holds a cell -/

/-- **No funded event is enabled at a location where no purse holds a cell.** -/
theorem costResource_disabled_of_no_cell (config : CostConfig Ground)
    {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (noCell : ∀ top rest, (location, top :: rest) ∉ config.purses) :
    ¬ (costResourceSystem Ground).Enables config event := fun enabled =>
  pursesMany_disabled_of_no_cell config.purses location event.val.chosenPurses noCell
    event.val.chosenPurses_ne_zero ((costResource_enables_iff config event).mp enabled).2

/-- **A purse at another location does not pay.** With no purse at a location,
no funded event there is enabled, whatever the other purses hold. -/
theorem costResource_disabled_elsewhere (config : CostConfig Ground)
    {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (elsewhere : ∀ purse ∈ config.purses, purse.1 ≠ location) :
    ¬ (costResourceSystem Ground).Enables config event :=
  costResource_disabled_of_no_cell config event fun _ _ member => elsewhere _ member rfl

/-! ## The funded system and the product on the sum of the two carriers -/

/-- A configuration split into its components that are not purses and its
purses. -/
def CostConfig.split (config : CostConfig Ground) :
    Multiset (CostTerm Ground ⊕ (CostName Ground × List (CostSig Ground))) :=
  marking (config.filter fun term => ¬ term.isPurse) config.purses

/-- Reading the purses of a split configuration as terms gives the
configuration back. -/
theorem CostConfig.map_split (config : CostConfig Ground) :
    config.split.map (Sum.elim id purseTerm) = config := by
  unfold CostConfig.split
  rw [map_elim_marking, Multiset.map_id, ← CostConfig.filter_isPurse, add_comm]
  exact Multiset.filter_add_not _ config

/-- **A funded event is enabled in a configuration exactly when it is enabled
in the product at the split configuration.** -/
theorem costResource_enables_iff_product (config : CostConfig Ground)
    {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    (costResourceSystem Ground).Enables config event ↔
      (paidProductSystem Ground).Enables config.split event :=
  (costResource_enables_iff config event).trans
    ((unpaidResourceSystem Ground).product_enables_iff
      (pursesMany (CostName Ground) (CostSig Ground)) (@unpaidEntry Ground) (@purseEntry Ground)
      (config.filter fun term => ¬ term.isPurse) config.purses event).symm

/-- **Two funded events are concurrent in a configuration exactly when they are
concurrent in the product at the split configuration.** -/
theorem costResource_concurrent_iff_product (config : CostConfig Ground)
    {location₁ location₂ : CostName Ground}
    (first : {event : CostedEvent Ground // event.location = location₁})
    (second : {event : CostedEvent Ground // event.location = location₂}) :
    (costResourceSystem Ground).Concurrent config first second ↔
      (paidProductSystem Ground).Concurrent config.split first second :=
  (costResource_concurrent_iff config first second).trans
    ((unpaidResourceSystem Ground).product_concurrent_iff
      (pursesMany (CostName Ground) (CostSig Ground)) (@unpaidEntry Ground) (@purseEntry Ground)
      (config.filter fun term => ¬ term.isPurse) config.purses first second).symm

/-- **Firing a funded event is firing the product at the split configuration
and reading the purses of the result as terms.** -/
theorem costResource_fire_eq_map_product [DecidableEq Ground] (config : CostConfig Ground)
    {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    (costResourceSystem Ground).fire config event =
      ((paidProductSystem Ground).fire config.split event).map (Sum.elim id purseTerm) := by
  have fired := (unpaidResourceSystem Ground).product_fire
    (pursesMany (CostName Ground) (CostSig Ground)) (@unpaidEntry Ground) (@purseEntry Ground)
    (config.filter fun term => ¬ term.isPurse) config.purses event
  rw [costResource_fire]
  refine Eq.trans ?_ (congrArg (Multiset.map (Sum.elim id purseTerm)) fired).symm
  rw [map_elim_marking, Multiset.map_id]
  rfl

/-- **Splitting commutes with firing when the contractum releases no purse.**
Then the configuration after a funded firing, split, is the product fired at
the split configuration. A released purse is a purse after the firing on terms,
and a term of the first factor after the firing of the product. -/
theorem costResource_split_fire [DecidableEq Ground] (config : CostConfig Ground)
    {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (releasesNone : event.val.contractum.purses = 0) :
    CostConfig.split ((costResourceSystem Ground).fire config event) =
      (paidProductSystem Ground).fire config.split event := by
  have fired := (unpaidResourceSystem Ground).product_fire
    (pursesMany (CostName Ground) (CostSig Ground)) (@unpaidEntry Ground) (@purseEntry Ground)
    (config.filter fun term => ¬ term.isPurse) config.purses event
  refine Eq.trans ?_ fired.symm
  unfold CostConfig.split
  rw [costResource_fire_purses, costResource_fire_code, releasesNone, add_zero,
    CostConfig.filter_not_isPurse_eq_self releasesNone, ← CostedEvent.unpaid_endpoints,
    ← CostedEvent.unpaid_contractum]
  rfl

/-- **Splitting commutes with firing exactly when the contractum releases no
purse.** -/
theorem costResource_split_fire_iff [DecidableEq Ground] (config : CostConfig Ground)
    {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location}) :
    CostConfig.split ((costResourceSystem Ground).fire config event) =
        (paidProductSystem Ground).fire config.split event ↔
      event.val.contractum.purses = 0 := by
  refine ⟨fun same => ?_, costResource_split_fire config event⟩
  have fired := (unpaidResourceSystem Ground).product_fire
    (pursesMany (CostName Ground) (CostSig Ground)) (@unpaidEntry Ground) (@purseEntry Ground)
    (config.filter fun term => ¬ term.isPurse) config.purses event
  have purses := congrArg rightPart (same.trans fired)
  unfold CostConfig.split at purses
  rw [rightPart_marking, rightPart_marking, costResource_fire_purses] at purses
  exact add_eq_left.mp purses

/-- **The steps of the funded system are the steps of the product at the split
configuration, with the purses of the result read as terms.** -/
theorem costResource_rewrites_iff_product [DecidableEq Ground]
    {source target : CostConfig Ground} :
    (costResourceSystem Ground).theory.rewrites source target ↔
      ∃ result, (paidProductSystem Ground).theory.rewrites source.split result ∧
        target = result.map (Sum.elim id purseTerm) := by
  constructor
  · rintro ⟨location, event, enabled, rfl⟩
    exact ⟨_,
      ⟨location, event, (costResource_enables_iff_product source event).mp enabled, rfl⟩,
      costResource_fire_eq_map_product source event⟩
  · rintro ⟨_, ⟨location, event, enabled, rfl⟩, rfl⟩
    exact ⟨location, event, (costResource_enables_iff_product source event).mpr enabled,
      (costResource_fire_eq_map_product source event).symm⟩

/-! ## The joint instances are the permitted pairs -/

namespace UnpaidEvent

/-- Paying for a communication gives an event for that communication. -/
theorem unpaid_fund (unpaid : UnpaidEvent Ground)
    (funding : FundingSelection Ground unpaid.location unpaid.demand) :
    (unpaid.fund funding).unpaid = unpaid := by
  cases unpaid <;> rfl

/-- Paying for a communication with a selection gives an event selecting those
purses. -/
theorem chosenPurses_fund (unpaid : UnpaidEvent Ground)
    (funding : FundingSelection Ground unpaid.location unpaid.demand) :
    (unpaid.fund funding).chosenPurses =
      funding.chosen.map fun choice => (choice.head, choice.tail.toList) := by
  cases unpaid <;> rfl

end UnpaidEvent

/-- The selection of the purses with the given top cells and rests, when every
top cell is a valid signature and the top cells sum to the demand. -/
def FundingSelection.ofPurses (location : CostName Ground) (demand : CostSig Ground)
    (chosen : Multiset (CostSig Ground × List (CostSig Ground)))
    (valid : ∀ purse ∈ chosen, purse.1.RuntimeValid)
    (sums : demand = (chosen.map Prod.fst).sum) : FundingSelection Ground location demand where
  chosen := chosen.attach.map fun purse =>
    ⟨purse.1.1, CostStack.ofList purse.1.2, valid purse.1 purse.2⟩
  demand_eq := by
    rw [Multiset.map_map]
    change demand = (chosen.attach.map (Prod.fst ∘ Subtype.val)).sum
    rw [← Multiset.map_map, Multiset.attach_map_val]
    exact sums

/-- The selection built from a bag of purses selects those purses. -/
theorem FundingSelection.ofPurses_chosen (location : CostName Ground) (demand : CostSig Ground)
    (chosen : Multiset (CostSig Ground × List (CostSig Ground)))
    (valid : ∀ purse ∈ chosen, purse.1.RuntimeValid)
    (sums : demand = (chosen.map Prod.fst).sum) :
    (FundingSelection.ofPurses location demand chosen valid sums).chosen.map
        (fun choice => (choice.head, choice.tail.toList)) = chosen := by
  unfold FundingSelection.ofPurses
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.attach_map_val chosen]
  refine Multiset.map_congr rfl fun purse _ => ?_
  change (purse.1.1, (CostStack.ofList purse.1.2).toList) = purse.1
  rw [CostStack.toList_ofList]

/-- A selected purse is determined by its head and the cells of its tail. -/
theorem selectedPurse_injective :
    Function.Injective fun choice : SelectedPurseHead Ground =>
      (choice.head, choice.tail.toList) := by
  rintro ⟨head, tail, valid⟩ ⟨head', tail', valid'⟩ same
  obtain ⟨rfl, sameCells⟩ := Prod.mk.inj same
  obtain rfl : tail = tail' := by
    have restored := congrArg CostStack.ofList sameCells
    rwa [CostStack.ofList_toList, CostStack.ofList_toList] at restored
  rfl

namespace CostedEvent

/-- **A funded event is a communication with a selection of purses** at its
location whose heads sum to its demand. -/
def equivUnpaidFunding : CostedEvent Ground ≃
    Σ unpaid : UnpaidEvent Ground, FundingSelection Ground unpaid.location unpaid.demand where
  toFun
    | .wholeRecvSend channel body payload outerSig valid funding =>
        ⟨.wholeRecvSend channel body payload outerSig valid, funding⟩
    | .wholeSendRecv channel body payload outerSig valid funding =>
        ⟨.wholeSendRecv channel body payload outerSig valid, funding⟩
    | .split channel body payload recvSeal sendSeal recvValid sendValid funding =>
        ⟨.split channel body payload recvSeal sendSeal recvValid sendValid, funding⟩
  invFun pair := pair.1.fund pair.2
  left_inv event := by cases event <;> rfl
  right_inv := by
    rintro ⟨unpaid, funding⟩
    cases unpaid <;> rfl

/-- The first component of an event, as a pair, is its communication. -/
theorem equivUnpaidFunding_fst (event : CostedEvent Ground) :
    (equivUnpaidFunding event).1 = event.unpaid := by
  cases event <;> rfl

/-- The second component of an event, as a pair, selects what the event selects. -/
theorem equivUnpaidFunding_chosen (event : CostedEvent Ground) :
    (equivUnpaidFunding event).2.chosen = event.funding.chosen := by
  cases event <;> rfl

/-- **A funded event is determined by its communication and the purses it
selects.** -/
theorem ext_unpaid_chosenPurses {first second : CostedEvent Ground}
    (sameUnpaid : first.unpaid = second.unpaid)
    (samePurses : first.chosenPurses = second.chosenPurses) : first = second := by
  have determined : ∀ p q : Σ unpaid : UnpaidEvent Ground,
      FundingSelection Ground unpaid.location unpaid.demand,
      p.1 = q.1 → p.2.chosen = q.2.chosen → p = q := by
    rintro ⟨unpaid, chosen, sums⟩ ⟨unpaid', chosen', sums'⟩ sameUnpaid sameChosen
    cases sameUnpaid
    cases sameChosen
    rfl
  refine equivUnpaidFunding.injective (determined _ _ ?_ ?_)
  · rw [equivUnpaidFunding_fst, equivUnpaidFunding_fst, sameUnpaid]
  · rw [equivUnpaidFunding_chosen, equivUnpaidFunding_chosen]
    exact Multiset.map_injective selectedPurse_injective samePurses

end CostedEvent

/-- **Which choices of purses pay for a communication.** A bag of purses, each
given by its top cell and the cells under it, is what a funded event for the
communication selects exactly when every top cell is a valid signature and the
top cells sum to the demand of the communication. -/
theorem UnpaidEvent.exists_funded_iff (unpaid : UnpaidEvent Ground)
    (chosen : Multiset (CostSig Ground × List (CostSig Ground))) :
    (∃ event : CostedEvent Ground, event.unpaid = unpaid ∧ event.chosenPurses = chosen) ↔
      (∀ purse ∈ chosen, purse.1.RuntimeValid) ∧
        unpaid.demand = (chosen.map Prod.fst).sum := by
  constructor
  · rintro ⟨event, rfl, rfl⟩
    refine ⟨fun purse member => ?_, ?_⟩
    · obtain ⟨choice, _, rfl⟩ := Multiset.mem_map.mp member
      exact choice.head_valid
    · rw [CostedEvent.chosenPurses_tops, CostedEvent.sum_selected_heads,
        CostedEvent.unpaid_demand]
  · rintro ⟨valid, sums⟩
    refine ⟨unpaid.fund (FundingSelection.ofPurses unpaid.location unpaid.demand chosen valid
      sums), unpaid.unpaid_fund _, ?_⟩
    rw [UnpaidEvent.chosenPurses_fund]
    exact FundingSelection.ofPurses_chosen unpaid.location unpaid.demand chosen valid sums

/-- **The funded events are the communications with a permitted choice of
purses.** -/
def CostedEvent.equivPermitted : CostedEvent Ground ≃
    {pair : UnpaidEvent Ground × Multiset (CostSig Ground × List (CostSig Ground)) //
      (∀ purse ∈ pair.2, purse.1.RuntimeValid) ∧
        pair.1.demand = (pair.2.map Prod.fst).sum} where
  toFun event := ⟨(event.unpaid, event.chosenPurses),
    (event.unpaid.exists_funded_iff event.chosenPurses).mp ⟨event, rfl, rfl⟩⟩
  invFun pair := pair.1.1.fund
    (FundingSelection.ofPurses pair.1.1.location pair.1.1.demand pair.1.2 pair.2.1 pair.2.2)
  left_inv _ := CostedEvent.ext_unpaid_chosenPurses (UnpaidEvent.unpaid_fund _ _)
    ((UnpaidEvent.chosenPurses_fund _ _).trans (FundingSelection.ofPurses_chosen _ _ _ _ _))
  right_inv _ := Subtype.ext (Prod.ext (UnpaidEvent.unpaid_fund _ _)
    ((UnpaidEvent.chosenPurses_fund _ _).trans (FundingSelection.ofPurses_chosen _ _ _ _ _)))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Controls on terms

Two receivers and two senders meet on one channel, each pair under the seal
`{7}`. A purse pays for a meeting with a cell `{7}` on top. -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.PaidControls

open Mettapedia.GSLT.Causality.ResourceInteraction

/-- The channel of the meetings. -/
def channel : CostName ℕ := .signature {0}

/-- Another location. -/
def elsewhere : CostName ℕ := .signature {1}

/-- The seal of a meeting, and the cell that pays for it. -/
def stamp : CostSig ℕ := {7}

theorem stamp_valid : stamp.RuntimeValid := Multiset.singleton_ne_zero 7

/-- A receiver and a sender on the channel under one seal. The receiver runs
what it receives. -/
def meeting (payload : CostTerm ℕ) : UnpaidEvent ℕ :=
  .wholeRecvSend channel (.drop (.bvar 0)) payload stamp stamp_valid

/-- The term holding the two endpoints of a meeting. -/
def endpointsOf (payload : CostTerm ℕ) : CostTerm ℕ :=
  .signed (.par (.recv channel (.drop (.bvar 0))) (.send channel payload)) stamp

/-- The first message. -/
def first : CostTerm ℕ := .signed .nil {1}

/-- The second message. -/
def second : CostTerm ℕ := .signed .nil {2}

/-- The selection of one purse on the channel: `stamp` on top of the cells `rest`. -/
def fromPurse (rest : List (CostSig ℕ)) : FundingSelection ℕ channel stamp where
  chosen := {⟨stamp, CostStack.ofList rest, stamp_valid⟩}
  demand_eq := by simp

/-- The meeting, paid from a purse on the channel holding `stamp` on top of
`rest`. -/
def paid (payload : CostTerm ℕ) (rest : List (CostSig ℕ)) :
    (costResourceSystem ℕ).Instance channel :=
  ⟨(meeting payload).fund (fromPurse rest), rfl⟩

/-! ### Communication without payment -/

/-- **The unpaid communication needs no purse; the funded one does.** With the
two endpoints and no purse, the meeting is enabled in the unpaid system and no
funded event on the channel is enabled. The unpaid meeting is not enabled where
its endpoints are missing. -/
theorem unpaid_needs_no_purse :
    (unpaidResourceSystem ℕ).Enables {endpointsOf first} (site := channel)
        ⟨meeting first, rfl⟩ ∧
      (∀ event : (costResourceSystem ℕ).Instance channel,
        ¬ (costResourceSystem ℕ).Enables {endpointsOf first} event) ∧
      ¬ (unpaidResourceSystem ℕ).Enables {endpointsOf second} (site := channel)
        ⟨meeting first, rfl⟩ := by
  refine ⟨by unfold System.Enables; decide, fun event => ?_, by unfold System.Enables; decide⟩
  have none : CostConfig.purses ({endpointsOf first} : CostConfig ℕ) = 0 := by decide
  refine costResource_disabled_elsewhere _ event fun purse member => ?_
  rw [none] at member
  exact (Multiset.notMem_zero purse member).elim

/-! ### One purse orders its payments -/

/-- Two meetings and one purse of two cells. -/
def onePurse : CostConfig ℕ :=
  {endpointsOf first, endpointsOf second, purseTerm (channel, [stamp, stamp])}

/-- **One purse with two cells orders two payments.** Either meeting can be paid
from the purse, and the two firings are not concurrent: both name the one purse.
After the first, the second is paid from what is left of the purse. -/
theorem one_purse_orders_payments :
    (costResourceSystem ℕ).Enables onePurse (paid first [stamp]) ∧
      (costResourceSystem ℕ).Enables onePurse (paid second [stamp]) ∧
      ¬ (costResourceSystem ℕ).Concurrent onePurse (paid first [stamp]) (paid second [stamp]) ∧
      (costResourceSystem ℕ).Enables ((costResourceSystem ℕ).fire onePurse (paid first [stamp]))
        (paid second []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold System.Enables; decide
  · unfold System.Enables; decide
  · unfold System.Concurrent; decide
  · unfold System.Enables System.fire; decide

/-- Two meetings and one purse of one cell. -/
def oneCell : CostConfig ℕ :=
  {endpointsOf first, endpointsOf second, purseTerm (channel, [stamp])}

/-- **A purse with one cell pays once.** The first meeting is paid. After it the
purse is empty, and no funded event on the channel is enabled, whatever purses
it selects. -/
theorem one_cell_pays_once :
    (costResourceSystem ℕ).Enables oneCell (paid first []) ∧
      ∀ event : (costResourceSystem ℕ).Instance channel,
        ¬ (costResourceSystem ℕ).Enables ((costResourceSystem ℕ).fire oneCell (paid first []))
          event := by
  refine ⟨by unfold System.Enables; decide, fun event => ?_⟩
  have emptied : CostConfig.purses ((costResourceSystem ℕ).fire oneCell (paid first [])) =
      {(channel, [])} := by
    unfold System.fire; decide
  refine costResource_disabled_of_no_cell _ event fun top rest member => ?_
  rw [emptied] at member
  cases Multiset.mem_singleton.mp member

/-! ### Two purses pay concurrently -/

/-- Two meetings and two purses holding the same cell. -/
def twoPurses : CostConfig ℕ :=
  {endpointsOf first, endpointsOf second, purseTerm (channel, [stamp]),
    purseTerm (channel, [stamp])}

/-- **Two purses with equal contents at one location pay concurrently.** With
one of them the two meetings are each enabled and not concurrent. -/
theorem equal_purses_pay_concurrently :
    (costResourceSystem ℕ).Concurrent twoPurses (paid first []) (paid second []) ∧
      (costResourceSystem ℕ).Enables oneCell (paid first []) ∧
      (costResourceSystem ℕ).Enables oneCell (paid second []) ∧
      ¬ (costResourceSystem ℕ).Concurrent oneCell (paid first []) (paid second []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold System.Concurrent; decide
  · unfold System.Enables; decide
  · unfold System.Enables; decide
  · unfold System.Concurrent; decide

/-! ### The purse a firing names -/

/-- Two meetings, a purse of two cells and a purse of one cell. -/
def twoKinds : CostConfig ℕ :=
  {endpointsOf first, endpointsOf second, purseTerm (channel, [stamp, stamp]),
    purseTerm (channel, [stamp])}

/-- **Two firings naming the same single purse are not concurrent**, although
another purse with the right cell on top is at the location. Naming the two
different purses, they are concurrent. -/
theorem same_purse_named_twice :
    ¬ (costResourceSystem ℕ).Concurrent twoKinds (paid first [stamp]) (paid second [stamp]) ∧
      (costResourceSystem ℕ).Concurrent twoKinds (paid first [stamp]) (paid second []) := by
  refine ⟨?_, ?_⟩
  · unfold System.Concurrent; decide
  · unfold System.Concurrent; decide

/-! ### A purse at another location -/

/-- A meeting and a purse at its channel. -/
def purseHere : CostConfig ℕ := {endpointsOf first, purseTerm (channel, [stamp])}

/-- The meeting, with the same purse at another location. -/
def purseElsewhere : CostConfig ℕ := {endpointsOf first, purseTerm (elsewhere, [stamp])}

/-- **A purse at another location does not pay.** The purse at the channel pays
for the meeting. With the same purse elsewhere, no funded event on the channel
is enabled, whatever purses it selects. -/
theorem purse_elsewhere_does_not_pay :
    (costResourceSystem ℕ).Enables purseHere (paid first []) ∧
      ∀ event : (costResourceSystem ℕ).Instance channel,
        ¬ (costResourceSystem ℕ).Enables purseElsewhere event := by
  refine ⟨by unfold System.Enables; decide, fun event => ?_⟩
  have away : CostConfig.purses purseElsewhere = {(elsewhere, [stamp])} := by decide
  refine costResource_disabled_elsewhere _ event fun purse member => ?_
  rw [away] at member
  obtain rfl := Multiset.mem_singleton.mp member
  decide

/-! ### What the type of events forbids -/

/-- **The heads of the selected purses must be valid and sum to the demand.**
One purse with `{7}` on top pays for the meeting. A purse with another cell on
top, two purses with `{7}` on top, no purse, and a purse with the empty
signature on top beside the right one, are not selections of any funded event
for the meeting. -/
theorem heads_must_sum_to_demand :
    (∃ event : CostedEvent ℕ, event.unpaid = meeting first ∧
        event.chosenPurses = {(stamp, [])}) ∧
      (¬ ∃ event : CostedEvent ℕ, event.unpaid = meeting first ∧
        event.chosenPurses = {({8}, [])}) ∧
      (¬ ∃ event : CostedEvent ℕ, event.unpaid = meeting first ∧
        event.chosenPurses = {(stamp, []), (stamp, [])}) ∧
      (¬ ∃ event : CostedEvent ℕ, event.unpaid = meeting first ∧ event.chosenPurses = 0) ∧
      ¬ ∃ event : CostedEvent ℕ, event.unpaid = meeting first ∧
        event.chosenPurses = {(stamp, []), (0, [])} := by
  refine ⟨⟨(paid first []).val, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [UnpaidEvent.exists_funded_iff]
    exact fun permitted => absurd permitted.2 (by decide)
  · rw [UnpaidEvent.exists_funded_iff]
    exact fun permitted => absurd permitted.2 (by decide)
  · rw [UnpaidEvent.exists_funded_iff]
    exact fun permitted => absurd permitted.2 (by decide)
  · rw [UnpaidEvent.exists_funded_iff]
    exact fun permitted => permitted.1 (0, []) (by decide) rfl

/-! ### One firing paid by two purses -/

/-- A receiver under the seal `{7}` and a sender under the seal `{8}`. Their
meeting asks for both seals. -/
def sealedApart : UnpaidEvent ℕ :=
  .split channel (.drop (.bvar 0)) first {7} {8} (Multiset.singleton_ne_zero 7)
    (Multiset.singleton_ne_zero 8)

/-- The selection of two purses on the channel, one cell each: `{7}` and `{8}`. -/
def fromTwoPurses : FundingSelection ℕ channel ({7} + {8}) where
  chosen := {⟨{7}, .empty, Multiset.singleton_ne_zero 7⟩,
    ⟨{8}, .empty, Multiset.singleton_ne_zero 8⟩}
  demand_eq := by decide

/-- The meeting of the two separately sealed endpoints, paid from two purses. -/
def paidByTwo : (costResourceSystem ℕ).Instance channel :=
  ⟨sealedApart.fund fromTwoPurses, rfl⟩

/-- The two endpoints, a purse holding `{7}` and a purse holding `{8}`. -/
def twoSeals : CostConfig ℕ :=
  {.signed (.recv channel (.drop (.bvar 0))) {7}, .signed (.send channel first) {8},
    purseTerm (channel, [{7}]), purseTerm (channel, [{8}])}

/-- **One firing takes the top cells of two purses.** Both purses are needed:
with the second purse elsewhere the event is not enabled. The two purses stay,
empty. -/
theorem one_firing_takes_two_purses :
    (costResourceSystem ℕ).Enables twoSeals paidByTwo ∧
      ¬ (costResourceSystem ℕ).Enables
        {.signed (.recv channel (.drop (.bvar 0))) {7}, .signed (.send channel first) {8},
          purseTerm (channel, [{7}]), purseTerm (elsewhere, [{8}])} paidByTwo ∧
      CostConfig.purses twoSeals = {(channel, [{7}]), (channel, [{8}])} ∧
      CostConfig.purses ((costResourceSystem ℕ).fire twoSeals paidByTwo) =
        {(channel, []), (channel, [])} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold System.Enables; decide
  · unfold System.Enables; decide
  · decide
  · unfold System.fire; decide

/-! ### A purse released by the contractum -/

/-- A receiver whose continuation is a purse on the channel holding one cell. -/
def releasing : UnpaidEvent ℕ :=
  .wholeRecvSend channel (.purse channel (.cons stamp .empty)) .nil stamp stamp_valid

/-- The releasing meeting, paid from a purse holding one cell. -/
def releasingPaid : (costResourceSystem ℕ).Instance channel :=
  ⟨releasing.fund (fromPurse []), rfl⟩

/-- The releasing meeting, the first meeting, and one purse of one cell. -/
def beforeRelease : CostConfig ℕ :=
  {.signed (.par (.recv channel (.purse channel (.cons stamp .empty))) (.send channel .nil)) stamp,
    endpointsOf first, purseTerm (channel, [stamp])}

/-- **A purse released by the contractum pays later.** The one purse pays for
one of the two meetings, so they are not concurrent. Firing the releasing
meeting empties that purse and adds the purse of its contractum, which then
pays for the other meeting. The purses after the firing are therefore not what
the purse system alone gives. -/
theorem released_purse_pays_later :
    (costResourceSystem ℕ).Enables beforeRelease releasingPaid ∧
      ¬ (costResourceSystem ℕ).Concurrent beforeRelease releasingPaid (paid first []) ∧
      (costResourceSystem ℕ).Enables ((costResourceSystem ℕ).fire beforeRelease releasingPaid)
        (paid first []) ∧
      CostConfig.purses ((costResourceSystem ℕ).fire beforeRelease releasingPaid) =
        {(channel, []), (channel, [stamp])} ∧
      (pursesMany (CostName ℕ) (CostSig ℕ)).fire beforeRelease.purses (site := channel)
        releasingPaid.val.chosenPurses = {(channel, [])} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold System.Enables; decide
  · unfold System.Concurrent; decide
  · unfold System.Enables System.fire; decide
  · unfold System.fire; decide
  · unfold System.fire; decide

/-- **With a released purse, splitting does not commute with firing.** The
product keeps the released purse among the terms of its first factor, where it
pays for nothing: the first meeting is not enabled there. Read on terms it is a
purse of the configuration, and the first meeting is enabled. -/
theorem released_purse_is_not_split :
    CostConfig.split ((costResourceSystem ℕ).fire beforeRelease releasingPaid) ≠
        (paidProductSystem ℕ).fire beforeRelease.split releasingPaid ∧
      ¬ (paidProductSystem ℕ).Enables
        ((paidProductSystem ℕ).fire beforeRelease.split releasingPaid) (paid first []) ∧
      (costResourceSystem ℕ).Enables ((costResourceSystem ℕ).fire beforeRelease releasingPaid)
        (paid first []) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold System.fire; decide
  · unfold System.Enables System.fire; decide
  · unfold System.Enables System.fire; decide

/-- **The cells taken balance only with the released purse.** The releasing
meeting takes the one cell `{7}`, and its contractum releases a purse holding
`{7}`: the cells of the purses are the same before and after. With the cells of
the released purse the balance holds; without them it fails. -/
theorem released_cells_balance :
    cellBag beforeRelease.purses + cellBag releasingPaid.val.contractum.purses =
        cellBag (CostConfig.purses ((costResourceSystem ℕ).fire beforeRelease releasingPaid)) +
          releasingPaid.val.funding.chosen.map SelectedPurseHead.head ∧
      cellBag beforeRelease.purses ≠
        cellBag (CostConfig.purses ((costResourceSystem ℕ).fire beforeRelease releasingPaid)) +
          releasingPaid.val.funding.chosen.map SelectedPurseHead.head :=
  ⟨costResource_cells_taken beforeRelease releasingPaid (by unfold System.Enables; decide),
    by unfold System.fire; decide⟩

/-- **The unpaid communication does not produce only terms that are not
purses**, where the purse system produces only purses. This is why the purses
after a firing are not the firing of the purse system alone. -/
theorem contractum_may_hold_a_purse :
    (∃ term ∈ (unpaidResourceSystem ℕ).produce (unpaidEntry releasingPaid).2,
        term.isPurse) ∧
      ∀ term ∈ (unpaidResourceSystem ℕ).produce (unpaidEntry (paid first [])).2,
        ¬ term.isPurse := by
  refine ⟨⟨purseTerm (channel, [stamp]), by decide, rfl⟩, ?_⟩
  decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.PaidControls
