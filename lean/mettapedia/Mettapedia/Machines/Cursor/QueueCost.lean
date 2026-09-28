import Mettapedia.Machines.Cursor.RelationalAmortized

/-!
# Two-list queues, live clients, and sequential potential

The queue provider keeps a front list and a reversed rear list. Enqueue conses
onto the rear; dequeue reverses the rear only when the front is empty. Its
representation map is proved against an independently implemented list queue.
The cursor protocol preserves replies, order, duplicate occurrences, and the
actual paused or completed continuation of every adaptive bounded client.

The meter charges one unit per request, one per cons allocation, and one per
visited list cell. Reversal counts both its visit and its new cons. Rear-list
potential pays for reversal along one successive chain of residual states.
The comparison with other providers assumes the same sequential unit-request
model; it says nothing about hardware, batching, concurrency, or client work.

Immutable residuals may safely be shared, but sharing does not duplicate their
amortization credit: independent branches can each repeat the same reversal.
`ExclusiveSequenceMutation.Exclusive` supplies a separate transitive-ownership
condition for destructive sequence updates. The pure queue proofs here neither
establish that heap condition nor authorize mutation of a shared residual.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.QueueCost

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open CategoryTheory

variable (Item : Type)

inductive Request where
  | enqueue (item : Item)
  | dequeue
  deriving Repr, DecidableEq

def Reply : Request Item → Type
  | .enqueue _ => Unit
  | .dequeue => Option Item

def protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Request Item
  Position request := Reply Item request
  next _ _ := ()

structure Queue where
  front : List Item
  rear : List Item
  deriving Repr, DecidableEq

def contents (queue : Queue Item) : List Item := queue.front ++ queue.rear.reverse

/-- An independent queue specification: enqueue appends, dequeue takes a head. -/
def logical : Provider (protocol Item) where
  State _ _ := List Item
  step items request := match request with
    | .enqueue item => ⟨(), items ++ [item]⟩
    | .dequeue => match items with
      | [] => ⟨none, []⟩
      | item :: rest => ⟨some item, rest⟩

/-- Tail-recursive reversal counts a cell inspection and a cons at each step. -/
def reverseCount : List Item → List Item → Nat × List Item
  | [], result => (0, result)
  | item :: rest, result =>
      let next := reverseCount rest (item :: result)
      (2 + next.1, next.2)

theorem reverseCount_exact (items result : List Item) :
    reverseCount Item items result = (2 * items.length, items.reverse ++ result) := by
  induction items generalizing result with
  | nil => simp [reverseCount]
  | cons item rest ih =>
      simp [reverseCount, ih, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_comm]

/-- Execution returns its actual receipt together with the protocol reply and
residual. There is no reversal or full-list traversal in enqueue. -/
def execute (queue : Queue Item) :
    (request : Request Item) → Nat × (Reply Item request × Queue Item)
  | .enqueue item => (2, (), ⟨queue.front, item :: queue.rear⟩)
  | .dequeue => match queue.front with
    | item :: rest => (2, some item, ⟨rest, queue.rear⟩)
    | [] =>
        let reversed := reverseCount Item queue.rear []
        match reversed.2 with
        | [] => (1 + reversed.1, none, ⟨[], []⟩)
        | item :: rest => (2 + reversed.1, some item, ⟨rest, []⟩)

def provider : Provider (protocol Item) where
  State _ _ := Queue Item
  step queue request := ⟨(execute Item queue request).2.1,
    (execute Item queue request).2.2⟩

def work : Charge (provider Item) := fun queue request => (execute Item queue request).1

def representation : Hom (provider Item) (logical Item) where
  map queue := contents Item queue
  step queue request := by
    rcases queue with ⟨front, rear⟩
    cases request with
    | enqueue item =>
        simp [provider, execute, contents, logical, List.reverse_cons, List.append_assoc]
    | dequeue =>
        cases front with
        | cons item rest => simp [provider, execute, contents, logical]
        | nil =>
            simp only [provider, execute, reverseCount_exact, List.append_nil, contents,
              List.nil_append, logical]
            cases rear.reverse <;> simp

/-- Two credits per rear cell pay for its later inspection and reverse-cons. -/
def potential : Potential (provider Item) := fun queue => 2 * queue.rear.length

theorem request_cost_positive (queue : Queue Item) (request : Request Item) :
    1 ≤ work Item (base := ()) (index := ()) queue request := by
  cases request with
  | enqueue item => simp [work, execute]
  | dequeue =>
      rcases queue with ⟨front, rear⟩
      cases front with
      | cons item rest => simp [work, execute]
      | nil =>
          simp only [work, execute, reverseCount_exact, List.append_nil]
          cases rear.reverse <;> simp
          omega

theorem local_amortized :
    Amortized (representation Item) (work Item) (fun _ _ => 4) (potential Item) := by
  intro base index queue request
  rcases queue with ⟨front, rear⟩
  cases request with
  | enqueue item =>
      simp [work, provider, execute, potential, Nat.mul_add]
      omega
  | dequeue =>
      cases front with
      | cons item rest => simp [work, provider, execute, potential]
      | nil =>
          simp only [work, provider, execute, reverseCount_exact, List.append_nil, potential]
          cases rear.reverse <;> simp

/-- Scaling a constant unit-request meter scales the actual executed request
count, even when the client returns early or remains suspended. -/
theorem constant_meter
    {Base : Type} {Index : Base → Type}
    {P : IndexedPolynomial Base Index} {Return : (base : Base) → Index base → Type}
    (M : Provider P) (C : Client (P := P) (Return := Return))
    (weight fuel : Nat) {base : Base} (packet : Packet M C base) :
    (advance M C (fun _ _ => weight) fuel packet).1 =
      weight * (advance M C (fun _ _ => 1) fuel packet).1 := by
  simpa only [Nat.mul_one] using
    advance_charge_scale (source := M) C (fun _ _ => 1) weight fuel packet

theorem request_count_le_budget
    {Base : Type} {Index : Base → Type}
    {P : IndexedPolynomial Base Index} {Return : (base : Base) → Index base → Type}
    (M : Provider P) (C : Client (P := P) (Return := Return))
    (fuel : Nat) {base : Base} (packet : Packet M C base) :
    (advance M C (fun _ _ => 1) fuel packet).1 ≤ fuel := by
  induction fuel generalizing packet with
  | zero => simp [advance]
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      cases eq : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl result => simp [advance, eq]
          | inr request =>
              simp only [advance, eq]
              dsimp only [withHoles]
              have next := ih ⟨_, children (M.step state request).1,
                (M.step state request).2⟩
              dsimp only [withHoles] at next
              omega

/-- Any realization in the stated unit-request model pays at least once for
each operation it executes. No lower bound is imposed on unexecuted work. -/
theorem request_lower_bound
    {Base : Type} {Index : Base → Type}
    {P : IndexedPolynomial Base Index} {Return : (base : Base) → Index base → Type}
    (M : Provider P) (C : Client (P := P) (Return := Return))
    (cost : Charge M)
    (positive : ∀ {base index} (state : M.State base index) (request : P.Shape base index),
      1 ≤ cost state request)
    (fuel : Nat) {base : Base} (packet : Packet M C base) :
    (advance M C (fun _ _ => 1) fuel packet).1 ≤
      (advance M C cost fuel packet).1 := by
  have bound := advance_cost_le C (Hom.id M) (fun _ _ => 1) cost (fun _ => 0)
    (by intro base index state request; simpa [Hom.id] using positive state request)
    fuel packet rfl
  simpa [Hom.packet, Hom.id] using bound

variable {Item}
variable {Return : Unit → Unit → Type}

/-- Exact live-client refinement is independent of the cost model. The full
outcome contains the retained continuation and state, so this also reflects
all responses and distinguishes early return from scheduler suspension. -/
theorem client_refinement (C : Client (P := protocol Item) (Return := Return))
    (fuel : Nat) (packet : Packet (provider Item) C ()) :
    (representation Item).outcome C (advance (provider Item) C (work Item) fuel packet).2 =
      (advance (logical Item) C (fun _ _ => 1) fuel
        ((representation Item).packet C packet)).2 :=
  Hom.advance C (representation Item) _ _ fuel packet

/-- The residual keeps the unspent credit, including while suspended. -/
theorem client_amortized (C : Client (P := protocol Item) (Return := Return))
    (fuel : Nat) (packet : Packet (provider Item) C ()) :
    (advance (provider Item) C (work Item) fuel packet).1 +
        outcomePotential C (potential Item) (advance (provider Item) C (work Item) fuel packet).2 ≤
      4 * (advance (provider Item) C (fun _ _ => 1) fuel packet).1 +
        potential Item packet.2.2 := by
  have bound := advance_amortized C (representation Item) (work Item) (fun _ _ => 4)
    (potential Item) (local_amortized Item) fuel packet
  rw [constant_meter] at bound
  rw [← Hom.advance_charge C (representation Item) (fun _ _ => 1) (fun _ _ => 1)
    (by intros; rfl) fuel packet] at bound
  exact bound

theorem client_linear (C : Client (P := protocol Item) (Return := Return))
    (fuel : Nat) (packet : Packet (provider Item) C ()) :
    (advance (provider Item) C (work Item) fuel packet).1 ≤
      4 * (advance (provider Item) C (fun _ _ => 1) fuel packet).1 +
        2 * packet.2.2.rear.length := by
  have bound := client_amortized C fuel packet
  dsimp only [potential] at bound
  omega

/-- The queue's actual request count is a lower bound, and four units per
request plus initial rear credit is an upper bound, for the same execution. -/
theorem client_cost_sandwich (C : Client (P := protocol Item) (Return := Return))
    (fuel : Nat) (packet : Packet (provider Item) C ()) :
    (advance (provider Item) C (fun _ _ => 1) fuel packet).1 ≤
      (advance (provider Item) C (work Item) fuel packet).1 ∧
    (advance (provider Item) C (work Item) fuel packet).1 ≤
      4 * (advance (provider Item) C (fun _ _ => 1) fuel packet).1 +
        2 * packet.2.2.rear.length := by
  constructor
  · exact request_lower_bound (provider Item) C (work Item)
      (by intro base index queue request; exact request_cost_positive Item queue request)
      fuel packet
  · exact client_linear C fuel packet

theorem empty_client_linear (C : Client (P := protocol Item) (Return := Return))
    (fuel : Nat) (index : Unit) (control : C.V () index) :
    (advance (provider Item) C (work Item) fuel ⟨index, control, ⟨[], []⟩⟩).1 ≤
      4 * (advance (provider Item) C (fun _ _ => 1) fuel
        ⟨index, control, ⟨[], []⟩⟩).1 := by
  simpa using client_linear C fuel ⟨index, control, ⟨[], []⟩⟩

/-- Resuming the actual packet retains the same bound; the potential is not
charged again at each scheduler boundary. -/
theorem resumed_amortized (C : Client (P := protocol Item) (Return := Return))
    (earlier later : Nat) (packet : Packet (provider Item) C ()) :
    (resume (provider Item) C (work Item) later
        (advance (provider Item) C (work Item) earlier packet)).1 +
      outcomePotential C (potential Item)
        (resume (provider Item) C (work Item) later
          (advance (provider Item) C (work Item) earlier packet)).2 ≤
    4 * (resume (provider Item) C (fun _ _ => 1) later
      (advance (provider Item) C (fun _ _ => 1) earlier packet)).1 +
        potential Item packet.2.2 := by
  simpa only [advance_add] using client_amortized C (earlier + later) packet

/-- Compare any other exact provider with the same logical starting queue.
Only unit request charges are lower-bounded, not an invented hardware optimum. -/
theorem constant_factor
    (other : Provider (protocol Item)) (h : Hom other (logical Item))
    (cost : Charge other)
    (positive : ∀ {base index} (state : other.State base index)
      (request : (protocol Item).Shape base index), 1 ≤ cost state request)
    (C : Client (P := protocol Item) (Return := Return)) (fuel : Nat)
    (index : Unit) (control : C.V () index) (queue : Queue Item)
    (state : other.State () index) (same : h.map state = contents Item queue) :
    (advance (provider Item) C (work Item) fuel ⟨index, control, queue⟩).1 ≤
      4 * (advance other C cost fuel ⟨index, control, state⟩).1 + 2 * queue.rear.length := by
  have first := Hom.advance_charge C (representation Item) (fun _ _ => 1)
    (fun _ _ => 1) (by intros; rfl) fuel ⟨index, control, queue⟩
  have second := Hom.advance_charge C h (fun _ _ => 1)
    (fun _ _ => 1) (by intros; rfl) fuel ⟨index, control, state⟩
  simp only [Hom.packet, representation] at first second
  rw [same] at second
  have counts := first.trans second.symm
  have bound := client_linear C fuel ⟨index, control, queue⟩
  rw [counts] at bound
  have lower := request_lower_bound other C cost positive fuel ⟨index, control, state⟩
  dsimp only at bound
  omega

/-- An ordinary interactive client that enqueues its retained input and returns.
Its control is separate from the provider's queue representation. -/
def enqueueClient (Item : Type) : Client (P := protocol Item) (Return := fun _ _ => Unit) where
  V _ _ := List Item
  str := fun _ _ => ↾(fun items => match items with
    | [] => ⟨.inl (), fun impossible => nomatch impossible⟩
    | item :: rest => ⟨.inr (.enqueue item), fun _ => rest⟩)

theorem enqueues_exact (items : List Item) (queue : Queue Item) :
    advance (provider Item) (enqueueClient Item) (work Item) (items.length + 1)
      (base := ()) ⟨(), items, queue⟩ =
    (2 * items.length, .done ⟨(), (), ⟨queue.front, items.reverse ++ queue.rear⟩⟩) := by
  induction items generalizing queue with
  | nil => rfl
  | cons item rest ih =>
      change (2 + (advance (provider Item) (enqueueClient Item) (work Item)
        (rest.length + 1) (base := ()) ⟨(), rest, ⟨queue.front, item :: queue.rear⟩⟩).1,
        (advance (provider Item) (enqueueClient Item) (work Item)
        (rest.length + 1) (base := ()) ⟨(), rest, ⟨queue.front, item :: queue.rear⟩⟩).2) = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_comm]

/-- Eager immutable append visits and recreates each old cell, then allocates
the singleton. This implements the slower comparison provider explicitly. -/
def appendCount (Item : Type) : List Item → Item → Nat × List Item
  | [], item => (1, [item])
  | first :: rest, item =>
      let next := appendCount Item rest item
      (2 + next.1, first :: next.2)

theorem appendCount_exact (items : List Item) (item : Item) :
    appendCount Item items item = (2 * items.length + 1, items ++ [item]) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp [appendCount, ih, Nat.mul_add]
      omega

def naiveExecute (Item : Type) (items : List Item) :
    (request : Request Item) → Nat × (Reply Item request × List Item)
  | .enqueue item =>
      let appended := appendCount Item items item
      (1 + appended.1, (), appended.2)
  | .dequeue => match items with
    | [] => (1, none, [])
    | item :: rest => (2, some item, rest)

def naive (Item : Type) : Provider (protocol Item) where
  State _ _ := List Item
  step items request := ⟨(naiveExecute Item items request).2.1,
    (naiveExecute Item items request).2.2⟩

def naiveWork (Item : Type) : Charge (naive Item) :=
  fun items request => (naiveExecute Item items request).1

def naiveRepresentation (Item : Type) : Hom (naive Item) (logical Item) where
  map items := items
  step items request := by
    change List Item at items
    cases request with
    | enqueue item =>
        change (⟨(), (appendCount Item items item).2⟩ : Σ _ : Unit, List Item) =
          ⟨(), items ++ [item]⟩
        rw [appendCount_exact (Item := Item)]
    | dequeue => cases items <;> rfl

theorem naive_enqueues_work (items initial : List Item) :
    (advance (naive Item) (enqueueClient Item) (naiveWork Item) (items.length + 1)
      (base := ()) ⟨(), items, initial⟩).1 =
      items.length * (2 * initial.length + items.length + 1) := by
  induction items generalizing initial with
  | nil => change 0 = 0 * (2 * initial.length + 0 + 1); simp
  | cons item rest ih =>
      change 1 + (appendCount Item initial item).1 +
        (advance (naive Item) (enqueueClient Item) (naiveWork Item) (rest.length + 1)
          (base := ()) ⟨(), rest, (appendCount Item initial item).2⟩).1 = _
      rw [appendCount_exact, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      nlinarith

/-- Starting empty, eager append is triangular in cell pairs; rear-consing
is linear. Both are the same enqueue client under exact provider morphisms. -/
theorem enqueue_cost_separation (items : List Item) :
    (advance (naive Item) (enqueueClient Item) (naiveWork Item) (items.length + 1)
      (base := ()) ⟨(), items, []⟩).1 = items.length * (items.length + 1) ∧
    (advance (provider Item) (enqueueClient Item) (work Item) (items.length + 1)
      (base := ()) ⟨(), items, ⟨[], []⟩⟩).1 = 2 * items.length := by
  constructor
  · simpa using naive_enqueues_work items []
  · rw [enqueues_exact]

theorem naive_enqueue_triangular (items : List Item) :
    (advance (naive Item) (enqueueClient Item) (naiveWork Item) (items.length + 1)
      (base := ()) ⟨(), items, []⟩).1 = 2 * SequenceCost.triangular items.length := by
  rw [(enqueue_cost_separation items).1, SequenceCost.triangular_closed]

theorem rear_dequeue_work (rear : List Item) (nonempty : rear ≠ []) :
    work Item (base := ()) (index := ()) ⟨[], rear⟩ .dequeue = 2 + 2 * rear.length := by
  simp only [work, execute, reverseCount_exact, List.append_nil]
  cases reversed : rear.reverse with
  | nil => exact False.elim (nonempty (List.reverse_eq_nil_iff.mp reversed))
  | cons item rest => rfl

/-- Each branch is deliberately given the same immutable residual. This is a
different execution from repeatedly resuming the successor returned by a pull. -/
def forkedPulls (queue : Queue Item) : Nat → Nat × List (Option Item)
  | 0 => (0, [])
  | branches + 1 =>
      let pulled := execute Item queue .dequeue
      let rest := forkedPulls queue branches
      (pulled.1 + rest.1, pulled.2.1 :: rest.2)

theorem forked_reversals_repaid (rear : List Item) (nonempty : rear ≠ []) (branches : Nat) :
    (forkedPulls (⟨[], rear⟩ : Queue Item) branches).1 =
      branches * (2 + 2 * rear.length) := by
  induction branches with
  | zero => simp [forkedPulls]
  | succ branches ih =>
      change work Item (base := ()) (index := ()) ⟨[], rear⟩ .dequeue +
        (forkedPulls (⟨[], rear⟩ : Queue Item) branches).1 = _
      rw [rear_dequeue_work rear nonempty, ih]
      simp [Nat.add_mul, Nat.add_comm]

/-- Even two branches can exceed the bound obtained by counting the common
initial potential only once. No potential is duplicated by the sequential law. -/
theorem duplicated_credit_is_unsound (rear : List Item) (large : 2 < rear.length) :
    4 * 2 + 2 * rear.length < (forkedPulls (⟨[], rear⟩ : Queue Item) 2).1 := by
  have nonempty : rear ≠ [] := by intro eq; simp [eq] at large
  rw [forked_reversals_repaid rear nonempty]
  omega

namespace Controls

abbrev Answers := fun (_ : Unit) (_ : Unit) => List (Option Nat)

def answerClient : Client (P := protocol Nat) (Return := Answers) :=
  CoalgebraicPlans.retainedPlanRealizer

def twoDequeues : (protocol Nat).Free Answers () () :=
  Free.node (protocol Nat) .dequeue fun first =>
    Free.node (protocol Nat) .dequeue fun second =>
      Free.pure (protocol Nat) [first, second]

def threeDequeues : (protocol Nat).Free Answers () () :=
  Free.node (protocol Nat) .dequeue fun first =>
    Free.node (protocol Nat) .dequeue fun second =>
      Free.node (protocol Nat) .dequeue fun third =>
        Free.pure (protocol Nat) [first, second, third]

theorem ordered_duplicates_then_empty :
    advance (provider Nat) answerClient (work Nat) 4
      ⟨(), threeDequeues, ⟨[], [7, 7]⟩⟩ =
    (9, .done ⟨(), [some 7, some 7, none], ⟨[], []⟩⟩) := rfl

theorem suspension_keeps_reversed_residual :
    (advance (provider Nat) answerClient (work Nat) 1
      ⟨(), twoDequeues, ⟨[], [1, 2, 3, 4]⟩⟩).1 = 10 ∧
    (match (advance (provider Nat) answerClient (work Nat) 1
      ⟨(), twoDequeues, ⟨[], [1, 2, 3, 4]⟩⟩).2 with
      | .paused packet => packet.2.2
      | .done result => result.2.2) = ⟨[3, 2, 1], []⟩ := ⟨rfl, rfl⟩

theorem actual_resume_reverses_only_once :
    resume (provider Nat) answerClient (work Nat) 2
      (advance (provider Nat) answerClient (work Nat) 1
        ⟨(), twoDequeues, ⟨[], [1, 2, 3, 4]⟩⟩) =
    (12, .done ⟨(), [some 4, some 3], ⟨[2, 1], []⟩⟩) := rfl

theorem fork_repeats_reversal_and_answer :
    forkedPulls (⟨[], [1, 2, 3, 4]⟩ : Queue Nat) 2 = (20, [some 4, some 4]) ∧
    4 * 2 + 2 * ([1, 2, 3, 4] : List Nat).length < 20 := by decide

theorem four_enqueues_cost_eight_or_twenty :
    (advance (provider Nat) (enqueueClient Nat) (work Nat) 5
      (base := ()) ⟨(), [1, 1, 2, 3], ⟨[], []⟩⟩).1 = 8 ∧
    (advance (naive Nat) (enqueueClient Nat) (naiveWork Nat) 5
      (base := ()) ⟨(), [1, 1, 2, 3], []⟩).1 = 20 := ⟨rfl, rfl⟩

end Controls

end Mettapedia.Machines.Cursor.QueueCost
