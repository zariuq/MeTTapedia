import Mettapedia.Computability.FuelRecursion
import Mettapedia.Computability.ComputableLists

/-!
# Functions computable on codes

A type with codes (`Coded`) has a code in `ℕ` for each value: numbers are their own codes, a list is coded by the
standard code of the list of its members' codes, and a pair by the pairing of its components' codes. A function is
computable on codes (`CodeComputable`) when a computable function on `ℕ` takes the code of each argument to the code
of its value. Unlike `Computable`, this asks nothing of decoding: the codes need not be onto, and a type may have more
than one value with a code, so long as the function's tracking respects it.

Functions computable on codes are closed under the identity, constants, composition and pairing, the list operations,
choices by a computable test, and the two recursions within a fuel (`fuel`, `rounds`), so a function given by such a
definition is computable on codes by following its definition.
-/

set_option autoImplicit false

namespace Mettapedia.Computability

/-- **A type whose values have codes.** -/
class Coded (α : Type*) where
  code : α → ℕ

export Coded (code)

instance : Coded ℕ := ⟨id⟩

instance : Coded Bool := ⟨fun value => cond value 1 0⟩

instance {α : Type*} [Coded α] : Coded (List α) := ⟨fun members => Encodable.encode (members.map code)⟩

instance {α β : Type*} [Coded α] [Coded β] : Coded (α × β) := ⟨fun pair => Nat.pair (code pair.1) (code pair.2)⟩

instance {α : Type*} [Coded α] : Coded (Option α) := ⟨fun option => Option.casesOn option 0 fun value => code value + 1⟩

@[simp] theorem code_none {α : Type*} [Coded α] : code (none : Option α) = 0 := rfl

@[simp] theorem code_some {α : Type*} [Coded α] (value : α) : code (some value) = code value + 1 := rfl

@[simp] theorem code_nat (value : ℕ) : code value = value := rfl

@[simp] theorem code_true : code true = 1 := rfl

@[simp] theorem code_false : code false = 0 := rfl

theorem code_list {α : Type*} [Coded α] (members : List α) :
    code members = Encodable.encode (members.map code) := rfl

@[simp] theorem list_map_code_nat (members : List ℕ) : members.map code = members := List.map_id members

theorem code_pair {α β : Type*} [Coded α] [Coded β] (pair : α × β) :
    code pair = Nat.pair (code pair.1) (code pair.2) := rfl

/-- Decoding the code of a list gives the codes of its members. -/
theorem ofNat_code_list {α : Type*} [Coded α] (members : List α) :
    Denumerable.ofNat (List ℕ) (code members) = members.map code := by
  rw [code_list, Denumerable.ofNat_encode]

/-- **A function computable on codes**: a computable function on `ℕ` takes the code of each argument to the code of
its value. -/
def CodeComputable {α β : Type*} [Coded α] [Coded β] (f : α → β) : Prop :=
  ∃ track : ℕ → ℕ, Computable track ∧ ∀ argument, track (code argument) = code (f argument)

/-- A function of two arguments computable on codes, as a function of their pair. -/
abbrev CodeComputable₂ {α β γ : Type*} [Coded α] [Coded β] [Coded γ] (f : α → β → γ) : Prop :=
  CodeComputable fun pair : α × β => f pair.1 pair.2

namespace CodeComputable

variable {α β γ δ : Type*} [Coded α] [Coded β] [Coded γ] [Coded δ]

theorem of_eq {f g : α → β} (computable : CodeComputable f) (same : ∀ argument, f argument = g argument) :
    CodeComputable g := by
  obtain ⟨track, trackComputable, tracks⟩ := computable
  exact ⟨track, trackComputable, fun argument => (tracks argument).trans (congrArg code (same argument))⟩

theorem id : CodeComputable (fun argument : α => argument) := ⟨_root_.id, Computable.id, fun _ => rfl⟩

theorem const (value : β) : CodeComputable (fun _ : α => value) :=
  ⟨fun _ => code value, Computable.const _, fun _ => rfl⟩

theorem comp {f : β → γ} {g : α → β} (hf : CodeComputable f) (hg : CodeComputable g) :
    CodeComputable fun argument => f (g argument) := by
  obtain ⟨trackF, computableF, tracksF⟩ := hf
  obtain ⟨trackG, computableG, tracksG⟩ := hg
  exact ⟨fun n => trackF (trackG n), computableF.comp computableG, fun argument => by beta_reduce; rw [tracksG, tracksF]⟩

theorem pair {f : α → β} {g : α → γ} (hf : CodeComputable f) (hg : CodeComputable g) :
    CodeComputable fun argument => (f argument, g argument) := by
  obtain ⟨trackF, computableF, tracksF⟩ := hf
  obtain ⟨trackG, computableG, tracksG⟩ := hg
  exact ⟨fun n => Nat.pair (trackF n) (trackG n), Primrec₂.natPair.to_comp.comp computableF computableG,
    fun argument => by beta_reduce; rw [tracksF, tracksG]; rfl⟩

theorem fst : CodeComputable (fun pair : α × β => pair.1) :=
  ⟨fun n => n.unpair.1, Primrec.fst.to_comp.comp Primrec.unpair.to_comp, fun pair => by simp [code_pair]⟩

theorem snd : CodeComputable (fun pair : α × β => pair.2) :=
  ⟨fun n => n.unpair.2, Primrec.snd.to_comp.comp Primrec.unpair.to_comp, fun pair => by simp [code_pair]⟩

theorem comp₂ {f : β → γ → δ} {g : α → β} {h : α → γ} (hf : CodeComputable₂ f) (hg : CodeComputable g)
    (hh : CodeComputable h) : CodeComputable fun argument => f (g argument) (h argument) :=
  hf.comp (hg.pair hh)

/-- A computable function of numbers is computable on codes. -/
theorem of_computable {f : ℕ → ℕ} (computable : Computable f) : CodeComputable f :=
  ⟨f, computable, fun _ => rfl⟩

/-- A computable function of two numbers is computable on codes. -/
theorem of_computable₂ {f : ℕ → ℕ → ℕ} (computable : Computable₂ f) : CodeComputable₂ f :=
  ⟨fun n => f n.unpair.1 n.unpair.2, computable.comp (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
    (Primrec.snd.to_comp.comp Primrec.unpair.to_comp), fun pair => by simp [code_pair]⟩

/-- A computable test of two numbers is computable on codes. -/
theorem of_computable_test₂ {test : ℕ → ℕ → Bool} (computable : Computable₂ test) : CodeComputable₂ test :=
  ⟨fun n => cond (test n.unpair.1 n.unpair.2) 1 0,
    Computable.cond (computable.comp (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
      (Primrec.snd.to_comp.comp Primrec.unpair.to_comp)) (Computable.const 1) (Computable.const 0),
    fun pair => by simp [code_pair]; rfl⟩

/-- **Choice by a test computable on codes.** -/
theorem cond {test : α → Bool} {f g : α → β} (hTest : CodeComputable test) (hf : CodeComputable f)
    (hg : CodeComputable g) : CodeComputable fun argument => cond (test argument) (f argument) (g argument) := by
  obtain ⟨trackTest, computableTest, tracksTest⟩ := hTest
  obtain ⟨trackF, computableF, tracksF⟩ := hf
  obtain ⟨trackG, computableG, tracksG⟩ := hg
  refine ⟨fun n => _root_.cond (trackTest n != 0) (trackF n) (trackG n),
    Computable.cond ((Primrec.not.to_comp).comp ((Primrec.beq.to_comp).comp computableTest (Computable.const 0)))
      computableF computableG, fun argument => ?_⟩
  beta_reduce
  rw [tracksTest]
  cases test argument <;> simp [tracksF, tracksG]

/-- **Choice by a test computable on codes**, written with `if`. -/
theorem ite {test : α → Bool} {f g : α → β} (hTest : CodeComputable test) (hf : CodeComputable f)
    (hg : CodeComputable g) : CodeComputable fun argument => if test argument then f argument else g argument :=
  (cond hTest hf hg).of_eq fun argument => by cases test argument <;> rfl

/-! ## Lists -/

private theorem decoded {f : α → List β} (hf : CodeComputable f) :
    ∃ track : ℕ → List ℕ, Computable track ∧ ∀ argument, track (code argument) = (f argument).map code := by
  obtain ⟨trackF, computableF, tracksF⟩ := hf
  exact ⟨fun n => Denumerable.ofNat (List ℕ) (trackF n), (Primrec.ofNat (List ℕ)).to_comp.comp computableF,
    fun argument => by beta_reduce; rw [tracksF, ofNat_code_list]⟩

private theorem encoded {f : α → List β} {track : ℕ → List ℕ} (computable : Computable track)
    (tracks : ∀ argument, track (code argument) = (f argument).map code) : CodeComputable f :=
  ⟨fun n => Encodable.encode (track n), Primrec.encode.to_comp.comp computable,
    fun argument => by beta_reduce; rw [tracks]; rfl⟩

/-- **A map with a function computable on codes.** -/
theorem list_map {members : α → List β} {image : α → β → γ} (hMembers : CodeComputable members)
    (hImage : CodeComputable₂ image) : CodeComputable fun argument => (members argument).map (image argument) := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  obtain ⟨trackImage, computableImage, tracksImage⟩ := hImage
  refine encoded (track := fun n => (trackMembers n).map fun member => trackImage (Nat.pair n member))
    (Computable.list_map' computableMembers (computableImage.comp (Primrec₂.natPair.to_comp.comp
      (Computable.fst) Computable.snd))) fun argument => ?_
  rw [tracksMembers, List.map_map, List.map_map]
  exact List.map_congr_left fun member _ => tracksImage (argument, member)

/-- **A left fold with a step computable on codes.** -/
theorem list_foldl {members : α → List β} {start : α → γ} {step : α → γ → β → γ}
    (hMembers : CodeComputable members) (hStart : CodeComputable start)
    (hStep : CodeComputable fun input : α × γ × β => step input.1 input.2.1 input.2.2) :
    CodeComputable fun argument => (members argument).foldl (step argument) (start argument) := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  obtain ⟨trackStart, computableStart, tracksStart⟩ := hStart
  obtain ⟨trackStep, computableStep, tracksStep⟩ := hStep
  refine ⟨fun n => (trackMembers n).foldl (fun accumulated member =>
      trackStep (Nat.pair n (Nat.pair accumulated member))) (trackStart n),
    Computable.list_foldl' computableMembers computableStart (computableStep.comp
      (Primrec₂.natPair.to_comp.comp Computable.fst (Primrec₂.natPair.to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))), fun argument => ?_⟩
  beta_reduce
  rw [tracksMembers, tracksStart]
  generalize start argument = accumulated
  induction members argument generalizing accumulated with
  | nil => rfl
  | cons member rest recurse =>
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← recurse]
      congr 1
      exact tracksStep (argument, accumulated, member)

/-- **A right fold with a step computable on codes.** -/
theorem list_foldr {members : α → List β} {start : α → γ} {step : α → β → γ → γ}
    (hMembers : CodeComputable members) (hStart : CodeComputable start)
    (hStep : CodeComputable fun input : α × β × γ => step input.1 input.2.1 input.2.2) :
    CodeComputable fun argument => (members argument).foldr (step argument) (start argument) := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  obtain ⟨trackStart, computableStart, tracksStart⟩ := hStart
  obtain ⟨trackStep, computableStep, tracksStep⟩ := hStep
  refine ⟨fun n => (trackMembers n).foldr (fun member accumulated =>
      trackStep (Nat.pair n (Nat.pair member accumulated))) (trackStart n),
    Computable.list_foldr' computableMembers computableStart (computableStep.comp
      (Primrec₂.natPair.to_comp.comp Computable.fst (Primrec₂.natPair.to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))), fun argument => ?_⟩
  beta_reduce
  rw [tracksMembers, tracksStart]
  induction members argument with
  | nil => rfl
  | cons member rest recurse =>
      rw [List.map_cons, List.foldr_cons, List.foldr_cons, recurse]
      exact tracksStep (argument, member, _)

theorem list_cons {head : α → β} {tail : α → List β} (hHead : CodeComputable head) (hTail : CodeComputable tail) :
    CodeComputable fun argument => head argument :: tail argument := by
  obtain ⟨trackHead, computableHead, tracksHead⟩ := hHead
  obtain ⟨trackTail, computableTail, tracksTail⟩ := decoded hTail
  exact encoded (track := fun n => trackHead n :: trackTail n)
    ((Primrec.list_cons.to_comp).comp computableHead computableTail)
    fun argument => by rw [tracksHead, tracksTail, List.map_cons]

theorem list_nil : CodeComputable fun _ : α => ([] : List β) := const []

theorem list_append {left right : α → List β} (hLeft : CodeComputable left) (hRight : CodeComputable right) :
    CodeComputable fun argument => left argument ++ right argument := by
  obtain ⟨trackLeft, computableLeft, tracksLeft⟩ := decoded hLeft
  obtain ⟨trackRight, computableRight, tracksRight⟩ := decoded hRight
  exact encoded (track := fun n => trackLeft n ++ trackRight n)
    ((Primrec.list_append.to_comp).comp computableLeft computableRight)
    fun argument => by rw [tracksLeft, tracksRight, List.map_append]

theorem list_length {members : α → List β} (hMembers : CodeComputable members) :
    CodeComputable fun argument => (members argument).length := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  exact ⟨fun n => (trackMembers n).length, Primrec.list_length.to_comp.comp computableMembers,
    fun argument => by beta_reduce; rw [tracksMembers, List.length_map]; rfl⟩

theorem list_take {count : α → ℕ} {members : α → List β} (hCount : CodeComputable count)
    (hMembers : CodeComputable members) : CodeComputable fun argument => (members argument).take (count argument) := by
  obtain ⟨trackCount, computableCount, tracksCount⟩ := hCount
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  exact encoded (track := fun n => (trackMembers n).take (trackCount n))
    ((Primrec.list_take.to_comp).comp computableCount computableMembers)
    fun argument => by rw [tracksMembers, tracksCount, List.map_take]; rfl

theorem list_drop {count : α → ℕ} {members : α → List β} (hCount : CodeComputable count)
    (hMembers : CodeComputable members) : CodeComputable fun argument => (members argument).drop (count argument) := by
  obtain ⟨trackCount, computableCount, tracksCount⟩ := hCount
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  exact encoded (track := fun n => (trackMembers n).drop (trackCount n))
    ((Primrec.list_drop.to_comp).comp computableCount computableMembers)
    fun argument => by rw [tracksMembers, tracksCount, List.map_drop]; rfl

theorem list_flatten {members : α → List (List β)} (hMembers : CodeComputable members) :
    CodeComputable fun argument => (members argument).flatten := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  refine encoded (track := fun n => ((trackMembers n).map (Denumerable.ofNat (List ℕ))).flatten)
    (Primrec.list_flatten.to_comp.comp (Computable.list_map' computableMembers
      ((Primrec.ofNat (List ℕ)).to_comp.comp Computable.snd))) fun argument => ?_
  rw [tracksMembers, List.map_map, List.map_flatten]
  congr 1
  exact List.map_congr_left fun member _ => ofNat_code_list member

theorem list_flatMap {members : α → List β} {image : α → β → List γ} (hMembers : CodeComputable members)
    (hImage : CodeComputable₂ image) :
    CodeComputable fun argument => (members argument).flatMap (image argument) :=
  (list_flatten (list_map hMembers hImage)).of_eq fun _ => List.flatMap_def.symm

theorem list_headI [Inhabited β] {members : α → List β} (hMembers : CodeComputable members) :
    CodeComputable fun argument => (members argument).headI := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  refine ⟨fun n => ((trackMembers n).head?).getD (code (default : β)),
    (Primrec.option_getD.to_comp).comp (Primrec.list_head?.to_comp.comp computableMembers) (Computable.const _),
    fun argument => ?_⟩
  beta_reduce
  rw [tracksMembers]
  cases members argument <;> rfl

theorem list_tail {members : α → List β} (hMembers : CodeComputable members) :
    CodeComputable fun argument => (members argument).tail := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  exact encoded (track := fun n => (trackMembers n).tail) (Primrec.list_tail.to_comp.comp computableMembers)
    fun argument => by rw [tracksMembers, List.map_tail]

theorem list_reverse {members : α → List β} (hMembers : CodeComputable members) :
    CodeComputable fun argument => (members argument).reverse := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  exact encoded (track := fun n => (trackMembers n).reverse) (Primrec.list_reverse.to_comp.comp computableMembers)
    fun argument => by rw [tracksMembers, List.map_reverse]

theorem list_range {count : α → ℕ} (hCount : CodeComputable count) :
    CodeComputable fun argument => List.range (count argument) := by
  obtain ⟨trackCount, computableCount, tracksCount⟩ := hCount
  exact encoded (track := fun n => List.range (trackCount n)) (Primrec.list_range.to_comp.comp computableCount)
    fun argument => by rw [tracksCount]; exact (List.map_id _).symm

theorem list_filter {members : α → List β} {test : α → β → Bool} (hMembers : CodeComputable members)
    (hTest : CodeComputable₂ test) : CodeComputable fun argument => (members argument).filter (test argument) := by
  have kept := list_flatMap (image := fun argument member => if test argument member then [member] else [])
    hMembers (ite hTest (list_cons snd list_nil) list_nil)
  refine kept.of_eq fun argument => ?_
  induction members argument with
  | nil => rfl
  | cons member rest recurse =>
      rw [List.flatMap_cons, recurse, List.filter_cons]
      cases test argument member <;> rfl

/-! ## Tests -/

/-- **Equality of values with distinct codes is computable on codes.** -/
theorem beq_of_injective [DecidableEq β] (injective : Function.Injective (code : β → ℕ)) :
    CodeComputable₂ fun left right : β => decide (left = right) :=
  ⟨fun n => _root_.cond (n.unpair.1 == n.unpair.2) 1 0,
    Computable.cond ((Primrec.beq.to_comp).comp (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
      (Primrec.snd.to_comp.comp Primrec.unpair.to_comp)) (Computable.const 1) (Computable.const 0),
    fun pair => by
      simp only [code_pair, Nat.unpair_pair]
      by_cases same : pair.1 = pair.2
      · simp [same]
      · have different : (code pair.1 == code pair.2) = false := by
          simpa [beq_iff_eq] using fun equal => same (injective equal)
        simp [same, different]⟩

theorem not {test : α → Bool} (hTest : CodeComputable test) : CodeComputable fun argument => !test argument :=
  (cond hTest (const false) (const true)).of_eq fun argument => by cases test argument <;> rfl

theorem and {left right : α → Bool} (hLeft : CodeComputable left) (hRight : CodeComputable right) :
    CodeComputable fun argument => left argument && right argument :=
  (cond hLeft hRight (const false)).of_eq fun argument => by cases left argument <;> rfl

theorem or {left right : α → Bool} (hLeft : CodeComputable left) (hRight : CodeComputable right) :
    CodeComputable fun argument => left argument || right argument :=
  (cond hLeft (const true) hRight).of_eq fun argument => by cases left argument <;> rfl

theorem list_any {members : α → List β} {test : α → β → Bool} (hMembers : CodeComputable members)
    (hTest : CodeComputable₂ test) : CodeComputable fun argument => (members argument).any (test argument) := by
  have folded := list_foldr (start := fun _ => false) (step := fun argument member accumulated =>
      test argument member || accumulated) hMembers (const false)
    (or (hTest.comp (fst.pair (fst.comp snd))) (snd.comp snd))
  refine folded.of_eq fun argument => ?_
  induction members argument with
  | nil => rfl
  | cons member rest recurse => rw [List.foldr_cons, recurse, List.any_cons]

theorem list_all {members : α → List β} {test : α → β → Bool} (hMembers : CodeComputable members)
    (hTest : CodeComputable₂ test) : CodeComputable fun argument => (members argument).all (test argument) := by
  have folded := list_foldr (start := fun _ => true) (step := fun argument member accumulated =>
      test argument member && accumulated) hMembers (const true)
    (and (hTest.comp (fst.pair (fst.comp snd))) (snd.comp snd))
  refine folded.of_eq fun argument => ?_
  induction members argument with
  | nil => rfl
  | cons member rest recurse => rw [List.foldr_cons, recurse, List.all_cons]

/-- Membership in a list of values with distinct codes is computable on codes. -/
theorem list_contains [DecidableEq β] (injective : Function.Injective (code : β → ℕ)) {members : α → List β}
    {element : α → β} (hMembers : CodeComputable members) (hElement : CodeComputable element) :
    CodeComputable fun argument => (members argument).contains (element argument) := by
  have found := list_any (test := fun argument member => decide (element argument = member)) hMembers
    ((beq_of_injective injective).comp ((hElement.comp fst).pair snd))
  exact found.of_eq fun argument => by rw [List.contains_eq_any_beq]; rfl

/-! ## Numbers and iteration -/

/-- The code of a value, as a number, is computable on codes. -/
theorem code' : CodeComputable fun argument : α => (code argument : ℕ) := ⟨_root_.id, Computable.id, fun _ => rfl⟩

theorem nat_add {left right : α → ℕ} (hLeft : CodeComputable left) (hRight : CodeComputable right) :
    CodeComputable fun argument => left argument + right argument :=
  (of_computable₂ Primrec.nat_add.to_comp).comp (hLeft.pair hRight)

theorem nat_sub {left right : α → ℕ} (hLeft : CodeComputable left) (hRight : CodeComputable right) :
    CodeComputable fun argument => left argument - right argument :=
  (of_computable₂ Primrec.nat_sub.to_comp).comp (hLeft.pair hRight)

theorem nat_mul {left right : α → ℕ} (hLeft : CodeComputable left) (hRight : CodeComputable right) :
    CodeComputable fun argument => left argument * right argument :=
  (of_computable₂ Primrec.nat_mul.to_comp).comp (hLeft.pair hRight)

theorem nat_lt {left right : α → ℕ} (hLeft : CodeComputable left) (hRight : CodeComputable right) :
    CodeComputable fun argument => decide (left argument < right argument) :=
  (of_computable_test₂ (Primrec.nat_lt.decide.to_comp)).comp (hLeft.pair hRight)

theorem nat_eq {left right : α → ℕ} (hLeft : CodeComputable left) (hRight : CodeComputable right) :
    CodeComputable fun argument => decide (left argument = right argument) :=
  (of_computable_test₂ (Primrec.eq.decide.to_comp)).comp (hLeft.pair hRight)

theorem list_sum {members : α → List ℕ} (hMembers : CodeComputable members) :
    CodeComputable fun argument => (members argument).sum :=
  (list_foldr (start := fun _ => 0) (step := fun _ member total => member + total) hMembers (const 0)
    (nat_add (fst.comp snd) (snd.comp snd))).of_eq fun _ => rfl

/-- **Iterating a step computable on codes a computable number of times.** -/
theorem iterate {count : α → ℕ} {start : α → β} {step : α → β → β} (hCount : CodeComputable count)
    (hStart : CodeComputable start) (hStep : CodeComputable₂ step) :
    CodeComputable fun argument => (step argument)^[count argument] (start argument) := by
  obtain ⟨trackCount, computableCount, tracksCount⟩ := hCount
  obtain ⟨trackStart, computableStart, tracksStart⟩ := hStart
  obtain ⟨trackStep, computableStep, tracksStep⟩ := hStep
  refine ⟨fun n => (fun value => trackStep (Nat.pair n value))^[trackCount n] (trackStart n),
    Computable.iterate' computableCount computableStart
      (computableStep.comp (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)), fun argument => ?_⟩
  beta_reduce
  rw [tracksCount, tracksStart, code_nat]
  generalize start argument = value
  induction count argument generalizing value with
  | zero => rfl
  | succ n recurse =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← recurse]
      congr 1
      exact tracksStep (argument, value)

theorem list_getD {members : α → List β} {position : α → ℕ} (fallback : β) (hMembers : CodeComputable members)
    (hPosition : CodeComputable position) :
    CodeComputable fun argument => (members argument).getD (position argument) fallback := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  obtain ⟨trackPosition, computablePosition, tracksPosition⟩ := hPosition
  refine ⟨fun n => (trackMembers n).getD (trackPosition n) (code fallback),
    (Primrec.list_getD _).to_comp.comp computableMembers computablePosition, fun argument => ?_⟩
  beta_reduce
  rw [tracksMembers, tracksPosition, code_nat, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases (members argument)[position argument]? <;> rfl

omit [Coded β] [Coded γ] in
theorem zipWith_eq_map_range {γ' : Type*} (combine : β → γ → γ') (fallbackLeft : β) (fallbackRight : γ) :
    ∀ (lefts : List β) (rights : List γ), List.zipWith combine lefts rights =
      (List.range (min lefts.length rights.length)).map fun index =>
        combine (lefts.getD index fallbackLeft) (rights.getD index fallbackRight)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | left :: lefts, right :: rights => by
      rw [List.zipWith_cons_cons, zipWith_eq_map_range combine fallbackLeft fallbackRight lefts rights,
        List.length_cons, List.length_cons, Nat.succ_min_succ, List.range_succ_eq_map]
      simp [Function.comp_def]

/-- **Zipping with a function computable on codes.** -/
theorem list_zipWith {lefts : α → List β} {rights : α → List γ} {combine : α → β → γ → δ}
    (fallbackLeft : β) (fallbackRight : γ) (hLefts : CodeComputable lefts) (hRights : CodeComputable rights)
    (hCombine : CodeComputable fun input : α × β × γ => combine input.1 input.2.1 input.2.2) :
    CodeComputable fun argument => List.zipWith (combine argument) (lefts argument) (rights argument) := by
  have mapped := list_map (members := fun argument => List.range (min (lefts argument).length
      (rights argument).length))
    (image := fun argument index => combine argument ((lefts argument).getD index fallbackLeft)
      ((rights argument).getD index fallbackRight))
    (list_range ((of_computable₂ (Primrec.nat_min.to_comp)).comp ((list_length hLefts).pair (list_length hRights))))
    (hCombine.comp (fst.pair ((list_getD fallbackLeft (hLefts.comp fst) snd).pair
      (list_getD fallbackRight (hRights.comp fst) snd))))
  exact mapped.of_eq fun argument => (zipWith_eq_map_range _ fallbackLeft fallbackRight _ _).symm

/-! ## Recursion within a fuel -/

/-- **Recursion within a fuel** whose base, calls and combination are computable on codes is computable on codes. -/
theorem fuel {run : ℕ → α → β} {base : α → β} {calls : ℕ → α → List α} {combine : ℕ → α → List β → β}
    (zero : ∀ argument, run 0 argument = base argument)
    (succ : ∀ k argument, run (k + 1) argument = combine k argument ((calls k argument).map (run k)))
    (hBase : CodeComputable base) (hCalls : CodeComputable₂ calls)
    (hCombine : CodeComputable fun input : ℕ × α × List β => combine input.1 input.2.1 input.2.2) :
    CodeComputable₂ run := by
  obtain ⟨trackBase, computableBase, tracksBase⟩ := hBase
  obtain ⟨trackCalls, computableCalls, tracksCalls⟩ := decoded hCalls
  obtain ⟨trackCombine, computableCombine, tracksCombine⟩ := hCombine
  let codeRun := FuelRecursion.run trackBase (fun k n => trackCalls (Nat.pair k n))
    (fun k n values => trackCombine (Nat.pair k (Nat.pair n (Encodable.encode values))))
  have runs : ∀ k argument, codeRun k (code argument) = code (run k argument) := by
    intro k
    induction k with
    | zero => intro argument; rw [zero]; exact tracksBase argument
    | succ k recurse =>
        intro argument
        have callsTracked := tracksCalls (k, argument)
        simp only [code_pair, code_nat] at callsTracked
        simp only [codeRun, FuelRecursion.run_succ] at recurse ⊢
        rw [callsTracked, List.map_map]
        rw [show (List.map (FuelRecursion.run trackBase (fun k n => trackCalls (Nat.pair k n))
            (fun k n values => trackCombine (Nat.pair k (Nat.pair n (Encodable.encode values)))) k ∘ code)
            (calls k argument)) = (calls k argument).map (code ∘ run k) from
          List.map_congr_left fun call _ => recurse call]
        have combined := tracksCombine (k, argument, (calls k argument).map (run k))
        simp only [code_pair, code_nat, code_list, List.map_map] at combined
        rw [combined, succ]
  refine ⟨fun n => codeRun n.unpair.1 n.unpair.2, ?_, fun pair => by simp [code_pair, runs]⟩
  have runComputable := FuelRecursion.run_computable (base := trackBase)
    (calls := fun k n => trackCalls (Nat.pair k n))
    (combine := fun k n values => trackCombine (Nat.pair k (Nat.pair n (Encodable.encode values)))) computableBase
    (computableCalls.comp (Primrec₂.natPair.to_comp))
    (computableCombine.comp (Primrec₂.natPair.to_comp.comp Computable.fst (Primrec₂.natPair.to_comp.comp
      (Computable.fst.comp Computable.snd) (Primrec.encode.to_comp.comp (Computable.snd.comp Computable.snd)))))
  exact runComputable.comp (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
    (Primrec.snd.to_comp.comp Primrec.unpair.to_comp)

/-! ## Options -/

theorem option_some {value : α → β} (hValue : CodeComputable value) :
    CodeComputable fun argument => some (value argument) := by
  obtain ⟨track, computable, tracks⟩ := hValue
  exact ⟨fun n => track n + 1, Primrec.succ.to_comp.comp computable, fun argument => by
    beta_reduce; rw [tracks]; rfl⟩

theorem option_none : CodeComputable fun _ : α => (none : Option β) := const none

/-- **Cases on an option computable on codes.** -/
theorem option_casesOn {option : α → Option β} {onNone : α → γ} {onSome : α → β → γ}
    (hOption : CodeComputable option) (hNone : CodeComputable onNone) (hSome : CodeComputable₂ onSome) :
    CodeComputable fun argument => Option.casesOn (motive := fun _ => γ) (option argument) (onNone argument)
      (onSome argument) := by
  obtain ⟨trackOption, computableOption, tracksOption⟩ := hOption
  obtain ⟨trackNone, computableNone, tracksNone⟩ := hNone
  obtain ⟨trackSome, computableSome, tracksSome⟩ := hSome
  refine ⟨fun n => _root_.cond (trackOption n == 0) (trackNone n) (trackSome (Nat.pair n (trackOption n - 1))),
    Computable.cond ((Primrec.beq.to_comp).comp computableOption (Computable.const 0)) computableNone
      (computableSome.comp (Primrec₂.natPair.to_comp.comp Computable.id
        (Primrec.nat_sub.to_comp.comp computableOption (Computable.const 1)))), fun argument => ?_⟩
  beta_reduce
  rw [tracksOption]
  cases option argument with
  | none => simp [tracksNone]
  | some value =>
      simp only [code_some, Nat.add_sub_cancel]
      have positive : (code value + 1 == 0) = false := by simp
      rw [positive]
      exact tracksSome (argument, value)

theorem option_getD {option : α → Option β} {fallback : α → β} (hOption : CodeComputable option)
    (hFallback : CodeComputable fallback) :
    CodeComputable fun argument => (option argument).getD (fallback argument) :=
  (option_casesOn hOption hFallback snd).of_eq fun argument => by cases option argument <;> rfl

theorem option_map {option : α → Option β} {image : α → β → γ} (hOption : CodeComputable option)
    (hImage : CodeComputable₂ image) :
    CodeComputable fun argument => (option argument).map (image argument) :=
  (option_casesOn hOption option_none (option_some hImage)).of_eq fun argument => by cases option argument <;> rfl

theorem option_isSome {option : α → Option β} (hOption : CodeComputable option) :
    CodeComputable fun argument => (option argument).isSome :=
  (option_casesOn hOption (const false) (const true)).of_eq fun argument => by cases option argument <;> rfl

theorem list_head? {members : α → List β} (hMembers : CodeComputable members) :
    CodeComputable fun argument => (members argument).head? := by
  obtain ⟨trackMembers, computableMembers, tracksMembers⟩ := decoded hMembers
  refine ⟨fun n => Option.casesOn (motive := fun _ => ℕ) (trackMembers n).head? 0 fun first => first + 1,
    Computable.option_casesOn (Primrec.list_head?.to_comp.comp computableMembers) (Computable.const 0)
      (Primrec.succ.to_comp.comp Computable.snd), fun argument => ?_⟩
  beta_reduce
  rw [tracksMembers]
  cases members argument <;> rfl

theorem list_filterMap {members : α → List β} {image : α → β → Option γ} (hMembers : CodeComputable members)
    (hImage : CodeComputable₂ image) :
    CodeComputable fun argument => (members argument).filterMap (image argument) := by
  have listed : CodeComputable₂ fun argument member => (image argument member).toList :=
    (option_casesOn (option := fun input : α × β => image input.1 input.2) (onNone := fun _ => ([] : List γ))
      (onSome := fun _ value => [value]) hImage list_nil (list_cons snd list_nil)).of_eq fun input => by
      beta_reduce
      cases image input.1 input.2 <;> rfl
  have flattened := list_flatMap (image := fun argument member => (image argument member).toList) hMembers listed
  refine flattened.of_eq fun argument => ?_
  induction members argument with
  | nil => rfl
  | cons member rest recurse =>
      rw [List.flatMap_cons, recurse, List.filterMap_cons]
      cases image argument member <;> rfl

theorem list_find? {members : α → List β} {test : α → β → Bool} (hMembers : CodeComputable members)
    (hTest : CodeComputable₂ test) : CodeComputable fun argument => (members argument).find? (test argument) :=
  (list_head? (list_filter hMembers hTest)).of_eq fun _ => List.head?_filter ..

theorem list_findSome? {members : α → List β} {image : α → β → Option γ} (hMembers : CodeComputable members)
    (hImage : CodeComputable₂ image) :
    CodeComputable fun argument => (members argument).findSome? (image argument) :=
  (list_head? (list_filterMap hMembers hImage)).of_eq fun _ => List.head?_filterMap ..

/-! ## Recursion within a fuel, in rounds -/

/-- **The rest of a dialogue** within the fuel `k + 1`, on values: with `r` rounds left and the answers of the rounds
so far, each round asking for the values `value` of the arguments `ask` computes from the answers, and `finish` giving
the value at the end. -/
def conversation (ask : ℕ → α → List (List β) → List α) (finish : ℕ → α → List (List β) → β) (value : α → β)
    (k : ℕ) (argument : α) : ℕ → List (List β) → β
  | 0, answers => finish k argument answers
  | r + 1, answers => conversation ask finish value k argument r (answers ++ [(ask k argument answers).map value])

/-- The code of a list of rounds of answers, from the codes of the answers. -/
def answersCode (rounds : List (List ℕ)) : ℕ := Encodable.encode (rounds.map Encodable.encode)

theorem answersCode_code (answers : List (List β)) : answersCode (answers.map (List.map code)) = code answers := by
  simp only [answersCode, code_list, List.map_map]
  rfl

theorem answersCode_primrec : Primrec answersCode :=
  Primrec.encode.comp (Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd).to₂)

/-- The questions of a dialogue, on codes. -/
def askCode (trackAsk : ℕ → ℕ) (k n : ℕ) (rounds : List (List ℕ)) : List ℕ :=
  Denumerable.ofNat (List ℕ) (trackAsk (Nat.pair k (Nat.pair n (answersCode rounds))))

/-- The finish of a dialogue, on codes. -/
def finishCode (trackFinish : ℕ → ℕ) (k n : ℕ) (rounds : List (List ℕ)) : ℕ :=
  trackFinish (Nat.pair k (Nat.pair n (answersCode rounds)))

/-- **Recursion within a fuel, in rounds,** whose base, number of rounds, questions and finish are computable on codes
is computable on codes. -/
theorem rounds {run : ℕ → α → β} {base : α → β} {count : ℕ → α → ℕ} {ask : ℕ → α → List (List β) → List α}
    {finish : ℕ → α → List (List β) → β}
    (zero : ∀ argument, run 0 argument = base argument)
    (succ : ∀ k argument, run (k + 1) argument =
      conversation ask finish (run k) k argument (count k argument) [])
    (hBase : CodeComputable base) (hCount : CodeComputable₂ count)
    (hAsk : CodeComputable fun input : ℕ × α × List (List β) => ask input.1 input.2.1 input.2.2)
    (hFinish : CodeComputable fun input : ℕ × α × List (List β) => finish input.1 input.2.1 input.2.2) :
    CodeComputable₂ run := by
  obtain ⟨trackBase, computableBase, tracksBase⟩ := hBase
  obtain ⟨trackCount, computableCount, tracksCount⟩ := hCount
  obtain ⟨trackAsk, computableAsk, tracksAsk⟩ := hAsk
  obtain ⟨trackFinish, computableFinish, tracksFinish⟩ := hFinish
  have talks : ∀ k argument, FuelRecursion.Rounds.talk trackBase (fun k n => trackCount (Nat.pair k n))
      (askCode trackAsk) (finishCode trackFinish) k (code argument) = code (run k argument) := by
    intro k
    induction k with
    | zero => intro argument; rw [zero]; exact tracksBase argument
    | succ k recurse =>
        intro argument
        rw [succ, FuelRecursion.Rounds.talk_succ]
        have counted : trackCount (Nat.pair k (code argument)) = count k argument := tracksCount (k, argument)
        rw [counted]
        suffices conversing : ∀ (r : ℕ) (answers : List (List β)),
            FuelRecursion.Rounds.converse (askCode trackAsk) (finishCode trackFinish)
              (FuelRecursion.Rounds.talk trackBase (fun k n => trackCount (Nat.pair k n)) (askCode trackAsk)
                (finishCode trackFinish) k) k (code argument) r (answers.map (List.map code)) =
              code (conversation ask finish (run k) k argument r answers) from conversing _ []
        intro r
        induction r with
        | zero =>
            intro answers
            simp only [FuelRecursion.Rounds.converse, conversation, finishCode, answersCode_code]
            exact tracksFinish (k, argument, answers)
        | succ r recurseRounds =>
            intro answers
            simp only [FuelRecursion.Rounds.converse, conversation]
            have asked : askCode trackAsk k (code argument) (answers.map (List.map code)) =
                (ask k argument answers).map code := by
              simp only [askCode, answersCode_code]
              have tracked : trackAsk (Nat.pair k (Nat.pair (code argument) (code answers))) =
                  code (ask k argument answers) := tracksAsk (k, argument, answers)
              rw [tracked, ofNat_code_list]
            rw [asked, List.map_map]
            have values : (ask k argument answers).map (FuelRecursion.Rounds.talk trackBase
                (fun k n => trackCount (Nat.pair k n)) (askCode trackAsk) (finishCode trackFinish) k ∘ code) =
                ((ask k argument answers).map (run k)).map code := by
              rw [List.map_map]
              exact List.map_congr_left fun question _ => recurse question
            rw [values, show answers.map (List.map code) ++ [((ask k argument answers).map (run k)).map code] =
              (answers ++ [(ask k argument answers).map (run k)]).map (List.map code) by simp]
            exact recurseRounds _
  refine ⟨fun n => FuelRecursion.Rounds.talk trackBase (fun k n => trackCount (Nat.pair k n)) (askCode trackAsk)
      (finishCode trackFinish) n.unpair.1 n.unpair.2, ?_, fun pair => by simp [code_pair, talks]⟩
  have talkComputable := FuelRecursion.Rounds.talk_computable (base := trackBase)
    (rounds := fun k n => trackCount (Nat.pair k n)) (ask := askCode trackAsk) (finish := finishCode trackFinish)
    computableBase (computableCount.comp Primrec₂.natPair.to_comp)
    ((Primrec.ofNat (List ℕ)).to_comp.comp (computableAsk.comp (Primrec₂.natPair.to_comp.comp Computable.fst
      (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd)
        (answersCode_primrec.to_comp.comp (Computable.snd.comp Computable.snd))))))
    (computableFinish.comp (Primrec₂.natPair.to_comp.comp Computable.fst
      (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd)
        (answersCode_primrec.to_comp.comp (Computable.snd.comp Computable.snd)))))
  exact talkComputable.comp (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
    (Primrec.snd.to_comp.comp Primrec.unpair.to_comp)

end CodeComputable

end Mettapedia.Computability
