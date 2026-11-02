import Mathlib.Computability.Partrec

/-!
# Computable operations on lists with computable arguments

Mathlib proves list folds and maps primitive recursive when the function folded or mapped is. These are the same
operations when that function is only computable: a fold is an iteration over the list's length of a computable step
(`Computable.list_foldl'`), and a map, a right fold, a concatenating map, a filter and the tests `any` and `all` are
folds (`Computable.list_map'`, `Computable.list_foldr'`, `Computable.list_flatMap'`, `Computable.list_filter'`,
`Computable.list_any'`, `Computable.list_all'`).
-/

set_option autoImplicit false

namespace Computable

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

/-- Iterating a computable step a computable number of times is computable. -/
theorem iterate' {count : α → ℕ} {start : α → σ} {step : α → σ → σ} (hCount : Computable count)
    (hStart : Computable start) (hStep : Computable₂ step) :
    Computable fun a => (step a)^[count a] (start a) := by
  have recursion := Computable.nat_rec (f := count) (g := start) (h := fun a pair => step a pair.2) hCount hStart
    (hStep.comp Computable.fst (Computable.snd.comp Computable.snd))
  refine recursion.of_eq fun a => ?_
  induction count a with
  | zero => rfl
  | succ n recurse => rw [Function.iterate_succ_apply', ← recurse]

/-- One step of a left fold: the next member folded in, the rest left. -/
def foldStep (combine : σ → β → σ) (state : σ × List β) : σ × List β :=
  match state.2 with
  | [] => state
  | member :: rest => (combine state.1 member, rest)

omit [Primcodable β] [Primcodable σ] in
theorem iterate_foldStep (combine : σ → β → σ) :
    ∀ (members : List β) (accumulated : σ),
      (foldStep combine)^[members.length] (accumulated, members) = (members.foldl combine accumulated, [])
  | [], _ => rfl
  | member :: rest, accumulated => by
      rw [List.length_cons, Function.iterate_succ_apply]
      exact iterate_foldStep combine rest (combine accumulated member)

/-- **A left fold with a computable step is computable.** -/
theorem list_foldl' {members : α → List β} {start : α → σ} {combine : α → σ → β → σ}
    (hMembers : Computable members) (hStart : Computable start)
    (hCombine : Computable fun input : α × σ × β => combine input.1 input.2.1 input.2.2) :
    Computable fun a => (members a).foldl (combine a) (start a) := by
  have stepped : Computable₂ fun (a : α) (state : σ × List β) => foldStep (combine a) state := by
    have folded : Computable fun input : (α × σ × List β) × β =>
        ((combine input.1.1 input.1.2.1 input.2, input.1.2.2.tail) : σ × List β) :=
      Computable.pair (Computable.comp (f := fun triple : α × σ × β => combine triple.1 triple.2.1 triple.2.2)
          (g := fun input : (α × σ × List β) × β => (input.1.1, input.1.2.1, input.2)) hCombine
          (Computable.pair (Computable.fst.comp Computable.fst) (Computable.pair
            (Computable.fst.comp (Computable.snd.comp Computable.fst)) Computable.snd)))
        (Primrec.list_tail.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    have cased := Computable.option_casesOn (o := fun input : α × σ × List β => input.2.2.head?)
      (f := fun input : α × σ × List β => input.2)
      (g := fun (input : α × σ × List β) (member : β) =>
        ((combine input.1 input.2.1 member, input.2.2.tail) : σ × List β))
      (Primrec.list_head?.to_comp.comp (Computable.snd.comp Computable.snd)) Computable.snd folded
    refine cased.of_eq fun input => ?_
    rcases input with ⟨a, accumulated, _ | ⟨member, rest⟩⟩ <;> rfl
  have iterated := iterate' (count := fun a => (members a).length) (start := fun a => (start a, members a))
    (step := fun a state => foldStep (combine a) state) (Primrec.list_length.to_comp.comp hMembers)
    (Computable.pair hStart hMembers) stepped
  exact (Computable.fst.comp iterated).of_eq fun a => by rw [iterate_foldStep]

/-- **A map with a computable function is computable.** -/
theorem list_map' {members : α → List β} {image : α → β → σ} (hMembers : Computable members)
    (hImage : Computable₂ image) : Computable fun a => (members a).map (image a) := by
  have folded := list_foldl' (members := members) (start := fun _ => ([] : List σ))
    (combine := fun a accumulated member => accumulated ++ [image a member]) hMembers (Computable.const [])
    ((Primrec.list_concat.to_comp).comp (Computable.fst.comp Computable.snd)
      (hImage.comp Computable.fst (Computable.snd.comp Computable.snd)))
  refine folded.of_eq fun a => ?_
  have appended : ∀ (rest : List β) (accumulated : List σ),
      rest.foldl (fun accumulated member => accumulated ++ [image a member]) accumulated =
        accumulated ++ rest.map (image a) := by
    intro rest
    induction rest with
    | nil => intro accumulated; simp
    | cons member rest recurse => intro accumulated; simp [recurse]
  simpa using appended (members a) []

/-- **A right fold with a computable step is computable.** -/
theorem list_foldr' {members : α → List β} {start : α → σ} {combine : α → β → σ → σ}
    (hMembers : Computable members) (hStart : Computable start)
    (hCombine : Computable fun input : α × β × σ => combine input.1 input.2.1 input.2.2) :
    Computable fun a => (members a).foldr (combine a) (start a) := by
  have folded := list_foldl' (members := fun a => (members a).reverse) (start := start)
    (combine := fun a accumulated member => combine a member accumulated)
    (Primrec.list_reverse.to_comp.comp hMembers) hStart
    (Computable.comp (f := fun input : α × β × σ => combine input.1 input.2.1 input.2.2)
      (g := fun input : α × σ × β => (input.1, input.2.2, input.2.1)) hCombine
      (Computable.pair Computable.fst (Computable.pair (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.snd))))
  exact folded.of_eq fun a => by rw [List.foldl_reverse]

/-- **A concatenating map with a computable function is computable.** -/
theorem list_flatMap' {members : α → List β} {image : α → β → List σ} (hMembers : Computable members)
    (hImage : Computable₂ image) : Computable fun a => (members a).flatMap (image a) :=
  (Primrec.list_flatten.to_comp.comp (list_map' hMembers hImage)).of_eq fun a => by
    rw [List.flatMap_def]

/-- **A filter with a computable test is computable.** -/
theorem list_filter' {members : α → List β} {test : α → β → Bool} (hMembers : Computable members)
    (hTest : Computable₂ test) : Computable fun a => (members a).filter (test a) := by
  have kept := list_flatMap' (members := members) (image := fun a member => if test a member then [member] else [])
    hMembers ((Computable.cond hTest ((Primrec.list_cons.to_comp).comp Computable.snd (Computable.const []))
      (Computable.const [])).of_eq fun input => by cases hTested : test input.1 input.2 <;> simp [hTested])
  refine kept.of_eq fun a => ?_
  induction members a with
  | nil => rfl
  | cons member rest recurse =>
      rw [List.flatMap_cons, recurse, List.filter_cons]
      cases test a member <;> rfl

/-- **`any` with a computable test is computable.** -/
theorem list_any' {members : α → List β} {test : α → β → Bool} (hMembers : Computable members)
    (hTest : Computable₂ test) : Computable fun a => (members a).any (test a) := by
  have folded := list_foldr' (members := members) (start := fun _ => false)
    (combine := fun a member accumulated => test a member || accumulated) hMembers (Computable.const false)
    ((Primrec.or.to_comp).comp (hTest.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))
  refine folded.of_eq fun a => ?_
  induction members a with
  | nil => rfl
  | cons member rest recurse => rw [List.foldr_cons, recurse, List.any_cons]

/-- **`all` with a computable test is computable.** -/
theorem list_all' {members : α → List β} {test : α → β → Bool} (hMembers : Computable members)
    (hTest : Computable₂ test) : Computable fun a => (members a).all (test a) := by
  have folded := list_foldr' (members := members) (start := fun _ => true)
    (combine := fun a member accumulated => test a member && accumulated) hMembers (Computable.const true)
    ((Primrec.and.to_comp).comp (hTest.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))
  refine folded.of_eq fun a => ?_
  induction members a with
  | nil => rfl
  | cons member rest recurse => rw [List.foldr_cons, recurse, List.all_cons]

end Computable
