import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Bag

/-!
# The states of worlds with one program are bags of worlds

`Hosting.Alternatives.Worlds` has a list of worlds that all run one program, and a shared space that
is a list of rules. Such a state is a bag of worlds (`ofWState`): the same worlds, each with that
program, in any order; the same rows of the space, as a set.

* **`move_of_wstep`**: every step of worlds of `Hosting.Alternatives.Worlds` (a firing, a copy, a
  publication) is a move of the bag, one for one.

The bag forgets the order of the worlds and the multiplicity of the rows of the space, and it adds two
things: each world has its own rules, and two worlds can be merged.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence (System)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)
open Hosting.Alternatives.Worlds (WState WStep withSpace snapshot)

universe uO uT uH uE uOcc uA uB

/-! ## A list as a bag: one element, and the rest -/

section Lists

variable {α : Type uA} {β : Type uB}

/-- A list, mapped and read as a bag, is the image of one of its elements and the rest. -/
theorem coe_map_eq_cons (g : β → α) :
    ∀ (l : List β) (i : ℕ) (hi : i < l.length),
      ((l.map g : List α) : Multiset α) = g l[i] ::ₘ (((l.eraseIdx i).map g : List α) : Multiset α)
  | _ :: _, 0, _ => rfl
  | a :: l, i + 1, hi => by
      have inside : i < l.length := Nat.lt_of_succ_lt_succ hi
      have ih := coe_map_eq_cons g l i inside
      show g a ::ₘ ((l.map g : List α) : Multiset α) =
        g (l[i]'inside) ::ₘ (g a ::ₘ (((l.eraseIdx i).map g : List α) : Multiset α))
      rw [ih]
      exact Multiset.cons_swap _ _ _

/-- A list with one element replaced, mapped and read as a bag, is the image of the new element and
the rest. -/
theorem coe_map_set_eq_cons (g : β → α) :
    ∀ (l : List β) (i : ℕ) (_ : i < l.length) (x : β),
      (((l.set i x).map g : List α) : Multiset α) =
        g x ::ₘ (((l.eraseIdx i).map g : List α) : Multiset α)
  | _ :: _, 0, _, _ => rfl
  | a :: l, i + 1, hi, x => by
      have ih := coe_map_set_eq_cons g l i (Nat.lt_of_succ_lt_succ hi) x
      show g a ::ₘ (((l.set i x).map g : List α) : Multiset α) =
        g x ::ₘ (g a ::ₘ (((l.eraseIdx i).map g : List α) : Multiset α))
      rw [ih]
      exact Multiset.cons_swap _ _ _

end Lists

/-! ## The embedding -/

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {O : Type uOcc}

/-- **A state of worlds with one program, as a bag of worlds**: each world with that program; the rows
of the space as a set. -/
def ofWState (P : Program Tm) (w : WState Tm O) : Bag Tm O :=
  ⟨((w.worlds.map fun s => (⟨P, s⟩ : System Tm O) : List (System Tm O)) : Multiset (System Tm O)),
    {r | r ∈ w.space}⟩

variable [DecidableEq O] {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom}

/-- **Every step of worlds with one program is a move of the bag**, one for one. -/
theorem move_of_wstep (J : Joining X O) {P : Program Tm} {w w' : WState Tm O}
    (step : WStep X E P w w') : Move X J (events X O E) (ofWState P w) (ofWState P w') := by
  cases step with
  | fire ws space i hi f admitted =>
      have source : ofWState P ⟨ws, space⟩ =
          ⟨(⟨P, ws[i]⟩ : System Tm O) ::ₘ
            (((ws.eraseIdx i).map fun s => (⟨P, s⟩ : System Tm O) : List (System Tm O)) :
              Multiset (System Tm O)), {r | r ∈ space}⟩ :=
        congrArg (fun m => (⟨m, {r | r ∈ space}⟩ : Bag Tm O))
          (coe_map_eq_cons (fun s => (⟨P, s⟩ : System Tm O)) ws i hi)
      have target : ofWState P ⟨ws.set i (f.result X ws[i]), space⟩ =
          ⟨(⟨P, f.result X ws[i]⟩ : System Tm O) ::ₘ
            (((ws.eraseIdx i).map fun s => (⟨P, s⟩ : System Tm O) : List (System Tm O)) :
              Multiset (System Tm O)), {r | r ∈ space}⟩ :=
        congrArg (fun m => (⟨m, {r | r ∈ space}⟩ : Bag Tm O))
          (coe_map_set_eq_cons (fun s => (⟨P, s⟩ : System Tm O)) ws i hi _)
      rw [source, target]
      exact Move.fire (family := events X O E) _ {r | r ∈ space} ⟨P, ws[i]⟩ ⟨widen (fun _ member => member) f, admitted⟩
  | fork ws space i hi =>
      have source : ofWState P ⟨ws, space⟩ =
          ⟨(⟨P, ws[i]⟩ : System Tm O) ::ₘ
            (((ws.eraseIdx i).map fun s => (⟨P, s⟩ : System Tm O) : List (System Tm O)) :
              Multiset (System Tm O)), {r | r ∈ space}⟩ :=
        congrArg (fun m => (⟨m, {r | r ∈ space}⟩ : Bag Tm O))
          (coe_map_eq_cons (fun s => (⟨P, s⟩ : System Tm O)) ws i hi)
      have target : ofWState P ⟨ws[i] :: ws, space⟩ =
          ⟨(⟨P, ws[i]⟩ : System Tm O) ::ₘ (⟨P, ws[i]⟩ : System Tm O) ::ₘ
            (((ws.eraseIdx i).map fun s => (⟨P, s⟩ : System Tm O) : List (System Tm O)) :
              Multiset (System Tm O)), {r | r ∈ space}⟩ :=
        congrArg (fun m => (⟨(⟨P, ws[i]⟩ : System Tm O) ::ₘ m, {r | r ∈ space}⟩ : Bag Tm O))
          (coe_map_eq_cons (fun s => (⟨P, s⟩ : System Tm O)) ws i hi)
      rw [source, target]
      exact Move.fork (family := events X O E) _ {r | r ∈ space} ⟨P, ws[i]⟩
  | publish ws space i hi o present =>
      have source : ofWState P ⟨ws, space⟩ =
          ⟨(⟨P, ws[i]⟩ : System Tm O) ::ₘ
            (((ws.eraseIdx i).map fun s => (⟨P, s⟩ : System Tm O) : List (System Tm O)) :
              Multiset (System Tm O)), {r | r ∈ space}⟩ :=
        congrArg (fun m => (⟨m, {r | r ∈ space}⟩ : Bag Tm O))
          (coe_map_eq_cons (fun s => (⟨P, s⟩ : System Tm O)) ws i hi)
      have rows : {r | r ∈ snapshot ws[i] (ws[i].label o) :: space} =
          insert (snapshot ws[i] (ws[i].label o)) {r | r ∈ space} :=
        Set.ext fun _ => List.mem_cons
      have target : ofWState P ⟨ws.set i (withoutRow ws[i] o),
            snapshot ws[i] (ws[i].label o) :: space⟩ =
          ⟨(⟨P, withoutRow ws[i] o⟩ : System Tm O) ::ₘ
            (((ws.eraseIdx i).map fun s => (⟨P, s⟩ : System Tm O) : List (System Tm O)) :
              Multiset (System Tm O)), insert (snapshot ws[i] (ws[i].label o)) {r | r ∈ space}⟩ :=
        Bag.ext (coe_map_set_eq_cons (fun s => (⟨P, s⟩ : System Tm O)) ws i hi _) rows
      show Move X J (events X O E) (ofWState P ⟨ws, space⟩)
        (ofWState P ⟨ws.set i (withoutRow ws[i] o), snapshot ws[i] (ws[i].label o) :: space⟩)
      rw [source, target]
      exact Move.publish (family := events X O E) _ {r | r ∈ space} ⟨P, ws[i]⟩ o present

#print axioms coe_map_eq_cons
#print axioms coe_map_set_eq_cons
#print axioms move_of_wstep

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
