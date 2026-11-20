import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteNested

/-!
# Renaming into the variable convention across parallel parts

`FiniteHosting` hosts the manuscript's calculus on the single-firing step for processes whose parallel parts
are hosted and share no variable (`HostedProcess`): the variable convention across parts is a hypothesis.
Here it is established by alpha-equivalence, in the manuscript's own sense (`Corrected.Alpha`, the renaming
rule closed under equivalence and contexts).

## The renaming

Each parallel part is renamed by the canonical renaming of `CorrectedAlpha` (`canon`), with names that also
carry the part's position (`partName`): the bound variables of the `i`-th part become fresh names
`partName avoid i depth position`, distinct for distinct parts and outside every variable of the process.
`renameApart P` applies it along the binary parallel structure of `P`.

## What is shown

* `canon_of_binders_nil`: the canonical renaming changes nothing that binds nothing; so a hosted input's
  canonical form renames only its pattern's frame (`canon_hosted_input`), and stays hosted (`hosted_canon`).
* `parts_renameApart`: the `i`-th part of `renameApart P` is the canonical renaming of the `i`-th part of `P`
  with the names of position `i`.
* `alpha_renameApart`: renaming apart is a chain of instances of the manuscript's renaming rule, for every
  tame process.
* **`renaming_into_the_convention`**: every tame process whose parts are hosted is alpha-equivalent, part by
  part, to a hosted process in the exact form `manuscript_calculus_by_a_finite_program` assumes.
* **`apart_of_renameApart`**: for every tame process, hosted or not, every two input parts of the renamed
  process satisfy the variable convention of the corrected COMM (`Corrected.Apart`), in both orders.

Tameness is needed: outside it the closed form cannot tell a code from a bound occurrence, and renaming
reaches less than the closed form (`Corrected.alphaEq_not_alpha_with_code`; see `FiniteConventionControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero)
open MeTTaOperationsComm (psubst pvars firstOrder)
open MeTTaCalculus.Corrected (binders binders_apply bindersFor_cons3 bindersFor_short bindersList_eq_flatMap Apart
  tame tameList tame_pFor canon canonList canonFor canonList_eq_map canon_pFor levelRename Alpha alpha_canon
  frame frame_subset frame_of_guardFree rename rename_id pvars_rename binders_rename pvars_canon binders_canon
  freshName freshName_not_mem freshName_injective pvars_pFor pvars_par)
open FiniteProgram (parts Hosted HostedProcess IsPar parts_par parts_of_not_par pFor_inj binders_of_ground
  eq_of_mem_parts_of_not_par pvars_of_mem_parts)

/-! ## The canonical renaming of what binds nothing -/

theorem levelRename_nil (n : ℕ → ℕ → String) (D : ℕ) : levelRename n D [] = fun v => v := by
  funext v
  simp [levelRename]

theorem frame_eq_nil {t : Pattern} (ground : pvars t = []) : frame t = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun y member => by
    simpa [ground] using frame_subset t y member

/-- **The canonical renaming changes nothing that binds nothing.** -/
theorem canon_of_binders_nil (n : ℕ → ℕ → String) (p : Pattern) :
    ∀ D, binders p = [] → canon n D p = p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ D, binders q = [] → canon n D q = q) with
  | bvar k => intro _ _; rfl
  | fvar x => intro _ _; rfl
  | apply c args ih =>
      intro D none
      rw [binders_apply] at none
      simp only [canon]
      congr 1
      split_ifs at none ⊢ with isFor
      · match args, ih, none with
        | [], _, _ => simp [canonFor]
        | [p], ih, none =>
            rw [bindersFor_short _ (by simp)] at none
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at none
            simp only [canonFor, ih p (by simp) D none]
        | [p, q], ih, none =>
            rw [bindersFor_short _ (by simp)] at none
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_eq_nil_iff] at none
            simp only [canonFor, ih p (by simp) D none.1, ih q (by simp) D none.2]
        | t :: x :: k :: rest, ih, none =>
            rw [bindersFor_cons3] at none
            simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at none
            obtain ⟨⟨⟨noT, noX⟩, noK⟩, noRest⟩ := none
            have restSame : canonList n D rest = rest := by
              rw [canonList_eq_map]
              conv_rhs => rw [← List.map_id rest]
              exact List.map_congr_left fun q member => ih q (by simp [member]) D (noRest q member)
            simp only [canonFor, frame_eq_nil noT, levelRename_nil, rename_id, ih x (by simp) D noX,
              ih k (by simp) (D + 1) noK, restSame]
      · rw [canonList_eq_map]
        conv_rhs => rw [← List.map_id args]
        exact List.map_congr_left fun q member => ih q member D (List.flatMap_eq_nil_iff.mp none q member)
  | lambda nm b ih => intro _ _; rfl
  | multiLambda k nms b ih => intro _ _; rfl
  | subst b r ihb ihr => intro _ _; rfl
  | collection ct elems rest ih =>
      intro D none
      simp only [binders, bindersList_eq_flatMap, List.flatMap_eq_nil_iff] at none
      simp only [canon, canonList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id elems]
      exact List.map_congr_left fun q member => ih q member D (none q member)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member D none
      rcases List.mem_cons.mp member with rfl | later
      · exact head D none
      · exact tail q later D none

theorem canon_pZero (n : ℕ → ℕ → String) (D : ℕ) : canon n D pZero = pZero :=
  canon_of_binders_nil n pZero D (by decide +kernel)

/-- The canonical renaming keeps the shape of a binary parallel composition. -/
theorem isPar_of_canon {n : ℕ → ℕ → String} {D : ℕ} {p : Pattern} (isPar : IsPar (canon n D p)) : IsPar p := by
  obtain ⟨a, b, same⟩ := isPar
  cases p with
  | collection ct elems rest =>
      simp only [canon, canonList_eq_map, par, MeTTaCalculus.pPar, Pattern.collection.injEq] at same
      obtain ⟨rfl, lengths, rfl⟩ := same
      have two : elems.length = 2 := by simpa using congrArg List.length lengths
      match elems, two with
      | [a', b'], _ => exact ⟨a', b', rfl⟩
  | bvar k => simp [canon, par, MeTTaCalculus.pPar] at same
  | fvar x => simp [canon, par, MeTTaCalculus.pPar] at same
  | apply c args => simp [canon, par, MeTTaCalculus.pPar] at same
  | lambda nm b => simp [canon, par, MeTTaCalculus.pPar] at same
  | multiLambda k nms b => simp [canon, par, MeTTaCalculus.pPar] at same
  | subst b r => simp [canon, par, MeTTaCalculus.pPar] at same

/-- The canonical renaming of a process is `0` only when the process is. -/
theorem eq_pZero_of_canon {n : ℕ → ℕ → String} {D : ℕ} {p : Pattern} (zero : canon n D p = pZero) :
    p = pZero := by
  cases p with
  | apply c args =>
      simp only [canon, pZero, Pattern.apply.injEq] at zero
      obtain ⟨rfl, empty⟩ := zero
      have notFor : ¬ ("MZero" : String) = "MFor" := by decide
      simp only [notFor, if_false, canonList_eq_map, List.map_eq_nil_iff] at empty
      subst empty
      rfl
  | bvar k => simp [canon, pZero] at zero
  | fvar x => simp [canon, pZero] at zero
  | lambda nm b => simp [canon, pZero] at zero
  | multiLambda k nms b => simp [canon, pZero] at zero
  | subst b r => simp [canon, pZero] at zero
  | collection ct elems rest => simp [canon, pZero] at zero

/-! ## The canonical form of a hosted part -/

/-- Renaming keeps first-order terms first-order. -/
theorem firstOrder_rename (g : String → String) (p : Pattern) (fo : firstOrder p = true) :
    firstOrder (rename g p) = true :=
  FiniteProgram.firstOrder_psubst (fun x v found => by cases found; rfl) p fo

/-- **The canonical form of a hosted input renames only its pattern's frame.** -/
theorem canon_hosted_input (n : ℕ → ℕ → String) (D : ℕ) {t x A : Pattern} (hosted : Hosted (pFor t x A)) :
    canon n D (pFor t x A) =
      pFor (rename (levelRename n D (frame t)) t) x (rename (levelRename n D (frame t)) A) := by
  obtain ⟨groundX, -, noBinders, -⟩ := hosted.input
  rw [canon_pFor, canon_of_binders_nil n x D (binders_of_ground groundX),
    canon_of_binders_nil n A (D + 1) noBinders]

/-- **The canonical form of a hosted part is hosted.** -/
theorem hosted_canon (n : ℕ → ℕ → String) (D : ℕ) {c : Pattern} (hosted : Hosted c) : Hosted (canon n D c) := by
  rcases hosted.2 with ground | ⟨t, x, A, rfl, groundX, closed, noBinders⟩
  · rw [canon_of_binders_nil n c D (binders_of_ground ground)]
    exact hosted
  · rw [canon_hosted_input n D hosted]
    have fo := FiniteProgram.firstOrder_pFor.mp hosted.1
    refine ⟨FiniteProgram.firstOrder_pFor.mpr ⟨firstOrder_rename _ t fo.1, fo.2.1, firstOrder_rename _ A fo.2.2⟩,
      .inr ⟨_, x, _, rfl, groundX, fun y inside => ?_, ?_⟩⟩
    · rw [pvars_rename] at inside ⊢
      obtain ⟨v, inA, rfl⟩ := List.mem_map.mp inside
      exact List.mem_map_of_mem (closed v inA)
    · simp [binders_rename, noBinders]

/-- **Every variable of the canonical form of a tame hosted part is a canonical name of depth zero.** -/
theorem pvars_canon_hosted (n : ℕ → ℕ → String) {c : Pattern} (tameC : tame c = true) (hosted : Hosted c)
    {w : String} (inside : w ∈ pvars (canon n 0 c)) : ∃ j, w = n 0 j := by
  rcases hosted.2 with ground | ⟨t, x, A, rfl, groundX, closed, -⟩
  · rw [canon_of_binders_nil n c 0 (binders_of_ground ground), ground] at inside
    exact absurd inside List.not_mem_nil
  · rw [canon_hosted_input n 0 hosted, pvars_pFor, groundX] at inside
    obtain ⟨-, freeT, -, -⟩ := tame_pFor.mp tameC
    have frameIs := frame_of_guardFree t freeT
    simp only [List.append_nil, List.mem_append, pvars_rename, List.mem_map] at inside
    rcases inside with ⟨v, inT, rfl⟩ | ⟨v, inA, rfl⟩
    · exact ⟨(frame t).idxOf v, by simp [levelRename, frameIs, inT]⟩
    · exact ⟨(frame t).idxOf v, by simp [levelRename, frameIs, closed v inA]⟩

/-! ## Names for the parts -/

/-- Fresh names for the `i`-th part: one per part, depth and frame position, none in `avoid`. -/
def partName (avoid : List String) (i L j : ℕ) : String := freshName avoid (Nat.pair i (Nat.pair L j))

theorem partName_inj {avoid : List String} {i i' L L' j j' : ℕ}
    (same : partName avoid i L j = partName avoid i' L' j') : i = i' ∧ L = L' ∧ j = j' := by
  have codes := freshName_injective avoid same
  obtain ⟨rfl, inner⟩ := Nat.pair_eq_pair.mp codes
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp inner
  exact ⟨rfl, rfl, rfl⟩

theorem partName_not_mem (avoid : List String) (i L j : ℕ) : partName avoid i L j ∉ avoid :=
  freshName_not_mem avoid _

/-- **The canonical renaming of a part with the names of its position is alpha.** -/
theorem alpha_canon_part (avoid : List String) (k : ℕ) {p : Pattern} (tameP : tame p = true)
    (inside : ∀ v ∈ pvars p, v ∈ avoid) : Alpha p (canon (partName avoid k) 0 p) :=
  alpha_canon (partName avoid k)
    (fun L i L' i' same => by
      obtain ⟨-, sameL, sameI⟩ := partName_inj same
      exact ⟨sameL, sameI⟩)
    p tameP 0 (fun v occurs L i same => partName_not_mem avoid k L i (by rw [same]; exact inside v occurs))

/-! ## Renaming the parts apart -/

/-- **Renaming the parts apart.** Each parallel part, counted from `k` along the binary parallel structure, has its
bound variables renamed canonically with the names of its own position. -/
def apartFrom (avoid : List String) : ℕ → Pattern → Pattern
  | k, .collection .hashBag [a, b] none => par (apartFrom avoid k a) (apartFrom avoid (k + (parts a).length) b)
  | k, p => canon (partName avoid k) 0 p

theorem apartFrom_par (avoid : List String) (k : ℕ) (a b : Pattern) :
    apartFrom avoid k (par a b) = par (apartFrom avoid k a) (apartFrom avoid (k + (parts a).length) b) := by
  simp [par, MeTTaCalculus.pPar, apartFrom]

theorem apartFrom_of_not_par {avoid : List String} {k : ℕ} {p : Pattern} (notPar : ¬ IsPar p) :
    apartFrom avoid k p = canon (partName avoid k) 0 p := by
  unfold apartFrom
  split
  · rename_i a b
    exact absurd ⟨a, b, rfl⟩ notPar
  · rfl

theorem parts_apartFrom_of_not_par {avoid : List String} {k : ℕ} {p : Pattern} (notPar : ¬ IsPar p) :
    parts (apartFrom avoid k p) = (parts p).mapIdx fun i c => canon (partName avoid (k + i)) 0 c := by
  rw [apartFrom_of_not_par notPar, parts_of_not_par notPar,
    parts_of_not_par (fun isPar => notPar (isPar_of_canon isPar))]
  by_cases zero : p = pZero
  · subst zero
    simp [canon_pZero]
  · rw [if_neg zero, if_neg (fun same => zero (eq_pZero_of_canon same))]
    simp

/-- **The parts after renaming apart**: the `i`-th part is the canonical renaming of the `i`-th part, with the
names of position `k + i`. -/
theorem parts_apartFrom (avoid : List String) (P : Pattern) :
    ∀ k, parts (apartFrom avoid k P) = (parts P).mapIdx fun i c => canon (partName avoid (k + i)) 0 c := by
  induction P using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ k,
      parts (apartFrom avoid k q) = (parts q).mapIdx fun i c => canon (partName avoid (k + i)) 0 c) with
  | collection ct elems rest ih =>
      intro k
      by_cases isPar : IsPar (.collection ct elems rest)
      · obtain ⟨a, b, same⟩ := isPar
        simp only [par, MeTTaCalculus.pPar, Pattern.collection.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        rw [show Pattern.collection .hashBag [a, b] none = par a b from rfl, apartFrom_par, parts_par, parts_par,
          ih a (by simp) k, ih b (by simp) (k + (parts a).length), List.mapIdx_append]
        congr 2
        funext i c
        show canon (partName avoid (k + (parts a).length + i)) 0 c =
          canon (partName avoid (k + (i + (parts a).length))) 0 c
        rw [show k + (parts a).length + i = k + (i + (parts a).length) by omega]
      · exact parts_apartFrom_of_not_par isPar
  | bvar n => exact fun k => parts_apartFrom_of_not_par (by rintro ⟨a, b, same⟩; cases same)
  | fvar x => exact fun k => parts_apartFrom_of_not_par (by rintro ⟨a, b, same⟩; cases same)
  | apply f args ih => exact fun k => parts_apartFrom_of_not_par (by rintro ⟨a, b, same⟩; cases same)
  | lambda nm body ih => exact fun k => parts_apartFrom_of_not_par (by rintro ⟨a, b, same⟩; cases same)
  | multiLambda n nms body ih => exact fun k => parts_apartFrom_of_not_par (by rintro ⟨a, b, same⟩; cases same)
  | subst body repl ihb ihr => exact fun k => parts_apartFrom_of_not_par (by rintro ⟨a, b, same⟩; cases same)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member k
      rcases List.mem_cons.mp member with rfl | later
      · exact head k
      · exact tail q later k

theorem alpha_par {a a' b b' : Pattern} (left : Alpha a a') (right : Alpha b b') :
    Alpha (par a b) (par a' b') := by
  have first : Alpha (par a b) (par a' b) := by
    simpa [par, MeTTaCalculus.pPar] using Alpha.collection .hashBag [] [b] none left
  have second : Alpha (par a' b) (par a' b') := by
    simpa [par, MeTTaCalculus.pPar] using Alpha.collection .hashBag [a'] [] none right
  exact first.trans second

theorem tame_of_par {a b : Pattern} (tameP : tame (par a b) = true) : tame a = true ∧ tame b = true := by
  simpa [par, MeTTaCalculus.pPar, tame, tameList] using tameP

/-- **Renaming apart is a chain of instances of the manuscript's renaming rule**, for every tame process. -/
theorem alpha_apartFrom (avoid : List String) (P : Pattern) :
    ∀ k, tame P = true → (∀ v ∈ pvars P, v ∈ avoid) → Alpha P (apartFrom avoid k P) := by
  induction P using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ k, tame q = true →
      (∀ v ∈ pvars q, v ∈ avoid) → Alpha q (apartFrom avoid k q)) with
  | collection ct elems rest ih =>
      intro k tameP inside
      by_cases isPar : IsPar (.collection ct elems rest)
      · obtain ⟨a, b, same⟩ := isPar
        simp only [par, MeTTaCalculus.pPar, Pattern.collection.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        rw [show Pattern.collection .hashBag [a, b] none = par a b from rfl] at tameP inside ⊢
        rw [apartFrom_par]
        rw [pvars_par] at inside
        obtain ⟨tameA, tameB⟩ := tame_of_par tameP
        exact alpha_par (ih a (by simp) k tameA fun v occurs => inside v (List.mem_append_left _ occurs))
          (ih b (by simp) _ tameB fun v occurs => inside v (List.mem_append_right _ occurs))
      · rw [apartFrom_of_not_par isPar]
        exact alpha_canon_part avoid k tameP inside
  | bvar n => intro _ tameP _; simp [tame] at tameP
  | fvar x =>
      intro k tameP inside
      rw [apartFrom_of_not_par (by rintro ⟨a, b, same⟩; cases same)]
      exact alpha_canon_part avoid k tameP inside
  | apply f args ih =>
      intro k tameP inside
      rw [apartFrom_of_not_par (by rintro ⟨a, b, same⟩; cases same)]
      exact alpha_canon_part avoid k tameP inside
  | lambda nm body ih => intro _ tameP _; simp [tame] at tameP
  | multiLambda n nms body ih => intro _ tameP _; simp [tame] at tameP
  | subst body repl ihb ihr => intro _ tameP _; simp [tame] at tameP
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member k tameQ inside
      rcases List.mem_cons.mp member with rfl | later
      · exact head k tameQ inside
      · exact tail q later k tameQ inside

/-- **A part of a tame process is tame.** -/
theorem tame_of_mem_parts (p : Pattern) : ∀ c ∈ parts p, tame p = true → tame c = true := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ c ∈ parts q, tame q = true → tame c = true) with
  | collection ct elems rest ih =>
      intro c member tameP
      by_cases isPar : IsPar (.collection ct elems rest)
      · obtain ⟨a, b, same⟩ := isPar
        simp only [par, MeTTaCalculus.pPar, Pattern.collection.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        rw [show Pattern.collection .hashBag [a, b] none = par a b from rfl] at member tameP
        rw [parts_par] at member
        obtain ⟨tameA, tameB⟩ := tame_of_par tameP
        rcases List.mem_append.mp member with inA | inB
        · exact ih a (by simp) c inA tameA
        · exact ih b (by simp) c inB tameB
      · rw [eq_of_mem_parts_of_not_par isPar member]
        exact tameP
  | bvar n =>
      intro c member tameP
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact tameP
  | fvar x =>
      intro c member tameP
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact tameP
  | apply f args ih =>
      intro c member tameP
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact tameP
  | lambda nm body ih =>
      intro c member tameP
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact tameP
  | multiLambda n nms body ih =>
      intro c member tameP
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact tameP
  | subst body repl ihb ihr =>
      intro c member tameP
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact tameP
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member c inC tameQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head c inC tameQ
      · exact tail q later c inC tameQ

/-! ## Renaming a process apart -/

/-- **A process renamed apart**: its parts renamed canonically, with names outside all of its variables. -/
def renameApart (P : Pattern) : Pattern := apartFrom (pvars P) 0 P

/-- The `i`-th part of `renameApart P` is the canonical renaming of the `i`-th part of `P`. -/
theorem parts_renameApart (P : Pattern) :
    parts (renameApart P) = (parts P).mapIdx fun i c => canon (partName (pvars P) i) 0 c := by
  have shifted := parts_apartFrom (pvars P) P 0
  simp only [Nat.zero_add] at shifted
  exact shifted

theorem length_parts_renameApart (P : Pattern) : (parts (renameApart P)).length = (parts P).length := by
  rw [parts_renameApart, List.length_mapIdx]

/-- **Renaming apart is alpha**, for every tame process. -/
theorem alpha_renameApart (P : Pattern) (tameP : tame P = true) : Alpha P (renameApart P) :=
  alpha_apartFrom (pvars P) P 0 tameP fun _ occurs => occurs

theorem forall₂_mapIdx {α β : Type} {R : α → β → Prop} :
    ∀ (l : List α) (f : ℕ → α → β), (∀ i (small : i < l.length), R l[i] (f i l[i])) →
      List.Forall₂ R l (l.mapIdx f)
  | [], _, _ => List.Forall₂.nil
  | a :: l, f, each => by
      rw [List.mapIdx_cons]
      exact .cons (each 0 (by simp)) (forall₂_mapIdx l (fun i => f (i + 1)) fun i small =>
        each (i + 1) (by simp only [List.length_cons]; omega))

/-- **Renaming apart relates the parts one by one**, each by the manuscript's renaming rule. -/
theorem forall₂_alpha_renameApart (P : Pattern) (tameP : tame P = true) :
    List.Forall₂ Alpha (parts P) (parts (renameApart P)) := by
  rw [parts_renameApart]
  exact forall₂_mapIdx (parts P) _ fun i small =>
    alpha_canon_part (pvars P) i (tame_of_mem_parts P _ (List.getElem_mem small) tameP)
      fun v occurs => pvars_of_mem_parts P _ (List.getElem_mem small) v occurs

/-- **Renaming into the variable convention.** Every tame process whose parallel parts are hosted is
alpha-equivalent, by the manuscript's renaming rule, to a hosted process: its parts are hosted and no two of them
share a variable, the exact form that `manuscript_calculus_by_a_finite_program` assumes. The parts correspond one
by one, each by the renaming rule. -/
theorem renaming_into_the_convention (P : Pattern) (tameP : tame P = true)
    (hostedParts : ∀ c ∈ parts P, Hosted c) :
    Alpha P (renameApart P) ∧ HostedProcess (renameApart P) ∧
      List.Forall₂ Alpha (parts P) (parts (renameApart P)) := by
  refine ⟨alpha_renameApart P tameP, ⟨fun c member => ?_, ?_⟩, forall₂_alpha_renameApart P tameP⟩
  · rw [parts_renameApart] at member
    obtain ⟨i, small, rfl⟩ := List.mem_iff_getElem.mp member
    rw [List.getElem_mapIdx]
    exact hosted_canon _ 0 (hostedParts _ (List.getElem_mem _))
  · rw [parts_renameApart, List.pairwise_iff_getElem]
    intro i j small₁ small₂ before y inFirst inSecond
    rw [List.getElem_mapIdx] at inFirst inSecond
    rw [List.length_mapIdx] at small₁ small₂
    have tameI := tame_of_mem_parts P _ (List.getElem_mem small₁) tameP
    have tameJ := tame_of_mem_parts P _ (List.getElem_mem small₂) tameP
    obtain ⟨a, rfl⟩ := pvars_canon_hosted _ tameI (hostedParts _ (List.getElem_mem small₁)) inFirst
    obtain ⟨b, same⟩ := pvars_canon_hosted _ tameJ (hostedParts _ (List.getElem_mem small₂)) inSecond
    obtain ⟨sameIndex, -, -⟩ := partName_inj same
    omega

/-! ## The convention across parts, for every tame process -/

theorem canonFor_length (n : ℕ → ℕ → String) (D : ℕ) (ps : List Pattern) :
    (canonFor n D ps).length = ps.length := by
  match ps with
  | [] => simp [canonFor]
  | [p] => simp [canonFor]
  | [p, q] => simp [canonFor]
  | t :: x :: k :: rest => simp [canonFor, canonList_eq_map]

/-- The canonical renaming of a process is an input only when the process is one. -/
theorem input_of_canon {n : ℕ → ℕ → String} {D : ℕ} {c t x A : Pattern} (shape : canon n D c = pFor t x A) :
    ∃ t₀ x₀ A₀, c = pFor t₀ x₀ A₀ := by
  cases c with
  | apply f args =>
      simp only [canon, pFor, Pattern.apply.injEq] at shape
      obtain ⟨rfl, same⟩ := shape
      rw [if_pos rfl] at same
      have three : args.length = 3 := by simpa [canonFor_length] using congrArg List.length same
      match args, three with
      | [t₀, x₀, A₀], _ => exact ⟨t₀, x₀, A₀, rfl⟩
  | bvar k => simp [canon, pFor] at shape
  | fvar v => simp [canon, pFor] at shape
  | lambda nm b => simp [canon, pFor] at shape
  | multiLambda k nms b => simp [canon, pFor] at shape
  | subst b r => simp [canon, pFor] at shape
  | collection ct elems rest => simp [canon, pFor] at shape

/-- **The canonical input of a tame part**: its pattern's variables are the part's names of depth zero, and its
continuation binds only the part's names of positive depth. -/
theorem canon_input_facts (avoid : List String) (k : ℕ) {c t x A : Pattern} (tameC : tame c = true)
    (inside : ∀ v ∈ pvars c, v ∈ avoid) (shape : canon (partName avoid k) 0 c = pFor t x A) :
    (∀ v ∈ pvars t, ∃ a, v = partName avoid k 0 a) ∧
      ∀ v ∈ binders A, ∃ L b, 1 ≤ L ∧ v = partName avoid k L b := by
  obtain ⟨t₀, x₀, A₀, rfl⟩ := input_of_canon shape
  rw [canon_pFor] at shape
  obtain ⟨rfl, -, rfl⟩ := pFor_inj shape
  obtain ⟨-, freeT, -, tameA⟩ := tame_pFor.mp tameC
  have frameIs := frame_of_guardFree t₀ freeT
  refine ⟨fun v occurs => ?_, fun v bound => ?_⟩
  · rw [pvars_rename] at occurs
    obtain ⟨w, inT, rfl⟩ := List.mem_map.mp occurs
    exact ⟨(frame t₀).idxOf w, by simp [levelRename, frameIs, inT]⟩
  · rw [binders_rename] at bound
    obtain ⟨w, inner, rfl⟩ := List.mem_map.mp bound
    obtain ⟨L, b, deeper, rfl⟩ := binders_canon (partName avoid k) A₀ tameA 1 _ inner
    have outsideFrame : partName avoid k L b ∉ frame t₀ := fun member =>
      partName_not_mem avoid k L b
        (inside _ (MeTTaCalculus.Corrected.mem_pvars_apply_of (by simp) (frame_subset t₀ _ member)))
    exact ⟨L, b, deeper, by simp [levelRename, outsideFrame]⟩

/-- A variable of the canonical renaming of a tame part is a variable of the process or one of the part's names. -/
theorem pvars_canon_part (avoid : List String) (k : ℕ) {c : Pattern} (tameC : tame c = true)
    (inside : ∀ v ∈ pvars c, v ∈ avoid) {v : String} (occurs : v ∈ pvars (canon (partName avoid k) 0 c)) :
    v ∈ avoid ∨ ∃ L b, v = partName avoid k L b := by
  rcases pvars_canon (partName avoid k) c tameC 0 v occurs with own | ⟨L, b, -, rfl⟩
  · exact .inl (inside v own)
  · exact .inr ⟨L, b, rfl⟩

/-- A name of one part is no variable of another part. -/
theorem not_mem_other_part (avoid : List String) {i j : ℕ} (distinct : i ≠ j) {d : Pattern}
    (tameD : tame d = true) (insideD : ∀ v ∈ pvars d, v ∈ avoid) (L a : ℕ) :
    partName avoid i L a ∉ pvars (canon (partName avoid j) 0 d) := fun occurs => by
  rcases pvars_canon_part avoid j tameD insideD occurs with own | ⟨L', b, same⟩
  · exact partName_not_mem avoid i L a own
  · exact distinct (partName_inj same).1

/-- **Two canonical inputs of distinct parts satisfy the variable convention of the corrected COMM.** -/
theorem apart_of_canon_parts (avoid : List String) {i j : ℕ} (distinct : i ≠ j) {c d t x A u x' B : Pattern}
    (tameC : tame c = true) (tameD : tame d = true) (insideC : ∀ v ∈ pvars c, v ∈ avoid)
    (insideD : ∀ v ∈ pvars d, v ∈ avoid) (first : canon (partName avoid i) 0 c = pFor t x A)
    (second : canon (partName avoid j) 0 d = pFor u x' B) : Apart t A u B := by
  obtain ⟨patternC, keptC⟩ := canon_input_facts avoid i tameC insideC first
  obtain ⟨patternD, keptD⟩ := canon_input_facts avoid j tameD insideD second
  have inC : ∀ v, v ∈ pvars t ∨ v ∈ pvars A → v ∈ pvars (canon (partName avoid i) 0 c) := by
    intro v occurs
    rw [first, pvars_pFor]
    rcases occurs with inT | inA
    · exact List.mem_append_left _ (List.mem_append_left _ inT)
    · exact List.mem_append_right _ inA
  have inD : ∀ v, v ∈ pvars u ∨ v ∈ pvars B → v ∈ pvars (canon (partName avoid j) 0 d) := by
    intro v occurs
    rw [second, pvars_pFor]
    rcases occurs with inU | inB
    · exact List.mem_append_left _ (List.mem_append_left _ inU)
    · exact List.mem_append_right _ inB
  refine ⟨fun v inT inU => ?_, fun v inT inB => ?_, fun v inU inA => ?_, fun v inT bound => ?_,
    fun v inU bound => ?_⟩
  · obtain ⟨a, rfl⟩ := patternC v inT
    exact not_mem_other_part avoid distinct tameD insideD 0 a (inD _ (.inl inU))
  · obtain ⟨a, rfl⟩ := patternC v inT
    exact not_mem_other_part avoid distinct tameD insideD 0 a (inD _ (.inr inB))
  · obtain ⟨b, rfl⟩ := patternD v inU
    exact not_mem_other_part avoid (Ne.symm distinct) tameC insideC 0 b (inC _ (.inr inA))
  · obtain ⟨a, rfl⟩ := patternC v inT
    obtain ⟨L, b, deeper, same⟩ := keptC _ bound
    have depths := (partName_inj same).2.1
    omega
  · obtain ⟨a, rfl⟩ := patternD v inU
    obtain ⟨L, b, deeper, same⟩ := keptD _ bound
    have depths := (partName_inj same).2.1
    omega

/-- **The variable convention across parts, for every tame process.** After renaming apart, every two input parts
satisfy the convention of the corrected COMM (`Corrected.Apart`), in both orders. Nothing is asked of the parts
beyond tameness: free names stay, and every bound name becomes a name of its own part. -/
theorem apart_of_renameApart (P : Pattern) (tameP : tame P = true) :
    (parts (renameApart P)).Pairwise fun c d => ∀ t x A u x' B, c = pFor t x A → d = pFor u x' B →
      Apart t A u B ∧ Apart u B t A := by
  rw [parts_renameApart, List.pairwise_iff_getElem]
  intro i j small₁ small₂ before t x A u x' B first second
  rw [List.getElem_mapIdx] at first second
  rw [List.length_mapIdx] at small₁ small₂
  have tameI := tame_of_mem_parts P _ (List.getElem_mem small₁) tameP
  have tameJ := tame_of_mem_parts P _ (List.getElem_mem small₂) tameP
  have insideI : ∀ v ∈ pvars ((parts P)[i]), v ∈ pvars P := fun v occurs =>
    pvars_of_mem_parts P _ (List.getElem_mem small₁) v occurs
  have insideJ : ∀ v ∈ pvars ((parts P)[j]), v ∈ pvars P := fun v occurs =>
    pvars_of_mem_parts P _ (List.getElem_mem small₂) v occurs
  exact ⟨apart_of_canon_parts (pvars P) (by omega) tameI tameJ insideI insideJ first second,
    apart_of_canon_parts (pvars P) (by omega) tameJ tameI insideJ insideI second first⟩

#print axioms canon_of_binders_nil
#print axioms canon_pZero
#print axioms isPar_of_canon
#print axioms eq_pZero_of_canon
#print axioms canon_hosted_input
#print axioms hosted_canon
#print axioms pvars_canon_hosted
#print axioms partName_inj
#print axioms alpha_canon_part
#print axioms parts_apartFrom
#print axioms alpha_apartFrom
#print axioms tame_of_mem_parts
#print axioms parts_renameApart
#print axioms alpha_renameApart
#print axioms forall₂_alpha_renameApart
#print axioms renaming_into_the_convention
#print axioms input_of_canon
#print axioms canon_input_facts
#print axioms apart_of_canon_parts
#print axioms apart_of_renameApart

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention
