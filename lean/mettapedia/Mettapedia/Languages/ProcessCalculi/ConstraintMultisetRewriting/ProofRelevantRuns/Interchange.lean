import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mettapedia.Logic.LinearLogic.KnowledgeTensorTraces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Initial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Rearrangements

/-!
# Interchange cells of the two-zone calculus

The interchange cells of `Rearrangements`, for the knowledge-tensor system: a state is knowledge
and atoms, a step is a firing, and a swap is allowed where the two uses are independent there
(`System.Independent`: their takes fit side by side, one shared context serves both reads, and
each guard holds without the other's tell).

* `runs_iff_run`, `fires_deterministic`, `independent_square`: the step of the system, its runs,
  and why independent pairs close.
* `Cell.place`, `events_place`: **every cell is natural in placements**: putting the state beside
  more atoms and under more knowledge carries each cell to a cell with the same event map. The
  frame and knowledge actions on runs extend to cells.
* `movePast`, `interchange`: the cell that moves a use past a run beside it, and **the
  interchange cell** of two runs side by side, from `first ++ second` to `second ++ first`, as data.
  `interchange_events`: where the uses are distinct, its event map is the block exchange.
  `fourBlock`: the interchange law of a cut of tensors, by whiskering.
* `Cell.swaps`, `nonempty_cell_iff_swaps`: **the swap relation of traces is the truncation of the
  cells**: on words that run, `System.Swaps` holds exactly when a cell exists.
* `Cell.perm`, `weights_invariant`: a cell permutes its word, so weights in a commutative monoid
  are invariant under cells.
* `quiet_iff_never_waited_on`, `independent_of_quiet`: knowledge blocks an interchange only
  through a tell that some guard waits for; a tell already known at the state is waited for by
  no guard, and then a pair that runs in one order with its atoms apart is independent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns

open Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]

/-! ## The step of the system -/

/-- One firing of the system, between states of knowledge and atoms. -/
def fires (sys : System K Atom Rule) (s : K × Multiset Atom) (declaration : Rule)
    (t : K × Multiset Atom) : Prop :=
  sys.Fires declaration s.1 s.2 t.1 t.2

/-- Two uses are independent at a state. -/
def independent (sys : System K Atom Rule) (s : K × Multiset Atom) (first second : Rule) : Prop :=
  sys.Independent first second s.1 s.2

/-- The interchange cells of the system. -/
abbrev Cell (sys : System K Atom Rule) := Rearrangement (fires sys) (independent sys)

variable {sys : System K Atom Rule}

theorem runs_iff_run {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule} :
    Runs (fires sys) (k, Γ) uses (k', Γ') ↔ sys.Run k Γ uses k' Γ' := by
  constructor
  · intro run
    generalize hs : ((k, Γ) : K × Multiset Atom) = s at run
    generalize ht : ((k', Γ') : K × Multiset Atom) = t at run
    induction run generalizing k Γ with
    | nil s =>
        subst hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj ht
        exact System.Run.done _ _
    | @cons s₀ t₀ u a w step later ih =>
        subst hs
        exact System.Run.fire step (ih rfl ht)
  · intro run
    induction run with
    | done k Γ => exact Runs.nil _
    | fire step later ih => exact Runs.cons (t := (_, _)) step ih

theorem fires_deterministic : Deterministic (fires sys) := by
  intro s t t' a one two
  obtain ⟨same, same'⟩ := System.Fires.deterministic one two
  exact Prod.ext same same'

theorem independent_square {s : K × Multiset Atom} {first second : Rule}
    (independent' : independent sys s first second) : Square (fires sys) s first second := by
  obtain ⟨k', Γ', straight, swapped⟩ := System.Independent.diamond independent'
  exact ⟨(k', Γ'), runs_iff_run.mpr straight, runs_iff_run.mpr swapped⟩

/-- **A cell carries runs to runs**, between the same states. -/
theorem Cell.run {k k' : K} {Γ Γ' : Multiset Atom} {w w' : List Rule}
    (cell : Cell sys (k, Γ) w w') (run : sys.Run k Γ w k' Γ') : sys.Run k Γ w' k' Γ' :=
  runs_iff_run.mp (Rearrangement.runs (step := fires sys) (adm := independent sys)
    fires_deterministic independent_square cell (runs_iff_run.mpr run))

/-! ## Placements -/

/-- A placement: beside more atoms and under more knowledge. -/
def placed (extra : Multiset Atom) (more : K) (s : K × Multiset Atom) : K × Multiset Atom :=
  (s.1 ⊓ more, s.2 + extra)

theorem fires_placed (extra : Multiset Atom) (more : K) {s t : K × Multiset Atom} {a : Rule}
    (step : fires sys s a t) : fires sys (placed extra more s) a (placed extra more t) :=
  System.Fires.strengthen more (System.Fires.frame extra step)

theorem independent_placed (extra : Multiset Atom) (more : K) {s : K × Multiset Atom} {a b : Rule}
    (independent' : independent sys s a b) : independent sys (placed extra more s) a b := by
  obtain ⟨shared, source, firstReads, secondReads, firstAsked, secondAsked⟩ := independent'
  refine ⟨shared + extra, ?_, firstReads.trans (Multiset.le_add_right _ _),
    secondReads.trans (Multiset.le_add_right _ _), ?_, ?_⟩
  · show s.2 + extra = _
    rw [source, add_assoc]
  · exact sys.guard_mono a (inf_le_inf_right _ inf_le_left) firstAsked
  · exact sys.guard_mono b (inf_le_inf_right _ inf_le_left) secondAsked

/-- **Every cell is natural in placements**: beside more atoms and under more knowledge it is a
cell between the same words. -/
def Cell.place (extra : Multiset Atom) (more : K) {s : K × Multiset Atom} {w w' : List Rule}
    (cell : Cell sys s w w') : Cell sys (placed extra more s) w w' :=
  cell.mapAlong (placed extra more) (fires_placed extra more)
    (Rearrangement.survives_of_keeps _ (independent_placed extra more) cell)

/-- **A placed cell moves every event as the cell does.** -/
theorem events_place (extra : Multiset Atom) (more : K) {s : K × Multiset Atom} {w w' : List Rule}
    (cell : Cell sys s w w') : (cell.place extra more).events = cell.events :=
  Rearrangement.events_mapAlong _ _ cell _

/-! ## The interchange cell -/

section Interchange

variable [DecidableEq Atom]

omit [DecidableEq Atom] in
theorem cons_inv_exists {declaration : Rule} {rest : List Rule} {k : K} {Γ : Multiset Atom}
    (run : ∃ (k' : K) (Γ' : Multiset Atom), sys.Run k Γ (declaration :: rest) k' Γ')
    [DecidableEq Atom] :
    Γ = sys.premises declaration + (Γ - sys.premises declaration) ∧
      sys.guard declaration (k ⊓ sys.tell declaration) ∧
      ∃ (k' : K) (Γ' : Multiset Atom), sys.Run (k ⊓ sys.tell declaration)
        (sys.conclusions declaration + (Γ - sys.premises declaration)) rest k' Γ' := by
  obtain ⟨k', Γ', inner⟩ := run
  obtain ⟨source, asked, later⟩ := Path.cons_inv inner
  exact ⟨source, asked, k', Γ', later⟩

/-- A use fires beside a context `Γ`, from the atoms `Δ` that hold its premises. -/
theorem fires_beside {declaration : Rule} {k : K} {Δ : Multiset Atom} (Γ : Multiset Atom)
    (source : Δ = sys.premises declaration + (Δ - sys.premises declaration))
    (asked : sys.guard declaration (k ⊓ sys.tell declaration)) :
    fires sys (k, Γ + Δ) declaration
      (k ⊓ sys.tell declaration, Γ + (sys.conclusions declaration + (Δ - sys.premises declaration))) := by
  refine ⟨Γ + (Δ - sys.premises declaration), ?_, asked, rfl, ?_⟩
  · show Γ + Δ = _
    calc Γ + Δ = Γ + (sys.premises declaration + (Δ - sys.premises declaration)) := by rw [← source]
      _ = _ := add_left_comm _ _ _
  · show Γ + (sys.conclusions declaration + (Δ - sys.premises declaration)) = _
    exact add_left_comm _ _ _

/-- The independence of a use whose premises are owned beside a firing. -/
theorem independent_beside {declaration other : Rule} {k : K} {own Δ : Multiset Atom}
    (source : Δ = sys.premises other + (Δ - sys.premises other))
    (asked : sys.guard declaration (k ⊓ sys.tell declaration))
    (otherAsked : sys.guard other (k ⊓ sys.tell other)) :
    independent sys (k, sys.premises declaration + own + Δ) declaration other := by
  generalize hrest : Δ - sys.premises other = rest at source
  subst source
  refine ⟨sys.read declaration + own + (sys.read other + rest), ?_,
    (Multiset.le_add_right _ _).trans (Multiset.le_add_right _ _),
    (Multiset.le_add_right _ _).trans (Multiset.le_add_left _ _), asked, otherAsked⟩
  show sys.premises declaration + own + (sys.premises other + rest) = _
  simp only [System.premises]
  ac_rfl

/-- **Moving one use past a run beside it.** -/
def movePast (declaration : Rule) (own : Multiset Atom) :
    (uses : List Rule) → (k : K) → (Δ : Multiset Atom) →
      (∃ (k' : K) (Δ' : Multiset Atom), sys.Run k Δ uses k' Δ') →
      sys.guard declaration (k ⊓ sys.tell declaration) →
      Cell sys (k, sys.premises declaration + own + Δ) (declaration :: uses) (uses ++ [declaration])
  | [], _, _, _, _ => Rearrangement.refl _ _
  | other :: rest, k, Δ, run, asked =>
      Rearrangement.swap [] (k, sys.premises declaration + own + Δ) declaration other rest
        (Runs.nil _)
        (independent_beside (cons_inv_exists run).1 asked (cons_inv_exists run).2.1)
        (Rearrangement.whiskerLeft [other]
          (Runs.cons (fires_beside (sys.premises declaration + own) (cons_inv_exists run).1
            (cons_inv_exists run).2.1) (Runs.nil _))
          (movePast declaration own rest (k ⊓ sys.tell other)
            (sys.conclusions other + (Δ - sys.premises other)) (cons_inv_exists run).2.2
            (sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked)))

omit [DecidableEq Atom] in
theorem run_strengthen_exists {k : K} {Δ : Multiset Atom} {uses : List Rule} (more : K)
    (run : ∃ (k' : K) (Δ' : Multiset Atom), sys.Run k Δ uses k' Δ') :
    ∃ (k' : K) (Δ' : Multiset Atom), sys.Run (k ⊓ more) Δ uses k' Δ' := by
  obtain ⟨k', Δ', inner⟩ := run
  exact ⟨k' ⊓ more, Δ', System.Run.strengthen more inner⟩

/-- **The interchange cell** of two runs side by side: from `first ++ second` to
`second ++ first`, at the state that holds both. -/
def interchange (second : List Rule) : (first : List Rule) → (k : K) → (Γ Δ : Multiset Atom) →
    (∃ (k₁ : K) (Γ' : Multiset Atom), sys.Run k Γ first k₁ Γ') →
    (∃ (k₂ : K) (Δ' : Multiset Atom), sys.Run k Δ second k₂ Δ') →
    Cell sys (k, Γ + Δ) (first ++ second) (second ++ first)
  | [], _, _, _, _, _ => Rearrangement.cast rfl rfl (List.append_nil second).symm (Rearrangement.refl _ _)
  | declaration :: rest, k, Γ, Δ, one, two =>
      Rearrangement.trans
        (Rearrangement.whiskerLeft [declaration]
          (Runs.cons
            (by
              have moved := fires_beside (sys := sys) Δ (cons_inv_exists one).1 (cons_inv_exists one).2.1
              rw [add_comm Δ Γ, add_comm Δ] at moved
              exact moved)
            (Runs.nil _))
          (interchange second rest (k ⊓ sys.tell declaration)
            (sys.conclusions declaration + (Γ - sys.premises declaration)) Δ
            (cons_inv_exists one).2.2 (run_strengthen_exists (sys.tell declaration) two)))
        (Rearrangement.cast
          (by rw [← (cons_inv_exists one).1]) rfl
          (by simp only [List.append_assoc, List.singleton_append])
          (Rearrangement.whiskerRight rest
            (movePast declaration (Γ - sys.premises declaration) second k Δ two
              (cons_inv_exists one).2.1)))

/-- The block exchange of positions. -/
def blockSwap (n m j : Nat) : Nat := if j < n then j + m else j - n

/-- **Where the uses are distinct, the interchange cell moves events by the block exchange.** -/
theorem interchange_events (second first : List Rule) (k : K) (Γ Δ : Multiset Atom)
    (one : ∃ (k₁ : K) (Γ' : Multiset Atom), sys.Run k Γ first k₁ Γ')
    (two : ∃ (k₂ : K) (Δ' : Multiset Atom), sys.Run k Δ second k₂ Δ')
    (distinct : (second ++ first).Nodup) {j : Nat} (inside : j < (first ++ second).length) :
    (interchange second first k Γ Δ one two).events j = blockSwap first.length second.length j := by
  obtain ⟨x, hx⟩ : ∃ x, (first ++ second)[j]? = some x :=
    ⟨(first ++ second)[j], List.getElem?_eq_getElem inside⟩
  refine Rearrangement.index_eq_of_nodup distinct
    (((interchange second first k Γ Δ one two).events_label j).trans hx) ?_
  rw [← hx]
  unfold blockSwap
  rw [List.length_append] at inside
  split_ifs with small
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_left small]
    congr 1
    omega
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega)]

/-- **The interchange law of a cut of tensors, as a cell**: after a prefix, two runs side by side
exchange, and a suffix follows. -/
def fourBlock {s : K × Multiset Atom} (prefix' : List Rule) {k : K} {Γ Δ : Multiset Atom}
    (reach : Runs (fires sys) s prefix' (k, Γ + Δ)) (first second suffix : List Rule)
    (one : ∃ (k₁ : K) (Γ' : Multiset Atom), sys.Run k Γ first k₁ Γ')
    (two : ∃ (k₂ : K) (Δ' : Multiset Atom), sys.Run k Δ second k₂ Δ') :
    Cell sys s (prefix' ++ ((first ++ second) ++ suffix)) (prefix' ++ ((second ++ first) ++ suffix)) :=
  Rearrangement.whiskerLeft prefix' reach
    (Rearrangement.whiskerRight suffix (interchange second first k Γ Δ one two))

/-- **The event map of the four-block cell**: the prefix stays, the middle blocks exchange where
their uses are distinct, and the suffix stays. -/
theorem fourBlock_events {s : K × Multiset Atom} (prefix' : List Rule) {k : K} {Γ Δ : Multiset Atom}
    (reach : Runs (fires sys) s prefix' (k, Γ + Δ)) (first second suffix : List Rule)
    (one : ∃ (k₁ : K) (Γ' : Multiset Atom), sys.Run k Γ first k₁ Γ')
    (two : ∃ (k₂ : K) (Δ' : Multiset Atom), sys.Run k Δ second k₂ Δ')
    (distinct : (second ++ first).Nodup) (j : Nat) :
    (fourBlock prefix' reach first second suffix one two).events j =
      if j < prefix'.length then j
      else if j - prefix'.length < (first ++ second).length then
        prefix'.length + blockSwap first.length second.length (j - prefix'.length)
      else j := by
  unfold fourBlock
  rw [Rearrangement.events_whiskerLeft, Rearrangement.events_whiskerRight]
  split_ifs with small inside
  · rfl
  · rw [interchange_events second first k Γ Δ one two distinct inside]
  · rw [Rearrangement.events_beyond _ (Nat.le_of_not_lt inside)]
    omega

end Interchange

/-! ## The swap relation is the truncation of the cells -/

/-- **A cell gives the swap relation of traces.** -/
theorem Cell.swaps {k : K} {Γ : Multiset Atom} {w w' : List Rule} (cell : Cell sys (k, Γ) w w') :
    sys.Swaps k Γ w w' := by
  induction cell with
  | refl w => exact System.Swaps.same w
  | swap before mid a b after reach admissible rest ih =>
      refine System.Swaps.swap ?_ ih
      intro k₁ Γ₁ early
      have same := Runs.unique (step := fires sys) fires_deterministic reach
        (runs_iff_run.mpr early)
      subst same
      exact admissible

/-- **On words that run, the swap relation holds exactly when a cell exists.** -/
theorem nonempty_cell_iff_swaps {k k' : K} {Γ Γ' : Multiset Atom} {w : List Rule}
    (run : sys.Run k Γ w k' Γ') (w' : List Rule) :
    Nonempty (Cell sys (k, Γ) w w') ↔ sys.Swaps k Γ w w' := by
  constructor
  · rintro ⟨cell⟩
    exact cell.swaps
  · intro related
    induction related with
    | same uses => exact ⟨Rearrangement.refl _ _⟩
    | @swap before after first second later independent' rest ih =>
        obtain ⟨k₁, Γ₁, early, _⟩ := System.Run.split before run
        obtain ⟨cell⟩ := ih (System.Run.swap_independent run independent')
        exact ⟨Rearrangement.swap before (k₁, Γ₁) first second after (runs_iff_run.mpr early)
          (independent' k₁ Γ₁ early) cell⟩

/-- **On words that run, the block interchange relation of traces holds exactly when a cell
exists.** -/
theorem nonempty_cell_iff_interchanges {k k' : K} {Γ Γ' : Multiset Atom} {w : List Rule}
    (run : sys.Run k Γ w k' Γ') (w' : List Rule) :
    Nonempty (Cell sys (k, Γ) w w') ↔ sys.Interchanges k Γ w w' :=
  (nonempty_cell_iff_swaps run w').trans (System.interchanges_iff_swaps run w').symm

/-! ## Cells permute words -/

/-- **A cell permutes its word.** -/
theorem Cell.perm {s : K × Multiset Atom} {w w' : List Rule} (cell : Cell sys s w w') : w.Perm w' := by
  induction cell with
  | refl w => exact List.Perm.refl w
  | swap before mid a b after reach admissible rest ih =>
      exact (List.Perm.append_left before (List.Perm.swap b a after)).trans ih

/-- **Weights in a commutative monoid are invariant under cells.** -/
theorem weights_invariant {N : Type*} [CommMonoid N] (weight : Rule → N) {s : K × Multiset Atom}
    {w w' : List Rule} (cell : Cell sys s w w') : (w.map weight).prod = (w'.map weight).prod :=
  ((cell.perm).map weight).prod_eq

/-! ## Quiet tells -/

/-- **A tell is waited for by no guard exactly when it is already known.** Every guard that holds
after the tell holds before it exactly when the knowledge already refines the tell. -/
theorem quiet_iff_never_waited_on (k tell : K) :
    k ≤ tell ↔ ∀ guard : K → Prop, (∀ {stronger weaker : K}, stronger ≤ weaker → guard weaker → guard stronger) →
      guard (k ⊓ tell) → guard k := by
  constructor
  · intro quiet guard _ held
    rwa [inf_eq_left.mpr quiet] at held
  · intro never
    exact never (fun x => x ≤ tell) (fun refines held => refines.trans held) inf_le_right

/-- **A quiet use and a use beside it**: if the first use's tell is already known, the two run in
one order, and their atoms are apart, they are independent. -/
theorem independent_of_quiet {first second : Rule} {k : K} {Γ : Multiset Atom}
    (quiet : k ≤ sys.tell first)
    (apart : ∃ shared : Multiset Atom, Γ = sys.take first + sys.take second + shared ∧
      sys.read first ≤ shared ∧ sys.read second ≤ shared)
    (run : ∃ (k' : K) (Γ' : Multiset Atom), sys.Run k Γ [first, second] k' Γ') :
    sys.Independent first second k Γ := by
  obtain ⟨shared, source, firstReads, secondReads⟩ := apart
  obtain ⟨k', Γ', inner⟩ := run
  cases inner with
  | fire one later =>
      cases later with
      | fire two _ =>
          obtain ⟨_, _, firstAsked, told, _⟩ := one
          obtain ⟨_, _, secondAsked, _, _⟩ := two
          subst told
          rw [inf_eq_left.mpr quiet] at secondAsked
          exact ⟨shared, source, firstReads, secondReads, firstAsked, secondAsked⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns
