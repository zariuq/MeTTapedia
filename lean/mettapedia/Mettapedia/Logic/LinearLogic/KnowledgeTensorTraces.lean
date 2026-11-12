import Mettapedia.Logic.LinearLogic.KnowledgeTensorLending

/-!
# Independent uses commute inside a run

Two uses are independent at a state when their takes fit side by side, one shared context serves
the reads of both, and each guard holds without the other's tell. This is a property of the
state: it counts copies and asks the knowledge present there.

## Results

* `Run.deterministic`: a word has at most one run from a state.
* `Run.swap_independent`, `Swaps.run`: swapping two adjacent uses that are independent where they
  fire leaves a run between the same states. So words related by such swaps are runs between the
  same states, and the corresponding proofs have the same boundary.
* `Derives.interchange`, `Lends.interchange`: the two readouts of a tensor of proofs are related
  by swaps of independent uses, also when the two proofs share a lent zone.
* `interchanges_iff_swaps`: on words that run, exchanging adjacent blocks that run side by side
  under one lent context and swapping adjacent independent uses generate the same relation.

Runs that agree in both orders need not be independent; the controls file has a pair of uses
that take and remake one occurrence, run in both orders to the same state, and are not
independent. Commuting to the same state is therefore weaker than independence.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule

namespace System

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]
  (sys : System K Atom Rule)

/-- Two uses are independent at a state. -/
def Independent (first second : Rule) (k : K) (Γ : Multiset Atom) : Prop :=
  ∃ shared : Multiset Atom, Γ = sys.take first + sys.take second + shared ∧
    sys.read first ≤ shared ∧ sys.read second ≤ shared ∧
    sys.guard first (k ⊓ sys.tell first) ∧ sys.guard second (k ⊓ sys.tell second)

variable {sys}

/-- A word has at most one run from a state. -/
theorem Run.deterministic {k k₁ : K} {Γ Γ₁ : Multiset Atom} {uses : List Rule}
    (one : sys.Run k Γ uses k₁ Γ₁) :
    ∀ {k₂ : K} {Γ₂ : Multiset Atom}, sys.Run k Γ uses k₂ Γ₂ → k₁ = k₂ ∧ Γ₁ = Γ₂ := by
  induction one with
  | done k Γ =>
      intro k₂ Γ₂ two
      cases two
      exact ⟨rfl, rfl⟩
  | fire fires later ih =>
      intro k₂ Γ₂ two
      cases two with
      | fire fires' later' =>
          obtain ⟨rfl, rfl⟩ := Fires.deterministic fires fires'
          exact ih later'

/-- A run of a concatenated word passes through one state between the two words. -/
theorem Run.split (first : List Rule) {second : List Rule} :
    ∀ {k k' : K} {Γ Γ' : Multiset Atom}, sys.Run k Γ (first ++ second) k' Γ' →
      ∃ (k₁ : K) (Γ₁ : Multiset Atom), sys.Run k Γ first k₁ Γ₁ ∧ sys.Run k₁ Γ₁ second k' Γ' := by
  induction first with
  | nil =>
      intro k k' Γ Γ' run
      exact ⟨k, Γ, Run.done k Γ, run⟩
  | cons declaration rest ih =>
      intro k k' Γ Γ' run
      rw [List.cons_append] at run
      cases run with
      | fire fires later =>
          obtain ⟨k₁, Γ₁, early, late⟩ := ih later
          exact ⟨k₁, Γ₁, Run.fire fires early, late⟩

/-- Independent uses run in both orders to the same state. -/
theorem Independent.diamond {first second : Rule} {k : K} {Γ : Multiset Atom}
    (independent : sys.Independent first second k Γ) :
    ∃ (k' : K) (Γ' : Multiset Atom),
      sys.Run k Γ [first, second] k' Γ' ∧ sys.Run k Γ [second, first] k' Γ' := by
  obtain ⟨shared, source, firstReads, secondReads, firstAsked, secondAsked⟩ := independent
  obtain ⟨straight, swapped⟩ :=
    shared_read_diamond first second k shared firstReads secondReads firstAsked secondAsked
  rw [← source] at straight swapped
  exact ⟨_, _, straight, swapped⟩

/-- **Swapping adjacent independent uses leaves a run between the same states.** -/
theorem Run.swap_independent {before after : List Rule} {first second : Rule} {k k' : K}
    {Γ Γ' : Multiset Atom} (run : sys.Run k Γ (before ++ first :: second :: after) k' Γ')
    (independent : ∀ (k₁ : K) (Γ₁ : Multiset Atom),
      sys.Run k Γ before k₁ Γ₁ → sys.Independent first second k₁ Γ₁) :
    sys.Run k Γ (before ++ second :: first :: after) k' Γ' := by
  obtain ⟨k₁, Γ₁, early, late⟩ := Run.split before run
  obtain ⟨k₂, Γ₂, straight, swapped⟩ := (independent k₁ Γ₁ early).diamond
  obtain ⟨k₃, Γ₃, pair, tail⟩ := Run.split [first, second] (second := after) late
  obtain ⟨rfl, rfl⟩ := Run.deterministic pair straight
  exact Run.append early (Run.append swapped tail)

theorem Independent.symm {first second : Rule} {k : K} {Γ : Multiset Atom}
    (independent : sys.Independent first second k Γ) : sys.Independent second first k Γ := by
  obtain ⟨shared, source, firstReads, secondReads, firstAsked, secondAsked⟩ := independent
  exact ⟨shared, by rw [source, add_comm (sys.take first)], secondReads, firstReads, secondAsked, firstAsked⟩

/-- Words related, from a given state, by swaps of adjacent uses that are independent where they
fire. -/
inductive Swaps (system : System K Atom Rule) (k : K) (Γ : Multiset Atom) :
    List Rule → List Rule → Prop
  | same (uses : List Rule) : Swaps system k Γ uses uses
  | swap {before after : List Rule} {first second : Rule} {later : List Rule} :
      (∀ (k₁ : K) (Γ₁ : Multiset Atom),
        system.Run k Γ before k₁ Γ₁ → system.Independent first second k₁ Γ₁) →
      Swaps system k Γ (before ++ second :: first :: after) later →
        Swaps system k Γ (before ++ first :: second :: after) later

/-- **Words related by swaps of independent uses are runs between the same states.** -/
theorem Swaps.run {k k' : K} {Γ Γ' : Multiset Atom} {uses later : List Rule}
    (related : Swaps sys k Γ uses later) (run : sys.Run k Γ uses k' Γ') :
    sys.Run k Γ later k' Γ' := by
  induction related with
  | same uses => exact run
  | swap independent rest ih => exact ih (Run.swap_independent run independent)

theorem Swaps.trans {k : K} {Γ : Multiset Atom} {early middle later : List Rule}
    (one : Swaps sys k Γ early middle) (two : Swaps sys k Γ middle later) :
    Swaps sys k Γ early later := by
  induction one with
  | same uses => exact two
  | swap independent rest ih => exact Swaps.swap independent (ih two)

/-- Swaps after a run are swaps of the longer words that begin with that run. -/
theorem Swaps.after_run {k k₁ : K} {Γ Γ₁ : Multiset Atom} {pre : List Rule}
    (run : sys.Run k Γ pre k₁ Γ₁) {uses later : List Rule} (related : Swaps sys k₁ Γ₁ uses later) :
    Swaps sys k Γ (pre ++ uses) (pre ++ later) := by
  induction related with
  | same uses => exact Swaps.same _
  | @swap before after first second later independent rest ih =>
      have shape : pre ++ (before ++ first :: second :: after) =
          (pre ++ before) ++ first :: second :: after := (List.append_assoc _ _ _).symm
      have shape' : pre ++ (before ++ second :: first :: after) =
          (pre ++ before) ++ second :: first :: after := (List.append_assoc _ _ _).symm
      rw [shape]
      rw [shape'] at ih
      refine Swaps.swap ?_ ih
      intro k₂ Γ₂ whole
      obtain ⟨k₃, Γ₃, early, late⟩ := Run.split pre whole
      obtain ⟨rfl, rfl⟩ := Run.deterministic early run
      exact independent k₂ Γ₂ late

/-- Swaps extend to longer words that end alike. -/
theorem Swaps.append_right {k : K} {Γ : Multiset Atom} {uses later : List Rule} (post : List Rule)
    (related : Swaps sys k Γ uses later) : Swaps sys k Γ (uses ++ post) (later ++ post) := by
  induction related with
  | same uses => exact Swaps.same _
  | @swap before after first second later independent rest ih =>
      have shape : (before ++ first :: second :: after) ++ post =
          before ++ first :: second :: (after ++ post) := List.append_assoc _ _ _
      have shape' : (before ++ second :: first :: after) ++ post =
          before ++ second :: first :: (after ++ post) := List.append_assoc _ _ _
      rw [shape]
      rw [shape'] at ih
      exact Swaps.swap independent ih

/-- A use whose premises lie beside a run moves past that run by swaps of independent uses. -/
theorem Run.move_past {declaration : Rule} {Γ own : Multiset Atom}
    (source : Γ = sys.premises declaration + own) {k k' : K} {Δ Δ' : Multiset Atom}
    {uses : List Rule} (run : sys.Run k Δ uses k' Δ') :
    sys.guard declaration (k ⊓ sys.tell declaration) →
      Swaps sys k (Γ + Δ) (declaration :: uses) (uses ++ [declaration]) := by
  induction run with
  | done k Δ =>
      intro _
      exact Swaps.same _
  | @fire other k k₁ k' Δ Δ₁ Δ' rest fires later ih =>
      intro asked
      have fires' := fires
      obtain ⟨frame, there, otherAsked, knowledge, _⟩ := fires
      have independent : sys.Independent declaration other k (Γ + Δ) := by
        refine ⟨sys.read declaration + own + (sys.read other + frame), ?_,
          (Multiset.le_add_right _ _).trans (Multiset.le_add_right _ _),
          (Multiset.le_add_right _ _).trans (Multiset.le_add_left _ _), asked, otherAsked⟩
        rw [source, there, premises, premises]
        ac_rfl
      have first : Swaps sys k (Γ + Δ) (declaration :: other :: rest) (other :: declaration :: rest) := by
        refine Swaps.swap (before := []) ?_ (Swaps.same _)
        intro k₂ Γ₂ start
        cases start
        exact independent
      have moved : sys.Fires other k (Γ + Δ) k₁ (Γ + Δ₁) := by
        rw [add_comm Γ Δ, add_comm Γ Δ₁]
        exact Fires.frame Γ fires'
      have stronger : sys.guard declaration (k₁ ⊓ sys.tell declaration) := by
        rw [knowledge]
        exact sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked
      exact Swaps.trans first (Swaps.after_run (Run.fire moved (Run.done _ _)) (ih stronger))

/-- **Interchange is generated by swaps of independent uses.** The two readouts of two runs side
by side are related by swaps of adjacent uses, each independent of the other where they fire. -/
theorem Run.interchange {k k₁ : K} {Γ Γ' : Multiset Atom} {first : List Rule}
    (one : sys.Run k Γ first k₁ Γ') :
    ∀ {k₂ : K} {Δ Δ' : Multiset Atom} {second : List Rule}, sys.Run k Δ second k₂ Δ' →
      Swaps sys k (Γ + Δ) (first ++ second) (second ++ first) := by
  induction one with
  | done k Γ =>
      intro k₂ Δ Δ' second _
      rw [List.append_nil]
      exact Swaps.same second
  | @fire declaration k kᵣ k₁ Γ Γᵣ Γ' rest fires later ih =>
      intro k₂ Δ Δ' second two
      have fires' := fires
      obtain ⟨own, source, asked, knowledge, _⟩ := fires
      have told : sys.Run kᵣ Δ second (k₂ ⊓ sys.tell declaration) Δ' := by
        rw [knowledge]
        exact Run.strengthen (sys.tell declaration) two
      have headed := Swaps.after_run (Run.fire (Fires.frame Δ fires') (Run.done _ _)) (ih told)
      have moved := Swaps.append_right rest (Run.move_past source two asked)
      have shape : (second ++ [declaration]) ++ rest = second ++ declaration :: rest := by
        rw [List.append_assoc, List.singleton_append]
      rw [shape] at moved
      exact Swaps.trans headed moved

/-- The two readouts of a tensor of proofs are related by swaps of independent uses. -/
theorem Derives.interchange {k k₁ k₂ : K} {Γ Γ' Δ Δ' : Multiset Atom} {first second : List Rule}
    (one : sys.Derives k Γ first k₁ Γ') (two : sys.Derives k Δ second k₂ Δ') :
    Swaps sys k (Γ + Δ) (first ++ second) (second ++ first) :=
  Run.interchange (Derives.run one) (Derives.run two)

/-! ## Interchange under a shared lent context -/

/-- A firing under a lent context is a firing that owns the lent atoms, beside any extra atoms. -/
theorem FiresUnder.owning {lent : Multiset Atom} {declaration : Rule} {k k' : K}
    {Γ Γ' : Multiset Atom} (fires : sys.FiresUnder lent declaration k Γ k' Γ')
    (extra : Multiset Atom) :
    sys.Fires declaration k (Γ + extra + lent) k' (Γ' + extra + lent) := by
  obtain ⟨frame, source, readable, asked, knowledge, target⟩ := fires
  obtain ⟨rest, split⟩ := Multiset.le_iff_exists_add.mp readable
  have before : Γ + extra + lent = sys.take declaration + (frame + lent) + extra := by
    rw [source]
    ac_rfl
  have after : Γ' + extra + lent = sys.make declaration + (frame + lent) + extra := by
    rw [target]
    ac_rfl
  refine ⟨rest + extra, ?_, asked, knowledge, ?_⟩
  · rw [before, split, premises]
    ac_rfl
  · rw [after, split, conclusions]
    ac_rfl

/-- A use beside a firing under the same lent context is independent of it. -/
theorem FiresUnder.independent_beside {lent : Multiset Atom} {first second : Rule} {k k' : K}
    {Γ own Δ Δ' : Multiset Atom} (source : Γ = sys.take first + own)
    (readable : sys.read first ≤ own + lent) (asked : sys.guard first (k ⊓ sys.tell first))
    (fires : sys.FiresUnder lent second k Δ k' Δ') :
    sys.Independent first second k (Γ + Δ + lent) := by
  obtain ⟨frame, there, readable', asked', _, _⟩ := fires
  refine ⟨own + frame + lent, ?_, ?_, ?_, asked, asked'⟩
  · rw [source, there]
    ac_rfl
  · exact readable.trans (Multiset.le_iff_exists_add.mpr ⟨frame, by ac_rfl⟩)
  · exact readable'.trans (Multiset.le_iff_exists_add.mpr ⟨own, by ac_rfl⟩)

theorem RunUnder.move_past {lent : Multiset Atom} {declaration : Rule} {Γ own : Multiset Atom}
    (source : Γ = sys.take declaration + own) (readable : sys.read declaration ≤ own + lent)
    {k k' : K} {Δ Δ' : Multiset Atom} {uses : List Rule} (run : sys.RunUnder lent k Δ uses k' Δ') :
    sys.guard declaration (k ⊓ sys.tell declaration) →
      Swaps sys k (Γ + Δ + lent) (declaration :: uses) (uses ++ [declaration]) := by
  induction run with
  | done k Δ =>
      intro _
      exact Swaps.same _
  | @fire other k k₁ k' Δ Δ₁ Δ' rest fires later ih =>
      intro asked
      have independent := FiresUnder.independent_beside source readable asked fires
      have first : Swaps sys k (Γ + Δ + lent) (declaration :: other :: rest)
          (other :: declaration :: rest) := by
        refine Swaps.swap (before := []) ?_ (Swaps.same _)
        intro k₂ Γ₂ start
        cases start
        exact independent
      have moved : sys.Fires other k (Γ + Δ + lent) k₁ (Γ + Δ₁ + lent) := by
        have owning := FiresUnder.owning fires Γ
        rw [add_comm Δ Γ, add_comm Δ₁ Γ] at owning
        exact owning
      have stronger : sys.guard declaration (k₁ ⊓ sys.tell declaration) := by
        obtain ⟨_, _, _, _, knowledge, _⟩ := fires
        rw [knowledge]
        exact sys.guard_mono declaration (inf_le_inf_right _ inf_le_left) asked
      exact Swaps.trans first (Swaps.after_run (Run.fire moved (Run.done _ _)) (ih stronger))

/-- **Interchange under a shared lent context is generated by swaps of independent uses.** -/
theorem RunUnder.interchange {lent : Multiset Atom} {k k₁ : K} {Γ Γ' : Multiset Atom}
    {first : List Rule} (one : sys.RunUnder lent k Γ first k₁ Γ') :
    ∀ {k₂ : K} {Δ Δ' : Multiset Atom} {second : List Rule}, sys.RunUnder lent k Δ second k₂ Δ' →
      Swaps sys k (Γ + Δ + lent) (first ++ second) (second ++ first) := by
  induction one with
  | done k Γ =>
      intro k₂ Δ Δ' second _
      rw [List.append_nil]
      exact Swaps.same second
  | @fire declaration k kᵣ k₁ Γ Γᵣ Γ' rest fires later ih =>
      intro k₂ Δ Δ' second two
      have fires' := fires
      obtain ⟨own, source, readable, asked, knowledge, _⟩ := fires
      have told : sys.RunUnder lent kᵣ Δ second (k₂ ⊓ sys.tell declaration) Δ' := by
        rw [knowledge]
        exact RunUnder.strengthen (sys.tell declaration) two
      have stepped : sys.Run k (Γ + Δ + lent) [declaration] kᵣ (Γᵣ + Δ + lent) :=
        Run.fire (FiresUnder.owning fires' Δ) (Run.done _ _)
      have headed := Swaps.after_run stepped (ih told)
      have moved := Swaps.append_right rest (RunUnder.move_past source readable two asked)
      have shape : (second ++ [declaration]) ++ rest = second ++ declaration :: rest := by
        rw [List.append_assoc, List.singleton_append]
      rw [shape] at moved
      exact Swaps.trans headed moved

/-- The two readouts of a tensor of proofs over a shared lent zone are related by swaps of
independent uses. -/
theorem Lends.interchange {lent : Multiset Atom} {k k₁ k₂ : K} {Γ Γ' Δ Δ' : Multiset Atom}
    {first second : List Rule} (one : sys.Lends lent k Γ first k₁ Γ')
    (two : sys.Lends lent k Δ second k₂ Δ') :
    Swaps sys k (Γ + Δ + lent) (first ++ second) (second ++ first) :=
  RunUnder.interchange (Lends.run one) (Lends.run two)

/-! ## Interchange and swaps generate the same relation -/

/-- Words related, from a given state, by exchanging two adjacent blocks that run side by side
under one lent context. -/
inductive Interchanges (system : System K Atom Rule) (k : K) (Γ : Multiset Atom) :
    List Rule → List Rule → Prop
  | same (uses : List Rule) : Interchanges system k Γ uses uses
  | exchange {before after first second later : List Rule} :
      (∀ (k₁ : K) (Γ₁ : Multiset Atom), system.Run k Γ before k₁ Γ₁ →
        ∃ (lent left right : Multiset Atom) (kₗ kᵣ : K) (left' right' : Multiset Atom),
          Γ₁ = left + right + lent ∧ system.RunUnder lent k₁ left first kₗ left' ∧
            system.RunUnder lent k₁ right second kᵣ right') →
      Interchanges system k Γ (before ++ (second ++ first) ++ after) later →
        Interchanges system k Γ (before ++ (first ++ second) ++ after) later

/-- A swap of independent uses is an interchange of two leaves over their shared context. -/
theorem Swaps.interchanges {k : K} {Γ : Multiset Atom} {uses later : List Rule}
    (related : Swaps sys k Γ uses later) : Interchanges sys k Γ uses later := by
  induction related with
  | same uses => exact Interchanges.same uses
  | @swap before after first second later independent rest ih =>
      have shape : before ++ first :: second :: after = before ++ ([first] ++ [second]) ++ after :=
        (List.append_assoc before ([first] ++ [second]) after).symm
      have shape' : before ++ second :: first :: after = before ++ ([second] ++ [first]) ++ after :=
        (List.append_assoc before ([second] ++ [first]) after).symm
      rw [shape]
      rw [shape'] at ih
      refine Interchanges.exchange ?_ ih
      intro k₁ Γ₁ early
      obtain ⟨shared, source, firstReads, secondReads, firstAsked, secondAsked⟩ :=
        independent k₁ Γ₁ early
      exact ⟨shared, sys.take first, sys.take second, _, _, _, _, source,
        Lends.run (Lends.grow firstReads (Lends.rule first k₁ firstAsked)),
        Lends.run (Lends.grow secondReads (Lends.rule second k₁ secondAsked))⟩

/-- An interchange of a word that runs decomposes into swaps of independent uses. -/
theorem Interchanges.swaps {k k' : K} {Γ Γ' : Multiset Atom} {uses later : List Rule}
    (related : Interchanges sys k Γ uses later) :
    sys.Run k Γ uses k' Γ' → Swaps sys k Γ uses later := by
  induction related with
  | same uses =>
      intro _
      exact Swaps.same uses
  | @exchange before after first second later sideBySide rest ih =>
      intro run
      have shape : before ++ (first ++ second) ++ after = before ++ ((first ++ second) ++ after) :=
        List.append_assoc _ _ _
      have shape' : before ++ (second ++ first) ++ after = before ++ ((second ++ first) ++ after) :=
        List.append_assoc _ _ _
      rw [shape] at run ⊢
      rw [shape'] at ih
      obtain ⟨k₁, Γ₁, early, _⟩ := Run.split before run
      obtain ⟨lent, left, right, kₗ, kᵣ, left', right', source, one, two⟩ := sideBySide k₁ Γ₁ early
      subst source
      have whole := Swaps.after_run early (Swaps.append_right after (RunUnder.interchange one two))
      exact Swaps.trans whole (ih (Swaps.run whole run))

/-- **On words that run, interchange of side-by-side blocks and swaps of independent uses
generate the same relation.** -/
theorem interchanges_iff_swaps {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (run : sys.Run k Γ uses k' Γ') (later : List Rule) :
    Interchanges sys k Γ uses later ↔ Swaps sys k Γ uses later :=
  ⟨fun related => Interchanges.swaps related run, Swaps.interchanges⟩

end System

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
