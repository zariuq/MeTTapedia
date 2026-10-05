import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaControlBinders

/-!
# The emitter's actual variable supply

Pattern variables occupy precisely the allocation interval before the body is
emitted. Later control binders therefore cannot occur in the pattern, even
when guest strings resemble generated variable names.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open MeTTaData

theorem data_has_no_variables {atom : Atom} (data : DataAtom atom) (name : String) :
    ¬AtomOccurs atom name := by
  induction data with
  | symbol | grounded => intro occurrence; cases occurrence
  | expression children ih =>
      intro occurrence
      cases occurrence with
      | expression member occurrence => exact ih _ member occurrence

theorem occurs_call_iff (head : String) (arguments : List Atom) (name : String) :
    AtomOccurs (call head arguments) name ↔
      ∃ argument ∈ arguments, AtomOccurs argument name := by
  constructor
  · intro occurrence
    cases occurrence with
    | expression member occurrence =>
        rcases List.mem_cons.mp member with rfl | member
        · cases occurrence
        · exact ⟨_, member, occurrence⟩
  · rintro ⟨argument, member, occurrence⟩
    exact .expression (List.mem_cons_of_mem _ member) occurrence

mutual

theorem pattern_name_bounds (source : Term) (first : Nat) :
    first ≤ (pattern source first).2 ∧
      ∀ name, AtomOccurs (pattern source first).1.1 name →
        ∃ index, first ≤ index ∧ index < (pattern source first).2 ∧
          name = freshName index := by
  cases source with
  | var name =>
      rw [pattern_variable]
      refine ⟨by simp, ?_⟩
      intro other occurrence
      cases occurrence
      exact ⟨first, le_rfl, by simp, rfl⟩
  | sym name =>
      rw [pattern_symbol]
      exact ⟨le_rfl, fun other occurrence =>
        False.elim (data_has_no_variables (encode_data (.sym name)) other occurrence)⟩
  | lit text =>
      rw [pattern_literal]
      exact ⟨le_rfl, fun other occurrence =>
        False.elim (data_has_no_variables (encode_data (.lit text)) other occurrence)⟩
  | expr items =>
      rw [pattern_expression]
      obtain ⟨increases, names⟩ := patterns_name_bounds items first
      refine ⟨increases, ?_⟩
      intro name occurrence
      obtain ⟨argument, member, occurs⟩ := (occurs_call_iff _ _ _).mp occurrence
      have same := List.mem_singleton.mp member
      subst argument
      exact names name occurs
  | list items =>
      rw [pattern_list]
      obtain ⟨increases, names⟩ := patterns_name_bounds items first
      refine ⟨increases, ?_⟩
      intro name occurrence
      obtain ⟨argument, member, occurs⟩ := (occurs_call_iff _ _ _).mp occurrence
      have same := List.mem_singleton.mp member
      subst argument
      exact names name occurs
termination_by sizeOf source

theorem patterns_name_bounds (source : List Term) (first : Nat) :
    first ≤ (patterns source first).2 ∧
      ∀ name, AtomOccurs (patterns source first).1.1 name →
        ∃ index, first ≤ index ∧ index < (patterns source first).2 ∧
          name = freshName index := by
  cases source with
  | nil =>
      rw [patterns_nil]
      refine ⟨le_rfl, ?_⟩
      intro name occurrence
      cases occurrence
  | cons head rest =>
      rw [patterns_cons]
      dsimp only
      obtain ⟨headIncreases, headNames⟩ := pattern_name_bounds head first
      obtain ⟨tailIncreases, tailNames⟩ :=
        patterns_name_bounds rest (pattern head first).2
      refine ⟨headIncreases.trans tailIncreases, ?_⟩
      intro name occurrence
      obtain ⟨argument, member, occurs⟩ := (occurs_call_iff _ _ _).mp occurrence
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨index, lower, upper, same⟩ := headNames name occurs
        exact ⟨index, lower, upper.trans_le tailIncreases, same⟩
      · have same := List.mem_singleton.mp member
        subst argument
        obtain ⟨index, lower, upper, same⟩ := tailNames name occurs
        exact ⟨index, headIncreases.trans lower, upper, same⟩
termination_by sizeOf source

end

/-- A variable allocated after a pattern cannot be captured by that pattern. -/
theorem patterns_exclude_later_names (source : List Term) (first index : Nat)
    (later : (patterns source first).2 ≤ index) :
    ¬AtomOccurs (patterns source first).1.1 (freshName index) := by
  intro occurrence
  obtain ⟨earlier, _, upper, same⟩ :=
    (patterns_name_bounds source first).2 _ occurrence
  have equalIndex := freshName_injective same
  omega

mutual

theorem alpha_occurs_image {rename : String → String} {source target : Atom}
    (renamed : AlphaRenameAtomRel rename source target) {name : String}
    (occurrence : AtomOccurs target name) :
    ∃ original, AtomOccurs source original ∧ rename original = name := by
  cases renamed with
  | symbol | grounded => cases occurrence
  | «variable» original =>
      cases occurrence
      exact ⟨original, .var _, rfl⟩
  | expression items =>
      cases occurrence with
      | expression member occurs =>
          obtain ⟨atom, rawMember, original, rawOccurs, same⟩ :=
            alpha_items_occurs_image items member occurs
          exact ⟨original, .expression rawMember rawOccurs, same⟩
termination_by sizeOf source

theorem alpha_items_occurs_image {rename : String → String} {source target : List Atom}
    (renamed : AlphaRenameAtomsRel rename source target) {atom : Atom}
    (member : atom ∈ target) {name : String} (occurrence : AtomOccurs atom name) :
    ∃ raw ∈ source, ∃ original, AtomOccurs raw original ∧ rename original = name := by
  cases renamed with
  | nil => cases member
  | cons head tail =>
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨original, rawOccurs, same⟩ := alpha_occurs_image head occurrence
        exact ⟨_, by simp, original, rawOccurs, same⟩
      · obtain ⟨raw, rawMember, original, rawOccurs, same⟩ :=
          alpha_items_occurs_image tail member occurrence
        exact ⟨raw, List.mem_cons_of_mem _ rawMember, original, rawOccurs, same⟩
termination_by sizeOf source

end

/-- Runtime alpha-renaming preserves the allocator's pattern/binder separation. -/
theorem alpha_patterns_exclude_later_names (source : List Term) (first index : Nat)
    {rename : String → String} (injective : Function.Injective rename) {target : Atom}
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 target)
    (later : (patterns source first).2 ≤ index) :
    ¬AtomOccurs target (rename (freshName index)) := by
  intro occurrence
  obtain ⟨original, rawOccurs, same⟩ := alpha_occurs_image renamed occurrence
  have originalName : original = freshName index := injective same
  exact patterns_exclude_later_names source first index later (originalName ▸ rawOccurs)

/-- The target query's existing freshness condition and the emitter's actual
allocation order discharge the local binder condition used by selection. -/
theorem allocated_binder_private (source : List Term) (first index : Nat)
    {rename : String → String} (injective : Function.Injective rename)
    {target query : Atom} {incoming : Bindings} {live : List Atom}
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 target)
    (later : (patterns source first).2 ≤ index)
    (privateCaller : ¬QueryVisibleName live query incoming (rename (freshName index))) :
    ¬QueryVisibleName [target] query incoming (rename (freshName index)) := by
  intro visible
  rcases visible with queryOccurs | ⟨atom, member, occurs⟩ | incomingOccurs
  · exact privateCaller (.inl queryOccurs)
  · have same := List.mem_singleton.mp member
    subst atom
    exact alpha_patterns_exclude_later_names source first index injective renamed later occurs
  · exact privateCaller (.inr (.inr incomingOccurs))

/-- Guest variable spellings are encoded strings, not target variable names. -/
theorem guest_name_cannot_capture (name : String) (index : Nat) :
    ¬AtomOccurs (MeTTaData.encode (.var name)) (freshName index) :=
  data_has_no_variables (encode_data (.var name)) _

/-- Reusing an allocated pattern index would violate the freshness boundary. -/
theorem reused_index_occurs (name : String) (first : Nat) :
    AtomOccurs (patterns [.var name] first).1.1 (freshName first) := by
  simp only [patterns_cons, pattern_variable, patterns_nil]
  exact (occurs_call_iff _ _ _).mpr ⟨_, by simp, .var _⟩

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
