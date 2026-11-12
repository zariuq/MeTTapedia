import Mettapedia.Languages.MeTTa.PeTTa.UnifyingDecides
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRefinement

/-!
# The pattern unifier decides within its fuel

A call unifies its values with an equation's argument patterns by `unifyPattern`, which
reads a pattern `(cons first rest)` against a nonempty list as PeTTa's list view: `first`
with the list's first item, `rest` with the list of the others. `UnifyingDecides` proves
that `unifyTerms` never runs out of the fuel `unify` gives it. This module proves the same
for `unifyPattern`: `unifyAsPattern`, `unifyBinding` and `unifyArguments` answer a unifier
or a clash on an idempotent substitution, whatever the patterns and the values are.

The descent of `unifyPattern` follows the pattern as it is written, one level for each
level of the pattern, and hands a part that is no expression, or that meets a variable, to
`unifyTerms`. The argument of `UnifyingDecides` carries over with one addition. The list of
the others, `(tail ...)`, is a term the two starting terms need not hold. It can be bound
to a variable and met again below a member. So it joins the members when it is made
(`covers_tail`): the members grow by at most one for each part of the written pattern,
and the fuel has room for that (`fuelFor` counts the written pattern once more).

* `covers_tail`: the cover is kept when the list of the others joins the members.
* `Each`, `lists_aux`, `pattern_aux`: the descent with its chain and its growing members.
* `unifyPattern_decides`, `unifyAsPattern_decides`, `unifyBinding_decides`,
  `unifyArguments_decides`.

Positive and negative examples: `Controls.view_met_again_decides` (the list of the others
is bound to a variable, met again inside a later argument, and the unifier decides);
`Controls.view_short_of_fuel` (with fuel 3 the same unification runs out: the bound is
used); `Controls.cyclic_binding_pattern_runs_out` (on a substitution that is not idempotent
the pattern unifier runs out with the fuel it is given: the hypothesis is used).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)
open Mettapedia.Languages.ProcessCalculi

/-! ## Members -/

theorem Below.tail {u head : Atom} {tail : List Atom} (below : Below u (.expression tail)) :
    Below u (.expression (head :: tail)) := by
  cases below with
  | child member => exact .child (List.mem_cons_of_mem _ member)
  | deeper member inner => exact .deeper (List.mem_cons_of_mem _ member) inner

theorem resolve_expression (bindings : Subst) (items : List Atom) :
    resolve bindings (.expression items) = .expression (items.map (resolve bindings)) :=
  applySubst_expression bindings items

/-- Terms equal under a substitution are equal under one that refines it. -/
theorem Refines.same {earlier later : Subst} (refines : Refines earlier later) {a c : Atom}
    (same : resolve earlier a = resolve earlier c) : resolve later a = resolve later c := by
  rw [← refines a, ← refines c, same]

/-- A member whose resolved form is that of an item of a list a member resolves as. -/
theorem covers_item {bindings : Subst} {S : List Atom} (covers : Covers bindings S)
    {holder : Atom} {items : List Atom} (inS : holder ∈ S)
    (shape : resolve bindings holder = resolve bindings (.expression items))
    {item : Atom} (member : item ∈ items) :
    ∃ s ∈ S, resolve bindings s = resolve bindings item ∧
      Below (resolve bindings s) (resolve bindings holder) := by
  have below : Below (resolve bindings item) (resolve bindings holder) := by
    rw [shape, resolve_expression]
    exact .child (List.mem_map_of_mem member)
  obtain ⟨s, inS', same⟩ := covers holder inS (resolve bindings item) below
  exact ⟨s, inS', same, same ▸ below⟩

/-- **The list of the others can join the members.** When a member resolves as a list with
a first item, the list of its other items, added as a member, keeps the cover: what lies
below it lies below that member. -/
theorem covers_tail {bindings : Subst} {S : List Atom} (covers : Covers bindings S)
    {holder head : Atom} {tail : List Atom} (inS : holder ∈ S)
    (shape : resolve bindings holder = resolve bindings (.expression (head :: tail))) :
    Covers bindings (.expression tail :: S) := by
  intro s member u below
  rcases List.mem_cons.mp member with same | old
  · subst same
    rw [resolve_expression] at below
    have inHolder : Below u (resolve bindings holder) := by
      rw [shape, resolve_expression, List.map_cons]
      exact below.tail
    obtain ⟨s', inS', same⟩ := covers holder inS u inHolder
    exact ⟨s', List.mem_cons_of_mem _ inS', same⟩
  · obtain ⟨s', inS', same⟩ := covers s old u below
    exact ⟨s', List.mem_cons_of_mem _ inS', same⟩

/-- A resolved list is the list of its resolved items. -/
theorem resolved_items {bindings : Subst} (idempotent : Idempotent bindings) {term : Atom}
    {items : List Atom} (shape : resolve bindings term = .expression items) :
    resolve bindings (.expression items) = .expression items := by
  rw [← shape]
  exact resolve_idem idempotent term

/-! ## The descent -/

/-- The statement of the descent at one fuel: inside the members `outers`, with fuel for the
members not yet entered and for the members the written pattern can add, `unifyPattern`
does not run out, and a unifier it returns keeps the cover over members that grew by no
more than the pattern is large. -/
def Each (fuel : Nat) : Prop :=
  ∀ (bindings : Subst) (pattern value : Atom) (S outers : List Atom) (sp sv : Atom),
    Idempotent bindings → Covers bindings S →
    sp ∈ S → resolve bindings sp = resolve bindings pattern →
    sv ∈ S → resolve bindings sv = resolve bindings value →
    (∀ outer ∈ outers, outer ∈ S) → Chain bindings outers sp →
    S.length + atomSize pattern ≤ fuel + outers.length →
    unifyPattern fuel bindings pattern value ≠ .exhausted ∧
      ∀ bound, unifyPattern fuel bindings pattern value = .ok bound →
        ∃ S₂, (∀ s ∈ S, s ∈ S₂) ∧ S₂.length ≤ S.length + atomSize pattern ∧ Covers bound S₂

/-- A part of the descent handed to `unifyTerms`. -/
theorem terms_part {fuel : Nat} {bindings : Subst} {pattern value : Atom} {S outers : List Atom}
    {sp sv : Atom} (idempotent : Idempotent bindings) (covers : Covers bindings S)
    (spIn : sp ∈ S) (spSame : resolve bindings sp = resolve bindings pattern)
    (svIn : sv ∈ S) (svSame : resolve bindings sv = resolve bindings value)
    (outersIn : ∀ outer ∈ outers, outer ∈ S) (chain : Chain bindings outers sp)
    (enough : S.length + atomSize pattern ≤ fuel + 1 + outers.length) :
    unifyTerms fuel bindings pattern value ≠ .exhausted ∧
      ∀ bound, unifyTerms fuel bindings pattern value = .ok bound →
        ∃ S₂, (∀ s ∈ S, s ∈ S₂) ∧ S₂.length ≤ S.length + atomSize pattern ∧ Covers bound S₂ := by
  have positive := atomSize_pos pattern
  obtain ⟨decides, keeps⟩ := decides_aux S fuel bindings sp sv outers idempotent covers spIn svIn
    outersIn chain (by omega)
  rw [unifyTerms_congr fuel bindings spSame svSame] at decides keeps
  exact ⟨decides, fun bound unified =>
    ⟨S, fun _ member => member, Nat.le_add_right _ _, keeps bound unified⟩⟩

/-- **The items of two lists, one after another**, each under the member the lists are
items of: the members grow by no more than the patterns are large. -/
theorem lists_aux {fuel : Nat} (each : Each fuel) {bindings : Subst} {S outers : List Atom}
    {sp sv : Atom} {patterns values : List Atom}
    (spIn : sp ∈ S) (spShape : resolve bindings sp = resolve bindings (.expression patterns))
    (svIn : sv ∈ S) (svShape : resolve bindings sv = resolve bindings (.expression values))
    (outersIn : ∀ outer ∈ outers, outer ∈ S) (chain : Chain bindings outers sp) :
    ∀ (items others : List Atom) (current : Subst) (Sc : List Atom),
      Idempotent current → Refines bindings current → Covers current Sc →
      (∀ s ∈ S, s ∈ Sc) → (∀ item ∈ items, item ∈ patterns) →
      (∀ other ∈ others, other ∈ values) →
      Sc.length + atomSize.listSize items ≤ fuel + outers.length →
      unifyLists (unifyPattern fuel) current items others ≠ .exhausted ∧
        ∀ bound, unifyLists (unifyPattern fuel) current items others = .ok bound →
          ∃ S₂, (∀ s ∈ Sc, s ∈ S₂) ∧ S₂.length ≤ Sc.length + atomSize.listSize items ∧
            Covers bound S₂ := by
  intro items
  induction items with
  | nil =>
      intro others current Sc _ _ covers _ _ _ _
      cases others with
      | nil =>
          refine ⟨by simp [unifyLists], fun bound same => ?_⟩
          simp only [unifyLists, Unified.ok.injEq] at same
          exact ⟨Sc, fun _ member => member, Nat.le_add_right _ _, same ▸ covers⟩
      | cons _ _ => exact ⟨by simp [unifyLists], fun bound same => by simp [unifyLists] at same⟩
  | cons first rest restIh =>
      intro others current Sc idempotent refines covers grown itemsIn othersIn enough
      cases others with
      | nil => exact ⟨by simp [unifyLists], fun bound same => by simp [unifyLists] at same⟩
      | cons other remaining =>
          have sizes : atomSize.listSize (first :: rest) = atomSize first + atomSize.listSize rest :=
            rfl
          obtain ⟨sf, sfIn, sfSame, sfBelow⟩ := covers_item covers (grown sp spIn)
            (refines.same spShape) (itemsIn first List.mem_cons_self)
          obtain ⟨so, soIn, soSame, _⟩ := covers_item covers (grown sv svIn)
            (refines.same svShape) (othersIn other List.mem_cons_self)
          obtain ⟨decides, keeps⟩ := each current first other Sc (sp :: outers) sf so idempotent
            covers sfIn sfSame soIn soSame
            (fun outer member => by
              rcases List.mem_cons.mp member with same | later
              · exact same ▸ grown sp spIn
              · exact grown outer (outersIn outer later))
            ⟨sfBelow, chain.refine refines⟩ (by simp only [List.length_cons]; omega)
          simp only [unifyLists]
          cases step : unifyPattern fuel current first other with
          | clash => exact ⟨by simp, fun bound same => by simp at same⟩
          | exhausted => exact absurd step decides
          | ok middle =>
              simp only [Unified.ok_andThen]
              obtain ⟨S₁, grown₁, length₁, covers₁⟩ := keeps middle step
              obtain ⟨middleIdempotent, middleRefines⟩ :=
                unifyPattern_refines fuel current middle first other idempotent step
              obtain ⟨laterDecides, laterKeeps⟩ := restIh remaining middle S₁ middleIdempotent
                (refines.trans middleRefines) covers₁ (fun s member => grown₁ s (grown s member))
                (fun item member => itemsIn item (List.mem_cons_of_mem _ member))
                (fun item member => othersIn item (List.mem_cons_of_mem _ member)) (by omega)
              refine ⟨laterDecides, fun bound unified => ?_⟩
              obtain ⟨S₂, grown₂, length₂, covers₂⟩ := laterKeeps bound unified
              exact ⟨S₂, fun s member => grown₂ s (grown₁ s member), by omega, covers₂⟩

theorem atomSize_view (first rest : Atom) :
    atomSize (.expression [.symbol "cons", first, rest]) = atomSize first + atomSize rest + 2 := by
  simp [atomSize, atomSize.listSize]
  omega

/-- **The descent of the pattern unifier.** -/
theorem pattern_aux : ∀ fuel : Nat, Each fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro bindings pattern value S outers sp sv _ _ spIn _ _ _ outersIn chain enough
      have short := chain.length_lt spIn outersIn
      have positive := atomSize_pos pattern
      omega
  | succ fuel ih =>
      intro bindings pattern value S outers sp sv idempotent covers spIn spSame svIn svSame
        outersIn chain enough
      have viaTerms := terms_part idempotent covers spIn spSame svIn svSame outersIn chain enough
      simp only [unifyPattern]
      split
      · -- the list view against a list with a first item
        rename_i first rest head tail valueShape
        have sizes := atomSize_view first rest
        have svShape : resolve bindings sv = resolve bindings (.expression (head :: tail)) := by
          rw [svSame, valueShape, resolved_items idempotent valueShape]
        have spShape : resolve bindings sp =
            resolve bindings (.expression [.symbol "cons", first, rest]) := spSame
        obtain ⟨sf, sfIn, sfSame, sfBelow⟩ := covers_item covers spIn spShape
          (item := first) (by simp)
        obtain ⟨sh, shIn, shSame, _⟩ := covers_item covers svIn svShape
          (item := head) List.mem_cons_self
        have inChain : ∀ outer ∈ sp :: outers, outer ∈ S := by
          intro outer member
          rcases List.mem_cons.mp member with same | later
          · exact same ▸ spIn
          · exact outersIn outer later
        obtain ⟨decides, keeps⟩ := ih bindings first head S (sp :: outers) sf sh idempotent covers
          sfIn sfSame shIn shSame inChain ⟨sfBelow, chain⟩
          (by simp only [List.length_cons]; omega)
        cases step : unifyPattern fuel bindings first head with
        | clash => exact ⟨by simp, fun bound same => by simp at same⟩
        | exhausted => exact absurd step decides
        | ok middle =>
            simp only [Unified.ok_andThen]
            obtain ⟨S₁, grown₁, length₁, covers₁⟩ := keeps middle step
            obtain ⟨middleIdempotent, middleRefines⟩ :=
              unifyPattern_refines fuel bindings middle first head idempotent step
            have coversTail : Covers middle (.expression tail :: S₁) :=
              covers_tail covers₁ (grown₁ sv svIn) (middleRefines.same svShape)
            obtain ⟨sr, srIn, srSame, srBelow⟩ := covers_item covers₁ (grown₁ sp spIn)
              (middleRefines.same spShape) (item := rest) (by simp)
            obtain ⟨laterDecides, laterKeeps⟩ := ih middle rest (.expression tail)
              (.expression tail :: S₁) (sp :: outers) sr (.expression tail) middleIdempotent
              coversTail (List.mem_cons_of_mem _ srIn) srSame List.mem_cons_self rfl
              (fun outer member => List.mem_cons_of_mem _ (grown₁ outer (inChain outer member)))
              ⟨srBelow, chain.refine middleRefines⟩
              (by simp only [List.length_cons]; omega)
            refine ⟨laterDecides, fun bound unified => ?_⟩
            obtain ⟨S₂, grown₂, length₂, covers₂⟩ := laterKeeps bound unified
            refine ⟨S₂, fun s member => grown₂ s (List.mem_cons_of_mem _ (grown₁ s member)), ?_,
              covers₂⟩
            simp only [List.length_cons] at length₂
            omega
      · exact viaTerms
      · exact ⟨by simp, fun bound same => by simp at same⟩
      · -- two lists, item by item
        rename_i patterns values _ _ valueShape
        have svShape : resolve bindings sv = resolve bindings (.expression values) := by
          rw [svSame, valueShape, resolved_items idempotent valueShape]
        have sizes : atomSize (.expression patterns) = atomSize.listSize patterns + 1 := rfl
        obtain ⟨decides, keeps⟩ := lists_aux ih spIn spSame svIn svShape outersIn chain patterns
          values bindings S idempotent (Refines.refl idempotent) covers (fun _ member => member)
          (fun _ member => member) (fun _ member => member) (by omega)
        refine ⟨decides, fun bound unified => ?_⟩
        obtain ⟨S₂, grown, length, covers₂⟩ := keeps bound unified
        exact ⟨S₂, grown, by omega, covers₂⟩
      · exact viaTerms
      · exact ⟨by simp, fun bound same => by simp at same⟩
      · exact viaTerms

/-! ## The theorems -/

/-- **The pattern unifier decides.** On an idempotent substitution, with fuel for the sizes
of the two resolved terms and of the written pattern, `unifyPattern` answers a unifier or a
clash. -/
theorem unifyPattern_decides (fuel : Nat) (bindings : Subst) (pattern value : Atom)
    (idempotent : Idempotent bindings)
    (enough : atomSize (resolve bindings pattern) + atomSize (resolve bindings value) +
      atomSize pattern ≤ fuel) :
    unifyPattern fuel bindings pattern value ≠ .exhausted :=
  (pattern_aux fuel bindings pattern value
    (subterms (resolve bindings pattern) ++ subterms (resolve bindings value)) []
    (resolve bindings pattern) (resolve bindings value) idempotent
    (covers_subterms idempotent pattern value)
    (List.mem_append_left _ (self_mem_subterms _)) (resolve_idem idempotent pattern)
    (List.mem_append_right _ (self_mem_subterms _)) (resolve_idem idempotent value)
    (fun _ member => by cases member) trivial
    (by simp only [List.length_append, length_subterms, List.length_nil]; omega)).1

/-- **A pattern with the list view never runs out of fuel** on an idempotent substitution. -/
theorem unifyAsPattern_decides (bindings : Subst) (pattern value : Atom)
    (idempotent : Idempotent bindings) : unifyAsPattern bindings pattern value ≠ .exhausted := by
  unfold unifyAsPattern
  exact unifyPattern_decides _ bindings pattern value idempotent (by unfold fuelFor; omega)

/-- **A `let` pattern never runs out of fuel** on an idempotent substitution. -/
theorem unifyBinding_decides (bindings : Subst) (pattern value : Atom)
    (idempotent : Idempotent bindings) : unifyBinding bindings pattern value ≠ .exhausted := by
  unfold unifyBinding
  split
  · exact unify_decides bindings _ value idempotent
  · exact unifyAsPattern_decides bindings pattern value idempotent

/-- **A call's arguments against an equation's argument patterns never run out of fuel** on
an idempotent substitution. -/
theorem unifyArguments_decides (bindings : Subst) (patterns values : List Atom)
    (idempotent : Idempotent bindings) : unifyArguments bindings patterns values ≠ .exhausted := by
  unfold unifyArguments
  have sizes : atomSize (.expression patterns) = atomSize.listSize patterns + 1 := rfl
  exact (lists_aux (pattern_aux _)
    (S := subterms (resolve bindings (.expression patterns)) ++
      subterms (resolve bindings (.expression values)))
    (outers := []) (sp := resolve bindings (.expression patterns))
    (sv := resolve bindings (.expression values))
    (List.mem_append_left _ (self_mem_subterms _)) (resolve_idem idempotent _)
    (List.mem_append_right _ (self_mem_subterms _)) (resolve_idem idempotent _)
    (fun _ member => by cases member) trivial patterns values bindings _ idempotent
    (Refines.refl idempotent) (covers_subterms idempotent _ _) (fun _ member => member)
    (fun _ member => member) (fun _ member => member)
    (by
      simp only [List.length_append, length_subterms, List.length_nil]
      unfold fuelFor
      omega)).1

namespace Controls

/-- `(f (cons $h $r) (g $r))` against `(f (a b c) (g (b d)))`: the list of the others,
`(b c)`, is in neither term; it is bound to `$r` and met again inside the second argument. -/
def viewAgain : Atom × Atom :=
  (.expression [.symbol "f", .expression [.symbol "cons", .var "h", .var "r"],
     .expression [.symbol "g", .var "r"]],
   .expression [.symbol "f", .expression [.symbol "a", .symbol "b", .symbol "c"],
     .expression [.symbol "g", .expression [.symbol "b", .symbol "d"]]])

/-- Positive: the pattern unifier decides it (a clash, `c` against `d`). -/
theorem view_met_again_decides : unifyAsPattern [] viewAgain.1 viewAgain.2 = .clash := by
  decide +kernel

/-- Negative: with fuel 3 the same unification runs out, so the bound on fuel is used. -/
theorem view_short_of_fuel : unifyPattern 3 [] viewAgain.1 viewAgain.2 = .exhausted := by
  decide +kernel

/-- Negative: on the cyclic binding of `UnifyingDecides`, which is not idempotent, the
pattern unifier runs out with the fuel it is given. -/
theorem cyclic_binding_pattern_runs_out :
    unifyAsPattern cyclic (.var "x") (.var "x") = .exhausted := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
