import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge

/-!
# Atom Zipper: Huet-style one-hole context for MORK Atoms

Formalizes a concrete zipper over `Atom` for focused sub-expression navigation
and replacement. Based on the Rust `ExprZipper` in `MORK/expr/src/lib.rs`.

## Architecture

- `AtomCrumb`: one level of context (left siblings reversed + right siblings)
- `AtomContext`: stack of crumbs from focus to root
- `AtomZipper`: focus atom + context
- Navigation: `descendExprChild?`, `ascend?`, `focusAtPath?`
- Replacement: `replaceFocus`, `replaceAtPath?`
- Round-trip proofs: descend/ascend preserve rebuild, focusAtPath rebuild = original

## Lens Laws

`LensRel whole part newPart newWhole` witnesses that `part` is a sub-expression
of `whole`, and replacing it with `newPart` yields `newWhole`. Proven: get-put,
put-get, put-put (same context).

## Collection Specialization

MORK collections are `.expression (symbol :: elems)`. Collection element at
logical index `i` lives at expression child `i+1`. Theorems connect zipper
replacement at path `[i+1]` with `List.set i`.

## LLM Notes
- `morkPatternToAtomList_eq_map` is reproven here (not imported from CollectionBridge)
  because CollectionBridge will depend on AtomZipper, not the other way.
- `left` in `AtomCrumb` is stored reversed for O(1) cons (classic Huet zipper).
- `List.set_eq_take_cons_drop` is the key identity for collection replacement.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Core types -/

/-- One-hole context for a single level of `Atom.expression`.
    `left` is stored reversed (closest sibling to hole first) for O(1) cons. -/
structure AtomCrumb where
  left  : List Atom
  right : List Atom
  deriving Repr, Inhabited, DecidableEq

/-- A path from the focus to the root: stack of crumbs. -/
abbrev AtomContext := List AtomCrumb

/-- Huet zipper over Atom: a focus sub-expression plus its surrounding context. -/
@[ext] structure AtomZipper where
  focus : Atom
  ctx   : AtomContext
  deriving Repr, Inhabited, DecidableEq

/-! ## Reconstruction -/

/-- Plug a single crumb: reassemble the expression with the atom in the hole. -/
def plugCrumb (a : Atom) (c : AtomCrumb) : Atom :=
  .expression (c.left.reverse ++ [a] ++ c.right)

/-- Rebuild the full atom from focus outward through the context. -/
def rebuild (z : AtomZipper) : Atom :=
  z.ctx.foldl plugCrumb z.focus

/-- Replace the focus, keeping context. -/
def replaceFocus (z : AtomZipper) (newFocus : Atom) : AtomZipper :=
  { z with focus := newFocus }

@[simp] theorem replaceFocus_focus (z : AtomZipper) (a : Atom) :
    (replaceFocus z a).focus = a := rfl

@[simp] theorem replaceFocus_ctx (z : AtomZipper) (a : Atom) :
    (replaceFocus z a).ctx = z.ctx := rfl

/-! ## Navigation -/

/-- Focus on the `i`-th child of an expression.
    Returns `none` for non-expressions or out-of-bounds index. -/
def descendExprChild? (z : AtomZipper) (i : Nat) : Option AtomZipper :=
  match z.focus with
  | .expression children =>
    if h : i < children.length then
      some {
        focus := children[i]
        ctx   := ⟨(children.take i).reverse, children.drop (i + 1)⟩ :: z.ctx
      }
    else none
  | _ => none

/-- Move focus back to parent expression. -/
def ascend? (z : AtomZipper) : Option AtomZipper :=
  match z.ctx with
  | c :: rest => some { focus := plugCrumb z.focus c, ctx := rest }
  | []        => none

/-- Focus at a path of child indices, starting from a root atom. -/
def focusAtPath? (a : Atom) (path : List Nat) : Option AtomZipper :=
  path.foldlM (fun z i => descendExprChild? z i) ⟨a, []⟩

/-- Replace the sub-expression at a path and rebuild to root. -/
def replaceAtPath? (a : Atom) (path : List Nat) (newFocus : Atom) : Option Atom :=
  (focusAtPath? a path).map (fun z => rebuild (replaceFocus z newFocus))

/-! ## Round-trip proofs -/

private theorem take_append_getElem_drop (l : List α) (i : Nat) (hi : i < l.length) :
    l.take i ++ [l[i]] ++ l.drop (i + 1) = l := by
  rw [List.append_assoc, List.singleton_append,
      List.cons_getElem_drop_succ (h := hi), List.take_append_drop]

/-- Descending preserves rebuild: the full atom is unchanged. -/
theorem rebuild_descendExprChild (z : AtomZipper) (i : Nat) (z' : AtomZipper)
    (h : descendExprChild? z i = some z') : rebuild z' = rebuild z := by
  unfold descendExprChild? at h
  match hf : z.focus with
  | .expression cs =>
    simp [hf] at h
    obtain ⟨hi, rfl⟩ := h
    simp only [rebuild, List.foldl, plugCrumb, List.reverse_reverse]
    congr 1
    rw [take_append_getElem_drop cs i hi, ← hf]
  | .symbol _ | .var _ | .grounded _ => simp [hf] at h

/-- Ascending preserves rebuild: the full atom is unchanged. -/
theorem rebuild_ascend (z : AtomZipper) (z' : AtomZipper)
    (h : ascend? z = some z') : rebuild z' = rebuild z := by
  simp only [ascend?] at h
  split at h
  · rename_i c rest heq
    simp at h; obtain ⟨rfl, rfl⟩ := h
    simp only [rebuild, heq, List.foldl]
  · simp at h

/-- Helper: descending through a path preserves rebuild at each step. -/
private theorem foldlM_descendExprChild_rebuild
    (path : List Nat) (z z' : AtomZipper)
    (h : path.foldlM (fun z i => descendExprChild? z i) z = some z') :
    rebuild z' = rebuild z := by
  induction path generalizing z with
  | nil => simp [List.foldlM] at h; exact h ▸ rfl
  | cons i rest ih =>
    simp only [List.foldlM] at h
    -- h : (do let s' ← descendExprChild? z i; foldlM ... s' rest) = some z'
    match hd : descendExprChild? z i with
    | none => simp [hd] at h
    | some z_mid =>
      simp [hd] at h
      rw [ih z_mid h, rebuild_descendExprChild z i z_mid hd]

/-- Focusing at a path and rebuilding gives back the original atom. -/
theorem focusAtPath_rebuild (a : Atom) (path : List Nat) (z : AtomZipper)
    (h : focusAtPath? a path = some z) : rebuild z = a := by
  simp only [focusAtPath?] at h
  rw [foldlM_descendExprChild_rebuild path ⟨a, []⟩ z h]
  rfl

/-- `replaceAtPath?` factors through `focusAtPath?` + `replaceFocus` + `rebuild`. -/
theorem replaceAtPath_spec (a : Atom) (path : List Nat) (newFocus : Atom) (a' : Atom)
    (h : replaceAtPath? a path newFocus = some a') :
    ∃ z, focusAtPath? a path = some z ∧ a' = rebuild (replaceFocus z newFocus) := by
  simp only [replaceAtPath?, Option.map_eq_some_iff] at h
  obtain ⟨z, hz, ha'⟩ := h
  exact ⟨z, hz, ha'.symm⟩

/-! ## Lens relation -/

/-- A lens relation witnessing that `part` is a sub-expression of `whole`,
    and replacing it with `newPart` yields `newWhole`.
    Matches the MM2 schema: `(lens name whole part newpart newwhole)`. -/
def LensRel (whole part newPart newWhole : Atom) : Prop :=
  ∃ z : AtomZipper, rebuild z = whole ∧ z.focus = part ∧
    rebuild (replaceFocus z newPart) = newWhole

/-- Get-Put: replacing the focus with itself recovers the original. -/
theorem lensRel_get_put {whole part whole' : Atom}
    (h : LensRel whole part part whole') : whole' = whole := by
  obtain ⟨z, hz_whole, hz_part, hz_new⟩ := h
  simp only [replaceFocus] at hz_new
  have : ({ focus := part, ctx := z.ctx } : AtomZipper) = z := by
    ext <;> simp [hz_part]
  rw [this] at hz_new
  exact hz_new ▸ hz_whole

/-- Put-Get: after replacement, we can focus on the new value. -/
theorem lensRel_put_get {whole part newPart newWhole : Atom}
    (h : LensRel whole part newPart newWhole) :
    ∃ z' : AtomZipper, rebuild z' = newWhole ∧ z'.focus = newPart := by
  obtain ⟨z, _, _, hz_new⟩ := h
  exact ⟨replaceFocus z newPart, hz_new, rfl⟩

/-- Put-Put: any replacement at the same zipper context produces a valid LensRel. -/
theorem lensRel_put_put (z : AtomZipper) (newPart : Atom) :
    LensRel (rebuild z) z.focus newPart (rebuild (replaceFocus z newPart)) :=
  ⟨z, rfl, rfl, rfl⟩

/-! ## Collection specialization -/

private abbrev ILP := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILCT := Mettapedia.OSLF.MeTTaIL.Syntax.CollType

/-- `morkPatternToAtomList` is `List.map morkPatternToAtom`.
    (Reproven here to avoid circular dependency with CollectionBridge.) -/
private theorem morkPatternToAtomList_eq_map (elems : List ILP) :
    morkPatternToAtom.morkPatternToAtomList elems = elems.map morkPatternToAtom := by
  induction elems with
  | nil => rfl
  | cons p ps ih =>
    simp only [morkPatternToAtom.morkPatternToAtomList, List.map_cons, ih]

/-- The expression-child index for logical collection index `i`.
    MORK collections are `.expression (symbol :: elems)`, so element `i` is child `i+1`. -/
abbrev collChildIdx (i : Nat) : Nat := i + 1

/-- Helper: `descendExprChild?` on `.expression (hd :: tl)` at index `i+1`. -/
private theorem descendExprChild_collection_aux
    (hd : Atom) (tl : List Atom) (ctx : AtomContext)
    (i : Nat) (hi : i < tl.length) :
    descendExprChild? ⟨.expression (hd :: tl), ctx⟩ (i + 1) =
    some ⟨tl[i], ⟨(tl.take i).reverse ++ [hd], tl.drop (i + 1)⟩ :: ctx⟩ := by
  simp only [descendExprChild?]
  have hlen : i + 1 < (hd :: tl).length := by simp; omega
  rw [dif_pos hlen]
  congr 1
  · simp [List.getElem_cons_succ, List.take_succ_cons, List.reverse_cons,
         List.drop_succ_cons]

/-- Focusing on path `[i+1]` in a translated collection yields the i-th element. -/
theorem focusAtPath_collection (ct : ILCT) (elems : List ILP) (i : Nat)
    (hi : i < elems.length) :
    ∃ z, focusAtPath? (morkPatternToAtom (.collection ct elems none)) [collChildIdx i] = some z ∧
      z.focus = morkPatternToAtom elems[i] := by
  simp only [focusAtPath?, collChildIdx, List.foldlM, Option.pure_def]
  simp only [morkPatternToAtom, morkPatternToAtomList_eq_map]
  have hi' : i < (elems.map morkPatternToAtom).length := by simp; exact hi
  rw [descendExprChild_collection_aux (.symbol (morkCollTypeSymbol ct))
      (elems.map morkPatternToAtom) [] i hi']
  exact ⟨_, rfl, by simp [List.getElem_map]⟩

/-- Replacing at path `[i+1]` in a translated collection = translating `List.set`. -/
theorem replaceAtPath_collection (ct : ILCT) (elems : List ILP) (i : Nat)
    (hi : i < elems.length) (q' : ILP) :
    replaceAtPath? (morkPatternToAtom (.collection ct elems none)) [collChildIdx i]
        (morkPatternToAtom q') =
    some (morkPatternToAtom (.collection ct (elems.set i q') none)) := by
  simp only [replaceAtPath?, focusAtPath?, collChildIdx, List.foldlM, Option.pure_def,
             morkPatternToAtom, morkPatternToAtomList_eq_map, Option.map_eq_some_iff]
  have hi' : i < (elems.map morkPatternToAtom).length := by simp; exact hi
  rw [descendExprChild_collection_aux (.symbol (morkCollTypeSymbol ct))
      (elems.map morkPatternToAtom) [] i hi']
  refine ⟨_, rfl, ?_⟩
  simp only [rebuild, replaceFocus, List.foldl, plugCrumb, List.reverse_reverse,
             List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append]
  congr 1
  rw [List.append_assoc, List.singleton_append, List.cons_append,
      ← List.set_eq_take_cons_drop (morkPatternToAtom q') hi',
      List.map_set]

/-- Collection element update satisfies `LensRel`. -/
theorem collection_lensRel (ct : ILCT) (elems : List ILP) (i : Nat)
    (hi : i < elems.length) (q' : ILP) :
    LensRel
      (morkPatternToAtom (.collection ct elems none))
      (morkPatternToAtom elems[i])
      (morkPatternToAtom q')
      (morkPatternToAtom (.collection ct (elems.set i q') none)) := by
  obtain ⟨z, hz_path, hz_focus⟩ := focusAtPath_collection ct elems i hi
  refine ⟨z, focusAtPath_rebuild _ _ z hz_path, hz_focus, ?_⟩
  have hrep := replaceAtPath_collection ct elems i hi q'
  simp only [replaceAtPath?, Option.map_eq_some_iff] at hrep
  obtain ⟨z', hz'_path, hz'_eq⟩ := hrep
  -- z and z' are both obtained from focusAtPath? at [collChildIdx i], so z' = z
  have : focusAtPath? (morkPatternToAtom (.collection ct elems none)) [collChildIdx i] = some z :=
    hz_path
  rw [this] at hz'_path
  simp only [Option.some.injEq] at hz'_path
  rw [← hz'_eq, hz'_path]

end Mettapedia.Languages.ProcessCalculi.MORK
