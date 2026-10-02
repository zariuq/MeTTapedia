import Mettapedia.Computability.CourseOfValues
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# Rewriting patterns from the leaves up, on codes

`Pattern.bottomUp operation` rewrites a pattern from the leaves up: the
sub-patterns first, then `operation` at the node.  A normalizer that reduces
a node once its components are normal has this form.

The structural code of a pattern determines the codes of its immediate
sub-patterns, and each of them is smaller than the code of the pattern.  So
a bottom-up rewriting is a course-of-values recursion on codes: replace the
codes of the sub-patterns by the values already computed, then apply the
operation.  If the operation is tracked by a primitive recursive function on
codes, so is the whole rewriting (`bottomUpCode_primrec`,
`bottomUpCode_patternCode`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- Apply a function to the immediate sub-patterns of a pattern. -/
def mapChildren (image : Pattern → Pattern) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => .apply label (arguments.map image)
  | .lambda binder body => .lambda binder (image body)
  | .multiLambda arity binders body => .multiLambda arity binders (image body)
  | .subst body replacement => .subst (image body) (image replacement)
  | .collection kind elements rest => .collection kind (elements.map image) rest

mutual
  /-- Rewrite a pattern from the leaves up: the sub-patterns first, then the
  operation at the node. -/
  def bottomUp (operation : Pattern → Pattern) : Pattern → Pattern
    | .bvar index => operation (.bvar index)
    | .fvar name => operation (.fvar name)
    | .apply label arguments => operation (.apply label (bottomUpList operation arguments))
    | .lambda binder body => operation (.lambda binder (bottomUp operation body))
    | .multiLambda arity binders body =>
        operation (.multiLambda arity binders (bottomUp operation body))
    | .subst body replacement =>
        operation (.subst (bottomUp operation body) (bottomUp operation replacement))
    | .collection kind elements rest =>
        operation (.collection kind (bottomUpList operation elements) rest)

  /-- Rewrite every member of a list from the leaves up. -/
  def bottomUpList (operation : Pattern → Pattern) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => bottomUp operation pattern :: bottomUpList operation patterns
end

@[simp] theorem bottomUpList_eq_map (operation : Pattern → Pattern) (patterns : List Pattern) :
    bottomUpList operation patterns = patterns.map (bottomUp operation) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [bottomUpList, recurse]

/-- **The recursion equation**: rewrite the immediate sub-patterns, then
apply the operation. -/
theorem bottomUp_eq (operation : Pattern → Pattern) (pattern : Pattern) :
    bottomUp operation pattern = operation (mapChildren (bottomUp operation) pattern) := by
  cases pattern <;> simp [bottomUp, mapChildren]

end Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

namespace Mettapedia.OSLF.MeTTaIL.PatternCode

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Computability

/-! ## Codes of lists and of sub-patterns -/

/-- The code of a list of patterns is the standard code of the list of their
codes. -/
theorem patternListCode_eq_encode (patterns : List Pattern) :
    patternListCode patterns = Encodable.encode (patterns.map patternCode) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [patternListCode, recurse]

/-- Decoding the code of a list of patterns gives the list of their codes. -/
theorem ofNat_patternListCode (patterns : List Pattern) :
    Denumerable.ofNat (List ℕ) (patternListCode patterns) = patterns.map patternCode := by
  rw [patternListCode_eq_encode, Denumerable.ofNat_encode]

/-- The second component of a pair with a positive first component is
smaller than the pair. -/
theorem lt_pair_of_pos {tag : ℕ} (positive : 0 < tag) (payload : ℕ) :
    payload < Nat.pair tag payload := by
  unfold Nat.pair
  split
  · exact (Nat.le_mul_self payload).trans_lt (Nat.lt_add_of_pos_right positive)
  · exact Nat.lt_add_of_pos_left (Nat.add_pos_right _ positive)

/-- A member of a list of patterns has a smaller code than the list. -/
theorem patternCode_lt_patternListCode {pattern : Pattern} {patterns : List Pattern}
    (member : pattern ∈ patterns) : patternCode pattern < patternListCode patterns := by
  induction patterns with
  | nil => cases member
  | cons head tail recurse =>
      rw [patternListCode]
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.lt_succ_of_le (Nat.left_le_pair _ _)
      · exact Nat.lt_succ_of_le ((recurse later).le.trans (Nat.right_le_pair _ _))

theorem patternCode_lt_apply {label : String} {arguments : List Pattern} {pattern : Pattern}
    (member : pattern ∈ arguments) :
    patternCode pattern < patternCode (.apply label arguments) := by
  rw [patternCode]
  exact (patternCode_lt_patternListCode member).trans_le
    ((Nat.right_le_pair _ _).trans (lt_pair_of_pos (by decide) _).le)

theorem patternCode_lt_lambda (binder : Option String) (body : Pattern) :
    patternCode body < patternCode (.lambda binder body) := by
  rw [patternCode]
  exact (Nat.right_le_pair _ _).trans_lt (lt_pair_of_pos (by decide) _)

theorem patternCode_lt_multiLambda (arity : ℕ) (binders : List String) (body : Pattern) :
    patternCode body < patternCode (.multiLambda arity binders body) := by
  rw [patternCode]
  exact ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _)).trans_lt
    (lt_pair_of_pos (by decide) _)

theorem patternCode_lt_subst_body (body replacement : Pattern) :
    patternCode body < patternCode (.subst body replacement) := by
  rw [patternCode]
  exact (Nat.left_le_pair _ _).trans_lt (lt_pair_of_pos (by decide) _)

theorem patternCode_lt_subst_replacement (body replacement : Pattern) :
    patternCode replacement < patternCode (.subst body replacement) := by
  rw [patternCode]
  exact (Nat.right_le_pair _ _).trans_lt (lt_pair_of_pos (by decide) _)

theorem patternCode_lt_collection {kind : CollType} {elements : List Pattern}
    {rest : Option String} {pattern : Pattern} (member : pattern ∈ elements) :
    patternCode pattern < patternCode (.collection kind elements rest) := by
  rw [patternCode]
  exact (patternCode_lt_patternListCode member).trans_le
    (((Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _)).trans
      (lt_pair_of_pos (by decide) _).le)

/-! ## Looking sub-patterns up in a table -/

/-- Replace each member of an encoded list of codes by its entry in a table. -/
def lookupListCode (table : List ℕ) (listCode : ℕ) : ℕ :=
  Encodable.encode ((Denumerable.ofNat (List ℕ) listCode).map fun code => table.getD code 0)

/-- Replace the codes of the immediate sub-patterns inside a code by their
entries in a table. -/
def lookupChildrenCode (table : List ℕ) (code : ℕ) : ℕ :=
  if code.unpair.1 = 2 then
    Nat.pair 2 (Nat.pair code.unpair.2.unpair.1 (lookupListCode table code.unpair.2.unpair.2))
  else if code.unpair.1 = 3 then
    Nat.pair 3 (Nat.pair code.unpair.2.unpair.1 (table.getD code.unpair.2.unpair.2 0))
  else if code.unpair.1 = 4 then
    Nat.pair 4 (Nat.pair code.unpair.2.unpair.1
      (Nat.pair code.unpair.2.unpair.2.unpair.1
        (table.getD code.unpair.2.unpair.2.unpair.2 0)))
  else if code.unpair.1 = 5 then
    Nat.pair 5 (Nat.pair (table.getD code.unpair.2.unpair.1 0)
      (table.getD code.unpair.2.unpair.2 0))
  else if code.unpair.1 = 6 then
    Nat.pair 6 (Nat.pair code.unpair.2.unpair.1
      (Nat.pair (lookupListCode table code.unpair.2.unpair.2.unpair.1)
        code.unpair.2.unpair.2.unpair.2))
  else code

theorem lookupListCode_primrec : Primrec₂ lookupListCode := by
  have decoded : Primrec fun input : List ℕ × ℕ => Denumerable.ofNat (List ℕ) input.2 :=
    (Primrec.ofNat (List ℕ)).comp Primrec.snd
  have looked : Primrec₂ fun (input : List ℕ × ℕ) (code : ℕ) => input.1.getD code 0 :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.encode.comp (Primrec.list_map decoded looked)

theorem lookupChildrenCode_primrec : Primrec₂ lookupChildrenCode := by
  have table : Primrec fun input : List ℕ × ℕ => input.1 := Primrec.fst
  have tag : Primrec fun input : List ℕ × ℕ => input.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have payload : Primrec fun input : List ℕ × ℕ => input.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have first : Primrec fun input : List ℕ × ℕ => input.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp payload)
  have second : Primrec fun input : List ℕ × ℕ => input.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp payload)
  have third : Primrec fun input : List ℕ × ℕ => input.2.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp second)
  have fourth : Primrec fun input : List ℕ × ℕ => input.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp second)
  have entry : ∀ {position : List ℕ × ℕ → ℕ}, Primrec position →
      Primrec fun input : List ℕ × ℕ => input.1.getD (position input) 0 :=
    fun primitive => (Primrec.list_getD 0).comp table primitive
  have entries : ∀ {position : List ℕ × ℕ → ℕ}, Primrec position →
      Primrec fun input : List ℕ × ℕ => lookupListCode input.1 (position input) :=
    fun primitive => lookupListCode_primrec.comp table primitive
  have paired : ∀ {left right : List ℕ × ℕ → ℕ}, Primrec left → Primrec right →
      Primrec fun input : List ℕ × ℕ => Nat.pair (left input) (right input) :=
    fun leftPrimitive rightPrimitive => Primrec₂.natPair.comp leftPrimitive rightPrimitive
  have tagged : ∀ value : ℕ, PrimrecPred fun input : List ℕ × ℕ => input.2.unpair.1 = value :=
    fun value => Primrec.eq.comp tag (Primrec.const value)
  exact Primrec.ite (tagged 2)
      (paired (Primrec.const 2) (paired first (entries second)))
    (Primrec.ite (tagged 3)
      (paired (Primrec.const 3) (paired first (entry second)))
    (Primrec.ite (tagged 4)
      (paired (Primrec.const 4) (paired first (paired third (entry fourth))))
    (Primrec.ite (tagged 5)
      (paired (Primrec.const 5) (paired (entry first) (entry second)))
    (Primrec.ite (tagged 6)
      (paired (Primrec.const 6) (paired first (paired (entries third) fourth)))
      Primrec.snd))))

/-- Looking a list of patterns up in the table of a tracking function gives
the code of the list of their images. -/
theorem lookupListCode_eq {track : ℕ → ℕ} {image : Pattern → Pattern} {bound : ℕ}
    (patterns : List Pattern)
    (tracked : ∀ pattern ∈ patterns, patternCode pattern < bound ∧
      track (patternCode pattern) = patternCode (image pattern)) :
    lookupListCode ((List.range bound).map track) (patternListCode patterns) =
      patternListCode (patterns.map image) := by
  rw [lookupListCode, ofNat_patternListCode, patternListCode_eq_encode, List.map_map,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro pattern member
  obtain ⟨smaller, value⟩ := tracked pattern member
  simp only [Function.comp_apply]
  rw [getD_map_range track 0 smaller, value]

/-- **Looking the sub-patterns up.**  In the table of a function that tracks
`image` on every pattern with a smaller code, the code of a pattern becomes
the code of the pattern with `image` applied to its immediate sub-patterns. -/
theorem lookupChildrenCode_eq {track : ℕ → ℕ} {image : Pattern → Pattern} (pattern : Pattern)
    (tracked : ∀ child, patternCode child < patternCode pattern →
      track (patternCode child) = patternCode (image child)) :
    lookupChildrenCode ((List.range (patternCode pattern)).map track) (patternCode pattern) =
      patternCode (pattern.mapChildren image) := by
  cases pattern with
  | bvar index => simp [lookupChildrenCode, patternCode, Pattern.mapChildren]
  | fvar name => simp [lookupChildrenCode, patternCode, Pattern.mapChildren]
  | apply label arguments =>
      have members := lookupListCode_eq (track := track) (image := image)
        (bound := patternCode (.apply label arguments)) arguments
        fun child member =>
          ⟨patternCode_lt_apply member, tracked child (patternCode_lt_apply member)⟩
      simp only [patternCode] at members
      simp [lookupChildrenCode, patternCode, Pattern.mapChildren, members]
  | lambda binder body =>
      have value := tracked body (patternCode_lt_lambda binder body)
      have entry := getD_map_range track 0 (patternCode_lt_lambda binder body)
      simp only [patternCode] at entry
      simp only [lookupChildrenCode, patternCode, Pattern.mapChildren, Nat.unpair_pair, entry,
        value]
      rfl
  | multiLambda arity binders body =>
      have value := tracked body (patternCode_lt_multiLambda arity binders body)
      have entry := getD_map_range track 0 (patternCode_lt_multiLambda arity binders body)
      simp only [patternCode] at entry
      simp only [lookupChildrenCode, patternCode, Pattern.mapChildren, Nat.unpair_pair, entry,
        value]
      rfl
  | subst body replacement =>
      have bodyValue := tracked body (patternCode_lt_subst_body body replacement)
      have replacementValue :=
        tracked replacement (patternCode_lt_subst_replacement body replacement)
      have bodyEntry := getD_map_range track 0 (patternCode_lt_subst_body body replacement)
      have replacementEntry :=
        getD_map_range track 0 (patternCode_lt_subst_replacement body replacement)
      simp only [patternCode] at bodyEntry replacementEntry
      simp only [lookupChildrenCode, patternCode, Pattern.mapChildren, Nat.unpair_pair, bodyEntry,
        replacementEntry, bodyValue, replacementValue]
      rfl
  | collection kind elements rest =>
      have members := lookupListCode_eq (track := track) (image := image)
        (bound := patternCode (.collection kind elements rest)) elements
        fun child member =>
          ⟨patternCode_lt_collection member, tracked child (patternCode_lt_collection member)⟩
      simp only [patternCode] at members
      simp [lookupChildrenCode, patternCode, Pattern.mapChildren, members]

/-! ## Bottom-up rewriting on codes -/

/-- One step of a bottom-up rewriting on codes: look the sub-patterns up in
the table of earlier values, then apply the operation.  The code being
rewritten is the length of the table. -/
def bottomUpStep (operationCode : ℕ → ℕ) (table : List ℕ) : ℕ :=
  operationCode (lookupChildrenCode table table.length)

/-- The function on codes that tracks a bottom-up rewriting whose node
operation is tracked by `operationCode`. -/
def bottomUpCode (operationCode : ℕ → ℕ) : ℕ → ℕ :=
  courseOfValues (bottomUpStep operationCode)

/-- **A bottom-up rewriting is primitive recursive on codes** when its node
operation is. -/
theorem bottomUpCode_primrec {operationCode : ℕ → ℕ} (primitive : Primrec operationCode) :
    Primrec (bottomUpCode operationCode) := by
  apply courseOfValues_primrec
  exact primitive.comp (lookupChildrenCode_primrec.comp Primrec.id Primrec.list_length)

/-- **The function on codes tracks the rewriting.**  If `operationCode`
tracks `operation` on the code of every pattern, then `bottomUpCode
operationCode` tracks `bottomUp operation`. -/
theorem bottomUpCode_patternCode {operation : Pattern → Pattern} {operationCode : ℕ → ℕ}
    (tracks : ∀ pattern, operationCode (patternCode pattern) = patternCode (operation pattern))
    (pattern : Pattern) :
    bottomUpCode operationCode (patternCode pattern) =
      patternCode (pattern.bottomUp operation) := by
  induction bound : patternCode pattern using Nat.strong_induction_on generalizing pattern with
  | _ bound recurse =>
      subst bound
      have step : bottomUpCode operationCode (patternCode pattern) =
          operationCode (lookupChildrenCode
            ((List.range (patternCode pattern)).map (bottomUpCode operationCode))
            (patternCode pattern)) := by
        rw [bottomUpCode, courseOfValues_eq, bottomUpStep, List.length_map, List.length_range]
      rw [step, lookupChildrenCode_eq (image := Pattern.bottomUp operation) pattern
        fun child smaller => recurse _ smaller child rfl, tracks,
        ← Pattern.bottomUp_eq operation pattern]

end Mettapedia.OSLF.MeTTaIL.PatternCode
