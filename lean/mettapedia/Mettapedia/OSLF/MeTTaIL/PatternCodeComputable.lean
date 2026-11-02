import Mettapedia.Computability.FuelRecursion
import Mettapedia.OSLF.MeTTaIL.PatternCodeRecursion
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-!
# Structural recursion on pattern codes is computable

The code of a pattern determines its constructor, its data and the codes of its parts, the immediate sub-patterns
(`partsCode`), and how many binders each part sits under (`bindersCode`); a code with its parts replaced is computed
from the codes of the new parts (`rebuildCode`). Each of these is primitive recursive, and each agrees with the
pattern (`partsCode_patternCode`, `bindersCode_patternCode`, `rebuildCode_patternCode`).

A function of a parameter and a pattern given by structural recursion, at each pattern calling itself on parameters
and patterns of smaller code and combining the values, is read on codes as a recursion within a fuel one more than
the code (`structural`). It is computable when its calls and its combination are (`structural_computable`), and it
agrees with the function (`structural_patternCode`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.PatternCode

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Computability

/-! ## The parts of a pattern -/

/-- The immediate sub-patterns of a pattern, in order. -/
def parts : Pattern → List Pattern
  | .bvar _ => []
  | .fvar _ => []
  | .apply _ arguments => arguments
  | .lambda _ body => [body]
  | .multiLambda _ _ body => [body]
  | .subst body replacement => [body, replacement]
  | .collection _ elements _ => elements

/-- How many binders each immediate sub-pattern sits under. -/
def partBinders : Pattern → List ℕ
  | .bvar _ => []
  | .fvar _ => []
  | .apply _ arguments => arguments.map fun _ => 0
  | .lambda _ _ => [1]
  | .multiLambda arity _ _ => [arity]
  | .subst _ _ => [1, 0]
  | .collection _ elements _ => elements.map fun _ => 0

/-- A pattern with its immediate sub-patterns replaced, in order. -/
def withParts : Pattern → List Pattern → Pattern
  | .bvar index, _ => .bvar index
  | .fvar name, _ => .fvar name
  | .apply label _, replaced => .apply label replaced
  | .lambda binder _, replaced => .lambda binder (replaced.headD (.bvar 0))
  | .multiLambda arity binders _, replaced => .multiLambda arity binders (replaced.headD (.bvar 0))
  | .subst _ _, replaced => .subst (replaced.getD 0 (.bvar 0)) (replaced.getD 1 (.bvar 0))
  | .collection kind _ rest, replaced => .collection kind replaced rest

theorem partBinders_length (pattern : Pattern) : (partBinders pattern).length = (parts pattern).length := by
  cases pattern <;> simp [partBinders, parts]

/-- **The parts of a pattern have smaller codes.** -/
theorem patternCode_lt_of_mem_parts {pattern part : Pattern} (member : part ∈ parts pattern) :
    patternCode part < patternCode pattern := by
  cases pattern with
  | bvar => cases member
  | fvar => cases member
  | apply label arguments => exact patternCode_lt_apply member
  | lambda binder body =>
      simp only [parts, List.mem_singleton] at member
      subst member
      exact patternCode_lt_lambda binder _
  | multiLambda arity binders body =>
      simp only [parts, List.mem_singleton] at member
      subst member
      exact patternCode_lt_multiLambda arity binders _
  | subst body replacement =>
      simp only [parts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact patternCode_lt_subst_body _ replacement
      · exact patternCode_lt_subst_replacement body _
  | collection kind elements rest => exact patternCode_lt_collection member

/-! ## The parts of a code -/

/-- The codes of the parts of the pattern with a code, in order. -/
def partsCode (code : ℕ) : List ℕ :=
  if code.unpair.1 = 2 then Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2
  else if code.unpair.1 = 3 then [code.unpair.2.unpair.2]
  else if code.unpair.1 = 4 then [code.unpair.2.unpair.2.unpair.2]
  else if code.unpair.1 = 5 then [code.unpair.2.unpair.1, code.unpair.2.unpair.2]
  else if code.unpair.1 = 6 then Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2.unpair.1
  else []

/-- How many binders each part of the pattern with a code sits under. -/
def bindersCode (code : ℕ) : List ℕ :=
  if code.unpair.1 = 3 then [1]
  else if code.unpair.1 = 4 then [code.unpair.2.unpair.1]
  else if code.unpair.1 = 5 then [1, 0]
  else (partsCode code).map fun _ => 0

/-- The code of the pattern with a code, its parts replaced by the patterns with the given codes. -/
def rebuildCode (code : ℕ) (values : List ℕ) : ℕ :=
  if code.unpair.1 = 2 then Nat.pair 2 (Nat.pair code.unpair.2.unpair.1 (Encodable.encode values))
  else if code.unpair.1 = 3 then Nat.pair 3 (Nat.pair code.unpair.2.unpair.1 values.headI)
  else if code.unpair.1 = 4 then
    Nat.pair 4 (Nat.pair code.unpair.2.unpair.1 (Nat.pair code.unpair.2.unpair.2.unpair.1 values.headI))
  else if code.unpair.1 = 5 then Nat.pair 5 (Nat.pair (values.getD 0 0) (values.getD 1 0))
  else if code.unpair.1 = 6 then
    Nat.pair 6 (Nat.pair code.unpair.2.unpair.1 (Nat.pair (Encodable.encode values) code.unpair.2.unpair.2.unpair.2))
  else code

private theorem pair_zero_zero : Nat.pair 0 0 = 0 := rfl

theorem partsCode_patternCode (pattern : Pattern) : partsCode (patternCode pattern) = (parts pattern).map patternCode := by
  cases pattern <;> simp [partsCode, patternCode, parts, ofNat_patternListCode]

theorem bindersCode_patternCode (pattern : Pattern) : bindersCode (patternCode pattern) = partBinders pattern := by
  cases pattern <;> simp [bindersCode, partsCode, patternCode, partBinders, ofNat_patternListCode, Function.comp_def]

theorem rebuildCode_patternCode (pattern : Pattern) (replaced : List Pattern) :
    rebuildCode (patternCode pattern) (replaced.map patternCode) = patternCode (withParts pattern replaced) := by
  cases pattern with
  | bvar index => simp [rebuildCode, patternCode, withParts]
  | fvar name => simp [rebuildCode, patternCode, withParts]
  | apply label arguments => simp [rebuildCode, patternCode, withParts, patternListCode_eq_encode]
  | lambda binder body =>
      cases replaced <;> simp [rebuildCode, patternCode, withParts, pair_zero_zero]
  | multiLambda arity binders body =>
      cases replaced <;> simp [rebuildCode, patternCode, withParts, pair_zero_zero]
  | subst body replacement =>
      rcases replaced with _ | ⟨first, _ | ⟨second, _⟩⟩ <;> simp [rebuildCode, patternCode, withParts, pair_zero_zero]
  | collection kind elements rest => simp [rebuildCode, patternCode, withParts, patternListCode_eq_encode]

/-! ## Computability of the parts -/

private theorem tag_eq (value : ℕ) : PrimrecPred fun code : ℕ => code.unpair.1 = value :=
  Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const value)

private theorem first_primrec : Primrec fun code : ℕ => code.unpair.2.unpair.1 :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

private theorem second_primrec : Primrec fun code : ℕ => code.unpair.2.unpair.2 :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

private theorem third_primrec : Primrec fun code : ℕ => code.unpair.2.unpair.2.unpair.1 :=
  Primrec.fst.comp (Primrec.unpair.comp second_primrec)

private theorem fourth_primrec : Primrec fun code : ℕ => code.unpair.2.unpair.2.unpair.2 :=
  Primrec.snd.comp (Primrec.unpair.comp second_primrec)

theorem partsCode_primrec : Primrec partsCode := by
  have decoded : ∀ {position : ℕ → ℕ}, Primrec position →
      Primrec fun code => Denumerable.ofNat (List ℕ) (position code) :=
    fun primitive => (Primrec.ofNat (List ℕ)).comp primitive
  have single : ∀ {position : ℕ → ℕ}, Primrec position → Primrec fun code => [position code] :=
    fun primitive => Primrec.list_cons.comp primitive (Primrec.const [])
  exact Primrec.ite (tag_eq 2) (decoded second_primrec)
    (Primrec.ite (tag_eq 3) (single second_primrec)
    (Primrec.ite (tag_eq 4) (single fourth_primrec)
    (Primrec.ite (tag_eq 5) (Primrec.list_cons.comp first_primrec (single second_primrec))
    (Primrec.ite (tag_eq 6) (decoded third_primrec) (Primrec.const [])))))

theorem bindersCode_primrec : Primrec bindersCode := by
  have zeros : Primrec fun code => (partsCode code).map fun _ => (0 : ℕ) :=
    Primrec.list_map partsCode_primrec (Primrec.const 0).to₂
  exact Primrec.ite (tag_eq 3) (Primrec.const [1])
    (Primrec.ite (tag_eq 4) (Primrec.list_cons.comp first_primrec (Primrec.const []))
    (Primrec.ite (tag_eq 5) (Primrec.const [1, 0]) zeros))

theorem rebuildCode_primrec : Primrec₂ rebuildCode := by
  have code : Primrec fun input : ℕ × List ℕ => input.1 := Primrec.fst
  have values : Primrec fun input : ℕ × List ℕ => input.2 := Primrec.snd
  have tagged : ∀ value : ℕ, PrimrecPred fun input : ℕ × List ℕ => input.1.unpair.1 = value :=
    fun value => (tag_eq value).comp code
  have paired : ∀ {left right : ℕ × List ℕ → ℕ}, Primrec left → Primrec right →
      Primrec fun input => Nat.pair (left input) (right input) :=
    fun leftPrimitive rightPrimitive => Primrec₂.natPair.comp leftPrimitive rightPrimitive
  have encoded : Primrec fun input : ℕ × List ℕ => Encodable.encode input.2 := Primrec.encode.comp values
  have head : Primrec fun input : ℕ × List ℕ => input.2.headI := Primrec.list_headI.comp values
  have entry : ∀ position : ℕ, Primrec fun input : ℕ × List ℕ => input.2.getD position 0 :=
    fun position => (Primrec.list_getD 0).comp values (Primrec.const position)
  exact Primrec.ite (tagged 2) (paired (Primrec.const 2) (paired (first_primrec.comp code) encoded))
    (Primrec.ite (tagged 3) (paired (Primrec.const 3) (paired (first_primrec.comp code) head))
    (Primrec.ite (tagged 4) (paired (Primrec.const 4) (paired (first_primrec.comp code)
      (paired (third_primrec.comp code) head)))
    (Primrec.ite (tagged 5) (paired (Primrec.const 5) (paired (entry 0) (entry 1)))
    (Primrec.ite (tagged 6) (paired (Primrec.const 6) (paired (first_primrec.comp code)
      (paired encoded (fourth_primrec.comp code)))) code))))

/-! ## Structural recursion on codes -/

/-- **A structural recursion read on codes**: within a fuel one more than the code, the parameter and the code paired
as the argument, calling itself on the pairs `calls` lists and combining their values. -/
def structural (calls : ℕ → ℕ → List ℕ) (combine : ℕ → ℕ → List ℕ → ℕ) (parameter code : ℕ) : ℕ :=
  FuelRecursion.run (fun _ => 0) (fun _ input => calls input.unpair.1 input.unpair.2)
    (fun _ input values => combine input.unpair.1 input.unpair.2 values) (code + 1) (Nat.pair parameter code)

/-- **A structural recursion on codes is computable** when its calls and its combination are. -/
theorem structural_computable {calls : ℕ → ℕ → List ℕ} {combine : ℕ → ℕ → List ℕ → ℕ}
    (hCalls : Computable₂ calls)
    (hCombine : Computable fun input : ℕ × ℕ × List ℕ => combine input.1 input.2.1 input.2.2) :
    Computable₂ (structural calls combine) := by
  have unpaired : Computable fun input : ℕ => input.unpair := Primrec.unpair.to_comp
  have recursion := FuelRecursion.run_computable (base := fun _ => 0)
    (calls := fun _ input => calls input.unpair.1 input.unpair.2)
    (combine := fun _ input values => combine input.unpair.1 input.unpair.2 values) (Computable.const 0)
    (Computable.comp (f := fun pair : ℕ × ℕ => calls pair.1 pair.2) (g := fun input : ℕ × ℕ => input.2.unpair)
      hCalls (unpaired.comp Computable.snd))
    (Computable.comp (f := fun triple : ℕ × ℕ × List ℕ => combine triple.1 triple.2.1 triple.2.2)
      (g := fun input : ℕ × ℕ × List ℕ => (input.2.1.unpair.1, input.2.1.unpair.2, input.2.2)) hCombine
      (Computable.pair (Computable.fst.comp (unpaired.comp (Computable.fst.comp Computable.snd)))
        (Computable.pair (Computable.snd.comp (unpaired.comp (Computable.fst.comp Computable.snd)))
          (Computable.snd.comp Computable.snd))))
  exact Computable.comp (f := fun pair : ℕ × ℕ => FuelRecursion.run (fun _ => 0)
      (fun _ input => calls input.unpair.1 input.unpair.2)
      (fun _ input values => combine input.unpair.1 input.unpair.2 values) pair.1 pair.2)
    (g := fun input : ℕ × ℕ => (input.2 + 1, Nat.pair input.1 input.2)) recursion
    (Computable.pair (Primrec.succ.to_comp.comp Computable.snd) (Primrec₂.natPair.to_comp))

/-- **A structural recursion on codes agrees with the function on patterns** it reads: at every pattern, the function
is the combination of its values at the calls, every call is to a pattern of smaller code, and the calls on codes are
the calls on patterns read on codes. -/
theorem structural_patternCode {calls : ℕ → ℕ → List ℕ} {combine : ℕ → ℕ → List ℕ → ℕ} {value : ℕ → Pattern → ℕ}
    (patternCalls : ℕ → Pattern → List (ℕ × Pattern))
    (node : ∀ parameter pattern, value parameter pattern =
      combine parameter (patternCode pattern) ((patternCalls parameter pattern).map fun call => value call.1 call.2))
    (callsAgree : ∀ parameter pattern, calls parameter (patternCode pattern) =
      (patternCalls parameter pattern).map fun call => Nat.pair call.1 (patternCode call.2))
    (smaller : ∀ parameter pattern, ∀ call ∈ patternCalls parameter pattern, patternCode call.2 < patternCode pattern)
    (parameter : ℕ) (pattern : Pattern) :
    structural calls combine parameter (patternCode pattern) = value parameter pattern := by
  suffices within : ∀ fuel parameter pattern, patternCode pattern < fuel →
      FuelRecursion.run (fun _ => 0) (fun _ input => calls input.unpair.1 input.unpair.2)
        (fun _ input values => combine input.unpair.1 input.unpair.2 values) fuel
        (Nat.pair parameter (patternCode pattern)) = value parameter pattern from
    within _ parameter pattern (Nat.lt_succ_self _)
  intro fuel
  induction fuel with
  | zero => intro _ _ impossible; exact absurd impossible (Nat.not_lt_zero _)
  | succ fuel recurse =>
      intro parameter pattern bounded
      rw [FuelRecursion.run_succ]
      simp only [Nat.unpair_pair]
      rw [callsAgree, node, List.map_map]
      congr 1
      apply List.map_congr_left
      intro call member
      exact recurse call.1 call.2 (Nat.lt_of_lt_of_le (smaller parameter pattern call member)
        (Nat.lt_succ_iff.mp bounded))


/-! ## Maps of the bound variables

A map of the bound variables replaces each bound variable by a pattern that depends on a parameter and the variable;
under binders the parameter moves (`under`), and every other node keeps its data. Shifting the free bound variables
(`liftBVars`) and renaming them (`ContextSubstitution.substitute` of variables) are such maps. On codes a map of the
bound variables is a structural recursion (`bvarMapCode`), computable when the leaf and the move under binders are
(`bvarMapCode_computable`), and it tracks the map (`bvarMapCode_patternCode`).
-/

mutual
  /-- **A map of the bound variables**, with the parameter `q`. -/
  def bvarMap (leaf : ℕ → ℕ → Pattern) (under : ℕ → ℕ → ℕ) : ℕ → Pattern → Pattern
    | q, .bvar index => leaf q index
    | _, .fvar name => .fvar name
    | q, .apply label arguments => .apply label (bvarMapList leaf under (under q 0) arguments)
    | q, .lambda binder body => .lambda binder (bvarMap leaf under (under q 1) body)
    | q, .multiLambda arity binders body => .multiLambda arity binders (bvarMap leaf under (under q arity) body)
    | q, .subst body replacement =>
        .subst (bvarMap leaf under (under q 1) body) (bvarMap leaf under (under q 0) replacement)
    | q, .collection kind elements rest => .collection kind (bvarMapList leaf under (under q 0) elements) rest

  /-- A map of the bound variables on each member of a list. -/
  def bvarMapList (leaf : ℕ → ℕ → Pattern) (under : ℕ → ℕ → ℕ) : ℕ → List Pattern → List Pattern
    | _, [] => []
    | q, pattern :: patterns => bvarMap leaf under q pattern :: bvarMapList leaf under q patterns
end

@[simp] theorem bvarMapList_eq_map (leaf : ℕ → ℕ → Pattern) (under : ℕ → ℕ → ℕ) (q : ℕ) :
    ∀ patterns : List Pattern, bvarMapList leaf under q patterns = patterns.map (bvarMap leaf under q)
  | [] => rfl
  | pattern :: patterns => by simp [bvarMapList, bvarMapList_eq_map leaf under q patterns]

/-- The calls of a map of the bound variables: each part, with the parameter moved under its binders. -/
def underCalls (under : ℕ → ℕ → ℕ) (q : ℕ) (pattern : Pattern) : List (ℕ × Pattern) :=
  ((partBinders pattern).zip (parts pattern)).map fun part => (under q part.1, part.2)

/-- The calls of a map of the bound variables, on codes. -/
def underCallsCode (under : ℕ → ℕ → ℕ) (q code : ℕ) : List ℕ :=
  if code.unpair.1 = 3 then [Nat.pair (under q 1) code.unpair.2.unpair.2]
  else if code.unpair.1 = 4 then [Nat.pair (under q code.unpair.2.unpair.1) code.unpair.2.unpair.2.unpair.2]
  else if code.unpair.1 = 5 then
    [Nat.pair (under q 1) code.unpair.2.unpair.1, Nat.pair (under q 0) code.unpair.2.unpair.2]
  else (partsCode code).map fun part => Nat.pair (under q 0) part

/-- The combination of a map of the bound variables, on codes: the leaf at a bound variable, the node rebuilt from
the values of its parts elsewhere. -/
def bvarMapCombine (leafCode : ℕ → ℕ → ℕ) (q code : ℕ) (values : List ℕ) : ℕ :=
  if code.unpair.1 = 0 then leafCode q code.unpair.2 else rebuildCode code values

/-- **A map of the bound variables, on codes.** -/
def bvarMapCode (leafCode : ℕ → ℕ → ℕ) (under : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ :=
  structural (underCallsCode under) (bvarMapCombine leafCode)

private theorem zip_zeros (patterns : List Pattern) :
    (List.replicate patterns.length (0 : ℕ)).zip patterns = patterns.map fun pattern => (0, pattern) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [List.replicate_succ, recurse]

theorem underCallsCode_patternCode (under : ℕ → ℕ → ℕ) (q : ℕ) (pattern : Pattern) :
    underCallsCode under q (patternCode pattern) =
      (underCalls under q pattern).map fun call => Nat.pair call.1 (patternCode call.2) := by
  cases pattern <;>
    simp [underCallsCode, underCalls, partsCode, patternCode, parts, partBinders, ofNat_patternListCode, zip_zeros]

theorem underCalls_smaller (under : ℕ → ℕ → ℕ) (q : ℕ) (pattern : Pattern) :
    ∀ call ∈ underCalls under q pattern, patternCode call.2 < patternCode pattern := by
  intro call member
  simp only [underCalls, List.mem_map] at member
  obtain ⟨part, inZip, rfl⟩ := member
  exact patternCode_lt_of_mem_parts (List.of_mem_zip inZip).2

/-- A map of the bound variables at a node other than a bound variable maps its parts. -/
theorem bvarMap_node (leaf : ℕ → ℕ → Pattern) (under : ℕ → ℕ → ℕ) (q : ℕ) (pattern : Pattern)
    (notBVar : ∀ index, pattern ≠ .bvar index) :
    bvarMap leaf under q pattern =
      withParts pattern ((underCalls under q pattern).map fun call => bvarMap leaf under call.1 call.2) := by
  cases pattern with
  | bvar index => exact absurd rfl (notBVar index)
  | _ => simp [bvarMap, withParts, underCalls, parts, partBinders, zip_zeros, Function.comp_def]

theorem bvarMapCode_patternCode {leaf : ℕ → ℕ → Pattern} {under : ℕ → ℕ → ℕ} {leafCode : ℕ → ℕ → ℕ}
    (tracks : ∀ q index, leafCode q index = patternCode (leaf q index)) (q : ℕ) (pattern : Pattern) :
    bvarMapCode leafCode under q (patternCode pattern) = patternCode (bvarMap leaf under q pattern) := by
  refine structural_patternCode (value := fun q pattern => patternCode (bvarMap leaf under q pattern))
    (underCalls under) ?_ (underCallsCode_patternCode under) (underCalls_smaller under) q pattern
  intro q pattern
  by_cases isBVar : ∃ index, pattern = .bvar index
  · obtain ⟨index, rfl⟩ := isBVar
    simp [bvarMapCombine, patternCode, bvarMap, tracks]
  · have notBVar : ∀ index, pattern ≠ .bvar index := fun index same => isBVar ⟨index, same⟩
    have tag : (patternCode pattern).unpair.1 ≠ 0 := by
      cases pattern with
      | bvar index => exact absurd rfl (notBVar index)
      | _ => simp [patternCode]
    rw [bvarMapCombine, if_neg tag, bvarMap_node leaf under q pattern notBVar, ← rebuildCode_patternCode,
      List.map_map]
    rfl

theorem underCallsCode_computable {under : ℕ → ℕ → ℕ} (hUnder : Computable₂ under) :
    Computable₂ (underCallsCode under) := by
  have code : Computable fun input : ℕ × ℕ => input.2 := Computable.snd
  have moved : ∀ {binders : ℕ × ℕ → ℕ}, Computable binders →
      Computable fun input : ℕ × ℕ => under input.1 (binders input) :=
    fun computable => hUnder.comp Computable.fst computable
  have paired : ∀ {left right : ℕ × ℕ → ℕ}, Computable left → Computable right →
      Computable fun input => Nat.pair (left input) (right input) :=
    fun leftComputable rightComputable => Primrec₂.natPair.to_comp.comp leftComputable rightComputable
  have single : ∀ {element : ℕ × ℕ → ℕ}, Computable element → Computable fun input => [element input] :=
    fun computable => (Primrec.list_cons.to_comp).comp computable (Computable.const [])
  have field : ∀ {position : ℕ → ℕ}, Primrec position → Computable fun input : ℕ × ℕ => position input.2 :=
    fun primitive => primitive.to_comp.comp code
  have tagged : ∀ value : ℕ, Computable fun input : ℕ × ℕ => decide (input.2.unpair.1 = value) :=
    fun value => ((tag_eq value).decide.to_comp).comp code
  have mapped : Computable fun input : ℕ × ℕ => (partsCode input.2).map fun part => Nat.pair (under input.1 0) part := by
    have atZero := moved (Computable.const 0)
    have pairing : Primrec fun pair : List ℕ × ℕ => pair.1.map fun part => Nat.pair pair.2 part :=
      Primrec.list_map Primrec.fst (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
    exact Computable.comp (f := fun pair : List ℕ × ℕ => pair.1.map fun part => Nat.pair pair.2 part)
      (g := fun input : ℕ × ℕ => (partsCode input.2, under input.1 0)) pairing.to_comp
      (Computable.pair (partsCode_primrec.to_comp.comp code) atZero)
  have chosen := Computable.cond (tagged 3) (single (paired (moved (Computable.const 1)) (field second_primrec)))
    (Computable.cond (tagged 4) (single (paired (moved (field first_primrec)) (field fourth_primrec)))
    (Computable.cond (tagged 5) ((Primrec.list_cons.to_comp).comp
        (paired (moved (Computable.const 1)) (field first_primrec))
        (single (paired (moved (Computable.const 0)) (field second_primrec))))
      mapped))
  refine chosen.of_eq fun input => ?_
  simp only [underCallsCode]
  by_cases three : input.2.unpair.1 = 3
  · simp [three]
  by_cases four : input.2.unpair.1 = 4
  · simp [four]
  by_cases five : input.2.unpair.1 = 5
  · simp [five]
  simp [three, four, five]

theorem bvarMapCombine_computable {leafCode : ℕ → ℕ → ℕ} (hLeaf : Computable₂ leafCode) :
    Computable fun input : ℕ × ℕ × List ℕ => bvarMapCombine leafCode input.1 input.2.1 input.2.2 := by
  have leafValue : Computable fun input : ℕ × ℕ × List ℕ => leafCode input.1 input.2.1.unpair.2 :=
    hLeaf.comp Computable.fst (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp
      (Computable.fst.comp Computable.snd)))
  have rebuilt : Computable fun input : ℕ × ℕ × List ℕ => rebuildCode input.2.1 input.2.2 :=
    rebuildCode_primrec.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)
  have tagged : Computable fun input : ℕ × ℕ × List ℕ => decide (input.2.1.unpair.1 = 0) :=
    ((tag_eq 0).decide.to_comp).comp (Computable.fst.comp Computable.snd)
  exact (Computable.cond tagged leafValue rebuilt).of_eq fun input => by
    by_cases zero : input.2.1.unpair.1 = 0 <;> simp [bvarMapCombine, zero]

/-- **A map of the bound variables is computable on codes** when its leaf and its move under binders are. -/
theorem bvarMapCode_computable {leafCode : ℕ → ℕ → ℕ} {under : ℕ → ℕ → ℕ} (hLeaf : Computable₂ leafCode)
    (hUnder : Computable₂ under) : Computable₂ (bvarMapCode leafCode under) :=
  structural_computable (underCallsCode_computable hUnder) (bvarMapCombine_computable hLeaf)

/-! ### Shifting the bound variables -/

open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList_eq_map)

/-- The leaf of a shift: with the parameter `(cutoff, shift)`, a variable from the cutoff on moves by the shift. -/
def liftLeaf (q index : ℕ) : Pattern := .bvar (if index ≥ q.unpair.1 then index + q.unpair.2 else index)

/-- Under binders the cutoff of a shift moves past them. -/
def liftUnder (q binders : ℕ) : ℕ := Nat.pair (q.unpair.1 + binders) q.unpair.2

/-- **`liftBVars` is a map of the bound variables.** -/
theorem liftBVars_eq_bvarMap (pattern : Pattern) :
    ∀ cutoff shift, liftBVars cutoff shift pattern = bvarMap liftLeaf liftUnder (Nat.pair cutoff shift) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro cutoff shift
      by_cases above : cutoff ≤ index <;> simp [liftBVars, bvarMap, liftLeaf, above]
  | hfvar name => intro cutoff shift; simp [liftBVars, bvarMap]
  | happly label arguments recurse =>
      intro cutoff shift
      simp only [liftBVars, bvarMap, liftBVarsList_eq_map, bvarMapList_eq_map, liftUnder, Nat.unpair_pair,
        Nat.add_zero, Pattern.apply.injEq, true_and]
      exact List.map_congr_left fun argument member => recurse argument member cutoff shift
  | hlambda binder body recurse =>
      intro cutoff shift; simp [liftBVars, bvarMap, liftUnder, recurse]
  | hmultiLambda arity binders body recurse =>
      intro cutoff shift; simp [liftBVars, bvarMap, liftUnder, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro cutoff shift; simp [liftBVars, bvarMap, liftUnder, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      intro cutoff shift
      simp only [liftBVars, bvarMap, liftBVarsList_eq_map, bvarMapList_eq_map, liftUnder, Nat.unpair_pair,
        Nat.add_zero, Pattern.collection.injEq, true_and, and_true]
      exact List.map_congr_left fun element member => recurse element member cutoff shift

/-- `liftBVars` on codes. -/
def liftCode (cutoff shift code : ℕ) : ℕ :=
  bvarMapCode (fun q index => patternCode (liftLeaf q index)) liftUnder (Nat.pair cutoff shift) code

theorem liftCode_patternCode (cutoff shift : ℕ) (pattern : Pattern) :
    liftCode cutoff shift (patternCode pattern) = patternCode (liftBVars cutoff shift pattern) := by
  rw [liftCode, bvarMapCode_patternCode (fun _ _ => rfl), liftBVars_eq_bvarMap]

theorem liftCode_computable : Computable fun input : ℕ × ℕ × ℕ => liftCode input.1 input.2.1 input.2.2 := by
  have leafComputable : Computable₂ fun q index : ℕ => patternCode (liftLeaf q index) := by
    have shifted : Computable₂ fun q index : ℕ =>
        Nat.pair 0 (if index ≥ q.unpair.1 then index + q.unpair.2 else index) := by
      have cutoff : Computable fun input : ℕ × ℕ => input.1.unpair.1 :=
        Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst)
      have amount : Computable fun input : ℕ × ℕ => input.1.unpair.2 :=
        Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst)
      have chosen := Computable.cond ((Primrec.nat_le.decide.to_comp).comp cutoff Computable.snd)
        (Primrec.nat_add.to_comp.comp Computable.snd amount) Computable.snd
      exact Primrec₂.natPair.to_comp.comp (Computable.const 0) (chosen.of_eq fun input => by
        by_cases bigger : input.1.unpair.1 ≤ input.2 <;> simp [bigger, ge_iff_le])
    exact shifted.of_eq fun input => by simp [liftLeaf, patternCode]
  have underComputable : Computable₂ liftUnder :=
    Primrec₂.natPair.to_comp.comp (Primrec.nat_add.to_comp.comp
      (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst)) Computable.snd)
      (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst))
  exact Computable.comp (f := fun pair : ℕ × ℕ => bvarMapCode (fun q index => patternCode (liftLeaf q index)) liftUnder
      pair.1 pair.2)
    (g := fun input : ℕ × ℕ × ℕ => (Nat.pair input.1 input.2.1, input.2.2))
    (bvarMapCode_computable leafComputable underComputable)
    (Computable.pair (Primrec₂.natPair.to_comp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))

/-! ### Renaming the bound variables -/

open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (substitute lift substituteList_eq_map)

/-- The leaf of a renaming by `relabel data`, under `depth` binders, with the parameter `(data, depth)`: a variable
bound by the binders stays, a variable past them is renamed. -/
def renameLeaf (relabel : ℕ → ℕ → ℕ) (q index : ℕ) : Pattern :=
  .bvar (if index < q.unpair.2 then index else relabel q.unpair.1 (index - q.unpair.2) + q.unpair.2)

/-- Under binders the depth of a renaming moves past them. -/
def renameUnder (q binders : ℕ) : ℕ := Nat.pair q.unpair.1 (q.unpair.2 + binders)

/-- The variables of a renaming under `depth` binders. -/
def renamed (relabel : ℕ → ℕ → ℕ) (data depth : ℕ) : ℕ → Pattern :=
  fun index => .bvar (if index < depth then index else relabel data (index - depth) + depth)

theorem lift_renamed (relabel : ℕ → ℕ → ℕ) (data depth binders : ℕ) :
    lift binders (renamed relabel data depth) = renamed relabel data (depth + binders) := by
  funext index
  simp only [lift, renamed]
  by_cases below : index < binders
  · rw [if_pos below, if_pos (show index < depth + binders by omega)]
  · rw [if_neg below]
    simp only [Substitution.liftBVars, ge_iff_le, Nat.zero_le, if_true]
    by_cases inner : index - binders < depth
    · rw [if_pos inner, if_pos (show index < depth + binders by omega)]
      congr 1
      omega
    · rw [if_neg inner, if_neg (show ¬ index < depth + binders by omega)]
      congr 1
      rw [show index - (depth + binders) = index - binders - depth by omega]
      omega

/-- **Substituting renamed variables is a map of the bound variables.** -/
theorem substitute_renamed_eq_bvarMap (relabel : ℕ → ℕ → ℕ) (data : ℕ) (pattern : Pattern) :
    ∀ depth, substitute (renamed relabel data depth) pattern =
      bvarMap (renameLeaf relabel) renameUnder (Nat.pair data depth) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; simp [substitute, bvarMap, renamed, renameLeaf]
  | hfvar name => intro depth; simp [substitute, bvarMap]
  | happly label arguments recurse =>
      intro depth
      simp only [substitute, bvarMap, substituteList_eq_map, bvarMapList_eq_map, renameUnder, Nat.unpair_pair,
        Nat.add_zero, Pattern.apply.injEq, true_and]
      exact List.map_congr_left fun argument member => recurse argument member depth
  | hlambda binder body recurse =>
      intro depth; simp [substitute, bvarMap, renameUnder, lift_renamed, recurse]
  | hmultiLambda arity binders body recurse =>
      intro depth; simp [substitute, bvarMap, renameUnder, lift_renamed, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro depth
      simp [substitute, bvarMap, renameUnder, lift_renamed, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      intro depth
      simp only [substitute, bvarMap, substituteList_eq_map, bvarMapList_eq_map, renameUnder, Nat.unpair_pair,
        Nat.add_zero, Pattern.collection.injEq, true_and, and_true]
      exact List.map_congr_left fun element member => recurse element member depth

/-- Renaming the free bound variables by `relabel data`, on codes. -/
def renameCode (relabel : ℕ → ℕ → ℕ) (data code : ℕ) : ℕ :=
  bvarMapCode (fun q index => patternCode (renameLeaf relabel q index)) renameUnder (Nat.pair data 0) code

/-- **Renaming on codes tracks the renaming of the free bound variables.** -/
theorem renameCode_patternCode (relabel : ℕ → ℕ → ℕ) (data : ℕ) (pattern : Pattern) :
    renameCode relabel data (patternCode pattern) =
      patternCode (substitute (fun index => .bvar (relabel data index)) pattern) := by
  have zero : renamed relabel data 0 = fun index => .bvar (relabel data index) := by
    funext index
    simp [renamed]
  rw [renameCode, bvarMapCode_patternCode (fun _ _ => rfl), ← substitute_renamed_eq_bvarMap, zero]

/-- **Renaming by a computable family is computable on codes.** -/
theorem renameCode_computable {relabel : ℕ → ℕ → ℕ} (hRelabel : Computable₂ relabel) :
    Computable₂ (renameCode relabel) := by
  have leafComputable : Computable₂ fun q index : ℕ => patternCode (renameLeaf relabel q index) := by
    have data : Computable fun input : ℕ × ℕ => input.1.unpair.1 :=
      Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst)
    have depth : Computable fun input : ℕ × ℕ => input.1.unpair.2 :=
      Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst)
    have image : Computable fun input : ℕ × ℕ => relabel input.1.unpair.1 (input.2 - input.1.unpair.2) +
        input.1.unpair.2 :=
      Primrec.nat_add.to_comp.comp (hRelabel.comp data (Primrec.nat_sub.to_comp.comp Computable.snd depth)) depth
    have chosen := Computable.cond ((Primrec.nat_lt.decide.to_comp).comp Computable.snd depth) Computable.snd image
    exact (Primrec₂.natPair.to_comp.comp (Computable.const 0) chosen).of_eq fun input => by
      by_cases below : input.2 < input.1.unpair.2 <;> simp [renameLeaf, patternCode, below]
  have underComputable : Computable₂ renameUnder :=
    Primrec₂.natPair.to_comp.comp (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst))
      (Primrec.nat_add.to_comp.comp (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst))
        Computable.snd)
  exact Computable.comp (f := fun pair : ℕ × ℕ =>
      bvarMapCode (fun q index => patternCode (renameLeaf relabel q index)) renameUnder pair.1 pair.2)
    (g := fun input : ℕ × ℕ => (Nat.pair input.1 0, input.2))
    (bvarMapCode_computable leafComputable underComputable)
    (Computable.pair (Primrec₂.natPair.to_comp.comp Computable.fst (Computable.const 0)) Computable.snd)

end Mettapedia.OSLF.MeTTaIL.PatternCode
