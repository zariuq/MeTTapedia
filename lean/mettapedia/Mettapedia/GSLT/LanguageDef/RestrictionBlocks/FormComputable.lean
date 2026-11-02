import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Form
import Mettapedia.OSLF.MeTTaIL.PatternCoded

/-!
# The block of a process is computable on codes

A block is coded by its count of restrictions and the codes of its components (`Coded Prenex`). Whether a pattern
mentions a bound variable, its size, its renamings along the block's reorderings (`dropIndex`, `Prenex.permute`), the
blocks side by side (`Prenex.par`) and closed by one more restriction (`Prenex.close`), and the block of a process
(`decompose`) are computable on codes. `decompose` is a structural recursion whose calls are the body of a restriction,
the argument of a named multiset whose empty instance is inaction, and the members of a closed bag, read through
one-level tests of a pattern's shape.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.PatternCode.CodeComputable'
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (PatternLe serList ser)
open CodeComputable

instance : Coded Prenex := ⟨fun form => code (form.count, form.components)⟩


theorem code_prenex (form : Prenex) : code form = code (form.count, form.components) := rfl

namespace FormCodes

variable {α : Type*} [Coded α]

/-! ## Blocks -/

theorem prenex {count : α → ℕ} {components : α → List Pattern} (hCount : CodeComputable count)
    (hComponents : CodeComputable components) :
    CodeComputable fun argument => (⟨count argument, components argument⟩ : Prenex) := by
  obtain ⟨track, computable, tracks⟩ := hCount.pair hComponents
  exact ⟨track, computable, tracks⟩

theorem count : CodeComputable fun form : Prenex => form.count := by
  obtain ⟨track, computable, tracks⟩ := (fst : CodeComputable fun pair : ℕ × List Pattern => pair.1)
  exact ⟨track, computable, fun form => tracks (form.count, form.components)⟩

theorem components : CodeComputable fun form : Prenex => form.components := by
  obtain ⟨track, computable, tracks⟩ := (snd : CodeComputable fun pair : ℕ × List Pattern => pair.2)
  exact ⟨track, computable, fun form => tracks (form.count, form.components)⟩

theorem nil : CodeComputable fun _ : α => Prenex.nil := const _

theorem atom {component : α → Pattern} (hComponent : CodeComputable component) :
    CodeComputable fun argument => Prenex.atom (component argument) :=
  prenex (const 0) (list_cons hComponent list_nil)

theorem restrict {form : α → Prenex} (hForm : CodeComputable form) :
    CodeComputable fun argument => (form argument).restrict :=
  prenex (nat_add (count.comp hForm) (const 1)) (components.comp hForm)

/-! ## Bound variables -/

theorem mentionsList_eq_any (index : ℕ) : ∀ patterns : List Pattern,
    mentionsList index patterns = patterns.any (mentions index)
  | [] => rfl
  | pattern :: patterns => by rw [mentionsList, mentionsList_eq_any index patterns, List.any_cons]

private theorem zip_replicate_zero (patterns : List Pattern) :
    (List.replicate patterns.length (0 : ℕ)).zip patterns = patterns.map fun pattern => (0, pattern) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [List.replicate_succ, recurse]

theorem underCalls_codeComputable {under : ℕ → ℕ → ℕ} (hUnder : Computable₂ under) :
    CodeComputable₂ (underCalls under) :=
  ⟨fun n => Encodable.encode (underCallsCode under n.unpair.1 n.unpair.2),
    Primrec.encode.to_comp.comp (Computable.comp (f := fun pair : ℕ × ℕ => underCallsCode under pair.1 pair.2)
      (g := fun n : ℕ => (n.unpair.1, n.unpair.2)) (underCallsCode_computable hUnder)
      (Computable.pair (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
        (Primrec.snd.to_comp.comp Primrec.unpair.to_comp))),
    fun pair => by
      simp only [code_pair, code_pattern, Nat.unpair_pair, underCallsCode_patternCode, code_list]
      rfl⟩

/-- The combination of `mentions`: at a bound variable whether it is the one sought, elsewhere whether a part
mentions it. -/
def mentionsCombine (index : ℕ) (pattern : Pattern) (values : List Bool) : Bool :=
  @Pattern.casesOn (fun _ => Bool) pattern (fun other => other == index) (fun _ => values.any id)
    (fun _ _ => values.any id) (fun _ _ => values.any id) (fun _ _ _ => values.any id) (fun _ _ => values.any id)
    (fun _ _ _ => values.any id)

theorem mentions_node (index : ℕ) (pattern : Pattern) :
    mentions index pattern = mentionsCombine index pattern
      ((underCalls (· + ·) index pattern).map fun call => mentions call.1 call.2) := by
  cases pattern with
  | bvar other => rfl
  | fvar name => rfl
  | apply label arguments =>
      simp [mentionsCombine, mentions, underCalls, partBinders, parts, zip_replicate_zero, mentionsList_eq_any,
        Function.comp_def]
  | lambda binder body => simp [mentionsCombine, mentions, underCalls, partBinders, parts]
  | multiLambda arity binders body => simp [mentionsCombine, mentions, underCalls, partBinders, parts]
  | subst body replacement => simp [mentionsCombine, mentions, underCalls, partBinders, parts]
  | collection kind elements rest =>
      simp [mentionsCombine, mentions, underCalls, partBinders, parts, zip_replicate_zero, mentionsList_eq_any,
        Function.comp_def]

theorem mentionsCombine_codeComputable :
    CodeComputable fun input : ℕ × Pattern × List Bool => mentionsCombine input.1 input.2.1 input.2.2 := by
  have anyValues : CodeComputable fun input : ℕ × Pattern × List Bool => input.2.2.any id :=
    list_any (snd.comp snd) snd
  have cased := casesOn (pattern := fun input : ℕ × Pattern × List Bool => input.2.1)
    (onBVar := fun input other => other == input.1) (onFVar := fun input _ => input.2.2.any id)
    (onApply := fun input _ _ => input.2.2.any id) (onLambda := fun input _ _ => input.2.2.any id)
    (onMultiLambda := fun input _ _ _ => input.2.2.any id) (onSubst := fun input _ _ => input.2.2.any id)
    (onCollection := fun input _ _ _ => input.2.2.any id) (fst.comp snd)
    ((nat_eq snd (fst.comp fst)).of_eq fun pair => Bool.eq_iff_iff.mpr (by simp))
    (anyValues.comp fst) (anyValues.comp fst) (anyValues.comp fst) (anyValues.comp fst) (anyValues.comp fst)
    (anyValues.comp fst)
  exact cased.of_eq fun input => rfl

/-- **Whether a pattern mentions a bound variable is computable on codes.** -/
theorem mentions_codeComputable : CodeComputable₂ mentions :=
  structural (calls := underCalls (· + ·)) (combine := mentionsCombine) mentions_node
    (fun parameter pattern => underCalls_smaller _ parameter pattern)
    (underCalls_codeComputable Primrec.nat_add.to_comp) mentionsCombine_codeComputable

theorem sizeList_eq_sum : ∀ patterns : List Pattern, sizeList patterns = (patterns.map size).sum
  | [] => rfl
  | pattern :: patterns => by rw [sizeList, sizeList_eq_sum patterns, List.map_cons, List.sum_cons]

theorem size_node (pattern : Pattern) : size pattern = ((parts pattern).map size).sum + 1 := by
  cases pattern <;> simp [size, parts, sizeList_eq_sum, Nat.add_comm]

/-- **The size of a pattern is computable on codes.** -/
theorem size_codeComputable : CodeComputable size := by
  have calls : CodeComputable₂ fun (_ : ℕ) (pattern : Pattern) => (parts pattern).map fun part => ((0 : ℕ), part) :=
    ⟨fun n => Encodable.encode ((partsCode n.unpair.2).map (Nat.pair 0)),
      Primrec.encode.to_comp.comp (Primrec.list_map (partsCode_primrec.comp (Primrec.snd.comp Primrec.unpair))
        (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd).to₂).to_comp,
      fun pair => by
        simp only [code_pair, code_pattern, Nat.unpair_pair, partsCode_patternCode, code_list, List.map_map]
        rfl⟩
  have structured := structural (value := fun (_ : ℕ) pattern => size pattern)
    (calls := fun _ pattern => (parts pattern).map fun part => ((0 : ℕ), part))
    (combine := fun _ _ values => values.sum + 1)
    (fun _ pattern => by rw [size_node, List.map_map]; rfl)
    (fun _ pattern call member => by
      simp only [List.mem_map] at member
      obtain ⟨part, inParts, rfl⟩ := member
      exact patternCode_lt_of_mem_parts inParts) calls (nat_add (list_sum (snd.comp snd)) (const 1))
  exact structured.comp ((const 0).pair id)

/-! ## Renamings -/

theorem dropIndex_computable : Computable₂ dropIndex :=
  (Computable.cond ((Primrec.nat_lt.decide.to_comp).comp Computable.snd Computable.fst) Computable.snd
    (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const 1))).of_eq fun input => by
    by_cases below : input.2 < input.1 <;> simp [dropIndex, below]

theorem rename_dropIndex : CodeComputable fun input : ℕ × Pattern => rename (dropIndex input.1) input.2 :=
  rename' dropIndex_computable

/-- The reorderings of a block, as a family of renamings indexed by codes. -/
def permuteFamily (data index : ℕ) : ℕ :=
  Prenex.permute data.unpair.1 (Denumerable.ofNat (List ℕ) data.unpair.2) index

theorem permuteFamily_computable : Computable₂ permuteFamily := by
  have count : Computable fun input : ℕ × ℕ => input.1.unpair.1 :=
    Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst)
  have order : Computable fun input : ℕ × ℕ => Denumerable.ofNat (List ℕ) input.1.unpair.2 :=
    (Primrec.ofNat (List ℕ)).to_comp.comp (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp Computable.fst))
  have fetched : Computable fun input : ℕ × ℕ =>
      ((Denumerable.ofNat (List ℕ) input.1.unpair.2)[input.2]?).getD input.2 :=
    Primrec.option_getD.to_comp.comp (Primrec.list_getElem?.to_comp.comp order Computable.snd) Computable.snd
  exact (Computable.cond ((Primrec.nat_lt.decide.to_comp).comp Computable.snd count) fetched Computable.snd).of_eq
    fun input => by
      by_cases below : input.2 < input.1.unpair.1
      · simp [permuteFamily, Prenex.permute, below, List.getD_eq_getElem?_getD]
      · simp [permuteFamily, Prenex.permute, below]

theorem rename_permute :
    CodeComputable fun input : (ℕ × List ℕ) × Pattern => rename (Prenex.permute input.1.1 input.1.2) input.2 :=
  ((rename' permuteFamily_computable).comp ((code'.comp fst).pair snd)).of_eq fun input => by
    simp only [rename]
    congr 1
    funext index
    simp [permuteFamily, code_pair, ofNat_code_list]

/-! ## Blocks side by side, and closed -/

theorem par {first second : α → Prenex} (hFirst : CodeComputable first) (hSecond : CodeComputable second) :
    CodeComputable fun argument => (first argument).par (second argument) := by
  have lifted : ∀ {cutoff shift : α → ℕ}, CodeComputable cutoff → CodeComputable shift →
      ∀ {members : α → List Pattern}, CodeComputable members →
        CodeComputable fun argument =>
          (members argument).map
            (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars (cutoff argument) (shift argument)) :=
    fun {cutoff shift} hCutoff hShift members hMembers => list_map (members := members)
      (image := fun argument component =>
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars (cutoff argument) (shift argument) component) hMembers
      (liftBVars'.comp ((hCutoff.comp fst).pair ((hShift.comp fst).pair snd)))
  exact (prenex (nat_add (count.comp hFirst) (count.comp hSecond))
    (list_append (lifted (const 0) (count.comp hSecond) (components.comp hFirst))
      (lifted (count.comp hSecond) (count.comp hFirst) (components.comp hSecond)))).of_eq fun _ => rfl

theorem close {form : α → Prenex} (hForm : CodeComputable form) :
    CodeComputable fun argument => (form argument).close := by
  have used := list_any (members := fun argument => (form argument).components)
    (test := fun argument component => mentions (form argument).count component) (components.comp hForm)
    (mentions_codeComputable.comp ((count.comp (hForm.comp fst)).pair snd))
  have dropped := prenex (count.comp hForm) (list_map (members := fun argument => (form argument).components)
    (image := fun argument component => rename (dropIndex (form argument).count) component) (components.comp hForm)
    (rename_dropIndex.comp ((count.comp (hForm.comp fst)).pair snd)))
  exact (ite used (restrict hForm) dropped).of_eq fun argument => by
    simp only [Prenex.close]

/-! ## Shapes of a pattern -/

/-- The label of an application, the empty string otherwise. -/
def applyLabel : Pattern → String
  | .apply label _ => label
  | _ => ""

/-- The arguments of an application, none otherwise. -/
def applyArguments : Pattern → List Pattern
  | .apply _ arguments => arguments
  | _ => []

/-- Whether a pattern is an application. -/
def isApply : Pattern → Bool
  | .apply _ _ => true
  | _ => false

/-- Whether a pattern is an abstraction. -/
def isLambda : Pattern → Bool
  | .lambda _ _ => true
  | _ => false

/-- The body of an abstraction, a bound variable otherwise. -/
def lambdaBody : Pattern → Pattern
  | .lambda _ body => body
  | _ => .bvar 0

/-- Whether a pattern is a closed bag. -/
def isClosedBag : Pattern → Bool
  | .collection .hashBag _ none => true
  | _ => false

/-- The members of a collection, none otherwise. -/
def collectionElements : Pattern → List Pattern
  | .collection _ elements _ => elements
  | _ => []

private theorem shape {β : Type*} [Coded β] {value : Pattern → β} {onBVar : ℕ → β} {onFVar : String → β}
    {onApply : String → List Pattern → β} {onLambda : Option String → Pattern → β}
    {onMultiLambda : ℕ → List String → Pattern → β} {onSubst : Pattern → Pattern → β}
    {onCollection : CollType → List Pattern → Option String → β}
    (cases : ∀ pattern, value pattern = @Pattern.casesOn (fun _ => β) pattern onBVar onFVar onApply onLambda
      onMultiLambda onSubst onCollection)
    (hBVar : CodeComputable onBVar) (hFVar : CodeComputable onFVar)
    (hApply : CodeComputable fun input : String × List Pattern => onApply input.1 input.2)
    (hLambda : CodeComputable fun input : Option String × Pattern => onLambda input.1 input.2)
    (hMultiLambda : CodeComputable fun input : ℕ × List String × Pattern =>
      onMultiLambda input.1 input.2.1 input.2.2)
    (hSubst : CodeComputable fun input : Pattern × Pattern => onSubst input.1 input.2)
    (hCollection : CodeComputable fun input : CollType × List Pattern × Option String =>
      onCollection input.1 input.2.1 input.2.2) : CodeComputable value :=
  (casesOn (pattern := fun pattern : Pattern => pattern) (onBVar := fun _ => onBVar) (onFVar := fun _ => onFVar)
    (onApply := fun _ => onApply) (onLambda := fun _ => onLambda) (onMultiLambda := fun _ => onMultiLambda)
    (onSubst := fun _ => onSubst) (onCollection := fun _ => onCollection) CodeComputable.id (hBVar.comp snd)
    (hFVar.comp snd) (hApply.comp snd) (hLambda.comp snd) (hMultiLambda.comp snd) (hSubst.comp snd)
    (hCollection.comp snd)).of_eq fun pattern => (cases pattern).symm

theorem applyLabel_codeComputable : CodeComputable applyLabel :=
  shape (onBVar := fun _ => "") (onFVar := fun _ => "") (onApply := fun label _ => label)
    (onLambda := fun _ _ => "") (onMultiLambda := fun _ _ _ => "") (onSubst := fun _ _ => "")
    (onCollection := fun _ _ _ => "") (fun pattern => by cases pattern <;> rfl) (const _) (const _) fst (const _)
    (const _) (const _) (const _)

theorem applyArguments_codeComputable : CodeComputable applyArguments :=
  shape (onBVar := fun _ => []) (onFVar := fun _ => []) (onApply := fun _ arguments => arguments)
    (onLambda := fun _ _ => []) (onMultiLambda := fun _ _ _ => []) (onSubst := fun _ _ => [])
    (onCollection := fun _ _ _ => []) (fun pattern => by cases pattern <;> rfl) (const _) (const _) snd (const _)
    (const _) (const _) (const _)

theorem isApply_codeComputable : CodeComputable isApply :=
  shape (onBVar := fun _ => false) (onFVar := fun _ => false) (onApply := fun _ _ => true)
    (onLambda := fun _ _ => false) (onMultiLambda := fun _ _ _ => false) (onSubst := fun _ _ => false)
    (onCollection := fun _ _ _ => false) (fun pattern => by cases pattern <;> rfl) (const _) (const _) (const _)
    (const _) (const _) (const _) (const _)

theorem isLambda_codeComputable : CodeComputable isLambda :=
  shape (onBVar := fun _ => false) (onFVar := fun _ => false) (onApply := fun _ _ => false)
    (onLambda := fun _ _ => true) (onMultiLambda := fun _ _ _ => false) (onSubst := fun _ _ => false)
    (onCollection := fun _ _ _ => false) (fun pattern => by cases pattern <;> rfl) (const _) (const _) (const _)
    (const _) (const _) (const _) (const _)

theorem lambdaBody_codeComputable : CodeComputable lambdaBody :=
  shape (onBVar := fun _ => .bvar 0) (onFVar := fun _ => .bvar 0) (onApply := fun _ _ => .bvar 0)
    (onLambda := fun _ body => body) (onMultiLambda := fun _ _ _ => .bvar 0) (onSubst := fun _ _ => .bvar 0)
    (onCollection := fun _ _ _ => .bvar 0) (fun pattern => by cases pattern <;> rfl) (const _) (const _) (const _)
    snd (const _) (const _) (const _)

theorem collectionElements_codeComputable : CodeComputable collectionElements :=
  shape (onBVar := fun _ => []) (onFVar := fun _ => []) (onApply := fun _ _ => [])
    (onLambda := fun _ _ => []) (onMultiLambda := fun _ _ _ => []) (onSubst := fun _ _ => [])
    (onCollection := fun _ elements _ => elements) (fun pattern => by cases pattern <;> rfl) (const _) (const _)
    (const _) (const _) (const _) (const _) (fst.comp snd)

private theorem optionStringCode_eq_zero (rest : Option String) : (optionStringCode rest = 0) = (rest = none) := by
  cases rest with
  | none => exact propext (iff_of_true rfl rfl)
  | some string =>
      have positive : optionStringCode (some string) ≠ 0 := by
        simp only [optionStringCode]
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.left_le_pair 1 _))
      exact propext (iff_of_false positive (by simp))

theorem isClosedBag_codeComputable : CodeComputable isClosedBag := by
  have test : CodeComputable fun input : CollType × List Pattern × Option String =>
      decide (collectionCode input.1 = 1) && decide (optionStringCode input.2.2 = 0) :=
    and (nat_eq (code'.comp fst) (const 1)) (nat_eq (code'.comp (snd.comp snd)) (const 0))
  exact shape (onBVar := fun _ => false) (onFVar := fun _ => false) (onApply := fun _ _ => false)
    (onLambda := fun _ _ => false) (onMultiLambda := fun _ _ _ => false) (onSubst := fun _ _ => false)
    (onCollection := fun kind _ rest => decide (collectionCode kind = 1) && decide (optionStringCode rest = 0))
    (fun pattern => by
      cases pattern with
      | collection kind elements rest =>
          cases kind <;> cases rest <;> simp [isClosedBag, collectionCode, optionStringCode_eq_zero]
      | _ => rfl) (const _) (const _) (const _) (const _) (const _) (const _) test

/-! ## The block of a process -/

theorem decomposeList_eq_foldr (block : Block) : ∀ elements : List Pattern,
    decomposeList block elements = elements.foldr (fun element rest => (decompose block element).par rest) Prenex.nil
  | [] => rfl
  | element :: elements => by rw [decomposeList, decomposeList_eq_foldr block elements, List.foldr_cons]

/-- The calls of `decompose`: the body of a restriction, the argument of a named multiset whose empty instance is
inaction, the members of a closed bag. -/
def decomposeCalls (block : Block) (_ : ℕ) (pattern : Pattern) : List (ℕ × Pattern) :=
  if isApply pattern && decide ((applyArguments pattern).length = 1) then
    if isLambda ((applyArguments pattern).getD 0 (.bvar 0)) then
      if decide (applyLabel pattern = block.restrict) then [(0, lambdaBody ((applyArguments pattern).getD 0 (.bvar 0)))] else []
    else if block.emptyUnits.contains (applyLabel pattern) then [(0, (applyArguments pattern).getD 0 (.bvar 0))] else []
  else if isClosedBag pattern then (collectionElements pattern).map fun element => (0, element)
  else []

/-- The combination of `decompose`. -/
def decomposeCombine (block : Block) (_ : ℕ) (pattern : Pattern) (values : List Prenex) : Prenex :=
  if isApply pattern && decide ((applyArguments pattern).length = 0) then
    if decide (applyLabel pattern = block.unit) then Prenex.nil else Prenex.atom pattern
  else if isApply pattern && decide ((applyArguments pattern).length = 1) then
    if isLambda ((applyArguments pattern).getD 0 (.bvar 0)) then
      if decide (applyLabel pattern = block.restrict) then (values.getD 0 Prenex.nil).close else Prenex.atom pattern
    else if block.emptyUnits.contains (applyLabel pattern) && decide (values.getD 0 Prenex.nil = Prenex.nil) then Prenex.nil
      else Prenex.atom pattern
  else if isClosedBag pattern then values.foldr Prenex.par Prenex.nil
  else Prenex.atom pattern

theorem decompose_node (block : Block) (parameter : ℕ) (pattern : Pattern) :
    decompose block pattern = decomposeCombine block parameter pattern
      ((decomposeCalls block parameter pattern).map fun call => decompose block call.2) := by
  cases pattern with
  | apply label arguments =>
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
      · by_cases unit : label = block.unit <;>
          simp [decompose, decomposeCombine, isApply, applyArguments, applyLabel, unit]
      · cases argument with
        | lambda binder body =>
            by_cases restricted : label = block.restrict <;>
              simp [decompose, decomposeCombine, decomposeCalls, isApply, applyArguments, applyLabel, isLambda,
                lambdaBody, restricted]
        | _ =>
            by_cases empty : label ∈ block.emptyUnits <;>
              simp [decompose, decomposeCombine, decomposeCalls, isApply, applyArguments, applyLabel, isLambda,
                empty]
      · simp [decompose, decomposeCombine, isApply, applyArguments, isClosedBag]
  | collection kind elements rest =>
      cases kind <;> cases rest <;>
        simp [decompose, decomposeCombine, decomposeCalls, isApply, isClosedBag, collectionElements,
          decomposeList_eq_foldr, List.foldr_map]
  | _ => simp [decompose, decomposeCombine, isApply, isClosedBag]

theorem decomposeCalls_smaller (block : Block) (parameter : ℕ) (pattern : Pattern) :
    ∀ call ∈ decomposeCalls block parameter pattern, patternCode call.2 < patternCode pattern := by
  intro call member
  cases pattern with
  | apply label arguments =>
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
      · simp [decomposeCalls, isApply, applyArguments, isClosedBag] at member
      · cases argument with
        | lambda binder body =>
            by_cases restricted : label = block.restrict <;>
              simp [decomposeCalls, isApply, applyArguments, applyLabel, isLambda, lambdaBody, restricted] at member
            subst member
            exact (patternCode_lt_lambda binder body).trans (patternCode_lt_apply (List.mem_singleton_self _))
        | _ =>
            by_cases empty : label ∈ block.emptyUnits <;>
              simp [decomposeCalls, isApply, applyArguments, applyLabel, isLambda, empty] at member
            subst member
            exact patternCode_lt_apply (List.mem_singleton_self _)
      · simp [decomposeCalls, isApply, applyArguments, isClosedBag] at member
  | collection kind elements rest =>
      cases kind <;> cases rest <;>
        simp [decomposeCalls, isApply, isClosedBag, collectionElements] at member
      obtain ⟨element, inElements, rfl⟩ := member
      exact patternCode_lt_collection inElements
  | _ => simp [decomposeCalls, isApply, isClosedBag] at member

theorem code_prenex_injective : Function.Injective (code : Prenex → ℕ) := by
  intro first second same
  simp only [code_prenex, code_pair, code_nat, code_list, Nat.pair_eq_pair] at same
  obtain ⟨counts, codes⟩ := same
  have components : first.components = second.components :=
    (List.map_injective_iff.mpr patternCode_injective') (Encodable.encode_injective codes)
  cases first; cases second
  simp_all

theorem decompose_codeComputable (block : Block) : CodeComputable (decompose block) := by
  have pattern : CodeComputable fun input : ℕ × Pattern => input.2 := snd
  have arguments := applyArguments_codeComputable.comp pattern
  have single : CodeComputable fun input : ℕ × Pattern =>
      isApply input.2 && decide ((applyArguments input.2).length = 1) :=
    and (isApply_codeComputable.comp pattern) (nat_eq (list_length arguments) (const 1))
  have first := list_getD (.bvar 0) arguments (const 0)
  have restricted : CodeComputable fun input : ℕ × Pattern => decide (applyLabel input.2 = block.restrict) :=
    stringEq.comp ((applyLabel_codeComputable.comp pattern).pair (const _))
  have emptyUnit : CodeComputable fun input : ℕ × Pattern => block.emptyUnits.contains (applyLabel input.2) :=
    list_contains stringCode_injective' (const _) (applyLabel_codeComputable.comp pattern)
  have calls : CodeComputable₂ (decomposeCalls block) :=
    (ite single (ite (isLambda_codeComputable.comp first)
        (ite restricted (list_cons ((const 0).pair (lambdaBody_codeComputable.comp first)) list_nil) list_nil)
        (ite emptyUnit (list_cons ((const 0).pair first) list_nil) list_nil))
      (ite (isClosedBag_codeComputable.comp pattern)
        (list_map (members := fun input : ℕ × Pattern => collectionElements input.2)
          (image := fun _ element => ((0 : ℕ), element)) (collectionElements_codeComputable.comp pattern)
          ((const 0).pair snd))
        list_nil)).of_eq fun _ => rfl
  have patternIn : CodeComputable fun input : ℕ × Pattern × List Prenex => input.2.1 := fst.comp snd
  have valuesIn : CodeComputable fun input : ℕ × Pattern × List Prenex => input.2.2 := snd.comp snd
  have argumentsIn := applyArguments_codeComputable.comp patternIn
  have labelIn := applyLabel_codeComputable.comp patternIn
  have combine : CodeComputable fun input : ℕ × Pattern × List Prenex =>
      decomposeCombine block input.1 input.2.1 input.2.2 :=
    (ite (and (isApply_codeComputable.comp patternIn) (nat_eq (list_length argumentsIn) (const 0)))
      (ite (stringEq.comp (labelIn.pair (const _))) nil (atom patternIn))
      (ite (and (isApply_codeComputable.comp patternIn) (nat_eq (list_length argumentsIn) (const 1)))
        (ite (isLambda_codeComputable.comp (list_getD (.bvar 0) argumentsIn (const 0)))
          (ite (stringEq.comp (labelIn.pair (const _))) (close (list_getD Prenex.nil valuesIn (const 0)))
            (atom patternIn))
          (ite (and (list_contains stringCode_injective' (const _) labelIn)
              ((beq_of_injective code_prenex_injective).comp ((list_getD Prenex.nil valuesIn (const 0)).pair nil)))
            nil (atom patternIn)))
        (ite (isClosedBag_codeComputable.comp patternIn)
          (list_foldr (step := fun _ form rest => form.par rest) valuesIn nil (par (fst.comp snd) (snd.comp snd)))
          (atom patternIn)))).of_eq fun _ => rfl
  exact (structural (value := fun (_ : ℕ) pattern => decompose block pattern) (decompose_node block)
    (decomposeCalls_smaller block) calls combine).comp ((const 0).pair CodeComputable.id)

/-! ## Reading a block back -/

theorem body_eq (block : Block) (components : List Pattern) :
    Prenex.body block components =
      if decide (components.length = 0) then .apply block.unit []
      else if decide (components.length = 1) then components.getD 0 (.bvar 0)
      else .collection .hashBag components none := by
  rcases components with _ | ⟨component, _ | ⟨second, rest⟩⟩ <;> rfl

theorem body_codeComputable (block : Block) {components : α → List Pattern} (hComponents : CodeComputable components) :
    CodeComputable fun argument => Prenex.body block (components argument) :=
  (ite (nat_eq (list_length hComponents) (const 0)) (const _)
    (ite (nat_eq (list_length hComponents) (const 1)) (list_getD (.bvar 0) hComponents (const 0))
      (collection (const _) hComponents (const _)))).of_eq fun _ => (body_eq block _).symm

/-- One restriction around a process. -/
def wrapRestriction (block : Block) (process : Pattern) : Pattern := .apply block.restrict [.lambda none process]

theorem restricts_eq_iterate (block : Block) (process : Pattern) :
    ∀ count, Prenex.restricts block count process = (wrapRestriction block)^[count] process
  | 0 => rfl
  | count + 1 => by
      rw [Function.iterate_succ_apply', ← restricts_eq_iterate block process count]
      rfl

theorem toPattern_codeComputable (block : Block) {form : α → Prenex} (hForm : CodeComputable form) :
    CodeComputable fun argument => Prenex.toPattern block (form argument) := by
  have wrapped : CodeComputable₂ fun (_ : α) (process : Pattern) => wrapRestriction block process :=
    apply (const _) (list_cons (lambda (const none) snd) list_nil)
  exact (iterate (count.comp hForm) (body_codeComputable block (components.comp hForm)) wrapped).of_eq
    fun argument => (restricts_eq_iterate block _ _).symm

theorem multisetOf_codeComputable (block : Block) {form : α → Prenex} (hForm : CodeComputable form) :
    CodeComputable fun argument => multisetOf block (form argument) :=
  (ite (nat_eq (count.comp hForm) (const 0))
    (collection (kind := fun _ => CollType.hashBag) (rest := fun _ => none) (const _) (components.comp hForm)
      (const _))
    (collection (kind := fun _ => CollType.hashBag) (rest := fun _ => none) (const _)
      (list_cons (toPattern_codeComputable block hForm) list_nil) (const _))).of_eq
    fun argument => by
      unfold multisetOf
      by_cases zero : (form argument).count = 0 <;> simp [zero]

/-! ## The orders of the restrictions, and the least reading -/

theorem insertions_eq {β : Type} (element : β) : ∀ members : List β,
    insertions element members =
      (List.range (members.length + 1)).map fun position => members.take position ++ element :: members.drop position
  | [] => rfl
  | first :: rest => by
      rw [insertions, insertions_eq element rest, List.length_cons,
        List.range_succ_eq_map (n := rest.length + 1)]
      simp only [List.map_cons, List.map_map]
      exact congrArg₂ List.cons (by simp) (List.map_congr_left fun position _ => by simp)

theorem orders_eq_foldr {β : Type} : ∀ members : List β,
    orders members = members.foldr (fun first rest => rest.flatMap (insertions first)) [[]]
  | [] => rfl
  | first :: rest => by rw [orders, orders_eq_foldr rest, List.foldr_cons]

theorem orders_codeComputable {members : α → List ℕ} (hMembers : CodeComputable members) :
    CodeComputable fun argument => orders (members argument) := by
  have inserted : CodeComputable fun input : ℕ × List ℕ =>
      insertions input.1 input.2 :=
    (list_map (members := fun input : ℕ × List ℕ => List.range (input.2.length + 1))
      (image := fun input position => input.2.take position ++ input.1 :: input.2.drop position)
      (list_range (nat_add (list_length snd) (const 1)))
      (list_append (list_take snd (snd.comp fst)) (list_cons (fst.comp fst) (list_drop snd (snd.comp fst))))).of_eq
      fun input => (insertions_eq _ _).symm
  exact (list_foldr (start := fun _ => [[]]) (step := fun _ first rest => rest.flatMap (insertions first))
    hMembers (const _) (list_flatMap (snd.comp snd) (inserted.comp ((fst.comp (snd.comp fst)).pair snd)))).of_eq
    fun argument => (orders_eq_foldr _).symm

theorem lexLe_codeComputable : CodeComputable₂ Mettapedia.OSLF.MeTTaIL.PatternLexOrder.lexLe :=
  ⟨fun n => _root_.cond (Mettapedia.OSLF.MeTTaIL.PatternLexOrder.lexLe (Denumerable.ofNat (List ℕ) n.unpair.1)
      (Denumerable.ofNat (List ℕ) n.unpair.2)) 1 0,
    Computable.cond (Mettapedia.OSLF.MeTTaIL.PatternLexOrder.lexLe_primrec.to_comp.comp
      ((Primrec.ofNat (List ℕ)).to_comp.comp (Primrec.fst.to_comp.comp Primrec.unpair.to_comp))
      ((Primrec.ofNat (List ℕ)).to_comp.comp (Primrec.snd.to_comp.comp Primrec.unpair.to_comp)))
      (Computable.const 1) (Computable.const 0),
    fun pair => by simp [code_pair, ofNat_code_list]; rfl⟩

theorem least_eq (candidates : List (List Pattern)) :
    least candidates = candidates.tail.foldl
      (fun best next => if serList next < serList best then next else best) candidates.headI := by
  cases candidates <;> rfl

theorem least_codeComputable {candidates : α → List (List Pattern)} (hCandidates : CodeComputable candidates) :
    CodeComputable fun argument => least (candidates argument) := by
  have serialized : CodeComputable fun patterns : List Pattern => serList patterns :=
    (list_flatMap (members := fun patterns : List Pattern => patterns) (image := fun _ pattern => ser pattern)
      CodeComputable.id (ser'.comp snd)).of_eq fun patterns =>
      (Mettapedia.OSLF.MeTTaIL.PatternLexOrder.serList_eq_flatMap patterns).symm
  have smaller : CodeComputable fun input : α × List Pattern × List Pattern =>
      decide (serList input.2.2 < serList input.2.1) :=
    (not (lexLe_codeComputable.comp ((serialized.comp (fst.comp snd)).pair (serialized.comp (snd.comp snd))))).of_eq
      fun input => (Mettapedia.OSLF.MeTTaIL.PatternLexOrder.decide_lt_eq_lexLe _ _).symm
  refine (list_foldl (step := fun _ best next => if decide (serList next < serList best) then next else best)
    (list_tail hCandidates) (list_headI hCandidates) (ite smaller (snd.comp snd) (fst.comp snd))).of_eq
    fun argument => ?_
  rw [least_eq]
  congr 1
  funext best next
  simp only [decide_eq_true_eq]

/-! ## More shapes -/

/-- Whether a pattern is a binder of one or more variables. -/
def isBinder : Pattern → Bool
  | .lambda _ _ => true
  | .multiLambda _ _ _ => true
  | _ => false

/-- The body of a binder, a bound variable otherwise. -/
def binderBody : Pattern → Pattern
  | .lambda _ body => body
  | .multiLambda _ _ body => body
  | _ => .bvar 0

/-- Whether a pattern is a collection. -/
def isCollection : Pattern → Bool
  | .collection _ _ _ => true
  | _ => false

/-- Whether a pattern is an open collection. -/
def isOpenCollection : Pattern → Bool
  | .collection _ _ (some _) => true
  | _ => false

/-- Whether a pattern is an explicit substitution. -/
def isSubst : Pattern → Bool
  | .subst _ _ => true
  | _ => false

/-- Whether a constructor argument is kept as it is by `canonArgument`: a variable or an explicit substitution. -/
def isKept : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .subst _ _ => true
  | _ => false

theorem isBinder_codeComputable : CodeComputable isBinder :=
  shape (onBVar := fun _ => false) (onFVar := fun _ => false) (onApply := fun _ _ => false)
    (onLambda := fun _ _ => true) (onMultiLambda := fun _ _ _ => true) (onSubst := fun _ _ => false)
    (onCollection := fun _ _ _ => false) (fun pattern => by cases pattern <;> rfl) (const _) (const _) (const _)
    (const _) (const _) (const _) (const _)

theorem binderBody_codeComputable : CodeComputable binderBody :=
  shape (onBVar := fun _ => .bvar 0) (onFVar := fun _ => .bvar 0) (onApply := fun _ _ => .bvar 0)
    (onLambda := fun _ body => body) (onMultiLambda := fun _ _ body => body) (onSubst := fun _ _ => .bvar 0)
    (onCollection := fun _ _ _ => .bvar 0) (fun pattern => by cases pattern <;> rfl) (const _) (const _) (const _)
    snd (snd.comp snd) (const _) (const _)

theorem isCollection_codeComputable : CodeComputable isCollection :=
  shape (onBVar := fun _ => false) (onFVar := fun _ => false) (onApply := fun _ _ => false)
    (onLambda := fun _ _ => false) (onMultiLambda := fun _ _ _ => false) (onSubst := fun _ _ => false)
    (onCollection := fun _ _ _ => true) (fun pattern => by cases pattern <;> rfl) (const _) (const _) (const _)
    (const _) (const _) (const _) (const _)

theorem isOpenCollection_codeComputable : CodeComputable isOpenCollection := by
  have test : CodeComputable fun input : CollType × List Pattern × Option String =>
      !decide (optionStringCode input.2.2 = 0) :=
    not (nat_eq (code'.comp (snd.comp snd)) (const 0))
  exact shape (onBVar := fun _ => false) (onFVar := fun _ => false) (onApply := fun _ _ => false)
    (onLambda := fun _ _ => false) (onMultiLambda := fun _ _ _ => false) (onSubst := fun _ _ => false)
    (onCollection := fun _ _ rest => !decide (optionStringCode rest = 0))
    (fun pattern => by
      cases pattern with
      | collection kind elements rest => cases rest <;> simp [isOpenCollection, optionStringCode_eq_zero]
      | _ => rfl) (const _) (const _) (const _) (const _) (const _) (const _) test

theorem isSubst_codeComputable : CodeComputable isSubst :=
  shape (onBVar := fun _ => false) (onFVar := fun _ => false) (onApply := fun _ _ => false)
    (onLambda := fun _ _ => false) (onMultiLambda := fun _ _ _ => false) (onSubst := fun _ _ => true)
    (onCollection := fun _ _ _ => false) (fun pattern => by cases pattern <;> rfl) (const _) (const _) (const _)
    (const _) (const _) (const _) (const _)

theorem isKept_codeComputable : CodeComputable isKept :=
  shape (onBVar := fun _ => true) (onFVar := fun _ => true) (onApply := fun _ _ => false)
    (onLambda := fun _ _ => false) (onMultiLambda := fun _ _ _ => false) (onSubst := fun _ _ => true)
    (onCollection := fun _ _ _ => false) (fun pattern => by cases pattern <;> rfl) (const _) (const _) (const _)
    (const _) (const _) (const _) (const _)

/-- A binder with its body replaced; any other pattern as it is. -/
def withBody (pattern body : Pattern) : Pattern :=
  match pattern with
  | .lambda binder _ => .lambda binder body
  | .multiLambda arity binders _ => .multiLambda arity binders body
  | other => other

/-- A collection with its members replaced; any other pattern as it is. -/
def withElements (pattern : Pattern) (elements : List Pattern) : Pattern :=
  match pattern with
  | .collection kind _ rest => .collection kind elements rest
  | other => other

theorem withBody_codeComputable : CodeComputable₂ withBody := by
  have cased := casesOn (pattern := fun input : Pattern × Pattern => input.1)
    (onBVar := fun input _ => input.1) (onFVar := fun input _ => input.1) (onApply := fun input _ _ => input.1)
    (onLambda := fun input binder _ => .lambda binder input.2)
    (onMultiLambda := fun input arity binders _ => .multiLambda arity binders input.2)
    (onSubst := fun input _ _ => input.1) (onCollection := fun input _ _ _ => input.1) fst (fst.comp fst)
    (fst.comp fst) (fst.comp fst) (lambda (fst.comp snd) (snd.comp fst))
    (multiLambda (fst.comp snd) (fst.comp (snd.comp snd)) (snd.comp fst)) (fst.comp fst) (fst.comp fst)
  exact cased.of_eq fun input => by rcases input with ⟨pattern, body⟩; cases pattern <;> rfl

theorem withElements_codeComputable : CodeComputable₂ withElements := by
  have cased := casesOn (pattern := fun input : Pattern × List Pattern => input.1)
    (onBVar := fun input _ => input.1) (onFVar := fun input _ => input.1) (onApply := fun input _ _ => input.1)
    (onLambda := fun input _ _ => input.1) (onMultiLambda := fun input _ _ _ => input.1)
    (onSubst := fun input _ _ => input.1)
    (onCollection := fun input kind _ rest => .collection kind input.2 rest) fst (fst.comp fst)
    (fst.comp fst) (fst.comp fst) (fst.comp fst) (fst.comp fst) (fst.comp fst)
    (collection (fst.comp snd) (snd.comp fst) (snd.comp (snd.comp snd)))
  exact cased.of_eq fun input => by rcases input with ⟨pattern, elements⟩; cases pattern <;> rfl

/-! ## The canonical form as one family within a fuel -/

/-- **The canonical forms within a fuel, as one family**: `0` the canonical form, `1` the canonical argument of a
named multiset, `2` a component with canonical parts, and any other tag keeps the pattern. -/
def canonFamily (block : Block) (fuel : ℕ) (input : ℕ × Pattern) : Pattern :=
  if input.1 = 0 then canonWith block fuel input.2
  else if input.1 = 1 then canonMultisetWith block fuel input.2
  else if input.1 = 2 then canonComponentWith block fuel input.2
  else input.2

/-- The call for a constructor argument outside a named multiset: the body of an abstraction or the argument,
canonically; a variable or explicit substitution kept. -/
def argumentCall (argument : Pattern) : ℕ × Pattern :=
  if isLambda argument then (0, lambdaBody argument) else if isKept argument then (3, argument) else (0, argument)

/-- The argument read back from its call's value. -/
def argumentRebuild (argument value : Pattern) : Pattern :=
  if isLambda argument then withBody argument value else value

/-- The calls of a block's canonical reading: every component under every order of its restrictions. -/
def blockCalls (block : Block) (pattern : Pattern) : List (ℕ × Pattern) :=
  (orders (List.range (decompose block pattern).count)).flatMap fun order =>
    (decompose block pattern).components.map fun component =>
      (2, rename (Prenex.permute (decompose block pattern).count order) component)

/-- The least reading of a block, from the values of its calls. -/
def blockLeast (block : Block) (pattern : Pattern) (values : List Pattern) : Prenex :=
  ⟨(decompose block pattern).count, least ((List.range (orders (List.range (decompose block pattern).count)).length).map
    fun position => sortComponents ((values.drop (position * (decompose block pattern).components.length)).take
      (decompose block pattern).components.length))⟩

/-- The calls of the family within one more fuel. -/
def familyCalls (block : Block) (_ : ℕ) (input : ℕ × Pattern) : List (ℕ × Pattern) :=
  if input.1 = 0 then blockCalls block input.2
  else if input.1 = 1 then
    if isOpenCollection input.2 then (collectionElements input.2).map fun element => (0, element)
    else if isSubst input.2 then [] else blockCalls block input.2
  else if input.1 = 2 then
    if isApply input.2 then
      if block.multisets.contains (applyLabel input.2) then
        (applyArguments input.2).map fun argument => (1, argument)
      else (applyArguments input.2).map argumentCall
    else if isBinder input.2 then [(0, binderBody input.2)]
    else if isCollection input.2 then (collectionElements input.2).map fun element => (0, element)
    else []
  else []

/-- The combination of the family within one more fuel. -/
def familyCombine (block : Block) (_ : ℕ) (input : ℕ × Pattern) (values : List Pattern) : Pattern :=
  if input.1 = 0 then Prenex.toPattern block (blockLeast block input.2 values)
  else if input.1 = 1 then
    if isOpenCollection input.2 then withElements input.2 values
    else if isSubst input.2 then input.2 else multisetOf block (blockLeast block input.2 values)
  else if input.1 = 2 then
    if isApply input.2 then
      if block.multisets.contains (applyLabel input.2) then .apply (applyLabel input.2) values
      else .apply (applyLabel input.2) (List.zipWith argumentRebuild (applyArguments input.2) values)
    else if isBinder input.2 then withBody input.2 (values.getD 0 (.bvar 0))
    else if isCollection input.2 then withElements input.2 values
    else input.2
  else input.2

/-- **Equal-length pieces of a concatenation come back.** -/
theorem chunks_flatMap {β γ : Type*} (pieces : β → List γ) (length : ℕ) :
    ∀ members : List β, (∀ member ∈ members, (pieces member).length = length) →
      (List.range members.length).map (fun position => ((members.flatMap pieces).drop (position * length)).take length) =
        members.map pieces
  | [], _ => rfl
  | member :: rest, lengths => by
      have first := lengths member List.mem_cons_self
      rw [List.length_cons, List.range_succ_eq_map (n := rest.length), List.map_cons, List.map_map, List.flatMap_cons,
        List.map_cons]
      refine congrArg₂ List.cons ?_ ?_
      · simp [List.take_left' first]
      · rw [← chunks_flatMap pieces length rest fun other inRest => lengths other (List.mem_cons_of_mem _ inRest)]
        apply List.map_congr_left
        intro position _
        simp only [Function.comp_apply, Nat.succ_mul, Nat.add_comm (position * length) length, ← List.drop_drop,
          List.drop_left' first]

theorem blockLeast_values (block : Block) (fuel : ℕ) (pattern : Pattern) :
    blockLeast block pattern ((blockCalls block pattern).map (canonFamily block fuel)) =
      ⟨(decompose block pattern).count, least ((orders (List.range (decompose block pattern).count)).map fun order =>
        sortComponents ((decompose block pattern).components.map fun component =>
          canonComponentWith block fuel (rename (Prenex.permute (decompose block pattern).count order) component)))⟩ := by
  have chunked := chunks_flatMap (fun order => (decompose block pattern).components.map fun component =>
      canonComponentWith block fuel (rename (Prenex.permute (decompose block pattern).count order) component))
    (decompose block pattern).components.length (orders (List.range (decompose block pattern).count))
    (fun _ _ => by simp)
  have values : (blockCalls block pattern).map (canonFamily block fuel) =
      (orders (List.range (decompose block pattern).count)).flatMap fun order =>
        (decompose block pattern).components.map fun component =>
          canonComponentWith block fuel (rename (Prenex.permute (decompose block pattern).count order) component) := by
    simp [blockCalls, List.map_flatMap, canonFamily, Function.comp_def]
  simp only [blockLeast, values]
  congr 2
  have sorted := congrArg (List.map sortComponents) chunked
  simpa [List.map_map, Function.comp_def] using sorted

theorem zipWith_map_self {β γ δ : Type*} (combine : β → γ → δ) (image : β → γ) :
    ∀ members : List β, List.zipWith combine members (members.map image) = members.map fun member =>
      combine member (image member)
  | [] => rfl
  | member :: rest => by simp [zipWith_map_self combine image rest]

theorem argumentRebuild_call (block : Block) (fuel : ℕ) (argument : Pattern) :
    argumentRebuild argument (canonFamily block fuel (argumentCall argument)) =
      canonArgument (canonWith block fuel) argument := by
  cases argument <;> simp [argumentRebuild, argumentCall, canonFamily, isLambda, isKept, lambdaBody, withBody,
    canonArgument]

theorem canonFamily_zero (block : Block) (input : ℕ × Pattern) : canonFamily block 0 input = input.2 := by
  simp only [canonFamily]
  split_ifs <;> simp [canonWith, canonMultisetWith, canonComponentWith]

theorem canonFamily_succ (block : Block) (fuel : ℕ) (input : ℕ × Pattern) :
    canonFamily block (fuel + 1) input =
      familyCombine block fuel input ((familyCalls block fuel input).map (canonFamily block fuel)) := by
  rcases input with ⟨tag, pattern⟩
  by_cases zero : tag = 0
  · subst zero
    simp only [canonFamily, familyCombine, familyCalls, if_true, canonWith, blockLeast_values]
  by_cases one : tag = 1
  · subst one
    cases pattern with
    | collection kind elements rest =>
        cases rest with
        | some rest => simp [canonFamily, familyCombine, familyCalls, isOpenCollection, withElements,
            collectionElements, canonMultisetWith, Function.comp_def]
        | none => simp [canonFamily, familyCombine, familyCalls, isOpenCollection, isSubst, canonMultisetWith,
            blockLeast_values]
    | subst body replacement => simp [canonFamily, familyCombine, isOpenCollection, isSubst,
        canonMultisetWith]
    | _ => simp [canonFamily, familyCombine, familyCalls, isOpenCollection, isSubst, canonMultisetWith,
        blockLeast_values]
  by_cases two : tag = 2
  · subst two
    cases pattern with
    | apply label arguments =>
        by_cases multiset : label ∈ block.multisets
        · simp [canonFamily, familyCombine, familyCalls, isApply, applyLabel, applyArguments, multiset,
            canonComponentWith, Function.comp_def]
        · simp only [canonFamily, familyCombine, familyCalls, isApply, applyLabel, applyArguments,
            canonComponentWith, if_true, if_neg multiset, if_false,
            show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide, List.contains_iff_mem,
            List.map_map, zipWith_map_self]
          congr 1
          exact List.map_congr_left fun argument _ => (argumentRebuild_call block fuel argument).symm
    | lambda binder body => simp [canonFamily, familyCombine, familyCalls, isApply, isBinder, binderBody, withBody,
        canonComponentWith]
    | multiLambda arity binders body => simp [canonFamily, familyCombine, familyCalls, isApply, isBinder, binderBody,
        withBody, canonComponentWith]
    | collection kind elements rest => simp [canonFamily, familyCombine, familyCalls, isApply, isBinder, isCollection,
        collectionElements, withElements, canonComponentWith, Function.comp_def]
    | _ => simp [canonFamily, familyCombine, isApply, isBinder, isCollection, canonComponentWith]
  simp [canonFamily, familyCombine, zero, one, two]

/-! ## The family is computable on codes -/

theorem blockCalls_codeComputable (block : Block) : CodeComputable (blockCalls block) := by
  have form := decompose_codeComputable block
  have counted := count.comp form
  exact list_flatMap (members := fun pattern => orders (List.range (decompose block pattern).count))
    (image := fun pattern order => (decompose block pattern).components.map fun component =>
      ((2 : ℕ), rename (Prenex.permute (decompose block pattern).count order) component))
    (orders_codeComputable (list_range counted))
    (list_map (members := fun input : Pattern × List ℕ => (decompose block input.1).components)
      (image := fun input component => ((2 : ℕ), rename (Prenex.permute (decompose block input.1).count input.2)
        component)) (components.comp (form.comp fst))
      ((const 2).pair (rename_permute.comp (((counted.comp (fst.comp fst)).pair (snd.comp fst)).pair snd))))

theorem blockLeast_codeComputable (block : Block) :
    CodeComputable₂ (blockLeast block) := by
  have form := (decompose_codeComputable block).comp (fst : CodeComputable fun input : Pattern × List Pattern => input.1)
  have size := list_length (components.comp form)
  have readings := list_length (orders_codeComputable (list_range (count.comp form)))
  have chunk : CodeComputable fun input : (Pattern × List Pattern) × ℕ =>
      sortComponents ((input.1.2.drop (input.2 * (decompose block input.1.1).components.length)).take
        (decompose block input.1.1).components.length) :=
    insertionSort'.comp (list_take (size.comp fst) (list_drop (nat_mul snd (size.comp fst)) (snd.comp fst)))
  exact prenex (count.comp form) (least_codeComputable (list_map (list_range readings) chunk))

theorem argumentCall_codeComputable : CodeComputable argumentCall :=
  (ite isLambda_codeComputable ((const 0).pair lambdaBody_codeComputable)
    (ite isKept_codeComputable ((const 3).pair CodeComputable.id) ((const 0).pair CodeComputable.id))).of_eq
    fun _ => rfl

theorem argumentRebuild_codeComputable : CodeComputable₂ argumentRebuild :=
  (ite (isLambda_codeComputable.comp fst) withBody_codeComputable snd).of_eq fun _ => rfl

theorem familyCalls_codeComputable (block : Block) : CodeComputable₂ (familyCalls block) := by
  have tag : CodeComputable fun input : ℕ × ℕ × Pattern => input.2.1 := fst.comp snd
  have pattern : CodeComputable fun input : ℕ × ℕ × Pattern => input.2.2 := snd.comp snd
  have elements := list_map (members := fun input : ℕ × ℕ × Pattern => collectionElements input.2.2)
    (image := fun _ element => ((0 : ℕ), element)) (collectionElements_codeComputable.comp pattern)
    ((const 0).pair snd)
  have blockReading := (blockCalls_codeComputable block).comp pattern
  have arguments := applyArguments_codeComputable.comp pattern
  have computed := ite (nat_eq tag (const 0)) blockReading
    (ite (nat_eq tag (const 1))
      (ite (isOpenCollection_codeComputable.comp pattern) elements
        (ite (isSubst_codeComputable.comp pattern) list_nil blockReading))
      (ite (nat_eq tag (const 2))
        (ite (isApply_codeComputable.comp pattern)
          (ite (list_contains stringCode_injective' (const block.multisets) (applyLabel_codeComputable.comp pattern))
            (list_map (members := fun input : ℕ × ℕ × Pattern => applyArguments input.2.2)
              (image := fun _ argument => ((1 : ℕ), argument)) arguments ((const 1).pair snd))
            (list_map (members := fun input : ℕ × ℕ × Pattern => applyArguments input.2.2)
              (image := fun _ argument => argumentCall argument) arguments (argumentCall_codeComputable.comp snd)))
          (ite (isBinder_codeComputable.comp pattern)
            (list_cons ((const 0).pair (binderBody_codeComputable.comp pattern)) list_nil)
            (ite (isCollection_codeComputable.comp pattern) elements list_nil)))
        list_nil))
  refine computed.of_eq fun input => ?_
  simp only [familyCalls, decide_eq_true_eq]

theorem familyCombine_codeComputable (block : Block) :
    CodeComputable fun input : ℕ × (ℕ × Pattern) × List Pattern =>
      familyCombine block input.1 input.2.1 input.2.2 := by
  have tag : CodeComputable fun input : ℕ × (ℕ × Pattern) × List Pattern => input.2.1.1 := fst.comp (fst.comp snd)
  have pattern : CodeComputable fun input : ℕ × (ℕ × Pattern) × List Pattern => input.2.1.2 :=
    snd.comp (fst.comp snd)
  have values : CodeComputable fun input : ℕ × (ℕ × Pattern) × List Pattern => input.2.2 := snd.comp snd
  have leastReading := (blockLeast_codeComputable block).comp (pattern.pair values)
  have label := applyLabel_codeComputable.comp pattern
  have computed := ite (nat_eq tag (const 0)) (toPattern_codeComputable block leastReading)
    (ite (nat_eq tag (const 1))
      (ite (isOpenCollection_codeComputable.comp pattern) (withElements_codeComputable.comp (pattern.pair values))
        (ite (isSubst_codeComputable.comp pattern) pattern (multisetOf_codeComputable block leastReading)))
      (ite (nat_eq tag (const 2))
        (ite (isApply_codeComputable.comp pattern)
          (ite (list_contains stringCode_injective' (const block.multisets) label) (apply label values)
            (apply label (list_zipWith (combine := fun _ argument value => argumentRebuild argument value)
              (.bvar 0) (.bvar 0) (applyArguments_codeComputable.comp pattern) values
              (argumentRebuild_codeComputable.comp snd))))
          (ite (isBinder_codeComputable.comp pattern)
            (withBody_codeComputable.comp (pattern.pair (list_getD (.bvar 0) values (const 0))))
            (ite (isCollection_codeComputable.comp pattern) (withElements_codeComputable.comp (pattern.pair values))
              pattern)))
        pattern))
  refine computed.of_eq fun input => ?_
  simp only [familyCombine, decide_eq_true_eq]

/-- **The canonical forms within a fuel are computable on codes.** -/
theorem canonFamily_codeComputable (block : Block) : CodeComputable₂ (canonFamily block) :=
  fuel (canonFamily_zero block) (canonFamily_succ block) snd (familyCalls_codeComputable block)
    (familyCombine_codeComputable block)

/-- **The canonical form of a calculus with restriction is computable on codes.** -/
theorem canon_codeComputable (block : Block) : CodeComputable (canon block) :=
  ((canonFamily_codeComputable block).comp ((nat_add (nat_mul (const 2) size_codeComputable) (const 2)).pair
    ((const 0).pair CodeComputable.id))).of_eq fun pattern => by simp [canon, canonFamily]

end FormCodes

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
