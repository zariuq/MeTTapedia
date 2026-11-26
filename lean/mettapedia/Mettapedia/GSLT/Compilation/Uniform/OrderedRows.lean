import Mettapedia.GSLT.Compilation.RootRewritesOnTheStep
import Mettapedia.GSLT.Compilation.Uniform.OrderedMatching

/-!
# Ordered patterns as row patterns

A vector is the row of its list. A variable that is a rest somewhere in its rule (`rests`)
has the tail's list as its unknown, wherever it occurs: alone it is written as the vector
of that list, and as a rest it closes the list of the elements before it.

* `inst_lower`: lowering commutes with instantiation.
* `lower_captures`: where a lowered pattern meets a source row, every unknown holds a
  source row, or a source list for a rest.
* `exists_witness`: such unknowns are one list of bindings.
* `unknowns_lower`: the unknowns are the codes of the variables, rests included.

Controls: a head and a tail are lowered (`Controls.head_tail_lowers`), and a bag is not
(`Controls.bag_not_lowered`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.OrderedRows

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode)
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines
open RootRewritesOnTheStep (labelCode appTerm symTerm encode encodeList)
open OrderedMatching (names namesList)

/-- The row pattern of a closed vector with the given list. -/
def vectorTerm (list : Tm) : Tm :=
  appTerm (symTerm 6) (appTerm (symTerm (collectionCode .vec)) (appTerm list (symTerm 0)))

theorem inst_vectorTerm {θ : ℕ → Expr} {list : Tm} {items : List Pattern} (listed : inst θ list = encodeList items) :
    inst θ (vectorTerm list) = encode (.collection .vec items none) := by
  simp [vectorTerm, encode, listed, RootRewritesOnTheStep.optionRow]

mutual
  /-- An ordered pattern as a row pattern. -/
  def lower? (rests : List String) : Pattern → Option Tm
    | .fvar name =>
        some (if name ∈ rests then vectorTerm (.var (labelCode name)) else .var (labelCode name))
    | .bvar index => RootRewritesOnTheStep.lower? (.bvar index)
    | .apply label arguments => (lowerThen? rests arguments (symTerm 0)).map fun list =>
        appTerm (symTerm 2) (appTerm (symTerm (labelCode label)) list)
    | .collection .vec elements none => (lowerThen? rests elements (symTerm 0)).map vectorTerm
    | .collection .vec elements (some rest) =>
        if rest ∈ rests then (lowerThen? rests elements (.var (labelCode rest))).map vectorTerm else none
    | .collection _ _ _ => none
    | .lambda _ _ => none
    | .multiLambda _ _ _ => none
    | .subst _ _ => none

  /-- The patterns as one list, closed by the given tail. -/
  def lowerThen? (rests : List String) : List Pattern → Tm → Option Tm
    | [], close => some close
    | pattern :: patterns, close => (lower? rests pattern).bind fun head =>
        (lowerThen? rests patterns close).map fun tail => appTerm head tail
end

/-- What an unknown holds under a witness: the row of the value, or the list of a rest. -/
def Holds (rests : List String) (θ : ℕ → Expr) (witness : Bindings) (name : String) : Prop :=
  if name ∈ rests then
    ∃ tail, lookupOrFvar witness name = .collection .vec tail none ∧ θ (labelCode name) = encodeList tail
  else θ (labelCode name) = encode (lookupOrFvar witness name)

mutual
  /-- **Lowering commutes with instantiation.** -/
  theorem inst_lower {rests : List String} {θ : ℕ → Expr} {witness : Bindings} : ∀ (pattern : Pattern) {term : Tm},
      lower? rests pattern = some term → (∀ name ∈ names pattern, Holds rests θ witness name) →
      inst θ term = encode (applyBindings witness pattern)
    | .fvar name, _, lowered, holds => by
        have held := holds name (by simp [names])
        simp only [lower?, Option.some.injEq] at lowered
        subst lowered
        unfold Holds at held
        split at held
        · rename_i inRests
          obtain ⟨tail, value, listed⟩ := held
          rw [if_pos inRests, inst_vectorTerm (list := .var (labelCode name)) (items := tail) listed]
          exact congrArg encode value.symm
        · rename_i outside
          rw [if_neg outside]
          exact held
    | .bvar index, term, lowered, _ => by
        exact RootRewritesOnTheStep.inst_lower θ witness (.bvar index) term lowered (by simp [freeVars])
    | .apply _ arguments, _, lowered, holds => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨list, listLowered, rfl⟩ := lowered
        simp only [names] at holds
        have listed := inst_lowerThen arguments listLowered holds (tail := []) (by simp [encodeList])
        simp [applyBindings, encode, listed]
    | .collection .vec elements none, _, lowered, holds => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨list, listLowered, rfl⟩ := lowered
        simp only [names, Option.toList_none, List.append_nil] at holds
        rw [inst_vectorTerm (inst_lowerThen elements listLowered holds (tail := []) (by simp [encodeList]))]
        simp [applyBindings]
    | .collection .vec elements (some rest), _, lowered, holds => by
        simp only [lower?] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff] at lowered
          obtain ⟨list, listLowered, rfl⟩ := lowered
          have held := holds rest (by simp [names])
          simp only [Holds, if_pos inRests] at held
          obtain ⟨tail, value, closed⟩ := held
          rw [inst_vectorTerm (inst_lowerThen elements listLowered
            (fun name member => holds name (by simp [names, member])) (tail := tail) closed)]
          simp only [lookupOrFvar, applyBindings] at value
          cases found : witness.find? (·.1 == rest) with
          | none => simp [found] at value
          | some entry =>
            obtain ⟨_, bound⟩ := entry
            simp only [found] at value
            subst value
            simp [applyBindings, found]
        · cases lowered
    | .collection .hashBag _ _, _, lowered, _ => by simp [lower?] at lowered
    | .collection .hashSet _ _, _, lowered, _ => by simp [lower?] at lowered
    | .lambda _ _, _, lowered, _ => by simp [lower?] at lowered
    | .multiLambda _ _ _, _, lowered, _ => by simp [lower?] at lowered
    | .subst _ _, _, lowered, _ => by simp [lower?] at lowered

  theorem inst_lowerThen {rests : List String} {θ : ℕ → Expr} {witness : Bindings} :
      ∀ (patterns : List Pattern) {close list : Tm}, lowerThen? rests patterns close = some list →
      (∀ name ∈ namesList patterns, Holds rests θ witness name) →
      ∀ {tail : List Pattern}, inst θ close = encodeList tail →
        inst θ list = encodeList (patterns.map (applyBindings witness) ++ tail)
    | [], _, _, lowered, _, _, closed => by
        simp only [lowerThen?, Option.some.injEq] at lowered
        subst lowered
        simpa using closed
    | pattern :: patterns, _, _, lowered, holds, _, closed => by
        simp only [lowerThen?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
        obtain ⟨head, headLowered, others, othersLowered, rfl⟩ := lowered
        simp [encodeList,
          inst_lower pattern headLowered fun name member => holds name (by simp [namesList, member]),
          inst_lowerThen patterns othersLowered (fun name member => holds name (by simp [namesList, member])) closed]
end

/-- What an unknown may hold: a source row, or a source list for a rest. -/
def Captured (rests : List String) (θ : ℕ → Expr) (name : String) : Prop :=
  if name ∈ rests then ∃ tail, θ (labelCode name) = encodeList tail
  else ∃ value, θ (labelCode name) = encode value

theorem list_of_vectorTerm {θ : ℕ → Expr} {list : Tm} {source : Pattern}
    (met : inst θ (vectorTerm list) = encode source) : ∃ items, inst θ list = encodeList items := by
  cases source <;> simp [vectorTerm, encode] at met
  exact ⟨_, met.2.1⟩

mutual
  /-- **A lowered pattern captures source terms only.** -/
  theorem lower_captures {rests : List String} {θ : ℕ → Expr} : ∀ (pattern : Pattern) {term : Tm} {source : Pattern},
      lower? rests pattern = some term → inst θ term = encode source →
      ∀ name ∈ names pattern, Captured rests θ name
    | .fvar name, _, source, lowered, met => by
        simp only [lower?, Option.some.injEq] at lowered
        subst lowered
        intro other member
        simp only [names, List.mem_singleton] at member
        subst member
        unfold Captured
        split
        · rename_i inRests
          rw [if_pos inRests] at met
          exact list_of_vectorTerm (list := .var _) met
        · rename_i outside
          rw [if_neg outside] at met
          exact ⟨source, met⟩
    | .bvar _, _, _, _, _ => by simp [names]
    | .apply _ arguments, _, source, lowered, met => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨list, listLowered, rfl⟩ := lowered
        cases source <;> simp [encode] at met
        simpa only [names] using (lowerThen_captures arguments listLowered met.2).1
    | .collection .vec elements none, _, _, lowered, met => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨list, listLowered, rfl⟩ := lowered
        obtain ⟨items, listed⟩ := list_of_vectorTerm met
        simpa only [names, Option.toList_none, List.append_nil] using (lowerThen_captures elements listLowered listed).1
    | .collection .vec elements (some rest), _, _, lowered, met => by
        simp only [lower?] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff] at lowered
          obtain ⟨list, listLowered, rfl⟩ := lowered
          obtain ⟨items, listed⟩ := list_of_vectorTerm met
          obtain ⟨inElements, tail, closed⟩ := lowerThen_captures elements listLowered listed
          intro name member
          simp only [names, Option.toList_some, List.mem_append, List.mem_singleton] at member
          rcases member with before | rfl
          · exact inElements name before
          · simp only [Captured, if_pos inRests]
            exact ⟨tail, closed⟩
        · cases lowered
    | .collection .hashBag _ _, _, _, lowered, _ => by simp [lower?] at lowered
    | .collection .hashSet _ _, _, _, lowered, _ => by simp [lower?] at lowered
    | .lambda _ _, _, _, lowered, _ => by simp [lower?] at lowered
    | .multiLambda _ _ _, _, _, lowered, _ => by simp [lower?] at lowered
    | .subst _ _, _, _, lowered, _ => by simp [lower?] at lowered

  theorem lowerThen_captures {rests : List String} {θ : ℕ → Expr} :
      ∀ (patterns : List Pattern) {close list : Tm} {items : List Pattern},
      lowerThen? rests patterns close = some list → inst θ list = encodeList items →
      (∀ name ∈ namesList patterns, Captured rests θ name) ∧ ∃ tail, inst θ close = encodeList tail
    | [], _, _, items, lowered, met => by
        simp only [lowerThen?, Option.some.injEq] at lowered
        subst lowered
        exact ⟨by simp [namesList], items, met⟩
    | pattern :: patterns, _, _, items, lowered, met => by
        simp only [lowerThen?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
        obtain ⟨head, headLowered, others, othersLowered, rfl⟩ := lowered
        cases items <;> simp [encodeList] at met
        obtain ⟨later, closed⟩ := lowerThen_captures patterns othersLowered met.2
        refine ⟨fun name member => ?_, closed⟩
        simp only [namesList, List.mem_append] at member
        rcases member with here | after
        · exact lower_captures pattern headLowered met.1 name here
        · exact later name after
end

/-- **Captured unknowns are one witness.** -/
theorem exists_witness {rests : List String} {θ : ℕ → Expr} : ∀ (wanted : List String),
    (∀ name ∈ wanted, Captured rests θ name) →
    ∃ witness : Bindings, ∀ name ∈ wanted, Holds rests θ witness name
  | [], _ => ⟨[], by simp⟩
  | first :: others, captured => by
      obtain ⟨witness, holds⟩ := exists_witness others fun name member => captured name (by simp [member])
      have here := captured first (by simp)
      have value : ∃ bound, Holds rests θ ((first, bound) :: witness) first := by
        unfold Captured at here
        split at here
        · rename_i inRests
          obtain ⟨tail, listed⟩ := here
          exact ⟨.collection .vec tail none, by simp [Holds, inRests, lookupOrFvar, applyBindings, listed]⟩
        · rename_i outside
          obtain ⟨bound, encoded⟩ := here
          exact ⟨bound, by simp [Holds, outside, lookupOrFvar, applyBindings, encoded]⟩
      obtain ⟨bound, firstHolds⟩ := value
      refine ⟨(first, bound) :: witness, fun name member => ?_⟩
      by_cases same : first = name
      · subst same
        exact firstHolds
      · have later : name ∈ others := (List.mem_cons.mp member).resolve_left fun equal => same equal.symm
        simpa [Holds, lookupOrFvar, applyBindings, same] using holds name later

mutual
  /-- **The unknowns are the variables.** -/
  theorem unknowns_lower {rests : List String} : ∀ (pattern : Pattern) {term : Tm},
      lower? rests pattern = some term → unknowns term = (names pattern).map labelCode
    | .fvar name, _, lowered => by
        simp only [lower?, Option.some.injEq] at lowered
        subst lowered
        split <;> simp [vectorTerm, unknowns, names]
    | .bvar index, term, lowered => by
        rw [RootRewritesOnTheStep.unknowns_lower (.bvar index) term lowered]
        simp [freeVars, names]
    | .apply _ arguments, _, lowered => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨list, listLowered, rfl⟩ := lowered
        simp [names, unknowns_lowerThen arguments listLowered]
    | .collection .vec elements none, _, lowered => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨list, listLowered, rfl⟩ := lowered
        simp [names, vectorTerm, unknowns_lowerThen elements listLowered]
    | .collection .vec elements (some rest), _, lowered => by
        simp only [lower?] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff] at lowered
          obtain ⟨list, listLowered, rfl⟩ := lowered
          simp [names, vectorTerm, unknowns, unknowns_lowerThen elements listLowered]
        · cases lowered
    | .collection .hashBag _ _, _, lowered => by simp [lower?] at lowered
    | .collection .hashSet _ _, _, lowered => by simp [lower?] at lowered
    | .lambda _ _, _, lowered => by simp [lower?] at lowered
    | .multiLambda _ _ _, _, lowered => by simp [lower?] at lowered
    | .subst _ _, _, lowered => by simp [lower?] at lowered

  theorem unknowns_lowerThen {rests : List String} : ∀ (patterns : List Pattern) {close list : Tm},
      lowerThen? rests patterns close = some list →
      unknowns list = (namesList patterns).map labelCode ++ unknowns close
    | [], _, _, lowered => by
        simp only [lowerThen?, Option.some.injEq] at lowered
        subst lowered
        simp [namesList]
    | pattern :: patterns, _, _, lowered => by
        simp only [lowerThen?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
        obtain ⟨head, headLowered, others, othersLowered, rfl⟩ := lowered
        simp [namesList, unknowns_lower pattern headLowered, unknowns_lowerThen patterns othersLowered]
end

/-! ## Controls -/

namespace Controls

/-- **Positive**: a head and a tail. -/
theorem head_tail_lowers : ∃ term, lower? ["tail"] OrderedMatching.Controls.headTail = some term := by
  simp [lower?, lowerThen?, OrderedMatching.Controls.headTail]

/-- **Negative**: a bag is no ordered pattern. -/
theorem bag_not_lowered : lower? [] (.collection .hashBag [.fvar "x"] none) = none := by
  simp [lower?]

end Controls

#print axioms inst_lower
#print axioms lower_captures
#print axioms exists_witness
#print axioms unknowns_lower
#print axioms Controls.head_tail_lowers
#print axioms Controls.bag_not_lowered

end Mettapedia.GSLT.Compilation.Uniform.OrderedRows
