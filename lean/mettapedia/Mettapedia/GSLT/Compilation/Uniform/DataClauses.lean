import Mettapedia.GSLT.Compilation.Uniform.DemandTransformation
import Mettapedia.GSLT.Compilation.Uniform.OrderedMatching

/-!
# Data over a supply of labels, as clauses

A clause program produces only the labels its clauses and its input hold: a label is an atomic constant of the row it
is in. A value that a clause may choose freely, such as a name that one side of an equation has and the other lacks, so
ranges over the data built from labels the run is given: a **supply** (`supplyClause`), like a bound on the work of a
run. Reachability is then the union over supplies.

The relation of data (`datumRelation`) relates the unit to the row of every data term whose labels are in the supply,
and to nothing else (`datum_iff`): bound indices and binder arities are numbers (`numeralRelation`), names and
constructor labels come from the supply, and the other forms are built from data. Its clauses read no input, so they
are moded (`dataClauses_moded`).

Controls: `Controls.supplied` (a term over the supply is data of the relation) and `Controls.unsupplied` (a term with
a label outside the supply is not).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.DataClauses

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode collectionCode_injective)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.ComputedConditions (Relations)
open RootRewritesOnTheStep (symTerm appTerm encode encodeList numeral labelCode labelCode_injective inst_appTerm
  inst_symTerm)
open OrderedMatching (isData isDataList)
open DemandTransformation (Goal Clause goalHolds DerivesAt Derives)

/-! ## The labels of a term -/

mutual
  /-- The names and constructor labels of a term. -/
  def labelsOf : Pattern → List String
    | .bvar _ => []
    | .fvar name => [name]
    | .apply label arguments => label :: labelsOfList arguments
    | .lambda _ body => labelsOf body
    | .multiLambda _ _ body => labelsOf body
    | .subst body value => labelsOf body ++ labelsOf value
    | .collection _ elements _ => labelsOfList elements

  /-- The names and constructor labels of some terms. -/
  def labelsOfList : List Pattern → List String
    | [] => []
    | term :: terms => labelsOf term ++ labelsOfList terms
end

/-! ## The clauses -/

/-- The relation from the unit to the row of a data term over the supply. -/
def datumRelation : ℕ := 41

/-- The relation from the unit to the row of a list of data terms over the supply. -/
def datumListRelation : ℕ := 42

/-- The relation from the unit to every number. -/
def numeralRelation : ℕ := 43

/-- The relation from the unit to every label of the supply. -/
def supplyRelation : ℕ := 44

/-- The unit row. -/
def unitTerm : Tm := symTerm 0

def numeralZero : Clause := { relation := numeralRelation, input := unitTerm, output := symTerm 0, body := [] }

def numeralSucc : Clause :=
  { relation := numeralRelation, input := unitTerm, output := appTerm (symTerm 1) (.var 0),
    body := [.ask numeralRelation unitTerm (.var 0)] }

def datumBvar : Clause :=
  { relation := datumRelation, input := unitTerm, output := appTerm (symTerm 0) (.var 0),
    body := [.ask numeralRelation unitTerm (.var 0)] }

def datumFvar : Clause :=
  { relation := datumRelation, input := unitTerm, output := appTerm (symTerm 1) (.var 0),
    body := [.ask supplyRelation unitTerm (.var 0)] }

def datumApply : Clause :=
  { relation := datumRelation, input := unitTerm, output := appTerm (symTerm 2) (appTerm (.var 0) (.var 1)),
    body := [.ask supplyRelation unitTerm (.var 0), .ask datumListRelation unitTerm (.var 1)] }

def datumLambda : Clause :=
  { relation := datumRelation, input := unitTerm, output := appTerm (symTerm 3) (appTerm (symTerm 0) (.var 0)),
    body := [.ask datumRelation unitTerm (.var 0)] }

def datumMultiLambda : Clause :=
  { relation := datumRelation, input := unitTerm,
    output := appTerm (symTerm 4) (appTerm (.var 0) (appTerm (symTerm 0) (.var 1))),
    body := [.ask numeralRelation unitTerm (.var 0), .ask datumRelation unitTerm (.var 1)] }

def datumSubst : Clause :=
  { relation := datumRelation, input := unitTerm, output := appTerm (symTerm 5) (appTerm (.var 0) (.var 1)),
    body := [.ask datumRelation unitTerm (.var 0), .ask datumRelation unitTerm (.var 1)] }

def datumCollection (kind : CollType) : Clause :=
  { relation := datumRelation, input := unitTerm,
    output := appTerm (symTerm 6) (appTerm (symTerm (collectionCode kind)) (appTerm (.var 0) (symTerm 0))),
    body := [.ask datumListRelation unitTerm (.var 0)] }

def datumNil : Clause := { relation := datumListRelation, input := unitTerm, output := symTerm 0, body := [] }

def datumCons : Clause :=
  { relation := datumListRelation, input := unitTerm, output := appTerm (.var 0) (.var 1),
    body := [.ask datumRelation unitTerm (.var 0), .ask datumListRelation unitTerm (.var 1)] }

/-- **The clauses of data**: numbers, and every form of data built from the supply and from data. -/
def dataClauses : List Clause :=
  [numeralZero, numeralSucc, datumBvar, datumFvar, datumApply, datumLambda, datumMultiLambda, datumSubst,
    datumCollection .vec, datumCollection .hashBag, datumCollection .hashSet, datumNil, datumCons]

/-- A label of the supply, as a clause. -/
def supplyClause (label : String) : Clause :=
  { relation := supplyRelation, input := unitTerm, output := symTerm (labelCode label), body := [] }

/-- The supply as clauses. -/
def supplyClauses (supply : List String) : List Clause := supply.map supplyClause

/-- **A program with the clauses of data over a supply**, and no other clauses of their relations. -/
structure DataProgram (supply : List String) (program : List Clause) : Prop where
  data : ∀ c ∈ dataClauses, c ∈ program
  supplied : ∀ label ∈ supply, supplyClause label ∈ program
  onlyData : ∀ c ∈ program, (c.relation = datumRelation ∨ c.relation = datumListRelation ∨
    c.relation = numeralRelation) → c ∈ dataClauses
  onlySupply : ∀ c ∈ program, c.relation = supplyRelation → ∃ label ∈ supply, c = supplyClause label

theorem dataClauses_moded : ∀ c ∈ dataClauses, DemandTransformation.Moded c := by
  intro c inside
  simp only [dataClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact DemandTransformation.moded_of_check (by decide)

theorem supplyClause_moded (label : String) : DemandTransformation.Moded (supplyClause label) :=
  DemandTransformation.moded_of_inputsBound (.nil _) fun x inside => by
    simp [supplyClause, symTerm, RuleSyntax.Machines.unknowns] at inside

theorem dataClauses_relation : ∀ c ∈ dataClauses,
    c.relation = datumRelation ∨ c.relation = datumListRelation ∨ c.relation = numeralRelation := by
  intro c inside
  simp only [dataClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## What the clauses relate -/

theorem collection_row {θ : ℕ → Expr} {kind : CollType} {elements : List Pattern}
    (elementsIs : θ 0 = encodeList elements) :
    inst θ (datumCollection kind).output = encode (.collection kind elements none) := by
  simp [datumCollection, elementsIs, encode, RootRewritesOnTheStep.optionRow]

variable {R : Relations} {program : List Clause} {supply : List String}

theorem numeral_sound (data : DataProgram supply program) :
    ∀ (depth : ℕ) {x : Expr}, DerivesAt R program depth numeralRelation (.sym 0) x → ∃ n, x = numeral n
  | 0, _, derived => derived.elim
  | depth + 1, x, ⟨c, member, isNumeral, θ, _, output, goals⟩ => by
      have inData := data.onlyData c member (.inr (.inr isNumeral))
      simp only [dataClauses, List.mem_cons, List.not_mem_nil, or_false] at inData
      rcases inData with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd isNumeral (by decide)
          | skip
      · exact ⟨0, output.symm⟩
      · obtain ⟨n, rowIs⟩ := numeral_sound data depth (goals _ List.mem_cons_self)
        refine ⟨n + 1, ?_⟩
        rw [← output]
        simp only [numeralSucc, inst_appTerm, inst_symTerm, rowIs]
        rfl

theorem numeral_complete (data : DataProgram supply program) :
    ∀ n : ℕ, Derives R program numeralRelation (.sym 0) (numeral n)
  | 0 => by
      simpa [numeralZero, unitTerm, numeral] using DemandTransformation.derives_of_clause (R := R)
        (data.data numeralZero (by simp [dataClauses])) (fun _ => .sym 0) (fun g inside => by simp [numeralZero] at inside)
  | n + 1 => by
      have clause := DemandTransformation.derives_of_clause (R := R)
        (data.data numeralSucc (by simp [dataClauses])) (fun _ => numeral n) (fun g inside => by
          simp only [numeralSucc, List.mem_singleton] at inside
          subst inside
          simpa [goalHolds, unitTerm] using numeral_complete data n)
      simpa [numeralSucc, unitTerm, numeral] using clause

theorem supply_sound (data : DataProgram supply program) {x : Expr}
    (derived : Derives R program supplyRelation (.sym 0) x) : ∃ label ∈ supply, x = .sym (labelCode label) := by
  obtain ⟨c, member, isSupply, θ, -, output, -⟩ := DemandTransformation.derives_cases derived
  obtain ⟨label, inSupply, rfl⟩ := data.onlySupply c member isSupply
  exact ⟨label, inSupply, output.symm⟩

theorem supply_complete (data : DataProgram supply program) {label : String} (inSupply : label ∈ supply) :
    Derives R program supplyRelation (.sym 0) (.sym (labelCode label)) := by
  simpa [supplyClause, unitTerm] using DemandTransformation.derives_of_clause (R := R)
    (data.supplied label inSupply) (fun _ => .sym 0) (fun g inside => by simp [supplyClause] at inside)

/-- **Every derivation of data is the row of a data term over the supply.** -/
theorem data_sound (data : DataProgram supply program) : ∀ depth : ℕ,
    (∀ {x : Expr}, DerivesAt R program depth datumRelation (.sym 0) x →
      ∃ p, x = encode p ∧ isData p = true ∧ ∀ label ∈ labelsOf p, label ∈ supply) ∧
    (∀ {x : Expr}, DerivesAt R program depth datumListRelation (.sym 0) x →
      ∃ ps, x = encodeList ps ∧ isDataList ps = true ∧ ∀ label ∈ labelsOfList ps, label ∈ supply)
  | 0 => ⟨fun derived => derived.elim, fun derived => derived.elim⟩
  | depth + 1 => by
      obtain ⟨single, many⟩ := data_sound data depth
      have numeralAt : ∀ {y : Expr}, DerivesAt R program depth numeralRelation (.sym 0) y → ∃ n, y = numeral n :=
        fun found => numeral_sound data depth found
      have supplyAt : ∀ {y : Expr}, DerivesAt R program depth supplyRelation (.sym 0) y →
          ∃ label ∈ supply, y = .sym (labelCode label) :=
        fun found => supply_sound data ⟨depth, found⟩
      refine ⟨fun {x} derived => ?_, fun {x} derived => ?_⟩
      · obtain ⟨c, member, isDatum, θ, -, output, goals⟩ := derived
        have inData := data.onlyData c member (.inl isDatum)
        simp only [dataClauses, List.mem_cons, List.not_mem_nil, or_false] at inData
        rcases inData with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact absurd isDatum (by decide)
            | skip
        · obtain ⟨n, rowIs⟩ := numeralAt (goals _ List.mem_cons_self)
          refine ⟨.bvar n, ?_, rfl, fun label inside => by simp [labelsOf] at inside⟩
          rw [← output]
          simp [datumBvar, rowIs, encode]
        · obtain ⟨label, inSupply, rowIs⟩ := supplyAt (goals _ List.mem_cons_self)
          refine ⟨.fvar label, ?_, rfl, fun other inside => ?_⟩
          · rw [← output]
            simp [datumFvar, rowIs, encode]
          · simp only [labelsOf, List.mem_singleton] at inside
            exact inside ▸ inSupply
        · obtain ⟨label, inSupply, labelIs⟩ := supplyAt (goals _ List.mem_cons_self)
          obtain ⟨arguments, argumentsIs, argumentsData, argumentsSupplied⟩ :=
            many (goals _ (List.mem_cons_of_mem _ List.mem_cons_self))
          refine ⟨.apply label arguments, ?_, by simpa [isData] using argumentsData, fun other inside => ?_⟩
          · rw [← output]
            simp [datumApply, labelIs, argumentsIs, encode]
          · simp only [labelsOf, List.mem_cons] at inside
            rcases inside with rfl | inArguments
            · exact inSupply
            · exact argumentsSupplied other inArguments
        · obtain ⟨body, bodyIs, bodyData, bodySupplied⟩ := single (goals _ List.mem_cons_self)
          refine ⟨.lambda none body, ?_, by simpa [isData] using bodyData, fun other inside => ?_⟩
          · rw [← output]
            simp [datumLambda, bodyIs, encode,
              RootRewritesOnTheStep.optionRow]
          · exact bodySupplied other (by simpa [labelsOf] using inside)
        · obtain ⟨n, arityIs⟩ := numeralAt (goals _ List.mem_cons_self)
          obtain ⟨body, bodyIs, bodyData, bodySupplied⟩ := single (goals _ (List.mem_cons_of_mem _ List.mem_cons_self))
          refine ⟨.multiLambda n [] body, ?_, by simpa [isData] using bodyData, fun other inside => ?_⟩
          · rw [← output]
            simp [datumMultiLambda, arityIs, bodyIs, encode,
              RootRewritesOnTheStep.namesRow]
          · exact bodySupplied other (by simpa [labelsOf] using inside)
        · obtain ⟨body, bodyIs, bodyData, bodySupplied⟩ := single (goals _ List.mem_cons_self)
          obtain ⟨value, valueIs, valueData, valueSupplied⟩ :=
            single (goals _ (List.mem_cons_of_mem _ List.mem_cons_self))
          refine ⟨.subst body value, ?_, by simp [isData, bodyData, valueData], fun other inside => ?_⟩
          · rw [← output]
            simp [datumSubst, bodyIs, valueIs, encode]
          · simp only [labelsOf, List.mem_append] at inside
            exact inside.elim (bodySupplied other) (valueSupplied other)
        all_goals
          obtain ⟨elements, elementsIs, elementsData, elementsSupplied⟩ := many (goals _ List.mem_cons_self)
          exact ⟨_, ((collection_row elementsIs).symm.trans output).symm, by simpa [isData] using elementsData,
            fun other inside => elementsSupplied other (by simpa [labelsOf] using inside)⟩
      · obtain ⟨c, member, isList, θ, -, output, goals⟩ := derived
        have inData := data.onlyData c member (.inr (.inl isList))
        simp only [dataClauses, List.mem_cons, List.not_mem_nil, or_false] at inData
        rcases inData with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact absurd isList (by decide)
            | skip
        · exact ⟨[], output.symm, rfl, fun label inside => by simp [labelsOfList] at inside⟩
        · obtain ⟨head, headIs, headData, headSupplied⟩ := single (goals _ List.mem_cons_self)
          obtain ⟨tail, tailIs, tailData, tailSupplied⟩ := many (goals _ (List.mem_cons_of_mem _ List.mem_cons_self))
          refine ⟨head :: tail, ?_, by simp [isDataList, headData, tailData], fun other inside => ?_⟩
          · rw [← output]
            simp [datumCons, headIs, tailIs, encodeList]
          · simp only [labelsOfList, List.mem_append] at inside
            exact inside.elim (headSupplied other) (tailSupplied other)

mutual
  /-- **Every data term over the supply is a derivation of data.** -/
  theorem datum_complete (data : DataProgram supply program) : ∀ (p : Pattern), isData p = true →
      (∀ label ∈ labelsOf p, label ∈ supply) → Derives R program datumRelation (.sym 0) (encode p)
    | .bvar n, _, _ => by
        have clause := DemandTransformation.derives_of_clause (R := R)
          (data.data datumBvar (by simp [dataClauses])) (fun _ => numeral n) (fun g inside => by
            simp only [datumBvar, List.mem_singleton] at inside
            subst inside
            simpa [goalHolds, unitTerm] using numeral_complete data n)
        simpa [datumBvar, unitTerm, encode] using clause
    | .fvar name, _, supplied => by
        have clause := DemandTransformation.derives_of_clause (R := R)
          (data.data datumFvar (by simp [dataClauses])) (fun _ => .sym (labelCode name)) (fun g inside => by
            simp only [datumFvar, List.mem_singleton] at inside
            subst inside
            simpa [goalHolds, unitTerm] using supply_complete data (supplied name (by simp [labelsOf])))
        simpa [datumFvar, unitTerm, encode] using clause
    | .apply label arguments, isData', supplied => by
        have clause := DemandTransformation.derives_of_clause (R := R)
          (data.data datumApply (by simp [dataClauses]))
          (fun x => if x = 0 then .sym (labelCode label) else encodeList arguments) (fun g inside => by
            simp only [datumApply, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, unitTerm] using supply_complete data (supplied label (by simp [labelsOf]))
            · simpa [goalHolds, unitTerm] using datumList_complete data arguments (by simpa [isData] using isData')
                fun other inside => supplied other (by simp [labelsOf, inside]))
        simpa [datumApply, unitTerm, encode] using clause
    | .lambda binder body, isData', supplied => by
        simp only [isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at isData'
        obtain ⟨rfl, bodyData⟩ := isData'
        have clause := DemandTransformation.derives_of_clause (R := R)
          (data.data datumLambda (by simp [dataClauses])) (fun _ => encode body) (fun g inside => by
            simp only [datumLambda, List.mem_singleton] at inside
            subst inside
            simpa [goalHolds, unitTerm] using datum_complete data body bodyData
              fun other inside => supplied other (by simpa [labelsOf] using inside))
        simpa [datumLambda, unitTerm, encode, RootRewritesOnTheStep.optionRow] using clause
    | .multiLambda arity binders body, isData', supplied => by
        simp only [isData, Bool.and_eq_true, List.isEmpty_iff] at isData'
        obtain ⟨rfl, bodyData⟩ := isData'
        have clause := DemandTransformation.derives_of_clause (R := R)
          (data.data datumMultiLambda (by simp [dataClauses]))
          (fun x => if x = 0 then numeral arity else encode body) (fun g inside => by
            simp only [datumMultiLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, unitTerm] using numeral_complete data arity
            · simpa [goalHolds, unitTerm] using datum_complete data body bodyData
                fun other inside => supplied other (by simpa [labelsOf] using inside))
        simpa [datumMultiLambda, unitTerm, encode, RootRewritesOnTheStep.namesRow] using clause
    | .subst body value, isData', supplied => by
        simp only [isData, Bool.and_eq_true] at isData'
        have clause := DemandTransformation.derives_of_clause (R := R)
          (data.data datumSubst (by simp [dataClauses]))
          (fun x => if x = 0 then encode body else encode value) (fun g inside => by
            simp only [datumSubst, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, unitTerm] using datum_complete data body isData'.1
                fun other inside => supplied other (by simp [labelsOf, inside])
            · simpa [goalHolds, unitTerm] using datum_complete data value isData'.2
                fun other inside => supplied other (by simp [labelsOf, inside]))
        simpa [datumSubst, unitTerm, encode] using clause
    | .collection kind elements rest, isData', supplied => by
        simp only [isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at isData'
        obtain ⟨rfl, elementsData⟩ := isData'
        have member : datumCollection kind ∈ program := data.data _ (by cases kind <;> simp [dataClauses])
        have clause := DemandTransformation.derives_of_clause (R := R) member (fun _ => encodeList elements)
          (fun g inside => by
            simp only [datumCollection, List.mem_singleton] at inside
            subst inside
            simpa [goalHolds, unitTerm] using datumList_complete data elements elementsData
              fun other inside => supplied other (by simpa [labelsOf] using inside))
        simpa [datumCollection, unitTerm, encode, RootRewritesOnTheStep.optionRow] using clause

  theorem datumList_complete (data : DataProgram supply program) : ∀ (ps : List Pattern), isDataList ps = true →
      (∀ label ∈ labelsOfList ps, label ∈ supply) → Derives R program datumListRelation (.sym 0) (encodeList ps)
    | [], _, _ => by
        simpa [datumNil, unitTerm, encodeList] using DemandTransformation.derives_of_clause (R := R)
          (data.data datumNil (by simp [dataClauses])) (fun _ => .sym 0) (fun g inside => by simp [datumNil] at inside)
    | p :: ps, isData', supplied => by
        simp only [isDataList, Bool.and_eq_true] at isData'
        have clause := DemandTransformation.derives_of_clause (R := R)
          (data.data datumCons (by simp [dataClauses]))
          (fun x => if x = 0 then encode p else encodeList ps) (fun g inside => by
            simp only [datumCons, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, unitTerm] using datum_complete data p isData'.1
                fun other inside => supplied other (by simp [labelsOfList, inside])
            · simpa [goalHolds, unitTerm] using datumList_complete data ps isData'.2
                fun other inside => supplied other (by simp [labelsOfList, inside]))
        simpa [datumCons, unitTerm, encodeList] using clause
end

/-- **The relation of data relates the unit to exactly the rows of data terms over the supply.** -/
theorem datum_iff (data : DataProgram supply program) {x : Expr} :
    Derives R program datumRelation (.sym 0) x ↔
      ∃ p, x = encode p ∧ isData p = true ∧ ∀ label ∈ labelsOf p, label ∈ supply := by
  constructor
  · rintro ⟨depth, derived⟩
    exact (data_sound data depth).1 derived
  · rintro ⟨p, rfl, pData, supplied⟩
    exact datum_complete data p pData supplied

/-- **The relation of lists of data relates the unit to exactly the rows of lists of data terms over the supply.** -/
theorem datumList_iff (data : DataProgram supply program) {x : Expr} :
    Derives R program datumListRelation (.sym 0) x ↔
      ∃ ps, x = encodeList ps ∧ isDataList ps = true ∧ ∀ label ∈ labelsOfList ps, label ∈ supply := by
  constructor
  · rintro ⟨depth, derived⟩
    exact (data_sound data depth).2 derived
  · rintro ⟨ps, rfl, psData, supplied⟩
    exact datumList_complete data ps psData supplied

namespace Controls

/-- The clauses of data over the supply `a`, `f`. -/
def sample : List Clause := dataClauses ++ supplyClauses ["a", "f"]

theorem dataProgram : DataProgram ["a", "f"] sample where
  data c inside := List.mem_append_left _ inside
  supplied label inside := List.mem_append_right _ (List.mem_map.mpr ⟨label, inside, rfl⟩)
  onlyData c member isData' := by
    rcases List.mem_append.mp member with inData | inSupply
    · exact inData
    · obtain ⟨label, -, rfl⟩ := List.mem_map.mp inSupply
      simp [supplyClause, datumRelation, datumListRelation, numeralRelation, supplyRelation] at isData'
  onlySupply c member isSupply := by
    rcases List.mem_append.mp member with inData | inSupply
    · rcases dataClauses_relation c inData with same | same | same <;>
        · rw [same] at isSupply
          exact absurd isSupply (by decide)
    · obtain ⟨label, inside, rfl⟩ := List.mem_map.mp inSupply
      exact ⟨label, inside, rfl⟩

/-- **Positive**: a term over the supply, under a binder, with a bound index, is data of the relation. -/
theorem supplied : Derives (fun _ _ _ => False) sample datumRelation (.sym 0)
    (encode (.lambda none (.apply "f" [.fvar "a", .bvar 0]))) :=
  datum_iff dataProgram |>.mpr ⟨_, rfl, by decide, by decide⟩

/-- **Negative**: a term with a label outside the supply is not. -/
theorem unsupplied : ¬ Derives (fun _ _ _ => False) sample datumRelation (.sym 0)
    (encode (.apply "f" [.fvar "b"])) := by
  intro derived
  obtain ⟨p, same, -, supplied⟩ := datum_iff dataProgram |>.mp derived
  obtain rfl := RootRewritesOnTheStep.encode_injective same
  exact absurd (supplied "b" (by simp [labelsOf, labelsOfList])) (by decide)

end Controls

end Mettapedia.GSLT.Compilation.Uniform.DataClauses

#print axioms Mettapedia.GSLT.Compilation.Uniform.DataClauses.datum_iff
#print axioms Mettapedia.GSLT.Compilation.Uniform.DataClauses.dataClauses_moded
#print axioms Mettapedia.GSLT.Compilation.Uniform.DataClauses.Controls.supplied
#print axioms Mettapedia.GSLT.Compilation.Uniform.DataClauses.Controls.unsupplied
