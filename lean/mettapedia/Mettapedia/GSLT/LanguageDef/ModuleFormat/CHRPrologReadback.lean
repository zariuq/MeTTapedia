import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologPrinter
import Mettapedia.Languages.CHR.TupleNormal
import Batteries.Data.List.Lemmas

/-! Canonical source reads back as its IR. The printed form of a C0 program
denotes, as Prolog terms, the terms below; lowering those terms gives the
program's IR back in tuple normal form, with every variable at its printed
index. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologReadback

open Mettapedia.Logic.Prolog
open Mettapedia.Languages
open CHRPrologLowering (SourceTerm Variable Allocation)
open Mettapedia.Languages.CHR.TupleNormal

/-! ## Canonical variables -/

/-- The canonical spelling of the variable at an index. -/
def variableName (index : Nat) : String := "V" ++ toString index

theorem preferredIndex_canonical (index occurrence : Nat) :
    CHRPrologLowering.preferredIndex? ⟨variableName index, occurrence⟩ = some index := by
  unfold variableName
  have dropped : (("V" ++ toString index).drop 1).toString = toString index := by
    apply String.toList_inj.mp
    rw [show (("V" ++ toString index).drop 1).toString = (("V" ++ toString index).drop 1).copy from rfl,
      String.toList_copy_drop]
    simp
  have parsed : (("V" ++ toString index).drop 1).toString.toNat? = some index := by
    rw [dropped]
    exact Nat.toNat?_repr index
  have starts : ("V" ++ toString index).startsWith "V" = true := by simp
  simp only [CHRPrologLowering.preferredIndex?, starts, Bool.not_true, Bool.false_eq_true, if_false, parsed]
  simp

theorem mapM_preferred {α : Type} (preferred : α → Option Nat) :
    ∀ names : List α, (∀ name ∈ names, ∃ index, preferred name = some index) →
      names.mapM preferred = some (names.map fun name => (preferred name).getD 0)
  | [], _ => rfl
  | name :: rest, every => by
    obtain ⟨index, found⟩ := every name List.mem_cons_self
    rw [List.mapM_cons, found, mapM_preferred preferred rest
      (fun other member => every other (List.mem_cons_of_mem _ member))]
    simp [found]

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] : ∀ names : List α, names.eraseDups.Nodup
  | [] => List.nodup_nil
  | name :: rest => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, eraseDups_nodup _⟩
    intro inside
    have := (List.mem_filter.mp (List.mem_eraseDups.mp inside)).2
    simp at this
termination_by names => names.length
decreasing_by
  simp only [List.length_cons]
  have := List.length_filter_le (fun other => !other == name) rest
  omega

theorem lookup_zip_map {α : Type} [BEq α] [LawfulBEq α] (image : α → Nat) :
    ∀ (names : List α) (name : α), name ∈ names → (names.zip (names.map image)).lookup name = some (image name)
  | [], _, member => by simp at member
  | first :: rest, name, member => by
    by_cases same : name = first
    · subst same
      simp
    · have later : name ∈ rest := by simpa [same] using member
      have different : (name == first) = false := by simpa using same
      simp only [List.map_cons, List.zip_cons_cons, List.lookup, different]
      exact lookup_zip_map image rest name later

/-- An allocation whose preferred indices are injective on the names keeps
them. -/
theorem allocate_preferred {α : Type} [BEq α] [LawfulBEq α] (names : List α) (preferred : α → Option Nat)
    (every : ∀ name ∈ names, ∃ index, preferred name = some index)
    (injective : ∀ first ∈ names, ∀ second ∈ names, preferred first = preferred second → first = second) :
    ∀ name ∈ names, (List.IndexAllocation.allocate names preferred).lookup name = preferred name := by
  intro name member
  have distinctEvery : ∀ other ∈ names.eraseDups, ∃ index, preferred other = some index :=
    fun other inside => every other (List.mem_eraseDups.mp inside)
  have mapped := mapM_preferred preferred names.eraseDups distinctEvery
  have image : ∀ other ∈ names.eraseDups, preferred other = some ((preferred other).getD 0) := by
    intro other inside
    obtain ⟨index, found⟩ := distinctEvery other inside
    simp [found]
  have distinctIndices : (names.eraseDups.map fun other => (preferred other).getD 0).Nodup := by
    apply List.Nodup.map_on _ (eraseDups_nodup names)
    intro first firstIn second secondIn same
    apply injective first (List.mem_eraseDups.mp firstIn) second (List.mem_eraseDups.mp secondIn)
    rw [image first firstIn, image second secondIn, same]
  unfold List.IndexAllocation.allocate
  simp only [mapped, distinctIndices, if_true]
  have inside : name ∈ names.eraseDups := List.mem_eraseDups.mpr member
  rw [lookup_zip_map _ names.eraseDups name inside, ← image name inside]

/-! ## Values and terms in tuple normal form -/

theorem finRange_mapM_get {β : Type} (items : List SourceTerm) (convert : SourceTerm → Except String β) :
    (List.finRange items.length).mapM (fun position => convert (items.get position)) = items.mapM convert := by
  rw [show (fun position => convert (items.get position)) = convert ∘ items.get from rfl, ← List.mapM_map,
    List.map_get_finRange]

mutual
  /-- A C0 value as the canonical source writes it. -/
  def valueSource : CHR.Value → SourceTerm
    | .integer number => SourceSignature.integer number
    | .atom name => SourceSignature.atom name
    | .tuple fields => SourceSignature.compound "tuple" (valuesSource fields)
  def valuesSource : List CHR.Value → List SourceTerm
    | [] => []
    | first :: rest => valueSource first :: valuesSource rest
end

mutual
  /-- A term as the canonical source writes it, its variables named by `name`. -/
  def termSource (name : Nat → Variable) : CHR.Term → SourceTerm
    | .value datum => valueSource datum
    | .var index => .var (name index)
    | .tuple fields => SourceSignature.compound "tuple" (termsSource name fields)
  def termsSource (name : Nat → Variable) : List CHR.Term → List SourceTerm
    | [] => []
    | first :: rest => termSource name first :: termsSource name rest
end

theorem termsSource_length (name : Nat → Variable) :
    ∀ terms : List CHR.Term, (termsSource name terms).length = terms.length
  | [] => rfl
  | _ :: rest => by simp [termsSource, termsSource_length name rest]

theorem compound_lowers (allocation : Allocation) (items : List SourceTerm) :
    CHRPrologLowering.term allocation (SourceSignature.compound "tuple" items) =
      CHR.Term.tuple <$> items.mapM (CHRPrologLowering.term allocation) := by
  simp only [SourceSignature.compound, CHRPrologLowering.term]
  rw [if_pos (by decide)]
  exact congrArg _ (finRange_mapM_get items _)

mutual
  theorem value_lowers (allocation : Allocation) : ∀ datum : CHR.Value,
      CHRPrologLowering.term allocation (valueSource datum) = .ok (normalValue datum)
    | .integer _ => rfl
    | .atom _ => rfl
    | .tuple fields => by
      rw [valueSource, compound_lowers, values_lower allocation fields]
      rfl
  theorem values_lower (allocation : Allocation) : ∀ data : List CHR.Value,
      (valuesSource data).mapM (CHRPrologLowering.term allocation) = .ok (normalValues data)
    | [] => rfl
    | first :: rest => by
      rw [valuesSource, List.mapM_cons, value_lowers allocation first, values_lower allocation rest]
      rfl
end

/-- The allocation gives every variable of the term its index. -/
def Assigns (allocation : Allocation) (name : Nat → Variable) (indices : List Nat) : Prop :=
  ∀ index ∈ indices, CHRPrologLowering.index? allocation (name index) = some index

mutual
  theorem term_lowers (allocation : Allocation) (name : Nat → Variable) : ∀ term : CHR.Term,
      Assigns allocation name term.variables →
      CHRPrologLowering.term allocation (termSource name term) = .ok (normalTerm term)
    | .value datum, _ => value_lowers allocation datum
    | .var index, assigns => by
      have found := assigns index (by simp [CHR.Term.variables])
      simp [termSource, CHRPrologLowering.term, found, normalTerm, pure, Except.pure]
    | .tuple fields, assigns => by
      rw [termSource, compound_lowers, terms_lower allocation name fields
        (fun index member => assigns index (by simpa [CHR.Term.variables] using member))]
      rfl
  theorem terms_lower (allocation : Allocation) (name : Nat → Variable) : ∀ terms : List CHR.Term,
      Assigns allocation name (terms.flatMap CHR.Term.variables) →
      (termsSource name terms).mapM (CHRPrologLowering.term allocation) = .ok (normalTerms terms)
    | [], _ => rfl
    | first :: rest, assigns => by
      rw [termsSource, List.mapM_cons,
        term_lowers allocation name first (fun index member => assigns index (by simp [member])),
        terms_lower allocation name rest (fun index member => assigns index (by simp [member]))]
      rfl
end

/-! ## Heads, arithmetic, guards and goals -/

theorem application_compound (head : String) (items : List SourceTerm) :
    CHRPrologLowering.application? (SourceSignature.compound head items) = some (head, items) := by
  simp [CHRPrologLowering.application?, SourceSignature.compound, List.ofFn_get]

/-- A head as the canonical source writes it. -/
def headSource (name : Nat → Variable) (head : CHR.Head) : SourceTerm :=
  if head.arguments.isEmpty then SourceSignature.atom head.name
  else SourceSignature.compound head.name (termsSource name head.arguments)

theorem head_application (name : Nat → Variable) (head : CHR.Head) :
    CHRPrologLowering.application? (headSource name head) = some (head.name, termsSource name head.arguments) := by
  unfold headSource
  split
  · rename_i empty
    simp only [List.isEmpty_iff] at empty
    simp [CHRPrologLowering.application?, SourceSignature.atom, empty, termsSource]
  · exact application_compound _ _

theorem head_lowers (allocation : Allocation) (name : Nat → Variable) (head : CHR.Head)
    (assigns : Assigns allocation name head.variables) :
    CHRPrologLowering.head allocation (headSource name head) = .ok (normalHead head) := by
  simp only [CHRPrologLowering.head, head_application,
    terms_lower allocation name head.arguments assigns]
  rfl

/-- The source spelling of an integer operation. -/
def operatorName : CHR.IntOperator → String
  | .add => "+"
  | .subtract => "-"
  | .multiply => "*"
  | .quotient => "//"
  | .remainder => "rem"
  | .modulo => "mod"

theorem intOperator_name (operator : CHR.IntOperator) :
    CHRPrologLowering.intOperator? (operatorName operator) = some operator := by
  cases operator <;> rfl

/-- Arithmetic as the canonical source writes it, fully parenthesised. -/
def expressionSource (name : Nat → Variable) : CHR.IntExpr → SourceTerm
  | .literal number => SourceSignature.integer number
  | .index index => .var (name index)
  | .operation operator left right =>
    SourceSignature.compound (operatorName operator) [expressionSource name left, expressionSource name right]

theorem expression_lowers (allocation : Allocation) (name : Nat → Variable) : ∀ expression : CHR.IntExpr,
    Assigns allocation name expression.variables →
    CHRPrologLowering.expression allocation (expressionSource name expression) = .ok expression
  | .literal _, _ => rfl
  | .index index, assigns => by
    have found := assigns index (by simp [CHR.IntExpr.variables])
    simp [expressionSource, CHRPrologLowering.expression, found, pure, Except.pure]
  | .operation operator left right, assigns => by
    have leftLowers := expression_lowers allocation name left
      (fun index member => assigns index (by simp [CHR.IntExpr.variables, member]))
    have rightLowers := expression_lowers allocation name right
      (fun index member => assigns index (by simp [CHR.IntExpr.variables, member]))
    simp only [expressionSource, SourceSignature.compound, CHRPrologLowering.expression]
    simp [intOperator_name, leftLowers, rightLowers, bind, Except.bind, pure, Except.pure]

/-- The source spelling of a comparison. -/
def comparisonName : CHR.Comparison → String
  | .equal => "=:="
  | .different => "=\\="
  | .less => "<"
  | .lessEqual => "=<"
  | .greater => ">"
  | .greaterEqual => ">="

theorem comparison_name (comparison : CHR.Comparison) :
    CHRPrologLowering.comparison? (comparisonName comparison) = some comparison ∧
      comparisonName comparison ≠ "==" ∧ comparisonName comparison ≠ "\\==" := by
  cases comparison <;> decide

/-- A guard as the canonical source writes it. -/
def guardSource (name : Nat → Variable) : CHR.Guard → SourceTerm
  | .identical left right => SourceSignature.compound "==" [termSource name left, termSource name right]
  | .distinct left right => SourceSignature.compound "\\==" [termSource name left, termSource name right]
  | .compare comparison left right =>
    SourceSignature.compound (comparisonName comparison) [expressionSource name left, expressionSource name right]

theorem guard_lowers (allocation : Allocation) (name : Nat → Variable) (guard : CHR.Guard)
    (assigns : Assigns allocation name guard.variables) :
    CHRPrologLowering.guard allocation (guardSource name guard) = .ok (normalGuard guard) := by
  cases guard with
  | identical left right =>
    have leftLowers := term_lowers allocation name left
      (fun index member => assigns index (by simp [CHR.Guard.variables, member]))
    have rightLowers := term_lowers allocation name right
      (fun index member => assigns index (by simp [CHR.Guard.variables, member]))
    simp [guardSource, CHRPrologLowering.guard, application_compound, leftLowers, rightLowers, normalGuard,
      bind, Except.bind, pure, Except.pure]
  | distinct left right =>
    have leftLowers := term_lowers allocation name left
      (fun index member => assigns index (by simp [CHR.Guard.variables, member]))
    have rightLowers := term_lowers allocation name right
      (fun index member => assigns index (by simp [CHR.Guard.variables, member]))
    simp [guardSource, CHRPrologLowering.guard, application_compound, leftLowers, rightLowers, normalGuard,
      bind, Except.bind, pure, Except.pure]
  | compare comparison left right =>
    obtain ⟨found, notIdentical, notDistinct⟩ := comparison_name comparison
    have leftLowers := expression_lowers allocation name left
      (fun index member => assigns index (by simp [CHR.Guard.variables, member]))
    have rightLowers := expression_lowers allocation name right
      (fun index member => assigns index (by simp [CHR.Guard.variables, member]))
    simp [guardSource, CHRPrologLowering.guard, application_compound, leftLowers, rightLowers, normalGuard,
      found, notIdentical, notDistinct, bind, Except.bind, pure, Except.pure]

/-- The variables of a goal. -/
def goalVariables : CHR.Goal → List Nat
  | .tell head => head.variables
  | .assign index expression => index :: expression.variables
  | .fail => []

/-- A goal as the canonical source writes it. -/
def goalSource (name : Nat → Variable) : CHR.Goal → SourceTerm
  | .tell head => headSource name head
  | .assign index expression =>
    SourceSignature.compound "is" [.var (name index), expressionSource name expression]
  | .fail => SourceSignature.atom "fail"

/-- Told constraints distinct from builtin goals by name and arity. -/
def TellPrintable (head : CHR.Head) : Prop := ¬(head.name = "is" ∧ head.arguments.length = 2) ∧ head ≠ ⟨"fail", []⟩ ∧ head ≠ ⟨"true", []⟩

theorem headSource_not_fail (name : Nat → Variable) (head : CHR.Head) (notFail : head ≠ ⟨"fail", []⟩) :
    headSource name head ≠ SourceSignature.atom "fail" := by
  intro same
  apply notFail
  unfold headSource at same
  split at same
  · rename_i empty
    simp only [List.isEmpty_iff] at empty
    simp [SourceSignature.atom] at same
    cases head
    simp_all
  · simp [SourceSignature.compound, SourceSignature.atom] at same

theorem goal_lowers (allocation : Allocation) (name : Nat → Variable) (goal : CHR.Goal)
    (assigns : Assigns allocation name (goalVariables goal))
    (printable : ∀ head, goal = .tell head → TellPrintable head) :
    CHRPrologLowering.goal allocation (goalSource name goal) = .ok (normalGoal goal) := by
  cases goal with
  | tell head =>
    obtain ⟨notIs, notFail, _⟩ := printable head rfl
    have lowers := head_lowers allocation name head assigns
    simp only [goalSource, CHRPrologLowering.goal, headSource_not_fail name head notFail, if_false,
      head_application]
    split
    · rename_i same
      have pair := Prod.mk.inj (Option.some.inj same)
      apply (notIs ⟨pair.1, ?_⟩).elim
      have sizes := congrArg List.length pair.2
      simpa only [termsSource_length, List.length_cons, List.length_nil] using sizes
    · rename_i same
      have pair := Prod.mk.inj (Option.some.inj same)
      apply (notIs ⟨pair.1, ?_⟩).elim
      have sizes := congrArg List.length pair.2
      simpa only [termsSource_length, List.length_cons, List.length_nil] using sizes
    · simp [lowers, normalGoal, Functor.map, Except.map]
  | assign index expression =>
    have found := assigns index (by simp [goalVariables])
    have lowers := expression_lowers allocation name expression
      (fun other member => assigns other (by simp [goalVariables, member]))
    have notFailAtom : SourceSignature.compound "is" [.var (name index), expressionSource name expression] ≠
        SourceSignature.atom "fail" := by simp [SourceSignature.compound, SourceSignature.atom]
    simp [goalSource, CHRPrologLowering.goal, notFailAtom, application_compound, found, lowers, normalGoal,
      bind, Except.bind, pure, Except.pure]
  | fail => simp [goalSource, CHRPrologLowering.goal, normalGoal, pure, Except.pure]

/-! ## Conjunctions and rules -/

/-- A conjunction as the canonical source writes it: right nested, `true`
when empty. -/
def conjunctionSource : List SourceTerm → SourceTerm
  | [] => SourceSignature.atom "true"
  | [single] => single
  | first :: second :: more => SourceSignature.compound "," [first, conjunctionSource (second :: more)]

/-- A term the conjunction reader keeps whole. -/
def ConjunctionFree (source : SourceTerm) : Prop := CHRPrologLowering.conjunction source = [source]

theorem conjunction_compound (first second : SourceTerm) :
    CHRPrologLowering.conjunction (SourceSignature.compound "," [first, second]) =
      CHRPrologLowering.conjunction first ++ CHRPrologLowering.conjunction second := by
  simp [SourceSignature.compound, CHRPrologLowering.conjunction]

theorem conjunction_source : ∀ items : List SourceTerm, items ≠ [] → (∀ item ∈ items, ConjunctionFree item) →
    CHRPrologLowering.conjunction (conjunctionSource items) = items
  | [], absent, _ => absurd rfl absent
  | [single], _, free => free single List.mem_cons_self
  | first :: second :: more, _, free => by
    rw [conjunctionSource, conjunction_compound, free first List.mem_cons_self,
      conjunction_source (second :: more) (by simp) (fun item member => free item (List.mem_cons_of_mem _ member))]
    rfl

/-- A head whose source the reader would split or read as rule syntax:
`,`, `|` or `\` with two arguments. -/
def operatorShaped (head : CHR.Head) : Bool :=
  head.arguments.length == 2 && [",", "|", "\\"].contains head.name

theorem head_conjunctionFree (name : Nat → Variable) (head : CHR.Head) (plain : operatorShaped head = false) :
    ConjunctionFree (headSource name head) := by
  unfold ConjunctionFree headSource
  split
  · simp [SourceSignature.atom, CHRPrologLowering.conjunction]
  · simp only [SourceSignature.compound, CHRPrologLowering.conjunction]
    rw [dif_neg]
    rintro ⟨named, two⟩
    simp only [operatorShaped, Bool.and_eq_false_iff] at plain
    rcases plain with wrong | wrong
    · simp only [termsSource_length] at two
      simp [two] at wrong
    · simp [named] at wrong

/-- Rules the canonical source spells without ambiguity. -/
structure RulePrintable (rule : CHR.Rule) : Prop where
  heads : rule.kept ++ rule.removed ≠ []
  headsPlain : ∀ head ∈ rule.kept ++ rule.removed, operatorShaped head = false
  tells : ∀ head, CHR.Goal.tell head ∈ rule.body → TellPrintable head ∧ operatorShaped head = false

/-! ## The variables of canonical sources -/

open CHRPrologLowering (sourceVariables)

theorem sourceVariables_compound (head : String) (items : List SourceTerm) :
    sourceVariables (SourceSignature.compound head items) = items.flatMap sourceVariables := by
  simp only [SourceSignature.compound, sourceVariables]
  conv_rhs => rw [← List.map_get_finRange items]
  rw [List.flatMap_map]

mutual
  theorem value_variables : ∀ datum : CHR.Value, sourceVariables (valueSource datum) = []
    | .integer _ => rfl
    | .atom _ => rfl
    | .tuple fields => by rw [valueSource, sourceVariables_compound, values_variables fields]
  theorem values_variables : ∀ data : List CHR.Value, (valuesSource data).flatMap sourceVariables = []
    | [] => rfl
    | first :: rest => by simp [valuesSource, value_variables first, values_variables rest]
end

mutual
  theorem term_variables (name : Nat → Variable) : ∀ term : CHR.Term,
      sourceVariables (termSource name term) = term.variables.map name
    | .value datum => by simp [termSource, value_variables, CHR.Term.variables]
    | .var _ => by simp [termSource, sourceVariables, CHR.Term.variables]
    | .tuple fields => by
      rw [termSource, sourceVariables_compound, terms_variables name fields]
      simp [CHR.Term.variables]
  theorem terms_variables (name : Nat → Variable) : ∀ terms : List CHR.Term,
      (termsSource name terms).flatMap sourceVariables = (terms.flatMap CHR.Term.variables).map name
    | [] => rfl
    | first :: rest => by simp [termsSource, term_variables name first, terms_variables name rest]
end

theorem head_variables (name : Nat → Variable) (head : CHR.Head) :
    sourceVariables (headSource name head) = head.variables.map name := by
  unfold headSource
  split
  · rename_i empty
    simp only [List.isEmpty_iff] at empty
    simp [SourceSignature.atom, sourceVariables, CHR.Head.variables, empty]
  · rw [sourceVariables_compound, terms_variables]
    rfl

theorem expression_variables (name : Nat → Variable) : ∀ expression : CHR.IntExpr,
    sourceVariables (expressionSource name expression) = expression.variables.map name
  | .literal _ => rfl
  | .index _ => rfl
  | .operation _ left right => by
    rw [expressionSource, sourceVariables_compound]
    simp [expression_variables name left, expression_variables name right, CHR.IntExpr.variables]

theorem guard_variables (name : Nat → Variable) (guard : CHR.Guard) :
    sourceVariables (guardSource name guard) = guard.variables.map name := by
  cases guard <;> simp [guardSource, sourceVariables_compound, term_variables, expression_variables,
    CHR.Guard.variables]

theorem goal_variables (name : Nat → Variable) (goal : CHR.Goal) :
    sourceVariables (goalSource name goal) = (goalVariables goal).map name := by
  cases goal with
  | tell head => exact head_variables name head
  | assign index expression =>
    simp [goalSource, sourceVariables_compound, expression_variables, goalVariables, sourceVariables]
  | fail => rfl

theorem conjunction_variables : ∀ items : List SourceTerm,
    sourceVariables (conjunctionSource items) = items.flatMap sourceVariables
  | [] => rfl
  | [single] => by simp [conjunctionSource]
  | first :: second :: more => by
    simp only [conjunctionSource, sourceVariables_compound, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      conjunction_variables (second :: more)]

/-! ## Rules -/

/-- The heads of a rule side, as the canonical source writes them. -/
def headsSource (name : Nat → Variable) (heads : List CHR.Head) : SourceTerm :=
  conjunctionSource (heads.map (headSource name))

/-- A rule as the canonical source writes it. -/
def ruleSource (name : Nat → Variable) (rule : CHR.Rule) : SourceTerm :=
  let left := if rule.removed.isEmpty then headsSource name rule.kept
    else if rule.kept.isEmpty then headsSource name rule.removed
    else SourceSignature.compound "\\" [headsSource name rule.kept, headsSource name rule.removed]
  let body := conjunctionSource (rule.body.map (goalSource name))
  let right := if rule.guards.isEmpty then body
    else SourceSignature.compound "|" [conjunctionSource (rule.guards.map (guardSource name)), body]
  SourceSignature.compound "@" [SourceSignature.atom rule.name,
    SourceSignature.compound (if rule.removed.isEmpty then "==>" else "<=>") [left, right]]

/-- A rule's variables in the order its source names them. -/
def ruleVariables (rule : CHR.Rule) : List Nat :=
  (rule.kept ++ rule.removed).flatMap CHR.Head.variables ++ rule.guards.flatMap CHR.Guard.variables ++
    rule.body.flatMap goalVariables

theorem rule_variables (name : Nat → Variable) (rule : CHR.Rule) :
    sourceVariables (ruleSource name rule) = (ruleVariables rule).map name := by
  have heads : ∀ heads : List CHR.Head,
      sourceVariables (headsSource name heads) = (heads.flatMap CHR.Head.variables).map name := by
    intro heads
    simp [headsSource, conjunction_variables, head_variables, List.flatMap_map, List.map_flatMap]
  have guards : sourceVariables (conjunctionSource (rule.guards.map (guardSource name))) =
      (rule.guards.flatMap CHR.Guard.variables).map name := by
    simp [conjunction_variables, guard_variables, List.flatMap_map, List.map_flatMap]
  have body : sourceVariables (conjunctionSource (rule.body.map (goalSource name))) =
      (rule.body.flatMap goalVariables).map name := by
    simp [conjunction_variables, goal_variables, List.flatMap_map, List.map_flatMap]
  simp only [ruleSource, sourceVariables_compound, ruleVariables]
  split <;> split <;> (try split) <;>
    simp_all [sourceVariables_compound, SourceSignature.atom, sourceVariables, List.isEmpty_iff]

/-! ## Rules read back -/

/-- Canonical naming: the variable at an index is spelled by the index. -/
def Canonical (name : Nat → Variable) : Prop := ∀ index, (name index).spelling = variableName index

theorem canonical_preferred (name : Nat → Variable) (canonical : Canonical name) (index : Nat) :
    CHRPrologLowering.preferredIndex? (name index) = some index := by
  have spelled := canonical index
  generalize name index = named at spelled ⊢
  obtain ⟨spelling, occurrence⟩ := named
  simp only at spelled
  subst spelled
  exact preferredIndex_canonical index occurrence

theorem Assigns.mono {allocation : Allocation} {name : Nat → Variable} {wide narrow : List Nat}
    (assigns : Assigns allocation name wide) (within : ∀ index ∈ narrow, index ∈ wide) :
    Assigns allocation name narrow :=
  fun index member => assigns index (within index member)

theorem rule_assigns (name : Nat → Variable) (canonical : Canonical name) (rule : CHR.Rule) :
    Assigns (CHRPrologLowering.allocate (ruleSource name rule)) name (ruleVariables rule) := by
  intro index member
  unfold CHRPrologLowering.allocate CHRPrologLowering.index?
  rw [rule_variables]
  have inside : name index ∈ (ruleVariables rule).map name := List.mem_map_of_mem member
  rw [allocate_preferred _ _ ?every ?injective (name index) inside, canonical_preferred name canonical index]
  · intro named namedIn
    obtain ⟨other, _, rfl⟩ := List.mem_map.mp namedIn
    exact ⟨other, canonical_preferred name canonical other⟩
  · intro first firstIn second secondIn same
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp firstIn
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp secondIn
    rw [canonical_preferred name canonical i, canonical_preferred name canonical j] at same
    cases same
    rfl

theorem mapM_map_ok {α β γ : Type} (convert : α → β) (lower : β → Except String γ) (result : α → γ) :
    ∀ items : List α, (∀ item ∈ items, lower (convert item) = .ok (result item)) →
      (items.map convert).mapM lower = .ok (items.map result)
  | [], _ => rfl
  | item :: rest, each => by
    rw [List.map_cons, List.mapM_cons, each item List.mem_cons_self,
      mapM_map_ok convert lower result rest (fun other member => each other (List.mem_cons_of_mem _ member))]
    rfl

theorem heads_lowers (allocation : Allocation) (name : Nat → Variable) (heads : List CHR.Head)
    (nonempty : heads ≠ []) (plain : ∀ head ∈ heads, operatorShaped head = false)
    (assigns : Assigns allocation name (heads.flatMap CHR.Head.variables)) :
    CHRPrologLowering.heads allocation (headsSource name heads) = .ok (heads.map normalHead) := by
  unfold CHRPrologLowering.heads headsSource
  rw [conjunction_source _ (by simpa using nonempty) (fun item member => by
    obtain ⟨head, inside, rfl⟩ := List.mem_map.mp member
    exact head_conjunctionFree name head (plain head inside))]
  exact mapM_map_ok _ _ _ heads (fun head inside => head_lowers allocation name head
    (assigns.mono (fun index member => List.mem_flatMap.mpr ⟨head, inside, member⟩)))

theorem guard_conjunctionFree (name : Nat → Variable) (guard : CHR.Guard) :
    ConjunctionFree (guardSource name guard) ∧ guardSource name guard ≠ SourceSignature.atom "true" := by
  cases guard with
  | compare comparison left right =>
    have named := comparison_name comparison
    refine ⟨?_, by simp [guardSource, SourceSignature.compound, SourceSignature.atom]⟩
    unfold ConjunctionFree guardSource
    simp only [SourceSignature.compound, CHRPrologLowering.conjunction]
    rw [dif_neg]
    rintro ⟨same, _⟩
    cases comparison <;> simp [comparisonName] at same
  | _ =>
    refine ⟨?_, by simp [guardSource, SourceSignature.compound, SourceSignature.atom]⟩
    unfold ConjunctionFree guardSource
    simp [SourceSignature.compound, CHRPrologLowering.conjunction]

theorem guards_lowers (allocation : Allocation) (name : Nat → Variable) (guards : List CHR.Guard)
    (nonempty : guards ≠ []) (assigns : Assigns allocation name (guards.flatMap CHR.Guard.variables)) :
    CHRPrologLowering.guards allocation (conjunctionSource (guards.map (guardSource name))) =
      .ok (guards.map normalGuard) := by
  unfold CHRPrologLowering.guards
  rw [conjunction_source _ (by simpa using nonempty) (fun item member => by
    obtain ⟨guard, _, rfl⟩ := List.mem_map.mp member
    exact (guard_conjunctionFree name guard).1)]
  rw [List.filter_eq_self.mpr (fun item member => by
    obtain ⟨guard, _, rfl⟩ := List.mem_map.mp member
    simpa using (guard_conjunctionFree name guard).2)]
  exact mapM_map_ok _ _ _ guards (fun guard inside => guard_lowers allocation name guard
    (assigns.mono (fun index member => List.mem_flatMap.mpr ⟨guard, inside, member⟩)))

theorem goal_conjunctionFree (name : Nat → Variable) (goal : CHR.Goal)
    (printable : ∀ head, goal = .tell head → TellPrintable head ∧ operatorShaped head = false) :
    ConjunctionFree (goalSource name goal) ∧ goalSource name goal ≠ SourceSignature.atom "true" := by
  cases goal with
  | tell head =>
    obtain ⟨⟨_, _, notTrue⟩, plain⟩ := printable head rfl
    refine ⟨head_conjunctionFree name head plain, ?_⟩
    intro same
    apply notTrue
    simp only [goalSource] at same
    unfold headSource at same
    split at same
    · rename_i empty
      simp only [List.isEmpty_iff] at empty
      simp [SourceSignature.atom] at same
      cases head
      simp_all
    · simp [SourceSignature.compound, SourceSignature.atom] at same
  | assign index expression =>
    refine ⟨?_, by simp [goalSource, SourceSignature.compound, SourceSignature.atom]⟩
    unfold ConjunctionFree goalSource
    simp [SourceSignature.compound, CHRPrologLowering.conjunction]
  | fail =>
    refine ⟨?_, by simp [goalSource, SourceSignature.atom]⟩
    unfold ConjunctionFree goalSource
    simp [SourceSignature.atom, CHRPrologLowering.conjunction]

theorem goals_lowers (allocation : Allocation) (name : Nat → Variable) (goals : List CHR.Goal)
    (printable : ∀ head, CHR.Goal.tell head ∈ goals → TellPrintable head ∧ operatorShaped head = false)
    (assigns : Assigns allocation name (goals.flatMap goalVariables)) :
    CHRPrologLowering.goals allocation (conjunctionSource (goals.map (goalSource name))) =
      .ok (goals.map normalGoal) := by
  unfold CHRPrologLowering.goals
  by_cases empty : goals = []
  · subst empty
    simp [conjunctionSource, SourceSignature.atom, CHRPrologLowering.conjunction, pure, Except.pure]
  have free := fun goal (inside : goal ∈ goals) => goal_conjunctionFree name goal
    (fun head same => printable head (same ▸ inside))
  rw [conjunction_source _ (by simpa using empty) (fun item member => by
    obtain ⟨goal, inside, rfl⟩ := List.mem_map.mp member
    exact (free goal inside).1)]
  rw [List.filter_eq_self.mpr (fun item member => by
    obtain ⟨goal, inside, rfl⟩ := List.mem_map.mp member
    simpa using (free goal inside).2)]
  exact mapM_map_ok _ _ _ goals (fun goal inside => goal_lowers allocation name goal
    (assigns.mono (fun index member => List.mem_flatMap.mpr ⟨goal, inside, member⟩))
    (fun head same => (printable head (same ▸ inside)).1))

theorem conjunction_application (first second : SourceTerm) (more : List SourceTerm) :
    CHRPrologLowering.application? (conjunctionSource (first :: second :: more)) =
      some (",", [first, conjunctionSource (second :: more)]) := by
  rw [conjunctionSource, application_compound]

theorem head_application_plain (name : Nat → Variable) (head : CHR.Head) (plain : operatorShaped head = false)
    (operator : String) (operatorIn : operator ∈ [",", "|", "\\"]) (left right : SourceTerm) :
    CHRPrologLowering.application? (headSource name head) ≠ some (operator, [left, right]) := by
  rw [head_application]
  intro same
  simp only [Option.some.injEq, Prod.mk.injEq] at same
  obtain ⟨named, arguments⟩ := same
  have two : head.arguments.length = 2 := by
    rw [← termsSource_length name, arguments]
    rfl
  simp only [operatorShaped, two, named] at plain
  simp at operatorIn
  rcases operatorIn with rfl | rfl | rfl <;> simp at plain

theorem headsSource_not_backslash (name : Nat → Variable) (heads : List CHR.Head) (nonempty : heads ≠ [])
    (plain : ∀ head ∈ heads, operatorShaped head = false) (left right : SourceTerm) :
    CHRPrologLowering.application? (headsSource name heads) ≠ some ("\\", [left, right]) := by
  unfold headsSource
  match heads, nonempty with
  | [single], _ =>
    simpa [conjunctionSource] using
      head_application_plain name single (plain single List.mem_cons_self) "\\" (by simp) left right
  | first :: second :: more, _ =>
    simp [conjunction_application]

theorem goal_not_bar (name : Nat → Variable) (goal : CHR.Goal)
    (printable : ∀ head, goal = .tell head → TellPrintable head ∧ operatorShaped head = false)
    (left right : SourceTerm) :
    CHRPrologLowering.application? (goalSource name goal) ≠ some ("|", [left, right]) := by
  cases goal with
  | tell head => exact head_application_plain name head (printable head rfl).2 "|" (by simp) left right
  | assign index expression => simp [goalSource, application_compound]
  | fail => simp [goalSource, SourceSignature.atom, CHRPrologLowering.application?]

theorem body_not_bar (name : Nat → Variable) (goals : List CHR.Goal)
    (printable : ∀ head, CHR.Goal.tell head ∈ goals → TellPrintable head ∧ operatorShaped head = false)
    (left right : SourceTerm) :
    CHRPrologLowering.application? (conjunctionSource (goals.map (goalSource name))) ≠ some ("|", [left, right]) := by
  match goals with
  | [] => simp [conjunctionSource, SourceSignature.atom, CHRPrologLowering.application?]
  | [single] =>
    simpa [conjunctionSource] using goal_not_bar name single
      (fun head same => printable head (by simp [same])) left right
  | first :: second :: more => simp [conjunction_application]

/-- **A rule reads back.** Lowering a rule's canonical source gives the rule
in tuple normal form. -/
theorem rule_lowers (name : Nat → Variable) (canonical : Canonical name) (ordinal : Nat) (rule : CHR.Rule)
    (printable : RulePrintable rule) :
    CHRPrologLowering.rule ordinal (ruleSource name rule) = .ok (normalRule rule) := by
  have assigns := rule_assigns name canonical rule
  have keptAssigns := assigns.mono (narrow := rule.kept.flatMap CHR.Head.variables)
    (fun index member => by simp only [ruleVariables, List.flatMap_append, List.mem_append]; exact .inl (.inl (.inl member)))
  have removedAssigns := assigns.mono (narrow := rule.removed.flatMap CHR.Head.variables)
    (fun index member => by simp only [ruleVariables, List.flatMap_append, List.mem_append]; exact .inl (.inl (.inr member)))
  have guardsAssigns := assigns.mono (narrow := rule.guards.flatMap CHR.Guard.variables)
    (fun index member => by simp only [ruleVariables, List.flatMap_append, List.mem_append]; exact .inl (.inr member))
  have bodyAssigns := assigns.mono (narrow := rule.body.flatMap goalVariables)
    (fun index member => by simp only [ruleVariables, List.flatMap_append, List.mem_append]; exact .inr member)
  have keptPlain : ∀ head ∈ rule.kept, operatorShaped head = false :=
    fun head inside => printable.headsPlain head (List.mem_append_left _ inside)
  have removedPlain : ∀ head ∈ rule.removed, operatorShaped head = false :=
    fun head inside => printable.headsPlain head (List.mem_append_right _ inside)
  have bodyLowers := goals_lowers _ name rule.body printable.tells bodyAssigns
  have notBar := body_not_bar name rule.body printable.tells
  unfold CHRPrologLowering.rule
  generalize CHRPrologLowering.allocate (ruleSource name rule) = allocation at keptAssigns removedAssigns guardsAssigns bodyAssigns bodyLowers ⊢
  obtain ⟨ruleName, kept, removed, guards, body⟩ := rule
  simp only at keptAssigns removedAssigns guardsAssigns bodyAssigns keptPlain removedPlain bodyLowers notBar ⊢
  have heads := printable.heads
  simp only at heads
  simp only [ruleSource, application_compound, SourceSignature.atom]
  by_cases removedEmpty : removed = []
  · subst removedEmpty
    have keptNonempty : kept ≠ [] := by simpa using heads
    have keptLowers := heads_lowers allocation name kept keptNonempty keptPlain keptAssigns
    by_cases guardsEmpty : guards = []
    · subst guardsEmpty
      simp [application_compound, keptLowers, bodyLowers, normalRule, bind, Except.bind, pure, Except.pure]
    · have guardsLower := guards_lowers allocation name guards guardsEmpty guardsAssigns
      simp [guardsEmpty, application_compound, keptLowers, guardsLower, bodyLowers, normalRule, bind,
        Except.bind, pure, Except.pure]
  · have removedLowers := heads_lowers allocation name removed removedEmpty removedPlain removedAssigns
    by_cases keptEmpty : kept = []
    · subst keptEmpty
      have notBackslash := headsSource_not_backslash name removed removedEmpty removedPlain
      by_cases guardsEmpty : guards = []
      · subst guardsEmpty
        simp [removedEmpty, application_compound, removedLowers, bodyLowers, normalRule, bind, Except.bind,
          pure, Except.pure]
      · have guardsLower := guards_lowers allocation name guards guardsEmpty guardsAssigns
        simp [removedEmpty, guardsEmpty, application_compound, removedLowers, guardsLower, bodyLowers,
          normalRule, bind, Except.bind, pure, Except.pure]
    · have keptLowers := heads_lowers allocation name kept keptEmpty keptPlain keptAssigns
      by_cases guardsEmpty : guards = []
      · subst guardsEmpty
        simp [removedEmpty, keptEmpty, application_compound, keptLowers, removedLowers, bodyLowers,
          normalRule, bind, Except.bind, pure, Except.pure]
      · have guardsLower := guards_lowers allocation name guards guardsEmpty guardsAssigns
        simp [removedEmpty, keptEmpty, guardsEmpty, application_compound, keptLowers, removedLowers,
          guardsLower, bodyLowers, normalRule, bind, Except.bind, pure, Except.pure]

#print axioms rule_lowers

/-! ## Declarations, directives and the query -/

/-- A declaration as the canonical source writes it. -/
def declarationSource (declaration : CHR.Declaration) : SourceTerm :=
  SourceSignature.compound "/" [SourceSignature.atom declaration.name, SourceSignature.integer declaration.arity]

theorem declaration_lowers (declaration : CHR.Declaration) :
    CHRPrologLowering.declaration (declarationSource declaration) = .ok declaration := by
  simp [CHRPrologLowering.declaration, declarationSource, application_compound, SourceSignature.atom,
    SourceSignature.integer, pure, Except.pure]

theorem declaration_conjunctionFree (declaration : CHR.Declaration) :
    ConjunctionFree (declarationSource declaration) := by
  simp [ConjunctionFree, declarationSource, SourceSignature.compound, CHRPrologLowering.conjunction]

/-- The declaration directive as the canonical source writes it. -/
def declarationsSource (declarations : List CHR.Declaration) : SourceTerm :=
  SourceSignature.compound ":-" [SourceSignature.compound "chr_constraint"
    [conjunctionSource (declarations.map declarationSource)]]

theorem declarations_form (ordinal : Nat) (declarations : List CHR.Declaration) (nonempty : declarations ≠ []) :
    CHRPrologLowering.form ordinal (declarationsSource declarations) = .ok (.declarations declarations) := by
  have split := conjunction_source (declarations.map declarationSource) (by simpa using nonempty)
    (fun item inside => by
      obtain ⟨declaration, _, rfl⟩ := List.mem_map.mp inside
      exact declaration_conjunctionFree declaration)
  have lowered : (declarations.map declarationSource).mapM CHRPrologLowering.declaration = .ok declarations := by
    rw [mapM_map_ok declarationSource CHRPrologLowering.declaration id declarations
      (fun declaration _ => declaration_lowers declaration)]
    simp
  simp [CHRPrologLowering.form, declarationsSource, application_compound, split, lowered, Functor.map,
    Except.map]

/-- The library directive the canonical source starts with. -/
def libraryDirective : SourceTerm :=
  SourceSignature.compound ":-" [SourceSignature.compound "use_module"
    [SourceSignature.compound "library" [SourceSignature.atom "chr"]]]

/-- The option directive that names the declared execution profile. -/
def optionDirective : SourceTerm :=
  SourceSignature.compound ":-" [SourceSignature.compound "chr_option"
    [SourceSignature.atom "optimize", SourceSignature.atom "off"]]

theorem library_form (ordinal : Nat) : CHRPrologLowering.form ordinal libraryDirective = .ok .metadata := by
  simp [CHRPrologLowering.form, libraryDirective, application_compound, pure, Except.pure]

theorem option_form (ordinal : Nat) : CHRPrologLowering.form ordinal optionDirective = .ok .metadata := by
  simp [CHRPrologLowering.form, optionDirective, application_compound, pure, Except.pure]

/-- A ground constraint as the canonical source writes it. -/
def constraintSource (constraint : CHR.Constraint) : SourceTerm :=
  if constraint.arguments.isEmpty then SourceSignature.atom constraint.name
  else SourceSignature.compound constraint.name (valuesSource constraint.arguments)

theorem valuesSource_eq (data : List CHR.Value) : valuesSource data = data.map valueSource := by
  induction data with
  | nil => rfl
  | cons first rest ih => simp [valuesSource, ih]

theorem constraint_application (constraint : CHR.Constraint) :
    CHRPrologLowering.application? (constraintSource constraint) =
      some (constraint.name, valuesSource constraint.arguments) := by
  unfold constraintSource
  split
  · rename_i empty
    simp only [List.isEmpty_iff] at empty
    simp [CHRPrologLowering.application?, SourceSignature.atom, empty, valuesSource]
  · exact application_compound _ _

theorem groundConstraint_lowers (constraint : CHR.Constraint) :
    CHRPrologLowering.groundConstraint (constraintSource constraint) = .ok constraint := by
  have lowered : CHRPrologLowering.head [] (constraintSource constraint) =
      .ok ⟨constraint.name, normalValues constraint.arguments⟩ := by
    simp only [CHRPrologLowering.head, constraint_application, values_lower [] constraint.arguments]
    rfl
  have instantiated : CHR.Head.instantiate [] ⟨constraint.name, normalValues constraint.arguments⟩ =
      some constraint := by
    simp only [CHR.Head.instantiate, normalValues_instantiate [] constraint.arguments]
    rfl
  simp [CHRPrologLowering.groundConstraint, lowered, instantiated, bind, Except.bind, pure, Except.pure]

/-- A constraint the query reader keeps whole and does not drop as `true`. -/
def QueryPrintable (constraint : CHR.Constraint) : Prop :=
  constraint ≠ ⟨"true", []⟩ ∧ operatorShaped ⟨constraint.name, constraint.arguments.map CHR.Term.value⟩ = false

theorem constraint_conjunctionFree (constraint : CHR.Constraint) (printable : QueryPrintable constraint) :
    ConjunctionFree (constraintSource constraint) := by
  unfold ConjunctionFree constraintSource
  split
  · simp [SourceSignature.atom, CHRPrologLowering.conjunction]
  · have plain := printable.2
    simp only [operatorShaped, List.length_map, Bool.and_eq_false_iff] at plain
    simp only [SourceSignature.compound, CHRPrologLowering.conjunction]
    rw [dif_neg]
    rintro ⟨comma, two⟩
    have arity : constraint.arguments.length = 2 := by simpa [valuesSource_eq] using two
    rcases plain with wrongArity | notOperator
    · simp [arity] at wrongArity
    · simp [comma] at notOperator

theorem constraint_not_true (constraint : CHR.Constraint) (printable : QueryPrintable constraint) :
    constraintSource constraint ≠ SourceSignature.atom "true" := by
  unfold constraintSource
  split
  · rename_i empty
    simp only [List.isEmpty_iff] at empty
    intro same
    have named : constraint.name = "true" := by simpa [SourceSignature.atom] using same
    exact printable.1 (by cases constraint; simp_all)
  · simp [SourceSignature.compound, SourceSignature.atom]

/-- The query as the canonical source writes it. -/
def querySource (inputs : List CHR.Constraint) : SourceTerm :=
  SourceSignature.compound "?-" [conjunctionSource (inputs.map constraintSource)]

theorem filterMapM_map_some {α β γ : Type} (embed : α → β) (convert : β → Except String (Option γ))
    (result : α → γ) :
    ∀ items : List α, (∀ item ∈ items, convert (embed item) = .ok (some (result item))) →
      (items.map embed).filterMapM convert = .ok (items.map result)
  | [], _ => rfl
  | item :: rest, every => by
    rw [List.map_cons, List.filterMapM_cons, every item List.mem_cons_self]
    simp only [bind, Except.bind]
    rw [filterMapM_map_some embed convert result rest
      (fun other inside => every other (List.mem_cons_of_mem _ inside))]
    rfl

theorem query_form (ordinal : Nat) (inputs : List CHR.Constraint) (nonempty : inputs ≠ [])
    (printable : ∀ constraint ∈ inputs, QueryPrintable constraint) :
    CHRPrologLowering.form ordinal (querySource inputs) = .ok (.query inputs) := by
  have split := conjunction_source (inputs.map constraintSource) (by simpa using nonempty)
    (fun item inside => by
      obtain ⟨constraint, member, rfl⟩ := List.mem_map.mp inside
      exact constraint_conjunctionFree constraint (printable constraint member))
  simp only [CHRPrologLowering.form, querySource, application_compound, split]
  rw [filterMapM_map_some constraintSource _ id inputs (fun constraint member => by
    rw [if_neg (constraint_not_true constraint (printable constraint member)), groundConstraint_lowers]
    rfl)]
  simp

theorem rule_form (name : Nat → Variable) (canonical : Canonical name) (ordinal : Nat) (rule : CHR.Rule)
    (printable : RulePrintable rule) :
    CHRPrologLowering.form ordinal (ruleSource name rule) = .ok (.rule (normalRule rule)) := by
  have lowered := rule_lowers name canonical ordinal rule printable
  have shape : CHRPrologLowering.application? (ruleSource name rule) =
      some ("@", [SourceSignature.atom rule.name,
        SourceSignature.compound (if rule.removed.isEmpty then "==>" else "<=>")
          [if rule.removed.isEmpty then headsSource name rule.kept
            else if rule.kept.isEmpty then headsSource name rule.removed
            else SourceSignature.compound "\\" [headsSource name rule.kept, headsSource name rule.removed],
          if rule.guards.isEmpty then conjunctionSource (rule.body.map (goalSource name))
            else SourceSignature.compound "|" [conjunctionSource (rule.guards.map (guardSource name)),
              conjunctionSource (rule.body.map (goalSource name))]]]) := by
    unfold ruleSource
    exact application_compound _ _
  unfold CHRPrologLowering.form
  rw [shape]
  simp [lowered, Functor.map, Except.map]

/-! ## Programs -/

/-- The sentences of a program's canonical source, the variables of rule
`index` named by `names index`. -/
def programSources (names : Nat → Nat → Variable) (program : CHR.Program) (inputs : List CHR.Constraint) :
    List SourceTerm :=
  [libraryDirective] ++
    (if program.declarations.isEmpty then [] else [declarationsSource program.declarations, optionDirective]) ++
    program.rules.mapIdx (fun index rule => ruleSource (names index) rule) ++
    (if inputs.isEmpty then [] else [querySource inputs])

/-- The forms those sentences lower to. -/
def programForms (program : CHR.Program) (inputs : List CHR.Constraint) : List CHRPrologLowering.Form :=
  [.metadata] ++
    (if program.declarations.isEmpty then [] else [.declarations program.declarations, .metadata]) ++
    program.rules.map (fun rule => .rule (normalRule rule)) ++
    (if inputs.isEmpty then [] else [.query inputs])

/-- What the canonical printer can write so that it reads back. -/
structure ProgramPrintable (program : CHR.Program) (inputs : List CHR.Constraint) : Prop where
  rules : ∀ rule ∈ program.rules, RulePrintable rule
  inputs : ∀ constraint ∈ inputs, QueryPrintable constraint

theorem sentences_form (names : Nat → Nat → Variable) (canonical : ∀ index, Canonical (names index))
    (program : CHR.Program) (inputs : List CHR.Constraint) (printable : ProgramPrintable program inputs) :
    List.Forall₂ (fun source form => ∀ ordinal, CHRPrologLowering.form ordinal source = .ok form)
      (programSources names program inputs) (programForms program inputs) := by
  unfold programSources programForms
  have rules : List.Forall₂ (fun source form => ∀ ordinal, CHRPrologLowering.form ordinal source = .ok form)
      (program.rules.mapIdx fun index rule => ruleSource (names index) rule)
      (program.rules.map fun rule => .rule (normalRule rule)) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun index first second => ?_⟩
    have inside : index < program.rules.length := by simpa using first
    simp only [List.get_eq_getElem, List.getElem_mapIdx, List.getElem_map]
    exact fun ordinal => rule_form (names index) (canonical index) ordinal _
      (printable.rules _ (List.getElem_mem inside))
  have declarations : List.Forall₂ (fun source form => ∀ ordinal, CHRPrologLowering.form ordinal source = .ok form)
      (if program.declarations.isEmpty then [] else [declarationsSource program.declarations, optionDirective])
      (if program.declarations.isEmpty then [] else [.declarations program.declarations, .metadata]) := by
    by_cases empty : program.declarations.isEmpty
    · simp only [empty, if_true]
      exact .nil
    · simp only [empty, if_false, Bool.false_eq_true]
      have nonempty : program.declarations ≠ [] := by simpa using empty
      exact .cons (fun ordinal => declarations_form ordinal _ nonempty) (.cons option_form .nil)
  have query : List.Forall₂ (fun source form => ∀ ordinal, CHRPrologLowering.form ordinal source = .ok form)
      (if inputs.isEmpty then [] else [querySource inputs])
      (if inputs.isEmpty then [] else [.query inputs]) := by
    by_cases empty : inputs.isEmpty
    · simp only [empty, if_true]
      exact .nil
    · simp only [empty, if_false, Bool.false_eq_true]
      have nonempty : inputs ≠ [] := by simpa using empty
      exact .cons (fun ordinal => query_form ordinal inputs nonempty printable.inputs) .nil
  exact List.rel_append (List.rel_append (List.rel_append (.cons library_form .nil) declarations) rules) query

theorem flatMap_rules_nil {α : Type} (select : CHRPrologLowering.Form → List α)
    (none : ∀ rule, select (.rule rule) = []) :
    ∀ rules : List CHR.Rule, (rules.map fun rule => CHRPrologLowering.Form.rule (normalRule rule)).flatMap select = []
  | [] => rfl
  | rule :: rest => by
    rw [List.map_cons, List.flatMap_cons, none, flatMap_rules_nil select none rest]
    rfl

theorem programForms_flatMap {α : Type} (program : CHR.Program) (inputs : List CHR.Constraint)
    (select : CHRPrologLowering.Form → List α) (onRule : ∀ rule, select (.rule rule) = [])
    (onMetadata : select .metadata = []) :
    (programForms program inputs).flatMap select =
      (if program.declarations.isEmpty then [] else select (.declarations program.declarations)) ++
        (if inputs.isEmpty then [] else select (.query inputs)) := by
  unfold programForms
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_append, flatMap_rules_nil select onRule]
  by_cases empty : program.declarations.isEmpty <;> by_cases noInputs : inputs.isEmpty <;>
    simp [empty, noInputs, onMetadata]

theorem filterMap_some_eq {α β : Type} (convert : α → β) :
    ∀ items : List α, items.filterMap (fun item => some (convert item)) = items.map convert
  | [] => rfl
  | item :: rest => by simp [filterMap_some_eq convert rest]

theorem programForms_filterMap (program : CHR.Program) (inputs : List CHR.Constraint)
    (select : CHRPrologLowering.Form → Option CHR.Rule) (onRule : ∀ rule, select (.rule rule) = some rule)
    (onMetadata : select .metadata = none) (onDeclarations : ∀ rows, select (.declarations rows) = none)
    (onQuery : ∀ rows, select (.query rows) = none) :
    (programForms program inputs).filterMap select = program.rules.map normalRule := by
  unfold programForms
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append, List.filterMap_map]
  have rulesPart : program.rules.filterMap (select ∘ fun rule => CHRPrologLowering.Form.rule (normalRule rule)) =
      program.rules.map normalRule := by
    simp only [Function.comp_def, onRule]
    exact filterMap_some_eq normalRule program.rules
  rw [rulesPart]
  by_cases empty : program.declarations.isEmpty <;> by_cases noInputs : inputs.isEmpty <;>
    simp [empty, noInputs, onMetadata, onDeclarations, onQuery]

theorem ite_isEmpty {α : Type} (items : List α) : (if items.isEmpty then [] else items) = items := by
  cases items <;> rfl

theorem assemble_forms (program : CHR.Program) (inputs : List CHR.Constraint)
    (declared : ∀ constraint ∈ inputs,
      CHR.Admission.declared program ⟨constraint.name, constraint.arguments.map CHR.Term.value⟩ = true)
    (admitted : CHR.Admission.diagnose program = none) :
    CHRPrologLowering.assemble (programForms program inputs) = .ok ⟨normalProgram program, inputs⟩ := by
  have allDeclared : inputs.all (fun constraint => CHR.Admission.declared (normalProgram program)
      ⟨constraint.name, constraint.arguments.map CHR.Term.value⟩) = true := by
    rw [List.all_eq_true]
    intro constraint member
    rw [declared_same (first := normalProgram program) (second := program) rfl]
    exact declared constraint member
  have normalAdmitted := (diagnose_normal_none program).mpr admitted
  simp only [normalProgram] at allDeclared normalAdmitted
  unfold CHRPrologLowering.assemble
  simp only [programForms_flatMap, programForms_filterMap, implies_true, ite_isEmpty]
  simp [allDeclared, normalAdmitted, normalProgram, pure, Except.pure]

#print axioms declarations_form
#print axioms sentences_form
#print axioms assemble_forms
#print axioms query_form
#print axioms rule_form

example : TellPrintable ⟨"is", [.value (.integer 7)]⟩ := by simp [TellPrintable]
example : ¬TellPrintable ⟨"is", [.var 0, .value (.integer 7)]⟩ := by simp [TellPrintable]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologReadback
