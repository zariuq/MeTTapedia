import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# Reusing computations under disjoint equation extensions

An extension may add new calls while retaining an existing computation. Its
heads must avoid every call in the old bodies, including constructor and host
heads. Preserving only old equation names would let an extension turn old
constructor data into executable calls.

The transport compares the actual dispatcher and evaluator at every fuel.
It preserves values, failure and exhaustion, for arbitrary environments and
direct-call arguments. Reading a bound value does not execute that value.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

mutual
def calledHeads : Term → List String
  | .sym _ | .lit _ | .var _ => []
  | .list items => calledHeadsList items
  | .expr (.sym head :: arguments) => head :: calledHeadsList arguments
  | .expr items => calledHeadsList items

def calledHeadsList : List Term → List String
  | [] => []
  | first :: rest => calledHeads first ++ calledHeadsList rest
end

def CallsWithin (heads : List String) (source : Term) : Prop :=
  ∀ head ∈ calledHeads source, head ∈ heads

def Program.calledHeads (program : Program) : List String :=
  program.flatMap fun equation => equation.head :: DeterministicEquations.calledHeads equation.body

private theorem calledHeadsList_member {items : List Term} {item : Term} {head : String}
    (member : item ∈ items) (used : head ∈ calledHeads item) : head ∈ calledHeadsList items := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact List.mem_append_left _ used
      · exact List.mem_append_right _ (ih later)

private theorem calledHeads_expr_items (items : List Term) {head : String}
    (used : head ∈ calledHeadsList items) : head ∈ calledHeads (.expr items) := by
  cases items with
  | nil => cases used
  | cons first rest =>
      cases first with
      | sym name => exact List.mem_cons_of_mem _ used
      | lit _ => exact used
      | var _ => exact used
      | list _ => exact used
      | expr _ => exact used

theorem CallsWithin.expr_child {heads : List String} {items : List Term} {item : Term}
    (confined : CallsWithin heads (.expr items)) (member : item ∈ items) :
    CallsWithin heads item :=
  fun head used => confined head (calledHeads_expr_items items (calledHeadsList_member member used))

theorem CallsWithin.list_child {heads : List String} {items : List Term} {item : Term}
    (confined : CallsWithin heads (.list items)) (member : item ∈ items) :
    CallsWithin heads item :=
  fun head used => confined head (calledHeadsList_member member used)

theorem CallsWithin.head {heads : List String} {head : String} {arguments : List Term}
    (confined : CallsWithin heads (.expr (.sym head :: arguments))) : head ∈ heads :=
  confined head (List.mem_cons_self ..)

theorem Program.calledHeads_body {program : Program} {equation : Equation}
    (member : equation ∈ program) : CallsWithin program.calledHeads equation.body := by
  intro head used
  exact List.mem_flatMap.mpr ⟨equation, member, List.mem_cons_of_mem _ used⟩

theorem Program.calledHeads_head {program : Program} {equation : Equation}
    (member : equation ∈ program) : equation.head ∈ program.calledHeads :=
  List.mem_flatMap.mpr ⟨equation, member, List.mem_cons_self ..⟩

theorem Program.selected_mem {program : Program} {head : String} {arguments : List Term}
    {equation : Equation} {environment : Env}
    (selected : program.select head arguments = some (equation, environment)) : equation ∈ program := by
  obtain ⟨candidate, member, found⟩ := List.exists_of_findSome?_eq_some selected
  split at found
  · cases matched : matchTerms candidate.params arguments with
    | none => simp [matched] at found
    | some bindings =>
        simp only [matched, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
        exact found.1 ▸ member
  · cases found

/-- Equality of the real call-dispatch fields on the declared call domain. -/
structure DispatchAgreement (source target : Program) (heads : List String) : Prop where
  definesAt : ∀ head ∈ heads, ∀ arity, source.definesAt head arity = target.definesAt head arity
  defines : ∀ head ∈ heads, source.defines head = target.defines head
  select : ∀ head ∈ heads, ∀ arguments, source.select head arguments = target.select head arguments

private theorem items_eq_on {ev ev' : Env → Term → Outcome} {environment : Env} (items : List Term)
    (equal : ∀ item ∈ items, ev environment item = ev' environment item) :
    evalItemsWith ev environment items = evalItemsWith ev' environment items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp only [evalItemsWith, equal first (List.mem_cons_self ..)]
      rw [ih (fun item member => equal item (List.mem_cons_of_mem _ member))]

/-- Every fuel gives the same outcome under equal dispatch and closed bodies.
The body condition is syntactic and follows from `Program.calledHeads_body`
for the automatic call domain of a program. -/
theorem eval_dispatch_eq {source target : Program} {heads : List String} (host : Host)
    (dispatch : DispatchAgreement source target heads)
    (closed : ∀ equation ∈ source, CallsWithin heads equation.body)
    (fuel : Nat) (environment : Env) (term : Term) (confined : CallsWithin heads term) :
    eval source host fuel environment term = eval target host fuel environment term := by
  induction fuel generalizing environment term with
  | zero => rfl
  | succ fuel ih =>
      have callEqual (head : String) (used : head ∈ heads) (arguments : List Term) :
          apply source host fuel head arguments = apply target host fuel head arguments := by
        unfold apply applyWith
        rw [← dispatch.definesAt head used arguments.length, ← dispatch.defines head used,
          ← dispatch.select head used arguments]
        split
        · cases selected : source.select head arguments with
          | none => rfl
          | some pair =>
              exact ih pair.2 pair.1.body (closed pair.1 (Program.selected_mem selected))
        · rfl
      rw [eval, eval]
      cases term with
      | var _ => rfl
      | sym _ => rfl
      | lit _ => rfl
      | list items =>
          have same := items_eq_on items (fun item member => ih environment item (confined.list_child member))
          simp only [evalStep, same]
      | expr items =>
          unfold evalStep
          split
          · rename_i _ _ impossible
            cases impossible
          · rename_i _ _ impossible
            cases impossible
          · rename_i _ _ impossible
            cases impossible
          · rename_i _ _ impossible
            cases impossible
          · rfl
          · rename_i _ name value body same
            have equalItems := Term.expr.inj same
            subst items
            rw [ih environment value (confined.expr_child (by simp))]
            split
            · exact ih _ body (confined.expr_child (by simp))
            · rfl
          · rfl
          · rfl
          · rfl
          · rename_i _ head arguments _ _ _ _ same
            have equalItems := Term.expr.inj same
            subst items
            rw [items_eq_on arguments (fun item member =>
              ih environment item (confined.expr_child (List.mem_cons_of_mem _ member)))]
            split
            · exact callEqual head confined.head _
            · rfl
          · rename_i _ terms _ _ _ _ _ _ same
            have equalItems := Term.expr.inj same
            subst items
            rw [items_eq_on terms (fun item member => ih environment item (confined.expr_child member))]

theorem apply_dispatch_eq {source target : Program} {heads : List String} (host : Host)
    (dispatch : DispatchAgreement source target heads)
    (closed : ∀ equation ∈ source, CallsWithin heads equation.body)
    (fuel : Nat) (head : String) (used : head ∈ heads) (arguments : List Term) :
    apply source host fuel head arguments = apply target host fuel head arguments := by
  unfold apply applyWith
  rw [← dispatch.definesAt head used arguments.length, ← dispatch.defines head used,
    ← dispatch.select head used arguments]
  split
  · cases selected : source.select head arguments with
    | none => rfl
    | some pair =>
        exact eval_dispatch_eq host dispatch closed fuel pair.2 pair.1.body
          (closed pair.1 (Program.selected_mem selected))
  · rfl

theorem Program.select_none_of_undefined {program : Program} {head : String}
    (undefined : program.defines head = false) (arguments : List Term) :
    program.select head arguments = none := by
  simp only [Program.defines, List.any_eq_false] at undefined
  unfold Program.select
  apply List.findSome?_eq_none_iff.mpr
  intro equation member
  have different : equation.head ≠ head := by
    intro same
    have refused := undefined equation member
    simp [same] at refused
  simp [different]

/-- Adding definitions outside all old calls preserves old dispatch,
including constructor and primitive calls. -/
theorem DispatchAgreement.append (source addition : Program)
    (disjoint : ∀ equation ∈ addition, equation.head ∉ source.calledHeads) :
    DispatchAgreement source (source ++ addition) source.calledHeads := by
  have undefined (head : String) (used : head ∈ source.calledHeads) : addition.defines head = false := by
    simp only [Program.defines, List.any_eq_false]
    intro equation member
    have different : equation.head ≠ head := fun same => disjoint equation member (same.symm ▸ used)
    simp [different]
  constructor
  · intro head used arity
    unfold Program.definesAt
    rw [List.any_append]
    change source.definesAt head arity = (source.definesAt head arity || addition.definesAt head arity)
    rw [Program.definesAt_false_of_defines_false (undefined head used) arity, Bool.or_false]
  · intro head used
    unfold Program.defines
    rw [List.any_append]
    change source.defines head = (source.defines head || addition.defines head)
    rw [undefined head used, Bool.or_false]
  · intro head used arguments
    unfold Program.select
    rw [List.findSome?_append]
    change source.select head arguments = (source.select head arguments).or (addition.select head arguments)
    rw [Program.select_none_of_undefined (undefined head used) arguments, Option.or_none]

theorem apply_append_eq (source addition : Program) (host : Host)
    (disjoint : ∀ equation ∈ addition, equation.head ∉ source.calledHeads)
    (fuel : Nat) (head : String) (used : head ∈ source.calledHeads) (arguments : List Term) :
    apply (source ++ addition) host fuel head arguments = apply source host fuel head arguments :=
  (apply_dispatch_eq host (DispatchAgreement.append source addition disjoint)
    (fun _ member => Program.calledHeads_body member) fuel head used arguments).symm

theorem Applies.append_iff (source addition : Program) (host : Host)
    (disjoint : ∀ equation ∈ addition, equation.head ∉ source.calledHeads)
    (head : String) (used : head ∈ source.calledHeads) (arguments : List Term) (result : Term) :
    Applies (source ++ addition) host head arguments result ↔ Applies source host head arguments result := by
  unfold Applies
  simp only [apply_append_eq source addition host disjoint _ head used arguments]

/-- Definitions before and after a component preserve its complete dispatch when
both avoid every call made by that component. First-match order is retained. -/
theorem DispatchAgreement.frame (source leading trailing : Program)
    (before : ∀ equation ∈ leading, equation.head ∉ source.calledHeads)
    (after : ∀ equation ∈ trailing, equation.head ∉ source.calledHeads) :
    DispatchAgreement source (leading ++ source ++ trailing) source.calledHeads := by
  have undefined (extra : Program)
      (apart : ∀ equation ∈ extra, equation.head ∉ source.calledHeads)
      (head : String) (used : head ∈ source.calledHeads) : extra.defines head = false := by
    simp only [Program.defines, List.any_eq_false]
    intro equation member
    have different : equation.head ≠ head := fun same => apart equation member (same.symm ▸ used)
    simp [different]
  constructor
  · intro head used arity
    unfold Program.definesAt
    rw [List.any_append, List.any_append]
    change source.definesAt head arity =
      ((leading.definesAt head arity || source.definesAt head arity) || trailing.definesAt head arity)
    rw [Program.definesAt_false_of_defines_false (undefined leading before head used) arity,
      Program.definesAt_false_of_defines_false (undefined trailing after head used) arity]
    simp only [Bool.false_or, Bool.or_false]
  · intro head used
    unfold Program.defines
    rw [List.any_append, List.any_append]
    change source.defines head = ((leading.defines head || source.defines head) || trailing.defines head)
    rw [undefined leading before head used, undefined trailing after head used]
    simp only [Bool.false_or, Bool.or_false]
  · intro head used arguments
    unfold Program.select
    rw [List.findSome?_append, List.findSome?_append]
    change source.select head arguments =
      ((leading.select head arguments).or (source.select head arguments)).or (trailing.select head arguments)
    rw [Program.select_none_of_undefined (undefined leading before head used) arguments,
      Program.select_none_of_undefined (undefined trailing after head used) arguments,
      Option.none_or, Option.or_none]

theorem eval_frame_eq (source leading trailing : Program) (host : Host)
    (before : ∀ equation ∈ leading, equation.head ∉ source.calledHeads)
    (after : ∀ equation ∈ trailing, equation.head ∉ source.calledHeads)
    (fuel : Nat) (environment : Env) (term : Term) (confined : CallsWithin source.calledHeads term) :
    eval (leading ++ source ++ trailing) host fuel environment term =
      eval source host fuel environment term :=
  (eval_dispatch_eq host (DispatchAgreement.frame source leading trailing before after)
    (fun _ member => Program.calledHeads_body member) fuel environment term confined).symm

theorem apply_frame_eq (source leading trailing : Program) (host : Host)
    (before : ∀ equation ∈ leading, equation.head ∉ source.calledHeads)
    (after : ∀ equation ∈ trailing, equation.head ∉ source.calledHeads)
    (fuel : Nat) (head : String) (used : head ∈ source.calledHeads) (arguments : List Term) :
    apply (leading ++ source ++ trailing) host fuel head arguments = apply source host fuel head arguments :=
  (apply_dispatch_eq host (DispatchAgreement.frame source leading trailing before after)
    (fun _ member => Program.calledHeads_body member) fuel head used arguments).symm

theorem Applies.frame_iff (source leading trailing : Program) (host : Host)
    (before : ∀ equation ∈ leading, equation.head ∉ source.calledHeads)
    (after : ∀ equation ∈ trailing, equation.head ∉ source.calledHeads)
    (head : String) (used : head ∈ source.calledHeads) (arguments : List Term) (result : Term) :
    Applies (leading ++ source ++ trailing) host head arguments result ↔ Applies source host head arguments result := by
  unfold Applies
  simp only [apply_frame_eq source leading trailing host before after _ head used arguments]

theorem Applies.prepend_iff (source leading : Program) (host : Host)
    (before : ∀ equation ∈ leading, equation.head ∉ source.calledHeads)
    (head : String) (used : head ∈ source.calledHeads) (arguments : List Term) (result : Term) :
    Applies (leading ++ source) host head arguments result ↔ Applies source host head arguments result := by
  simpa using Applies.frame_iff source leading [] host before (by simp) head used arguments result

namespace ProgramExtensionControls

private def copyProgram : Program :=
  [⟨"copy", "copy", [.var "x"], .expr [.sym "Some", .var "x"]⟩]

private def unrelated : Program := [⟨"other", "other", [.var "x"], .var "x"⟩]

private def constructorOverride : Program :=
  [⟨"override", "Some", [.var "x"], .sym "Invented"⟩]

private def unhandledHost : Host := ⟨fun _ _ => .unhandled⟩

theorem unrelated_definition_preserves_every_call (host : Host) (fuel : Nat) (argument : Term) :
    apply (copyProgram ++ unrelated) host fuel "copy" [argument] =
      apply copyProgram host fuel "copy" [argument] := by
  apply apply_append_eq
  · simp [copyProgram, unrelated, Program.calledHeads, calledHeads, calledHeadsList]
  · simp [copyProgram, Program.calledHeads, calledHeads, calledHeadsList]

theorem constructor_definition_changes_old_result :
    apply copyProgram unhandledHost 2 "copy" [.lit "3"] =
      .value (.expr [.sym "Some", .lit "3"]) ∧
    apply (copyProgram ++ constructorOverride) unhandledHost 2 "copy" [.lit "3"] =
      .value (.sym "Invented") := by
  constructor <;> rfl

theorem constructor_definition_is_not_disjoint :
    ¬ (∀ equation ∈ constructorOverride, equation.head ∉ copyProgram.calledHeads) := by
  simp [copyProgram, constructorOverride, Program.calledHeads, calledHeads, calledHeadsList]

theorem unrelated_prefix_and_suffix_preserve_every_call (host : Host) (fuel : Nat) (argument : Term) :
    apply (unrelated ++ copyProgram ++ unrelated) host fuel "copy" [argument] =
      apply copyProgram host fuel "copy" [argument] := by
  apply apply_frame_eq
  · simp [copyProgram, unrelated, Program.calledHeads, calledHeads, calledHeadsList]
  · simp [copyProgram, unrelated, Program.calledHeads, calledHeads, calledHeadsList]
  · simp [copyProgram, Program.calledHeads, calledHeads, calledHeadsList]

theorem prefix_constructor_capture_changes_old_result :
    apply (constructorOverride ++ copyProgram) unhandledHost 2 "copy" [.lit "3"] =
      .value (.sym "Invented") := by rfl

end ProgramExtensionControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
