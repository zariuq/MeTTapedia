import Mettapedia.GSLT.LanguageDef.Collections.Evaluation
import Mettapedia.Logic.LP.UnificationIdempotence
import Mettapedia.Logic.LP.UnificationRestriction

/-!
# A functional fragment of the collection evaluation model

The fragment is hereditary in the existing term encoding: quoted data,
environments and returned code must exclude `superpose` and stored `match`,
which can be nondeterministic. Calls, constructors, lists, open spines,
quotation, pattern lets, pure unification and map are
retained. Program conditions concern its native/rule relations and their
syntax closure, not an assumed functional evaluation judgment.

Determinism concerns successful results only. It does not establish
termination, and these are laws of `Evaluation`, not native HE adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.FunctionalEvaluation

open Mettapedia.Logic.Unification.ListSplice
open Evaluation

variable {Symbol Var : Type}

def Allowed (builtin : Builtin) : Prop :=
  builtin ≠ .superpose ∧ builtin ≠ .match_

def AllowedConstant : Mettapedia.Logic.Unification.ListPrefixMeeting.Constant (Leaf Symbol) → Prop
  | .nil => True
  | .atom (.sym _) => True
  | .atom (.builtin builtin) => Allowed builtin

abbrev Wire (Symbol Var : Type) :=
  Mettapedia.Logic.Unification.ListPrefixMeeting.Tm (Leaf Symbol) Var

inductive CleanWire : Wire Symbol Var → Prop where
  | variable (name : Var) : CleanWire (.var name)
  | constant (value) : AllowedConstant value → CleanWire (.const value)
  | application {function children} : (∀ index, CleanWire (children index)) → CleanWire (.app function children)

def Clean (term : Tm Symbol Var) : Prop := CleanWire (Encoding.encode term)
def CleanEnv (environment : Env Symbol Var) : Prop := ∀ name, Clean (environment name)
def CleanAll (terms : List (Tm Symbol Var)) : Prop := ∀ term ∈ terms, Clean term

theorem cleanWire_const (value) : CleanWire (.const value : Wire Symbol Var) ↔ AllowedConstant value := by
  constructor
  · intro clean
    cases clean with | constant _ allowed => exact allowed
  · exact CleanWire.constant value

theorem cleanWire_app (function) (children) :
    CleanWire (.app function children : Wire Symbol Var) ↔ ∀ index, CleanWire (children index) := by
  constructor
  · intro clean
    cases clean with | application each => exact each
  · exact CleanWire.application

theorem cleanWire_cons (head tail : Wire Symbol Var) :
    CleanWire (Mettapedia.Logic.Unification.ListPrefixMeeting.cons head tail) ↔ CleanWire head ∧ CleanWire tail := by
  rw [Mettapedia.Logic.Unification.ListPrefixMeeting.cons, cleanWire_app]
  constructor
  · intro each
    exact ⟨by simpa using each 0, by simpa using each 1⟩
  · rintro ⟨first, rest⟩ index
    split <;> assumption

theorem cleanWire_expr (children : List (Wire Symbol Var)) :
    CleanWire (Mettapedia.Logic.Unification.ListPrefixMeeting.expr children) ↔ ∀ child ∈ children, CleanWire child := by
  rw [Mettapedia.Logic.Unification.ListPrefixMeeting.expr, cleanWire_app]
  constructor
  · intro each child member
    obtain ⟨index, same⟩ := List.mem_iff_get.mp member
    exact same ▸ each index
  · intro each index
    exact each _ (List.get_mem ..)

theorem cleanWire_spine (children : List (Wire Symbol Var)) (tail : Option (Wire Symbol Var)) :
    CleanWire (Mettapedia.Logic.Unification.ListPrefixMeeting.spine children tail) ↔
      (∀ child ∈ children, CleanWire child) ∧ CleanWire (Mettapedia.Logic.Unification.ListPrefixMeeting.close tail) := by
  induction children with
  | nil => simp [Mettapedia.Logic.Unification.ListPrefixMeeting.spine]
  | cons child children ih =>
    rw [Mettapedia.Logic.Unification.ListPrefixMeeting.spine_cons, cleanWire_cons, ih]
    simp only [List.forall_mem_cons, and_assoc]

@[simp] theorem clean_symbol (symbol : Symbol) : Clean (.atom (.sym symbol) : Tm Symbol Var) := by
  unfold Clean
  rw [Encoding.encode]
  exact CleanWire.constant _ trivial

@[simp] theorem clean_variable (name : Var) : Clean (.var name : Tm Symbol Var) := by
  unfold Clean
  rw [Encoding.encode]
  exact CleanWire.variable name

theorem clean_builtin (builtin : Builtin) : Clean (head builtin : Tm Symbol Var) ↔ Allowed builtin := by
  simp only [Clean, head, Encoding.encode, cleanWire_const, AllowedConstant]

theorem clean_expr (terms : List (Tm Symbol Var)) : Clean (.expr terms) ↔ CleanAll terms := by
  rw [Clean, Encoding.encode, cleanWire_expr]
  simp only [CleanAll, List.forall_mem_map, Clean]

theorem clean_list (terms : List (Tm Symbol Var)) : Clean (.list terms) ↔ CleanAll terms := by
  rw [Clean, Encoding.encode, cleanWire_spine]
  simp only [Mettapedia.Logic.Unification.ListPrefixMeeting.close_none,
    Mettapedia.Logic.Unification.ListPrefixMeeting.nil, cleanWire_const, AllowedConstant, and_true,
    CleanAll, List.forall_mem_map, Clean]

theorem clean_rest (terms : List (Tm Symbol Var)) (tail : Tm Symbol Var) :
    Clean (.rest terms tail) ↔ CleanAll terms ∧ Clean tail := by
  rw [Clean, Encoding.encode, cleanWire_spine]
  simp only [Mettapedia.Logic.Unification.ListPrefixMeeting.close_some, CleanAll, List.forall_mem_map, Clean]

theorem clean_normalize {term : Tm Symbol Var} (clean : Clean term) : Clean (normalize term) := by
  simpa only [Clean, Encoding.encode_normalize] using clean

theorem cleanWire_subst (substitution : Mettapedia.Logic.Unification.ListPrefixMeeting.Substitution (Leaf Symbol) Var)
    (cleanSubstitution : ∀ name, CleanWire (substitution name)) {term : Wire Symbol Var} (clean : CleanWire term) :
    CleanWire (substitution.applyTerm term) := by
  induction clean with
  | «variable» name => exact cleanSubstitution name
  | constant value allowed => exact CleanWire.constant value allowed
  | application each ih => exact CleanWire.application ih

theorem clean_inst {environment : Env Symbol Var} {term : Tm Symbol Var}
    (bindings : CleanEnv environment) (clean : Clean term) : Clean (inst environment term) := by
  rw [Clean, inst, Encoding.encode_normalize, Encoding.encode_subst]
  exact cleanWire_subst (Encoding.encodeSubst environment) bindings clean

theorem clean_identity : CleanEnv (Term.var : Env Symbol Var) := fun _ => clean_variable _

variable [DecidableEq Var]

theorem clean_bindOne {environment : Env Symbol Var} {name : Var} {value : Tm Symbol Var}
    (bindings : CleanEnv environment) (clean : Clean value) : CleanEnv (Program.bindOne environment name value) := by
  intro other
  unfold Program.bindOne
  split
  · exact clean
  · exact bindings other

/-- A clean substituted term has clean images for the variables it really
mentions. No condition on unused substitution entries follows or is needed. -/
theorem cleanWire_substituted_variable
    (substitution : Mettapedia.Logic.Unification.ListPrefixMeeting.Substitution (Leaf Symbol) Var)
    (term : Wire Symbol Var) (clean : CleanWire (substitution.applyTerm term)) :
    ∀ name ∈ term.freeVars, CleanWire (substitution name) := by
  induction term with
  | var original =>
    intro name member
    have same : name = original := by simpa [Mettapedia.Logic.LP.Term.freeVars] using member
    exact same ▸ clean
  | const value =>
    intro name member
    simp [Mettapedia.Logic.LP.Term.freeVars] at member
  | app function children ih =>
    intro name member
    obtain ⟨index, occurs⟩ := Mettapedia.Logic.LP.Term.mem_freeVars_app.mp member
    exact ih index ((cleanWire_app _ _).mp clean index) name occurs

theorem substituted_variables_agree
    (first second : Mettapedia.Logic.Unification.ListPrefixMeeting.Substitution (Leaf Symbol) Var)
    (term : Wire Symbol Var) (same : first.applyTerm term = second.applyTerm term) :
    ∀ name ∈ term.freeVars, first name = second name := by
  induction term with
  | var original =>
    intro name member
    have equal : name = original := by simpa [Mettapedia.Logic.LP.Term.freeVars] using member
    exact equal ▸ same
  | const value =>
    intro name member
    simp [Mettapedia.Logic.LP.Term.freeVars] at member
  | app function children ih =>
    intro name member
    obtain ⟨index, occurs⟩ := Mettapedia.Logic.LP.Term.mem_freeVars_app.mp member
    have childrenSame : (fun index => first.applyTerm (children index)) =
        (fun index => second.applyTerm (children index)) := by
      simpa only [Mettapedia.Logic.LP.Subst.applyTerm, Mettapedia.Logic.LP.Term.app.injEq, heq_eq_eq, true_and] using same
    exact ih index (congrFun childrenSame index) name occurs

theorem bindPattern_congr (environment first second : Env Symbol Var) (pattern bound : Tm Symbol Var)
    (left : Equivalent (subst first pattern) bound) (right : Equivalent (subst second pattern) bound) :
    Program.bindPattern environment first pattern = Program.bindPattern environment second pattern := by
  have equal := ((Encoding.encode_eq_iff _ _).mpr left).trans ((Encoding.encode_eq_iff _ _).mpr right).symm
  rw [Encoding.encode_subst, Encoding.encode_subst] at equal
  funext name
  unfold Program.bindPattern
  split
  next member =>
    have image := substituted_variables_agree (Encoding.encodeSubst first) (Encoding.encodeSubst second)
      (Encoding.encode pattern) equal name member
    exact (Encoding.decode_encode (first name)).symm.trans
      ((congrArg Encoding.decode image).trans (Encoding.decode_encode (second name)))
  next => rfl

theorem clean_bindPattern {environment substitution : Env Symbol Var} {pattern bound : Tm Symbol Var}
    (bindings : CleanEnv environment) (clean : Clean bound) (matched : Equivalent (subst substitution pattern) bound) :
    CleanEnv (Program.bindPattern environment substitution pattern) := by
  have same := (Encoding.encode_eq_iff _ _).mpr matched
  rw [Encoding.encode_subst] at same
  have allClean : CleanWire ((Encoding.encodeSubst substitution).applyTerm (Encoding.encode pattern)) := same.symm ▸ clean
  intro name
  unfold Program.bindPattern
  split
  next member =>
    apply clean_normalize
    exact cleanWire_substituted_variable (Encoding.encodeSubst substitution) (Encoding.encode pattern) allClean name member
  next => exact bindings name

omit [DecidableEq Var] in
theorem clean_afterUnify {environment substitution : Env Symbol Var}
    (bindings : CleanEnv environment) (images : CleanEnv substitution) :
    CleanEnv (Program.afterUnify environment substitution) :=
  fun name => clean_inst images (bindings name)

/-- Independent obligations on primitive computation and equation dispatch.
None of the fields asserts determinism or successful execution of Eval. -/
structure Functional (program : Program Symbol Var) : Prop where
  native_unique : ∀ function arguments first second,
    program.native function arguments first → program.native function arguments second → first = second
  rule_unique : ∀ function arguments firstEnv firstBody secondEnv secondBody,
    program.rule function arguments firstEnv firstBody → program.rule function arguments secondEnv secondBody →
      firstEnv = secondEnv ∧ firstBody = secondBody
  disjoint : ∀ function arguments value environment body,
    program.native function arguments value → program.rule function arguments environment body → False
  native_clean : ∀ function arguments value, CleanAll arguments → program.native function arguments value → Clean value
  rule_clean : ∀ function arguments environment body,
    CleanAll arguments → program.rule function arguments environment body → CleanEnv environment ∧ Clean body

variable [DecidableEq Symbol]

omit [DecidableEq Var] [DecidableEq Symbol] in
theorem cleanWire_iff_respect (term : Wire Symbol Var) :
    CleanWire term ↔ Mettapedia.Logic.LP.UnificationRestriction.Respect AllowedConstant term := by
  induction term with
  | var name =>
    constructor
    · intro _
      trivial
    · intro _
      exact CleanWire.variable name
  | const value => exact cleanWire_const value
  | app function children ih =>
    rw [cleanWire_app]
    exact forall_congr' ih

/-- The actual source solver's substitution introduces no forbidden builtin.
The proof uses its first-order MGU and the lossless cons encoding. -/
theorem clean_solve {left right : Tm Symbol Var} {substitution : Env Symbol Var}
    (leftClean : Clean left) (rightClean : Clean right)
    (solved : Encoding.solve left right = some substitution) : CleanEnv substitution := by
  classical
  unfold Encoding.solve at solved
  obtain ⟨wireSubstitution, accepted, rfl⟩ := Option.map_eq_some_iff.mp solved
  have images := Mettapedia.Logic.LP.UnificationRestriction.unifyTotal_respects
    AllowedConstant (.nil : Mettapedia.Logic.Unification.ListPrefixMeeting.Constant (Leaf Symbol))
    (by trivial) [(Encoding.encode left, Encoding.encode right)] wireSubstitution accepted (by
      intro pair member
      have same := List.mem_singleton.mp member
      subst pair
      exact ⟨(cleanWire_iff_respect _).mp leftClean, (cleanWire_iff_respect _).mp rightClean⟩)
  intro name
  change CleanWire (Encoding.encode (Encoding.decode (wireSubstitution name)))
  rw [Encoding.encode_decode]
  exact (cleanWire_iff_respect _).mpr (images name)

omit [DecidableEq Var] [DecidableEq Symbol] in
private theorem clean_child {terms : List (Tm Symbol Var)} (clean : Clean (.expr terms))
    (term : Tm Symbol Var) (member : term ∈ terms) : Clean term := (clean_expr terms).mp clean term member

omit [DecidableEq Var] [DecidableEq Symbol] in
private theorem forbidden_head {builtin : Builtin} {arguments : List (Tm Symbol Var)}
    (clean : Clean (.expr (head builtin :: arguments))) : Allowed builtin :=
  (clean_builtin builtin).mp (clean_child clean _ List.mem_cons_self)

theorem eval_properties {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {term value : Tm Symbol Var}
    (first : Eval program environment term value) (bindings : CleanEnv environment) (clean : Clean term) :
    Clean value ∧ ∀ other, Eval program environment term other → value = other := by
  revert bindings clean
  refine Eval.rec
    (motive_1 := fun environment term value _ => CleanEnv environment → Clean term →
      Clean value ∧ ∀ other, Eval program environment term other → value = other)
    (motive_2 := fun environment terms values _ => CleanEnv environment → CleanAll terms →
      CleanAll values ∧ ∀ other, EvalAll program environment terms other → values = other)
    (motive_3 := fun environment modes terms values _ => CleanEnv environment → CleanAll terms →
      CleanAll values ∧ ∀ other, Receive program environment modes terms other → values = other)
    (motive_4 := fun mode environment body value _ => CleanEnv environment → Clean body →
      Clean value ∧ ∀ other, Return program mode environment body other → value = other)
    (motive_5 := fun mode value result _ => Clean value →
      Clean result ∧ ∀ other, Output program mode value other → result = other)
    (motive_6 := fun environment name body inputs outputs _ => CleanEnv environment → Clean body → CleanAll inputs →
      CleanAll outputs ∧ ∀ other, EvalEach program environment name body inputs other → outputs = other)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ first
  · intro environment symbol absent bindings clean
    exact ⟨clean, fun _ other => by cases other; rfl⟩
  · intro environment builtin bindings clean
    exact ⟨clean, fun _ other => by cases other; rfl⟩
  · intro environment name data bindings clean
    exact ⟨bindings name, fun other run => ((eval_var_iff data name other).mp run).symm⟩
  · intro environment name free bindings clean
    refine ⟨clean_variable name, ?_⟩
    intro other run
    cases run with
    | variableData => exact free.symm
    | variableFree => rfl
    | variableCode _ notFree _ => exact (notFree free).elim
  · intro environment name value code bound run ih bindings clean
    have result := ih clean_identity (bindings name)
    exact ⟨result.1, fun other again => result.2 other ((eval_var_code_iff code name bound other).mp again)⟩
  · intro environment terms bindings clean
    exact ⟨clean_inst bindings clean, fun other run => ((eval_list_iff _ other).mp run).symm⟩
  · intro environment terms tail bindings clean
    exact ⟨clean_inst bindings clean, fun other run => ((eval_rest_iff _ _ other).mp run).symm⟩
  · intro environment terms values notCall each ih bindings clean
    have result := ih bindings ((clean_expr terms).mp clean)
    refine ⟨(clean_expr values).mpr result.1, ?_⟩
    intro other run
    obtain ⟨outputs, eachOutput, rfl⟩ := (eval_construct_iff terms notCall other).mp run
    exact congrArg Term.expr (result.2 outputs eachOutput)
  · intro environment function modes args received value output passing receives native delivered
      inputIH outputIH bindings clean
    have input := inputIH bindings
      (fun term member => clean_child clean term (List.mem_cons_of_mem _ member))
    have result := outputIH (functional.native_clean function received value input.1 native)
    refine ⟨result.1, ?_⟩
    intro other run
    rcases (eval_call_iff function args other).mp run with
      ⟨absent, _⟩ | ⟨otherModes, otherReceived, otherPassing, otherReceives,
        ⟨otherValue, otherNative, otherDelivered⟩ | ⟨otherEnv, otherBody, otherRule, _⟩⟩
    · rw [passing] at absent
      cases absent
    · have modeEq := Option.some.inj (passing.symm.trans otherPassing)
      subst otherModes
      have receivedEq := input.2 otherReceived otherReceives
      subst otherReceived
      have valueEq := functional.native_unique function received value otherValue native otherNative
      subst otherValue
      exact result.2 other otherDelivered
    · have modeEq := Option.some.inj (passing.symm.trans otherPassing)
      subst otherModes
      have receivedEq := input.2 otherReceived otherReceives
      subst otherReceived
      exact (functional.disjoint function received value otherEnv otherBody native otherRule).elim
  · intro environment function modes args received ruleEnv body value passing receives rule returned inputIH resultIH bindings clean
    have input := inputIH bindings
      (fun term member => clean_child clean term (List.mem_cons_of_mem _ member))
    have ruleClean := functional.rule_clean function received ruleEnv body input.1 rule
    have result := resultIH ruleClean.1 ruleClean.2
    refine ⟨result.1, ?_⟩
    intro other run
    rcases (eval_call_iff function args other).mp run with
      ⟨absent, _⟩ | ⟨otherModes, otherReceived, otherPassing, otherReceives,
        ⟨otherValue, otherNative, _⟩ | ⟨otherEnv, otherBody, otherRule, otherReturn⟩⟩
    · rw [passing] at absent
      cases absent
    · have modeEq := Option.some.inj (passing.symm.trans otherPassing)
      subst otherModes
      have receivedEq := input.2 otherReceived otherReceives
      subst otherReceived
      exact (functional.disjoint function received otherValue ruleEnv body otherNative rule).elim
    · have modeEq := Option.some.inj (passing.symm.trans otherPassing)
      subst otherModes
      have receivedEq := input.2 otherReceived otherReceives
      subst otherReceived
      obtain ⟨envEq, bodyEq⟩ := functional.rule_unique function received ruleEnv body otherEnv otherBody rule otherRule
      subst otherEnv
      subst otherBody
      exact result.2 other otherReturn
  · intro environment body bindings clean
    exact ⟨clean_inst bindings (clean_child clean body (by simp)),
      fun other run => ((eval_quote_iff body other).mp run).symm⟩
  · intro environment pattern producer bound substitution body value produced matched evaluated inputIH resultIH bindings clean
    have input := inputIH bindings (clean_child clean producer (by simp))
    have nextBindings := clean_bindPattern bindings input.1 matched
    have result := resultIH nextBindings (clean_child clean body (by simp))
    refine ⟨result.1, ?_⟩
    intro other run
    obtain ⟨otherBound, otherSubstitution, otherProduced, otherMatched, otherEvaluated⟩ :=
      (eval_let_iff pattern producer body other).mp run
    have boundEq := input.2 otherBound otherProduced
    subst otherBound
    have environmentEq := bindPattern_congr environment substitution otherSubstitution pattern bound matched otherMatched
    rw [← environmentEq] at otherEvaluated
    exact result.2 other otherEvaluated
  · intro environment left right substitution yes no value solved evaluated ih bindings clean
    have cleanSubstitution := clean_solve (clean_inst bindings (clean_child clean left (by simp)))
      (clean_inst bindings (clean_child clean right (by simp))) solved
    have result := ih (clean_afterUnify bindings cleanSubstitution) (clean_child clean yes (by simp))
    refine ⟨result.1, ?_⟩
    intro other run
    rcases (eval_unify_iff left right yes no other).mp run with
      ⟨otherSubstitution, otherSolved, otherBranch⟩ | ⟨failed, _⟩
    · have same := Option.some.inj (solved.symm.trans otherSolved)
      subst otherSubstitution
      exact result.2 other otherBranch
    · rw [solved] at failed
      cases failed
  · intro environment left right yes no value failed evaluated ih bindings clean
    have result := ih bindings (clean_child clean no (by simp))
    refine ⟨result.1, ?_⟩
    intro other run
    rcases (eval_unify_iff left right yes no other).mp run with
      ⟨_, solved, _⟩ | ⟨_, otherBranch⟩
    · rw [failed] at solved
      cases solved
    · exact result.2 other otherBranch
  · intros
    rename_i bindings clean
    exact ((forbidden_head clean).1 rfl).elim
  · intros
    rename_i bindings clean
    exact ((forbidden_head clean).2 rfl).elim
  · intro environment source name body inputs outputs listed each inputIH resultIH bindings clean
    have input := inputIH bindings (clean_child clean source (by simp))
    have result := resultIH bindings (clean_child clean body (by simp))
      ((clean_list inputs).mp input.1)
    refine ⟨(clean_list outputs).mpr result.1, ?_⟩
    intro other run
    obtain ⟨otherInputs, otherOutputs, otherListed, otherEach, rfl⟩ := (eval_map_iff source body name other).mp run
    have inputsEq := Term.list.inj (input.2 _ otherListed)
    subst otherInputs
    exact congrArg Term.list (result.2 otherOutputs otherEach)
  · intro environment bindings clean
    constructor
    · intro _ member
      cases member
    · intro _ other
      cases other
      rfl
  · intro environment term terms value values evaluated evaluatedRest oneIH restIH bindings clean
    have one := oneIH bindings (clean term List.mem_cons_self)
    have rest := restIH bindings (fun term member => clean term (List.mem_cons_of_mem _ member))
    refine ⟨?_, ?_⟩
    · intro term member
      rcases List.mem_cons.mp member with rfl | later
      · exact one.1
      · exact rest.1 term later
    · intro other run
      cases run with
      | cons otherOne otherRest => exact congrArg₂ List.cons (one.2 _ otherOne) (rest.2 _ otherRest)
  · intro environment bindings clean
    constructor
    · intro _ member
      cases member
    · intro _ other
      cases other
      rfl
  · intro environment modes term terms values received restIH bindings clean
    have one := clean_inst bindings (clean term List.mem_cons_self)
    have rest := restIH bindings (fun term member => clean term (List.mem_cons_of_mem _ member))
    refine ⟨?_, ?_⟩
    · intro term member
      rcases List.mem_cons.mp member with rfl | later
      · exact one
      · exact rest.1 term later
    · intro other run
      cases run with
      | data otherRest => exact congrArg (List.cons _) (rest.2 _ otherRest)
  · intro environment modes term terms value values evaluated received oneIH restIH bindings clean
    have one := oneIH bindings (clean term List.mem_cons_self)
    have rest := restIH bindings (fun term member => clean term (List.mem_cons_of_mem _ member))
    refine ⟨?_, ?_⟩
    · intro term member
      rcases List.mem_cons.mp member with rfl | later
      · exact one.1
      · exact rest.1 term later
    · intro other run
      cases run with
      | evaluated otherOne otherRest => exact congrArg₂ List.cons (one.2 _ otherOne) (rest.2 _ otherRest)
  · intro environment body bindings clean
    exact ⟨clean_inst bindings clean, fun _ other => by cases other; rfl⟩
  · intro environment body value run ih bindings clean
    have result := ih bindings clean
    exact ⟨result.1, fun other returned => result.2 other ((return_once_iff _ _ _).mp returned)⟩
  · intro value clean
    exact ⟨clean, fun other delivered => ((output_asWritten_iff _ _).mp delivered).symm⟩
  · intro value result run ih clean
    have evaluated := ih clean_identity clean
    exact ⟨evaluated.1, fun other delivered => evaluated.2 other ((output_once_iff _ _).mp delivered)⟩
  · intro environment name body bindings bodyClean clean
    constructor
    · intro _ member
      cases member
    · intro _ other
      cases other
      rfl
  · intro environment name body element elements value values evaluated each oneIH restIH bindings bodyClean clean
    have instantiated := clean_inst (clean_bindOne (name := name) bindings (clean element List.mem_cons_self)) bodyClean
    have one := oneIH clean_identity instantiated
    have rest := restIH bindings bodyClean (fun element member => clean element (List.mem_cons_of_mem _ member))
    refine ⟨?_, ?_⟩
    · intro term member
      rcases List.mem_cons.mp member with rfl | later
      · exact one.1
      · exact rest.1 term later
    · intro other run
      cases run with
      | cons otherOne otherRest => exact congrArg₂ List.cons (one.2 _ otherOne) (rest.2 _ otherRest)

theorem all_properties {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {terms values : List (Tm Symbol Var)}
    (first : EvalAll program environment terms values) (bindings : CleanEnv environment) (clean : CleanAll terms) :
    CleanAll values ∧ ∀ other, EvalAll program environment terms other → values = other := by
  revert values first clean
  induction terms with
  | nil =>
    intro values first clean
    cases first
    constructor
    · intro _ member
      cases member
    · intro _ other
      cases other
      rfl
  | cons term terms ih =>
    intro values first clean
    cases first with
    | cons evaluated evaluatedRest =>
      have one := eval_properties functional evaluated bindings (clean term List.mem_cons_self)
      have rest := ih evaluatedRest (fun term member => clean term (List.mem_cons_of_mem _ member))
      refine ⟨?_, ?_⟩
      · intro term member
        rcases List.mem_cons.mp member with rfl | later
        · exact one.1
        · exact rest.1 term later
      · intro other run
        cases run with
        | cons otherOne otherRest => exact congrArg₂ List.cons (one.2 _ otherOne) (rest.2 _ otherRest)

theorem receive_properties {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {modes : List Passing} {terms values : List (Tm Symbol Var)}
    (first : Receive program environment modes terms values) (bindings : CleanEnv environment) (clean : CleanAll terms) :
    CleanAll values ∧ ∀ other, Receive program environment modes terms other → values = other := by
  revert terms values first clean
  induction modes with
  | nil =>
    intro terms values first clean
    cases first
    constructor
    · intro _ member
      cases member
    · intro _ other
      cases other
      rfl
  | cons mode modes ih =>
    intro terms values first clean
    cases first with
    | data received =>
      have one := clean_inst bindings (clean _ List.mem_cons_self)
      have rest := ih received (fun term member => clean term (List.mem_cons_of_mem _ member))
      refine ⟨?_, ?_⟩
      · intro term member
        rcases List.mem_cons.mp member with rfl | later
        · exact one
        · exact rest.1 term later
      · intro other run
        cases run with
        | data otherRest => exact congrArg (List.cons _) (rest.2 _ otherRest)
    | evaluated evaluated received =>
      have one := eval_properties functional evaluated bindings (clean _ List.mem_cons_self)
      have rest := ih received (fun term member => clean term (List.mem_cons_of_mem _ member))
      refine ⟨?_, ?_⟩
      · intro term member
        rcases List.mem_cons.mp member with rfl | later
        · exact one.1
        · exact rest.1 term later
      · intro other run
        cases run with
        | evaluated otherOne otherRest => exact congrArg₂ List.cons (one.2 _ otherOne) (rest.2 _ otherRest)

theorem return_properties {program : Program Symbol Var} (functional : Functional program)
    {mode : Returning} {environment : Env Symbol Var} {body value : Tm Symbol Var}
    (first : Return program mode environment body value) (bindings : CleanEnv environment) (clean : Clean body) :
    Clean value ∧ ∀ other, Return program mode environment body other → value = other := by
  cases first with
  | asWritten => exact ⟨clean_inst bindings clean, fun _ other => by cases other; rfl⟩
  | once run =>
    have result := eval_properties functional run bindings clean
    exact ⟨result.1, fun other returned => result.2 other ((return_once_iff _ _ _).mp returned)⟩

theorem output_properties {program : Program Symbol Var} (functional : Functional program)
    {mode : Returning} {value result : Tm Symbol Var}
    (first : Output program mode value result) (clean : Clean value) :
    Clean result ∧ ∀ other, Output program mode value other → result = other := by
  cases first with
  | asWritten => exact ⟨clean, fun other delivered => ((output_asWritten_iff _ _).mp delivered).symm⟩
  | once run =>
    have evaluated := eval_properties functional run clean_identity clean
    exact ⟨evaluated.1, fun other delivered => evaluated.2 other ((output_once_iff _ _).mp delivered)⟩

theorem each_properties {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {name : Var} {body : Tm Symbol Var} {inputs outputs : List (Tm Symbol Var)}
    (first : EvalEach program environment name body inputs outputs) (bindings : CleanEnv environment)
    (bodyClean : Clean body) (clean : CleanAll inputs) :
    CleanAll outputs ∧ ∀ other, EvalEach program environment name body inputs other → outputs = other := by
  revert outputs first clean
  induction inputs with
  | nil =>
    intro outputs first clean
    cases first
    constructor
    · intro _ member
      cases member
    · intro _ other
      cases other
      rfl
  | cons element elements ih =>
    intro outputs first clean
    cases first with
    | cons evaluated each =>
      have instantiated := clean_inst (clean_bindOne (name := name) bindings (clean element List.mem_cons_self)) bodyClean
      have one := eval_properties functional evaluated clean_identity instantiated
      have rest := ih each (fun element member => clean element (List.mem_cons_of_mem _ member))
      refine ⟨?_, ?_⟩
      · intro term member
        rcases List.mem_cons.mp member with rfl | later
        · exact one.1
        · exact rest.1 term later
      · intro other run
        cases run with
        | cons otherOne otherRest => exact congrArg₂ List.cons (one.2 _ otherOne) (rest.2 _ otherRest)

theorem eval_unique {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {term first second : Tm Symbol Var}
    (bindings : CleanEnv environment) (clean : Clean term)
    (left : Eval program environment term first) (right : Eval program environment term second) : first = second :=
  (eval_properties functional left bindings clean).2 second right

theorem receive_unique {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {modes : List Passing} {terms first second : List (Tm Symbol Var)}
    (bindings : CleanEnv environment) (clean : CleanAll terms)
    (left : Receive program environment modes terms first) (right : Receive program environment modes terms second) : first = second :=
  (receive_properties functional left bindings clean).2 second right

theorem return_unique {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {mode : Returning} {body first second : Tm Symbol Var}
    (bindings : CleanEnv environment) (clean : Clean body)
    (left : Return program mode environment body first) (right : Return program mode environment body second) : first = second :=
  (return_properties functional left bindings clean).2 second right

theorem evalAll_unique {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {terms first second : List (Tm Symbol Var)}
    (bindings : CleanEnv environment) (clean : CleanAll terms)
    (left : EvalAll program environment terms first) (right : EvalAll program environment terms second) : first = second :=
  (all_properties functional left bindings clean).2 second right

theorem evalEach_unique {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {name : Var} {body : Tm Symbol Var} {inputs first second : List (Tm Symbol Var)}
    (bindings : CleanEnv environment) (bodyClean : Clean body) (clean : CleanAll inputs)
    (left : EvalEach program environment name body inputs first) (right : EvalEach program environment name body inputs second) : first = second :=
  (each_properties functional left bindings bodyClean clean).2 second right

theorem eval_iff_value {program : Program Symbol Var} (functional : Functional program)
    {environment : Env Symbol Var} {term value : Tm Symbol Var}
    (bindings : CleanEnv environment) (clean : Clean term) (computed : Eval program environment term value)
    (other : Tm Symbol Var) : Eval program environment term other ↔ other = value :=
  ⟨fun run => (eval_unique functional bindings clean computed run).symm, fun same => same ▸ computed⟩

end Mettapedia.GSLT.LanguageDef.Collections.FunctionalEvaluation
