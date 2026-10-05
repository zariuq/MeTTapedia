import Mettapedia.Languages.MM0.Presentation.SharedWitnessTranslation
import Mettapedia.Languages.MM0.Presentation.MeTTaExecution
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ComputationLists

/-!
# Sequential local certificates in the authored MM0 service

Only the scope protocol is added: check an initializer, append its conclusion
after acceptance, and continue in that scope. Logical checking calls the
existing calculus program. The same equation emitter handles this component.
Each saved entry is data containing its claim and its supplied certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ScopedService

open Kernel Calculus ComputationalCalculus SharedCertificates
open ComputationalContext ComputationalArguments ComputationalProof
open ComputationalTyping ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name
private def theory : List Term := [v "terms", v "definitions", v "theorems"]
private def scope : List Term := theory ++ [v "context", v "hypotheses"]
private def root : List Term := [v "root", v "certificate"]

/-- The claim built from the current variable and local hypothesis scope. -/
def goal (context hypotheses expression : Term) : Term :=
  .expr [.sym "Pattern:Apply", .lit "mm0:derives",
    .list [dataCode context, dataCode hypotheses, dataCode expression]]

private def goalBody : Term :=
  c "Pattern:Apply" [.lit "mm0:derives",
    .list [c "Pattern:Data" [v "context"], c "Pattern:Data" [v "hypotheses"],
      c "Pattern:Data" [v "expression"]]]

def equations : Program := [
  ⟨"scoped-certificate", "mm0:scoped-certificate", scope ++ [v "expression", v "certificate"],
    c "mm0:certificate" (theory ++ [goalBody, v "certificate"])⟩,
  ⟨"scoped-run", "mm0:scoped-run", scope ++ [v "saved"] ++ root,
    c "mm0:scoped-view" ([c "nik:list-view" [v "saved"]] ++ scope ++ root)⟩,
  ⟨"scoped-empty", "mm0:scoped-view", [.sym "List:Nil"] ++ scope ++ root,
    c "mm0:scoped-certificate" (scope ++ root)⟩,
  ⟨"scoped-next", "mm0:scoped-view",
    [c "List:Cons" [.list [v "expression", v "initializer"], v "remaining"]] ++ scope ++ root,
    c "mm0:scoped-continue"
      ([c "mm0:scoped-certificate" (scope ++ [v "expression", v "initializer"])] ++
        scope ++ [v "expression", v "remaining"] ++ root)⟩,
  ⟨"scoped-refused", "mm0:scoped-continue",
    [.sym "False"] ++ scope ++ [v "expression", v "remaining"] ++ root, .sym "False"⟩,
  ⟨"scoped-accepted", "mm0:scoped-continue",
    [.sym "True"] ++ scope ++ [v "expression", v "remaining"] ++ root,
    c "mm0:scoped-run" (theory ++ [v "context",
      c "nik:list-append" [v "hypotheses", .list [v "expression"]],
      v "remaining"] ++ root)⟩]

def program : Program := Service.program ++ equations

theorem equations_disjoint :
    ∀ equation ∈ equations, equation.head ∉ Service.program.calledHeads := by
  have checked : equations.all
      (fun equation => !Service.program.calledHeads.contains equation.head) = true := by
    decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp checked equation member

/-- Every existing call retains its outcomes at every source budget. -/
theorem original_outcomes (fuel : Nat) (head : String)
    (used : head ∈ Service.program.calledHeads) (arguments : List Term) :
    apply program dataEqualityHost fuel head arguments =
      apply Service.program dataEqualityHost fuel head arguments :=
  apply_append_eq Service.program equations dataEqualityHost equations_disjoint
    fuel head used arguments

theorem original_returns (head : String) (used : head ∈ Service.program.calledHeads)
    (arguments : List Term) (result : Term) :
    Applies program dataEqualityHost head arguments result ↔
      Applies Service.program dataEqualityHost head arguments result := by
  unfold Applies
  simp only [original_outcomes _ _ used]

theorem scoped_apply (head : String) (used : head ∈ equations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply program dataEqualityHost fuel head arguments =
      applyWith equations dataEqualityHost (eval program dataEqualityHost fuel) head arguments :=
  apply_suffix_eq Service.program equations dataEqualityHost equations_disjoint
    head used fuel arguments

theorem scoped_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term}
    (used : head ∈ equations.map Equation.head)
    (defined : equations.definesAt head arguments.length = true)
    (selected : equations.select head arguments = some (equation, environment))
    (body : Evaluates program dataEqualityHost environment equation.body result) :
    Applies program dataEqualityHost head arguments result :=
  Applies.suffix_equation equations_disjoint used defined selected body

def arguments (T : Theory) (context : Context) (hypotheses : List Preterm) : List Term :=
  theoryArguments T ++ [encodeContext context, encodeExpressions hypotheses]

def encodeSaved (T : Theory) (saved : List (Preterm × Certificate T)) : Term :=
  .list (saved.map fun entry => .list [encode entry.1, certificateCode T entry.2])

def request (T : Theory) (context : Context) (hypotheses : List Preterm)
    (saved : List (Preterm × Certificate T)) (claim : Preterm)
    (certificate : Certificate T) : List Term :=
  arguments T context hypotheses ++ [encodeSaved T saved, encode claim, certificateCode T certificate]

theorem goal_code (context : Context) (hypotheses : List Preterm) (claim : Preterm) :
    goal (encodeContext context) (encodeExpressions hypotheses) (encode claim) =
      code (derivesJ context hypotheses claim) := by
  simp only [derivesJ, jDerives, contextPattern, expressionsPattern, expressionPattern,
    code, codes, code_termPattern]
  simp [applyCode, goal, applyGeneric]

private theorem certificate_called : "mm0:certificate" ∈ Service.program.calledHeads := by
  decide +kernel

def verdict (T : Theory) (context : Context) (hypotheses : List Preterm)
    (claim : Preterm) (certificate : Certificate T) : Bool :=
  Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves.check formMM0 (settledEvaluate T)
    (derivesJ context hypotheses claim) certificate

private theorem constructors_undefined (head : String)
    (member : head ∈ ["Pattern:Apply", "Pattern:Data", "nik:list-view"]) :
    program.defines head = false := by
  have checked : ["Pattern:Apply", "Pattern:Data", "nik:list-view"].all
      (fun name => !program.defines name) = true := by decide +kernel
  simpa using List.all_eq_true.mp checked head member

private theorem goal_computes (environment : Env) (context hypotheses expression : Term)
    (contextFound : environment.lookup "context" = some context)
    (hypothesesFound : environment.lookup "hypotheses" = some hypotheses)
    (expressionFound : environment.lookup "expression" = some expression) :
    Evaluates program dataEqualityHost environment goalBody (goal context hypotheses expression) := by
  refine Evaluates.call (by simp [Special])
    (.cons (.literal _ _ _ _) (.cons ?_ .nil))
    (.constructor (constructors_undefined _ (by decide)) (by rfl))
  refine Evaluates.list (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable contextFound) .nil)
      (.constructor (constructors_undefined _ (by decide)) (by rfl))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable hypothesesFound) .nil)
      (.constructor (constructors_undefined _ (by decide)) (by rfl))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable expressionFound) .nil)
      (.constructor (constructors_undefined _ (by decide)) (by rfl))

/-- The protocol delegates each proof to the existing checker. -/
theorem certificate_computes (T : Theory) (context : Context) (hypotheses : List Preterm)
    (claim : Preterm) (certificate : Certificate T) :
    Applies program dataEqualityHost "mm0:scoped-certificate"
      (arguments T context hypotheses ++ [encode claim, certificateCode T certificate])
      (boolean (verdict T context hypotheses claim certificate)) := by
  refine scoped_equation (equation := equations[0])
    (environment := [("terms", encodeTable T.terms), ("definitions", encodeDefinitions T.definitions),
      ("theorems", encodeTheorems T.theorems), ("context", encodeContext context),
      ("hypotheses", encodeExpressions hypotheses), ("expression", encode claim),
      ("certificate", certificateCode T certificate)]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := ComputationalCalculus.request T
      (derivesJ context hypotheses claim) certificate) (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) .nil))))) ?_
  · rw [← goal_code]
    exact goal_computes _ _ _ _ (by rfl) (by rfl) (by rfl)
  · exact (original_returns _ certificate_called _ _).mpr
      ((Service.calculus_returns _ (by decide +kernel) _ _).mpr
        (ComputationalCalculus.certificate_computes T _ _))

private theorem append_computes (left right : List Term) :
    Applies program dataEqualityHost "nik:list-append"
      [.list left, .list right] (.list (left ++ right)) := by
  let tail := ComputationalSupport.supportEquations ++ naturalMembershipProgram ++
    ComputationalDependency.dependencyEquations ++ argumentEquations
  have inArguments : Applies argumentProgram computationalHost "nik:list-append"
      [.list left, .list right] (.list (left ++ right)) := by
    have run := (Applies.frame_iff listAppendProgram ComputationalTyping.typingProgram tail
      computationalHost (by decide) (by decide) "nik:list-append" (by decide) _ _).mpr
      (list_append_computes left right)
    simpa only [argumentProgram, ComputationalDependency.dependencyProgram,
      ComputationalSupport.supportProgram, tail, List.append_assoc] using run
  have inConversion := ComputationalConversion.argument_reused "nik:list-append"
    (by decide) _ _ inArguments
  have inProof := (Applies.append_iff ComputationalConversion.conversionProgram proofEquations
    dataEqualityHost proofEquations_disjoint "nik:list-append" (by decide) _ _).mpr inConversion
  have inCalculus := (Applies.append_iff proofProgram calculusEquations dataEqualityHost
    calculusEquations_disjoint "nik:list-append" (by decide) _ _).mpr inProof
  exact (original_returns _ (by decide) _ _).mpr
    ((Service.calculus_returns _ (by decide) _ _).mpr inCalculus)

def checkSaved (T : Theory) (context : Context) :
    List Preterm → List (Preterm × Certificate T) → Bool
  | _, [] => true
  | hypotheses, (claim, certificate) :: rest =>
      verdict T context hypotheses claim certificate &&
        checkSaved T context (hypotheses ++ [claim]) rest

def checkRun (T : Theory) (context : Context) :
    List Preterm → List (Preterm × Certificate T) → Preterm → Certificate T → Bool
  | hypotheses, [], claim, certificate => verdict T context hypotheses claim certificate
  | hypotheses, (claim, certificate) :: rest, root, proof =>
      verdict T context hypotheses claim certificate &&
        checkRun T context (hypotheses ++ [claim]) rest root proof

private theorem run_view (T : Theory) (context : Context) (hypotheses : List Preterm)
    (saved : List (Preterm × Certificate T)) (claim : Preterm) (certificate : Certificate T)
    (result : Term)
    (next : Applies program dataEqualityHost "mm0:scoped-view"
      ([listView (saved.map fun entry => .list [encode entry.1, certificateCode T entry.2])] ++
        arguments T context hypotheses ++ [encode claim, certificateCode T certificate]) result) :
    Applies program dataEqualityHost "mm0:scoped-run"
      (request T context hypotheses saved claim certificate) result := by
  refine scoped_equation (equation := equations[1])
    (environment := [("terms", encodeTable T.terms), ("definitions", encodeDefinitions T.definitions),
      ("theorems", encodeTheorems T.theorems), ("context", encodeContext context),
      ("hypotheses", encodeExpressions hypotheses), ("saved", encodeSaved T saved),
      ("root", encode claim), ("certificate", certificateCode T certificate)])
    (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) .nil)))))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (constructors_undefined _ (by decide)) (by rfl))

private theorem run_nil (T : Theory) (context : Context) (hypotheses : List Preterm)
    (claim : Preterm) (certificate : Certificate T) :
    Applies program dataEqualityHost "mm0:scoped-view"
      ([.sym "List:Nil"] ++ arguments T context hypotheses ++
        [encode claim, certificateCode T certificate])
      (boolean (verdict T context hypotheses claim certificate)) := by
  refine scoped_equation (equation := equations[2])
    (environment := [("terms", encodeTable T.terms), ("definitions", encodeDefinitions T.definitions),
      ("theorems", encodeTheorems T.theorems), ("context", encodeContext context),
      ("hypotheses", encodeExpressions hypotheses), ("root", encode claim),
      ("certificate", certificateCode T certificate)]) (by decide) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) .nil)))))))
    (certificate_computes T context hypotheses claim certificate)

private theorem run_cons (T : Theory) (context : Context) (hypotheses : List Preterm)
    (first : Preterm) (initializer : Certificate T) (saved : List (Preterm × Certificate T))
    (claim : Preterm) (certificate : Certificate T) (result : Term)
    (next : Applies program dataEqualityHost "mm0:scoped-continue"
      ([boolean (verdict T context hypotheses first initializer)] ++
        arguments T context hypotheses ++
        [encode first, encodeSaved T saved, encode claim, certificateCode T certificate]) result) :
    Applies program dataEqualityHost "mm0:scoped-view"
      ([listView ((first, initializer) :: saved |>.map
        fun entry => .list [encode entry.1, certificateCode T entry.2])] ++
        arguments T context hypotheses ++ [encode claim, certificateCode T certificate]) result := by
  refine scoped_equation (equation := equations[3])
    (environment := [("expression", encode first), ("initializer", certificateCode T initializer),
      ("remaining", encodeSaved T saved), ("terms", encodeTable T.terms),
      ("definitions", encodeDefinitions T.definitions), ("theorems", encodeTheorems T.theorems),
      ("context", encodeContext context), ("hypotheses", encodeExpressions hypotheses),
      ("root", encode claim), ("certificate", certificateCode T certificate)])
    (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ ?_) next
  · exact Evaluates.call (by simp [Special]) (by
      repeat' first | apply List.Forall₂.cons | exact List.Forall₂.nil |
        exact Evaluates.variable (by rfl))
      (certificate_computes T context hypotheses first initializer)
  · repeat' first | apply List.Forall₂.cons | exact List.Forall₂.nil |
      exact Evaluates.variable (by rfl)

private theorem continue_false (T : Theory) (context : Context) (hypotheses : List Preterm)
    (first : Preterm) (saved : List (Preterm × Certificate T)) (claim : Preterm)
    (certificate : Certificate T) :
    Applies program dataEqualityHost "mm0:scoped-continue"
      ([.sym "False"] ++ arguments T context hypotheses ++
        [encode first, encodeSaved T saved, encode claim, certificateCode T certificate]) (.sym "False") :=
  ⟨1, by rw [scoped_apply _ (by decide)]; rfl⟩

private theorem continue_true (T : Theory) (context : Context) (hypotheses : List Preterm)
    (first : Preterm) (saved : List (Preterm × Certificate T)) (claim : Preterm)
    (certificate : Certificate T) (result : Term)
    (next : Applies program dataEqualityHost "mm0:scoped-run"
      (request T context (hypotheses ++ [first]) saved claim certificate) result) :
    Applies program dataEqualityHost "mm0:scoped-continue"
      ([.sym "True"] ++ arguments T context hypotheses ++
        [encode first, encodeSaved T saved, encode claim, certificateCode T certificate]) result := by
  refine scoped_equation (equation := equations[5])
    (environment := [("terms", encodeTable T.terms), ("definitions", encodeDefinitions T.definitions),
      ("theorems", encodeTheorems T.theorems), ("context", encodeContext context),
      ("hypotheses", encodeExpressions hypotheses), ("expression", encode first),
      ("remaining", encodeSaved T saved), ("root", encode claim),
      ("certificate", certificateCode T certificate)]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons ?_ ?_))))) next
  · refine Evaluates.call (values := [encodeExpressions hypotheses, .list [encode first]])
      (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (Evaluates.list (.cons (.variable (by rfl)) .nil)) .nil)) ?_
    simpa only [encodeExpressions, List.map_append, List.map_cons, List.map_nil] using
      append_computes (hypotheses.map encode) [encode first]
  · repeat' first | apply List.Forall₂.cons | exact List.Forall₂.nil |
      exact Evaluates.variable (by rfl)

/-- Every finite submitted store finishes, retaining initializer order and scope. -/
theorem run_computes (T : Theory) (context : Context) (hypotheses : List Preterm)
    (saved : List (Preterm × Certificate T)) (claim : Preterm) (certificate : Certificate T) :
    Applies program dataEqualityHost "mm0:scoped-run"
      (request T context hypotheses saved claim certificate)
      (boolean (checkRun T context hypotheses saved claim certificate)) := by
  induction saved generalizing hypotheses with
  | nil =>
    exact run_view T context hypotheses [] claim certificate _
      (run_nil T context hypotheses claim certificate)
  | cons entry rest ih =>
      obtain ⟨first, initializer⟩ := entry
      apply run_view T context hypotheses ((first, initializer) :: rest) claim certificate
      apply run_cons T context hypotheses first initializer rest claim certificate
      cases checked : verdict T context hypotheses first initializer with
      | false => simpa [checkRun, checked, boolean] using
          continue_false T context hypotheses first rest claim certificate
      | true => simpa [checkRun, checked, boolean] using
          continue_true T context hypotheses first rest claim certificate _ (ih (hypotheses ++ [first]))

theorem run_result_exact (T : Theory) (context : Context) (hypotheses : List Preterm)
    (saved : List (Preterm × Certificate T)) (claim : Preterm) (certificate : Certificate T)
    (result : Term) :
    Applies program dataEqualityHost "mm0:scoped-run"
      (request T context hypotheses saved claim certificate) result ↔
      result = boolean (checkRun T context hypotheses saved claim certificate) :=
  ⟨fun computed => computed.deterministic (run_computes T context hypotheses saved claim certificate),
    fun same => same ▸ run_computes T context hypotheses saved claim certificate⟩

end Mettapedia.Languages.MM0.Presentation.ScopedService
