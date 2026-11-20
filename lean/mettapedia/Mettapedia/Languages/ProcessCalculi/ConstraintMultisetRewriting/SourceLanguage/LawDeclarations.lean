import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Laws

/-!
# A surface program is a bag of declarations and equations

* **Unambiguous declarations** (`Unambiguous`): two declarations of one head are the same
  declaration. Consistency (`DeclarationsConsistent`) asks only that they agree on which positions
  hold; the elaboration reads the first declaration of a head, so its value types must agree too.
* **The order of declarations is unobservable** (`declOf_perm`, `elaborate_perm_decls`): permuting
  unambiguous declarations changes neither the elaborated program nor any elaborated query.
* **The order of equations is unobservable** (`elaborate_perm_equations`): permuting the surface
  equations permutes the elaborated ones and keeps the reading of text, so the runs are the same
  (`Laws.runs_perm`).
* **The control** (`overloaded_order`): two consistent declarations of one head with different value
  types elaborate the same call with different checks in the two orders. Such an overloaded head is
  consistent and not unambiguous; its elaboration would have to consult every declaration of the head.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.LawDeclarations

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration

/-- **Unambiguous declarations**: two declarations of one head are the same declaration. -/
def Unambiguous (decls : List Decl) : Prop :=
  ∀ d ∈ decls, ∀ d' ∈ decls, d.head = d'.head → d = d'

instance (decls : List Decl) : Decidable (Unambiguous decls) := by
  unfold Unambiguous; infer_instance

/-- **The declaration of a head does not depend on the order of unambiguous declarations.** -/
theorem declOf_perm {decls decls' : List Decl} (perm : decls.Perm decls') (unambiguous : Unambiguous decls)
    (f : String) : declOf decls f = declOf decls' f := by
  unfold declOf
  cases found : decls.find? (fun d => d.head == f) with
  | none =>
      have none' : decls'.find? (fun d => d.head == f) = none := by
        rw [List.find?_eq_none] at found ⊢
        intro d member
        exact found d (perm.symm.subset member)
      rw [none']
  | some d =>
      have dIn := List.mem_of_find?_eq_some found
      have dHead := List.find?_some found
      cases found' : decls'.find? (fun d => d.head == f) with
      | none =>
          rw [List.find?_eq_none] at found'
          exact absurd dHead (found' d (perm.subset dIn))
      | some d' =>
          have d'In := perm.symm.subset (List.mem_of_find?_eq_some found')
          have d'Head := List.find?_some found'
          simp only [beq_iff_eq] at dHead d'Head
          rw [unambiguous d dIn d' d'In (dHead.trans d'Head.symm)]

/-! ## The elaboration reads declarations only through `declOf` -/

section
variable (π : Params) {decls decls' : List Decl} (same : ∀ f, declOf decls f = declOf decls' f)
include same

theorem passOf_congr (f : String) (i : ℕ) (a : View) : passOf π decls f i a = passOf π decls' f i a := by
  unfold passOf
  rw [same f]

theorem finish_congr (f : String) (args : List MData) : finish decls f args = finish decls' f args := by
  unfold finish
  rw [same f]
end

mutual
theorem elabText_congr (π : Params) {decls decls' : List Decl} (same : ∀ f, declOf decls f = declOf decls' f)
    (modes : Name mkeys → VarMode) (path : List ℕ) : (v : View) →
      elabText π decls modes path v = elabText π decls' modes path v
  | .holdMark _ _ => rfl
  | .runMark _ inner => by
      cases inner with
      | var o x => rfl
      | holdMark o u => exact elabText_congr π same modes path (.holdMark o u)
      | runMark o i => exact elabText_congr π same modes path (.runMark o i)
      | symbol o g => exact elabText_congr π same modes path (.symbol o g)
      | call o g args => exact elabText_congr π same modes path (.call o g args)
      | inert o => exact elabText_congr π same modes path (.inert o)
      | other o => exact elabText_congr π same modes path (.other o)
  | .var _ _ => rfl
  | .symbol _ _ => rfl
  | .call _ f args => elabArgs_congr π same modes path f 0 args []
  | .inert _ => rfl
  | .other _ => rfl

theorem elabArgs_congr (π : Params) {decls decls' : List Decl} (same : ∀ f, declOf decls f = declOf decls' f)
    (modes : Name mkeys → VarMode) (path : List ℕ) (f : String) (i : ℕ) :
    (args : List View) → (done : List MData) →
      elabArgs π decls modes path f i args done = elabArgs π decls' modes path f i args done
  | [], done => finish_congr same f done.reverse
  | a :: rest, done => by
      simp only [elabArgs]
      rw [passOf_congr π same f i a]
      generalize passOf π decls' f i a = p
      cases p with
      | text u => exact elabArgs_congr π same modes path f (i + 1) rest (u :: done)
      | byName => exact elabArgs_congr π same modes path f (i + 1) rest (a.orig :: done)
      | evaluate check =>
          cases check with
          | none =>
              rw [elabText_congr π same modes (path ++ [i]) a,
                elabArgs_congr π same modes path f (i + 1) rest (slot (path ++ [i]) :: done)]
          | some T =>
              rw [elabText_congr π same modes (path ++ [i]) a,
                elabArgs_congr π same modes path f (i + 1) rest (slot (path ++ [i]) :: done)]
      | byNeed =>
          rw [elabText_congr π same modes (path ++ [i]) a,
            elabArgs_congr π same modes path f (i + 1) rest (slot (path ++ [i]) :: done)]
end

section
variable (π : Params) {decls decls' : List Decl} (same : ∀ f, declOf decls f = declOf decls' f)
include same

theorem elabComp_congr (modes : Name mkeys → VarMode) (path : List ℕ) (c : SComp) :
    elabComp π decls modes path c = elabComp π decls' modes path c := by
  induction c generalizing path with
  | text t => exact elabText_congr π same modes path (view t)
  | let_ s p c k ihc ihk => simp only [elabComp, ihc, ihk]
  | choice c d ihc ihd => simp only [elabComp, ihc, ihd]
  | fail => rfl
  | query sp p k ih => simp only [elabComp, ih]
  | add sp t k ih => simp only [elabComp, ih]
  | remove sp t k ih => simp only [elabComp, ih]
  | new s x k ih => simp only [elabComp, ih]

theorem paramModes_congr (e : SEquation) : paramModes π decls e = paramModes π decls' e := by
  funext x
  unfold paramModes paramMode
  simp only [passOf_congr π same]

theorem elabBody_congr (e : SEquation) : elabBody π decls e = elabBody π decls' e := by
  unfold elabBody
  rw [paramModes_congr π same e, same e.head]
  simp only [elabText_congr π same, elabComp_congr π same]

theorem elabEquation_congr (e : SEquation) : elabEquation π decls e = elabEquation π decls' e := by
  unfold elabEquation
  rw [elabBody_congr π same e]
end

/-! ## Permutations -/

/-- **Permuting unambiguous declarations changes no elaborated program and no elaborated query.** -/
theorem elaborate_perm_decls (π : Params) {P P' : SProgram} (perm : P.decls.Perm P'.decls)
    (unambiguous : Unambiguous P.decls) (equations : P.equations = P'.equations) :
    elaborate π P = elaborate π P' ∧ ∀ q, elabQuery π P q = elabQuery π P' q := by
  have same := declOf_perm perm unambiguous
  refine ⟨?_, fun q => elabComp_congr π same _ _ q⟩
  unfold elaborate
  rw [← equations]
  congr 1
  · exact List.map_congr_left fun e _ => elabEquation_congr π same e
  · funext t
    exact elabText_congr π same _ _ _

/-- **Permuting surface equations permutes the elaborated equations** and keeps the reading of text;
so the runs of the two elaborated programs are the same (`Laws.runs_perm`). -/
theorem elaborate_perm_equations (π : Params) {P P' : SProgram} (decls : P.decls = P'.decls)
    (perm : P.equations.Perm P'.equations) :
    (elaborate π P).equations.Perm (elaborate π P').equations ∧ (elaborate π P).reflect = (elaborate π P').reflect := by
  refine ⟨?_, ?_⟩
  · simp only [elaborate, decls]
    exact perm.map _
  · simp only [elaborate, decls]

/-! ## The control: an overloaded head -/

/-- Two declarations of `f`, consistent (neither position holds) with different value types. -/
def overloaded : List Decl := [⟨"f", [.value "Number"], .undefined⟩, ⟨"f", [.value "Bool"], .undefined⟩]

theorem overloaded_consistent : DeclarationsConsistent overloaded := by decide

theorem overloaded_ambiguous : ¬ Unambiguous overloaded := by decide

theorem single_unambiguous : Unambiguous [⟨"f", [.value "Number"], .undefined⟩] := by decide

/-- The reading by value, with held text staying. -/
def byValue : Params := ⟨fun _ _ => .value, false, false⟩

def callF : MData := tuple [sym "f", num 1]

/-- The type checked at the first argument of an elaborated call, if any. -/
def firstCheck : Comp mkeys [] () MTy → Option MTy
  | .let_ _ _ (.check T _) _ => some T
  | _ => none

/-- **The order of overloaded declarations is observable** in the elaboration: `(f 1)` is checked at
`Number` under one order and at `Bool` under the other. -/
theorem overloaded_order :
    elabQuery byValue ⟨overloaded, []⟩ (.text callF) ≠ elabQuery byValue ⟨overloaded.reverse, []⟩ (.text callF) := by
  intro same
  have one : firstCheck (elabQuery byValue ⟨overloaded, []⟩ (.text callF)) = some (.value "Number") := rfl
  have two : firstCheck (elabQuery byValue ⟨overloaded.reverse, []⟩ (.text callF)) = some (.value "Bool") := rfl
  rw [same, two] at one
  simp at one

#print axioms declOf_perm
#print axioms elaborate_perm_decls
#print axioms elaborate_perm_equations
#print axioms overloaded_consistent
#print axioms overloaded_ambiguous
#print axioms overloaded_order

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.LawDeclarations
