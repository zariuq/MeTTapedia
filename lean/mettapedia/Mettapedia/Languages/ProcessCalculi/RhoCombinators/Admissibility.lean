/-
# When does a presentation admit a name-free combinator target?

The lane's deliverable is a condition on a presentation, not on this one
calculus. This file states it in the presentation language the tree already
has — `LanguageDef` plus a `ReflectivePresentationDecl`, which declares the
process sort, the name sort, the quote and drop constructors, and the quote/drop
equation by name — and checks it against the authored rho presentation.

Three questions, three answers.

**Which constructors must be reflected?** The constructors of the process sort,
since those are the shapes a name can quote. `reflectedShapes`.

**Which node shapes require a code constructor?** Each of them, one apiece,
reading one name per parameter and writing one: `codeConstructorFamily`, whose
length is the number of reflected shapes and no more. The family is indexed by
the presentation's own constructors rather than supplied alongside them.

**When is the encoding linear rather than expanding?** When every reflected
shape is *positionally assemblable* — no parameter binds, and no parameter is
collection-valued. Then a context's cost is the sum of its nodes' arities plus
one, and `atomCount_assemble_eq_sum_arities` proves that prediction is exactly
what the verified compiler emits.

## The census is the interesting part

Rho as authored **fails** the condition, and for two different reasons:

```
    PZero    Proc   []                  assemblable
    PDrop    Proc   [simple]            assemblable
    PPar     Proc   [collection]        NO — variadic
    POutput  Proc   [simple, simple]    assemblable
    PInput   Proc   [simple, binder]    NO — binds
```

A collection-valued parameter has no fixed arity, so no fixed-arity code
constructor can assemble it. A binding parameter is not a name, so a code
constructor cannot receive it as one.

Those two failures are exactly the two places the combinator calculus departs
from the authored presentation: its parallel composition is **binary** rather
than a bag, and its input is replaced by **routers** rather than a binder. So
the condition is not a formality that rho happens to satisfy — it is the
condition whose failure explains the target's design.

## The negative condition

One further condition is necessary and is not about the source. The
presentation declares its quote/drop equation by name, and rho declares exactly
one equation, `QuoteDrop`. That equation is correct for rho, where drop is a
process former. Carried into a presentation where the drop has become a guard on
a communication rule it collapses the calculus — which is `defect`, proved
axiom-free in `Basic.lean`. So a target must exclude it, and the check is at the
level of a declared name rather than a semantic search.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.CollapsedConstructor
import Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The conditions, on a presentation -/

/-- A type is variadic when it mentions a collection: a parameter of that type
has no fixed number of children. -/
def variadicType : TypeExpr → Bool
  | .base _ => false
  | .arrow domain codomain => variadicType domain || variadicType codomain
  | .multiBinder body => variadicType body
  | .collection _ _ => true

/-- A parameter is a single assemblable name position when it neither binds nor
varies in arity.  A binder is not a name, so a code constructor cannot receive
it as one; a collection has no fixed arity, so no fixed-arity code constructor
can assemble it. -/
def assemblableParam : TermParam → Bool
  | .simple _ ty => !variadicType ty
  | .abstractionNamed _ _ _ => false
  | .multiAbstractionNamed _ _ _ => false

/-- A shape is positionally assemblable when all of its parameters are. -/
def positionallyAssemblable (rule : GrammarRule) : Bool :=
  rule.params.all assemblableParam

/-- The shapes a name can quote: the constructors of the process sort. -/
def reflectedShapes (processSort : String) (lang : LanguageDef) : List GrammarRule :=
  lang.terms.filter fun rule => rule.category == processSort

/-- The code constructor a shape requires: it reads one name per parameter and
writes one. -/
def codeConstructorArity (rule : GrammarRule) : ℕ := rule.params.length + 1

/-- The code-constructor family a presentation requires: one per reflected
shape, indexed by the presentation's own constructors. -/
def codeConstructorFamily (processSort : String) (lang : LanguageDef) :
    List (String × ℕ) :=
  (reflectedShapes processSort lang).map fun rule => (rule.label, codeConstructorArity rule)

/-- One code constructor per reflected shape, no more and no fewer. -/
theorem codeConstructorFamily_length (processSort : String) (lang : LanguageDef) :
    (codeConstructorFamily processSort lang).length =
      (reflectedShapes processSort lang).length :=
  List.length_map _

/-- The cost of compiling a one-hole context whose nodes are the given shapes:
one atom per parameter of each node, plus the forwarder at the hole. -/
def contextCost (nodes : List GrammarRule) : ℕ :=
  (nodes.map fun rule => rule.params.length).sum + 1

/-! ## The rules, not only the terms

A first pass at this condition looked only at term constructors.  That is not
enough, and MeTTa is the counterexample: its term signature has no binding and
no variadic parameter at all, because its binding lives in the *patterns* of its
rewrite rules.  A condition that reads only `lang.terms` would therefore report
a presentation as assemblable while the obstruction sat in `lang.rewrites`.  So
the rules carry their own clause.

Two obstructions again, and the same two.  A pattern binder is a source-level
binder the term signature does not show.  An open collection tail is a variadic
position: the rest variable stands for any number of elements, so no fixed-arity
code constructor can assemble the pattern it sits in.
-/

mutual

/-- Whether a pattern binds anywhere. -/
def patternBinds : Pattern → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .apply _ arguments => patternBindsList arguments
  | .lambda _ _ => true
  | .multiLambda _ _ _ => true
  | .subst target replacement => patternBinds target || patternBinds replacement
  | .collection _ elements _ => patternBindsList elements

def patternBindsList : List Pattern → Bool
  | [] => false
  | pattern :: rest => patternBinds pattern || patternBindsList rest

end

mutual

/-- Whether a pattern has a variadic position: an open collection tail. -/
def patternVariadic : Pattern → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .apply _ arguments => patternVariadicList arguments
  | .lambda _ body => patternVariadic body
  | .multiLambda _ _ body => patternVariadic body
  | .subst target replacement =>
      patternVariadic target || patternVariadic replacement
  | .collection _ elements rest => rest.isSome || patternVariadicList elements

def patternVariadicList : List Pattern → Bool
  | [] => false
  | pattern :: rest => patternVariadic pattern || patternVariadicList rest

end

/-- A rule is assemblable when neither side binds and neither side is
variadic. -/
def ruleAssemblable (rule : RewriteRule) : Bool :=
  !patternBinds rule.left && !patternBinds rule.right &&
    !patternVariadic rule.left && !patternVariadic rule.right

/-- **The condition.**  Every shape a name can quote is positionally
assemblable, and every rule is assemblable, so one fixed-arity code constructor
per shape suffices and the compiled cost is the sum of the arities plus one. -/
structure AdmitsNameFreeTarget (presentation : ReflectivePresentationDecl)
    (lang : LanguageDef) : Prop where
  shapesAssemblable :
    (reflectedShapes presentation.processSort lang).all positionallyAssemblable = true
  rulesAssemblable : lang.rewrites.all ruleAssemblable = true

/-! ## The census of the authored rho presentation -/

theorem rhoCalc_reflectedShapes_labels :
    (reflectedShapes "Proc" rhoCalc).map GrammarRule.label
      = ["PZero", "PDrop", "PPar", "POutput", "PInput"] := by decide

/-- **The census.**  Three of rho's five process constructors are positionally
assemblable; two are not, for two different reasons. -/
theorem rhoCalc_assemblable_census :
    (reflectedShapes "Proc" rhoCalc).map
        (fun rule => (rule.label, positionallyAssemblable rule))
      = [("PZero", true), ("PDrop", true), ("PPar", false),
         ("POutput", true), ("PInput", false)] := by decide

/-- The code-constructor family rho would require, by arity. -/
theorem rhoCalc_codeConstructorFamily :
    codeConstructorFamily "Proc" rhoCalc
      = [("PZero", 1), ("PDrop", 2), ("PPar", 2), ("POutput", 3), ("PInput", 3)] := by
  decide

/-- **Rho as authored does not admit a name-free target.**  The obstruction is
not incidental: it is `PPar`'s bag-valued parameter and `PInput`'s binder, and
those are precisely the two constructors the combinator calculus re-presents. -/
theorem rhoCalc_not_admits :
    ¬ AdmitsNameFreeTarget
      rhoReflectivePresentation.toReflectivePresentationDecl rhoCalc := by
  intro h
  have failed := h.shapesAssemblable
  revert failed
  decide

/-- **Rho's rules fail too, and at both obstructions.**  `Comm` binds (its input
prefix) and is variadic (the parallel bag); `ParCong` is variadic.  So rho fails
the condition at the term level and at the rule level independently. -/
theorem rhoCalc_rules_census :
    rhoCalc.rewrites.map
        (fun rule => (rule.name, patternBinds rule.left || patternBinds rule.right,
          patternVariadic rule.left || patternVariadic rule.right))
      = [("Comm", true, true), ("ParCong", false, true)] := by decide

/-- Rho declares exactly one equation, and it is the quote/drop identification
the presentation names.  `defect` is the proof that carrying it into a
guard-style target collapses the calculus, so a target must exclude it. -/
theorem rhoCalc_equations_are_quoteDrop :
    rhoCalc.equations.map Equation.name
      = [rhoReflectivePresentation.toReflectivePresentationDecl.quoteDropEquation] := by
  decide

/-! ## The repair, and the cost bridge

The combinator calculus answers both census failures: its parallel composition
is binary rather than a bag, and its input is replaced by routers rather than a
binder.  So every node shape of its one-hole contexts has a fixed arity, and the
cost prediction is exact.
-/

/-- The arities of the nodes of a one-hole context. -/
def NameContext.arities : NameContext → List ℕ
  | .hole => []
  | .parLeft ctx _ => 2 :: ctx.arities
  | .parRight _ ctx => 2 :: ctx.arities
  | .msgLeft ctx _ => 2 :: ctx.arities
  | .msgRight _ ctx => 2 :: ctx.arities
  | .ddSubject ctx _ _ => 3 :: ctx.arities
  | .ddFirst _ ctx _ => 3 :: ctx.arities
  | .ddSecond _ _ ctx => 3 :: ctx.arities
  | .sySubject ctx _ _ => 3 :: ctx.arities
  | .syFirst _ ctx _ => 3 :: ctx.arities
  | .sySecond _ _ ctx => 3 :: ctx.arities

theorem NameContext.weight_eq_sum_arities :
    ∀ ctx : NameContext, ctx.weight = ctx.arities.sum
  | .hole => rfl
  | .parLeft ctx _ | .parRight _ ctx | .msgLeft ctx _ | .msgRight _ ctx => by
      have ih := NameContext.weight_eq_sum_arities ctx
      simp only [NameContext.weight, NameContext.arities, List.sum_cons] at ih ⊢
      omega
  | .ddSubject ctx _ _ | .ddFirst _ ctx _ | .ddSecond _ _ ctx
  | .sySubject ctx _ _ | .syFirst _ ctx _ | .sySecond _ _ ctx => by
      have ih := NameContext.weight_eq_sum_arities ctx
      simp only [NameContext.weight, NameContext.arities, List.sum_cons] at ih ⊢
      omega

/-- **Every node shape of the target has a fixed arity.**  This is the repair
for `PPar`'s variadicity: a bag parameter is replaced by a binary composition,
so nothing in a compiled context has unbounded arity. -/
theorem NameContext.arities_fixed :
    ∀ (ctx : NameContext), ∀ a ∈ ctx.arities, a = 2 ∨ a = 3
  | .hole, _, h => by simp [NameContext.arities] at h
  | .parLeft ctx _, a, h | .parRight _ ctx, a, h
  | .msgLeft ctx _, a, h | .msgRight _ ctx, a, h => by
      simp only [NameContext.arities, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact NameContext.arities_fixed ctx a h
  | .ddSubject ctx _ _, a, h | .ddFirst _ ctx _, a, h | .ddSecond _ _ ctx, a, h
  | .sySubject ctx _ _, a, h | .syFirst _ ctx _, a, h
  | .sySecond _ _ ctx, a, h => by
      simp only [NameContext.arities, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr rfl
      · exact NameContext.arities_fixed ctx a h

/-- **The cost prediction is the compiler's actual output.**  Summing the
arities of a context's nodes and adding one — the presentation-level formula
`contextCost` computes from declared parameter counts — is exactly the atom
count the verified compiler emits.  So "linear in the source" is a checked
statement about a compiler, not an estimate. -/
theorem atomCount_assemble_eq_sum_arities (s : Comb) (ctx : NameContext)
    (inName outName : Comb) (d : ℕ) :
    atomCount (assemble s ctx inName outName d) = ctx.arities.sum + 1 := by
  rw [atomCount_assemble, NameContext.weight_eq_sum_arities]

/-- The same, packaged with the two other guarantees the compiler carries. -/
theorem target_realizes_prediction (s : Comb) (ctx : NameContext)
    (outName v : Comb) :
    atomCount (assemble s ctx s outName 0) = ctx.arities.sum + 1
      ∧ ReachesFull (par (assemble s ctx s outName 0) (mm s v))
          (mm outName (ctx.fill v))
      ∧ Linear (assemble s ctx s outName 0) :=
  ⟨atomCount_assemble_eq_sum_arities s ctx s outName 0,
    assemble_reaches s ctx s outName 0 v,
    assemble_linear s ctx outName⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
