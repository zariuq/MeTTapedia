import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingContracts

/-!
# Controls: entry evidence and the return view

The runtime typing draft: if `old` and `new` both have type `A`, a call `(keep old)` under
`(: keep (-> $a $a))` may remove `(: old A)` and return `new`. The input's evidence is read at entry,
the result at return. In the typed-call firing the entry view `Γ₀` and the return view `Γ₁` are
separate (`Joint_d`).

* `keep_admitted_across_edit`: the call is admitted with the entry view declaring `old` and `new`,
  and the return view declaring only `new`.
* `keep_refused_if_rechecked`: checking the input again in the return view refuses it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingContractsViews

open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Logic.ConstraintTypes renaming Tree → VTree
open Mettapedia.Logic.ConstraintTypes.SymbolicTypes (Expr Closed)
open TypingFirings

inductive Sym where
  | old
  | new
  deriving DecidableEq

def valueArity : Sym → Nat := fun _ => 0

inductive Name where
  | a
  deriving DecidableEq

def typeArity : Empty → Nat := fun e => e.elim

abbrev Ty := Closed Name Empty typeArity
abbrev Value := VTree Sym valueArity

def leaf (s : Sym) : Value := .node s Fin.elim0

/-- `(: s A)`. -/
def declared (s : Sym) : DeclarationTyping.Fact Unit Empty Name Empty Sym typeArity valueArity where
  pattern := .node s Fin.elim0
  type := .closed .a

/-- The view `true` declares `old` and `new`; the view `false`, after the edit, only `new`. -/
def decls : DeclarationTyping.Declarations Bool Unit Empty Name Empty Sym typeArity valueArity where
  childContext Γ _ _ := Γ
  constructors _ _ := []
  facts Γ := if Γ then [declared .old, declared .new] else [declared .new]

theorem declared_typed (Γ : Bool) (s : Sym) (present : declared s ∈ decls.facts Γ) :
    DeclarationTyping.HasType decls Γ (leaf s) (.closed .a) :=
  .nominal (declared s) present (fun _ => leaf s)
    (congrArg (Mettapedia.Logic.ConstraintTypes.Tree.node s) (funext fun i => i.elim0))
    Empty.elim (fun _ member => by cases member)

theorem old_untyped_after (τ : Ty) : ¬ DeclarationTyping.HasType decls false (leaf .old) τ := by
  intro typed
  rcases (DeclarationTyping.hasType_node_iff decls false .old Fin.elim0 τ).1 typed with
    ⟨rule, present, _⟩ | ⟨fact, present, matched, equal, _⟩
  · cases present
  · have same : fact = declared .new := List.mem_singleton.mp present
    subst same
    have names := (Mettapedia.Logic.ConstraintTypes.Tree.node.inj equal).1
    cases names

def nothing (_ : Name) : Prop := False

abbrev T := Term Bool Nat Nat Name Empty Sym typeArity valueArity

def label : Nat → T := fun _ => .yes

def start : Configuration T Nat := ⟨[], ∅⟩

def seed : Point Nat Nat Name Empty Sym typeArity valueArity nothing :=
  ⟨fun _ => leaf .new, fun _ => .closed .a, fun _ _ _ impossible => impossible⟩

def ν : Unit → Nat := fun _ => 0

theorem ν_injective : Function.Injective ν := fun _ _ _ => rfl

/-- `(: keep (-> $a $a))`. -/
def keep : Signature Unit Name Empty typeArity 1 := ⟨fun _ => .parameter (), .parameter ()⟩

def keepCall (Γ₀ Γ₁ : Bool) :
    AnnotatedRuns.Firing T (Instantiation Nat Nat Name Empty Sym typeArity valueArity nothing) Nat :=
  callFiring ν keep Γ₀ Γ₁ (fun _ => ofTree (leaf .old)) (ofTree (leaf .new))

/-- **Entry evidence survives the edit**: `(keep old)` returning `new` is admitted with `old`'s
membership read at entry and `new`'s at return. -/
theorem keep_admitted_across_edit :
    (AnnotatedRuns.firstOrder (action decls nothing) label).Admits (s := start) (keepCall true false) := by
  rw [keepCall, closed_call_admits_iff label start ⟨seed, fun _ member => by cases member⟩ ν_injective
    (avoids_nil ν)]
  exact ⟨fun _ => .closed .a, fun _ _ _ impossible => impossible,
    fun _ => declared_typed true .old (by simp [decls]), declared_typed false .new (by simp [decls])⟩

/-- **Checking the input again at return refuses it**: after the edit, `old` has no type. -/
theorem keep_refused_if_rechecked :
    ¬ (AnnotatedRuns.firstOrder (action decls nothing) label).Admits (s := start) (keepCall false false) := by
  rw [keepCall, closed_call_admits_iff label start ⟨seed, fun _ member => by cases member⟩ ν_injective
    (avoids_nil ν)]
  rintro ⟨θ, _, inputs, _⟩
  exact old_untyped_after _ (inputs 0)

#print axioms keep_admitted_across_edit
#print axioms keep_refused_if_rechecked

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingContractsViews
