import Mettapedia.Languages.HOLLight.CachedSourceDefinitionTable
import Mettapedia.Logic.HOL.ContextualConversionFree

/-!
# Bounded closure of checked defining equations

Each unfolding layer composes the selected row equation with the retained
expansion of its body. The finite bound controls only table unfolding.
Completion means that no authored table key remains; it does not mean beta
normality or normalization for a larger source language. Exhausted results
retain their actual term and equality evidence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.CachedSourceDefinitionClosure

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open CachedSourceDefinitionTable CachedSourceExpansion

def containsKey (bindings : List Binding) (key : Key) : Bool :=
  bindings.any (fun binding => sameKey binding.key key)

def imagesReplacement {assumptions : List Formula}
    (images : (key : Key) → Image assumptions key)
    {type : HOL.Ty AtomicTy} (symbol : Symbol type) : HOL.ClosedTerm Symbol type :=
  (images ⟨type, symbol⟩).body

def imagesEquations {assumptions : List Formula} (images : (key : Key) → Image assumptions key)
    {type : HOL.Ty AtomicTy} (symbol : Symbol type) (body : HOL.ClosedTerm Symbol type)
    (present : some (imagesReplacement images symbol) = some body) :
    HOL.ProofSyntax Symbol assumptions (.eq (.const symbol) body) :=
  HOL.ProofSyntax.castIndices rfl (congrArg (HOL.Term.eq (.const symbol)) (Option.some.inj present))
    (images ⟨type, symbol⟩).proof

theorem imagesEquations_free {assumptions : List Formula} (images : (key : Key) → Image assumptions key)
    {type : HOL.Ty AtomicTy} (symbol : Symbol type) (body : HOL.ClosedTerm Symbol type)
    (present : some (imagesReplacement images symbol) = some body) :
    (imagesEquations images symbol body present).FunctionExtensionalityFree := by
  unfold imagesEquations
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (images ⟨type, symbol⟩).free

def closedExpansion {assumptions : List Formula} (images : (key : Key) → Image assumptions key)
    {type : HOL.Ty AtomicTy} (term : HOL.ClosedTerm Symbol type) :
    HOL.ProofSyntax Symbol assumptions (.eq term (HOL.substConst (imagesReplacement images) term)) :=
  HOL.ProofSyntax.castIndices (by change assumptions.map id = assumptions; simp) rfl
    (HOL.ConstantExpansionProofs.expand assumptions
      (fun symbol => some (imagesReplacement images symbol)) (imagesEquations images)
      term (HOL.substConst?_some (imagesReplacement images) term))

theorem closedExpansion_free {assumptions : List Formula} (images : (key : Key) → Image assumptions key)
    {type : HOL.Ty AtomicTy} (term : HOL.ClosedTerm Symbol type) :
    (closedExpansion images term).FunctionExtensionalityFree := by
  unfold closedExpansion
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact HOL.ConstantExpansionProofs.expand_free assumptions
    (fun symbol => some (imagesReplacement images symbol)) (imagesEquations images)
    (imagesEquations_free images) term (HOL.substConst?_some (imagesReplacement images) term)

def image (bindings : List Binding) : (depth : Nat) → (key : Key) → Image (theory bindings) key
  | 0, key => .literal _ key
  | depth + 1, key =>
      if containsKey bindings key then
        let first := CachedSourceDefinitionTable.image bindings key
        let further := image bindings depth
        ⟨HOL.substConst (imagesReplacement further) first.body,
          .eqTrans first.proof (closedExpansion further first.body),
          ⟨first.free, closedExpansion_free further first.body⟩⟩
      else .literal _ key

def applyTerm (bindings : List Binding) (depth : Nat) {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ type) : HOL.Term Symbol Γ type :=
  HOL.substConst (imagesReplacement (image bindings depth)) term

theorem applyTerm_zero (bindings : List Binding) {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ type) : applyTerm bindings 0 term = term := by
  induction term <;> simp_all [applyTerm, image, imagesReplacement, Image.literal, HOL.substConst]

theorem image_succ_body (bindings : List Binding) (depth : Nat) (key : Key)
    (present : containsKey bindings key = true) :
    (image bindings (depth + 1) key).body =
      HOL.substConst (imagesReplacement (image bindings depth))
        (CachedSourceDefinitionTable.image bindings key).body := by
  simp only [image, present, ↓reduceIte]

def task (bindings : List Binding) (depth : Nat) (source : Formula) : Task where
  source := source
  target := applyTerm bindings depth source
  theory := theory bindings
  replacements := fun symbol => some (imagesReplacement (image bindings depth) symbol)
  equations := imagesEquations (image bindings depth)
  equationsFree := imagesEquations_free (image bindings depth)
  expanded := HOL.substConst?_some (imagesReplacement (image bindings depth)) source

def mentions (bindings : List Binding) : {Γ : HOL.Ctx AtomicTy} → {type : HOL.Ty AtomicTy} →
    HOL.Term Symbol Γ type → Bool
  | _, _, .var _ | _, _, .top | _, _, .bot => false
  | _, _, .const symbol => containsKey bindings ⟨_, symbol⟩
  | _, _, .app first second | _, _, .and first second | _, _, .or first second
  | _, _, .imp first second | _, _, .eq first second => mentions bindings first || mentions bindings second
  | _, _, .lam body | _, _, .not body | _, _, .all body | _, _, .ex body => mentions bindings body

inductive Completion where
  | tableClosed
  | depthExhausted
  deriving DecidableEq, Repr

def completion (bindings : List Binding) (depth : Nat) {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (source : HOL.Term Symbol Γ type) : Completion :=
  if mentions bindings (applyTerm bindings depth source) then .depthExhausted else .tableClosed

theorem tableClosed_iff (bindings : List Binding) (depth : Nat)
    {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy} (source : HOL.Term Symbol Γ type) :
    completion bindings depth source = .tableClosed ↔
      mentions bindings (applyTerm bindings depth source) = false := by
  cases present : mentions bindings (applyTerm bindings depth source) <;>
    simp [completion, present]

namespace Controls

def symbol (name : String) : Symbol (.prop : HOL.Ty AtomicTy) :=
  .constant (.mk (.global name) .undefined) Ty.bool Ty.toHOL_bool

def first : Key := ⟨.prop, symbol "__closure_first"⟩
def second : Key := ⟨.prop, symbol "__closure_second"⟩
def terminal : HOL.ClosedTerm Symbol .prop := .eq (.lam (.var (.vz : HOL.Var [.prop] .prop))) (.lam (.var .vz))

def chain : List Binding := [⟨first, .const second.2⟩, ⟨second, terminal⟩]
def cycle : List Binding := [⟨first, .const first.2⟩]
def input : Formula := .const first.2

theorem chain_one_incomplete : completion chain 1 input = .depthExhausted := by decide +kernel
theorem chain_two_complete : completion chain 2 input = .tableClosed := by decide +kernel
theorem chain_two_result : applyTerm chain 2 input = terminal := by
  have distinct : first ≠ second := by
    intro same
    have accepted := (sameKey_iff first second).mpr same
    have refused : sameKey first second = false := by decide +kernel
    rw [refused] at accepted
    cases accepted
  have firstBody : (CachedSourceDefinitionTable.image chain first).body = .const second.2 :=
    image_here_body ⟨first, .const second.2⟩ [⟨second, terminal⟩]
  have secondBody : (CachedSourceDefinitionTable.image chain second).body = terminal :=
    (image_tail_body ⟨first, .const second.2⟩ [⟨second, terminal⟩] second distinct).trans
      (image_here_body ⟨second, terminal⟩ [])
  change (image chain 2 first).body = terminal
  rw [image_succ_body chain 1 first (by decide +kernel), firstBody]
  change (image chain 1 second).body = terminal
  rw [image_succ_body chain 0 second (by decide +kernel), secondBody]
  exact applyTerm_zero chain terminal
theorem cycle_stays_incomplete : completion cycle 4 input = .depthExhausted := by decide +kernel

def redex : Formula := .app (.lam (.var (.vz : HOL.Var [.prop] .prop))) .top

theorem tableClosed_with_beta_redex : completion [] 0 redex = .tableClosed ∧
    Nonempty (HOL.ContextualTrinity.BetaStep redex (.top : Formula)) :=
  ⟨rfl, ⟨.beta (.var .vz) .top⟩⟩

end Controls

#print axioms closedExpansion_free
#print axioms task
#print axioms tableClosed_iff
#print axioms Controls.chain_two_result
#print axioms Controls.cycle_stays_incomplete
#print axioms Controls.tableClosed_with_beta_redex

end Mettapedia.Languages.HOLLight.CachedSourceDefinitionClosure
