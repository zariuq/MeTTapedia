import Mettapedia.OSLF.Syntax.PatternAsBindingSignature
import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-!
# Typed and executable substitution agree on the pattern signature

The one-sort pattern signature already interprets every raw pattern former,
including binders, explicit substitutions and collection rests. This module
compares its intrinsically scoped variable substitution with the executable
simultaneous substitution on `Pattern`. The raw assignment is total because it
has no source-context index; the comparison only constrains indices that occur
in the typed source context.
-/

namespace Mettapedia.OSLF.Binding.PatternPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

mutual
/-- Number of term nodes, used to make the mutual induction's descent
through operator arguments explicit. -/
private def termNodeCount : {Γ : Ctx patSig} → {s : PatSrt} → Term patSig Γ s → Nat
  | _, _, .var _ => 1
  | _, _, .op _ args => argsNodeCount args + 1

private def argsNodeCount : {as : List (List PatSrt × PatSrt)} → {Γ : Ctx patSig} →
    Args patSig as Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => termNodeCount head + argsNodeCount tail + 1
end

/-- The executable assignment is the erasure of a typed substitution at every
variable of its declared source context. -/
def ErasesAssignment {Γ Δ : Ctx patSig}
    (sigma : Sub patSig Γ Δ) (assignment : Assignment) : Prop :=
  ∀ (s : PatSrt) (v : Var Γ s),
    erase (sigma s v) = assignment (varIndex v)

/-- Binder lifting preserves agreement between typed and executable variable
substitutions. In particular it fixes every newly bound variable. -/
theorem erasesAssignment_liftSub {Γ Δ : Ctx patSig}
    {sigma : Sub patSig Γ Δ} {assignment : Assignment}
    (h : ErasesAssignment sigma assignment) :
    ∀ (bs : List PatSrt),
      ErasesAssignment (liftSub sigma bs) (lift bs.length assignment)
  | [] => by
      simpa only [liftSub, List.length_nil, lift_zero] using h
  | _ :: bs => by
      intro s v
      cases v with
      | zero => rfl
      | succ w =>
          have ih := erasesAssignment_liftSub h bs s w
          have hw := erase_rename_shift (fun _ x => Var.succ x) 0
            shiftsAt_succ (liftSub sigma bs s w)
          change erase (weaken (liftSub sigma bs s w)) =
            lift (bs.length + 1) assignment (varIndex w + 1)
          rw [weaken, hw, ih, ← lift_lift 1 bs.length assignment]
          simp [lift]

mutual
/-- Erasure commutes with simultaneous context-variable substitution for
every typed pattern term, including terms under binders. -/
theorem erase_bind_substitute :
    ∀ {Γ Δ : Ctx patSig} (sigma : Sub patSig Γ Δ)
      (assignment : Assignment) (_ : ErasesAssignment sigma assignment)
      {s : PatSrt} (term : Term patSig Γ s),
      erase (bind sigma term) = substitute assignment (erase term)
  | _, _, sigma, assignment, h, _, .var v => h _ v
  | _, _, _, _, _, _, .op (.fvarOp _) _ => rfl
  | _, _, sigma, assignment, h, _, .op (.applyOp label _) args => by
      show Pattern.apply label (eraseArgs (bindArgs sigma args)) = _
      rw [eraseArgs_bind_substitute sigma assignment h args
        (fun e he => by rw [List.eq_of_mem_replicate he])]
      simp only [erase, substitute, substituteList_eq_map]
  | _, _, sigma, assignment, h, _, .op (.lamOp name) (.cons body .nil) => by
      show Pattern.lambda name
          (erase (bind (liftSub sigma [PatSrt.pat]) body)) = _
      rw [erase_bind_substitute (liftSub sigma [PatSrt.pat])
        (lift 1 assignment)
        (erasesAssignment_liftSub h [PatSrt.pat]) body]
      rfl
  | _, _, sigma, assignment, h, _, .op (.multiLamOp ar names) (.cons body .nil) => by
      show Pattern.multiLambda ar names
          (erase (bind (liftSub sigma (List.replicate ar PatSrt.pat)) body)) = _
      rw [erase_bind_substitute (liftSub sigma (List.replicate ar PatSrt.pat))
        (lift ar assignment)
        (by simpa using erasesAssignment_liftSub h (List.replicate ar PatSrt.pat)) body]
      rfl
  | _, _, sigma, assignment, h, _, .op .substOp (.cons body (.cons repl .nil)) => by
      show Pattern.subst
          (erase (bind (liftSub sigma [PatSrt.pat]) body))
          (erase (bind (liftSub sigma []) repl)) = _
      rw [erase_bind_substitute (liftSub sigma [PatSrt.pat])
          (lift 1 assignment)
          (erasesAssignment_liftSub h [PatSrt.pat]) body,
        erase_bind_substitute (liftSub sigma []) assignment
          (by simpa only [liftSub] using h) repl]
      rfl
  | _, _, sigma, assignment, h, _, .op (.collOp kind _ rest) args => by
      show Pattern.collection kind (eraseArgs (bindArgs sigma args)) rest = _
      rw [eraseArgs_bind_substitute sigma assignment h args
        (fun e he => by rw [List.eq_of_mem_replicate he])]
      simp only [erase, substitute, substituteList_eq_map]
termination_by _ _ _ _ _ _ term => termNodeCount term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termNodeCount, argsNodeCount]
  all_goals omega

/-- The ordered argument traversal preserves occurrence order; in particular
collection entries are not collapsed when their erasures happen to agree. -/
theorem eraseArgs_bind_substitute :
    ∀ {Γ Δ : Ctx patSig} (sigma : Sub patSig Γ Δ)
      (assignment : Assignment) (_ : ErasesAssignment sigma assignment)
      {as : List (List PatSrt × PatSrt)} (args : Args patSig as Γ),
      (∀ e ∈ as, e.1 = []) →
      eraseArgs (bindArgs sigma args) =
        (eraseArgs args).map (substitute assignment)
  | _, _, _, _, _, _, .nil, _ => rfl
  | _, _, sigma, assignment, h, (bs, _) :: rest, .cons head tail, hnb => by
      have hbs : bs = [] := hnb _ List.mem_cons_self
      have hlift : ErasesAssignment (liftSub sigma bs) assignment := by
        subst hbs
        simpa only [liftSub] using h
      show erase (bind (liftSub sigma bs) head) ::
          eraseArgs (bindArgs sigma tail) = _
      rw [erase_bind_substitute (liftSub sigma bs) assignment hlift head,
        eraseArgs_bind_substitute sigma assignment h tail
          (fun e he => hnb e (List.mem_cons_of_mem _ he))]
      rfl
termination_by _ _ _ _ _ _ args _ => argsNodeCount args
decreasing_by
  all_goals simp only [argsNodeCount]
  all_goals omega
end

/-- The pre-existing contextual metavariable assignment uses the same raw
simultaneous substitution after erasure. Its two source-context segments are
assembled by `joinSub`; the stated agreement is exactly the obligation for a
concrete occurrence spine and ambient transport. -/
theorem erase_contextualApply {M : List (MetaArity patSig)} {Γ Δ : Ctx patSig}
    (body : ContextualAssignment patSig M Γ) (i : Fin M.length)
    (arguments : Sub patSig (M.get i).1 Δ) (ambient : Sub patSig Γ Δ)
    (assignment : Assignment)
    (h : ErasesAssignment (ContextualAssignment.joinSub arguments ambient) assignment) :
    erase (ContextualAssignment.apply body i arguments ambient) =
      substitute assignment (erase (body i)) := by
  exact erase_bind_substitute _ _ h (body i)

end Mettapedia.OSLF.Binding.PatternPresentation
