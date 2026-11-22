import Mettapedia.OSLF.Syntax.RhoPayloadExecutorComparison

/-!
# Constructing names from open code

A literal quotation is sealed: substitution does not enter it. A name can
still be built from code that mentions enclosing bound names, by lift: output
the code as a process and receive its name. The payload is a process in the
enclosing scope, so substitution reaches it, and the receiver obtains the
quotation of the payload as filled when it was sent. Construction is fill,
then seal, and it costs one communication.

While the code is in flight it is inert: an output has no step of its own,
whatever its payload. Quotation identifies two codes exactly when they are
equal, except through a code that is a single drop, where `@*n = n` applies.

The birth of an offspring in the reflective ecology is the worked instance:
the parent sends the child's code, which mentions the parent's received name,
and receiving it and dropping it runs the filled code.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial (Rule)

/-! ## Construction by lift -/

section Construction

variable {Γ : Ctx sig}

/-- Read the name hole of a context as the name received by a new input. -/
def asReceived : Sub sig (Srt.nm :: Γ) (Srt.pr :: Γ)
  | _, .zero => received
  | _, .succ v => .var (.succ v)

/-- A context with one name hole, receiving that name from an input. -/
def receiving (context : Term sig (Srt.nm :: Γ) Srt.pr) : Term sig (Srt.pr :: Γ) Srt.pr :=
  bind asReceived context

/-- Receiving code `P` fills the name hole with `@P`. -/
theorem inst_receiving (context : Term sig (Srt.nm :: Γ) Srt.pr) (code : Term sig Γ Srt.pr) :
    inst (receiving context) code = inst context (quoT code) := by
  unfold inst receiving
  rw [bind_comp]
  congr 1
  funext _ v
  cases v with
  | zero => rfl
  | succ _ => rfl

/-- **Construction by lift.** Sending code on a channel and receiving it into a
context with a name hole reaches the context with the hole filled by the
quotation of the code, in one communication of either profile. The code is
whatever the enclosing binders have made it when it is sent. -/
theorem lift_constructs_name (rest : List (Rule sig metas)) (channel : Term sig Γ Srt.nm)
    (code : Term sig Γ Srt.pr) (context : Term sig (Srt.nm :: Γ) Srt.pr) :
    Steps (comm :: parCong :: rest)
      (parT (outT channel code) (inpT channel (receiving context)))
      (inst context (quoT code)) :=
  inst_receiving context code ▸ steps_comm rest channel code (receiving context)

end Construction

/-! ## A germ in flight is inert -/

section Inert

variable {Γ : Ctx sig}

/-- **An output does not step**, in either profile, whatever its payload,
including a payload that could step if it were running. -/
theorem output_inert {rest : List (Rule sig metas)} (hrest : rest = [] ∨ rest = [drop])
    (channel : Term sig Γ Srt.nm) (code target : Term sig Γ Srt.pr) :
    ¬ Steps (comm :: parCong :: rest) (outT channel code) target := by
  intro step
  have hsingle : atoms (outT channel code) = {cls (outT channel code)} := rfl
  rcases steps_inversion hrest step with
    ⟨c, q, K, others, hsrc, _⟩ | ⟨_, code', others, hsrc, _⟩
  · -- a communication would consume an input among the output's atoms
    have hmem : cls (inpT c K) ∈ atoms (outT channel code) := by
      change atoms (outT channel code) = _ at hsrc
      rw [hsrc]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
    rw [hsingle] at hmem
    have hparts := inpParts_invariant (cls_eq_iff.mp (Multiset.mem_singleton.mp hmem))
    change ({(cls c, cls K)} : Multiset _) = 0 at hparts
    exact Multiset.singleton_ne_zero _ hparts
  · -- a Drop would consume a dropped quotation among the output's atoms
    have hmem : cls (drpT (quoT code')) ∈ atoms (outT channel code) := by
      change atoms (outT channel code) = _ at hsrc
      rw [hsrc]
      exact Multiset.mem_cons_self _ _
    rw [hsingle] at hmem
    have hparts := outParts_invariant (cls_eq_iff.mp (Multiset.mem_singleton.mp hmem))
    change (0 : Multiset _) = {(cls channel, cls code)} at hparts
    exact Multiset.singleton_ne_zero _ hparts.symm

end Inert

/-! ## Quotation up to the equations -/

section Quotation

variable {Γ : Ctx sig}

/-- **Quotation is injective away from drops.** Two codes that are not single
drops have one name exactly when they are one class. -/
theorem quote_injective {code code' : Term sig Γ Srt.pr}
    (hcode : key code = none) (hcode' : key code' = none)
    (same : cls (quoT code) = cls (quoT code')) : cls code = cls code' := by
  have hcore := qcore_invariant (cls_eq_iff.mp same)
  rw [qcore_quo, qcore_quo, hcode, hcode'] at hcore
  injection hcore

/-- The exception is exact: quoting the drop of a quotation is that quotation,
though the dropped quotation and the code are different processes. -/
theorem quote_not_injective :
    cls (quoT (drpT (quoT (nilT : Term sig Γ Srt.pr)))) = cls (quoT nilT) ∧
      cls (drpT (quoT (nilT : Term sig Γ Srt.pr))) ≠ cls nilT := by
  refine ⟨cls_eq (quoteDrop_equiv _), fun same => ?_⟩
  have := congrArg Multiset.card (atoms_invariant (cls_eq_iff.mp same))
  change Multiset.card ({cls (drpT (quoT (nilT : Term sig Γ Srt.pr)))} : Multiset _) =
    Multiset.card (0 : Multiset (Cls Γ Srt.pr)) at this
  simp at this

/-- **Under the name law a drop codes a name it contains.** The process `*@0`
mentions the name `@0`, and its own name `@*@0` is `@0`, so a process need not
avoid its own name when it is a single drop. Quoting the syntactically larger
`*@0 | 0` gives `@0` as well; that term equals `*@0` up to the equations. -/
theorem self_code_through_drop :
    cls (quoT (drpT (quoT (nilT : Term sig Γ Srt.pr)))) = cls (quoT nilT) ∧
      cls (quoT (parT (drpT (quoT (nilT : Term sig Γ Srt.pr))) nilT)) = cls (quoT nilT) :=
  ⟨cls_eq (quoteDrop_equiv _),
    cls_eq ((equiv_quoT (parT_nil _)).trans (quoteDrop_equiv _))⟩

end Quotation

/-! ## Birth: a quotation, then a drop

The parent receives a name `m` and sends its child's code `m!(0)`, which
mentions `m`; the child is born when that code is received as a name and
dropped. The authored executor takes two steps, and each is one step of the
presented calculus. -/

section Birth

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep)

private def zeroP : Pattern := .apply "PZero" []
/-- `@0`, the parent's channel. -/
private def parentChannel : Pattern := .apply "NQuote" [zeroP]
/-- `@{@0!(0)}`, the channel carrying the child's code. -/
private def codeChannel : Pattern :=
  .apply "NQuote" [.apply "POutput" [parentChannel, zeroP]]

/-- `for(g <- code){*g} | code!(m!(0))` beneath the parent's input binding `m`. -/
private def parentBody : Pattern :=
  .collection .hashBag
    [.apply "PInput" [codeChannel, .lambda none (.apply "PDrop" [.bvar 0])],
     .apply "POutput" [codeChannel, .apply "POutput" [.bvar 0, zeroP]]] none

/-- `for(m <- @0){ parentBody } | @0!(0)`. -/
def birthSource : Pattern :=
  .collection .hashBag
    [.apply "PInput" [parentChannel, .lambda none parentBody],
     .apply "POutput" [parentChannel, zeroP]] none

/-- After the parent receives, its child's code is filled and in flight. -/
def birthMiddle : Pattern :=
  .collection .hashBag [semanticCommSubst parentBody zeroP] none

/-- After the child's code is received as a name and dropped. -/
def birthFinal : Pattern :=
  .collection .hashBag
    [.collection .hashBag
      [semanticCommSubst (.apply "PDrop" [.bvar 0])
        (.apply "POutput" [parentChannel, zeroP])] none] none

/-- The filled code in flight is `code!(@0!(0))`: the parent's name has been
substituted into the child's code before it is sealed. -/
theorem birthMiddle_eq :
    semanticCommSubst parentBody zeroP =
      .collection .hashBag
        [.apply "PInput" [codeChannel, .lambda none (.apply "PDrop" [.bvar 0])],
         .apply "POutput" [codeChannel, .apply "POutput" [parentChannel, zeroP]]] none := rfl

/-- The child runs its filled code `@0!(0)`. -/
theorem birthFinal_eq :
    semanticCommSubst (.apply "PDrop" [.bvar 0]) (.apply "POutput" [parentChannel, zeroP]) =
      .apply "POutput" [parentChannel, zeroP] := rfl

private theorem parentChannel_typed (bound : List String) :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty bound parentChannel :=
  .quote .unit

private theorem codeChannel_typed (bound : List String) :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty bound codeChannel :=
  .quote (.output (parentChannel_typed bound) .unit)

private theorem parentBody_typed :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      [rhoReflectivePresentation.nameSort] parentBody :=
  .parallel (.cons (.input (codeChannel_typed _) (.drop (.bvar rfl)))
    (.cons (.output (codeChannel_typed _) (.output (.bvar rfl) .unit)) .nil))

private theorem middleBody_typed :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
      (semanticCommSubst parentBody zeroP) := by
  rw [birthMiddle_eq]
  exact .parallel (.cons (.input (codeChannel_typed _) (.drop (.bvar rfl)))
    (.cons (.output (codeChannel_typed _) (.output (parentChannel_typed _) .unit)) .nil))

theorem birthSource_typed :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] birthSource :=
  .parallel (.cons (.input (parentChannel_typed _) parentBody_typed)
    (.cons (.output (parentChannel_typed _) .unit) .nil))

theorem birthMiddle_typed :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] birthMiddle :=
  .parallel (.cons middleBody_typed .nil)

/-- The parent receives its name and its child's code is filled. -/
theorem birth_first_step : RhoStep birthSource birthMiddle :=
  RhoStep.comm (bound := []) parentChannel parentBody zeroP [] parentBody_typed .unit

/-- The child's code is received as a name and dropped, inside the parallel
composition. -/
theorem birth_second_step : RhoStep birthMiddle birthFinal := by
  unfold birthMiddle birthFinal
  rw [birthMiddle_eq]
  exact RhoStep.par []
    (RhoStep.comm (bound := []) codeChannel (.apply "PDrop" [.bvar 0])
      (.apply "POutput" [parentChannel, zeroP]) [] (.drop (.bvar rfl))
      (.output (parentChannel_typed _) .unit))

/-- **Birth in the presented calculus.** Both executor steps are steps between
equation classes, and the child is the filled code `@0!(0)`. -/
theorem birth_presented :
    ∃ s m f, tProc (Env.empty []) birthSource = some s ∧
      tProc (Env.empty []) birthMiddle = some m ∧
      tProc (Env.empty []) birthFinal = some f ∧
      Steps strictRules s m ∧ Steps strictRules m f ∧
      f = parT (parT (outT (quoT nilT) nilT) nilT) nilT := by
  obtain ⟨m, hm, step₁⟩ :=
    rhoStep_simulation birthSource_typed birth_first_step (s₀ := _) rfl
  obtain ⟨f, hf, step₂⟩ := rhoStep_simulation birthMiddle_typed birth_second_step hm
  refine ⟨_, m, f, rfl, hm, hf, step₁, step₂, ?_⟩
  have : tProc (Env.empty []) birthFinal =
      some (parT (parT (outT (quoT nilT) nilT) nilT) nilT) := rfl
  rw [this] at hf
  exact (Option.some.inj hf).symm

end Birth

#print axioms lift_constructs_name
#print axioms output_inert
#print axioms quote_injective
#print axioms self_code_through_drop
#print axioms birth_presented

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
