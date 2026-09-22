import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Gate
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NormalForm

/-!
# Encoding an input prefix, verified on the worked cases

The reflective encoding of an input prefix has three parts: a distributor
broadcasting the arriving name to one proxy per occurrence of the bound name
plus one trigger, a gate holding the continuation, and one link per occurrence
converting the received name into the wiring that occurrence needs.

This file verifies the cases whose reduction sequences are fully determined,
end to end.

## The optimized clauses

Three inputs encode to a single atom, and each discharges in one step:

* a bound name that never occurs — the arriving message is discarded;
* a body that is exactly the bound name dropped — the arriving name is opened;
* a body forwarding the bound name — the arriving name is forwarded on.

## The worked occurrence

`encodeOutputSubjectInput` is the encoding of an input whose bound name occurs
once, as an output subject.  `encodeOutputSubjectInput_reaches` runs it: the
distributor splits the arriving name, the gate releases the continuation with
its subject standing at a proxy, the link turns the received name into a
forwarder from that proxy, and the continuation's message is delivered on the
received name.  The result is exactly the encoding of an output on the
received name.

That sequence is where the linearity comes from.  The continuation is never
rewritten — it is stored, released, and then rewired by a single forwarder.

## The constructor occurrence, and a missing atom

The remaining occurrence kind is one inside a quotation, where the name must
be rebuilt from the received one by a constructor chain.
`encodeQuotedOccurrenceInput` handles it and
`encodeQuotedOccurrenceInput_reaches` runs it in eight steps to exactly the
encoding of an output on the assembled name.

The shape is forced by the output-subject case.  There the link produces a
*forwarder* at the proxy and the continuation produces the message, and the
forwarder is what reroutes that message to the name which actually arrived.
The constructor case must end the same way: the chain assembles the name, and
then a bind-out atom turns the assembled name into a forwarder at the proxy.
The chain *computes* the name where the other case *receives* it; the wiring
that consumes it is identical.

Without that atom the assembled name arrives as a message at the proxy while
the continuation also carries a message at the proxy, leaving two producers at
one subject and no consumer between them.  The source note's worked example
for this occurrence kind omits the atom, which is worth reporting; the
encoding here includes it and is verified.

## References

- F1R3FLY.io research note, *Name-Free Combinators for the Rho Calculus*,
  draft 3, 2026, whose translation clauses and worked examples these follow.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## The optimized clauses -/

/-- An input whose bound name never occurs: discard the arriving message. -/
theorem encodeInputDiscard_reaches (subject v : Comb) :
    Reaches (par (kk subject) (mm subject v)) nil :=
  Reaches.single (StepMinus.discard v (Cong.refl subject))

/-- An input whose body is the bound name dropped: open the arriving name. -/
theorem encodeInputDrop_reaches (subject v : Comb) :
    Reaches (par (ev subject) (mm subject v)) v :=
  Reaches.single (StepMinus.opening v (Cong.refl subject))

/-- An input forwarding the bound name: forward the arriving name on. -/
theorem encodeInputForward_reaches (subject target v : Comb) :
    Reaches (par (fw subject target) (mm subject v)) (mm target v) :=
  Reaches.single (StepMinus.forward target v (Cong.refl subject))

/-! ## The worked occurrence -/

/-- The encoding of an input whose bound name occurs once, as an output
subject: distribute the arriving name, gate the continuation, and install a
forwarder from the proxy to the received name. -/
def encodeOutputSubjectInput (subject p₀ p₁ store run proxy : Comb) : Comb :=
  par (dd subject p₀ p₁)
    (par (gate p₀ store run (mm proxy nil))
      (br p₁ proxy))

/-- **The encoding sends on the received name.**  Supplying a message at the
input subject carrying `v`, the encoded term reaches exactly the encoding of
an output on `v` — the continuation arrives through the gate and the link
rewires the proxy to `v`. -/
theorem encodeOutputSubjectInput_reaches
    (subject p₀ p₁ store run proxy v : Comb) :
    Reaches (par (encodeOutputSubjectInput subject p₀ p₁ store run proxy)
        (mm subject v))
      (mm v nil) := by
  -- distribute the arriving name to the gate trigger and to the link
  have distribute :
      StepMinus Cong
        (par (encodeOutputSubjectInput subject p₀ p₁ store run proxy)
          (mm subject v))
        (par (par (mm p₀ v) (mm p₁ v))
          (par (gate p₀ store run (mm proxy nil)) (br p₁ proxy))) := by
    refine StepMinus.congruent
      (p' := par (par (dd subject p₀ p₁) (mm subject v))
        (par (gate p₀ store run (mm proxy nil)) (br p₁ proxy)))
      (q' := par (par (mm p₀ v) (mm p₁ v))
        (par (gate p₀ store run (mm proxy nil)) (br p₁ proxy)))
      ?_ ?_ (Cong.refl _)
    · exact par_rotate' (dd subject p₀ p₁)
        (par (gate p₀ store run (mm proxy nil)) (br p₁ proxy)) (mm subject v)
    · exact StepMinus.parLeft _
        (StepMinus.duplicate p₀ p₁ v (Cong.refl subject))
  -- bring the gate next to its trigger message
  have shape :
      Cong
        (par (par (mm p₀ v) (mm p₁ v))
          (par (gate p₀ store run (mm proxy nil)) (br p₁ proxy)))
        (par (par (gate p₀ store run (mm proxy nil)) (mm p₀ v))
          (par (mm p₁ v) (br p₁ proxy))) :=
    Cong.trans (Cong.parComm _ _)
      (Cong.trans (Cong.parAssoc _ _ _)
        (Cong.trans (Cong.parRight _
            (Cong.trans (Cong.parComm _ _) (Cong.parAssoc _ _ _)))
          (Cong.symm (Cong.parAssoc _ _ _))))
  -- the gate releases the body, leaving the link and its message
  have gateFires :
      Reaches
        (par (par (gate p₀ store run (mm proxy nil)) (mm p₀ v))
          (par (mm p₁ v) (br p₁ proxy)))
        (par (mm proxy nil) (par (mm p₁ v) (br p₁ proxy))) :=
    Reaches.parLeft _ (gate_releases p₀ store run (mm proxy nil) v)
  -- the link converts the received name into a forwarder from the proxy
  have linkFires :
      StepMinus Cong (par (mm proxy nil) (par (mm p₁ v) (br p₁ proxy)))
        (par (mm proxy nil) (fw proxy v)) := by
    refine StepMinus.congruent
      (p' := par (mm proxy nil) (par (br p₁ proxy) (mm p₁ v)))
      (q' := par (mm proxy nil) (fw proxy v))
      (Cong.parRight _ (Cong.parComm _ _)) ?_ (Cong.refl _)
    exact StepMinus.congruent (Cong.parComm _ _)
      (StepMinus.parLeft _ (StepMinus.bindOut proxy v (Cong.refl p₁)))
      (Cong.parComm _ _)
  -- the forwarder delivers the body's message on the received name
  have deliver :
      StepMinus Cong (par (mm proxy nil) (fw proxy v)) (mm v nil) := by
    refine StepMinus.congruent
      (p' := par (fw proxy v) (mm proxy nil))
      (q' := mm v nil)
      (Cong.parComm _ _) ?_ (Cong.refl _)
    exact StepMinus.forward v nil (Cong.refl proxy)
  exact Reaches.trans (Reaches.single distribute)
    (Reaches.trans (Reaches.congruent shape)
      (Reaches.trans gateFires
        (Reaches.trans (Reaches.single linkFires) (Reaches.single deliver))))

/-! ## The quoted occurrence -/

/-- The encoding of an input whose bound name occurs once inside a quotation.
The constructor rebuilds the quoted name from the received one, and the link
installs a forwarder from the proxy to the rebuilt name, exactly as the
output-subject case installs one to a received name. -/
def encodeQuotedOccurrenceInput
    (subject p₀ p₁ r₁ r₂ built store run proxy : Comb) : Comb :=
  par (dd subject p₀ p₁)
    (par (dd p₁ r₁ r₂)
      (par (consPar r₁ r₂ built)
        (par (br built proxy) (gate p₀ store run (mm proxy nil)))))

/-- **The encoding sends on the rebuilt name.**  Supplying a message at the
input subject carrying `v`, the encoded term reaches exactly the encoding of
an output on the assembled name `⌜v ∣ v⌝`. -/
theorem encodeQuotedOccurrenceInput_reaches
    (subject p₀ p₁ r₁ r₂ built store run proxy v : Comb) :
    ReachesFull (par (encodeQuotedOccurrenceInput subject p₀ p₁ r₁ r₂ built store run proxy)
        (mm subject v))
      (mm (par v v) nil) := by
  have ac : ∀ x y : Comb, components x = components y → Cong x y :=
    fun _ _ h => cong_of_components h
  -- 1. the outer duplicator splits the arriving name
  have s1 : StepMinus Cong
      (par (encodeQuotedOccurrenceInput subject p₀ p₁ r₁ r₂ built store run proxy)
        (mm subject v))
      (par (mm p₀ v) (par (mm p₁ v) (par (dd p₁ r₁ r₂)
        (par (consPar r₁ r₂ built)
          (par (br built proxy) (gate p₀ store run (mm proxy nil))))))) := by
    refine StepMinus.congruent
      (p' := par (par (dd subject p₀ p₁) (mm subject v))
        (par (dd p₁ r₁ r₂) (par (consPar r₁ r₂ built)
          (par (br built proxy) (gate p₀ store run (mm proxy nil))))))
      (q' := par (par (mm p₀ v) (mm p₁ v))
        (par (dd p₁ r₁ r₂) (par (consPar r₁ r₂ built)
          (par (br built proxy) (gate p₀ store run (mm proxy nil))))))
      (ac _ _ (by simp only [components, encodeQuotedOccurrenceInput, gate]; ac_rfl))
      (StepMinus.parLeft _ (StepMinus.duplicate p₀ p₁ v (Cong.refl subject)))
      (ac _ _ (by simp only [components, gate]; ac_rfl))
  -- 2. the inner duplicator supplies both constructor arguments
  have s2 : StepMinus Cong
      (par (mm p₀ v) (par (mm p₁ v) (par (dd p₁ r₁ r₂)
        (par (consPar r₁ r₂ built)
          (par (br built proxy) (gate p₀ store run (mm proxy nil)))))))
      (par (mm r₁ v) (par (mm r₂ v) (par (mm p₀ v)
        (par (consPar r₁ r₂ built)
          (par (br built proxy) (gate p₀ store run (mm proxy nil))))))) := by
    refine StepMinus.congruent
      (p' := par (par (dd p₁ r₁ r₂) (mm p₁ v))
        (par (mm p₀ v) (par (consPar r₁ r₂ built)
          (par (br built proxy) (gate p₀ store run (mm proxy nil))))))
      (q' := par (par (mm r₁ v) (mm r₂ v))
        (par (mm p₀ v) (par (consPar r₁ r₂ built)
          (par (br built proxy) (gate p₀ store run (mm proxy nil))))))
      (ac _ _ (by simp only [components, gate]; ac_rfl))
      (StepMinus.parLeft _ (StepMinus.duplicate r₁ r₂ v (Cong.refl p₁)))
      (ac _ _ (by simp only [components, gate]; ac_rfl))
  -- 3. the constructor assembles the quoted name
  have s3 : Step Cong
      (par (mm r₁ v) (par (mm r₂ v) (par (mm p₀ v)
        (par (consPar r₁ r₂ built)
          (par (br built proxy) (gate p₀ store run (mm proxy nil)))))))
      (par (mm built (par v v)) (par (mm p₀ v)
        (par (br built proxy) (gate p₀ store run (mm proxy nil))))) := by
    refine Step.congruent
      (p' := par (par (consPar r₁ r₂ built) (par (mm r₁ v) (mm r₂ v)))
        (par (mm p₀ v) (par (br built proxy)
          (gate p₀ store run (mm proxy nil)))))
      (q' := par (mm built (par v v)) (par (mm p₀ v)
        (par (br built proxy) (gate p₀ store run (mm proxy nil)))))
      (ac _ _ (by simp only [components, gate]; ac_rfl))
      (Step.parLeft _ (Step.buildPar built v v (Cong.refl r₁) (Cong.refl r₂)))
      (Cong.refl _)
  -- 4. the link installs a forwarder from the proxy to the assembled name
  have s4 : Step Cong
      (par (mm built (par v v)) (par (mm p₀ v)
        (par (br built proxy) (gate p₀ store run (mm proxy nil)))))
      (par (fw proxy (par v v))
        (par (mm p₀ v) (gate p₀ store run (mm proxy nil)))) := by
    refine Step.congruent
      (p' := par (par (br built proxy) (mm built (par v v)))
        (par (mm p₀ v) (gate p₀ store run (mm proxy nil))))
      (q' := par (fw proxy (par v v))
        (par (mm p₀ v) (gate p₀ store run (mm proxy nil))))
      (ac _ _ (by simp only [components, gate]; ac_rfl))
      (Step.parLeft _ (Step.ofMinus
        (StepMinus.bindOut proxy (par v v) (Cong.refl built))))
      (Cong.refl _)
  -- 5. the gate releases the continuation, whose subject stands at the proxy
  have s5 : ReachesFull
      (par (fw proxy (par v v))
        (par (mm p₀ v) (gate p₀ store run (mm proxy nil))))
      (par (mm proxy nil) (fw proxy (par v v))) := by
    refine ReachesFull.trans
      (ReachesFull.congruent (ac _ _ (by simp only [components, gate]; ac_rfl) :
        Cong (par (fw proxy (par v v))
            (par (mm p₀ v) (gate p₀ store run (mm proxy nil))))
          (par (par (gate p₀ store run (mm proxy nil)) (mm p₀ v))
            (fw proxy (par v v))))) ?_
    exact ReachesFull.parLeft _ (ReachesFull.ofReaches
      (gate_releases p₀ store run (mm proxy nil) v))
  -- 6. the forwarder delivers the continuation on the assembled name
  have s6 : Step Cong (par (mm proxy nil) (fw proxy (par v v)))
      (mm (par v v) nil) := by
    refine Step.congruent
      (p' := par (fw proxy (par v v)) (mm proxy nil))
      (q' := mm (par v v) nil)
      (Cong.parComm _ _)
      (Step.ofMinus (StepMinus.forward (par v v) nil (Cong.refl proxy)))
      (Cong.refl _)
  exact ReachesFull.trans (ReachesFull.single (Step.ofMinus s1))
    (ReachesFull.trans (ReachesFull.single (Step.ofMinus s2))
      (ReachesFull.trans (ReachesFull.single s3)
        (ReachesFull.trans (ReachesFull.single s4)
          (ReachesFull.trans s5 (ReachesFull.single s6)))))

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.encodeInputDiscard_reaches
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.encodeInputDrop_reaches
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.encodeInputForward_reaches
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.encodeOutputSubjectInput_reaches
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.encodeQuotedOccurrenceInput_reaches
