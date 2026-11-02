import Mettapedia.Computability.KolmogorovComplexity.ConditionalProgramModel

/-!
# Contextual field codes and framed conditional programs

Two independently decoded fields form a complete program frame. The parser
retains contextual suffixes and checks canonical re-encoding. Prefix freeness
is derived from the contextual decoding laws, not assumed of the interpreter.
All codecs are ordinary mathematical data with proved primitive recursion.
-/

set_option autoImplicit false

namespace KolmogorovComplexity

open scoped Classical

structure ContextualWordCode where
  put : List Bool → List Bool
  read : List Bool → Option (List Bool × List Bool)
  read_put_append : ∀ word suffix, read (put word ++ suffix) = some (word, suffix)
  put_primrec : Primrec put
  read_primrec : Primrec read

structure PairedWordCode where
  head : ContextualWordCode
  payload : ContextualWordCode

structure ConditionPairing where
  pack : List Bool → List Bool → List Bool
  unpack : List Bool → Option (List Bool × List Bool)
  unpack_pack : ∀ condition payload, unpack (pack condition payload) = some (condition, payload)
  pack_computable : Computable₂ pack
  unpack_computable : Computable unpack

def ContextualWordCode.conditionPairing (code : ContextualWordCode) : ConditionPairing where
  pack := fun condition payload => code.put condition ++ payload
  unpack := code.read
  unpack_pack := code.read_put_append
  pack_computable :=
    (Primrec.list_append.comp (code.put_primrec.comp Primrec.fst) Primrec.snd).to_comp
  unpack_computable := code.read_primrec.to_comp

def NaturalWordCodec.conditionPairing (codec : NaturalWordCodec) : ConditionPairing where
  pack := codec.packCondition
  unpack := fun word => some (codec.unpackCondition word)
  unpack_pack := fun condition payload => by simp only [codec.unpack_packCondition]
  pack_computable := codec.packCondition_computable
  unpack_computable := Computable.option_some.comp codec.unpackCondition_computable

namespace ConditionPairing

def relay (pairing : ConditionPairing) (V : ConditionalAlgorithm) : ConditionalAlgorithm :=
  fun _program condition => (Part.ofOption (pairing.unpack condition)).bind fun fields => V fields.2 fields.1

theorem relay_partrec (pairing : ConditionPairing) {V : ConditionalAlgorithm} (effective : Partrec₂ V) :
    Partrec₂ (pairing.relay V) := by
  have parsed : Partrec fun input : List Bool × List Bool => Part.ofOption (pairing.unpack input.2) :=
    (pairing.unpack_computable.comp Computable.snd).ofOption
  exact parsed.bind (effective.comp (Computable.snd.comp Computable.snd)
    (Computable.fst.comp Computable.snd)).to₂

theorem relay_packed (pairing : ConditionPairing) (V : ConditionalAlgorithm)
    (program condition payload : List Bool) : pairing.relay V program (pairing.pack condition payload) =
      V payload condition := by
  simp only [relay, pairing.unpack_pack, Part.coe_some, Part.bind_some]

/-- A single actual source program applies the simulated algorithm to every
payload and condition, supplied through the declared condition codec. -/
theorem relay_compiler (pairing : ConditionPairing) (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) {V : ConditionalAlgorithm} (effective : Partrec₂ V) :
    ∃ program : List Bool, ∀ payload condition output, output ∈ V payload condition →
      output ∈ U program (pairing.pack condition payload) := by
  obtain ⟨compiler, compiles⟩ := universal (pairing.relay V) (pairing.relay_partrec effective)
  refine ⟨compiler, fun payload condition output observed => ?_⟩
  have result : output ∈ pairing.relay V [] (pairing.pack condition payload) := by
    simpa only [pairing.relay_packed] using observed
  simpa only [List.append_nil] using compiles [] _ output result

end ConditionPairing

namespace PairedWordCode

def encode (code : PairedWordCode) (head payload : List Bool) : List Bool :=
  code.head.put head ++ code.payload.put payload

def fields (code : PairedWordCode) (input : List Bool) : Option (List Bool × List Bool × List Bool) :=
  (code.head.read input).bind fun first =>
    (code.payload.read first.2).map fun second => (first.1, second.1, second.2)

def read (code : PairedWordCode) (input : List Bool) : Option (List Bool × List Bool) :=
  (code.fields input).bind fun values =>
    if values.2.2 = [] then
      if code.encode values.1 values.2.1 = input then some (values.1, values.2.1) else none
    else none

theorem encode_primrec (code : PairedWordCode) : Primrec₂ code.encode :=
  Primrec.list_append.comp (code.head.put_primrec.comp Primrec.fst)
    (code.payload.put_primrec.comp Primrec.snd)

theorem fields_primrec (code : PairedWordCode) : Primrec code.fields := by
  have second : Primrec fun context : List Bool × (List Bool × List Bool) => code.payload.read context.2.2 :=
    code.payload.read_primrec.comp (Primrec.snd.comp Primrec.snd)
  have grouped : Primrec₂ fun (context : List Bool × (List Bool × List Bool)) (values : List Bool × List Bool) =>
      (context.2.1, values.1, values.2) :=
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd).to₂
  exact Primrec.option_bind code.head.read_primrec (Primrec.option_map second grouped).to₂

theorem read_primrec (code : PairedWordCode) : Primrec code.read := by
  have encoded : Primrec fun context : List Bool × (List Bool × List Bool × List Bool) =>
      code.encode context.2.1 context.2.2.1 :=
    code.encode_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have pair : Primrec fun context : List Bool × (List Bool × List Bool × List Bool) =>
      (context.2.1, context.2.2.1) :=
    (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.option_bind code.fields_primrec
    (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const []))
      (Primrec.ite (Primrec.eq.comp encoded Primrec.fst)
        (Primrec.option_some.comp pair) (Primrec.const none)) (Primrec.const none)).to₂

theorem fields_encoded_append (code : PairedWordCode) (head payload suffix : List Bool) :
    code.fields (code.encode head payload ++ suffix) = some (head, payload, suffix) := by
  simp only [fields, encode, List.append_assoc, code.head.read_put_append, Option.bind_some,
    code.payload.read_put_append, Option.map_some]

theorem read_encoded (code : PairedWordCode) (head payload : List Bool) :
    code.read (code.encode head payload) = some (head, payload) := by
  have fields := code.fields_encoded_append head payload []
  simp only [List.append_nil] at fields
  simp only [read, fields, Option.bind_some, ↓reduceIte]

theorem read_sound (code : PairedWordCode) {input : List Bool} {values : List Bool × List Bool}
    (observed : code.read input = some values) : code.encode values.1 values.2 = input := by
  obtain ⟨fields, _readFields, selected⟩ := Option.bind_eq_some_iff.mp observed
  split_ifs at selected with empty canonical
  · have same := Option.some.inj selected
    exact (congrArg (fun pair : List Bool × List Bool => code.encode pair.1 pair.2) same.symm).trans canonical

/-- Contextual decoding leaves no possible nonempty suffix between two
complete paired encodings. -/
theorem suffix_empty_of_encoded_append (code : PairedWordCode) {first second : List Bool × List Bool}
    {suffix : List Bool} (same : code.encode first.1 first.2 ++ suffix = code.encode second.1 second.2) :
    suffix = [] := by
  have headRead := congrArg code.head.read same
  simp only [encode, List.append_assoc, code.head.read_put_append] at headRead
  have tails := congrArg Prod.snd (Option.some.inj headRead)
  have payloadRead := congrArg code.payload.read tails
  have finished : code.payload.read (code.payload.put second.2) = some (second.2, []) := by
    simpa only [List.append_nil] using code.payload.read_put_append second.2 []
  rw [code.payload.read_put_append, finished] at payloadRead
  exact congrArg Prod.snd (Option.some.inj payloadRead)

theorem read_rejects_extension (code : PairedWordCode) (head payload suffix : List Bool) (nonempty : suffix ≠ []) :
    code.read (code.encode head payload ++ suffix) = none := by
  cases observed : code.read (code.encode head payload ++ suffix) with
  | none => rfl
  | some values =>
      have same := code.read_sound observed
      exact False.elim (nonempty (code.suffix_empty_of_encoded_append
        (first := (head, payload)) (second := values) same.symm))

theorem accepted_prefix_eq (code : PairedWordCode) {first second : List Bool}
    {fields other : List Bool × List Bool}
    (before : code.read first = some fields) (after : code.read second = some other)
    (pref : first <+: second) : first = second := by
  obtain ⟨suffix, extended⟩ := pref
  have firstWord := code.read_sound before
  have secondWord := code.read_sound after
  have same : code.encode fields.1 fields.2 ++ suffix = code.encode other.1 other.2 := by
    rw [firstWord, secondWord]
    exact extended
  have empty := code.suffix_empty_of_encoded_append same
  simpa only [empty, List.append_nil] using extended

def execute (code : PairedWordCode) (U : ConditionalAlgorithm) (pack : List Bool → List Bool → List Bool) : ConditionalAlgorithm :=
  fun program condition => (Part.ofOption (code.read program)).bind fun fields => U fields.1 (pack condition fields.2)

theorem execute_encoded (code : PairedWordCode) (U : ConditionalAlgorithm) (pack : List Bool → List Bool → List Bool)
    (head payload condition : List Bool) :
    code.execute U pack (code.encode head payload) condition = U head (pack condition payload) := by
  simp only [execute, code.read_encoded, Part.coe_some, Part.bind_some]

theorem execute_iff (code : PairedWordCode) (U : ConditionalAlgorithm) (pack : List Bool → List Bool → List Bool)
    (program condition output : List Bool) :
    output ∈ code.execute U pack program condition ↔
      ∃ head payload, program = code.encode head payload ∧ output ∈ U head (pack condition payload) := by
  constructor
  · intro observed
    obtain ⟨fields, parsed, computes⟩ := Part.mem_bind_iff.mp observed
    have parsedOption : code.read program = some fields := by simpa using parsed
    exact ⟨fields.1, fields.2, (code.read_sound parsedOption).symm, computes⟩
  · rintro ⟨head, payload, rfl, computes⟩
    simpa only [code.execute_encoded] using computes

theorem execute_partrec (code : PairedWordCode) {U : ConditionalAlgorithm}
    (effective : Partrec₂ U) {pack : List Bool → List Bool → List Bool} (packing : Computable₂ pack) :
    Partrec₂ (code.execute U pack) := by
  have parsed : Partrec fun input : List Bool × List Bool => Part.ofOption (code.read input.1) :=
    (code.read_primrec.comp Primrec.fst).to_comp.ofOption
  have context : Computable fun input : (List Bool × List Bool) × (List Bool × List Bool) =>
      pack input.1.2 input.2.2 :=
    packing.comp (Computable.snd.comp Computable.fst) (Computable.snd.comp Computable.snd)
  exact parsed.bind (effective.comp (Computable.fst.comp Computable.snd) context).to₂

/-- The admitted program domain is prefix-free for every condition,
independently of which framed computations actually terminate. -/
theorem execute_prefix_none (code : PairedWordCode) (U : ConditionalAlgorithm)
    (pack : List Bool → List Bool → List Bool) {first second condition : List Bool}
    (pref : first <+: second) (different : first ≠ second)
    (halts : (code.execute U pack first condition).Dom) : code.execute U pack second condition = Part.none := by
  obtain ⟨output, computes⟩ := Part.dom_iff_mem.mp halts
  obtain ⟨head, payload, same, _observed⟩ := (code.execute_iff U pack first condition output).mp computes
  apply Part.eq_none_iff.mpr
  intro later observed
  obtain ⟨otherHead, otherPayload, otherSame, _computed⟩ := (code.execute_iff U pack second condition later).mp observed
  apply different
  apply code.accepted_prefix_eq (fields := (head, payload)) (other := (otherHead, otherPayload))
  · rw [same, code.read_encoded]
  · rw [otherSame, code.read_encoded]
  · exact pref

#print axioms encode_primrec
#print axioms fields_primrec
#print axioms read_primrec
#print axioms fields_encoded_append
#print axioms read_encoded
#print axioms read_sound
#print axioms suffix_empty_of_encoded_append
#print axioms read_rejects_extension
#print axioms accepted_prefix_eq
#print axioms execute_encoded
#print axioms execute_iff
#print axioms execute_partrec
#print axioms execute_prefix_none

end PairedWordCode

end KolmogorovComplexity
