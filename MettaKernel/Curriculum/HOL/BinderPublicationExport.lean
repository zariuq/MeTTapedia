import Mettapedia.Logic.TierZero.Adequacy.HOLLightBinderPublication
import Mettapedia.Languages.HOLLight.ExportCodec
import Mettapedia.Logic.TierZero.Adequacy.HOLLightPrimeRoute

/-! Replay the actual HOL Light JSONL export at the specimen's source signature
and compare its named root with the sequent used by the protected firing. -/
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open Mettapedia.Logic.TierZero.Adequacy.HOLLightBinderPublication
open DefinitionAdapters SignatureFormation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.TierZero.Adequacy.HOLLightPrimeRoute

private def predSymbol : Const := .mk (Name.global "cross_pred") .undefined

private def basis : ExportCodec.State :=
  let core := ContextControls.coreContext
  let schema := Ty.function (.var (Name.global "A")) Ty.bool
  let context := core.addConstant predSymbol schema
    ((typeFormedB_eq_true_iff _ _).mp (by decide +kernel)) (by decide +kernel)
  { received := ExportReplay.empty context
    symbols := ⟨[("fun", TypeOp.function), ("bool", TypeOp.bool)],
      [("=", Const.equality), ("cross_pred", predSymbol)]⟩ }

private def requireCheck (label : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError label)

private def routeControls (source : Pattern) (authority : Authority) (claim : Theorem)
    (cert : ProofSystem.Certificate) : IO Unit := do
  let registry : Registry := fun key => if key = source then some authority else none
  let run := dispatch registry (fun _ _ => []) source
  let target := (routeDecl source).targetSpace
  let atTarget := Mettapedia.GSLT.LanguageDef.GSLTIL.atPattern target
  let expected := issued source claim cert
  requireCheck "source export or its receipt changed on crossing"
    (run (request claim cert) == [atTarget expected] && recheck registry expected)

  let other := ProofExecution.Controls.reflexivityTheorem
  let otherGraph := ProofSystem.Controls.reflexivityCertificate
  requireCheck "second theorem failed through the same route"
    (run (request other otherGraph) == [atTarget (issued source other otherGraph)] &&
      recheck registry (issued source other otherGraph))
  let erased := { claim with sequent := { claim.sequent with hyp := ∅ } }
  requireCheck "erased hypotheses or wrong graph passed"
    ((run (request erased cert)).isEmpty && (run (request claim otherGraph)).isEmpty)
  let forged := Pattern.apply "Prime.import" [image other.sequent,
    .apply "HOLLight.receipt" [source, request claim cert]]
  requireCheck "tampered target or unknown source accepted"
    (!recheck registry forged && !recheck (fun _ => none) expected)
  let core : Authority := ⟨ContextControls.coreContext, emptyAxiomPolicy, inferInstance⟩
  requireCheck "missing source declaration was accepted" (!recheck (fun _ => some core) expected)

  let Γ := [Ty.bool, Ty.bool]
  let t := DBTerm.abs Ty.bool (.abs .bool (.bound 2))
  let swap := fun i => DBTerm.bound (if i == 0 then 1 else 0)
  let result := termImage Γ (.abs .bool (.abs .bool (.bound 3))) (.function .bool (.function .bool .bool))
  requireCheck "open substitution captured the outer variable"
    (run (termRequest Γ (substituteBound swap t)) == [atTarget result])
  requireCheck "dangling index or malformed packet admitted"
    ((run (termRequest Γ (.bound 2))).isEmpty && (run (.apply "HOLLight.request" [])).isEmpty)
  let A := Ty.var (Name.global "A")
  requireCheck "inferred function type absent from the signature"
    ((termType? TheoryContext.empty [] (.abs A (.bound 0))).isNone)
  let pending := Pattern.apply "still-running" []
  let waiting := Mettapedia.GSLT.LanguageDef.GSLTIL.viaPattern
    Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.forwardKind
    (Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.routeIdentity (routeDecl source)) source target pending
  requireCheck "rejection lost the independent source step"
    (dispatch registry (fun _ _ => [pending]) source (request erased cert) == [waiting])

  -- An unused axiom node still belongs to the source graph. Its independent
  -- REFL root has no axiom tags, but the entire graph needs the selected policy.
  let premise : Sequent := ⟨∅, ProofExecution.Controls.proposition⟩
  let selected : AxiomPolicy := fun s => s = premise
  let decideSelected : DecidablePred selected := fun q => inferInstanceAs (Decidable (q = premise))
  let some licensed := @RuleRequest.check selected decideSelected (.axiom premise)
    | throw (IO.userError "test axiom refused")
  let graph : ProofSystem.Certificate := ([
    ⟨licensed, .axiom premise, [], ("policy-control", 0)⟩,
    ProofExecution.Controls.reflexivity ("policy-control", 1)], 1)
  let permissive : Authority := ⟨core.context, selected, decideSelected⟩
  requireCheck "source policy failed to distinguish an unused proof node"
    (recheck (fun _ => some permissive) (issued source other graph) &&
     !recheck (fun _ => some core) (issued source other graph))

def main (args : List String) : IO UInt32 := do
  let [nodes, roots] := args | throw (IO.userError "expected nodes.jsonl and roots.jsonl")
  let events ← (← IO.FS.lines nodes).toList.mapM (fun line => IO.ofExcept (Lean.Json.parse line))
  let #[root] ← IO.FS.lines roots | throw (IO.userError "expected one source root")
  let root ← IO.ofExcept (Lean.Json.parse root)
  let name ← IO.ofExcept ((← IO.ofExcept (root.getObjVal? "name")).getStr?)
  let id ← IO.ofExcept ((← IO.ofExcept (root.getObjVal? "id")).getNat?)
  unless name == "BINDER_PUBLICATION" do throw (IO.userError "wrong root name")
  let some state := ExportCodec.receiveMany? emptyAxiomPolicy basis events
    | throw (IO.userError "source proof or claimed intermediate sequent refused")
  -- Compare the inference requests, parent slots and complete intermediate
  -- theorems. Source event identifiers are local to a HOL Light session.
  let mut nodes : Array ProofExecution.Receipt := #[]
  for event in state.received.receipts do
    let .proof node _ := event.command | throw (IO.userError "unexpected declaration event")
    nodes := nodes.push node
  let graph := nodes.mapIdx fun i node => ProofDataEncoding.receiptCodec.put { node with origin := (name, i) }
  unless graph.toList == certificate.1.map ProofDataEncoding.receiptCodec.put &&
      state.received.addresses.get? id == some certificate.2 do
    throw (IO.userError "different inference graph or named root slot")
  let expected := claim Ty.bool
  let some actual := ExportReplay.root? state.received id expected.sequent
    | throw (IO.userError "named root does not have the publication sequent")
  unless actual == expected do throw (IO.userError "root has different axiom dependencies")
  let source := Pattern.apply "HOLLight.core+cross_pred/v1" []
  let authority : Authority := ⟨basis.received.registered.context, emptyAxiomPolicy, inferInstance⟩
  let graph := (nodes.toList, certificate.2)
  routeControls source authority actual graph
  IO.println "HOL Light → Prime.simpleSlice: both theorems, source policies, scoped substitution and receipt replay passed"
  IO.println s!"{name}: {events.length} source events, {actual.sequent.hyp.card} hypothesis, {actual.axioms.card} axioms"
  return 0
