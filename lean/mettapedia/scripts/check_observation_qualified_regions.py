#!/usr/bin/env python3
"""Check region-theory imports and optional fresh Lean foundation receipts.

This is a source/receipt audit, not a Lean build or native-C qualification.
Run the audit root with warnings as errors before supplying its output log.
"""

import argparse
import copy
import json
from pathlib import Path
import re


MODULES = tuple("Mettapedia.GSLT.Dynamics." + name for name in (
    "RegionObservations", "RegionPortfolio", "PreparedRegion", "RegionCountInstances",
    "RegionInformationCoding", "RegionInformationTransport", "RegionDescriptionFloors",
    "RegionModeInformation", "RegionRepresentation", "RegionProtocolBridge",
    "SymbolicRegionPortfolio", "ClosureRegionPortfolio", "ImprovementRegionPortfolio",
    "ConjunctiveRegionProvenance", "ConjunctiveRowMatching", "ConjunctiveBindingJoin",
    "ConjunctiveBindingDomain", "ConjunctiveBindingEnumeration", "ConjunctiveBindingObservation",
    "ConjunctiveOutputDomain",
    "GenericJoinRegions", "IndexedJoinRegions", "IndexedTriangleCost", "CyclicJoinRegions", "PreparedFactorIndex", "NestedCTLRegion",
    "FactorProjectionLayout", "PreparedJoinRegions", "IndexedJoinLeaves", "PreparedJoinLedger",
    "IndexedJoinMaterialization", "IndexedJoinDelivery",
    "OrderedOCamlRegion", "CanonicalStorageRegion", "CollectedReadRegion", "CollectedReadInformation",
    "RootRetirementInformation",
)) + tuple("Mettapedia.Languages.MeTTa.PeTTa.Bridges." + name for name in (
    "AggregationPortfolio", "PureCallExtraction", "PureCallExtractionControls", "PureCallPortfolio",
    "OptionalCallExtraction", "QueryRegionExtraction", "QueryRegionControls",
    "ReadOnlyQuerySource", "ReadOnlyRegionExecution", "ReadOnlyQueryExtraction", "ReadOnlyQueryControls",
    "FlatQueryRowCodec", "FlatQueryPatternExtraction", "FlatQueryRelationCompilation",
    "FlatQueryConjunctionCompilation", "FlatQuerySourceExecution", "FlatQueryIndexedSource",
    "CapturedQuerySource", "SourceRegionExtraction", "IndexedQueryExtraction", "IndexedQueryControls",
    "ClosedQueryAdmission", "GuardedInsertionSource",
    "EffectfulQuerySource", "QuerySetMaterialization", "QuerySetMaterializationControls",
    "FreshInsertionSource", "FreshQueryMaterialization", "FreshQueryMaterializationControls",
    "NestedQuerySource", "FreshNestedQuerySource", "FreshQueryPhaseSource", "FreshQueryPhaseControls",
    "FreshInsertionContinuation", "FreshInsertionRank", "FreshInsertionContinuationControls",
    "BoundQueryPattern", "FreshConstructorSource", "FreshConstructorControls",
    "FlatQueryOutputDomain", "FlatQueryOutputControls",
    "FlatQueryDomainInvariant", "FiniteNestedQuerySource", "FiniteNestedQueryControls",
    "FiniteNestedQueryCompletion", "FiniteNestedQueryRank", "FiniteNestedQueryIteration",
    "FiniteNestedQueryDriver", "FiniteNestedDriverControls", "FiniteNestedQueryPortfolio", "FiniteNestedPortfolioControls",
    "KeyedImprovementSource", "KeyedImprovementEntry", "KeyedImprovementControls",
    "KeyedImprovementRows", "KeyedImprovementRowsControls", "WeightedImprovementSource", "WeightedImprovementControls",
    "FrontierCollectionSource", "FrontierIterationSource", "FrontierIterationRegion", "WeightedFrontierDriverControls",
    "FrontierIterationEntry", "FrontierIterationEntryControls",
    "WeightedQueryRows", "WeightedQueryExecution", "WeightedFrontierRefinement", "WeightedFrontierDriver",
    "KeyedSourceQualification",
    "QueryReadStability", "PreparedEffectfulQuery", "PreparedEffectfulQueryControls",
    "FirstQueryCursor", "OncePrimitiveSource", "ConstantQuerySource", "OnceQuerySource", "OnceQueryControls",
    "ClosedOnceQueryExecution", "ClosedOnceQueryRegion", "ClosedOnceQueryExtraction", "ClosedOnceQueryControls",
    "ClosedOnceQueryFrame", "LiteralQuerySource", "CollectedOnceQuerySource", "CollectedOnceQueryControls",
    "PresenceGuardSource", "PresenceGuardControls",
    "QueryBagMaterialization", "EffectfulTraversal", "CTLPreimageSource", "CTLPreimageExecution", "CTLPreimageControls",
    "PresenceGuardContinuation", "PresenceGuardContinuationControls", "QueryBagErasure", "CTLFrontierCleanupControls",
    "PresenceConditionalSource", "PresenceConditionalRegion", "PresenceConditionalControls",
    "ScopedQuerySource", "ScopedQueryControls", "CTLUntilRoundControls",
    "ScopedQueryContinuation", "ScopedQueryContinuationControls",
    "ScopedGuardSource", "ScopedOnceSource", "ScopedPresenceSource", "ScopedPresenceControls",
    "CapturedOnceSource", "CapturedPatternSupport", "CapturedCollectedOnceSource", "CapturedOnceSourceControls",
    "CapturedPresenceSource", "ScopedMutationSource", "CapturedPresenceControls",
    "ScopedInsertionSource", "ScopedInsertionSequence", "ScopedInsertionControls",
    "GuardedInsertionPairSource", "GuardedInsertionPairControls",
    "ScopedQueryScanStability",
    "ScopedEquationSource", "NamedPresenceSource", "ScopedEquationControls",
    "CTLUntilSourceRows", "CTLUntilSourceCapture", "CTLUntilSourceRowsControls",
    "CTLUntilMixedStore", "CTLUntilMixedCapture", "CTLUntilMixedControls",
    "CTLUntilPublicationSource", "CTLUntilPublicationControls",
    "ScopedCallOperands", "NamedPresenceConditional", "NamedPresenceAdmission", "NamedPresenceConditionalControls",
    "NamedGuardedInsertionSource", "NamedGuardedInsertionAdmission", "NamedGuardedInsertionControls",
    "NamedGuardedCandidateExecution", "NamedGuardedCandidateBatch", "CTLUntilCandidateBatchSource", "NamedGuardedCandidateBatchControls",
    "ScopedMatchPreparation", "CTLUntilCandidateAdmission",
    "ScopedMatchEntry", "ScopedNestedQueryExecution", "GuardedNestedQuerySource", "ScopedNestedQueryControls",
    "GuardedQueryGrowth", "CTLUntilQueryGrowth", "GuardedQueryGrowthControls",
    "GuardedQueryPackets",
    "GuardedQueryCollection", "GuardedCountReturn", "GuardedCountSource", "GuardedCountControls",
    "CTLUntilLeafPublication", "CTLUntilScopedCapture", "CTLUntilScopedFrame", "CTLUntilScopedRound",
    "CTLUntilRoundViews", "CTLUntilRoundPublication", "CTLUntilScopedRoundControls",
    "ScopedQueryWordRefinement", "CTLUntilWordUpdate", "CTLUntilCandidateWords", "CTLUntilRoundRefinement", "CTLUntilWordUpdateControls",
    "CTLUntilAdmissionFrame", "CTLUntilLeafAdmission", "CTLUntilCaptureAdmission", "ScopedQueryAdmission",
    "CTLUntilRoundAdmission", "CTLUntilRoundAdmissionControls",
    "ScalarCopyCapacity", "GuardedQueryCapacity", "CTLUntilLeafCompletion", "ScopedQueryWordCompletion",
    "GuardedQueryCopyCapacity", "CTLUntilRoundCompletion", "CTLUntilRoundCompletionControls",
    "CTLUntilDriverControls",
    "CapturedQueryOperands", "CapturedOnceQueryRegion", "CapturedQueryControls",
    "FoldCallbackExtraction", "AdditiveFoldSource", "FoldSurfaceClassifier", "FoldSurfaceControls",
    "FoldRegionEntry", "FoldRegionEntryControls", "CTLInstructionCodec", "OCamlRegionSourceBridge",
    "ScalarBodyNormalization", "ModeFoldSource", "ModeReadoutSource", "ModeSourceReplay", "ModeSourceControls",
    "ModeAggregationPortfolio", "ModePortfolioControls", "ExtremumFoldSource", "FoldAlgebraPortfolio",
    "PagedFoldAdmission", "PagedFoldSourceBoundary", "PagedFoldControls", "AccountedFoldEntry",
    "AccountedFoldControls", "PagedFoldPortfolio",
    "IntegerSortSource", "IntegerSortEntry",
)) + ("Mettapedia.Tools.KernelReflexivity", "Mettapedia.Languages.MeTTa.MetavariableFrameStoreCapacity",
      "Mettapedia.Logic.LP.UnificationReadSupport",
      "Mettapedia.Machines.CTLUntilFrontier", "Mettapedia.Machines.CTLUntilFrontierControls",
      "Mettapedia.Machines.CTLUntilCandidateBag", "Mettapedia.Machines.CTLUntilCandidateBagControls",
      "Mettapedia.InformationTheory.FiniteInterfaceCoding", "Mettapedia.InformationTheory.FiniteDescriptionFloors",
      "Mettapedia.Languages.MeTTa.PeTTa.StdLib", "Mettapedia.Languages.MeTTa.PeTTa.FoldSource",
      "Mettapedia.Languages.MeTTa.PeTTa.StreamSource", "Mettapedia.Languages.MeTTa.PeTTa.StreamSourceControls",
      "Mettapedia.Languages.MeTTa.PeTTa.CodeSupportAlgebra",
      "Mettapedia.Languages.MeTTa.PeTTa.MatchValueExtension",
      "Mettapedia.Languages.MeTTa.PeTTa.ControlComposition",
      "Mettapedia.Languages.ProcessCalculi.MORK.MatchLookupLocality",
      "Mettapedia.Languages.MeTTa.PeTTa.FoldSourceBoundary",
      "Mettapedia.Machines.Cursor.IndexedIntersection",
      "Mettapedia.Machines.Cursor.IndexedMultiwayProjection",
      "Mettapedia.Machines.Cursor.CyclicProgress",
      "Mettapedia.Machines.Cursor.IndexedCyclicIntersection",
      "Mettapedia.Machines.Cursor.IndexedCyclicEntry",
      "Mettapedia.Algorithms.CountedKeySort",
      "Mettapedia.Algorithms.Compression.ParameterRegionCost",
      "Mettapedia.Machines.Cursor.ContiguousKeyRuns",
      "Mettapedia.Machines.Cursor.IndexedKeyLookup",
      "Mettapedia.Machines.Cursor.IndexedKeyTable",
      "Mettapedia.Machines.Cursor.PreparedKeyRuns",
      "Mettapedia.Machines.Cursor.PrefixRunIndex",
      "Mettapedia.Machines.Cursor.PrefixProjectionIndex",
      "Mettapedia.Machines.StoredIdCandidateRetrieval",
      "Mettapedia.Algebra.Order.FiniteSetIteration", "Mettapedia.Logic.CTLFormula",
      "Mettapedia.Logic.CTLContextualInformation") + tuple("Mettapedia.Logic.BDD." + name for name in (
          "BoundedFixedPoints", "NestedCTL", "Canonical", "CTLProgram", "NestedCTLControls", "OperationCache")) + tuple(
              "Mettapedia.Languages.OCaml." + name for name in (
                  "ConstructorDispatch", "CompiledDispatch", "CompiledDispatchControls",
                  "InstructionEquality", "LiveCompiledDispatch")) + (
                      "Mettapedia.Machines.FiniteCutCatalogue", "Mettapedia.Machines.OrderedCutStore",
                      "Mettapedia.Machines.RegionReadCollection", "Mettapedia.Machines.RegionReadStability",
                      "Mettapedia.Machines.RegionReadCollectionControls", "Mettapedia.Machines.TypedScalarEquality",
                      "Mettapedia.Machines.RegionReadInformation", "Mettapedia.Machines.RegionReadCensus",
                      "Mettapedia.Machines.RootRetirementLedger", "Mettapedia.Machines.RootRetirementControls", "Mettapedia.Machines.OrderedKeyedRows",
                      "Mettapedia.Machines.ShortestPathRounds", "Mettapedia.Machines.ShortestPathRoundsControls", "Mettapedia.Machines.WeightedPathTransport",
                      "Mettapedia.GSLT.Parsing.SourceScanFinished", "Mettapedia.Machines.ResumableFinality",
                      "Mettapedia.Languages.MeTTa.PeTTa.EvaluatorAccounting", "Mettapedia.Languages.MeTTa.PeTTa.PagedFold",
                      "Mettapedia.Languages.MeTTa.PeTTa.PagedFoldCompletion", "Mettapedia.Languages.MeTTa.PeTTa.PagedFoldLedger")
AUDIT = "Mettapedia.GSLT.Dynamics.ObservationQualifiedRegionAudit"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORT = re.compile(r"^(?:(?:public|meta)\s+)?import\s+([\w.]+)", re.MULTILINE)


def without_comments(text):
    """Remove nested Lean comments without interpreting strings as comments."""
    out, position, depth, quoted = [], 0, 0, False
    while position < len(text):
        pair = text[position:position + 2]
        char = text[position]
        if depth:
            if pair == "/-":
                depth += 1
                position += 2
                continue
            if pair == "-/":
                depth -= 1
                position += 2
                continue
            out.append("\n" if char == "\n" else " ")
        elif quoted:
            out.append(char)
            if char == "\\" and position + 1 < len(text):
                position += 1
                out.append(text[position])
            elif char == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            out.append(" ")
            position += 2
            continue
        elif pair == "--":
            end = text.find("\n", position)
            position = len(text) if end < 0 else end
            continue
        else:
            out.append(char)
            quoted = char == '"'
        position += 1
    if depth:
        raise ValueError("unterminated block comment")
    return "".join(out)


def forbidden(module):
    return "PrimeCandidates" in module.split(".")


def import_closure(roots, read_module):
    pending, seen = list(roots), set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        if forbidden(module):
            raise ValueError(f"Prime draft dependency: {module}")
        seen.add(module)
        if module.startswith("Mettapedia."):
            pending.extend(IMPORT.findall(without_comments(read_module(module))))
    return seen


def decode_manifests(text):
    decoder, documents, position = json.JSONDecoder(), [], 0
    while True:
        start = text.find("{", position)
        if start < 0:
            return documents
        try:
            value, used = decoder.raw_decode(text[start:])
        except json.JSONDecodeError:
            position = start + 1
            continue
        if isinstance(value, dict) and "ownerModule" in value:
            documents.append(value)
        position = start + used


def check_manifests(documents, expected):
    by_owner = {}
    bodies = companions = 0
    axioms = set()
    for document in documents:
        owner = document["ownerModule"]
        if owner in by_owner:
            raise ValueError(f"duplicate module receipt: {owner}")
        by_owner[owner] = document
        if document.get("schemaVersion") != 2:
            raise ValueError(f"unsupported manifest schema: {owner}")
        if any(forbidden(name) for name in document["checkingEnvironment"]["importClosure"]):
            raise ValueError(f"Prime draft in checked import closure: {owner}")
        declarations = document["declarations"]
        if not declarations or document["kernelDeclarationCount"] != len(declarations):
            raise ValueError(f"missing or inconsistent declaration inventory: {owner}")
        counted = sum(entry["declaration"]["hasCheckedBody"] for entry in declarations)
        if counted != document["checkedBodyDeclarationCount"]:
            raise ValueError(f"body-count mismatch: {owner}")
        bodies += counted
        for entry in declarations:
            declaration = entry["declaration"]
            if declaration["originModule"] != owner:
                raise ValueError(f"wrong declaration owner: {declaration['name']}")
            if entry["containsAdmission"] or declaration["kind"] == "axiom":
                raise ValueError(f"admission or added axiom: {declaration['name']}")
            if declaration["unsafe"] or declaration["partial"]:
                raise ValueError(f"nonlogical body counted as checked: {declaration['name']}")
            names = {axiom["name"] for axiom in entry["transitiveAxioms"]}
            if not names <= ALLOWED_AXIOMS:
                raise ValueError(f"unexpected axioms: {declaration['name']}: {sorted(names)}")
            axioms.update(names)
        nonlogical = document["nonLogicalDeclarations"]
        if len(nonlogical) != document["nonLogicalDeclarationCount"]:
            raise ValueError(f"companion-count mismatch: {owner}")
        for entry in nonlogical:
            if not entry["runtimeCounterpart"]:
                raise ValueError(f"unpaired nonlogical declaration: {entry['name']}")
        companions += len(nonlogical)
    if set(by_owner) != set(expected):
        raise ValueError(f"module coverage mismatch: missing={sorted(set(expected) - set(by_owner))}, "
                         f"extra={sorted(set(by_owner) - set(expected))}")
    return {"modules": len(by_owner), "checked_bodies": bodies,
            "nonlogical_companions": companions, "axioms": sorted(axioms)}


def self_test():
    graph = {"Mettapedia.A": "import Mettapedia.B\n", "Mettapedia.B": "import Mathlib.Data.List.Basic\n"}
    assert import_closure(["Mettapedia.A"], graph.__getitem__) == set(graph) | {"Mathlib.Data.List.Basic"}
    tests = 1
    for bad in ("import Mettapedia.Languages.MeTTa.PrimeCandidates.Bad\n",
                "public import Mettapedia.Languages.MeTTa.PrimeCandidates.Bad\n",
                "import Mettapedia.Missing\n"):
        changed = {**graph, "Mettapedia.B": bad}
        try:
            import_closure(["Mettapedia.A"], changed.__getitem__)
        except (ValueError, KeyError):
            tests += 1
        else:
            raise AssertionError("bad import closure passed")
    hidden = "/- outer /- import Mettapedia.Bad -/ still -/\n-- import Mettapedia.Bad\nimport Mathlib.Data.List.Basic\n"
    assert IMPORT.findall(without_comments(hidden)) == ["Mathlib.Data.List.Basic"]
    tests += 1
    try:
        check_manifests([], MODULES)
    except ValueError:
        tests += 1
    else:
        raise AssertionError("empty audit log passed")
    fixture = {
        "ownerModule": "Mettapedia.Control", "schemaVersion": 2,
        "checkingEnvironment": {"importClosure": ["Mettapedia.Control"]},
        "kernelDeclarationCount": 1, "checkedBodyDeclarationCount": 1,
        "declarations": [{"declaration": {
            "name": "control", "originModule": "Mettapedia.Control", "kind": "theorem",
            "hasCheckedBody": True, "unsafe": False, "partial": False},
            "containsAdmission": False, "transitiveAxioms": [{"name": "propext"}]}],
        "nonLogicalDeclarationCount": 0, "nonLogicalDeclarations": [],
    }
    assert check_manifests([fixture], ["Mettapedia.Control"])["checked_bodies"] == 1
    tests += 1
    for mutation in ("admission", "axiom", "unsafe", "body_count", "owner", "dependency", "companion"):
        changed = copy.deepcopy(fixture)
        entry = changed["declarations"][0]
        if mutation == "admission":
            entry["containsAdmission"] = True
        elif mutation == "axiom":
            entry["transitiveAxioms"] = [{"name": "invented_axiom"}]
        elif mutation == "unsafe":
            entry["declaration"]["unsafe"] = True
        elif mutation == "body_count":
            changed["checkedBodyDeclarationCount"] = 0
        elif mutation == "owner":
            entry["declaration"]["originModule"] = "Mettapedia.Other"
        elif mutation == "dependency":
            changed["checkingEnvironment"]["importClosure"].append("Mettapedia.Languages.MeTTa.PrimeCandidates.Bad")
        else:
            changed["nonLogicalDeclarationCount"] = 1
            changed["nonLogicalDeclarations"] = [{"name": "unsafe", "runtimeCounterpart": None}]
        try:
            check_manifests([changed], ["Mettapedia.Control"])
        except ValueError:
            tests += 1
        else:
            raise AssertionError(f"broken manifest passed: {mutation}")
    return tests


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-log", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    def read_module(module):
        return (root / (module.replace(".", "/") + ".lean")).read_text()
    tests = self_test()
    closure = import_closure((*MODULES, AUDIT), read_module)
    for module in (*MODULES, AUDIT):
        source = without_comments(read_module(module))
        if re.search(r"\b(?:sorry|admit|native_decide|theorem_wanted)\b|\b\w*_wanted\w*\b", source):
            raise ValueError(f"unproved or native-evaluated source declaration: {module}")
        if re.search(r"^\s*(?:axiom|unsafe|partial)\s", source, re.MULTILINE):
            raise ValueError(f"untrusted source declaration: {module}")
    result = {"self_tests": tests, "source_modules": len(MODULES),
              "import_nodes": len(closure), "prime_draft_dependencies": 0}
    if args.audit_log:
        text = args.audit_log.read_text()
        if re.search(r"\berror:|\bwarning:|sorryAx", text):
            raise ValueError("audit log includes a diagnostic or admission")
        result["foundations"] = check_manifests(decode_manifests(text), MODULES)
    else:
        result["foundations"] = "not checked; supply a fresh strict Lean audit log"
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, AssertionError) as error:
        raise SystemExit(f"FAIL: {error}") from error
