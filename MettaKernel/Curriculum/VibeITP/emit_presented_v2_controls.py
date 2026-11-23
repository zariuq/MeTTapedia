#!/usr/bin/env python3
"""Emit a shared concrete article and kernel-decided controls for the crossing fixture.

This is an untrusted data producer. The generated theorem checks its article
against the independently authored source goal, not a goal supplied by JSON.
"""

import argparse
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidates", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--actual-theory", action="store_true",
                        help="also transport this same article to the admitted byte-run theory")
    args = parser.parse_args()
    rows = json.loads(args.candidates.read_text())["results"]
    selected = [row for row in rows if row["name"] == "crossing" and row["status"] == "candidate"]
    if len(selected) != 1:
        raise ValueError("expected exactly one crossing candidate")
    patterns, articles, lines = {}, {}, []

    def pattern(value):
        head, children = value
        if not isinstance(head, str) or not isinstance(children, list):
            raise ValueError("expected a ground application")
        refs = tuple(pattern(child) for child in children)
        key = head, refs
        if key not in patterns:
            name = f"p{len(patterns)}"
            patterns[key] = name
            lines.append(f"private def {name} : Pattern := .apply {json.dumps(head, ensure_ascii=False)} [{', '.join(refs)}]")
        return patterns[key]

    def article(value):
        children = tuple(article(child) for child in value["children"])
        arguments = tuple(pattern(p) for p in value["arguments"])
        key = value["rule"], arguments, children
        if key not in articles:
            name = f"a{len(articles)}"
            articles[key] = name
            lines.append(f"private def {name} : RawProof := .node ⟨⟨{json.dumps(key[0])}⟩, [{', '.join(arguments)}]⟩ [{', '.join(children)}]")
        return articles[key]

    root = article(selected[0]["article"])
    text = """import Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentationControls

-- Generated calibration data; the kernel checks the supplied article below.
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousArticleControl
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open SimultaneousPresentation

""" + "\n".join(lines) + f"\n\ndef crossingArticle : RawProof := {root}\n" + """
theorem crossing_checked :
    checkRaw (validatedV2 Controls.theory Controls.allocated)
      (jThm (encTerm Controls.theory.sig Controls.crossing)) crossingArticle = true := by decide +kernel

theorem crossing_derived : Spec.DerivesV2 Controls.theory Controls.crossing :=
  checkRaw_soundV2 Controls.hosted crossing_checked

theorem sequential_goal_refused :
    checkRaw (validatedV2 Controls.theory Controls.allocated)
      (jThm (encTerm Controls.theory.sig Controls.sequential)) crossingArticle = false := by decide +kernel

#print axioms crossing_checked
#print axioms crossing_derived
#print axioms sequential_goal_refused
end Mettapedia.Languages.VibeITP.Presentation.SimultaneousArticleControl
"""
    if args.actual_theory:
        text = text.replace("import Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentationControls\n",
                            "import Mettapedia.Languages.VibeITP.Native.ProtocolV2PresentedReadback\n", 1)
        closing = "end Mettapedia.Languages.VibeITP.Presentation.SimultaneousArticleControl\n"
        extra = """
theorem actual_byte_theory_checks_same_article :
    checkRaw
      (validatedV2 Native.ProtocolV2LogicalControls.finalState.theory
        Native.ProtocolV2LogicalControls.finalState.nextFresh)
      (jThm (encTerm Native.ProtocolV2LogicalControls.finalState.theory.sig
        Spec.ProtocolV2.Controls.crossingResult)) crossingArticle = true :=
  Native.ProtocolV2PresentedReadback.supplied_article_transports crossingArticle crossing_checked

#print axioms actual_byte_theory_checks_same_article
"""
        text = text.replace(closing, extra + closing)
    args.output.write_text(text)
    print(f"{len(patterns)} distinct patterns, {len(articles)} distinct proof nodes")


if __name__ == "__main__":
    main()
