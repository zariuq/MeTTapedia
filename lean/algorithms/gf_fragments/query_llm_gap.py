#!/usr/bin/env python3
"""Query LLM to fill a gap, then parse the suggestion through GF C runtime.

Returns JSON with suggestion text AND GF parse tree in RawTerm format,
so Lean consumes it through the same FromJson pipeline as dev_eval.json.

Usage: python3 gf_fragments/query_llm_gap.py '{"hypothesis":"...","premises":[...],"gap":"..."}'
Output: {"suggestion":"...", "model":"...", "confidence":0.7, "trees":[{...}], "errors":[...]}
"""
import json, sys, os

PGF_PATH = "/home/zar/claude/gf-wordnet/build/ParseEng.pgf"

def mock_response(hypothesis, premises, gap):
    """Mock responses for known EntailmentBank examples."""
    h = hypothesis.lower()
    if "sound" in h and "vacuum" in h:
        return ("if something requires matter to travel and a place has no matter "
                "then that thing cannot travel through that place",
                "mock:entailmentbank-gold", 0.5)
    if "moon" in h and "impact" in h:
        return ("the moon is less bright than the sun so looking at it "
                "has less negative impact on the eyes",
                "mock:entailmentbank-gold", 0.5)
    if "gravity" in h and "orbit" in h:
        return ("gravity is the force that causes objects to orbit other objects",
                "mock:entailmentbank-gold", 0.5)
    if "weathering" in h and "erosion" in h:
        return ("erosion is the step that follows weathering in the rock cycle",
                "mock:entailmentbank-gold", 0.5)
    return ("the hypothesis follows from the given premises",
            "mock:generic-fallback", 0.3)

def pgf_tree_to_json(tree):
    """Convert a PGF Expr tree to RawTerm JSON format (fun + args)."""
    result = tree.unpack()
    if isinstance(result, tuple):
        fun_name, args = result
        return {"fun": fun_name, "args": [pgf_tree_to_json(a) for a in args]}
    else:
        return {"fun": str(result), "args": []}

def parse_with_gf(sentence):
    """Parse sentence through GF C runtime. Returns (trees_json, errors)."""
    try:
        import pgf
        g = pgf.readPGF(PGF_PATH)
        eng = g.languages["ParseEng"]
        trees = []
        for i, (prob, tree) in enumerate(eng.parse(sentence, cat=g.startCat)):
            trees.append(pgf_tree_to_json(tree))
            if i >= 0:  # top-1 only
                break
        return trees, []
    except ImportError:
        return [], ["pgf module not available"]
    except Exception as e:
        return [], [str(e)]

def main():
    if len(sys.argv) < 2:
        print(json.dumps({"error": "usage: query_llm_gap.py '{json}'"}))
        sys.exit(1)

    try:
        query = json.loads(sys.argv[1])
    except json.JSONDecodeError as e:
        print(json.dumps({"error": f"invalid JSON: {e}"}))
        sys.exit(1)

    hypothesis = query.get("hypothesis", "")
    premises = query.get("premises", [])
    gap = query.get("gap", "")

    # Get LLM suggestion (mock or real API)
    api_key = os.environ.get("ANTHROPIC_API_KEY", "")
    if api_key:
        try:
            import urllib.request
            premises_text = "\n".join(f"- {p}" for p in premises)
            prompt = (f"Given these premises about science:\n{premises_text}\n\n"
                      f"The hypothesis is: {hypothesis}\n\n"
                      f"A formal proof system identified this gap: {gap}\n\n"
                      f"What single factual sentence would bridge this gap?\n"
                      f"The sentence should be a simple, clear scientific fact.\n"
                      f"Reply with ONLY the bridging sentence, nothing else.")
            body = json.dumps({
                "model": "claude-sonnet-4-20250514",
                "max_tokens": 256,
                "messages": [{"role": "user", "content": prompt}]
            }).encode()
            headers = {
                "Content-Type": "application/json",
                "x-api-key": api_key,
                "anthropic-version": "2023-06-01"
            }
            req = urllib.request.Request(
                "https://api.anthropic.com/v1/messages",
                data=body, headers=headers, method="POST")
            with urllib.request.urlopen(req, timeout=30) as resp:
                data = json.loads(resp.read())
                suggestion = data["content"][0]["text"].strip()
                model = data.get("model", "claude-sonnet-4-20250514")
                confidence = 0.7
        except Exception as e:
            print(json.dumps({"warning": f"API failed: {e}"}), file=sys.stderr)
            suggestion, model, confidence = mock_response(hypothesis, premises, gap)
    else:
        suggestion, model, confidence = mock_response(hypothesis, premises, gap)

    # Parse suggestion through GF C runtime
    # Redirect stderr to suppress PGF_SYMBOL_CAPIT warnings
    import io, contextlib
    with contextlib.redirect_stderr(io.StringIO()):
        trees, errors = parse_with_gf(suggestion)

    print(json.dumps({
        "suggestion": suggestion,
        "model": model,
        "confidence": confidence,
        "trees": trees,
        "errors": errors,
    }))

if __name__ == "__main__":
    main()
