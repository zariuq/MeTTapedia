"""Parse each authored fixture once, then frame the packets for the independent Lean reader."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cetta", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    tool = Path(__file__).resolve().parent
    checker = tool / "check_module_reader.lean"
    inputs = [tool / name for name in re.findall(r'^#module_file\s+"([^"]+)"',
                                                  checker.read_text(), re.M)]
    if not inputs or len(set(p.resolve() for p in inputs)) != len(inputs):
        parser.error("missing or repeated .module fixture")
    binary = args.cetta.resolve()
    quote = lambda path: json.dumps(str(path), ensure_ascii=False)
    program = [
        f"!(import! &self {quote(binary.parent / 'lib/lib_lbnf.metta')})",
        f"""!(bind! &module-fixture-parser (let $read (lbnf:read-file {quote(tool.parent / 'module/module_v1.cf')})
  (case (lbnf:finish-read $read)
    (((LbnfReadValueV1 $binding $origin $document)
      (let $syntax (lbnf:lower-document $document "ModuleV1" "ModuleFile" (SyntaxLexicalPolicyV1 bnfc-documented))
        (case $syntax (((SyntaxGSLTAdmittedV1 $entry) (langdef:load-syntax-gslt-parser $syntax)) ($other $other)))))
     ($other $other)))))""",
        *(f"!(langdef:parse-authored-file &module-fixture-parser {quote(p.resolve())})" for p in inputs),
        "!(langdef:close-parser &module-fixture-parser)",
    ]
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    driver = out / "read_modules.metta"
    driver.write_text("\n".join(program) + "\n")
    verdict = subprocess.run([str(binary), "--lang", "he", "--profile", "extended", str(driver)],
                             capture_output=True, check=True)
    rows = [line for line in verdict.stdout.splitlines() if line.startswith(b"[(LangDef:AuthoredParse")]
    if len(rows) != len(inputs):
        raise SystemExit(f"expected {len(inputs)} parser results, got {len(rows)}")
    packet = re.compile(rb'^\[\(LangDef:AuthoredParseAccepted ModuleV1 "([0-9a-f]{64})" "([0-9a-f]{64})" ')
    grammar_ids = set()
    for path, row in zip(inputs, rows):
        header = packet.match(row)
        if not header or not row.endswith(b")]"):
            raise SystemExit(f"{path.name}: expected a complete accepted packet")
        if header[2].decode() != hashlib.sha256(path.read_bytes()).hexdigest():
            raise SystemExit(f"{path.name}: parser packet does not match source bytes")
        grammar_ids.add(header[1])
    if len(grammar_ids) != 1:
        raise SystemExit("fixture packets were produced by different grammars")
    # The parser payloads are data. Do not send the growing prefix through
    # MeTTa evaluation again merely to construct the outer transport list.
    (out / "module_reads.metta").write_bytes(b"(ModuleReads " + b" ".join(r[1:-1] for r in rows) + b")\n")


if __name__ == "__main__":
    main()
