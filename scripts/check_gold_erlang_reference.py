#!/usr/bin/env python3
"""Run local-actor observations on an explicitly pinned Erlang/OTP prefix.

The native harness uses process_info only to inspect reference mailboxes. The
two source programs use ordinary local spawn, send and selective receive.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "metta/gslt/module/gold/Erlang/examples"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--erlang-prefix", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    prefix = args.erlang_prefix.resolve(strict=True)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    versions = list(prefix.glob("lib/erlang/releases/*/OTP_VERSION"))
    if len(versions) != 1 or versions[0].read_text().strip() != "29.1.2":
        raise AssertionError("expected an Erlang/OTP 29.1.2 prefix")
    binaries = {name: (prefix / "bin" / name).resolve(strict=True) for name in ("erl", "erlc")}
    sources = sorted(EXAMPLES.glob("*.erl"))
    for source in sources:
        shutil.copyfile(source, output / source.name)
    pins = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    pins[str(Path(__file__).resolve().relative_to(ROOT))] = digest(Path(__file__).resolve())
    runtime = {str(p.relative_to(prefix)): digest(p) for p in sorted(prefix.rglob("*"))
               if p.is_file() and (p.suffix in (".beam", ".boot", ".so") or
                                  p.name in ("erl", "erlc", "erlexec", "beam.smp",
                                             "erl_child_setup", "OTP_VERSION"))}
    (output / "runtime-pins.json").write_text(json.dumps(runtime, indent=2) + "\n")
    environment = {k: v for k, v in os.environ.items()
                   if k not in ("ERL_FLAGS", "ERL_AFLAGS", "ERL_ZFLAGS", "ERL_LIBS")}
    environment["ERL_FLAGS"] = "+S 1:1 +A 1"
    record = {"passed": False, "compiler_correspondence_qualified": False,
              "otp_version": "29.1.2", "source_sha256": pins,
              "runtime_pins_sha256": digest(output / "runtime-pins.json"),
              "erl_flags": environment["ERL_FLAGS"], "runs": []}

    def run(name, engine, arguments):
        started = time.monotonic()
        result = subprocess.run([str(binaries[engine]), *arguments], cwd=output,
                                env=environment, capture_output=True, text=True, timeout=60)
        (output / (name + ".stdout")).write_text(result.stdout)
        (output / (name + ".stderr")).write_text(result.stderr)
        record["runs"].append({"name": name, "exit": result.returncode,
                               "elapsed_seconds": time.monotonic() - started,
                               "stdout_sha256": digest(output / (name + ".stdout")),
                               "stderr_sha256": digest(output / (name + ".stderr"))})
        if result.returncode != 0 or result.stderr:
            raise AssertionError(name + ": native command or diagnostics failed")
        return result.stdout

    try:
        record["system_version"] = run("version", "erl", ["-noshell", "-eval",
            'io:format("~s~n",[erlang:system_info(system_version)]),halt().']).strip()
        driver = '''-module(gold_native_checks).
-export([run/0]).

check(Name, true) -> io:format("PASS ~s~n", [Name]);
check(Name, false) -> erlang:error({failed, Name}).

run() ->
    Tasks = [{first,2},{same,3},{same,3},{last,-1}],
    Expected = [{0,first,6},{1,same,9},{2,same,9},{3,last,-3}],
    check("worker-pool", gold_worker_pool:run(3,3,Tasks) =:= Expected),
    check("schedule-independent-observation", gold_worker_pool:run(1,3,Tasks) =:= Expected),
    check("empty-work", gold_worker_pool:run(2,3,[]) =:= []),
    check("arbitrary-precision-integers",
          gold_worker_pool:run(1,3,[{large,1267650600228229401496703205376}])
          =:= [{0,large,3802951800684688204490109616128}]),
    Workers = gold_worker_pool:start(3,1,self()),
    check("fresh-process-identities", length(lists:usort(Workers)) =:= 3
          andalso not lists:member(self(), Workers)),
    lists:foreach(fun(Pid) -> Pid ! stop, receive {stopped, Pid} -> ok end end, Workers),
    check("invalid-worker-count-is-a-fault",
          try gold_worker_pool:run(0,1,[]) of
              _ -> false
          catch error:function_clause -> true end),

    Server = gold_selective_reply:start(3),
    check("callable-request-reply", gold_selective_reply:request(Server,first,7) =:= 21),
    self() ! unrelated,
    Server ! {request,self(),first,2},
    Server ! {request,self(),second,4},
    check("selective-later-reply", gold_selective_reply:collect(second) =:= 12),
    check("earlier-reply-retained", gold_selective_reply:collect(first) =:= 6),
    check("unmatched-message-retained", receive unrelated -> true after 0 -> false end),

    Server ! {request,self(),ordered_first,1},
    Server ! {request,self(),ordered_second,2},
    First = receive {reply, A, X} -> {A,X} end,
    Second = receive {reply, B, Y} -> {B,Y} end,
    check("same-sender-order", First =:= {ordered_first,3} andalso Second =:= {ordered_second,6}),
    Server ! {request,self(),duplicate,5},
    Server ! {request,self(),duplicate,5},
    check("duplicate-message-occurrences", gold_selective_reply:collect(duplicate) =:= 15
          andalso gold_selective_reply:collect(duplicate) =:= 15),

    Server ! unexpected,
    Server ! {request,self(),bad,not_an_integer},
    Server ! {barrier,self(),inspected},
    receive {barrier_reached,inspected} -> ok end,
    {messages, Mailbox} = process_info(Server,messages),
    check("failed-guard-preserves-mailbox", Mailbox =:= [unexpected,{request,self(),bad,not_an_integer}]),
    check("server-continues-after-unmatched-input", gold_selective_reply:request(Server,after_bad,9) =:= 27),
    {messages, StillRetained} = process_info(Server,messages),
    check("unmatched-prefix-remains-ordered", StillRetained =:= Mailbox),
    Server ! stop,
    ok.
'''
        (output / "gold_native_checks.erl").write_text(driver)
        compiled = run("compile", "erlc", ["-Werror", "+debug_info", "-o", ".",
            *[p.name for p in sources], "gold_native_checks.erl"])
        if compiled:
            raise AssertionError("unexpected native compiler output")
        observed = run("observations", "erl", ["-noshell", "-pa", ".", "-eval",
            "gold_native_checks:run(),halt()."])
        expected = ["worker-pool", "schedule-independent-observation", "empty-work",
                    "arbitrary-precision-integers", "fresh-process-identities",
                    "invalid-worker-count-is-a-fault", "callable-request-reply",
                    "selective-later-reply", "earlier-reply-retained", "unmatched-message-retained",
                    "same-sender-order", "duplicate-message-occurrences",
                    "failed-guard-preserves-mailbox", "server-continues-after-unmatched-input",
                    "unmatched-prefix-remains-ordered"]
        if observed.splitlines() != ["PASS " + name for name in expected]:
            raise AssertionError("incomplete native observation account")
        if not all(digest(ROOT / name) == value for name, value in pins.items()):
            raise AssertionError("source changed during reference run")
        if not all(digest(prefix / name) == value for name, value in runtime.items()):
            raise AssertionError("native runtime changed during reference run")
        record["checks"] = expected
        record["generated_sha256"] = {p.name: digest(p) for p in sorted(output.iterdir())
                                      if p.suffix in (".beam", ".erl")}
        record["passed"] = True
    except Exception as error:
        record["error"] = str(error)
        raise
    finally:
        (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"passed": True, "checks": len(record["checks"]),
                      "record_sha256": digest(output / "result.json")}))


if __name__ == "__main__":
    main()
