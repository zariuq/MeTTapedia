#!/usr/bin/env python3
"""Replay typed guarded quantifier transport through native HOL Light."""

from pathlib import Path

from check_natural_facts import main


if __name__ == "__main__":
    raise SystemExit(main(family="guarded", entrypoint=Path(__file__)))
