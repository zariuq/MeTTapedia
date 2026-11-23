#!/usr/bin/env python3
"""Replay the admitted Boolean family's typed facts in native HOL Light."""

from pathlib import Path

from check_natural_facts import main


if __name__ == "__main__":
    raise SystemExit(main(family="boolean", entrypoint=Path(__file__)))
