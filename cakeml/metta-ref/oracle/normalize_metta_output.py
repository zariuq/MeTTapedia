#!/usr/bin/env python3
import argparse
import sys


def split_top_level_items(text):
    items = []
    buf = []
    depth = 0
    in_string = False
    escape = False

    def flush():
        item = "".join(buf).strip()
        if item:
            items.append(item)
        buf.clear()

    for ch in text:
        if in_string:
            buf.append(ch)
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue

        if ch == '"':
            in_string = True
            buf.append(ch)
        elif ch == "(":
            depth += 1
            buf.append(ch)
        elif ch == ")":
            depth -= 1
            buf.append(ch)
        elif depth == 0 and (ch == "," or ch.isspace()):
            flush()
        else:
            buf.append(ch)

    flush()
    return items


def normalize_line(line, bag):
    line = line.strip()
    if len(line) >= 2 and line[0] == "[" and line[-1] == "]":
        items = split_top_level_items(line[1:-1])
        if bag:
            items = sorted(items)
        return "[" + " ".join(items) + "]"
    return " ".join(line.split())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bag", action="store_true")
    args = parser.parse_args()

    for line in sys.stdin:
      print(normalize_line(line, args.bag))


if __name__ == "__main__":
    main()
