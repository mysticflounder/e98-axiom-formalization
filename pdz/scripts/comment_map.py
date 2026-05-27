#!/usr/bin/env python3
"""Map Lean 4 block-comment structure of a file, deterministically.

Lean block comments open with `/-` and close with `-/` and NEST. Docstrings
`/--` and module docs `/-!` are block-comment variants (also closed by `-/`).
A line-comment `--` runs to end of line and does not open a block.

We scan character by character (no regex), tracking nesting depth and the
"kind" of the outermost open comment (plain `/-`, doc `/--`, module `/-!`).
We then report maximal top-level comment regions, classified by kind, and the
line ranges of code that is ACTIVE (depth 0, outside any block comment).
"""
import sys

def scan(text):
    i, n = 0, len(text)
    line = 1
    # stack of (kind, open_line); kind in {'plain','doc','mod'}
    stack = []
    regions = []  # (kind, start_line, end_line) for top-level comments
    cur_start = None
    cur_kind = None
    in_line_comment = False
    while i < n:
        c = text[i]
        if c == '\n':
            line += 1
            in_line_comment = False
            i += 1
            continue
        if in_line_comment:
            i += 1
            continue
        # are we inside a block comment?
        if stack:
            # look for nested open or close
            if c == '/' and i + 1 < n and text[i+1] == '-':
                # nested open; classify
                third = text[i+2] if i + 2 < n else ''
                kind = 'doc' if third == '-' else ('mod' if third == '!' else 'plain')
                stack.append((kind, line))
                i += 2
                continue
            if c == '-' and i + 1 < n and text[i+1] == '/':
                stack.pop()
                i += 2
                if not stack:
                    regions.append((cur_kind, cur_start, line))
                    cur_start = None
                    cur_kind = None
                continue
            i += 1
            continue
        # not in a block comment
        if c == '-' and i + 1 < n and text[i+1] == '-':
            in_line_comment = True
            i += 2
            continue
        if c == '/' and i + 1 < n and text[i+1] == '-':
            third = text[i+2] if i + 2 < n else ''
            kind = 'doc' if third == '-' else ('mod' if third == '!' else 'plain')
            stack.append((kind, line))
            cur_start = line
            cur_kind = kind
            i += 2
            continue
        i += 1
    if stack:
        regions.append((cur_kind or 'plain', cur_start, line, 'UNCLOSED'))
    return regions

def main():
    path = sys.argv[1]
    with open(path) as f:
        text = f.read()
    total_lines = text.count('\n') + 1
    regions = scan(text)
    print(f"file: {path}  ({total_lines} lines)")
    print("\n== PLAIN block-comment regions (candidate dead/quarantined code) ==")
    dead_lines = 0
    for r in regions:
        kind = r[0]
        if kind != 'plain':
            continue
        start, end = r[1], r[2]
        span = end - start + 1
        if span >= 5:  # only sizeable blocks
            dead_lines += span
            tag = ' '.join(r[3:]) if len(r) > 3 else ''
            print(f"  lines {start:>5}-{end:<5}  ({span} lines) {tag}")
    print(f"\n  total lines in sizeable PLAIN blocks: {dead_lines} / {total_lines}")
    print("\n== count of doc/module-doc regions ==")
    docs = sum(1 for r in regions if r[0] == 'doc')
    mods = sum(1 for r in regions if r[0] == 'mod')
    print(f"  doc (/--): {docs}   module (/-!): {mods}")

if __name__ == '__main__':
    main()
