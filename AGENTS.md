# AGENTS.md — working conventions for the `crossing-lemma` project

This file orients automated agents (and humans) working in this repository.
Read it before editing.

## What this project is

A self-contained Lean 4 / Mathlib formalization of the **multigraph crossing
lemma** (Székely / Ajtai–Chvátal–Newborn–Szemerédi). It exists to be *imported*
— principally by the sibling `pdz` project — so its public surface and its
dependency footprint both matter.

## Invariants — do not violate

1. **Mathlib-only.** This project depends on Mathlib and nothing else. Never add
   a dependency on any problem-specific or application library (no `Erdos98Proof`,
   no `pdz`, no distinct-distances code). The crossing lemma is pure graph
   combinatorics; if a proof here seems to *need* something problem-specific,
   the proof is structured wrong — fix the structure, don't add the dependency.
2. **Toolchain pin.** `leanprover/lean4:v4.27.0`, `mathlib @ v4.27.0`. These must
   stay in lockstep with the `pdz` consumer so the cross-project `require` is
   binary-compatible. Do not bump one without the other.
3. **Vendored as written.** The proof was brought in from a larger effort. Edits
   to date are mechanical only (namespace de-prefixing, import localization). Do
   not silently rewrite the mathematics; if a proof must change, say so.

## Scope discipline

In scope: the crossing inequality and the combinatorial-map / planar-Euler
machinery its proof rests on. Out of scope: anything else. Do not generalize,
add unrelated graph theory, or pursue tangents. A lemma that is not on the path
to the crossing inequality does not belong here.

There is at least one known exploratory lemma off the critical path (a
tower-construction `sorry` in `CrossingFreeEuler`) slated for removal — do not
build on it.

## Building & verifying

```bash
./lake-build.sh                       # full build (use this, not bare `lake build`)
./lake-build.sh CrossingLemma.Foo     # single module
lake exe cache get                    # (re)fetch Mathlib oleans after a clean
```

`lake-build.sh` injects a per-`lean` memory cap and a lockfile; respect it rather
than invoking `lake`/`lean` directly. After a green build, scan stderr for
`warning:` and triage immediately — do not let lint warnings accumulate.

## Conventions (Mathlib idiom)

- Schema names describe **mathematics, not tooling**: `crossingNumber`,
  `eulerChar_residualMap_ge_two` — never a tool/project name in a `def`/`theorem`.
- `snake_case` theorems, `camelCase` defs/structures; every public declaration
  gets a `/-- … -/` docstring; every file leads with a `/-! … -/` module doc.
- Files target ≤ ~500 lines; split past that. Keep the public surface small —
  expose the crossing-lemma statement + theorem; mark bookkeeping `private` or
  push it into an internal namespace.
- Authorship header (humans only — AI assistance is not authorship):
  ```
  /-
  Copyright (c) 2026 Adam McKenna. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Adam McKenna
  -/
  ```

## The contract with `pdz`

`pdz` imports the crossing inequality from here to discharge its incidence bound.
The stable surface is the frozen statement in `CrossingLemma/CrossingLemma.lean`
and its proof. Keep that statement's name and shape stable; coordinate any change
to it with the `pdz` side.

## Status pointer

`PLAN.md` holds the live frontier (open `sorry`s, the vendor/rename steps, the
axiom-surface pin). Consult it before claiming the proof is complete.
