# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

This is an **Isabelle/HOL theorem proving** project. The `.thy` files are Isabelle theory files for formal mathematical proofs.

## Working with Isabelle

Run a theory file or build the project:
```bash
isabelle build -D .
```

Check a single theory interactively:
```bash
isabelle jedit Sqrt2.thy
```

## Finding Facts

Use `./find-facts` to search the loaded Isabelle session index. This is the primary way to discover lemmas, definitions, and theorems relevant to a proof goal.

**Default behaviour (no `--field`):** searches across source text, names, theory, and session simultaneously — like Isabelle's `find_theorems`. This is the right starting point for most queries.

**Common search patterns:**

| Goal | Command |
|---|---|
| Find anything about a concept | `./find-facts "prime"` |
| Find a lemma by (partial) name | `./find-facts "prime_dvd_power"` |
| Find lemmas using a specific constant | `./find-facts --field consts --exact "Factorial_Ring.prime"` |
| Look up a theorem by exact qualified name | `./find-facts --field names --exact "NthRoot.real_sqrt_mult"` |
| Find `[simp]` rules about a concept | `./find-facts --field source "simp.*sqrt"` |
| Restrict to a session | `./find-facts --session HOL-Analysis "norm"` |
| Only lemma/theorem commands | `./find-facts --command lemma "prime"` |
| Fetch full source of a block by id | `./find-facts --id "<id from previous result>"` |

**Workflow for proof search:**
1. Start with `./find-facts "keyword"` to get an overview across all sessions.
2. Narrow with `--session`, `--command lemma`, or `--field` as needed.
3. Use `-n 20` or `-p` / `--cursor` to page through results.
4. Once you find a candidate, use `--id` to see its full context (`src_before`, `src_after`).

**Field reference:** `source` (full-text), `names` (constants/types/thms used), `consts`, `typs`, `thms`, `session`, `theory`, `command`, `chapter`, `file_type`

The server must be running: `isabelle find_facts_server -p 8080 -v`

To index additional sessions (e.g. after building them): `isabelle find_facts_index -n SESSION_NAME`

Currently indexed sessions: HOL, HOL-Library, HOL-Analysis, HOL-Computational_Algebra, HOL-Algebra, HOL-Number_Theory

## AutoSh / sh proof method

`AutoSh` is a local theory (imported as `AutoSh`) that defines the `sh` proof method.

**What it does:** runs one ATP prover (same backend as `sledgehammer_with_metis_tac`), then tries the found facts with `metis → simp → auto` in order. On success it appends one line to `/tmp/isabelle_sh_results.txt`:
```
<file>:<line> | <goal (first 80 chars)> | by (metis ...) / by auto / ...
```

**IMPORTANT — use at most ONE `by sh` per build.** Multiple simultaneous ATP calls compete for the same prover process and can block each other. Always build with a single `by sh`, extract the tactic, then add the next one.

**Proving power:** slightly weaker than interactive `sledgehammer` (which runs multiple provers in parallel and does fuller preplay). If `sh` fails, try adding more `using` hints before it.

**Skill: filling a gap with sh**

Use this workflow for each `sorry` you want to fill:

1. Replace ONE `sorry` (or write the structured proof step) with `by sh`.
2. Run `./sh_fill.sh <file> <line>` — it will:
   a. Build (sh records the found tactic to `/tmp/isabelle_sh_results.txt`)
   b. Replace `by sh` at `<file>:<line>` with the found tactic
   c. **Rebuild to verify** the replacement actually works (catches looping `metis` etc.)
   d. Revert if verification fails

Manual steps if needed:
```bash
rm -f /tmp/isabelle_sh_results.txt
isabelle build -D . -o timeout=60    # -o timeout catches looping tactics
cat /tmp/isabelle_sh_results.txt     # <file>:<line> | <goal> | <tactic>
```

**Always rebuild after replacing `by sh`** — the recorded tactic may loop or fail
(e.g. `metis` can loop on certain goals even if the ATP found the facts).

```bash
./sh_fill.sh EnestromKakeya.thy 42   # find, replace, and verify line 42
./sh_fill.sh                         # build only, show results
```

**When NOT to use sh:**
- Goals involving exotic constants outside the indexed sessions (will time out).
- Goals that require induction or complex multi-step reasoning (sh only closes single goals).
- More than one gap at a time.

## Isabelle Conventions

- `sorry` marks an unproven lemma — it is accepted by Isabelle but signals incomplete work.
- `Complex_Main` is the standard import for real/complex analysis; use it when working with `sqrt`, `Rats`, or related types.
- Unicode symbols like `\<notin>` render as `∉` in the IDE.
