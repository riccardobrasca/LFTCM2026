# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

Workshop material for *Lean For The Curious Mathematician 2026*
(<https://amosturchet.github.io/lftcm26/index.html>) — a Lean 4 project that participants clone
and then work through in VS Code.

**The audience is beginners in Lean.** That single fact drives most of the decisions below: the
"product" is the source files people read and edit, so clarity of the exercise files and a
frictionless first-run experience matter more than elegance, brevity, or generality.

## The import invariant

**No file imports anything other than `Mathlib` and modules under `LFTCM2026.Preliminaries`.**
In particular, exercise files are imported by *nothing* — not by `LFTCM2026.lean`, not by each
other. (The single exception is the root `LFTCM2026.lean` itself, which also imports
`LFTCM2026.Test`, the installation check; see below.)

The reason is the participant experience, and it is worth protecting carefully. Everything an
exercise file imports is already compiled before anyone opens it: Mathlib comes from
`lake exe cache get!`, `Preliminaries` from `lake build`. So any exercise file opens instantly,
never shows the `Imports of '...' are out of date and must be rebuilt` popup, and never sets off a
rebuild — which is also what keeps Codespaces usable. The moment one participant-visible file
imports another, that guarantee is gone for everyone downstream of it.

The invariant buys a second thing: since nothing imports an exercise file, nothing compiles it
either. **Exercise files may contain as many errors, `sorry`s and warnings as you like.** That is
the intended state during the workshop, not a defect to clean up.

## The kinds of file

### Exercise files — participant-facing, one per talk/session

These are what beginners read during the conference. `LFTCM2026/1_BasicTactic.lean` is the model.

- **Imported from nowhere. Never add one to `LFTCM2026.lean`.** Nothing else in the repository may
  mention them.
- **May import only `Mathlib` and `LFTCM2026.Preliminaries.*`.**
- Free to be broken: errors, `sorry`s and warnings are all fine and expected.
- By convention they live in the `LFTCM2026/` source directory, which is what the README tells
  participants to open and what the VS Code explorer is set up to show. Nothing technical depends
  on the location — nothing imports them — so this is about the curated view, not the build.
- **Do not over-comment. There is a speaker in the room.** These files are used while someone is
  explaining them out loud, so the comments are a support for that talk, not a substitute for it.
  Say what a tactic does, what a piece of notation means, why a hypothesis is needed — then stop.
  Anything the speaker will say anyway, and anything the participant can read off the Infoview,
  does not need to be written down. A file drowning in prose is harder to follow along with than a
  sparse one.
  - The heavily commented first example of `LFTCM2026/1_BasicTactic.lean` is the right amount for a
    *first* contact with tactics, where every symbol is new. It is the ceiling, not the norm: for
    the rest of that file and for later sessions, comment noticeably more lightly.
  - When in doubt, cut. Err on the side of too little; the speaker fills the gap, and whoever
    writes the session can always add a line back.
- Prefer the readable proof over the short one, and prefer spelling a step out over a clever
  one-liner. Assume the reader has just met Lean.
- Keep the visible machinery minimal: anything technical, ugly, or off-topic that a session needs
  belongs in `Preliminaries` instead.

### `LFTCM2026/Preliminaries/*.lean` — hidden support code

Everything an exercise file needs but participants should not have to look at: missing instances,
setup, glue, custom notation, helper lemmas.

- **May import anything.** No restrictions.
- **Must compile cleanly.** This is the only code that is ever built, so a `sorry` or an error here
  breaks `lake build` for every participant. Errors are free in exercise files and expensive
  here — the exact opposite of the rule above.
- Imported only from `LFTCM2026/Preliminaries.lean`, the aggregator that re-exports the directory.
  Regenerate it rather than editing it by hand:

  ```
  lake exe mk_all --lib LFTCM2026/Preliminaries --module
  ```

- Import them from nowhere else.
- No obligation to be beginner-readable; ordinary code comments are enough.
- `.vscode/settings.json` hides this whole tree from the explorer, so participants never see it.

### `LFTCM2026/Test.lean` — the installation check

The file the README tells participants to open first, to confirm that their setup works (`#eval
2 ^ 5` should print `32`, and nothing in the file should be red). It is the one participant-facing
file that is *not* an exercise file:

- It imports `LFTCM2026.Preliminaries`, like everything else, and `LFTCM2026.lean` imports **it**.
- Because it is imported, it **must compile cleanly** — same rule as `Preliminaries`, opposite of
  the exercise files. A `sorry` or an error here breaks `lake build` for every participant, and
  would make the install check report a broken installation.
- It stays visible in the explorer, on purpose.

### `LFTCM2026.lean` — the library root

Contains exactly two lines:

```lean
import LFTCM2026.Preliminaries
import LFTCM2026.Test
```

Those two are fine, and nothing else belongs here. It is deliberately *not* an index of the
repository: adding an exercise file would pull a file that is allowed to be broken into the build
and defeat the whole arrangement above.

## Commands

```
lake exe cache get!    # download the pinned mathlib build (slow, several GB)
lake build             # build Preliminaries and Test (fast once the mathlib cache is in place)
```

`lake build` follows `LFTCM2026.lean`, so it builds `Preliminaries` and `Test`, and nothing else.
Exercise files are not part of it.

CI (`.github/workflows/lean_action_ci.yml`) runs `leanprover/lean-action@v1` with
`test: false, lint: false` on pushes to `master` only. There are no tests and no linter step, and by
construction no exercise file is compiled, so **a green CI means exactly "`Preliminaries` and
`Test` compile"** — it says nothing about the sessions. Exercise files are checked by whoever writes
them, in the editor.

**Do not run `lake build` or `lake exe cache get` yourself.** A build that misses the cache
recompiles mathlib and takes hours. Make the edit, say it is unverified, and let the user build.
To check a file without a full build, use the Lean LSP tools (`lean_diagnostic_messages`,
`lean_goal`) against the running language server — this works on exercise files too, even though
nothing ever builds them.

## Lean conventions in this repo

The project uses the **Lean 4 module system** (toolchain `v4.34.0-rc1`):

- Every file under `LFTCM2026/` begins with a bare `module` line, before the imports. The root
  `LFTCM2026.lean`, which is nothing but a list of imports, does not.
- `Preliminaries.lean` and the files under `Preliminaries/` use `public import`, so that what they
  import stays visible to the exercise files downstream. Exercise files, which nothing imports, use
  a plain `import`.

Source files carry the mathlib-style copyright header (Apache 2.0, `Authors:` line).

**Every tactic proof ends with `done`.** Write it as the last line of the block, at the same
indentation as the other tactics:

```lean
example : ... := by
  intro U hU
  exact hfgU
  done
```

It is redundant — the proof is already complete without it — and that is the point: for a beginner
it marks the end of the proof explicitly, and while editing it gives an error exactly when goals
are still open, instead of the mistake surfacing somewhere further down the file. The
`linter.unusedTactic` linter, which would otherwise warn "`done` does nothing" on every proof, is
off — see below. Add `done` to proofs you write, and do not delete the ones already there.

`lakefile.toml` sets `autoImplicit = false` and, deliberately, **`linter.all = false`**: no linter
of any kind — core or mathlib, present or future — fires in this project. The other `warn.*`
options are off too, with a single exception: `warn.sorry` stays on, so `declaration uses 'sorry'`
is the *only* warning a participant can ever see, and it means exactly "this exercise is still
open". Do not "fix" warnings these options turn off, and do not re-enable a linter to tidy
something up.

Formatting (enforced by `.vscode/settings.json`, not by a linter): 2-space indent, spaces not tabs,
100-column ruler, UTF-8, LF, final newline, no trailing whitespace.

## Participant-visible surface

Two files decide what a participant actually encounters, and both need a thought when adding
material:

- `.vscode/settings.json` `files.exclude` hides from the VS Code explorer everything participants
  have no business opening — build output, project plumbing, `.github`, `.claude`, `img`,
  `CLAUDE.md`/`AGENTS.md`, `README.md`, and the whole `Preliminaries` tree. Markdown is not hidden
  as a class, though: the exercise sheet `Exercises.md` is listed nowhere and is meant to be
  visible. A new file that participants should not see goes on that list.
- `README.md` is the installation and troubleshooting guide participants follow. It is in good
  shape; leave it alone unless the workflow it describes actually changes.

Note that the repository root and the source directory are both called `LFTCM2026`, so the path of
an exercise file looks doubled (`LFTCM2026/LFTCM2026/1_BasicTactic.lean` from outside the project).
That is correct, and it is the same confusion the README warns participants about when they open
the wrong folder in VS Code.

## Mathlib version

`lake-manifest.json` pins mathlib to an exact revision. Bumping it invalidates every participant's
downloaded cache and forces a fresh multi-GB `lake exe cache get!`, so treat a mathlib bump as a
deliberate, announced change rather than routine maintenance.
