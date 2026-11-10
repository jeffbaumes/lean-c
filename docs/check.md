# `lc check`: one command for "is this module done?"

`lake exe lc check <module> [cases]` builds one module and prints a short summary. It's meant as the inner loop for writing a verified function, whether a person or an agent is writing it. One command answers "does it type-check, do the tests pass, are the proofs complete, and does the C agree with the interpreter?"

```bash
lake exe lc check Examples.SpecFirst          # or: lake exe lc check Examples/SpecFirst.lean
```

```
lc check Examples.SpecFirst
  build     ok    0.2s
  #guard    ok    12 passed
  proofs    ok    5 theorems
  axioms    ok    1 checked, standard only
  hygiene   ok    no sorry / admit / native_decide / axiom
  difftest  ok    is_sorted: 30 random cases each, C (UBSan/ASan, -O2) vs. interpreter
PASS
```

On failure it adds a `problems:` section with each error's position and the first lines of its message, and exits 1.

## The rows

| Row | Passes when | How |
|---|---|---|
| `build` | `lake build <module>` succeeds | its messages are split between the next two rows |
| `#guard` | no `#guard` fails (type checks, interpreter runs, reference property tests) | errors reading "did not evaluate to `true`" |
| `proofs` | no other error, and no "declaration uses `sorry`" warning | |
| `axioms` | every `#print axioms` in the file lists only `propext`, `Classical.choice`, `Quot.sound`. A file with theorems but no `#print axioms` fails | parses the `info:` lines |
| `hygiene` | no `sorry`, `admit`, `native_decide` or `axiom` in the source, outside comments and strings | token scan |
| `difftest` | the module's functions in `Tests/Suite.lean` pass `cases` random inputs (default 30) under UBSan/ASan and `-O2` | `nice -n 19 lake exe lc difftest <cases> 1 --module <module>` |

The difftest runs only after every other row passes, because it needs the whole suite to build. A module with no suite functions (proofs only, like `Examples.Auto`) shows `skip`. If the file seems to define an `Fn`, the `skip` line also says to add it to `difftestFns`. `cases = 0` skips the difftest.

## Two executables

`lc` itself imports nothing from the project. If it imported the examples, a broken proof in the module being checked would stop `lc` from building, and `check` could never report on it. So `check` runs `lake build` as a subprocess and reads its messages. `emit`, `difftest` and `ringtest` need every example function, so they live in a second executable, `lc-suite` ([Tools/Suite.lean](../Tools/Suite.lean)), and `lc` forwards them to it.

Each `Tests/Suite.lean` entry is written `suite_entry% Examples.Foo.foo`. The macro records the declaring module at elaboration time, which is how `--module` selects functions.

## Cost

With the module already built, everything except the difftest takes about a second, because Lake replays the cached messages. The 30-case difftest adds 10–25 s, mostly C compilation. After an edit, the time is dominated by re-elaborating the module's proofs, as with `lake build`.

## Limits

- Counts come from a token scan, so a `#guard` produced by a macro isn't counted, and "passed" means "present and not reported as failed".
- When elaboration stops early (a parse error), later `#guard`s and proofs aren't run, and the rows can't tell you about them.
- Errors in imported modules are listed, but `check` doesn't separate them from errors in the module itself.
- The axiom check covers only the theorems that have a `#print axioms`. The hygiene scan is the backstop.
