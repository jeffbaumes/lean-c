# Benchmark prompts

Replace `<task>` with a file name from `tasks/` and `<dir>` with a scratch directory. Each prompt goes to a fresh session; LC sessions get their own git worktree.

## C arm

> You are one run in a productivity benchmark. Write the C function specified in /Users/jeff/code/lean-c/bench/tasks/<task>.md, with unit tests, the way you would for production code you want to be confident in.
>
> Rules:
> - Work only in the directory <dir>/<task> (create it). Do not read or use anything else under /Users/jeff/code/lean-c except the task file.
> - The function goes in `<task>.c` (+ `<task>.h`): C11, only <stdint.h>/<stdbool.h>/<limits.h>, no libc, no allocation. Tests go in `test_<task>.c` and may use libc.
> - Build and run tests with e.g. `cc -std=c11 -Wall -Wextra -Werror -g -fsanitize=address,undefined <task>.c test_<task>.c -o t && ./t`.
> - Run EVERY compile/test command through the logger: `/Users/jeff/code/lean-c/bench/run.sh c-<task> <command...>`. It counts iterations.
> - You are done when you are confident the function is correct and all tests pass.
>
> Final report (keep it short): STATUS (done/partial); what the tests cover; number of compile/test iterations; any spec decisions or bugs you hit along the way.

## LC arm

> You are one run in a productivity benchmark. Write the function specified in /Users/jeff/code/lean-c/bench/tasks/<task>.md in LC, and establish its correctness with proofs instead of unit tests.
>
> You are in a fresh git worktree of the lean-c repo (your current directory). Setup and rules:
> - First run `cp -Rc /Users/jeff/code/lean-c/.lake .` in the worktree root (a prebuilt build directory; a cold build is slow). Then read CLAUDE.md and follow the lc-program skill (.claude/skills/lc-program/SKILL.md) and the "Adding a function to the project" steps 1–3 in CLAUDE.md. Do not edit README.md, docs/ or TODO.md.
> - Run EVERY lake / lc / lean / cc command through the logger: `/Users/jeff/code/lean-c/bench/run.sh lc-<task> <command...>`. It counts iterations. Use `nice -n 19` for difftests.
> - Avoid changing the LC/ library; if you must add a general lemma or tactic there, keep it small and list it in your report.
> - Done = the correctness theorem is proved (no sorry, no native_decide, no new axioms) and `lake exe lc check Examples.<Name>` says PASS. Then commit your work on the current branch (one commit).
> - If after about 300 tool calls you are still not done, stop, commit what you have on the branch, and report it as partial with what is left.
>
> Final report (keep it short): STATUS (done/partial); the main theorem statement(s), pasted; branch name and commit; number of check iterations; library changes, if any; the top 3 things that cost you the most iterations, and what tooling or docs would have removed them.
