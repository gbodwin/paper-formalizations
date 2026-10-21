# Privileged-startup correction: source review only

This compact additive checkpoint preserves d3ab441d7698f93248a0011d2ba996219b5a79a2
and its earlier bundle. No production file, workflow, proof, gate or limit is
modified. `PROPOSED.patch` is an unapplied, zero-context diff for later review
against the exact production base. Its two proposed destinations are the global
replay script and that step's shell/run fields in `.github/workflows/lean.yml`.

The earlier proposal was unsafe: imported Bash functions named `exec` or
`command` can return success without launching the intended checks. `hash`,
`printf`, `exit`, `set` and other shell commands also need an explicit startup
contract. Merely checking BASH_ENV/ENV or writing `builtin` does not establish
that contract, since a function may replace the inspection command itself.

## Enforced launch contract

The workflow change and script change are inseparable:

1. The runner starts the step through the custom shell template
   `/bin/bash --noprofile --norc -p -e -o pipefail {0}`.
2. Its fixed step body starts the replay script with the absolute command
   `/bin/bash --noprofile --norc -p -e -o pipefail scripts/KernelCheck.sh`.
3. The script runs the single Lake environment setup and starts its loop through
   `/bin/bash --noprofile --norc -p -euo pipefail -c ...`.

In each case `-p` is supplied when the process is created, before script code
or imported functions can run. This is a Bash startup setting, with no OS
permission elevation. The script also has `#!/bin/bash -p` for direct executable
invocation. Its first command is reserved `case` syntax; the unsupported mode
arm contains reserved arithmetic returning failure and never enters the loop.

The mode check is only secondary evidence. It is **not proof of privileged
startup**: an unprivileged process can import functions and subsequently enable
the option through inherited SHELLOPTS. A negative-control model demonstrates
that forgery. Arbitrary `bash FILE` invocation is outside the accepted contract,
even if `$-` later contains `p`. Static source checks require the literal runner,
script and inner-shell startup arguments; late `set -p`, a missing flag or a
default shell cannot qualify. Future integration must bind the complete workflow
and script bytes through the existing exact-source machinery. A script-only
integration is rejected by this proposal.

GNU documents privileged startup as suppressing imported functions and startup
hooks. Consequently outer `set`, `printf`, `exit`, `exec` and Lake lookup run in
a function-free shell. The inner shell also starts with `-p`, so `hash` and
`command` are genuine builtins and `command_not_found_handle` cannot be imported
to suppress a missing checker. No accepted code defines functions, sources
files, evaluates code, installs traps or enables aliases. Assignments and quoted
parameter expansion remain data; `case`, `if`, `[[ ]]`, `for`, `in`, `do`, `done`
and `esac` are shell syntax. Every invoked command and builtin is listed in
`PLAN.json`, rather than relying only on protecting the name `leanchecker`.

The [GNU set reference](https://www.gnu.org/software/bash/manual/html_node/The-Set-Builtin.html)
and [GitHub custom-shell documentation](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#jobsjob_idstepsshell)
support those startup and runner-template semantics. The review artifact records
that full GNU-page retrieval was unavailable; its indexed primary result was
available. Runner v2.338.0 `ScriptHandler.cs` was retrieved and Git-blob verified:
it passes the parsed executable and arguments separately to StepHost execution.
The same runner version appears in the preserved cancelled-run log. Host Bash
5.2.37, identified by exact executable hash, is used only for offline shell models;
this does not qualify a future CI runner or Lean execution.

## Coverage, failures and remaining qualification

The original immutable environment proposal is retained: one Lake setup, all
567 ordered, fresh, sequential official checker processes, and all existing
kernel/declaration/axiom/full/focused/exact-commit requirements. The accepted
no-writer/configuration/toolchain-change assumption remains necessary. No result
cache, imported-kernel-environment reuse, aggregate-prefix replacement, added
job, deadline reset or resource increase is introduced. Both 120-minute job caps
and every child limit remain unchanged.

Adversarial models cover each invoked primitive separately, all imported
functions together, functions introduced after Lake setup, startup hooks, and
the full 567 target inventory. The fake checker runs under a hermetic PATH with
no actual Lean executable. Missing and non-executable checker files must yield
127/126 despite an imported command-not-found handler. Ordinary exits 37/126/127,
SIGTERM and SIGKILL must propagate failure with no successor checker launches.
Controls reproduce the earlier `exec`, `command` and missing-command-handler
false successes. No model success is reported as kernel verification.

Runtime PATH/LEAN_PATH/executable equivalence, actual savings and fit in the
unchanged envelope remain unmeasured. All 36 mathematical bodies remain
unelaborated. The previous physical-attempt allowance is consumed. This turn
does not integrate, compile, push or launch CI. Sequential independent review
of this correction is next; any later native measurement or attempt requires
separate explicit bounded authorization. Fast remains off.
