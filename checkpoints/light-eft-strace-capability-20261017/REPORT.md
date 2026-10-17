# Installed strace and ordinary own-child tracing capability

Installed `/usr/bin/strace`, package `strace 6.13+ds-1`, SHA256 `69f88291a4e47f258b8e32b089c919a247509f063ef3d6afe5389939051102b3`; 2,189,792 bytes. The executable matches its installed package metadata checksum. No installation, replacement, credential, security or permission change was made.

The first package-wide check exited zero but reported six missing documentation/man files. Preparation initially stopped before any probe because of that output. The subsequent exact executable check established that the binary matches installed package metadata; missing documentation was not treated as a binary mismatch. All original output is retained in installed-tracer.json and binary-verification.json. This is installed-package reconciliation, not a claim of new external package-signature authentication.

Exactly one bounded harmless own-child probe then ran under the common lock. Its argv, explicit environment scope, configured caps and cleanup are in probe-receipt.json. It traced `/usr/bin/true`, not Lean. The probe exited **0**, with an empty probe-raw.log and a 1,986-byte [trace](harmless-child.trace). Reads are represented as addresses via `-e raw=read`; file contents were not dumped. Successful mapping records and decoded descriptor paths are visible.

The supervisor enabled subreaping, held common lock device 33/inode 3849 through cleanup, and verified all descendants gone and kernel ECHILD. Thus ordinary tracing of its own child is permitted in the current environment. No approval request, denial workaround or tracing escalation was needed.

The subsequent FiniteLaw diagnostic was refused by its unchanged memory gate before starting a tracer or Lean. See [diagnostic refusal](../light-eft-finitelaw-traced-20261017/REPORT.md). No traced Lean result or child-side errno is established by this capability test.
