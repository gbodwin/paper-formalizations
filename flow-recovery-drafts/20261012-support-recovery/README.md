# Draft checkpoint: physical support search and costed recovery

This is a durable progress backup, outside the production library. It adds no production imports or workflow targets.

Exact full-CI baseline: 9d1487be5b694153735305915582fdb8f0b18344 (Flow172). All inherited repository bytes are preserved.

The 35 reconstructed modules have fresh strict Lean 4.34.0 checks with autoImplicit=false and warningAsError=true, plus ten concrete support-search interpreter fixtures and ten complete costed-recovery interpreter fixtures. The 280-slot support search refines the literal retained-search recurrence; the 592-slot program consumes its actual result, projects index words, materializes costs and returns the exact original recovered candidate on the same paid lower-machine run. Exact heap/representation and initial width bounds remain explicit.

Independent review is pending: the peer has read the first 15 of the 20 trace modules without a finding, but has not issued a verdict. The eight refinement/bounds and seven cost-composition modules are also pending review. Production/root audits, official module replays and full aggregate CI have not been run for these drafts. The commit deliberately skips CI because the unchanged parent workflow does not test this isolated directory.

The only byte-identical recovered original unpushed file is SupportSearchInvariants.lean, SHA256 3a80083adc1cbbcbc39867ca0b5ec4e3f65807191a8d031c3ecdf3614930dbbe. The other files are newly reconstructed or newly written and freshly checked.

Next: actual minimizer-to-recovery composition, then demand collection and the outer packing/controller/fuel execution. Raw graph preparation and the whole-paper physical runtime remain unfinished.

Each source and its successful strict log/receipt is included. The three freeze manifests record exact hashes. Shared toolchain reconstruction used official Lean 4.34.0 and mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.
