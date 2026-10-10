# Recovered reference simulation diagnostic

This separate branch tests exact recovered source be2085ab3a8633f472b3fef60b04d856206c94e9e9983c84dca4148ce7bf95aa. It is not included in the promoted paper index. No Lean success is claimed by publication: the source has never passed fresh compilation. CI checks its source closure, builds and strictly rechecks the new module, runs four recovered executable fixtures, audits all owned declarations in the imported closure, and replays that closure through the Lean kernel.

The source models bounded-arity immutable cells using explicit binary words and conservative sequential list copying. Its central result bounds supplied successful instruction prefixes in the chosen Boolean/list cost model. Terminal failed/halt-operation charges, transient implementation storage, physical pointer allocation, fixed-program embeddings, random-source distribution, and integration with the flow-cut algorithm remain separate obligations. Valid store properties require their explicit validity premise.

This branch intentionally uses a targeted diagnostic workflow. It does not replace the independent 193-component full-project runtime gate or claim verification of the 251-component draft integration.

## First fresh compiler result

CI 38054380346 rejected the recovered source during elaboration (no runtime/audit/kernel success). The successor repairs definitional unfolding, a Boolean branch split, an explicit copy-cost hypothesis normalization, implicit cell inference, a reserved binder name, and strict-linter warnings. All computational definitions and theorem conclusions are preserved. Fresh CI remains required.
