# Physical adaptive controller from a represented cache

The fixed 15,323-slot controller takes a represented cache, static graph and scalar parameters, three stored unary control spines, and a literal fair tape.

- Cache installation shares the previous optimizer’s table and optimum pointers and allocates six cells, including two low zero bits for the scale.
- A failed ready test installs that cache and refreshes it from the live graph and masks. A successful ready test preserves the cache. The stabilization loop consumes the supplied restart spine.
- Each new epoch reads and trims the stabilized state’s actual current mass. It tests the exact optimum for zero before a draw. The epoch uses this snapshot as its threshold. The updated cache drives the next iteration.
- `ControllerTapeModel.tree_exact` identifies the outcome with the retained finite-draw controller under the tabulated optimizer and physical midpoint cut oracle. `physical_controller` joins the fixed instructions and the literal-tape interpretation, including the unread suffix and short-tape rejection. Its successful runs have explicit bounds on instructions, heap growth and modeled interpreter operations. The proof covers rejection during any scheduled epoch.
- The epoch allocation bound is independent of the entry heap size. The controller’s proof uses this bound across all iterations, with bounded stored row and scale widths.

The path fixture uses two available epochs and two stabilization steps per epoch. The first draw and scan cut the interior vertex. The controller refreshes the cache to zero and stops before drawing the second epoch. The two-bit suffix survives. The guarded program completes 13,772 instructions and charges 1,350,504,971 modeled operations. The guarded one-bit case rejects before the first scan.

The fixtures also exercise cached installation, a frozen current-mass threshold with padded input, zero and positive stabilization fuel, and the exact charged epoch with canonical candidate rows. The unready restart fixture runs the actual cache installation and reaches the physical candidate solver with the original labels, live masks and installed scale. It completes 253 instructions and charges 8,736,781 modeled operations before the solver’s first instruction. The separate prepared-candidate gate exercises the solver through completion.

This scope begins with a represented exact cache and parameter records. The original-input initialization, reductions, and a joined polynomial bit bound from the original stored input remain separate obligations.
