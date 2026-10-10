# Weighted-girth draft extension

This branch adds a proposed one-edge weighted-girth lower-bound transfer. It is pending compilation, all-declarations audit, and independent kernel replay through repository CI. Do not treat it as a verified result until the exact branch commit passes those checks.

The separately audited baseline is `6d98b7359b7885c96309d31aa1332aae596879a5` on `light-spanner-continuation`: 15 source modules, 213 declarations, targeted aggregate compilation and independent kernel replay passed. This draft adds a sixteenth module. The README and prior verification records describe that verified baseline, not a completed check of this extension.

Proposed scope: splitting any edge into two nonnegative pieces with the same total weight cannot decrease a nonnegative weighted-girth lower bound. Cycles avoiding the inserted vertex use the old-graph embedding; cycles through it contract through the original edge. No full-paper lightness claim is made. Repeated subdivision and tree/lightness transfer remain open.
