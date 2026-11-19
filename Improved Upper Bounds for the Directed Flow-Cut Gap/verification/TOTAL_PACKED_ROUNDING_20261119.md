# Total packed rounding on the represented graph

The guarded driver follows the cached store until it halts or sees an
empty tape at a request. An accessibility proof for the represented graph
uses the actual finite controller trace. Lean erases that proof before
execution, so the positive-level branch runs directly with the prepared
state. The reference fuel bound remains in the agreement proof. The
zero-level fallback retains its previous behavior.

The total driver preserves the exact reference state, unread suffix and
model charges, including the terminal guard. The executable checks use a
request loop that exhausts a supplied tape and a direct zero-vertex call
to the original packed controller at positive level. The packed call
returns the same empty mask, the entire tape and the same recorded
charge. Earlier nonempty controller fixtures remain part of the
verification record.
