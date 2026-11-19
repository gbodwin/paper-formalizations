# Binary source serialization, fuel and terminal readback

`BinarySourceSerialization.run_value` checks the literal bits supplied to
the fixed physical dispatcher, including the order, rational padding and
repeated demands. One measured binary label scan is shared by the demand
fields. The serializer counts the framing work and charges for constructing
the source tables.

`BinarySourceFuel.fuel_value` identifies the computed fuel with one plus
the verified instruction polynomial at the actual packed length. The
polynomial coefficients are checked against the original bound in Lean.
The executable implementation uses measured binary arithmetic for Horner
evaluation.

`BinaryCoverReadback.readPlan_value` proves that the measured terminal
reader returns the same plan as the reference reader for every heap and
root. It charges validation of reached denominators, decoding of padded
rational fields and obstruction endpoints, and array construction. The
cached version reads the same store returned by the dispatcher.

`PhysicalSourceReadback.run_eq` connects all three phases to the existing
physical trace and the exact retained plan. The `readback` counter now
includes the source setup. The dispatch counter still pays for the executed
instructions and the terminal attempt. The composed vertex, edge and
adaptive polynomial proofs use the enlarged bound.

The execution cases include repeated ordered demands, padded source fields,
a retained 1/2 cover row, an obstruction, a mask and a rejected zero
denominator. The existing positive original-wire fixture exercises the
complete path on the three-vertex input. The theorem counts the specified
operations of the Lean model. The remaining structural envelopes and the
near-linear exact-original-weight form of Theorem 33 are separate obligations.
