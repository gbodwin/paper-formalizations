# Source argument and author review

Status: author's sequential mathematical/source inspection only. The new Lean
module has not been elaborated, resolved, audited or replayed. Parent independent
review is pending. No models or static checks count as a Lean result.

1. Let O be the same `(univ : Finset (Sym2 (Fin n))).toList` used by accepted
   StoredFlagSample.entries and typed. rawKeys maps each O entry to the literal
   natural endpoint pair, while responses maps that same entry to its supplied
   Boolean value. The two lengths agree. List.zip_map' gives the exact ordered
   entries list, retaining false responses and every cell. Nothing filters the
   inputs before the serializer.

2. PaidFlagSerialization.execute_eq therefore returns those exact entries.
   StoredFlagSample.execute_eq and execute_encoded identify the filter's value
   with StoredEdges.encode (StoredFlagSample.typed bits). The existing composed
   full_trace and execute_eq provide the operational trace and exact returned
   encoded list. Rewriting rawKeys_length yields the local 5U+5 bound without
   changing the accepted machine, transition system or cost statement.

3. Apply the local theorem independently to bits p j i. The returned raw rows
   have a concrete typed witness, namely StoredFlagSample.typed (bits p j i).
   Its edge set equals BernoulliFlags.selected (bits p j i), which is definitionally
   decodeHost (bits p) j i. This uses the established typed_edgeSet theorem,
   rather than assuming that some caller-supplied representation matches a law.

4. storedHost packages those exact typed witnesses' edge sets. Pointwise
   extensionality proves storedHost = decodeHost. storedAssignment uses the
   identical dependent List.rec structure as accepted decodeAssignment: empty
   assignment initially, decode the tail using p.succ, then update the head key
   with coordinate 0. Induction substitutes the tail equality and host equality.
   Thus storedAssignment = decodeAssignment for every supplied tensor, including
   empty lists, repeated keys and empty host/repetition dimensions. In particular,
   Function.update_self yields the head-wins rule. Equality also inherits the
   decoder's empty assignment outside visited candidate keys.

5. Rewrite storedAssignment to decodeAssignment inside any assignment predicate
   P and apply accepted decoded_assignment_probability. The underlying law is
   still jointSourceLaw, and all its occurrence-indexed independence and bias
   content comes from its existing literal product definition. No probability
   statement about a new generator, flattened list or seed is introduced. The
   canonical actual-output failure predicate is one permissible P, with all
   hypotheses of that existing corollary retained when using its bound.

Source checks consulted the pinned Lean 4.34.0 List.zip_map' statement directly.
Other theorem names and definitions are bound to their accepted source files.
The Classical.propDecidable attribute matches the accepted decoder context for
Function.update. The dependent recursion keeps candidate positions distinct;
no candidate-list nodup premise or key deduplication is added.

The author review checked that the trace starts with already supplied lists,
that all finite-set interpretations and the assignment fold are explicitly
mathematical, and that no probability claim changes the source distribution.
It also identified the outstanding literal-bank/canonical-bank distinction in
UNRESOLVED.md. These inspections do not establish Lean elaboration success.
