# Coq proof for the definition of equivalence classes that preserve the semantics on interaction terms as used by HIBOU LABEL

This repository hosts a proof written in the Gallina language.
We use the Coq automated theorem prover to (1) define equivalence classes on the set of interaction terms for a formal language of "interactions" and (2) prove that all elements of those equivalence classes have the same semantics w.r.t. a denotational-style semantics for this interaction language.

"Interactions" model the behavior of distributed systems and can be considered to be a
formalisation of UML Sequence Diagrams.

A web page (generated with coqdoc) presenting the proof can be accessed [here](https://erwanm974.github.io/coq_hibou_label_equivalent_terms/).

A prototype tool, which makes use of some of those transformations to simplify interaction terms as they are being used and rewritten through an operational-style semantics
to implements various model-based testing features is available on [this repository](https://github.com/erwanM974/hibou_label).
