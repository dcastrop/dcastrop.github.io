---
title: "Automatically deriving cost models for structured parallel processes using hylomorphisms"
collection: publications
authors: "David Castro-Perez, Kevin Hammond, Susmit Sarkar, Yasir Alguwaifli"
permalink: /publication/2018-fcgs-automatically
year: 2018
journal: 'Future Gener. Comput. Syst. 79'
pages: '653-668'
paperurl: 'files/2018-fcgs-automatically.pdf'
---

Structured parallelism using nested algorithmic skeletons can greatly ease the
task of writing parallel software, since common, but hard-to-debug, problems
such as race conditions are eliminated by design. However, choosing the best
combination of algorithmic skeletons to yield good parallel speedups for a
specific program on a specific parallel architecture is still a difficult
problem. This paper uses the unifying notion of hylomorphisms, a general
recursion pattern, to make it possible to reason about both the functional
correctness properties and the extra-functional timing properties of structured
parallel programs. We have previously used hylomorphisms to provide a
denotational semantics for skeletons, and proved that a given parallel
structure for a program satisfies functional correctness. This paper expands on
this theme, providing a simple operational semantics for algorithmic skeletons
and a cost semantics that can be automatically derived from that operational
semantics. We prove that both semantics are sound with respect to our
previously defined denotational semantics. This means that we can now
automatically and statically choose a provably optimal parallel structure for a
given program with respect to a cost model for a (class of) parallel
architecture. By deriving an automatic amortised analysis from our cost model,
we can also accurately predict parallel runtimes and speedups.
