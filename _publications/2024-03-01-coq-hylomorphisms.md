---
title: "Mechanising Recursion Schemes with Magic-Free Coq Extraction"
collection: publications
authors: "David Castro-Perez, Marco Paviotti, and Michael Vollmer"
permalink: /publication/2024-03-20-coq-hylomorphisms
year: 2024
venue: 'ITP'
pages: ''
submission: true
paperurl: 'files/2024-coq-hylos.pdf'
---

Generic programming with recursion schemes provides a powerful abstraction for
structuring recursion while ensuring termination and providing reasoning about
program equivalences as well as deriving optimisations which has been
successfully applied to functional programming. Formalising recursion schemes
in a type theory offers additional termination guarantees, but it often
requires compromises affecting the resulting code, such as imposing performance
penalties, requiring the assumption of additional axioms, or introducing unsafe
casts into extracted code (e.g. Obj.magic in OCaml).

This paper presents the first Coq formalisation to our knowledge of a recursion
scheme, called the hylomorphism, along with its algebraic laws allowing for the
mechanisation of all recognised (terminating) recursive algorithms. The key
contribution of this paper is that this formalisation is fully axiom-free
allowing for the extraction of safe, idiomatic OCaml code. We exemplify the
framework by formalising a series of algorithms based on different recursive
paradigms such as divide-and conquer, dynamic programming, and mutual recursion
and demonstrate that the extracted OCaml code for the programs formalised in
our framework is efficient, resembles code that a human programmer would write,
and contains no occurrences of Obj.magic.  We also present a machine-checked
proof of the well-known short-cut fusion optimisation.

