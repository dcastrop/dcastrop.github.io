---
layout: archive
title: "Research"
permalink: /research/
author_profile: true
redirect_from:
  - /research
  - /research.html
---

{% include base_path %}

My [ongoing research projects](#ongoing-research-projects) are listed at
the end of this page.

# Research Areas

## Session Types

Multiparty session types (MPST) describe the communication protocols of
concurrent and distributed systems as types, and guarantee that well-typed
programs are free from deadlocks and communication errors. My work on session
types covers:

* **Expressive and compositional theories.** The _synthetic_ approach to MPST
  [(POPL 2026)](/publication/2026-popl-synthetic) checks each process directly
  against a global protocol, given as a labelled transition system, with no
  projection or local types. It is mechanised in Agda.
* **Protocols with dynamic participants.** Role-parametric session types for
  Go [(POPL 2019)](/publication/2019-popl-distributed) and dynamically
  updatable protocols with unbounded participants
  [(ECOOP 2023)](/publication/2023-ecoop-dynamically).
* **Cost and performance.** CAMP [(OOPSLA 2020)](/publication/2020-oopsla-camp)
  is a static performance analysis for message-passing systems built on MPST.

## Interactive Theorem Proving

I build mechanised metatheory and certified tools in proof assistants, mostly
Rocq (formerly Coq):

* **Mechanised session types.** EMTST
  [(TACAS 2020)](/publication/2020-tacas-emtst) is a library for the
  metatheory of session type calculi. Zooid
  [(PLDI 2021)](/publication/2021-pldi-zooid) is a Coq-embedded language for
  certified multiparty communication, built on a mechanisation of asynchronous
  MPST. I also contributed to the
  [Concurrent Calculi Formalisation Benchmark](/publication/2024-coordination-benchmark)
  (COORDINATION 2024).
* **Recursion schemes and program calculation.** An axiom-free formalisation
  of hylomorphisms in Rocq [(ITP 2025)](/publication/2025-itp-hylomorphisms),
  whose laws are used to calculate efficient programs that extract to safe,
  idiomatic OCaml.

## Parallel Programming Frameworks

Structured parallelism gives correctness by construction; the hard part is
choosing a parallel structure that achieves good speedups. I have used
hylomorphisms to reason about both the semantics and the cost of structured
parallel programs [(ICFP 2016](/publication/2016-ifcp),
[FGCS 2018)](/publication/2018-fcgs-automatically), the subject of my
[PhD thesis](/publication/2018-castro-thesis). PAlg
[(CC 2020)](/publication/2020-cc-compiling) compiles first-order functions to
message-passing parallel code that is deadlock-free by construction, using
multiparty session types.

# Ongoing Research Projects

* **Hylomorphisms in Rocq.** A library of terminating hylomorphisms and their
  laws, for program calculation with idiomatic code extraction.
  Code: [dcastrop/rocq-hylomorphisms](https://github.com/dcastrop/rocq-hylomorphisms).
  Talk: [Program Calculation with Hylomorphisms in Rocq](/talks/).
* **Synthetic multiparty session types.** Compositional verification of
  processes directly against global protocol specifications
  ([POPL 2026](/publication/2026-popl-synthetic)), with Francisco Ferreira
  and Sung-Shik Jongmans.
