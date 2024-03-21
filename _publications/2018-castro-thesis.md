---
title: "Structured arrows : a type-based framework for structured parallelism"
collection: publications
authors: "David Castro-Perez"
permalink: /publication/2018-castro-thesis
year: 2018
venue: 'University of St Andrews, UK,'
paperurl: 'files/2018-castro-thesis.pdf'
---

This thesis deals with the important problem of parallelising sequential code.
Despite the importance of parallelism in modern computing, writing parallel
software still relies on many low-level and often error-prone approaches. These
low-level approaches can lead to serious execution problems such as deadlocks
and race conditions. Due to the non-deterministic behaviour of most parallel
programs, testing parallel software can be both tedious and time-consuming. A
way of providing guarantees of correctness for parallel programs would
therefore provide significant benefit. Moreover, even if we ignore the problem
of correctness, achieving good speedups is not straightforward, since this
generally involves rewriting a program to consider a (possibly large) number of
alternative parallelisations. This thesis argues that new languages and
frameworks are needed. These language and frameworks must not only support
high-level parallel programming constructs, but must also provide predictable
cost models for these parallel constructs. Moreover, they need to be built
around solid, well-understood theories that ensure that: (a) changes to the
source code will not change the functional behaviour of a program, and (b) the
speedup obtained by doing the necessary changes is predictable. Algorithmic
skeletons are parametric implementations of common patterns of parallelism that
provide good abstractions for creating new high-level languages, and also
support frameworks for parallel computing that satisfy the correctness and
predictability requirements that we require. This thesis presents a new
type-based framework, based on the connection between structured parallelism
and structured patterns of recursion, that provides parallel structures as type
abstractions that can be used to statically parallelise a program.
Specifically, this thesis exploits hylomorphisms as a single, unifying
construct to represent the functional behaviour of parallel programs, and to
perform correct code rewritings between alternative parallel implementations,
represented as algorithmic skeletons. This thesis also defines a mechanism for
deriving cost models for parallel constructs from a queue-based operational
semantics. In this way, we can provide strong static guarantees about the
correctness of a parallel program, while simultaneously achieving predictable
speedups.
