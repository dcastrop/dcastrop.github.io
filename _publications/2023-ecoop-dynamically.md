---
title: "Dynamically Updatable Multiparty Session Protocols: Generating Concurrent Go Code from Unbounded Protocols"
collection: publications
authors: "David Castro-Perez, Nobuko Yoshida"
permalink: /publication/2023-ecoop-dynamically
year: 2023
venue: 'ECOOP'
pages: '6:1-6:30'
paperurl: 'files/2023-ecoop-dynamically.pdf'
---

Multiparty Session Types (MPST) are a typing disciplines that guarantee the
absence of deadlocks and communication errors in concurrent and distributed
systems. However, existing MPST frameworks do not support protocols with
dynamic unbounded participants, and cannot express many common programming
patterns that require the introduction of new participants into a protocol.
This poses a barrier for the adoption of MPST in languages that favour the
creation of new participants (processes, lightweight threads, etc) that
communicate via message passing, such as Go or Erlang. This paper proposes
Dynamically Updatable Multiparty Session Protocols, a new MPST theory (DMst)
that supports protocols with an unbounded number of fresh participants, whose
communication topologies are dynamically updatable. We prove that DMst
guarantees deadlock-freedom and liveness. We implement a toolchain, GoScr
(Go-Scribble), which generates Go implementations from DMst, ensuring by
construction, that the different participants will only perform I/O actions
that comply with a given protocol specification. We evaluate our toolchain by
(1) implementing representative parallel and concurrent algorithms from
existing benchmarks, textbooks and literature; (2) showing that GoScr does not
introduce significant overheads compared to a naive implementation, for
computationally expensive benchmarks; and (3) building three realistic
protocols (dynamic task delegation, recursive Domain Name System, and a
parallel Min-Max strategy) in GoScr that could not be represented with previous
theories of session types.
