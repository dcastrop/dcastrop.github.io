---
title: "EMTST: Engineering the Meta-theory of Session Types"
collection: publications
authors: "David Castro-Perez, Francisco Ferreira, Nobuko Yoshida"
permalink: /publication/2020-tacas-emtst
year: 2020
venue: 'TACAS(2)'
pages: '278-285'
paperurl: 'files/2020-tacas-emtst.pdf'
---

Session types provide a principled programming discipline for structured
interactions. They represent a wide spectrum of type-systems for concurrency.
Their type safety is thus extremely important. EMTST is a tool to aid in
representing and validating theorems about session types in the Coq proof
assistant. On paper, these proofs are often tricky, and error prone. In proof
assistants, they are typically long and difficult to prove. In this work, we
propose a library that helps validate the theory of session types calculi in
proof assistants. As a case study, we study two of the most used binary session
types systems: we show the impossibility of representing the first system in
α-equivalent representations, and we prove type preservation for the revisited
system. We develop our tool in the Coq proof assistant, using locally nameless
for binders and small scale reflection to simplify the handling of linear
typing environments.
