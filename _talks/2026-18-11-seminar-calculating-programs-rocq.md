---
layout: slide
title: "Hylomorphisms: From the Algebra of Programming to Certified Code"
venue: CS Seminar Series @ Royal Holloway, University of London
venueurl: https://rhul-cs-seminars.github.io
upcoming: false # shown as "Upcoming: <date>"; remove once given
date: 2026-11-18 # 13:00, Queens 240 (also streamed on Teams)
author: David Castro-Perez
description: 
# Shown on /talks/ as a collapsible [abstract]; Markdown, one paragraph per
# blank-line-separated block. Keep it here, not in the body (the slide
# layout renders the body as reveal.js slides).
abstract: |
  Can we calculate a program the way we solve an equation? Since the 1980s, *program calculation* (the "Squiggol" school of Bird and Meertens) has answered yes: efficient programs can be derived one algebraic law at a time. This talk explores *hylomorphisms*, a single algebraic pattern behind divide-and-conquer computations, how their laws have traditionally been used for program calculation, and the benefits of their mechanisation in proof assistants. I will present our Rocq library of hylomorphisms, which is fully axiom-free and checks every calculation step. Building it required carefully considering the trade-offs between definitions that are easy to reason about and definitions that extract to clean code. I will finish with ongoing work towards low-level program calculation, based on laws that change how data is represented and how work is scheduled.
comments: true
latex: 'tex/2026-hylos-general'
sources: 'tex/2026-hylos-general'
tags:
  - rocq
  - hylomorphisms
  - program calculation
  - code extraction
---
