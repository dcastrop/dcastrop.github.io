---
layout: archive
title: "CV"
permalink: /cv/
author_profile: true
redirect_from:
  - /resume
---

{% include base_path %}

<!-- NOTE: this page is deliberately hidden from the navigation (see
     _data/navigation.yml) until the TODOs below are filled in. It is still
     reachable at /cv/. -->

Current position
======
* Lecturer, Department of Computer Science, Royal Holloway, University of London
  <!-- TODO: start date -->

Previous positions
======
* Lecturer (Assistant Professor), School of Computing, University of Kent,
  2021&ndash;<!-- TODO: end date -->
* Research Associate, Imperial College London, Mobility Reading Group
  <!-- TODO: dates -->

Education
======
* Ph.D. in Computer Science, University of St Andrews, 2018.
  Thesis: [_Structured arrows: a type-based framework for structured
  parallelism_](/publication/2018-castro-thesis)
<!-- TODO: earlier degrees -->

Software
======
* [rocq-hylomorphisms](https://github.com/dcastrop/rocq-hylomorphisms):
  axiom-free hylomorphisms in Rocq, with idiomatic code extraction (ITP 2025)
* [Zooid](https://github.com/emtst/zooid-cmpst): certified multiparty session
  types and processes in Coq (PLDI 2021)
* [GoScr](https://github.com/dcastrop/goscr-benchmarks): Go code generation for
  dynamically updatable multiparty session protocols, with benchmarks (ECOOP 2023)

Publications
======
  <ul>{% for post in site.publications reversed %}
    {% include archive-single-cv.html %}
  {% endfor %}</ul>
  
Talks
======
  <ul>{% for post in site.talks reversed %}
    {% include archive-single-talk-cv.html  %}
  {% endfor %}</ul>
  
Teaching
======
  <ul>{% for post in site.teaching reversed %}
    {% include archive-single-cv.html %}
  {% endfor %}</ul>
  
<!-- TODO: Service and leadership (PC memberships, reviewing, organisation) -->
