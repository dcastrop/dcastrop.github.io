---
layout: archive
title: "Publications"
permalink: /publications/
author_profile: true
---

{% if site.author.googlescholar and site.author.dblp %}
  <div class="wordwrap">You can also find my articles on <a href="{{site.author.googlescholar}}">my Google Scholar profile</a> and <a href="{{site.author.dblp}}">DBLP</a>.</div>
{% elsif site.author.googlescholar %}
  <div class="wordwrap">You can also find my articles on <a href="{{site.author.googlescholar}}">my Google Scholar profile</a>.</div>
{% elsif site.author.dblp %}
  <div class="wordwrap">You can also find my articles on <a href="{{site.author.dblp}}">DBLP</a>.</div>
{% endif %}

{% include base_path %}

{% for post in site.publications reversed %}
  <b>{{ post.title }}</b><br>
  {{post.authors}}<br>
  <i>{{post.venue}}</i><br>
  <a href="{{ base_path }}{{ post.url }}" rel="permalink">[abstract]</a> <a href="{{ post.paperurl | relative_url }}">[pdf]</a><br><br>
{% endfor %}
