/* The PaPC challenge site: maths, milestones, copy buttons.
   Milestone ticks live in this browser only (localStorage), and the page
   works without them. */
(function () {
  'use strict';

  // ------------------------------------------------------------- maths
  var MACROS = {
    '\\sel': '\\sigma_{#1}',
    '\\proj': '\\pi_{#1}',
    '\\ren': '\\rho_{#1\\to #2}',
    '\\join': '\\bowtie',
    '\\att': '\\mathit{#1}',
    '\\val': '\\mathrm{#1}',
    '\\rel': '\\mathit{#1}',
    '\\B': '\\mathbb{B}',
    '\\N': '\\mathbb{N}',
    '\\true': '\\mathsf{true}',
    '\\false': '\\mathsf{false}',
    '\\lBrack': '\\llbracket',
    '\\rBrack': '\\rrbracket',
    '\\cat': '\\mathbin{+\\!\\!+}'
  };
  if (window.renderMathInElement) {
    window.renderMathInElement(document.body, {
      delimiters: [
        { left: '\\[', right: '\\]', display: true },
        { left: '\\(', right: '\\)', display: false }
      ],
      macros: MACROS,
      throwOnError: false
    });
  }

  // -------------------------------------------------------- milestones
  var KEY = 'papc-challenge:v1';
  function load() {
    try {
      var s = JSON.parse(window.localStorage.getItem(KEY));
      return s && typeof s === 'object' ? s : {};
    } catch (e) {
      return {};
    }
  }
  function save(s) {
    try {
      window.localStorage.setItem(KEY, JSON.stringify(s));
    } catch (e) { /* private window, or storage blocked: keep going */ }
  }

  function update() {
    var s = load();
    document.querySelectorAll('[data-progress]').forEach(function (el) {
      var keys = (el.getAttribute('data-progress') || '').split(' ')
        .filter(Boolean);
      if (!keys.length) return;
      var done = keys.filter(function (k) { return s[k]; }).length;
      var all = done === keys.length;
      el.classList.toggle('done', all);
      var bar = el.querySelector('progress');
      if (bar) bar.value = done;
      var count = el.querySelector('.ms-count');
      if (count) {
        count.textContent = all ? 'All ' + keys.length + ' done: well done!'
          : done + ' of ' + keys.length + ' done';
      }
      var badge = el.querySelector('.lvl-p');
      if (badge) {
        badge.textContent = all ? '✓ Done' : done ? done + ' of ' +
          keys.length + ' milestones' : '';
      }
    });
  }

  var state = load();
  document.querySelectorAll('input[data-milestone]').forEach(function (box) {
    var k = box.getAttribute('data-milestone');
    box.checked = !!state[k];
    box.addEventListener('change', function () {
      var s = load();
      if (box.checked) s[k] = true; else delete s[k];
      save(s);
      update();
    });
  });
  update();

  document.querySelectorAll('button.reset').forEach(function (btn) {
    btn.hidden = false;
    btn.addEventListener('click', function () {
      if (window.confirm('Clear all your ticked milestones, on every level?')) {
        save({});
        document.querySelectorAll('input[data-milestone]').forEach(
          function (b) { b.checked = false; });
        update();
      }
    });
  });

  // ------------------------------------------------------ copy buttons
  document.querySelectorAll('.code').forEach(function (block) {
    var btn = block.querySelector('button.copy');
    var pre = block.querySelector('pre');
    if (!btn || !pre || !navigator.clipboard) return;
    btn.hidden = false;
    btn.setAttribute('aria-label', 'Copy this code');
    btn.addEventListener('click', function () {
      navigator.clipboard.writeText(pre.innerText.replace(/\n$/, '')).then(
        function () {
          btn.textContent = 'Copied';
          setTimeout(function () { btn.textContent = 'Copy'; }, 1500);
        },
        function () { btn.textContent = 'Select and copy'; });
    });
  });
})();
