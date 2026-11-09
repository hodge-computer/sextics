/* Local atlas compiled from exact records and mathematical prose. */
(() => {
  'use strict';
  const $ = (id) => document.getElementById(id);
  const escape = (s) =>
    String(s ?? '').replace(
      /[&<>"']/g,
      (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]
    );
  const state = {
    records: [],
    cache: new Map(),
    current: null,
    page: 'home',
    renderer: null,
    exploring: false,
    surfaceState: 'loading',
    loadId: 0,
    lastFocus: null,
    accounts: new Map(),
    chapters: [],
    contentCache: new Map(),
    modalId: 0,
    solutionId: null,
    overview: null
  };
  const isProved = (r) => r.formalStatus === 'proved';
  const group = (r) => (isProved(r) ? 'solved' : 'open');
  const groupNames = { open: 'Open', solved: 'Solved' };
  const groupOrder = ['open', 'solved'];
  function firstOpenInstance() {
    return state.records
      .filter((r) => group(r) === 'open')
      .sort((a, b) => Number(a.number) - Number(b.number))[0];
  }
  function updateOpenInstanceLinks() {
    const record = firstOpenInstance();
    document.querySelectorAll('[data-open-instance]').forEach((link) => {
      link.hidden = !record;
      if (link.tagName === 'A')
        link.href = record ? `#case/${encodeURIComponent(record.id)}` : '#home';
      else link.disabled = !record;
    });
  }
  function math(tex, display = false) {
    const span = document.createElement('span');
    if (!tex) return '';
    katex.render(tex, span, {
      displayMode: display,
      throwOnError: true,
      trust: false,
      strict: 'ignore',
      output: 'htmlAndMathml'
    });
    return span.innerHTML;
  }
  function coefficientFractions(tex) {
    // Move coefficients out of monomial fractions without changing the exact record.
    return tex.replace(
      /\\frac\{(?:(\d+)\s+)?((?:[XY]_\{\d+\}(?:\^\{\d+\})?\s*)+)\}\{(\d+)\}/g,
      (_, coefficient, monomial, denominator) =>
        `\\frac{${coefficient || '1'}}{${denominator}}\\cdot ${monomial.trim()}`
    );
  }
  function polynomialTex(tex) {
    tex = coefficientFractions(tex);
    let at = 0,
      result = '',
      previous = null;
    // Keep scripts and command arguments intact: z_1^2 z_2 is a product,
    // while f(z), a subscript, and the words in \text{...} are not.
    function argument(format = false) {
      let leading = '';
      while (/\s/.test(tex[at] || '') && at < tex.length) leading += tex[at++];
      if (tex[at] === '{') {
        const start = ++at;
        let depth = 1;
        while (at < tex.length && depth) {
          if (tex[at] === '{') depth++;
          else if (tex[at] === '}') depth--;
          at++;
        }
        const body = tex.slice(start, at - 1);
        return leading + '{' + (format ? polynomialTex(body) : body) + '}';
      }
      if (tex[at] === '\\') {
        const command = tex.slice(at).match(/^\\(?:[A-Za-z]+|.)/)[0];
        at += command.length;
        return leading + command;
      }
      return leading + (tex[at++] || '');
    }
    function scripts() {
      let suffix = '';
      while (tex[at] === '_' || tex[at] === '^') {
        suffix += tex[at++] + argument();
      }
      return suffix;
    }
    while (at < tex.length) {
      let token = tex[at++],
        kind = null;
      if (/\s/.test(token)) {
        result += token;
        continue;
      }
      if (token === '\\') {
        const command = tex.slice(at).match(/^[A-Za-z]+|^./)?.[0] || '';
        at += command.length;
        token += command;
        if ([',', '!', ';', ' '].includes(command)) {
          result += token;
          continue;
        }
        if (['frac', 'dfrac', 'tfrac'].includes(command)) {
          token += argument(true) + argument(true);
          kind = 'factor';
        } else if (['text', 'operatorname', 'mathrm'].includes(command)) {
          token += argument();
        } else if (['sum', 'prod'].includes(command)) kind = 'operator';
        else if (['mathcal', 'mathbb', 'mathbf'].includes(command)) {
          token += argument();
          kind = 'factor';
        } else if (
          /^(?:alpha|beta|gamma|delta|theta|lambda|mu|nu|xi|pi|rho|sigma|tau|phi|chi|psi|omega|Delta|Theta|Phi|Psi|Omega)$/.test(
            command
          )
        )
          kind = 'factor';
        else if (/^(?:left|right|bigl|bigr|Bigl|Bigr|biggl|biggr|Biggl|Biggr)$/.test(command)) {
          token += tex[at++] || '';
          kind = /[)\]]$/.test(token) ? 'close' : /[(\[]$/.test(token) ? 'open' : null;
        }
        token += scripts();
      } else if (/[A-Za-z]/.test(token)) {
        token += scripts();
        kind = /^[XYZxyz]_/.test(token) ? 'scalar' : 'factor';
      } else if (/\d/.test(token)) {
        while (/\d/.test(tex[at] || '') && at < tex.length) token += tex[at++];
        token += scripts();
        kind = 'number';
      } else if (/[)\]]/.test(token)) {
        token += scripts();
        kind = 'close';
      } else if (/[(\[]/.test(token)) kind = 'open';
      if (
        (['factor', 'scalar', 'number', 'operator'].includes(kind) &&
          ['factor', 'scalar', 'number', 'close'].includes(previous)) ||
        (kind === 'open' && ['number', 'scalar', 'close'].includes(previous))
      )
        result += '\\cdot ';
      result += token;
      previous = kind;
    }
    return result;
  }
  function displayPolynomial(p) {
    return math(polynomialTex(p.latex), true);
  }
  function renderMath(root) {
    root.querySelectorAll('[data-math]:not([data-rendered])').forEach((node) => {
      node.innerHTML = math(node.textContent, node.hasAttribute('data-display'));
      node.dataset.rendered = 'true';
    });
  }
  function accountFor(login) {
    return (
      state.accounts.get(login.toLowerCase()) || {
        githubLogin: login,
        name: login
      }
    );
  }
  function avatar(account) {
    const source =
      account.avatar ||
      `https://avatars.githubusercontent.com/${encodeURIComponent(account.githubLogin)}?s=96`;
    return `<img class="account-avatar" src="${escape(source)}" alt="" width="48" height="48" loading="lazy" decoding="async" referrerpolicy="no-referrer">`;
  }
  function statusCard(record) {
    if (!isProved(record))
      return '<div class="status-certificate open"><span class="status-word"><span class="certificate-mark" aria-hidden="true"></span><strong>open</strong></span><span class="certificate-detail">Awaiting a construction</span></div>';
    const account = accountFor(record.credit.githubLogin);
    return `<a href="#case/${encodeURIComponent(record.id)}/solution" class="status-certificate solved" aria-haspopup="dialog" aria-label="Solved by ${escape(account.name)}: read the construction"><span class="status-word"><span class="certificate-mark" aria-hidden="true">✓</span><strong>solved</strong></span><span class="certificate-author">${avatar(account)}<span>@${escape(account.githubLogin)}</span></span><span class="certificate-arrow" aria-hidden="true">↗</span></a>`;
  }
  async function loadContent(path) {
    if (!state.contentCache.has(path))
      state.contentCache.set(
        path,
        fetch(path)
          .then((r) => {
            if (!r.ok) throw new Error('Content unavailable');
            return r.text();
          })
          .catch((e) => {
            state.contentCache.delete(path);
            throw e;
          })
      );
    return state.contentCache.get(path);
  }
  function positionDialog() {
    const dialog = $('infoDialog'),
      panel =
        state.page === 'case'
          ? $('caseView')
          : state.page === 'leaderboard'
            ? $('leaderboardView')
            : state.page === 'technical-information'
              ? $('chapterView').hidden
                ? $('technicalView')
                : $('chapterView')
              : $('homeView');
    const aligned =
      (dialog.classList.contains('solution-dialog') ||
        dialog.classList.contains('participate-dialog')) &&
      panel &&
      !panel.hidden;
    dialog.classList.toggle('column-dialog', !!aligned);
    if (aligned) {
      const bounds = panel.getBoundingClientRect();
      dialog.style.setProperty('--solution-left', `${bounds.left}px`);
      dialog.style.setProperty('--solution-width', `${bounds.width}px`);
    } else {
      dialog.style.removeProperty('--solution-left');
      dialog.style.removeProperty('--solution-width');
    }
  }
  async function showSolution(record, anchor) {
    state.solutionId = record.id;
    const token = ++state.modalId,
      account = accountFor(record.credit.githubLogin),
      dialog = $('infoDialog');
    dialog.classList.remove('participate-dialog', 'instance-participation');
    dialog.classList.add('solution-dialog');
    dialog.setAttribute('aria-labelledby', 'solutionTitle');
    positionDialog();
    const header = `<header class="solution-header"><p class="dialog-eyebrow">THE CONSTRUCTION</p><h2 id="solutionTitle">${escape(record.title)}</h2><div class="solution-contributor"><a class="solver-leaderboard-link" href="#leaderboard/${encodeURIComponent(account.githubLogin)}" aria-label="View ${escape(account.name)} on the leaderboard">${avatar(account)}<span><span class="solver-label">Solved by</span><strong>${escape(account.name)}</strong><span class="account-handle">@${escape(account.githubLogin)} · view leaderboard →</span></span></a><a class="solver-github-link" href="${escape(record.pullRequest.url)}" target="_blank" rel="noopener noreferrer">View pull request ↗</a></div></header>`;
    $('dialogContent').innerHTML =
      header + '<p role="status">Loading the mathematical explanation…</p>';
    dialog.showModal();
    dialog.scrollTop = 0;
    try {
      const content = await loadContent(record.content.solution);
      if (token !== state.modalId || !dialog.open) return;
      $('dialogContent').innerHTML =
        header +
        `<div class="solution-body mathematical-prose">${content}</div><footer class="solution-footer">${isProved(record) ? '<p>Lean proof verified.</p>' : ''}${record.leanVerification?.proofFile ? `<a href="${escape(record.leanVerification.proofFile)}" download>Lean proof ↓</a><a href="${escape(record.leanVerification.receipt)}" download>Acceptance receipt ↓</a>` : ''}<a href="data/${encodeURIComponent(record.id)}/instance.rec" download>Exact instance ↓</a>${record.D ? `<a href="data/${encodeURIComponent(record.id)}/witness.json" download>Exact witness ↓</a>` : ''}<a href="data/${encodeURIComponent(record.id)}/provenance.json" download>Context & related targets ↓</a></footer>`;
      renderMath($('dialogContent'));
      if (anchor)
        [...$('dialogContent').querySelectorAll('[id]')]
          .find((node) => node.id === anchor)
          ?.scrollIntoView({ block: 'start' });
    } catch (error) {
      if (token !== state.modalId || !dialog.open) return;
      $('dialogContent').innerHTML =
        header + '<p>The explanation could not be loaded. Close this window and try again.</p>';
      console.error(error);
    }
  }
  function setChaptersExpanded(open) {
    $('technicalChapters').hidden = !open;
    $('technicalDisclosure').setAttribute('aria-expanded', String(open));
    $('technicalDisclosure').setAttribute(
      'aria-label',
      `${open ? 'Collapse' : 'Expand'} technical chapters`
    );
  }
  function buildChapterIndex(active) {
    $('technicalChapters').innerHTML = state.chapters
      .map(
        (page) =>
          `<a href="#technical-information/${escape(page.id)}" ${active === page.id ? 'aria-current="page"' : ''}><span>${escape(page.number)}</span>${escape(page.shortTitle)}</a>`
      )
      .join('');
    $('chapterDirectory').innerHTML = state.chapters
      .map(
        (page) =>
          `<a href="#technical-information/${escape(page.id)}"><span>${escape(page.number)}</span><span><strong>${escape(page.shortTitle)}</strong><small>${escape(page.description)}</small></span><span aria-hidden="true">→</span></a>`
      )
      .join('');
  }
  async function renderChapter(chapterId, anchor, loadId) {
    const page = state.chapters.find((p) => p.id === chapterId);
    if (!page) {
      $('chapterView').hidden = true;
      $('notFound').hidden = false;
      return;
    }
    $('chapterTitle').textContent = page.title;
    $('chapterBody').innerHTML = '<p role="status">Reading the chapter…</p>';
    document.title = `${page.shortTitle} — hodge.computer`;
    try {
      const content = await loadContent(page.content);
      if (loadId !== state.loadId) return;
      $('chapterBody').innerHTML = content;
      renderMath($('chapterBody'));
      if (anchor) {
        const target = [...$('chapterBody').querySelectorAll('[id]')].find((n) => n.id === anchor);
        target?.scrollIntoView({ block: 'start' });
      }
    } catch (error) {
      if (loadId === state.loadId)
        $('chapterBody').innerHTML = '<p>This chapter could not be loaded. Please try again.</p>';
      console.error(error);
    }
  }
  function announce(message) {
    $('toast').textContent = message;
    $('toast').hidden = false;
    clearTimeout(announce.timer);
    announce.timer = setTimeout(() => ($('toast').hidden = true), 2600);
  }
  function openDrawer(open) {
    const sidebar = $('sidebar'),
      restoreFocus = !open && sidebar.contains(document.activeElement);
    document.body.classList.toggle('drawer-open', open);
    $('menuButton').setAttribute('aria-expanded', String(open));
    $('drawerBackdrop').hidden = !open;
    if (open) sidebar.focus({ preventScroll: true });
    else if (restoreFocus) $('menuButton').focus({ preventScroll: true });
  }
  function setExploring(value, fromRenderer = false) {
    state.exploring = !!value;
    $('exploreInfo').hidden = !value;
    $('exploreGuide').hidden = !value;
    updateSurfaceLoading();
    if (value) {
      $('exploreGuide').open = true;
      state.lastFocus = document.activeElement;
      openDrawer(false);
      if ($('infoDialog').open) $('infoDialog').close();
    }
    document.body.classList.toggle('exploring', value);
    $('appShell').inert = value;
    $('exploreToggle').setAttribute('aria-pressed', String(value));
    $('exploreToggle').setAttribute(
      'aria-label',
      value
        ? 'back to the challenge and reset the camera'
        : 'explore the surface with a free camera'
    );
    $('toggleLabel').textContent = value ? 'back to the challenge' : 'explore surface';
    if (!fromRenderer) state.renderer?.setMode(value ? 'free' : 'parallax');
    if (!value && state.lastFocus?.isConnected) state.lastFocus.focus({ preventScroll: true });
  }
  function instancesInGroup(key, records = state.records) {
    return records
      .filter((r) => group(r) === key)
      .sort((a, b) => Number(b.number) - Number(a.number));
  }
  function buildIndex() {
    const query = $('caseSearch').value.toLowerCase().trim();
    $('clearCaseSearch').disabled = !$('caseSearch').value;
    $('atlasColophon').hidden = !!query || !state.records.length;
    const filtered = state.records.filter((r) =>
      `${r.id} ${r.title} ${r.category} ${r.evidenceKind}`.toLowerCase().includes(query)
    );
    $('caseIndex').innerHTML =
      groupOrder
        .map((key) => {
          const rows = instancesInGroup(key, filtered);
          if (!rows.length && key !== 'solved') return '';
          if (!rows.length && query) return '';
          return `<section class="index-section" aria-label="${escape(groupNames[key])}"><h2 class="index-heading"><span class="status-dot ${key === 'open' ? 'open' : ''}"></span>${escape(groupNames[key])}<span class="index-count">${rows.length.toString().padStart(2, '0')}</span></h2>${rows.map((r) => `<div class="case-index-row"><a class="case-link${state.current === r.id ? ' active' : ''}" href="#case/${encodeURIComponent(r.id)}" ${state.current === r.id ? 'aria-current="page"' : ''}><span class="case-number">${escape(r.number)}</span><span class="case-index-title"><span class="case-name">${escape(r.title)}</span>${r.id === 'holdout' ? `<span class="case-family">${escape(r.category)}</span>` : ''}</span></a><a class="case-discussion-link" href="#case/${encodeURIComponent(r.id)}/discussion" data-discussion="${escape(r.id)}" data-title="${escape(r.title)}" aria-label="Open discussion for ${escape(r.title)}"><svg viewBox="0 0 30 25" aria-hidden="true"><path d="M6 2.5h18a3 3 0 0 1 3 3v11a3 3 0 0 1-3 3h-8l-6 4v-4H6a3 3 0 0 1-3-3v-11a3 3 0 0 1 3-3Z"/></svg><span aria-hidden="true">—</span></a></div>`).join('')}${!rows.length ? '<p class="index-empty">Reserved for verified Lean proofs.</p>' : ''}</section>`;
        })
        .join('') || '<p class="index-empty">No instances match this search.</p>';
    updateDiscussionCounts();
  }
  function updateDiscussionCounts() {
    $('caseIndex')
      .querySelectorAll('.case-discussion-link')
      .forEach((link) => {
        const count = HodgeDiscussion.count(link.dataset.discussion),
          known = Number.isSafeInteger(count);
        link.querySelector('span').textContent = known ? (count > 99 ? '99+' : String(count)) : '—';
        link.classList.toggle('has-comments', known && count > 0);
        const label = known
          ? `${count} ${count === 1 ? 'comment' : 'comments'}, including replies · ${link.dataset.title}`
          : `Open discussion for ${link.dataset.title}`;
        link.title = label;
        link.setAttribute('aria-label', label);
      });
  }
  async function revealDiscussion(commentNumber = null) {
    const panel = $('instanceDiscussion');
    if (!panel) return;
    openDrawer(false);
    panel.hidden = false;
    $('discussionToggle').setAttribute('aria-expanded', 'true');
    $('discussionToggle').querySelector('span').textContent = '−';
    panel.focus({ preventScroll: true });
    await HodgeDiscussion.open(commentNumber);
    if (!commentNumber && panel.isConnected && !panel.hidden)
      panel.scrollIntoView({
        behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'instant' : 'smooth',
        block: 'start'
      });
  }
  function updateSurfaceLoading() {
    const loading = state.surfaceState === 'loading',
      failed = state.surfaceState === 'error';
    $('surfaceLoading').hidden = !state.exploring || (!loading && !failed);
    $('surfaceLoading').dataset.state = state.surfaceState;
    $('surfaceLoadingLabel').textContent = failed
      ? 'The 3D view has been paused. You can still use the atlas.'
      : 'Loading surface…';
    $('surface').setAttribute('aria-busy', String(loading));
  }
  function onStatus(status) {
    if (status.state) {
      state.surfaceState = status.state;
      updateSurfaceLoading();
    }
    $('surfaceStatus').textContent = status.state === 'ready' ? '' : status.message || '';
    if (status.state === 'ready' && state.renderer) {
      const meta = state.renderer.getMeta();
      if (meta) {
        const signs = meta.phaseSigns;
        const phased = signs?.some((s) => s < 0);
        $('sliceLabel').textContent = phased
          ? 'a real slice in complex coordinates'
          : 'a real slice of X = {F = 0}';
      }
    }
  }
  function setScene(record) {
    const status = group(record),
      title = record.title;
    $('exploreInfo').innerHTML =
      `<span class="explore-status-dot ${status}" aria-hidden="true"></span><span class="explore-instance-name">${escape(title)}</span>`;
    $('exploreInfo').setAttribute('aria-label', `${groupNames[status]} instance shown`);
    $('exploreInfo').title = title;
    $('sceneLabel').textContent = title;
    $('sliceLabel').textContent = record.render?.phaseSigns?.some((s) => s < 0)
      ? 'a real slice in complex coordinates'
      : 'a real slice of X = {F = 0}';
    state.renderer?.setCase(record).catch((error) => {
      console.error(error);
      $('surfaceStatus').textContent = 'Surface unavailable';
    });
  }
  function definitionsMarkup(r) {
    const definitions = r.displayDefinitions;
    return definitions.length
      ? `<div class="definitions">${definitions.map((definition) => math(polynomialTex(definition), true)).join('')}</div>`
      : '';
  }

  function caseNavigation(record) {
    const ordered = groupOrder.flatMap((key) => instancesInGroup(key));
    const index = ordered.findIndex((r) => r.id === record.id);
    if (index < 0) return '';
    const link = (target, direction, label, arrow) =>
      target
        ? `<div class="case-pagination-entry ${direction}"><a class="page-next" href="#case/${encodeURIComponent(target.id)}" rel="${direction}" aria-label="${label} instance: ${escape(target.title)}">${direction === 'prev' ? `<span aria-hidden="true">${arrow}</span>` : ''}${label}${direction === 'next' ? `<span aria-hidden="true">${arrow}</span>` : ''}</a><p class="case-pagination-title">${escape(target.title)}</p></div>`
        : '';
    return `<nav class="case-pagination" aria-label="Browse instances">${link(ordered[index - 1], 'prev', 'Previous', '←')}${link(ordered[index + 1], 'next', 'Next', '→')}</nav>`;
  }
  async function renderCase(record, loadId) {
    const why = await loadContent(record.content.why);
    if (loadId !== state.loadId) return;
    const proved = isProved(record);
    const number = state.records.find((r) => r.id === record.id)?.number || '';
    const category = record.category;

    $('caseView').innerHTML =
      `<div class="case-breadcrumb">THE ATLAS <span>/</span> ${proved ? 'SOLVED' : 'OPEN TARGET'} <span>/</span> ${escape(number)}</div>
    <div class="case-heading"><h1 class="case-title">${escape(record.title)}</h1>${statusCard(record)}</div>
    <div class="case-meta"><span class="badge">q = ${escape(record.q)}</span>${category ? `<span class="badge">${escape(category)}</span>` : ''}</div>
    <section class="goal-panel" aria-label="Certificate problem"><h2 class="goal-label">THE GOAL</h2><p class="goal-intro">Find a homogeneous polynomial ${math('D')} on six complex variables such that</p><div class="goal-equation">${math('F^{q+1}\\;\\bigm|\\; A-q\\cdot\\mathrm dF(v)+F\\cdot\\operatorname{div}(v)', true)}</div><div class="goal-fields"><span>for some vector field</span><span class="goal-field-equation">${math('v=\\left(\\frac{N_0}{D},\\ldots,\\frac{N_5}{D}\\right)')}</span><span>with</span><span class="goal-field-equation">${math('\\deg N_i=\\deg D+6q-5.')}</span></div><div class="goal-fineprint">${math('D\\ne0')} and ${math('\\gcd(D,F)=1')}. Divisibility is in ${math('\\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2]_{(F)}')}. The challenge asks for a Lean proof that such a field exists.</div></section>
    <section class="instance-panel" aria-label="Exact instance"><div class="section-line"><h2>THIS INSTANCE</h2><button id="copyInstance" class="subtle-button copy-instance-button" aria-label="Copy (F, q, A)">Copy ${math('(F, q, A)')}</button></div><div class="polynomial-row"><div class="polynomial-symbol">${math('F')}</div><div class="polynomial-value"><div class="primary-polynomial">${displayPolynomial(record.F)}</div>${definitionsMarkup(record)}</div></div><div class="polynomial-row"><div class="polynomial-symbol">${math('q')}</div><div class="polynomial-value">${math(String(record.q), true)}</div></div><div class="polynomial-row"><div class="polynomial-symbol">${math('A')}</div><div class="polynomial-value"><div class="primary-polynomial">${displayPolynomial(record.A)}</div></div></div>${proved && record.D ? `<div class="solution-panel"><div class="solution-title"><span class="status-dot"></span> Known certificate </div><div class="polynomial-row"><div class="polynomial-symbol">${math('D')}</div><div class="polynomial-value"><div class="primary-polynomial">${displayPolynomial(record.D)}</div>${record.D.degree !== undefined ? `<p class="goal-fineprint">Homogeneous degree ${escape(record.D.degree)}. Highlighted on the surface where visible.</p>` : ''}</div></div></div>` : ''}</section>
    <section class="case-notes mathematical-prose"><h2>Why this instance matters</h2>${why}</section>
    <div class="record-actions"><button class="participate-action" data-modal="participate" data-instance="${escape(record.id)}">Participate <span>↗</span></button><button id="discussionToggle" aria-expanded="false" aria-controls="instanceDiscussion">Discussion <span aria-hidden="true">＋</span></button></div>${HodgeDiscussion.markup(record)}${caseNavigation(record)}`;
    renderMath($('caseView'));
    $('caseView')
      .querySelector('.case-pagination')
      .addEventListener('click', (event) => {
        if (event.target.closest('a')) $('main').focus({ preventScroll: true });
      });
    const discussion = HodgeDiscussion.mount($('instanceDiscussion'));
    $('discussionToggle').addEventListener('click', () => {
      const panel = $('instanceDiscussion'),
        open = panel.hidden;
      panel.hidden = !open;
      $('discussionToggle').setAttribute('aria-expanded', String(open));
      $('discussionToggle').querySelector('span').textContent = open ? '−' : '＋';
      if (open) revealDiscussion();
    });
    if (discussion.resume || HodgeRoutes.parse(location.hash)?.discussion)
      revealDiscussion(HodgeRoutes.parse(location.hash)?.comment);
    $('copyInstance').addEventListener('click', () =>
      copyText(
        `F = ${record.F.expression}\nq = ${record.q}\nA = ${record.A.expression}\nvariables = X0, X1, X2, Y0, Y1, Y2`
      )
    );
  }
  async function copyText(text, message = 'Exact instance copied.') {
    try {
      await navigator.clipboard.writeText(text);
      announce(message);
    } catch {
      const node = document.createElement('textarea');
      node.value = text;
      node.style.position = 'fixed';
      node.style.opacity = '0';
      document.body.append(node);
      node.select();
      const copied = document.execCommand('copy');
      node.remove();
      announce(copied ? message : 'Select the text and copy it manually.');
    }
  }
  async function getRecord(id) {
    if (state.cache.has(id)) return state.cache.get(id);
    const summary = state.records.find((r) => r.id === id);
    if (!summary) throw new Error('Unknown instance');
    const pending = fetch(summary.path, { cache: 'no-cache' })
      .then((response) => {
        if (!response.ok) throw new Error('Instance unavailable');
        return response.json();
      })
      .catch((error) => {
        state.cache.delete(id);
        throw error;
      });
    state.cache.set(id, pending);
    return pending;
  }
  async function loadProfiles(logins, signal) {
    const missing = [...new Set(logins)].filter(
      (login) => !state.accounts.has(login.toLowerCase())
    );
    if (!missing.length) return;
    for (let offset = 0; offset < missing.length; offset += 50) {
      const data = await HodgeAccount.request(
        '/api/profiles?logins=' + encodeURIComponent(missing.slice(offset, offset + 50).join(',')),
        { signal }
      );
      if (signal?.aborted) return;
      for (const account of data.accounts)
        state.accounts.set(account.githubLogin.toLowerCase(), account);
    }
  }
  async function loadCatalogue() {
    const responses = await Promise.all(
      [
        'assets/atlas/index.json',
        'docs/index.json',
        'assets/home-scene.json',
        'discussions/index.json'
      ].map((path) => fetch(path, { cache: 'no-cache' }))
    );
    if (responses.some((r) => !r.ok)) throw new Error('Catalogue content unavailable');
    const [data, chapters, home, discussions] = await Promise.all(responses.map((r) => r.json()));
    state.homeScene = home;
    state.chapters = chapters.pages;
    state.overview = chapters.overview;
    buildChapterIndex();
    state.records = data.records.map((r, i) => ({ ...r, number: String(i + 1).padStart(2, '0') }));
    HodgeRoutes.startLinks(state.records, chapters, discussions);
    updateOpenInstanceLinks();
    $('totalCount').textContent = `${state.records.length} instances`;
    $('openCount').textContent = state.records.filter((r) => group(r) === 'open').length;
    $('solvedCount').textContent = state.records.filter(isProved).length;
  }
  const leaderboard = HodgeLeaderboardView.create({
    records: () => state.records,
    accountFor,
    avatar,
    loadProfiles,
    rememberAccounts: (accounts) => {
      for (const account of accounts)
        state.accounts.set(account.githubLogin.toLowerCase(), account);
    },
    clearAccounts: () => state.accounts.clear()
  });
  async function route() {
    const id = ++state.loadId;
    const destination = HodgeRoutes.parse(location.hash) || { page: 'home' };
    const { page, caseId = null, chapterId = null } = destination;
    openDrawer(false);
    if (state.exploring) setExploring(false);
    if ($('infoDialog').open) $('infoDialog').close();
    // Navigation within an instance preserves its discussion draft and surface.
    if (
      page === 'case' &&
      state.page === 'case' &&
      state.current === caseId &&
      $('instanceDiscussion')?.dataset.instance === caseId
    ) {
      if (!destination.discussion && !destination.solution)
        $('main').scrollTo({
          top: 0,
          behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'instant' : 'smooth'
        });
      if (destination.discussion) revealDiscussion(destination.comment);
      if (destination.solution) {
        const record = await getRecord(caseId);
        if (id === state.loadId && isProved(record)) await showSolution(record, destination.anchor);
      }
      return;
    }
    if (page === 'leaderboard' && state.page === 'leaderboard') {
      await leaderboard.show(destination);
      return;
    }
    if (page !== 'leaderboard') leaderboard.leave();
    HodgeDiscussion.unmount();
    state.current = caseId;
    state.page = page;
    document.body.classList.toggle('home-page', page === 'home');
    buildChapterIndex(chapterId);
    for (const [key, linkId] of [
      ['home', 'homeLink'],
      ['technical-information', 'technicalLink'],
      ['leaderboard', 'leaderboardLink']
    ]) {
      const link = $(linkId);
      link.classList.toggle('active', page === key);
      if (page === key) link.setAttribute('aria-current', 'page');
      else link.removeAttribute('aria-current');
    }
    buildIndex();
    const activeLink = $('caseIndex').querySelector('.case-link.active');
    if (!caseId) $('sidebarScroll').scrollTop = 0;
    else if (activeLink) activeLink.scrollIntoView({ block: 'nearest' });
    $('homeView').hidden = page !== 'home';
    $('technicalView').hidden = page !== 'technical-information' || !!chapterId;
    $('chapterView').hidden = !chapterId;
    $('leaderboardView').hidden = page !== 'leaderboard';
    $('caseView').hidden = page !== 'case';
    $('notFound').hidden = true;
    $('main').scrollTop = 0;
    if (!caseId) {
      document.title =
        page === 'home'
          ? 'hodge.computer'
          : `${page === 'leaderboard' ? 'Leaderboard' : 'Technical information'} — hodge.computer`;
      const contactSummary = state.records.find((r) => r.id === 'contact46006');
      const contact =
        contactSummary && isProved(contactSummary)
          ? await getRecord('contact46006')
          : contactSummary;
      if (id !== state.loadId) return;
      // Shared front-page camera; the atlas entry retains its own saved view.
      setScene({
        ...contact,
        id: 'home',
        title: 'Contact cone 46006',
        render: {
          divisorTerms: contact?.render?.divisorTerms,
          divisorProgram: contact?.render?.divisorProgram,
          ...state.homeScene
        }
      });
      if (page === 'technical-information') {
        setChaptersExpanded(true);
        if (chapterId) await renderChapter(chapterId, destination.anchor, id);
        else if (state.overview) {
          const content = await loadContent(state.overview.content);
          if (id === state.loadId) {
            $('technicalBody').innerHTML = content;
            renderMath($('technicalBody'));
          }
        }
      }
      if (page === 'leaderboard') await leaderboard.show(destination);
      return;
    }
    const summary = state.records.find((r) => r.id === caseId);
    if (!summary) {
      $('caseView').hidden = true;
      $('notFound').hidden = false;
      return;
    }
    $('caseView').innerHTML = '<p class="eyebrow">READING THE INSTANCE…</p>';
    try {
      const record = await getRecord(caseId);
      if (id !== state.loadId) return;
      document.title = `${record.title} — hodge.computer`;
      setScene(record);
      await renderCase(record, id);
      if (id !== state.loadId) return;
      if (destination.solution && isProved(record)) await showSolution(record, destination.anchor);
    } catch (error) {
      if (id !== state.loadId) return;
      console.error(error);
      $('caseView').innerHTML =
        '<p class="eyebrow">The instance could not be loaded.</p><p>Please reload the page.</p>';
    }
  }
  function participationPrompt(record) {
    const target = record
      ? `${isProved(record) ? 'Study the accepted proof for' : 'Work on'} instance ${record.id} (${record.title}), with q = ${record.q}. Read the exact F and A from data/${record.id}/instance.rec. Read why.md and provenance.json in that folder.`
      : 'Choose an open instance from data/catalogue.json. Read its exact instance.rec, why.md, and provenance.json.';
    const task =
      record && isProved(record)
        ? 'Read the accepted solution and its PR. Explain the argument and identify useful next open targets; do not submit a duplicate first-solve proposal.'
        : 'Check whether this instance already has a merged proposal. If it is still open for submission, prove its exact HodgeComputer.HasCertificate statement in Lean. Add the permitted solution files to the existing data/' +
          (record ? record.id : '<instance-id>') +
          '/ folder using the current schema in CONTRIBUTING.md. Include a thorough explanation and credit prior mathematical work. Run the prescribed checks and report their results.';
    return `Work in https://github.com/hodge-computer/sextics.\n\nFirst read README.md, AGENTS.md, CONTRIBUTING.md, and formal/README.md.\n\n${target}\n\n${task}\n\nYou are encouraged to share useful partial results, failed approaches, questions, and observations in the relevant instance's discussion, even without a complete solve. Read the existing thread first and explain the assumptions and limits of any unsuccessful search.\n\nKeep (F, q, A) fixed. Keep every existing file unchanged. Add only the permitted solution files in one instance folder; do not edit generated atlas data, the leaderboard, website, or verifier. Submit a checked solution through a branch in your contributor's fork and a PR against hodge-computer/sextics:main. Use CONTRIBUTING.md#discuss-an-instance to post progress in the existing instance thread.`;
  }
  function showParticipation(record = null) {
    const dialog = $('infoDialog'),
      proved = record && isProved(record),
      prompt = participationPrompt(record);
    const commands =
      'git clone https://github.com/hodge-computer/sextics.git\ncd sextics' +
      (record && !proved ? `\ngit switch -c codex/solve-${record.id}` : '');
    const repo = 'https://github.com/hodge-computer/sextics';
    state.modalId++;
    state.solutionId = null;
    dialog.classList.remove('solution-dialog', 'column-dialog');
    dialog.classList.add('participate-dialog');
    dialog.classList.toggle('instance-participation', !!record);
    dialog.setAttribute('aria-labelledby', 'participateTitle');
    positionDialog();
    $('dialogContent').innerHTML =
      `<header class="participate-heading"><p class="dialog-eyebrow">PARTICIPATE</p><h2 id="participateTitle">${proved ? 'Build on this result.' : record ? 'Take on this instance.' : 'Bring an agent.<br>Find a proof.'}</h2><p>${proved ? 'Study the checked construction, then carry its ideas to an open target.' : record ? 'Give your agent this exact target and the contribution instructions.' : 'Choose an open instance and work toward a Lean proof, with a human-readable mathematical explanation.'}</p></header>
    ${record ? `<section class="participate-target" aria-label="Selected instance"><strong>${escape(record.title)}</strong><div><code>${escape(record.id)}</code><span>${math(`q=${record.q}`)}</span></div><p>${proved ? 'This instance has an accepted proof. First-solve submissions are for open instances.' : 'This is an open target. Its exact statement lives in the instance record.'}</p><button type="button" id="participateCopyTarget" class="participate-copy" aria-label="Copy (F, q, A)">Copy ${math('(F, q, A)')}</button>${proved && record.pullRequest ? `<a href="${escape(record.pullRequest.url)}" target="_blank" rel="noopener noreferrer">Read the accepted PR ↗</a>` : ''}</section>` : ''}
    <section class="participate-step"><div class="participate-step-heading"><h3>1. Give your agent a starting point</h3><button type="button" id="copyAgentPrompt" class="participate-copy">Copy prompt</button></div><pre class="agent-prompt"><code>${escape(prompt)}</code></pre></section>
    <section class="participate-step"><div class="participate-step-heading"><h3>2. Open the repository</h3><button type="button" id="copySetupCommands" class="participate-copy">Copy commands</button></div><pre><code>${escape(commands)}</code></pre><p>Start with <a href="${repo}/blob/main/README.md" target="_blank" rel="noopener noreferrer">README.md ↗</a>. The <a href="${repo}/blob/main/CONTRIBUTING.md" target="_blank" rel="noopener noreferrer">proposal specification ↗</a> gives the current file format, Lean theorem, and verification commands.</p></section>
    <section class="participate-step"><h3>3. Submit one clear mathematical contribution</h3><p>${proved ? 'Choose an open instance for your next solution PR.' : 'A solution PR adds proof.json, Solution.lean, solution.md, and permitted supporting files to the existing data/&lt;instance-id&gt;/ folder. Preserve every existing file, including the target and motivation.'} Automated checks verify the fixed target; the project owner reviews the result before merging. Credit belongs to the contributor’s GitHub account, with collaborators acknowledged in the explanation.</p><p>A complete solve is not required to contribute. Agents and people are encouraged to share partial results, failed approaches, questions, and useful observations in the instance’s discussion. Read the <a href="${repo}/blob/main/CONTRIBUTING.md#discuss-an-instance" target="_blank" rel="noopener noreferrer">discussion instructions ↗</a> to get started.</p></section>
    `;
    $('copyAgentPrompt').addEventListener('click', () => copyText(prompt, 'Agent prompt copied.'));
    $('copySetupCommands').addEventListener('click', () =>
      copyText(commands, 'Setup commands copied.')
    );
    $('participateCopyTarget')?.addEventListener('click', () =>
      copyText(
        `F = ${record.F.expression}\nq = ${record.q}\nA = ${record.A.expression}\nvariables = X0, X1, X2, Y0, Y1, Y2`
      )
    );
    renderMath($('dialogContent'));
    dialog.showModal();
    dialog.scrollTop = 0;
  }
  const modals = {
    about: `<div class="endorsement"><h2>I value responsible, human-centered mathematics.</h2><p>I endorse and affirm the contents of the <a href="https://leidendeclaration.ai/" target="_blank" rel="noopener noreferrer">Leiden</a> and <a href="https://www.mathandai.org/" target="_blank" rel="noopener noreferrer">Math and AI</a> Declarations.</p><p>I am fully committed to establishing, crystallizing, and communicating <em>human understanding</em> of any and all mathematical results that ensue from this project. I am committed to fully determining where and how previous human mathematical results have been used in any advance that might arise during the course of this project, and assigning full credit to the authors of said results during the preparation of any manuscript describing this project's advances.</p><footer class="endorsement-footer"><nav class="endorsement-links" aria-label="Author and community"><a href="https://x.com/hodgecomputer" target="_blank" rel="noopener noreferrer">Twitter ↗</a><a href="https://benediamond.github.io" target="_blank" rel="noopener noreferrer">Personal website ↗</a><a href="https://discord.gg/X6VVp5EZY" target="_blank" rel="noopener noreferrer">Join our Discord ↗</a><a href="mailto:contact@hodge.computer">Contact us ↗</a></nav></footer></div>`
  };
  function showModal(name) {
    if (!modals[name]) return;
    state.modalId++;
    const dialog = $('infoDialog');
    dialog.classList.remove(
      'solution-dialog',
      'participate-dialog',
      'instance-participation',
      'column-dialog'
    );
    dialog.removeAttribute('aria-labelledby');
    $('dialogContent').innerHTML = modals[name];
    dialog.showModal();
    dialog.scrollTop = 0;
  }
  async function main() {
    renderMath(document);
    $('technicalDisclosure').addEventListener('click', () =>
      setChaptersExpanded($('technicalChapters').hidden)
    );
    try {
      state.renderer = HodgeRenderer.create($('surface'), {
        onStatus,
        onModeChange: (mode) => {
          if (state.exploring !== (mode === 'free')) setExploring(mode === 'free', true);
        }
      });
    } catch (error) {
      console.error(error);
      onStatus({ state: 'error', message: 'WebGL2 unavailable' });
    }
    $('exploreToggle').addEventListener('click', () => setExploring(!state.exploring));
    $('caseSearch').addEventListener('input', () => {
      buildIndex();
      $('caseSearch').scrollIntoView({ block: 'nearest' });
    });
    $('clearCaseSearch').addEventListener('click', () => {
      $('caseSearch').value = '';
      buildIndex();
      $('caseSearch').focus();
    });
    $('menuButton').addEventListener('click', () =>
      openDrawer(!document.body.classList.contains('drawer-open'))
    );
    $('drawerBackdrop').addEventListener('click', () => openDrawer(false));
    $('closeDialog').addEventListener('click', () => $('infoDialog').close());
    $('infoDialog').addEventListener('close', () => {
      if ($('infoDialog').open) return;
      const destination = HodgeRoutes.parse(location.hash);
      if (destination?.solution && destination.caseId === state.solutionId)
        history.replaceState(null, '', '#case/' + state.solutionId);
      state.modalId++;
      state.solutionId = null;
      $('infoDialog').classList.remove('column-dialog');
    });
    addEventListener('resize', () => {
      if ($('infoDialog').open) positionDialog();
    });
    $('infoDialog').addEventListener('click', (event) => {
      if (event.target === $('infoDialog')) {
        const box = $('infoDialog').getBoundingClientRect();
        if (
          event.clientX < box.left ||
          event.clientX > box.right ||
          event.clientY < box.top ||
          event.clientY > box.bottom
        )
          $('infoDialog').close();
      }
    });
    document.addEventListener('click', async (event) => {
      const link = event.target.closest('a[href]');
      if (
        link &&
        link.origin === location.origin &&
        link.pathname === location.pathname &&
        HodgeRoutes.parse(link.hash) &&
        link.hash === location.hash &&
        event.button === 0 &&
        !event.metaKey &&
        !event.ctrlKey &&
        !event.shiftKey &&
        !event.altKey
      ) {
        event.preventDefault();
        await route();
        return;
      }
      const target = event.target.closest('[data-modal]');
      if (target) {
        if (target.tagName === 'A') {
          if (
            event.button !== 0 ||
            event.metaKey ||
            event.ctrlKey ||
            event.shiftKey ||
            event.altKey
          )
            return;
          event.preventDefault();
        }
        if (target.dataset.modal === 'participate') {
          try {
            showParticipation(
              target.dataset.instance ? await getRecord(target.dataset.instance) : null
            );
          } catch (error) {
            announce('Could not load this instance. Please try again.');
          }
        } else showModal(target.dataset.modal);
      }
    });
    document.addEventListener('keydown', (event) => {
      if (event.key === 'Escape') {
        if (state.exploring) setExploring(false);
        openDrawer(false);
      }
      if (
        event.key === '/' &&
        !state.exploring &&
        !$('infoDialog').open &&
        !['INPUT', 'TEXTAREA'].includes(document.activeElement.tagName)
      ) {
        event.preventDefault();
        if (innerWidth <= 680) openDrawer(true);
        $('caseSearch').focus();
      }
    });
    $('startExploring').addEventListener('click', () => {
      const r = firstOpenInstance();
      if (r) location.hash = `case/${encodeURIComponent(r.id)}`;
    });
    document.addEventListener('hodge-discussion-counts', updateDiscussionCounts);
    try {
      await loadCatalogue();
      HodgeDiscussion.startCounts();
      await route();
    } catch (error) {
      console.error(error);
      $('caseIndex').innerHTML =
        '<p class="index-empty">The atlas could not be loaded. Please reload the page.</p>';
      onStatus({ state: 'error', message: 'Surface unavailable' });
    }
    addEventListener('hashchange', route);
  }
  main();
})();
