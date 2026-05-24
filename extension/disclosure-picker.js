// Disclosure picker popup — nonce-bound.
// P0-1/P0-2: token facts (which may contain email/userId/org) are fetched
// from background memory via pyana:getPendingDecision rather than embedded
// in the URL. The decision message includes the nonce.

function parseNonce() {
  const hash = window.location.hash || '';
  const m = hash.match(/(?:^#|&)nonce=([0-9a-f]+)/);
  return m ? m[1] : null;
}

const NONCE = parseNonce();

let origin = 'Unknown site';
let action = 'unknown';
let resource = '*';
let tokenFacts = [];
let requiredFacts = [];
let siteRequestedFacts = [];
let initialized = false;

// ---------------------------------------------------------------------------
// Fact categorization / formatting
// ---------------------------------------------------------------------------

const FACT_CATEGORIES = {
  permissions: { label: 'Permissions', keys: ['action', 'actions', 'resource', 'service', 'grant', 'scope'] },
  identity: { label: 'Identity', keys: ['user', 'userId', 'org', 'organization', 'email', 'name', 'subject'] },
  temporal: { label: 'Temporal', keys: ['expires', 'expiry', 'issued', 'issuedAt', 'notBefore', 'notAfter'] },
  resource: { label: 'Resource', keys: ['resource', 'domain', 'path', 'uri', 'url', 'target'] },
  metadata: { label: 'Metadata', keys: [] },
};

function categorizeFact(fact) {
  const key = (fact.key || '').toLowerCase();
  for (const [catId, cat] of Object.entries(FACT_CATEGORIES)) {
    if (catId === 'metadata') continue;
    if (cat.keys.some(k => key.includes(k))) return catId;
  }
  return 'metadata';
}

function isFactRequired(fact) {
  return requiredFacts.some(rf => rf.key === fact.key) ||
    fact.key === 'action' || fact.key === 'resource';
}

function isFactSiteRequested(fact) {
  return siteRequestedFacts.some(sf => sf.key === fact.key);
}

function isNumericFact(fact) {
  const val = fact.value;
  if (typeof val === 'number') return true;
  if (typeof val === 'string' && val.trim() !== '' && !isNaN(Number(val))) return true;
  return false;
}

function formatFactKey(key) {
  return String(key)
    .replace(/([A-Z])/g, ' $1')
    .replace(/_/g, ' ')
    .replace(/^\w/, c => c.toUpperCase())
    .trim();
}

function formatFactValue(key, value) {
  const lowerKey = String(key).toLowerCase();
  if (lowerKey.includes('expir') || lowerKey.includes('issued') || lowerKey.includes('notbefore') || lowerKey.includes('notafter')) {
    const ts = Number(value);
    if (!isNaN(ts) && ts > 1000000000) {
      return new Date(ts > 9999999999 ? ts : ts * 1000).toLocaleDateString();
    }
  }
  if (typeof value === 'string' && value.length > 32) {
    return value.slice(0, 16) + '...' + value.slice(-8);
  }
  if (Array.isArray(value)) {
    return value.join(', ');
  }
  return String(value);
}

// ---------------------------------------------------------------------------
// Build fact picker UI
// ---------------------------------------------------------------------------

function buildFactPicker() {
  const factListEl = document.getElementById('factList');
  while (factListEl.firstChild) factListEl.removeChild(factListEl.firstChild);

  const grouped = {};
  for (let i = 0; i < tokenFacts.length; i++) {
    const fact = tokenFacts[i];
    fact._index = i;
    const cat = categorizeFact(fact);
    if (!grouped[cat]) grouped[cat] = [];
    grouped[cat].push(fact);
  }

  const categoryOrder = ['permissions', 'identity', 'temporal', 'resource', 'metadata'];
  for (const catId of categoryOrder) {
    const facts = grouped[catId];
    if (!facts || facts.length === 0) continue;

    const catDef = FACT_CATEGORIES[catId];
    const categoryEl = document.createElement('div');
    categoryEl.className = 'fact-category';

    const catNameEl = document.createElement('div');
    catNameEl.className = 'fact-category-name';
    catNameEl.textContent = catDef.label;
    categoryEl.appendChild(catNameEl);

    for (const fact of facts) {
      const required = isFactRequired(fact);
      const siteRequested = isFactSiteRequested(fact);
      const numeric = isNumericFact(fact);
      const radioName = `fact-${fact._index}`;

      const itemEl = document.createElement('div');
      itemEl.className = 'fact-disclosure' + (required ? ' required mode-reveal' : '');
      itemEl.dataset.factIndex = fact._index;

      const labelEl = document.createElement('div');
      labelEl.className = 'fact-label';

      const keyEl = document.createElement('span');
      keyEl.className = 'fact-key';
      keyEl.textContent = formatFactKey(fact.key);

      const valueEl = document.createElement('span');
      valueEl.className = 'fact-value';
      valueEl.textContent = formatFactValue(fact.key, fact.value);

      labelEl.appendChild(keyEl);
      labelEl.appendChild(valueEl);
      itemEl.appendChild(labelEl);

      const optionsEl = document.createElement('div');
      optionsEl.className = 'disclosure-options';

      const revealOpt = document.createElement('label');
      revealOpt.className = 'disclosure-opt opt-reveal' + ((required || siteRequested) ? ' active' : '');
      const revealRadio = document.createElement('input');
      revealRadio.type = 'radio';
      revealRadio.name = radioName;
      revealRadio.value = 'reveal';
      revealRadio.checked = required || siteRequested;
      revealRadio.dataset.factKey = fact.key;
      revealRadio.dataset.factIndex = fact._index;
      if (required) revealRadio.disabled = true;
      revealOpt.appendChild(revealRadio);
      revealOpt.appendChild(document.createTextNode(' Reveal'));
      optionsEl.appendChild(revealOpt);

      if (numeric && !required) {
        const predOpt = document.createElement('label');
        predOpt.className = 'disclosure-opt opt-predicate';
        const predRadio = document.createElement('input');
        predRadio.type = 'radio';
        predRadio.name = radioName;
        predRadio.value = 'predicate';
        predRadio.dataset.factKey = fact.key;
        predRadio.dataset.factIndex = fact._index;
        predOpt.appendChild(predRadio);
        predOpt.appendChild(document.createTextNode(' ≥ '));

        const thresholdInput = document.createElement('input');
        thresholdInput.type = 'number';
        thresholdInput.className = 'threshold-input';
        thresholdInput.placeholder = 'min';
        thresholdInput.dataset.factIndex = fact._index;
        thresholdInput.addEventListener('click', (e) => e.stopPropagation());
        thresholdInput.addEventListener('input', () => {
          predRadio.checked = true;
          updateFactItemMode(itemEl, 'predicate');
          updatePreview();
        });
        predOpt.appendChild(thresholdInput);

        const tooltip = document.createElement('span');
        tooltip.className = 'predicate-tooltip';
        tooltip.textContent = '?';
        tooltip.dataset.tooltip = 'Prove that this value satisfies a condition without revealing the exact value';
        predOpt.appendChild(tooltip);

        optionsEl.appendChild(predOpt);
      }

      if (!required) {
        const hideOpt = document.createElement('label');
        hideOpt.className = 'disclosure-opt opt-hide' + ((!required && !siteRequested) ? ' active' : '');
        const hideRadio = document.createElement('input');
        hideRadio.type = 'radio';
        hideRadio.name = radioName;
        hideRadio.value = 'hide';
        hideRadio.dataset.factKey = fact.key;
        hideRadio.dataset.factIndex = fact._index;
        if (!required && !siteRequested) {
          hideRadio.checked = true;
          itemEl.className = 'fact-disclosure mode-hide';
        }
        hideOpt.appendChild(hideRadio);
        hideOpt.appendChild(document.createTextNode(' Hide'));
        optionsEl.appendChild(hideOpt);
      }

      itemEl.appendChild(optionsEl);

      if (required) {
        const reqTag = document.createElement('span');
        reqTag.className = 'fact-required-tag';
        reqTag.textContent = 'required';
        itemEl.appendChild(reqTag);
      }

      const radios = optionsEl.querySelectorAll('input[type="radio"]');
      for (const radio of radios) {
        radio.addEventListener('change', () => {
          updateFactItemMode(itemEl, radio.value);
          updateActiveOpts(optionsEl, radio.value);
          updatePreview();
        });
      }

      if (required || siteRequested) {
        itemEl.classList.add('mode-reveal');
        updateActiveOpts(optionsEl, 'reveal');
      }

      categoryEl.appendChild(itemEl);
    }

    factListEl.appendChild(categoryEl);
  }
}

function updateFactItemMode(itemEl, mode) {
  itemEl.classList.remove('mode-reveal', 'mode-predicate', 'mode-hide');
  itemEl.classList.add(`mode-${mode}`);
}

function updateActiveOpts(optionsEl, activeValue) {
  const opts = optionsEl.querySelectorAll('.disclosure-opt');
  for (const opt of opts) {
    const radio = opt.querySelector('input[type="radio"]');
    opt.classList.toggle('active', radio.value === activeValue);
  }
}

// ---------------------------------------------------------------------------
// Preview update — P2-3: build via textContent/DOM, never innerHTML with values
// ---------------------------------------------------------------------------

function updatePreview() {
  const previewEl = document.getElementById('preview');
  const level = getSelectedLevel();

  // Clear previous content.
  while (previewEl.firstChild) previewEl.removeChild(previewEl.firstChild);

  if (level !== 'selective') {
    previewEl.classList.remove('visible');
    return;
  }
  previewEl.classList.add('visible');

  const decisions = getFactDecisions();
  const revealed = decisions.filter(d => d.disclosure === 'reveal');
  const proven = decisions.filter(d => d.disclosure === 'predicate');
  const hidden = decisions.filter(d => d.disclosure === 'hide');

  function appendLineSpan(cls, label, items) {
    if (previewEl.childNodes.length > 0) previewEl.appendChild(document.createElement('br'));
    const span = document.createElement('span');
    span.className = cls;
    span.textContent = label + items.join(', ');
    previewEl.appendChild(span);
  }

  if (revealed.length > 0) {
    appendLineSpan(
      'preview-revealed',
      'Revealed: ',
      revealed.map(d => {
        const fact = tokenFacts[d.index];
        return `${formatFactKey(fact.key)}=${formatFactValue(fact.key, fact.value)}`;
      }),
    );
  }
  if (proven.length > 0) {
    appendLineSpan(
      'preview-proven',
      'Proven: ',
      proven.map(d => {
        const fact = tokenFacts[d.index];
        const thresholdStr = d.threshold != null ? d.threshold : '?';
        return `${formatFactKey(fact.key)} ≥ ${thresholdStr}`;
      }),
    );
  }
  if (hidden.length > 0) {
    appendLineSpan(
      'preview-hidden',
      'Hidden: ',
      hidden.map(d => formatFactKey(tokenFacts[d.index].key)),
    );
  }

  updateAuthorizeButton();
}

function getFactDecisions() {
  const decisions = [];
  for (let i = 0; i < tokenFacts.length; i++) {
    const radioName = `fact-${i}`;
    const selected = document.querySelector(`input[name="${radioName}"]:checked`);
    if (!selected) {
      const required = isFactRequired(tokenFacts[i]);
      decisions.push({ index: i, disclosure: required ? 'reveal' : 'hide' });
      continue;
    }
    const decision = { index: i, disclosure: selected.value };
    if (selected.value === 'predicate') {
      const thresholdInput = document.querySelector(`.threshold-input[data-fact-index="${i}"]`);
      if (thresholdInput && thresholdInput.value !== '') {
        decision.predicateType = 'gte';
        decision.threshold = Number(thresholdInput.value);
      }
    }
    decisions.push(decision);
  }
  return decisions;
}

function getSelectedLevel() {
  const selected = document.querySelector('input[name="privacy"]:checked');
  return selected ? selected.value : 'full';
}

function selectLevel(level) {
  const radios = document.querySelectorAll('input[name="privacy"]');
  for (const radio of radios) {
    radio.checked = radio.value === level;
    const parent = radio.closest('.privacy-level');
    parent.classList.toggle('selected', radio.value === level);
  }

  const factPicker = document.getElementById('factPicker');
  if (level === 'selective') {
    factPicker.classList.add('visible');
  } else {
    factPicker.classList.remove('visible');
  }

  updatePreview();
  updateAuthorizeButton();
}

function updateAuthorizeButton() {
  const btn = document.getElementById('authorizeBtn');
  const level = getSelectedLevel();

  switch (level) {
    case 'full':
      btn.textContent = 'Authorize (full disclosure)';
      break;
    case 'selective': {
      const decisions = getFactDecisions();
      const revealCount = decisions.filter(d => d.disclosure === 'reveal').length;
      const provenCount = decisions.filter(d => d.disclosure === 'predicate').length;
      const hiddenCount = decisions.filter(d => d.disclosure === 'hide').length;
      const parts = [];
      if (revealCount > 0) parts.push(`${revealCount} revealed`);
      if (provenCount > 0) parts.push(`${provenCount} proven`);
      if (hiddenCount > 0) parts.push(`${hiddenCount} hidden`);
      btn.textContent = `Authorize (${parts.join(', ')})`;
      break;
    }
    case 'private':
      btn.textContent = 'Authorize privately';
      break;
  }
}

function sendDecision(authorized) {
  if (!NONCE) return;
  const level = getSelectedLevel();
  const decisions = level === 'selective' ? getFactDecisions() : [];
  const message = {
    type: 'pyana:disclosureDecision',
    nonce: NONCE,
    authorized,
    level,
    disclosedFacts: decisions.filter(d => d.disclosure === 'reveal').map(d => tokenFacts[d.index].key),
    facts: decisions,
    mode: level === 'selective' ? 'selective' : level,
    remember: document.getElementById('rememberCheckbox').checked,
  };
  chrome.runtime.sendMessage(message);
  window.close();
}

// ---------------------------------------------------------------------------
// Init
// ---------------------------------------------------------------------------

async function init() {
  if (!NONCE) {
    document.getElementById('originName').textContent = 'Error: no nonce.';
    document.getElementById('authorizeBtn').disabled = true;
    return;
  }
  try {
    const resp = await chrome.runtime.sendMessage({
      type: 'pyana:getPendingDecision',
      nonce: NONCE,
    });
    if (resp && resp.result && resp.result.payload) {
      const p = resp.result.payload;
      origin = p.origin || 'Unknown site';
      action = p.action || 'unknown';
      resource = p.resource || '*';
      tokenFacts = Array.isArray(p.tokenFacts) ? p.tokenFacts : [];
      requiredFacts = Array.isArray(p.requiredFacts) ? p.requiredFacts : [];
      siteRequestedFacts = Array.isArray(p.siteRequestedFacts) ? p.siteRequestedFacts : [];
      initialized = true;
    } else {
      document.getElementById('originName').textContent = 'Error: pending decision not found.';
      document.getElementById('authorizeBtn').disabled = true;
      return;
    }
  } catch (_e) {
    document.getElementById('originName').textContent = 'Error: failed to load request.';
    document.getElementById('authorizeBtn').disabled = true;
    return;
  }

  document.getElementById('originName').textContent = origin;
  document.getElementById('actionName').textContent = action;
  document.getElementById('resourceName').textContent = resource === '*' ? 'all resources' : resource;

  if (siteRequestedFacts.length > 0) {
    const siteRequestEl = document.getElementById('siteRequest');
    siteRequestEl.textContent =
      `This site requests disclosure of: ${siteRequestedFacts.map(f => f.key).join(', ')}. ` +
      `You can decline, which may fail the authorization.`;
    siteRequestEl.classList.add('visible');
  }

  document.getElementById('rememberLabel').textContent =
    `Always use this disclosure level for ${origin}`;

  document.querySelectorAll('.privacy-level').forEach(el => {
    el.addEventListener('click', () => {
      selectLevel(el.dataset.level);
    });
  });

  document.getElementById('authorizeBtn').addEventListener('click', () => {
    sendDecision(true);
  });

  document.getElementById('denyBtn').addEventListener('click', () => {
    sendDecision(false);
  });

  window.addEventListener('beforeunload', () => {
    if (initialized) sendDecision(false);
  });

  buildFactPicker();
  updateAuthorizeButton();

  if (tokenFacts.length === 0) {
    const selectiveEl = document.querySelector('.privacy-level[data-level="selective"]');
    if (selectiveEl) {
      selectiveEl.style.opacity = '0.5';
      selectiveEl.style.pointerEvents = 'none';
      const selectiveDesc = selectiveEl.querySelector('.privacy-level-desc');
      if (selectiveDesc) selectiveDesc.textContent = 'No disclosable facts available for this token.';
    }
  }
}

init();
