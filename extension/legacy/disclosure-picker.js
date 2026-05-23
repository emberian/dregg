// Disclosure picker popup script — lets users choose privacy level and facts to reveal.

const params = new URLSearchParams(window.location.search);

// Parse authorization request details from URL params.
const origin = params.get('origin') || 'Unknown site';
const action = params.get('action') || 'unknown';
const resource = params.get('resource') || '*';
let tokenFacts = [];
let requiredFacts = [];
let siteRequestedFacts = [];

try {
  tokenFacts = JSON.parse(decodeURIComponent(params.get('facts') || '[]'));
} catch (e) {
  tokenFacts = [];
}

try {
  requiredFacts = JSON.parse(decodeURIComponent(params.get('required') || '[]'));
} catch (e) {
  requiredFacts = [];
}

try {
  siteRequestedFacts = JSON.parse(decodeURIComponent(params.get('siteRequested') || '[]'));
} catch (e) {
  siteRequestedFacts = [];
}

// ---------------------------------------------------------------------------
// Populate header
// ---------------------------------------------------------------------------

document.getElementById('originName').textContent = origin;
document.getElementById('actionName').textContent = action;
document.getElementById('resourceName').textContent = resource === '*' ? 'all resources' : resource;

// Show site request notice if the site requested specific facts.
if (siteRequestedFacts.length > 0) {
  const siteRequestEl = document.getElementById('siteRequest');
  siteRequestEl.textContent =
    `This site requests disclosure of: ${siteRequestedFacts.map(f => f.key).join(', ')}. ` +
    `You can decline, which may fail the authorization.`;
  siteRequestEl.classList.add('visible');
}

document.getElementById('rememberLabel').textContent =
  `Always use this disclosure level for ${origin}`;

// ---------------------------------------------------------------------------
// Fact categorization
// ---------------------------------------------------------------------------

const FACT_CATEGORIES = {
  permissions: { label: 'Permissions', keys: ['action', 'actions', 'resource', 'service', 'grant', 'scope'] },
  identity: { label: 'Identity', keys: ['user', 'userId', 'org', 'organization', 'email', 'name', 'subject'] },
  temporal: { label: 'Temporal', keys: ['expires', 'expiry', 'issued', 'issuedAt', 'notBefore', 'notAfter'] },
  resource: { label: 'Resource', keys: ['resource', 'domain', 'path', 'uri', 'url', 'target'] },
  metadata: { label: 'Metadata', keys: [] }, // Catch-all
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
  // A fact is required if it's in the requiredFacts list (action/resource are always required).
  return requiredFacts.some(rf => rf.key === fact.key) ||
    fact.key === 'action' || fact.key === 'resource';
}

function isFactSiteRequested(fact) {
  return siteRequestedFacts.some(sf => sf.key === fact.key);
}

// ---------------------------------------------------------------------------
// Numeric fact detection
// ---------------------------------------------------------------------------

function isNumericFact(fact) {
  const val = fact.value;
  if (typeof val === 'number') return true;
  if (typeof val === 'string' && val.trim() !== '' && !isNaN(Number(val))) return true;
  return false;
}

// ---------------------------------------------------------------------------
// Build fact picker UI (three-way: reveal / predicate / hide)
// ---------------------------------------------------------------------------

function buildFactPicker() {
  const factListEl = document.getElementById('factList');
  factListEl.innerHTML = '';

  // Group facts by category.
  const grouped = {};
  for (let i = 0; i < tokenFacts.length; i++) {
    const fact = tokenFacts[i];
    fact._index = i; // Track index for radio name uniqueness.
    const cat = categorizeFact(fact);
    if (!grouped[cat]) grouped[cat] = [];
    grouped[cat].push(fact);
  }

  // Render categories in order.
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

      // Fact label (key + value).
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

      // Three-way disclosure options.
      const optionsEl = document.createElement('div');
      optionsEl.className = 'disclosure-options';

      // Option: Reveal
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

      // Option: Prove Predicate (only for numeric facts, and not required facts)
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
          // Auto-select the predicate radio when user types a threshold.
          predRadio.checked = true;
          updateFactItemMode(itemEl, 'predicate');
          updatePreview();
        });
        predOpt.appendChild(thresholdInput);

        // Tooltip
        const tooltip = document.createElement('span');
        tooltip.className = 'predicate-tooltip';
        tooltip.textContent = '?';
        tooltip.dataset.tooltip = 'Prove that this value satisfies a condition without revealing the exact value';
        predOpt.appendChild(tooltip);

        optionsEl.appendChild(predOpt);
      }

      // Option: Hide
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

      // Attach change listeners to all radios in this item.
      const radios = optionsEl.querySelectorAll('input[type="radio"]');
      for (const radio of radios) {
        radio.addEventListener('change', () => {
          updateFactItemMode(itemEl, radio.value);
          updateActiveOpts(optionsEl, radio.value);
          updatePreview();
        });
      }

      // Set initial mode class.
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

function formatFactKey(key) {
  // Convert camelCase/snake_case to human-readable.
  return key
    .replace(/([A-Z])/g, ' $1')
    .replace(/_/g, ' ')
    .replace(/^\w/, c => c.toUpperCase())
    .trim();
}

function formatFactValue(key, value) {
  // Format values for human readability.
  const lowerKey = key.toLowerCase();
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
// Preview update
// ---------------------------------------------------------------------------

function updatePreview() {
  const previewEl = document.getElementById('preview');
  const level = getSelectedLevel();

  if (level !== 'selective') {
    previewEl.classList.remove('visible');
    return;
  }

  previewEl.classList.add('visible');

  const decisions = getFactDecisions();
  const revealed = decisions.filter(d => d.disclosure === 'reveal');
  const proven = decisions.filter(d => d.disclosure === 'predicate');
  const hidden = decisions.filter(d => d.disclosure === 'hide');

  let html = '';
  if (revealed.length > 0) {
    html += '<span class="preview-revealed">Revealed: ' +
      revealed.map(d => {
        const fact = tokenFacts[d.index];
        return `${formatFactKey(fact.key)}=${formatFactValue(fact.key, fact.value)}`;
      }).join(', ') + '</span>';
  }
  if (proven.length > 0) {
    html += (html ? '<br>' : '') +
      '<span class="preview-proven">Proven: ' +
      proven.map(d => {
        const fact = tokenFacts[d.index];
        const thresholdStr = d.threshold != null ? d.threshold : '?';
        return `${formatFactKey(fact.key)} ≥ ${thresholdStr}`;
      }).join(', ') + '</span>';
  }
  if (hidden.length > 0) {
    html += (html ? '<br>' : '') +
      '<span class="preview-hidden">Hidden: ' +
      hidden.map(d => formatFactKey(tokenFacts[d.index].key)).join(', ') + '</span>';
  }
  previewEl.innerHTML = html;

  updateAuthorizeButton();
}

/**
 * Get the disclosure decision for each fact as a structured array.
 */
function getFactDecisions() {
  const decisions = [];
  for (let i = 0; i < tokenFacts.length; i++) {
    const radioName = `fact-${i}`;
    const selected = document.querySelector(`input[name="${radioName}"]:checked`);
    if (!selected) {
      // Default: required facts are revealed, others hidden.
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

/**
 * Legacy helper: get facts that are set to "reveal" (for backward compat).
 */
function getCheckedFacts() {
  const decisions = getFactDecisions();
  return decisions
    .filter(d => d.disclosure === 'reveal')
    .map(d => tokenFacts[d.index]);
}

// ---------------------------------------------------------------------------
// Privacy level selection
// ---------------------------------------------------------------------------

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

// Attach click handlers to privacy level rows.
document.querySelectorAll('.privacy-level').forEach(el => {
  el.addEventListener('click', () => {
    selectLevel(el.dataset.level);
  });
});

// ---------------------------------------------------------------------------
// Authorize button text
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Decision handlers
// ---------------------------------------------------------------------------

function sendDecision(authorized) {
  const level = getSelectedLevel();
  const decisions = level === 'selective' ? getFactDecisions() : [];
  const message = {
    type: 'pyana:disclosureDecision',
    authorized,
    level,
    // Legacy field for backward compat.
    disclosedFacts: decisions.filter(d => d.disclosure === 'reveal').map(d => tokenFacts[d.index].key),
    // Full structured disclosure spec.
    facts: decisions,
    mode: level === 'selective' ? 'selective' : level,
    remember: document.getElementById('rememberCheckbox').checked,
  };
  chrome.runtime.sendMessage(message);
  window.close();
}

document.getElementById('authorizeBtn').addEventListener('click', () => {
  sendDecision(true);
});

document.getElementById('denyBtn').addEventListener('click', () => {
  sendDecision(false);
});

// If the popup is closed without deciding, treat as denial.
window.addEventListener('beforeunload', () => {
  sendDecision(false);
});

// ---------------------------------------------------------------------------
// Initialization
// ---------------------------------------------------------------------------

buildFactPicker();
updateAuthorizeButton();

// If there are no facts to disclose, disable selective option.
if (tokenFacts.length === 0) {
  const selectiveEl = document.querySelector('.privacy-level[data-level="selective"]');
  selectiveEl.style.opacity = '0.5';
  selectiveEl.style.pointerEvents = 'none';
  const selectiveDesc = selectiveEl.querySelector('.privacy-level-desc');
  selectiveDesc.textContent = 'No disclosable facts available for this token.';
}
