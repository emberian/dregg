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
// Build fact picker UI
// ---------------------------------------------------------------------------

function buildFactPicker() {
  const factListEl = document.getElementById('factList');
  factListEl.innerHTML = '';

  // Group facts by category.
  const grouped = {};
  for (const fact of tokenFacts) {
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

      const itemEl = document.createElement('div');
      itemEl.className = 'fact-item' + (required ? ' required' : '');

      const checkbox = document.createElement('input');
      checkbox.type = 'checkbox';
      checkbox.checked = required || siteRequested;
      checkbox.dataset.factKey = fact.key;
      if (required) {
        checkbox.disabled = true;
      }
      checkbox.addEventListener('change', updatePreview);

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

      itemEl.appendChild(checkbox);
      itemEl.appendChild(labelEl);

      if (required) {
        const reqTag = document.createElement('span');
        reqTag.className = 'fact-required-tag';
        reqTag.textContent = 'required';
        itemEl.appendChild(reqTag);
      }

      // Click the row to toggle checkbox.
      itemEl.addEventListener('click', (e) => {
        if (e.target === checkbox) return;
        if (!checkbox.disabled) {
          checkbox.checked = !checkbox.checked;
          updatePreview();
        }
      });

      categoryEl.appendChild(itemEl);
    }

    factListEl.appendChild(categoryEl);
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

  const checked = getCheckedFacts();
  const unchecked = tokenFacts.filter(f => !checked.some(c => c.key === f.key));

  let html = '';
  if (checked.length > 0) {
    html += '<span class="preview-revealed">Revealed: ' +
      checked.map(f => formatFactKey(f.key)).join(', ') + '</span>';
  }
  if (unchecked.length > 0) {
    html += (html ? '<br>' : '') +
      '<span class="preview-hidden">Hidden: ' +
      unchecked.map(f => formatFactKey(f.key)).join(', ') + '</span>';
  }
  previewEl.innerHTML = html;

  updateAuthorizeButton();
}

function getCheckedFacts() {
  const checkboxes = document.querySelectorAll('#factList input[type="checkbox"]');
  const checked = [];
  for (const cb of checkboxes) {
    if (cb.checked) {
      const fact = tokenFacts.find(f => f.key === cb.dataset.factKey);
      if (fact) checked.push(fact);
    }
  }
  return checked;
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
      const count = getCheckedFacts().length;
      btn.textContent = `Authorize with ${count} fact${count !== 1 ? 's' : ''} revealed`;
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
  const message = {
    type: 'pyana:disclosureDecision',
    authorized,
    level,
    disclosedFacts: level === 'selective' ? getCheckedFacts().map(f => f.key) : [],
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
