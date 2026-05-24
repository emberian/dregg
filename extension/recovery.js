// Pyana Wallet Recovery — handles mnemonic input validation and wallet restore.

const wordGrid = document.getElementById('wordGrid');
const pasteBtn = document.getElementById('pasteBtn');
const recoverBtn = document.getElementById('recoverBtn');
const passphraseInput = document.getElementById('passphrase');
const resultDiv = document.getElementById('result');

// Create 24 word inputs.
const wordInputs = [];
for (let i = 0; i < 24; i++) {
  const wrapper = document.createElement('div');
  wrapper.className = 'word-input-wrapper';

  const number = document.createElement('span');
  number.className = 'word-number';
  number.textContent = String(i + 1);

  const input = document.createElement('input');
  input.type = 'text';
  input.className = 'word-input';
  input.autocomplete = 'off';
  input.spellcheck = false;
  input.dataset.index = i;

  wrapper.appendChild(number);
  wrapper.appendChild(input);
  wordGrid.appendChild(wrapper);
  wordInputs.push(input);
}

// Validate on input and enable/disable recover button.
function validateInputs() {
  let allFilled = true;
  for (const input of wordInputs) {
    const word = input.value.trim().toLowerCase();
    if (!word) {
      allFilled = false;
      input.classList.remove('valid', 'invalid');
    } else {
      // Basic validation: only letters, reasonable length.
      const valid = /^[a-z]{3,8}$/.test(word);
      input.classList.toggle('valid', valid);
      input.classList.toggle('invalid', !valid);
      if (!valid) allFilled = false;
    }
  }
  recoverBtn.disabled = !allFilled;
}

wordInputs.forEach(input => {
  input.addEventListener('input', (e) => {
    // If user pastes multiple words into one field, distribute them.
    const val = e.target.value.trim();
    const words = val.split(/\s+/);
    if (words.length > 1) {
      const startIdx = parseInt(e.target.dataset.index);
      for (let i = 0; i < words.length && (startIdx + i) < 24; i++) {
        wordInputs[startIdx + i].value = words[i].toLowerCase();
      }
    }
    validateInputs();
  });

  input.addEventListener('keydown', (e) => {
    if (e.key === ' ' || e.key === 'Tab') {
      // Move to next input.
      const idx = parseInt(e.target.dataset.index);
      if (idx < 23) {
        e.preventDefault();
        wordInputs[idx + 1].focus();
      }
    }
  });
});

// Paste button: paste from clipboard and distribute words.
// P2-4: warn the user that the mnemonic is in the OS clipboard (visible to
// other apps / clipboard managers), and wipe the clipboard after reading.
pasteBtn.addEventListener('click', async () => {
  const proceed = window.confirm(
    'About to read your 24-word recovery phrase from the system clipboard.\n\n' +
    'Other apps and clipboard managers may have already seen this phrase. ' +
    'After reading, we will wipe the clipboard. Continue?'
  );
  if (!proceed) return;

  try {
    const text = await navigator.clipboard.readText();
    const words = text.trim().split(/\s+/);
    for (let i = 0; i < 24 && i < words.length; i++) {
      wordInputs[i].value = words[i].toLowerCase();
    }
    validateInputs();
    // Wipe clipboard so the phrase isn't left available to other apps.
    try {
      await navigator.clipboard.writeText('');
    } catch (_e) {
      // Best effort; some browsers require focus.
    }
  } catch (e) {
    // Clipboard API may not be available in extension context.
    resultDiv.textContent = 'Clipboard access denied. Please paste words manually.';
    resultDiv.className = 'result error';
    resultDiv.style.display = 'block';
  }
});

// Recover button: validate mnemonic and send to background.
recoverBtn.addEventListener('click', async () => {
  recoverBtn.disabled = true;
  recoverBtn.textContent = 'Recovering...';
  resultDiv.style.display = 'none';

  const words = wordInputs.map(input => input.value.trim().toLowerCase());
  const mnemonic = words.join(' ');
  const passphrase = passphraseInput.value;

  try {
    const id = `recovery_${Date.now()}`;
    const response = await chrome.runtime.sendMessage({
      type: 'pyana:recover',
      id,
      mnemonic,
      passphrase,
    });

    if (response?.result?.success) {
      resultDiv.textContent = 'Wallet recovered successfully! You can close this tab.';
      resultDiv.className = 'result success';
      resultDiv.style.display = 'block';
      // Clear inputs for security.
      wordInputs.forEach(input => { input.value = ''; });
      passphraseInput.value = '';
    } else {
      const error = response?.result?.error || response?.error || 'Recovery failed';
      resultDiv.textContent = error;
      resultDiv.className = 'result error';
      resultDiv.style.display = 'block';
      recoverBtn.disabled = false;
    }
  } catch (e) {
    resultDiv.textContent = 'Error: ' + e.message;
    resultDiv.className = 'result error';
    resultDiv.style.display = 'block';
    recoverBtn.disabled = false;
  }

  recoverBtn.textContent = 'Recover Wallet';
});

// Focus first input on load.
wordInputs[0].focus();
