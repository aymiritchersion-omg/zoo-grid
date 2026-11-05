/* Zoo Grid - a "one animal per row, column and color" logic puzzle. Vanilla JS, no deps. */
(function () {
  'use strict';

  // ---------- Tuning ----------
  var HINTS_PER_LEVEL = 3;
  var AD_EVERY_LEVELS = 3;                 // midgame ad on every Nth level start
  var ANIMALS = ['pig', 'chick', 'frog', 'duck', 'penguin', 'panda', 'owl', 'rabbit', 'cow', 'monkey', 'elephant', 'hippo', 'bear', 'parrot', 'sloth', 'zebra'];
  var REGION_COLORS = ['#ffd3d3', '#cfe9ff', '#d9f2c4', '#fff0b3', '#e7d5ff', '#ffdcb8', '#c9f0ea', '#f9cfe9', '#e6e0c8', '#d4e6b5', '#cfd8f5', '#ffe2c2'];

  function sizeForLevel(level) {
    if (level <= 4) return 5;
    if (level <= 12) return 6;
    if (level <= 25) return 7;
    if (level <= 45) return 8;
    return 9;
  }

  // ---------- Seeded random ----------
  function mulberry32(seed) {
    var a = seed >>> 0;
    return function () {
      a = (a + 0x6D2B79F5) >>> 0;
      var t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // ---------- Puzzle generator ----------
  // 1) place n animals: one per row/col, consecutive rows never adjacent (that covers diagonal touching)
  function randomPlacement(n, rng) {
    var cols = [], used = [];
    function go(row) {
      if (row === n) return true;
      var order = [];
      for (var c = 0; c < n; c++) order.push(c);
      for (var i = order.length - 1; i > 0; i--) { var j = Math.floor(rng() * (i + 1)); var t = order[i]; order[i] = order[j]; order[j] = t; }
      for (var k = 0; k < order.length; k++) {
        var c2 = order[k];
        if (used[c2]) continue;
        if (row > 0 && Math.abs(c2 - cols[row - 1]) <= 1) continue;
        used[c2] = true; cols[row] = c2;
        if (go(row + 1)) return true;
        used[c2] = false;
      }
      return false;
    }
    return go(0) ? cols : null;
  }
  // 2) grow n regions from those cells until the board is covered
  function growRegions(n, cols, rng) {
    var reg = [];
    for (var r = 0; r < n; r++) { reg.push([]); for (var c = 0; c < n; c++) reg[r].push(-1); }
    for (var i = 0; i < n; i++) reg[i][cols[i]] = i;
    var left = n * n - n, active = [];
    for (var a = 0; a < n; a++) active.push(a);
    var dirs = [[1, 0], [-1, 0], [0, 1], [0, -1]];
    while (left > 0 && active.length) {
      var ai = Math.floor(rng() * active.length), id = active[ai];
      // every empty cell next to this region
      var cand = [];
      for (var r2 = 0; r2 < n; r2++) for (var c2 = 0; c2 < n; c2++) {
        if (reg[r2][c2] !== id) continue;
        for (var d = 0; d < 4; d++) {
          var nr = r2 + dirs[d][0], nc = c2 + dirs[d][1];
          if (nr >= 0 && nr < n && nc >= 0 && nc < n && reg[nr][nc] === -1) cand.push([nr, nc]);
        }
      }
      if (!cand.length) { active.splice(ai, 1); continue; }
      var pick = cand[Math.floor(rng() * cand.length)];
      reg[pick[0]][pick[1]] = id; left--;
    }
    if (left > 0) return null;
    return reg;
  }
  // 3) count solutions (stop at 2) so we only keep puzzles with exactly one answer
  function countSolutions(n, reg, limit) {
    var count = 0, usedCol = [], usedReg = [], prev = -5;
    function go(row, prevCol) {
      if (count >= limit) return;
      if (row === n) { count++; return; }
      for (var c = 0; c < n; c++) {
        if (usedCol[c] || usedReg[reg[row][c]]) continue;
        if (Math.abs(c - prevCol) <= 1) continue;
        usedCol[c] = true; usedReg[reg[row][c]] = true;
        go(row + 1, c);
        usedCol[c] = false; usedReg[reg[row][c]] = false;
      }
    }
    go(0, prev);
    return count;
  }
  // 4) if a board has several answers, nudge region borders one cell at a time until only one is left
  function regionConnected(n, reg, id, skipR, skipC) {
    var start = null, seen = {}, stack = [], total = 0;
    for (var r = 0; r < n; r++) for (var c = 0; c < n; c++) {
      if (reg[r][c] === id && !(r === skipR && c === skipC)) { total++; if (!start) start = [r, c]; }
    }
    if (!start) return false;
    stack.push(start); seen[start[0] + ',' + start[1]] = true;
    var cnt = 0, dirs = [[1, 0], [-1, 0], [0, 1], [0, -1]];
    while (stack.length) {
      var cur = stack.pop(); cnt++;
      for (var d = 0; d < 4; d++) {
        var nr = cur[0] + dirs[d][0], nc = cur[1] + dirs[d][1];
        if (nr < 0 || nr >= n || nc < 0 || nc >= n) continue;
        if (nr === skipR && nc === skipC) continue;
        if (reg[nr][nc] !== id || seen[nr + ',' + nc]) continue;
        seen[nr + ',' + nc] = true; stack.push([nr, nc]);
      }
    }
    return cnt === total;
  }
  function repairUniqueness(n, reg, cols, rng) {
    var LIMIT = 24, count = countSolutions(n, reg, LIMIT), maxIter = n >= 9 ? 2500 : n >= 8 ? 1200 : 600;
    var dirs = [[1, 0], [-1, 0], [0, 1], [0, -1]];
    for (var iter = 0; iter < maxIter && count > 1; iter++) {
      var r = Math.floor(rng() * n), c = Math.floor(rng() * n);
      if (cols[r] === c) continue;                          // never move an answer cell
      var id = reg[r][c], d = dirs[Math.floor(rng() * 4)];
      var nr = r + d[0], nc = c + d[1];
      if (nr < 0 || nr >= n || nc < 0 || nc >= n) continue;
      var nid = reg[nr][nc];
      if (nid === id) continue;
      if (!regionConnected(n, reg, id, r, c)) continue;      // the old region must stay in one piece
      reg[r][c] = nid;
      var c2 = countSolutions(n, reg, LIMIT);
      if (c2 <= count && c2 > 0) count = c2; else reg[r][c] = id;
    }
    return count === 1;
  }
  function makePuzzle(n, seed) {
    var rng = mulberry32(seed);
    for (var attempt = 0; attempt < 40; attempt++) {
      var cols = randomPlacement(n, rng);
      if (!cols) continue;
      var reg = growRegions(n, cols, rng);
      if (!reg) continue;
      if (countSolutions(n, reg, 2) === 1 || repairUniqueness(n, reg, cols, rng)) return { n: n, regions: reg, solution: cols };
    }
    return null;
  }

  // ---------- DOM ----------
  var $ = function (id) { return document.getElementById(id); };
  var elBoard = $('board'), elLevel = $('level'), elLevelLbl = $('level-lbl'), elTime = $('time');
  var elGoalImg = $('goal-img'), elGoalText = $('goal-text'), elRuleAnimal = $('rule-animal');
  var elOverlay = $('overlay'), elFinalTime = $('final-time'), elBestBadge = $('best-badge');
  var btnNext = $('btn-next'), btnDailyDone = $('btn-daily-done');
  var btnMute = $('btn-mute'), btnUndo = $('btn-undo'), btnHint = $('btn-hint'), btnClear = $('btn-clear'), btnDaily = $('btn-daily'), btnRestart = $('btn-restart');
  var elHintCount = $('hint-count');
  var elHelp = $('help'), elDemo = $('demo'), btnHelp = $('btn-help'), btnHelpClose = $('btn-help-close');
  var stage = $('stage');
  var elToast = document.createElement('div'); elToast.id = 'toast'; $('board-wrap').appendChild(elToast);

  // ---------- State ----------
  var level = 1, daily = false, puzzle = null, n = 5, animal = 'pig';
  var grid = [], cells = [], history = [];
  var hints = HINTS_PER_LEVEL, solved = false;
  var startAt = 0, elapsed = 0, timerId = null;
  var muted = false, sdk = null;
  var best = {};

  function save() {
    try {
      localStorage.setItem('zoogrid_level', String(level));
      localStorage.setItem('zoogrid_best', JSON.stringify(best));
      localStorage.setItem('zoogrid_muted', muted ? '1' : '0');
    } catch (e) {}
  }
  function load() {
    try {
      level = parseInt(localStorage.getItem('zoogrid_level') || '1', 10) || 1;
      best = JSON.parse(localStorage.getItem('zoogrid_best') || '{}') || {};
      muted = localStorage.getItem('zoogrid_muted') === '1';
    } catch (e) { level = 1; best = {}; muted = false; }
  }

  // ---------- Sound (synthesized) ----------
  var audio = null;
  function getAudio() {
    if (!audio) { try { audio = new (window.AudioContext || window.webkitAudioContext)(); } catch (e) { return null; } }
    if (audio.state === 'suspended') audio.resume();
    return audio;
  }
  function ac() { return muted ? null : getAudio(); }
  function tone(f, dur, type, vol, when) {
    var a = ac(); if (!a) return;
    var t = a.currentTime + (when || 0);
    var o = a.createOscillator(), g = a.createGain();
    o.type = type || 'sine'; o.frequency.setValueAtTime(f, t);
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(vol || 0.2, t + 0.01);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g).connect(a.destination);
    o.start(t); o.stop(t + dur + 0.05);
  }
  function sfxTap() { tone(660, 0.08, 'sine', 0.12); }
  function sfxPlace() { tone(520, 0.12, 'sine', 0.2); tone(780, 0.14, 'sine', 0.12, 0.05); }
  function sfxErr() { tone(180, 0.18, 'square', 0.08); }
  function sfxWin() { [523, 659, 784, 1047].forEach(function (f, i) { tone(f, 0.35, 'triangle', 0.2, i * 0.11); }); }
  function sfxHint() { tone(880, 0.1, 'sine', 0.15); tone(1174, 0.2, 'sine', 0.15, 0.08); }

  // ---------- Haptics ----------
  var iosSwitch = $('haptic-switch');
  function haptic(kind) {
    if (muted) return;
    var pattern = kind === 'place' ? 12 : kind === 'err' ? [30, 40, 30] : kind === 'win' ? [20, 40, 20, 40, 60] : 6;
    try { if (navigator.vibrate && navigator.vibrate(pattern)) return; } catch (e) {}
    if (iosSwitch && /iPhone|iPad/.test(navigator.userAgent)) { try { iosSwitch.click(); } catch (e) {} }
  }

  // ---------- CrazyGames SDK (safe when absent) ----------
  function initSDK() {
    if (!window.CrazyGames || !window.CrazyGames.SDK) return Promise.resolve();
    return window.CrazyGames.SDK.init().then(function () { sdk = window.CrazyGames.SDK; }).catch(function () { sdk = null; });
  }
  function sdkCall(path) {
    if (!sdk) return;
    try { var parts = path.split('.'), fn = sdk; for (var i = 0; i < parts.length; i++) fn = fn[parts[i]]; if (typeof fn === 'function') fn.call(sdk[parts[0]]); } catch (e) {}
  }
  function adsAvailable() { return !!(sdk && sdk.environment !== 'disabled'); }
  function maybeMidgameAd(then) {
    if (!adsAvailable() || daily || level % AD_EVERY_LEVELS !== 1 || level === 1) { then(); return; }
    var was = muted;
    try { sdk.ad.requestAd('midgame', { adStarted: function () { muted = true; }, adFinished: function () { muted = was; then(); }, adError: function () { muted = was; then(); } }); }
    catch (e) { muted = was; then(); }
  }
  function rewardedAd(onReward) {
    if (!adsAvailable()) return;
    var was = muted;
    try { sdk.ad.requestAd('rewarded', { adStarted: function () { muted = true; }, adFinished: function () { muted = was; onReward(); }, adError: function () { muted = was; } }); }
    catch (e) { muted = was; }
  }

  // ---------- Helpers ----------
  function fitStage() {
    var s = Math.min(window.innerWidth / 440, window.innerHeight / 840);
    stage.style.transform = 'translate(-50%, -50%) scale(' + s + ')';
  }
  function fmt(ms) { var s = Math.floor(ms / 1000); return Math.floor(s / 60) + ':' + ('0' + (s % 60)).slice(-2); }
  function toast(text) {
    elToast.textContent = text; elToast.classList.add('show');
    clearTimeout(toast.t); toast.t = setTimeout(function () { elToast.classList.remove('show'); }, 1400);
  }
  function dailySeed() {
    var d = new Date();
    return d.getFullYear() * 10000 + (d.getMonth() + 1) * 100 + d.getDate();
  }
  function dailyKey() { return 'daily-' + dailySeed(); }
  function imgSrc(name) { return 'assets/animals/' + name + '.png'; }

  // ---------- Help card (first launch, and the ? button) ----------
  var DEMO_REGIONS = [[0, 0, 0, 1], [2, 2, 3, 1], [2, 3, 3, 1], [2, 3, 3, 1]];
  var DEMO_SOLUTION = [1, 3, 0, 2];       // column of the animal in each row
  var helpOpenedAt = 0;
  function buildDemo() {
    elDemo.innerHTML = '';
    for (var r = 0; r < 4; r++) for (var c = 0; c < 4; c++) {
      var d = document.createElement('div');
      d.className = 'cell';
      d.style.background = REGION_COLORS[DEMO_REGIONS[r][c]];
      if (r === 0 || DEMO_REGIONS[r - 1][c] !== DEMO_REGIONS[r][c]) d.classList.add('bt');
      if (r === 3 || DEMO_REGIONS[r + 1][c] !== DEMO_REGIONS[r][c]) d.classList.add('bb');
      if (c === 0 || DEMO_REGIONS[r][c - 1] !== DEMO_REGIONS[r][c]) d.classList.add('bl');
      if (c === 3 || DEMO_REGIONS[r][c + 1] !== DEMO_REGIONS[r][c]) d.classList.add('br');
      if (DEMO_SOLUTION[r] === c) { var img = document.createElement('img'); img.src = imgSrc(animal); img.alt = ''; d.appendChild(img); }
      else { var x = document.createElement('div'); x.className = 'x'; d.appendChild(x); }
      elDemo.appendChild(d);
    }
  }
  function openHelp() {
    buildDemo();
    helpOpenedAt = performance.now();
    elHelp.classList.remove('hidden');
  }
  function closeHelp() {
    if (helpOpenedAt && !solved) startAt += performance.now() - helpOpenedAt;   // the clock does not run while reading
    helpOpenedAt = 0;
    elHelp.classList.add('hidden');
    try { localStorage.setItem('zoogrid_seen', '1'); } catch (e) {}
  }
  btnHelp.addEventListener('click', openHelp);
  btnHelpClose.addEventListener('click', closeHelp);

  // ---------- Level flow ----------
  function startLevel() {
    solved = false; history = []; hints = HINTS_PER_LEVEL;
    if (daily) {
      n = 7; puzzle = makePuzzle(n, dailySeed() * 7 + 13);
      animal = ANIMALS[dailySeed() % ANIMALS.length];
      elLevelLbl.textContent = 'Daily'; elLevel.textContent = (new Date().getMonth() + 1) + '/' + new Date().getDate();
    } else {
      n = sizeForLevel(level); puzzle = makePuzzle(n, 1000 + level * 7919);
      animal = ANIMALS[(level - 1) % ANIMALS.length];
      elLevelLbl.textContent = 'Level'; elLevel.textContent = level;
    }
    for (var extra = 1; !puzzle && extra <= 6; extra++) puzzle = makePuzzle(n, (daily ? dailySeed() : 1000 + level * 7919) + extra * 101);   // same fallback for everyone
    grid = []; for (var r = 0; r < n; r++) { grid.push([]); for (var c = 0; c < n; c++) grid[r].push(0); }
    elGoalImg.src = imgSrc(animal); elGoalText.textContent = 'Place ' + n;
    elRuleAnimal.textContent = animal;
    buildBoard();
    renderTools();
    elOverlay.classList.add('hidden');
    elapsed = 0; startAt = performance.now(); elTime.textContent = '0:00';
    clearInterval(timerId);
    timerId = setInterval(function () { if (!solved) { elapsed = performance.now() - startAt; elTime.textContent = fmt(elapsed); } }, 250);
    sdkCall('game.gameplayStart');
  }

  function buildBoard() {
    elBoard.innerHTML = '';
    elBoard.style.gridTemplateColumns = 'repeat(' + n + ', 1fr)';
    elBoard.style.gridTemplateRows = 'repeat(' + n + ', 1fr)';
    cells = [];
    var reg = puzzle.regions;
    for (var r = 0; r < n; r++) {
      cells.push([]);
      for (var c = 0; c < n; c++) {
        var d = document.createElement('div');
        d.className = 'cell';
        d.style.background = REGION_COLORS[reg[r][c] % REGION_COLORS.length];
        if (r === 0 || reg[r - 1][c] !== reg[r][c]) d.classList.add('bt');
        if (r === n - 1 || reg[r + 1][c] !== reg[r][c]) d.classList.add('bb');
        if (c === 0 || reg[r][c - 1] !== reg[r][c]) d.classList.add('bl');
        if (c === n - 1 || reg[r][c + 1] !== reg[r][c]) d.classList.add('br');
        d.dataset.r = r; d.dataset.c = c;
        elBoard.appendChild(d);
        cells[r].push(d);
      }
    }
  }

  function renderCell(r, c) {
    var d = cells[r][c], v = grid[r][c];
    d.innerHTML = '';
    if (v === 1) { var x = document.createElement('div'); x.className = 'x'; d.appendChild(x); }
    else if (v === 2) { var img = document.createElement('img'); img.src = imgSrc(animal); img.alt = ''; d.appendChild(img); }
  }
  function setCell(r, c, v, silent) {
    if (grid[r][c] === v) return;
    if (!silent) history.push([r, c, grid[r][c]]);
    grid[r][c] = v;
    renderCell(r, c);
    cells[r][c].classList.remove('hinted');
  }

  function checkConflicts() {
    var reg = puzzle.regions, bad = {}, placed = [];
    for (var r = 0; r < n; r++) for (var c = 0; c < n; c++) if (grid[r][c] === 2) placed.push([r, c]);
    for (var i = 0; i < placed.length; i++) for (var j = i + 1; j < placed.length; j++) {
      var a = placed[i], b = placed[j];
      var clash = a[0] === b[0] || a[1] === b[1] || reg[a[0]][a[1]] === reg[b[0]][b[1]] ||
                  (Math.abs(a[0] - b[0]) <= 1 && Math.abs(a[1] - b[1]) <= 1);
      if (clash) { bad[a[0] + ',' + a[1]] = true; bad[b[0] + ',' + b[1]] = true; }
    }
    for (var r2 = 0; r2 < n; r2++) for (var c2 = 0; c2 < n; c2++) cells[r2][c2].classList.toggle('conflict', !!bad[r2 + ',' + c2]);
    return { placed: placed.length, conflicts: Object.keys(bad).length };
  }

  function afterChange() {
    var st = checkConflicts();
    renderTools();
    if (st.placed === n && st.conflicts === 0) win();
  }

  function win() {
    solved = true;
    elapsed = performance.now() - startAt; elTime.textContent = fmt(elapsed);
    var key = daily ? dailyKey() : 'size' + n;
    var isBest = !best[key] || elapsed < best[key];
    if (isBest) { best[key] = Math.round(elapsed); }
    if (!daily) level++;
    save();
    for (var r = 0; r < n; r++) for (var c = 0; c < n; c++) if (grid[r][c] === 2) cells[r][c].classList.add('won');
    sfxWin(); haptic('win');
    sdkCall('game.gameplayStop'); sdkCall('game.happytime');
    elFinalTime.textContent = fmt(elapsed);
    elBestBadge.classList.toggle('hidden', !isBest);
    btnNext.classList.toggle('hidden', daily);
    btnDailyDone.classList.toggle('hidden', !daily);
    setTimeout(function () { elOverlay.classList.remove('hidden'); }, 650);
  }

  // ---------- Tools ----------
  function renderTools() {
    elHintCount.textContent = hints > 0 ? hints : (adsAvailable() ? 'AD' : '0');
    elHintCount.classList.toggle('ad', hints === 0 && adsAvailable());
    btnHint.classList.toggle('disabled', hints === 0 && !adsAvailable());
    btnUndo.classList.toggle('disabled', history.length === 0);
    btnDaily.classList.toggle('active', daily);
  }
  function undo() {
    if (solved || !history.length) return;
    var h = history.pop();
    setCell(h[0], h[1], h[2], true);
    sfxTap(); afterChange();
  }
  function clearBoard() {
    if (solved) return;
    for (var r = 0; r < n; r++) for (var c = 0; c < n; c++) setCell(r, c, 0, true);
    history = []; sfxTap(); afterChange();
  }
  function hint() {
    if (solved) return;
    if (hints <= 0) { rewardedAd(function () { hints++; renderTools(); }); return; }
    // first fix a wrongly placed animal, otherwise reveal a correct one
    var sol = puzzle.solution;
    for (var r = 0; r < n; r++) for (var c = 0; c < n; c++) {
      if (grid[r][c] === 2 && sol[r] !== c) { hints--; setCell(r, c, 1); cells[r][c].classList.add('hinted'); sfxHint(); toast('That one was wrong'); afterChange(); return; }
    }
    var open = [];
    for (var r2 = 0; r2 < n; r2++) if (grid[r2][sol[r2]] !== 2) open.push(r2);
    if (!open.length) return;
    var row = open[Math.floor(Math.random() * open.length)];
    hints--;
    setCell(row, sol[row], 2); cells[row][sol[row]].classList.add('hinted');
    sfxHint(); haptic('place'); afterChange();
  }

  // ---------- Input: tap cycles empty -> X -> animal; drag paints X's ----------
  var pressing = false, dragMode = null, startCell = null, moved = false, lastCell = null;
  function cellAt(x, y) {
    var el = document.elementFromPoint(x, y);
    while (el && el !== elBoard && !el.classList.contains('cell')) el = el.parentNode;
    return el && el.classList && el.classList.contains('cell') ? el : null;
  }
  elBoard.addEventListener('pointerdown', function (e) {
    if (solved) return;
    var d = cellAt(e.clientX, e.clientY); if (!d) return;
    pressing = true; moved = false; startCell = d; lastCell = d; dragMode = null;
    getAudio();
    e.preventDefault();
  });
  elBoard.addEventListener('pointermove', function (e) {
    if (!pressing || solved) return;
    var d = cellAt(e.clientX, e.clientY);
    if (!d || d === lastCell) return;
    if (!dragMode) {
      var sv = grid[startCell.dataset.r][startCell.dataset.c];
      dragMode = sv === 0 ? 'mark' : sv === 1 ? 'erase' : 'none';
      if (dragMode === 'mark') setCell(+startCell.dataset.r, +startCell.dataset.c, 1);
      if (dragMode === 'erase') setCell(+startCell.dataset.r, +startCell.dataset.c, 0);
    }
    moved = true; lastCell = d;
    var r = +d.dataset.r, c = +d.dataset.c;
    if (dragMode === 'mark' && grid[r][c] === 0) { setCell(r, c, 1); sfxTap(); }
    if (dragMode === 'erase' && grid[r][c] === 1) { setCell(r, c, 0); sfxTap(); }
  });
  function endPress(e) {
    if (!pressing) return;
    pressing = false;
    if (solved) return;
    if (!moved && startCell) {
      var r = +startCell.dataset.r, c = +startCell.dataset.c, v = grid[r][c];
      var nv = v === 0 ? 1 : v === 1 ? 2 : 0;
      setCell(r, c, nv);
      if (nv === 2) { sfxPlace(); haptic('place'); } else { sfxTap(); haptic('tap'); }
      var st = checkConflicts();
      if (nv === 2 && st.conflicts) { sfxErr(); haptic('err'); }
      renderTools();
      if (st.placed === n && st.conflicts === 0) win();
    } else {
      afterChange();
    }
    startCell = null; dragMode = null;
  }
  elBoard.addEventListener('pointerup', endPress);
  elBoard.addEventListener('pointercancel', endPress);
  window.addEventListener('pointerup', endPress);

  btnUndo.addEventListener('click', undo);
  btnClear.addEventListener('click', clearBoard);
  btnHint.addEventListener('click', hint);
  btnNext.addEventListener('click', function () { daily = false; maybeMidgameAd(startLevel); });
  btnDailyDone.addEventListener('click', function () { daily = false; startLevel(); });
  btnDaily.addEventListener('click', function () {
    daily = !daily;
    if (daily && best[dailyKey()]) { toast('Daily done in ' + fmt(best[dailyKey()])); }
    startLevel();
  });
  btnRestart.addEventListener('click', function () { if (solved && !daily) { startLevel(); return; } clearBoard(); });
  function renderMute() { btnMute.classList.toggle('off', muted); }
  btnMute.addEventListener('click', function () { muted = !muted; save(); renderMute(); });
  window.addEventListener('keydown', function (e) {
    if (e.key === 'z' && (e.ctrlKey || e.metaKey)) { undo(); e.preventDefault(); }
  });
  window.addEventListener('resize', fitStage);

  // ---------- Boot ----------
  load(); renderMute(); fitStage();
  initSDK().then(function () {
    sdkCall('game.loadingStart');
    var pre = ANIMALS.map(function (a) { return new Promise(function (res) { var i = new Image(); i.onload = res; i.onerror = res; i.src = imgSrc(a); }); });
    if (document.fonts && document.fonts.load) pre.push(document.fonts.load('700 20px Fredoka').catch(function () {}));
    return Promise.all(pre);
  }).then(function () {
    sdkCall('game.loadingStop');
    startLevel();
    var seen = false;
    try { seen = localStorage.getItem('zoogrid_seen') === '1'; } catch (e) {}
    if (!seen) openHelp();
  });
})();
