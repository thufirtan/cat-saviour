(() => {
  'use strict';

  // ---------------------------------------------------------------- tuning
  const CONFIG = {
    cols: 41,               // must be odd
    rows: 25,               // must be odd
    tile: 24,
    braid: 0.1,             // chance of knocking out a wall to create loops

    playerSpeed: 6.5,       // tiles per second
    speedBoost: 1.6,
    speedTime: 7,
    invisTime: 6,
    maxPunchLevel: 3,
    punchCooldown: 0.3,

    escapeTime: 38,         // seconds the burglar needs to stroll home on level 1
    escapeTimeStep: 3,      // ...shrinks by this much each level
    escapeTimeMin: 20,
    burglarHeadStart: 0.25, // fraction of the route he has already covered
    burglarSprint: 4.8,     // speed once he spots Clarence
    burglarAlert: 4,        // tiles at which he spots Clarence

    goonSpeed: 3.4,
    goonSight: 7,           // path distance at which goons give chase
    goonHitStun: 1.2,
    goonHitCoins: 2,

    coins: 28,
    speedUps: 3,
    punchUps: 3,
    invisUps: 3,
  };

  const W = CONFIG.cols, H = CONFIG.rows, T = CONFIG.tile;
  const WALL = 1, FLOOR = 0;
  const KEY_DIRS = {
    KeyW: { x: 0, y: -1 },
    KeyS: { x: 0, y: 1 },
    KeyA: { x: -1, y: 0 },
    KeyD: { x: 1, y: 0 },
  };
  const DIR_LIST = Object.values(KEY_DIRS);
  const ITEM_ICON = { speed: '⚡', punch: '🥊', invis: '👻' };
  const ITEM_COLOR = { speed: '#3fd0ff', punch: '#ff6b5e', invis: '#b693ff' };

  // ---------------------------------------------------------------- helpers
  const idx = (x, y) => y * W + x;
  const rand = (n) => Math.floor(Math.random() * n);
  const pick = (arr) => arr[rand(arr.length)];
  const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
  const tileOf = (e) => ({ x: Math.round(e.x), y: Math.round(e.y) });
  const interior = (x, y) => x > 0 && y > 0 && x < W - 1 && y < H - 1;

  function shuffle(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = rand(i + 1);
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  // ---------------------------------------------------------------- maze
  function generateMaze() {
    const grid = new Uint8Array(W * H).fill(WALL);
    const stack = [[1, 1]];
    grid[idx(1, 1)] = FLOOR;
    while (stack.length) {
      const [x, y] = stack[stack.length - 1];
      const options = DIR_LIST.filter((d) => {
        const nx = x + d.x * 2, ny = y + d.y * 2;
        return interior(nx, ny) && grid[idx(nx, ny)] === WALL;
      });
      if (!options.length) { stack.pop(); continue; }
      const d = pick(options);
      grid[idx(x + d.x, y + d.y)] = FLOOR;
      grid[idx(x + d.x * 2, y + d.y * 2)] = FLOOR;
      stack.push([x + d.x * 2, y + d.y * 2]);
    }
    // Knock out some walls between corridors so there is more than one route.
    for (let y = 1; y < H - 1; y++) {
      for (let x = 1; x < W - 1; x++) {
        const between = (x % 2) !== (y % 2);
        if (between && grid[idx(x, y)] === WALL && Math.random() < CONFIG.braid) {
          grid[idx(x, y)] = FLOOR;
        }
      }
    }
    return grid;
  }

  // Path distance from (sx, sy) to every reachable tile; -1 if unreachable.
  function distanceMap(grid, sx, sy) {
    const dist = new Int16Array(W * H).fill(-1);
    const queue = [idx(sx, sy)];
    dist[queue[0]] = 0;
    for (let head = 0; head < queue.length; head++) {
      const cur = queue[head];
      const cx = cur % W, cy = (cur - cx) / W;
      for (const d of DIR_LIST) {
        const n = idx(cx + d.x, cy + d.y);
        if (grid[n] === FLOOR && dist[n] === -1) {
          dist[n] = dist[cur] + 1;
          queue.push(n);
        }
      }
    }
    return dist;
  }

  // Open neighbour of (x, y) that is closest to the source of `dist`.
  function downhill(grid, dist, x, y) {
    let best = null, bestDist = dist[idx(x, y)];
    for (const d of DIR_LIST) {
      const n = idx(x + d.x, y + d.y);
      if (grid[n] === FLOOR && dist[n] !== -1 && dist[n] < bestDist) {
        best = d;
        bestDist = dist[n];
      }
    }
    return best;
  }

  // ---------------------------------------------------------------- state
  const state = {
    mode: 'intro',   // intro | playing | won | lost
    level: 1,
    time: 0,
    grid: null,
    home: { x: W - 2, y: H - 2 },
    homeDist: null,
    playerDist: null,
    playerTile: -1,
    startDist: 1,
    player: null,
    burglar: null,
    goons: [],
    items: new Map(),
    floaters: [],
    punchFx: null,
  };

  const held = [];   // movement keys currently held, most recent last

  function makeEntity(x, y) {
    return { x, y, cx: x, cy: y, tx: x, ty: y, moving: false, dir: DIR_LIST[1], stunT: 0 };
  }

  function startLevel(level) {
    const grid = generateMaze();
    const home = state.home;
    const homeDist = distanceMap(grid, home.x, home.y);

    // The burglar is already part-way along his route home.
    const route = [{ x: 1, y: 1 }];
    for (;;) {
      const last = route[route.length - 1];
      const d = downhill(grid, homeDist, last.x, last.y);
      if (!d) break;
      route.push({ x: last.x + d.x, y: last.y + d.y });
    }
    const startAt = route[Math.floor(route.length * CONFIG.burglarHeadStart)];
    const burglar = makeEntity(startAt.x, startAt.y);
    const remaining = homeDist[idx(startAt.x, startAt.y)];
    const escapeTime = Math.max(
      CONFIG.escapeTimeMin,
      CONFIG.escapeTime - CONFIG.escapeTimeStep * (level - 1),
    );
    burglar.walk = clamp(remaining / escapeTime, 1.6, 4.6);

    const player = makeEntity(1, 1);
    Object.assign(player, {
      face: DIR_LIST[1], coins: 0, punchLevel: 1, speedT: 0, invisT: 0, punchCd: 0,
    });

    const fromPlayer = distanceMap(grid, 1, 1);
    const free = [];
    for (let y = 1; y < H - 1; y++) {
      for (let x = 1; x < W - 1; x++) {
        const i = idx(x, y);
        if (grid[i] === FLOOR && fromPlayer[i] > 0 && homeDist[i] > 0) free.push(i);
      }
    }
    shuffle(free);

    const items = new Map();
    const place = (type, count) => {
      for (let n = 0; n < count && free.length; n++) items.set(free.pop(), type);
    };
    place('coin', CONFIG.coins);
    place('speed', CONFIG.speedUps);
    place('punch', CONFIG.punchUps);
    place('invis', CONFIG.invisUps);

    const goons = [];
    const goonCount = Math.min(7, 2 + level);
    for (const i of free) {
      if (goons.length >= goonCount) break;
      if (fromPlayer[i] < 14) continue;
      const g = makeEntity(i % W, Math.floor(i / W));
      g.dir = pick(DIR_LIST);
      goons.push(g);
    }

    Object.assign(state, {
      mode: 'playing', level, grid, homeDist, player, burglar, goons, items,
      playerDist: fromPlayer, playerTile: idx(1, 1), startDist: remaining,
      floaters: [], punchFx: null,
    });
    overlay.classList.add('hidden');
  }

  // ---------------------------------------------------------------- movement
  // Advance an entity `dist` tiles along the grid. `choose` returns the next
  // direction (or null to stand still) each time it reaches a tile centre.
  function stepEntity(e, dist, choose) {
    while (dist > 0) {
      if (!e.moving) {
        const d = choose(e);
        if (!d) return;
        e.dir = d;
        e.tx = e.cx + d.x;
        e.ty = e.cy + d.y;
        e.moving = true;
      }
      const remaining = Math.abs(e.tx - e.x) + Math.abs(e.ty - e.y);
      if (dist >= remaining) {
        e.x = e.cx = e.tx;
        e.y = e.cy = e.ty;
        e.moving = false;
        dist -= remaining;
      } else {
        e.x += Math.sign(e.tx - e.x) * dist;
        e.y += Math.sign(e.ty - e.y) * dist;
        dist = 0;
      }
    }
  }

  const isOpen = (x, y) => state.grid[idx(x, y)] === FLOOR;

  function choosePlayerDir(p) {
    const d = held.length ? KEY_DIRS[held[held.length - 1]] : null;
    if (!d) return null;
    p.face = d;
    return isOpen(p.cx + d.x, p.cy + d.y) ? d : null;
  }

  function chooseBurglarDir(b) {
    return downhill(state.grid, state.homeDist, b.cx, b.cy);
  }

  function chooseGoonDir(g) {
    const seen = state.playerDist[idx(g.cx, g.cy)];
    if (state.player.invisT <= 0 && seen !== -1 && seen <= CONFIG.goonSight) {
      const d = downhill(state.grid, state.playerDist, g.cx, g.cy);
      if (d) return d;
    }
    const open = DIR_LIST.filter((d) => isOpen(g.cx + d.x, g.cy + d.y));
    const forward = open.filter((d) => d.x !== -g.dir.x || d.y !== -g.dir.y);
    return pick(forward.length ? forward : open);
  }

  // ---------------------------------------------------------------- actions
  function floatText(text, x, y, color = '#fff') {
    state.floaters.push({ text, x, y, color, t: 0 });
  }

  function collect(p) {
    const t = tileOf(p);
    const i = idx(t.x, t.y);
    const type = state.items.get(i);
    if (!type) return;
    state.items.delete(i);
    if (type === 'coin') {
      p.coins++;
    } else if (type === 'speed') {
      p.speedT = CONFIG.speedTime;
      floatText('Speed!', p.x, p.y, ITEM_COLOR.speed);
    } else if (type === 'punch') {
      p.punchLevel = Math.min(CONFIG.maxPunchLevel, p.punchLevel + 1);
      floatText(p.punchLevel >= 2 ? 'Wall-smashing punch!' : 'Punch up!', p.x, p.y, ITEM_COLOR.punch);
    } else if (type === 'invis') {
      p.invisT = CONFIG.invisTime;
      floatText('Invisible!', p.x, p.y, ITEM_COLOR.invis);
    }
  }

  // Punch reaches (1 + level) tiles ahead and stuns whoever it hits. From
  // level 2 it also smashes a wall directly in front of Clarence.
  function punch() {
    const p = state.player;
    if (state.mode !== 'playing' || p.stunT > 0 || p.punchCd > 0) return;
    if (p.coins <= 0) {
      floatText('Need a coin!', p.x, p.y, '#ffd24a');
      return;
    }
    p.coins--;
    p.punchCd = CONFIG.punchCooldown;

    const origin = tileOf(p);
    const reach = 1 + p.punchLevel;
    const stun = 1.2 + 0.8 * p.punchLevel;
    const tiles = [origin];
    for (let i = 1; i <= reach; i++) {
      const x = origin.x + p.face.x * i, y = origin.y + p.face.y * i;
      if (!isOpen(x, y)) {
        if (i === 1 && p.punchLevel >= 2 && interior(x, y)) {
          state.grid[idx(x, y)] = FLOOR;
          state.homeDist = distanceMap(state.grid, state.home.x, state.home.y);
          state.playerTile = -1;   // forces playerDist to be rebuilt
          tiles.push({ x, y });
          floatText('Smash!', x, y, ITEM_COLOR.punch);
        }
        break;
      }
      tiles.push({ x, y });
    }

    for (const target of [state.burglar, ...state.goons]) {
      const t = tileOf(target);
      if (tiles.some((tile) => tile.x === t.x && tile.y === t.y)) {
        target.stunT = Math.max(target.stunT, stun);
        floatText('Pow!', target.x, target.y, ITEM_COLOR.punch);
      }
    }
    state.punchFx = { tiles: tiles.slice(1), t: 0 };
  }

  function finish(mode) {
    state.mode = mode;
    if (mode === 'won') {
      showOverlay(
        'Cat rescued! 🐱',
        `Clarence caught the burglar on level ${state.level}. Gerald's cat is safe… until the burglar tries again.`,
        'Press Enter for the next level',
      );
    } else {
      showOverlay(
        'He got away…',
        'The cat burglar made it home with Gerald\'s cat.',
        'Press Enter to try again',
      );
    }
  }

  // ---------------------------------------------------------------- update
  function update(dt) {
    if (state.mode !== 'playing') return;
    state.time += dt;
    const { player: p, burglar: b, goons } = state;

    p.speedT = Math.max(0, p.speedT - dt);
    p.invisT = Math.max(0, p.invisT - dt);
    p.punchCd = Math.max(0, p.punchCd - dt);
    for (const e of [p, b, ...goons]) e.stunT = Math.max(0, e.stunT - dt);

    // Clarence
    if (p.stunT <= 0) {
      const want = held.length ? KEY_DIRS[held[held.length - 1]] : null;
      if (want) p.face = want;
      if (want && p.moving && want.x === -p.dir.x && want.y === -p.dir.y) {
        // Turn around mid-tile instead of finishing the step first.
        [p.cx, p.tx] = [p.tx, p.cx];
        [p.cy, p.ty] = [p.ty, p.cy];
        p.dir = want;
      }
      const speed = CONFIG.playerSpeed * (p.speedT > 0 ? CONFIG.speedBoost : 1);
      stepEntity(p, speed * dt, choosePlayerDir);
    }
    collect(p);

    const pt = tileOf(p);
    if (idx(pt.x, pt.y) !== state.playerTile) {
      state.playerTile = idx(pt.x, pt.y);
      state.playerDist = distanceMap(state.grid, pt.x, pt.y);
    }

    // Burglar
    if (b.stunT <= 0) {
      const spotted = p.invisT <= 0 && Math.hypot(p.x - b.x, p.y - b.y) <= CONFIG.burglarAlert;
      b.sprinting = spotted;
      stepEntity(b, (spotted ? Math.max(CONFIG.burglarSprint, b.walk) : b.walk) * dt, chooseBurglarDir);
    }

    // Goons
    for (const g of goons) {
      if (g.stunT <= 0) stepEntity(g, CONFIG.goonSpeed * dt, chooseGoonDir);
      const touching = Math.hypot(p.x - g.x, p.y - g.y) < 0.6;
      if (touching && g.stunT <= 0 && p.stunT <= 0 && p.invisT <= 0) {
        const lost = Math.min(p.coins, CONFIG.goonHitCoins);
        p.coins -= lost;
        p.stunT = CONFIG.goonHitStun;
        g.stunT = 3;
        floatText(lost ? `Ouch! -${lost} 🪙` : 'Ouch!', p.x, p.y, '#ff5d6c');
      }
    }

    for (const f of state.floaters) f.t += dt;
    state.floaters = state.floaters.filter((f) => f.t < 1);
    if (state.punchFx && (state.punchFx.t += dt) > 0.18) state.punchFx = null;

    if (Math.hypot(p.x - b.x, p.y - b.y) < 0.6) finish('won');
    else if (!b.moving && b.cx === state.home.x && b.cy === state.home.y) finish('lost');
  }

  // ---------------------------------------------------------------- rendering
  const canvas = document.getElementById('game');
  const ctx = canvas.getContext('2d');
  const overlay = document.getElementById('overlay');
  const hud = {
    level: document.getElementById('hud-level'),
    coins: document.getElementById('hud-coins'),
    punch: document.getElementById('hud-punch'),
    speed: document.getElementById('hud-speed'),
    invis: document.getElementById('hud-invis'),
    escape: document.getElementById('hud-escape'),
  };

  const dpr = window.devicePixelRatio || 1;
  canvas.width = W * T * dpr;
  canvas.height = H * T * dpr;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

  function showOverlay(title, body, hint) {
    overlay.innerHTML = `<h2>${title}</h2><p>${body}</p><p class="hint">${hint}</p>`;
    overlay.classList.remove('hidden');
  }

  function emoji(char, x, y, size) {
    ctx.font = `${size}px serif`;
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(char, x, y + 1);
  }

  function drawMaze() {
    ctx.fillStyle = '#14162b';
    ctx.fillRect(0, 0, W * T, H * T);
    for (let y = 0; y < H; y++) {
      for (let x = 0; x < W; x++) {
        if (state.grid[idx(x, y)] !== WALL) continue;
        ctx.fillStyle = '#2b3263';
        ctx.fillRect(x * T, y * T, T, T);
        ctx.fillStyle = '#3d4688';
        ctx.fillRect(x * T, y * T, T, 4);
      }
    }
  }

  function drawItems() {
    for (const [i, type] of state.items) {
      const cx = (i % W + 0.5) * T, cy = (Math.floor(i / W) + 0.5) * T;
      if (type === 'coin') {
        ctx.fillStyle = '#ffd24a';
        ctx.beginPath();
        ctx.arc(cx, cy, 4.5, 0, Math.PI * 2);
        ctx.fill();
        ctx.fillStyle = '#b8860b';
        ctx.fillRect(cx - 0.75, cy - 2.5, 1.5, 5);
      } else {
        const pulse = 1 + 0.08 * Math.sin(state.time * 5 + i);
        ctx.fillStyle = ITEM_COLOR[type];
        ctx.globalAlpha = 0.3;
        ctx.beginPath();
        ctx.arc(cx, cy, 10 * pulse, 0, Math.PI * 2);
        ctx.fill();
        ctx.globalAlpha = 1;
        emoji(ITEM_ICON[type], cx, cy, 15);
      }
    }
  }

  function drawBody(e, color, { mask = false } = {}) {
    const cx = (e.x + 0.5) * T, cy = (e.y + 0.5) * T;
    const r = T * 0.4;
    ctx.fillStyle = color;
    ctx.beginPath();
    ctx.arc(cx, cy, r, 0, Math.PI * 2);
    ctx.fill();
    const look = e.face || e.dir;
    const ex = cx + look.x * 3, ey = cy + look.y * 3 - 1;
    if (mask) {
      ctx.fillStyle = '#111';
      ctx.fillRect(cx - r, ey - 3, r * 2, 6);
    }
    ctx.fillStyle = '#fff';
    for (const side of [-1, 1]) {
      ctx.beginPath();
      ctx.arc(ex + side * 3.2, ey, 2, 0, Math.PI * 2);
      ctx.fill();
    }
    if (e.stunT > 0) emoji('💫', cx, cy - r - 4, 12);
  }

  function draw() {
    const { player: p, burglar: b, home } = state;
    drawMaze();

    emoji('🏠', (home.x + 0.5) * T, (home.y + 0.5) * T, 20);
    drawItems();

    if (state.punchFx) {
      ctx.fillStyle = 'rgba(255, 107, 94, 0.55)';
      for (const t of state.punchFx.tiles) ctx.fillRect(t.x * T + 3, t.y * T + 3, T - 6, T - 6);
    }

    for (const g of state.goons) drawBody(g, '#8a4fd6');

    drawBody(b, b.sprinting && b.stunT <= 0 ? '#5c5f66' : '#3b3d44', { mask: true });
    emoji('🐱', (b.x + 0.5) * T + 7, (b.y + 0.5) * T - 9, 12);

    ctx.globalAlpha = p.invisT > 0 ? 0.35 : 1;
    if (p.speedT > 0) {
      ctx.strokeStyle = ITEM_COLOR.speed;
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.arc((p.x + 0.5) * T, (p.y + 0.5) * T, T * 0.48, 0, Math.PI * 2);
      ctx.stroke();
    }
    drawBody(p, '#ff9a3c');
    ctx.globalAlpha = 1;

    for (const f of state.floaters) {
      ctx.globalAlpha = 1 - f.t;
      ctx.fillStyle = f.color;
      ctx.font = 'bold 13px system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      const fx = clamp((f.x + 0.5) * T, 60, W * T - 60);
      ctx.fillText(f.text, fx, (f.y + 0.5) * T - 14 - f.t * 18);
    }
    ctx.globalAlpha = 1;

    hud.level.textContent = state.level;
    hud.coins.textContent = p.coins;
    hud.punch.textContent = p.punchLevel;
    hud.speed.classList.toggle('active', p.speedT > 0);
    hud.speed.querySelector('b').textContent = p.speedT.toFixed(1);
    hud.invis.classList.toggle('active', p.invisT > 0);
    hud.invis.querySelector('b').textContent = p.invisT.toFixed(1);
    const bt = tileOf(b);
    const left = Math.max(0, state.homeDist[idx(bt.x, bt.y)]);
    hud.escape.style.width = `${clamp(1 - left / state.startDist, 0, 1) * 100}%`;
  }

  // ---------------------------------------------------------------- input
  window.addEventListener('keydown', (e) => {
    if (e.code in KEY_DIRS) {
      if (!held.includes(e.code)) held.push(e.code);
      e.preventDefault();
    } else if (e.code === 'KeyP') {
      if (!e.repeat) punch();
    } else if (e.code === 'Enter' || e.code === 'Space') {
      e.preventDefault();
      if (state.mode === 'won') startLevel(state.level + 1);
      else if (state.mode !== 'playing') startLevel(state.mode === 'lost' ? state.level : 1);
    }
  });

  window.addEventListener('keyup', (e) => {
    const i = held.indexOf(e.code);
    if (i !== -1) held.splice(i, 1);
  });

  window.addEventListener('blur', () => { held.length = 0; });

  // ---------------------------------------------------------------- main loop
  let lastFrame = 0;
  function frame(now) {
    const dt = Math.min(0.05, (now - lastFrame) / 1000);
    lastFrame = now;
    update(dt);
    draw();
    requestAnimationFrame(frame);
  }

  // Draw a maze behind the intro screen, then wait for the player to start.
  startLevel(1);
  state.mode = 'intro';
  showOverlay(
    'Cat Saviour',
    'A cat burglar has stolen Gerald\'s cat! You are Clarence. Chase the burglar through the maze and catch him before he reaches his home. ' +
    'Collect coins to pay for punches, grab power-ups, and watch out for his goons.',
    'Press Enter to start',
  );
  window.__catSaviour = { state, update, punch, held, CONFIG };
  requestAnimationFrame(frame);
})();
