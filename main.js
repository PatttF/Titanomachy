// --- Enemy Health Bars ---
// main.js - Entry point for a geometric space shooter demo
// All objects are geometric shapes, no textures.

let scene, camera, renderer;
let input = { w: false, a: false, s: false, d: false };
let velocity = new THREE.Vector3();
let rotation = { yaw: 0, pitch: 0 };
let lasers = [];
const LASER_SPEED = 1.2;
// missiles now travel slower and will home on the player
const MISSILE_SPEED = 0.3; // reduced from 0.6
// cap active missiles to avoid CPU/GPU spike
const MAX_ACTIVE_MISSILES = 3;
// shared temporary vectors to avoid per-frame allocations
if (!window._tmpVecA) { window._tmpVecA = new THREE.Vector3(); window._tmpVecB = new THREE.Vector3(); }

// Enemy system
let enemies = [];
let cubeMissiles = [];
let pyramidBeamsActive = [];
const ENEMY_SPEED = 0.12;
// How quickly enemies steer toward the player (lower = slower, smoother turning)
const ENEMY_FOLLOW_LERP = 0.02;
// If fewer than this number of enemies are visible on-screen, spawn extras
const MIN_ENEMIES_IN_VIEW = 2;
// Multiplier applied to enemies that are outside the enclosing sphere on cube-in-sphere level
const OUTSIDE_ENEMY_SPEED_MULT = 1.8;
// Maximum total enemies allowed in the scene to avoid overload
const MAX_ENEMIES_TOTAL = 14;
const ENEMY_SPAWN_INTERVAL = 120; // frames
let enemySpawnTimer = 0;
// Optimization tuning
const MAX_SPAWN_PER_FRAME_CUBEINSPHERE = 2; // cap additional spawns per frame in cube-in-sphere
const COLLISION_CHECK_RADIUS = 160; // only check collisions for enemies within this distance to player
let gameOver = false;
let enemyLasers = [];
let playerHealth = 100;
const PLAYER_MAX_HEALTH = 100;
let playerLastDamageAt = 0; // timestamp of last applied player damage

function applyPlayerDamage(amount, opts) {
  opts = opts || {};
  const now = Date.now();
  const minInterval = (typeof opts.minIntervalMs === 'number') ? opts.minIntervalMs : 100; // default 100ms guard
  if (now - playerLastDamageAt < minInterval) return false;
  playerLastDamageAt = now;
  const prev = playerHealth;
  playerHealth = Math.max(0, playerHealth - (amount || 0));
  // (debug removed)
  if (opts.sound) {
    try { playSound(opts.sound); } catch (e) {}
  } else {
    try { playSound('playerHit'); } catch (e) {}
  }
  if (playerHealth <= 0) {
    playerHealth = 0;
    gameOver = true;
    try { playSound('gameover'); } catch (e) {}
    showGameOver();
    return true;
  }
  return true;
}
// base damage of player's lasers (can be increased for harder levels)
let PLAYER_LASER_DAMAGE = 1;
const SPEED = 0.2;
let killCount = 0;
let effects = [];
let lastTime = Date.now();
let levelCube = null;

// Lightweight touch detection and state
const isTouchDevice = (('ontouchstart' in window) || (navigator && navigator.maxTouchPoints && navigator.maxTouchPoints > 0));
let touchInput = { forward: 0, right: 0, firing: false, boosting: false, _fireInterval: null };
// Mobile tuning: reduce sensitivity and provide deadzone
const TOUCH_ROT_MULT = 0.5; // multiplier applied to ROT_SPEED for touch (lower => less sensitive)
const TOUCH_MAX_R = 140; // larger joystick radius -> less sensitive control over a larger area
const TOUCH_DEADZONE = 8; // pixels

// Starfield globals and tuning
let stars, starsGeo, starPositions;
const STAR_INITIAL_COUNT = 400;
const STAR_CHECK_INTERVAL_FRAMES = 30; // how often to check visibility
const STAR_MIN_VISIBLE = 80; // if fewer than this are visible, spawn more
const STAR_SPAWN_BATCH = 120; // how many to add when repopulating
const STAR_MAX_TOTAL = 1200; // cap total stars to avoid huge buffers
let starVisibilityTimer = 0;
// Burst laser spawn queue to spread expensive spawn over frames
const BURST_SPAWN_PER_FRAME = 12; // how many burst lasers to instantiate per frame (reduced)
let burstSpawnQueue = [];

// Object pools for performance
const playerLaserPool = [];
const enemyLaserPool = [];
const missilePool = [];
// Pyramid beam pool (large gold beams)
const pyramidBeamPool = [];

// Shared geometries/materials for pooled objects
const _playerLaserGeom = new THREE.CylinderGeometry(0.08, 0.08, 2, 8);
const _playerLaserMat = new THREE.MeshBasicMaterial({ color: 0xff4444, transparent: true, opacity: 0.95 });
const _enemyLaserGeom = new THREE.CylinderGeometry(0.08, 0.08, 2, 8);
const _enemyLaserMat = new THREE.MeshBasicMaterial({ color: 0x00ff00, transparent: true, opacity: 0.95 });
// pink burst lasers used by sphere-level special attack
const _sphereBurstLaserMat = new THREE.MeshBasicMaterial({ color: 0xff2aa6, transparent: true, opacity: 0.98 });
// make missiles larger (wider and longer) for visibility and impact
// simpler missile geometry (fewer segments) to reduce render cost
const _missileGeom = new THREE.CylinderGeometry(0.5, 0.5, 2.2, 6);
const _missileMat = new THREE.MeshBasicMaterial({ color: 0x4444ff, transparent: true, opacity: 0.95 });
// Pyramid beam geometry/material (long thin cylinder oriented along Y)
const _pyramidBeamGeom = new THREE.CylinderGeometry(0.6, 0.6, 1.0, 6);
const _pyramidBeamMat = new THREE.MeshStandardMaterial({ color: 0xffd700, emissive: 0xffd700, emissiveIntensity: 1.2, metalness: 0.9, roughness: 0.08, transparent: true, opacity: 0.98 });

// Shared asteroid / powerup geometries & materials for pooling (optimization)
let _sharedAsteroidGeom = null;
let _sharedAsteroidMat = null;
let _sharedPowerupGeom = null;
let _sharedPowerupMat = null;

function acquirePlayerLaser() {
  let m = playerLaserPool.pop();
  if (!m) {
    m = new THREE.Mesh(_playerLaserGeom, _playerLaserMat);
    m.frustumCulled = false;
    try { m.material.depthWrite = false; } catch (e) {}
  }
  m.visible = true;
  return m;
}
function acquireEnemyLaser() {
  let m = enemyLaserPool.pop();
  if (!m) {
    m = new THREE.Mesh(_enemyLaserGeom, _enemyLaserMat);
    m.frustumCulled = false;
    try { m.material.depthWrite = false; } catch (e) {}
  }
  // ensure default transform/scale when reused
  try { m.scale.set(1,1,1); } catch (e) {}
  m.visible = true;
  return m;
}
function releaseEnemyLaser(m) {
  try { scene.remove(m); } catch (e) {}
  m.visible = false;
  // restore default material for pooled enemy lasers
  try { m.material = _enemyLaserMat; } catch (e) {}
  try { m.scale.set(1,1,1); } catch (e) {}
  m.userData = {};
  enemyLaserPool.push(m);
}

function releasePlayerLaser(m) {
  try { scene.remove(m); } catch (e) {}
  m.visible = false;
  m.userData = {};
  playerLaserPool.push(m);
}

function acquireMissile() {
  let m = missilePool.pop();
  if (!m) {
    m = new THREE.Mesh(_missileGeom, _missileMat);
    // allow frustum culling so offscreen missiles don't render
    m.frustumCulled = true;
    try { m.material.depthWrite = false; } catch (e) {}
  }
  m.visible = true;
  return m;
}
function releaseMissile(m) {
  try { scene.remove(m); } catch (e) {}
  m.visible = false;
  m.userData = {};
  missilePool.push(m);
}
// Pyramid beam pool helpers
function acquirePyramidBeam() {
  let b = pyramidBeamPool.pop();
  if (!b) {
    b = new THREE.Mesh(_pyramidBeamGeom, _pyramidBeamMat);
    b.frustumCulled = false;
    try { b.material.depthWrite = false; } catch (e) {}
  }
  b.visible = true;
  return b;
}
function releasePyramidBeam(b) {
  try { scene.remove(b); } catch (e) {}
  b.visible = false;
  b.userData = {};
  try { b.scale.set(1,1,1); } catch (e) {}
  try { b.material = _pyramidBeamMat; } catch (e) {}
  pyramidBeamPool.push(b);
}
// Performance helpers
let lastHealthBarUpdate = 0;
const boost = {
  active: false,
  multiplier: 3.0,
  duration: 6000, // ms (tripled from 2000 -> 6000)
  cooldown: 5000, // ms
  endTime: 0,
  cooldownUntil: 0
};

const ROT_SPEED = 0.03;
const MOUSE_SENS = 0.0028;
let pointerLocked = false;
        
function getAudioCtx() {
  if (!__audioCtx) {
    try { __audioCtx = new (window.AudioContext || window.webkitAudioContext)(); } catch (e) { __audioCtx = null; }
  }
  return __audioCtx;
}
function playSound(name) {
  const ctx = getAudioCtx();
  if (!ctx) return;
  if (ctx.state === 'suspended') { try { ctx.resume(); } catch (e) {} }
  const now = ctx.currentTime;

  const mkGain = (initial) => { const g = ctx.createGain(); g.gain.setValueAtTime(initial, now); g.connect(ctx.destination); return g; };

  const playNoise = (duration, volume=0.2) => {
    const bufferSize = ctx.sampleRate * duration;
    const buffer = ctx.createBuffer(1, bufferSize, ctx.sampleRate);
    const data = buffer.getChannelData(0);
    for (let i = 0; i < bufferSize; i++) data[i] = (Math.random() * 2 - 1) * (Math.random() * 0.5);
    const src = ctx.createBufferSource();
    src.buffer = buffer;
    const g = ctx.createGain();
    g.gain.setValueAtTime(volume, now);
    g.gain.exponentialRampToValueAtTime(0.001, now + duration);
    src.start(now);
    src.stop(now + duration + 0.02);
  };

  switch (name) {
    case 'shoot': {
      const g = mkGain(0.12);
      const o = ctx.createOscillator(); o.type = 'square'; o.frequency.setValueAtTime(1100, now);
      o.connect(g);
      g.gain.exponentialRampToValueAtTime(0.001, now + 0.12);
      o.start(now); o.stop(now + 0.12);
      break;
    }
    case 'hit': {
      const g = mkGain(0.12);
      const o = ctx.createOscillator(); o.type = 'triangle'; o.frequency.setValueAtTime(640, now);
      o.connect(g);
      g.gain.exponentialRampToValueAtTime(0.001, now + 0.14);
      o.start(now); o.stop(now + 0.14);
      break;
    }
    case 'explosion': {
      // short burst noise + low-frequency rumble
      playNoise(0.6, 0.28);
      const g = mkGain(0.24);
      const o = ctx.createOscillator(); o.type = 'sawtooth'; o.frequency.setValueAtTime(160, now);
      o.connect(g);
      g.gain.exponentialRampToValueAtTime(0.001, now + 0.9);
      o.start(now); o.stop(now + 0.9);
      break;
    }
    case 'marker': {
      // rising chirp
      const g = mkGain(0.12);
      const o = ctx.createOscillator(); o.type = 'triangle'; o.frequency.setValueAtTime(360, now);
      o.frequency.exponentialRampToValueAtTime(880, now + 0.18);
      o.connect(g);
      g.gain.exponentialRampToValueAtTime(0.001, now + 0.22);
      o.start(now); o.stop(now + 0.22);
      break;
    }
    case 'playerHit': {
      const g = mkGain(0.18);
      const o = ctx.createOscillator(); o.type = 'sine'; o.frequency.setValueAtTime(110, now);
      o.connect(g);
      g.gain.exponentialRampToValueAtTime(0.001, now + 0.28);
      o.start(now); o.stop(now + 0.28);
      break;
    }
    case 'gameover': {
      const g = mkGain(0.28);
      const o = ctx.createOscillator(); o.type = 'sine'; o.frequency.setValueAtTime(60, now);
      o.connect(g);
      g.gain.exponentialRampToValueAtTime(0.001, now + 1.2);
      o.start(now); o.stop(now + 1.2);
      break;
    }
    case 'boost': {
      const g = mkGain(0.14);
      const o = ctx.createOscillator(); o.type = 'triangle'; o.frequency.setValueAtTime(300, now);
      o.frequency.exponentialRampToValueAtTime(600, now + 0.18);
      o.connect(g);
      g.gain.exponentialRampToValueAtTime(0.001, now + 0.24);
      o.start(now); o.stop(now + 0.24);
      break;
    }
    default: {
      const g = mkGain(0.08);
      const o = ctx.createOscillator(); o.type = 'sine'; o.frequency.setValueAtTime(440, now);
      o.connect(g);
      g.gain.exponentialRampToValueAtTime(0.001, now + 0.12);
      o.start(now); o.stop(now + 0.12);
    }
  }
}
let paused = false;

// Initialize Three.js scene, camera, and renderer
function init() {
  scene = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
  renderer = new THREE.WebGLRenderer();
  renderer.setSize(window.innerWidth, window.innerHeight);
  document.body.appendChild(renderer.domElement);

  // Pointer lock instruction overlay (desktop only)
  let pointerOverlay = null;
  if (!isTouchDevice) {
    pointerOverlay = document.createElement('div');
    pointerOverlay.id = 'pointer-instructions';
    pointerOverlay.style.position = 'fixed';
    pointerOverlay.style.left = '50%';
    pointerOverlay.style.top = '90%';
    pointerOverlay.style.transform = 'translateX(-50%)';
    pointerOverlay.style.color = '#fff';
    pointerOverlay.style.background = 'rgba(0,0,0,0.5)';
    pointerOverlay.style.padding = '8px 12px';
    pointerOverlay.style.borderRadius = '6px';
    pointerOverlay.style.zIndex = '200';
    pointerOverlay.innerText = 'Click the canvas to lock mouse and control ship. Press Esc to unlock.';
    document.body.appendChild(pointerOverlay);
  }

  // Desktop: pointer lock on click
  renderer.domElement.style.cursor = 'crosshair';
  if (!isTouchDevice) {
    renderer.domElement.addEventListener('click', () => {
      try { renderer.domElement.requestPointerLock(); } catch (e) {}
    });
    // prevent context menu inside canvas so right-click can be used for boost
    renderer.domElement.addEventListener('contextmenu', (e) => { e.preventDefault(); });
  } else {
    // On touch devices, provide simple on-screen controls
    createTouchUI();
  }
  // prevent context menu inside canvas so right-click can be used for boost
  

  document.addEventListener('pointerlockchange', () => {
    pointerLocked = (document.pointerLockElement === renderer.domElement);
    try { if (pointerOverlay) pointerOverlay.style.display = pointerLocked ? 'none' : 'block'; } catch (e) {}
  });

  // Shared raycaster and vector for reticule / ray tests (avoid per-frame allocations)
  window._sharedRaycaster = new THREE.Raycaster();
  window._sharedMouseVec2 = new THREE.Vector2(0, 0);

  // Pause overlay (hidden by default)
  const pauseOverlay = document.createElement('div');
  pauseOverlay.id = 'pause-overlay';
  pauseOverlay.style.position = 'fixed';
  pauseOverlay.style.left = '50%';
  pauseOverlay.style.top = '50%';
  pauseOverlay.style.transform = 'translate(-50%, -50%)';
  pauseOverlay.style.color = '#fff';
  pauseOverlay.style.background = 'rgba(0,0,0,0.8)';
  pauseOverlay.style.padding = '30px 40px';
  pauseOverlay.style.borderRadius = '10px';
  pauseOverlay.style.zIndex = '500';
  pauseOverlay.style.display = 'none';
  pauseOverlay.innerHTML = '<div style="font-size:24px;margin-bottom:8px">PAUSED</div><div style="font-size:14px">Press Esc to resume or click to resume</div>';
  pauseOverlay.addEventListener('click', () => { pauseOverlay.style.display = 'none'; paused = false; });
  document.body.appendChild(pauseOverlay);

  // Pointer-lock mouse movement handler (high precision)
  document.addEventListener('mousemove', (e) => {
    if (!pointerLocked) return;
    const ship = window.playerShip;
    if (!ship) return;
    // apply yaw around world up and pitch around ship's local X to avoid Euler flips
    const yaw = -e.movementX * MOUSE_SENS;
    const pitch = e.movementY * MOUSE_SENS;
    // compute new forward after tentative rotations to avoid inversion
    try {
        // Apply yaw (around world up)
        ship.rotateOnWorldAxis(new THREE.Vector3(0, 1, 0), yaw);
        // For pitch, compute a stable "screen right" axis from the camera forward and world up
        const forward = new THREE.Vector3();
        try { camera.getWorldDirection(forward); } catch (e) { forward.set(0,0,-1).applyQuaternion(ship.quaternion); }
        const worldUp = new THREE.Vector3(0,1,0);
        const screenRight = new THREE.Vector3().crossVectors(worldUp, forward);
        if (screenRight.lengthSq() > 1e-6) {
          screenRight.normalize();
          ship.rotateOnWorldAxis(screenRight, pitch);
        } else {
          // fallback if forward is parallel to worldUp
          ship.rotateOnWorldAxis(new THREE.Vector3(1,0,0), pitch);
        }
      } catch (e) {
        // Fallback: still apply rotations if anything unexpected occurs
        ship.rotateOnWorldAxis(new THREE.Vector3(0, 1, 0), yaw);
        ship.rotateOnWorldAxis(new THREE.Vector3(1, 0, 0), pitch);
    }
  });

  // Add lighting
  const light = new THREE.PointLight(0xffffff, 1, 100);
  light.position.set(10, 10, 10);
  scene.add(light);

  const ambientLight = new THREE.AmbientLight(0x404040); // soft white light
  scene.add(ambientLight);

  // Brighter ambient + directional light for clearer visibility
  ambientLight.intensity = 1.0;
  const dirLight = new THREE.DirectionalLight(0xffffff, 0.6);
  dirLight.position.set(-1, 2, 3);
  scene.add(dirLight);

  // Simple starfield for visual reference (store buffers in module-scope vars)
  const starCount = STAR_INITIAL_COUNT;
  starPositions = new Float32Array(starCount * 3);
  for (let i = 0; i < starCount; i++) {
    starPositions[i * 3 + 0] = (Math.random() - 0.5) * 400;
    starPositions[i * 3 + 1] = (Math.random() - 0.5) * 200;
    starPositions[i * 3 + 2] = -Math.random() * 800; // in front of camera
  }
  starsGeo = new THREE.BufferGeometry();
  starsGeo.setAttribute('position', new THREE.BufferAttribute(starPositions, 3));
  const starsMat = new THREE.PointsMaterial({ color: 0xffffff, size: 1 });
  stars = new THREE.Points(starsGeo, starsMat);
  scene.add(stars);

  console.log('init: scene, camera, renderer initialized');

  // Add player ship to the scene
  const shipGeometry = new THREE.ConeGeometry(0.7, 2, 4);
  // rotate geometry so the cone points forward along -Z, keep mesh rotation identity
  shipGeometry.rotateX(Math.PI / 2);
  const shipMaterial = new THREE.MeshStandardMaterial({ color: 0x00fffc, flatShading: true });
  const ship = new THREE.Mesh(shipGeometry, shipMaterial);
  ship.position.set(0, 0, 0);
  ship.visible = false; // Keep ship invisible for first-person view (used for logic)
  shipMaterial.emissive = 0x002222;
  shipMaterial.emissiveIntensity = 0.3;
  scene.add(ship);
  window.playerShip = ship;

  // Add reticule (simple crosshair)
  addReticule();

  // Kill counter UI
  createKillCounter();
  // Start at Level 1 (Cube) per user mapping: 1=cube,2=sphere,3=pyramid,4=cube-in-sphere
  window.levelIndex = 1;
  try { createLevelCube(); } catch (e) { console.warn('failed to start Cube level', e); }
  try { updateLevelIndicator(); } catch (e) {}
  // Danger HUD for approaching the level cube
  createDangerUI();
  // Boost UI
  createBoostUI();

  // First-person camera: put camera at ship position (slightly above) and match rotation
  camera.position.copy(ship.position).add(new THREE.Vector3(0, 0.6, 0));
  camera.quaternion.copy(ship.quaternion);

  animate();
}

let __firstFrameLogged = false;

// Add a simple reticule (crosshair) to the center of the screen
function addReticule() {
  const crosshair = document.createElement('div');
  crosshair.id = 'reticule';
  crosshair.style.position = 'fixed';
  crosshair.style.left = '50%';
  crosshair.style.top = '50%';
  crosshair.style.width = '32px';
  crosshair.style.height = '32px';
  crosshair.style.marginLeft = '-16px';
  crosshair.style.marginTop = '-16px';
  crosshair.style.pointerEvents = 'none';
  crosshair.style.zIndex = '10';
  crosshair.innerHTML = `
    <svg width="32" height="32">
      <line x1="16" y1="8" x2="16" y2="24" stroke="#fff" stroke-width="2" />
      <line x1="8" y1="16" x2="24" y2="16" stroke="#fff" stroke-width="2" />
    </svg>
  `;
  document.body.appendChild(crosshair);
}

function animate() {
  if (gameOver) return;
  if (!__firstFrameLogged) { console.log('animate started'); __firstFrameLogged = true; }
  requestAnimationFrame(animate);
  if (paused) {
    // while paused still render the scene once and skip updates
    renderer.render(scene, camera);
    return;
  }
  const now = Date.now();
  const dt = now - lastTime;
  lastTime = now;
  const ship = window.playerShip;
  const dtScale = Math.max(0.5, Math.min(3.0, dt / 16.6667));
  updateEnemyHealthBars();
  updatePlayerHealthBar();
  // (debug UI removed)


  // Controls act as rotations; ship always moves forward in facing direction
  if (isTouchDevice) {
    // Use left-side joystick for pitch/yaw on touch devices
    try {
      const yaw = -touchInput.right * ROT_SPEED * TOUCH_ROT_MULT;
      const pitch = touchInput.forward * ROT_SPEED * TOUCH_ROT_MULT;
      ship.rotateOnWorldAxis(new THREE.Vector3(0,1,0), yaw);
      // apply pitch around a stable screen-right axis similar to mouse handler
      const forward = new THREE.Vector3();
      try { camera.getWorldDirection(forward); } catch (e) { forward.set(0,0,-1).applyQuaternion(ship.quaternion); }
      const worldUp = new THREE.Vector3(0,1,0);
      const screenRight = new THREE.Vector3().crossVectors(worldUp, forward);
      if (screenRight.lengthSq() > 1e-6) {
        screenRight.normalize();
        ship.rotateOnWorldAxis(screenRight, pitch);
      } else {
        ship.rotateOnWorldAxis(new THREE.Vector3(1,0,0), pitch);
      }
    } catch (e) {
      if (touchInput.right) ship.rotateOnWorldAxis(new THREE.Vector3(0,1,0), -touchInput.right * ROT_SPEED);
      if (touchInput.forward) ship.rotateX(touchInput.forward * ROT_SPEED);
    }
  } else {
    if (input.a) ship.rotateOnWorldAxis(new THREE.Vector3(0,1,0), ROT_SPEED); // yaw left
    if (input.d) ship.rotateOnWorldAxis(new THREE.Vector3(0,1,0), -ROT_SPEED); // yaw right
    // Arrow/keyboard pitch: invert so 'Up' moves view up (more intuitive)
    if (input.w) ship.rotateX(-ROT_SPEED);
    if (input.s) ship.rotateX(ROT_SPEED);
  }
  // Continuous keyboard roll (Q/E) removed
  // Apply any barrel roll in progress (userData.rollRemaining in radians)
  if (ship.userData && ship.userData.rollRemaining && Math.abs(ship.userData.rollRemaining) > 0.0001) {
    const rollSpeed = ship.userData.rollSpeed || Math.PI; // rad/s (fallback to slower roll)
    const maxDelta = rollSpeed * (dt / 1000);
    const take = Math.sign(ship.userData.rollRemaining) * Math.min(Math.abs(ship.userData.rollRemaining), maxDelta);
    ship.rotateZ(take);
    ship.userData.rollRemaining -= take;
  }

  // Move forward in the ship's facing direction
  const speedMult = (boost.active ? boost.multiplier : 1.0);
  const forward = new THREE.Vector3(0, 0, -1).applyEuler(ship.rotation).multiplyScalar(SPEED * speedMult);
  ship.position.add(forward);

  // Collision: entering the level cube should instantly kill the player
  if (levelCube) {
    try {
      // Use cached AABB of the cube and check closest point to ship mesh
      const shipPos = ship.position;
      const box = (levelCube.userData && levelCube.userData.box) ? levelCube.userData.box : new THREE.Box3().setFromObject(levelCube);
      const closest = new THREE.Vector3();
      box.clampPoint(shipPos, closest);
      const shipRadius = 1.0; // approximate ship collision radius
      const distToBox = closest.distanceTo(shipPos);
      // Small forgiving buffer to avoid premature kills
      const buffer = 0.2;
      if (distToBox <= (shipRadius - buffer)) {
        playerHealth = 0;
        try { playSound('gameover'); } catch (e) {}
        gameOver = true;
        showGameOver();
        return;
      }
    } catch (e) {}
  }

  // Update Danger HUD: compute distance based on cube AABB to match collision test
  try {
    if (window.cubeDangerEl && levelCube) {
      const shipPos = ship.position.clone();
      const box = new THREE.Box3().setFromObject(levelCube);
      const closest = new THREE.Vector3();
      box.clampPoint(shipPos, closest);
      const distToBox = shipPos.distanceTo(closest);
      const shipRadius = 1.0; // must match collision radius used in animate
      const distUntilCollision = Math.max(0, distToBox - shipRadius);
      const warnThreshold = 50; // show warning when within this many units
      if (distUntilCollision <= warnThreshold) {
        const pct = 1 - (distUntilCollision / warnThreshold);
        const alpha = 0.45 + 0.5 * pct;
        window.cubeDangerEl.style.display = 'block';
        window.cubeDangerEl.style.background = `rgba(160,0,0,${alpha})`;
        const distText = Math.max(0, Math.floor(distUntilCollision));
        window.cubeDangerEl.innerText = `Danger: ${distText} units — Collision is fatal`;
      } else {
        window.cubeDangerEl.style.display = 'none';
      }
    }
  } catch (e) {}

  // Update boost state and UI: end boost when time expires, update UI text
  try {
    const be = window.boostEl;
    if (boost.active && now >= boost.endTime) {
      boost.active = false;
    }
    if (be) {
      if (boost.active) {
        const remain = Math.max(0, Math.ceil((boost.endTime - now) / 1000));
        be.innerText = `BOOST: ${remain}s`;
        be.style.background = 'rgba(0,128,0,0.6)';
      } else {
        const nowMs = now;
        if (nowMs < boost.cooldownUntil) {
          const cd = Math.ceil((boost.cooldownUntil - nowMs) / 1000);
          be.innerText = `BOOST: CD ${cd}s`;
          be.style.background = 'rgba(80,0,0,0.6)';
        } else {
          be.innerText = 'BOOST: READY';
          be.style.background = 'rgba(0,0,0,0.4)';
        }
      }
    }
  } catch (e) {}

  // First-person camera: inside the ship (slightly above) and aligned with ship rotation
  camera.position.copy(ship.position).add(new THREE.Vector3(0, 0.6, 0));
  camera.quaternion.copy(ship.quaternion);

  // Pulsate level cube emissive
  if (levelCube && levelCube.material) {
    const now = Date.now();
    const base = levelCube.userData._emissiveBase || 1.0;
    const amp = levelCube.userData._emissiveAmp || 0.5;
    const val = base + Math.sin(now * 0.0025) * amp * 0.5 + Math.sin(now * 0.01) * amp * 0.5;
    levelCube.material.emissiveIntensity = Math.max(0, val);
  }
  // Rotate level object if it defines a rotateSpeed (radians/sec)
  try {
    if (levelCube && levelCube.userData && levelCube.userData.rotateSpeed) {
      const rot = levelCube.userData.rotateSpeed * (dt / 1000);
      levelCube.rotation.y += rot;
    }
  } catch (e) {}


  // Update player lasers
  for (let i = lasers.length - 1; i >= 0; i--) {
    const laser = lasers[i];
    // swept collision: consider segment from prevPos to nextPos
    const prevPos = laser.userData.prevPos ? laser.userData.prevPos.clone() : laser.position.clone();
    const nextPos = laser.position.clone().add(laser.userData.dir.clone().multiplyScalar(LASER_SPEED * dtScale));

    // helper: distance from point p to segment ab
    const segDist = (a, b, p) => {
      const ab = b.clone().sub(a);
      const ap = p.clone().sub(a);
      const abLen2 = ab.dot(ab) || 1e-6;
      const t = Math.max(0, Math.min(1, ap.dot(ab) / abLen2));
      const closest = a.clone().add(ab.multiplyScalar(t));
      return p.distanceTo(closest);
    };

      // ensure laser has a valid direction (fallback to its world forward)
      if (!laser.userData.dir) {
        try {
          const f = new THREE.Vector3(0, 0, -1).applyQuaternion(laser.quaternion).normalize();
          laser.userData.dir = f;
        } catch (e) { laser.userData.dir = new THREE.Vector3(0,0,-1); }
      }

    // advance laser to nextPos (store prev to check swept collisions)
    if (!laser.userData.prevPos) laser.userData.prevPos = laser.position.clone();
    laser.userData.prevPos.copy(laser.position);
    laser.position.copy(nextPos);
    if (laser.position.distanceTo(ship.position) > 1200) {
      releasePlayerLaser(laser);
      lasers.splice(i, 1);
      continue;
    }
    // Check collision with enemies
    // Check collision with level cube first
    if (levelCube) {
      const lr = levelCube.userData.hitRadius || 20;
      if (laser.position.distanceTo(levelCube.position) < lr) {
        // Marker collision: use stored marker local/world position and hit radius
        try {
          let markerWorld = null;
          if (levelCube.userData && levelCube.userData.markerLocal) {
            try {
              const t = levelCube.userData && levelCube.userData.type;
              if (t === 'pyramid' || t === 'sphere' || t === 'cubeinsphere') markerWorld = levelCube.position.clone().add(levelCube.userData.markerLocal.clone());
              else markerWorld = levelCube.localToWorld(levelCube.userData.markerLocal.clone());
            } catch (e) { markerWorld = null; }
          }
          if (!markerWorld && levelCube.userData && levelCube.userData.markerWorldPos) markerWorld = levelCube.userData.markerWorldPos.clone();
          if (markerWorld) {
            const markerRadius = levelCube.userData.markerHitRadius || Math.max(8, ((levelCube.userData.size || 400) * 0.12) * 0.5);
            const dsegMarker = segDist(prevPos, nextPos, markerWorld);
            if (dsegMarker < markerRadius && !(levelCube.userData && levelCube.userData.markerOccluded)) {
              const ab = nextPos.clone().sub(prevPos);
              const abLen2 = ab.lengthSq() || 1e-6;
              const t = Math.max(0, Math.min(1, markerWorld.clone().sub(prevPos).dot(ab) / abLen2));
              const intersectPoint = prevPos.clone().add(ab.multiplyScalar(t));
              levelCube.userData.hp -= 1;
              levelCube.userData.markerHits = (levelCube.userData.markerHits || 0) + 1;
              try { createExplosion(intersectPoint); } catch (e) {}
              if (levelCube.userData.markerHits >= 15) {
                placeLevelMarker(levelCube);
              }
              updateLevelHealthUI();
              if (levelCube.userData.hp <= 0) {
                levelPassed();
              }
            }
          }
        } catch (e) {}
        releasePlayerLaser(laser);
        lasers.splice(i, 1);
        continue;
      }
    }
    for (let j = enemies.length - 1; j >= 0; j--) {
      const enemy = enemies[j];
      const hitRadius = (enemy.userData && enemy.userData.hitRadius) ? enemy.userData.hitRadius : 1.2;
      // Check swept segment vs enemy sphere
      const dseg = segDist(prevPos, nextPos, enemy.position);
      if (dseg < hitRadius) {
          // Damage enemy
          enemy.userData.hp -= (typeof PLAYER_LASER_DAMAGE !== 'undefined') ? PLAYER_LASER_DAMAGE : 1;
        try { playSound('hit'); } catch (e) {}
        updateEnemyHealthBar(enemy);
        releasePlayerLaser(laser);
        lasers.splice(i, 1);
        if (enemy.userData.hp <= 0) {
            // Create explosion effect, increment kill counter, then remove enemy
            try { createExplosion(enemy.position.clone()); } catch (e) { console.error(e); }
            killCount++;
            updateKillCounter();
            removeEnemyHealthBar(enemy);
            scene.remove(enemy);
            enemies.splice(j, 1);
        }
        break;
      }
    }
    // Check collision with cube missiles
    for (let j = cubeMissiles.length - 1; j >= 0; j--) {
      const m = cubeMissiles[j];
      const missileRadius = 1.4; // larger radius to match bigger missile mesh
      const dsegM = segDist(prevPos, nextPos, m.position);
      if (dsegM < missileRadius) {
        // destroy missile
        try { createExplosion(m.position.clone()); } catch (e) {}
        try { playSound('hit'); } catch (e) {}
        releaseMissile(m);
        cubeMissiles.splice(j, 1);
        // remove laser
        releasePlayerLaser(laser);
        lasers.splice(i, 1);
        break;
      }
    }
  }

    // Update enemy lasers
  for (let i = enemyLasers.length - 1; i >= 0; i--) {
    const laser = enemyLasers[i];
    if (!laser.userData.dir) {
      laser.userData.dir = new THREE.Vector3(0,0,-1).applyQuaternion(laser.quaternion).normalize();
    }
    if (!laser.userData.prevPos) laser.userData.prevPos = laser.position.clone();
    laser.userData.prevPos.copy(laser.position);
    const speed = (laser.userData && laser.userData.speed) ? laser.userData.speed : LASER_SPEED;
    laser.position.add(laser.userData.dir.clone().multiplyScalar(speed * dtScale));
    // Remove if too far (respect per-laser range if set)
    const range = (laser.userData && laser.userData.range) ? laser.userData.range : 400;
    if (laser.position.distanceTo(laser.userData.origin) > range) {
      releaseEnemyLaser(laser);
      enemyLasers.splice(i, 1);
      continue;
    }
    // Check collision with player (respect per-laser collision radius if set)
    const hitRadius = (laser.userData && laser.userData.radius) ? laser.userData.radius : 1.2;
    if (laser.position.distanceTo(ship.position) < hitRadius) {
      // remove laser from scene/array
      releaseEnemyLaser(laser);
      enemyLasers.splice(i, 1);

      // Determine whether the firing ship (owner) is visible to the player's camera.
      // If owner is not visible (off-screen or occluded) then the laser will not damage the player.
      let ownerVisible = true;
      try {
        const owner = laser.userData && laser.userData.owner;
        if (owner) {
          // get owner world position
          const ownerWorld = (owner.getWorldPosition) ? owner.getWorldPosition(new THREE.Vector3()) : owner.position.clone();
          // quick frustum check via projection to NDC
          const ndc = ownerWorld.clone().project(camera);
          if (ndc.x < -1 || ndc.x > 1 || ndc.y < -1 || ndc.y > 1 || ndc.z < -1 || ndc.z > 1) {
            ownerVisible = false;
          } else {
            // raycast from camera to owner to detect occluders
            const dirToOwner = ownerWorld.clone().sub(camera.position).normalize();
            const distToOwner = ownerWorld.distanceTo(camera.position);
            const rc = new THREE.Raycaster(camera.position, dirToOwner, 0, distToOwner);
            const occluders = [];
            scene.traverse(o => {
              if (o && o.isMesh && o.visible && o !== owner && !o.userData._occluderIgnore) occluders.push(o);
            });
            const hits = rc.intersectObjects(occluders, true);
            if (hits && hits.length > 0) ownerVisible = false;
          }
        }
      } catch (e) { ownerVisible = true; }

      if (!ownerVisible) {
        // Owner not visible: do not apply damage
        continue;
      }

      // base enemy laser damage (owner was visible)
      let dmg = 3;
      try { if (levelCube && levelCube.userData && levelCube.userData.type === 'pyramid') dmg += 2; } catch (e) {}
      // apply damage from enemy laser
      applyPlayerDamage(dmg, { minIntervalMs: 200, source: 'enemyLaser' });
      if (gameOver) return;
      if (playerHealth <= 0) {
        playerHealth = 0;
        gameOver = true;
        try { playSound('gameover'); } catch (e) {}
        showGameOver();
        return;
      }
    }
  }

  // Update pyramid beams (stationary beams that last for a short duration)
  for (let i = pyramidBeamsActive.length - 1; i >= 0; i--) {
    const beam = pyramidBeamsActive[i];
    try {
      const now = Date.now();
      const start = beam.userData.start || 0;
      const dur = beam.userData.duration || 1000;
      let origin = beam.userData.origin.clone();
      let dir = beam.userData.dir.clone();
      const range = beam.userData.range || 1200;
      // if beam is persistent and has a localPos, update its world position/direction to follow the pyramid
      if (beam.userData.persistent && beam.userData.localPos && beam.userData.localNormal && levelCube) {
        try {
          const lp = beam.userData.localPos.clone();
          // compute exact world origin from mesh transform
          origin = levelCube.localToWorld(lp.clone());
          // if the beam was created as world-aligned (apex), keep it pointing straight up
          if (beam.userData.worldAligned) {
            dir = new THREE.Vector3(0,1,0);
          } else {
            // transform the stored local normal by the mesh rotation to get beam direction
            dir = beam.userData.localNormal.clone().applyQuaternion(levelCube.quaternion).normalize();
          }
          // update beam mesh transform to follow
          const halfLen = range * 0.5;
          const center = origin.clone().add(dir.clone().multiplyScalar(halfLen));
          beam.position.copy(center);
          beam.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), dir);
          beam.userData.origin = origin.clone();
          beam.userData.dir = dir.clone();
        } catch (e) {}
      }
      const end = origin.clone().add(dir.clone().multiplyScalar(range));
      // collision helper: distance from point to segment
      const segDist = (a, b, p) => {
        const ab = b.clone().sub(a);
        const ap = p.clone().sub(a);
        const abLen2 = ab.dot(ab) || 1e-6;
        const t = Math.max(0, Math.min(1, ap.dot(ab) / abLen2));
        const closest = a.clone().add(ab.multiplyScalar(t));
        return p.distanceTo(closest);
      };
      // check collision with player
      const playerDist = segDist(origin, end, ship.position);
      if (playerDist < (beam.userData.radius || 10)) {
        // apply heavy damage once when hit
          // apply damage with a short cooldown to avoid per-frame stacking
          applyPlayerDamage((beam.userData.damage || 40), { minIntervalMs: 250, source: 'beam' });
      }
      // check collision with enemies (beam can kill many)
      for (let j = enemies.length - 1; j >= 0; j--) {
        const enemy = enemies[j];
        const er = (enemy.userData && enemy.userData.hitRadius) ? enemy.userData.hitRadius : 1.2;
        const d = segDist(origin, end, enemy.position);
        if (d < (beam.userData.radius || 10) + er) {
          enemy.userData.hp -= (beam.userData.damage || 40);
          try { createExplosion(enemy.position.clone()); } catch (e) {}
          try { playSound('hit'); } catch (e) {}
          updateEnemyHealthBar(enemy);
          if (enemy.userData.hp <= 0) {
            killCount++;
            updateKillCounter();
            try { removeEnemyHealthBar(enemy); } catch (e) {}
            try { scene.remove(enemy); } catch (e) {}
            enemies.splice(j, 1);
          }
        }
      }
      // remove when duration elapsed (skip if persistent)
      if (!beam.userData.persistent) {
        if (now - start > dur) {
          try { releasePyramidBeam(beam); } catch (e) {}
          pyramidBeamsActive.splice(i, 1);
        }
      }
    } catch (e) { try { releasePyramidBeam(beam); } catch (ee) {} pyramidBeamsActive.splice(i, 1); }
  }

  // Update cube missiles
  let missileIncoming = false;
  const MISSILE_WARNING_DIST = 250; // units
  for (let i = cubeMissiles.length - 1; i >= 0; i--) {
    const m = cubeMissiles[i];
    if (!m.userData.dir) m.userData.dir = new THREE.Vector3(0,0,-1).applyQuaternion(m.quaternion).normalize();
    if (!m.userData.prevPos) m.userData.prevPos = m.position.clone();
    m.userData.prevPos.copy(m.position);
    // simple homing behaviour: steer missile toward current player position
    try {
      if (ship && ship.position) {
        const d = window._tmpVecA;
        d.copy(ship.position).sub(m.position).normalize();
        // smooth the turn to avoid instant direction snap
        m.userData.dir.lerp(d, 0.06);
        m.userData.dir.normalize();
      }
    } catch (e) {}
    // move using a shared temp to avoid creating a new vector each frame
    const mv = window._tmpVecB;
    mv.copy(m.userData.dir).multiplyScalar(MISSILE_SPEED * dtScale);
    m.position.add(mv);
    // flag incoming warning if within threshold
    try {
      if (ship && m.position.distanceTo(ship.position) < MISSILE_WARNING_DIST) {
        missileIncoming = true;
        m.userData._warning = true;
      }
    } catch (e) {}
    // remove if too far
    if (m.position.distanceTo(m.userData.origin) > 1200) {
      releaseMissile(m);
      cubeMissiles.splice(i, 1);
      continue;
    }
    // check collision with player
    if (m.position.distanceTo(ship.position) < 2.2) {
      releaseMissile(m);
      cubeMissiles.splice(i, 1);
      // missile impact damage (guarded)
      applyPlayerDamage(12, { minIntervalMs: 200, source: 'missile' });
      if (gameOver) return;
      continue;
    }
  }

  // Show/hide incoming missile warning
  try { showMissileWarning(missileIncoming); } catch (e) {}

  // Spawn enemies
  enemySpawnTimer++;
  if (enemySpawnTimer >= ENEMY_SPAWN_INTERVAL) {
    spawnEnemy();
    enemySpawnTimer = 0;
  }

  // If very few enemies are visible on-screen, spawn a few more to keep action engaging
  try {
    let visibleCount = 0;
    const tmpV = new THREE.Vector3();
    for (let en of enemies) {
      try {
        const p = en.getWorldPosition(tmpV).project(camera);
        if (isFinite(p.x) && isFinite(p.y) && isFinite(p.z) && p.z >= -1 && p.z <= 1 && p.x >= -1 && p.x <= 1 && p.y >= -1 && p.y <= 1) {
          visibleCount++;
        }
      } catch (e) {}
    }
    if (visibleCount < MIN_ENEMIES_IN_VIEW && enemies.length < MAX_ENEMIES_TOTAL) {
      let spawnCount = Math.min((MIN_ENEMIES_IN_VIEW - visibleCount) + 1, MAX_ENEMIES_TOTAL - enemies.length);
      try { if (levelCube && levelCube.userData && levelCube.userData.type === 'cubeinsphere') spawnCount = Math.min(spawnCount, MAX_SPAWN_PER_FRAME_CUBEINSPHERE); } catch (e) {}
      for (let s = 0; s < spawnCount; s++) spawnEnemy();
    }
  } catch (e) {}

  // Process burst spawn queue (instantiate a limited number per frame to avoid spikes)
  try {
    let spawnThisFrame = BURST_SPAWN_PER_FRAME;
    while (spawnThisFrame > 0 && burstSpawnQueue.length > 0) {
      const item = burstSpawnQueue.shift();
      try {
        const laser = acquireEnemyLaser();
        try { laser.material = _sphereBurstLaserMat; } catch (e) {}
        laser.position.copy(item.origin);
        laser.userData.dir = item.dir.clone();
        laser.userData.origin = item.origin.clone();
        laser.userData.prevPos = laser.position.clone();
        laser.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), item.dir.clone());
        try { laser.scale.set(2.5, 6.0, 2.5); } catch (e) {}
        laser.userData.radius = 3.0;
        laser.userData.range = 1200;
        laser.userData.speed = LASER_SPEED * 1.2;
        scene.add(laser);
        enemyLasers.push(laser);
      } catch (e) {}
      spawnThisFrame--;
    }
  } catch (e) {}
  // Periodically check visible stars and add more near the player if density drops
  try {
    starVisibilityTimer = (starVisibilityTimer || 0) + 1;
    if (starVisibilityTimer >= STAR_CHECK_INTERVAL_FRAMES && starsGeo && starPositions) {
      starVisibilityTimer = 0;
      let visibleStars = 0;
      const tmpV = new THREE.Vector3();
      const posArr = starPositions;
      const total = Math.floor(posArr.length / 3);
      for (let i = 0; i < total; i++) {
        try {
          tmpV.set(posArr[i*3+0], posArr[i*3+1], posArr[i*3+2]);
          const p = tmpV.project(camera);
          if (isFinite(p.x) && isFinite(p.y) && isFinite(p.z) && p.z >= -1 && p.z <= 1 && p.x >= -1 && p.x <= 1 && p.y >= -1 && p.y <= 1) {
            visibleStars++;
            // early out if plenty visible
            if (visibleStars >= STAR_MIN_VISIBLE) break;
          }
        } catch (e) {}
      }
      if (visibleStars < STAR_MIN_VISIBLE) {
        // spawn stars around camera to repopulate the local view
        const current = Math.floor(starPositions.length / 3);
        // reduce spawn batch when inside the cube-in-sphere level to lower particle load
        let batchLimit = STAR_SPAWN_BATCH;
        try { if (levelCube && levelCube.userData && levelCube.userData.type === 'cubeinsphere') batchLimit = Math.max(8, Math.floor(STAR_SPAWN_BATCH / 3)); } catch (e) {}
        const canAdd = Math.max(0, Math.min(batchLimit, STAR_MAX_TOTAL - current));
        if (canAdd > 0) {
          const newArr = new Float32Array((current + canAdd) * 3);
          newArr.set(starPositions);
          for (let j = 0; j < canAdd; j++) {
            const idx = (current + j) * 3;
            // place relative to camera so new stars appear nearby
            newArr[idx + 0] = camera.position.x + (Math.random() - 0.5) * 500;
            newArr[idx + 1] = camera.position.y + (Math.random() - 0.5) * 250;
            newArr[idx + 2] = camera.position.z - (Math.random() * 1200);
          }
          starPositions = newArr;
          // replace geometry attribute (safer than resizing existing typed array)
          starsGeo.setAttribute('position', new THREE.BufferAttribute(starPositions, 3));
          starsGeo.attributes.position.needsUpdate = true;
        }
      }
    }
  } catch (e) {}

  // Cube firing: missiles every ~180 frames
  if (levelCube) {
    // Enforce a hard cooldown of 10 seconds between cube missiles
    try {
      const now = Date.now();
      const last = levelCube.userData.lastMissileAt || 0;
      const cooldown = (levelCube.userData && levelCube.userData.missileCooldown) ? levelCube.userData.missileCooldown : 10000;
      if (now - last >= cooldown) {
        shootCubeMissile();
        levelCube.userData.lastMissileAt = now;
      }
      // Sphere-specific burst attack
      try {
        if (levelCube.userData) {
          const blastLast = levelCube.userData.burstLastAt || 0;
          if (levelCube.userData.burstCooldown && (now - blastLast >= levelCube.userData.burstCooldown)) {
            // choose attack based on level type
            if (levelCube.userData.type === 'sphere') {
              shootSphereBurst();
            } else if (levelCube.userData.type === 'pyramid') {
              try {
                // ensure persistent beams are created once for pyramid level
                if (!levelCube.userData.beamsPersistentCreated) {
                  createPersistentPyramidBeams();
                  levelCube.userData.beamsPersistentCreated = true;
                }
              } catch (e) {}
            }
            levelCube.userData.burstLastAt = now;
          }
        }
      } catch (e) {}
      // For pyramid levels: spawn an occasional outward beam at a random mesh location
      try {
        if (levelCube.userData && levelCube.userData.type === 'pyramid') {
          const lastRand = levelCube.userData.randomBeamLastAt || 0;
          const interval = levelCube.userData.randomBeamInterval || 10000; // default 10s
          if (now - lastRand >= interval) {
            try { spawnRandomPyramidBeam(); } catch (e) {}
            levelCube.userData.randomBeamLastAt = now;
          }
        }
      } catch (e) {}
    } catch (e) {}
  }

  // Cube-in-Sphere: expand/move sphere, drain HP on touch, and rotate cube in phases
  try {
    if (levelCube && levelCube.userData && levelCube.userData.type === 'cubeinsphere') {
      const sph = levelCube.userData.enclosingSphere;
      if (sph) {
        const now = Date.now();
        sph.userData.lastExpandAt = sph.userData.lastExpandAt || now;
        sph.userData.lastDrainAt = sph.userData.lastDrainAt || 0;
        // Expansion step every interval (discrete jumps as configured)
        const expandInterval = sph.userData.expandInterval || 2000;
        if (now - sph.userData.lastExpandAt >= expandInterval) {
          sph.userData.lastExpandAt = now;
          sph.userData.radius = (sph.userData.radius || sph.userData.baseRadius) + (sph.userData.expandDelta || 10);
          const scale = sph.userData.radius / (sph.userData.baseRadius || 1);
          try { sph.scale.set(scale, scale, scale); } catch (e) {}
          // shift the sphere a little toward the player each expansion
          try {
            const dirToPlayer = window.playerShip.position.clone().sub(sph.position).normalize();
            sph.position.add(dirToPlayer.multiplyScalar(sph.userData.shiftAmount || 6));
          } catch (e) {}
        }

        // Cube rotation phases: rotate for a duration, pause, then pick a new axis/direction
        levelCube.userData.rotatePhase = levelCube.userData.rotatePhase || {};
        const rp = levelCube.userData.rotatePhase;
        rp.duration = rp.duration || 5000; // rotate phase length (ms)
        rp.pause = (typeof rp.pause === 'number') ? rp.pause : 500; // pause between phases
        const nowPhase = Date.now();
        if (!rp.startedAt) {
          rp.startedAt = nowPhase;
          rp.rotating = true;
          const axes = [new THREE.Vector3(1,0,0), new THREE.Vector3(0,1,0), new THREE.Vector3(0,0,1), new THREE.Vector3(1,1,0).normalize(), new THREE.Vector3(1,0,1).normalize(), new THREE.Vector3(0,1,1).normalize()];
          rp.axis = axes[Math.floor(Math.random()*axes.length)];
          rp.speed = 0.4 + Math.random() * 1.2; // rad/s
        }
        const elapsed = nowPhase - rp.startedAt;
        if (rp.rotating) {
          try {
            const ang = (rp.speed || 0.6) * (dt / 1000);
            // apply rotation to the level cube
            levelCube.rotateOnAxis(rp.axis, ang);
            // also rotate all enemies around the cube center by the same small rotation
            try {
              const q = new THREE.Quaternion().setFromAxisAngle(rp.axis, ang);
              const center = levelCube.position.clone();
              const sph = (levelCube.userData && levelCube.userData.enclosingSphere) ? levelCube.userData.enclosingSphere : null;
              const sphRadius = sph ? (sph.userData && (sph.userData.radius || sph.userData.baseRadius)) : 0;
              for (let ei = 0; ei < enemies.length; ei++) {
                const enemy = enemies[ei];
                if (!enemy) continue;
                try {
                  // only rotate enemies that are inside the enclosing sphere
                  if (sph && enemy.position.distanceTo(center) <= (sphRadius || 0) + 0.001) {
                    // rotate world position around cube center
                    enemy.position.sub(center).applyQuaternion(q).add(center);
                    // rotate movement direction so steering continues consistently
                    if (enemy.userData && enemy.userData.dir) enemy.userData.dir.applyQuaternion(q).normalize();
                  }
                } catch (e) {}
              }
              // refresh cached box for cube-based collision tests
              try { levelCube.userData.box = new THREE.Box3().setFromObject(levelCube); } catch (e) { levelCube.userData.box = null; }
            } catch (e) {}
          } catch (e) {}
          if (elapsed >= rp.duration) {
            rp.rotating = false;
            rp.startedAt = nowPhase;
          }
        } else {
          // pause complete? pick a new axis and resume
          if (elapsed >= rp.pause) {
            rp.rotating = true;
            rp.startedAt = nowPhase;
            const axes = [new THREE.Vector3(1,0,0), new THREE.Vector3(0,1,0), new THREE.Vector3(0,0,1), new THREE.Vector3(1,1,0).normalize(), new THREE.Vector3(1,0,1).normalize(), new THREE.Vector3(0,1,1).normalize()];
            rp.axis = axes[Math.floor(Math.random()*axes.length)];
            rp.speed = 0.4 + Math.random() * 1.2;
          }
        }

        // Drain player HP when inside the sphere
        try {
          const dist = window.playerShip.position.distanceTo(sph.position);
          const radius = sph.userData.radius || sph.userData.baseRadius || 0;
          if (dist < radius) {
            const nowDrain = Date.now();
            const drainInterval = sph.userData.drainIntervalMs || 500;
            if (nowDrain - sph.userData.lastDrainAt >= drainInterval) {
              sph.userData.lastDrainAt = nowDrain;
              // use applyPlayerDamage but allow the sphere's own drain interval to control frequency
              applyPlayerDamage(1, { minIntervalMs: 0, source: 'sphereDrain' });
              if (gameOver) return;
            }
          }
        } catch (e) {}
      }
    }
  } catch (e) {}

  // Update enemies
  for (let i = enemies.length - 1; i >= 0; i--) {
    const enemy = enemies[i];
    // Smooth/steering follow: maintain a direction vector and slowly lerp toward the player
    try {
      const desired = ship.position.clone().sub(enemy.position).normalize();
      if (!enemy.userData.dir) enemy.userData.dir = desired.clone();
      enemy.userData.dir.lerp(desired, ENEMY_FOLLOW_LERP);
      enemy.userData.dir.normalize();
      // move with frame-rate scaling
      try {
        // Increase speed for enemies that are outside the enclosing sphere on cube-in-sphere level
        let enemySpeed = ENEMY_SPEED;
        try {
          if (levelCube && levelCube.userData && levelCube.userData.type === 'cubeinsphere' && levelCube.userData.enclosingSphere) {
            const sph = levelCube.userData.enclosingSphere;
            const sphRadius = sph.userData && (sph.userData.radius || sph.userData.baseRadius) ? (sph.userData.radius || sph.userData.baseRadius) : 0;
            const dist = enemy.position.distanceTo(sph.position);
            if (dist > sphRadius) enemySpeed *= OUTSIDE_ENEMY_SPEED_MULT;
          }
        } catch (e) {}
        enemy.position.add(enemy.userData.dir.clone().multiplyScalar(enemySpeed * dtScale));
      } catch (e) {
        // fallback to original movement if anything fails
        enemy.position.add(enemy.userData.dir.clone().multiplyScalar(ENEMY_SPEED * dtScale));
      }
      // orient enemy to face movement direction (best-effort)
      try { enemy.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), enemy.userData.dir.clone()); } catch (e) {}
    } catch (e) {
      // Fallback: direct move if anything fails
      try {
        const toPlayer = ship.position.clone().sub(enemy.position).normalize();
        enemy.position.add(toPlayer.multiplyScalar(ENEMY_SPEED * dtScale));
      } catch (e) {}
    }
    // Enemy shoots at player every 90 frames
    enemy.userData.shootTimer = (enemy.userData.shootTimer || 0) + 1;
    const distToPlayer = enemy.position.distanceTo(ship.position);
    if (enemy.userData.shootTimer >= 90) {
      // Only fire if enemy is visible in the player's camera frustum
      let inView = false;
      try {
        const p = enemy.getWorldPosition(new THREE.Vector3()).project(camera);
        if (isFinite(p.x) && isFinite(p.y) && isFinite(p.z) && p.z >= -1 && p.z <= 1 && p.x >= -1 && p.x <= 1 && p.y >= -1 && p.y <= 1) {
          inView = true;
        }
      } catch (e) {}
      // Only shoot if the player is within a close range to avoid spam
      if (inView && distToPlayer <= 100) shootEnemyLaser(enemy, ship);
      enemy.userData.shootTimer = 0;
    }
    // Collision with player using hit radii (skip for far-away enemies to save checks)
    const enemyRadius = (enemy.userData && enemy.userData.hitRadius) ? enemy.userData.hitRadius : 1.2;
    const shipRadius = 1.0; // approximate
    if (distToPlayer <= COLLISION_CHECK_RADIUS && distToPlayer < (enemyRadius + shipRadius)) {
      // Collision: player takes damage and the enemy is destroyed by impact
      let dmg = 3;
      try { if (levelCube && levelCube.userData && levelCube.userData.type === 'pyramid') dmg += 2; } catch (e) {}
      // collision damage from ramming an enemy (reduced to 1)
      applyPlayerDamage(1, { minIntervalMs: 200, source: 'ram' });
      if (gameOver) return;
      // Create explosion and remove enemy
      try { createExplosion(enemy.position.clone()); } catch (e) {}
      killCount++;
      updateKillCounter();
      try { removeEnemyHealthBar(enemy); } catch (e) {}
      try { scene.remove(enemy); } catch (e) {}
      enemies.splice(i, 1);
      // Check player death after taking damage
      if (playerHealth <= 0) {
        playerHealth = 0;
        gameOver = true;
        try { playSound('gameover'); } catch (e) {}
        showGameOver();
        return;
      }
      // continue to next enemy
      continue;
    }
  }
  // Powerup pickup checks (supports instanced and per-mesh powerups)
  try {
    if (_powerupInstanced && powerupInfos && powerupInfos.length > 0) {
      const m4 = new THREE.Matrix4();
      for (let i = 0; i < powerupInfos.length; i++) {
        const info = powerupInfos[i];
        if (!info || !info.alive) continue;
        const pr = info.radius || 3;
        if (info.pos.distanceTo(window.playerShip.position) <= pr + 1.0) {
          try { playSound('marker'); } catch (e) {}
          playerHealth = Math.min(PLAYER_MAX_HEALTH, playerHealth + (info.heal || 10));
          updatePlayerHealthBar();
          // mark dead and shrink instance
          info.alive = false;
          const zeroScale = new THREE.Vector3(0.0001,0.0001,0.0001);
          m4.compose(info.pos, new THREE.Quaternion(), zeroScale);
          _powerupInstanced.setMatrixAt(i, m4);
          _powerupInstanced.instanceMatrix.needsUpdate = true;
        }
      }
    } else {
      for (let i = powerups.length - 1; i >= 0; i--) {
        const p = powerups[i];
        if (!p) continue;
        const pr = p.userData && p.userData.radius ? p.userData.radius : 3;
        if (p.position.distanceTo(window.playerShip.position) <= pr + 1.0) {
          // pickup
          try { playSound('marker'); } catch (e) {}
          playerHealth = Math.min(PLAYER_MAX_HEALTH, playerHealth + (p.userData && p.userData.heal ? p.userData.heal : 10));
          updatePlayerHealthBar();
          // remove and pool
          try { scene.remove(p); } catch (e) {}
          powerups.splice(i, 1);
          powerupPool.push(p);
        }
      }
    }
  } catch (e) {}
  // Update HUD marker (positions square or edge arrow)
  try { updateLevelMarkerHUD(); } catch (e) {}
  try { updateReticule(); } catch (e) {}
  renderer.render(scene, camera);
  // update particle effects after rendering
  updateEffects(dt);
  // update asteroids rotation
  try { updateAsteroids(dt); } catch (e) {}
  // update powerups
  try { updatePowerups(dt); } catch (e) {}
}
// Update particle effects each frame
function updateEffects(dt) {
  const now = Date.now();
  for (let i = effects.length - 1; i >= 0; i--) {
    const ef = effects[i];
    const age = now - ef.start;
    const t = age / ef.lifetime;
    const posAttr = ef.geom.getAttribute('position');
    for (let p = 0; p < ef.velocities.length; p++) {
      const v = ef.velocities[p];
      posAttr.array[p * 3 + 0] += v.x * (dt / 1000);
      posAttr.array[p * 3 + 1] += v.y * (dt / 1000);
      posAttr.array[p * 3 + 2] += v.z * (dt / 1000);
      // simple gravity
      v.y -= 9.8 * 0.06;
    }
    posAttr.needsUpdate = true;
    ef.mat.opacity = Math.max(0, 1 - t);
    if (age > ef.lifetime) {
      scene.remove(ef.pts);
      try { ef.geom.dispose(); } catch (e) {}
      try { ef.mat.dispose(); } catch (e) {}
      effects.splice(i, 1);
    }
  }
}
// Spawn a geometric enemy (tetrahedron or cube)
function spawnEnemy(center) {
  const types = [
    () => new THREE.CylinderGeometry(0.9, 0.9, 0.6, 3), // triangular prism
    () => new THREE.ConeGeometry(1.0, 1.2, 3) // triangular cone
  ];
  const geo = types[Math.floor(Math.random() * types.length)]();
  // Choose lower-cost enemy visuals on pyramid levels for performance
  const isPyramidLevel = (levelCube && levelCube.userData && levelCube.userData.type === 'pyramid');
  let mat;
  if (isPyramidLevel) {
    // simple unlit material reduces shader cost
    mat = new THREE.MeshBasicMaterial({ color: 0xd0d0d0 });
  } else {
    // Brighter, glowing "space-plane" material (orange)
    mat = new THREE.MeshStandardMaterial({ color: 0xd0d0d0, flatShading: true, emissive: 0x999999, emissiveIntensity: 0.35, metalness: 0.3, roughness: 0.4 });
  }
  const enemy = new THREE.Mesh(geo, mat);
  // Allow frustum culling for pyramid-level enemies to reduce render cost when offscreen
  try { enemy.frustumCulled = !!isPyramidLevel; } catch (e) {}
  // Compute hit radius from geometry bounding sphere (account for scale)
  if (!geo.boundingSphere) geo.computeBoundingSphere();
  const baseRadius = geo.boundingSphere ? geo.boundingSphere.radius : 1;
  const maxScale = Math.max(enemy.scale.x, enemy.scale.y, enemy.scale.z) || 1;
  enemy.userData.hitRadius = baseRadius * maxScale;
  // Make shape flatter/elongated to look more like a space-plane
  enemy.scale.set(1.6, 0.5, 2.0);
  // Add a small point light and sprite for non-pyramid (higher-fidelity) enemies
  if (!isPyramidLevel) {
    const glow = new THREE.PointLight(0xdddddd, 0.25, 8);
    glow.position.set(0, 0, 0);
    enemy.add(glow);
    enemy.userData.glow = glow;
    const sprMat = new THREE.SpriteMaterial({ color: 0xcccccc, blending: THREE.AdditiveBlending, opacity: 0.6 });
    const spr = new THREE.Sprite(sprMat);
    spr.scale.set(1.2, 1.2, 1);
    spr.position.set(0, -0.2, -0.9);
    spr.material.depthWrite = false;
    spr.material.depthTest = true;
    enemy.add(spr);
    enemy.userData.glowSprite = spr;
  }
  // ensure hitRadius accounts for scale we just set
  enemy.userData.hitRadius = (geo.boundingSphere ? geo.boundingSphere.radius : 1) * Math.max(enemy.scale.x, enemy.scale.y, enemy.scale.z);
  // Add a small white cockpit/dome on the nose
  // Add a small cockpit dome; use cheaper geometry/material on pyramid level
  try {
    if (isPyramidLevel) {
      const domeGeo = new THREE.SphereGeometry(0.22, 6, 4);
      const domeMat = new THREE.MeshBasicMaterial({ color: 0xffffff });
      const dome = new THREE.Mesh(domeGeo, domeMat);
      dome.position.set(0, 0.12, 0.7);
      enemy.add(dome);
      enemy.userData.dome = dome;
    } else {
      const domeGeo = new THREE.SphereGeometry(0.22, 12, 8);
      const domeMat = new THREE.MeshStandardMaterial({ color: 0xffffff, metalness: 0.3, roughness: 0.2 });
      const dome = new THREE.Mesh(domeGeo, domeMat);
      dome.position.set(0, 0.12, 0.7);
      enemy.add(dome);
      enemy.userData.dome = dome;
    }
  } catch (e) {}
  // Enemy health
  enemy.userData.hp = 3;
  // Spawn position: either around a provided center (e.g., the cube) or relative to player
  const ship = window.playerShip;
  const minDist = 80;
  const maxDist = 160;
  let spawnPos = new THREE.Vector3();
  if (center && levelCube && center.equals(levelCube.position)) {
    // Spawn around the cube at a radius outside the cube surface
    const cubeRadius = levelCube.userData.hitRadius || (levelCube.userData.size ? levelCube.userData.size / 2 : 200);
    const minFromCube = cubeRadius + 20;
    const maxFromCube = cubeRadius + 140;
    const distFromCube = minFromCube + Math.random() * (maxFromCube - minFromCube);
    const rnd = new THREE.Vector3((Math.random()-0.5), (Math.random()-0.5), (Math.random()-0.5)).normalize();
    spawnPos.copy(center).add(rnd.multiplyScalar(distFromCube));
    // ensure minimum separation from player
    if (spawnPos.distanceTo(ship.position) < minDist) {
      const dir = spawnPos.clone().sub(ship.position).normalize();
      spawnPos.copy(ship.position).add(dir.multiplyScalar(minDist));
    }
  } else {
    // Default: spawn in front of player with slight forward bias
    const dist = minDist + Math.random() * (maxDist - minDist);
    const rnd = new THREE.Vector3((Math.random() - 0.5), (Math.random() - 0.3), -(0.2 + Math.random() * 0.8)).normalize();
    spawnPos.copy(ship.position).add(rnd.multiplyScalar(dist));
    if (spawnPos.distanceTo(ship.position) < minDist) spawnPos.copy(ship.position).add(rnd.normalize().multiplyScalar(minDist));
  }
  // Ensure we do not spawn inside the level cube
  if (levelCube) {
    try {
      const cubeCenter = levelCube.position.clone();
      const cubeRadius = levelCube.userData.hitRadius || (levelCube.userData.size ? levelCube.userData.size / 2 : 200);
      const enemyRadius = enemy.userData.hitRadius || 1.0;
      const minFromCube = cubeRadius + enemyRadius + 8; // ensure enemy appears outside cube + buffer
      const toCube = spawnPos.clone().sub(cubeCenter);
      if (toCube.length() < minFromCube) {
        if (toCube.length() < 1e-3) {
          // pick a random direction away from cube
          const dir = new THREE.Vector3((Math.random()-0.5), (Math.random()-0.5), (Math.random()-0.5)).normalize();
          spawnPos.copy(cubeCenter).add(dir.multiplyScalar(minFromCube));
        } else {
          spawnPos.copy(cubeCenter).add(toCube.normalize().multiplyScalar(minFromCube));
        }
      }
    } catch (e) {}
  }
  // For cube-in-sphere level, also ensure spawn is outside the enclosing sphere
  if (levelCube && levelCube.userData && levelCube.userData.type === 'cubeinsphere' && levelCube.userData.enclosingSphere) {
    try {
      const sph = levelCube.userData.enclosingSphere;
      const sphCenter = sph.position ? sph.position.clone() : levelCube.position.clone();
      const sphRadius = (sph.userData && (sph.userData.radius || sph.userData.baseRadius)) ? (sph.userData.radius || sph.userData.baseRadius) : (sph.geometry && sph.geometry.boundingSphere ? sph.geometry.boundingSphere.radius : 0);
      const enemyRadius = enemy.userData.hitRadius || 1.0;
      const minFromSphere = sphRadius + enemyRadius + 12; // buffer to keep enemies clear of sphere
      const toSph = spawnPos.clone().sub(sphCenter);
      if (toSph.length() < minFromSphere) {
        if (toSph.length() < 1e-3) {
          const dir = new THREE.Vector3((Math.random()-0.5), (Math.random()-0.5), (Math.random()-0.5)).normalize();
          spawnPos.copy(sphCenter).add(dir.multiplyScalar(minFromSphere));
        } else {
          spawnPos.copy(sphCenter).add(toSph.normalize().multiplyScalar(minFromSphere));
        }
      }
    } catch (e) {}
  }
  enemy.position.copy(spawnPos);
  scene.add(enemy);
  enemies.push(enemy);
  createEnemyHealthBar(enemy);
}

// Spawn a batch of enemies around the cube at game start
function spawnInitialShips(count) {
  if (!levelCube) return;
  // global tuning: reduce overall initial ships by 20% to lower load
  try { count = Math.max(1, Math.floor(count * 0.8)); } catch (e) {}
  // For cube-in-sphere level, spawn more enemies outside the enclosing sphere and spread them wider
  if (levelCube && levelCube.userData && levelCube.userData.type === 'cubeinsphere' && levelCube.userData.enclosingSphere) {
    const sph = levelCube.userData.enclosingSphere;
    const baseCount = count * 2; // double
    const center = levelCube.position.clone();
    const sphRadius = sph.userData && (sph.userData.radius || sph.userData.baseRadius) ? (sph.userData.radius || sph.userData.baseRadius) : 0;
    for (let i = 0; i < baseCount; i++) {
      try {
        const dir = new THREE.Vector3((Math.random()-0.5), (Math.random()-0.5), (Math.random()-0.5)).normalize();
        const dist = sphRadius + 60 + Math.random() * 600; // spread from just outside sphere to far field
        const pos = center.clone().add(dir.multiplyScalar(dist));
        // spawn an enemy at pos
        const e = spawnEnemy();
        if (e && e.position) {
          e.position.copy(pos);
        } else {
          // fallback: create enemy like spawnBlockingShips
          const types = [
            () => new THREE.CylinderGeometry(0.9, 0.9, 0.6, 3),
            () => new THREE.ConeGeometry(1.0, 1.2, 3)
          ];
          const geo = types[Math.floor(Math.random() * types.length)]();
          const mat = new THREE.MeshStandardMaterial({ color: 0xd0d0d0, flatShading: true, emissive: 0x999999, emissiveIntensity: 0.35, metalness: 0.3, roughness: 0.4 });
          const enemy = new THREE.Mesh(geo, mat);
          enemy.scale.set(1.6, 0.5, 2.0);
          enemy.position.copy(pos);
          if (!geo.boundingSphere) geo.computeBoundingSphere();
          enemy.userData.hitRadius = (geo.boundingSphere ? geo.boundingSphere.radius : 1) * Math.max(enemy.scale.x, enemy.scale.y, enemy.scale.z);
          enemy.userData.hp = 3;
          scene.add(enemy);
          enemies.push(enemy);
          createEnemyHealthBar(enemy);
        }
      } catch (e) { console.warn('spawnInitialShips (cubeinsphere) failed', e); }
    }
    return;
  }
  for (let i = 0; i < count; i++) {
    try { spawnEnemy(levelCube.position); } catch (e) { console.warn('spawnInitialShips failed', e); }
  }
}

// Spawn ships on a band between the player and the cube so they block the approach
function spawnBlockingShips(count) {
  const ship = window.playerShip;
  if (!ship || !levelCube) return;
  // global tuning: reduce blocking ships by 20% to lower load
  try { count = Math.max(1, Math.floor(count * 0.8)); } catch (e) {}
  const cubePos = levelCube.position.clone();
  const dir = cubePos.clone().sub(ship.position).normalize();
  const totalDist = ship.position.distanceTo(cubePos);
  // spawn in the corridor from ~18% to ~72% of the way to the cube (widen if cube-in-sphere)
  let minT = 0.18, maxT = 0.72;
  let offsetMin = 20, offsetMax = 120;
  if (levelCube.userData && levelCube.userData.type === 'cubeinsphere') {
    // spread further and allow more blocking ships
    minT = 0.12; maxT = 0.9;
    offsetMin = 60; offsetMax = 320;
    // double count when requested
    count = Math.max(count * 2, count);
  }
  for (let i = 0; i < count; i++) {
    const t = minT + Math.random() * (maxT - minT);
    const basePos = ship.position.clone().lerp(cubePos, t);
    // offset randomly perpendicular to the direction
    const perp = new THREE.Vector3((Math.random()-0.5), (Math.random()-0.5), (Math.random()-0.5)).normalize();
    const offset = perp.multiplyScalar(offsetMin + Math.random() * (offsetMax - offsetMin));
    const spawnPos = basePos.add(offset);
    try {
      // spawn enemy at spawnPos but ensure minimum distance from player
      const e = spawnEnemy();
      if (e) {
        // if spawnEnemy returns a mesh when refactored; otherwise place by creating a new enemy directly
      }
      // fallback: create enemy similar to spawnEnemy but positioned at spawnPos
      const types = [
        () => new THREE.CylinderGeometry(0.9, 0.9, 0.6, 3),
        () => new THREE.ConeGeometry(1.0, 1.2, 3)
      ];
      const geo = types[Math.floor(Math.random() * types.length)]();
      const mat = new THREE.MeshStandardMaterial({ color: 0xd0d0d0, flatShading: true, emissive: 0x999999, emissiveIntensity: 0.35, metalness: 0.3, roughness: 0.4 });
      const enemy = new THREE.Mesh(geo, mat);
      enemy.scale.set(1.6, 0.5, 2.0);
      enemy.position.copy(spawnPos);
      if (!geo.boundingSphere) geo.computeBoundingSphere();
      enemy.userData.hitRadius = (geo.boundingSphere ? geo.boundingSphere.radius : 1) * Math.max(enemy.scale.x, enemy.scale.y, enemy.scale.z);
      enemy.userData.hp = 3;
      scene.add(enemy);
      enemies.push(enemy);
      createEnemyHealthBar(enemy);
    } catch (e) { console.warn('spawnBlockingShips item failed', e); }
  }
}

// Enemy shoots a laser at the player
function shootEnemyLaser(enemy, player) {
  const laser = acquireEnemyLaser();
  laser.position.copy(enemy.position);
  const dir = player.position.clone().sub(enemy.position).normalize();
  laser.userData.dir = dir;
  laser.userData.origin = enemy.position.clone();
  laser.userData.owner = enemy;
  laser.userData.prevPos = laser.position.clone();
  laser.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), dir);
  scene.add(laser);
  enemyLasers.push(laser);
  try { playSound('shoot'); } catch (e) {}
}

// Cube fires destructible missiles at the player
function shootCubeMissile() {
  if (!levelCube || !window.playerShip) return;
  // enforce a soft cap on active missiles to prevent spikes
  const perLevelCap = (levelCube && levelCube.userData && levelCube.userData.maxActiveMissiles) ? levelCube.userData.maxActiveMissiles : MAX_ACTIVE_MISSILES;
  if (cubeMissiles.length >= perLevelCap) return;
  const missile = acquireMissile();
  // spawn at a random point on cube surface
  const local = new THREE.Vector3((Math.random()-0.5), (Math.random()-0.5), (Math.random()-0.5)).normalize();
  const cubeSize = levelCube.userData.size || 400;
  const surfacePos = local.clone().multiplyScalar(cubeSize/2 + 2).add(levelCube.position);
  missile.position.copy(surfacePos);
  const dir = window.playerShip.position.clone().sub(missile.position).normalize();
  missile.userData = { dir, origin: missile.position.clone(), hp: 1, prevPos: missile.position.clone() };
  missile.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), dir);
  try { missile.material.depthWrite = false; } catch (e) {}
  scene.add(missile);
  cubeMissiles.push(missile);
  try { playSound('shoot'); } catch (e) {}
}

// Sphere special: emit a burst of pink lasers in a random band around the sphere
function shootSphereBurst() {
  if (!levelCube) return;
  // Enqueue burst directions and let the animate loop instantiate them over several frames
  const count = 320; // total desired burst lasers (reduced for performance)
  const minPolar = (30 * Math.PI) / 180; // 30 degrees
  const maxPolar = (150 * Math.PI) / 180; // 150 degrees -> band around equator
  for (let i = 0; i < count; i++) {
    try {
      const phi = Math.random() * Math.PI * 2;
      const theta = minPolar + Math.random() * (maxPolar - minPolar);
      const dir = new THREE.Vector3(Math.sin(theta) * Math.cos(phi), Math.cos(theta), Math.sin(theta) * Math.sin(phi)).normalize();
      burstSpawnQueue.push({ origin: levelCube.position.clone(), dir });
    } catch (e) {}
  }
  try { playSound('shoot'); } catch (e) {}
}

// Pyramid attack: fire huge golden beams from pyramid 'points'
function shootPyramidBeams() {
  if (!levelCube) return;
  // define beam parameters
  const points = 5; // apex + 4 base corners
  const range = 1600; // how far beams reach
  const duration = 1200; // ms beam stays active
  const beamRadius = 12; // collision radius (large damage)
  // pyramid geometry params we used when creating: radius/height stored on userData
  const radius = levelCube.userData.radius || 200;
  const height = levelCube.userData.height || 300;
  const originLocal = new THREE.Vector3(0, 0, 0);
  for (let i = 0; i < points; i++) {
    try {
      // prefer exact geometry-derived corner positions/normals on the mesh
      let localPos, localNormal;
      const localCorners = (levelCube.userData && levelCube.userData.cornersLocal) ? levelCube.userData.cornersLocal : null;
      if (localCorners && localCorners[i]) {
        localPos = localCorners[i].pos.clone();
        localNormal = localCorners[i].normal.clone();
      } else {
        if (i === 0) {
          localPos = new THREE.Vector3(0, height * 0.5, 0);
          localNormal = new THREE.Vector3(0, 1, 0);
        } else {
          const a = ((i - 1) / 4) * Math.PI * 2;
          localPos = new THREE.Vector3(Math.cos(a) * radius, -height * 0.5, Math.sin(a) * radius);
          localNormal = localPos.clone().normalize();
        }
      }
      // compute world-space origin and direction using mesh transform
      const worldPos = levelCube.localToWorld(localPos.clone());
      // apex/top beam should point straight up in world-space
      const dir = (i === 0) ? new THREE.Vector3(0,1,0) : localNormal.clone().applyQuaternion(levelCube.quaternion).normalize();
      // create beam mesh, stretch it to cover range and position its center
      const beam = acquirePyramidBeam();
      const halfLen = range * 0.5;
      beam.scale.set(6, range, 6);
      // cylinder is centered; place its center at origin + dir * halfLen
      const center = worldPos.clone().add(dir.clone().multiplyScalar(halfLen));
      beam.position.copy(center);
      // beam should point along world-fixed dir
      beam.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), dir);
      // mark apex beam as world-aligned so it always points straight up
      const worldAligned = (i === 0);
      beam.userData = { origin: worldPos.clone(), dir: dir.clone(), range, start: Date.now(), duration, radius: beamRadius, damage: 40, localPos: localPos.clone(), localNormal: localNormal.clone(), worldAligned };
      scene.add(beam);
      pyramidBeamsActive.push(beam);
    } catch (e) {}
  }
  try { playSound('shoot'); } catch (e) {}
}

// Create persistent beams at the pyramid's corners (they remain until level end)
function createPersistentPyramidBeams() {
  if (!levelCube) return;
  // reuse pyramid beam logic but mark beams persistent
  const range = 1600;
  const radius = levelCube.userData.radius || 200;
  // use stored geometry corner positions if available
  const localPositions = (levelCube.userData && levelCube.userData.cornersLocal && levelCube.userData.cornersLocal.length) ? levelCube.userData.cornersLocal : null;
  const points = localPositions ? localPositions.length : 5;
  for (let i = 0; i < points; i++) {
    try {
      let localPos, localNormal;
      if (localPositions && localPositions[i]) {
        localPos = localPositions[i].pos.clone();
        localNormal = localPositions[i].normal.clone();
      } else {
        if (i === 0) {
          localPos = new THREE.Vector3(0, levelCube.userData.height * 0.5, 0);
          localNormal = new THREE.Vector3(0,1,0);
        } else {
          const a = ((i - 1) / 4) * Math.PI * 2;
          localPos = new THREE.Vector3(Math.cos(a) * radius, -levelCube.userData.height * 0.5, Math.sin(a) * radius);
          localNormal = localPos.clone().normalize();
        }
      }
      const worldPos = levelCube.localToWorld(localPos.clone());
      // apex/top beam should point straight up in world-space, not follow mesh rotation
      const dir = (i === 0) ? new THREE.Vector3(0,1,0) : localNormal.clone().applyQuaternion(levelCube.quaternion).normalize();
      const beam = acquirePyramidBeam();
      const halfLen = range * 0.5;
      beam.scale.set(6, range, 6);
      const center = worldPos.clone().add(dir.clone().multiplyScalar(halfLen));
      beam.position.copy(center);
      beam.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), dir);
      const worldAligned = (i === 0);
      beam.userData = { origin: worldPos.clone(), dir: dir.clone(), range, persistent: true, radius: 12, damage: 40, localPos: localPos.clone(), localNormal: localNormal.clone(), worldAligned };
      scene.add(beam);
      pyramidBeamsActive.push(beam);
    } catch (e) {}
  }
}

// Spawn a one-off outward beam from a random point on the pyramid mesh
function spawnRandomPyramidBeam() {
  if (!levelCube || levelCube.userData.type !== 'pyramid') return;
  try {
    const geo = levelCube.geometry;
    if (!geo || !geo.attributes || !geo.attributes.position) return;
    const posAttr = geo.attributes.position;
    const normAttr = geo.attributes.normal;
    const idx = Math.floor(Math.random() * posAttr.count);
    const localPos = new THREE.Vector3(posAttr.getX(idx), posAttr.getY(idx), posAttr.getZ(idx));
    const localNormal = normAttr ? new THREE.Vector3(normAttr.getX(idx), normAttr.getY(idx), normAttr.getZ(idx)) : localPos.clone().normalize();
    const worldPos = levelCube.localToWorld(localPos.clone());
    // pick a random direction (uniform-ish) for the spawned beam
    let dir = new THREE.Vector3(Math.random() * 2 - 1, Math.random() * 2 - 1, Math.random() * 2 - 1).normalize();
    const beam = acquirePyramidBeam();
    // make spawned beams persistent and match the persistent-beam appearance
    const range = 1600;
    const radius = 12;
    beam.scale.set(6, range, 6);
    const halfLen = range * 0.5;
    const center = worldPos.clone().add(dir.clone().multiplyScalar(halfLen));
    beam.position.copy(center);
    beam.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), dir);
    beam.userData = { origin: worldPos.clone(), dir: dir.clone(), range, radius, damage: 40, localPos: localPos.clone(), localNormal: localNormal.clone(), persistent: true, worldAligned: false };
    scene.add(beam);
    pyramidBeamsActive.push(beam);
    try { playSound('shoot'); } catch (e) {}
  } catch (e) {}
}

function createEnemyHealthBar(enemy) {
  const bar = document.createElement('div');
  bar.className = 'enemy-health-bar';
  bar.style.position = 'absolute';
  // Start offscreen until first update places it (use GPU transform to avoid layouts)
  bar.style.transform = 'translate3d(-9999px,-9999px,0)';
  bar.style.willChange = 'transform';
  bar.style.display = 'none';
  bar.style.width = '40px';
  bar.style.height = '6px';
  bar.style.background = '#222';
  bar.style.border = '1px solid #fff';
  bar.style.borderRadius = '3px';
  bar.style.overflow = 'hidden';
  bar.style.pointerEvents = 'none';
  bar.style.zIndex = '20';
  const fill = document.createElement('div');
  fill.className = 'enemy-health-fill';
  fill.style.height = '100%';
  fill.style.width = '100%';
  fill.style.background = '#f00';
  fill.style.transition = 'width 0.1s';
  bar.appendChild(fill);
  document.body.appendChild(bar);
  enemy.userData.healthBar = bar;
  enemy.userData.healthFill = fill;
}

function createKillCounter() {
  const el = document.createElement('div');
  el.id = 'kill-counter';
  el.style.position = 'fixed';
  el.style.right = '18px';
  el.style.top = '18px';
  el.style.color = '#fff';
  el.style.background = 'rgba(0,0,0,0.4)';
  el.style.padding = '8px 12px';
  el.style.borderRadius = '8px';
  el.style.fontFamily = 'sans-serif';
  el.style.fontSize = '18px';
  el.style.zIndex = '200';
  el.innerText = `Kills: ${killCount}`;
  document.body.appendChild(el);
  window.killCounterEl = el;
}

function updateKillCounter() {
  if (!window.killCounterEl) createKillCounter();
  window.killCounterEl.innerText = `Kills: ${killCount}`;
}

function createExplosion(origin) {
  const particleCount = 24;
  const positions = new Float32Array(particleCount * 3);
  const colors = new Float32Array(particleCount * 3);
  const velocities = [];
  for (let i = 0; i < particleCount; i++) {
    positions[i * 3 + 0] = origin.x;
    positions[i * 3 + 1] = origin.y;
    positions[i * 3 + 2] = origin.z;
    const t = Math.random();
    const r = 1.0;
    const g = 0.45 + 0.5 * t;
    const b = 0.08;
    colors[i * 3 + 0] = r;
    colors[i * 3 + 1] = g;
    colors[i * 3 + 2] = b;
    // softer velocity
    const dir = new THREE.Vector3((Math.random() - 0.5), (Math.random() - 0.5), (Math.random() - 0.5)).normalize();
    const speed = 3 + Math.random() * 3;
    velocities.push(dir.multiplyScalar(speed));
  }
  const geom = new THREE.BufferGeometry();
  geom.setAttribute('position', new THREE.BufferAttribute(positions, 3));
  geom.setAttribute('color', new THREE.BufferAttribute(colors, 3));
  const mat = new THREE.PointsMaterial({ size: 0.12, vertexColors: true, transparent: true, opacity: 0.6, depthWrite: false, blending: THREE.NormalBlending });
  const pts = new THREE.Points(geom, mat);
  scene.add(pts);
  effects.push({ pts, geom, mat, velocities, start: Date.now(), lifetime: 900 });
  try { playSound('explosion'); } catch (e) {}
}

// Level cube (background objective)
function createLevelCube() {
  // remove existing
  if (levelCube) {
    try { scene.remove(levelCube); } catch(e){}
    levelCube = null;
  }
  // create canvases: white base + green grid emissive
  const size = 1024;
  const base = document.createElement('canvas');
  base.width = base.height = size;
  const bctx = base.getContext('2d');
  // very dark grey base for the cube faces
  bctx.fillStyle = '#111218';
  bctx.fillRect(0,0,size,size);

  const grid = document.createElement('canvas');
  grid.width = grid.height = size;
  const gctx = grid.getContext('2d');
  gctx.clearRect(0,0,size,size);
  // dark-blue grid that will be used as an emissive map (pulses brighter)
  gctx.strokeStyle = '#0b2b66';
  gctx.lineWidth = 3;
  const step = 64;
  for (let x = 0; x < size; x += step) {
    gctx.beginPath(); gctx.moveTo(x,0); gctx.lineTo(x,size); gctx.stroke();
  }
  for (let y = 0; y < size; y += step) {
    gctx.beginPath(); gctx.moveTo(0,y); gctx.lineTo(size,y); gctx.stroke();
  }

  const baseTex = new THREE.CanvasTexture(base);
  baseTex.needsUpdate = true;
  const gridTex = new THREE.CanvasTexture(grid);
  gridTex.needsUpdate = true;

  // make a true cube (not a flat slab)
  const cubeSize = 400;
  const geo = new THREE.BoxGeometry(cubeSize, cubeSize, cubeSize);
  // tile the grid texture across faces
  gridTex.wrapS = gridTex.wrapT = THREE.RepeatWrapping;
  gridTex.repeat.set(8, 8);
  const mat = new THREE.MeshStandardMaterial({ color: 0x111218, map: baseTex, emissiveMap: gridTex, emissive: 0x0b2b66, emissiveIntensity: 0.2, metalness: 0.2, roughness: 0.4, side: THREE.DoubleSide });
  const cube = new THREE.Mesh(geo, mat);
  // place far ahead of player's start position
  const start = window.playerShip ? window.playerShip.position.clone() : new THREE.Vector3(0,0,0);
  const forward = new THREE.Vector3(0,0,-1).applyEuler((window.playerShip && window.playerShip.rotation) ? window.playerShip.rotation : new THREE.Euler());
  // place the cube farther away so player must fight through ships
  cube.position.copy(start).add(forward.multiplyScalar(1200));
  cube.userData.hp = 100;
  cube.userData.size = cubeSize;
  // pulsate settings: start dim and pulse brighter
  cube.userData._emissiveBase = 0.2;
  cube.userData._emissiveAmp = 0.8;
  // compute hit radius
  geo.computeBoundingSphere();
  cube.userData.hitRadius = geo.boundingSphere ? geo.boundingSphere.radius : Math.max(cubeW,cubeH)/2;
  scene.add(cube);
  levelCube = cube;
  // cache cube bounding box for reuse in collision/occlusion tests
  try { levelCube.userData.box = new THREE.Box3().setFromObject(levelCube); } catch (e) { levelCube.userData.box = null; }
  // last missile timestamp (ms) - used to enforce cooldown between cube missiles
  levelCube.userData.lastMissileAt = 0;
  // default missile cooldown for cube (10s)
  levelCube.userData.missileCooldown = 10000;
  createLevelHealthUI();
  placeLevelMarker(cube);
  createLevelMarkerHUD();
  try { updateLevelMarkerHUD(); } catch (e) {}
  // spawn initial enemy wave around cube (reduced for smoother play)
  try { spawnInitialShips(15); } catch (e) { console.warn('initial spawn failed', e); }
  // spawn blocking ships between player and the cube so player must fight through (reduced)
  try { spawnBlockingShips(15); } catch (e) { console.warn('blocking spawn failed', e); }
}

// Create a spherical level (next-level variant) with pink base and purple grid
function createLevelSphere() {
  if (levelCube) {
    try { scene.remove(levelCube); } catch(e){}
    levelCube = null;
  }
  const size = 1024;
  const base = document.createElement('canvas');
  base.width = base.height = size;
  const bctx = base.getContext('2d');
  // bright pink base for the sphere
  bctx.fillStyle = '#ff2aa6';
  bctx.fillRect(0,0,size,size);

  const grid = document.createElement('canvas');
  grid.width = grid.height = size;
  const gctx = grid.getContext('2d');
  gctx.clearRect(0,0,size,size);
  // purple grid
  gctx.strokeStyle = '#5a00b8';
  gctx.lineWidth = 3;
  const step = 64;
  for (let x = 0; x < size; x += step) { gctx.beginPath(); gctx.moveTo(x,0); gctx.lineTo(x,size); gctx.stroke(); }
  for (let y = 0; y < size; y += step) { gctx.beginPath(); gctx.moveTo(0,y); gctx.lineTo(size,y); gctx.stroke(); }

  const baseTex = new THREE.CanvasTexture(base);
  baseTex.needsUpdate = true;
  const gridTex = new THREE.CanvasTexture(grid);
  gridTex.needsUpdate = true;

  // sphere geometry
  const sphereRadius = 200;
  const geo = new THREE.SphereGeometry(sphereRadius, 24, 18);
  gridTex.wrapS = gridTex.wrapT = THREE.RepeatWrapping;
  gridTex.repeat.set(8, 8);
  const mat = new THREE.MeshStandardMaterial({ color: 0xff2aa6, map: baseTex, emissiveMap: gridTex, emissive: 0x5a00b8, emissiveIntensity: 0.45, metalness: 0.2, roughness: 0.4, side: THREE.DoubleSide });
  const sphere = new THREE.Mesh(geo, mat);
  const start = window.playerShip ? window.playerShip.position.clone() : new THREE.Vector3(0,0,0);
  const forward = new THREE.Vector3(0,0,-1).applyEuler((window.playerShip && window.playerShip.rotation) ? window.playerShip.rotation : new THREE.Euler());
  sphere.position.copy(start).add(forward.multiplyScalar(1200));
  sphere.userData.hp = 120;
  sphere.userData.size = sphereRadius * 2;
  sphere.userData.type = 'sphere';
  sphere.userData._emissiveBase = 0.2;
  sphere.userData._emissiveAmp = 0.8;
  geo.computeBoundingSphere();
  sphere.userData.hitRadius = geo.boundingSphere ? geo.boundingSphere.radius : sphereRadius;
  scene.add(sphere);
  levelCube = sphere;
  try { levelCube.userData.box = new THREE.Box3().setFromObject(levelCube); } catch (e) { levelCube.userData.box = null; }
  levelCube.userData.lastMissileAt = 0;
  // sphere fires missiles faster (6s)
  levelCube.userData.missileCooldown = 6000;
  // sphere burst attack: 30 lasers every 15s
  levelCube.userData.burstLastAt = 0;
  levelCube.userData.burstCooldown = 15000;
  createLevelHealthUI();
  placeLevelMarker(sphere);
  createLevelMarkerHUD();
  try { updateLevelMarkerHUD(); } catch (e) {}
  // increase ships for sphere level (harder)
  try { spawnInitialShips(80); } catch (e) { console.warn('initial spawn failed', e); }
  try { spawnBlockingShips(60); } catch (e) { console.warn('blocking spawn failed', e); }
}

// Create a level with a cube inside a translucent sphere. The sphere expands every
// `expandInterval` ms, moves slightly toward the player, and drains HP when touched.
function createLevelCubeInSphere() {
  // remove existing
  if (levelCube) {
    try { scene.remove(levelCube); } catch(e){}
    levelCube = null;
  }
  // create cube (dark blue)
  const cubeSize = 400;
  const geo = new THREE.BoxGeometry(cubeSize, cubeSize, cubeSize);
  const mat = new THREE.MeshStandardMaterial({ color: 0x001244, metalness: 0.2, roughness: 0.4 });
  const cube = new THREE.Mesh(geo, mat);
  const start = window.playerShip ? window.playerShip.position.clone() : new THREE.Vector3(0,0,0);
  const forward = new THREE.Vector3(0,0,-1).applyEuler((window.playerShip && window.playerShip.rotation) ? window.playerShip.rotation : new THREE.Euler());
  cube.position.copy(start).add(forward.multiplyScalar(1200));
  cube.userData.size = cubeSize;
  cube.userData.hp = 200;
  cube.userData.type = 'cubeinsphere';
  // compute hit radius
  try { geo.computeBoundingSphere(); cube.userData.hitRadius = geo.boundingSphere ? geo.boundingSphere.radius : cubeSize / 2; } catch (e) { cube.userData.hitRadius = cubeSize / 2; }
  scene.add(cube);
  levelCube = cube;

  // create enclosing translucent white sphere initially touching cube corners
  const cornerDist = Math.sqrt(3) * (cubeSize / 2);
  const sphereRadius = cornerDist; // so corners touch
  const sphGeo = new THREE.SphereGeometry(sphereRadius, 32, 24);
  const sphMat = new THREE.MeshStandardMaterial({ color: 0xffffff, transparent: true, opacity: 0.12, side: THREE.DoubleSide });
  const sphere = new THREE.Mesh(sphGeo, sphMat);
  // sphere initially centered on cube
  sphere.position.copy(cube.position);
  sphere.userData.baseRadius = sphereRadius;
  sphere.userData.radius = sphereRadius;
  sphere.userData.expandInterval = 2000; // ms
  sphere.userData.lastExpandAt = Date.now();
  sphere.userData.expandDelta = 10; // increase radius by 10 units per expand
  sphere.userData.shiftAmount = 6; // move toward player by this many units each expand
  // drain settings
  sphere.userData.drainIntervalMs = 500; // drain 1 HP every 500ms while touching
  sphere.userData.lastDrainAt = 0;
  scene.add(sphere);
  // keep reference on cube
  try { cube.userData.enclosingSphere = sphere; } catch (e) {}

  // make sphere visually very translucent and not write depth to avoid blocking visuals
  try { sphere.material.depthWrite = false; } catch (e) {}

  // adjust missile behaviour for this level: fire twice as often and allow more active missiles
  try { levelCube.userData.lastMissileAt = 0; } catch (e) {}
  try { levelCube.userData.missileCooldown = 5000; } catch (e) {}
  try { levelCube.userData.maxActiveMissiles = MAX_ACTIVE_MISSILES * 2; } catch (e) {}

  // UI and marker
  createLevelHealthUI();
  placeLevelMarker(cube);
  createLevelMarkerHUD();
  try { updateLevelMarkerHUD(); } catch (e) {}

  // spawn enemies moderately
  try { spawnInitialShips(30); } catch (e) { console.warn('initial spawn failed', e); }
  try { spawnBlockingShips(30); } catch (e) { console.warn('blocking spawn failed', e); }
  // create an asteroid field outside the sphere for visual variety
  try { createAsteroidField(36); } catch (e) {}
}

// Simple asteroid field: non-colliding visual rocks placed around the level
let asteroids = [];
let asteroidInfos = []; // per-instance transform + spin data
let _asteroidInstanced = null;
function createAsteroidField(count) {
  // remove old asteroids
  try {
    for (let a of asteroids) scene.remove(a);
    if (_asteroidInstanced) { try { scene.remove(_asteroidInstanced); } catch (e) {} _asteroidInstanced = null; }
  } catch (e) {}
  asteroids = [];
  asteroidInfos = [];
  if (!levelCube || !levelCube.userData || !levelCube.userData.enclosingSphere) return;
  const sph = levelCube.userData.enclosingSphere;
  const center = levelCube.position.clone();
  const baseRadius = sph.userData && (sph.userData.radius || sph.userData.baseRadius) ? (sph.userData.radius || sph.userData.baseRadius) : 200;
  // prepare shared geometry/material to avoid per-asteroid allocations
  try {
    if (!_sharedAsteroidGeom) _sharedAsteroidGeom = new THREE.IcosahedronGeometry(1, 0);
    if (!_sharedAsteroidMat) _sharedAsteroidMat = new THREE.MeshStandardMaterial({ color: 0x6b4b34, roughness: 0.9, metalness: 0.0 });
  } catch (e) { _sharedAsteroidGeom = null; _sharedAsteroidMat = null; }

  // Use InstancedMesh when available to reduce draw calls
  try {
    const instGeom = _sharedAsteroidGeom ? _sharedAsteroidGeom : new THREE.IcosahedronGeometry(1, 0);
    const instMat = _sharedAsteroidMat ? _sharedAsteroidMat : new THREE.MeshStandardMaterial({ color: 0x6b4b34, roughness: 0.9, metalness: 0.0 });
    _asteroidInstanced = new THREE.InstancedMesh(instGeom, instMat, count);
    _asteroidInstanced.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
    // per-instance data
    for (let i = 0; i < count; i++) {
      try {
        const r = baseRadius + 40 + Math.random() * 900;
        const phi = Math.random() * Math.PI * 2;
        const cost = (Math.random() * 2 - 1);
        const theta = Math.acos(cost);
        const pos = new THREE.Vector3(Math.sin(theta) * Math.cos(phi), Math.cos(theta), Math.sin(theta) * Math.sin(phi)).multiplyScalar(r).add(center);
        const size = 2 + Math.random() * 8;
        const mat4 = new THREE.Matrix4();
        const scale = new THREE.Vector3(size, size, size);
        mat4.compose(pos, new THREE.Quaternion(), scale);
        _asteroidInstanced.setMatrixAt(i, mat4);
        const spin = new THREE.Vector3((Math.random()-0.5)*0.02, (Math.random()-0.5)*0.02, (Math.random()-0.5)*0.02);
        asteroidInfos.push({ pos: pos.clone(), size, quat: new THREE.Quaternion(), spin });
      } catch (e) {}
    }
    try { scene.add(_asteroidInstanced); } catch (e) {}
  } catch (e) {
    // fallback to individual meshes
    for (let i = 0; i < count; i++) {
      try {
        const r = baseRadius + 40 + Math.random() * 900;
        const phi = Math.random() * Math.PI * 2;
        const cost = (Math.random() * 2 - 1);
        const theta = Math.acos(cost);
        const pos = new THREE.Vector3(Math.sin(theta) * Math.cos(phi), Math.cos(theta), Math.sin(theta) * Math.sin(phi)).multiplyScalar(r).add(center);
        const size = 2 + Math.random() * 8;
        const geo = _sharedAsteroidGeom ? _sharedAsteroidGeom : new THREE.IcosahedronGeometry(size, 0);
        const mat = _sharedAsteroidMat ? _sharedAsteroidMat : new THREE.MeshStandardMaterial({ color: 0x6b4b34, roughness: 0.9, metalness: 0.0 });
        const rock = new THREE.Mesh(geo, mat);
        rock.position.copy(pos);
        rock.scale.set(size, size, size);
        rock.userData.spin = new THREE.Vector3((Math.random()-0.5)*0.02, (Math.random()-0.5)*0.02, (Math.random()-0.5)*0.02);
        rock.userData._occluderIgnore = true;
        scene.add(rock);
        asteroids.push(rock);
      } catch (e) {}
    }
  }
}

// Powerup system: pooled health pickups
let powerupPool = [];
let powerups = [];
let powerupInfos = [];
let _powerupInstanced = null;
function createHealthPowerups(count) {
  // remove existing powerups/instanced
  try { for (let p of powerups) scene.remove(p); } catch (e) {}
  powerups = [];
  powerupInfos = [];
  try { if (_powerupInstanced) { scene.remove(_powerupInstanced); _powerupInstanced = null; } } catch (e) {}
  // prepare shared geom/material
  try {
    if (!_sharedPowerupGeom) _sharedPowerupGeom = new THREE.SphereGeometry(1.2, 8, 6);
    if (!_sharedPowerupMat) _sharedPowerupMat = new THREE.MeshBasicMaterial({ color: 0x33ff66, transparent: true, opacity: 0.95 });
  } catch (e) { _sharedPowerupGeom = null; _sharedPowerupMat = null; }
  if (!levelCube) return;
  const center = levelCube.position.clone();
  const sph = (levelCube.userData && levelCube.userData.enclosingSphere) ? levelCube.userData.enclosingSphere : null;
  const baseRadius = sph ? (sph.userData.radius || sph.userData.baseRadius) : 200;
  // Try to use InstancedMesh
  try {
    const g = _sharedPowerupGeom ? _sharedPowerupGeom : new THREE.SphereGeometry(1.2, 8, 6);
    const m = _sharedPowerupMat ? _sharedPowerupMat : new THREE.MeshBasicMaterial({ color: 0x33ff66, transparent: true, opacity: 0.95 });
    _powerupInstanced = new THREE.InstancedMesh(g, m, count);
    _powerupInstanced.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
    const mat4 = new THREE.Matrix4();
    for (let i = 0; i < count; i++) {
      try {
        const dir = new THREE.Vector3((Math.random()-0.5), (Math.random()-0.5), (Math.random()-0.5)).normalize();
        const dist = baseRadius + 30 + Math.random() * 800;
        const pos = center.clone().add(dir.multiplyScalar(dist));
        const scale = new THREE.Vector3(1.8,1.8,1.8);
        mat4.compose(pos, new THREE.Quaternion(), scale);
        _powerupInstanced.setMatrixAt(i, mat4);
        powerupInfos.push({ pos: pos.clone(), heal: 10, radius: 3, bobPhase: Math.random() * Math.PI * 2, alive: true });
      } catch (e) {}
    }
    scene.add(_powerupInstanced);
    return;
  } catch (e) {
    // fallback to individual meshes
  }
  for (let i = 0; i < count; i++) {
    try {
      const g = _sharedPowerupGeom ? _sharedPowerupGeom : new THREE.SphereGeometry(1.2, 8, 6);
      const m = _sharedPowerupMat ? _sharedPowerupMat : new THREE.MeshBasicMaterial({ color: 0x33ff66, transparent: true, opacity: 0.95 });
      const mesh = new THREE.Mesh(g, m);
      const dir = new THREE.Vector3((Math.random()-0.5), (Math.random()-0.5), (Math.random()-0.5)).normalize();
      const dist = baseRadius + 30 + Math.random() * 800;
      mesh.position.copy(center).add(dir.multiplyScalar(dist));
      mesh.userData = { heal: 10, radius: 3 };
      scene.add(mesh);
      powerups.push(mesh);
    } catch (e) {}
  }
}

function updatePowerups(dt) {
  try {
    if (_powerupInstanced && powerupInfos && powerupInfos.length > 0) {
      const m = new THREE.Matrix4();
      const q = new THREE.Quaternion();
      const s = new THREE.Vector3();
      const tempPos = new THREE.Vector3();
      const time = Date.now() * 0.001;
      for (let i = 0; i < powerupInfos.length; i++) {
        try {
          const info = powerupInfos[i];
          if (!info) continue;
          if (!info.alive) continue;
          // bobbing
          tempPos.copy(info.pos);
          tempPos.y += Math.sin(time + (info.bobPhase || 0)) * 0.5;
          s.set(1.8, 1.8, 1.8);
          m.compose(tempPos, q, s);
          _powerupInstanced.setMatrixAt(i, m);
        } catch (e) {}
      }
      _powerupInstanced.instanceMatrix.needsUpdate = true;
      return;
    }
    for (let i = powerups.length - 1; i >= 0; i--) {
      const p = powerups[i];
      // simple bob and rotate for visibility
      p.rotation.y += 0.01 * dt * 0.06;
      p.position.y += Math.sin(Date.now() * 0.001 + i) * 0.0002 * dt;
    }
  } catch (e) {}
}

// rotate asteroids for visual motion
function updateAsteroids(dt) {
  try {
    if (_asteroidInstanced && asteroidInfos.length > 0) {
      const m = new THREE.Matrix4();
      for (let i = 0; i < asteroidInfos.length; i++) {
        try {
          const info = asteroidInfos[i];
          // update rotation stored in quaternion
          const angX = info.spin.x * dt * 0.06;
          const angY = info.spin.y * dt * 0.06;
          const angZ = info.spin.z * dt * 0.06;
          const qx = new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(1,0,0), angX);
          const qy = new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(0,1,0), angY);
          const qz = new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(0,0,1), angZ);
          info.quat.multiply(qx).multiply(qy).multiply(qz);
          const scale = new THREE.Vector3(info.size, info.size, info.size);
          m.compose(info.pos, info.quat, scale);
          _asteroidInstanced.setMatrixAt(i, m);
        } catch (e) {}
      }
      _asteroidInstanced.instanceMatrix.needsUpdate = true;
      return;
    }
  } catch (e) {}
  for (let a of asteroids) {
    try { a.rotation.x += a.userData.spin.x * dt * 0.06; a.rotation.y += a.userData.spin.y * dt * 0.06; a.rotation.z += a.userData.spin.z * dt * 0.06; } catch (e) {}
  }
}

// Create a gold pyramid level with white grid and beam attack
function createLevelPyramid() {
  // build procedural base + grid textures using the project's existing palette
  const size = 1024;
  const base = document.createElement('canvas'); base.width = size; base.height = size; const g = base.getContext('2d');
  // gold base with white grid so pyramid faces are gold and edges read white
  g.fillStyle = '#ffd700'; g.fillRect(0,0,size,size);
  const grid = document.createElement('canvas'); grid.width = size; grid.height = size; const g2 = grid.getContext('2d');
  g2.clearRect(0,0,size,size);
  // white grid lines for visible edges
  g2.strokeStyle = '#ffffff'; g2.lineWidth = 4; const step = 64;
  for (let x = 0; x < size; x += step) { g2.beginPath(); g2.moveTo(x,0); g2.lineTo(x,size); g2.stroke(); }
  for (let y = 0; y < size; y += step) { g2.beginPath(); g2.moveTo(0,y); g2.lineTo(size,y); g2.stroke(); }
  const baseTex = new THREE.CanvasTexture(base); baseTex.needsUpdate = true;
  const gridTex = new THREE.CanvasTexture(grid); gridTex.needsUpdate = true; gridTex.wrapS = gridTex.wrapT = THREE.RepeatWrapping; gridTex.repeat.set(6,6);

  const radius = 200;
  const height = 300;
  const geo = new THREE.ConeGeometry(radius, height, 4, 1); // 4-sided pyramid
  // compute exact local corner positions and normals from geometry
  // so beams can originate from the mesh surface and follow mesh rotation
  const cornersLocal = [];
  try {
    const posAttr = geo.attributes && geo.attributes.position;
    const normAttr = geo.attributes && geo.attributes.normal;
    if (posAttr) {
      const pts = [];
      const norms = [];
      for (let i = 0; i < posAttr.count; i++) {
        pts.push(new THREE.Vector3(posAttr.getX(i), posAttr.getY(i), posAttr.getZ(i)));
        if (normAttr) norms.push(new THREE.Vector3(normAttr.getX(i), normAttr.getY(i), normAttr.getZ(i)));
        else norms.push(new THREE.Vector3(0,1,0));
      }
      // find apex index
      let apexIdx = 0;
      for (let i = 1; i < pts.length; i++) if (pts[i].y > pts[apexIdx].y) apexIdx = i;
      cornersLocal.push({ pos: pts[apexIdx].clone(), normal: norms[apexIdx].clone() });
      // find base vertices (y near minY)
      let minY = pts[0].y;
      for (let i = 1; i < pts.length; i++) if (pts[i].y < minY) minY = pts[i].y;
      const baseIdxs = [];
      for (let i = 0; i < pts.length; i++) if (Math.abs(pts[i].y - minY) < 1e-3) baseIdxs.push(i);
      // dedupe base positions by rounded x/z and average normals for each unique base corner
      const map = {};
      for (const idx of baseIdxs) {
        const p = pts[idx];
        const n = norms[idx];
        const key = `${Math.round(p.x*100)}/${Math.round(p.z*100)}`;
        if (!map[key]) map[key] = { pos: new THREE.Vector3(0,0,0), normal: new THREE.Vector3(0,0,0), count: 0 };
        map[key].pos.add(p);
        map[key].normal.add(n);
        map[key].count++;
      }
      for (const k in map) {
        const e = map[k];
        e.pos.multiplyScalar(1 / e.count);
        e.normal.multiplyScalar(1 / e.count).normalize();
        cornersLocal.push({ pos: e.pos.clone(), normal: e.normal.clone() });
      }
    }
  } catch (e) { }
  // Use a white wireframe look for the pyramid to reduce shader cost and match the requested style
  const mat = new THREE.MeshBasicMaterial({ color: 0xffffff, wireframe: true, side: THREE.DoubleSide });
  const pyr = new THREE.Mesh(geo, mat);
  // store per-corner local positions and normals for beam alignment
  if (cornersLocal.length) pyr.userData.cornersLocal = cornersLocal;
  // add white edge lines to make faces read as in the concept sketch
  try {
    const edges = new THREE.EdgesGeometry(geo);
    const line = new THREE.LineSegments(edges, new THREE.LineBasicMaterial({ color: 0xffffff, linewidth: 2 }));
    line.renderOrder = 999;
    pyr.add(line);
  } catch (e) {}
  const start = window.playerShip ? window.playerShip.position.clone() : new THREE.Vector3(0,0,0);
  const forward = new THREE.Vector3(0,0,-1).applyEuler((window.playerShip && window.playerShip.rotation) ? window.playerShip.rotation : new THREE.Euler());
  pyr.position.copy(start).add(forward.multiplyScalar(1200));
  // store parameters for beam origins
  pyr.userData.radius = radius;
  pyr.userData.height = height;
  pyr.userData.hp = 200;
  pyr.userData.size = Math.max(radius, height) * 2;
  pyr.userData._emissiveBase = 0.4;
  pyr.userData._emissiveAmp = 0.9;
  pyr.userData.hitRadius = Math.max(radius, height) * 0.6;
  // assign type so update loop runs pyramid attacks
  pyr.userData.type = 'pyramid';
  // rotate slowly to make beam matching easier (one full rotation every 20s)
  pyr.userData.rotateSpeed = (2 * Math.PI) / 20.0; // radians per second
  // beam cooldown (how often beams fire)
  pyr.userData.burstCooldown = 10000; // 10s
  pyr.userData.burstLastAt = 0;
  scene.add(pyr);
  levelCube = pyr;
  // start random-beam timer for pyramid (spawn beams every 3s)
  pyr.userData.randomBeamLastAt = Date.now();
  pyr.userData.randomBeamInterval = 3000;
  // create persistent beams immediately for constant beams
  try { createPersistentPyramidBeams(); levelCube.userData.beamsPersistentCreated = true; } catch (e) {}
  try { levelCube.userData.box = new THREE.Box3().setFromObject(levelCube); } catch (e) { levelCube.userData.box = null; }
  createLevelHealthUI();
  placeLevelMarker(pyr);
  createLevelMarkerHUD();
  try { updateLevelMarkerHUD(); } catch (e) {}
  // spawn more ships for pyramid (harder final level)
  try { spawnInitialShips(50); } catch (e) { console.warn('initial spawn failed', e); }
  try { spawnBlockingShips(40); } catch (e) { console.warn('blocking spawn failed', e); }
  // double ships for tougher pyramid level
  try { spawnInitialShips(100); } catch (e) { console.warn('initial spawn failed', e); }
  try { spawnBlockingShips(80); } catch (e) { console.warn('blocking spawn failed', e); }
}

// Level indicator helpers
function updateLevelIndicator() {
  try {
    let idx = (typeof window.levelIndex === 'number') ? window.levelIndex : 1;
    const el = document.getElementById('level-indicator');
    if (!el) return;
    let label = 'Level 1: Cube';
    if (idx === 1) label = 'Level 1: Cube';
    else if (idx === 2) label = 'Level 2: Sphere';
    else if (idx === 3) label = 'Level 3: Pyramid';
    else if (idx === 4) label = 'Level 4: Cube in Sphere';
    el.innerText = label;
  } catch (e) {}
}

// Start the next level: clear current enemies/missiles and spawn sphere level
function startNextLevel() {
  // clear waiting flag when starting
  try { window.waitingForNextLevel = false; } catch (e) {}
  // remove overlay/button if present
  try { const over = document.getElementById('levelpassed'); if (over) over.remove(); } catch (e) {}
  try { const btn = document.getElementById('next-level-btn'); if (btn) btn.remove(); } catch (e) {}
  // Remove any leftover level-complete UI so the new level UI is clean
  try { const over = document.getElementById('levelpassed'); if (over) over.remove(); } catch (e) {}
  try { const btn = document.getElementById('next-level-btn'); if (btn) btn.remove(); } catch (e) {}
  // clear existing enemy lasers
  try {
    enemyLasers.forEach(l => { try { releaseEnemyLaser(l); } catch (e) {} });
    enemyLasers = [];
  } catch (e) {}
  // clear player lasers
  try { lasers.forEach(l => { try { releasePlayerLaser(l); } catch (e) {} }); lasers = []; } catch (e) {}
  // clear cube missiles
  try { cubeMissiles.forEach(m => { try { releaseMissile(m); } catch (e) {} }); cubeMissiles = []; } catch (e) {}
  // remove enemies and their health bars
  try {
    enemies.forEach(en => { try { removeEnemyHealthBar(en); scene.remove(en); } catch (e) {} });
    enemies = [];
  } catch (e) {}
  // increase player laser damage for the next level
  PLAYER_LASER_DAMAGE += 2;
  // reset player health to full at new level
  try { playerHealth = PLAYER_MAX_HEALTH; updatePlayerHealthBar(); } catch (e) {}
  gameOver = false;
  // reset timing and restart the animation loop
  lastTime = Date.now();
  // advance level index: 1 = cube, 2 = sphere, 3 = pyramid, 4 = cube-in-sphere
  window.levelIndex = (typeof window.levelIndex === 'number') ? (window.levelIndex + 1) : 1;
  if (window.levelIndex === 1) {
    createLevelCube();
  } else if (window.levelIndex === 2) {
    createLevelSphere();
  } else if (window.levelIndex === 3) {
    createLevelPyramid();
  } else if (window.levelIndex === 4) {
    createLevelCubeInSphere();
  } else {
    // wrap to cube (1)
    window.levelIndex = 1;
    createLevelCube();
  }
  try { updateLevelIndicator(); } catch (e) {}
  try { animate(); } catch (e) {}
}

// Create HUD elements for the level marker (screen-space)
function createLevelMarkerHUD() {
  // container
  let hud = document.getElementById('level-marker-hud');
  if (hud) hud.remove();
  hud = document.createElement('div');
  hud.id = 'level-marker-hud';
  hud.style.position = 'fixed';
  hud.style.left = '0';
  hud.style.top = '0';
  hud.style.width = '100%';
  hud.style.height = '100%';
  hud.style.pointerEvents = 'none';
  hud.style.zIndex = '300';

  const marker = document.createElement('div');
  marker.id = 'level-marker-hud-square';
  marker.style.position = 'absolute';
  marker.style.width = '48px';
  marker.style.height = '48px';
  marker.style.background = 'rgba(255,51,51,0.6)';
  marker.style.border = '1px solid rgba(255,255,255,0.9)';
  marker.style.borderRadius = '4px';
  marker.style.transform = 'translate(-50%, -50%)';
  marker.style.display = 'none';
  hud.appendChild(marker);
  // create level indicator (bottom-right)
  let lvl = document.getElementById('level-indicator');
  if (lvl) lvl.remove();
  lvl = document.createElement('div');
  lvl.id = 'level-indicator';
  lvl.style.position = 'fixed';
  lvl.style.right = '12px';
  lvl.style.bottom = '12px';
  lvl.style.padding = '6px 10px';
  lvl.style.background = 'rgba(0,0,0,0.5)';
  lvl.style.color = '#fff';
  lvl.style.zIndex = '400';
  lvl.style.borderRadius = '6px';
  lvl.style.fontFamily = 'sans-serif';
  lvl.style.fontSize = '14px';
  lvl.innerText = 'Level: ?';
  document.body.appendChild(lvl);

  const arrow = document.createElement('div');
  arrow.id = 'level-marker-hud-arrow';
  arrow.style.position = 'absolute';
  arrow.style.width = '0';
  arrow.style.height = '0';
  arrow.style.borderLeft = '14px solid transparent';
  arrow.style.borderRight = '14px solid transparent';
  arrow.style.borderTop = '22px solid #ff3333';
  arrow.style.transform = 'translate(-50%, -50%) rotate(0deg)';
  arrow.style.display = 'none';
  hud.appendChild(arrow);

  document.body.appendChild(hud);
  window._levelMarkerHUD = { hud, marker, arrow };
}

function updateLevelMarkerHUD() {
  if (!levelCube) return;
  if (!window._levelMarkerHUD) createLevelMarkerHUD();
  const { marker, arrow } = window._levelMarkerHUD;
  const world = new THREE.Vector3();
  // compute the world position for the marker in preferred order:
  // 1) recompute from stored local coords (accurate and follows rotation)
  // 2) live mesh world position
  // 3) cached world position fallback
  if (levelCube.userData && levelCube.userData.markerLocal) {
    try {
      const t = levelCube.userData && levelCube.userData.type;
      if (t === 'pyramid' || t === 'sphere' || t === 'cubeinsphere') {
        // for these level types the marker should NOT rotate with the mesh: use cube position + local offset
        world.copy(levelCube.position.clone().add(levelCube.userData.markerLocal.clone()));
      } else {
        world.copy(levelCube.localToWorld(levelCube.userData.markerLocal.clone()));
      }
    } catch (e) { /* ignore and try other fallbacks */ }
  }
  if (world.lengthSq() === 0) {
    if (levelCube.userData.markerMesh) {
      try { levelCube.userData.markerMesh.getWorldPosition(world); } catch (e) { world.copy(levelCube.userData.markerWorldPos || levelCube.position); }
    } else if (levelCube.userData && levelCube.userData.markerWorldPos) {
      world.copy(levelCube.userData.markerWorldPos);
    } else {
      return;
    }
  }
  const ndc = world.clone().project(camera);
  const w = window.innerWidth, h = window.innerHeight;
  const padding = 48;
  // Compute screen position and clamp to viewport so marker is always visible as HUD
  if (!isFinite(ndc.x) || !isFinite(ndc.y)) return;
  // convert NDC to screen coords
  let sx = (ndc.x + 1) / 2 * w;
  let sy = (-ndc.y + 1) / 2 * h;
  // clamp to inside viewport with padding
  sx = Math.max(padding, Math.min(w - padding, sx));
  sy = Math.max(padding, Math.min(h - padding, sy));
  marker.style.left = sx + 'px';
  marker.style.top = sy + 'px';
  marker.style.display = 'block';
  // hide the arrow entirely (HUD marker will indicate position)
  arrow.style.display = 'none';

  // Occlusion check: if marker world pos is behind the level cube from camera, tint blue
  try {
    let occluded = false;
    if (levelCube) {
      const camPos = camera.position.clone();
      let target = null;
      if (levelCube.userData && levelCube.userData.markerLocal) {
        try {
          const t = levelCube.userData.type;
          if (t === 'pyramid' || t === 'sphere' || t === 'cubeinsphere') target = levelCube.position.clone().add(levelCube.userData.markerLocal.clone());
          else target = levelCube.localToWorld(levelCube.userData.markerLocal.clone());
        } catch (e) { target = null; }
      } else if (levelCube.userData && levelCube.userData.markerWorldPos) {
        target = levelCube.userData.markerWorldPos.clone();
      }
      if (target) {
        // Skip occlusion testing for sphere/cube-in-sphere levels so the enclosing sphere
        // doesn't force the HUD marker blue (marker should remain hittable/visible).
        const levelType = (levelCube && levelCube.userData) ? levelCube.userData.type : null;
        if (levelType === 'sphere' || levelType === 'cubeinsphere') {
          // do not mark occluded for these level types
          occluded = false;
        } else {
          const dir = target.clone().sub(camPos);
          const dist = dir.length();
          if (dist > 1e-4) {
            dir.normalize();
            const ray = window._sharedRaycaster || new THREE.Raycaster();
            ray.set(camPos, dir);
            let hits = [];
            try {
              // Collect only larger geometry as occluders to avoid enemies/particles making the marker blue
              const occluders = [];
              scene.traverse(obj => {
                try {
                  // skip levelCube itself and any of its descendant children (avoid self-occlusion)
                  let p = obj;
                  let isDescendant = false;
                  while (p) { if (p === levelCube) { isDescendant = true; break; } p = p.parent; }
                  if (isDescendant) return;
                  if (obj.userData && obj.userData._occluderIgnore) return;
                  // require a geometry with a bounding sphere and sufficient size
                  if (obj.geometry && obj.geometry.boundingSphere) {
                    const bs = obj.geometry.boundingSphere;
                    const scale = Math.max(obj.scale.x||1, obj.scale.y||1, obj.scale.z||1);
                    const approxRadius = (bs.radius || 0) * scale;
                    if (approxRadius >= 8) occluders.push(obj);
                  }
                } catch (e) {}
              });
              if (occluders.length > 0) {
                hits = ray.intersectObjects(occluders, true);
              } else {
                hits = [];
              }
            } catch (e) {
              // fallback: no occluders
              hits = [];
            }
            if (hits && hits.length > 0 && hits[0].distance < dist - 1.0) {
              occluded = true;
            }
          }
        }
      }
    }
    // store occlusion state and respawn marker if occluded for a while
    try {
      if (levelCube && levelCube.userData) {
        if (occluded) {
          if (!levelCube.userData.markerOccludedSince) levelCube.userData.markerOccludedSince = Date.now();
          else if (Date.now() - levelCube.userData.markerOccludedSince > 1000) {
            // if marker has been occluded for >1s, pick a new visible marker
            try { placeLevelMarker(levelCube); } catch (e) {}
            levelCube.userData.markerOccludedSince = null;
            levelCube.userData.markerOccluded = false;
          }
        } else {
          levelCube.userData.markerOccludedSince = null;
        }
        levelCube.userData.markerOccluded = occluded;
      }
    } catch (e) {}
    // size marker based on distance: closer -> larger
    try {
      let markerWorld = null;
      if (levelCube && levelCube.userData && levelCube.userData.markerLocal) {
        try {
          const t = levelCube.userData.type;
          if (t === 'pyramid' || t === 'sphere' || t === 'cubeinsphere') markerWorld = levelCube.position.clone().add(levelCube.userData.markerLocal.clone());
          else markerWorld = levelCube.localToWorld(levelCube.userData.markerLocal.clone());
        } catch (e) { markerWorld = null; }
      } else if (levelCube && levelCube.userData && levelCube.userData.markerWorldPos) {
        markerWorld = levelCube.userData.markerWorldPos.clone();
      }
      if (markerWorld) {
        const dist = camera.position.distanceTo(markerWorld);
        // map distance -> size (px): near 0 -> 72px, far ~1200 -> 24px
        let size = Math.round(Math.max(24, Math.min(72, 72 - dist * 0.04)));
        marker.style.width = size + 'px';
        marker.style.height = size + 'px';
      }
    } catch (e) {}
    marker.style.background = occluded ? 'rgba(60,90,255,0.75)' : 'rgba(255,51,51,0.6)';
    marker.style.border = occluded ? '1px solid rgba(200,220,255,0.95)' : '1px solid rgba(255,255,255,0.9)';
  } catch (e) {}
}

// Update reticule color when aiming at a damageable target (enemy or level marker)
function updateReticule() {
  const el = document.getElementById('reticule');
  if (!el || !camera) return;
  const lines = el.querySelectorAll('line');
  const r = window._sharedRaycaster || new THREE.Raycaster();
  const v2 = window._sharedMouseVec2 || new THREE.Vector2(0,0);
  r.setFromCamera(v2, camera);
  const ray = r.ray;
  let hit = false;

  // quick check against enemies using distance from ray to enemy position
  for (let i = 0; i < enemies.length; i++) {
    const enemy = enemies[i];
    if (!enemy) continue;
    const toEnemy = enemy.position.clone().sub(ray.origin);
    const t = ray.direction.dot(toEnemy);
    if (t <= 0) continue;
    const closest = ray.origin.clone().add(ray.direction.clone().multiplyScalar(t));
    const dist = closest.distanceTo(enemy.position);
    const hr = (enemy.userData && enemy.userData.hitRadius) ? enemy.userData.hitRadius : 1.2;
    if (dist < hr) { hit = true; break; }
  }

  // check marker if not already hitting an enemy
  if (!hit && levelCube) {
    try {
      let markerWorld = null;
      if (levelCube.userData && levelCube.userData.markerLocal) {
        try { markerWorld = levelCube.localToWorld(levelCube.userData.markerLocal.clone()); } catch (e) { markerWorld = null; }
      }
      if (!markerWorld && levelCube.userData && levelCube.userData.markerWorldPos) markerWorld = levelCube.userData.markerWorldPos.clone();
      if (markerWorld) {
        const markerRadius = levelCube.userData.markerHitRadius || Math.max(8, (levelCube.userData.size || 400) * 0.04);
        const toMarker = markerWorld.clone().sub(ray.origin);
        const t2 = Math.max(0, ray.direction.dot(toMarker));
        const closest2 = ray.origin.clone().add(ray.direction.clone().multiplyScalar(t2));
        const d2 = closest2.distanceTo(markerWorld);
        if (d2 < markerRadius * 1.4 && !(levelCube.userData && levelCube.userData.markerOccluded)) hit = true;
      }
    } catch (e) {}
  }

  const color = hit ? '#00ff00' : '#ffffff';
  lines.forEach(l => l.setAttribute('stroke', color));
}

function placeLevelMarker(cube) {
  if (!cube) return;
  // remove previous marker data (HUD-only marker: no world meshes)
  try { cube.userData.markerMesh = null; } catch (e) {}
  try { cube.userData.markerGlow = null; } catch (e) {}
  try { cube.userData.markerHitProxy = null; } catch (e) {}
  const size = cube.userData.size || 400;
  const margin = Math.floor(size * 0.08);
  // Special-case sphere: place marker on visible hemisphere (randomized so it can move)
  try {
    if (cube.userData && cube.userData.type === 'sphere') {
      const radius = (cube.userData.size ? cube.userData.size * 0.5 : 200);
      const camDir = camera.position.clone().sub(cube.position).normalize();
      const maxAngleDeg = 70;
      const cosThresh = Math.cos((maxAngleDeg * Math.PI) / 180);
      let chosenWorld = null;
      const tries = 24;
      for (let t = 0; t < tries; t++) {
        // sample a random direction on unit sphere biased toward camera-facing hemisphere
        // rejection-sample until dot(camDir, v) >= cosThresh
        let v = new THREE.Vector3();
        for (let k = 0; k < 6; k++) {
          const z = (Math.random() * 2 - 1);
          const phi = Math.random() * Math.PI * 2;
          const r = Math.sqrt(Math.max(0, 1 - z * z));
          v.set(r * Math.cos(phi), r * Math.sin(phi), z).normalize();
          if (v.dot(camDir) >= cosThresh) break;
        }
        const worldPos = cube.position.clone().add(v.multiplyScalar(radius + 2));
        // occlusion check
        let occluded = false;
        try {
          const rc = window._sharedRaycaster || new THREE.Raycaster();
          const origin = camera.position.clone();
          const dir = worldPos.clone().sub(origin).normalize();
          const dist = origin.distanceTo(worldPos);
          rc.set(origin, dir);
          // build occluder list but exclude the enclosing sphere for cube-in-sphere levels
          let occluders = [];
          try {
            scene.traverse(o => {
              try {
                // skip the cube itself and its descendants to avoid self-occlusion
                let p = o;
                let isDescendant = false;
                while (p) { if (p === cube) { isDescendant = true; break; } p = p.parent; }
                if (isDescendant) return;
                // skip the enclosing sphere (if present) to allow visibility through it
                if (cube.userData && cube.userData.enclosingSphere && o === cube.userData.enclosingSphere) return;
                occluders.push(o);
              } catch (e) {}
            });
          } catch (e) { occluders = scene.children.slice(); }
          const hits = rc.intersectObjects(occluders, true);
          if (hits && hits.length) {
            const h = hits[0];
            let hitObj = h.object;
            let belongsToCube = false;
            while (hitObj) { if (hitObj === cube) { belongsToCube = true; break; } hitObj = hitObj.parent; }
            if (belongsToCube) {
              if (h.point.distanceTo(worldPos) > 4) occluded = true;
            } else {
              if (h.distance < dist - 0.5) occluded = true;
            }
          }
        } catch (e) { occluded = false; }
        const ndc = worldPos.clone().project(camera);
        const onScreen = isFinite(ndc.x) && isFinite(ndc.y) && isFinite(ndc.z) && ndc.z >= -1 && ndc.z <= 1 && ndc.x >= -1 && ndc.x <= 1 && ndc.y >= -1 && ndc.y <= 1;
        if (!occluded && onScreen) { chosenWorld = worldPos.clone(); break; }
      }
      if (!chosenWorld) {
        // fallback to camera-aligned point
        const dir = camDir;
        chosenWorld = cube.position.clone().add(dir.multiplyScalar(radius + 2));
      }
      try { cube.userData.markerWorldPos = chosenWorld.clone(); } catch (e) {}
      try { cube.userData.markerLocal = cube.worldToLocal(chosenWorld.clone()); } catch (e) { try { cube.userData.markerLocal = chosenWorld.clone().sub(cube.position); } catch (e) {} }
      cube.userData.markerHits = 0;
      const markerSize = Math.max(36, Math.floor(size * 0.12));
      try { cube.userData.markerHitRadius = Math.max(8, Math.floor(markerSize * 0.5)); } catch (e) {}
      try { cube.userData.markerOccluded = false; } catch (e) {}
      return;
    }
  } catch (e) {}
  // Prefer cube face facing camera when possible (deterministic for box); otherwise sample
  let chosenLocal = null;
  let chosenWorld = null;
  const tmpLocal = new THREE.Vector3();
  const tmpWorld = new THREE.Vector3();
  const camDir = new THREE.Vector3();
  try {
    const isBox = (cube.geometry && cube.geometry.type && cube.geometry.type.toLowerCase().includes('box')) || (!!cube.userData && !!cube.userData.size && !cube.userData.type);
    if (isBox) {
      // pick the axis with largest camera-local component
      const camLocal = cube.worldToLocal(camera.position.clone());
      const ax = Math.abs(camLocal.x), ay = Math.abs(camLocal.y), az = Math.abs(camLocal.z);
      const half = size / 2;
      const u = (Math.random() * (size - 2 * margin)) - (size / 2 - margin);
      const v = (Math.random() * (size - 2 * margin)) - (size / 2 - margin);
      if (ax >= ay && ax >= az) {
        if (camLocal.x > 0) tmpLocal.set(half, v, u); else tmpLocal.set(-half, v, u);
      } else if (ay >= ax && ay >= az) {
        if (camLocal.y > 0) tmpLocal.set(u, half, v); else tmpLocal.set(u, -half, v);
      } else {
        if (camLocal.z > 0) tmpLocal.set(u, v, half); else tmpLocal.set(u, v, -half);
      }
      const normal = tmpLocal.clone().normalize();
      const localPos = tmpLocal.clone().add(normal.clone().multiplyScalar(2));
      try { tmpWorld.copy(cube.localToWorld(localPos.clone())); } catch (e) { tmpWorld.copy(localPos).add(cube.position); }
      chosenLocal = localPos.clone();
      chosenWorld = tmpWorld.clone();
    }
  } catch (e) {}
  if (!chosenLocal) {
    const tries = 40; // increase tries for better chance of front-facing sample
    for (let t = 0; t < tries; t++) {
      const face = Math.floor(Math.random() * 6); // 0..5
      const half = size / 2;
      const u = (Math.random() * (size - 2 * margin)) - (size / 2 - margin);
      const v = (Math.random() * (size - 2 * margin)) - (size / 2 - margin);
      switch (face) {
        case 0: tmpLocal.set(half, v, u); break; // +X
        case 1: tmpLocal.set(-half, v, u); break; // -X
        case 2: tmpLocal.set(u, half, v); break; // +Y
        case 3: tmpLocal.set(u, -half, v); break; // -Y
        case 4: tmpLocal.set(u, v, half); break; // +Z
        default: tmpLocal.set(u, v, -half); break; // -Z
      }
      const normal = tmpLocal.clone().normalize();
      const localPos = tmpLocal.clone().add(normal.clone().multiplyScalar(2));
      if (cube.userData && cube.userData.type === 'pyramid') {
        tmpWorld.copy(cube.position).add(localPos);
      } else {
        try { tmpWorld.copy(cube.localToWorld(localPos.clone())); } catch (e) { tmpWorld.copy(localPos).add(cube.position); }
      }
      camDir.copy(camera.position).sub(tmpWorld).normalize();
      const normalWorld = normal.clone().applyQuaternion(cube.quaternion || new THREE.Quaternion()).normalize();
      const facing = normalWorld.dot(camDir);
      const ndc = tmpWorld.clone().project(camera);
      const onScreen = isFinite(ndc.x) && isFinite(ndc.y) && isFinite(ndc.z) && ndc.z >= -1 && ndc.z <= 1 && ndc.x >= -1 && ndc.x <= 1 && ndc.y >= -1 && ndc.y <= 1;
      // perform an occlusion raycast: accept candidate only if not blocked
      let occluded = false;
      try {
        const rc = window._sharedRaycaster || new THREE.Raycaster();
        const origin = camera.position.clone();
        const dir = tmpWorld.clone().sub(origin).normalize();
        const dist = origin.distanceTo(tmpWorld);
        rc.set(origin, dir);
        // Raycast excluding the enclosing sphere (so the sphere doesn't self-occlude marker candidates)
        let hits = [];
        try {
          const occluders = [];
          scene.traverse(o => {
            try {
              if (cube.userData && cube.userData.enclosingSphere && o === cube.userData.enclosingSphere) return;
              occluders.push(o);
            } catch (e) {}
          });
          hits = rc.intersectObjects(occluders, true);
        } catch (e) { hits = rc.intersectObjects(scene.children, true); }
        if (hits && hits.length) {
          const h = hits[0];
          let hitObj = h.object;
          let belongsToCube = false;
          while (hitObj) { if (hitObj === cube) { belongsToCube = true; break; } hitObj = hitObj.parent; }
          if (belongsToCube) {
            if (h.point.distanceTo(tmpWorld) > 4) occluded = true;
          } else {
            if (h.distance < dist - 0.5) occluded = true;
          }
        }
      } catch (e) { occluded = false; }
      if (facing > 0.6 && onScreen && !occluded) {
        chosenLocal = localPos.clone();
        chosenWorld = tmpWorld.clone();
        break;
      }
      if (t === tries - 1) {
        chosenLocal = localPos.clone();
        chosenWorld = tmpWorld.clone();
      }
    }
  }
  if (!chosenLocal) return;
  try {
    if (cube.userData && cube.userData.type === 'pyramid') {
      cube.userData.markerLocal = chosenWorld.clone().sub(cube.position);
      cube.userData.markerWorldPos = chosenWorld.clone();
    } else {
      cube.userData.markerLocal = chosenLocal.clone();
      cube.userData.markerWorldPos = chosenWorld.clone();
    }
    // Ensure marker is not initially marked occluded; HUD will update each frame
    try { cube.userData.markerOccluded = false; } catch (e) {}
  } catch (e) {}
  // marker size relative (larger so it's visible at distance)
  const markerSize = Math.max(36, Math.floor(size * 0.12));
  cube.userData.markerHits = 0;
  // determine hit radius for marker (used by lasers/reticule)
  const markerRadius = Math.max(8, Math.floor(markerSize * 0.5));
  try { cube.userData.markerHitRadius = markerRadius; } catch (e) {}
}

function createLevelHealthUI() {
  if (window.levelHealthEl) { window.levelHealthEl.remove(); }
  const el = document.createElement('div');
  el.id = 'level-health';
  el.style.position = 'fixed';
  el.style.right = '18px';
  el.style.top = '52px';
  el.style.color = '#0f0';
  el.style.background = 'rgba(0,0,0,0.25)';
  el.style.padding = '6px 10px';
  el.style.borderRadius = '6px';
  el.style.fontFamily = 'sans-serif';
  el.style.fontSize = '14px';
  el.style.zIndex = '200';
  el.innerText = `Objective HP: ${levelCube ? levelCube.userData.hp : 0}`;
  document.body.appendChild(el);
  window.levelHealthEl = el;
}

// Create a persistent danger HUD that shows distance to the level cube
function createDangerUI() {
  if (window.cubeDangerEl) { window.cubeDangerEl.remove(); }
  const el = document.createElement('div');
  el.id = 'cube-danger';
  el.style.position = 'fixed';
  el.style.left = '50%';
  el.style.bottom = '18px';
  el.style.transform = 'translateX(-50%)';
  el.style.padding = '10px 14px';
  el.style.borderRadius = '8px';
  el.style.fontFamily = 'sans-serif';
  el.style.fontSize = '16px';
  el.style.zIndex = '400';
  el.style.pointerEvents = 'none';
  el.style.display = 'none';
  el.style.color = '#ffdddd';
  el.style.background = 'rgba(128,0,0,0.75)';
  el.style.border = '1px solid rgba(255,100,100,0.9)';
  el.innerText = '';
  document.body.appendChild(el);
  window.cubeDangerEl = el;
}

// Boost UI: shows readiness, active time remaining, or cooldown
function createBoostUI() {
  if (window.boostEl) { window.boostEl.remove(); }
  const el = document.createElement('div');
  el.id = 'boost-ui';
  el.style.position = 'fixed';
  el.style.left = '18px';
  el.style.bottom = '18px';
  el.style.padding = '8px 12px';
  el.style.borderRadius = '8px';
  el.style.fontFamily = 'sans-serif';
  el.style.fontSize = '14px';
  el.style.zIndex = '400';
  el.style.pointerEvents = 'none';
  el.style.color = '#fff';
  el.style.background = 'rgba(0,0,0,0.4)';
  el.innerText = 'BOOST: READY';
  document.body.appendChild(el);
  window.boostEl = el;
}

// Create on-screen touch controls (joystick + fire + boost)
function createTouchUI() {
  try {
    // Use document-level touch handlers so user can start dragging anywhere (no static joystick graphic)
    let activeId = null;
    let baseX = 0, baseY = 0, maxR = TOUCH_MAX_R;
    let movementActive = false;
    const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

    const onTouchStart = (ev) => {
      for (let i = 0; i < ev.changedTouches.length; i++) {
        const t = ev.changedTouches[i];
        // ignore touches that started on buttons (they handle themselves)
        try { if (t.target && t.target.closest && t.target.closest('.touch-button')) continue; } catch (e) {}
        ev.preventDefault();
        activeId = t.identifier;
        baseX = t.clientX; baseY = t.clientY;
        movementActive = true;
        break;
      }
    };
    const onTouchMove = (ev) => {
      if (!movementActive) return;
      ev.preventDefault();
      for (let i = 0; i < ev.changedTouches.length; i++) {
        const t = ev.changedTouches[i];
        if (t.identifier !== activeId) continue;
        const dx = t.clientX - baseX;
        const dy = t.clientY - baseY;
        const len = Math.sqrt(dx*dx + dy*dy);
        if (len < TOUCH_DEADZONE) {
          touchInput.right = 0; touchInput.forward = 0;
        } else {
          const r = Math.min(len, maxR);
          const nx = (len > 0) ? (dx / len) * (r / maxR) : 0;
          const ny = (len > 0) ? (dy / len) * (r / maxR) : 0;
          touchInput.right = clamp(nx, -1, 1);
          // keep sign so dragging up produces negative forward (matches keyboard 'Up' -> rotateX(-...))
          touchInput.forward = clamp(ny, -1, 1);
        }
        break;
      }
    };
    const onTouchEnd = (ev) => {
      for (let i = 0; i < ev.changedTouches.length; i++) {
        const t = ev.changedTouches[i];
        if (t.identifier === activeId) {
          activeId = null; movementActive = false; touchInput.right = 0; touchInput.forward = 0;
        }
      }
    };
    document.addEventListener('touchstart', onTouchStart, { passive: false });
    document.addEventListener('touchmove', onTouchMove, { passive: false });
    document.addEventListener('touchend', onTouchEnd, { passive: false });
    document.addEventListener('touchcancel', onTouchEnd, { passive: false });

    // Fire button
    const fire = document.createElement('div');
    fire.className = 'touch-button fire';
    fire.id = 'touch-fire';
    fire.innerText = 'FIRE';
    fire.style.touchAction = 'none';
    document.body.appendChild(fire);

    fire.addEventListener('touchstart', (ev) => {
      ev.preventDefault();
      if (touchInput._fireInterval) return;
      touchInput.firing = true;
      try { shootLaser(); } catch (e) {}
      touchInput._fireInterval = setInterval(() => { try { shootLaser(); } catch (e) {} }, 160);
    }, { passive: false });
    const endFire = (ev) => { ev.preventDefault(); touchInput.firing = false; if (touchInput._fireInterval) { clearInterval(touchInput._fireInterval); touchInput._fireInterval = null; } };
    fire.addEventListener('touchend', endFire, { passive: false });
    fire.addEventListener('touchcancel', endFire, { passive: false });

    // Boost button
    const boostBtn = document.createElement('div');
    boostBtn.className = 'touch-button boost';
    boostBtn.id = 'touch-boost';
    boostBtn.innerText = 'BOOST';
    boostBtn.style.touchAction = 'none';
    document.body.appendChild(boostBtn);
    boostBtn.addEventListener('touchstart', (ev) => { ev.preventDefault(); try { startBoost(); } catch (e) {} }, { passive: false });

  } catch (e) { console.warn('createTouchUI failed', e); }
}

// Missile incoming warning UI
function createMissileWarningUI() {
  if (window.missileWarningEl) { window.missileWarningEl.remove(); }
  const el = document.createElement('div');
  el.id = 'missile-warning';
  el.style.position = 'fixed';
  el.style.left = '50%';
  el.style.top = '10px';
  el.style.transform = 'translateX(-50%)';
  el.style.padding = '10px 14px';
  el.style.borderRadius = '8px';
  el.style.fontFamily = 'sans-serif';
  el.style.fontSize = '16px';
  el.style.zIndex = '500';
  el.style.pointerEvents = 'none';
  el.style.color = '#fff';
  el.style.background = 'rgba(200,40,40,0.9)';
  el.style.border = '1px solid rgba(255,120,120,0.95)';
  el.style.display = 'none';
  el.innerText = 'WARNING: Incoming missile!';
  document.body.appendChild(el);
  window.missileWarningEl = el;
}

function showMissileWarning(show) {
  if (!window.missileWarningEl) createMissileWarningUI();
  try { window.missileWarningEl.style.display = show ? 'block' : 'none'; } catch (e) {}
}

function updateLevelHealthUI() {
  if (!window.levelHealthEl) createLevelHealthUI();
  window.levelHealthEl.innerText = `Objective HP: ${levelCube ? Math.max(0, levelCube.userData.hp) : 0}`;
}

// Start a speed boost if not on cooldown
function startBoost() {
  const now = Date.now();
  if (now < boost.cooldownUntil) return; // still cooling down
  boost.active = true;
  boost.endTime = now + boost.duration;
  boost.cooldownUntil = boost.endTime + boost.cooldown;
  try { playSound('boost'); } catch (e) {}
}

function levelPassed() {
  gameOver = true;
  // show instruction overlay; keep pointer locked so user can press fire
  window.waitingForNextLevel = true;
  // remove the level object from scene so it doesn't remain visible while waiting
  try {
    if (levelCube) {
      // remove marker mesh/glow if present
      try { if (levelCube.userData && levelCube.userData.markerMesh) { if (levelCube.userData.markerMesh.parent) levelCube.userData.markerMesh.parent.remove(levelCube.userData.markerMesh); levelCube.userData.markerMesh = null; } } catch (e) {}
      try { if (levelCube.userData && levelCube.userData.markerGlow) { if (levelCube.userData.markerGlow.parent) levelCube.userData.markerGlow.parent.remove(levelCube.userData.markerGlow); levelCube.userData.markerGlow = null; } } catch (e) {}
      try { if (levelCube.userData && levelCube.userData.markerHitProxy) { if (levelCube.userData.markerHitProxy.parent) levelCube.userData.markerHitProxy.parent.remove(levelCube.userData.markerHitProxy); levelCube.userData.markerHitProxy = null; } } catch (e) {}
      try { scene.remove(levelCube); } catch (e) {}
      levelCube = null;
      // release any persistent pyramid beams
      try {
        for (let i = pyramidBeamsActive.length - 1; i >= 0; i--) {
          try { releasePyramidBeam(pyramidBeamsActive[i]); } catch (e) {}
          pyramidBeamsActive.splice(i, 1);
        }
      } catch (e) {}
      try { updateLevelHealthUI(); } catch (e) {}
    }
  } catch (e) {}
  const isFinal = (typeof window.levelIndex === 'number' && window.levelIndex === 4);
  if (isFinal) {
    const over = document.createElement('div');
    over.id = 'levelpassed';
    over.style.position = 'fixed';
    over.style.left = '50%';
    over.style.top = '50%';
    over.style.transform = 'translate(-50%, -50%)';
    over.style.color = '#fff';
    over.style.fontFamily = 'sans-serif';
    over.style.background = 'linear-gradient(180deg,#222,#444)';
    over.style.padding = '30px 40px';
    over.style.borderRadius = '12px';
    over.style.zIndex = '200';
    over.style.textAlign = 'center';
    const title = document.createElement('div');
    title.style.fontSize = '2.2em';
    title.style.marginBottom = '8px';
    title.innerText = 'Congratulations.... for now.';
    const btn = document.createElement('button');
    btn.style.marginTop = '12px';
    btn.style.padding = '10px 16px';
    btn.style.borderRadius = '8px';
    btn.style.border = 'none';
    btn.style.cursor = 'pointer';
    btn.style.background = '#1e90ff';
    btn.style.color = '#fff';
    btn.innerText = 'Start Over';
    btn.addEventListener('click', () => {
      try { document.getElementById('levelpassed')?.remove(); } catch (e) {}
      try { restartGame(); } catch (e) {}
    });
    over.appendChild(title);
    over.appendChild(btn);
    document.body.appendChild(over);
  } else {
    const over = document.createElement('div');
    over.id = 'levelpassed';
    over.style.position = 'fixed';
    over.style.left = '50%';
    over.style.top = '50%';
    over.style.transform = 'translate(-50%, -50%)';
    over.style.color = '#000';
    over.style.fontFamily = 'sans-serif';
    over.style.background = '#aaff66';
    over.style.padding = '30px 40px';
    over.style.borderRadius = '12px';
    over.style.zIndex = '200';
    over.style.textAlign = 'center';
    const title = document.createElement('div');
    title.style.fontSize = '2.2em';
    title.innerText = 'LEVEL COMPLETE';
    const sub = document.createElement('div');
    sub.style.fontSize = '1em';
    sub.style.marginTop = '8px';
    sub.innerText = 'Press FIRE (left click or Space) to continue';
    over.appendChild(title);
    over.appendChild(sub);
    document.body.appendChild(over);
  }
}

function updateEnemyHealthBar(enemy) {
  if (!enemy.userData.healthFill) return;
  const percent = Math.max(0, enemy.userData.hp / 3);
  enemy.userData.healthFill.style.width = (percent * 100) + '%';
}

function removeEnemyHealthBar(enemy) {
  if (enemy.userData.healthBar) {
    document.body.removeChild(enemy.userData.healthBar);
    enemy.userData.healthBar = null;
    enemy.userData.healthFill = null;
  }
}

// Update screen positions for all enemy health bars
function updateEnemyHealthBars() {
  if (!camera) return;
  const now = Date.now();
  // throttle health bar updates (use higher refresh + GPU transforms)
  // 40ms -> ~25 FPS gives smoother motion while still reducing DOM work
  if (now - lastHealthBarUpdate < 40) return;
  lastHealthBarUpdate = now;
  for (let i = enemies.length - 1; i >= 0; i--) {
    const enemy = enemies[i];
    if (!enemy.userData || !enemy.userData.healthBar) continue;
    // Use world position (in case enemy is parented) and guard against invalid projections
    const worldPos = new THREE.Vector3();
    enemy.getWorldPosition(worldPos);
    if (!isFinite(worldPos.x) || !isFinite(worldPos.y) || !isFinite(worldPos.z)) {
      enemy.userData.healthBar.style.display = 'none';
      continue;
    }
    const pos = worldPos.clone().project(camera);
    // If projection produced invalid numbers, hide
    if (!isFinite(pos.x) || !isFinite(pos.y) || !isFinite(pos.z)) {
      enemy.userData.healthBar.style.display = 'none';
      // throttle rare warn logs to once per 5s per enemy
      const t = Date.now();
      if (!enemy.userData._lastWarn || (t - enemy.userData._lastWarn) > 5000) {
        enemy.userData._lastWarn = t;
        console.warn('Enemy projection invalid — hiding health bar', { idx: i, worldPos });
      }
      continue;
    }
    // If offscreen (behind camera or outside NDC), hide
    if (pos.z < -1 || pos.z > 1 || pos.x < -1 || pos.x > 1 || pos.y < -1 || pos.y > 1) {
      enemy.userData.healthBar.style.display = 'none';
      continue;
    }
    // Occlusion: hide health bar if the level cube blocks line-of-sight from camera to enemy
    if (levelCube && levelCube.userData && levelCube.userData.box) {
      try {
        const camPos = camera.position;
        const toEnemy = worldPos.clone().sub(camPos);
        const dir = toEnemy.clone().normalize();
        // use shared raycaster to test intersection with cached box
        const r = window._sharedRaycaster;
        r.set(camPos, dir);
        const ip = new THREE.Vector3();
        const hit = r.ray.intersectBox(levelCube.userData.box, ip);
        if (hit) {
          const distToHit = ip.distanceTo(camPos);
          const distToEnemy = worldPos.distanceTo(camPos);
          if (distToHit < distToEnemy - 0.1) {
            enemy.userData.healthBar.style.display = 'none';
            continue;
          }
        }
      } catch (e) {}
    }
    const x = (pos.x + 1) / 2 * window.innerWidth;
    const y = (-pos.y + 1) / 2 * window.innerHeight;
    // Guard against NaN/infinite screen coords
    if (!isFinite(x) || !isFinite(y)) {
      enemy.userData.healthBar.style.display = 'none';
      continue;
    }
    // Use transform to position (GPU compositing) to avoid layout/reflow stutter
    enemy.userData.healthBar.style.transform = `translate3d(${(x - 20)}px, ${(y - 10)}px, 0)`;
    enemy.userData.healthBar.style.display = 'block';
    // Update fill width
    updateEnemyHealthBar(enemy);
  }
}

// Player health bar HUD
function createPlayerHealthBar() {
  const bar = document.createElement('div');
  bar.id = 'player-health-bar';
  bar.style.position = 'fixed';
  bar.style.left = '20px';
  bar.style.top = '20px';
  bar.style.width = '200px';
  bar.style.height = '16px';
  bar.style.background = '#222';
  bar.style.border = '1px solid #fff';
  bar.style.borderRadius = '8px';
  bar.style.overflow = 'hidden';
  bar.style.zIndex = '50';
  const fill = document.createElement('div');
  fill.id = 'player-health-fill';
  fill.style.height = '100%';
  fill.style.width = ((playerHealth / PLAYER_MAX_HEALTH) * 100) + '%';
  fill.style.background = '#0f0';
  bar.appendChild(fill);
  document.body.appendChild(bar);
  window.playerHealthBar = { bar, fill };
}

function updatePlayerHealthBar() {
  if (!window.playerHealthBar) createPlayerHealthBar();
  const pct = Math.max(0, (playerHealth / PLAYER_MAX_HEALTH) * 100);
  window.playerHealthBar.fill.style.width = pct + '%';
}

// damage debug UI removed

// Show game over message

function showGameOver() {
  const over = document.createElement('div');
  over.id = 'gameover';
  over.style.position = 'fixed';
  over.style.left = '50%';
  over.style.top = '50%';
  over.style.transform = 'translate(-50%, -50%)';
  over.style.color = '#fff';
  over.style.fontSize = '3em';
  over.style.fontFamily = 'sans-serif';
  over.style.background = 'rgba(0,0,0,0.7)';
  over.style.padding = '40px 60px';
  over.style.borderRadius = '20px';
  over.style.zIndex = '100';
  over.innerHTML = '<div style="margin-bottom:16px">GAME OVER</div>';
  const btn = document.createElement('button');
  btn.innerText = 'Restart (R)';
  btn.style.fontSize = '16px';
  btn.style.padding = '10px 18px';
  btn.style.borderRadius = '8px';
  btn.style.cursor = 'pointer';
  btn.addEventListener('click', () => { try { document.body.removeChild(over); } catch (e) {} restartGame(); });
  over.appendChild(btn);
  document.body.appendChild(over);
}

// Remove redundant render calls
// Removed `renderer.render(scene, camera);` outside of functions

// Add a restart mechanism for game over
function restartGame() {
  // Reset game variables
  playerHealth = PLAYER_MAX_HEALTH;
  gameOver = false;
  enemySpawnTimer = 0;
  enemies.forEach(enemy => {
    // remove mesh
    scene.remove(enemy);
    // remove any associated health bar
    try { removeEnemyHealthBar(enemy); } catch (e) {}
  });
  enemies = [];
  lasers.forEach(laser => scene.remove(laser));
  lasers = [];
  enemyLasers.forEach(laser => scene.remove(laser));
  enemyLasers = [];
  // Remove lingering effects
  effects.forEach(ef => { try { scene.remove(ef.pts); ef.geom.dispose(); ef.mat.dispose(); } catch (e) {} });
  effects = [];
  killCount = 0;
  updateKillCounter();
  // Remove level passed / game over overlays if present
  const passed = document.getElementById('levelpassed');
  if (passed) document.body.removeChild(passed);
  const over = document.getElementById('gameover');
  if (over) document.body.removeChild(over);
  // Recreate/reset level cube and its UI
  try { 
    // release any pyramid beams still active
    try { for (let i = pyramidBeamsActive.length - 1; i >= 0; i--) { try { releasePyramidBeam(pyramidBeamsActive[i]); } catch (e) {} pyramidBeamsActive.splice(i,1); } } catch (e) {}
    // Reset progression to level one (cube)
    window.levelIndex = 1;
    createLevelCube(); 
    updateLevelHealthUI(); 
    try { updateLevelIndicator(); } catch (e) {}
  } catch (e) {}

  // Remove game over message
  const gameOverMessage = document.getElementById('gameover');
  if (gameOverMessage) {
    document.body.removeChild(gameOverMessage);
  }

  // Restart animation loop
  animate();
}

// Add event listener for restarting the game
window.addEventListener('keydown', (e) => {
  if (gameOver && e.key === 'r') {
    restartGame();
  }
});

// Toggle pause on Escape: show overlay and release pointer lock
window.addEventListener('keydown', (e) => {
  if (e.key === 'Escape') {
    paused = !paused;
    const overlay = document.getElementById('pause-overlay');
    if (paused) {
      try { document.exitPointerLock(); } catch (e) {}
      if (overlay) overlay.style.display = 'block';
    } else {
      if (overlay) overlay.style.display = 'none';
    }
  }
});

// Arrow keys: map to pitch/yaw input booleans
window.addEventListener('keydown', (e) => {
  if (e.key === 'ArrowUp') { input.w = true; }
  if (e.key === 'ArrowDown') { input.s = true; }
  if (e.key === 'ArrowLeft') { input.a = true; }
  if (e.key === 'ArrowRight') { input.d = true; }
});
window.addEventListener('keyup', (e) => {
  if (e.key === 'ArrowUp') { input.w = false; }
  if (e.key === 'ArrowDown') { input.s = false; }
  if (e.key === 'ArrowLeft') { input.a = false; }
  if (e.key === 'ArrowRight') { input.d = false; }
});

function showStartScreen() {
  // Create full-screen title/start overlay
  const overlay = document.createElement('div');
  overlay.id = 'start-overlay';
  overlay.style.position = 'fixed';
  overlay.style.left = '0';
  overlay.style.top = '0';
  overlay.style.width = '100%';
  overlay.style.height = '100%';
  overlay.style.display = 'flex';
  overlay.style.alignItems = 'center';
  overlay.style.justifyContent = 'center';
  overlay.style.flexDirection = 'column';
  overlay.style.background = 'linear-gradient(180deg, rgba(0,0,0,0.95) 0%, rgba(0,0,0,0.85) 100%)';
  overlay.style.zIndex = '1000';

  const title = document.createElement('div');
  title.innerText = 'Titanomachy';
  title.style.color = '#ffffff';
  title.style.fontFamily = 'sans-serif';
  title.style.fontSize = '68px';
  title.style.fontWeight = '700';
  title.style.marginBottom = '18px';
  overlay.appendChild(title);

  const subtitle = document.createElement('div');
  subtitle.innerText = 'A geometric space shooter';
  subtitle.style.color = '#cccccc';
  subtitle.style.fontFamily = 'sans-serif';
  subtitle.style.fontSize = '18px';
  subtitle.style.marginBottom = '28px';
  overlay.appendChild(subtitle);

  const instr = document.createElement('div');
  instr.id = 'start-instructions';
  instr.style.color = '#dddddd';
  instr.style.fontFamily = 'sans-serif';
  instr.style.fontSize = '14px';
  instr.style.maxWidth = '640px';
  instr.style.textAlign = 'center';
  instr.style.margin = '0 20px 18px';
  instr.innerHTML = '<div style="font-weight:600;margin-bottom:8px">How to Play</div>' +
    '<div style="text-align:left;display:inline-block;line-height:1.5">' +
    '- Mouse: Look / Aim<br>' +
    '- Left click or Space: Fire<br>' +
    '- Right click or Shift: Boost<br>' +
    '- Esc: Release mouse / Pause' +
    '</div>';
  overlay.appendChild(instr);

  const startBtn = document.createElement('button');
  startBtn.id = 'start-button';
  startBtn.innerText = 'Start';
  startBtn.style.fontSize = '18px';
  startBtn.style.padding = '12px 22px';
  startBtn.style.borderRadius = '8px';
  startBtn.style.border = 'none';
  startBtn.style.cursor = 'pointer';
  startBtn.style.background = '#1e90ff';
  startBtn.style.color = '#fff';
  startBtn.style.boxShadow = '0 6px 18px rgba(30,144,255,0.24)';
  overlay.appendChild(startBtn);

  const info = document.createElement('div');
  info.innerText = 'Click Start to begin and lock the mouse. Press Esc to release.';
  info.style.color = '#999';
  info.style.fontFamily = 'sans-serif';
  info.style.fontSize = '12px';
  info.style.marginTop = '16px';
  overlay.appendChild(info);

  document.body.appendChild(overlay);

  const doStart = (e) => {
    try { overlay.remove(); } catch (err) {}
    // set document title
    try { document.title = 'Titanomachy'; } catch (e) {}
    // initialize the game
    try { init(); } catch (e) { console.warn('init failed from start screen', e); }
    // request pointer lock on the canvas (must be in user gesture)
    try {
      if (renderer && renderer.domElement && typeof renderer.domElement.requestPointerLock === 'function') {
        renderer.domElement.requestPointerLock();
      }
    } catch (e) {}
  };

  startBtn.addEventListener('click', doStart);
  // allow pressing Enter to start
  window.addEventListener('keydown', function onKey(e) {
    if (e.key === 'Enter') { window.removeEventListener('keydown', onKey); doStart(); }
  });
}

window.onload = showStartScreen;

// Keyboard controls
window.addEventListener('keydown', (e) => {
  if (e.repeat) return;
  // WASD trigger barrel rolls in their directions
  const ship = window.playerShip;
  const startRoll = (sign) => {
    if (!ship) return;
    if (!ship.userData) ship.userData = {};
    if (ship.userData.rollRemaining && Math.abs(ship.userData.rollRemaining) > 0.001) return; // already rolling
    const amount = Math.PI * 2; // full 360deg barrel roll
    ship.userData.rollRemaining = sign * amount;
    ship.userData.rollSpeed = Math.PI; // radians per second (≈2s duration)
  };
  // WASD controls removed (barrel-roll mapping disabled)
  // Shift key triggers boost
  if (e.key === 'Shift') { startBoost(); }
  // Q/E controls removed
  if (e.code === 'Space') shootLaser();
});
window.addEventListener('keyup', (e) => {
  // WASD roll keys are one-shot; no need to clear
  // Q/E controls removed
});

function shootLaser() {
  // If we're waiting to start the next level, use fire to continue instead of shooting
  if (window.waitingForNextLevel) {
    try { startNextLevel(); } catch (e) {}
    return;
  }
  const ship = window.playerShip;
  const laser = acquirePlayerLaser();
  laser.position.copy(ship.position);
  const dir = new THREE.Vector3(0, 0, -1).applyEuler(ship.rotation).normalize();
  laser.userData.dir = dir;
  laser.userData.prevPos = laser.position.clone();
  laser.userData.origin = laser.position.clone();
  laser.quaternion.copy(ship.quaternion);
  scene.add(laser);
  lasers.push(laser);
  // Instant-hit fallback: test camera-center ray against stored HUD marker position
  try {
    if (levelCube) {
      const raycaster = new THREE.Raycaster();
      raycaster.setFromCamera(new THREE.Vector2(0, 0), camera);
      // compute marker world position from stored local coords or fallback
      let markerWorldPos = null;
      try {
        if (levelCube.userData && levelCube.userData.markerLocal) {
          try { const t = levelCube.userData.type; markerWorldPos = (t === 'pyramid' || t === 'sphere' || t === 'cubeinsphere') ? levelCube.position.clone().add(levelCube.userData.markerLocal.clone()) : levelCube.localToWorld(levelCube.userData.markerLocal.clone()); } catch (e) { markerWorldPos = null; }
        }
      } catch (e) { markerWorldPos = null; }
      if (!markerWorldPos && levelCube.userData && levelCube.userData.markerWorldPos) markerWorldPos = levelCube.userData.markerWorldPos.clone();
      if (markerWorldPos) {
        const toMarker = markerWorldPos.clone().sub(raycaster.ray.origin);
        const t = Math.max(0, raycaster.ray.direction.dot(toMarker));
        const closest = raycaster.ray.origin.clone().add(raycaster.ray.direction.clone().multiplyScalar(t));
        const d = closest.distanceTo(markerWorldPos);
        const markerRadius = levelCube.userData && levelCube.userData.markerHitRadius ? levelCube.userData.markerHitRadius : Math.max(8, ((levelCube.userData.size || 400) * 0.12) * 0.5);
        if (d < markerRadius * 1.4 && !(levelCube.userData && levelCube.userData.markerOccluded)) {
          // register damage instantly
          const intersectPoint = closest;
          levelCube.userData.hp -= 1;
          levelCube.userData.markerHits = (levelCube.userData.markerHits || 0) + 1;
          try { createExplosion(markerWorldPos); } catch (e) {}
          if (levelCube.userData.markerHits >= 15) placeLevelMarker(levelCube);
          updateLevelHealthUI();
          if (levelCube.userData.hp <= 0) levelPassed();
        }
      }
    }
  } catch (e) { console.warn('instant marker raycast failed', e); }
} // Close shootLaser function

// Mouse movement for 360° rotation
let mouseDown = false;
let lastMouse = { x: 0, y: 0 };
window.addEventListener('mousedown', (e) => {
  // Left click (button 0) shoots; also start drag-rotate when not pointer-locked
  if (e.button === 0) {
    try { shootLaser(); } catch (err) {}
    if (!pointerLocked) {
      mouseDown = true;
      lastMouse.x = e.clientX;
      lastMouse.y = e.clientY;
    }
    return;
  }
  // Right click triggers boost (if available)
  if (e.button === 2) {
    try { startBoost(); } catch (err) {}
    return;
  }
  // Other buttons start drag behavior
  mouseDown = true;
  lastMouse.x = e.clientX;
  lastMouse.y = e.clientY;
});
window.addEventListener('mouseup', () => { mouseDown = false; });
window.addEventListener('mousemove', (e) => {
  if (!mouseDown) return;
  const dx = e.clientX - lastMouse.x;
  const dy = e.clientY - lastMouse.y;
  lastMouse.x = e.clientX;
  lastMouse.y = e.clientY;
  const ship = window.playerShip;
  if (ship) {
    const yaw = -dx * ROT_SPEED;
    const pitch = dy * ROT_SPEED;
    // Direct application: allow full 360° rotation without clamping
    ship.rotateOnWorldAxis(new THREE.Vector3(0,1,0), yaw);
    // For drag-based pitch, compute a stable screen-right axis from camera forward and world up
    const _fwd = new THREE.Vector3();
    try { camera.getWorldDirection(_fwd); } catch (e) { _fwd.set(0,0,-1).applyQuaternion(ship.quaternion); }
    const _worldUp = new THREE.Vector3(0,1,0);
    const _screenRight = new THREE.Vector3().crossVectors(_worldUp, _fwd);
    if (_screenRight.lengthSq() > 1e-6) { _screenRight.normalize(); ship.rotateOnWorldAxis(_screenRight, pitch); }
    else { ship.rotateOnWorldAxis(new THREE.Vector3(1,0,0), pitch); }
  }
});
