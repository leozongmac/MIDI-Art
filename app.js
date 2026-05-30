const SAMPLE_ROOTS = [36, 48, 53, 60, 65, 72, 81];
const SAMPLE_FILES = Object.fromEntries(
  SAMPLE_ROOTS.map((note) => [note, `assets/samples/piano_${note}.wav`])
);
const DEFAULT_ART_IMAGE = 'assets/starry_night_particles_source.png';

const canvas = document.getElementById('scene');
const ctx = canvas.getContext('2d');
const startBtn = document.getElementById('startBtn');
const audioStatusEl = document.getElementById('audioStatus');
const midiStatusEl = document.getElementById('midiStatus');
const noteStatusEl = document.getElementById('noteStatus');
const particleStatusEl = document.getElementById('particleStatus');
const expressionStatusEl = document.getElementById('expressionStatus');
const sustainStatusEl = document.getElementById('sustainStatus');
const imageStatusEl = document.getElementById('imageStatus');
const imageUploadInput = document.getElementById('imageUpload');
const resetImageBtn = document.getElementById('resetImageBtn');
const uploadPanelEl = document.getElementById('uploadPanel');
const cameraBtn = document.getElementById('cameraBtn');
const fullscreenBtn = document.getElementById('fullscreenBtn');

const imageThresholdSlider = document.getElementById('imageThreshold');
const particleDensitySlider = document.getElementById('particleDensity');
const particleLifetimeSlider = document.getElementById('particleLifetime');
const gravitySlider = document.getElementById('gravityStrength');
const ejectionSlider = document.getElementById('ejectionStrength');

const imageThresholdValueEl = document.getElementById('imageThresholdValue');
const particleDensityValueEl = document.getElementById('particleDensityValue');
const particleLifetimeValueEl = document.getElementById('particleLifetimeValue');
const gravityValueEl = document.getElementById('gravityStrengthValue');
const ejectionValueEl = document.getElementById('ejectionStrengthValue');

let width = window.innerWidth;
let height = window.innerHeight;
let dpr = Math.min(window.devicePixelRatio || 1, 2);

let audioCtx = null;
let masterGain = null;
let analyser = null;
let compressor = null;
let reverb = null;
let reverbGain = null;
let dryGain = null;
let sampleBuffers = new Map();
let midiAccess = null;
let midiInputs = [];
let audioStarted = false;
let samplesLoaded = false;
let sustainPedal = false;
let turbulence = 0.35;
let pitchBend = 0;
let visualEnergy = 0;
let sourceImage = null;
let cameraVideo = null;
let cameraStream = null;
let cameraActive = false;
let lastDynamicSourceRefresh = 0;
let presentationMode = false;
let persistedImageStatus = '当前：默认星空';
let uploadDragDepth = 0;

const visualParams = {
  imageThreshold: 42,
  particleDensity: 1.0,
  particleLifetime: 1.0,
  gravity: 0.65,
  ejection: 1.0,
};

const particles = [];
const ripples = [];
const bursts = [];
const ambientStars = [];
const activeNotes = new Map();
const sustainedNotes = new Set();
const heldNotes = new Set();
const pressedKeys = new Set();
const frequencyData = new Uint8Array(128);
let artBounds = { x: 0, y: 0, width: 0, height: 0 };

const KEYBOARD_MAP = {
  a: 60,
  w: 61,
  s: 62,
  e: 63,
  d: 64,
  f: 65,
  t: 66,
  g: 67,
  y: 68,
  h: 69,
  u: 70,
  j: 71,
  k: 72,
};

function setStatus(el, text) {
  if (el) el.textContent = text;
}

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function lerp(a, b, t) {
  return a + (b - a) * t;
}

function noteName(note) {
  const names = ['C', 'C♯', 'D', 'D♯', 'E', 'F', 'F♯', 'G', 'G♯', 'A', 'A♯', 'B'];
  const octave = Math.floor(note / 12) - 1;
  return `${names[note % 12]}${octave}`;
}

function pickNearestRoot(note) {
  let best = SAMPLE_ROOTS[0];
  let bestDist = Infinity;
  for (const root of SAMPLE_ROOTS) {
    const dist = Math.abs(root - note);
    if (dist < bestDist) {
      best = root;
      bestDist = dist;
    }
  }
  return best;
}

function updateSliderReadouts() {
  imageThresholdValueEl.textContent = `${Math.round(visualParams.imageThreshold)}`;
  particleDensityValueEl.textContent = `${visualParams.particleDensity.toFixed(2)}x`;
  particleLifetimeValueEl.textContent = `${visualParams.particleLifetime.toFixed(2)}x`;
  gravityValueEl.textContent = `${visualParams.gravity.toFixed(2)}x`;
  ejectionValueEl.textContent = `${visualParams.ejection.toFixed(2)}x`;
}

function updateExpressionStatus() {
  setStatus(expressionStatusEl, `Turbulence ${Math.round(turbulence * 100)}%`);
}

function updatePedalStatus() {
  setStatus(sustainStatusEl, sustainPedal ? '开启' : '关闭');
}

function setImageStatus(text, { persist = true } = {}) {
  if (persist) persistedImageStatus = text;
  setStatus(imageStatusEl, text);
}

function restoreImageStatus() {
  if (cameraActive) {
    setStatus(imageStatusEl, '当前：摄像头实时画面');
    return;
  }
  setStatus(imageStatusEl, persistedImageStatus);
}

function updateCameraButton() {
  if (!cameraBtn) return;
  cameraBtn.textContent = cameraActive ? '关闭摄像头' : '启动摄像头';
}

function updateFullscreenButton() {
  if (!fullscreenBtn) return;
  fullscreenBtn.textContent = presentationMode ? '退出全屏' : '全屏模式';
}

function getActiveSourceElement() {
  if (cameraActive && cameraVideo && cameraVideo.videoWidth && cameraVideo.videoHeight) {
    return cameraVideo;
  }
  return sourceImage;
}

async function loadImageFromSource(src) {
  const img = new Image();
  img.src = src;
  await img.decode();
  return img;
}

function resizeCanvas() {
  width = window.innerWidth;
  height = window.innerHeight;
  dpr = Math.min(window.devicePixelRatio || 1, 2);
  canvas.width = Math.floor(width * dpr);
  canvas.height = Math.floor(height * dpr);
  canvas.style.width = `${width}px`;
  canvas.style.height = `${height}px`;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  if (sourceImage) {
    buildParticlesFromImage();
  }
}

function createImpulseResponse(context, duration = 3.2, decay = 2.4) {
  const length = Math.floor(context.sampleRate * duration);
  const impulse = context.createBuffer(2, length, context.sampleRate);
  for (let channel = 0; channel < impulse.numberOfChannels; channel += 1) {
    const data = impulse.getChannelData(channel);
    for (let i = 0; i < length; i += 1) {
      const t = i / length;
      data[i] = (Math.random() * 2 - 1) * Math.pow(1 - t, decay);
    }
  }
  return impulse;
}

async function initAudio() {
  if (audioStarted) {
    if (audioCtx?.state === 'suspended') {
      await audioCtx.resume();
    }
    return;
  }

  audioCtx = new (window.AudioContext || window.webkitAudioContext)();

  compressor = audioCtx.createDynamicsCompressor();
  compressor.threshold.value = -18;
  compressor.knee.value = 22;
  compressor.ratio.value = 3.2;
  compressor.attack.value = 0.002;
  compressor.release.value = 0.23;

  masterGain = audioCtx.createGain();
  masterGain.gain.value = 0.82;

  dryGain = audioCtx.createGain();
  dryGain.gain.value = 1.0;

  reverb = audioCtx.createConvolver();
  reverb.buffer = createImpulseResponse(audioCtx);

  reverbGain = audioCtx.createGain();
  reverbGain.gain.value = 0.26;

  analyser = audioCtx.createAnalyser();
  analyser.fftSize = 256;
  analyser.smoothingTimeConstant = 0.84;

  dryGain.connect(masterGain);
  reverb.connect(reverbGain);
  reverbGain.connect(masterGain);
  masterGain.connect(compressor);
  compressor.connect(analyser);
  analyser.connect(audioCtx.destination);

  audioStarted = true;
  setStatus(audioStatusEl, '已启动');
}

async function loadSamples() {
  if (samplesLoaded) return;
  setStatus(audioStatusEl, '加载采样中…');

  const entries = await Promise.all(
    SAMPLE_ROOTS.map(async (root) => {
      const response = await fetch(SAMPLE_FILES[root]);
      const arrayBuffer = await response.arrayBuffer();
      const decoded = await audioCtx.decodeAudioData(arrayBuffer.slice(0));
      return [root, decoded];
    })
  );

  for (const [root, buffer] of entries) {
    sampleBuffers.set(root, buffer);
  }

  samplesLoaded = true;
  setStatus(audioStatusEl, '采样已就绪');
}

async function requestMidi() {
  if (!navigator.requestMIDIAccess) {
    setStatus(midiStatusEl, '浏览器不支持 Web MIDI');
    return;
  }

  midiAccess = await navigator.requestMIDIAccess({ sysex: false });

  const refreshInputs = () => {
    midiInputs = [...midiAccess.inputs.values()];
    midiInputs.forEach((input) => {
      input.onmidimessage = handleMidiMessage;
    });

    if (midiInputs.length > 0) {
      setStatus(
        midiStatusEl,
        `已连接 ${midiInputs.length} 台：${midiInputs.map((x) => x.name).join(' / ')}`
      );
    } else {
      setStatus(midiStatusEl, '未检测到 MIDI 设备（可用电脑键盘演示）');
    }
  };

  refreshInputs();
  midiAccess.onstatechange = refreshInputs;
}

function getNotePosition(note, velocity = 96) {
  const n = clamp((note - 36) / (96 - 36), 0, 1);
  const x = artBounds.x + artBounds.width * (0.08 + n * 0.84);
  const y = artBounds.y + artBounds.height * (0.78 - n * 0.5 - (velocity / 127) * 0.08);
  return { x, y };
}

function noteHue(note) {
  return ((note % 12) / 12) * 360;
}

function addRipple(note, velocity) {
  const pos = getNotePosition(note, velocity);
  const lifetime = visualParams.particleLifetime;
  const ejection = visualParams.ejection;
  const gravity = visualParams.gravity;

  ripples.push({
    x: pos.x,
    y: pos.y,
    age: 0,
    maxAge: 2.2 * lifetime,
    speed: (72 + (note - 48) * 0.45) * (0.95 + ejection * 0.16),
    band: 40 + velocity * 0.24,
    strength: (1.0 + (velocity / 127) * 2.8) * ejection,
    gravity: gravity * (0.3 + velocity / 220),
    swirl: (note % 2 === 0 ? 1 : -1) * (0.18 + turbulence * 0.75),
    hue: noteHue(note),
    alpha: 0.18 + velocity / 300,
  });

  bursts.push({
    x: pos.x,
    y: pos.y,
    age: 0,
    maxAge: 0.95 * lifetime,
    radius: 10 + velocity * 0.18,
    hue: noteHue(note),
    intensity: (0.5 + velocity / 127) * ejection,
  });
}

function applyPitchBendToVoices() {
  if (!audioCtx) return;
  activeNotes.forEach((voices) => {
    voices.forEach((voice) => {
      if (voice.released) return;
      voice.source.detune.setTargetAtTime(pitchBend * 200, audioCtx.currentTime, 0.01);
    });
  });
}

function refreshSustainAcoustics() {
  if (!audioCtx || !reverbGain) return;
  const target = sustainPedal ? 0.36 : 0.26;
  reverbGain.gain.setTargetAtTime(target, audioCtx.currentTime, 0.08);
}

function releaseVoice(voice, now = audioCtx.currentTime, releaseMultiplier = 1) {
  if (!voice || voice.released) return;
  voice.released = true;
  const releaseTime = 1.6 * releaseMultiplier;
  const current = Math.max(voice.gain.gain.value, 0.001);
  voice.gain.gain.cancelScheduledValues(now);
  voice.gain.gain.setValueAtTime(current, now);
  voice.gain.gain.exponentialRampToValueAtTime(0.0001, now + releaseTime);
  voice.source.stop(now + releaseTime + 0.08);
}

function stopNote(note, { forced = false } = {}) {
  const voices = activeNotes.get(note);
  if (!voices?.length) return;

  if (sustainPedal && !forced && !heldNotes.has(note)) {
    sustainedNotes.add(note);
    return;
  }

  const releaseMultiplier = sustainPedal || sustainedNotes.has(note) ? 1.2 : 1;
  voices.forEach((voice) => releaseVoice(voice, audioCtx.currentTime, releaseMultiplier));
  activeNotes.delete(note);
  sustainedNotes.delete(note);
}

function releaseSustainedNotes() {
  [...sustainedNotes].forEach((note) => {
    if (!heldNotes.has(note)) {
      stopNote(note, { forced: true });
    }
  });
}

function setSustainPedal(nextState) {
  sustainPedal = nextState;
  updatePedalStatus();
  refreshSustainAcoustics();
  if (!sustainPedal) {
    releaseSustainedNotes();
  }
}

function playNote(note, velocity = 100) {
  if (!audioStarted || !samplesLoaded) return;

  if (activeNotes.has(note)) {
    stopNote(note, { forced: true });
  }

  const root = pickNearestRoot(note);
  const buffer = sampleBuffers.get(root);
  if (!buffer) return;

  const now = audioCtx.currentTime;
  const source = audioCtx.createBufferSource();
  source.buffer = buffer;
  source.playbackRate.value = Math.pow(2, (note - root) / 12);
  source.detune.value = pitchBend * 200;

  const gain = audioCtx.createGain();
  const filter = audioCtx.createBiquadFilter();
  filter.type = 'lowpass';
  filter.frequency.value = 3500 + velocity * 36;
  filter.Q.value = 0.4;

  const velocityGain = clamp(0.18 + (velocity / 127) * 0.72, 0.12, 1.0);
  gain.gain.setValueAtTime(0.0001, now);
  gain.gain.exponentialRampToValueAtTime(velocityGain, now + 0.01);
  gain.gain.exponentialRampToValueAtTime(Math.max(velocityGain * 0.82, 0.08), now + 0.32);

  source.connect(filter);
  filter.connect(gain);
  gain.connect(dryGain);
  gain.connect(reverb);
  source.start(now);

  const voice = { note, source, gain, filter, released: false };
  source.onended = () => {
    const voices = activeNotes.get(note);
    if (!voices) return;
    const next = voices.filter((v) => v !== voice);
    if (next.length > 0) activeNotes.set(note, next);
    else activeNotes.delete(note);
  };

  activeNotes.set(note, [...(activeNotes.get(note) || []), voice]);
  sustainedNotes.delete(note);
  addRipple(note, velocity);
  setStatus(noteStatusEl, `${noteName(note)} · velocity ${velocity}`);
}

function handleControlChange(controller, value) {
  if (controller === 1 || controller === 74) {
    turbulence = clamp(value / 127, 0, 1);
    updateExpressionStatus();
  }

  if (controller === 64) {
    setSustainPedal(value >= 64);
  }
}

function handleMidiMessage(event) {
  const [status, data1, data2] = event.data;
  const messageType = status & 0xf0;

  switch (messageType) {
    case 0x90:
      if (data2 === 0) {
        heldNotes.delete(data1);
        stopNote(data1);
      } else {
        heldNotes.add(data1);
        playNote(data1, data2);
      }
      break;
    case 0x80:
      heldNotes.delete(data1);
      stopNote(data1);
      break;
    case 0xb0:
      handleControlChange(data1, data2);
      break;
    case 0xe0: {
      const value = ((data2 << 7) | data1) - 8192;
      pitchBend = clamp(value / 8192, -1, 1);
      applyPitchBendToVoices();
      break;
    }
    default:
      break;
  }
}

function attachKeyboardFallback() {
  window.addEventListener('keydown', (event) => {
    const key = event.key.toLowerCase();

    if (key === ' ') {
      event.preventDefault();
      if (!sustainPedal) setSustainPedal(true);
      return;
    }

    if (!(key in KEYBOARD_MAP)) return;
    if (pressedKeys.has(key)) return;

    pressedKeys.add(key);
    heldNotes.add(KEYBOARD_MAP[key]);
    playNote(KEYBOARD_MAP[key], 104);
  });

  window.addEventListener('keyup', (event) => {
    const key = event.key.toLowerCase();

    if (key === ' ') {
      event.preventDefault();
      setSustainPedal(false);
      return;
    }

    if (!(key in KEYBOARD_MAP)) return;
    pressedKeys.delete(key);
    heldNotes.delete(KEYBOARD_MAP[key]);
    stopNote(KEYBOARD_MAP[key]);
  });
}

function bindVisualControls() {
  imageThresholdSlider.addEventListener('input', () => {
    visualParams.imageThreshold = Number(imageThresholdSlider.value);
    updateSliderReadouts();
    buildParticlesFromImage();
  });

  particleDensitySlider.addEventListener('input', () => {
    visualParams.particleDensity = Number(particleDensitySlider.value);
    updateSliderReadouts();
    buildParticlesFromImage();
  });

  particleLifetimeSlider.addEventListener('input', () => {
    visualParams.particleLifetime = Number(particleLifetimeSlider.value);
    updateSliderReadouts();
  });

  gravitySlider.addEventListener('input', () => {
    visualParams.gravity = Number(gravitySlider.value);
    updateSliderReadouts();
  });

  ejectionSlider.addEventListener('input', () => {
    visualParams.ejection = Number(ejectionSlider.value);
    updateSliderReadouts();
  });

  updateSliderReadouts();
}

function createAmbientStars() {
  ambientStars.length = 0;
  const count = Math.round(Math.max(60, Math.min(180, width / 9)));
  for (let i = 0; i < count; i += 1) {
    ambientStars.push({
      x: Math.random() * width,
      y: Math.random() * height,
      radius: Math.random() * 1.8 + 0.3,
      alpha: Math.random() * 0.45 + 0.12,
      speed: Math.random() * 0.8 + 0.15,
      phase: Math.random() * Math.PI * 2,
    });
  }
}

async function ensureCameraVideo() {
  if (cameraVideo) return cameraVideo;
  cameraVideo = document.createElement('video');
  cameraVideo.autoplay = true;
  cameraVideo.muted = true;
  cameraVideo.playsInline = true;
  return cameraVideo;
}

async function startCamera() {
  if (!navigator.mediaDevices?.getUserMedia) {
    setImageStatus('摄像头不可用：浏览器不支持');
    return;
  }

  try {
    const video = await ensureCameraVideo();
    cameraStream = await navigator.mediaDevices.getUserMedia({
      video: {
        facingMode: 'user',
        width: { ideal: 1280 },
        height: { ideal: 720 },
      },
      audio: false,
    });
    video.srcObject = cameraStream;
    await video.play();
    cameraActive = true;
    lastDynamicSourceRefresh = 0;
    updateCameraButton();
    setImageStatus('当前：摄像头实时画面', { persist: false });
    buildParticlesFromImage();
  } catch (error) {
    console.error(error);
    setImageStatus('摄像头启动失败');
  }
}

function stopCamera() {
  if (cameraStream) {
    cameraStream.getTracks().forEach((track) => track.stop());
    cameraStream = null;
  }
  if (cameraVideo) {
    cameraVideo.pause();
    cameraVideo.srcObject = null;
  }
  cameraActive = false;
  updateCameraButton();
  restoreImageStatus();
  buildParticlesFromImage();
}

async function toggleCamera() {
  if (cameraActive) stopCamera();
  else await startCamera();
}

async function loadDefaultSourceImage() {
  sourceImage = await loadImageFromSource(DEFAULT_ART_IMAGE);
  buildParticlesFromImage();
  setImageStatus('当前：默认星空');
}

function setPresentationMode(active) {
  presentationMode = active;
  document.body.classList.toggle('presentation-mode', active);
  updateFullscreenButton();
}

async function togglePresentationMode() {
  const entering = !presentationMode;
  setPresentationMode(entering);

  if (entering) {
    try {
      if (!document.fullscreenElement && document.documentElement.requestFullscreen) {
        await document.documentElement.requestFullscreen();
      }
    } catch (error) {
      console.warn('requestFullscreen failed:', error);
    }
  } else {
    try {
      if (document.fullscreenElement && document.exitFullscreen) {
        await document.exitFullscreen();
      }
    } catch (error) {
      console.warn('exitFullscreen failed:', error);
    }
  }
}

function setUploadPanelActive(active) {
  uploadPanelEl.classList.toggle('drag-over', active);
  if (active) {
    setImageStatus('松手即可替换图片', { persist: false });
  } else {
    restoreImageStatus();
  }
}

async function applyUploadedImage(file) {
  if (!file) return;

  if (!file.type.startsWith('image/')) {
    setImageStatus('上传失败：请选择图片文件');
    return;
  }

  const objectUrl = URL.createObjectURL(file);
  try {
    sourceImage = await loadImageFromSource(objectUrl);
    buildParticlesFromImage();
    setImageStatus(`当前：${file.name}`);
  } catch (error) {
    console.error(error);
    setImageStatus('上传失败：无法解析该图片');
  } finally {
    URL.revokeObjectURL(objectUrl);
  }
}

function bindImageControls() {
  imageUploadInput.addEventListener('change', async (event) => {
    const [file] = event.target.files || [];
    if (cameraActive) stopCamera();
    await applyUploadedImage(file);
    imageUploadInput.value = '';
  });

  resetImageBtn.addEventListener('click', async () => {
    if (cameraActive) stopCamera();
    await loadDefaultSourceImage();
  });

  uploadPanelEl.addEventListener('dragenter', (event) => {
    event.preventDefault();
    uploadDragDepth += 1;
    setUploadPanelActive(true);
  });

  uploadPanelEl.addEventListener('dragover', (event) => {
    event.preventDefault();
    if (event.dataTransfer) event.dataTransfer.dropEffect = 'copy';
    setUploadPanelActive(true);
  });

  uploadPanelEl.addEventListener('dragleave', (event) => {
    event.preventDefault();
    uploadDragDepth = Math.max(0, uploadDragDepth - 1);
    if (uploadDragDepth === 0) {
      setUploadPanelActive(false);
    }
  });

  uploadPanelEl.addEventListener('drop', async (event) => {
    event.preventDefault();
    uploadDragDepth = 0;
    setUploadPanelActive(false);
    const [file] = event.dataTransfer?.files || [];
    if (cameraActive) stopCamera();
    await applyUploadedImage(file);
  });
}

function buildParticlesFromImage() {
  const source = getActiveSourceElement();
  if (!source) return;

  const sourceWidth = source.videoWidth || source.naturalWidth || source.width;
  const sourceHeight = source.videoHeight || source.naturalHeight || source.height;
  if (!sourceWidth || !sourceHeight) return;

  particles.length = 0;

  const margin = Math.min(width, height) * 0.06;
  const maxW = width - margin * 2;
  const maxH = height - margin * 2;
  const imageRatio = sourceWidth / sourceHeight;

  let drawWidth = maxW;
  let drawHeight = drawWidth / imageRatio;
  if (drawHeight > maxH) {
    drawHeight = maxH;
    drawWidth = drawHeight * imageRatio;
  }

  artBounds = {
    x: (width - drawWidth) / 2,
    y: (height - drawHeight) / 2 + 6,
    width: drawWidth,
    height: drawHeight,
  };

  const offscreen = document.createElement('canvas');
  const offCtx = offscreen.getContext('2d', { willReadFrequently: true });
  offscreen.width = Math.max(420, Math.round(drawWidth));
  offscreen.height = Math.max(260, Math.round(drawHeight));
  offCtx.drawImage(source, 0, 0, offscreen.width, offscreen.height);

  const imageData = offCtx.getImageData(0, 0, offscreen.width, offscreen.height).data;
  const density = visualParams.particleDensity;
  const area = offscreen.width * offscreen.height;
  const baseStep = Math.max(4, Math.round(Math.sqrt(area / 17000)));
  const step = clamp(Math.round(baseStep / Math.sqrt(density)), 2, 10);
  const keepChance = density >= 1 ? 1 : clamp(0.45 + density * 0.55, 0.22, 1);

  for (let y = 0; y < offscreen.height; y += step) {
    for (let x = 0; x < offscreen.width; x += step) {
      const idx = (y * offscreen.width + x) * 4;
      const r = imageData[idx];
      const g = imageData[idx + 1];
      const b = imageData[idx + 2];
      const a = imageData[idx + 3];
      const luminance = 0.2126 * r + 0.7152 * g + 0.0722 * b;
      const channelMax = Math.max(r, g, b);
      const channelMin = Math.min(r, g, b);
      const saturation = channelMax - channelMin;
      const detailScore = luminance * 0.78 + saturation * 0.72 + a * 0.08;
      const threshold = visualParams.imageThreshold;

      if (a < 80) continue;
      if (detailScore < threshold) continue;
      if (detailScore < threshold + 18 && Math.random() < 0.38) continue;
      if (Math.random() > keepChance) continue;

      const px = artBounds.x + (x / offscreen.width) * artBounds.width;
      const py = artBounds.y + (y / offscreen.height) * artBounds.height;
      const size = luminance > 180 ? 2.5 : luminance > 110 ? 1.9 : 1.25;

      particles.push({
        x: px + (Math.random() - 0.5) * 8,
        y: py + (Math.random() - 0.5) * 8,
        homeX: px,
        homeY: py,
        vx: 0,
        vy: 0,
        color: `rgb(${r}, ${g}, ${b})`,
        size,
        alpha: clamp(0.38 + luminance / 320, 0.16, 0.94),
        twinkle: Math.random() * Math.PI * 2,
      });
    }
  }

  particleStatusEl.textContent = String(particles.length);
  if (cameraActive) {
    setImageStatus('当前：摄像头实时画面', { persist: false });
  } else {
    restoreImageStatus();
  }
}

function drawBackground(time) {
  ctx.clearRect(0, 0, width, height);

  const bg = ctx.createLinearGradient(0, 0, 0, height);
  bg.addColorStop(0, '#041127');
  bg.addColorStop(0.58, '#08152c');
  bg.addColorStop(1, '#030712');
  ctx.fillStyle = bg;
  ctx.fillRect(0, 0, width, height);

  const glowA = ctx.createRadialGradient(width * 0.22, height * 0.18, 0, width * 0.22, height * 0.18, width * 0.34);
  glowA.addColorStop(0, `rgba(70, 118, 255, ${0.12 + visualEnergy * 0.12})`);
  glowA.addColorStop(1, 'rgba(70, 118, 255, 0)');
  ctx.fillStyle = glowA;
  ctx.fillRect(0, 0, width, height);

  const glowB = ctx.createRadialGradient(width * 0.82, height * 0.16, 0, width * 0.82, height * 0.16, width * 0.28);
  glowB.addColorStop(0, `rgba(255, 214, 86, ${0.14 + visualEnergy * 0.08})`);
  glowB.addColorStop(1, 'rgba(255, 214, 86, 0)');
  ctx.fillStyle = glowB;
  ctx.fillRect(0, 0, width, height);

  ctx.save();
  ctx.globalCompositeOperation = 'screen';
  for (const star of ambientStars) {
    const twinkle = 0.6 + Math.sin(time * 0.001 * star.speed + star.phase) * 0.4;
    ctx.globalAlpha = star.alpha * twinkle;
    ctx.fillStyle = 'rgba(255, 241, 191, 1)';
    ctx.beginPath();
    ctx.arc(star.x, star.y, star.radius + visualEnergy * 0.8, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.restore();
}

function updateRipples(dt) {
  for (let i = ripples.length - 1; i >= 0; i -= 1) {
    const ripple = ripples[i];
    ripple.age += dt;
    if (ripple.age > ripple.maxAge) ripples.splice(i, 1);
  }

  for (let i = bursts.length - 1; i >= 0; i -= 1) {
    const burst = bursts[i];
    burst.age += dt;
    if (burst.age > burst.maxAge) bursts.splice(i, 1);
  }
}

function applyParticlePhysics(time, dt) {
  const centerX = artBounds.x + artBounds.width * 0.5;
  const centerY = artBounds.y + artBounds.height * 0.5;
  const spring = 0.01 + visualParams.gravity * 0.025 + turbulence * 0.008;
  const damping = clamp(0.86 + visualParams.particleLifetime * 0.05, 0.84, 0.96);
  const currentEnergy = 0.4 + visualEnergy * 2.3;
  const globalBend = pitchBend * 0.4;

  for (const p of particles) {
    let ax = (p.homeX - p.x) * spring;
    let ay = (p.homeY - p.y) * spring;

    const centerDx = centerX - p.x;
    const centerDy = centerY - p.y;
    ax += centerDx * 0.00002 * visualParams.gravity;
    ay += centerDy * 0.00002 * visualParams.gravity;

    const flow = Math.sin(time * 0.0012 + p.homeY * 0.015 + p.twinkle) * (0.08 + turbulence * 0.25);
    ax += flow * 0.12;
    ay += Math.cos(time * 0.001 + p.homeX * 0.01 + p.twinkle) * 0.04 * turbulence;

    for (const ripple of ripples) {
      const age01 = ripple.age / ripple.maxAge;
      const radius = ripple.age * ripple.speed;
      const dx = p.x - ripple.x;
      const dy = p.y - ripple.y;
      const dist = Math.hypot(dx, dy) + 0.0001;
      const spread = ripple.band + ripple.age * 14;
      const diff = Math.abs(dist - radius);
      const nx = dx / dist;
      const ny = dy / dist;
      const tangentX = -ny;
      const tangentY = nx;

      if (diff < spread) {
        const strength = (1 - diff / spread) ** 2 * ripple.strength * (1 - age01);
        ax += nx * strength * currentEnergy * 0.55;
        ay += ny * strength * currentEnergy * 0.55;
        ax += tangentX * strength * ripple.swirl * 0.22;
        ay += tangentY * strength * ripple.swirl * 0.22;
      }

      if (dist < radius + spread * 1.8) {
        const pull = ripple.gravity * (1 - age01) * 0.18;
        ax -= nx * pull;
        ay -= ny * pull;
      }
    }

    ax += globalBend * 0.03;
    ay += Math.sin(time * 0.0014 + p.homeX * 0.008) * 0.01 * visualEnergy;

    p.vx = (p.vx + ax * dt * 60) * damping;
    p.vy = (p.vy + ay * dt * 60) * damping;
    p.x += p.vx;
    p.y += p.vy;
  }
}

function drawRipples() {
  ctx.save();
  ctx.lineWidth = 1.25;
  ctx.globalCompositeOperation = 'screen';

  for (const ripple of ripples) {
    const age01 = ripple.age / ripple.maxAge;
    const radius = ripple.age * ripple.speed;
    ctx.globalAlpha = ripple.alpha * (1 - age01);
    ctx.strokeStyle = `hsla(${ripple.hue}, 95%, 74%, 0.8)`;
    ctx.beginPath();
    ctx.arc(ripple.x, ripple.y, radius, 0, Math.PI * 2);
    ctx.stroke();

    ctx.globalAlpha = ripple.alpha * 0.42 * (1 - age01);
    ctx.strokeStyle = `hsla(${ripple.hue}, 100%, 82%, 0.6)`;
    ctx.beginPath();
    ctx.arc(ripple.x, ripple.y, radius + 18, 0, Math.PI * 2);
    ctx.stroke();
  }

  for (const burst of bursts) {
    const life = 1 - burst.age / burst.maxAge;
    const radius = burst.radius + burst.age * 42;
    const gradient = ctx.createRadialGradient(burst.x, burst.y, 0, burst.x, burst.y, radius);
    gradient.addColorStop(0, `hsla(${burst.hue}, 100%, 74%, ${0.5 * life * burst.intensity})`);
    gradient.addColorStop(1, `hsla(${burst.hue}, 100%, 74%, 0)`);
    ctx.globalAlpha = life;
    ctx.fillStyle = gradient;
    ctx.beginPath();
    ctx.arc(burst.x, burst.y, radius, 0, Math.PI * 2);
    ctx.fill();
  }

  ctx.restore();
}

function drawParticles(time) {
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';

  for (const p of particles) {
    const twinkle = 0.84 + Math.sin(time * 0.0018 + p.twinkle + p.homeX * 0.01) * 0.22;
    ctx.globalAlpha = clamp(p.alpha * twinkle + visualEnergy * 0.14, 0.05, 1);
    ctx.fillStyle = p.color;
    ctx.fillRect(p.x, p.y, p.size, p.size);
  }

  ctx.restore();
}

function updateAudioEnergy() {
  if (!analyser || !audioStarted) {
    visualEnergy = lerp(visualEnergy, 0, 0.08);
    return;
  }

  analyser.getByteFrequencyData(frequencyData);
  let low = 0;
  let mid = 0;
  for (let i = 0; i < frequencyData.length; i += 1) {
    if (i < 18) low += frequencyData[i];
    else if (i < 54) mid += frequencyData[i];
  }

  low /= 18 * 255;
  mid /= 36 * 255;
  const activity = clamp(activeNotes.size / 6, 0, 1);
  const target = clamp(low * 1.2 + mid * 0.55 + activity * 0.14, 0, 1);
  visualEnergy = lerp(visualEnergy, target, 0.12);
}

let previousTime = performance.now();
function animate(now) {
  const dt = Math.min((now - previousTime) / 1000, 0.033);
  previousTime = now;

  if (cameraActive && now - lastDynamicSourceRefresh > 120) {
    buildParticlesFromImage();
    lastDynamicSourceRefresh = now;
  }

  updateAudioEnergy();
  updateRipples(dt);
  applyParticlePhysics(now, dt);
  drawBackground(now);
  drawRipples();
  drawParticles(now);

  requestAnimationFrame(animate);
}

startBtn.addEventListener('click', async () => {
  startBtn.disabled = true;
  startBtn.textContent = '正在初始化…';

  try {
    await initAudio();
    await loadSamples();
    await requestMidi();
    if (audioCtx.state === 'suspended') {
      await audioCtx.resume();
    }
    startBtn.textContent = '已启动';
  } catch (error) {
    console.error(error);
    setStatus(audioStatusEl, '初始化失败');
    setStatus(midiStatusEl, '请检查浏览器权限');
    startBtn.disabled = false;
    startBtn.textContent = '重新尝试';
  }
});

cameraBtn.addEventListener('click', async () => {
  await toggleCamera();
});

fullscreenBtn.addEventListener('click', async () => {
  await togglePresentationMode();
});

document.addEventListener('fullscreenchange', () => {
  if (!document.fullscreenElement && presentationMode) {
    setPresentationMode(false);
  }
});

window.addEventListener('beforeunload', () => {
  if (cameraActive) stopCamera();
});

window.addEventListener('resize', () => {
  resizeCanvas();
  createAmbientStars();
});

(async function boot() {
  resizeCanvas();
  bindVisualControls();
  bindImageControls();
  createAmbientStars();
  attachKeyboardFallback();
  updateExpressionStatus();
  updatePedalStatus();
  updateCameraButton();
  updateFullscreenButton();
  await loadDefaultSourceImage();
  requestAnimationFrame(animate);
})();
