/* Pinball — faithful reimplementation of CBC "Pinball Space Adventures"
   Uses the original Box2DWeb engine + extracted level geometry + original
   physics constants/scoring so ball physics & obstacle behaviour match. */

//// ---- constants (from original settings.js) ----
var WORLD_SCALE = 100;
var GRAVITY = 13.6;
var GENERAL_RESTITUTION = 0.33;
var GENERAL_FRICTION = 0.7;
var FPS = 60;
var BALL_RADIUS = 28;
var BALL_STARTPOS = {x: 1092, y: 1770};
var FLIPPER_STRENGTH = 18;
var SPRING_MAX_STRENGTH = 1;
var BALL_RETURN_Y = 1860;              // on bottom return platform, ready to fire
var BALL_RETURN_FLIPPER_LOW_Y = 1760;  // ball top below down-flipper low point can return
var TABLE_W = 1152, TABLE_H = 1920;

//// ---- scoring tables (from CScoreController.js) ----
var SINGLE_BUTTON_SCORE = 5;
var CIRCLE_BUMPER_START_SCORE = 1;
var GATE_SCORE = 12;
var ROUTER_GATE_SCORE = [5,12,17,21,28,33,39];
var JUMPER_SCORE = 3;
var ALL_JUMPER_BUTTONS_SCORE = 33;
var CHANNEL_LIGHT_SCORE = 28;
var MULTIPLIER_BANK_SCORE = 21;
var SINGLE_LETTERS_LIT_SCORE = 39;
var ALL_LETTERS_LIT_SCORE = 47;
var BIG_SCORE_THRESHOLD = 470;
var BIG_SCORE_RECENT_COUNT = 30;
var BIG_SCORE_MIN_SAMPLES = 10;
var BIG_SCORE_MULTIPLE = 4;
var BIG_SCORE_COMBO_MS = 500;
var BIG_SCORE_COOLDOWN_MS = 60000;
var MULTIPLIER_STEP = 0.1;
var LIGHT_BANK_COOLDOWN_MS = 400;
var CODEX_ENHANCED_MS = 45000;
var CODEX_VELOCITY_MULT = 2;
var CODEX_FLIPPER_MULT = 3;
var CODEX_SPEED_BOOST = 1.006;
var CODEX_MAX_BALL_SPEED = 78;
var CODEX_EXTRA_GRAVITY = 1.15;
var CODEX_ANTIGRAVITY_MS = 10000;
var CODEX_ANTIGRAVITY_CHANCE = 0.15;
var CODEX_ANTIGRAVITY_MULT = -0.5;
var CODEX_ANTIGRAVITY_SUPPRESS_Y = 270;
var CODEX_ANTIGRAVITY_RESUME_Y = 668;

//// ---- Box2D aliases ----
var b2Vec2 = Box2D.Common.Math.b2Vec2,
    b2BodyDef = Box2D.Dynamics.b2BodyDef,
    b2Body = Box2D.Dynamics.b2Body,
    b2FixtureDef = Box2D.Dynamics.b2FixtureDef,
    b2World = Box2D.Dynamics.b2World,
    b2PolygonShape = Box2D.Collision.Shapes.b2PolygonShape,
    b2CircleShape = Box2D.Collision.Shapes.b2CircleShape,
    b2RevoluteJointDef = Box2D.Dynamics.Joints.b2RevoluteJointDef,
    b2WorldManifold = Box2D.Collision.b2WorldManifold;

// Box2DWeb postDefs init-order bug: b2_polygonRadius is computed before
// b2_linearSlop is set, leaving it NaN. That gives every polygon a NaN collision
// skin so the solver never converges (steps take seconds and positions blow up to
// NaN). Restore the correct value before any shape is created.
(function(){
  var S = Box2D.Common.b2Settings;
  if(isNaN(S.b2_polygonRadius)) S.b2_polygonRadius = 2.0 * S.b2_linearSlop;
})();

var world, ball, leftFlipper, rightFlipper;
var score = 0, multiplier = 1, jackpot = 0;
var circleBumperScore = CIRCLE_BUMPER_START_SCORE, routerLevel = 0, bumperLevelButtons = 0;
var ballInGame = false, gameStarted = false;
var onPlatform = true;          // ball resting on launch platform
var charge = 0, charging = false;
var keyLeft = false, keyRight = false, keyUp = false, keyDown = false;
var returnFlipperOpenFrames = 0;
var debugMode = false;
var paused = false;
var settingsOpen = false, pausedBeforeSettings = false;
var gateToggleQueue = [];       // deferred SetActive() for one-way gate walls

//// ---- camera (matches original CGame.updateCamera) ----
// Renders a VIEW_W x VIEW_H window of the 1152x1920 table at 1:1, centred on the
// ball and lerped, clamped to the table edges (original CGame.updateCamera). A
// smaller window = more zoom; a larger W/H ratio = wider relative to height.
// (Original was 768x1280; tuned a touch wider + zoomed-in here.)
var VIEW_W = 720, VIEW_H = 1000;
var LERP_SLOW = {x:0.01, y:0.01};
var LERP_FOLLOW = {x:0.05, y:0.15};
var cam = {x: TABLE_W-VIEW_W, y: TABLE_H-VIEW_H};   // start over the plunger lane
var lerp = LERP_SLOW;
// plunger visual (animated launcher in the plunger lane, below the ball start)
var plungerY = 0, plungerVel = 0;     // offset from rest (px); + = pulled back/down
// PINBALL letters system (CModuleLetters): arm via the 3 curve buttons, then a lane
// pass lights the next letter; all letters lit = big bonus.
var letterArmed = false, orionCodex = null, letterLights = [], nextLetter = 0, letterBankResetTimer = 0;
var wallJumpers = {left:null, right:null};
var floatingTexts = [];
var sparkles = [];
var bigScoreFx = {t:0, max:60, parts:[], label:"ABOVE AVERAGE!!", subLabel:"", subLabels:[], size:74, subSize:32, labelColor:"#fff600", outline:false, wrap:false, wordLines:false, colorCycle:false};
var bigScoreLastAt = -Infinity;
var recentScoreEvents = [];
var pendingScoreCombo = null;
var channelTrap = null;
var channelDeflectArmed = false;
var channelDeflectSpeed = 56;
var channelDeflectTarget = null;
var lightHitQueue = [];   // group-light contacts this step, resolved to the single closest
var codexEnhanced = {until:0, nextSound:0};
var codexAntiGravity = {until:0, armed:true, suppressed:false};
var codexBarrierBodies = [];
// ENCOURAGEMENTS lives in encouragements.js (1000 daft words), loaded before this file.
function updateCamera(){
  var bx = ball.GetPosition().x*WORLD_SCALE, by = ball.GetPosition().y*WORLD_SCALE;
  var tx = Math.max(0, Math.min(TABLE_W-VIEW_W, bx - VIEW_W/2));
  var ty = Math.max(0, Math.min(TABLE_H-VIEW_H, by - VIEW_H/2));
  cam.x += (tx-cam.x)*lerp.x;
  cam.y += (ty-cam.y)*lerp.y;
}

//// ---- audio (original sounds/*.mp3, played via HTML5 Audio) ----
var SOUNDS = {};
["bumper","flipper","gate","toggle","launch","ball_out","start_game",
 "pinball_button_on","pinball_button_off","jumper","in_hole","out_hole",
 "letter","game_over","click","all_lights_on_1","all_letters_complete"].forEach(function(n){
  var a = new Audio("sounds/"+n+".mp3"); a.preload = "auto"; SOUNDS[n] = a;
});
var REWARD_COUNT = 10;
for(var ri=1; ri<=REWARD_COUNT; ri++){
  var rn = "reward_"+ri; var ra = new Audio("sounds/"+rn+".mp3"); ra.preload = "auto"; SOUNDS[rn] = ra;
}
function playSound(name, vol){
  var s = SOUNDS[name]; if(!s) return;
  try { var c = s.cloneNode(); c.volume = (vol==null?1:vol); c.play().catch(function(){}); } catch(e){}
}
// Play a sound but skip it if the same one fired less than minMs ago — avoids the
// machine-gun effect when the ball rattles quickly between bumpers.
var soundLastPlayed = {};
function playSoundThrottled(name, minMs, vol){
  var now = (typeof performance !== "undefined" ? performance.now() : Date.now());
  if(now - (soundLastPlayed[name] || -Infinity) < minMs) return;
  soundLastPlayed[name] = now;
  playSound(name, vol);
}
// random celebratory sound for single-light hits
function playReward(){ playSound("reward_" + (1 + Math.floor(Math.random()*REWARD_COUNT))); }
var audioCtx = null, musicOn = false, musicTimer = null, musicStep = 0, musicNextTime = 0, musicChunk = null;
var musicTrack = 0;
var MUSIC_BPM = 132, MUSIC_STEP = 60 / MUSIC_BPM / 2;
var MUSIC_CHUNKS = [
  {m:[72,76,79,83, 81,79,76,72, 71,74,78,81, 79,76,74,71], b:[36,36,43,43, 41,41,48,48, 35,35,42,42, 40,40,47,47], d:"full"},
  {m:[76,79,83,86, 84,83,79,76, 74,78,81,85, 83,81,78,74], b:[41,41,48,48, 40,40,47,47, 38,38,45,45, 43,43,50,50], d:"full"},
  {m:[79,83,86,88, 86,83,81,79, 78,81,85,88, 86,85,81,78], b:[43,43,50,50, 45,45,52,52, 42,42,49,49, 47,47,54,54], d:"busy"},
  {m:[71,74,78,81, 83,81,78,74, 72,76,79,83, 84,83,79,76], b:[35,35,42,42, 43,43,50,50, 36,36,43,43, 41,41,48,48], d:"full"},
  {m:[84,83,81,79, 78,76,74,72, 71,72,74,76, 78,79,81,83], b:[45,45,44,44, 43,43,42,42, 41,41,40,40, 39,39,38,38], d:"break"},
  {m:[72,79,76,83, 79,86,83,88, 71,78,74,81, 76,83,79,86], b:[36,43,36,43, 41,48,41,48, 35,42,35,42, 40,47,40,47], d:"busy"},
  {m:[83,81,79,76, 74,76,79,81, 86,84,83,79, 78,79,83,84], b:[48,48,43,43, 41,41,36,36, 50,50,45,45, 43,43,38,38], d:"light"},
  {m:[76,76,83,81, 79,79,86,83, 74,74,81,79, 78,78,85,81], b:[41,48,41,48, 43,50,43,50, 38,45,38,45, 42,49,42,49], d:"full"},
  {m:[88,86,83,79, 81,79,76,72, 85,83,81,78, 79,78,74,71], b:[48,48,47,47, 45,45,44,44, 43,43,42,42, 41,41,40,40], d:"break"},
  {m:[72,76,79,76, 83,79,76,79, 74,78,81,78, 85,81,78,81], b:[36,36,36,36, 43,43,43,43, 38,38,38,38, 45,45,45,45], d:"light"},
  {m:[79,81,83,86, 83,81,79,76, 74,76,78,81, 78,76,74,71], b:[43,43,41,41, 40,40,38,38, 36,36,35,35, 33,33,35,35], d:"busy"}
];
// Downbeat atmospheric trip-hop, ~90bpm, centred on A minor so any chunk follows any
// other when shuffled. Each chunk = 16 eighth-note steps (2 bars). b = dubby bass,
// m = reverby lead (sparse, with rests for the echo tails), p = sustained maj7 pad
// chords for a yearning feel. Two chunks use the minor line cliché (the descending
// A - G# - G - F# voice): #1 as an inner pad voice, #5 as the chromatic bass.
var TRIP_CHUNKS = [
  // 1 — Am line cliché (inner voice Am, Am(maj7), Am7, Am6); lead echoes it up high
  {b:[33,null,null,null, null,null,33,null, 33,null,null,null, null,null,33,null],
   m:[69,null,null,null, 68,null,null,null, 67,null,null,null, 66,null,null,null],
   p:[{s:0,n:[57,60,64],d:4},{s:4,n:[57,60,64,68],d:4},{s:8,n:[57,60,64,67],d:4},{s:12,n:[57,60,64,66],d:4}], d:"full"},
  // 2 — Fmaj7 (the E natural-7th yearning)
  {b:[29,null,null,null, null,null,29,null, 36,null,null,null, null,null,29,null],
   m:[72,null,76,null, 74,null,null,null, 72,null,69,null, 67,null,69,null],
   p:[{s:0,n:[53,57,60,64],d:8},{s:8,n:[53,57,60,64],d:8}], d:"full"},
  // 3 — Cmaj7 (the B natural-7th)
  {b:[36,null,null,null, null,null,36,null, 31,null,null,null, null,null,36,null],
   m:[71,null,null,79, null,76,null,null, 74,null,72,null, 71,null,null,null],
   p:[{s:0,n:[48,52,55,59],d:16}], d:"full"},
  // 4 — Dm9
  {b:[38,null,null,null, null,null,33,null, 38,null,null,null, null,null,40,null],
   m:[null,null,69,null, 72,null,69,null, null,null,67,null, 65,null,62,null],
   p:[{s:0,n:[50,53,57,60],d:8},{s:8,n:[50,53,57,60,64],d:8}], d:"full"},
  // 5 — Am with descending chromatic bass line cliché (A G# G F#)
  {b:[33,null,null,null, 32,null,null,null, 31,null,null,null, 30,null,null,null],
   m:[76,null,null,null, null,null,74,null, 72,null,null,null, null,null,71,null],
   p:[{s:0,n:[57,60,64],d:16}], d:"full"},
  // 6 — Gmaj7 (bVII, a wistful lift)
  {b:[31,null,null,null, null,null,38,null, 31,null,null,null, null,null,31,null],
   m:[null,74,null,71, 74,null,79,null, 78,null,74,null, 71,null,null,null],
   p:[{s:0,n:[55,59,62,66],d:16}], d:"full"},
  // 7 — Em7 (the melancholy v)
  {b:[40,null,null,null, null,null,35,null, 40,null,null,null, null,null,40,null],
   m:[79,null,76,null, 74,null,null,null, 71,null,74,null, 76,null,null,null],
   p:[{s:0,n:[52,55,59,62],d:16}], d:"full"},
  // 8 — Fmaj7 -> E (the mournful loss cadence; G# leading-tone tension)
  {b:[29,null,null,null, null,null,29,null, 40,null,null,null, null,null,40,null],
   m:[null,null,72,null, 76,null,null,null, null,null,68,null, 71,null,68,null],
   p:[{s:0,n:[53,57,60,64],d:8},{s:8,n:[52,56,59],d:8}], d:"full"},
  // 9 — Am9 break: drums drop, just pad + bass + a sparse low line, very spacious
  {b:[33,null,null,null, null,null,null,null, 33,null,null,null, null,null,null,null],
   m:[null,null,null,null, 64,null,null,null, null,null,null,null, 62,null,null,null],
   p:[{s:0,n:[57,60,64,67,71],d:16}], d:"break"},
  // 10 — Dm7 -> Cmaj7 gentle motion
  {b:[38,null,null,null, 31,null,null,null, 36,null,null,null, null,null,40,null],
   m:[69,null,72,null, 74,null,72,null, 71,null,72,null, 76,null,null,null],
   p:[{s:0,n:[50,53,57,60],d:8},{s:8,n:[48,52,55,59],d:8}], d:"full"}
];
var MUSIC_TRACKS = [
  {name:"chip", bpm:132, chunks:MUSIC_CHUNKS},
  {name:"trip", bpm:90, chunks:TRIP_CHUNKS}
];
function ensureAudioCtx(){
  if(!audioCtx){
    var AC = window.AudioContext || window.webkitAudioContext;
    if(AC) audioCtx = new AC();
  }
  if(audioCtx && audioCtx.state === "suspended") audioCtx.resume().catch(function(){});
  return audioCtx;
}
function noteHz(n){ return 440 * Math.pow(2, (n-69)/12); }
function blip(freq, t, dur, type, vol){
  var ac = ensureAudioCtx(); if(!ac) return;
  var o = ac.createOscillator(), g = ac.createGain();
  o.type = type; o.frequency.setValueAtTime(freq, t);
  g.gain.setValueAtTime(0.0001, t);
  g.gain.exponentialRampToValueAtTime(vol, t+0.01);
  g.gain.exponentialRampToValueAtTime(0.0001, t+dur);
  o.connect(g); g.connect(ac.destination); o.start(t); o.stop(t+dur+0.02);
}
function codexPulseSound(t){
  var ac = ensureAudioCtx(); if(!ac) return;
  var o = ac.createOscillator(), o2 = ac.createOscillator(), g = ac.createGain(), f = ac.createBiquadFilter();
  o.type = "sawtooth"; o2.type = "triangle";
  o.frequency.setValueAtTime(74, t); o.frequency.exponentialRampToValueAtTime(98, t+0.22);
  o2.frequency.setValueAtTime(148, t); o2.frequency.exponentialRampToValueAtTime(196, t+0.22);
  f.type = "lowpass"; f.frequency.setValueAtTime(420, t); f.frequency.exponentialRampToValueAtTime(1100, t+0.14);
  g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(0.28, t+0.03);
  g.gain.exponentialRampToValueAtTime(0.0001, t+0.34);
  o.connect(f); o2.connect(f); f.connect(g); g.connect(ac.destination);
  o.start(t); o2.start(t); o.stop(t+0.38); o2.stop(t+0.38);
}
function noiseHit(t, dur, vol){
  var ac = ensureAudioCtx(); if(!ac) return;
  var len = Math.max(1, Math.floor(ac.sampleRate * dur));
  var buf = ac.createBuffer(1, len, ac.sampleRate), data = buf.getChannelData(0);
  for(var i=0;i<len;i++) data[i] = Math.random()*2-1;
  var src = ac.createBufferSource(), g = ac.createGain(), f = ac.createBiquadFilter();
  f.type = "highpass"; f.frequency.setValueAtTime(3200, t);
  g.gain.setValueAtTime(vol, t); g.gain.exponentialRampToValueAtTime(0.0001, t+dur);
  src.buffer = buf; src.connect(f); f.connect(g); g.connect(ac.destination); src.start(t);
}

// ---- Trip-hop voices on a shared reverb + dub-delay bus (built lazily, reused) ----
// The whole trip track plays through one gain -> compressor master so it stays mellow
// and glued; the chip track and SFX are untouched (they go straight to destination).
var fx = null;
function makeImpulse(ac, dur, decay){
  var len = Math.max(1, Math.floor(ac.sampleRate*dur));
  var buf = ac.createBuffer(2, len, ac.sampleRate);
  for(var ch=0; ch<2; ch++){
    var d = buf.getChannelData(ch);
    for(var i=0;i<len;i++) d[i] = (Math.random()*2-1) * Math.pow(1 - i/len, decay);
  }
  return buf;
}
function ensureFx(){
  var ac = ensureAudioCtx(); if(!ac) return null;
  if(fx && fx.ac === ac) return fx;
  var master = ac.createGain(); master.gain.value = 0.85;
  var comp = ac.createDynamicsCompressor();
  comp.threshold.value = -10; comp.knee.value = 22; comp.ratio.value = 6;
  comp.attack.value = 0.004; comp.release.value = 0.18;
  master.connect(comp); comp.connect(ac.destination);
  var reverb = ac.createConvolver(); reverb.buffer = makeImpulse(ac, 2.8, 2.6);
  var revGain = ac.createGain(); revGain.gain.value = 0.7;
  reverb.connect(revGain); revGain.connect(master);
  var delay = ac.createDelay(2.0); delay.delayTime.value = (60/90)*0.75;   // dotted-8th dub echo
  var fb = ac.createGain(); fb.gain.value = 0.32;
  var delayWet = ac.createGain(); delayWet.gain.value = 0.4;
  delay.connect(fb); fb.connect(delay);                 // feedback
  delay.connect(delayWet); delayWet.connect(master);
  delay.connect(reverb);                                // smear echoes into the reverb
  fx = {ac:ac, master:master, reverb:reverb, delay:delay};
  return fx;
}
function tripKick(t){
  var fxb = ensureFx(); if(!fxb) return; var ac = fxb.ac;
  var o = ac.createOscillator(), g = ac.createGain();
  o.type = "sine";
  o.frequency.setValueAtTime(95, t); o.frequency.exponentialRampToValueAtTime(40, t+0.13);
  g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(0.4, t+0.01);
  g.gain.exponentialRampToValueAtTime(0.0001, t+0.28);
  o.connect(g); g.connect(fxb.master); o.start(t); o.stop(t+0.3);
}
function tripNoise(t, dur, ftype, freq, Q, vol, send){
  var fxb = ensureFx(); if(!fxb) return; var ac = fxb.ac;
  var len = Math.max(1, Math.floor(ac.sampleRate*dur));
  var buf = ac.createBuffer(1, len, ac.sampleRate), dd = buf.getChannelData(0);
  for(var i=0;i<len;i++) dd[i] = Math.random()*2-1;
  var src = ac.createBufferSource(); src.buffer = buf;
  var f = ac.createBiquadFilter(); f.type = ftype; f.frequency.value = freq; if(Q) f.Q.value = Q;
  var g = ac.createGain();
  g.gain.setValueAtTime(vol, t); g.gain.exponentialRampToValueAtTime(0.0001, t+dur);
  src.connect(f); f.connect(g); g.connect(fxb.master);
  if(send){ var s = ac.createGain(); s.gain.value = send; g.connect(s); s.connect(fxb.reverb); }
  src.start(t);
}
function tripSnare(t){ tripNoise(t, 0.18, "bandpass", 1900, 0.8, 0.17, 0.4); }  // dusty, roomy
function tripHat(t, vol){ tripNoise(t, 0.03, "highpass", 7000, 0, vol, 0); }
// One or more detuned osc pairs through a lowpass, with optional reverb/delay sends.
// conf: {t1,t2 wave types, det cents, lp Hz, vol, atk, rel, rev, dly}. Notes are MIDI.
function tripVoice(notes, t, dur, conf){
  var fxb = ensureFx(); if(!fxb) return; var ac = fxb.ac;
  for(var i=0;i<notes.length;i++){
    var freq = noteHz(notes[i]);
    var o = ac.createOscillator(), o2 = ac.createOscillator(), g = ac.createGain(), lp = ac.createBiquadFilter();
    o.type = conf.t1; o.frequency.value = freq;
    o2.type = conf.t2; o2.frequency.value = freq; o2.detune.value = conf.det;
    lp.type = "lowpass"; lp.frequency.value = conf.lp;
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(conf.vol, t+conf.atk);
    if(dur - conf.rel > conf.atk) g.gain.setValueAtTime(conf.vol, t+dur-conf.rel);  // hold
    g.gain.exponentialRampToValueAtTime(0.0001, t+dur);
    o.connect(lp); o2.connect(lp); lp.connect(g); g.connect(fxb.master);
    if(conf.rev){ var rv = ac.createGain(); rv.gain.value = conf.rev; g.connect(rv); rv.connect(fxb.reverb); }
    if(conf.dly){ var dl = ac.createGain(); dl.gain.value = conf.dly; g.connect(dl); dl.connect(fxb.delay); }
    o.start(t); o2.start(t); o.stop(t+dur+0.1); o2.stop(t+dur+0.1);
  }
}
function tripBass(n, t, dur){ tripVoice([n], t, dur, {t1:"sine", t2:"triangle", det:-6, lp:260, vol:0.42, atk:0.03, rel:0.12, rev:0, dly:0.12}); }
function tripLead(n, t, dur){ tripVoice([n], t, dur, {t1:"triangle", t2:"sine", det:4, lp:2600, vol:0.14, atk:0.02, rel:0.1, rev:0.5, dly:0.4}); }
function tripPad(notes, t, dur){ tripVoice(notes, t, dur, {t1:"triangle", t2:"sine", det:-7, lp:1600, vol:0.045, atk:0.35, rel:0.7, rev:0.8, dly:0}); }
function currentMusicTrack(){ return MUSIC_TRACKS[musicTrack]; }
function updateMusicStep(){ MUSIC_STEP = 60 / currentMusicTrack().bpm / 2; }
function pickMusicChunk(){ var chunks = currentMusicTrack().chunks; return chunks[Math.floor(Math.random()*chunks.length)]; }
function scheduleTripHopStep(t, s){
  var c = musicChunk, d = c.d, half = MUSIC_STEP/2;
  // halftime groove: kick on the 1 (+ a syncopated push), dusty snare on the 3
  if(d !== "break"){
    if(s === 0 || s === 8 || s === 11) tripKick(t);
    if(s === 4 || s === 12) tripSnare(t);
    if(s === 2 || s === 6 || s === 10 || s === 14) tripHat(t+half, 0.03);   // 16th shuffle
  }
  tripHat(t, s % 2 === 0 ? 0.055 : 0.035);
  if(c.b[s] != null) tripBass(c.b[s], t, MUSIC_STEP*1.6);
  if(c.m[s] != null) tripLead(c.m[s], t, MUSIC_STEP*1.8);
  if(c.p){ for(var i=0;i<c.p.length;i++){ if(c.p[i].s === s) tripPad(c.p[i].n, t, c.p[i].d*MUSIC_STEP); } }
}
function scheduleMusicStep(t){
  var s = musicStep % 16;
  if(s === 0 || !musicChunk) musicChunk = pickMusicChunk();
  if(currentMusicTrack().name === "trip"){
    scheduleTripHopStep(t, s); musicStep++; return;
  }
  var d = musicChunk.d;
  if(d !== "break" && s % 4 === 0) blip(55, t, 0.08, "sine", 0.28);       // kick
  if(d === "busy" && s === 8) blip(82, t, 0.05, "sine", 0.18);
  if(d !== "break" && (s === 4 || s === 12)) noiseHit(t, 0.055, 0.16);     // snare
  if((d === "busy" && s % 2 === 1) || (d === "full" && (s === 3 || s === 7 || s === 11 || s === 15))) noiseHit(t, 0.018, 0.07);
  if(s % 2 === 0 || d === "busy") blip(noteHz(musicChunk.b[s]), t, 0.16, "square", d === "break" ? 0.18 : 0.16);
  if(d !== "light" || s % 2 === 0) blip(noteHz(musicChunk.m[s]), t, 0.09, "square", 0.12);
  musicStep++;
}
function musicTick(){
  var ac = ensureAudioCtx(); if(!ac) return;
  while(musicNextTime < ac.currentTime + 0.25){ scheduleMusicStep(musicNextTime); musicNextTime += MUSIC_STEP; }
}
function startMusic(){
  var ac = ensureAudioCtx(); if(!ac) return;
  updateMusicStep();
  musicOn = true; musicStep = 0; musicChunk = null; musicNextTime = ac.currentTime + 0.04;
  if(musicTimer) clearInterval(musicTimer);
  musicTimer = setInterval(musicTick, 80); musicTick();
}
function stopMusic(){
  musicOn = false;
  if(musicTimer) clearInterval(musicTimer);
  musicTimer = null;
}
function toggleMusic(){ if(musicOn) stopMusic(); else startMusic(); }
function switchMusicTrack(){
  musicTrack = (musicTrack + 1) % MUSIC_TRACKS.length;
  musicStep = 0; musicChunk = null; updateMusicStep();
  var ac = ensureAudioCtx(); if(ac) musicNextTime = ac.currentTime + 0.04;
  if(musicOn) musicTick();
}
var flashTimers = [];           // visual hit flashes {x,y,r,t,col}

//// ---- builders ----
function addEdge(v1, v2, restitution, userData){
  var fd = new b2FixtureDef;
  fd.density = 1; fd.friction = GENERAL_FRICTION; fd.restitution = restitution; fd.userData = userData;
  fd.shape = new b2PolygonShape;
  fd.shape.SetAsEdge(new b2Vec2(v1.x/WORLD_SCALE, v1.y/WORLD_SCALE),
                     new b2Vec2(v2.x/WORLD_SCALE, v2.y/WORLD_SCALE));
  var bd = new b2BodyDef; bd.type = b2Body.b2_staticBody;
  return world.CreateBody(bd).CreateFixture(fd).GetBody();
}
// Solid wall polygon, exactly as the original CTable does (full outline, up to 14
// vertices — this engine handles them fine once b2_polygonRadius is valid). Box2D
// requires CCW winding (positive signed area), else the fixture gets negative mass
// and inverted collision normals, so we enforce it.
function addFilledPoly(pts, restitution){
  // Drop coincident consecutive vertices (incl. an explicitly closed loop whose
  // last point repeats the first); Box2D asserts on any zero-length polygon edge.
  var clean = [];
  for(var k=0;k<pts.length;k++){
    var p = pts[k], q = clean.length ? clean[clean.length-1] : pts[pts.length-1];
    if(p.x !== q.x || p.y !== q.y) clean.push(p);
  }
  if(clean.length < 3){ skipBoardEntity({type:"wall"}, "solid polygon needs >=3 distinct vertices"); return; }
  pts = clean;
  var area = 0;
  for(var i=0;i<pts.length;i++){ var a=pts[i], b=pts[(i+1)%pts.length]; area += a.x*b.y - b.x*a.y; }
  var ring = area < 0 ? pts.slice().reverse() : pts;
  var fd = new b2FixtureDef;
  fd.density = 1; fd.friction = GENERAL_FRICTION; fd.restitution = restitution;
  fd.shape = new b2PolygonShape;
  var vs = ring.map(function(p){ return new b2Vec2(p.x/WORLD_SCALE, p.y/WORLD_SCALE); });
  fd.shape.SetAsArray(vs, vs.length);
  var bd = new b2BodyDef; bd.type = b2Body.b2_staticBody;
  world.CreateBody(bd).CreateFixture(fd);
}
function addStaticCircle(rad, x, y, restitution, userData){
  var fd = new b2FixtureDef;
  fd.density = 0; fd.friction = 0; fd.restitution = restitution; fd.userData = userData;
  fd.shape = new b2CircleShape(rad/WORLD_SCALE);
  var bd = new b2BodyDef; bd.type = b2Body.b2_staticBody;
  bd.position.Set(x/WORLD_SCALE, y/WORLD_SCALE);
  return world.CreateBody(bd).CreateFixture(fd);
}
function addButton(w, h, x, y, angle, restitution, userData){
  var fd = new b2FixtureDef;
  fd.density = 0; fd.friction = 0; fd.restitution = restitution; fd.userData = userData;
  fd.shape = new b2PolygonShape;
  fd.shape.SetAsBox((w/2)/WORLD_SCALE, (h/2)/WORLD_SCALE);
  var bd = new b2BodyDef; bd.type = b2Body.b2_staticBody;
  bd.position.Set(x/WORLD_SCALE, y/WORLD_SCALE);
  bd.angle = angle*Math.PI/180;
  var body = world.CreateBody(bd); body.CreateFixture(fd);
  return body;
}
// One-way gate (replicates the original CGateSystem): a solid wall plus sensor rings.
// An "opener" on the allowed-approach side disables the wall so the ball passes; a
// "closer" on the far side re-enables it, so the ball can exit but not re-enter.
// Body active-state can't be changed mid-step, so toggles are queued (see step()).
function addOneWayGate(gx, gy, gw, gh, gangle, openers, closers, onPass){
  var wall = addButton(gw, gh, gx, gy, gangle, 0.4, {type:"gatewall"});  // solid, rest 0.4
  var gate = { wall: wall, onPass: onPass };
  openers.forEach(function(p){
    var f = addStaticCircle(12, gx+p[0], gy+p[1], 0, {type:"opener", gate:gate});
    f.SetSensor(true);
  });
  closers.forEach(function(p){
    var f = addStaticCircle(12, gx+p[0], gy+p[1], 0, {type:"closer", gate:gate});
    f.SetSensor(true);
  });
  return gate;
}
function queueGate(body, active){ gateToggleQueue.push({body:body, active:active}); }

//// ---- light indicators (replicates the original CLightIndicator groups) ----
// A light turns ON and stays on when the ball hits its sensor; completing all the
// lights of a group fires a reward. Positions are taken from the original modules.
var lights = [];                 // all lights, for rendering
var lightGroups = {};            // name -> {lights:[], onComplete, sound}
function addLight(x, y, r, col, shape){
  var L = {x:x, y:y, r:r||13, on:false, flash:0, col:col||"#ffd43b", shape:shape||"circle", angle:0};
  lights.push(L); return L;
}
function defGroup(name, onComplete, sound){ lightGroups[name] = {lights:[], onComplete:onComplete, sound:sound||"toggle", complete:false, cooldownUntil:0}; }
// A light hooked to a physics sensor: lights on contact, checks its group.
// Args mirror addButton: (w, h, x, y, angle, group, light).
// Unit normal of a light button's face: perpendicular to its long dimension, so
// the ball's velocity component along it measures how steeply it strikes the face
// (a ball sliding along the face has ~0 component and won't trigger the light).
function lightFaceNormal(w, h, angle){
  var t = angle*Math.PI/180;
  return h >= w ? {x:Math.cos(t), y:Math.sin(t)} : {x:-Math.sin(t), y:Math.cos(t)};
}
function addLightButton(w, h, x, y, angle, group, light){
  light.angle = angle;
  if(group){ lightGroups[group].lights.push(light); }
  var b = addButton(w, h, x, y, angle, 0, {type:"light", group:group, light:light, normal:lightFaceNormal(w,h,angle)});
  b.GetFixtureList().SetSensor(true);
  return b;
}
var LIGHT_TIE_BAND = 4;   // px²: candidates this close to the nearest count as equidistant
// From the queued candidates pick the light the ball is closest to; if two are
// (near-)equidistant, pick a random one of them rather than lighting none.
function pickNearest(cands){
  if(!cands.length) return null;
  var minD = Infinity, i;
  for(i=0;i<cands.length;i++) if(cands[i].d < minD) minD = cands[i].d;
  var tied = [];
  for(i=0;i<cands.length;i++) if(cands[i].d - minD <= LIGHT_TIE_BAND) tied.push(cands[i]);
  return tied[Math.floor(Math.random()*tied.length)];
}
function resolveLightHits(){
  if(!lightHitQueue.length) return;
  var bp = ball.GetPosition(), bx = bp.x*WORLD_SCALE, by = bp.y*WORLD_SCALE;
  var cands = [];
  var seen = [];
  lightHitQueue.forEach(function(ud){
    var L = ud.light, g = ud.group && lightGroups[ud.group];
    if(ud.group === "curve" && codexEnhancedActive()) return;
    if(g && nowMs() < g.cooldownUntil) return;
    if(L.on && !(g && g.complete)) return;           // already on (and group not full): nothing to do
    if(seen.indexOf(L) >= 0) return;
    seen.push(L);
    var dx = L.x-bx, dy = L.y-by;
    cands.push({ud:ud, d:dx*dx + dy*dy});
  });
  var pick = pickNearest(cands);
  if(pick) hitLight(pick.ud);
  lightHitQueue.length = 0;
}
function hitLight(ud){
  var L = ud.light;
  var g = ud.group && lightGroups[ud.group];
  if(g && g.complete){            // group fully lit -> this qualifying hit clears it
    if(ud.group === "curve") return;
    setGroupLit(g, false); g.complete = false; playSound("toggle");
    announceReset(L.x, L.y); return;
  }
  if(L.on) return;
  L.on = true; L.flash = 1;
  if(g) g.cooldownUntil = nowMs() + LIGHT_BANK_COOLDOWN_MS;
  addScore(SINGLE_BUTTON_SCORE * multiplier, L.x, L.y);
  encourage(L.x, L.y - 20);
  playReward();
  if(g && g.lights.every(function(x){ return x.on; })){ g.complete = true; g.onComplete(g); }
}
function setGroupLit(g, on){ g.lights.forEach(function(L){ L.on = on; if(on) L.flash = 1; }); }
function addBonusLightButton(w, h, x, y, angle, light, scoreValue, trap){
  light.angle = angle;
  var b = addButton(w, h, x, y, angle, 0, {type:"bonuslight", light:light, scoreValue:scoreValue, normal:lightFaceNormal(w,h,angle), trap:trap});
  b.GetFixtureList().SetSensor(true);
  return b;
}
function hitBonusLight(ud){
  var L = ud.light;
  if(L.on) return;
  L.on = true; L.flash = 1;
  addScore(ud.scoreValue * multiplier, L.x, L.y);
  encourage(L.x, L.y - 20);
  playSound("pinball_button_on");
  if(ud.trap) startChannelTrap(ud.trap, L);
}

// Passing the D1 curve summit while armed lights the next PINBALL letter.
function setCodexArmed(on){
  if(orionCodex){ orionCodex.on = on; orionCodex.flash = on ? 1 : 0; }
}
function codexEnhancedActive(){ return nowMs() < codexEnhanced.until; }
function codexVelocityMult(){ return codexEnhancedActive() ? CODEX_VELOCITY_MULT : 1; }
function codexFlipperMult(){ return codexEnhancedActive() ? CODEX_FLIPPER_MULT : 1; }
function startCodexEnhancedMode(x, y){
  var now = nowMs();
  if(now < codexEnhanced.until) return;
  codexEnhanced.until = now + CODEX_ENHANCED_MS;
  codexEnhanced.nextSound = 0;
  flash(x, y, 120, "#9b6bff");
  addFloatText("CODEX OVERDRIVE", x, y - 70, "#d780ff", 110, 38, true);
}
function codexAntiGravityActive(){ return codexEnhancedActive() && nowMs() < codexAntiGravity.until; }
function triggerCodexAntiGravity(x, y){
  if(!codexEnhancedActive() || !codexAntiGravity.armed || codexAntiGravityActive()) return;
  if(Math.random() >= CODEX_ANTIGRAVITY_CHANCE) return;
  var until = nowMs() + CODEX_ANTIGRAVITY_MS;
  codexAntiGravity.until = until;
  if(codexEnhanced.until < until) codexEnhanced.until = until;
  codexAntiGravity.armed = false;
  codexAntiGravity.suppressed = false;
  flash(x, y, 150, "#65d46e");
  logEvent("ANTI-GRAVITY", "#65d46e");
}
function armCodexAntiGravity(){
  if(!codexAntiGravityActive()) codexAntiGravity.armed = true;
}
function addCodexAntiGravityBarrier(){
  var pts = [{x:225,y:950}, {x:300,y:1000}, {x:430,y:930}, {x:585,y:850}];
  codexBarrierBodies.length = 0;
  for(var i=0; i<pts.length-1; i++){
    var b = addEdge(pts[i], pts[i+1], 0.2, {type:"codexbarrier"});
    b.SetActive(false);
    codexBarrierBodies.push(b);
  }
}
function updateCodexAntiGravityBarrier(){
  var active = codexAntiGravityActive();
  for(var i=0; i<codexBarrierBodies.length; i++){
    if(codexBarrierBodies[i].IsActive() !== active) codexBarrierBodies[i].SetActive(active);
  }
}
function letterLanePass(){
  if(!letterArmed || nextLetter >= letterLights.length) return;
  addScore(ROUTER_GATE_SCORE[routerLevel] * multiplier, 224, 210);
  routerLevel = Math.min(routerLevel+1, ROUTER_GATE_SCORE.length-1);
  playSound("jumper");
  var L = letterLights[nextLetter]; L.on = true; L.flash = 1; nextLetter++;
  letterArmed = false; setCodexArmed(false);
  if(lightGroups.curve){ setGroupLit(lightGroups.curve, false); lightGroups.curve.complete = false; }
  addScore(SINGLE_LETTERS_LIT_SCORE * multiplier, L.x, L.y);
  encourage(L.x, L.y - 20);
  playSound("letter");
  startCodexEnhancedMode(L.x, L.y);
  if(nextLetter >= letterLights.length){   // all 7 lit -> missile launch reward
    var factor = multiplier / 2;
    if(factor < 1) factor = multiplier;
    var missileScore = Math.round(score * 0.05 * factor);
    addScore(missileScore, L.x, L.y);
    playSound("all_letters_complete");
    playSound("launch", 0.85);
    triggerBigScore("MISSILE LAUNCHED!", {
      force:true,
      subLabels:["You've doomed humanity! You monster!", missileScore.toLocaleString() + " points!!"],
      outline:true,
      wrap:true,
      wordLines:true,
      colorCycle:true,
      count:420,
      frames:300,
      size:96,
      subSize:34,
      spread:260,
      maxSpd:18
    });
    letterBankResetTimer = 300;
    letterLights.forEach(function(LL){ LL.on = true; LL.flash = 1; });
  } else {
    announceBank("ORION CODEX TRIGGERED");   // armed curve pass lit the next letter
  }
}
function updateCodexEnhanced(){
  if(!codexEnhancedActive()) return;
  var v = ball.GetLinearVelocity(), speed = Math.sqrt(v.x*v.x + v.y*v.y);
  if(speed > 0.01 && speed < CODEX_MAX_BALL_SPEED) ball.SetLinearVelocity(new b2Vec2(v.x*CODEX_SPEED_BOOST, v.y*CODEX_SPEED_BOOST));
  if(codexAntiGravityActive()){
    var py = ball.GetPosition().y * WORLD_SCALE;
    if(py < CODEX_ANTIGRAVITY_SUPPRESS_Y) codexAntiGravity.suppressed = true;
    else if(py >= CODEX_ANTIGRAVITY_RESUME_Y) codexAntiGravity.suppressed = false;
    var targetGravity = codexAntiGravity.suppressed ? 1 : CODEX_ANTIGRAVITY_MULT;
    ball.ApplyForce(new b2Vec2(0, ball.GetMass()*GRAVITY*(targetGravity - 1)), ball.GetWorldCenter());
  } else {
    ball.ApplyForce(new b2Vec2(0, ball.GetMass()*GRAVITY*CODEX_EXTRA_GRAVITY), ball.GetWorldCenter());
  }
  var ac = ensureAudioCtx();
  if(ac && ac.currentTime >= codexEnhanced.nextSound){
    codexPulseSound(ac.currentTime);
    codexEnhanced.nextSound = ac.currentTime + 0.42;
  }
}
function updateLetterBankReset(){
  if(letterBankResetTimer <= 0) return;
  letterBankResetTimer--;
  var lit = Math.floor(letterBankResetTimer / 15) % 2 === 0;
  letterLights.forEach(function(L){ L.on = lit; L.flash = lit ? 1 : 0; });
  if(letterBankResetTimer <= 0){
    letterLights.forEach(function(L){ L.on = false; L.flash = 0; });
    nextLetter = 0;
  }
}
function triggerLetterBankCompleteDebug(){
  if(!gameStarted) return;
  letterBankResetTimer = 0;
  for(var i=0; i<letterLights.length; i++){
    letterLights[i].on = true;
    letterLights[i].flash = 1;
  }
  nextLetter = Math.max(0, letterLights.length - 1);
  letterArmed = true;
  letterLanePass();
}
function addBall(){
  var fd = new b2FixtureDef;
  fd.density = 0.1; fd.friction = 0.7; fd.restitution = 0;
  fd.userData = {id:"ball"};
  fd.shape = new b2CircleShape(BALL_RADIUS/WORLD_SCALE);
  var bd = new b2BodyDef;
  bd.type = b2Body.b2_dynamicBody; bd.bullet = true; bd.allowSleep = false;
  bd.position.Set(BALL_STARTPOS.x/WORLD_SCALE, BALL_STARTPOS.y/WORLD_SCALE);
  return world.CreateBody(bd).CreateFixture(fd).GetBody();
}
function addFlipper(pts, x, y, isLeft){
  // body
  var fd = new b2FixtureDef;
  fd.density = 1; fd.friction = 0; fd.restitution = GENERAL_RESTITUTION;
  fd.userData = {type:"flipper"};
  fd.shape = new b2PolygonShape;
  var raw = pts.map(function(p){ return {x:(p.x*(isLeft?-1:1)), y:p.y}; });
  // Box2D requires CCW winding (positive signed area). The left flipper mirrors the
  // outline (negate x), which flips winding to CW and yields negative mass+inertia —
  // that gives the motor an infinite effective mass and the flipper explodes. Enforce
  // CCW so both flippers get valid mass.
  var area = 0;
  for(var i=0;i<raw.length;i++){ var a=raw[i], b=raw[(i+1)%raw.length]; area += a.x*b.y - b.x*a.y; }
  if(area < 0) raw.reverse();
  var vs = raw.map(function(p){ return new b2Vec2(p.x/WORLD_SCALE, p.y/WORLD_SCALE); });
  fd.shape.SetAsArray(vs, vs.length);
  var bd = new b2BodyDef; bd.type = b2Body.b2_dynamicBody;
  bd.position.Set(x/WORLD_SCALE, (y+28)/WORLD_SCALE);
  var body = world.CreateBody(bd); body.CreateFixture(fd);
  // pivot
  var pfd = new b2FixtureDef;
  pfd.density = 1; pfd.friction = 0; pfd.restitution = GENERAL_RESTITUTION;
  pfd.shape = new b2CircleShape(11/WORLD_SCALE);
  var pbd = new b2BodyDef; pbd.type = b2Body.b2_staticBody;
  pbd.position.Set(x/WORLD_SCALE, y/WORLD_SCALE);
  var pivot = world.CreateBody(pbd); pivot.CreateFixture(pfd);
  // joint
  var jd = new b2RevoluteJointDef;
  jd.Initialize(body, pivot, pivot.GetWorldCenter());
  if(isLeft){ jd.lowerAngle = 5*Math.PI/180; jd.upperAngle = 50*Math.PI/180; }
  else      { jd.lowerAngle = -50*Math.PI/180; jd.upperAngle = -5*Math.PI/180; }
  jd.enableLimit = true; jd.maxMotorTorque = 1000; jd.enableMotor = true;
  var joint = world.CreateJoint(jd); joint.EnableMotor(true);
  return joint;
}

//// ---- contact handling ----
function ballBodyFrom(contact){
  var a = contact.GetFixtureA().GetUserData(), b = contact.GetFixtureB().GetUserData();
  if(a && a.id === "ball") return contact.GetFixtureA().GetBody();
  if(b && b.id === "ball") return contact.GetFixtureB().GetBody();
  return null;
}
function popBumperHit(idx, contact){
  var b = ballBodyFrom(contact); if(!b) return;
  triggerCodexAntiGravity(idx.x, idx.y);
  var wm = new b2WorldManifold(); contact.GetWorldManifold(wm);
  var n = wm.m_normal;
  b.SetLinearVelocity(new b2Vec2(0,0)); b.SetAngularVelocity(0);
  var imp = new b2Vec2(n.x, n.y); imp.Multiply(-b.GetMass()*14);
  imp.Multiply(codexVelocityMult());
  b.ApplyImpulse(imp, b.GetPosition());
  addScore(circleBumperScore, idx.x, idx.y);
  flash(idx.x, idx.y, 70, "#ff3df0");
  playSoundThrottled("bumper", 90);
}
function slingHit(dir, contact){           // dir: -1 left, +1 right
  var b = ballBodyFrom(contact); if(!b) return;
  var n = new b2Vec2(0.4*dir, 0.5);
  b.SetLinearVelocity(new b2Vec2(0,0)); b.SetAngularVelocity(0);
  n.Multiply(-b.GetMass()*20);
  n.Multiply(codexVelocityMult());
  b.ApplyImpulse(n, b.GetPosition());
  addScore(SINGLE_BUTTON_SCORE * multiplier, 540 + dir*284, 1460);
  playSound("bumper");
}
function wallJumperHit(ud, contact){
  var b = ballBodyFrom(contact); if(!b) return;

  var dir = ud.side === "left" ? 1 : -1;
  var v = b.GetLinearVelocity();
  var speed = Math.sqrt(v.x*v.x + v.y*v.y);
  var boost = codexVelocityMult();
  b.SetLinearVelocity(new b2Vec2(dir * Math.max(4.25, Math.min(5.75, speed*0.475)) * boost, v.y * boost));
  b.SetAngularVelocity(0);

  var state = wallJumpers[ud.side];
  if(!state) return;

  // panel fully lit -> this qualifying hit clears it
  if(state.complete){
    state.complete = false;
    state.lights.forEach(function(L){ L.on = false; L.flash = 0; });
    playSound("toggle");
    announceReset(ud.x, ud.y);
    return;
  }

  // light the wall light the ball is closest to (a direct hit); if two are
  // (near-)equidistant, pick a random one of them.
  if(nowMs() < (state.cooldownUntil || 0)) return;
  var bp = b.GetPosition(), bx = bp.x*WORLD_SCALE, by = bp.y*WORLD_SCALE;
  var cands = [];
  state.lights.forEach(function(L){
    if(L.on) return;
    var dx = L.x-bx, dy = L.y-by; cands.push({L:L, d:dx*dx + dy*dy});
  });
  var pick = pickNearest(cands);
  if(pick){
    var best = pick.L;
    best.on = true; best.flash = 1;
    state.cooldownUntil = nowMs() + LIGHT_BANK_COOLDOWN_MS;
    addScore(JUMPER_SCORE * multiplier, ud.x, ud.y);
    flash(ud.x, ud.y, 55, "#ffd43b");
    encourage(best.x, best.y - 20); playReward();
  }

  if(state.lights.every(function(L){ return L.on; })){
    state.complete = true;
    increaseMultiplier();
    addScore(ALL_JUMPER_BUTTONS_SCORE * multiplier, ud.x, ud.y);
    announceBank("MULTIPLIER", (ud.side === "left" ? "W1" : "W2") + " BANK COMPLETE");
    playSound("all_lights_on_1");
  }
}
function channelDeflectHit(){
  if(!channelDeflectArmed) return;
  var v = ball.GetLinearVelocity();
  var speed = Math.max(channelDeflectSpeed, Math.sqrt(v.x*v.x + v.y*v.y)) * codexVelocityMult();
  var a = (220 + Math.random()*100) * Math.PI / 180;
  ball.SetLinearVelocity(new b2Vec2(Math.sin(a)*speed, -Math.cos(a)*speed));
  channelDeflectArmed = false;
  channelDeflectTarget = null;
}
function updateChannelDeflect(px, py){
  if(!channelDeflectArmed || !channelDeflectTarget) return;
  var dx = px - channelDeflectTarget.x, dy = py - channelDeflectTarget.y;
  if(dx*dx + dy*dy <= channelDeflectTarget.r*channelDeflectTarget.r || py >= channelDeflectTarget.y){
    channelDeflectHit();
  }
}
function setupContacts(){
  var L = new Box2D.Dynamics.b2ContactListener;
  L.BeginContact = function(c){
    [c.GetFixtureA().GetUserData(), c.GetFixtureB().GetUserData()].forEach(function(ud){
      if(!ud) return;
      if(ud.type === "pop")  popBumperHit(ud, c);
      if(ud.type === "flipper" && ballBodyFrom(c)) armCodexAntiGravity();
      if(ud.type === "sling") slingHit(ud.dir, c);
      if(ud.type === "walljumper") wallJumperHit(ud, c);
      if(ud.type === "opener"){ queueGate(ud.gate.wall, false); if(ud.gate.onPass) ud.gate.onPass(); playSound("gate"); }
      if(ud.type === "closer"){ queueGate(ud.gate.wall, true); }
      if(ud.type === "checkpoint"){ addScore(SINGLE_BUTTON_SCORE*multiplier, ud.x, ud.y); playSound("toggle"); }
      if(ud.type === "light"){ lightHitQueue.push(ud); }
      if(ud.type === "bonuslight"){ hitBonusLight(ud); }
      if(ud.type === "letterlane") letterLanePass();
      if(ud.type === "channeldeflect") channelDeflectHit();
    });
  };
  L.PreSolve = function(c){
    var a = c.GetFixtureA().GetUserData(), b = c.GetFixtureB().GetUserData();
    if(!((a && a.type === "codexbarrier") || (b && b.type === "codexbarrier"))) return;
    var bb = ballBodyFrom(c); if(!bb) return;
    if(bb.GetLinearVelocity().y > 0) c.SetEnabled(false);
  };
  L.EndContact = function(c){};
  world.SetContactListener(L);
}

//// ---- score ----
function nowMs(){ return (typeof performance !== "undefined" ? performance.now() : Date.now()); }
function recentScoreMean(){
  if(!recentScoreEvents.length) return 0;
  var total = 0;
  for(var i=0;i<recentScoreEvents.length;i++) total += recentScoreEvents[i];
  return total / recentScoreEvents.length;
}
function bigScoreThreshold(mean){ return recentScoreEvents.length >= BIG_SCORE_MIN_SAMPLES ? mean * BIG_SCORE_MULTIPLE : BIG_SCORE_THRESHOLD; }
function recordScoreEvent(n){
  recentScoreEvents.push(n);
  if(recentScoreEvents.length > BIG_SCORE_RECENT_COUNT) recentScoreEvents.shift();
}
function maybeTriggerBigScoreForValue(n, mean){
  if(n >= bigScoreThreshold(mean)) triggerBigScore();
}
function finalizeScoreCombo(force){
  if(!pendingScoreCombo) return;
  var now = nowMs();
  if(!force && now - pendingScoreCombo.lastAt <= BIG_SCORE_COMBO_MS) return;
  if(pendingScoreCombo.count > 1) maybeTriggerBigScoreForValue(pendingScoreCombo.total, recentScoreMean());
  pendingScoreCombo = null;
}
function addToScoreCombo(n, at){
  if(pendingScoreCombo && at - pendingScoreCombo.lastAt > BIG_SCORE_COMBO_MS) finalizeScoreCombo(true);
  if(!pendingScoreCombo) pendingScoreCombo = {total:n, count:1, lastAt:at};
  else {
    pendingScoreCombo.total += n;
    pendingScoreCombo.count++;
    pendingScoreCombo.lastAt = at;
  }
}
function addScore(n, x, y){
  n = Math.round(n);
  var at = nowMs();
  maybeTriggerBigScoreForValue(n, recentScoreMean());
  recordScoreEvent(n);
  addToScoreCombo(n, at);
  score += n;
  jackpot += Math.floor(n*2);
  if(x != null && y != null) addFloatText("+" + n.toLocaleString(), x, y, "#fff600", 60, 42);
}
function increaseMultiplier(){ multiplier = Math.round((multiplier + MULTIPLIER_STEP) * 10) / 10; }
function multiplierText(){ return multiplier.toFixed(1); }
function flash(x,y,r,col){ flashTimers.push({x:x,y:y,r:r,t:1,col:col}); }
// logCol (optional) sets the left-panel colour independently of the on-screen colour
// — used to give an associated headline + sub-line a single shared log colour.
function addFloatText(text, x, y, col, frames, size, fx, logCol){ floatingTexts.push({text:text, x:x, y:y, col:col||"#fff600", t:frames||60, max:frames||60, size:size||72, fx:fx||false, phase:Math.random()*Math.PI*2}); logEvent(text, logCol || col || "#fff600"); }
// Bright candy palette for encouragement words
var ENCOURAGE_COLORS = ["#ff9ed8", "#fff27a", "#a8ff8f", "#ffb347", "#7afcff", "#ffa6f0", "#b69bff"];
var ENCOURAGE_MIN_DIST = 110;   // keep encouragement words from overlapping
function encourage(x, y){
  var dx = (Math.random()*2-1) * 60;
  var ex = x + dx, ey = y - 45;
  // if too close to an existing encouragement word, skip it rather than overlap
  for(var i=0;i<floatingTexts.length;i++){
    var ft = floatingTexts[i]; if(!ft.fx) continue;
    var ddx = ft.x-ex, ddy = ft.y-ey;
    if(ddx*ddx + ddy*ddy < ENCOURAGE_MIN_DIST*ENCOURAGE_MIN_DIST) return;
  }
  var col = ENCOURAGE_COLORS[Math.floor(Math.random()*ENCOURAGE_COLORS.length)];
  addFloatText(ENCOURAGEMENTS[Math.floor(Math.random()*ENCOURAGEMENTS.length)], ex, ey, col, 60, 42, true);
  spawnSparkles(ex, ey, 30);
}
function spawnSparkles(x, y, n){
  for(var i=0;i<n;i++){
    var ang = Math.random()*Math.PI*2, spd = 3 + Math.random()*7;
    sparkles.push({
      x:x, y:y, vx:Math.cos(ang)*spd, vy:Math.sin(ang)*spd - 2,
      t:1, decay:0.012 + Math.random()*0.025, r:2 + Math.random()*4,
      col:ENCOURAGE_COLORS[Math.floor(Math.random()*ENCOURAGE_COLORS.length)]
    });
  }
}
function drawSparkles(){
  ctx.save();
  for(var i=sparkles.length-1;i>=0;i--){
    var s = sparkles[i];
    s.x += s.vx; s.y += s.vy; s.vy += 0.12; s.t -= s.decay;
    if(s.t <= 0){ sparkles.splice(i,1); continue; }
    ctx.globalAlpha = Math.max(0, s.t);
    ctx.fillStyle = s.col;
    ctx.shadowColor = s.col; ctx.shadowBlur = 8;
    ctx.beginPath(); ctx.arc(s.x, s.y, s.r * s.t, 0, Math.PI*2); ctx.fill();
  }
  ctx.restore();
}
// Centre-screen confetti burst + banner. Default is the above-average payout;
// opts can override the label/scale and force past the cooldown for landmark
// events (e.g. completing PINBALL) so they always celebrate.
function triggerBigScore(label, opts){
  opts = opts || {};
  var now = (typeof performance !== "undefined" ? performance.now() : Date.now());
  if(!opts.force && now - bigScoreLastAt < BIG_SCORE_COOLDOWN_MS) return;
  bigScoreLastAt = now;
  bigScoreFx.label = label || "ABOVE AVERAGE!!";
  bigScoreFx.subLabel = opts.subLabel || "";
  bigScoreFx.subLabels = opts.subLabels || (bigScoreFx.subLabel ? [bigScoreFx.subLabel] : []);
  bigScoreFx.size = opts.size || 74;
  bigScoreFx.subSize = opts.subSize || 32;
  bigScoreFx.labelColor = opts.labelColor || "#fff600";
  bigScoreFx.outline = !!opts.outline;
  bigScoreFx.wrap = !!opts.wrap;
  bigScoreFx.wordLines = !!opts.wordLines;
  bigScoreFx.colorCycle = !!opts.colorCycle;
  bigScoreFx.max = opts.frames || 60;
  bigScoreFx.t = bigScoreFx.max;
  bigScoreFx.parts.length = 0;
  logEvent(bigScoreFx.label, "#fff600");
  var count = opts.count || 150, spread = opts.spread || 170, maxSpd = opts.maxSpd || 12;
  for(var i=0;i<count;i++){
    var ang = Math.random()*Math.PI*2, spd = 2 + Math.random()*maxSpd;
    bigScoreFx.parts.push({
      x:VIEW_W/2 + (Math.random()-0.5)*spread, y:VIEW_H/2 + (Math.random()-0.5)*spread*0.53,
      vx:Math.cos(ang)*spd, vy:Math.sin(ang)*spd,
      r:2 + Math.random()*7, t:1, decay:0.008 + Math.random()*0.015,
      col:ENCOURAGE_COLORS[Math.floor(Math.random()*ENCOURAGE_COLORS.length)]
    });
  }
}
function drawBigScoreFx(){
  if(bigScoreFx.t <= 0) return;
  var a = bigScoreFx.t / bigScoreFx.max;
  ctx.save();
  ctx.setTransform(1,0,0,1,0,0);
  for(var i=bigScoreFx.parts.length-1;i>=0;i--){
    var p = bigScoreFx.parts[i];
    p.x += p.vx; p.y += p.vy; p.vx *= 0.985; p.vy = p.vy*0.985 + 0.035; p.t -= p.decay;
    if(p.t <= 0){ bigScoreFx.parts.splice(i,1); continue; }
    ctx.globalAlpha = Math.max(0, p.t) * Math.min(1, a*1.8);
    ctx.fillStyle = p.col; ctx.shadowColor = p.col; ctx.shadowBlur = 18;
    ctx.beginPath(); ctx.arc(p.x*view.scale, p.y*view.scale, p.r*p.t*view.scale, 0, 7); ctx.fill();
  }
  ctx.globalAlpha = Math.min(1, a*2.2);
  ctx.translate(canvas.width/2, canvas.height/2);
  ctx.textAlign = "center"; ctx.textBaseline = "middle";
  ctx.font = "bold " + Math.round(bigScoreFx.size*view.scale) + "px 'Trebuchet MS',Arial,sans-serif";
  ctx.shadowBlur = 0;
  var lines = bigScoreFx.wordLines ? bigScoreFx.label.split(" ") : [bigScoreFx.label];
  if(bigScoreFx.wrap && !bigScoreFx.wordLines){
    lines = [];
    var words = bigScoreFx.label.split(" "), line = "", maxWidth = canvas.width * 0.92;
    for(var wi=0; wi<words.length; wi++){
      var next = line ? line + " " + words[wi] : words[wi];
      if(line && ctx.measureText(next).width > maxWidth){ lines.push(line); line = words[wi]; }
      else line = next;
    }
    if(line) lines.push(line);
  }
  var lineHeight = Math.round(bigScoreFx.size*view.scale*0.82);
  var startY = -lineHeight * (lines.length - 1) / 2;
  ctx.lineJoin = "round";
  ctx.lineWidth = Math.max(4, Math.round(bigScoreFx.size*view.scale*0.09));
  ctx.strokeStyle = "rgba(0,0,0,0.9)";
  ctx.fillStyle = bigScoreFx.colorCycle ? ENCOURAGE_COLORS[Math.floor((animT / 6) % ENCOURAGE_COLORS.length)] : bigScoreFx.labelColor;
  for(var li=0; li<lines.length; li++){
    var y = startY + li*lineHeight;
    if(bigScoreFx.outline) ctx.strokeText(lines[li], 0, y);
    ctx.fillText(lines[li], 0, y);
  }
  if(bigScoreFx.subLabels.length){
    ctx.font = "bold " + Math.round(bigScoreFx.subSize*view.scale) + "px 'Trebuchet MS',Arial,sans-serif";
    var subY = startY + lines.length*lineHeight + Math.round(10*view.scale);
    var subLineHeight = Math.round(bigScoreFx.subSize*view.scale*1.08);
    var wrappedSubs = [];
    for(var si=0; si<bigScoreFx.subLabels.length; si++){
      var subWords = bigScoreFx.subLabels[si].split(" "), subLine = "";
      for(var swi=0; swi<subWords.length; swi++){
        var subNext = subLine ? subLine + " " + subWords[swi] : subWords[swi];
        if(subLine && ctx.measureText(subNext).width > canvas.width * 0.9){ wrappedSubs.push(subLine); subLine = subWords[swi]; }
        else subLine = subNext;
      }
      if(subLine) wrappedSubs.push(subLine);
    }
    for(si=0; si<wrappedSubs.length; si++){
      var sy = subY + si*subLineHeight;
      if(bigScoreFx.outline) ctx.strokeText(wrappedSubs[si], 0, sy);
      ctx.fillText(wrappedSubs[si], 0, sy);
    }
  }
  ctx.restore();
  bigScoreFx.t--;
}
// Largest bold size (<= max) at which text fits within maxWidth, so long headlines
// like "ORION CODEX TRIGGERED" don't run off the sides.
function fitFontSize(text, max, maxWidth){
  ctx.save();
  var s = max;
  while(s > 20){
    ctx.font = "bold " + s + "px 'Trebuchet MS',Arial,sans-serif";
    if(ctx.measureText(text).width <= maxWidth) break;
    s -= 2;
  }
  ctx.restore();
  return s;
}
// Big centre-screen banner shown for a landmark event: a headline ("MULTIPLIER" /
// "ORION CODEX ARMED") with an optional smaller sub-line (e.g. "A1 BANK COMPLETE").
// Both lines land in the left log sharing one encouragement colour, so the headline
// and its cause read as associated (while staying yellow on the board).
function announceBank(headline, sub){
  var cx = cam.x + VIEW_W/2, cy = cam.y + VIEW_H/2;
  var logCol = ENCOURAGE_COLORS[Math.floor(Math.random()*ENCOURAGE_COLORS.length)];
  addFloatText(headline, cx, cy, "#fff600", 70, fitFontSize(headline, 72, VIEW_W*0.9), false, logCol);
  if(sub) addFloatText(sub, cx, cy + 50, "#fff600", 70, 32, false, logCol);
}
// A completed bank stays lit until struck again, then clears: announce "RESET",
// styled and behaving like the encouragement words (pop-in fx + sparkles + log).
function announceReset(x, y){
  var col = ENCOURAGE_COLORS[Math.floor(Math.random()*ENCOURAGE_COLORS.length)];
  addFloatText("RESET", x, y - 20, col, 60, 42, true);
  spawnSparkles(x, y - 20, 30);
}

//// ---- build table from extracted geometry ----
function abs(o, p){ return {x:o.x+p[0], y:o.y+p[1]}; }
function isBottomDrainLip(a, b){
  var x = (a.x + b.x) / 2;
  return a.y > 1840 && b.y > 1840 && Math.abs(a.x-b.x) < 6 && x > 300 && x < 730;
}
function buildTable(){
  resetTableState();   // clear shared lights/groups/role state so rebuilds don't duplicate
  LEVEL.layers.forEach(function(layer){
    var name = layer.name;
    layer.objects.forEach(function(o){
      switch(name){
        case "edge_frame":
        case "left_router":
          if(o.polyline) for(var i=0;i<o.polyline.length-1;i++){
            var a = abs(o,o.polyline[i]), b = abs(o,o.polyline[i+1]);
            if(name === "edge_frame" && isBottomDrainLip(a, b)) continue;
            addEdge(a, b, 0);
          }
          break;
        case "top_channellers":
          if(o.polygon) addFilledPoly(o.polygon.map(function(p){return abs(o,p);}), GENERAL_RESTITUTION*1.5);
          break;
        case "right_channeller":
          if(o.polygon) addFilledPoly(o.polygon.map(function(p){return abs(o,p);}), 0.7);
          break;
        case "bot_channellers":
          if(o.ellipse) addStaticCircle(o.w/2, o.x+o.w/2, o.y+o.w/2, 0);
          else if(o.polygon) addFilledPoly(o.polygon.map(function(p){return abs(o,p);}), GENERAL_RESTITUTION/2);
          break;
        case "flipper_bumper":
          if(o.polygon) addFilledPoly(o.polygon.map(function(p){return abs(o,p);}), 0.3);
          break;
        case "circle_bumper":
          var cx = o.x+o.w/2, cy = o.y+o.w/2;
          addStaticCircle(o.w/2, cx, cy, 0, {type:"pop", x:cx, y:cy});
          break;
        case "centersafe":
          // Removed: bottom-centre pin blocked the below-flipper return lane.
          break;
        case "flipper":
          // The original builds BOTH flippers from the right outline; the left is the
          // same shape mirrored (negate-x), so it's a true mirror of the right. The
          // separate "left" Tiled object has a different/offset layout — don't use it.
          if(o.name==="right"){
            var fpts = o.polygon.map(function(p){ return {x:p[0], y:p[1]}; });
            rightFlipper = addFlipper(fpts, 726, 1706, false);
            leftFlipper  = addFlipper(fpts, 326, 1706, true);
          }
          break;
      }
    });
  });

  // slingshot sensors (flipper_bumper buttons) — original CModuleBumper
  var sl = addButton(220, 12, 252, 1460, 66.7, 0, {type:"sling", dir:-1}); sl.GetFixtureList().SetSensor(true);
  var sr = addButton(220, 12, 824, 1460, -69,  0, {type:"sling", dir: 1}); sr.GetFixtureList().SetSensor(true);

  // W1/W2 wall jumpers: invisible hit zones over the lower central side walls. The
  // original CModuleJumper uses a side-wall jumper and completion lights; this mirrors
  // that behavior on both sides so side-wall hits clear the slingshots below.
  var w1 = addButton(56, 260, 40, 1125, 0, 0, {type:"walljumper", side:"left", x:40, y:1125}); w1.GetFixtureList().SetSensor(true);
  var w2 = addButton(56, 260, 922, 1125, 0, 0, {type:"walljumper", side:"right", x:922, y:1125}); w2.GetFixtureList().SetSensor(true);

  // --- Light groups (CLightIndicator). Positions from the original modules. ---

  wallJumpers.left = {complete:false, lights:[], cooldownUntil:0};
  wallJumpers.right = {complete:false, lights:[], cooldownUntil:0};
  // embed the lights in the side-wall surfaces (left wall ~x30, right central-side
  // wall ~x931) rather than floating off them
  for(var wi=0; wi<4; wi++){
    wallJumpers.left.lights.push(addLight(40, 1015 + wi*60, 11, "#ffd43b"));
    wallJumpers.right.lights.push(addLight(922, 1015 + wi*60, 11, "#ffd43b"));
  }

  // R1: right return channel top target, inside the channel between the slanted limb
  // and the right-side wall protrusion. Lighting it briefly traps and ejects the ball.
  var channelLight = addLight(1000, 650, 13, "#65d46e");
  addBonusLightButton(86, 16, 1000, 650, -62, channelLight, CHANNEL_LIGHT_SCORE,
    {x:1000, y:650, target:{x:900, y:875}, speed:56, deflect:{x:800, y:1050, r:100}});
  var channelDeflect = addButton(200, 200, 800, 1050, 0, 0, {type:"channeldeflect"});
  channelDeflect.GetFixtureList().SetSensor(true);

  // Bumper level-up: 3 lights right of the pop bumpers (CModuleBumper). Complete
  // them to raise the pop-bumper value; they stay lit until the next qualifying hit.
  defGroup("bumper", function(g){
    circleBumperScore += Math.random() < 0.1 ? 2 : 1;
    playSound("pinball_button_on");
    announceBank("BUMPER LEVEL UP", "B2 BANK COMPLETE");
  }, "pinball_button_on");
  for(var i=0;i<3;i++){
    var L = addLight(930+i*18, 340+i*70, 11, "#ff3df0");
    addLightButton(8, 60, 930+i*18, 340+i*70, -13, "bumper", L);
  }

  // Multiplier bank: 5 toggle lights across the top (CModuleMultiplier). Complete
  // all 5 to raise the score multiplier; they stay lit until the next qualifying hit.
  defGroup("mult", function(g){
    increaseMultiplier();
    addScore(MULTIPLIER_BANK_SCORE*multiplier, 600, 300); playSound("pinball_button_on");
    announceBank("MULTIPLIER", "A1 BANK COMPLETE");
  }, "toggle");
  var multPos = [[380,280],[490,304],[600,320],[710,304],[820,280]];
  multPos.forEach(function(p){
    var L = addLight(p[0], p[1], 12, "#39d3ff");
    addLightButton(34, 12, p[0], p[1], 0, "mult", L);
  });

  // PINBALL letters (CModuleLetters): 7 letter-lights, the curve-button arming
  // group, the Orion Codex indicator, and the lane that lights a letter when armed.
  for(var i=0;i<7;i++){
    var lx = [300,360,440,530,630,720,810][i];
    letterLights.push(addLight(lx, 1300, 15, "#fff600"));
  }
  // The Orion Codex (armed indicator — drawn as a circle) sits at the summit of the
  // D1 curved tunnel, in the channel where the ball travels over the top of the arc.
  orionCodex = addLight(368, 620, 18, "#ff7a1a"); orionCodex.pulse = true;
  defGroup("curve", function(g){
    letterArmed = true; setCodexArmed(true);
    announceBank("ORION CODEX ARMED", "D1 BANK COMPLETE");
    playSound("gate");
  }, "toggle");
  for(var i=0;i<3;i++){
    var L = addLight(324+i*60, 806, 12, "#9b6bff");
    addLightButton(40, 10, 324+i*60, 806, 0, "curve", L);
  }
  // D1 curve summit pass: when armed, this lights the next PINBALL letter.
  var ll = addButton(120,22,368,620,0,0,{type:"letterlane"}); ll.GetFixtureList().SetSensor(true);

  // checkpoint sensors near flippers / lane exits (original CTable._addCheckPoints)
  [[140,1460],[936,1460],[56,1460],[1016,1460]].forEach(function(p){
    var c = addButton(8,40,p[0],p[1],0,0,{type:"checkpoint", x:p[0], y:p[1]}); c.GetFixtureList().SetSensor(true);
  });

  // One-way gates at the top of both outer lanes — ball can exit upward but not
  // re-enter. Right (plunger) lane uses the original CModuleStart values; the left
  // lane mirrors it across the table centre (x' = 1152-x, angle negated).
  addOneWayGate(924, 176, 64, 10, -45, [[60,60]], [[-56,-32],[132,176]],
                function(){ if(!ballInGame){ ballInGame = true; addScore(GATE_SCORE*multiplier, 924, 176); } });
  // left lane isn't a true mirror (it's the router opening) — centre it in the
  // channel and lengthen so the ball can't wedge between the gate and the router.
  addOneWayGate(250, 170, 78, 10, 45, [[-62,58]], [[34,-30],[-150,170]], null);

  // Bottom center and side exits stay in play; the ball rests here until fired.
  addEdge({x:340.7, y:1856}, {x:461, y:1912}, 0);
  addEdge({x:700, y:1851.3}, {x:568, y:1912}, 0);
  addButton(900, 14, TABLE_W/2, 1912, 0, 0.05, null);
  addCodexAntiGravityBarrier();
}

//// ---- data-driven board loader (editor output) ----
// buildTableFromBoard() reconstructs a table from an editor/board.json (see editor/PROPOSAL.md).
// It reuses every existing builder, so there is no new physics code. The stock hardcoded
// buildTable() above remains the default/fallback when no board is supplied.

// The stock right-flipper outline, copied (frozen) from LEVEL so a board referencing only
// stock flippers stays portable and the loader never reads geom.js at load (PROPOSAL §4.3).
var FLIPPER_OUTLINE = [
  {x:0,y:0},{x:-144,y:55.33},{x:-150.67,y:53.33},{x:-154.5,y:49.58},{x:-156.67,y:46},
  {x:-158.67,y:41.33},{x:-159.25,y:35.5},{x:-158.08,y:30.67},{x:-153.5,y:26.42},
  {x:-20.58,y:-44.58},{x:-13.83,y:-46.17},{x:-8,y:-45.33},{x:-2,y:-42.67},{x:2,y:-39.33},
  {x:5.33,y:-32.67},{x:8.83,y:-24.58},{x:9.33,y:-14.67},{x:6.67,y:-6.67}
];

// Group-completion rewards, keyed by id (PROPOSAL §4.1). The board picks an id; the closures
// live here. These are the exact onComplete bodies from the stock buildTable() defGroup calls.
var REWARDS = { groupComplete: {
  multiplierUp: function(g){
    increaseMultiplier();
    addScore(MULTIPLIER_BANK_SCORE*multiplier, 600, 300); playSound("pinball_button_on");
    announceBank("MULTIPLIER", "A1 BANK COMPLETE");
  },
  bumperLevelUp: function(g){
    circleBumperScore += Math.random() < 0.1 ? 2 : 1;
    playSound("pinball_button_on");
    announceBank("BUMPER LEVEL UP", "B2 BANK COMPLETE");
  },
  armCodex: function(g){
    letterArmed = true; setCodexArmed(true);
    announceBank("ORION CODEX ARMED", "D1 BANK COMPLETE");
    playSound("gate");
  }
}};

function countFixtures(w){
  var n = 0;
  for(var b = w.GetBodyList(); b; b = b.GetNext())
    for(var f = b.GetFixtureList(); f; f = f.GetNext()) n++;
  return n;
}

// Clear the shared render/state collections the builders populate. MUST run before any
// (re)build, including the legacy buildTable(), or switching boards leaves stale lights,
// groups, and role slots behind (they live outside the Box2D world, which is itself fresh).
function resetTableState(){
  lights.length = 0;
  for(var k in lightGroups) delete lightGroups[k];
  wallJumpers.left  = {complete:false, lights:[], cooldownUntil:0};   // ready for the loader's first pass
  wallJumpers.right = {complete:false, lights:[], cooldownUntil:0};
  letterLights.length = 0; orionCodex = null; nextLetter = 0; letterArmed = false;
}

// Loader helpers. fin() guards the ballStart read in initGame; entAngle() defaults an absent
// (but schema-valid) angle to 0; samePt() drops zero-length edge segments before Box2D sees them.
function fin(v){ return typeof v === "number" && isFinite(v); }
function entAngle(e){ return fin(e.angle) ? e.angle : 0; }
function samePt(a, b){ return a[0] === b[0] && a[1] === b[1]; }
function boardLimits(){ return ((typeof BoardSchema !== "undefined" && BoardSchema.LIMITS) || {maxJsonBytes:2*1024*1024, maxGroups:200, maxEntities:2000}); }
function skipBoardEntity(e, why){
  if(typeof console !== "undefined" && console.warn) console.warn("Skipping board entity" + (e && e.type ? " " + e.type : "") + ": " + why, e);
}
function safeBoardUrl(raw){
  try {
    var u = new URL(decodeURIComponent(raw), location.href);
    if(u.origin !== location.origin) return null;
    if(u.protocol !== "http:" && u.protocol !== "https:" && u.protocol !== "file:") return null;
    return u.href;
  } catch(e){ return null; }
}
function parseBoardJson(txt){
  if(txt.length > boardLimits().maxJsonBytes) throw new Error("board JSON is too large");
  return JSON.parse(txt);
}
function fetchBoardJson(raw){
  var url = safeBoardUrl(raw);
  if(!url) return Promise.reject(new Error("board URL must be same-origin"));
  return fetch(url).then(function(r){
    var len = Number(r.headers.get("content-length"));
    if(len && len > boardLimits().maxJsonBytes) throw new Error("board JSON is too large");
    return r.text();
  }).then(parseBoardJson);
}
// buildTableFromBoard reconstructs a table from an editor/board.json. A board can reach here
// having bypassed editor validation (forced export, hand-edited, hostile JSON), so the loader
// must never throw or build NaN geometry. Rather than re-deriving per-field guards (which drift
// from the editor's rules — see editor/CARLISLE-BUGS.md), it uses the SAME shared validator the
// editor does: BoardSchema.entityErrors(). Any entity that wouldn't pass validation is skipped.
function buildTableFromBoard(board){
  resetTableState();
  var ents = board && Array.isArray(board.entities) ? board.entities : [];
  var schema = (typeof window !== "undefined" && window.BoardSchema) || (typeof BoardSchema !== "undefined" && BoardSchema);
  if(!schema){ skipBoardEntity(null, "BoardSchema not loaded; cannot validate board — building empty table"); return; }
  if(!board || typeof board !== "object" || !board.table || !fin(board.table.w) || !fin(board.table.h)){ skipBoardEntity(null, "board is missing table dimensions"); return; }
  var lim = boardLimits(), groups = board && Array.isArray(board.groups) ? board.groups : [];
  if(groups.length > lim.maxGroups || ents.length > lim.maxEntities){ skipBoardEntity(null, "board exceeds size limits"); return; }
  var ctx = schema.collectContext(board);
  function ok(e){
    var errs = schema.entityErrors(e, board, ctx);
    if(errs.length) skipBoardEntity(e, errs[0]);
    return errs.length === 0;
  }

  // first pass: create all valid lights, index by id, fill ordered/role slots.
  var byId = Object.create(null);
  ents.forEach(function(e){
    if(!e || typeof e !== "object" || e.type !== "light" || !ok(e)) return;
    var L = addLight(e.x, e.y, e.r, e.color, e.shape);
    if(e.id) byId[e.id] = L;
    if(e.role === "letter") letterLights.push(L);
    else if(e.role === "codex"){ orionCodex = L; orionCodex.pulse = true; }
    else if(e.role === "wallJumper" && wallJumpers[e.side]) wallJumpers[e.side].lights.push(L);
  });

  // groups (before lightButtons, which register themselves into a group). Names are validated by
  // entityErrors' references; here we only need them to be safe object-map keys.
  (board && Array.isArray(board.groups) ? board.groups : []).forEach(function(g){
    if(!g || typeof g !== "object" || typeof g.name !== "string" || g.name === "__proto__" || g.name === "constructor" || g.name === "prototype") return;
    defGroup(g.name, REWARDS.groupComplete[g.onComplete] || function(){}, g.sound);
  });

  // index valid channelDeflect entities so a bonusLight trap can resolve its deflectRef.
  var deflectById = Object.create(null);
  ents.forEach(function(e){ if(e && typeof e === "object" && e.type === "channelDeflect" && ok(e) && e.id) deflectById[e.id] = e; });

  // second pass: build everything else. ok() has already vetted geometry/refs, so the builders
  // below receive only finite, in-bounds, well-formed values.
  ents.forEach(function(e){
    if(!e || typeof e !== "object" || !ok(e)) return;
    switch(e.type){
      case "light": break;   // already created
      case "wall":
        var pts = e.points.map(function(p){ return {x:p[0], y:p[1]}; });
        if(e.solid) addFilledPoly(pts, e.restitution || 0);
        else for(var i=0;i<pts.length-1;i++) if(!samePt(e.points[i], e.points[i+1])) addEdge(pts[i], pts[i+1], 0);
        break;
      case "returnEdge":
        for(var i=0;i<e.points.length-1;i++) if(!samePt(e.points[i], e.points[i+1])) addEdge({x:e.points[i][0],y:e.points[i][1]}, {x:e.points[i+1][0],y:e.points[i+1][1]}, 0);
        break;
      case "returnPlatform":
        addButton(e.w, e.h, e.x, e.y, entAngle(e), e.restitution||0, null);
        break;
      case "popBumper":
        addStaticCircle(e.r, e.x, e.y, 0, {type:"pop", x:e.x, y:e.y});
        break;
      case "post":
        addStaticCircle(e.r, e.x, e.y, 0);
        break;
      case "slingshot":
        addButton(e.w, e.h, e.x, e.y, entAngle(e), 0, {type:"sling", dir:e.dir}).GetFixtureList().SetSensor(true);
        break;
      case "wallJumper":
        addButton(e.w, e.h, e.x, e.y, entAngle(e), 0, {type:"walljumper", side:e.side, x:e.x, y:e.y}).GetFixtureList().SetSensor(true);
        break;
      case "checkpoint":
        addButton(e.w, e.h, e.x, e.y, entAngle(e), 0, {type:"checkpoint", x:e.x, y:e.y}).GetFixtureList().SetSensor(true);
        break;
      case "letterLane":
        addButton(e.w, e.h, e.x, e.y, entAngle(e), 0, {type:"letterlane"}).GetFixtureList().SetSensor(true);
        break;
      case "channelDeflect":
        addButton(e.w, e.h, e.x, e.y, entAngle(e), 0, {type:"channeldeflect"}).GetFixtureList().SetSensor(true);
        break;
      case "lightButton":
        // entityErrors guarantees e.light resolves to a declared id, but that light may itself have
        // been skipped for bad geometry, so byId can still miss — guard the deref either way.
        if(!byId[e.light]){ skipBoardEntity(e, "linked light was skipped"); break; }
        addLightButton(e.w, e.h, e.x, e.y, entAngle(e), e.group, byId[e.light]);
        break;
      case "bonusLight":
        if(!byId[e.light]){ skipBoardEntity(e, "linked light was skipped"); break; }
        var trap = null;
        if(e.trap){
          // A valid deflectRef may still point at a channelDeflect that was skipped for bad
          // geometry; then the trap loads without its deflect zone (the original's soft-degrade).
          var d = e.trap.deflectRef && deflectById[e.trap.deflectRef];
          trap = {x:e.x, y:e.y, target:e.trap.target, speed:e.trap.speed,
                  deflect: d ? {x:d.x, y:d.y, r:Math.max(d.w, d.h)/2} : null};
        }
        addBonusLightButton(e.w, e.h, e.x, e.y, entAngle(e), byId[e.light], e.score, trap);
        break;
      case "oneWayGate":
        var onPass = e.entersPlay ? (function(gx, gy){ return function(){
          if(!ballInGame){ ballInGame = true; addScore(GATE_SCORE*multiplier, gx, gy); }
        }; })(e.x, e.y) : null;
        addOneWayGate(e.x, e.y, e.w, e.h, entAngle(e), e.openers, e.closers, onPass);
        break;
      case "flipper":
        var outline = e.outline ? e.outline.map(function(p){ return {x:p[0], y:p[1]}; }) : FLIPPER_OUTLINE;
        var joint = addFlipper(outline, e.x, e.y, e.side === "left");
        if(e.side === "left") leftFlipper = joint; else rightFlipper = joint;
        break;
    }
  });
  addCodexAntiGravityBarrier();
}

//// ---- launch / drain ----
function startChannelTrap(conf, light){
  channelTrap = {x:conf.x, y:conf.y, target:conf.target, speed:conf.speed || 54, deflect:conf.deflect, light:light, t:60, max:60};
  var chamberScore = Math.round(score * 0.01 * multiplier);
  addScore(chamberScore, conf.x, conf.y);
  var chamberColors = ENCOURAGE_COLORS.filter(function(c){ return c !== "#fff27a"; });
  triggerBigScore("XENON CHAMBER ACTIVATED!", {
    force:true,
    subLabel:chamberScore.toLocaleString() + " points!!",
    labelColor:chamberColors[Math.floor(Math.random()*chamberColors.length)],
    outline:true,
    wrap:true,
    size:68,
    subSize:38,
    frames:120,
    count:520,
    spread:260,
    maxSpd:18
  });
  playSound("all_letters_complete");
  playSound("all_lights_on_1", 0.75);
  ball.SetLinearVelocity(new b2Vec2(0,0));
  ball.SetAngularVelocity(0);
}
function updateChannelTrap(){
  if(!channelTrap) return false;
  if(channelTrap.t > 0){
    var phase = channelTrap.max - channelTrap.t;
    var shake = 5 + 3*Math.sin(phase*0.37);
    var jx = Math.sin(phase*1.7) * shake;
    var jy = Math.cos(phase*1.35) * shake*0.55;
    ball.SetPosition(new b2Vec2((channelTrap.x+jx)/WORLD_SCALE, (channelTrap.y+jy)/WORLD_SCALE));
    ball.SetLinearVelocity(new b2Vec2(0,0));
    ball.SetAngularVelocity(0);
    channelTrap.t--;
    return true;
  }
  var p = ball.GetPosition(), px = p.x*WORLD_SCALE, py = p.y*WORLD_SCALE;
  var dx = channelTrap.target.x - px, dy = channelTrap.target.y - py;
  var len = Math.sqrt(dx*dx + dy*dy) || 1;
  var boost = codexVelocityMult();
  ball.SetPosition(new b2Vec2(channelTrap.x/WORLD_SCALE, channelTrap.y/WORLD_SCALE));
  ball.SetLinearVelocity(new b2Vec2(dx/len*channelTrap.speed*boost, dy/len*channelTrap.speed*boost));
  ball.SetAngularVelocity(0);
  ballInGame = true; lerp = LERP_FOLLOW;
  channelDeflectArmed = true;
  channelDeflectSpeed = channelTrap.speed;
  channelDeflectTarget = channelTrap.deflect || null;
  flash(channelTrap.x, channelTrap.y, 80, "#65d46e");
  playSound("launch");
  if(channelTrap.light){ channelTrap.light.on = false; channelTrap.light.flash = 0; }
  channelTrap = null;
  return false;
}
function launchBall(strength){
  ball.SetActive(true);
  var x = -0.001 + Math.random()*0.002;
  ball.ApplyImpulse(new b2Vec2(x, -strength * codexVelocityMult()), ball.GetPosition());
  lerp = LERP_FOLLOW;                 // camera follows the ball closely once in play
  plungerVel = -(plungerY*7 + 36);    // snap the launcher head up (fire)
  playSound("launch");
}
function resetBall(){
  ball.SetLinearVelocity(new b2Vec2(0,0));
  ball.SetAngularVelocity(0);
  ball.SetPosition(new b2Vec2(BALL_STARTPOS.x/WORLD_SCALE, BALL_STARTPOS.y/WORLD_SCALE));
  onPlatform = true; ballInGame = false;
  returnFlipperOpenFrames = 0;
  lerp = LERP_SLOW;
}
function canReturnBallFromBottom(){
  if(!gameStarted || onPlatform) return false;
  return ball.GetPosition().y*WORLD_SCALE - BALL_RADIUS > BALL_RETURN_FLIPPER_LOW_Y;
}
function returnDirectionFromKeys(){
  if(keyLeft && !keyRight) return "left";
  if(keyRight && !keyLeft) return "right";
  return "center";
}
function returnBallFromBottom(px, dir){
  ball.SetAngularVelocity(0);
  dir = dir || "center";
  var py = ball.GetPosition().y*WORLD_SCALE;
  var target, speed;
  if(dir === "left"){
    target = {x:70, y:1500}; speed = 58;
  } else if(dir === "right"){
    target = {x:1082, y:1500}; speed = 58;
  } else {                               // aim between the flippers
    target = {x:TABLE_W/2, y:1420}; speed = 52;
  }
  var dx = target.x - px, dy = target.y - py;
  var len = Math.sqrt(dx*dx + dy*dy) || 1;
  var vx = dx/len*speed + (Math.random()-0.5)*2;
  var vy = dy/len*speed - Math.random()*2;
  var boost = codexVelocityMult();
  ball.SetLinearVelocity(new b2Vec2(vx*boost, vy*boost));
  returnFlipperOpenFrames = 30;
  ballInGame = true; lerp = LERP_FOLLOW;
  playSound("launch");
}

//// ---- render ----
var canvas, ctx, view;
var panelsVisible = false;
var PANEL_PAD = 16, PANEL_GAP = 16, PANEL_MIN = 230, PANEL_MAX = 360;
function fitView(){
  canvas = document.getElementById("c");
  var scale = Math.min((window.innerWidth-PANEL_PAD*2)/VIEW_W, (window.innerHeight-PANEL_PAD*2)/VIEW_H);
  var cw = Math.round(VIEW_W*scale), ch = Math.round(VIEW_H*scale);
  canvas.width = cw; canvas.height = ch;

  // show side panels only if there's room for both beside the table
  var pL = document.getElementById("panel-left"), pR = document.getElementById("panel-right");
  var leftover = window.innerWidth - cw - PANEL_PAD*2 - PANEL_GAP*2;
  panelsVisible = leftover >= PANEL_MIN*2;
  if(panelsVisible){
    var pw = Math.min(PANEL_MAX, Math.floor(leftover/2));
    [pL,pR].forEach(function(p){ p.style.display="flex"; p.style.width=pw+"px"; p.style.height=ch+"px"; });
  } else {
    [pL,pR].forEach(function(p){ p.style.display="none"; });
  }
  view = {scale:scale};
  ctx = canvas.getContext("2d");
}
// Left panel: scrolling log mirroring the board's floating text. On-screen text is
// shouty all-caps; the log reads better in Title Case. Score popups ("+23") stay
// yellow; other yellow board messages ("Multiplier", "A1 Bank Complete") adopt one of
// the encouragement-word colours in the log (they stay yellow on the board). Already-
// coloured entries (encouragement words, reset) keep their colour.
var logEl;
function toTitleCase(s){
  return s ? s.replace(/\S+/g, function(w){ return w.charAt(0).toUpperCase() + w.slice(1).toLowerCase(); }) : s;
}
function logEvent(text, col){
  if(!panelsVisible) return;
  text = toTitleCase(text);
  if(!logEl) logEl = document.getElementById("log");
  col = col || "#fff600";
  if(col === "#fff600" && text.charAt(0) !== "+"){
    col = ENCOURAGE_COLORS[Math.floor(Math.random()*ENCOURAGE_COLORS.length)];
  }
  // collapse consecutive identical entries into one with an "(xN)" counter
  var last = logEl.lastChild;
  if(last && last._text === text){
    last._count = (last._count || 1) + 1;
    last.textContent = text + " (x" + last._count + ")";
    return;
  }
  var d = document.createElement("div");
  d.className = "logentry"; d.textContent = text; d.style.color = col;
  d._text = text; d._count = 1;
  logEl.appendChild(d);
  // remove whole entries from the top once the column overflows (no squashing)
  while(logEl.scrollHeight > logEl.clientHeight && logEl.firstChild !== logEl.lastChild){
    logEl.removeChild(logEl.firstChild);
  }
}
// Right panel: large score (wraps) with the current multiplier above it.
var scoreEl, multEl, lastScoreShown = -1, lastMultShown = -1;
function updatePanels(){
  if(!panelsVisible) return;
  if(!scoreEl){ scoreEl = document.getElementById("bigscore"); multEl = document.getElementById("mult"); }
  if(score !== lastScoreShown){ scoreEl.textContent = score.toLocaleString(); lastScoreShown = score; }
  if(multiplier !== lastMultShown){
    multEl.innerHTML = '<div class="mlabel">MULTIPLIER</div><div class="mval">×' + multiplierText() + '</div>';
    lastMultShown = multiplier;
  }
}
function drawWorld(){
  ctx.setTransform(1,0,0,1,0,0);
  ctx.fillStyle = "#0a0a1f"; ctx.fillRect(0,0,canvas.width,canvas.height);
  ctx.save();
  ctx.scale(view.scale, view.scale);
  ctx.translate(-cam.x, -cam.y);    // camera follow (table-pixel space)

  // static shapes
  ctx.lineWidth = 4; ctx.strokeStyle = "#3b5bdb"; ctx.fillStyle = "#1b2a6b";
  for(var b = world.GetBodyList(); b; b = b.GetNext()){
    if(b.GetType() === b2Body.b2_dynamicBody) continue;
    if(!b.IsActive()) continue;   // hide one-way gate walls while open
    for(var f = b.GetFixtureList(); f; f = f.GetNext()){
      if(f.IsSensor()) continue;
      var ud = f.GetUserData();
      if(ud && ud.type === "codexbarrier") continue;
      drawFixture(b, f, ud && ud.type==="pop" ? "#ff3df0" : null);
    }
  }
  // lights
  drawLights();
  // plunger (animated launcher in the plunger lane)
  drawPlunger();
  // flippers
  var codexOn = codexEnhancedActive();
  ctx.fillStyle = codexOn ? "#9b6bff" : "#ffd43b"; ctx.strokeStyle = codexOn ? "#d780ff" : "#f08c00";
  if(codexOn){ ctx.shadowColor = "#d780ff"; ctx.shadowBlur = 12 + 10*Math.sin(animT*0.22); }
  [leftFlipper, rightFlipper].forEach(function(j){
    if(j) drawFixture(j.GetBodyA(), j.GetBodyA().GetFixtureList(), codexOn ? "#9b6bff" : "#ffd43b");
  });
  ctx.shadowBlur = 0;
  // ball
  var p = ball.GetPosition();
  ctx.beginPath();
  ctx.arc(p.x*WORLD_SCALE, p.y*WORLD_SCALE, BALL_RADIUS, 0, 7);
  var grd = ctx.createRadialGradient(p.x*WORLD_SCALE-8, p.y*WORLD_SCALE-8, 4, p.x*WORLD_SCALE, p.y*WORLD_SCALE, BALL_RADIUS);
  if(codexOn){
    var ballPulse = 0.5 + 0.5*Math.sin(animT*0.08);
    grd.addColorStop(0,"#fff");
    grd.addColorStop(0.45, ballPulse > 0.5 ? "#d780ff" : "#f0c8ff");
    grd.addColorStop(1,"#6f42c1");
  } else {
    grd.addColorStop(0,"#fff"); grd.addColorStop(1,"#888");
  }
  ctx.fillStyle = grd; ctx.fill();

  // flashes
  for(var i=flashTimers.length-1;i>=0;i--){
    var fl = flashTimers[i];
    ctx.globalAlpha = fl.t; ctx.fillStyle = fl.col;
    ctx.beginPath(); ctx.arc(fl.x, fl.y, fl.r*(1.4-fl.t*0.4), 0, 7); ctx.fill();
    ctx.globalAlpha = 1; fl.t -= 0.08; if(fl.t<=0) flashTimers.splice(i,1);
  }
  drawSparkles();
  drawFloatingTexts();
  ctx.restore();
  drawBigScoreFx();
  drawCodexAntiGravityBanner();
  drawHUD();
  updatePanels();
}
function roundRect(x,y,w,h,r){
  ctx.beginPath();
  ctx.moveTo(x+r,y); ctx.arcTo(x+w,y,x+w,y+h,r); ctx.arcTo(x+w,y+h,x,y+h,r);
  ctx.arcTo(x,y+h,x,y,r); ctx.arcTo(x,y,x+w,y,r); ctx.closePath();
}
function drawLights(){
  for(var i=0;i<lights.length;i++){
    var L = lights[i];
    var lit = L.on || L.flash > 0.5;
    ctx.beginPath(); ctx.arc(L.x, L.y, L.r, 0, 7);
    if(lit){
      ctx.fillStyle = L.col; ctx.fill();
      var halo = L.r + 8 + (L.flash>0?6*L.flash:0);
      if(L.pulse && L.on) halo += 6 + 6*Math.sin(animT*0.18);   // armed-lane pulse
      ctx.save(); ctx.globalAlpha = 0.35; ctx.beginPath();
      ctx.arc(L.x, L.y, halo, 0, 7);
      ctx.fillStyle = L.col; ctx.fill(); ctx.restore();
    } else {
      ctx.fillStyle = "rgba(255,255,255,0.06)"; ctx.fill();
      ctx.lineWidth = 2; ctx.strokeStyle = L.col; ctx.globalAlpha = 0.45; ctx.stroke(); ctx.globalAlpha = 1;
    }
    if(L.flash > 0) L.flash -= 0.06;
  }
}
function drawFloatingTexts(){
  ctx.save();
  ctx.textAlign = "center"; ctx.textBaseline = "middle";
  for(var i=floatingTexts.length-1;i>=0;i--){
    var ft = floatingTexts[i];
    var a = ft.t / ft.max;
    var rise = (ft.max-ft.t)*0.55;
    var px = ft.x, py = ft.y - rise;
    if(ft.fx){
      // pop-in overshoot + glow, bright solid colour
      var age = ft.max - ft.t;
      var pop = age < 8 ? (age/8) : 1;
      var scale = pop < 1 ? (1.6 - 0.6*pop) : 1;
      ctx.save();
      ctx.globalAlpha = Math.max(0, Math.min(1, a*1.2));
      ctx.translate(px, py); ctx.scale(scale, scale);
      ctx.font = "bold " + (ft.size||42) + "px 'Trebuchet MS',Arial,sans-serif";
      ctx.lineWidth = 3; ctx.strokeStyle = "rgba(0,0,0,0.8)";
      ctx.strokeText(ft.text, 0, 0);
      ctx.shadowColor = ft.col; ctx.shadowBlur = 14;
      ctx.fillStyle = ft.col; ctx.fillText(ft.text, 0, 0);
      ctx.restore();
    } else {
      ctx.globalAlpha = Math.max(0, Math.min(1, a));
      ctx.font = "bold " + (ft.size||72) + "px 'Trebuchet MS',Arial,sans-serif";
      ctx.lineWidth = 4; ctx.strokeStyle = "rgba(0,0,0,0.75)";
      ctx.strokeText(ft.text, px, py);
      ctx.fillStyle = ft.col; ctx.fillText(ft.text, px, py);
    }
    ft.t--;
    if(ft.t <= 0) floatingTexts.splice(i,1);
  }
  ctx.restore();
}
function drawPlunger(){
  // a solid launcher head in the plunger lane, just below the ball start; pulls
  // down while charging and snaps up on release (perfunctory — hits the lane floor).
  var px = BALL_STARTPOS.x, baseY = BALL_STARTPOS.y + 70;
  var y = baseY + plungerY;
  ctx.fillStyle = "#ffd43b"; ctx.strokeStyle = "#f08c00"; ctx.lineWidth = 3;
  roundRect(px-26, y, 52, 26, 6); ctx.fill(); ctx.stroke();
  ctx.fillStyle = "#b8860b";                       // shaft below the head
  ctx.fillRect(px-6, y+24, 12, 120 - plungerY);
}
function drawCodexAntiGravityBanner(){
  if(!codexAntiGravityActive()) return;
  ctx.save();
  ctx.setTransform(1,0,0,1,0,0);
  ctx.textAlign = "center"; ctx.textBaseline = "middle";
  var a = 0.55 + 0.45*Math.sin(animT*0.28);
  var x = canvas.width/2, y = canvas.height*2/3;
  ctx.globalAlpha = 0.65 + 0.35*a;
  ctx.font = "bold " + Math.round(Math.max(24, canvas.height*0.052)) + "px 'Trebuchet MS',Arial,sans-serif";
  ctx.lineWidth = Math.max(4, Math.round(canvas.height*0.006));
  ctx.strokeStyle = "rgba(0,0,0,0.86)";
  ctx.shadowColor = "#65d46e"; ctx.shadowBlur = 14 + 18*a;
  ctx.fillStyle = a > 0.55 ? "#c8ffd6" : "#65d46e";
  ctx.strokeText("ANTI-GRAVITY", x, y);
  ctx.fillText("ANTI-GRAVITY", x, y);
  ctx.restore();
}
function drawHUD(){
  // small score panel overlaid top-left, with a background for legibility
  var pad = 8, w = Math.min(150, canvas.width*0.34), h = 46;
  ctx.fillStyle = "rgba(6,6,22,0.78)"; roundRect(pad,pad,w,h,7); ctx.fill();
  ctx.strokeStyle = "#3b5bdb"; ctx.lineWidth = 1.5; roundRect(pad,pad,w,h,7); ctx.stroke();
  ctx.textBaseline = "top";
  ctx.fillStyle = "#8fa6c8"; ctx.font = "9px 'Trebuchet MS',Arial,sans-serif";
  ctx.fillText("SCORE", pad+9, pad+6);
  ctx.fillStyle = "#fff600"; ctx.font = "bold 18px 'Courier New',monospace";
  ctx.fillText(score.toLocaleString(), pad+9, pad+15);
  ctx.fillStyle = "#8fa6c8"; ctx.font = "10px 'Trebuchet MS',Arial,sans-serif";
  ctx.fillText("MULTIPLIER  x" + multiplierText(), pad+9, pad+34);
  if(paused){
    ctx.fillStyle = "rgba(0,0,0,0.55)"; ctx.fillRect(0,0,canvas.width,canvas.height);
    ctx.fillStyle = "#fff600"; ctx.textAlign = "center"; ctx.textBaseline = "middle";
    ctx.font = "bold 40px 'Trebuchet MS',Arial,sans-serif";
    ctx.fillText("PAUSED", canvas.width/2, canvas.height/2 - 14);
    ctx.fillStyle = "#9bb"; ctx.font = "15px 'Trebuchet MS',Arial,sans-serif";
    ctx.fillText("press P to resume", canvas.width/2, canvas.height/2 + 22);
    ctx.textAlign = "start"; ctx.textBaseline = "top";
  }
}
function drawFixture(body, fix, fillOverride){
  var shape = fix.GetShape();
  var t = body.GetTransform();
  if(shape.GetType() === b2Shape_e_circle || shape instanceof b2CircleShape){
    var c = body.GetWorldCenter();
    var r = shape.GetRadius()*WORLD_SCALE;
    ctx.beginPath(); ctx.arc(c.x*WORLD_SCALE, c.y*WORLD_SCALE, r, 0, 7);
    if(fillOverride){ ctx.fillStyle=fillOverride; } ctx.fill(); ctx.stroke();
  } else {
    var verts = shape.GetVertices();
    if(!verts || !verts.length) return;
    ctx.beginPath();
    for(var i=0;i<verts.length;i++){
      var wv = Box2D.Common.Math.b2Math.MulX(t, verts[i]);
      var x = wv.x*WORLD_SCALE, y = wv.y*WORLD_SCALE;
      if(i===0) ctx.moveTo(x,y); else ctx.lineTo(x,y);
    }
    if(verts.length>2){ ctx.closePath(); if(fillOverride) ctx.fillStyle=fillOverride; ctx.fill(); }
    ctx.stroke();
  }
}
var b2Shape_e_circle = 0;

//// ---- main loop ----
var animT = 0, stuckFrames = 0;
function step(){
  animT++;
  finalizeScoreCombo(false);
  if(paused){ drawWorld(); requestAnimationFrame(step); return; }
  if(debugMode){ debugStep(); requestAnimationFrame(step); return; }
  if(updateChannelTrap()){ updateCamera(); drawWorld(); requestAnimationFrame(step); return; }
  // flipper motors
  var returnOpen = returnFlipperOpenFrames > 0;
  if(returnOpen) returnFlipperOpenFrames--;
  var flipperStrength = FLIPPER_STRENGTH * codexFlipperMult();
  if(leftFlipper)  leftFlipper.SetMotorSpeed((keyLeft || returnOpen) ? flipperStrength : -flipperStrength);
  if(rightFlipper) rightFlipper.SetMotorSpeed((keyRight || returnOpen) ? -flipperStrength : flipperStrength);
  updateCodexEnhanced();
  updateCodexAntiGravityBarrier();

  // plunger charge + visual animation
  if(charging && onPlatform){ charge = Math.min(charge + 1/60/1.0, SPRING_MAX_STRENGTH); }
  if(charging && onPlatform){
    plungerY = (charge/SPRING_MAX_STRENGTH) * 70;   // pulled back (down)
    plungerVel = 0;
  } else {
    plungerVel += (0 - plungerY) * 0.55;            // spring back up to rest
    plungerVel *= 0.55;                             // damping
    plungerY += plungerVel;
    if(Math.abs(plungerY) < 0.3 && Math.abs(plungerVel) < 0.3){ plungerY = 0; plungerVel = 0; }
  }

  world.Step(1/FPS, 8, 8);
  world.ClearForces();
  updateLetterBankReset();

  // apply queued one-way gate open/close toggles (deferred from contact callbacks)
  for(var gi=0; gi<gateToggleQueue.length; gi++) gateToggleQueue[gi].body.SetActive(gateToggleQueue[gi].active);
  gateToggleQueue.length = 0;
  resolveLightHits();

  // Below-flipper exits remain in play; player fires them back with Down/Up/Space.
  var px = ball.GetPosition().x*WORLD_SCALE, py = ball.GetPosition().y*WORLD_SCALE;
  updateChannelDeflect(px, py);

  // the plunger works whenever the ball is resting in the plunger lane, so a ball
  // that falls back down can always be re-launched.
  onPlatform = gameStarted && px > BALL_STARTPOS.x - 52 && py > BALL_STARTPOS.y - 30;

  // anti-stuck: if the ball sits nearly still in play (e.g. wedged against a gate),
  // nudge it free after ~1.3s.
  if(ballInGame && !onPlatform){
    var v = ball.GetLinearVelocity();
    if(v.x*v.x + v.y*v.y < 0.04){ if(++stuckFrames > 80){ stuckFrames = 0;
      ball.ApplyImpulse(new b2Vec2((Math.random()-0.5)*0.08, -0.05), ball.GetPosition()); } }
    else stuckFrames = 0;
  } else stuckFrames = 0;

  updateCamera();
  drawWorld();
  requestAnimationFrame(step);
}

// Debug mode: gravity off. Arrow keys drive the ball at constant velocity; the
// camera follows it so the ball appears fixed on screen and the board scrolls
// around it. Because the ball still collides with the static board, running into
// an obstacle stops it (and thus the scroll) in that direction while leaving the
// others free. Contacts still fire, so lights light up on touch.
var DEBUG_PAN = 14;                            // px/frame feel
var DEBUG_SPEED = DEBUG_PAN * FPS / WORLD_SCALE; // -> m/s for the physics ball
function toggleDebug(){
  debugMode = !debugMode;
  world.SetGravity(debugMode ? new b2Vec2(0,0) : new b2Vec2(0, GRAVITY));
  if(!debugMode){ ball.SetLinearVelocity(new b2Vec2(0,0)); }
}
function debugStep(){
  var vx = ((keyRight?1:0) - (keyLeft?1:0)) * DEBUG_SPEED;
  var vy = ((keyDown?1:0) - (keyUp?1:0)) * DEBUG_SPEED;
  ball.SetLinearVelocity(new b2Vec2(vx, vy));
  ball.SetAngularVelocity(0);
  world.Step(1/FPS, 8, 8);
  world.ClearForces();
  // apply any gate toggles queued from contact callbacks this step
  for(var gi=0; gi<gateToggleQueue.length; gi++) gateToggleQueue[gi].body.SetActive(gateToggleQueue[gi].active);
  gateToggleQueue.length = 0;
  resolveLightHits();
  updateCodexEnhanced();
  updateCodexAntiGravityBarrier();
  // camera follows the ball directly (unbounded) so it stays centred on screen
  cam.x = ball.GetPosition().x*WORLD_SCALE - VIEW_W/2;
  cam.y = ball.GetPosition().y*WORLD_SCALE - VIEW_H/2;
  drawWorld();
}

//// ---- input ----
function startGame(){
  score=0; multiplier=1; jackpot=0; circleBumperScore=CIRCLE_BUMPER_START_SCORE; routerLevel=0; bumperLevelButtons=0;
  gameStarted=true; ballInGame=false; paused=false;
  lights.forEach(function(L){ L.on=false; L.flash=0; });
  for(var gn in lightGroups){ lightGroups[gn].complete = false; lightGroups[gn].cooldownUntil = 0; }
  floatingTexts.length = 0;
  sparkles.length = 0;
  bigScoreFx.t = 0; bigScoreFx.parts.length = 0; bigScoreFx.subLabel = ""; bigScoreFx.subLabels = []; bigScoreFx.labelColor = "#fff600"; bigScoreFx.outline = false; bigScoreFx.wrap = false; bigScoreFx.wordLines = false; bigScoreFx.colorCycle = false;
  bigScoreLastAt = -Infinity;
  recentScoreEvents.length = 0;
  pendingScoreCombo = null;
  channelTrap = null;
  channelDeflectArmed = false;
  channelDeflectTarget = null;
  lightHitQueue.length = 0;
  codexEnhanced.until = 0;
  codexEnhanced.nextSound = 0;
  codexAntiGravity.until = 0;
  codexAntiGravity.armed = true;
  codexAntiGravity.suppressed = false;
  updateCodexAntiGravityBarrier();
  if(logEl) logEl.innerHTML = "";
  lastScoreShown = -1; lastMultShown = -1;
  resetWallJumpers();
  letterArmed=false; nextLetter=0; letterBankResetTimer=0; setCodexArmed(false);
  document.getElementById("msg").style.display="none";
  document.getElementById("help").style.display="block";
  resetBall();
}
function pressLaunchControl(){
  if(canReturnBallFromBottom()){
    returnBallFromBottom(ball.GetPosition().x*WORLD_SCALE, returnDirectionFromKeys());
    return;
  }
  if(!charging){ charging=true; charge=0; }
}
function releaseLaunchControl(){
  charging=false;
  if(onPlatform && gameStarted){ launchBall(charge); }
  charge=0;
}
function toggleCodexDebugMode(){
  if(codexEnhancedActive() && codexAntiGravityActive() && codexEnhanced.until === Infinity){
    codexEnhanced.until = 0;
    codexAntiGravity.until = 0;
    codexAntiGravity.armed = true;
    codexAntiGravity.suppressed = false;
  } else {
    codexEnhanced.until = Infinity;
    codexEnhanced.nextSound = 0;
    codexAntiGravity.until = Infinity;
    codexAntiGravity.armed = false;
    codexAntiGravity.suppressed = false;
    logEvent("ANTI-GRAVITY", "#65d46e");
  }
  updateCodexAntiGravityBarrier();
}
function setSettingsOpen(open){
  var menu = document.getElementById("settings-menu");
  if(!menu) return;
  if(open === settingsOpen) return;
  settingsOpen = open;
  menu.classList.toggle("open", open);
  if(open){
    pausedBeforeSettings = paused;
    paused = true;
  } else {
    paused = pausedBeforeSettings;
  }
}
function bindHoldButton(id, down, up){
  var el = document.getElementById(id);
  if(!el) return;
  var held = false;
  function release(e){
    if(e) e.preventDefault();
    if(!held) return;
    held = false;
    el.classList.remove("down");
    up();
  }
  el.addEventListener("pointerdown", function(e){
    e.preventDefault();
    if(held) return;
    held = true;
    el.setPointerCapture(e.pointerId);
    el.classList.add("down");
    down();
  });
  el.addEventListener("pointerup", release);
  el.addEventListener("pointercancel", release);
  el.addEventListener("lostpointercapture", release);
}
function setupMobileControls(){
  bindHoldButton("left-btn", function(){ if(!keyLeft && gameStarted) playSound("flipper",0.6); keyLeft=true; }, function(){ keyLeft=false; });
  bindHoldButton("right-btn", function(){ if(!keyRight && gameStarted) playSound("flipper",0.6); keyRight=true; }, function(){ keyRight=false; });
  bindHoldButton("launch-btn", pressLaunchControl, releaseLaunchControl);
  var msg = document.getElementById("msg");
  if(msg) msg.addEventListener("pointerup", function(e){ if(!gameStarted){ e.preventDefault(); startGame(); } });
  var settingsBtn = document.getElementById("settings-btn");
  if(settingsBtn) settingsBtn.addEventListener("pointerup", function(e){ e.preventDefault(); setSettingsOpen(!settingsOpen); });
  var musicToggle = document.getElementById("music-toggle");
  if(musicToggle) musicToggle.addEventListener("pointerup", function(e){ e.preventDefault(); toggleMusic(); });
  var musicSwitch = document.getElementById("music-switch");
  if(musicSwitch) musicSwitch.addEventListener("pointerup", function(e){ e.preventDefault(); switchMusicTrack(); });
  document.addEventListener("pointerdown", function(e){
    if(!settingsOpen) return;
    var menu = document.getElementById("settings-menu"), btn = document.getElementById("settings-btn");
    if((menu && menu.contains(e.target)) || (btn && btn.contains(e.target))) return;
    setSettingsOpen(false);
  });
}
document.addEventListener("keydown", function(e){
  if(e.code==="Escape" && boardBrowserOpen){ closeBoardBrowser(); e.preventDefault(); return; }
  if(e.code==="Escape" && settingsOpen){ setSettingsOpen(false); e.preventDefault(); return; }
  if(e.code==="KeyB"){ toggleBoardBrowser(); e.preventDefault(); return; }
  if(e.code==="KeyD"){ toggleDebug(); e.preventDefault(); return; }
  if(e.code==="KeyG" && !e.repeat){ toggleCodexDebugMode(); e.preventDefault(); return; }
  if(debugMode){
    if(e.code==="ArrowLeft"){ keyLeft=true; e.preventDefault(); }
    if(e.code==="ArrowRight"){ keyRight=true; e.preventDefault(); }
    if(e.code==="ArrowUp"){ keyUp=true; e.preventDefault(); }
    if(e.code==="ArrowDown"){ keyDown=true; e.preventDefault(); }
    return;
  }
  if(e.code==="ArrowLeft"){ if(!keyLeft && gameStarted) playSound("flipper",0.6); keyLeft=true; e.preventDefault(); }
  if(e.code==="ArrowRight"){ if(!keyRight && gameStarted) playSound("flipper",0.6); keyRight=true; e.preventDefault(); }
  if(e.code==="ArrowDown" || e.code==="ArrowUp" || e.code==="Space"){
    if(e.code==="ArrowUp" && canReturnBallFromBottom()) pressLaunchControl();
    else if(e.code!=="ArrowUp") pressLaunchControl();
    e.preventDefault();
  }
  if(e.code==="Enter"){ if(!gameStarted) startGame(); }
  if(e.code==="KeyM"){ toggleMusic(); e.preventDefault(); }
  if(e.code==="KeyS"){ switchMusicTrack(); e.preventDefault(); }
  if(e.code==="KeyP"){ if(gameStarted){ paused = !paused; } e.preventDefault(); }
});
document.addEventListener("keyup", function(e){
  if(e.code==="ArrowLeft") keyLeft=false;
  if(e.code==="ArrowRight") keyRight=false;
  if(e.code==="ArrowUp") keyUp=false;
  if(e.code==="ArrowDown") keyDown=false;
  if(debugMode) return;
  if(e.code==="ArrowDown" || e.code==="Space"){
    releaseLaunchControl();
  }
});
window.addEventListener("resize", fitView);

//// ---- boot ----
// Resolve an optional editor board before building. Startup is async because the hosted
// ?board= path is a fetch (PROPOSAL §6 step 5/6): embedded BOARD and localStorage are
// synchronous; ?board= is hosted-only (file:// fetch is blocked). No board => stock build.
function selectBoard(){
  try { if(typeof BOARD !== "undefined" && BOARD) return Promise.resolve(BOARD); } catch(e){}
  try { var s = localStorage.getItem("pinball.board"); if(s) return Promise.resolve(parseBoardJson(s)); } catch(e){}
  var m = /[?&]board=([^&]+)/.exec(location.search);
  if(m && location.protocol !== "file:")
    return fetchBoardJson(m[1]).catch(function(){ return null; });
  return Promise.resolve(null);
}
// Build (or fully rebuild) the world and table from an optional board. A board switch at
// runtime must discard and recreate the world — calling a builder against the live world
// would duplicate bodies/sensors (PROPOSAL §6) — so this always starts from a fresh world.
function initGame(board){
  if(board && board.ballStart && fin(board.ballStart.x) && fin(board.ballStart.y))
    BALL_STARTPOS = {x:board.ballStart.x, y:board.ballStart.y};
  world = new b2World(new b2Vec2(0, GRAVITY), true);
  ball = addBall();
  if(board) buildTableFromBoard(board); else buildTable();
  setupContacts();
  setBallShapeType();
}
var loopRunning = false;
window.onload = function(){
  selectBoard().then(function(board){
    initGame(board);
    fitView();
    setupMobileControls();
    setupBoardBrowser();
    loopRunning = true; step();   // single animation loop; switches rebuild in place
  });
};
// Switch the live game to a different board (or the built-in table when board is null).
// Reuses the running loop; rebuilds the world and resets game state via startGame().
function switchToBoard(board){
  try { initGame(board); } catch(e){ return "load failed: " + (e && e.message || e); }
  startGame();
  return null;   // success
}

//// ---- in-game board browser ----
// Lists the site's official boards (boards/manifest.json, needs http — works on the
// published site and on a local server) and offers a "Load from file…" picker that works
// even from file:// (a user-chosen file read is not a fetch). Open with B.
var boardBrowserOpen = false, boardBrowserResume = false, manifestLoaded = false;
function openBoardBrowser(){
  var ov = document.getElementById("boards-overlay"); if(!ov) return;
  boardBrowserOpen = true; boardBrowserResume = paused; paused = true;
  ov.classList.add("open");
  if(!manifestLoaded) loadManifest();
}
function closeBoardBrowser(){
  var ov = document.getElementById("boards-overlay"); if(!ov) return;
  boardBrowserOpen = false; paused = boardBrowserResume;
  ov.classList.remove("open");
}
function toggleBoardBrowser(){ boardBrowserOpen ? closeBoardBrowser() : openBoardBrowser(); }
function boardMsg(text, ok){
  var m = document.getElementById("boards-msg"); if(m){ m.textContent = text || ""; m.style.color = ok ? "#65d46e" : "#ff8a8a"; }
}
function applyBoard(board){
  // Loading a board restarts the game; warn if one is in progress.
  if(gameStarted && !confirm("Load this board? Your current game (score, multiplier, lights) will be lost.")) return;
  var err = switchToBoard(board);
  if(err) boardMsg(err, false); else closeBoardBrowser();
}
function loadManifest(){
  var list = document.getElementById("boards-list"); if(!list) return;
  list.textContent = "loading…";
  fetch("boards/manifest.json").then(function(r){ return r.json(); }).then(function(items){
    manifestLoaded = true; list.innerHTML = "";
    (items || []).forEach(function(it){
      var b = document.createElement("button");
      b.className = "settings-action"; b.textContent = it.name + (it.description ? " — " + it.description : "");
      b.onclick = function(){
        boardMsg("loading " + it.name + "…", true);
        fetchBoardJson("boards/" + it.file).then(applyBoard)
          .catch(function(e){ boardMsg("couldn't load " + it.file + ": " + e.message, false); });
      };
      list.appendChild(b);
    });
    if(!list.children.length) list.textContent = "(no boards listed)";
  }).catch(function(){
    list.textContent = "Board list needs the site served over http. Use “Load from file…” below to open a board from disk.";
  });
}
function setupBoardBrowser(){
  var ov = document.getElementById("boards-overlay"); if(!ov) return;
  var open = document.getElementById("boards-open");          if(open) open.onclick = openBoardBrowser;
  var close = document.getElementById("boards-close");        if(close) close.onclick = closeBoardBrowser;
  var builtin = document.getElementById("boards-builtin");    if(builtin) builtin.onclick = function(){ applyBoard(null); };
  var fileBtn = document.getElementById("boards-file");
  var fileIn = document.getElementById("boards-fileinput");
  if(fileBtn && fileIn){
    fileBtn.onclick = function(){ fileIn.click(); };
    fileIn.onchange = function(ev){
      var f = ev.target.files[0]; if(!f) return;
      if(f.size > boardLimits().maxJsonBytes){ boardMsg("board JSON is too large", false); ev.target.value = ""; return; }
      f.text().then(function(txt){
        var board; try { board = parseBoardJson(txt); } catch(e){ boardMsg("invalid JSON: " + e.message, false); return; }
        applyBoard(board);
      });
      ev.target.value = "";
    };
  }
  ov.addEventListener("click", function(ev){ if(ev.target === ov) closeBoardBrowser(); });   // click backdrop to close
}
// Box2DWeb circle shape type id
function setBallShapeType(){
  try { b2Shape_e_circle = Box2D.Collision.Shapes.b2Shape.e_circleShape; } catch(e){}
}
function resetWallJumpers(){
  [wallJumpers.left, wallJumpers.right].forEach(function(state){
    if(!state) return;
    state.complete = false;
    state.cooldownUntil = 0;
    state.lights.forEach(function(L){ L.on = false; L.flash = 0; });
  });
}
