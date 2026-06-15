// Shared board schema — consumed by BOTH the editor and the game loader so they
// can't drift. Pure data + validation; no game logic, no executable rewards.
(function(global){
  "use strict";

  var TABLE = { w: 1152, h: 1920 };
  var LIMITS = { maxJsonBytes: 2 * 1024 * 1024, maxGroups: 200, maxEntities: 2000, maxOpenEdgePoints: 512 };

  // The ONE author-selectable reward registry: light-group completion (PROPOSAL §4.1).
  // The closures live in game.js; the editor only lets authors PICK one of these. Other
  // triggers are fixed config-driven stock behaviours (gate entersPlay, bonusLight trap,
  // letterLane), so they carry config — not reward ids — and are not modelled here.
  var REWARDS = {
    groupComplete: ["none", "multiplierUp", "bumperLevelUp", "armCodex"]
  };

  // Light roles: ordered/bank slots the loader reconstructs (see PROPOSAL §4.2).
  // "letter" is ordered (array position matters); "codex" is a singleton; "wallJumper"
  // lights need a `side` and fill wallJumpers[side].lights.
  var LIGHT_ROLES = ["letter", "codex", "wallJumper"];

  // Entity types and their editable fields (for the palette + property panel).
  // `glyph` drives the editor's representative drawing only. NOT placeable entities:
  // `ballStart` (top-level board.ballStart field) and light groups (top-level board.groups[]).
  var ENTITY_TYPES = {
    wall:         { glyph: "poly",   fields: ["points", "solid", "restitution"] },
    // `outline` is optional; absent → loader uses the stock FLIPPER_OUTLINE constant (§4.3).
    flipper:      { glyph: "flip",   fields: ["side", "x", "y", "outline"] },
    popBumper:    { glyph: "circle", fields: ["x", "y", "r"] },
    post:         { glyph: "circle", fields: ["x", "y", "r"] },   // plain static circle (no scoring), e.g. bot-channeller heads
    slingshot:    { glyph: "rect",   fields: ["x", "y", "w", "h", "angle", "dir"] },
    wallJumper:   { glyph: "rect",   fields: ["x", "y", "w", "h", "side"] },   // redirect sensor only
    // group membership is NOT declared here — it comes from the driving lightButton.
    light:        { glyph: "dot",    fields: ["id", "x", "y", "r", "color", "shape", "role", "side"] },
    lightButton:  { glyph: "rect",   fields: ["x", "y", "w", "h", "angle", "group", "light"] },
    // field order is for the panel only; the loader maps these names to the positional
    // addBonusLightButton(w,h,x,y,angle,light,scoreValue,trap) via an explicit adapter.
    // `trap` is null or a channel-trap config object {target,speed,deflectRef} — not an effect id.
    // `deflectRef` is the id of a channelDeflect entity to arm on eject (single source of truth).
    bonusLight:   { glyph: "rect",   fields: ["x", "y", "w", "h", "angle", "light", "score", "trap"] },
    oneWayGate:   { glyph: "gate",   fields: ["x", "y", "w", "h", "angle", "openers", "closers", "entersPlay"] },
    checkpoint:   { glyph: "rect",   fields: ["x", "y", "w", "h"] },
    letterLane:   { glyph: "rect",   fields: ["x", "y", "w", "h", "angle"] },   // stock-special: always letterAdvance
    channelDeflect:{ glyph: "rect",  fields: ["id", "x", "y", "w", "h", "angle"] },   // armed zone; referenced by trap.deflectRef
    returnEdge:   { glyph: "poly",   fields: ["points"] },
    // flat rest platform below the flippers (rectangular static body, not an edge chain)
    returnPlatform:{ glyph: "rect",  fields: ["x", "y", "w", "h", "angle", "restitution"] }
  };

  function emptyBoard(){
    return {
      format: "pinball-board", version: 1,
      table: { w: TABLE.w, h: TABLE.h },
      grid: { size: 24 },
      ballStart: { x: 1010, y: 1700 },
      physics: { useGlobalConstants: true },
      groups: [],
      entities: []
    };
  }

  var MAX_POLY_VERTS = 14;   // Box2DWeb practical limit for filled polygons

  // Finite-number guard: an emptied numeric field becomes undefined, and a bad value
  // would reach a builder as NaN (NaN-radius/extent fixtures break the solver). Required
  // numerics are validated up front so authoring mistakes report instead of silently
  // producing NaN geometry at load.
  function isNum(v){ return typeof v === "number" && isFinite(v); }
  function isPos(v){ return isNum(v) && v > 0; }
  function inBounds(board, x, y){ return isNum(x) && isNum(y) && x >= 0 && x <= board.table.w && y >= 0 && y <= board.table.h; }
  function safeKey(v){ return typeof v === "string" && v !== "__proto__" && v !== "constructor" && v !== "prototype"; }
  // Entities whose body needs finite w,h; and those whose circle needs finite r.
  var RECT_TYPES = { slingshot:1, wallJumper:1, lightButton:1, bonusLight:1, oneWayGate:1,
                     checkpoint:1, letterLane:1, channelDeflect:1, returnPlatform:1 };
  var CIRCLE_TYPES = { popBumper:1, post:1 };

  // Signed area; >0 == CCW. Used for degeneracy + convexity tests.
  function signedArea(pts){
    var a = 0;
    for(var i = 0; i < pts.length; i++){ var p = pts[i], q = pts[(i + 1) % pts.length]; a += p[0] * q[1] - q[0] * p[1]; }
    return a / 2;
  }
  // True iff `a` is an array of >= min finite numeric [x,y] pairs. Gates signedArea/isConvex and the
  // loader's coordinate reads so hostile JSON (e.g. points:[null]) reports instead of throwing.
  function isPointArray(a, min){
    return Array.isArray(a) && a.length >= min && a.every(function(p){
      return Array.isArray(p) && p.length >= 2 && isNum(p[0]) && isNum(p[1]);
    });
  }
  // Convex iff all cross products of consecutive edges share one sign.
  function isConvex(pts){
    if(pts.length < 3) return false;
    var sign = 0;
    for(var i = 0; i < pts.length; i++){
      var a = pts[i], b = pts[(i + 1) % pts.length], c = pts[(i + 2) % pts.length];
      var cr = (b[0] - a[0]) * (c[1] - b[1]) - (b[1] - a[1]) * (c[0] - b[0]);
      if(cr !== 0){ if(sign === 0) sign = cr > 0 ? 1 : -1; else if((cr > 0 ? 1 : -1) !== sign) return false; }
    }
    return true;
  }

  // Reference sets an entity is validated against: declared group names and the ids of all
  // light / channelDeflect entities. Built once, shared by validate() and the game loader so
  // both judge an entity's validity identically (single source of truth — no editor/loader drift).
  function collectContext(board){
    var entities = board && Array.isArray(board.entities) ? board.entities : [];
    var groups = board && Array.isArray(board.groups) ? board.groups : [];
    var lightIds = Object.create(null), deflectIds = Object.create(null), groupNames = [];
    groups.forEach(function(g){ if(g && typeof g === "object" && typeof g.name === "string") groupNames.push(g.name); });
    entities.forEach(function(e){
      if(!e || typeof e !== "object") return;
      if(e.type === "light" && e.id) lightIds[e.id] = true;
      if(e.type === "channelDeflect" && e.id) deflectIds[e.id] = true;
    });
    return { lightIds: lightIds, deflectIds: deflectIds, groupNames: groupNames };
  }

  // All validity errors for ONE entity, given board (for bounds) and ctx (for ref resolution).
  // Returns [] for a valid entity (and for an unknown type, which the loader simply skips). This
  // is the shared rule set: validate() runs it over every entity to report; the game loader runs
  // it per entity to decide whether to build or skip — so a board can never be authored valid yet
  // crash the loader, nor pass the loader yet be flagged by the editor.
  function entityErrors(e, board, ctx){
    var errors = [];
    if(!e || typeof e !== "object"){ errors.push("entity must be an object"); return errors; }
    if(!ENTITY_TYPES[e.type]) return errors;   // unknown type: skipped by both, not an error here
    if(e.type === "ballStart") errors.push("ballStart must be the top-level field, not an entity");
    if(e.type === "lightGroup") errors.push("a light group is a top-level groups[] record, not an entity");
    // Required numerics: positioned entities need finite in-bounds x,y; rect bodies need positive
    // w,h; circle/light bodies need positive r. (Walls/return edges carry geometry in `points`.)
    if(e.type !== "wall" && e.type !== "returnEdge"){
      if(!isNum(e.x) || !isNum(e.y)) errors.push(e.type + " needs numeric x,y");
      else if(!inBounds(board, e.x, e.y)) errors.push(e.type + " x,y is outside the table bounds");
    }
    if(RECT_TYPES[e.type] && (!isPos(e.w) || !isPos(e.h))) errors.push(e.type + " needs positive numeric w,h");
    if((CIRCLE_TYPES[e.type] || e.type === "light") && !isPos(e.r)) errors.push(e.type + " needs a positive numeric r");
    if(e.angle != null && !isNum(e.angle)) errors.push(e.type + ".angle must be a finite number");
    if(e.type === "flipper" && e.side !== "left" && e.side !== "right")
      errors.push("flipper needs side 'left' or 'right'");
    if((e.type === "light" || e.type === "channelDeflect") && e.id != null && (typeof e.id !== "string" || !e.id))
      errors.push(e.type + ".id must be a non-empty string when present");
    else if((e.type === "light" || e.type === "channelDeflect") && e.id != null && !safeKey(e.id))
      errors.push(e.type + ".id is reserved");
    if(e.type === "light"){
      if(e.role && LIGHT_ROLES.indexOf(e.role) < 0) errors.push("light has unknown role '" + e.role + "'");
      if(e.role === "wallJumper" && e.side !== "left" && e.side !== "right") errors.push("wallJumper-role light needs side 'left' or 'right'");
      if(e.group != null) errors.push("light must not declare 'group'; membership comes from its lightButton");
    }
    // flipper outline is optional (absent → stock FLIPPER_OUTLINE); if present, hold it to the
    // same polygon rules as a solid wall (≥3 pts, sane vertex count, non-degenerate area).
    // Winding is corrected by addFlipper() at load, so it is not checked here.
    if(e.type === "flipper" && e.outline != null){
      if(!isPointArray(e.outline, 3)) errors.push("flipper.outline, if present, must be an array of at least 3 numeric [x,y] points");
      else {
        if(e.outline.length > MAX_POLY_VERTS) errors.push("flipper.outline exceeds " + MAX_POLY_VERTS + " vertices");
        if(Math.abs(signedArea(e.outline)) < 1) errors.push("flipper.outline has near-degenerate area");
      }
    }
    // group membership is established only by lightButton (single source of truth)
    if(e.type === "lightButton" && e.group && ctx.groupNames.indexOf(e.group) < 0)
      errors.push("lightButton references undeclared group '" + e.group + "'");
    // lightButton/bonusLight drive a light by id — the loader dereferences it, so it is required.
    if(e.type === "lightButton" || e.type === "bonusLight"){
      if(!e.light) errors.push(e.type + " needs a linked light");
      else if(!ctx.lightIds[e.light]) errors.push(e.type + " references missing light '" + e.light + "'");
    } else if(e.light && !ctx.lightIds[e.light]) errors.push(e.type + " references missing light '" + e.light + "'");
    if(e.type === "oneWayGate"){
      if(e.entersPlay != null && typeof e.entersPlay !== "boolean") errors.push("oneWayGate.entersPlay must be a boolean");
      // openers/closers are arrays of numeric [dx,dy] offsets the loader adds to the gate origin;
      // the loader iterates both, so each must be a present array of numeric pairs (empty allowed).
      if(!isPointArray(e.openers, 0)) errors.push("oneWayGate needs an openers array of [dx,dy] pairs");
      if(!isPointArray(e.closers, 0)) errors.push("oneWayGate needs a closers array of [dx,dy] pairs");
    }
    if(e.type === "bonusLight" && e.trap != null){
      if(typeof e.trap !== "object") errors.push("bonusLight.trap must be null or a config object {target,speed,deflectRef}");
      else {
        if(typeof e.trap.target !== "object" || e.trap.target === null || !isNum(e.trap.target.x) || !isNum(e.trap.target.y))
          errors.push("bonusLight.trap.target must be finite {x,y} numbers");
        else if(!inBounds(board, e.trap.target.x, e.trap.target.y)) errors.push("bonusLight.trap.target is outside the table bounds");
        if(!isPos(e.trap.speed)) errors.push("bonusLight.trap.speed must be a positive finite number");
        if(e.trap.deflectRef != null && !ctx.deflectIds[e.trap.deflectRef])
          errors.push("bonusLight.trap.deflectRef '" + e.trap.deflectRef + "' must be the id of a channelDeflect entity");
      }
    }
    if(e.type === "wall" || e.type === "returnEdge"){
      var min = e.solid ? 3 : 2;
      if(!isPointArray(e.points, min)){ errors.push(e.type + " needs at least " + min + " numeric [x,y] points"); return errors; }
      if(!e.solid && e.points.length > LIMITS.maxOpenEdgePoints) errors.push(e.type + " exceeds " + LIMITS.maxOpenEdgePoints + " points");
      e.points.forEach(function(p){ if(!inBounds(board, p[0], p[1])) errors.push(e.type + " point is outside the table bounds"); });
      // Author-only strictness for filled polygons; imported stock geometry sets stock:true.
      if(e.type === "wall" && e.solid && !e.stock){
        if(e.points.length > MAX_POLY_VERTS) errors.push("solid wall exceeds " + MAX_POLY_VERTS + " vertices");
        if(Math.abs(signedArea(e.points)) < 1) errors.push("solid wall has near-degenerate area");
        if(!isConvex(e.points)) errors.push("solid wall is non-convex (split into open edges or decompose)");
      }
    }
    return errors;
  }

  // Returns { errors:[], warnings:[] }. Errors block export/load; warnings don't.
  function validate(board){
    var errors = [], warnings = [];
    // Prove board exists before any field read, so validate(null) reports instead of throwing.
    if(!board || typeof board !== "object"){
      errors.push("board is missing or not an object");
      return { errors: errors, warnings: warnings };
    }
    if(board.format !== "pinball-board") errors.push("not a pinball-board file");
    if(board.version !== 1) warnings.push("unexpected version " + board.version);

    // Guard required top-level shape before anything reads board.table.w/h.
    if(typeof board.table !== "object" || board.table === null || !isPos(board.table.w) || !isPos(board.table.h)){
      errors.push("board must have a top-level table {w, h}");
      return { errors: errors, warnings: warnings };   // can't bounds-check without it
    }
    if(board.grid != null && (typeof board.grid !== "object" || board.grid === null || !isPos(board.grid.size)))
      errors.push("board.grid.size must be a positive number when present");

    if(!board.ballStart || typeof board.ballStart !== "object") errors.push("board must have a top-level ballStart");
    else if(!isNum(board.ballStart.x) || !isNum(board.ballStart.y)) errors.push("ballStart needs numeric x,y");
    else if(board.ballStart.x < 0 || board.ballStart.x > board.table.w ||
            board.ballStart.y < 0 || board.ballStart.y > board.table.h) errors.push("ballStart is outside the table bounds");

    // groups/entities must be absent-or-array before any .map/.forEach (a truthy {} would throw).
    if(board.groups != null && !Array.isArray(board.groups)) errors.push("board.groups must be an array");
    if(board.entities != null && !Array.isArray(board.entities)) errors.push("board.entities must be an array");
    var groups = Array.isArray(board.groups) ? board.groups : [];
    var entities = Array.isArray(board.entities) ? board.entities : [];
    if(groups.length > LIMITS.maxGroups) errors.push("board has too many groups (max " + LIMITS.maxGroups + ")");
    if(entities.length > LIMITS.maxEntities) errors.push("board has too many entities (max " + LIMITS.maxEntities + ")");

    // Per-item object guards: a null/non-object element would throw on the field reads below.
    var seenGroup = Object.create(null);
    groups.forEach(function(g, i){
      if(!g || typeof g !== "object"){ errors.push("groups[" + i + "] must be an object"); return; }
      if(typeof g.name !== "string" || !g.name) errors.push("groups[" + i + "].name must be a non-empty string");
      else if(!safeKey(g.name)) errors.push("groups[" + i + "].name is reserved");
      if(seenGroup[g.name]) errors.push("duplicate group name '" + g.name + "'"); else seenGroup[g.name] = true;
      if(REWARDS.groupComplete.indexOf(g.onComplete) < 0) errors.push("group '" + g.name + "' has unknown onComplete reward '" + g.onComplete + "'");
    });

    // Board-level checks the per-entity validator can't see: duplicate ids/names and the codex
    // singleton. (Membership sets for entityErrors come from collectContext below.)
    var seenLight = Object.create(null), seenDeflect = Object.create(null), codexCount = 0;
    entities.forEach(function(e){
      if(!e || typeof e !== "object") return;
      if(e.type === "light" && e.id){ if(seenLight[e.id]) errors.push("duplicate light id '" + e.id + "'"); seenLight[e.id] = true; }
      if(e.type === "light" && e.role === "codex") codexCount++;
      if(e.type === "channelDeflect" && e.id){ if(seenDeflect[e.id]) errors.push("duplicate channelDeflect id '" + e.id + "'"); seenDeflect[e.id] = true; }
    });
    if(codexCount > 1) errors.push("at most one light may have role 'codex' (found " + codexCount + ")");

    // Per-entity validity via the shared rule set (same code the loader uses to skip).
    var ctx = collectContext(board);
    entities.forEach(function(e, i){
      if(!e || typeof e !== "object"){ errors.push("entities[" + i + "] must be an object"); return; }
      if(!ENTITY_TYPES[e.type]){ warnings.push("unknown entity type '" + e.type + "' (will be skipped)"); return; }
      entityErrors(e, board, ctx).forEach(function(m){ errors.push(m); });
    });
    return { errors: errors, warnings: warnings };
  }

  global.BoardSchema = {
    TABLE: TABLE, LIMITS: LIMITS, REWARDS: REWARDS, LIGHT_ROLES: LIGHT_ROLES, ENTITY_TYPES: ENTITY_TYPES,
    emptyBoard: emptyBoard, validate: validate, isConvex: isConvex,
    collectContext: collectContext, entityErrors: entityErrors
  };
})(typeof window !== "undefined" ? window : this);
