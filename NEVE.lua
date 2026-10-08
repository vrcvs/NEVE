-- NEVE
-- by VRCVS
--
-- snow falls, tears run down.
-- snow plays low notes, tears play
-- high notes. the third voice is
-- yours: play it on the grid.
--
-- INTRO:  K3 start
-- NORNS:  E1 page, E2/E3 params
--         K2 pause, K3 next harmony
-- GRID:   row 1 controls,
--         rows 2-8 live keyboard
-- ARC:    4 rings, 3 pages
--
-- every voice has its own outputs:
-- synth engine (PolyPerc or
-- mx.samples), MIDI, Just Friends
-- (crow i2c). delay + reverb on
-- the engine.
--
-- v1.0.0 @VRCVS
-- llllllll.co/t/XXXXX

local musicutil = require "musicutil"

---------------------------------------------------------------
-- PERSISTENT CONFIG (synth engine)
-- A norns script can only load one engine, so switching between
-- PolyPerc and mx.samples requires reloading the script. The
-- choice is used for that one reload only; NEVE always starts with PolyPerc.
---------------------------------------------------------------
local cfg_dir = _path.data .. "NEVE/"
local cfg_file = cfg_dir .. "config.txt"
local engine_choice = 1 -- 1 = PolyPerc, 2 = MxSamples
local pending_pset = nil  -- preset to reload after an engine switch
local last_pset = nil     -- last preset loaded by the user

do
  local f = io.open(cfg_file, "r")
  if f then
    engine_choice = tonumber(f:read("*l")) or 1
    pending_pset = f:read("*l")
    f:close()
    -- one-shot: the saved choice only applies to the reload right after
    -- switching engines. Any later launch starts with PolyPerc.
    local w = io.open(cfg_file, "w")
    if w then w:write("1\n") w:close() end
  end
  if engine_choice ~= 1 and engine_choice ~= 2 then engine_choice = 1 end
end

local function save_cfg(eng, pset)
  util.make_dir(cfg_dir)
  local f = io.open(cfg_file, "w")
  if f then
    f:write(eng .. "\n")
    if pset then f:write(tostring(pset) .. "\n") end
    f:close()
  end
end

-- mx.samples is optional: if missing, fall back to PolyPerc
local mxsamples = nil
local mx_msg = nil     -- problem with mx.samples, shown on screen after K3
if engine_choice == 2 then
  local ok, lib = pcall(include, "mx.samples/lib/mx.samples")
  if ok and type(lib) == "table" then
    mxsamples = lib
  else
    print("NEVE: could not load mx.samples (" .. tostring(lib) .. "), using PolyPerc")
    mx_msg = "mx: not found, PolyPerc"
    engine_choice = 1
  end
end

engine.name = (engine_choice == 2) and "MxSamples" or "PolyPerc"

---------------------------------------------------------------
-- GENERAL STATE
---------------------------------------------------------------
local DT = 1 / 30          -- physics / graphics step
local MX_GAIN = 2.0        -- mx.samples loudness at volume 1.0 and velocity 127 (raise it if too quiet)
local skeys = nil          -- mx.samples instance
local midi_dev = nil
local ready = false
local intro = true
local running = false
local t_intro = 0
local t_run = 0
local t_all = 0            -- total time (s), used for "sounding" notes
local ui_idle = 99         -- seconds since the last encoder movement
local page = 1
local ui_metro = nil
local frame = 0
local ui_msg = ""          -- short message on the norns screen
local ui_msg_t = 0

local NOTE_NAMES = { "C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B" }
local QUANT_NAMES = { "1/4", "1/8", "1/16" }
local QUANT_DIVS = { 1, 2, 4 }
local LIVE_QUANT_NAMES = { "free", "1/16", "1/8", "1/4" }
local LIVE_SYNC = { false, 0.25, 0.5, 1 }
local DELAY_NAMES = { "1/8", "1/8.", "1/4", "1/4.", "1/2", "1/2.", "1" }
local DELAY_BEATS = { 0.5, 0.75, 1, 1.5, 2, 3, 4 }
local PROG_NAMES = { "auto (fits the scale)", "i VI III VII", "i VII VI VII", "i iv VI v", "i III iv VI", "static", "wandering" }
local PROGS = {
  ["i VI III VII"] = { 0, 5, 2, 6 },
  ["i VII VI VII"] = { 0, 6, 5, 6 },
  ["i iv VI v"]    = { 0, 3, 5, 4 },
  ["i III iv VI"]  = { 0, 2, 3, 5 },
  ["static"]       = { 0 },
}

local scale_names = {}
for i = 1, #musicutil.SCALES do
  scale_names[i] = musicutil.SCALES[i].name
end

-- voices: 1 = snow (low notes), 2 = tears (high notes), 3 = live (grid)
local VOICE_NAMES = { "snow", "tears", "live" }

-- scale over 4 octaves: the lower half is for the snow,
-- the upper half for the tears
local scale = {}
local per_oct = 7
local scale_iv = { 0, 2, 3, 5, 7, 9, 10 }
local harm_due = 0   -- beat at which the chord changes
local last_bass_t = -99 -- time of the last bass note (slow style)
local slow_next = nil   -- beat of the next scheduled tear (slow style)
local slow_cycle = 0    -- beat at which the current 8-beat cell started
local slow_var = 1      -- rhythm variant of the cell
local slow_slots = {}   -- beats (within the cell) of the notes still to schedule
local slow_spawned = false
local function slow()
  return params.lookup and params.lookup["style"] ~= nil and params:get("style") >= 2
end
local function arp()
  return params.lookup and params.lookup["style"] ~= nil and params:get("style") == 3
end
local slow_kind = "cell"   -- kind of the tear being scheduled: cell / arp / top
local slow_kinds = {}
local arp_k = 0            -- position inside the arpeggio pattern
local arp_base = 1         -- first chord tone used by the arpeggio
local top_i = 0
local bass_n = 1
local lead_lo, lead_hi = 1, 1
local compute_chords = nil   -- defined after chord_ok
local good = {}               -- good[d] = chord on degree d is stable
local auto_seq = { 0 }        -- progression built from the scale
local center = 0        -- scale degree (0-based) the harmony rests on
local prog_i = 0
local harm_count = 0
local harm_flag = false -- the harmony has just changed
local bass_step = 0
local lead_pos = 1

-- live keyboard: its own scale table, wider than the other two
local lscale = {}
local live_step = 3     -- scale degrees between two rows

-- animated objects
local decor = {}        -- decorative snow (silent)
local flakes = {}       -- "voice" flakes (they play when they hit the bottom)
local tears = {}        -- tears
local splashes = {}     -- ripples on the bottom edge
local snow_timer = 1
local tear_timer = 3

local SNOW_MEAN = 2.0   -- mean seconds between two flakes (at frequency 1.0)
local TEAR_MEAN = 3.2   -- mean seconds between two tears (at frequency 1.0)

for i = 1, 40 do
  decor[i] = { x = math.random(0, 127), y = math.random(0, 63),
               spd = 4 + math.random() * 8, ph = math.random() * 6,
               l = math.random(1, 4) }
end

-- grid / arc state
local g = nil
local a = nil
local pressed = {}                 -- grid keys currently down ("x,y")
local held = {}                    -- live notes currently held
local note_flash = {}              -- midi note -> 0..1 (lights the keyboard)
local arc_flash = { 0, 0, 0, 0 }   -- ring glow: snow, tears, live, harmony
local arc_acc = { 0, 0, 0, 0 }     -- accumulators for integer params
local arc_page = 1
local arc_idle = 99
local arc_id = nil
local led_err = {}                 -- grid / arc errors already printed

-- parameter pages on the norns screen (E1)
local pages = {
  { { "quantity", "amount" },        { "freq", "frequency" } },
  { { "melvar", "melodic var." },    { "rhythm_var", "rhythmic var." } },
  { { "vel_min", "velocity min" },   { "vel_max", "velocity max" } },
  { { "root", "root" },              { "scale", "scale" } },
  { { "delay_mix", "delay" },        { "reverb_send", "reverb" } },
  { { "live_vel", "live velocity" }, { "live_oct", "live octave" } },
}

-- parameter pages on the arc (4 rings each)
local ARC_PAGES = {
  { "quantity", "freq", "melvar", "rhythm_var" },
  { "vel_min", "vel_max", "note_len", "wind" },
  { "delay_mix", "delay_fb", "reverb_send", "reverb_time" },
}
local ARC_NAMES = { "flow", "dynamics", "space" }
-- short labels, so they stay readable at normal size on the screen
local ARC_LABELS = {
  quantity = "amount", freq = "frequency", melvar = "melodic var.",
  rhythm_var = "rhythmic var.", vel_min = "velocity min", vel_max = "velocity max",
  note_len = "note length", wind = "wind", delay_mix = "delay level",
  delay_fb = "delay feedback", reverb_send = "reverb level", reverb_time = "reverb time",
}
-- value range of the integer params (used to draw the rings)
local PARAM_RANGE = { quantity = { 1, 24 }, vel_min = { 1, 127 }, vel_max = { 1, 127 } }
local ARC_SENS = 0.4                                   -- arc sensitivity (continuous params)
local ARC_INT = { quantity = 6, vel_min = 1.5, vel_max = 1.5 } -- arc units per step (integer params)

---------------------------------------------------------------
-- EFFECTS: delay (softcut) and reverb (system reverb)
-- They act on the synth engine (PolyPerc / mx.samples),
-- not on MIDI or Just Friends.
---------------------------------------------------------------
local sys_orig = {}
local function sys_set(id, v)
  if params.lookup and params.lookup[id] then
    if sys_orig[id] == nil then sys_orig[id] = params:get(id) end
    params:set(id, v)
  end
end

local delay_T = 0

local function setup_delay()
  softcut.reset()
  softcut.buffer_clear()
  for v = 1, 2 do
    softcut.enable(v, 1)
    softcut.buffer(v, v)
    softcut.level(v, 1.0)
    softcut.pan(v, v == 1 and -0.8 or 0.8)
    softcut.rate(v, 1.0)
    softcut.loop(v, 1)
    softcut.loop_start(v, 1)
    softcut.loop_end(v, 2)
    softcut.position(v, 1)
    softcut.play(v, 1)
    softcut.rec(v, 1)
    softcut.rec_level(v, 1.0)
    softcut.pre_level(v, 0.5)
    softcut.fade_time(v, 0.05)
    softcut.level_input_cut(1, v, 0.7)
    softcut.level_input_cut(2, v, 0.7)
    softcut.post_filter_dry(v, 0)
    softcut.post_filter_lp(v, 1.0)
    softcut.post_filter_fc(v, 3500)
    softcut.post_filter_rq(v, 2.0)
  end
end

local function update_delay_time()
  local beats = DELAY_BEATS[params:get("delay_time")]
  local T = util.clamp(beats * clock.get_beat_sec(), 0.05, 8)
  delay_T = T
  softcut.loop_end(1, 1 + T)
  softcut.loop_end(2, 1 + T * 1.5) -- second voice: dotted time, widens the stereo image
end

local function apply_delay()
  local mix = params:get("delay_mix")
  if params.lookup and params.lookup["cut_input_eng"] then
    sys_set("cut_input_adc", -80)
    sys_set("cut_input_eng", mix <= 0.001 and -80 or 20 * math.log(mix) / math.log(10))
  else
    audio.level_eng_cut(mix)
    audio.level_adc_cut(0)
  end
  for v = 1, 2 do
    softcut.pre_level(v, params:get("delay_fb"))
    softcut.post_filter_fc(v, params:get("delay_tone"))
  end
  update_delay_time()
end

local function apply_reverb()
  local send = params:get("reverb_send")
  sys_set("reverb", 2)
  sys_set("rev_eng_input", send <= -59 and -80 or send)
  sys_set("rev_mid_time", params:get("reverb_time"))
  sys_set("rev_hf_damping", params:get("reverb_damp"))
end

---------------------------------------------------------------
-- SCALE AND HARMONY
---------------------------------------------------------------
local function build_scale()
  local s = musicutil.SCALES[params:get("scale")]
  local iv = {}
  for _, v in ipairs(s.intervals) do
    if v < 12 then table.insert(iv, v) end
  end
  per_oct = #iv
  scale_iv = iv
  local root = (params:get("octave") + 1) * 12 + (params:get("root") - 1)
  scale = {}
  for o = 0, 3 do
    for _, v in ipairs(iv) do
      table.insert(scale, root + o * 12 + v)
    end
  end
  table.insert(scale, root + 48)

  bass_n = 2 * per_oct               -- first 2 octaves: snow
  lead_lo = 2 * per_oct + 1          -- last 2 octaves: tears
  lead_hi = #scale
  lead_pos = util.clamp(lead_pos, lead_lo, lead_hi)
  center = center % per_oct
  if compute_chords then compute_chords() end

  -- live keyboard: starts one octave above the root, a row up
  -- is about a fourth (in scale degrees)
  live_step = math.max(2, math.floor(per_oct * 3 / 7 + 0.5))
  local need = 16 + 6 * live_step + 2
  local base = root + 12 + 12 * params:get("live_oct")
  lscale = {}
  local o = 0
  while #lscale < need do
    for _, v in ipairs(iv) do table.insert(lscale, base + o * 12 + v) end
    o = o + 1
  end
end

local function map_deg(d)
  return math.floor(d * per_oct / 7 + 0.5) % per_oct
end

-- offsets (in scale degrees) of the third and the fifth, adapted to the scale
local function chord_offsets()
  return math.floor(per_oct * 2 / 7 + 0.5), math.floor(per_oct * 4 / 7 + 0.5)
end

-- does a scale note (index) belong to the current chord?
local function is_chord(pos)
  local d = (pos - 1) % per_oct
  local c1, c2 = chord_offsets()
  return d == center % per_oct
      or d == (center + c1) % per_oct
      or d == (center + c2) % per_oct
end

-- Which chords are good in the current scale/mode?
-- level 1: plain major or minor triad; level 2: at least no
-- semitone, tritone or major-seventh between its notes.
local function chord_level(d)
  local n = per_oct
  local c1, c2 = chord_offsets()
  local function note(k)
    local i = (d + k) % n
    return scale_iv[i + 1] + (((d + k) >= n) and 12 or 0)
  end
  local r = scale_iv[d % n + 1]
  local th = (note(c1) - r) % 12
  local fi = (note(c2) - r) % 12
  if (th == 3 or th == 4) and fi == 7 then return 1 end
  local pairs_ = { th, fi, (fi - th) % 12 }
  for _, ic in ipairs(pairs_) do
    if ic == 1 or ic == 6 or ic == 11 then return 3 end
  end
  return 2
end

local function safe_center(c)
  c = c % per_oct
  if good[c] then return c end
  for _, o in ipairs({ -2, 2, -1, 1, 3, -3, 4, -4 }) do
    local d = (c + o) % per_oct
    if good[d] then return d end
  end
  return c
end

-- builds, for the current scale: the list of stable chords and an
-- "auto" progression made only of them (e.g. Dorian: i IV VII v,
-- Aeolian: i VI iv VII, Lydian: I II vii ...)
compute_chords = function()
  local n = per_oct
  local lv, cnt = {}, { 0, 0, 0 }
  for d = 0, n - 1 do
    lv[d] = chord_level(d)
    cnt[lv[d]] = cnt[lv[d]] + 1
  end
  local limit = 1
  if cnt[1] < 3 then limit = 2 end
  if cnt[1] + cnt[2] < 2 then limit = 3 end
  good = {}
  for d = 0, n - 1 do good[d] = lv[d] <= limit end
  if not good[0] then good[0] = true end   -- the tonic is always allowed

  local function m(x) return math.floor(x * n / 7 + 0.5) % n end
  local seq, used = { 0 }, { [0] = true }
  local function take(from, cands)
    for _, c in ipairs(cands) do
      local d = (from + m(c)) % n
      if good[d] and not used[d] then
        used[d] = true
        table.insert(seq, d)
        return d
      end
    end
    for d = 0, n - 1 do
      if good[d] and not used[d] then
        used[d] = true
        table.insert(seq, d)
        return d
      end
    end
    return from
  end
  local a = take(0, { 5, 3, 2, 4, 1, 6 })
  take(a, { 3, 5, 2, 4, 1, 6 })
  local last = {}
  for _, c in ipairs({ 6, 4, 3 }) do table.insert(last, c) end
  take(0, last)
  auto_seq = seq
  prog_i = 0
  center = safe_center(center)
end

local function schedule_harmony()
  -- chords change on musical time (bars), not on random flake counts
  local beats = clock.get_beats()
  if slow() then
    -- slow style: chords change on the start of a 2-bar cell
    local period = math.max(8, math.floor(params:get("harm_notes") / 8 + 0.5) * 8)
    harm_due = math.floor(beats / 8) * 8 + period
    if harm_due <= beats + 2 then harm_due = harm_due + 8 end
  else
    harm_due = math.floor(beats / 4) * 4 + params:get("harm_notes")
    if harm_due <= beats + 1 then harm_due = harm_due + 4 end
  end
end

local function next_harmony()
  local name = params:string("prog")
  if name == "wandering" then
    -- moves by consonant jumps: third, fourth, fifth or one degree down
    local moves = { 2, 3, 4, -1 }
    center = safe_center(center + moves[math.random(#moves)])
  else
    local auto = name:sub(1, 4) == "auto"
    local p = auto and auto_seq or (PROGS[name] or { 0 })
    local function nxt()
      prog_i = prog_i % #p + 1
      return auto and p[prog_i] or safe_center(map_deg(p[prog_i]))
    end
    local c = nxt()
    if c == center and #p > 1 then c = nxt() end   -- never repeat the same chord
    center = c
  end
  harm_count = 0
  bass_step = 0        -- the bass restarts from the root of the new chord
  last_bass_t = -99
  -- (the melody phrase in progress is NOT cut: its last note
  -- will land on a note of the new chord)
  schedule_harmony()
  arc_flash[4] = 1
end

-- jump straight to a given degree (grid row 1)
local function set_harmony(deg)
  -- a pad on a clashing chord (e.g. a diminished one) plays the
  -- nearest stable chord instead
  center = safe_center(deg)
  harm_count = 0
  bass_step = 0
  harm_flag = true
  schedule_harmony()
  arc_flash[4] = 1
end

---------------------------------------------------------------
-- STILL-SOUNDING NOTES + CONSONANCE FILTER
-- The tears never pick notes that clash with the snow (or with
-- the notes you are playing) that are still sounding: minor
-- seconds, major sevenths, tritones. With high "melodic
-- variation" they occasionally use major seconds and minor
-- sevenths, which add color (9, 7) without hurting.
---------------------------------------------------------------
local sounding = {}
local CONS = { [0] = true, [3] = true, [4] = true, [5] = true, [7] = true, [8] = true, [9] = true }

local function add_sounding(note, dur)
  table.insert(sounding, { note = note, t_end = t_all + math.min(dur, 8) })
end

local function prune_sounding()
  for i = #sounding, 1, -1 do
    if sounding[i].t_end < t_all then table.remove(sounding, i) end
  end
end

local function consonant(note, allow_color)
  for _, b in ipairs(sounding) do
    local ic = (note - b.note) % 12
    if not CONS[ic] and not (allow_color and (ic == 2 or ic == 10)) then
      return false
    end
  end
  return true
end

---------------------------------------------------------------
-- MELODY: the two lines talk to each other
---------------------------------------------------------------
-- SNOW: a bass that follows the chord, like an upright bass:
-- root, fifth, root, third. After every harmony change it
-- restarts from the root. A flake on the right of the screen
-- plays the upper octave.
local BASS_PAT = { 0, 2, 0, 1 } -- 0 root, 1 third, 2 fifth

local function pick_bass(x)
  bass_step = bass_step + 1
  local c1, c2 = chord_offsets()
  local offs = { 0, c1, c2 }
  local first = BASS_PAT[(bass_step - 1) % #BASS_PAT + 1]
  local order = { first, 0, 2, 1 }
  local fallback
  for _, kind in ipairs(order) do
    local idx = center + offs[kind + 1] + 1
    if x > 92 and idx + per_oct <= bass_n then idx = idx + per_oct end
    idx = util.clamp(idx, 1, bass_n)
    fallback = fallback or idx
    -- the bass must not clash with the tears still ringing
    if consonant(scale[idx], false) then return idx end
  end
  return fallback
end

-- TEARS: find the nearest chord note (that is also consonant)
local function snap_chord(pos)
  local offs = { 0, 1, -1, 2, -2, 3, -3 }
  for pass = 1, 2 do
    for _, o in ipairs(offs) do
      local p = pos + o
      if p >= lead_lo and p <= lead_hi and is_chord(p) then
        if pass == 2 or consonant(scale[p], false) then return p end
      end
    end
  end
  return pos
end

-- TEARS: the melody grows out of a short MOTIF (3-5 notes, mostly
-- stepwise and descending) that is repeated, transposed onto the
-- new chord, sometimes inverted or shortened, and now and then
-- replaced. Repetition + variation is what makes a melody
-- recognizable. The first and last note of every phrase always
-- land on chord notes.
local motif = {}
local motif_i = 1
local motif_reps = 0
local motif_lock = 0     -- phrases during which a learned motif is kept
local anchor = 1
local learn_buf = {}     -- notes played live, waiting to become a motif
local learn_t = 0

local motif_scale = false  -- true: learned motif (offsets in scale steps)

-- chord tones inside the range of the tears: the melody walks on
-- these, so every note belongs to the current chord
local function chord_tones()
  local t = {}
  local lo, hi = lead_lo, lead_hi
  if slow() then
    -- slow style: a narrow register (about an octave and a half)
    lo = lead_lo + math.floor(per_oct * 0.3)
    hi = math.min(lead_hi, lo + per_oct + 3)
    if arp() then
      lo = lead_lo
      hi = math.min(lead_hi, lo + math.floor(per_oct * 1.8))
    end
  end
  for p = lo, hi do
    if is_chord(p) then t[#t + 1] = p end
  end
  return t
end

-- a generated motif is a short walk over CHORD TONES (offsets in
-- chord-tone steps): mostly descending, small steps
local function new_motif()
  local var = params:get("melvar")
  local len = slow() and 4 or math.random(3, 5)
  slow_var = math.random(3)
  local m = { 0 }
  local cur = 0
  for i = 2, len do
    local r = math.random()
    local step
    if r < 0.45 then step = -1
    elseif r < 0.70 then step = 1
    elseif r < 0.82 then step = -2
    else step = 2 end
    if not slow() and math.random() < var * 0.12 then
      step = (math.random() < 0.5 and -1 or 1) * 3
    end
    cur = cur + step
    m[i] = cur
  end
  motif = m
  motif_reps = 0
  motif_scale = false
end

-- starting point of the phrase: a chord note close to the last
-- note played (the melody falls, then climbs back up)
local function choose_anchor()
  local mn, mx = 0, 0
  for _, o in ipairs(motif) do
    mn = math.min(mn, o)
    mx = math.max(mx, o)
  end
  local range = lead_hi - lead_lo
  local target = lead_pos
  if lead_pos < lead_lo + range * 0.3 then
    target = lead_lo + math.floor(range * 0.8)
  end
  local cands = {}
  for pass = 1, 2 do
    for p = lead_lo - mn, lead_hi - mx do
      if p >= lead_lo and p <= lead_hi and is_chord(p)
          and (pass == 2 or consonant(scale[p], false)) then
        table.insert(cands, { p = p, d = math.abs(p - target) })
      end
    end
    if #cands > 0 then break end
  end
  if #cands == 0 then return util.clamp(target, lead_lo, lead_hi) end
  table.sort(cands, function(a, b) return a.d < b.d end)
  local r = math.random()
  local k = (r < 0.5) and 1 or ((r < 0.8) and 2 or 3)
  return cands[math.min(k, #cands)].p
end

-- starting chord tone of a phrase (index in chord_tones): near the
-- last note played; the melody falls, then climbs back up
local function choose_anchor_ct(ct)
  local mn, mx = 0, 0
  for _, o in ipairs(motif) do
    mn = math.min(mn, o)
    mx = math.max(mx, o)
  end
  local n = #ct
  local lo, hi = 1 - mn, n - mx
  if hi < lo then return util.clamp(math.floor(n / 2), 1, n) end
  local target = 1
  for i = 1, n do
    if ct[i] <= lead_pos then target = i end
  end
  if target < n * 0.35 then target = math.min(n, target + 3) end  -- climb back gradually
  if target > n * 0.85 then target = target - 1 end
  local cands = {}
  for i = lo, hi do
    -- never start a phrase on the note that just sounded
    if ct[i] ~= lead_pos or hi == lo or slow() then
      cands[#cands + 1] = { i = i, d = math.abs(i - target) }
    end
  end
  if #cands == 0 then return util.clamp(math.floor(n / 2), 1, n) end
  table.sort(cands, function(x, y) return x.d < y.d end)
  local r = math.random()
  local k = (r < 0.5) and 1 or ((r < 0.8) and 2 or 3)
  return cands[math.min(k, #cands)].i
end

-- start of a phrase: repeat, vary or replace the motif, choose the anchor
local function start_phrase()
  local var = params:get("melvar")
  harm_flag = false
  if motif_lock > 0 then
    -- a motif learned from the live voice stays for a while
    if motif_i > #motif then motif_lock = motif_lock - 1 end
    motif_reps = 0
  elseif slow() then
    -- slow style: the cell repeats almost identically; now and then
    -- only the last note changes; after many repetitions a new cell
    motif_reps = motif_reps + 1
    local max_reps = 4 + math.floor(4 * (1 - var))
    if motif_reps > max_reps then
      new_motif()
    elseif math.random() < 0.25 + var * 0.5 then
      local last = #motif
      motif[last] = motif[last] + (math.random() < 0.5 and -1 or 1)
    end
  else
    motif_reps = motif_reps + 1
    local max_reps = 3 + math.floor(3 * (1 - var))
    if motif_reps > max_reps or math.random() < var * 0.10 then
      new_motif()
    else
      if math.random() < var * 0.25 then
        for i = 2, #motif do motif[i] = -motif[i] end
      end
      if #motif > 3 and math.random() < var * 0.3 then
        table.remove(motif)
      end
    end
  end
  if motif_scale then
    anchor = choose_anchor()
  else
    anchor = choose_anchor_ct(chord_tones())
  end
  motif_i = 1
end

-- returns the note index and whether the phrase is finished
local function pick_tear_note()
  local var = params:get("melvar")
  if motif_i > #motif or (harm_flag and not slow()) then
    start_phrase()
  end

  local pos
  local strong = (motif_i == 1) or (motif_i == #motif)
  local color = math.random() < var * 0.5
  if motif_scale then
    -- learned motif: scale steps, first and last notes on the chord
    pos = util.clamp(anchor + motif[motif_i], lead_lo, lead_hi)
    if strong then pos = snap_chord(pos) end
    if not consonant(scale[pos], color) then
      for _, o in ipairs({ -1, 1, -2, 2 }) do
        local p = pos + o
        if p >= lead_lo and p <= lead_hi and consonant(scale[p], color)
            and (not strong or is_chord(p)) then
          pos = p
          break
        end
      end
    end
  else
    -- generated motif: always on the CURRENT chord tones
    local ct = chord_tones()
    local ci = util.clamp(anchor + motif[motif_i], 1, #ct)
    pos = ct[ci]
    if not consonant(scale[pos], false) then
      for _, o in ipairs({ -1, 1, -2, 2 }) do
        local j = ci + o
        if ct[j] and consonant(scale[ct[j]], false) then pos = ct[j] break end
      end
    end
    -- a passing/color note (the 9th, 6th or 4th) only in the middle
    -- of a phrase and only with some melodic variation
    if not strong and color and math.random() < 0.5 then
      local p = pos + (math.random() < 0.5 and 1 or -1)
      if p >= lead_lo and p <= lead_hi and consonant(scale[p], true) then pos = p end
    end
  end

  lead_pos = pos
  local done = (motif_i == #motif)
  motif_i = motif_i + 1
  return pos, done
end

-- LEARN: the last notes you played (3 to 6) become the motif of
-- the tears, transposed onto whatever chord is current.
local function learn_add(idx)
  table.insert(learn_buf, idx)
  if #learn_buf > 6 then table.remove(learn_buf, 1) end
  learn_t = t_all
end

local function learn_commit()
  if #learn_buf >= 3 then
    local m = {}
    for i, v in ipairs(learn_buf) do
      m[i] = util.clamp(v - learn_buf[1], -9, 9)
    end
    motif = m
    motif_scale = true
    motif_i = #motif + 1   -- the next tear opens a new phrase
    motif_reps = 0
    motif_lock = 10
    ui_msg = "motif learned"
    ui_msg_t = 2.5
  end
  learn_buf = {}
end

local function rand_vel()
  local a, b = params:get("vel_min"), params:get("vel_max")
  if a > b then a, b = b, a end
  return math.random(a, b)
end

---------------------------------------------------------------
-- AUDIO OUTPUTS (each voice has its own destinations)
-- voice 1 = snow, 2 = tears, 3 = live
---------------------------------------------------------------
local function pid(v, k)
  return "v" .. v .. "_" .. k
end

-- an audio problem must never stop the script: it is reported once
-- (on the screen and in the maiden console) and the note is skipped
local reported = {}
local function report(tag, detail)
  if reported[tag] then return end
  reported[tag] = true
  print("NEVE " .. tag .. ": " .. tostring(detail))
  ui_msg = tag
  ui_msg_t = 8
end

local function voice_on(v, note, vel127)
  if note < 0 or note > 127 then return end
  vel127 = util.clamp(math.floor(vel127), 1, 127)
  local vol = params:get(pid(v, "vol"))

  -- synth engine: PolyPerc or mx.samples
  if params:get(pid(v, "eng")) == 2 then
    if skeys then
      local name = params:string(pid(v, "inst"))
      if name ~= "-" and vol > 0.001 then
        -- mx.samples: velocity only picks the sample layer, it does not
        -- change the loudness (by default). The loudness is "amp", which
        -- we set here from the voice volume and the note velocity.
        local amp = vol * MX_GAIN * (vel127 / 127)
        local ok, r = pcall(function()
          return skeys:on({ name = name, midi = note, velocity = vel127, amp = amp })
        end)
        if not ok then
          report("mx: can't play " .. name, r)
        elseif r == -1 then
          report("mx: no sample " .. name, "no sample matched note " .. note)
        end
      end
    elseif engine.name == "PolyPerc" then
      engine.pan(params:get(pid(v, "pan")))
      engine.release(params:get(pid(v, "rel")))
      engine.cutoff(params:get(pid(v, "cut")))
      engine.amp((vel127 / 127) * vol)
      engine.hz(musicutil.note_num_to_freq(note))
    end
  end

  -- MIDI
  if params:get(pid(v, "midi")) == 2 and midi_dev then
    midi_dev:note_on(note, vel127, params:get(pid(v, "ch")))
  end

  -- Just Friends via crow i2c
  if params:get(pid(v, "jf")) == 2 and crow and crow.ii then
    local volts = (note - 60) / 12 + params:get(pid(v, "jfoct"))
    crow.ii.jf.play_note(volts, 1 + (vel127 / 127) * 5)
  end
end

local function voice_off(v, note)
  if skeys and params:get(pid(v, "eng")) == 2 then
    local name = params:string(pid(v, "inst"))
    if name ~= "-" then
      pcall(function() skeys:off({ name = name, midi = note }) end)
    end
  end
  if params:get(pid(v, "midi")) == 2 and midi_dev then
    midi_dev:note_off(note, 0, params:get(pid(v, "ch")))
  end
end

-- a note that ends by itself after "dur" seconds (snow and tears)
local function note_out(note, vel127, dur, voice)
  voice_on(voice, note, vel127)
  note_flash[note] = 1
  arc_flash[voice] = 1
  clock.run(function()
    clock.sleep(dur)
    voice_off(voice, note)
  end)
end

---------------------------------------------------------------
-- PHYSICS: flakes and tears, locked to the clock
-- The fall time of each flake is computed so that it lands
-- exactly on a grid pulse; each tear detaches on a pulse. This
-- way the notes fall in rhythm.
---------------------------------------------------------------
local function grid_div()
  return QUANT_DIVS[params:get("quant")]
end

-- random interval: with "rhythmic variation" = 0 it is regular,
-- with 1 it is a random (exponential) process, same mean
local function next_interval(mean)
  local v = params:get("rhythm_var")
  local m = mean / params:get("freq")
  local rnd = -math.log(1 - math.random())
  return math.max(0.1, m * ((1 - v) + v * rnd))
end

-- x is optional: the grid drops a flake in the column you press
local function spawn_flake(x)
  local v = params:get("rhythm_var")
  local bsec = clock.get_beat_sec()
  local div = grid_div()
  local now = clock.get_beats()
  local speed = 17 * (1 + (math.random() * 2 - 1) * 0.4 * v)
  local land_b = math.ceil((now + (62 / speed) / bsec) * div) / div
  while (land_b - now) * bsec < 1.5 do land_b = land_b + 1 / div end
  local T = (land_b - now) * bsec
  table.insert(flakes, {
    x = x or math.random(6, 122), y = 0,
    vy = 62 / T,
    ph = math.random() * 6,
  })
end

-- the flake hits the bottom: low note
local function land(f)
  if slow() then
    -- pedal: root at the start of the chord, the fifth halfway through;
    -- the other flakes only splash, silently
    local gap = (math.max(8, params:get("harm_notes")) * clock.get_beat_sec()) * 0.4
    table.insert(splashes, { x = f.x, age = 0 })
    if t_all - last_bass_t < gap then return end
    last_bass_t = t_all
    local c1, c2 = chord_offsets()
    local kind = (bass_step % 2 == 0) and 0 or c2
    bass_step = bass_step + 1
    local idx = util.clamp(center + kind + 1, 1, bass_n)
    local note = scale[idx]
    local dur = math.max(params:get("note_len") * 2.5, 6)
    note_out(note, math.floor(params:get("vel_min") + (params:get("vel_max") - params:get("vel_min")) * 0.5), dur, 1)
    add_sounding(note, math.max(dur, params:get(pid(1, "rel")) * 0.8))
    return
  end
  local idx = pick_bass(f.x)
  local note = scale[idx]
  local dur = params:get("note_len") * 1.6
  note_out(note, rand_vel(), dur, 1)
  add_sounding(note, math.max(dur, params:get(pid(1, "rel")) * 0.8))
  table.insert(splashes, { x = f.x, age = 0 })
end

local function spawn_tear(target, kind)
  local side = (math.random() < 0.5) and -1 or 1
  local bsec = clock.get_beat_sec()
  local div = grid_div()
  local now = clock.get_beats()
  local rel = math.ceil(now * div) / div
  while (rel - now) * bsec < 0.35 do rel = rel + 1 / div end
  if target and target > now then rel = target end
  table.insert(tears, {
    side = side, x0 = 64 + side * 6, y = 33.5, v = 3,
    state = "form", rel = rel, rem = (rel - now) * bsec, l = 8, kind = kind,
  })
end

local function update(dt)
  ui_idle = ui_idle + dt
  arc_idle = arc_idle + dt
  ui_msg_t = math.max(0, ui_msg_t - dt)
  t_all = t_all + dt
  frame = frame + 1
  if intro then t_intro = t_intro + dt else t_run = t_run + dt end
  local wind = params:get("wind")

  -- glow of the arc rings and of the keyboard keys fades out
  for i = 1, 4 do arc_flash[i] = math.max(0, arc_flash[i] - dt * 2.5) end
  for n, f in pairs(note_flash) do
    f = f - dt * 1.5
    note_flash[n] = (f > 0) and f or nil
  end
  if #learn_buf > 0 and t_all - learn_t > 1.8 then learn_commit() end

  -- decorative snow
  for _, s in ipairs(decor) do
    s.y = s.y + s.spd * dt
    s.x = s.x + (wind * 6 + math.sin(s.y * 0.12 + s.ph) * 3) * dt
    if s.y > 64 then
      s.y = 0
      s.x = math.random(0, 127)
    end
    if s.x < 0 then s.x = 127 elseif s.x > 127 then s.x = 0 end
  end

  for i = #splashes, 1, -1 do
    splashes[i].age = splashes[i].age + dt
    if splashes[i].age > 0.6 then table.remove(splashes, i) end
  end

  -- the delay follows the clock tempo
  if frame % 30 == 0 then
    local beats = DELAY_BEATS[params:get("delay_time")]
    if math.abs(beats * clock.get_beat_sec() - delay_T) > 0.005 then
      update_delay_time()
    end
  end
  prune_sounding()

  if intro or not running then return end

  -- chords change on bar boundaries
  if clock.get_beats() >= harm_due then next_harmony() end

  -- voice flakes
  snow_timer = snow_timer - dt
  if snow_timer <= 0 then
    if #flakes < params:get("quantity") then spawn_flake() end
    snow_timer = next_interval(SNOW_MEAN)
  end
  local wind10 = wind * 10
  for i = #flakes, 1, -1 do
    local f = flakes[i]
    f.y = f.y + f.vy * dt
    f.x = util.clamp(f.x + (wind10 + math.sin(f.y * 0.15 + f.ph) * 2.5) * dt, 3, 124)
    if f.y >= 62 then
      land(f)
      table.remove(flakes, i)
    end
  end

  -- tears, slow style: a fixed rhythmic cell, 2 bars (8 beats) long.
  -- Each tear is created about one beat before its note.
  if slow() then
    local now = clock.get_beats()
    if slow_next and slow_next < now - 2 then slow_next = nil end   -- after a pause
    if not slow_next then
      if slow_cycle < now then slow_cycle = math.ceil((now + 2) / 8) * 8 end
      if now >= slow_cycle - 1.5 then
        local pos, kinds = {}, {}
        if arp() then
          -- arpeggio: steady notes over the chord tones, a long "top"
          -- note on the first beat (and maybe on beat 4), a breath
          -- on the last beat of the cell
          local f = params:get("freq")
          local step = (f >= 1.6) and 0.25 or ((f >= 0.7) and 0.5 or 1)
          local t = 0
          while t < 7 - 0.001 do
            local kind = "arp"
            if t == 0 or (t == 4 and math.random() < 0.5) then kind = "top" end
            pos[#pos + 1] = t
            kinds[#kinds + 1] = kind
            t = t + step
          end
          arp_k = 0
          arp_base = (math.random() < 0.3) and 2 or 1
        else
          start_phrase()
          local n = #motif
          for i = 1, n do pos[i] = i - 1; kinds[i] = "cell" end
          if slow_var == 2 and n >= 4 then pos[n] = pos[n] - 0.5
          elseif slow_var == 3 and n >= 3 then pos[2] = pos[2] + 0.5 end
        end
        slow_slots = pos
        slow_kinds = kinds
        slow_next = slow_cycle + table.remove(slow_slots, 1)
        slow_kind = table.remove(slow_kinds, 1)
        slow_spawned = false
      end
    else
      if not slow_spawned and now >= slow_next - 1.2 then
        spawn_tear(slow_next, slow_kind)
        slow_spawned = true
      end
      if slow_spawned and now >= slow_next then
        if #slow_slots > 0 then
          slow_next = slow_cycle + table.remove(slow_slots, 1)
          slow_kind = table.remove(slow_kinds, 1)
          slow_spawned = false
        else
          slow_cycle = slow_cycle + 8
          slow_next = nil
        end
      end
    end
  else
    tear_timer = tear_timer - dt
    if tear_timer <= 0 then
      local max_tears = util.clamp(1 + math.floor(params:get("quantity") / 8), 1, 4)
      if #tears < max_tears then spawn_tear() end
      tear_timer = next_interval(TEAR_MEAN)
    end
  end
  for i = #tears, 1, -1 do
    local t = tears[i]
    if t.state == "form" then
      t.rem = (t.rel - clock.get_beats()) * clock.get_beat_sec()
      if t.rem <= 0 then
        -- the tear detaches: high note
        t.state = "fall"
        local vel = rand_vel()
        t.l = math.floor(8 + (vel / 127) * 7)
        local pos, done
        local dur = params:get("note_len") * 0.8
        if t.kind == "arp" or t.kind == "top" then
          local ct = chord_tones()
          local m = #ct
          local n = math.min(4, m)
          local b = util.clamp(arp_base, 1, math.max(1, m - n + 1))
          if t.kind == "top" then
            -- long note above the arpeggio
            top_i = util.clamp(m - math.random(0, 1), 1, m)
            pos = ct[top_i]
            dur = params:get("note_len") * 2.2
            vel = math.min(127, math.floor(vel * 1.1))
          else
            local L = {}
            local d = params:get("arp_dir")
            if d == 1 then for i = 1, n do L[#L + 1] = i end
            elseif d == 2 then for i = n, 1, -1 do L[#L + 1] = i end
            else
              for i = 1, n do L[#L + 1] = i end
              for i = n - 1, 2, -1 do L[#L + 1] = i end
            end
            arp_k = arp_k + 1
            pos = ct[b + L[(arp_k - 1) % #L + 1] - 1]
            vel = math.max(1, math.floor(vel * 0.75))
          end
          t.l = math.floor(8 + (vel / 127) * 7)
          done = false
        else
          pos, done = pick_tear_note()
        end
        pos = pos or lead_lo
        note_out(scale[pos], vel, dur, 2)
        add_sounding(scale[pos], math.max(dur, params:get(pid(2, "rel")) * 0.8))
        if done and not slow() then
          -- end of phrase: a breath before the next one
          tear_timer = tear_timer + TEAR_MEAN / params:get("freq") * (1.2 + math.random())
        end
      end
    else
      t.v = t.v + 14 * dt
      t.y = t.y + t.v * dt
      if t.y > 68 then table.remove(tears, i) end
    end
  end
end

---------------------------------------------------------------
-- GRAPHICS: static data
---------------------------------------------------------------
-- stylized profile of Monte Mucrone (squashed vertically to
-- leave room for the texts)
local function tf(pts)
  local out = {}
  for i, p in ipairs(pts) do out[i] = { p[1], 24 + (p[2] - 12) * 0.68 } end
  return out
end

local MOUNT = tf({
  { 0, 56 }, { 16, 52 }, { 30, 46 }, { 44, 40 }, { 58, 32 }, { 70, 22 },
  { 78, 16 }, { 83, 12 }, { 88, 18 }, { 94, 22 }, { 100, 21 }, { 106, 28 },
  { 116, 36 }, { 128, 42 },
})
local MOUNT_CAP = tf({ { 76, 18 }, { 79, 21 }, { 82, 17 }, { 85, 21 }, { 88, 18 } })
local MOUNT_HATCH = {
  { 90, 24, 100, 38 }, { 97, 28, 106, 40 }, { 104, 34, 110, 42 },
}
for _, h in ipairs(MOUNT_HATCH) do
  h[2] = 24 + (h[2] - 12) * 0.68
  h[4] = 24 + (h[4] - 12) * 0.68
end

local function mirror(pts)
  local out = {}
  for i, p in ipairs(pts) do out[i] = { 128 - p[1], p[2] } end
  return out
end

local function reversed(pts)
  local out = {}
  for i = #pts, 1, -1 do table.insert(out, pts[i]) end
  return out
end

-- melancholic girl: long dark hair falling over the shoulders,
-- pale face, closed eyes, side fringe, a barely downturned mouth
-- (nostalgic, not despairing)
local HAIR_L = { { 64, 8 }, { 54, 10 }, { 46, 16 }, { 41, 25 }, { 39, 36 },
                 { 36, 47 }, { 33, 57 }, { 34, 63 } }
local HAIR_OUT = {}
for _, p in ipairs(HAIR_L) do table.insert(HAIR_OUT, p) end
for _, p in ipairs(reversed(mirror(HAIR_L))) do table.insert(HAIR_OUT, p) end
-- (the right side, mirrored and reversed, closes the polygon)

local FACE = {}
for i = 0, 28 do
  local t = (i / 28) * 2 * math.pi
  local sy = math.sin(t)
  local px = 12.5 * math.cos(t) * (1 - 0.2 * math.max(0, sy))
  table.insert(FACE, { 64 + px, 31 + 17 * sy })
end

local CHEST = { { 58, 46 }, { 58, 53 }, { 50, 56 }, { 45, 60 }, { 43, 63 },
                { 85, 63 }, { 83, 60 }, { 78, 56 }, { 70, 53 }, { 70, 46 } }
local FRINGE = { { 54, 15 }, { 64, 11 }, { 75, 14 }, { 78, 22 }, { 77, 29 },
                 { 72, 25 }, { 64, 21 }, { 58, 18 } }
local FRINGE_EDGE = { { 54, 15 }, { 58, 18 }, { 64, 21 }, { 72, 25 }, { 77, 29 } }

local function path(pts, close)
  screen.move(pts[1][1] + 0.5, pts[1][2] + 0.5)
  for i = 2, #pts do
    screen.line(pts[i][1] + 0.5, pts[i][2] + 0.5)
  end
  if close then screen.close() end
end

local function stroke_poly(pts, level, close)
  screen.level(level)
  path(pts, close)
  screen.stroke()
end

local function fill_poly(pts, level)
  screen.level(level)
  path(pts, true)
  screen.fill()
end

-- text that shrinks to fit the available width
local function fit_text(str, x, y, maxw, align, sizes)
  for _, sz in ipairs(sizes) do
    screen.font_size(sz)
    if screen.text_extents(str) <= maxw then break end
  end
  screen.move(x, y)
  if align == "right" then
    screen.text_right(str)
  elseif align == "center" then
    screen.text_center(str)
  else
    screen.text(str)
  end
  screen.font_size(8)
end

---------------------------------------------------------------
-- GRAPHICS: drawing
---------------------------------------------------------------
local function draw_decor()
  for _, s in ipairs(decor) do
    screen.level(s.l)
    screen.pixel(math.floor(s.x), math.floor(s.y))
    screen.fill()
  end
end

local function draw_flakes()
  for _, f in ipairs(flakes) do
    local x, y = math.floor(f.x), math.floor(f.y)
    screen.level(12)
    screen.pixel(x, y)
    screen.pixel(x - 1, y)
    screen.pixel(x + 1, y)
    screen.pixel(x, y - 1)
    screen.pixel(x, y + 1)
    screen.fill()
  end
  for _, s in ipairs(splashes) do
    local r = math.floor(s.age * 12)
    screen.level(math.max(1, 10 - math.floor(s.age * 16)))
    screen.move(s.x - r, 63.5)
    screen.line(s.x + r + 1, 63.5)
    screen.stroke()
  end
end

local function draw_face()
  -- hair, shoulders, face, fringe
  fill_poly(HAIR_OUT, 2)
  stroke_poly(HAIR_OUT, 4, true)
  fill_poly(CHEST, 7)
  fill_poly(FACE, 7)
  fill_poly(FRINGE, 2)
  stroke_poly(FRINGE_EDGE, 8)

  -- dark strokes on the pale face
  for _, side in ipairs({ -1, 1 }) do
    local cx = 64 + side * 6
    -- closed eyes: lowered eyelids
    stroke_poly({ { cx - 4, 31 }, { cx - 2.5, 32.5 }, { cx, 33.5 },
                  { cx + 2.5, 32.5 }, { cx + 4, 31 } }, 0)
    -- lash on the outer corner
    stroke_poly({ { cx + side * 4, 31 }, { cx + side * 5.5, 33 } }, 0)
    -- soft eyebrows, slightly slanted
    stroke_poly({ { cx + side * 5, 28 }, { cx - side * 2, 26.5 } }, 0)
  end
  -- nose
  stroke_poly({ { 64, 34 }, { 64, 39 }, { 63, 39.5 } }, 0)
  -- small mouth, barely downturned
  stroke_poly({ { 61, 44.5 }, { 63, 43.5 }, { 65, 43.5 }, { 67, 44.5 } }, 0)
end

local function draw_tears()
  for _, t in ipairs(tears) do
    if t.state == "form" then
      -- the drop swells on the edge of the eyelid
      local g = util.clamp(1 - t.rem / 0.8, 0, 1)
      screen.level(3 + math.floor(g * 12))
      screen.pixel(math.floor(t.x0), 33)
      screen.fill()
    else
      local x = t.x0 + t.side * (t.y - 34) * 0.08
      screen.level(t.l)
      screen.pixel(math.floor(x), math.floor(t.y))
      screen.pixel(math.floor(x), math.floor(t.y) + 1)
      screen.fill()
      for k = 1, 5 do
        local yk = t.y - k * 1.6
        if yk >= 34 then
          local xk = t.x0 + t.side * (yk - 34) * 0.08
          screen.level(math.max(1, t.l - k * 2))
          screen.pixel(math.floor(xk), math.floor(yk))
          screen.fill()
        end
      end
    end
  end
end

local function draw_mountain()
  -- dark silhouette
  screen.level(1)
  path(MOUNT)
  screen.line(128.5, 64.5)
  screen.line(0.5, 64.5)
  screen.close()
  screen.fill()
  -- outline, snow cap, hatching on the shaded slope
  stroke_poly(MOUNT, 9)
  stroke_poly(MOUNT_CAP, 13)
  screen.level(3)
  for _, h in ipairs(MOUNT_HATCH) do
    screen.move(h[1] + 0.5, h[2] + 0.5)
    screen.line(h[3] + 0.5, h[4] + 0.5)
    screen.stroke()
  end
end

local function draw_intro()
  draw_mountain()
  draw_decor()

  local fade = math.min(15, math.floor(t_intro * 8) + 1)

  -- title and signature
  screen.level(fade)
  screen.font_size(16)
  screen.move(3, 18)
  screen.text("NEVE")
  screen.font_size(8)
  screen.level(math.floor(fade * 0.6))
  screen.move(4, 27)
  screen.text("by VRCVS")

  -- how to start (slow pulse)
  if t_intro > 1 then
    screen.level(math.floor(9 + 6 * math.sin(t_intro * 3)))
    screen.move(126, 8)
    screen.text_right("press K3")
  end
end

local function draw_overlay()
  screen.level(0)
  screen.rect(0, 49, 128, 15)
  screen.fill()
  local p = pages[page]
  screen.level(4)
  screen.move(0, 55)
  screen.text(p[1][2])
  screen.move(128, 55)
  screen.text_right(p[2][2])
  screen.level(14)
  screen.move(0, 63)
  screen.text(params:string(p[1][1]))
  screen.move(128, 63)
  screen.text_right(params:string(p[2][1]))
  screen.level(5)
  screen.move(64, 63)
  screen.text_center(page .. "/" .. #pages)
end

-- shown for a moment when you turn an arc ring or change arc page
local function draw_arc_overlay()
  screen.level(0)
  screen.rect(0, 49, 128, 15)
  screen.fill()
  screen.level(4)
  screen.move(0, 55)
  screen.text("arc " .. arc_page .. "/" .. #ARC_PAGES .. " " .. ARC_NAMES[arc_page])
  if arc_id then
    screen.level(14)
    fit_text(ARC_LABELS[arc_id] or arc_id, 0, 63, 78, "left", { 8, 7 })
    screen.level(14)
    screen.move(128, 63)
    screen.text_right(params:string(arc_id))
  end
end

function redraw()
  screen.clear()
  screen.aa(0)
  screen.line_width(1)

  if intro then
    draw_intro()
  else
    draw_decor()
    draw_face()
    draw_flakes()   -- voice flakes stay in front: you can see them land
    draw_tears()

    if t_run < 6 then
      screen.level(math.max(0, math.floor(5 - t_run * 0.6)))
      screen.move(0, 7)
      screen.text("NEVE by VRCVS")
    end
    if not running then
      screen.level(10)
      screen.move(128, 7)
      screen.text_right("paused")
    end
    if params:get("learn") == 2 then
      screen.level(6)
      screen.move(128, 15)
      screen.text_right("learn")
    end
    if ui_msg_t > 0 then
      screen.level(math.min(12, math.floor(ui_msg_t * 8)))
      fit_text(ui_msg, 0, 15, 126, "left", { 8, 6, 5 })
    end
    if arc_idle < 2.2 then
      draw_arc_overlay()
    elseif ui_idle < 2.5 then
      draw_overlay()
    end
  end

  screen.update()
end

---------------------------------------------------------------
-- LIVE VOICE + GRID + ARC
---------------------------------------------------------------
local function toggle_pause()
  running = not running
  if running then
    -- when resuming, flakes and tears in flight start over
    -- (so they land on the grid again)
    flakes = {}
    tears = {}
  end
end

-- live keyboard: key (x, y) -> index in lscale
local function live_idx(x, y)
  return (x - 1) + (g.rows - y) * live_step + 1
end

local function live_press(x, y)
  local idx = live_idx(x, y)
  local note = lscale[idx]
  if not note then return end
  local st = { note = note, down = true, on = false }
  held[x .. "," .. y] = st

  local function start()
    voice_on(3, note, params:get("live_vel"))
    st.on = true
    note_flash[note] = 1
    arc_flash[3] = 1
    add_sounding(note, 4)
    if params:get("learn") == 2 then learn_add(idx) end
    if not st.down then
      -- released before the quantized pulse: short note
      clock.run(function()
        clock.sleep(0.3 * clock.get_beat_sec())
        voice_off(3, note)
      end)
    end
  end

  local sync = LIVE_SYNC[params:get("live_quant")]
  if sync then
    clock.run(function()
      clock.sync(sync)
      start()
    end)
  else
    start()
  end
end

local function live_release(x, y)
  local key = x .. "," .. y
  local st = held[key]
  if not st then return end
  st.down = false
  held[key] = nil
  if st.on then voice_off(3, st.note) end
end

local function grid_key(x, y, z)
  pressed[x .. "," .. y] = (z == 1) or nil
  if intro then return end
  local cols = g.cols
  if y == 1 then
    if z ~= 1 then return end
    if x == cols then
      toggle_pause()
    elseif x == cols - 1 then
      next_harmony()
    elseif x == cols - 2 then
      arc_page = arc_page % #ARC_PAGES + 1
      arc_id = nil
      arc_idle = 0
    elseif x == cols - 3 then
      params:delta("live_oct", 1)
    elseif x == cols - 4 then
      params:delta("live_oct", -1)
    elseif x == cols - 5 then
      params:set("learn", params:get("learn") == 1 and 2 or 1)
    elseif x <= math.min(per_oct, cols - 6) then
      set_harmony(x - 1)
    end
  else
    if z == 1 then live_press(x, y) else live_release(x, y) end
  end
end

local function grid_redraw()
  if not (g and g.device) then return end
  local cols, rows = g.cols, g.rows
  if not cols or cols == 0 then return end

  local buf = {}
  for y = 1, rows do
    buf[y] = {}
    for x = 1, cols do buf[y][x] = 0 end
  end
  local function put(x, y, l)
    if x >= 1 and x <= cols and y >= 1 and y <= rows and buf[y][x] < l then
      buf[y][x] = l
    end
  end
  local function gx(px) return math.floor(px / 128 * cols) + 1 end
  local function gy(py) return math.floor(py / 64 * rows) + 1 end

  if intro then
    -- just the snow
    for i, s in ipairs(decor) do
      if i % 2 == 0 then put(gx(s.x), gy(s.y), s.l >= 3 and 3 or 1) end
    end
  else
    -- live keyboard: scale notes dim, chord notes brighter,
    -- chord root brightest; notes just played light up
    for y = 2, rows do
      for x = 1, cols do
        local idx = (x - 1) + (rows - y) * live_step + 1
        local note = lscale[idx]
        if note then
          local d = (idx - 1) % per_oct
          local l = 2
          if d == 0 then l = 4 end
          if is_chord(idx) then l = 7 end
          if d == center % per_oct then l = 10 end
          local fl = note_flash[note]
          if fl then l = math.max(l, math.floor(fl * 14)) end
          put(x, y, l)
        end
      end
    end
    -- falling snow and tears, kept dim so the keys stay readable
    for _, f in ipairs(flakes) do
      put(gx(f.x), gy(f.y), 6)
      put(gx(f.x), gy(f.y - 5), 3)
    end
    for _, s in ipairs(splashes) do
      local r = math.floor(s.age * 6)
      local l = math.max(2, 8 - math.floor(s.age * 12))
      for dx = -r, r do put(gx(s.x) + dx, rows, l) end
    end
    for _, t in ipairs(tears) do
      if t.state == "form" then
        put(gx(t.x0), gy(33), 5)
      elseif t.y < 64 then
        local x = t.x0 + t.side * (t.y - 34) * 0.08
        put(gx(x), gy(t.y), math.min(9, t.l))
      end
    end
  end

  g:all(0)
  for y = 1, rows do
    for x = 1, cols do
      if buf[y][x] > 0 then g:led(x, y, math.min(15, buf[y][x])) end
    end
  end

  if not intro then
    -- row 1: harmony degrees + controls
    local hcols = math.min(per_oct, cols - 6)
    for x = 1, hcols do
      local l = good[x - 1] and 4 or 1
      if is_chord(x) then l = 7 end
      if (x - 1) == center % per_oct then l = 12 end
      g:led(x, 1, l)
    end
    g:led(cols, 1, running and 9 or 3)                    -- pause
    g:led(cols - 1, 1, 5)                                 -- next harmony
    g:led(cols - 2, 1, 3 + arc_page * 3)                  -- arc page
    g:led(cols - 3, 1, 4)                                 -- live octave up
    g:led(cols - 4, 1, 4)                                 -- live octave down
    g:led(cols - 5, 1, params:get("learn") == 2 and 12 or 3) -- learn
    -- keys currently down
    for key in pairs(pressed) do
      local sx, sy = key:match("(%d+),(%d+)")
      g:led(tonumber(sx), tonumber(sy), 15)
    end
  end
  g:refresh()
end

-- normalized value (0..1) of a param, for drawing the rings.
-- integer params are computed from their range, the others
-- ask the paramset (with a safe fallback).
local function param_norm(id)
  local r = PARAM_RANGE[id]
  if r then
    return util.clamp((params:get(id) - r[1]) / (r[2] - r[1]), 0, 1)
  end
  local ok, v = pcall(function() return params:get_raw(id) end)
  if ok and type(v) == "number" then return util.clamp(v, 0, 1) end
  return 0
end

local function arc_redraw()
  if not (a and a.device) then return end
  a:all(0)
  local pg = ARC_PAGES[arc_page]
  for n = 1, 4 do
    local raw = param_norm(pg[n])
    local head = util.clamp(math.floor(raw * 63 + 0.5) + 1, 1, 64)
    local glow = math.floor(arc_flash[n] * 4)
    for x = 1, 64 do
      local l = glow
      if x <= head then l = l + 4 end
      if x == head then l = 15 end
      if l > 0 then a:led(n, x, math.min(15, l)) end
    end
  end
  a:refresh()
end

local function arc_delta(n, d)
  if intro then return end
  local id = ARC_PAGES[arc_page][n]
  if not id then return end
  local thr = ARC_INT[id]
  if thr then
    -- integer params: one step every "thr" arc units
    arc_acc[n] = arc_acc[n] + d
    local steps = 0
    while arc_acc[n] >= thr do
      arc_acc[n] = arc_acc[n] - thr
      steps = steps + 1
    end
    while arc_acc[n] <= -thr do
      arc_acc[n] = arc_acc[n] + thr
      steps = steps - 1
    end
    if steps ~= 0 then params:delta(id, steps) end
  else
    params:delta(id, d * ARC_SENS)
  end
  arc_id = id
  arc_idle = 0
  arc_redraw()   -- the ring follows your finger right away
end

---------------------------------------------------------------
-- PARAMETERS
---------------------------------------------------------------
-- looks for the first of "names" in "list" (ignoring case and the
-- difference between "ghost piano" and "ghost_piano")
local function find_idx(list, names)
  local function norm(s) return (tostring(s):gsub("_", " "):lower()) end
  for _, want in ipairs(names) do
    for i, n in ipairs(list) do
      if norm(n) == norm(want) then return i end
    end
  end
  return 1
end

local function jf_setup()
  if not (crow and crow.ii) then return end
  for v = 1, 3 do
    if params:get(pid(v, "jf")) == 2 then
      crow.ii.pullup(true)
      crow.ii.jf.mode(1)
      return
    end
  end
end

local VOICE_DEFAULTS = {
  { cut = 800,  rel = 5, pan = -0.3, ch = 1, inst = { "steinway b", "ghost piano", "kalimba" } },
  { cut = 2000, rel = 3.5, pan = 0.3,  ch = 2, inst = { "kalimba", "ghost piano", "steinway b" } },
  { cut = 2800, rel = 3, pan = 0.0,  ch = 3, inst = { "ghost piano", "steinway b", "kalimba" } },
}

local function add_params()
  local inst_list = { "-" }
  if skeys then
    local ok, l = pcall(function() return skeys:list_instruments() end)
    if ok and type(l) == "table" and #l > 0 then
      inst_list = l
    elseif ok then
      print("NEVE: mx.samples has no instruments (download some from the mx.samples script)")
      mx_msg = "mx: no samples installed"
    else
      print("NEVE: cannot list mx.samples instruments: " .. tostring(l))
      mx_msg = "mx: can't read instruments"
    end
  end

  params:add_separator("NEVE by VRCVS")

  -- SOUND: global choices
  params:add_group("sound", 2)
  params:add_option("engine_pick", "synth engine", { "PolyPerc", "mx.samples" }, engine_choice)
  params:set_action("engine_pick", function(v)
    if not ready or v == engine_choice then return end
    if v == 2 and not util.file_exists(_path.code .. "mx.samples/lib/mx.samples.lua") then
      -- do not reload for nothing: mx.samples is not installed
      print("NEVE: mx.samples is not installed. In maiden: ;install https://github.com/schollz/mx.samples")
      mx_msg = "mx: not installed"
      ui_msg = mx_msg
      ui_msg_t = 10
      params:set("engine_pick", engine_choice, true)
      return
    end
    -- switching the synth engine requires reloading the script:
    -- the screen freezes for a few seconds, then the cover comes back
    -- (deferred so a preset being loaded can finish loading first)
    clock.run(function()
      clock.sleep(0.3)
      save_cfg(v, last_pset)
      norns.script.load(norns.state.script)
    end)
  end)
  params:add_number("midi_dev", "MIDI device", 1, 4, 1)
  params:set_action("midi_dev", function(v) midi_dev = midi.connect(v) end)

  -- VOICES: each one has its own outputs
  -- (group names must differ from param ids)
  for v = 1, 3 do
    local d = VOICE_DEFAULTS[v]
    params:add_group("voice " .. v .. ": " .. VOICE_NAMES[v], 10)
    params:add_option(pid(v, "eng"), "synth engine out", { "off", "on" }, 2)
    params:add_control(pid(v, "vol"), "synth volume", controlspec.new(0, 1, "lin", 0.01, 0.5))
    params:add_option(pid(v, "inst"), "mx.samples instrument", inst_list, find_idx(inst_list, d.inst))
    params:add_control(pid(v, "cut"), "cutoff (PolyPerc)", controlspec.new(200, 8000, "exp", 0, d.cut, "hz"))
    params:add_control(pid(v, "rel"), "release (PolyPerc)", controlspec.new(0.5, 12, "lin", 0.1, d.rel))
    params:add_control(pid(v, "pan"), "pan (PolyPerc)", controlspec.new(-1, 1, "lin", 0.01, d.pan))
    params:add_option(pid(v, "midi"), "MIDI out", { "off", "on" }, 1)
    params:add_number(pid(v, "ch"), "MIDI channel", 1, 16, d.ch)
    params:add_option(pid(v, "jf"), "Just Friends out", { "off", "on" }, 1)
    params:set_action(pid(v, "jf"), function(x)
      if ready and x == 2 and crow and crow.ii then
        crow.ii.pullup(true)
        crow.ii.jf.mode(1)
      end
    end)
    params:add_number(pid(v, "jfoct"), "Just Friends octave", -3, 3, 0)
  end

  -- SCALE: all the ones in musicutil
  params:add_group("scale & harmony", 5)
  params:add_option("scale", "scale / mode", scale_names, find_idx(scale_names, { "Dorian", "Minor" }))
  params:set_action("scale", function() if ready then build_scale() end end)
  params:add_option("root", "root", NOTE_NAMES, 3)
  params:set_action("root", function() if ready then build_scale() end end)
  params:add_number("octave", "base octave", 1, 3, 2)
  params:set_action("octave", function() if ready then build_scale() end end)
  params:add_option("prog", "harmony", PROG_NAMES, 1)
  params:add_number("harm_notes", "harmony change (beats)", 4, 64, 16)

  -- GENERATIVE
  params:add_group("generative", 11)
  params:add_option("style", "style", { "snow (random)", "slow cell", "arpeggio" }, 2)
  params:add_option("arp_dir", "arpeggio direction", { "up", "down", "up & down" }, 3)
  params:set_action("style", function() slow_next = nil; last_bass_t = -99 end)
  params:add_number("quantity", "amount", 1, 24, 5)
  params:add_control("freq", "note frequency", controlspec.new(0.2, 4, "exp", 0, 1))
  params:add_control("melvar", "melodic variation", controlspec.new(0, 1, "lin", 0.01, 0.25))
  params:add_control("rhythm_var", "rhythmic variation", controlspec.new(0, 1, "lin", 0.01, 0.35))
  params:add_number("vel_min", "velocity min", 1, 127, 30)
  params:add_number("vel_max", "velocity max", 1, 127, 85)
  params:add_control("note_len", "note length (s)", controlspec.new(0.3, 12, "lin", 0.1, 3))
  params:add_control("wind", "wind", controlspec.new(-1, 1, "lin", 0.01, 0))
  params:add_option("quant", "quantization", QUANT_NAMES, 2)

  -- LIVE (grid)
  params:add_group("live (grid)", 4)
  params:add_option("live_quant", "live quantization", LIVE_QUANT_NAMES, 1)
  params:add_number("live_vel", "live velocity", 1, 127, 80)
  params:add_number("live_oct", "live octave", -2, 2, 0)
  params:set_action("live_oct", function() if ready then build_scale() end end)
  params:add_option("learn", "learn motif from live", { "off", "on" }, 1)

  -- EFFECTS
  params:add_group("delay & reverb", 7)
  params:add_control("delay_mix", "delay: level", controlspec.new(0, 1, "lin", 0.01, 0.3))
  params:set_action("delay_mix", function() if ready then apply_delay() end end)
  params:add_option("delay_time", "delay: time", DELAY_NAMES, 4)
  params:set_action("delay_time", function() if ready then update_delay_time() end end)
  params:add_control("delay_fb", "delay: feedback", controlspec.new(0, 0.95, "lin", 0.01, 0.5))
  params:set_action("delay_fb", function() if ready then apply_delay() end end)
  params:add_control("delay_tone", "delay: tone", controlspec.new(500, 8000, "exp", 0, 3500, "hz"))
  params:set_action("delay_tone", function() if ready then apply_delay() end end)
  params:add_control("reverb_send", "reverb: level", controlspec.new(-60, 0, "lin", 0.5, -12, "dB"))
  params:set_action("reverb_send", function() if ready then apply_reverb() end end)
  params:add_control("reverb_time", "reverb: time", controlspec.new(1, 20, "lin", 0.1, 8, "s"))
  params:set_action("reverb_time", function() if ready then apply_reverb() end end)
  params:add_control("reverb_damp", "reverb: damping", controlspec.new(1500, 20000, "exp", 0, 6000, "hz"))
  params:set_action("reverb_damp", function() if ready then apply_reverb() end end)
end

---------------------------------------------------------------
-- INIT / CLEANUP / CONTROLS
---------------------------------------------------------------
function init()
  math.randomseed(os.time())

  if engine_choice == 2 and mxsamples then
    local ok, inst = pcall(function() return mxsamples:new() end)
    if ok and inst then
      skeys = inst
    else
      print("NEVE: mx.samples failed to start: " .. tostring(inst))
      mx_msg = "mx: failed to start"
    end
  end

  add_params()
  midi_dev = midi.connect(1)
  params:set("clock_tempo", 60)
  -- remember which preset the user loads (needed for engine switches)
  local orig_read = params.read
  params.read = function(self, filename, silent)
    if filename ~= nil then last_pset = filename end
    return orig_read(self, filename, silent)
  end
  -- always start with NEVE's own defaults; only after an engine switch
  -- triggered by a preset, reload that same preset
  if pending_pset then
    pcall(function() params:read(tonumber(pending_pset) or pending_pset) end)
  end
  -- the running engine always wins over what the preset says
  params:set("engine_pick", engine_choice, true)
  params:bang()

  build_scale()
  next_harmony()
  new_motif()
  motif_i = #motif + 1          -- the first tear opens a new phrase
  lead_pos = math.random(lead_lo, lead_hi)
  ready = true

  setup_delay()
  apply_delay()
  apply_reverb()
  jf_setup()

  g = grid.connect()
  g.key = grid_key
  a = arc.connect()
  a.delta = arc_delta

  ui_metro = metro.init()
  ui_metro.time = DT
  ui_metro.event = function()
    -- a problem inside update() must not freeze the screen
    local ok, err = pcall(update, DT)
    if not ok and not led_err.update then
      led_err.update = true
      print("NEVE update error: " .. tostring(err))
      ui_msg = "error: see maiden"
      ui_msg_t = 8
    end
    redraw()
    if frame % 2 == 0 then
      -- a problem in one of them must not stop the other
      local ok, err = pcall(grid_redraw)
      if not ok and not led_err.grid then
        led_err.grid = true
        print("NEVE grid error: " .. tostring(err))
      end
      ok, err = pcall(arc_redraw)
      if not ok and not led_err.arc then
        led_err.arc = true
        print("NEVE arc error: " .. tostring(err))
      end
    end
  end
  ui_metro:start()
end

function cleanup()
  if ui_metro then ui_metro:stop() end
  -- release the live notes that are still held
  for _, st in pairs(held) do
    pcall(function() voice_off(3, st.note) end)
  end
  if midi_dev then
    pcall(function()
      for v = 1, 3 do
        midi_dev:cc(123, 0, params:get(pid(v, "ch")))
      end
    end)
  end
  -- restore the system settings (reverb, softcut)
  for id, v in pairs(sys_orig) do
    pcall(function() params:set(id, v) end)
  end
  pcall(function() audio.level_eng_cut(0) end)
  -- turn off the grid and arc lights
  pcall(function()
    if g and g.device then g:all(0) g:refresh() end
    if a and a.device then a:all(0) a:refresh() end
  end)
end

function key(n, z)
  if z ~= 1 then return end
  if intro then
    if n == 3 then
      intro = false
      running = true
      t_run = 0
      -- if mx.samples had a problem at load time, say so now
      if mx_msg then
        ui_msg = mx_msg
        ui_msg_t = 8
      end
    end
    return
  end
  if n == 2 then
    toggle_pause()
  elseif n == 3 then
    next_harmony()
  end
end

function enc(n, d)
  if intro then return end
  ui_idle = 0
  arc_idle = 99
  if n == 1 then
    page = util.clamp(page + (d > 0 and 1 or -1), 1, #pages)
  else
    params:delta(pages[page][n - 1][1], d)
  end
end
