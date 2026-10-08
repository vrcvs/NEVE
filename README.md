# NEVE

**by VRCVS** — a generative ambient sequencer for [monome norns](https://monome.org/docs/norns/), with grid and arc support.

Snow falls, tears run down a stylised face. Every snowflake that hits the bottom plays a low note, every tear that detaches plays a high one. A third voice is yours, to play live on the grid.

## Features

- **Three independent voices**: snow (bass), tears (melody) and live (grid). Each one can go to the internal engine (PolyPerc or [mx.samples](https://github.com/schollz/mx.samples)), MIDI and Just Friends (crow i2c), alone or combined.
- **Harmony that fits the scale**: all `musicutil` scales and modes. The default "auto" progression is built from the stable chords of the current scale and root, and chords change on bar boundaries. The melody follows the current chord.
- **Three styles** (`PARAMS > generative > style`):
  - `slow cell` (default): a 4-note cell with a fixed rhythm, slow chords, pedal bass.
  - `arpeggio`: a steady arpeggio on the chord with a long top note (up / down / up & down).
  - `snow (random)`: randomly falling notes, busier and less predictable.
- **Grid** (128, varibright): row 1 chooses the chord and has the controls (learn, octave, arc page, next chord, pause); rows 2-8 are an isomorphic keyboard locked to the scale. `learn` turns your live phrases into the motif of the tears.
- **Arc** (4 rings, no buttons needed): 3 pages of parameters with visual feedback — amount, frequency, melodic and rhythmic variation, velocity min/max, note length, wind, delay and reverb.
- **Delay and reverb**, and presets: NEVE always starts with its own defaults; a preset restores everything, engine included.

## Requirements

- norns. Works out of the box with the internal PolyPerc engine.
- Optional: grid, arc, [mx.samples](https://github.com/schollz/mx.samples) (`;install https://github.com/schollz/mx.samples` in maiden), a MIDI device, crow + Just Friends.

## Install

From maiden: `;install https://github.com/vrcvs/NEVE`
(or find NEVE in the community catalog), then restart and load it from SELECT.

## Quick start

Load NEVE, press **K3** on the cover, then listen. Turn the encoders (E1 changes page), touch the grid, turn the arc.

| Control | Action |
| --- | --- |
| E1 | page |
| E2 / E3 | parameters of the page |
| K2 | pause / resume |
| K3 | next harmony (on the cover: start) |
| Grid row 1 | choose chord + controls |
| Grid rows 2-8 | live keyboard |
| Arc | 3 pages x 4 rings of parameters |

Visual guides (PDF) in English and Italian are in [`docs/`](docs/).

## Notes

- Switching between PolyPerc and mx.samples reloads the script (a norns engine limitation): the screen freezes for a few seconds, then the cover returns.
- Each voice has its own volume and octave/offset parameters, so levels can be balanced for your setup.

## License

MIT, see [LICENSE](LICENSE).
