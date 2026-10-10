# STANDARD OPERATING PSYCHOPATHY

A post-apocalyptic bunker-management sim in the spirit of **Sheltered × Oxygen
Not Included × BoomTown**, skinned as an institutional surveillance terminal in the
aesthetic of the **Neue Deutsche Welle** — monochrome CRT amber, hard sans-serif
propaganda headers, and cold motorik audio.

You do not control the inmates directly. You manage the **grid** — power, air,
food, and excavation — while your subjects act on their own drives.

**v0.2 adds the surface.** Build a **Luftschleuse** (airlock) into the bunker
ceiling to send subjects on **expeditions** for Öl, Konserven and Schrott, and
to receive **Neuzugänge** (new subjects) — a powered **Funkturm** (radio tower)
doubles their arrival rate. Progress is persisted with **save / load**
(localStorage) plus a file export / import fallback.

---

## The fantasy

> Die Oberfläche ist erledigt. Sie überwachen Sektor 4.

The UI is diegetic: a rigid engineering monitor inside the bunker. Everything
is uppercase German institutional copy. The bottom strip is a looping
`DURCHSAGE` (announcement) ticker of NDW-flavored slogans.

## Systems

| System | What it does |
| --- | --- |
| **Conative Utility AI** | Each subject scores every possible action against its *Affective* state (Stress / Hunger / Erschöpfung / Argwohn / O₂-Mangel) and commits to the highest-scoring directive. No state machines. |
| **Blackboard** | Shared memory where dig orders, hazards, and electrical nodes are posted. Subjects read it to pick work. |
| **Power graph** | Devices are wired into components (Crosslink). Generation vs. draw decides whether a component is powered. Batteries buffer. |
| **Gas / O₂ diffusion** | A Laplacian spread over the grid. Digging can rupture gas pockets. Scrubbers clean. |
| **Ecology** | Farms grow rations from power. The generator burns **Öl** (dug up). Excavation yields caches of Beton / Metall / Rationen / Öl. |
| **Disasters** | Erdbeben break devices and spike stress. High-stress Pyromanes sabotage wiring. |
| **Surface** | The airlock is the only way out. An expedition sends one subject topside for a timer; they return with weighted loot and a chance of injury. New subjects arrive at the gate on their own schedule. |
| **Persistence** | Autosave every ~5 min, manual save/load, and JSON export/import of the whole Akte. |

## Traits

- **Pyromane** — triggers a psychotic break (cuts a wire) at very high stress.
- **Paranoid** — panics in darkness, needs light.
- **Befehlsfixiert** — digs harder, ignores warnings.
- **Schlafwandler** — sleeps anywhere.

## Controls

| Key / input | Action |
| --- | --- |
| `1–8`, `9`, `0` | Select a module to build |
| `Q` | Luftschleuse (airlock) — place on the ceiling row |
| `F` | Funkturm (radio tower) — doubles arrival rate |
| `W` | Build wall |
| `X` | Dig order (click dirt to mark) |
| `V` | Toggle Physical ↔ Crosslink |
| `E` | Toggle selected device on/off |
| `F5` | Save |
| `M` | Toggle audio |
| `Space` | Pause |
| `Esc` | Cancel placement |
| Click module in **Crosslink** twice | Wire / unwire two nodes (≤ 8 tiles) |
| Click the airlock | Open the expedition panel: pick a subject, send them topside |

## Device table

| Module | Watts | Role |
| --- | --- | --- |
| Tretbar-Dynamo | −60 | Hand-cranked power (a subject must work it) |
| Lampe | +12 | Light radius 4, suppresses dark-stress |
| Pritsche | 0 | Bed |
| Rationen-Ausgabe | +5 | Serves meals (needs power + rations) |
| Luft-Wäscher | +25 | Scrubs gas, emits O₂ |
| Notstromaggregat | −100 | Burns 1 Öl / 35 s |
| Schott | +10 | Door; blocks path while unpowered |
| Bewegungssensor | +5 | Can be coupled to a Schott |
| Akku-Block | 0 | Stores 2000 units of charge |
| Pilzfarm | +15 | Grows 1 ration / 30 s of power |
| Luftschleuse | 0 | Surface gate. One per sector, only on the ceiling row. Expedition + arrival point. |
| Funkturm | +30 | Broadcasts on all bands; halves the interval between new subjects. |

## Layout

```
game/
  index.html      shell + HUD
  style.css       brutalist CRT theme
  config.js       all tuning constants & data
  world.js        grid, devices, power graph, gas diffusion, Blackboard
  ai.js           Conative Utility AI (drives, pathing, execution)
  render.js       Physical + Crosslink canvas layers
  ui.js           inspector, build menu, log, overlays
  main.js         loop, input, events, day cycle
  audio.js        cold-wave sequencer (WebAudio)
  tools/smoke.js  headless simulation harness
  tools/dom_test.js  jsdom boot/integration test
```

## Tuning

Every balance number lives in `config.js`. The sim has been validated with
`tools/smoke.js` (headless) across long runs with earthquakes; the colony is
survivable with sensible play.

## NDW styling notes

- Palette: phosphor amber `#ffb000` on abyssal black `#050505`; alert red
  `#ff0033`; Crosslink cyan `#00ccff`.
- Typography: monospace body, `Arial Black` headers with wide letter-spacing.
- CRT scanlines + phosphor bloom overlay; hard edges, no border-radius.
- Audio: 4-on-the-floor kick, off-beat hats, sawtooth bassline ~126 BPM.
