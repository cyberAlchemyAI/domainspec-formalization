# Visualization

Interactive fractal visualizations that run directly in any browser — no install, no server, no dependencies.

## fractals/fractal-ghibli.html

An infinite Julia Set explorer styled after Studio Ghibli color palettes. Open the HTML file and explore.

**How to run:** double-click `fractals/fractal-ghibli.html` or drag it into any modern browser tab.

### What you can do

- **Explore the fractal** — drag to pan, scroll to zoom, or use the three parameter sliders (*Espírito*, *Profundidade*, *Essência*) to reshape the Julia Set in real time.
- **Dive** — press the `▼ Mergulhar` button or hit `Space` to fall infinitely into the fractal center at 60 fps. The dive does not stop at the float64 precision wall — a perturbation kernel takes over and carries you to ~10³⁰× magnification before the fall asymptotes smoothly.
- **Switch themes** — five Ghibli-inspired palettes: Totoro, Spirited Away, Mononoke, Howl, and Nausicaä. Each produces a distinct color ramp across the escape-time values.
- **Audio reactivity** — load any audio file (mp3, wav, ogg, m4a). The frequency spectrum is split into four bands that modulate the fractal parameters in real time. Bass hits cycle the color theme; the full ambient layer (vignette, edge particles, background haze, HUD glow, micro camera shake) responds to the music.
- **Performance diagnostics** — append `?perf=1` to the URL or press `P` to reveal the hidden diagnostics overlay (render times, frame drops). It never alters the default visual output.

### Technical notes

- Everything runs in a single self-contained HTML file — no network requests, no external scripts, no fonts.
- Fractal iteration (`z_{n+1} = z_n² + c`) runs off the main thread via a Web Worker, so the UI stays responsive during computation.
- Audio analysis uses the Web Audio API (`AnalyserNode`); only one `AudioContext` is created per session, shared between the parameter modulator and the ambient scene.
- Band sensitivities and ambient intensity are persisted via `localStorage` across reloads; no audio data leaves the page.
