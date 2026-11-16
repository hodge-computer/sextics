/* The optional WebGL view lives off the page's UI thread. */
'use strict';

const view = new EventTarget(), page = new EventTarget();
let renderer, canvas, stopped = false;
function send(type, value) { if (!stopped) postMessage({type, value}); }
function fatal(message) {
  if (stopped) return;
  send('fatal', message); stopped = true; close();
}
function dispatch(target, name, properties = {}) {
  target.dispatchEvent(Object.assign(new Event(name, {cancelable:true}), properties));
}
function present() {
  if (stopped) return;
  const frame = canvas.transferToImageBitmap();
  postMessage({type:'frame', value:frame}, [frame]);
}
function resize(size) {
  Object.assign(view, size);
  canvas.clientWidth = size.width; canvas.clientHeight = size.height;
  dispatch(view, 'resize');
}
// A live worker can still be waiting on a dead GPU: the core separately times
// out its GPU fence. This pulse catches blocked JS, shader compilation or drivers.
setInterval(() => send('pulse', renderer?.getCamera()), 500);
onerror = event => { event.preventDefault(); fatal(event.message || 'Surface worker failed.'); };
onunhandledrejection = event => { event.preventDefault(); fatal(event.reason?.message || 'Surface worker failed.'); };
function handleMessage({data}) {
  if (stopped) return;
  try {
    switch (data.type) {
      case 'init':
        // A worker-owned canvas, not a transferred placeholder: iOS Safari showed
        // a transferred canvas at low resolution and with distorted proportions.
        canvas = new OffscreenCanvas(data.size.pixelWidth, data.size.pixelHeight);
        page.hidden = data.hidden;
        resize(data.size);
        renderer = HodgeSurfaceCore.create(canvas, {
          host:{view, page, reducedMotion:data.reducedMotion},
          onStatus:value => send('status', value),
          onModeChange:value => send('mode', value),
          onLabel:value => send('label', value),
          onFatal:fatal,
          onFrame:present
        });
        send('initialized');
        break;
      case 'case':
        renderer.setCase(data.record).catch(error => {
          // Core reports current errors and ignores superseded loads.
          if (error.message !== 'Cancelled') console.warn('Surface:', error.message);
        });
        break;
      case 'mode': renderer.setMode(data.mode); break;
      case 'reset': renderer.resetCamera(); break;
      case 'size': resize(data.size); break;
      case 'visibility':
        page.hidden = data.hidden; dispatch(page, 'visibilitychange'); break;
      case 'input': dispatch(data.target === 'canvas' ? canvas : view, data.name, data.properties); break;
    }
  } catch (error) { fatal(error.message || String(error)); }
};

// Fetch dependencies asynchronously: the heartbeat must remain live while the
// network is slow. Queue controls until the renderer is available.
const pending = [];
onmessage = event => pending.push(event);
send('booting');
Promise.all([import('./divisor.js'), import('./mesh.js'), import('./slice-mesh.js'), import('./renderer.js')]).then(() => {
  if (stopped) return;
  onmessage = handleMessage;
  for (const event of pending) {
    if (stopped) break;
    handleMessage(event);
  }
  pending.length = 0;
}).catch(error => fatal(error.message || 'The renderer could not be downloaded.'));
