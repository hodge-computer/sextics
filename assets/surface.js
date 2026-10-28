/* Page-side controls and watchdog. Never create a WebGL context on this thread. */
(() => {
  'use strict';
  const workerURL = new URL('surface-worker.js', document.currentScript.src);
  const TIMEOUT = 5000,
    BOOT_TIMEOUT = 30000;
  function create(canvas, { onStatus = () => {}, onModeChange = () => {} } = {}) {
    let worker = null,
      failed = false,
      destroyed = false,
      mode = 'parallax',
      meta = null,
      camera = null,
      record = null;
    let lastPulse = performance.now(),
      lastTick = lastPulse,
      watchdog;
    let wasHidden = document.hidden,
      recoveryAllowed = false,
      recoveryPending = false,
      resumeUntil = 0;
    const motionPreference = matchMedia('(prefers-reduced-motion: reduce)');
    let tiltCenter = null,
      tiltAngle = null,
      lastTilt = -Infinity,
      usingTilt = false;
    const listeners = [],
      canvasListeners = [];
    const listen = (target, name, callback, options, removers = listeners) => {
      target.addEventListener(name, callback, options);
      removers.push(() => target.removeEventListener(name, callback, options));
    };
    const send = (message) => {
      if (!destroyed && worker) worker.postMessage(message);
    };
    function resetTilt() {
      tiltCenter = null;
      lastTilt = -Infinity;
      if (usingTilt)
        send({ type: 'input', target: 'view', name: 'parallax', properties: { x: 0, y: 0 } });
    }
    const size = () => ({
      width: canvas.clientWidth,
      height: canvas.clientHeight,
      innerWidth,
      innerHeight,
      devicePixelRatio: devicePixelRatio || 1
    });
    function release() {
      clearInterval(watchdog);
      worker?.terminate();
      worker = null;
      canvasListeners.splice(0).forEach((remove) => remove());
      // A new worker receives a new drawing surface. Never reuse GPU handles
      // from a lost context, even if the browser later restores that context.
      const blank = canvas.cloneNode(false);
      blank.classList.remove('free-camera');
      blank.style.touchAction = 'auto';
      canvas.replaceWith(blank);
      canvas = blank;
      meta = null;
      camera = null;
    }
    function stop(message, recoverable = true) {
      if (failed || destroyed) return;
      const recovering =
        recoverable &&
        recoveryAllowed &&
        (document.hidden || wasHidden || performance.now() < resumeUntil);
      release();
      recoveryAllowed = false;
      if (recovering) {
        recoveryPending = true;
        onStatus({ state: 'loading', message: 'Restoring the saved slice…' });
        if (!document.hidden) start();
        return;
      }
      failed = true;
      recoveryPending = false;
      console.warn('Surface paused:', message);
      onStatus({ state: 'error', message });
    }
    function setMode(value) {
      mode = value === 'free' ? 'free' : 'parallax';
      resetTilt();
      if (!failed && !destroyed && worker) {
        canvas.classList.toggle('free-camera', mode === 'free');
        canvas.style.touchAction = mode === 'free' ? 'none' : 'auto';
        send({ type: 'mode', mode });
      }
      onModeChange(mode);
    }
    const api = {
      async setCase(selected) {
        if (failed || destroyed) return;
        resetTilt();
        // Only presentation data crosses the worker boundary, not the proof/text.
        record = {
          id: selected.id,
          title: selected.title,
          F: selected.F.terms,
          render: selected.render,
          formalStatus: selected.formalStatus
        };
        meta = null;
        camera = null;
        onStatus({ state: 'loading', message: 'Preparing the saved slice…' });
        send({ type: 'case', record });
      },
      setMode,
      resetCamera: () => send({ type: 'reset' }),
      getMode: () => mode,
      getMeta: () => meta,
      getCamera: () => camera,
      destroy() {
        if (destroyed) return;
        destroyed = true;
        release();
        listeners.splice(0).forEach((remove) => remove());
      }
    };
    // Older browsers keep the atlas usable instead of falling back to blocking GL.
    if (typeof Worker === 'undefined' || !canvas.transferControlToOffscreen) {
      stop('This browser cannot run the 3D view separately from the page.', false);
      return api;
    }
    const keys = [
      'pointerId',
      'pointerType',
      'clientX',
      'clientY',
      'button',
      'deltaY',
      'key',
      'shiftKey',
      'altKey',
      'ctrlKey',
      'metaKey'
    ];
    function input(target, name, event) {
      // Scrolling must not replace the sensor's parallax with a finger position.
      if (usingTilt && target === 'view' && event.pointerType === 'touch') return;
      const properties = {};
      for (const key of keys) if (event[key] !== undefined) properties[key] = event[key];
      if (name === 'keydown') {
        if (event.metaKey || event.ctrlKey || event.altKey || event.target?.closest?.(
          'input,textarea,select,[contenteditable="true"]'
        )) return;
        if (mode === 'free' && event.key.startsWith('Arrow')) event.preventDefault();
      }
      send({ type: 'input', target, name, properties });
    }
    function start() {
      if (destroyed || failed || worker) return;
      recoveryPending = false;
      lastPulse = lastTick = performance.now();
      try {
        const current = new Worker(workerURL);
        worker = current;
        let booted = false;
        current.onmessage = ({ data }) => {
          if (worker !== current || destroyed) return;
          lastPulse = performance.now();
          booted = true;
          if (data.type === 'fatal') {
            stop(data.value);
            return;
          }
          if (data.type === 'status') {
            if (data.value.meta) meta = data.value.meta;
            onStatus(data.value);
          } else if (data.type === 'mode' && mode !== data.value) {
            mode = data.value;
            resetTilt();
            canvas.classList.toggle('free-camera', mode === 'free');
            canvas.style.touchAction = mode === 'free' ? 'none' : 'auto';
            onModeChange(mode);
          } else if (data.type === 'label') canvas.setAttribute('aria-label', data.value);
          else if (data.type === 'pulse' && data.value) camera = data.value;
        };
        current.onerror = (event) => {
          event.preventDefault();
          if (worker === current) stop(event.message || 'The 3D view could not start.');
        };
        current.onmessageerror = () => {
          if (worker === current) stop('The 3D view could not communicate with the page.');
        };
        const offscreen = canvas.transferControlToOffscreen();
        current.postMessage(
          {
            type: 'init',
            canvas: offscreen,
            size: size(),
            hidden: document.hidden,
            reducedMotion: motionPreference.matches
          },
          [offscreen]
        );
        if (record) send({ type: 'case', record });
        canvas.classList.toggle('free-camera', mode === 'free');
        canvas.style.touchAction = mode === 'free' ? 'none' : 'auto';
        send({ type: 'mode', mode });
        watchdog = setInterval(() => {
          const now = performance.now(),
            delayed = now - lastTick > TIMEOUT;
          lastTick = now;
          if (document.hidden) return;
          // A suspended page may run a queued timer before visibilitychange.
          // Give it a fresh deadline; a continuously blocked worker still times out.
          if (delayed) {
            lastPulse = now;
            send({ type: 'visibility', hidden: false });
            return;
          }
          if (now - lastPulse > (booted ? TIMEOUT : BOOT_TIMEOUT))
            stop(
              booted
                ? 'The 3D view stopped responding and has been paused to keep the page usable.'
                : 'The 3D renderer could not finish downloading. Reload the page to try again.'
            );
        }, 500);
        for (const name of [
          'contextmenu',
          'dblclick',
          'wheel',
          'pointerdown',
          'pointermove',
          'pointerup',
          'pointercancel',
          'lostpointercapture'
        ])
          listen(
            canvas,
            name,
            (event) => {
              if (mode !== 'free') return;
              if (event.cancelable) event.preventDefault();
              if (name === 'pointerdown') canvas.setPointerCapture?.(event.pointerId);
              input('canvas', name, event);
              if (name === 'pointerup' || name === 'pointercancel') {
                try {
                  canvas.releasePointerCapture?.(event.pointerId);
                } catch (_) {}
              }
            },
            { passive: false },
            canvasListeners
          );
      } catch (error) {
        stop(error.message || 'The 3D view could not start.', false);
      }
    }
    listen(window, 'resize', () => send({ type: 'size', size: size() }), { passive: true });
    listen(document, 'visibilitychange', () => {
      resetTilt();
      const hidden = document.hidden,
        returning = wasHidden && !hidden;
      if (hidden && !wasHidden && !failed) recoveryAllowed = true;
      // Include the watchdog's next tick after the five-second deadline.
      if (returning) resumeUntil = performance.now() + TIMEOUT + 1000;
      wasHidden = hidden;
      lastPulse = lastTick = performance.now();
      if (returning && recoveryPending) start();
      else send({ type: 'visibility', hidden });
    });
    for (const name of ['pointermove', 'pointerleave', 'blur', 'keydown', 'keyup'])
      listen(window, name, (event) => input('view', name, event), { passive: name !== 'keydown' });
    // Never request sensor permission. Browsers requiring it silently retain
    // the ordinary background view; already-granted access is usable as-is.
    const orientation = window.DeviceOrientationEvent;
    function startTilt() {
      if (destroyed || failed || motionPreference.matches) return;
      listen(
        window,
        'deviceorientation',
        (event) => {
          if (
            destroyed ||
            failed ||
            !worker ||
            document.hidden ||
            mode !== 'parallax' ||
            motionPreference.matches
          )
            return;
          if (![event.alpha, event.beta, event.gamma].every(Number.isFinite)) return;
          const now = performance.now();
          if (now - lastTilt < 32) return;
          lastTilt = now;
          const angle = window.screen.orientation.angle;
          if (angle !== tiltAngle) {
            tiltCenter = null;
            tiltAngle = angle;
          }
          // Relative quaternions avoid beta/gamma's angle jumps when a phone is
          // held upright. No compass heading or geographic position is needed.
          const half = Math.PI / 360,
            a = event.alpha * half;
          const b = event.beta * half,
            g = event.gamma * half;
          const ca = Math.cos(a),
            sa = Math.sin(a),
            cb = Math.cos(b),
            sb = Math.sin(b),
            cg = Math.cos(g),
            sg = Math.sin(g);
          const q = [
            ca * sb * cg - sa * cb * sg,
            ca * cb * sg + sa * sb * cg,
            sa * cb * cg + ca * sb * sg,
            ca * cb * cg - sa * sb * sg
          ];
          if (!tiltCenter) tiltCenter = q;
          const [x, y, z, w] = tiltCenter,
            [u, v, t, s] = q;
          const rw = w * s + x * u + y * v + z * t,
            direction = rw < 0 ? -1 : 1;
          const tiltX = 2 * Math.atan2(direction * (w * u - x * s - y * t + z * v), Math.abs(rw));
          const tiltY = 2 * Math.atan2(direction * (w * v + x * t - y * s - z * u), Math.abs(rw));
          const rotation = (angle * Math.PI) / 180,
            c = Math.cos(rotation),
            sn = Math.sin(rotation);
          const limit = (18 * Math.PI) / 180;
          const bounded = (v) => (Math.abs(v) < 0.015 ? 0 : Math.max(-1, Math.min(1, v)));
          usingTilt = true;
          send({
            type: 'input',
            target: 'view',
            name: 'parallax',
            properties: {
              x: bounded((tiltY * c + tiltX * sn) / limit),
              y: bounded((tiltX * c - tiltY * sn) / limit)
            }
          });
        },
        { passive: true }
      );
      listen(window, 'orientationchange', resetTilt, { passive: true });
      listen(window, 'blur', resetTilt, { passive: true });
    }
    if (
      window.isSecureContext &&
      matchMedia('(pointer: coarse)').matches &&
      !motionPreference.matches &&
      orientation
    ) {
      if (typeof orientation.requestPermission !== 'function') startTilt();
      else if (window.navigator?.permissions) {
        Promise.all(
          ['accelerometer', 'gyroscope'].map(async (name) =>
            window.navigator.permissions.query({ name })
          )
        )
          .then((states) => {
            if (states.every((s) => s.state === 'granted')) startTilt();
          })
          .catch(() => {}); // Unavailable permission information leaves tilt disabled.
      }
    }
    // An initially backgrounded tab need not allocate GPU resources yet.
    if (document.hidden) recoveryPending = true;
    else start();
    return api;
  }
  window.HodgeRenderer = Object.freeze({ create });
})();
