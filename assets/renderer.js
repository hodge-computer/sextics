/* WebGL surface renderer used by the visualization worker. */
(() => {
  'use strict';
  function shader(gl, type, source) {
    const s = gl.createShader(type);
    if (!s) throw new Error('The graphics device could not allocate a shader.');
    gl.shaderSource(s, source);
    gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) {
      const info = gl.getShaderInfoLog(s);
      gl.deleteShader(s);
      throw new Error('Shader compilation failed: ' + info);
    }
    return s;
  }

  function program(gl, vsSource, fsSource) {
    const p = gl.createProgram(),
      compiled = [];
    if (!p) throw new Error('The graphics device could not allocate a program.');
    try {
      compiled.push(shader(gl, gl.VERTEX_SHADER, vsSource));
      compiled.push(shader(gl, gl.FRAGMENT_SHADER, fsSource));
      for (const s of compiled) gl.attachShader(p, s);
      gl.linkProgram(p);
      if (!gl.getProgramParameter(p, gl.LINK_STATUS))
        throw new Error('Shader link failed: ' + gl.getProgramInfoLog(p));
      return p;
    } catch (error) {
      gl.deleteProgram(p);
      throw error;
    } finally {
      for (const s of compiled) gl.deleteShader(s);
    }
  }

  const VS = `#version 300 es
precision highp float;
precision highp int;
layout(location=0) in vec3 aPosition;
layout(location=1) in vec3 aNormal;
layout(location=2) in vec2 aComplex;
uniform mat4 uModel;
uniform mat4 uView;
uniform mat4 uProjection;
out vec3 vPosition;
out vec3 vNormal;
out vec2 vComplex;
void main() {
  vec4 world = uModel * vec4(aPosition, 1.0);
  vPosition = world.xyz;
  vNormal = mat3(uModel) * aNormal;
  vComplex = aComplex;
  gl_Position = uProjection * uView * world;
}`;

  const FS = `#version 300 es
precision highp float;
precision highp int;
in vec3 vPosition;
in vec3 vNormal;
in vec2 vComplex;
uniform vec3 uCamera;
uniform vec3 uOriginalCenter;
uniform float uDisplayScale;
uniform float uComplexScale;
uniform float uDivisorStrength;
uniform float uProjectionBox;
uniform bool uHomeScene;
uniform bool uDepthOnly;
uniform vec4 uDivisorPlane[6];
uniform float uTransNear;
uniform float uTransFar;
uniform float uTransMinAlpha;
uniform int uRenderPass; // 0: normal opaque, 1: opaque background, 2: depth peel
uniform bool uHasPreviousDepth;
uniform highp sampler2D uOpaqueDepth;
uniform highp sampler2D uPreviousDepth;
uniform highp sampler2D uAccumulated;
out vec4 outColor;
const float PI = 3.141592653589793;
const float TAU = 6.283185307179586;

// DIVISOR_EXPRESSION
// The homepage retains its separately curated contact-cone shading.
vec4 contactBlock(vec3 u){
  float x=u.x,y=u.y,z=u.z,h=x*x*x+2.0*z*z*z;
  float c=y*y*y+5.0*y*y*z-22.0*y*z*z-56.0*z*z*z;
  float k=y*y*y-10.0*y*y*z+y*z*z+120.0*z*z*z;
  return vec4(h*h+c*k,6.0*h*x*x,
    (3.0*y*y+10.0*y*z-22.0*z*z)*k+c*(3.0*y*y-20.0*y*z+z*z),
    12.0*h*z*z+(5.0*y*y-44.0*y*z-168.0*z*z)*k+c*(-10.0*y*y+2.0*y*z+360.0*z*z));
}
vec4 projectContact(vec4 sphere){
  // Correct flat-triangle interpolation to the curved F=0 slice before
  // evaluating D. This changes shading only, not the accepted polynomial.
  for(int step=0;step<3;step++){
    vec3 a=vec3(dot(uDivisorPlane[0],sphere),dot(uDivisorPlane[1],sphere),dot(uDivisorPlane[2],sphere));
    vec3 b=vec3(dot(uDivisorPlane[3],sphere),dot(uDivisorPlane[4],sphere),dot(uDivisorPlane[5],sphere));
    vec4 plus=contactBlock(a+b),minus=contactBlock(a-b);
    vec3 da=plus.yzw+minus.yzw,db=plus.yzw-minus.yzw;
    vec4 g=da.x*uDivisorPlane[0]+da.y*uDivisorPlane[1]+da.z*uDivisorPlane[2]+db.x*uDivisorPlane[3]+db.y*uDivisorPlane[4]+db.z*uDivisorPlane[5];
    g-=sphere*dot(sphere,g);
    vec4 correction=(plus.x+minus.x)*g/max(dot(g,g),1e-25);
    correction*=min(1.0,0.025/max(length(correction),1e-20));
    sphere=normalize(sphere-correction);
  }
  return sphere;
}
float contactCubic(vec3 u) {
  return (u.y-4.0*u.z)*(u.y+2.0*u.z)*(u.y+7.0*u.z);
}
vec4 projectSurface(vec4 sphere){
  // Atlas triangles approximate F=0. Correct their interpolated points before
  // evaluating D, so flat faces cannot introduce false divisor contours.
  for(int step=0;step<4;step++){
    vec3 a=vec3(dot(uDivisorPlane[0],sphere),dot(uDivisorPlane[1],sphere),dot(uDivisorPlane[2],sphere));
    vec3 b=vec3(dot(uDivisorPlane[3],sphere),dot(uDivisorPlane[4],sphere),dot(uDivisorPlane[5],sphere));
    DivJet f=surfaceField(a,b);
    vec4 g=f.a.x*uDivisorPlane[0]+f.a.y*uDivisorPlane[1]+f.a.z*uDivisorPlane[2]+f.b.x*uDivisorPlane[3]+f.b.y*uDivisorPlane[4]+f.b.z*uDivisorPlane[5];
    g-=sphere*dot(sphere,g);
    vec4 correction=f.v*g/max(dot(g,g),1e-25);
    correction*=min(1.0,0.025/max(length(correction),1e-20));
    sphere=normalize(sphere-correction);
  }
  return sphere;
}
float pixelDivisor(out vec2 complexValue) {
  vec3 p=vPosition*uDisplayScale+uOriginalCenter;
  float r2=dot(p,p);
  vec4 sphere=vec4(2.0*p,r2-1.0)/(1.0+r2);
  if(uHomeScene)sphere=projectContact(sphere);
  else if(uDivisorStrength>0.0)sphere=projectSurface(sphere);
  vec3 a=vec3(dot(uDivisorPlane[0],sphere),dot(uDivisorPlane[1],sphere),dot(uDivisorPlane[2],sphere));
  vec3 b=vec3(dot(uDivisorPlane[3],sphere),dot(uDivisorPlane[4],sphere),dot(uDivisorPlane[5],sphere));
  // Preserve the homepage's contact-cubic palette at its corrected point.
  complexValue = uHomeScene
    ? vec2(contactCubic(a+b),contactCubic(a-b))/uComplexScale : vComplex;
  return divisorField(a,b);
}

float pixelNoise(ivec2 pixel) {
  highp uint h=uint(pixel.x)*0x9E3779B9u ^ uint(pixel.y)*0x85EBCA6Bu;
  h ^= h>>16; h *= 0x7FEB352Du; h ^= h>>15; h *= 0x846CA68Bu; h ^= h>>16;
  return float(h & 0x00FFFFFFu) / 16777216.0;
}
vec3 phasePalette(float t) {
  // A cyclic domain-colouring palette: violet -> rose -> amber -> cyan -> blue -> violet.
  vec3 c = 0.54 + 0.46*cos(TAU*(t + vec3(0.03, 0.36, 0.69)));
  c = pow(max(c, 0.0), vec3(0.72));
  return mix(c, vec3(dot(c, vec3(0.2126,0.7152,0.0722))), -0.08);
}

float distributionGGX(vec3 N, vec3 H, float roughness) {
  float a = roughness*roughness;
  float a2 = a*a;
  float NdotH = max(dot(N,H), 0.0);
  float d = NdotH*NdotH*(a2-1.0)+1.0;
  return a2 / max(PI*d*d, 1e-5);
}
float geometrySchlickGGX(float NdotV, float roughness) {
  float r = roughness + 1.0;
  float k = (r*r)/8.0;
  return NdotV / max(NdotV*(1.0-k)+k, 1e-5);
}
float geometrySmith(vec3 N, vec3 V, vec3 L, float roughness) {
  return geometrySchlickGGX(max(dot(N,V),0.0), roughness) *
         geometrySchlickGGX(max(dot(N,L),0.0), roughness);
}
vec3 fresnelSchlick(float cosTheta, vec3 F0) {
  return F0 + (1.0-F0)*pow(clamp(1.0-cosTheta,0.0,1.0),5.0);
}
vec3 pbrLight(vec3 N, vec3 V, vec3 L, vec3 lightColor, vec3 albedo, float roughness, float metallic) {
  vec3 H = normalize(V+L);
  float NdotL = max(dot(N,L),0.0);
  float NdotV = max(dot(N,V),0.0);
  vec3 F0 = mix(vec3(0.035), albedo, metallic);
  float NDF = distributionGGX(N,H,roughness);
  float G = geometrySmith(N,V,L,roughness);
  vec3 F = fresnelSchlick(max(dot(H,V),0.0),F0);
  vec3 specular = (NDF*G*F) / max(4.0*NdotV*NdotL,0.002);
  vec3 kD = (1.0-F)*(1.0-metallic);
  return (kD*albedo/PI + specular)*lightColor*NdotL;
}
vec3 aces(vec3 x) {
  return clamp((x*(2.51*x+0.03))/(x*(2.43*x+0.59)+0.14),0.0,1.0);
}

// This opacity profile depends ONLY on point-to-camera distance (and the
// user's global settings), not front/back-facing state, normals, or divisors.
float distanceOpacity(float distanceToCamera) {
  float t = clamp(distanceToCamera / max(uTransFar, 1e-7), 0.0, 1.0);
  float smoothT = t*t*t*(t*(t*6.0 - 15.0) + 10.0); // C2 smootherstep
  float strength = smoothstep(0.0, 0.18, uTransFar);
  return clamp(1.0 - (1.0-uTransMinAlpha)*strength*(1.0-smoothT), 0.0, 1.0);
}
void main() {
  if(uDepthOnly) {
    float alpha = distanceOpacity(length(uCamera-vPosition));
    if(uRenderPass == 1 && alpha < 1.0) discard;
    if(uRenderPass == 2) {
      if(alpha >= 1.0) discard; // this portion is already in the opaque background
      ivec2 pixel = ivec2(gl_FragCoord.xy);
      highp float z = gl_FragCoord.z;
      if(z >= texelFetch(uOpaqueDepth,pixel,0).r) discard;
      // Highp depth sampling is essential on mobile. Two 24-bit depth units
      // avoid re-peeling the identical surface sample; lowp samplers break this.
      if(uHasPreviousDepth && z <= texelFetch(uPreviousDepth,pixel,0).r + 1.2e-7) discard;
      if(texelFetch(uAccumulated,pixel,0).a >= 0.9999) discard;
    }
    outColor=vec4(0.0);return;
  }
  // Derivatives need neighbouring fragments, including those subsequently
  // discarded by x-ray depth peeling. Evaluate before divergent discards.
  vec2 complexValue;
  float field = pixelDivisor(complexValue);
  float pixelWidth = max(length(vec2(dFdx(field),dFdy(field))),1e-35);
  float divisor = 1.0-smoothstep(0.55,1.45,abs(field)/pixelWidth);
  float alpha = distanceOpacity(length(uCamera-vPosition));
  if(uRenderPass == 1 && alpha < 1.0) discard;
  if(uRenderPass == 2) {
    if(alpha >= 1.0) discard; // this portion is already in the opaque background
    ivec2 pixel = ivec2(gl_FragCoord.xy);
    highp float z = gl_FragCoord.z;
    if(z >= texelFetch(uOpaqueDepth,pixel,0).r) discard;
    // Highp depth sampling is essential on mobile. Two 24-bit depth units
    // avoid re-peeling the identical surface sample; lowp samplers break this.
    if(uHasPreviousDepth && z <= texelFetch(uPreviousDepth,pixel,0).r + 1.2e-7) discard;
    if(texelFetch(uAccumulated,pixel,0).a >= 0.9999) discard;
  }
  vec3 N = normalize(vNormal);
  if (!gl_FrontFacing) N = -N;
  vec3 V = normalize(uCamera-vPosition);

  float phase = fract(atan(complexValue.y,complexValue.x)/TAU + 1.0);
  float magnitude = length(complexValue);
  vec3 albedo = phasePalette(phase);
  // A gentle modulus response without the old striping artefact.
  albedo *= mix(0.76,1.18,smoothstep(0.015,0.55,magnitude));
  albedo = mix(albedo, vec3(0.96), 0.055);

  float roughness = 0.19;
  float metallic = 0.22;
  vec3 color = albedo*0.075;
  color += pbrLight(N,V,normalize(vec3(0.75,0.62,1.10)),vec3(5.3,4.6,6.4),albedo,roughness,metallic);
  color += pbrLight(N,V,normalize(vec3(-0.82,0.20,0.54)),vec3(1.6,2.9,4.9),albedo,0.27,metallic);
  color += pbrLight(N,V,normalize(vec3(0.02,-0.92,0.35)),vec3(3.4,1.25,2.5),albedo,0.24,metallic);

  float rim = pow(1.0-max(dot(N,V),0.0),2.4);
  color += albedo*rim*0.52 + vec3(0.32,0.42,0.68)*rim*0.17;

  // A crisp, antialiased two-pixel curve, without a surrounding glow.
  vec3 divisorColor = mix(vec3(1.0,0.72,0.92),vec3(0.68,0.90,1.0),0.5+0.5*sin(TAU*phase));
  color += divisorColor*(0.96*divisor)*uDivisorStrength;

  // The mathematical projection box is [-10,10]^3.  Dissolve the last shell
  // instead of exposing marching-cube cut faces at the finite box boundary.
  vec3 stereo = vPosition*uDisplayScale + uOriginalCenter;
  float boxDistance = max(abs(stereo.x),max(abs(stereo.y),abs(stereo.z)));
  float edgeFade = uProjectionBox > 0.0 ? 1.0-smoothstep(0.825*uProjectionBox,0.992*uProjectionBox,boxDistance) : 1.0;
  float screenNoise = pixelNoise(ivec2(gl_FragCoord.xy));
  // Apply the same coverage fade to every slice. Multiplying generic-slice
  // colour by this fade left opaque black pixels and a visible box cut.
  if (screenNoise > edgeFade) discard;

  color = aces(color);
  color = pow(color,vec3(1.0/2.2));
  color += (screenNoise-0.5)/420.0;

  // Only the peeled layer uses alpha. Normal/zero-reach rendering is exactly
  // the original depth-writing, unblended path; no edge-alpha multiplier.
  outColor = (uRenderPass == 2) ? vec4(color*alpha,alpha) : vec4(color,1.0);
}`;

  // Six-layer front-to-back depth peeling, with a separately depth-tested opaque
  // background. No triangle sorting and no front/back-face grouping. RGBA8 and
  // depth textures are core WebGL 2; half-float is an optional precision upgrade.
  const PEEL_FULLSCREEN_VS = `#version 300 es
precision highp float;
precision highp int;
void main() {
  vec2 p = vec2(float((gl_VertexID << 1) & 2), float(gl_VertexID & 2));
  gl_Position = vec4(p * 2.0 - 1.0, 0.0, 1.0);
}`;
  const PEEL_COPY_FS = `#version 300 es
precision highp float;
precision highp int;
uniform highp sampler2D uLayer;
out vec4 outColor;
void main() { outColor = texelFetch(uLayer, ivec2(gl_FragCoord.xy), 0); }
`;
  const PEEL_RESOLVE_FS = `#version 300 es
precision highp float;
precision highp int;
uniform highp sampler2D uFront;
uniform highp sampler2D uBackground;
out vec4 outColor;
void main() {
  ivec2 pixel = ivec2(gl_FragCoord.xy);
  vec4 front = texelFetch(uFront, pixel, 0);
  vec4 back = texelFetch(uBackground, pixel, 0);
  vec4 composed = front + (1.0 - front.a) * back;
  // The canvas was created with premultipliedAlpha:false. Intermediate layers
  // are premultiplied, but the final canvas output must be straight-alpha.
  outColor = vec4(composed.rgb / max(composed.a, 1e-7), composed.a);
}`;

  function createDepthPeeler(gl, surfaceProgram) {
    if (!gl.getExtension('EXT_color_buffer_float'))
      throw new Error('The 3D view requires floating-point render targets.');
    const copyProgram = program(gl, PEEL_FULLSCREEN_VS, PEEL_COPY_FS);
    const resolveProgram = program(gl, PEEL_FULLSCREEN_VS, PEEL_RESOLVE_FS);
    const fullscreenVao = gl.createVertexArray();
    const passLoc = gl.getUniformLocation(surfaceProgram, 'uRenderPass');
    const prevLoc = gl.getUniformLocation(surfaceProgram, 'uHasPreviousDepth');
    const opaqueSampler = gl.getUniformLocation(surfaceProgram, 'uOpaqueDepth');
    const prevSampler = gl.getUniformLocation(surfaceProgram, 'uPreviousDepth');
    const accSampler = gl.getUniformLocation(surfaceProgram, 'uAccumulated');
    let targets = null;
    const zero = new Float32Array([0, 0, 0, 0]);
    const one = new Float32Array([1]);
    function bindTexture(unit, texture) {
      gl.activeTexture(gl.TEXTURE0 + unit);
      gl.bindTexture(gl.TEXTURE_2D, texture);
    }
    function releaseTargets() {
      if (!targets) return;
      gl.bindFramebuffer(gl.FRAMEBUFFER, null);
      for (let i = 0; i < 3; i++) bindTexture(i, null);
      targets.framebuffers.forEach((f) => gl.deleteFramebuffer(f));
      targets.textures.forEach((t) => gl.deleteTexture(t));
      targets = null;
    }
    function allocate(width, height) {
      const textures = [],
        framebuffers = [];
      function texture(internalFormat) {
        const t = gl.createTexture();
        if (!t) throw new Error('Unable to allocate a transparency texture.');
        textures.push(t);
        gl.bindTexture(gl.TEXTURE_2D, t);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
        gl.texStorage2D(gl.TEXTURE_2D, 1, internalFormat, width, height);
        return t;
      }
      function framebuffer(color, depth = null) {
        const f = gl.createFramebuffer();
        if (!f) throw new Error('Unable to allocate a transparency framebuffer.');
        framebuffers.push(f);
        gl.bindFramebuffer(gl.FRAMEBUFFER, f);
        gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, color, 0);
        if (depth)
          gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, depth, 0);
        gl.drawBuffers([gl.COLOR_ATTACHMENT0]);
        if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE)
          throw new Error('Depth-peeling framebuffer is not supported.');
        return f;
      }
      try {
        // One shared layer-color target, two ping-pong depth targets, a fixed
        // opaque background, and a premultiplied accumulation buffer.
        const opaqueColor = texture(gl.RGBA8),
          opaqueDepth = texture(gl.DEPTH_COMPONENT24);
        const layerColor = texture(gl.RGBA8),
          depth0 = texture(gl.DEPTH_COMPONENT24),
          depth1 = texture(gl.DEPTH_COMPONENT24);
        const accumulation = texture(gl.RGBA16F);
        const opaqueFbo = framebuffer(opaqueColor, opaqueDepth);
        const peelFbo = [framebuffer(layerColor, depth0), framebuffer(layerColor, depth1)];
        const accumulationFbo = framebuffer(accumulation);
        const err = gl.getError();
        if (err !== gl.NO_ERROR)
          throw new Error('Transparency allocation failed (WebGL ' + err + ').');
        return {
          width,
          height,
          opaqueColor,
          opaqueDepth,
          layerColor,
          depth: [depth0, depth1],
          accumulation,
          opaqueFbo,
          peelFbo,
          accumulationFbo,
          textures,
          framebuffers
        };
      } catch (error) {
        gl.bindFramebuffer(gl.FRAMEBUFFER, null);
        gl.bindTexture(gl.TEXTURE_2D, null);
        framebuffers.forEach((f) => gl.deleteFramebuffer(f));
        textures.forEach((t) => gl.deleteTexture(t));
        throw error;
      }
    }
    function ensureTargets(width, height) {
      if (targets && targets.width === width && targets.height === height) return;
      releaseTargets();
      if (width * height * 28 > 256 * 1024 * 1024)
        throw new Error('Transparency exceeds the 256 MiB render-target budget.');
      targets = allocate(width, height);
      gl.bindFramebuffer(gl.FRAMEBUFFER, null);
      for (let i = 0; i < 3; i++) bindTexture(i, null);
    }
    const depthOnlyLoc = gl.getUniformLocation(surfaceProgram, 'uDepthOnly');
    function drawWithPrepass(drawSurface) {
      gl.uniform1i(depthOnlyLoc, 1);
      gl.colorMask(false, false, false, false);
      gl.depthFunc(gl.LEQUAL);
      gl.depthMask(true);
      drawSurface();
      gl.uniform1i(depthOnlyLoc, 0);
      gl.colorMask(true, true, true, true);
      gl.depthFunc(gl.EQUAL);
      gl.depthMask(false);
      drawSurface();
      gl.depthFunc(gl.LEQUAL);
      gl.depthMask(true);
    }
    function render(width, height, vao, drawSurface, layers = 6, usePrepass = false) {
      const drawLayer = () => (usePrepass ? drawWithPrepass(drawSurface) : drawSurface());
      ensureTargets(width, height);
      const t = targets;
      gl.viewport(0, 0, width, height);
      gl.disable(gl.CULL_FACE);
      gl.disable(gl.BLEND);
      gl.enable(gl.DEPTH_TEST);
      gl.depthFunc(gl.LEQUAL);
      gl.depthMask(true);
      gl.colorMask(true, true, true, true);
      gl.useProgram(surfaceProgram);
      gl.bindVertexArray(vao);
      gl.uniform1i(opaqueSampler, 0);
      gl.uniform1i(prevSampler, 1);
      gl.uniform1i(accSampler, 2);
      for (let i = 0; i < 3; i++) bindTexture(i, null);

      // Correctly depth-test the portions outside the fade sphere first.
      gl.bindFramebuffer(gl.FRAMEBUFFER, t.opaqueFbo);
      gl.clearBufferfv(gl.COLOR, 0, zero);
      gl.clearBufferfv(gl.DEPTH, 0, one);
      gl.uniform1i(passLoc, 1);
      gl.uniform1i(prevLoc, 0);
      drawLayer();
      gl.bindFramebuffer(gl.FRAMEBUFFER, t.accumulationFbo);
      gl.clearBufferfv(gl.COLOR, 0, zero);

      for (let layer = 0; layer < layers; layer++) {
        const current = layer & 1;
        gl.bindFramebuffer(gl.FRAMEBUFFER, t.peelFbo[current]);
        gl.enable(gl.DEPTH_TEST);
        gl.depthMask(true);
        gl.disable(gl.BLEND);
        gl.clearBufferfv(gl.COLOR, 0, zero);
        gl.clearBufferfv(gl.DEPTH, 0, one);
        gl.useProgram(surfaceProgram);
        gl.bindVertexArray(vao);
        bindTexture(0, t.opaqueDepth);
        bindTexture(1, layer ? t.depth[current ^ 1] : t.opaqueDepth);
        bindTexture(2, t.accumulation);
        gl.uniform1i(passLoc, 2);
        gl.uniform1i(prevLoc, layer ? 1 : 0);
        drawLayer();

        // Accumulate this nearest remaining layer IN FRONT-TO-BACK ORDER.
        // premultiplied out = prior + (1-prior.alpha) * thisLayer
        gl.bindFramebuffer(gl.FRAMEBUFFER, t.accumulationFbo);
        gl.disable(gl.DEPTH_TEST);
        gl.depthMask(false);
        gl.enable(gl.BLEND);
        gl.blendEquation(gl.FUNC_ADD);
        gl.blendFuncSeparate(gl.ONE_MINUS_DST_ALPHA, gl.ONE, gl.ONE_MINUS_DST_ALPHA, gl.ONE);
        gl.useProgram(copyProgram);
        gl.bindVertexArray(fullscreenVao);
        bindTexture(0, t.layerColor);
        bindTexture(1, null);
        bindTexture(2, null);
        gl.uniform1i(gl.getUniformLocation(copyProgram, 'uLayer'), 0);
        gl.drawArrays(gl.TRIANGLES, 0, 3);
      }
      gl.bindFramebuffer(gl.FRAMEBUFFER, null);
      gl.disable(gl.BLEND);
      gl.disable(gl.DEPTH_TEST);
      gl.depthMask(true);
      gl.clearColor(0, 0, 0, 0);
      gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
      gl.useProgram(resolveProgram);
      gl.bindVertexArray(fullscreenVao);
      bindTexture(0, t.accumulation);
      bindTexture(1, t.opaqueColor);
      bindTexture(2, null);
      gl.uniform1i(gl.getUniformLocation(resolveProgram, 'uFront'), 0);
      gl.uniform1i(gl.getUniformLocation(resolveProgram, 'uBackground'), 1);
      gl.drawArrays(gl.TRIANGLES, 0, 3);
      for (let i = 0; i < 3; i++) bindTexture(i, null);
      gl.useProgram(surfaceProgram);
      gl.bindVertexArray(vao);
      gl.uniform1i(passLoc, 0);
      gl.enable(gl.DEPTH_TEST);
      gl.depthMask(true);
    }
    return {
      render,
      releaseTargets,
      dispose() {
        releaseTargets();
        gl.deleteProgram(copyProgram);
        gl.deleteProgram(resolveProgram);
        gl.deleteVertexArray(fullscreenVao);
      }
    };
  }

  /* Camera-only math: a unit quaternion maps camera-local right/up/back into
   world coordinates. Free dragging composes rotations in this local frame,
   never converts back to Euler angles, and never resets the up vector.
   Reference: Ken Shoemake's quaternion/trackball construction; no dependency. */
  const ScreenTrackball = Object.freeze({
    normalize(q) {
      const n = Math.hypot(q[0], q[1], q[2], q[3]);
      if (!Number.isFinite(n) || n < 1e-15) throw new Error('Invalid camera orientation.');
      return q.map((x) => x / n);
    },
    multiply(a, b) {
      const [x, y, z, w] = a,
        [X, Y, Z, W] = b;
      return [
        w * X + x * W + y * Z - z * Y,
        w * Y - x * Z + y * W + z * X,
        w * Z + x * Y - y * X + z * W,
        w * W - x * X - y * Y - z * Z
      ];
    },
    basis(q) {
      const [x, y, z, w] = q;
      return {
        right: [1 - 2 * (y * y + z * z), 2 * (x * y + w * z), 2 * (x * z - w * y)],
        up: [2 * (x * y - w * z), 1 - 2 * (x * x + z * z), 2 * (y * z + w * x)],
        back: [2 * (x * z + w * y), 2 * (y * z - w * x), 1 - 2 * (x * x + y * y)]
      };
    },
    rotate(q, horizontal, vertical) {
      // Rotate around the camera's own up/right axes, in radians.
      const x = -vertical,
        y = horizontal,
        angle = Math.hypot(x, y);
      if (angle < 1e-15) return q.slice();
      const s = Math.sin(angle / 2) / angle;
      return this.normalize(this.multiply(q, [x * s, y * s, 0, Math.cos(angle / 2)]));
    },
    slerp(a, b, t) {
      // Shortest path only for damping/reset/mode transitions, not drag integration.
      let end = b,
        d = a.reduce((s, x, i) => s + x * b[i], 0);
      if (d < 0) {
        end = b.map((x) => -x);
        d = -d;
      }
      d = Math.max(-1, Math.min(1, d));
      t = Math.max(0, Math.min(1, t));
      if (d > 0.9995) return this.normalize(a.map((x, i) => x + (end[i] - x) * t));
      const angle = Math.acos(d),
        denom = Math.sin(angle);
      const u = Math.sin((1 - t) * angle) / denom,
        v = Math.sin(t * angle) / denom;
      return this.normalize(a.map((x, i) => u * x + v * end[i]));
    },
    pan(center, dx, dy, q, distance, fov, height) {
      // Translation in the view plane: exact pixel tracking for points at the
      // target plane's depth, including when the camera is rolled.
      const { right, up } = this.basis(q),
        s = (2 * distance * Math.tan(fov / 2)) / Math.max(1, height);
      return center.map((c, i) => c - right[i] * dx * s + up[i] * dy * s);
    }
  });

  function mat4Identity() {
    return new Float32Array([1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
  }
  function perspective(fovy, aspect, near, far) {
    const f = 1 / Math.tan(fovy / 2),
      nf = 1 / (near - far);
    return new Float32Array([
      f / aspect,
      0,
      0,
      0,
      0,
      f,
      0,
      0,
      0,
      0,
      (far + near) * nf,
      -1,
      0,
      0,
      2 * far * near * nf,
      0
    ]);
  }
  function lookAt(eye, center, up) {
    let zx = eye[0] - center[0],
      zy = eye[1] - center[1],
      zz = eye[2] - center[2];
    let zn = Math.hypot(zx, zy, zz);
    zx /= zn;
    zy /= zn;
    zz /= zn;
    let xx = up[1] * zz - up[2] * zy,
      xy = up[2] * zx - up[0] * zz,
      xz = up[0] * zy - up[1] * zx;
    let xn = Math.hypot(xx, xy, xz);
    xx /= xn;
    xy /= xn;
    xz /= xn;
    const yx = zy * xz - zz * xy,
      yy = zz * xx - zx * xz,
      yz = zx * xy - zy * xx;
    return new Float32Array([
      xx,
      yx,
      zx,
      0,
      xy,
      yy,
      zy,
      0,
      xz,
      yz,
      zz,
      0,
      -(xx * eye[0] + xy * eye[1] + xz * eye[2]),
      -(yx * eye[0] + yy * eye[1] + yz * eye[2]),
      -(zx * eye[0] + zy * eye[1] + zz * eye[2]),
      1
    ]);
  }

  const SCRIPT_BASE = new URL('.', location.href);
  function create(canvas, options = {}) {
    // In production this core runs only in a dedicated worker. The host forwards
    // sizes and input; no graphics API is called by the page's UI thread.
    const { view: window, page: document, reducedMotion: reduced } = options.host;
    const assetBase = SCRIPT_BASE;
    const onStatus = typeof options.onStatus === 'function' ? options.onStatus : () => {};
    const onModeChange =
      typeof options.onModeChange === 'function' ? options.onModeChange : () => {};
    const gl = canvas.getContext('webgl2', {
      alpha: true,
      antialias: true,
      premultipliedAlpha: false,
      preserveDrawingBuffer: false,
      powerPreference: 'high-performance',
      failIfMajorPerformanceCaveat: true
    });
    if (!gl) throw new Error('WebGL 2 is required for the mathematical surface.');
    gl.disable(gl.DITHER);
    gl.enable(gl.DEPTH_TEST);
    gl.depthFunc(gl.LEQUAL);
    gl.disable(gl.CULL_FACE);
    gl.clearColor(0, 0, 0, 0);
    let p = null,
      programSource = null;
    const U = {};
    function useDivisorShader(pixel) {
      if (pixel.source !== programSource) {
        const next = program(gl, VS, FS.replace('// DIVISOR_EXPRESSION', pixel.source));
        if (depthPeeler) {
          depthPeeler.dispose();
          depthPeeler = null;
        }
        if (p) gl.deleteProgram(p);
        p = next;
        programSource = pixel.source;
        for (const name of [
          'Model',
          'View',
          'Projection',
          'Camera',
          'OriginalCenter',
          'DisplayScale',
          'ComplexScale',
          'DivisorStrength',
          'ProjectionBox',
          'HomeScene',
          'TransNear',
          'TransFar',
          'TransMinAlpha',
          'RenderPass'
        ])
          U[name] = gl.getUniformLocation(p, 'u' + name);
        U.DivisorPlane = gl.getUniformLocation(p, 'uDivisorPlane[0]');
      }
      gl.useProgram(p);
      gl.uniformMatrix4fv(U.Model, false, mat4Identity());
    }
    let activeVao = null,
      activeBuffers = [],
      activeCount = 0,
      activeMeta = null;
    let job = 0,
      destroyed = false,
      contextLost = false,
      graphicsFault = false,
      needsDraw = true;
    let depthPeeler = null,
      frameFence = null,
      frameId = 0,
      fenceStarted = 0,
      frameJob = 0,
      awaitingFirstFrame = false,
      lastFrameTick = performance.now();
    const listeners = [];
    const FOV = (42 * Math.PI) / 180,
      minDistance = 0.035,
      maxDistance = 12;
    let baseDistance = 1,
      baseCenter = [0, 0, 0];
    let homeOrientation = [0, 0, 0, 1];
    let cameraMode = 'parallax',
      cameraOrientation = homeOrientation.slice(),
      orbitOrientation = homeOrientation.slice();
    let cameraDistance = baseDistance,
      orbitDistance = baseDistance,
      cameraCenter = [0, 0, 0],
      orbitCenter = [0, 0, 0];
    let targetX = 0,
      targetY = 0,
      drag = null,
      touchGesture = null,
      last = performance.now(),
      lastDraw = 0;
    const touches = new Map(),
      heldKeys = new Set(),
      clamp = (x, a, b) => Math.max(a, Math.min(b, x)),
      clone3 = (v) => v.slice();
    function listen(target, name, fn, opts) {
      target.addEventListener(name, fn, opts);
      listeners.push(() => target.removeEventListener(name, fn, opts));
    }
    function status(state, message, meta) {
      onStatus({ state, message, meta: meta || undefined });
    }
    function cancel() {
      meshes.cancel();
      job++;
      awaitingFirstFrame = false;
    }
    function stop(message) {
      if (graphicsFault || destroyed) return;
      graphicsFault = true;
      cancel();
      cancelAnimationFrame(frameId);
      // Never delete or reuse handles from a lost/restored context. The owner
      // terminates the worker and discards this canvas. Any background recovery
      // starts a fresh worker and context, with none of these handles.
      activeVao = null;
      activeBuffers = [];
      activeCount = 0;
      frameFence = null;
      depthPeeler = null;
      status('error', message);
      options.onFatal?.(message);
    }
    function usable() {
      if (destroyed || contextLost || graphicsFault) return false;
      if (gl.isContextLost()) {
        contextLost = true;
        stop('The graphics context was lost.');
        return false;
      }
      return true;
    }
    function clearMesh() {
      if (!usable()) return;
      if (activeVao) gl.deleteVertexArray(activeVao);
      for (const b of activeBuffers) gl.deleteBuffer(b);
      activeVao = null;
      activeBuffers = [];
      activeCount = 0;
    }
    function upload(mesh, selected) {
      if (!usable()) return;
      const { meta, buffer, indexBuffer } = mesh;
      const vao = gl.createVertexArray(),
        vbo = gl.createBuffer(),
        ebo = gl.createBuffer();
      if (!vao || !vbo || !ebo) throw new Error('The graphics device could not allocate a mesh.');
      gl.bindVertexArray(vao);
      gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(buffer), gl.STATIC_DRAW);
      for (const [location, size, offset] of [
        [0, 3, 0],
        [1, 3, 12],
        [2, 2, 24]
      ]) {
        gl.enableVertexAttribArray(location);
        gl.vertexAttribPointer(location, size, gl.FLOAT, false, 36, offset);
      }
      gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, ebo);
      gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, new Uint32Array(indexBuffer), gl.STATIC_DRAW);
      if (!usable()) return;
      if (gl.getError() !== gl.NO_ERROR) {
        gl.deleteVertexArray(vao);
        gl.deleteBuffer(vbo);
        gl.deleteBuffer(ebo);
        throw new Error('Surface upload failed.');
      }
      clearMesh();
      activeVao = vao;
      activeBuffers = [vbo, ebo];
      activeCount = meta.triangleCount * 3;
      const hasD =
        selected.formalStatus === 'proved' &&
        !!(selected.render?.divisorTerms?.length || selected.render?.divisorProgram);
      const whole = meta.samplingMode === 'sphere' && meta.projectionBox === 0,
        projectionBox = whole ? 0 : 10;
      activeMeta = {
        ...meta,
        divisorVisible: hasD,
        projectionBox,
        xray: { enabled: true, reach: 2.0, layers: 6 },
        cameraDefault: {
          orientation: homeOrientation.slice(),
          distance: baseDistance,
          center: baseCenter.slice()
        },
        sliceDescription: whole
          ? 'The compact real slice, stereographically projected without a box cutoff.'
          : 'A real two-dimensional section of X, on a fixed phase-rotated real four-plane; stereographic projection in [−10, 10]³.'
      };
      const r = selected.render || {},
        pixel = HodgeDivisor.fragment(
          hasD ? r.divisorProgram || r.divisorTerms : null,
          meta.phaseSigns
        );
      pixel.source += '\n' + HodgeDivisor.surface(selected.F, meta.phaseSigns).source;
      useDivisorShader(pixel);
      gl.uniform3fv(U.OriginalCenter, new Float32Array(meta.centerOriginal));
      gl.uniform1f(U.DisplayScale, meta.displayScale);
      gl.uniform1f(U.ComplexScale, Math.max(1e-20, meta.complexScale || 1));
      gl.uniform1f(U.ProjectionBox, projectionBox);
      gl.uniform1f(U.DivisorStrength, hasD ? 1 : 0);
      gl.uniform1i(U.HomeScene, selected.id === 'home' ? 1 : 0);
      gl.uniform4fv(U.DivisorPlane, new Float32Array(meta.planeMatrix.flat()));
      activeMeta.divisorEvaluation = 'per-pixel polynomial';
      activeMeta.divisorOperations = pixel.operations;
      options.onLabel?.(
        selected.title +
          ' — real slice of F = 0' +
          (hasD ? ', with certificate divisor highlighted' : '')
      );
      needsDraw = true;
      awaitingFirstFrame = true;
    }
    const meshes = HodgeMeshes.create(assetBase, usable);
    async function setCase(selected) {
      if (!usable()) return;
      cancel();
      const id = job;
      activeCount = 0;
      needsDraw = true;
      status('loading', 'Preparing the saved slice…');
      try {
        const r = selected.render;
        const saved = r.camera;
        if (
          !Number.isFinite(saved.distance) ||
          saved.distance < minDistance ||
          saved.distance > maxDistance ||
          !Array.isArray(saved.center) ||
          saved.center.length !== 3 ||
          !saved.center.every(Number.isFinite)
        )
          throw new Error('Invalid saved camera.');
        baseDistance = saved.distance;
        baseCenter = saved.center.slice();
        if (
          !Array.isArray(saved.orientation) ||
          saved.orientation.length !== 4 ||
          !saved.orientation.every(Number.isFinite)
        )
          throw new Error('Invalid saved camera orientation.');
        homeOrientation = ScreenTrackball.normalize(saved.orientation);
        resetCamera();
        if (!r.mesh) throw new Error('This instance has no saved slice.');
        const mesh = await meshes.load(r.mesh);
        if (id !== job || !usable()) return;
        upload(mesh, selected);
      } catch (error) {
        if (id !== job || !usable()) return;
        status('error', error.message || String(error));
        throw error;
      }
    }
    function freezeVisibleCamera() {
      orbitOrientation = cameraOrientation.slice();
      orbitDistance = cameraDistance;
      orbitCenter = clone3(cameraCenter);
    }
    function resetCamera() {
      heldKeys.clear();
      orbitOrientation = homeOrientation.slice();
      orbitDistance = baseDistance;
      orbitCenter = baseCenter.slice();
      cameraOrientation = homeOrientation.slice();
      cameraDistance = baseDistance;
      cameraCenter = baseCenter.slice();
      targetX = targetY = 0;
      drag = null;
      touches.clear();
      touchGesture = null;
      needsDraw = true;
    }
    function setMode(mode) {
      heldKeys.clear();
      cameraMode = mode === 'free' ? 'free' : 'parallax';
      drag = null;
      touches.clear();
      touchGesture = null;
      targetX = targetY = 0;
      if (cameraMode === 'free') freezeVisibleCamera();
      // Keep the visible pose on return; the frame loop eases rotation, zoom and pan back to parallax.
      needsDraw = true;
      onModeChange(cameraMode);
    }
    function beginDrag(pointerId, action, x, y) {
      freezeVisibleCamera();
      return {
        pointerId,
        action,
        x,
        y,
        orientation: orbitOrientation.slice(),
        center: clone3(orbitCenter),
        distance: orbitDistance
      };
    }
    function pannedCenter(center, dx, dy, orientation, distance) {
      return ScreenTrackball.pan(center, dx, dy, orientation, distance, FOV, canvas.clientHeight);
    }
    function rotateCamera(dx, dy) {
      // Move the visible surface in screen directions, even when rolled.
      orbitOrientation = ScreenTrackball.rotate(orbitOrientation, -dx * 0.0047, dy * 0.0042);
      needsDraw = true;
    }
    function zoomCamera(amount) {
      orbitDistance = clamp(orbitDistance * Math.exp(amount), minDistance, maxDistance);
      needsDraw = true;
    }
    listen(
      window,
      'pointermove',
      (e) => {
        if (cameraMode === 'parallax' && !reduced) {
          targetX = (2 * e.clientX) / window.innerWidth - 1;
          targetY = (2 * e.clientY) / window.innerHeight - 1;
        }
      },
      { passive: true }
    );
    listen(
      window,
      'parallax',
      (e) => {
        if (cameraMode === 'parallax' && !reduced && Number.isFinite(e.x) && Number.isFinite(e.y)) {
          targetX = clamp(e.x, -1, 1);
          targetY = clamp(e.y, -1, 1);
          needsDraw = true;
        }
      },
      { passive: true }
    );
    listen(
      window,
      'pointerleave',
      () => {
        targetX = targetY = 0;
      },
      { passive: true }
    );
    listen(
      window,
      'blur',
      () => {
        heldKeys.clear();
        targetX = targetY = 0;
        drag = null;
        touches.clear();
        touchGesture = null;
      },
      { passive: true }
    );
    listen(canvas, 'contextmenu', (e) => {
      if (cameraMode === 'free') e.preventDefault();
    });
    listen(
      canvas,
      'dblclick',
      (e) => {
        if (cameraMode === 'free') {
          e.preventDefault();
          resetCamera();
        }
      },
      { passive: false }
    );
    listen(
      canvas,
      'wheel',
      (e) => {
        if (cameraMode !== 'free') return;
        e.preventDefault();
        zoomCamera(e.deltaY * 0.00135);
      },
      { passive: false }
    );
    listen(
      canvas,
      'pointerdown',
      (e) => {
        if (cameraMode !== 'free') return;
        e.preventDefault();
        canvas.setPointerCapture?.(e.pointerId);
        if (e.pointerType === 'touch') {
          touches.set(e.pointerId, { x: e.clientX, y: e.clientY });
          if (touches.size === 1) {
            drag = beginDrag(e.pointerId, 'orbit', e.clientX, e.clientY);
            touchGesture = null;
          } else if (touches.size === 2) {
            freezeVisibleCamera();
            const pts = [...touches.values()];
            touchGesture = {
              mx: (pts[0].x + pts[1].x) / 2,
              my: (pts[0].y + pts[1].y) / 2,
              separation: Math.max(8, Math.hypot(pts[1].x - pts[0].x, pts[1].y - pts[0].y)),
              distance: orbitDistance,
              center: clone3(orbitCenter),
              orientation: orbitOrientation.slice()
            };
            drag = null;
          }
          return;
        }
        drag = beginDrag(
          e.pointerId,
          e.button === 2 || e.button === 1 || e.shiftKey || e.altKey || e.ctrlKey || e.metaKey
            ? 'pan'
            : 'orbit',
          e.clientX,
          e.clientY
        );
      },
      { passive: false }
    );
    listen(
      canvas,
      'pointermove',
      (e) => {
        if (cameraMode !== 'free') return;
        if (e.pointerType === 'touch' && touches.has(e.pointerId)) {
          touches.set(e.pointerId, { x: e.clientX, y: e.clientY });
          if (touches.size >= 2 && touchGesture) {
            e.preventDefault();
            const pts = [...touches.values()].slice(0, 2),
              mx = (pts[0].x + pts[1].x) / 2,
              my = (pts[0].y + pts[1].y) / 2,
              separation = Math.max(8, Math.hypot(pts[1].x - pts[0].x, pts[1].y - pts[0].y));
            orbitDistance = clamp(
              (touchGesture.distance * touchGesture.separation) / separation,
              minDistance,
              maxDistance
            );
            orbitCenter = pannedCenter(
              touchGesture.center,
              mx - touchGesture.mx,
              my - touchGesture.my,
              touchGesture.orientation,
              touchGesture.distance
            );
            cameraCenter = clone3(orbitCenter);
            cameraDistance = orbitDistance;
            needsDraw = true;
            return;
          }
        }
        if (!drag || drag.pointerId !== e.pointerId) return;
        e.preventDefault();
        const dx = e.clientX - drag.x,
          dy = e.clientY - drag.y;
        if (drag.action === 'orbit') {
          rotateCamera(dx, dy);
          cameraOrientation = orbitOrientation.slice();
          drag.x = e.clientX;
          drag.y = e.clientY;
        } else {
          orbitCenter = pannedCenter(drag.center, dx, dy, drag.orientation, drag.distance);
          cameraCenter = clone3(orbitCenter);
          needsDraw = true;
        }
      },
      { passive: false }
    );
    function endPointer(e) {
      if (e.pointerType === 'touch') {
        touches.delete(e.pointerId);
        if (touches.size === 1) {
          const [id, pt] = touches.entries().next().value;
          drag = beginDrag(id, 'orbit', pt.x, pt.y);
          touchGesture = null;
        } else if (!touches.size) {
          drag = null;
          touchGesture = null;
        }
      } else if (drag?.pointerId === e.pointerId) drag = null;
      try {
        canvas.releasePointerCapture?.(e.pointerId);
      } catch (_) {}
    }
    listen(canvas, 'pointerup', endPointer, { passive: true });
    listen(canvas, 'pointercancel', endPointer, { passive: true });
    listen(
      canvas,
      'lostpointercapture',
      (e) => {
        if (drag?.pointerId === e.pointerId) drag = null;
      },
      { passive: true }
    );
    listen(window, 'keydown', (e) => {
      if (cameraMode !== 'free') return;
      const key = e.key.toLowerCase();
      if (/^(arrow(up|down|left|right)|[wasdzx])$/.test(key)) heldKeys.add(key);
      else if (e.key === 'Escape') setMode('parallax');
      else if (e.key === 'r' || e.key === 'R') resetCamera();
    });
    listen(window, 'keyup', (e) => heldKeys.delete(e.key.toLowerCase()));
    listen(canvas, 'webglcontextlost', () => {
      contextLost = true;
      stop('The graphics context was lost.');
    });
    function resize() {
      if (!usable()) return;
      const w0 = Math.max(1, canvas.clientWidth),
        h0 = Math.max(1, canvas.clientHeight),
        budget = window.innerWidth < 760 ? 1_500_000 : 3_000_000,
        dpr = Math.min(window.devicePixelRatio || 1, 2, Math.sqrt(budget / (w0 * h0))),
        w = Math.max(1, Math.floor(w0 * dpr)),
        h = Math.max(1, Math.floor(h0 * dpr));
      if (canvas.width !== w || canvas.height !== h) {
        canvas.width = w;
        canvas.height = h;
        gl.viewport(0, 0, w, h);
        needsDraw = true;
      }
    }
    listen(window, 'resize', resize, { passive: true });
    listen(document, 'visibilitychange', () => {
      heldKeys.clear();
      needsDraw = true;
      lastFrameTick = fenceStarted = performance.now();
    });
    resize();
    function frame(now) {
      const delayed = now - lastFrameTick > 5000;
      lastFrameTick = now;
      if (!usable()) return;
      frameId = requestAnimationFrame(frame);
      if (document.hidden) return;
      // Animation callbacks can resume before the forwarded visibility event.
      // Sleep/background time must not consume the GPU's response deadline.
      if (delayed) fenceStarted = now;
      if (frameFence) {
        const state = gl.clientWaitSync(frameFence, 0, 0);
        if (!usable()) return;
        if (state === gl.TIMEOUT_EXPIRED) {
          if (now - fenceStarted > 5000) stop('The graphics device stopped responding.');
          return;
        }
        gl.deleteSync(frameFence);
        frameFence = null;
        if (state === gl.WAIT_FAILED) {
          stop('Graphics synchronization failed.');
          return;
        }
        if (awaitingFirstFrame && frameJob === job) {
          awaitingFirstFrame = false;
          status('ready', 'Surface ready', activeMeta);
        }
      }
      if (now - lastDraw < 16 && !needsDraw) return;
      // Follow elapsed time during slow frames; cap only long suspension gaps.
      const dt = Math.min(0.25, (now - last) / 1000);
      last = now;
      resize();
      if (!activeCount || !activeVao) {
        if (needsDraw) {
          gl.bindFramebuffer(gl.FRAMEBUFFER, null);
          gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
          needsDraw = false;
        }
        return;
      }
      if (heldKeys.size) {
        const has = (key, alias) => heldKeys.has(key) || heldKeys.has(alias);
        const dx = has('arrowright', 'd') - has('arrowleft', 'a'),
          dy = has('arrowdown', 's') - has('arrowup', 'w'),
          dz = heldKeys.has('x') - heldKeys.has('z');
        if (dx || dy) rotateCamera(dx * 200 * dt, dy * 200 * dt);
        if (dz) zoomCamera(dz * 1.2 * dt);
      }
      // Camera easing also ramps held-key motion up and down without key-repeat steps.
      const idle = reduced ? 0 : 0.01 * Math.sin(now * 0.00023),
        idle2 = reduced ? 0 : 0.007 * Math.sin(now * 0.00017 + 1.7);
      const desiredOrientation =
        cameraMode === 'free'
          ? orbitOrientation
          : ScreenTrackball.rotate(
              homeOrientation,
              0.115 * targetX + idle,
              -0.082 * targetY + idle2
            );
      const homeBasis = ScreenTrackball.basis(homeOrientation);
      const desiredDistance = cameraMode === 'free' ? orbitDistance : baseDistance,
        desiredCenter =
          cameraMode === 'free'
            ? orbitCenter
            : baseCenter.map(
                (value, i) =>
                  value +
                  0.038 * targetX * homeBasis.right[i] -
                  0.026 * targetY * homeBasis.up[i] +
                  (reduced ? 0 : 0.008 * Math.sin(now * 0.00016)) * homeBasis.back[i]
              ),
        cameraEase = 1 - Math.exp(-dt * (cameraMode === 'free' ? 12 : 7));
      const turning =
        1 -
          Math.abs(
            cameraOrientation.reduce((sum, value, i) => sum + value * desiredOrientation[i], 0)
          ) >
        1e-12;
      const moving =
        turning ||
        Math.abs(desiredDistance - cameraDistance) > 1e-7 ||
        desiredCenter.some((value, i) => Math.abs(value - cameraCenter[i]) > 1e-7);
      if (!needsDraw && !moving && (reduced || cameraMode === 'free')) return;
      lastDraw = now;
      gl.bindFramebuffer(gl.FRAMEBUFFER, null);
      gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
      cameraOrientation = ScreenTrackball.slerp(cameraOrientation, desiredOrientation, cameraEase);
      cameraDistance += (desiredDistance - cameraDistance) * cameraEase;
      for (let i = 0; i < 3; i++)
        cameraCenter[i] += (desiredCenter[i] - cameraCenter[i]) * cameraEase;
      const basis = ScreenTrackball.basis(cameraOrientation),
        eye = cameraCenter.map((c, i) => c + cameraDistance * basis.back[i]);
      gl.useProgram(p);
      gl.bindVertexArray(activeVao);
      gl.uniformMatrix4fv(U.View, false, lookAt(eye, cameraCenter, basis.up));
      gl.uniformMatrix4fv(
        U.Projection,
        false,
        perspective(
          FOV,
          canvas.width / canvas.height,
          Math.max(0.0005, Math.min(0.035, cameraDistance * 0.025)),
          40
        )
      );
      gl.uniform3fv(U.Camera, new Float32Array(eye));
      gl.uniform1f(U.TransNear, 0);
      gl.uniform1f(U.TransFar, 2);
      gl.uniform1f(U.TransMinAlpha, 0.18);
      const draw = () => gl.drawElements(gl.TRIANGLES, activeCount, gl.UNSIGNED_INT, 0),
        bounds = Math.max(1.01, activeMeta.positionBound || 0),
        distanceToBounds = Math.hypot(...eye.map((c) => Math.max(0, Math.abs(c) - bounds)));
      if (distanceToBounds < 2) {
        try {
          if (!depthPeeler) depthPeeler = createDepthPeeler(gl, p);
          depthPeeler.render(
            canvas.width,
            canvas.height,
            activeVao,
            draw,
            6,
            activeMeta.projectionBox === 0
          );
        } catch (error) {
          if (!usable()) return;
          if (depthPeeler) depthPeeler.dispose();
          stop(error.message);
          return;
        }
      } else {
        gl.bindFramebuffer(gl.FRAMEBUFFER, null);
        gl.viewport(0, 0, canvas.width, canvas.height);
        gl.useProgram(p);
        gl.bindVertexArray(activeVao);
        gl.uniform1i(U.RenderPass, 0);
        gl.depthMask(true);
        gl.enable(gl.DEPTH_TEST);
        gl.disable(gl.BLEND);
        gl.disable(gl.CULL_FACE);
        draw();
      }
      if (!usable()) return;
      frameJob = job;
      fenceStarted = performance.now();
      frameFence = gl.fenceSync(gl.SYNC_GPU_COMMANDS_COMPLETE, 0);
      if (!frameFence) {
        stop('Graphics synchronization is unavailable.');
        return;
      }
      gl.flush();
      needsDraw = false;
    }
    frameId = requestAnimationFrame(frame);
    return {
      setCase,
      setMode,
      resetCamera,
      getMeta: () => activeMeta,
      getMode: () => cameraMode,
      getCamera: () => ({
        orientation: cameraOrientation.slice(),
        distance: cameraDistance,
        center: cameraCenter.slice(),
        mode: cameraMode
      }),
      destroy() {
        const valid = usable();
        cancel();
        cancelAnimationFrame(frameId);
        listeners.forEach((f) => f());
        if (valid) {
          if (frameFence) gl.deleteSync(frameFence);
          if (depthPeeler) depthPeeler.dispose();
          clearMesh();
          gl.deleteProgram(p);
        }
        destroyed = true;
        meshes.dispose();
      }
    };
  }
  globalThis.HodgeSurfaceCore = Object.freeze({ create });
})();
