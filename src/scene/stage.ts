import {
  ACESFilmicToneMapping,
  AmbientLight,
  Box3,
  Color,
  DirectionalLight,
  HemisphereLight,
  MathUtils,
  Mesh,
  OrthographicCamera,
  PCFSoftShadowMap,
  PerspectiveCamera,
  PlaneGeometry,
  Raycaster,
  Scene,
  ShadowMaterial,
  Vector2,
  Vector3,
  WebGLRenderer,
} from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { OVERVIEW_LEVEL } from '../lib/explorer-state';
import type { ExplorerSettings, SceneHandle, ViewPreset } from '../lib/explorer-state';
import { TileWorld } from './world';

export interface Stage extends SceneHandle {
  update(settings: ExplorerSettings, selectedId: number | null): void;
  dispose(): void;
}

const FIT_MARGIN = 1.4;
const TOP_EPSILON = 1e-3;
const CLICK_DISTANCE = 5;

function normalizeHiddenGroups(hiddenGroups: string[]): string[] {
  return [...new Set(hiddenGroups)].sort();
}

function cloneSettings(settings: ExplorerSettings): ExplorerSettings {
  return { ...settings, hiddenGroups: normalizeHiddenGroups(settings.hiddenGroups) };
}

function settingsEqual(first: ExplorerSettings, second: ExplorerSettings): boolean {
  const firstHiddenGroups = normalizeHiddenGroups(first.hiddenGroups);
  const secondHiddenGroups = normalizeHiddenGroups(second.hiddenGroups);
  return (
    first.level === second.level &&
    first.spread === second.spread &&
    first.slice === second.slice &&
    first.relief === second.relief &&
    first.showFeatures === second.showFeatures &&
    first.showEdges === second.showEdges &&
    first.colorMode === second.colorMode &&
    first.autoRotate === second.autoRotate &&
    firstHiddenGroups.length === secondHiddenGroups.length &&
    firstHiddenGroups.every((group, index) => group === secondHiddenGroups[index])
  );
}

function getReducedMotion(): boolean {
  return typeof window !== 'undefined' &&
    typeof window.matchMedia === 'function' &&
    window.matchMedia('(prefers-reduced-motion: reduce)').matches;
}

export function createStage(
  container: HTMLDivElement,
  initial: ExplorerSettings,
  onSelect: (id: number | null) => void,
  onCount: (count: number) => void,
): Stage {
  const reducedMotion = getReducedMotion();
  const settings = cloneSettings(initial);
  let renderedSettings = cloneSettings(settings);
  let selectedId: number | null = null;
  let lastWorldSettings: ExplorerSettings | null = null;
  let lastWorldSelection: number | null = null;
  let lastCount: number | null = null;
  let spread = settings.spread;
  let disposed = false;
  let frame = 0;
  let lastFrameTime = typeof performance !== 'undefined' ? performance.now() : 0;
  let initialFitPending = true;
  let needsRender = true;
  let pendingRenderFrames = 2;

  const renderer = new WebGLRenderer({
    antialias: true,
    alpha: false,
    preserveDrawingBuffer: true,
  });
  renderer.setPixelRatio(Math.min(typeof window === 'undefined' ? 1 : window.devicePixelRatio || 1, 1.75));
  renderer.outputColorSpace = 'srgb';
  renderer.toneMapping = ACESFilmicToneMapping;
  renderer.toneMappingExposure = 1.12;
  renderer.shadowMap.enabled = true;
  renderer.shadowMap.type = PCFSoftShadowMap;
  renderer.domElement.setAttribute('aria-label', 'Interactive Chair44 model');
  renderer.domElement.style.touchAction = 'none';
  container.appendChild(renderer.domElement);

  const scene = new Scene();
  scene.background = new Color('#f7f6f2');
  const camera = new PerspectiveCamera(38, 1, 0.05, 500);
  camera.up.set(0, 0, 1);
  camera.position.set(6, 6, 5);
  // Orthographic view mirrors the orbit camera; its frustum matches the perspective view at the target.
  const orthoCamera = new OrthographicCamera(-1, 1, 1, -1, -1000, 1000);
  let orthographic = false;
  const activeCamera = (): PerspectiveCamera | OrthographicCamera => {
    if (!orthographic) return camera;
    const distance = Math.max(camera.position.distanceTo(controls.target), 0.01);
    const halfHeight = distance * Math.tan(MathUtils.degToRad(camera.fov) * 0.5);
    const halfWidth = halfHeight * camera.aspect;
    orthoCamera.left = -halfWidth;
    orthoCamera.right = halfWidth;
    orthoCamera.top = halfHeight;
    orthoCamera.bottom = -halfHeight;
    orthoCamera.position.copy(camera.position);
    orthoCamera.quaternion.copy(camera.quaternion);
    orthoCamera.up.copy(camera.up);
    orthoCamera.updateProjectionMatrix();
    orthoCamera.updateMatrixWorld(true);
    return orthoCamera;
  };

  const world = new TileWorld(settings);
  scene.add(world.root);

  let extent = Math.max(world.extent, 1);
  const ambient = new AmbientLight(0xfffbf2, 0.8);
  const hemisphere = new HemisphereLight(0xfff9ef, 0x706b67, 1.1);
  const directional = new DirectionalLight(0xfff4e4, 2.1);
  directional.castShadow = true;
  directional.shadow.mapSize.set(1024, 1024);
  directional.shadow.camera.near = 0.1;
  directional.shadow.camera.far = extent * 8;
  directional.shadow.camera.left = -extent * 2;
  directional.shadow.camera.right = extent * 2;
  directional.shadow.camera.top = extent * 2;
  directional.shadow.camera.bottom = -extent * 2;
  directional.shadow.bias = -0.00025;
  directional.position.set(extent * 2.5, extent * 2.25, extent * 3.5);
  scene.add(ambient, hemisphere, directional);

  const bounds = new Box3();
  const size = new Vector3();
  const center = new Vector3();
  const fitTarget = new Vector3();

  const refreshBounds = (): number => {
    bounds.setFromObject(world.root);
    if (bounds.isEmpty()) {
      center.set(0, 0, 0);
      size.set(extent, extent, extent);
    } else {
      bounds.getCenter(center);
      bounds.getSize(size);
    }
    return Math.max(size.length() * 0.5, extent * 0.5, 0.5);
  };

  refreshBounds();
  const floorMaterial = new ShadowMaterial({ color: 0x000000, opacity: 0.09 });
  const floor = new Mesh(new PlaneGeometry(200, 200), floorMaterial);
  floor.position.z = -extent / 2 - renderedSettings.spread * (extent / 2 - 1) - 0.06;
  floor.receiveShadow = true;
  scene.add(floor);

  world.root.traverse((object) => {
    if (object instanceof Mesh) {
      object.castShadow = true;
      object.receiveShadow = true;
    }
  });

  const controls = new OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true;
  controls.dampingFactor = 0.08;
  controls.autoRotateSpeed = 0.7;
  controls.autoRotate = settings.autoRotate && !reducedMotion;
  controls.target.set(0, 0, 0);
  const onControlsChange = (): void => {
    needsRender = true;
  };
  controls.addEventListener('change', onControlsChange);

  const rescaleCameraForSpread = (previousSpread: number, nextSpread: number): void => {
    if (Math.abs(nextSpread - previousSpread) < 1e-8) return;
    const previousSide = extent + (extent - 2) * previousSpread;
    const nextSide = extent + (extent - 2) * nextSpread;
    if (
      !Number.isFinite(previousSide) ||
      !Number.isFinite(nextSide) ||
      previousSide <= 0 ||
      nextSide <= 0
    ) {
      return;
    }
    const offset = camera.position.clone().sub(controls.target);
    if (offset.lengthSq() < 1e-8) return;
    camera.position.copy(controls.target).add(offset.multiplyScalar(nextSide / previousSide));
  };

  const raycaster = new Raycaster();
  const pointer = new Vector2();
  let pointerDown: { id: number; x: number; y: number } | null = null;

  const setPointer = (event: PointerEvent): void => {
    const rect = renderer.domElement.getBoundingClientRect();
    const width = Math.max(rect.width, 1);
    const height = Math.max(rect.height, 1);
    pointer.set(
      ((event.clientX - rect.left) / width) * 2 - 1,
      -((event.clientY - rect.top) / height) * 2 + 1,
    );
  };

  const onPointerDown = (event: PointerEvent): void => {
    if (event.button !== 0) return;
    pointerDown = { id: event.pointerId, x: event.clientX, y: event.clientY };
  };

  const onPointerUp = (event: PointerEvent): void => {
    const down = pointerDown;
    pointerDown = null;
    if (!down || down.id !== event.pointerId || event.button !== 0) return;
    const dx = event.clientX - down.x;
    const dy = event.clientY - down.y;
    if (dx * dx + dy * dy >= CLICK_DISTANCE * CLICK_DISTANCE) return;
    setPointer(event);
    raycaster.setFromCamera(pointer, activeCamera());
    const picked = world.pick(raycaster);
    selectedId = picked;
    if (lastWorldSelection !== selectedId) syncWorld(true);
    onSelect(picked);
  };

  const onPointerCancel = (): void => {
    pointerDown = null;
  };

  renderer.domElement.addEventListener('pointerdown', onPointerDown);
  renderer.domElement.addEventListener('pointerup', onPointerUp);
  renderer.domElement.addEventListener('pointercancel', onPointerCancel);

  const onContextLost = (event: Event): void => {
    event.preventDefault();
  };
  renderer.domElement.addEventListener('webglcontextlost', onContextLost, false);

  const getTarget = (): Vector3 => {
    refreshBounds();
    fitTarget.copy(center);
    fitTarget.z -= Math.max(size.z * 0.12, extent * 0.04);
    return fitTarget;
  };

  const fit = (useIsoDirection: boolean): void => {
    const radius = refreshBounds();
    const target = getTarget();
    let direction = camera.position.clone().sub(controls.target);
    if (useIsoDirection || direction.lengthSq() < 1e-8) direction.set(1, 1, 0.82);
    direction.normalize();
    const aspect = Math.max(camera.aspect, 0.1);
    const vertical = Math.tan(MathUtils.degToRad(camera.fov) * 0.5);
    const horizontal = Math.tan(MathUtils.degToRad(camera.fov) * 0.5) * aspect;
    const distance = Math.max(radius / vertical, radius / horizontal) * FIT_MARGIN;
    controls.target.copy(target);
    camera.position.copy(target).add(direction.multiplyScalar(distance));
    camera.lookAt(target);
    controls.update();
    needsRender = true;
  };

  const setView = (next: ViewPreset): void => {
    const target = controls.target.clone();
    const distance = Math.max(camera.position.distanceTo(target), extent * 2);
    if (next === 'top') {
      camera.up.set(0, 0, 1);
      camera.position.set(target.x, target.y - TOP_EPSILON * distance, target.z + distance);
    } else if (next === 'front') {
      camera.up.set(0, 0, 1);
      camera.position.set(target.x, target.y - distance, target.z);
    } else {
      camera.up.set(0, 0, 1);
      camera.position.copy(target).add(new Vector3(1, 1, 0.82).normalize().multiplyScalar(distance));
    }
    camera.lookAt(target);
    controls.update();
    needsRender = true;
  };

  const reset = (): void => {
    setView('iso');
    fit(true);
  };

  const zoom = (factor: number): void => {
    if (!Number.isFinite(factor) || factor <= 0) return;
    const target = controls.target;
    const offset = camera.position.clone().sub(target);
    const distance = MathUtils.clamp(offset.length() * factor, Math.max(extent * 0.18, 0.25), extent * 30);
    if (offset.lengthSq() < 1e-8) offset.set(1, 1, 0.82).normalize();
    else offset.normalize();
    camera.position.copy(target).add(offset.multiplyScalar(distance));
    camera.lookAt(target);
    controls.update();
    needsRender = true;
  };

  const focus = (): void => {
    if (selectedId === null) return;
    const selectedCenter = world.tileCenter(selectedId);
    if (!selectedCenter) return;
    let direction = camera.position.clone().sub(controls.target);
    if (direction.lengthSq() < 1e-8) direction.set(1, 1, 0.82);
    controls.target.copy(selectedCenter);
    camera.position.copy(selectedCenter).add(direction.normalize().multiplyScalar(4));
    camera.lookAt(selectedCenter);
    controls.update();
    needsRender = true;
  };

  const capture = (): string | null => {
    try {
      renderer.render(scene, activeCamera());
      return renderer.domElement.toDataURL('image/png');
    } catch {
      return null;
    }
  };

  function syncWorld(force = false): void {
    if (
      !force &&
      lastWorldSettings &&
      settingsEqual(lastWorldSettings, renderedSettings) &&
      lastWorldSelection === selectedId
    ) {
      return;
    }
    world.update(renderedSettings, selectedId);
    if (selectedId !== null && world.tileCenter(selectedId) === null) {
      selectedId = null;
      onSelect(null);
    }
    extent = Math.max(world.extent, 1);
    // Keep the whole assembly (plus exploded spread) inside the depth range at every level.
    camera.far = Math.max(500, extent * 40);
    camera.updateProjectionMatrix();
    orthoCamera.near = -camera.far;
    orthoCamera.far = camera.far;
    floor.position.z = -extent / 2 - renderedSettings.spread * (extent / 2 - 1) - 0.06;
    directional.position.set(extent * 2.5, extent * 2.25, extent * 3.5);
    directional.shadow.camera.far = extent * 8;
    directional.shadow.camera.left = -extent * 2;
    directional.shadow.camera.right = extent * 2;
    directional.shadow.camera.top = extent * 2;
    directional.shadow.camera.bottom = -extent * 2;
    directional.shadow.camera.updateProjectionMatrix();
    lastWorldSettings = cloneSettings(renderedSettings);
    lastWorldSelection = selectedId;
    if (lastCount !== world.visibleCount) {
      lastCount = world.visibleCount;
      onCount(world.visibleCount);
    }
    needsRender = true;
  }

  const applySettings = (next: ExplorerSettings, nextSelectedId: number | null): void => {
    const previous = cloneSettings(settings);
    const normalizedNext = { ...next, hiddenGroups: normalizeHiddenGroups(next.hiddenGroups) };
    const changed = !settingsEqual(previous, normalizedNext) || selectedId !== nextSelectedId;
    const previousSpread = spread;
    const previousExtent = extent;
    Object.assign(settings, normalizedNext);
    selectedId = nextSelectedId;
    controls.autoRotate = settings.autoRotate && !reducedMotion;
    const immediateSpread = reducedMotion || settings.level >= OVERVIEW_LEVEL;
    if (immediateSpread) spread = settings.spread;
    renderedSettings = { ...settings, spread };
    if (changed) syncWorld();
    if (immediateSpread) rescaleCameraForSpread(previousSpread, spread);
    if (settings.level !== previous.level) {
      // The hierarchy is self-similar about the origin: scaling the view keeps the user's zoom, pan, and angle.
      const scale = extent / Math.max(previousExtent, 1e-6);
      camera.position.multiplyScalar(scale);
      controls.target.multiplyScalar(scale);
      camera.lookAt(controls.target);
      controls.update();
      needsRender = true;
    }
  };

  const resize = (): void => {
    if (disposed) return;
    const width = Math.max(container.clientWidth, 1);
    const height = Math.max(container.clientHeight, 1);
    needsRender = true;
    renderer.setPixelRatio(Math.min(typeof window === 'undefined' ? 1 : window.devicePixelRatio || 1, 1.75));
    renderer.setSize(width, height, false);
    camera.aspect = width / height;
    camera.updateProjectionMatrix();
    if (initialFitPending) {
      initialFitPending = false;
      fit(true);
    }
  };

  let resizeObserver: ResizeObserver | null = null;
  if (typeof ResizeObserver !== 'undefined') {
    resizeObserver = new ResizeObserver(resize);
    resizeObserver.observe(container);
  } else if (typeof window !== 'undefined') {
    window.addEventListener('resize', resize);
  }

  syncWorld(true);
  resize();

  const tick = (now: number): void => {
    if (disposed) return;
    const delta = Math.min(Math.max((now - lastFrameTime) / 1000, 0), 0.1);
    lastFrameTime = now;
    if (!reducedMotion && settings.level < OVERVIEW_LEVEL && Math.abs(spread - settings.spread) > 1e-5) {
      const previousSpread = spread;
      const nextSpread = MathUtils.damp(spread, settings.spread, 10, delta);
      spread = Math.abs(nextSpread - settings.spread) < 1e-5 ? settings.spread : nextSpread;
      rescaleCameraForSpread(previousSpread, spread);
      renderedSettings = { ...settings, spread };
      syncWorld();
    }
    controls.update();
    // Settle a second frame after geometry/instance changes, then leave idle GPUs alone.
    if (needsRender) pendingRenderFrames = 2;
    if (pendingRenderFrames > 0) {
      needsRender = false;
      renderer.render(scene, activeCamera());
      pendingRenderFrames -= 1;
    }
    frame = requestAnimationFrame(tick);
  };

  frame = requestAnimationFrame(tick);

  return {
    reset,
    setView,
    zoom,
    capture,
    focus,
    setOrthographic(enabled: boolean): void {
      orthographic = enabled;
      needsRender = true;
    },
    update(nextSettings: ExplorerSettings, nextSelectedId: number | null): void {
      applySettings(nextSettings, nextSelectedId);
    },
    dispose(): void {
      if (disposed) return;
      disposed = true;
      cancelAnimationFrame(frame);
      resizeObserver?.disconnect();
      if (!resizeObserver && typeof window !== 'undefined') window.removeEventListener('resize', resize);
      renderer.domElement.removeEventListener('pointerdown', onPointerDown);
      renderer.domElement.removeEventListener('pointerup', onPointerUp);
      renderer.domElement.removeEventListener('pointercancel', onPointerCancel);
      renderer.domElement.removeEventListener('webglcontextlost', onContextLost);
      controls.removeEventListener('change', onControlsChange);
      controls.dispose();
      world.dispose();
      scene.remove(floor, ambient, hemisphere, directional, world.root);
      floor.geometry.dispose();
      floorMaterial.dispose();
      directional.shadow.map?.dispose();
      renderer.dispose();
      if (renderer.domElement.parentElement === container) container.removeChild(renderer.domElement);
    },
  };
}
