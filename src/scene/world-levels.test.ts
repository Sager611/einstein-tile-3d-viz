import { afterEach, describe, expect, it } from 'vitest';
import { Color, Matrix4, MeshStandardMaterial, Raycaster, Vector3 } from 'three';
import { getTiles } from '../lib/chair44';
import { tileColor } from '../lib/color-groups';
import { DEFAULT_SETTINGS, type ExplorerSettings } from '../lib/explorer-state';
import { TileWorld } from './world';

const worlds: TileWorld[] = [];
function createWorld(overrides: Partial<ExplorerSettings> = {}): TileWorld {
  const world = new TileWorld({ ...DEFAULT_SETTINGS, spread: 0, ...overrides });
  worlds.push(world);
  return world;
}
afterEach(() => { worlds.splice(0).forEach((world) => world.dispose()); });

function featureMaterial(world: TileWorld): MeshStandardMaterial {
  const materials = world.body.material;
  if (!Array.isArray(materials) || !(materials[1] instanceof MeshStandardMaterial)) {
    throw new Error('Expected a separate material for the pyramid surfaces');
  }
  return materials[1];
}

function renderedColor(world: TileWorld, index: number): string {
  const color = new Color();
  world.body.getColorAt(index, color);
  return color.getHexString();
}

describe('large levels and color visibility', () => {
  it.each([[4, 4096], [5, 32768]])('renders every tile at level %i', (level, count) => {
    const world = createWorld({ level });
    expect(world.visibleCount).toBe(count);
    expect(world.body.count).toBe(count);
    expect(world.body.geometry.getAttribute('position').count / 3).toBe(48);
    expect(world.lines.visible).toBe(false);
    expect(world.selectedDetail.visible).toBe(false);
  });

  it('hides an entire level-five family and restores it without sampling', () => {
    const settings = { ...DEFAULT_SETTINGS, level: 5, spread: 0 };
    const world = createWorld(settings);
    world.update({ ...settings, hiddenGroups: ['families:0'] }, null);
    expect(world.visibleCount).toBe(28672);
    expect(world.body.count).toBe(28672);
    expect(world.tileCenter(0)).toBeNull();
    world.update(settings, null);
    expect(world.visibleCount).toBe(32768);
    expect(world.tileCenter(0)?.toArray()).toEqual([-31, -31, -31]);
    world.update({ ...settings, slice: 0.5 }, null);
    expect(world.visibleCount).toBeGreaterThan(0);
    expect(world.visibleCount).toBeLessThan(32768);
  });

  it('handles all-hidden views and scopes filters to their color mode', () => {
    const settings: ExplorerSettings = { ...DEFAULT_SETTINGS, level: 4, colorMode: 'porcelain', spread: 0 };
    const world = createWorld(settings);
    world.update({ ...settings, hiddenGroups: ['porcelain:0'] }, null);
    expect(world.visibleCount).toBe(0);
    expect(world.body.count).toBe(0);
    expect(world.tileCenter(0)).toBeNull();
    expect(world.pick(new Raycaster(new Vector3(0, 0, -100), new Vector3(0, 0, 1)))).toBeNull();
    world.update({ ...settings, hiddenGroups: ['families:0'] }, null);
    expect(world.visibleCount).toBe(4096);
    world.update(settings, null);
    expect(world.visibleCount).toBe(4096);
  });

  it('uses the same family, orientation, and clay colors as the legend', () => {
    const settings = { ...DEFAULT_SETTINGS, level: 2, spread: 0 };
    const world = createWorld(settings);
    const pose = getTiles(2)[1];
    const family = renderedColor(world, 1);
    expect(family).toBe(new Color(tileColor(pose, 'families')).getHexString());
    world.update({ ...settings, colorMode: 'orientation' }, null);
    expect(renderedColor(world, 1)).toBe(new Color(tileColor(pose, 'orientation')).getHexString());
    expect(renderedColor(world, 1)).not.toBe(family);
    world.update({ ...settings, colorMode: 'porcelain' }, null);
    expect(renderedColor(world, 1)).toBe(new Color(tileColor(pose, 'porcelain')).getHexString());
    expect(renderedColor(world, 0)).toBe(renderedColor(world, 1));
  });

  it('toggles highlighting and edges without removing the real surface', () => {
    const settings = { ...DEFAULT_SETTINGS, level: 1, spread: 0, showFeatures: false, showEdges: false };
    const world = createWorld(settings);
    const material = featureMaterial(world);
    expect(material.visible).toBe(true);
    expect(material.vertexColors).toBe(false);
    expect(world.lines.visible).toBe(false);
    const version = material.version;
    world.update({ ...settings, showFeatures: true, showEdges: true }, null);
    expect(material.visible).toBe(true);
    expect(material.vertexColors).toBe(true);
    expect(material.version).toBeGreaterThan(version);
    expect(world.lines.visible).toBe(true);
    expect(world.body.geometry.getAttribute('position').count / 3).toBe(4272);
  });

  it('promotes a selected overview tile, picks it, and removes it when filtered', () => {
    const settings = { ...DEFAULT_SETTINGS, level: 5, spread: 0 };
    const world = createWorld(settings);
    world.update(settings, 0);
    expect(world.visibleCount).toBe(32768);
    expect(world.selectedDetail.visible).toBe(true);
    expect(world.selectedDetail.geometry.getAttribute('position').count / 3).toBe(4272);
    const matrix = new Matrix4();
    world.body.getMatrixAt(0, matrix);
    expect(matrix.elements).toEqual(new Matrix4().makeScale(0, 0, 0).elements);
    expect(world.tileCenter(0)?.toArray()).toEqual([-31, -31, -31]);
    world.root.updateMatrixWorld(true);
    const ray = new Raycaster(new Vector3(-31.5, -31.5, -100), new Vector3(0, 0, 1));
    expect(world.pick(ray)).toBe(0);
    world.update({ ...settings, hiddenGroups: ['families:0'] }, 0);
    expect(world.selectedDetail.visible).toBe(false);
    expect(world.selectedDetail.matrix.getMaxScaleOnAxis()).toBe(0);
    expect(world.tileCenter(0)).toBeNull();
    world.update(settings, null);
    expect(world.visibleCount).toBe(32768);
    expect(world.selectedDetail.visible).toBe(false);
  });
});
