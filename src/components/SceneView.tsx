import { forwardRef, useEffect, useImperativeHandle, useRef } from 'react'

import type { ExplorerSettings, SceneHandle } from '@/lib/explorer-state'
import { createStage, type Stage } from '@/scene/stage'

export type SceneViewProps = {
  settings: ExplorerSettings
  selectedId: number | null
  onSelect: (id: number | null) => void
  onCount: (count: number) => void
  onError: (message: string) => void
}

export const SceneView = forwardRef<SceneHandle, SceneViewProps>(function SceneView(
  { settings, selectedId, onSelect, onCount, onError },
  ref,
) {
  const containerRef = useRef<HTMLDivElement>(null)
  const stageRef = useRef<Stage | null>(null)
  const settingsRef = useRef(settings)
  const onSelectRef = useRef(onSelect)
  const onCountRef = useRef(onCount)
  const onErrorRef = useRef(onError)

  settingsRef.current = settings
  onSelectRef.current = onSelect
  onCountRef.current = onCount
  onErrorRef.current = onError

  useEffect(() => {
    const container = containerRef.current
    if (!container) return

    let stage: Stage | null = null
    try {
      stage = createStage(
        container,
        settingsRef.current,
        (id) => onSelectRef.current(id),
        (count) => onCountRef.current(count),
      )
      stageRef.current = stage
    } catch {
      onErrorRef.current('Unable to start the 3D viewer. WebGL may be unavailable or blocked in this browser.')
    }

    return () => {
      stage?.dispose()
      if (stageRef.current === stage) stageRef.current = null
    }
  }, [])

  useEffect(() => {
    stageRef.current?.update(settings, selectedId)
  }, [settings, selectedId])

  useImperativeHandle(ref, () => ({
    reset: () => stageRef.current?.reset(),
    setView: (view) => stageRef.current?.setView(view),
    zoom: (factor) => stageRef.current?.zoom(factor),
    capture: () => stageRef.current?.capture() ?? null,
    focus: () => stageRef.current?.focus(),
    setOrthographic: (enabled) => stageRef.current?.setOrthographic(enabled),
  }), [])

  return <div ref={containerRef} className="scene-host" aria-label="Interactive Chair44 3D scene" />
})

export default SceneView
