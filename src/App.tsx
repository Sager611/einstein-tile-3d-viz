import { useCallback, useEffect, useRef, useState } from "react"
import {
  Box,
  Download,
  Focus,
  Github,
  Info,
  Link2,
  PanelTop,
  PanelsTopLeft,
  RotateCcw,
  X,
  ZoomIn,
  ZoomOut,
} from "lucide-react"

import { ControlDock, IconButton } from "./components/ControlDock"
import { InfoDialog } from "./components/InfoDialog"
import { SceneView } from "./components/SceneView"
import {
  DEFAULT_SETTINGS,
  decodeSettings,
  encodeSettings,
  normalizeSettings,
  type ExplorerSettings,
  type SceneHandle,
} from "./lib/explorer-state"
import {
  Tooltip,
  TooltipContent,
  TooltipProvider as AppTooltipProvider,
  TooltipTrigger,
} from "./components/ui/tooltip"

export default function App() {
  const sceneRef = useRef<SceneHandle>(null)
  const [settings, setSettings] = useState<ExplorerSettings>(() =>
    decodeSettings(typeof window === "undefined" ? "" : window.location.hash),
  )
  const [selectedId, setSelectedId] = useState<number | null>(null)
  const [visibleCount, setVisibleCount] = useState(0)
  const [sceneError, setSceneError] = useState(false)
  const [notice, setNotice] = useState<string | null>(null)
  const [aboutOpen, setAboutOpen] = useState(false)

  const update = useCallback((patch: Partial<ExplorerSettings>) => {
    setSettings((current) => normalizeSettings({ ...current, ...patch }))
  }, [])

  const announce = useCallback((message: string) => {
    setNotice(message)
    window.setTimeout(() => setNotice(null), 2200)
  }, [])

  const reset = useCallback(() => {
    setSettings(normalizeSettings(DEFAULT_SETTINGS))
    setSelectedId(null)
    sceneRef.current?.reset()
  }, [])

  useEffect(() => {
    setSelectedId(null)
  }, [settings.level])

  useEffect(() => {
    const timer = window.setTimeout(() => {
      const hash = encodeSettings(settings)
      if (window.location.hash !== hash) window.history.replaceState(null, "", hash)
    }, 180)
    return () => window.clearTimeout(timer)
  }, [settings])

  useEffect(() => {
    const onHashChange = () => setSettings(decodeSettings(window.location.hash))
    window.addEventListener("hashchange", onHashChange)
    return () => window.removeEventListener("hashchange", onHashChange)
  }, [])

  useEffect(() => {
    const onKeyDown = (event: KeyboardEvent) => {
      const target = event.target instanceof HTMLElement ? event.target : null
      if (
        target?.matches("input,textarea,select,button,[role=slider],[contenteditable=true]") ||
        target?.isContentEditable ||
        target?.closest('[role="dialog"]')
      ) {
        return
      }

      if (event.key === "Escape") {
        setSelectedId(null)
      } else if (event.key.toLowerCase() === "r") {
        event.preventDefault()
        reset()
      } else if (event.code === "Space") {
        event.preventDefault()
        update({ autoRotate: !settings.autoRotate })
      }
    }

    window.addEventListener("keydown", onKeyDown)
    return () => window.removeEventListener("keydown", onKeyDown)
  }, [reset, settings.autoRotate, update])

  const share = useCallback(async () => {
    const hash = encodeSettings(settings)
    if (window.location.hash !== hash) window.history.replaceState(null, "", hash)
    try {
      await navigator.clipboard.writeText(window.location.href)
      announce("Link copied")
    } catch {
      announce("Copy failed — use the address bar")
    }
  }, [announce, settings])

  const exportPng = useCallback(() => {
    const image = sceneRef.current?.capture()
    if (!image) {
      announce("PNG capture unavailable")
      return
    }
    const link = document.createElement("a")
    link.href = image
    link.download = `chair44-level${settings.level}.png`
    link.click()
    announce("PNG downloaded")
  }, [announce, settings.level])

  return (
    <AppTooltipProvider delayDuration={300}>
      <main className="app-shell">
        <header className="topbar">
          <div className="brand" aria-label="chair44">
            <svg className="brand-mark" viewBox="0 0 32 32" aria-hidden="true" focusable="false">
              <path d="M7 5v15m0 0h17M7 20l4 7m13-7 3 7M11 5h12v6H11m0 0v9" fill="none" stroke="currentColor" strokeLinecap="round" strokeLinejoin="round" strokeWidth="1.7" />
            </svg>
            <span className="wordmark">chair44</span>
          </div>

          <div className="header-actions">
            <IconButton label="Reset" onClick={reset}>
              <RotateCcw data-icon="reset" />
            </IconButton>
            <IconButton label="Share" onClick={share}>
              <Link2 data-icon="share" />
            </IconButton>
            <IconButton label="Export PNG" onClick={exportPng}>
              <Download data-icon="export" />
            </IconButton>
            <IconButton label="About" onClick={() => setAboutOpen(true)}>
              <Info data-icon="about" />
            </IconButton>
            <Tooltip>
              <TooltipTrigger asChild>
                <a
                  className="github-link"
                  href="https://github.com/Sager611/einstein-tile-3d-viz"
                  target="_blank"
                  rel="noreferrer"
                  aria-label="GitHub repository"
                >
                  <Github data-icon="github" />
                </a>
              </TooltipTrigger>
              <TooltipContent>GitHub</TooltipContent>
            </Tooltip>
          </div>
        </header>

        <div className="scene-stage">
          <SceneView
            ref={sceneRef}
            settings={settings}
            selectedId={selectedId}
            onSelect={setSelectedId}
            onCount={setVisibleCount}
            onError={() => setSceneError(true)}
          />

          <aside className="camera-rail" aria-label="Camera controls">
            <IconButton label="Iso" onClick={() => sceneRef.current?.setView("iso")}>
              <Box data-icon="iso" />
            </IconButton>
            <IconButton label="Top" onClick={() => sceneRef.current?.setView("top")}>
              <PanelsTopLeft data-icon="top" />
            </IconButton>
            <IconButton label="Front" onClick={() => sceneRef.current?.setView("front")}>
              <PanelTop data-icon="front" />
            </IconButton>
            <IconButton label="Zoom in" onClick={() => sceneRef.current?.zoom(0.8)}>
              <ZoomIn data-icon="zoom-in" />
            </IconButton>
            <IconButton label="Zoom out" onClick={() => sceneRef.current?.zoom(1.25)}>
              <ZoomOut data-icon="zoom-out" />
            </IconButton>
          </aside>

          <div className="scene-meta">
            <span>{visibleCount} {visibleCount === 1 ? "tile" : "tiles"}</span>
            {settings.relief > 1 && (
              <Tooltip>
                <TooltipTrigger asChild>
                  <span>×{settings.relief}</span>
                </TooltipTrigger>
                <TooltipContent>Magnified height, not to scale</TooltipContent>
              </Tooltip>
            )}
          </div>

          {selectedId !== null && (
            <div className="tile-selection" aria-label={`Selected tile #${selectedId + 1}`}>
              <span>#{selectedId + 1}</span>
              <IconButton label="Focus tile" onClick={() => sceneRef.current?.focus()}>
                <Focus data-icon="focus" />
              </IconButton>
              <IconButton label="Clear selection" onClick={() => setSelectedId(null)}>
                <X data-icon="clear" />
              </IconButton>
            </div>
          )}

          <ControlDock
            settings={settings}
            onChange={update}
            onInspect={() =>
              update({
                level: 0,
                spread: 0,
                slice: 1,
                relief: 1,
                showFeatures: true,
                colorMode: "porcelain",
              })
            }
          />

          {sceneError && (
            <div className="scene-error" role="alert">
              <span>WebGL issue. Reload to retry.</span>
              <IconButton label="Reload" onClick={() => window.location.reload()}>
                <RotateCcw data-icon="reload" />
              </IconButton>
            </div>
          )}
          {notice && (
            <div className="scene-notice" role="status" aria-live="polite">
              {notice}
            </div>
          )}
        </div>
      </main>
      <InfoDialog open={aboutOpen} onOpenChange={setAboutOpen} />
    </AppTooltipProvider>
  )
}
