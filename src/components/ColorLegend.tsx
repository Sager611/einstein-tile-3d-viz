import { useId, useMemo, useState, type CSSProperties } from "react"
import { ChevronDown, Eye, Palette, Repeat2 } from "lucide-react"

import {
  Tooltip,
  TooltipContent,
  TooltipProvider,
  TooltipTrigger,
} from "@/components/ui/tooltip"
import { Button } from "@/components/ui/button"
import { getLegendEntries } from "@/lib/color-groups"
import type { ExplorerSettings } from "@/lib/explorer-state"

import "./color-legend.css"

type ColorLegendProps = {
  settings: ExplorerSettings
  onChange: (patch: Partial<ExplorerSettings>) => void
}

const modeLabels = {
  families: "Family",
  orientation: "Rotation",
  porcelain: "Clay",
} as const

const nextMode = {
  orientation: "families",
  families: "porcelain",
  porcelain: "orientation",
} as const

function initialExpanded(): boolean {
  if (typeof window === "undefined" || typeof window.matchMedia !== "function") return true
  return !window.matchMedia("(max-width: 640px)").matches
}

export function ColorLegend({ settings, onChange }: ColorLegendProps) {
  const [expanded, setExpanded] = useState(initialExpanded)
  const reactId = useId()
  const entries = useMemo(
    () => getLegendEntries(settings.level, settings.colorMode),
    [settings.level, settings.colorMode],
  )
  const contentId = `color-legend-entries-${reactId.replace(/:/g, "")}`
  const modeLabel = modeLabels[settings.colorMode]
  const hiddenGroups = settings.hiddenGroups
  const hiddenSet = useMemo(() => new Set(hiddenGroups), [hiddenGroups])
  const hasCurrentFilters = entries.some((entry) => hiddenSet.has(entry.key))

  const toggleGroup = (key: string) => {
    const nextHiddenGroups = hiddenSet.has(key)
      ? hiddenGroups.filter((group) => group !== key)
      : [...hiddenGroups, key]
    onChange({ hiddenGroups: nextHiddenGroups })
  }

  return (
    <TooltipProvider delayDuration={180}>
      <section className="color-legend" aria-label="Color legend">
        <div className="color-legend__header">
          <Button
            className="color-legend__collapse"
            type="button"
            variant="ghost"
            size="sm"
            aria-expanded={expanded}
            aria-controls={contentId}
            onClick={() => setExpanded((current) => !current)}
          >
            <Palette aria-hidden="true" />
            <span>{modeLabel}</span>
            <ChevronDown className="color-legend__chevron" aria-hidden="true" />
          </Button>
          <Tooltip>
            <TooltipTrigger asChild>
              <Button
                className="color-legend__show-all"
                type="button"
                variant="ghost"
                size="icon"
                aria-label={`Color by ${modeLabels[nextMode[settings.colorMode]]}`}
                onClick={() => onChange({ colorMode: nextMode[settings.colorMode] })}
              >
                <Repeat2 aria-hidden="true" />
              </Button>
            </TooltipTrigger>
            <TooltipContent>{`Color by ${modeLabels[nextMode[settings.colorMode]]}`}</TooltipContent>
          </Tooltip>
          {hasCurrentFilters && (
            <Tooltip>
              <TooltipTrigger asChild>
                <Button
                  className="color-legend__show-all"
                  type="button"
                  variant="ghost"
                  size="icon"
                  aria-label="Show all colors"
                  onClick={() => onChange({ hiddenGroups: [] })}
                >
                  <Eye aria-hidden="true" />
                </Button>
              </TooltipTrigger>
              <TooltipContent>Show all colors</TooltipContent>
            </Tooltip>
          )}
        </div>
        <div
          id={contentId}
          className="color-legend__content"
          data-mode={settings.colorMode}
          hidden={!expanded}
        >
          <ul
            className="color-legend__entries"
            data-mode={settings.colorMode}
            aria-label={`${modeLabel} colors`}
          >
            {entries.map((entry, index) => {
              const isHidden = hiddenSet.has(entry.key)
              const action = isHidden ? "Show" : "Hide"
              const tooltip = `${action} ${entry.label}. ${entry.description} ${entry.count} tiles in this level`

              return (
                <li className="color-legend__item" key={entry.key}>
                  <Tooltip>
                    <TooltipTrigger asChild>
                      <Button
                        className="color-legend__swatch"
                        type="button"
                        variant="ghost"
                        size="icon-sm"
                        style={{ "--color-legend-color": entry.color } as CSSProperties}
                        data-hidden={isHidden ? "true" : "false"}
                        aria-label={`${action} ${entry.label}`}
                        aria-pressed={!isHidden}
                        onClick={() => toggleGroup(entry.key)}
                      >
                        <span className="color-legend__dot" aria-hidden="true" />
                        <span className="color-legend__index" aria-hidden="true">
                          {index + 1}
                        </span>
                      </Button>
                    </TooltipTrigger>
                    <TooltipContent side="top" align="center">
                      {tooltip}
                    </TooltipContent>
                  </Tooltip>
                </li>
              )
            })}
          </ul>
        </div>
      </section>
    </TooltipProvider>
  )
}
