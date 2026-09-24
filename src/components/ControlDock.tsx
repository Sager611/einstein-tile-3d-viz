import type { ButtonHTMLAttributes, ReactNode } from "react"
import { useState } from "react"
import { Microscope, Orbit, Pause, ScanSearch, Settings, Waves } from "lucide-react"

import { MAX_LEVEL } from "@/lib/chair44"
import { OVERVIEW_LEVEL, type ColorMode, type ExplorerSettings } from "@/lib/explorer-state"
import { Button } from "@/components/ui/button"
import {
  Field,
  FieldDescription,
  FieldGroup,
  FieldLabel,
} from "@/components/ui/field"
import { Sheet, SheetContent, SheetDescription, SheetHeader, SheetTitle } from "@/components/ui/sheet"
import { Slider } from "@/components/ui/slider"
import { Switch } from "@/components/ui/switch"
import { ToggleGroup, ToggleGroupItem } from "@/components/ui/toggle-group"
import {
  Tooltip,
  TooltipContent,
  TooltipProvider,
  TooltipTrigger,
} from "@/components/ui/tooltip"

export type ControlDockProps = {
  settings: ExplorerSettings
  onChange: (patch: Partial<ExplorerSettings>) => void
  onInspect: () => void
  warpOpen: boolean
  onWarp: () => void
}

type IconButtonProps = {
  label: string
  children: ReactNode
} & ButtonHTMLAttributes<HTMLButtonElement>

export function IconButton({
  label,
  children,
  "aria-pressed": ariaPressed,
  ...props
}: IconButtonProps) {
  const isActive = ariaPressed === true || ariaPressed === "true"

  return (
    <Tooltip>
      <TooltipTrigger asChild>
        <Button
          {...props}
          type={props.type ?? "button"}
          variant="ghost"
          size="icon"
          aria-label={label}
          aria-pressed={ariaPressed}
          data-active={isActive ? "true" : undefined}
        >
          {children}
        </Button>
      </TooltipTrigger>
      <TooltipContent>{label}</TooltipContent>
    </Tooltip>
  )
}

const colorModes: ReadonlyArray<{ value: ColorMode; label: string }> = [
  { value: "families", label: "Family" },
  { value: "porcelain", label: "Clay" },
  { value: "orientation", label: "Rotation" },
]

const isColorMode = (value: string): value is ColorMode =>
  colorModes.some((mode) => mode.value === value)

type DockSliderProps = {
  id: string
  label: string
  value: string
  currentValue: number
  min: number
  max: number
  step: number
  tooltip: string
  onValueChange: (value: number) => void
}

function DockSlider({
  id,
  label,
  value,
  currentValue,
  min,
  max,
  step,
  tooltip,
  onValueChange,
}: DockSliderProps) {
  return (
    <Field className="dock-field">
      <Tooltip>
        <TooltipTrigger asChild>
          <FieldLabel htmlFor={id}>
            <span>{label}</span>
            <span className="dock-value">{value}</span>
          </FieldLabel>
        </TooltipTrigger>
        <TooltipContent>{tooltip}</TooltipContent>
      </Tooltip>
      <Slider
        id={id}
        aria-label={label}
        min={min}
        max={max}
        step={step}
        value={[currentValue]}
        onValueChange={(nextValue) => onValueChange(nextValue[0] ?? currentValue)}
      />
    </Field>
  )
}

function HeightReset({
  exact,
  onReset,
}: {
  exact: boolean
  onReset: () => void
}) {
  const button = (
    <Button type="button" variant="outline" size="xs" onClick={onReset}>
      1×
    </Button>
  )

  if (exact) {
    return (
      <Tooltip>
        <TooltipTrigger asChild>{button}</TooltipTrigger>
        <TooltipContent>Exact height</TooltipContent>
      </Tooltip>
    )
  }

  return button
}

export function ControlDock({ settings, onChange, onInspect, warpOpen, onWarp }: ControlDockProps) {
  const [moreOpen, setMoreOpen] = useState(false)
  const effectiveRelief = settings.relief
  const reliefIsMagnified = effectiveRelief > 1

  const openMore = () => setMoreOpen(true)
  const handleInspect = () => {
    onInspect()
    openMore()
  }

  return (
    <TooltipProvider>
      <Sheet open={moreOpen} onOpenChange={setMoreOpen} modal={false}>
        <div className="control-dock">
          <DockSlider
            id="level-slider"
            label="Level"
            value={String(settings.level)}
            currentValue={settings.level}
            min={0}
            max={MAX_LEVEL}
            step={1}
            tooltip="8^level: each level multiplies the tile count by eight."
            onValueChange={(value) => onChange({ level: value })}
          />
          <DockSlider
            id="spread-slider"
            label="Spread"
            value={`${Math.round(settings.spread * 100)}%`}
            currentValue={settings.spread}
            min={0}
            max={1}
            step={0.01}
            tooltip="Zero spread means exact fits."
            onValueChange={(value) => onChange({ spread: value })}
          />
          <DockSlider
            id="layers-slider"
            label="Layers"
            value={`${Math.round(settings.slice * 100)}%`}
            currentValue={settings.slice}
            min={0.1}
            max={1}
            step={0.01}
            tooltip="Whole-tile peeling, not cutting."
            onValueChange={(value) => onChange({ slice: value })}
          />

          <div className="dock-actions">
            <IconButton
              label={settings.autoRotate ? "Pause" : "Orbit"}
              aria-pressed={settings.autoRotate}
              onClick={() => onChange({ autoRotate: !settings.autoRotate })}
            >
              {settings.autoRotate ? <Pause data-icon="pause" /> : <Orbit data-icon="orbit" />}
            </IconButton>
            <IconButton label="Single chair" onClick={() => onChange({ level: 0, spread: 0, slice: 1 })}>
              <ScanSearch data-icon="single-chair" />
            </IconButton>
            <IconButton label="Inspect" onClick={handleInspect}>
              <Microscope data-icon="inspect" />
            </IconButton>
            <IconButton label="Warp" aria-pressed={warpOpen} onClick={onWarp}>
              <Waves data-icon="warp" />
            </IconButton>
            <IconButton label="Settings" onClick={openMore}>
              <Settings data-icon="settings" />
            </IconButton>
          </div>
        </div>

        <SheetContent
          side="right"
          className="more-sheet"
          onInteractOutside={(e) => e.preventDefault()}
          onPointerDownOutside={(e) => e.preventDefault()}
          onFocusOutside={(e) => e.preventDefault()}
        >
          <SheetHeader>
            <SheetTitle>Details</SheetTitle>
            <SheetDescription className="sr-only">Additional display settings.</SheetDescription>
          </SheetHeader>
          <FieldGroup className="sheet-fields">
            <Field className="setting-row">
              <FieldLabel htmlFor="color-mode">Color</FieldLabel>
              <ToggleGroup
                id="color-mode"
                type="single"
                value={settings.colorMode}
                variant="outline"
                size="sm"
                aria-label="Color mode"
                onValueChange={(value) => {
                  if (isColorMode(value)) onChange({ colorMode: value })
                }}
              >
                {colorModes.map((mode) => (
                  <ToggleGroupItem key={mode.value} value={mode.value} aria-label={mode.label}>
                    {mode.label}
                  </ToggleGroupItem>
                ))}
              </ToggleGroup>
            </Field>

            <Field orientation="horizontal" className="setting-row">
              <Tooltip>
                <TooltipTrigger asChild>
                  <FieldLabel htmlFor="edges-switch">Edges</FieldLabel>
                </TooltipTrigger>
                {settings.level >= OVERVIEW_LEVEL && (
                  <TooltipContent>Outlines appear on the selected tile at overview levels.</TooltipContent>
                )}
              </Tooltip>
              <Switch
                id="edges-switch"
                checked={settings.showEdges}
                onCheckedChange={(checked) => onChange({ showEdges: checked })}
                aria-label="Edges"
              />
            </Field>

            <Field orientation="horizontal" className="setting-row">
              <Tooltip>
                <TooltipTrigger asChild>
                  <FieldLabel htmlFor="features-switch">Features</FieldLabel>
                </TooltipTrigger>
                {settings.level >= OVERVIEW_LEVEL && (
                  <TooltipContent>Exact detail appears on the selected tile at overview levels.</TooltipContent>
                )}
              </Tooltip>
              <Switch
                id="features-switch"
                checked={settings.showFeatures}
                onCheckedChange={(checked) => onChange({ showFeatures: checked })}
                aria-label="Features"
              />
            </Field>

            <Field className="setting-row">
              <Tooltip>
                <TooltipTrigger asChild>
                  <FieldLabel htmlFor="relief-slider">
                    <span>Height</span>
                    <span className="dock-value">×{effectiveRelief}</span>
                  </FieldLabel>
                </TooltipTrigger>
                {!reliefIsMagnified && <TooltipContent>Exact height</TooltipContent>}
              </Tooltip>
              <Slider
                id="relief-slider"
                aria-label="Height"
                min={1}
                max={80}
                step={1}
                value={[effectiveRelief]}
                onValueChange={(value) => onChange({ relief: value[0] ?? effectiveRelief })}
              />
              <div className="dock-actions">
                <HeightReset
                  exact={!reliefIsMagnified}
                  onReset={() => onChange({ relief: 1 })}
                />
              </div>
              {reliefIsMagnified && (
                <FieldDescription id="relief-warning" className="relief-warning">
                  Magnified · not to scale
                </FieldDescription>
              )}
            </Field>
          </FieldGroup>
        </SheetContent>
      </Sheet>
    </TooltipProvider>
  )
}
