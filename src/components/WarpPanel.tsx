import { Eye, FileCheck2, Info, Undo2 } from "lucide-react"

import { Button } from "@/components/ui/button"
import { Sheet, SheetContent, SheetDescription, SheetHeader, SheetTitle } from "@/components/ui/sheet"
import { Slider } from "@/components/ui/slider"
import { ToggleGroup, ToggleGroupItem } from "@/components/ui/toggle-group"
import { Tooltip, TooltipContent, TooltipTrigger } from "@/components/ui/tooltip"
import type { ExplorerSettings } from "@/lib/explorer-state"
import { FAMILIES, WARP_SHAPES, magnification, type WarpShape } from "@/lib/warp"

import "./warp-panel.css"

type WarpPanelProps = {
  open: boolean
  onOpenChange: (open: boolean) => void
  settings: ExplorerSettings
  onChange: (patch: Partial<ExplorerSettings>) => void
}

const SHAPE_LABELS: Record<WarpShape, string> = { a: "A", b: "B", c: "C" }

const LEAN_PROOF_URL = "https://github.com/Sager611/einstein-tile-3d-viz/tree/main/lean"

function familyTooltip(shape: WarpShape): string {
  const { k2, e } = FAMILIES[shape]
  const k = k2.map((n) => (n % 2 === 0 ? String(n / 2) : `${n}/2`)).join(", ")
  return `Family ${SHAPE_LABELS[shape]}: V(x) = Σ over the 24 rotations R of cos(2π k·Rx) R⁻¹e, k = (${k}), e = (${e.join(", ")}). Lean theorem family${SHAPE_LABELS[shape]}: for every amplitude 0 < s ≤ 10⁻⁹ the solid (id + sV)(Chair44) tiles space, has no symmetry, tiles only non-periodically (given the paper's theorem), and differs from Chair44. Not yet proved: that different s give non-congruent solids.`
}

function superscript(n: number): string {
  const map: Record<string, string> = { "-": "⁻", "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹" }
  return String(n).split("").map((c) => map[c] ?? c).join("")
}

function formatMagnification(value: number): string {
  const exponent = Math.floor(Math.log10(value))
  const mantissa = value / 10 ** exponent
  return `×${mantissa.toFixed(1)}·10${superscript(exponent)}`
}

const EXPLAINER =
  "Every Chair44 tiling places its tiles by motions of one group: the 24 cube rotations combined with the body-centred cubic lattice (space group I432). A deformation of space that commutes with that group turns every tiling into a tiling by one new solid. A, B, C are three such deformations, each a whole family in its amplitude s, all proved in Lean. The true shapes differ from Chair44 by at most 10⁻⁷; the slider magnifies the difference."

function statusLabel(settings: ExplorerSettings): string {
  if (settings.warp === 0) return "Original Chair44"
  return `Proved in Lean · shown ${formatMagnification(magnification({ shape: settings.warpShape, amount: settings.warp }))}`
}

function statusTooltip(settings: ExplorerSettings): string {
  if (settings.warp === 0) return "Flat faces: the paper's solid."
  return `${familyTooltip(settings.warpShape)} The view multiplies the proved displacement by the shown factor to make it visible; the magnified shape is an illustration of the proved one.`
}

export function WarpPanel({ open, onOpenChange, settings, onChange }: WarpPanelProps) {
  return (
    <Sheet open={open} onOpenChange={onOpenChange} modal={false}>
      <SheetContent
        side="left"
        className="warp-sheet"
        onInteractOutside={(event) => event.preventDefault()}
        onPointerDownOutside={(event) => event.preventDefault()}
        onFocusOutside={(event) => event.preventDefault()}
      >
        <SheetHeader className="warp-header">
          <SheetTitle className="warp-title">
            Warp
            <Tooltip>
              <TooltipTrigger asChild>
                <Button type="button" variant="ghost" size="icon-xs" aria-label="About warps">
                  <Info />
                </Button>
              </TooltipTrigger>
              <TooltipContent side="right" className="warp-tooltip">
                {EXPLAINER}
              </TooltipContent>
            </Tooltip>
          </SheetTitle>
          <SheetDescription className="sr-only">{EXPLAINER}</SheetDescription>
        </SheetHeader>

        <Tooltip>
          <TooltipTrigger asChild>
            <div
              className="warp-status"
              data-flat={settings.warp === 0 ? "true" : undefined}
              data-kind="proved"
              role="status"
            >
              {statusLabel(settings)}
            </div>
          </TooltipTrigger>
          <TooltipContent side="right" className="warp-tooltip">
            {statusTooltip(settings)}
          </TooltipContent>
        </Tooltip>

        <div className="warp-row">
          <ToggleGroup
            type="single"
            variant="outline"
            size="sm"
            value={settings.warpShape}
            aria-label="Warp family"
            onValueChange={(value) => {
              if (WARP_SHAPES.includes(value as WarpShape)) onChange({ warpShape: value as WarpShape })
            }}
          >
            {WARP_SHAPES.map((shape) => (
              <Tooltip key={shape}>
                <TooltipTrigger asChild>
                  <ToggleGroupItem value={shape} aria-label={`Family ${SHAPE_LABELS[shape]}`}>
                    {SHAPE_LABELS[shape]}
                  </ToggleGroupItem>
                </TooltipTrigger>
                <TooltipContent side="bottom" className="warp-tooltip">
                  {familyTooltip(shape)}
                </TooltipContent>
              </Tooltip>
            ))}
          </ToggleGroup>
        </div>

        <div className="warp-row warp-amount">
          <span>Magnify</span>
          <span className="warp-value">{Math.round(settings.warp * 100)}%</span>
          <Slider
            aria-label="Magnification"
            min={0}
            max={1}
            step={0.01}
            value={[settings.warp]}
            onValueChange={(value) => onChange({ warp: value[0] ?? settings.warp })}
          />
        </div>

        <div className="warp-row warp-actions">
          <Tooltip>
            <TooltipTrigger asChild>
              <Button
                type="button"
                variant="outline"
                size="icon-sm"
                aria-label="Show interlocking tiles"
                onClick={() => onChange({ level: 1, spread: 0.3, slice: 1, warp: settings.warp || 1 })}
              >
                <Eye />
              </Button>
            </TooltipTrigger>
            <TooltipContent>Show interlocking tiles</TooltipContent>
          </Tooltip>
          <Tooltip>
            <TooltipTrigger asChild>
              <Button type="button" variant="outline" size="icon-sm" aria-label="Flat faces" onClick={() => onChange({ warp: 0 })}>
                <Undo2 />
              </Button>
            </TooltipTrigger>
            <TooltipContent>Flat faces</TooltipContent>
          </Tooltip>
          <Tooltip>
            <TooltipTrigger asChild>
              <Button type="button" variant="outline" size="icon-sm" asChild>
                <a href={LEAN_PROOF_URL} target="_blank" rel="noreferrer" aria-label="Lean proof">
                  <FileCheck2 />
                </a>
              </Button>
            </TooltipTrigger>
            <TooltipContent>Lean proof</TooltipContent>
          </Tooltip>
        </div>
      </SheetContent>
    </Sheet>
  )
}
