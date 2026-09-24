import { Eye, FileCheck2, Info, Undo2 } from "lucide-react"

import { Button } from "@/components/ui/button"
import { Sheet, SheetContent, SheetDescription, SheetHeader, SheetTitle } from "@/components/ui/sheet"
import { Slider } from "@/components/ui/slider"
import { ToggleGroup, ToggleGroupItem } from "@/components/ui/toggle-group"
import { Tooltip, TooltipContent, TooltipTrigger } from "@/components/ui/tooltip"
import type { ExplorerSettings } from "@/lib/explorer-state"
import { LEAN_CERTIFIED_AMOUNT, WARP_SHAPES, leanMagnification, type WarpShape } from "@/lib/warp"

import "./warp-panel.css"

type WarpPanelProps = {
  open: boolean
  onOpenChange: (open: boolean) => void
  settings: ExplorerSettings
  onChange: (patch: Partial<ExplorerSettings>) => void
}

const SHAPE_LABELS: Record<WarpShape, string> = { lean: "Lean", nubs: "Nubs", wave: "Wave", ridge: "Ridge" }

const LEAN_PROOF_URL = "https://github.com/Sager611/einstein-tile-3d-viz/tree/main/lean"

const LEAN_TOOLTIP =
  "Proved in Lean 4 (theorem chair44_warp_concrete): these warped tiles fill space, the warped tile differs from Chair44 and has no symmetry, and warped Chair44 tilings have no period. The proof uses a displacement of at most 3.6·10⁻⁸; the view magnifies it, and up to the certified mark the same Lipschitz bound still guarantees a valid warp."

const FACE_TOOLTIP =
  "Illustration. The tiling is checked numerically. Ruling out periods also needs this warped tile to have no symmetry, which Lean proves only for the Lean warp."

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
  "Every Chair44 tiling places its tiles by motions of one group: the 24 cube rotations combined with the body-centred cubic lattice (space group I432). Any deformation of space that commutes with that group turns every tiling into a tiling by one new, congruent solid. Lean: a smooth wave averaged over the 24 rotations, proved to be such a deformation. Nubs, Wave, Ridge: face shapes f(u,v) = −f(v,u), since each unit face is fixed only by a diagonal half-turn."

const isCertified = (settings: ExplorerSettings): boolean =>
  settings.warpShape === "lean" && settings.warp <= LEAN_CERTIFIED_AMOUNT

function statusLabel(settings: ExplorerSettings): string {
  if (settings.warp === 0) return "Original Chair44"
  if (settings.warpShape !== "lean") return "Illustration · tiles exactly"
  const magnification = formatMagnification(leanMagnification(settings.warp))
  if (isCertified(settings)) return `Proved in Lean · ${magnification}`
  return `Lean warp · ${magnification} · numeric`
}

function statusTooltip(settings: ExplorerSettings): string {
  if (settings.warp === 0) return "Flat faces: the paper's solid."
  if (settings.warpShape !== "lean") return FACE_TOOLTIP
  if (isCertified(settings)) return LEAN_TOOLTIP
  return `${LEAN_TOOLTIP} Above ${Math.round(LEAN_CERTIFIED_AMOUNT * 100)}% the magnification exceeds that bound; there the warp is checked numerically only.`
}

export function WarpPanel({ open, onOpenChange, settings, onChange }: WarpPanelProps) {
  const percent = Math.round(settings.warp * 100)
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
              data-kind={isCertified(settings) ? "proved" : "illustration"}
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
            aria-label="Face shape"
            onValueChange={(value) => {
              if (WARP_SHAPES.includes(value as WarpShape)) onChange({ warpShape: value as WarpShape })
            }}
          >
            {WARP_SHAPES.map((shape) => (
              <ToggleGroupItem key={shape} value={shape} aria-label={SHAPE_LABELS[shape]}>
                {SHAPE_LABELS[shape]}
              </ToggleGroupItem>
            ))}
          </ToggleGroup>
        </div>

        <div className="warp-row warp-amount">
          <span>Amount</span>
          <span className="warp-value">{percent}%</span>
          <Slider
            aria-label="Warp amount"
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
