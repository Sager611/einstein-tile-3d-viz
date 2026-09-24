import { Eye, FileCheck2, Infinity as InfinityIcon, Info, Undo2 } from "lucide-react"

import { Button } from "@/components/ui/button"
import { Sheet, SheetContent, SheetDescription, SheetHeader, SheetTitle } from "@/components/ui/sheet"
import { Slider } from "@/components/ui/slider"
import { Switch } from "@/components/ui/switch"
import { ToggleGroup, ToggleGroupItem } from "@/components/ui/toggle-group"
import { Tooltip, TooltipContent, TooltipTrigger } from "@/components/ui/tooltip"
import type { ExplorerSettings } from "@/lib/explorer-state"
import { FAMILIES, WARP_SHAPES, amplitude, magnification, type WarpShape } from "@/lib/warp"

import "./warp-panel.css"

type WarpPanelProps = {
  open: boolean
  onOpenChange: (open: boolean) => void
  settings: ExplorerSettings
  onChange: (patch: Partial<ExplorerSettings>) => void
}

const SHAPE_LABELS: Record<WarpShape, string> = { a: "A", b: "B", c: "C" }

const LEAN_BLOB = "https://github.com/Sager611/einstein-tile-3d-viz/blob/main/lean/ChairWarp"
/** Direct links to each family's theorems (line anchors in the Lean sources). */
const FAMILY_PROOF_URL: Record<WarpShape, string> = {
  a: `${LEAN_BLOB}/FamilyFinal.lean#L172`,
  b: `${LEAN_BLOB}/FamilyFinal.lean#L180`,
  c: `${LEAN_BLOB}/FamilyFinal.lean#L188`,
}
const NONCONGRUENT_URL: Record<WarpShape, string> = {
  a: `${LEAN_BLOB}/Congruence.lean#L369`,
  b: `${LEAN_BLOB}/Congruence.lean#L374`,
  c: `${LEAN_BLOB}/Congruence.lean#L379`,
}

const PROOF_TOOLTIP =
  "Ghost: the original Chair44. White → red arrow: the point Lean proves the warp pushes out of Chair44, so the tile is new. Dark dots: four corners every such warp fixes; the proofs that the tile is rigid and that different s give non-congruent tiles pivot on them. Select a tile to move the markers."

function familyTooltip(shape: WarpShape): string {
  const { k2, e } = FAMILIES[shape]
  const k = k2.map((n) => (n % 2 === 0 ? String(n / 2) : `${n}/2`)).join(", ")
  return `Family ${SHAPE_LABELS[shape]}: V(x) = Σ over the 24 rotations R of cos(2π k·Rx) R⁻¹e, k = (${k}), e = (${e.join(", ")}). Lean theorem family${SHAPE_LABELS[shape]}: for every amplitude 0 < s ≤ 10⁻⁹ the solid (id + sV)(Chair44) tiles space, has no symmetry, tiles only non-periodically (given the paper's theorem), and differs from Chair44; different s give non-congruent solids (family${SHAPE_LABELS[shape]}_noncongruent), so the family is infinite.`
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
  "Every Chair44 tiling places its tiles by motions of one group: the 24 cube rotations combined with the body-centred cubic lattice (space group I432). A deformation of space that commutes with that group turns every tiling into a tiling by one new solid. A, B, C are three such deformations, each an infinite family of pairwise non-congruent tiles (one per amplitude s), all proved in Lean. The true shapes differ from Chair44 by at most 10⁻⁷; the slider magnifies the difference."

function formatAmplitude(value: number): string {
  if (value === 0) return "0"
  const exponent = Math.floor(Math.log10(value))
  return `${(value / 10 ** exponent).toFixed(1)}·10${superscript(exponent)}`
}

function statusLabel(settings: ExplorerSettings): string {
  if (settings.warp === 0) return "Original Chair44"
  return `Proved in Lean · view ${formatMagnification(magnification(settings.warpShape))}`
}

function statusTooltip(settings: ExplorerSettings): string {
  if (settings.warp === 0) return "Flat faces: the paper's solid (s = 0)."
  return `${familyTooltip(settings.warpShape)} Each slider position is one proved tile; the view multiplies its true displacement by the shown factor to make it visible.`
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
        onOpenAutoFocus={(event) => event.preventDefault()}
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
          <Tooltip>
            <TooltipTrigger asChild>
              <span className="warp-label">s</span>
            </TooltipTrigger>
            <TooltipContent side="right" className="warp-tooltip">
              Amplitude of the warp. Every s in (0, 10⁻⁹] is a proved tile, and different s give non-congruent tiles: an infinite family.
            </TooltipContent>
          </Tooltip>
          <span className="warp-value">s = {formatAmplitude(amplitude(settings.warp))}</span>
          <Slider
            aria-label="Amplitude s"
            min={0}
            max={1}
            step={0.01}
            value={[settings.warp]}
            onValueChange={(value) => onChange({ warp: value[0] ?? settings.warp })}
          />
        </div>

        <div className="warp-row warp-proof">
          <Switch
            id="warp-proof"
            size="sm"
            checked={settings.proof}
            disabled={settings.warp === 0}
            aria-label="Proof overlay"
            onCheckedChange={(checked) => onChange({ proof: checked })}
          />
          <label htmlFor="warp-proof">Proof</label>
          <Tooltip>
            <TooltipTrigger asChild>
              <Button type="button" variant="ghost" size="icon-xs" aria-label="About the proof overlay">
                <Info />
              </Button>
            </TooltipTrigger>
            <TooltipContent side="right" className="warp-tooltip">
              {PROOF_TOOLTIP}
            </TooltipContent>
          </Tooltip>
          <span className="warp-legend" aria-hidden="true">
            <i data-kind="ghost" />
            <i data-kind="point" />
            <i data-kind="corner" />
          </span>
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
                <a href={FAMILY_PROOF_URL[settings.warpShape]} target="_blank" rel="noreferrer" aria-label="Lean proof">
                  <FileCheck2 />
                </a>
              </Button>
            </TooltipTrigger>
            <TooltipContent>Lean proof: family {SHAPE_LABELS[settings.warpShape]} tiles, rigid, non-periodic</TooltipContent>
          </Tooltip>
          <Tooltip>
            <TooltipTrigger asChild>
              <Button type="button" variant="outline" size="icon-sm" asChild>
                <a href={NONCONGRUENT_URL[settings.warpShape]} target="_blank" rel="noreferrer" aria-label="Lean proof: infinite family">
                  <InfinityIcon />
                </a>
              </Button>
            </TooltipTrigger>
            <TooltipContent>Lean proof: different s give non-congruent tiles</TooltipContent>
          </Tooltip>
        </div>
      </SheetContent>
    </Sheet>
  )
}
