import {
  Dialog,
  DialogContent,
  DialogDescription,
  DialogHeader,
  DialogTitle,
} from '@/components/ui/dialog'

type InfoDialogProps = {
  open: boolean
  onOpenChange: (open: boolean) => void
}

export function InfoDialog({ open, onOpenChange }: InfoDialogProps) {
  return (
    <Dialog open={open} onOpenChange={onOpenChange}>
      <DialogContent>
        <DialogHeader>
          <DialogTitle>Chair44</DialogTitle>
          <DialogDescription>One shape. A hierarchy that never repeats.</DialogDescription>
        </DialogHeader>

        <div className="info-body">
          <section>
            <p>
              Chair44 is a proposed 2026 tile by Ioannis Tsiokos. Its seven-cube carrier is
              alone periodic; the actual tile has 192 square-pyramid bumps and recesses on 24
              panels. Bases are 0.02 units, with heights from 0.0001–0.0012 units.
            </p>
            <p>
              The exact microgeometry here was independently reconstructed. Finite 8^n patches
              are not proof of the full infinite world.
            </p>
          </section>

          <section>
            <p>
              Spread 0 and Height 1× show exact contacts. Layers removes whole tiles. Higher
              relief is illustrative and restricted to one tile.
            </p>
            <p>These are preprints; no journal-acceptance claim is made.</p>
          </section>

          <section>
            <p>
              Warp: a deformation of space that commutes with every motion used by Chair44
              tilings turns each tiling into a tiling by one new solid. For the Lean warp, Lean 4
              proves the warped tile has no symmetry and warped tilings have no period, assuming
              only the paper's theorem. Other warp shapes are illustrations.
            </p>
          </section>

          <p className="sr-only">
            At overview levels, all tiles and placements are retained; micro-surface keys and
            unselected outlines are omitted for performance; selected tiles have exact detail.
            Click legend entries to hide or show groups; use Show all to restore them.
          </p>

          <nav className="source-links" aria-label="Sources">
            <a href="https://arxiv.org/abs/2609.19214" target="_blank" rel="noopener noreferrer">
              Primary paper
            </a>
            <a href="https://arxiv.org/abs/2609.24779" target="_blank" rel="noopener noreferrer">
              Independent paper
            </a>
            <a href="https://x.com/nattyover/status/2102764113684533336" target="_blank" rel="noopener noreferrer">
              Inspiration
            </a>
            <a href="https://github.com/Sager611/einstein-tile-3d-viz/blob/main/docs/geometry.md" target="_blank" rel="noopener noreferrer">
              Reconstruction notes
            </a>
            <a href="https://github.com/Sager611/einstein-tile-3d-viz/tree/main/lean" target="_blank" rel="noopener noreferrer">
              Lean proof
            </a>
          </nav>

          <details className="key-guide">
            <summary>Help</summary>
            <p>Drag to orbit · right-drag to pan · pinch or scroll to zoom · tap a tile to select.</p>
            <p>R reset · Space orbit · Esc clear selection.</p>
          </details>
        </div>
      </DialogContent>
    </Dialog>
  )
}
