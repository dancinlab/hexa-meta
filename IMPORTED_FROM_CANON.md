# Imported from canon (2026-05-10)

All files in this repo were **moved** out of `dancinlab/canon` at `canon@a86ca143`
during the canon-minimization migration. `hexa-meta` is the new home for n=6
self-referential material; canon no longer holds these (recover prior history via
`git log` in canon).

- `proofs/` — 11 files ← `canon:theory/proofs/`
- `papers/` — 24 files ← `canon:papers/`
- `tools/`  — 15 dirs ← `canon:bridge/origins/`

## Excluded on import (security / hygiene)

- `tools/ready-absorber/findings/` — 40 MB of file-discovery scan output containing
  `preview` snippets of scanned files, including **live Google OAuth credentials** (a
  `gmail_credentials.json` / `gmail_token.json` that the scanner scooped up). Removed
  before publishing. (⚠️ Those credentials also live in `dancinlab/canon` history —
  see SECURITY note: rotate the Google client secret + tokens and scrub canon history.)
- `tools/ready-absorber/{state.json,phase2_state.json,verified/,growth/}` — runtime state.
